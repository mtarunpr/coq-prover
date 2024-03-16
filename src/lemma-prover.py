from alectryon import cli
from alectryon.serapi import Sentence, Text
from contextlib import redirect_stderr, redirect_stdout
from dotenv import load_dotenv
import re
import argparse
from coq import Theorem
from coq_parser import parse_file, parse_all_files
from pathlib import Path
from tqdm.auto import tqdm

load_dotenv()
from infer import GPT, LocalModel


LLM_TYPE = "GPT"  # GPT | LocalModel
GPT_MODEL_NAME = "gpt-4-1106-preview"
LOCAL_MODEL_NAME = "Phind/Phind-CodeLlama-34B-v2"
LOCAL_MODEL_CHECKPOINT = None
MAX_LEMMA_RETRIES = 5
MAX_LEMMA_DEPTH = 10

warning_indicators = ["deprecated", "Loading ML file", "(* debug"]
ignore_messages_keywords = [
    "Search",
    "Check",
    "Print",
    "Compute",
    "Eval",
    "Notation",
    "Fail",
    "Show",
    "Locate",
    "debug",
    "info_auto",
    "info_eauto",
]

if LLM_TYPE == "GPT":
    llm = GPT(GPT_MODEL_NAME)
elif LLM_TYPE == "LocalModel":
    llm = LocalModel(LOCAL_MODEL_NAME, LOCAL_MODEL_CHECKPOINT)
else:
    raise ValueError("Invalid model type")


def annotate_and_fetch_error(theorem: Theorem):
    """
    Annotates the theorem's proof using Alectryon and returns the annotated code
    fragments as well as the index of the first error, if any (or -1 if no error, or
    the length of the annotated code fragments if there is no error but there are
    unproven goals at the end).
    """
    warning_disabler = 'Set Silent.\nSet Warnings "-all".\nSet Debug "-all".\n\n'
    first_error_idx = -1

    try:
        err_file_path = project_dir / "proofs" / f"thm{thm_ct}_{theorem.name}.err"
    except NameError:
        err_file_path = project_dir / "coq_logs.err"

    with open(err_file_path, "w") as f_err:
        with redirect_stderr(f_err):
            annotated_code = cli.annotate_chunks(
                [
                    warning_disabler
                    + theorem.context_str
                    + "\n\n"
                    + str(theorem)
                    + "\n\n"
                    + theorem.get_proof_string()
                ],
                ".",
                "cachecoq",
                "xz",
                "coq",
                "sertop",
                ["-Q", f"{project_dir},LF"],
                cli.ExitCode(0),
            )

    with open(err_file_path, "r") as f_err:
        contents = f_err.read()
        error_exists = len(contents) > 0 and "ERROR" in contents

    # A Fragment is a Sentence (proof step) or a Text (comment)
    annotated_code_fragments = []
    i = 0
    for step in annotated_code[0]:
        if error_exists and isinstance(step, Sentence) and len(step.messages) > 0:
            if (
                first_error_idx == -1
                and not any(
                    keyword in step.contents for keyword in ignore_messages_keywords
                )
                and not all(
                    any(
                        warning_indicator in message.contents
                        for warning_indicator in warning_indicators
                    )
                    for message in step.messages
                )
            ):
                # If error is because there are no more goals, truncate the proof and try again
                if any(
                    "No more goals" in message.contents for message in step.messages
                ):
                    proof_str = ""
                    in_proof = False
                    for j in range(len(annotated_code[0])):
                        if (
                            not in_proof
                            and isinstance(annotated_code[0][j], Sentence)
                            and re.match(
                                f"{theorem.keyword}\s+{theorem.name}(?:\s+|:)",
                                annotated_code[0][j].contents,
                            )
                        ):
                            in_proof = True
                            continue
                        elif in_proof:
                            if j == i:
                                break
                            proof_str += annotated_code[0][j].contents + "\n"
                    proof_str += "Qed."
                    theorem.proof = re.findall(
                        r"(.+?\.)(?:\s+|$)", proof_str, flags=re.DOTALL
                    )

                    return annotate_and_fetch_error(theorem)
                # Otherwise we have our first error
                first_error_idx = i
        annotated_code_fragments.append(step)
        i += 1

    if first_error_idx == -1:
        try:
            confirm_proof(annotated_code_fragments)
        except Exception:
            first_error_idx = len(annotated_code_fragments)

    return annotated_code_fragments, first_error_idx


def proof_state_to_lemma(
    lemma_name_suffix: str, hypotheses, conclusion, preamble, context_str: str
):
    """
    Converts a proof state to a lemma that, if applied, would complete the proof
    of the current goal.
    """
    lemma_stmt = ""
    if len(hypotheses) > 0:
        for hypothesis in hypotheses:
            lemma_stmt += (
                "forall " + " ".join(hypothesis.names) + " : " + hypothesis.type + ", "
            )
    lemma_stmt += conclusion

    # Replace "helper_lemma" with a better name
    lemma_name = llm.create_lemma_name(
        f"Lemma helper_lemma : {lemma_stmt}", lemma_name_suffix
    )

    lemma = Theorem(
        "Lemma",
        lemma_name,
        lemma_stmt,
        [],
        preamble,
        context_str,
    )

    return lemma


def get_prev_sentence_and_error_message(annotated_code_fragments, first_error_idx):
    """
    Returns the Sentence before the one with the error, along with the error message.
    """
    # Get the closest Sentence before the error
    for i in range(first_error_idx - 1, -1, -1):
        if isinstance(annotated_code_fragments[i], Sentence):
            prev_sentence = annotated_code_fragments[i]
            break
    if first_error_idx == len(annotated_code_fragments):
        # If the error is at the end, there are still unproven goals
        error_message = f'Error after step "{prev_sentence.contents}".\nMessage: There are still unproven goals.\nGoal: {prev_sentence.goals[0].conclusion}.'
    else:
        # Get first non-warning error message
        for message in annotated_code_fragments[first_error_idx].messages:
            if all(
                warning_indicator not in message.contents
                for warning_indicator in warning_indicators
            ):
                try:
                    error_message = f'Error in step "{annotated_code_fragments[first_error_idx].contents}".\nMessage: {message.contents}.\nGoal: {prev_sentence.goals[0].conclusion}.'
                    break
                except IndexError:
                    raise Exception(
                        "UNEXPECTED ERROR. Possible causes include: the input files have some error, or a warning was mistaken to be an error, or the LLM output had an Admitted.",
                        "Error message: " + message.contents,
                    )

    return prev_sentence, error_message


def confirm_proof(annotated_code_fragments):
    """
    Checks that the proof is indeed valid by ensuring that there are no
    goals left at the end. If not, prints an error message and exits.
    """
    # Get last sentence of proof
    last_sentence = None
    for i in range(len(annotated_code_fragments) - 1, -1, -1):
        if isinstance(annotated_code_fragments[i], Sentence):
            last_sentence = annotated_code_fragments[i]
            break
    # If the last sentence's goals list is not empty, there is some error
    if last_sentence is None or len(last_sentence.goals) > 0:
        raise Exception(
            "UNEXPECTED ERROR. The proof is not complete. Possible causes include: the input files had some error, or the LLM did not output syntactically correct Coq code. Nevertheless, proof.v contains the attempted proof."
        )


def recursively_prove_lemma(
    lemma: Theorem,
    depth=0,
    prev_attempt_error_message=None,
    prev_attempt_error_idx=None,
):
    """
    Recursively attempts to prove a lemma, using the previous attempt's error message.
    """
    # If a previous attempt had an error, print it
    if prev_attempt_error_message is not None:
        print(f"ERROR MESSAGE IN LEMMA PROOF (FRAGMENT #{prev_attempt_error_idx})")
        print(prev_attempt_error_message)
        print()

    # Break out of recursion if we've reached the max depth
    if depth > MAX_LEMMA_RETRIES:
        raise Exception("MAX LEMMA RETRIES EXCEEDED. GIVING UP.")

    # If this is the first attempt, try to prove the lemma
    if depth == 0:
        llm.ask_for_proof(lemma)
    # Otherwise, try to prove the lemma again using the previous attempt's error message
    else:
        print(f"LEMMA PROOF IS INVALID. TRYING AGAIN... (ATTEMPT {depth})")
        print()
        llm.ask_for_proof(lemma, prev_attempt_error_message)

    # Print the lemma's proof
    print("GPT PROOF OF LEMMA")
    print(lemma.get_proof_string())
    print()

    # Check if lemma's proof is valid
    annotated_code_fragments, first_error_idx = annotate_and_fetch_error(lemma)

    # If invalid, try again recursively
    if first_error_idx != -1:
        _, error_message = get_prev_sentence_and_error_message(
            annotated_code_fragments, first_error_idx
        )
        return recursively_prove_lemma(
            lemma,
            depth + 1,
            error_message,
            first_error_idx,
        )
    # Otherwise, return the lemma's proof
    else:
        confirm_proof(annotated_code_fragments)

        print("LEMMA PROOF IS VALID")
        print()


def check_theorem_proof_and_maybe_reprove_using_lemmas(theorem: Theorem, depth=0):
    """
    Checks if the theorem's proof is valid. If not, extracts the proof state
    before the error and tries to prove that goal separately as a lemma.
    Does this recursively until either the theorem is proven or the max depth is reached.
    """
    # Break out of recursion if we've reached the max depth
    if depth > MAX_LEMMA_DEPTH:
        raise Exception(f"MAX LEMMA DEPTH REACHED. GIVING UP.")

    print(f"ATTEMPTED {theorem.keyword.upper()} PROOF (LEMMAS USED: {depth})")
    print(
        theorem.context_str
        + "\n\n"
        + str(theorem)
        + "\n\n"
        + theorem.get_proof_string()
    )
    print()

    # Check if proof is valid and get error index if any
    annotated_code_fragments, first_error_idx = annotate_and_fetch_error(theorem)

    # If there is an error, extract the proof state before the error
    # and try to prove that goal separately as a lemma
    if first_error_idx != -1:
        prev_sentence, error_message = get_prev_sentence_and_error_message(
            annotated_code_fragments, first_error_idx
        )
        print(
            f"ERROR MESSAGE IN {theorem.keyword.upper()} PROOF (FRAGMENT #{first_error_idx})"
        )
        print(error_message)
        print()

        lemma = proof_state_to_lemma(
            str(depth),
            prev_sentence.goals[0].hypotheses,
            prev_sentence.goals[0].conclusion,
            theorem.preamble.copy(),
            theorem.context_str,
        )
        # String containing a space-separated list of hypothesis names, passed when applying the lemma
        lemma_args = " ".join(
            [
                " ".join(hypothesis.names)
                for hypothesis in prev_sentence.goals[0].hypotheses
            ]
        )

        print("TRYING TO PROVE LEMMA")
        print(lemma)
        print()

        llm.ask_for_proof(lemma)
        check_theorem_proof_and_maybe_reprove_using_lemmas(lemma, depth + 1)

        # Now that we have a valid lemma, we can
        # 1) add it to the theorem's context + preamble, and
        # 2) use it to complete the proof

        # Add lemma to theorem's context + preamble
        theorem.preamble = lemma.preamble.copy()
        theorem.context_str = lemma.context_str
        theorem.preamble.append(lemma)
        theorem.context_str += "\n\n" + str(lemma) + "\n\n" + lemma.get_proof_string()

        # Apply lemma to complete theorem's proof
        proof_using_lemma_str = ""
        for i, fragment in enumerate(annotated_code_fragments):
            if i == first_error_idx:
                proof_using_lemma_str += (
                    "apply (@" + lemma.name + " " + lemma_args + ").\n"
                )
                still_in_same_goal = True
            elif i > first_error_idx:
                # If this line is trying to prove the same goal as the line that caused the error,
                # skip it
                if isinstance(fragment, Text) or not re.match(
                    r"^[\+\-\*]+$", fragment.contents
                ):
                    if still_in_same_goal:
                        continue
                    else:
                        proof_using_lemma_str += fragment.contents
                # The first time we reach a new bullet point, we know that we've reached the end
                # of what our helper lemma has taken care of
                # TODO: This isn't reliable, e.g. if the proof doesn't use bullet points
                # and simply continues to prove the next goal instead (as the proof of the following
                # goals will have been deleted).
                else:
                    proof_using_lemma_str += fragment.contents
                    still_in_same_goal = False
            else:
                proof_using_lemma_str += fragment.contents
        # Only keep proof (and discard theorem statement, etc. before it)
        proof_using_lemma_str = (
            "Proof.\n"
            + proof_using_lemma_str.split("Proof.")[-1].split("Qed.")[0]
            + "\nQed."
        )
        # Replace the old proof with the new proof
        theorem.proof = re.findall(
            r"(.+?\.)(?:\s+|$)", proof_using_lemma_str, flags=re.DOTALL
        )

        return check_theorem_proof_and_maybe_reprove_using_lemmas(theorem, depth + 1)

    # Otherwise, our proof is valid
    else:
        confirm_proof(annotated_code_fragments)

        print(f"{theorem.keyword.upper()} PROOF IS VALID")
        print()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    g = parser.add_mutually_exclusive_group(required=True)
    g.add_argument(
        "-e",
        "--example",
        help="name of example to prove (in data/raw/lemma_examples); must contain context.v and theorem.v files",
        type=str,
    )
    g.add_argument(
        "-p",
        "--project",
        help="name of Coq project (in data/raw); parses all theorems inside project and runs a sweep",
        type=str,
    )
    args = parser.parse_args()

    if args.example:
        project_dir = (
            Path(__file__).parent.parent
            / "data"
            / "raw"
            / "lemma_examples"
            / args.example
        )

        with open(project_dir / "context.v", "r") as f:
            context_str = f.read()
        with open(project_dir / "theorem.v", "r") as f:
            theorem_str = f.read()

        theorem_str_split = theorem_str.split(" ")
        keyword = theorem_str_split[0]
        name = theorem_str_split[1]
        statement = re.search(r":\s*(.+?)\.", theorem_str, re.DOTALL).group(1).strip()

        _, preamble = parse_file("context.v", project_dir)
        theorem = Theorem(
            keyword,
            name,
            statement,
            [],
            preamble,
            context_str,
        )

        llm.ask_for_proof(theorem)

        check_theorem_proof_and_maybe_reprove_using_lemmas(theorem)

        full_coq_code = (
            theorem.context_str
            + "\n\n"
            + str(theorem)
            + "\n\n"
            + theorem.get_proof_string()
        )

        with open(project_dir / "proof.v", "w") as f_v:
            f_v.write(full_coq_code)

    elif args.project:
        project_dir = Path(__file__).parent.parent / "data" / "raw" / args.project
        file_name_to_parsed = parse_all_files(project_dir)
        thm_ct = 0
        success_ct = 0
        error_ct = 0
        theorems = []

        for file_name in file_name_to_parsed:
            theorems += list(
                filter(
                    lambda x: isinstance(x, Theorem), file_name_to_parsed[file_name][1]
                )
            )

        for theorem in tqdm(theorems):
            thm_ct += 1
            llm.ask_for_proof(theorem)

            try:
                with open(
                    project_dir / "proofs" / f"thm{thm_ct}_{theorem.name}.out", "w"
                ) as f_out:
                    with redirect_stdout(f_out):
                        print(f"PROVING {theorem.name}")
                        check_theorem_proof_and_maybe_reprove_using_lemmas(theorem)

                full_coq_code = (
                    theorem.context_str
                    + "\n\n"
                    + str(theorem)
                    + "\n\n"
                    + theorem.get_proof_string()
                )

                with open(
                    project_dir / "proofs" / f"thm{thm_ct}_{theorem.name}.v", "w"
                ) as f_v:
                    f_v.write(full_coq_code)

                success_ct += 1
            except Exception as e:
                with open(
                    project_dir / "proofs" / f"thm{thm_ct}_{theorem.name}.out", "a"
                ) as f_out:
                    f_out.write(f"Error proving {theorem.name}\n")
                    f_out.write(str(e))

                # Save proof attempt anyway
                full_coq_code = (
                    theorem.context_str
                    + "\n\n"
                    + str(theorem)
                    + "\n\n"
                    + theorem.get_proof_string()
                )

                with open(
                    project_dir / "proofs" / f"thm{thm_ct}_err_{theorem.name}.v", "w"
                ) as f_v:
                    f_v.write(full_coq_code)

                error_ct += 1

        print(f"Total theorems: {thm_ct}")
        print(f"Successes: {success_ct}")
        print(f"Errors: {error_ct}")
