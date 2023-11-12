import openai
from alectryon.serapi import annotate, Sentence, Text
from tenacity import retry, stop_after_attempt, wait_random_exponential
from joblib import Memory
from contextlib import redirect_stderr
from dotenv import load_dotenv
import os

load_dotenv()

memory = Memory("cachegpt", verbose=0)

openai.api_key = os.getenv("OPENAI_API_KEY")
MODEL = "gpt-4"
MAX_LEMMA_DEPTH = 2
MAX_THEOREM_ERROR_COUNT = 5


# Caching process ported from https://github.com/metareflection/gpt-call
@retry(wait=wait_random_exponential(min=10, max=30), stop=stop_after_attempt(25))
def generate(messages, model):  # "gpt-3.5-turbo", "gpt-4"
    print("calling GPT... model=" + model)
    return openai.ChatCompletion.create(
        model=model,
        messages=messages,
    )


@memory.cache
def ask(messages, model):
    response = generate(messages, model)
    return response.choices[0].message.content


def prove_using_gpt(context, theorem_or_lemma, model, prev_attempt_with_error=None):
    messages = [
        {
            "role": "system",
            "content": "You are an automated theorem prover that can prove theorems and lemmas in Coq. Your entire response must be valid Coq code. You should explain your reasoning (what the proof steps are attempting to do), but only in comments inside the Coq code. The following messages will all consist of a theorem statement (possibly preceded by necessary definitions, imports, etc.), and your response must be a valid Coq proof of that theorem. Your response must be in this format: ```coq\n Proof.\n<proof>. Qed.\n```. Remember: do not add any other text besides Coq code and do not repeat any imports, definitions, lemmas, etc. provided in the prompt.",
        },
        {"role": "user", "content": context + "\n\n" + theorem_or_lemma},
    ]
    if prev_attempt_with_error is not None:
        prev_attempt, error = prev_attempt_with_error
        messages += [
            {"role": "assistant", "content": "```coq" + prev_attempt + "\n```"},
            {
                "role": "user",
                "content": "This is incorrect; Coq produced the following error message: "
                + error
                + "\n\nPlease try again.",
            },
        ]
    response = ask(messages, model)
    proof_contents = response.split("Proof.")[1].split("Qed.")[0]
    return "Proof.\n" + proof_contents + "\nQed."


def annotate_and_fetch_error(context, theorem_with_proof):
    first_error_idx = -1
    annotated_proof = annotate([context + "\n\n" + theorem_with_proof])
    # A Fragment is a Sentence (proof step) or a Text (comment)
    annotated_proof_fragments = []
    i = 0
    for step in annotated_proof[0]:
        if isinstance(step, Sentence) and len(step.messages) > 0:
            if first_error_idx == -1 and not any(
                "deprecated" in message.contents for message in step.messages
            ):
                first_error_idx = i
        annotated_proof_fragments.append(step)
        i += 1
    return annotated_proof_fragments, first_error_idx


def proof_state_to_lemma(lemma_name, hypotheses, conclusion):
    lemma = f"Lemma {lemma_name} : "
    if len(hypotheses) > 0:
        for hypothesis in hypotheses:
            lemma += (
                "forall " + " ".join(hypothesis.names) + " : " + hypothesis.type + ", "
            )
    lemma += conclusion + ".\n"
    return lemma


def recursively_prove_lemma(
    context,
    lemma,
    depth=0,
    prev_attempt_lemma_with_proof=None,
    prev_attempt_error_message=None,
    prev_attempt_error_idx=None,
):
    # Break out of recursion if we've reached the max depth
    if depth > MAX_LEMMA_DEPTH:
        print("MAX LEMMA DEPTH REACHED. GIVING UP.")
        exit(1)

    # If this is the first attempt, try to prove the lemma
    if depth == 0:
        proof = prove_using_gpt(context, lemma, MODEL)
    # Otherwise, try to prove the lemma again using the previous attempt's error message
    else:
        print(f"ERROR MESSAGE IN LEMMA PROOF (FRAGMENT #{prev_attempt_error_idx})")
        print(prev_attempt_error_message)
        print()
        print(f"LEMMA PROOF IS INVALID. TRYING AGAIN... (ATTEMPT {depth})")
        print()
        proof = prove_using_gpt(
            context,
            lemma,
            MODEL,
            (
                prev_attempt_lemma_with_proof,
                prev_attempt_error_message,
            ),
        )

    # Print the lemma's proof
    lemma_with_proof = lemma + "\n" + proof
    print("GPT PROOF OF LEMMA")
    print(lemma_with_proof)
    print()

    # Check if lemma's proof is valid
    annotated_proof_fragments, first_error_idx = annotate_and_fetch_error(
        context, lemma_with_proof
    )

    # If invalid, try again recursively
    if first_error_idx != -1:
        error_message = annotated_proof_fragments[first_error_idx].messages[0].contents
        return recursively_prove_lemma(
            context,
            lemma,
            depth + 1,
            lemma_with_proof,
            error_message,
            first_error_idx,
        )
    # Otherwise, return the lemma's proof
    else:
        print("LEMMA IS VALID")
        print()
        return lemma_with_proof


def check_theorem_proof_and_maybe_reprove_using_lemmas(
    context, theorem, proof, depth=0
):
    # Break out of recursion if we've reached the max depth
    if depth > MAX_THEOREM_ERROR_COUNT:
        print("MAX THEOREM ERROR COUNT REACHED. GIVING UP.")
        exit(1)

    print(f"ATTEMPTED COQ PROOF (LEMMAS USED: {depth})")
    print(context + "\n\n" + theorem + "\n\n" + proof)
    print()

    # Check if proof is valid and get error index if any
    annotated_proof_fragments, first_error_idx = annotate_and_fetch_error(
        context, theorem + "\n" + proof
    )

    # If there is an error, extract the proof state before the error
    # and try to prove that goal separately as a lemma
    if first_error_idx != -1:
        # Get the closest Sentence before the error (but note that some proof fragments may be Texts, not Sentences)
        for i in range(first_error_idx - 1, -1, -1):
            if isinstance(annotated_proof_fragments[i], Sentence):
                prev_sentence = annotated_proof_fragments[i]
                break
        error_message = annotated_proof_fragments[first_error_idx].messages[0].contents
        print(f"ERROR MESSAGE IN THEOREM PROOF (FRAGMENT #{first_error_idx})")
        print(error_message)
        print()

        lemma = proof_state_to_lemma(
            "helper_lemma_" + str(depth),
            prev_sentence.goals[0].hypotheses,
            prev_sentence.goals[0].conclusion,
        )
        # String containing a space-separated list of hypothesis names, passed when applying the lemma
        lemma_args = " ".join(
            [
                " ".join(hypothesis.names)
                for hypothesis in prev_sentence.goals[0].hypotheses
            ]
        )

        lemma_with_proof = recursively_prove_lemma(context, lemma)

        # Now that we have a valid lemma, we can use it to complete the proof
        # Convert sentences to Coq code
        proof_using_lemma = ""
        for i, sentence in enumerate(annotated_proof_fragments):
            if i == first_error_idx:
                proof_using_lemma += (
                    "apply (@"
                    + lemma.split("Lemma ")[1].split(" ")[0]
                    + " "
                    + lemma_args
                    + ").\n"
                )
                goal_count_at_error_line = len(sentence.goals)
                still_in_same_goal = True
            elif i > first_error_idx:
                # If this line is trying to prove the same goal as the line that caused the error,
                # skip it
                if isinstance(sentence, Text) or len(sentence.goals) >= goal_count_at_error_line:
                    if still_in_same_goal:
                        continue
                    else:
                        proof_using_lemma += sentence.contents + "\n"
                # The first time the number of goals drops below the number of goals at the error line,
                # we know that we've reached the end of the what our helper lemma has taken care of
                else:
                    still_in_same_goal = False
            else:
                proof_using_lemma += sentence.contents + "\n"
        # Only keep proof (and discard theorem statement, etc. before it)
        proof_using_lemma = (
            "Proof.\n"
            + proof_using_lemma.split("Proof.")[-1].split("Qed.")[0]
            + "\nQed."
        )

        return check_theorem_proof_and_maybe_reprove_using_lemmas(
            context + "\n" + lemma_with_proof, theorem, proof_using_lemma, depth + 1
        )

    # Otherwise, our proof is valid, so return the entire code
    else:
        full_coq_code = context + "\n\n" + theorem + "\n\n" + proof
        return full_coq_code


with open("context.v", "r") as f:
    context = f.read()
with open("theorem.v", "r") as f:
    theorem = f.read()

proof = prove_using_gpt(
    context,
    theorem,
    MODEL,
)


with open("stderr.txt", "w") as f:
    with redirect_stderr(f):
        full_coq_code = check_theorem_proof_and_maybe_reprove_using_lemmas(
            context, theorem, proof
        )

        print("PROOF IS VALID")
        with open("proof.v", "w") as f:
            f.write(full_coq_code)
