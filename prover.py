import openai
from alectryon.serapi import annotate, Sentence
from tenacity import retry, stop_after_attempt, wait_random_exponential
from joblib import Memory
from contextlib import redirect_stderr
from dotenv import load_dotenv
import os

load_dotenv()

memory = Memory("cachegpt")

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


def prove_theorem_using_gpt(context, theorem, model):
    messages = [
        {
            "role": "system",
            "content": "You are an automated theorem prover that can prove theorems in Coq. Your entire response must be valid Coq code. You should explain your reasoning (what the proof steps are attempting to do), but only in comments inside the Coq code. The following messages will all consist of a theorem statement (possibly preceded by necessary definitions, imports, etc.), and your response must be a valid Coq proof of that theorem. Do not include the theorem statement in your proof. Your response must be in this format: ```coq\n Proof.\n<proof>. Qed.\n```. Remember: do not add any other text besides Coq code and do not repeat the theorem statement or any imports, definitions, lemmas, etc. provided in the prompt.",
        },
        {"role": "user", "content": context + "\n\n" + theorem},
    ]
    # Get proof from inside the Coq code
    response = ask(messages, model)
    proof_contents = response.split("Proof.")[1].split("Qed.")[0]
    return "Proof.\n" + proof_contents + "\nQed."


def prove_lemma_using_gpt(context, proof_state, model, prev_attempt_with_error=None):
    messages = [
        {
            "role": "system",
            "content": "You are an automated theorem prover that can prove lemmas in Coq. Your entire response must be valid Coq code. You should explain your reasoning (what the proof steps are attempting to do), but only in comments inside the Coq code. The following message will consist of a proof state (hypotheses followed by the goal), and your response must be a valid Coq lemma whose statement contains the hypotheses and the conclusion, along with a valid proof of that goal. Your response must be in this format: ```coq\n Lemma <lemma_name> : <lemma_statement>.\n Proof.\n<proof>. Qed.\n```. Remember: do not add any other text besides Coq code and do not repeat any imports, definitions, lemmas, etc. provided in the prompt.",
        },
        {"role": "user", "content": context + "\n\n" + proof_state},
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
    lemma_with_proof_contents = response.split("Lemma ")[1].split("Qed.")[0]
    return "Lemma " + lemma_with_proof_contents + "\nQed."


def annotate_and_fetch_error(context, theorem_with_proof):
    first_error_idx = -1
    annotated_proof = annotate([context + "\n\n" + theorem_with_proof])
    annotated_proof_sentences = []
    i = 0
    for step in annotated_proof[0]:
        if not isinstance(step, Sentence):
            continue
        if len(step.messages) > 0:
            if first_error_idx == -1 and not any(
                "deprecated" in message.contents for message in step.messages
            ):
                first_error_idx = i
        annotated_proof_sentences.append(step)
        i += 1
    return annotated_proof_sentences, first_error_idx


def recursively_prove_lemma(
    context,
    proof_state,
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
        lemma_with_proof = prove_lemma_using_gpt(context, proof_state, MODEL)
    # Otherwise, try to prove the lemma again using the previous attempt's error message
    else:
        print(f"ERROR MESSAGE (SENTENCE #{prev_attempt_error_idx})")
        print(prev_attempt_error_message)
        print(f"LEMMA PROOF IS INVALID. TRYING AGAIN... (ATTEMPT {depth})")
        lemma_with_proof = prove_lemma_using_gpt(
            context,
            proof_state,
            MODEL,
            (
                prev_attempt_lemma_with_proof,
                prev_attempt_error_message,
            ),
        )

    # Print the lemma's proof
    print("GPT PROOF OF LEMMA")
    print(lemma_with_proof)
    print()

    # Check if lemma's proof is valid
    annotated_lemma_sentences, first_error_idx = annotate_and_fetch_error(
        context, lemma_with_proof
    )

    # If invalid, try again recursively
    if first_error_idx != -1:
        error_message = annotated_lemma_sentences[first_error_idx].messages[0].contents
        return recursively_prove_lemma(
            context,
            proof_state,
            depth + 1,
            lemma_with_proof,
            error_message,
            first_error_idx,
        )
    # Otherwise, return the lemma's proof
    else:
        print("LEMMA IS VALID")
        return lemma_with_proof


def check_theorem_proof_and_maybe_reprove_using_lemmas(
    context, theorem, proof, depth=0
):
    # Break out of recursion if we've reached the max depth
    if depth > MAX_THEOREM_ERROR_COUNT:
        print("MAX THEOREM ERROR COUNT REACHED. GIVING UP.")
        exit(1)

    print(f"ATTEMPTED COQ PROOF (LEMMAS USED: {depth})")
    print(context + "\n" + theorem + "\n" + proof)
    print()

    # Check if proof is valid and get error index if any
    annotated_proof_sentences, first_error_idx = annotate_and_fetch_error(
        context, theorem + "\n" + proof
    )

    # If there is an error, extract the proof state before the error
    # and try to prove that goal separately as a lemma
    if first_error_idx != -1:
        prev_sentence = annotated_proof_sentences[first_error_idx - 1]
        error_message = annotated_proof_sentences[first_error_idx].messages[0].contents
        print(f"ERROR MESSAGE (SENTENCE #{first_error_idx})")
        print(error_message)
        proof_state = ""
        for hypothesis in prev_sentence.goals[0].hypotheses:
            proof_state += ", ".join(hypothesis.names) + " : " + hypothesis.type + "\n"
        proof_state += "------------------\n"
        proof_state += prev_sentence.goals[0].conclusion
        print("PROOF STATE")
        print(proof_state)
        print()

        lemma_with_proof = recursively_prove_lemma(context, proof_state)

        # Now that we have a valid lemma, we can use it to complete the proof
        # Convert sentences to Coq code
        proof_using_lemma = ""
        i = 0
        for sentence in annotated_proof_sentences:
            if i == first_error_idx:
                proof_using_lemma += (
                    "apply " + lemma_with_proof.split("Lemma ")[1].split(" ")[0] + ".\n"
                )
            else:
                proof_using_lemma += sentence.contents + "\n"
            i += 1

        return check_theorem_proof_and_maybe_reprove_using_lemmas(
            context + "\n" + lemma_with_proof, theorem, proof_using_lemma, depth + 1
        )

    # Otherwise, our proof is valid, so return the entire code
    else:
        full_coq_code = context + "\n" + theorem + "\n" + proof
        return full_coq_code


with open("context.v", "r") as f:
    context = f.read()
with open("theorem.v", "r") as f:
    theorem = f.read()

proof = prove_theorem_using_gpt(
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
