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


def prove_theorem(theorem, model):
    messages = [
        {
            "role": "system",
            "content": "You are an automated theorem prover that can prove theorems in Coq. Your entire response must be valid Coq code. You are allowed to explain your reasoning, but only in comments inside the Coq code. The following messages will all consist of a theorem statement (possibly preceded by necessary definitions and other environment variables), and your response must be a valid Coq proof of that theorem. Do not include the theorem statement in your proof. Your response must begin with the keyword 'Proof.' and end with the keyword 'Qed.'",
        },
        {"role": "user", "content": theorem},
    ]
    return ask(messages, model)


def prove_lemma(proof_state, model, prev_attempt_with_error=None):
    messages = [
        {
            "role": "system",
            "content": "You are an automated theorem prover that can prove lemmas in Coq. Your entire response must be valid Coq code. You are allowed to explain your reasoning, but only in comments inside the Coq code. The following message will consist of a proof state (hypotheses followed by the goal), and your response must be a valid Coq lemma whose statement contains the hypotheses and the conclusion, along with a valid proof of that goal. Your response must be in this format: Lemma <lemma_name> : <lemma_statement>. Proof. <proof>. Qed.",
        },
        {"role": "user", "content": proof_state},
    ]
    if prev_attempt_with_error is not None:
        prev_attempt, error = prev_attempt_with_error
        messages += [
            {"role": "assistant", "content": prev_attempt},
            {
                "role": "user",
                "content": "This is incorrect; Coq produced the following error message: "
                + error
                + "\n\nPlease try again.",
            },
        ]
    return ask(messages, model)


def annotate_and_fetch_error(theorem_with_proof):
    first_error_idx = -1
    annotated_proof = annotate([theorem_with_proof])
    annotated_proof_sentences = []
    i = 0
    for step in annotated_proof[0]:
        if not isinstance(step, Sentence):
            continue
        if len(step.messages) > 0:
            if first_error_idx == -1:
                first_error_idx = i
        annotated_proof_sentences.append(step)
        print(i, step)
        i += 1
    print()
    return annotated_proof_sentences, first_error_idx


with open("theorem.v", "r") as f:
    theorem = f.read()

proof = prove_theorem(
    theorem,
    MODEL,
)


with open("stderr.txt", "w") as f:
    with redirect_stderr(f):
        print("COQ PROOF")
        print(theorem + "\n" + proof)
        print()

        print("ANNOTATED PROOF")
        annotated_proof_sentences, first_error_idx = annotate_and_fetch_error(
            theorem + "\n" + proof
        )

        # If there is an error, extract the proof state before the error
        # and try to prove that goal separately as a lemma
        if first_error_idx != -1:
            prev_sentence = annotated_proof_sentences[first_error_idx - 1]
            proof_state = ""
            for hypothesis in prev_sentence.goals[0].hypotheses:
                proof_state += (
                    ", ".join(hypothesis.names) + " : " + hypothesis.type + "\n"
                )
            proof_state += "------------------\n"
            proof_state += prev_sentence.goals[0].conclusion
            print("PROOF STATE")
            print(proof_state)
            print()
            lemma_with_proof = prove_lemma(proof_state, MODEL)
            print("GPT PROOF OF LEMMA")
            print(lemma_with_proof)
            print()

            # Check if lemma's proof is valid
            print("ANNOTATED LEMMA")
            annotated_lemma_sentences, first_error_idx_lemma = annotate_and_fetch_error(
                lemma_with_proof
            )
            if first_error_idx_lemma != -1:
                print("LEMMA PROOF IS INVALID. TRYING AGAIN...")
                lemma_with_proof = prove_lemma(
                    proof_state,
                    MODEL,
                    (
                        lemma_with_proof,
                        annotated_lemma_sentences[first_error_idx_lemma]
                        .messages[0]
                        .contents,
                    ),
                )
                print("GPT PROOF OF LEMMA - ATTEMPT 2")
                print(lemma_with_proof)
                print()

                # Check if attempt 2 lemma's proof is valid
                print("ANNOTATED LEMMA - ATTEMPT 2")
                (
                    annotated_lemma_sentences,
                    first_error_idx_lemma,
                ) = annotate_and_fetch_error(lemma_with_proof)
                if first_error_idx_lemma != -1:
                    print("ERROR AGAIN. GIVING UP.")
                    exit(1)
                else:
                    print("LEMMA IS VALID")
            else:
                print("LEMMA IS VALID")

            print()

            # Now that we have a valid lemma, we can use it to complete the proof
            print("PROOF USING LEMMA")
            # Convert sentences to Coq code
            proof_using_lemma = ""
            i = 0
            for sentence in annotated_proof_sentences:
                if i == first_error_idx:
                    proof_using_lemma += (
                        "apply " + lemma_with_proof.split(" ")[1] + ".\n"
                    )
                else:
                    proof_using_lemma += sentence.contents + "\n"
                i += 1
            print(proof_using_lemma)
            print()

            print("ANNOTATED PROOF USING LEMMA")
            full_coq_code = lemma_with_proof + "\n\n" + theorem + "\n" + proof_using_lemma
            annotated_proof_sentences, first_error_idx = annotate_and_fetch_error(
                full_coq_code
            )
            print()

            if first_error_idx != -1:
                print("ERROR EVEN AFTER USING LEMMA. GIVING UP.")
                exit(1)
            else:
                print("PROOF IS VALID")
                with open('proof.v', 'w') as f:
                    f.write(full_coq_code)
        else:
            print("PROOF IS VALID")
