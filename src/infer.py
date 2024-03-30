# Caching process ported from https://github.com/metareflection/gpt-call
# LocalModel inference ported from https://github.com/metareflection/llm-scripts

import torch
from transformers import (
    AutoModelForCausalLM,
    BitsAndBytesConfig,
    AutoTokenizer,
    TextStreamer,
)
import csv
from peft import PeftModel
from tenacity import retry, stop_after_attempt, wait_random_exponential
from joblib import Memory
from openai import OpenAI
from openai.types.chat import ChatCompletionMessageParam
from typing import Iterable, Union
from coq import Theorem
import os
import re

os.environ["TOKENIZERS_PARALLELISM"] = "false"

memory = Memory("cachegpt", verbose=0)
client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))


class BaseLLM:
    def ask(self, messages: Iterable[ChatCompletionMessageParam]):
        raise NotImplementedError

    def ask_for_proof(self, theorem: Theorem, prev_attempt_error_msg=None):
        """
        Attempts to prove a theorem using GPT-4. Stores the resulting proof in theorem.proof.
        """
        messages = [
            {
                "role": "system",
                "content": "You are an automated theorem prover that can prove theorems and lemmas in Coq. Your entire response must be valid Coq code. You should explain your reasoning (what the proof steps are attempting to do), but only in comments inside the Coq code. The following messages will all consist of a theorem statement (possibly preceded by necessary definitions, imports, etc.), and your response must be a valid Coq proof of that theorem. Your response must be in this format: ```coq\n Proof.\n<proof>. Qed.\n```. Remember: do not add any other text besides Coq code and do not repeat any imports, definitions, lemmas, etc. provided in the prompt.",
            },
            {
                "role": "user",
                "content": "#### CONTEXT\n\n"
                + theorem.get_preamble_string()
                + "\n\n#### THEOREM TO BE PROVEN\n\n"
                + str(theorem),
            },
        ]
        if prev_attempt_error_msg is not None:
            messages += [
                {
                    "role": "assistant",
                    "content": "```coq" + theorem.get_proof_string() + "\n```",
                },
                {
                    "role": "user",
                    "content": "This is incorrect; Coq produced the following error message: "
                    + prev_attempt_error_msg
                    + "\n\nPlease try again.",
                },
            ]
        response = self.ask(messages)
        proof_contents = response.split("Proof.")[1].split("Qed.")[0]
        proof_str = "Proof.\n" + proof_contents + "\nQed."
        theorem.proof = re.findall(r"(.+?\.)(?:\s+|$)", proof_str, flags=re.DOTALL)

    def create_lemma_name(self, lemma_str: str, suffix: str):
        messages = [
            {
                "role": "system",
                "content": "You are a proof helper for Coq that can come up with descriptive names for lemmas and theorems based on the statement of the proposition. Specifically, Replace `helper_lemma` with a better, more descriptive, name for the following lemma(s) in Coq. Your entire response must be valid Coq code. Your response must be in this format: ```coq\nLemma <new_lemma_name> : <lemma_statement>.\n```.",
            },
            {"role": "user", "content": lemma_str},
        ]
        response = self.ask(messages)
        new_lemma_name = response.split("Lemma ")[1].split(":")[0].strip()
        return new_lemma_name + "_" + suffix


class GPT(BaseLLM):
    def __init__(self, model_name: str):
        self.ask = memory.cache(self.ask)
        self.model_name = model_name

    @retry(wait=wait_random_exponential(min=10, max=30), stop=stop_after_attempt(25))
    def _generate(self, messages):
        print("Prompting GPT... model_name=" + self.model_name)
        return client.chat.completions.create(model=self.model_name, messages=messages)

    def ask(self, messages: Iterable[ChatCompletionMessageParam]):
        response = self._generate(messages)
        return response.choices[0].message.content


class LocalModel(BaseLLM):
    def __init__(self, model_name: str, model_checkpoint: Union[str, None] = None):
        # self.ask = memory.cache(self.ask)
        self.model_checkpoint = model_checkpoint
        self.base_model_name = model_name
        bnb_config = BitsAndBytesConfig(
            load_in_4bit=True,
            bnb_4bit_quant_type="nf4",
            bnb_4bit_compute_dtype=torch.float16,
        )
        base_model = AutoModelForCausalLM.from_pretrained(
            self.base_model_name,
            quantization_config=bnb_config,
            device_map="auto",
            trust_remote_code=True,
            use_auth_token=True,
        )

        self.tokenizer = AutoTokenizer.from_pretrained(
            self.base_model_name, trust_remote_code=True
        )
        self.tokenizer.pad_token = self.tokenizer.eos_token

        if self.model_checkpoint is None:
            self.model = base_model
        else:
            self.model = PeftModel.from_pretrained(base_model, self.model_checkpoint)

        self.streamer = TextStreamer(self.tokenizer)

    def _generate(self, prompt):
        print(
            "Prompting LocalMode... model_name="
            + self.model_name
            + (" model_checkpoint=" + self.model_checkpoint)
            if self.model_checkpoint is not None
            else ""
        )

        model_input = self.tokenizer(prompt, return_tensors="pt").to("cuda")

        self.model.eval()

        r = None
        with torch.no_grad():
            r = self.tokenizer.decode(
                self.model.generate(
                    **model_input,
                    max_new_tokens=1000,
                    pad_token_id=self.tokenizer.eos_token_id,
                )[0],
                skip_special_tokens=True,
            )
        return r

    def ask(self, messages: Iterable[ChatCompletionMessageParam]):
        prompt = ""
        for message in messages:
            if message["role"] == "system":
                prompt += "### System Prompt\n" + message["content"] + "\n\n"
            elif message["role"] == "user":
                prompt += "### User Message\n" + message["content"] + "\n\n"
            elif message["role"] == "assistant":
                prompt += "### Assistant\n" + message["content"] + "\n\n"
            else:
                raise ValueError("Invalid message role: " + message["role"])
        prompt += "### Assistant\n"
        return self._generate(prompt).split("### Assistant\n")[-1]


if __name__ == "__main__":
    with open("data/datasets/software_foundations.csv", "r") as file:
        reader = csv.DictReader(file)
        for example in reader:
            prompt = f"Given the following context and theorem statement in Coq, generate a proof.\n\n#### Context\n{example['preamble']}\n\n#### Theorem\n{example['theorem']}\n\n#### Proof\n"
            llm = LocalModel(
                "Phind/Phind-CodeLlama-34B-v2",
            )
            print(llm._generate(prompt))
            break
