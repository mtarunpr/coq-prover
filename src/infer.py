import torch
from transformers import (
    AutoModelForCausalLM,
    BitsAndBytesConfig,
    AutoTokenizer,
    TextStreamer,
)
import csv
import random

# model_checkpoint = "./phind-fine-tune-baby/checkpoint-250"

base_model_name = "Phind/Phind-CodeLlama-34B-v2"
bnb_config = BitsAndBytesConfig(
    load_in_4bit=True,
    bnb_4bit_quant_type="nf4",
    bnb_4bit_compute_dtype=torch.float16,
)
base_model = AutoModelForCausalLM.from_pretrained(
    base_model_name,
    quantization_config=bnb_config,
    device_map="auto",
    trust_remote_code=True,
    use_auth_token=True,
)

tokenizer = AutoTokenizer.from_pretrained(base_model_name, trust_remote_code=True)
tokenizer.pad_token = tokenizer.eos_token

streamer = TextStreamer(tokenizer)

model = base_model


def generate(eval_prompt):
    model_input = tokenizer(eval_prompt, return_tensors="pt").to("cuda")

    model.eval()

    r = None
    with torch.no_grad():
        r = tokenizer.decode(
            model.generate(**model_input, streamer=streamer, max_new_tokens=500)[0],
            skip_special_tokens=True,
        )
        print(r)
    return r


if __name__ == "__main__":
    with open("data/datasets/software_foundations.csv", "r") as file:
        reader = csv.DictReader(file)
        for example in reader:
            # if example["file_name"] != 'Logic.v':
            #     continue
            # if random.random() < 0.9:
            #     continue
            prompt = f"Given the following context and theorem statement in Coq, generate a proof.\n\n#### Context\n{example['preamble']}\n\n#### Theorem\n{example['theorem']}\n\n#### Proof\n"
            generate(prompt)
            break
