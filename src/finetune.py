from datasets import load_dataset
import torch
from transformers import (
    AutoModelForCausalLM,
    BitsAndBytesConfig,
    AutoTokenizer,
    TrainingArguments,
)
from peft import LoraConfig
from trl import SFTTrainer

from datasets import load_dataset

data_dir = "data/datasets"
output_dir = "./checkpoints"

train_dataset = load_dataset(data_dir, split="train")


def formatting_func(example):
    text = f"Given the following context and theorem statement in Coq, generate a proof.\n\n#### Context\n{example['preamble']}\n\n#### Theorem\n{example['theorem']}\n\n#### Proof\nProof.\n{example['proof']}\nQed."
    return [text]


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
base_model.config.use_cache = False

# More info: https://github.com/huggingface/transformers/pull/24906
base_model.config.pretraining_tp = 1

tokenizer = AutoTokenizer.from_pretrained(base_model_name, trust_remote_code=True)
tokenizer.pad_token = tokenizer.eos_token

training_args = TrainingArguments(
    output_dir=output_dir,
    per_device_train_batch_size=4,
    gradient_accumulation_steps=4,
    learning_rate=1e-4,
    logging_steps=50,
    max_steps=500,
    logging_dir="./logs",  # Directory for storing logs
    save_strategy="steps",  # Save the model checkpoint every logging step
    save_steps=50,  # Save checkpoints every 50 steps
    run_name="coq-sft",
    report_to="wandb",
    # evaluation_strategy="steps", # Evaluate the model every logging step
    # eval_steps=50,               # Evaluate and save checkpoints every 50 steps
    # do_eval=True                 # Perform evaluation at the end of training
)

peft_config = LoraConfig(
    lora_alpha=16,
    lora_dropout=0.1,
    r=64,
    bias="none",
    task_type="CAUSAL_LM",
)

max_seq_length = 4096
trainer = SFTTrainer(
    model=base_model,
    train_dataset=train_dataset,
    # eval_dataset=eval_dataset,
    peft_config=peft_config,
    formatting_func=formatting_func,
    max_seq_length=max_seq_length,
    tokenizer=tokenizer,
    args=training_args,
)

# pass in resume_from_checkpoint=True to resume from a checkpoint
trainer.train()
