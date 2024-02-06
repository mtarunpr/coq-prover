from datasets import load_dataset
from peft import LoraConfig, PeftModel
import torch
from transformers import AutoModelForCausalLM, BitsAndBytesConfig, AutoTokenizer, TrainingArguments
from trl import AutoModelForCausalLMWithValueHead, PPOConfig, PPOTrainer
from tqdm import tqdm

model_checkpoint = "./phind-fine-tune-baby/checkpoint-250"

base_model_name = "Phind/Phind-CodeLlama-34B-v2"

dataset = load_dataset('json', data_files='dafny-bench.jsonl', split='train')
dataset = dataset.rename_column("prompt", "query")
dataset = dataset.remove_columns(["file", "dafny"])

config = PPOConfig(
    model_name=base_model_name,
    learning_rate=1.41e-5,
    log_with='wandb',
    mini_batch_size=1,
    batch_size=1,
    gradient_accumulation_steps=1,
    early_stopping=False,
    target_kl=6.0,
    kl_penalty="kl",
    seed=0,
    use_score_scaling=False,
    use_score_norm=False,
    score_clip=None,
)

peft_config = LoraConfig(
    lora_alpha=16,
    #lora_dropout=0.1,
    r=16,
    bias="none",
    task_type="CAUSAL_LM",
)

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

model = PeftModel.from_pretrained(base_model, model_checkpoint)

model = AutoModelForCausalLMWithValueHead.from_pretrained(
    model,
    trust_remote_code=True,
    device_map="auto",
    peft_config=peft_config)

def tokenize(sample):
    sample["input_ids"] = tokenizer.encode(sample["query"])
    #sample["query"] = tokenizer.decode(sample["input_ids"])
    return sample

dataset = dataset.map(tokenize, batched=False)
dataset.set_format(type='torch')

def collator(data):
    return dict((key, [d[key] for d in data]) for key in data[0])

ppo_trainer = PPOTrainer(
    model=model,
    config=config,
    dataset=dataset,
    tokenizer=tokenizer,
    data_collator=collator
)

generation_kwargs = {
    "max_new_tokens": 600,
    "min_length": -1,
    "top_k": 0.0,
    "top_p": 1.0,
    "do_sample": True,
    "pad_token_id": tokenizer.eos_token_id,
}

for epoch, batch in tqdm(enumerate(ppo_trainer.dataloader)):
    query_tensors = batch["input_ids"]

    #### Get response from SFTModel
    response_tensors = ppo_trainer.generate(query_tensors, **generation_kwargs)
    batch["response"] = [tokenizer.decode(r.squeeze()) for r in response_tensors]

    #### Compute reward score
    texts = [q + r for q, r in zip(batch["query"], batch["response"])]
    pipe_outputs = reward_model(texts)
    rewards = [torch.tensor(output[1]["score"]) for output in pipe_outputs]

    #### Run PPO step
    stats = ppo_trainer.step(query_tensors, response_tensors, rewards)
    ppo_trainer.log_stats(stats, batch, rewards)

#### Save model
ppo_trainer._save_pretrained("my_ppo_model")