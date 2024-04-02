# Guided Proof Search Using Large Language Models and Lemma Extraction in Coq

## Setup

First, install the Python dependencies:

```bash
pip install -r requirements.txt
```

If you'd like to use an OpenAI model, create a `.env` file in the root directory containing your OpenAI API key:

```bash
OPENAI_API_KEY="sk-xxxx"
```

To control the language model used, the maximum depth, or the module name, change the relevant settings in `src/lemma_prover.py`.

## Usage

To run the prover on all theorems in a Coq project in `data/raw/`, run

```bash
python src/lemma_prover.py -p <project>
```

To run the prover on a single theorem, run

```bash
python src/lemma_prover.py -e <example>
``` 

To prove a custom theorem, create a new directory in `data/raw/lemma_examples/` and add a `context.v` file containing any required context (imports, definitions, lemmas, etc.) and a `theorem.v` file containing the statement of the theorem to prove. Then run the prover on this new example.
