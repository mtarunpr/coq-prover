# Coq Prover

## Setup

First create a `.env` file in the root directory containing your OpenAI API key:

```bash
OPENAI_API_KEY="sk-xxxx"
```

Also install the Python dependencies:

```bash
pip install -r requirements.txt
```

## Usage

To run the prover on an existing example, run the following command from the root directory:

```bash
python src/prover.py -e <example>
```

To prove a custom theorem, create a new directory in `examples/` and add a `context.v` file containing any required context (imports, definitions, lemmas, etc.) and a `theorem.v` file containing the statement of the theorem to prove. Then run the prover on this new example.
