# Coq Prover

## Setup

First create a `.env` file in the root directory containing your OpenAI API key:

```bash
OPENAI_API_KEY="sk-xxxx"
```

Also create a `theorem.v` file containing the statement of the theorem you want to prove, along with any other Coq definitions that may be needed:

```bash
echo "Theorem thm1 : forall (n : nat), n + 0 = n." > theorem.txt
```

Lastly, install the Python dependencies:

```bash
pip install -r requirements.txt
```

## Usage

```bash
python prover.py
```