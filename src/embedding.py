from sentence_transformers import SentenceTransformer
import os
import torch
from typing import Union

embedding_model = SentenceTransformer("sentence-transformers/all-mpnet-base-v2")
os.environ["TOKENIZERS_PARALLELISM"] = "false"


def embed(sentences: Union[str, list[str]]) -> torch.Tensor:
    """
    Given a sentence or list of sentences, returns an embedding of each tensor
    (stacked into a single tensor if multiple sentences are given)
    """
    return embedding_model.encode(
        sentences, convert_to_numpy=False, convert_to_tensor=True
    )
