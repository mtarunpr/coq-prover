from sentence_transformers import SentenceTransformer
import os

embedding_model = SentenceTransformer("sentence-transformers/all-mpnet-base-v2")
os.environ["TOKENIZERS_PARALLELISM"] = "false"

embed = embedding_model.encode