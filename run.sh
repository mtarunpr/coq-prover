#!/usr/bin/bash

CUDA_VISIBLE_DEVICES="1,2,3" TOKENIZERS_PARALLELISM=false python src/finetune.py > train.log
