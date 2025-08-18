import os
import json
from PIL import Image
from datasets import Dataset
from transformers import DonutProcessor, VisionEncoderDecoderModel, Seq2SeqTrainer, Seq2SeqTrainingArguments
import torch

# Set these paths
TRAIN_DIR = "train"
MODEL_NAME = "naver-clova-ix/donut-base"
OUTPUT_DIR = "donut-proof-model"

# Load processor and model
processor = DonutProcessor.from_pretrained(MODEL_NAME)
model = VisionEncoderDecoderModel.from_pretrained(MODEL_NAME)

# Freeze encoder (optional — speeds up training with small datasets)
model.encoder.requires_grad_(False)

# Prepare training data
def load_data():
    data = []
    for fname in sorted(os.listdir(TRAIN_DIR)):
        if fname.lower().endswith(".jpg"):
            img_path = os.path.join(TRAIN_DIR, fname)
            json_path = os.path.splitext(img_path)[0] + ".json"
            if os.path.exists(json_path):
                with open(json_path, "r") as f:
                    target_str = json.dumps(json.load(f), separators=(",", ":"))
                data.append({"image_path": img_path, "label": target_str})
    return data

raw_data = load_data()
dataset = Dataset.from_list(raw_data)

# Preprocess for Donut
def preprocess(example):
    image = Image.open(example["image_path"]).convert("RGB")
    pixel_values = processor(image, return_tensors="pt").pixel_values[0]
    input_ids = processor.tokenizer(
        example["label"],
        add_special_tokens=True,
        padding="max_length",
        truncation=True,
        max_length=768,
        return_tensors="pt"
    ).input_ids[0]
    return {"pixel_values": pixel_values, "labels": input_ids}

processed_dataset = dataset.map(preprocess, remove_columns=["label", "image_path"])

# Set format for PyTorch
processed_dataset.set_format(type="torch")

# Training args
training_args = Seq2SeqTrainingArguments(
    output_dir=OUTPUT_DIR,
    per_device_train_batch_size=2,
    num_train_epochs=10,
    logging_dir="./logs",
    logging_steps=1,
    save_strategy="epoch",
    save_total_limit=2,
    predict_with_generate=True,
    fp16=torch.cuda.is_available(),  # mixed precision if GPU
)

# Trainer
trainer = Seq2SeqTrainer(
    model=model,
    args=training_args,
    train_dataset=processed_dataset,
    tokenizer=processor.tokenizer,
)

# Fine-tune
trainer.train()

# Save model and processor
model.save_pretrained(OUTPUT_DIR)
processor.save_pretrained(OUTPUT_DIR)
