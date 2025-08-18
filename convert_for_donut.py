import os
import json
import shutil
from pathlib import Path
from random import seed

# CONFIG
SOURCE_DIR = Path("~/lemmon-checker/training-data").expanduser()
DEST_ROOT = Path("~/lemmon-checker/donut-data").expanduser()
TRAIN_SPLIT = 0.8  # 80% train, 20% valid

def get_numeric_subfolders(directory):
    # Only accept folder names that are numeric (e.g., 001, 002)
    return sorted([f for f in directory.iterdir() if f.is_dir() and f.name.isdigit()],
                  key=lambda f: int(f.name))

def convert_dataset():
    subfolders = get_numeric_subfolders(SOURCE_DIR)
    total = len(subfolders)
    split_idx = int(total * TRAIN_SPLIT)

    train_dir = DEST_ROOT / "train"
    valid_dir = DEST_ROOT / "valid"
    train_dir.mkdir(parents=True, exist_ok=True)
    valid_dir.mkdir(parents=True, exist_ok=True)

    def process(subset, dest_dir, base_index):
        for offset, folder in enumerate(subset):
            # Accept .jpeg, .jpg, .JPEG, .JPG
            img_path = next(
                (f for ext in [".jpeg", ".jpg", ".JPEG", ".JPG"] if (f := folder / f"proof{ext}").exists()),
                None
            ) 
            json_path = folder / "proof.json"
            if not (img_path.exists() and json_path.exists()):
                print(f"⚠️  Skipping {folder.name}: missing proof.jpeg or proof.json")
                continue

            # Load and wrap JSON
            with open(json_path) as f:
                proof = json.load(f)
            wrapped = {"gt_parse": json.dumps({"proof": proof}, separators=(",", ":"), ensure_ascii=False)}

            out_idx = f"{base_index + offset:03}"
            shutil.copy(img_path, dest_dir / f"{out_idx}.jpg")
            with open(dest_dir / f"{out_idx}.json", "w") as out:
                json.dump(wrapped, out, indent=2)

            print(f"✅ Processed {folder.name} → {out_idx}.jpg/.json")

    print(f"🔄 Converting {total} proof folders...")

    process(subfolders[:split_idx], train_dir, 0)
    process(subfolders[split_idx:], valid_dir, 100)

    print(f"✅ Done. {split_idx} training examples, {total - split_idx} validation examples.")

if __name__ == "__main__":
    convert_dataset()
