from transformers import DonutProcessor, VisionEncoderDecoderModel

model_name = "naver-clova-ix/donut-base-finetuned-docvqa"
processor = DonutProcessor.from_pretrained(model_name)
model = VisionEncoderDecoderModel.from_pretrained(model_name)
