# JAIDE v40 — Training on Modal B200 GPUs

## Quick Start

### 1. Setup Modal (one time)
```bash
cd jaide/src/scripts
bash modal_setup.sh
```

### 2. Start Training
```bash
cd jaide/src/scripts
modal run modal_train.py
```

Default config: 50 epochs, 128 batch size, dim=512, 8 RSF layers, 8x B200 GPUs.

### 3. Custom Parameters
```bash
modal run modal_train.py \
  --epochs 100 \
  --batch-size 256 \
  --dim 1024 \
  --layers 16 \
  --learning-rate 0.0003 \
  --sample-limit 100000
```

### 4. Run Inference After Training
```bash
modal run modal_inference.py --prompt "Your prompt here"
```

### 5. List Saved Models
```bash
modal run modal_train.py::list_models
```

## What Happens When You Run Training

1. Modal builds a CUDA 12.4 + Zig 0.13.0 + Futhark image
2. Your JAIDE source is uploaded to the container
3. `futhark_kernels.fut` is compiled to C
4. `distributed_trainer_futhark.zig` is compiled against the RSF architecture
5. `HuggingFaceFW/finephrase` dataset is downloaded (already built in)
6. Training runs on 8x NVIDIA B200 GPUs with NCCL allReduce
7. Model checkpoints saved to the `jaide-training-data` Modal volume
8. Training logs saved alongside checkpoints as JSON

## Architecture Summary

- **RSF layers** — Reversible Scatter Flow (bijective coupling, O(1) memory backprop)
- **MGT tokenizer** — Morpheme-Guided Tokenization
- **SFD optimizer** — Stochastic Fractal Descent
- **Futhark GPU kernels** — data-parallel GPU acceleration
- **NCCL allReduce** — multi-GPU gradient synchronization

## Files

| File | Purpose |
|------|---------|
| `src/scripts/modal_train.py` | Main training script for Modal |
| `src/scripts/modal_inference.py` | Inference script for Modal |
| `src/scripts/modal_setup.sh` | One-time Modal setup |
| `src/distributed/distributed_trainer_futhark.zig` | Core trainer (Zig) |
| `src/hw/accel/futhark_kernels.fut` | GPU kernels (Futhark) |
| `src/processor/rsf.zig` | RSF architecture |
| `src/tokenizer/mgt.zig` | MGT tokenizer |
| `src/optimizer/sfd.zig` | SFD optimizer |
