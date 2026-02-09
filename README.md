# SAM2INV - Automatic Loop Invariant Generator

[![Python](https://img.shields.io/badge/Python-3.8+-blue.svg)](https://www.python.org/)
[![License](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)

**SAM2INV** (Sample to Invariant) is an automatic loop invariant generation tool that leverages Large Language Models (LLMs) with parallel generation, diverse prompts, and smart sampling strategies to automatically generate ACSL (ANSI/ISO C Specification Language) invariant annotations for loops in C programs.

## Key Features

- **Parallel Generation**: Multi-threaded parallel generation of multiple candidate invariants (default: 20)
- **Diverse Prompts**: Multiple prompt templates with random selection for generation diversity
- **Multi-Model Support**: Supports multiple LLM models with random selection (gpt-4o, deepseek-v3.1, gpt-5)
- **Smart Sampling**: Starts from simple values to improve data quality
- **Vector Cache**: Caches solutions to similar problems to accelerate generation
- **Iterative Repair**: Automatically repairs invariants that fail verification
- **Trace-Based Filtering**: Uses execution traces to validate invariant correctness
- **Houdini Pruning**: Automatically removes redundant invariants

## Quick Start

### Installation

```bash
# Install Python dependencies
pip3 install z3-solver numpy chromadb sentence-transformers openai pyyaml

# Install Frama-C (for verification)
# Ubuntu/Debian:
sudo apt-get install frama-c

# macOS:
brew install frama-c
```

### Basic Usage

```bash
cd src
python3 loop_inv.py <file_name> [options]
```

**Examples:**

```bash
# Process NLA_lipus/1.c
python3 loop_inv.py 1 --input-subdir NLA_lipus

# Specify output directory and max iterations
python3 loop_inv.py 1 --input-subdir NLA_lipus --output-dir custom_output --max-iterations 10
```

### Command-Line Arguments

```
python3 loop_inv.py <file_name> [options]

Required:
  file_name              File name (without extension)

Optional:
  --input-subdir SUBDIR  Input subdirectory (default: NLA_lipus)
  --output-dir DIR       Output directory (default: auto-generated from config)
  --log-dir DIR          Log directory (default: auto-aligned with input path)
  --max-iterations N     Max iterative repair attempts (default: 5)
```

## Project Structure

```
SAM2INV/
├── README.md
├── src/
│   ├── loop_inv.py              # Main entry point
│   ├── config.py                # Configuration
│   ├── inv_generator.py         # Invariant generator (core)
│   ├── loop_sampler.py          # Loop sampler
│   ├── llmfit.py                # LLM invariant generation
│   ├── llm.py                   # LLM API wrapper
│   ├── output_verify.py         # Frama-C verifier
│   ├── vector_cache_manager.py  # Vector cache manager
│   ├── houdini_pruner.py        # Houdini pruner
│   ├── prompts/                 # Prompt templates
│   ├── input/                   # Input test cases
│   ├── output/                  # Output files
│   ├── log/                     # Logs
│   └── vector_cache_db/         # Vector cache database
└── VST/                         # VST verification goals
```

## Configuration

Core configuration is in `src/config.py`.

### LLM Settings

```python
@dataclass
class LLMConfig:
    use_api_model = True
    api_model = "gpt-4o-mini"  # Options: gpt-4o, deepseek-v3.1, gpt-5
    api_key = "your-api-key"
    base_url = "https://yunwu.ai/v1"
    api_temperature = 1.0
```

### Sampling Settings

```python
# Strategy: 'smart' (recommended) or 'random'
SAMPLING_STRATEGY = 'smart'

DYNAMIC_SAMPLING_CONFIG = {
    'num_groups': 10,
    'num_runs_per_loop': 10,
    'keep_traces_per_run': 3,
    'ensure_traces_per_loop': True,
}

SMART_SAMPLING_CONFIG = {
    'enable_negative': True,
    'max_samples': 100,
    'special_values': [0, 1, -1],
    'small_range': (2, 10),
    'medium_range': (11, 50),
    'large_range': (51, 100),
}
```

### Parallel Generation Settings

```python
PARALLEL_GENERATION_CONFIG = {
    'enabled': True,
    'num_candidates': 20,
    'temperature': 0.9,
    'filter_by_sampling': True,
    'use_houdini': True,
    'use_threading': True,
    'max_workers': 5,
}

PARALLEL_DIVERSITY_CONFIG = {
    'random_prompt': True,
    'random_model': False,
    'available_models': ['gpt-4o', 'deepseek-v3.1', 'gpt-5'],
}
```

## How It Works

```
Input C code
    |
Dynamic Sampling (collect execution traces)
    |
Vector Cache Lookup (similar problems)
    |
+-------------------------+
|  Parallel Generation    |
|  - Multi-threaded       | <-- 20 candidates by default
|  - Random prompts       | <-- Increase diversity
|  - Random model (opt.)  | <-- gpt-4o / deepseek-v3.1 / gpt-5
+-------------------------+
    |
Trace-Based Filtering
    |
Houdini Pruning
    |
Frama-C Verification
    |
+-------------------------+
|  Failed?                |
|  -> Iterative Repair    |
+-------------------------+
    |
Output annotated code
```

### Smart Sampling Strategy

Collects high-quality execution traces by sampling from simple values first:

```
Tier 0: [0, 1, -1]              # Special values
Tier 1: [2, 3, ..., 10]         # Small values
Tier 2: [11, 12, ..., 50]       # Medium values
Tier 3: [51, 52, ..., 100]      # Large values
```

### Vector Cache System

Caches solutions to similar problems using:
- Vector database: ChromaDB
- Embedding model: Sentence Transformers (all-MiniLM-L6-v2)
- Similarity search: Cosine similarity

### Prompt Template System

The system supports multiple prompt templates for generation diversity:

- `minimal.txt` — Code only with basic instructions (~8 lines)
- `simple.txt` — Core task + placeholders + output format (~15 lines)
- `standard.txt` — Default prompt with role, conditions, and boundary hints (~40 lines)
- `detailed.txt` — Full analysis, patterns, and error warnings (~90 lines)
- `experiment.txt` — Special rules and ACSL syntax constraints (~50 lines)

**Placeholders:** `{{content}}` for code template, `{{pre_cond}}` for loop context.

To add a custom prompt, create a `.txt` file in `src/prompts/` using the placeholders above. The system loads all templates automatically.

## Example

**Input** (`input/NLA_lipus/1.c`):
```c
/*@ requires a>=n && n==0;*/
int main1(int a,int n){
  int x,y,z;
  x=0; y=1; z=6;
  while(n<=a){
       n=n+1; x=x+y; y=y+z; z=z+6;
  }
  /*@ assert (n==a+1) && (y == 3*n*n + 3*n + 1) && (x == n*n*n) && (z == 6*n + 6);*/
}
```

**Run:**
```bash
python3 loop_inv.py 1 --input-subdir NLA_lipus
```

**Output** (`output/NLA_lipus/1.c`):
```c
/*@ requires a>=n && n==0;*/
int main1(int a,int n){
  int x,y,z;
  x=0; y=1; z=6;

  /*@
    loop invariant n >= 0;
    loop invariant n <= a + 1;
    loop invariant y == 3 * n * n + 3 * n + 1;
    loop invariant x == n * n * n;
    loop invariant z == 6 * n + 6;
    loop assigns n, x, y, z;
  */
  while(n<=a){
       n=n+1; x=x+y; y=y+z; z=z+6;
  }
  /*@ assert (n==a+1) && (y == 3*n*n + 3*n + 1) && (x == n*n*n) && (z == 6*n + 6);*/
}
```

## Batch Processing

```bash
for i in {1..10}; do
    python3 loop_inv.py $i --input-subdir NLA_lipus
done
```

## License

MIT
