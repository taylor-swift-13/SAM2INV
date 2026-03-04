import os
from dataclasses import dataclass

# 防止 vllm 导入时调用 dictConfig 导致已有 FileHandler 的 stream 变成 None
os.environ.setdefault("VLLM_CONFIGURE_LOGGING", "0")


@dataclass
class LLMConfig:
    # ── 模式开关 ──────────────────────────────────────────────────────────────
    # True  → 本地推理（vLLM 或 Transformers，由 use_vllm 进一步决定）
    # False → 云端服务商（yunwu.ai / OpenAI 等）
    # 也可通过环境变量 USE_LOCAL=1 / USE_LOCAL=0 控制
    use_local: bool = os.getenv("USE_LOCAL", "0").strip() in {"1", "true", "True", "yes"}

    # ── 云端服务商配置 ────────────────────────────────────────────────────────
    api_model: str = os.getenv("OPENAI_MODEL", "gpt-5-nano")
    api_key: str = os.getenv("OPENAI_API_KEY", "")
    base_url: str = os.getenv("OPENAI_BASE_URL", "https://yunwu.ai/v1")

    # ── 本地推理配置 ──────────────────────────────────────────────────────────
    # use_local=True 时生效；通过 use_vllm 选择后端：
    #   True  → vLLM（高吞吐，推荐多卡）
    #   False → Transformers（单卡或 CPU，无需 vllm 安装）
    # 也可通过环境变量 USE_VLLM=1 / USE_VLLM=0 控制
    use_vllm: bool = os.getenv("USE_VLLM", "1").strip() in {"1", "true", "True", "yes"}
    vllm_model_path: str = os.getenv("VLLM_MODEL_PATH", "")
    vllm_gpu_count: int = int(os.getenv("VLLM_GPU_COUNT", "1"))
    vllm_gpu_mem: float = float(os.getenv("VLLM_GPU_MEM", "0.90"))

    # ── 通用生成参数 ──────────────────────────────────────────────────────────
    api_temperature: float = 1.0
    api_top_p: float = 1.0
    api_max_tokens: int = int(os.getenv("OPENAI_MAX_TOKENS", "16384"))
    think_mode_enabled: bool = False

# 通用输入子目录配置：替代之前写死的 'linear'
SUBDIR = "NLA_lipus"

# ==============================================================================
# Traces 配置 (Execution Traces Configuration)
# ==============================================================================

# 是否启用 traces（执行轨迹）功能
# 设置为 False 时：
#   1. 不触发动态采样（跳过程序执行获取 traces）
#   2. Prompt 中不包含 traces 信息
#   3. 跳过基于 traces 的候选不变式筛选阶段
USE_TRACES = False

# ==============================================================================
# 采样策略配置 (Sampling Strategy Configuration)
# ==============================================================================

# 采样策略选择: 'smart' (智能采样) 或 'random' (随机采样)
# - 'smart': 从简单值开始系统遍历 (推荐，提升拟合成功率)
# - 'random': 完全随机采样 (原始版本)
SAMPLING_STRATEGY = 'smart'  # 可选: 'smart' 或 'random'

# 动态采样配置 (Dynamic Sampling Configuration)
# 每组采样对应一次独立的完整程序执行
DYNAMIC_SAMPLING_CONFIG = {
    'num_groups': 10,              # 采样组数（总共执行次数）
    'num_runs_per_loop': 60,       # 每个循环需要的 run 数量（n）
    'keep_traces_per_run': 3,      # 每个 run 保留的 traces 数量（m，保留前 m 个和后 m 个）
    'ensure_traces_per_loop': True, # 是否确保每个循环都有足够的 traces
}

# 智能采样参数 (仅当 SAMPLING_STRATEGY='smart' 时生效)
SMART_SAMPLING_CONFIG = {
    'enable_negative': True,      # 是否包含负数
    'max_samples': 100,           # 最大采样数量
    'special_values': [0, 1, -1], # 特殊值列表
    'small_range': (2, 10),       # 小整数范围
    'medium_range': (11, 50),     # 中等值范围
    'large_range': (51, 100),     # 大数值范围
}

# 随机采样参数 (仅当 SAMPLING_STRATEGY='random' 时生效)
RANDOM_SAMPLING_CONFIG = {
    'default_min': -100,          # 默认最小值
    'default_max': 100,           # 默认最大值
}

# 调试选项
SAMPLING_DEBUG = False  # 是否输出采样策略调试信息

# ==============================================================================
# 主流程配置 (Main Loop Configuration)
# ==============================================================================

# 主流程最大迭代次数
MAX_ITERATION = 1

# 不变量补强最大迭代次数（用于 syntax/valid 通过但 satisfy 失败时）
MAX_STRENGTHEN_ITERATIONS = 0

# ==============================================================================
# 不变式生成配置 (Invariant Generation Configuration)
# ==============================================================================

# 并行生成配置
PARALLEL_GENERATION_CONFIG = {
    'enabled': True,              # 是否启用并行生成多组候选不变式
    'num_candidates': 3,          # 并行生成的候选组数
    'temperature': 1.0,           # 生成温度，控制多样性
    'filter_by_sampling': True,   # 是否用采样数据过滤候选
    'use_houdini': True,         # 是否使用 Houdini 进一步筛选组合后的不变式
    'detect_conflicts': True,     # 是否检测并去除冲突的不变式
    'use_threading': True,        # 是否使用线程池实现真正的并行生成
    'max_workers': 20,            # API 模型：线程池最大并发数
}

# Prompt 构建配置 (Prompt Construction Configuration)
# 限制 traces 数量以避免 token 超限
PROMPT_CONFIG = {
    'max_samples': 5,              # 最大执行组数（避免 token 超限）
    'max_traces_per_sample': 10,   # 每个执行组最大 traces 数量
}

# 模板生成配置
# simplified=True: 使用简化模板（默认）
# simplified=False: 使用复杂模板（结合 var_maps/path_conds/updated_loop_conditions）
TEMPLATE_CONFIG = {
    'simplified': True,
}

# Invariant dedup configuration
# enabled=True: split top-level && invariants and deduplicate by text ignoring whitespace.
# enabled=False: keep Houdini output as-is.
INVARIANT_DEDUP_CONFIG = {
    'enabled': True,
}

# ==============================================================================
# Filter Configuration (Invariant Filtering)
# ==============================================================================

# 语法过滤配置 (Syntax Filter Configuration)
SYNTAX_FILTER_CONFIG = {
    'enabled': True,          # 是否启用语法过滤（基于 unified_filter.py）
    'verbose': True     # 是否输出详细的过滤日志
}

# Filter is always enabled and uses variables from symbolic execution record
# Variables are extracted from record dynamically


# ==============================================================================
# Loop Factory User Config (for loop_factory/batch_pipeline.py)
# ==============================================================================
# 用户可在此统一调节 batch pipeline 与 loop_factory 复杂度参数。
LOOP_FACTORY_USER_CONFIG = {
    # batch pipeline runtime
    'target_count': 100,
    'max_attempts': 100,
    'seed': 198964,
    'workers': 20,
    'max_skeleton_repeat': 4,
    'append': True,
    'work_dir': '',

    # loop_factory complexity knobs (shared names with loop_factory.py)
    'max_vars': 2,
    'min_vars': 1,      
    'max_params': 2,       
    'min_params': 0,       
    'min_loops': 1,
    'max_loops': 1,
    'max_assign': 3,
    'min_assign': 2,        
    'max_ifelse': 0,
    'min_ifelse': 0,        
    'max_depth': 1,
    'p_multi': 0.0,
    'q_nest': 0.0,
    'p_nonlinear': 1.00,
    'p_semantic_core': 0.80,
    # 允许生成的模板白名单（支持“语义模板名”或“core名”）。
    # 空列表表示不做限制（即全集）。
    # 示例:
    #   ['L1_affine_accumulator', 'L4_conservation']
    #   ['affine_chain', 'linear_conservation_family']
    'allowed_templates': [],
}


# ==============================================================================
# vLLM Engine Bootstrap (for src/scripts/vllm_warmup.py)
# ==============================================================================
# 配置在进程内直接加载的 vLLM 引擎参数，无需启动 HTTP 服务。
VLLM_ENGINE_CONFIG = {
    # 必填：本地模型路径（HuggingFace 格式）。
    'model_path': '',
    # 推理使用的 GPU 数量（tensor parallel）。
    'gpu_count': 1,
    # GPU 显存利用率（0~1）。
    'gpu_mem': 0.90,
}





   
