"""
Smart Sampling Strategy: From Simple to Complex
Author: Optimization for SE2INV
Purpose: Generate samples starting from simple values to facilitate polynomial fitting
"""

import random
from typing import List, Dict, Tuple, Set
from itertools import product


class SmartSampler:
    """
    智能采样器：从简单值开始，逐步增加复杂度

    采样策略分层：
    1. 特殊值层（0, 1, -1）
    2. 小整数层（2-10）
    3. 中等值层（11-50）
    4. 大数值层（51-100）
    """

    # 分层定义
    SPECIAL_VALUES = [0, 1, -1]
    SMALL_VALUES = list(range(2, 11))  # [2, 3, ..., 10]
    MEDIUM_VALUES = list(range(11, 51))  # [11, 12, ..., 50]
    LARGE_VALUES = list(range(51, 101))  # [51, 52, ..., 100]

    def __init__(self, enable_negative: bool = True, max_samples: int = 20):
        """
        Args:
            enable_negative: 是否包含负数
            max_samples: 最大采样数量
        """
        self.enable_negative = enable_negative
        self.max_samples = max_samples

    def _get_value_tiers(self, min_val: int, max_val: int) -> List[List[int]]:
        """
        根据约束范围，返回分层的值列表

        Args:
            min_val: 最小值约束
            max_val: 最大值约束

        Returns:
            分层的值列表，从简单到复杂
        """
        tiers = []

        # Tier 1: 特殊值（在范围内的）
        special = [v for v in self.SPECIAL_VALUES if min_val <= v <= max_val]
        if special:
            tiers.append(special)

        # Tier 2: 小整数
        small = [v for v in self.SMALL_VALUES if min_val <= v <= max_val]
        if small:
            tiers.append(small)

        # 如果允许负数，添加负的小整数
        if self.enable_negative:
            neg_small = [v for v in [-v for v in self.SMALL_VALUES] if min_val <= v <= max_val]
            if neg_small:
                tiers.append(neg_small)

        # Tier 3: 中等值
        medium = [v for v in self.MEDIUM_VALUES if min_val <= v <= max_val]
        if medium:
            # 从中等值中采样
            sampled_medium = random.sample(medium, min(5, len(medium)))
            tiers.append(sampled_medium)

        # Tier 4: 大数值（如果需要）
        large = [v for v in self.LARGE_VALUES if min_val <= v <= max_val]
        if large:
            sampled_large = random.sample(large, min(3, len(large)))
            tiers.append(sampled_large)

        return tiers

    def generate_samples(self,
                        constraints: Dict[str, Dict[str, int]],
                        num_samples: int = None) -> List[Dict[str, int]]:
        """
        生成从简单到复杂的采样点

        Args:
            constraints: 变量约束字典 {var_name: {'min': ..., 'max': ...}}
            num_samples: 需要的采样数量（默认使用 self.max_samples）

        Returns:
            采样点列表，每个采样点是 {var_name: value}
        """
        if num_samples is None:
            num_samples = self.max_samples

        var_names = list(constraints.keys())
        if not var_names:
            return []

        # 为每个变量生成分层值
        var_tiers = {}
        for var in var_names:
            min_val = constraints[var]['min']
            max_val = constraints[var]['max']
            var_tiers[var] = self._get_value_tiers(min_val, max_val)

        # 策略1: 优先组合低层级（简单值）
        samples = []
        seen = set()

        # Phase 1: 全部使用 Tier 0（特殊值）
        tier_combinations = self._generate_tier_combinations(var_tiers, [0] * len(var_names))
        samples.extend(self._sample_from_combinations(tier_combinations, var_names, seen, num_samples // 3))

        # Phase 2: 混合 Tier 0 和 Tier 1（特殊值 + 小整数）
        if len(samples) < num_samples:
            tier_indices = []
            for var in var_names:
                max_tier = len(var_tiers[var]) - 1
                tier_indices.append(min(1, max_tier))

            tier_combinations = self._generate_tier_combinations(var_tiers, tier_indices)
            samples.extend(self._sample_from_combinations(tier_combinations, var_names, seen, num_samples // 2))

        # Phase 3: 使用所有层级（如果还需要更多样本）
        if len(samples) < num_samples:
            all_tier_combinations = self._generate_all_tier_combinations(var_tiers, var_names)
            samples.extend(self._sample_from_combinations(all_tier_combinations, var_names, seen, num_samples))

        # Phase 4: 如果样本还不够，添加一些随机样本（保持简单优先）
        if len(samples) < num_samples:
            samples.extend(self._generate_random_samples(constraints, var_names, seen, num_samples - len(samples)))

        return samples[:num_samples]

    def _generate_tier_combinations(self,
                                   var_tiers: Dict[str, List[List[int]]],
                                   tier_indices: List[int]) -> List[Tuple[int, ...]]:
        """
        生成指定层级的笛卡尔积组合

        Args:
            var_tiers: 每个变量的分层值
            tier_indices: 每个变量使用的层级索引

        Returns:
            值的组合列表
        """
        var_names = list(var_tiers.keys())
        value_lists = []

        for i, var in enumerate(var_names):
            tier_idx = tier_indices[i]
            if tier_idx < len(var_tiers[var]):
                value_lists.append(var_tiers[var][tier_idx])
            else:
                # 如果超出层级范围，使用最后一层
                value_lists.append(var_tiers[var][-1] if var_tiers[var] else [0])

        # 生成笛卡尔积
        combinations = list(product(*value_lists))
        return combinations

    def _generate_all_tier_combinations(self,
                                       var_tiers: Dict[str, List[List[int]]],
                                       var_names: List[str]) -> List[Tuple[int, ...]]:
        """
        生成所有层级的组合（优先低层级）
        """
        all_combinations = []

        # 计算每个变量的最大层级
        max_tiers = [len(var_tiers[var]) for var in var_names]

        # 按层级和递增顺序生成组合
        for total_tier_sum in range(sum(max_tiers)):
            for tier_indices in product(*[range(mt) for mt in max_tiers]):
                if sum(tier_indices) == total_tier_sum:
                    combinations = self._generate_tier_combinations(var_tiers, list(tier_indices))
                    all_combinations.extend(combinations)

        return all_combinations

    def _sample_from_combinations(self,
                                 combinations: List[Tuple[int, ...]],
                                 var_names: List[str],
                                 seen: Set[Tuple[int, ...]],
                                 max_count: int) -> List[Dict[str, int]]:
        """
        从组合中采样，避免重复
        """
        samples = []

        for combo in combinations:
            if len(samples) >= max_count:
                break

            if combo not in seen:
                seen.add(combo)
                sample = {var_names[i]: combo[i] for i in range(len(var_names))}
                samples.append(sample)

        return samples

    def _generate_random_samples(self,
                                constraints: Dict[str, Dict[str, int]],
                                var_names: List[str],
                                seen: Set[Tuple[int, ...]],
                                count: int) -> List[Dict[str, int]]:
        """
        生成随机样本作为补充（仍然偏向小值）
        """
        samples = []
        attempts = 0
        max_attempts = count * 100

        while len(samples) < count and attempts < max_attempts:
            attempts += 1

            # 使用偏向小值的随机策略
            sample_values = []
            for var in var_names:
                min_val = constraints[var]['min']
                max_val = constraints[var]['max']

                # 80% 概率选择小值范围，20% 概率选择全范围
                if random.random() < 0.8:
                    # 偏向小值
                    small_max = min(max_val, 20)
                    val = random.randint(min_val, small_max)
                else:
                    # 全范围
                    val = random.randint(min_val, max_val)

                sample_values.append(val)

            combo = tuple(sample_values)
            if combo not in seen:
                seen.add(combo)
                sample = {var_names[i]: sample_values[i] for i in range(len(var_names))}
                samples.append(sample)

        return samples


# ================ 使用示例 ================

def demo_smart_sampling():
    """演示智能采样器的使用"""
    sampler = SmartSampler(enable_negative=True, max_samples=20)

    # 示例约束
    constraints = {
        'x': {'min': 0, 'max': 100},
        'y': {'min': 0, 'max': 100}
    }

    samples = sampler.generate_samples(constraints, num_samples=20)

    print("Generated samples (from simple to complex):")
    for i, sample in enumerate(samples, 1):
        print(f"  {i:2d}. {sample}")

    return samples


if __name__ == '__main__':
    demo_smart_sampling()
