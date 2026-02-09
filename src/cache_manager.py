#!/usr/bin/env python3
"""
Vector Cache 管理脚本
支持查看、添加、删除 cache 条目

用法:
    python3 cache_manager.py list                    # 列出所有 cache 条目
    python3 cache_manager.py show <id>               # 显示特定条目详情
    python3 cache_manager.py stats                   # 显示统计信息
    python3 cache_manager.py add <json_file>          # 从 JSON 文件添加条目
    python3 cache_manager.py delete <id>             # 删除指定 ID 的条目
    python3 cache_manager.py delete-multiple <id1> <id2> ...  # 批量删除
    python3 cache_manager.py clear                   # 清空所有 cache
    python3 cache_manager.py search <query>         # 搜索相似问题
"""

import argparse
import json
import sys
import os
from pathlib import Path
from typing import Dict, List, Any, Optional
from datetime import datetime

# 添加当前目录到路径
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from vector_cache_manager import VectorCacheManager, CacheEntry
import logging

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


class CacheManagerCLI:
    """Cache 管理命令行接口"""
    
    def __init__(self, config_path: Optional[str] = None):
        """初始化 Cache Manager"""
        # config_path 参数已废弃，现在从 config.py 读取配置
        self.cache_manager = VectorCacheManager(logger=logger)
        
        if not self.cache_manager.enabled:
            logger.error("Vector cache is not enabled.")
            logger.error("Possible reasons:")
            logger.error("  1. Cache is disabled in config.py (set CACHE_CONFIG['enabled'] = True)")
            logger.error("  2. Missing dependencies (sentence-transformers, chromadb)")
            logger.error("  3. Configuration error in config.py")
            sys.exit(1)
    
    def list_all(self, limit: int = None, show_details: bool = False):
        """列出所有 cache 条目"""
        try:
            if not hasattr(self.cache_manager, 'collection'):
                logger.error("ChromaDB collection not available")
                return
            
            # 获取所有条目
            # ChromaDB 没有直接的 get_all 方法，需要使用 query 或 peek
            try:
                # 尝试使用 peek 获取前 N 个条目
                if limit:
                    results = self.cache_manager.collection.peek(limit=limit)
                else:
                    # 获取所有条目（先获取总数）
                    count = self.cache_manager.collection.count()
                    results = self.cache_manager.collection.peek(limit=count)
            except Exception as e:
                logger.error(f"Failed to retrieve entries: {e}")
                return
            
            if not results or not results.get('ids'):
                print("Cache is empty")
                return
            
            ids = results['ids']
            metadatas = results.get('metadatas', [])
            documents = results.get('documents', [])
            
            print(f"\n{'='*80}")
            print(f"Cache Entries (Total: {len(ids)})")
            print(f"{'='*80}\n")
            
            for i, (entry_id, metadata, document) in enumerate(zip(ids, metadatas, documents), 1):
                print(f"[{i}] ID: {entry_id[:16]}...")
                
                if metadata:
                    timestamp = metadata.get('timestamp', 0)
                    loop_idx = metadata.get('loop_idx', 'N/A')
                    
                    # 解析 invariants 和 verification results
                    solution_invariants = metadata.get('solution_invariants', '[]')
                    verification_results = metadata.get('verification_results', '{}')
                    
                    try:
                        if isinstance(solution_invariants, str):
                            solution_invariants = json.loads(solution_invariants)
                        if isinstance(verification_results, str):
                            verification_results = json.loads(verification_results)
                    except:
                        pass
                    
                    print(f"    Loop Index: {loop_idx}")
                    print(f"    Timestamp: {datetime.fromtimestamp(timestamp).strftime('%Y-%m-%d %H:%M:%S') if timestamp else 'N/A'}")
                    print(f"    Invariants: {len(solution_invariants) if isinstance(solution_invariants, list) else 'N/A'}")
                    
                    if show_details:
                        print(f"    Problem Text: {document[:200]}...")
                        if isinstance(solution_invariants, list) and solution_invariants:
                            print(f"    Invariants Preview:")
                            for inv in solution_invariants[:3]:
                                print(f"      - {inv[:80]}...")
                
                print()
            
            print(f"{'='*80}\n")
            
        except Exception as e:
            logger.error(f"Error listing cache entries: {e}")
            import traceback
            traceback.print_exc()
    
    def show_entry(self, entry_id: str):
        """显示特定条目的详细信息"""
        try:
            if not hasattr(self.cache_manager, 'collection'):
                logger.error("ChromaDB collection not available")
                return
            
            # 获取指定 ID 的条目
            try:
                results = self.cache_manager.collection.get(ids=[entry_id])
            except Exception as e:
                logger.error(f"Entry not found: {e}")
                return
            
            if not results['ids']:
                print(f"Entry '{entry_id}' not found")
                return
            
            entry_id = results['ids'][0]
            metadata = results['metadatas'][0] if results['metadatas'] else {}
            document = results['documents'][0] if results['documents'] else ''
            
            print(f"\n{'='*80}")
            print(f"Cache Entry Details")
            print(f"{'='*80}\n")
            print(f"ID: {entry_id}\n")
            
            # 基本信息
            timestamp = metadata.get('timestamp', 0)
            loop_idx = metadata.get('loop_idx', 'N/A')

            print(f"Loop Index: {loop_idx}")
            print(f"Timestamp: {datetime.fromtimestamp(timestamp).strftime('%Y-%m-%d %H:%M:%S') if timestamp else 'N/A'}\n")
            
            # 问题文本
            print(f"Problem Text:")
            print(f"{'-'*80}")
            print(document)
            print(f"{'-'*80}\n")
            
            # 解决方案代码
            solution_code = metadata.get('solution_code', '')
            if solution_code:
                print(f"Solution Code:")
                print(f"{'-'*80}")
                print(solution_code[:1000])  # 限制长度
                if len(solution_code) > 1000:
                    print(f"... (truncated, total length: {len(solution_code)})")
                print(f"{'-'*80}\n")
            
            # 不变量
            solution_invariants = metadata.get('solution_invariants', '[]')
            try:
                if isinstance(solution_invariants, str):
                    solution_invariants = json.loads(solution_invariants)
            except:
                solution_invariants = []
            
            if isinstance(solution_invariants, list) and solution_invariants:
                print(f"Solution Invariants ({len(solution_invariants)}):")
                print(f"{'-'*80}")
                for i, inv in enumerate(solution_invariants, 1):
                    print(f"  [{i}] {inv}")
                print(f"{'-'*80}\n")
            
            # 验证结果
            verification_results = metadata.get('verification_results', '{}')
            try:
                if isinstance(verification_results, str):
                    verification_results = json.loads(verification_results)
            except:
                verification_results = {}
            
            if isinstance(verification_results, dict) and verification_results:
                print(f"Verification Results:")
                print(f"{'-'*80}")
                print(json.dumps(verification_results, indent=2, ensure_ascii=False))
                print(f"{'-'*80}\n")
            
            # 特征
            features = metadata.get('features', '{}')
            try:
                if isinstance(features, str):
                    features = json.loads(features)
            except:
                features = {}
            
            if isinstance(features, dict) and features:
                print(f"Problem Features:")
                print(f"{'-'*80}")
                print(json.dumps(features, indent=2, ensure_ascii=False))
                print(f"{'-'*80}\n")
            
            print(f"{'='*80}\n")
            
        except Exception as e:
            logger.error(f"Error showing entry: {e}")
            import traceback
            traceback.print_exc()
    
    def show_stats(self):
        """显示统计信息"""
        try:
            stats = self.cache_manager.get_cache_stats()
            
            print(f"\n{'='*80}")
            print(f"Cache Statistics")
            print(f"{'='*80}\n")
            
            print(f"Database Type: {stats.get('database_type', 'N/A')}")
            print(f"Total Entries: {stats.get('total_entries', 0)}")
            
            if 'error' in stats:
                print(f"Error: {stats['error']}")
            
            print(f"\n{'='*80}\n")
            
        except Exception as e:
            logger.error(f"Error getting stats: {e}")
            import traceback
            traceback.print_exc()
    
    def add_entry(self, json_file: str):
        """从 JSON 文件添加条目"""
        try:
            with open(json_file, 'r', encoding='utf-8') as f:
                data = json.load(f)
            
            # 验证必需字段
            required_fields = ['record', 'loop_idx', 'solution_code', 'solution_invariants']
            for field in required_fields:
                if field not in data:
                    logger.error(f"Missing required field: {field}")
                    return
            
            record = data['record']
            loop_idx = data['loop_idx']
            solution_code = data['solution_code']
            solution_invariants = data['solution_invariants']
            verification_results = data.get('verification_results', {})
            
            # 存储到 cache
            self.cache_manager.store_problem_solution(
                record=record,
                loop_idx=loop_idx,
                solution_code=solution_code,
                solution_invariants=solution_invariants,
                verification_results=verification_results
            )
            
            print(f"✓ Successfully added entry to cache")
            
        except FileNotFoundError:
            logger.error(f"File not found: {json_file}")
        except json.JSONDecodeError as e:
            logger.error(f"Invalid JSON file: {e}")
        except Exception as e:
            logger.error(f"Error adding entry: {e}")
            import traceback
            traceback.print_exc()
    
    def delete_entry(self, entry_id: str):
        """删除指定条目"""
        try:
            if not hasattr(self.cache_manager, 'collection'):
                logger.error("ChromaDB collection not available")
                return
            
            # 检查条目是否存在
            try:
                results = self.cache_manager.collection.get(ids=[entry_id])
                if not results['ids']:
                    print(f"Entry '{entry_id}' not found")
                    return
            except:
                print(f"Entry '{entry_id}' not found")
                return
            
            # 删除条目
            self.cache_manager.collection.delete(ids=[entry_id])
            print(f"✓ Successfully deleted entry: {entry_id}")
            
        except Exception as e:
            logger.error(f"Error deleting entry: {e}")
            import traceback
            traceback.print_exc()
    
    def delete_multiple(self, entry_ids: List[str]):
        """批量删除条目"""
        try:
            if not hasattr(self.cache_manager, 'collection'):
                logger.error("ChromaDB collection not available")
                return
            
            # 检查哪些条目存在
            existing_ids = []
            for entry_id in entry_ids:
                try:
                    results = self.cache_manager.collection.get(ids=[entry_id])
                    if results['ids']:
                        existing_ids.append(entry_id)
                    else:
                        print(f"⚠ Entry '{entry_id}' not found, skipping")
                except:
                    print(f"⚠ Entry '{entry_id}' not found, skipping")
            
            if not existing_ids:
                print("No valid entries to delete")
                return
            
            # 批量删除
            self.cache_manager.collection.delete(ids=existing_ids)
            print(f"✓ Successfully deleted {len(existing_ids)} entries")
            
        except Exception as e:
            logger.error(f"Error deleting entries: {e}")
            import traceback
            traceback.print_exc()
    
    def clear_cache(self):
        """清空所有 cache"""
        try:
            confirm = input("Are you sure you want to clear all cache? (yes/no): ")
            if confirm.lower() != 'yes':
                print("Operation cancelled")
                return
            
            self.cache_manager.clear_cache()
            print("✓ Cache cleared successfully")
            
        except Exception as e:
            logger.error(f"Error clearing cache: {e}")
            import traceback
            traceback.print_exc()
    
    def search_similar(self, query: str, top_k: int = 5):
        """搜索相似问题"""
        try:
            # 创建一个简单的 record 用于搜索
            record = {
                'loop_content': query,
                'pre_condition': '',
                'current_vars': [],
            }
            
            results = self.cache_manager.search_similar_problems(record, loop_idx=0)
            
            if not results:
                print("No similar problems found")
                return
            
            print(f"\n{'='*80}")
            print(f"Similar Problems (Top {min(top_k, len(results))})")
            print(f"{'='*80}\n")
            
            for i, result in enumerate(results[:top_k], 1):
                entry = result.entry
                print(f"[{i}] Similarity: {result.similarity_score:.4f} (Distance: {result.distance:.4f})")
                print(f"    ID: {entry.problem_id[:16]}...")
                print(f"    Problem: {entry.problem_text[:100]}...")
                print()
            
            print(f"{'='*80}\n")
            
        except Exception as e:
            logger.error(f"Error searching: {e}")
            import traceback
            traceback.print_exc()


def main():
    """主函数"""
    parser = argparse.ArgumentParser(
        description='Vector Cache 管理工具',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    
    # --config 参数已废弃，现在从 config.py 读取配置
    # parser.add_argument(
    #     '--config',
    #     type=str,
    #     default='./cache_config.yaml',
    #     help='Cache 配置文件路径 (默认: ./cache_config.yaml)'
    # )
    
    subparsers = parser.add_subparsers(dest='command', help='可用命令')
    
    # list 命令
    list_parser = subparsers.add_parser('list', help='列出所有 cache 条目')
    list_parser.add_argument('--limit', type=int, help='限制显示数量')
    list_parser.add_argument('--details', action='store_true', help='显示详细信息')
    
    # show 命令
    show_parser = subparsers.add_parser('show', help='显示特定条目详情')
    show_parser.add_argument('id', help='条目 ID')
    
    # stats 命令
    subparsers.add_parser('stats', help='显示统计信息')
    
    # add 命令
    add_parser = subparsers.add_parser('add', help='从 JSON 文件添加条目')
    add_parser.add_argument('json_file', help='JSON 文件路径')
    
    # delete 命令
    delete_parser = subparsers.add_parser('delete', help='删除指定条目')
    delete_parser.add_argument('id', help='条目 ID')
    
    # delete-multiple 命令
    delete_multiple_parser = subparsers.add_parser('delete-multiple', help='批量删除条目')
    delete_multiple_parser.add_argument('ids', nargs='+', help='条目 ID 列表')
    
    # clear 命令
    subparsers.add_parser('clear', help='清空所有 cache')
    
    # search 命令
    search_parser = subparsers.add_parser('search', help='搜索相似问题')
    search_parser.add_argument('query', help='搜索查询（循环代码）')
    search_parser.add_argument('--top-k', type=int, default=5, help='返回前 K 个结果 (默认: 5)')
    
    args = parser.parse_args()
    
    if not args.command:
        parser.print_help()
        sys.exit(1)
    
    # 创建 CLI 实例
    cli = CacheManagerCLI()
    
    # 执行命令
    if args.command == 'list':
        cli.list_all(limit=args.limit, show_details=args.details)
    elif args.command == 'show':
        cli.show_entry(args.id)
    elif args.command == 'stats':
        cli.show_stats()
    elif args.command == 'add':
        cli.add_entry(args.json_file)
    elif args.command == 'delete':
        cli.delete_entry(args.id)
    elif args.command == 'delete-multiple':
        cli.delete_multiple(args.ids)
    elif args.command == 'clear':
        cli.clear_cache()
    elif args.command == 'search':
        cli.search_similar(args.query, top_k=args.top_k)


if __name__ == '__main__':
    main()
