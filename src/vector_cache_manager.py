"""
Vector Cache Manager for SE2INV
向量数据库缓存管理器

功能：
1. 向量数据库初始化和连接
2. 问题向量化和存储
3. 相似度检索和阈值过滤
4. 缓存命中时的结果复用
5. 缓存未命中时的新问题求解和存储
"""

import os
import json
import hashlib
import logging
import yaml
from typing import Dict, List, Optional, Tuple, Any
from dataclasses import dataclass
from pathlib import Path
import numpy as np

# 可选依赖导入
try:
    import chromadb
    from chromadb.config import Settings
    CHROMA_AVAILABLE = True
except ImportError:
    CHROMA_AVAILABLE = False

try:
    from sentence_transformers import SentenceTransformer
    SENTENCE_TRANSFORMERS_AVAILABLE = True
except ImportError:
    SENTENCE_TRANSFORMERS_AVAILABLE = False

try:
    import openai
    OPENAI_AVAILABLE = True
except ImportError:
    OPENAI_AVAILABLE = False

try:
    import pinecone
    PINECONE_AVAILABLE = True
except ImportError:
    PINECONE_AVAILABLE = False


@dataclass
class CacheEntry:
    """缓存条目数据结构"""
    problem_id: str
    problem_text: str
    problem_features: Dict[str, Any]
    solution_code: str
    solution_invariants: List[str]
    metadata: Dict[str, Any]
    timestamp: float
    verification_results: Dict[str, Any]


@dataclass
class SimilarityResult:
    """相似度检索结果"""
    entry: CacheEntry
    similarity_score: float
    distance: float


class VectorCacheManager:
    """向量数据库缓存管理器"""

    def __init__(self, config_path: Optional[str] = None, logger: Optional[logging.Logger] = None):
        """
        初始化向量缓存管理器

        Args:
            config_path: 配置文件路径（已废弃，保留用于向后兼容）
            logger: 日志记录器
        """
        self.logger = logger or logging.getLogger(__name__)
        
        # 从主配置文件读取缓存配置
        try:
            from config import CACHE_CONFIG
            self.config = {'cache': CACHE_CONFIG}
            self.logger.info("Loaded cache configuration from config.py")
        except ImportError:
            self.logger.warning("Failed to import CACHE_CONFIG from config.py, cache disabled")
            self.enabled = False
            return
        except Exception as e:
            self.logger.warning(f"Failed to load cache config from config.py: {e}")
            self.enabled = False
            return

        # 检查是否启用缓存
        if not self.config.get('cache', {}).get('enabled', False):
            self.logger.info("Vector cache is disabled in configuration")
            self.enabled = False
            return

        self.enabled = True
        self.vector_db = None
        self.embedding_model = None

        # 初始化组件
        self._init_embedding_model()
        self._init_vector_database()

        self.logger.info("Vector cache manager initialized successfully")

    def _init_embedding_model(self):
        """初始化向量化模型"""
        if not self.enabled:
            return

        embedding_config = self.config['cache']['embedding']
        model_type = embedding_config.get('model_type', 'sentence_transformers')

        if model_type == 'sentence_transformers':
            if not SENTENCE_TRANSFORMERS_AVAILABLE:
                self.logger.error("sentence-transformers not available, please install: pip install sentence-transformers")
                self.enabled = False
                return

            model_name = embedding_config['sentence_transformers']['model_name']
            device = embedding_config['sentence_transformers'].get('device', 'cpu')

            try:
                self.embedding_model = SentenceTransformer(model_name, device=device)
                self.logger.info(f"Initialized SentenceTransformer model: {model_name}")
            except Exception as e:
                self.logger.error(f"Failed to initialize SentenceTransformer: {e}")
                self.enabled = False
                return

        elif model_type == 'openai':
            if not OPENAI_AVAILABLE:
                self.logger.error("openai not available, please install: pip install openai")
                self.enabled = False
                return

            api_key = embedding_config['openai'].get('api_key') or os.getenv('OPENAI_API_KEY')
            if not api_key:
                self.logger.error("OpenAI API key not found")
                self.enabled = False
                return

            openai.api_key = api_key
            self.openai_model = embedding_config['openai']['model']
            self.logger.info(f"Initialized OpenAI embeddings: {self.openai_model}")

        else:
            self.logger.error(f"Unsupported embedding model type: {model_type}")
            self.enabled = False

    def _init_vector_database(self):
        """初始化向量数据库"""
        if not self.enabled:
            return

        db_config = self.config['cache']['vector_db']
        db_type = db_config.get('type', 'chroma')

        if db_type == 'chroma':
            self._init_chroma_db(db_config['chroma'])
        elif db_type == 'pinecone':
            self._init_pinecone_db(db_config['pinecone'])
        elif db_type == 'milvus':
            self._init_milvus_db(db_config['milvus'])
        else:
            self.logger.error(f"Unsupported vector database type: {db_type}")
            self.enabled = False

    def _init_chroma_db(self, chroma_config: Dict[str, Any]):
        """初始化 ChromaDB"""
        if not CHROMA_AVAILABLE:
            self.logger.error("chromadb not available, please install: pip install chromadb")
            self.enabled = False
            return

        try:
            persist_dir = chroma_config.get('persist_directory', './vector_cache_db')
            collection_name = chroma_config.get('collection_name', 'se2inv_problems')

            # 创建持久化目录
            os.makedirs(persist_dir, exist_ok=True)

            # 初始化 ChromaDB 客户端
            self.vector_db = chromadb.PersistentClient(path=persist_dir)

            # 获取或创建集合
            try:
                self.collection = self.vector_db.get_collection(name=collection_name)
                self.logger.info(f"Connected to existing ChromaDB collection: {collection_name}")
            except:
                self.collection = self.vector_db.create_collection(name=collection_name)
                self.logger.info(f"Created new ChromaDB collection: {collection_name}")

        except Exception as e:
            self.logger.error(f"Failed to initialize ChromaDB: {e}")
            self.enabled = False

    def _init_pinecone_db(self, pinecone_config: Dict[str, Any]):
        """初始化 Pinecone"""
        if not PINECONE_AVAILABLE:
            self.logger.error("pinecone-client not available, please install: pip install pinecone-client")
            self.enabled = False
            return

        # Pinecone 初始化逻辑（需要 API key）
        api_key = pinecone_config.get('api_key') or os.getenv('PINECONE_API_KEY')
        if not api_key:
            self.logger.error("Pinecone API key not found")
            self.enabled = False
            return

        # 这里可以添加 Pinecone 的具体初始化代码
        self.logger.info("Pinecone initialization not fully implemented yet")

    def _init_milvus_db(self, milvus_config: Dict[str, Any]):
        """初始化 Milvus"""
        # Milvus 初始化逻辑
        self.logger.info("Milvus initialization not fully implemented yet")

    def _extract_problem_features(self, record: Dict[str, Any], loop_idx: int) -> Dict[str, Any]:
        """
        从循环记录中提取问题特征

        Args:
            record: 循环记录
            loop_idx: 循环索引

        Returns:
            问题特征字典
        """
        features = {}

        feature_config = self.config['cache'].get('problem_features', {})

        if feature_config.get('include_loop_content', True):
            features['loop_content'] = record.get('loop_content', '')

        if feature_config.get('include_pre_condition', True):
            features['pre_condition'] = record.get('pre_condition', '')

        if feature_config.get('include_variables', True):
            features['current_vars'] = record.get('current_vars', [])
            features['param_pre_vars'] = record.get('param_pre_vars', [])

        if feature_config.get('include_loop_bound', True):
            features['loop_bound'] = record.get('loop_bound', '')

        if feature_config.get('include_execution_traces', True):
            # 这里可以包含采样内容或执行轨迹
            features['var_maps'] = record.get('var_maps', [])
            features['path_conds'] = record.get('path_conds', [])

        features['loop_idx'] = loop_idx

        return features

    def _create_problem_text(self, features: Dict[str, Any]) -> str:
        """
        从特征创建问题文本描述（用于向量化）

        Args:
            features: 问题特征

        Returns:
            问题文本描述
        """
        text_parts = []

        # 循环内容
        if 'loop_content' in features and features['loop_content']:
            text_parts.append(f"Loop: {features['loop_content']}")

        # 前置条件
        if 'pre_condition' in features and features['pre_condition']:
            text_parts.append(f"Precondition: {features['pre_condition']}")

        # 变量信息
        if 'current_vars' in features and features['current_vars']:
            text_parts.append(f"Variables: {', '.join(features['current_vars'])}")

        # 循环边界
        if 'loop_bound' in features and features['loop_bound']:
            text_parts.append(f"Loop bound: {features['loop_bound']}")

        # 变量映射（简化）
        if 'var_maps' in features and features['var_maps']:
            # 只取前几个映射作为示例
            sample_maps = features['var_maps'][:3]
            for var_map in sample_maps:
                if isinstance(var_map, dict):
                    map_str = ', '.join([f"{k}={v}" for k, v in var_map.items()])
                    text_parts.append(f"Sample: {map_str}")

        return " | ".join(text_parts)

    def _generate_problem_id(self, features: Dict[str, Any]) -> str:
        """
        生成问题唯一标识符

        Args:
            features: 问题特征

        Returns:
            问题ID
        """
        # 使用关键特征生成哈希
        key_features = {
            'loop_content': features.get('loop_content', ''),
            'pre_condition': features.get('pre_condition', ''),
            'current_vars': sorted(features.get('current_vars', [])),
            'loop_bound': features.get('loop_bound', '')
        }

        feature_str = json.dumps(key_features, sort_keys=True)
        return hashlib.md5(feature_str.encode()).hexdigest()

    def _get_embedding(self, text: str) -> np.ndarray:
        """
        获取文本的向量表示

        Args:
            text: 输入文本

        Returns:
            向量表示
        """
        if not self.enabled:
            return np.array([])

        embedding_config = self.config['cache']['embedding']
        model_type = embedding_config.get('model_type', 'sentence_transformers')

        try:
            if model_type == 'sentence_transformers':
                embedding = self.embedding_model.encode(text)
                return embedding

            elif model_type == 'openai':
                response = openai.Embedding.create(
                    input=text,
                    model=self.openai_model
                )
                embedding = np.array(response['data'][0]['embedding'])
                return embedding

        except Exception as e:
            self.logger.error(f"Failed to generate embedding: {e}")
            return np.array([])

        return np.array([])

    def search_similar_problems(self, record: Dict[str, Any], loop_idx: int) -> List[SimilarityResult]:
        """
        搜索相似问题

        Args:
            record: 循环记录
            loop_idx: 循环索引

        Returns:
            相似问题列表
        """
        if not self.enabled:
            return []

        try:
            # 提取问题特征
            features = self._extract_problem_features(record, loop_idx)
            problem_text = self._create_problem_text(features)

            # 生成查询向量
            query_embedding = self._get_embedding(problem_text)
            if query_embedding.size == 0:
                return []

            # 在向量数据库中搜索
            similarity_config = self.config['cache']['similarity']
            top_k = similarity_config.get('top_k', 5)

            if hasattr(self, 'collection'):  # ChromaDB
                results = self.collection.query(
                    query_embeddings=[query_embedding.tolist()],
                    n_results=top_k,
                    include=['metadatas', 'documents', 'distances']
                )

                similar_results = []
                if results['ids'] and results['ids'][0]:
                    for i, (doc_id, metadata, document, distance) in enumerate(zip(
                        results['ids'][0],
                        results['metadatas'][0],
                        results['documents'][0],
                        results['distances'][0]
                    )):
                        # 将距离转换为相似度分数 (1 - normalized_distance)
                        similarity_score = max(0, 1 - distance)

                        # 解析 JSON 字符串（如果存储时被序列化了）
                        solution_invariants = metadata.get('solution_invariants', [])
                        if isinstance(solution_invariants, str):
                            try:
                                solution_invariants = json.loads(solution_invariants)
                            except (json.JSONDecodeError, TypeError):
                                # 如果不是有效的 JSON，尝试作为单个字符串处理
                                solution_invariants = [solution_invariants] if solution_invariants else []
                        
                        verification_results = metadata.get('verification_results', {})
                        if isinstance(verification_results, str):
                            try:
                                verification_results = json.loads(verification_results)
                            except (json.JSONDecodeError, TypeError):
                                # 如果不是有效的 JSON，保持为空字典
                                verification_results = {}
                        
                        # 重构缓存条目
                        cache_entry = CacheEntry(
                            problem_id=doc_id,
                            problem_text=document,
                            problem_features=metadata.get('features', {}),
                            solution_code=metadata.get('solution_code', ''),
                            solution_invariants=solution_invariants if isinstance(solution_invariants, list) else [],
                            metadata=metadata,
                            timestamp=metadata.get('timestamp', 0),
                            verification_results=verification_results if isinstance(verification_results, dict) else {}
                        )

                        similar_results.append(SimilarityResult(
                            entry=cache_entry,
                            similarity_score=similarity_score,
                            distance=distance
                        ))

                # 按相似度排序
                similar_results.sort(key=lambda x: x.similarity_score, reverse=True)

                # 过滤低于阈值的结果
                threshold = similarity_config.get('threshold', 0.85)
                filtered_results = [r for r in similar_results if r.similarity_score >= threshold]

                if filtered_results:
                    self.logger.info(f"Found {len(filtered_results)} similar problems above threshold {threshold}")
                    for i, result in enumerate(filtered_results[:3]):  # 只记录前3个
                        self.logger.info(f"  [{i+1}] Similarity: {result.similarity_score:.3f}, ID: {result.entry.problem_id[:8]}...")

                return filtered_results

        except Exception as e:
            self.logger.error(f"Failed to search similar problems: {e}")
            return []

        return []

    def store_problem_solution(self, record: Dict[str, Any], loop_idx: int,
                             solution_code: str, solution_invariants: List[str],
                             verification_results: Dict[str, Any]):
        """
        存储问题和解决方案到缓存
        
        如果已存在相同问题，则不存储（避免重复）

        Args:
            record: 循环记录
            loop_idx: 循环索引
            solution_code: 解决方案代码
            solution_invariants: 解决方案不变量
            verification_results: 验证结果
        """
        if not self.enabled:
            return

        try:
            # 提取问题特征
            features = self._extract_problem_features(record, loop_idx)
            problem_text = self._create_problem_text(features)
            problem_id = self._generate_problem_id(features)

            # 检查是否已存在相同问题
            existing_entry = self._get_existing_entry(problem_id)
            if existing_entry:
                self.logger.debug(f"Cache entry {problem_id[:8]}... already exists, skipping storage")
                return

            # 生成向量
            embedding = self._get_embedding(problem_text)
            if embedding.size == 0:
                self.logger.warning(f"Failed to generate embedding for problem {problem_id[:8]}...")
                return

            # 准备元数据
            metadata = {
                'features': json.dumps(features) if isinstance(features, (dict, list)) else str(features),
                'solution_code': solution_code,
                'solution_invariants': json.dumps(solution_invariants) if isinstance(solution_invariants, list) else str(solution_invariants),
                'verification_results': json.dumps(verification_results) if isinstance(verification_results, dict) else str(verification_results),
                'timestamp': __import__('time').time(),
                'loop_idx': loop_idx
            }

            # 存储到向量数据库
            if hasattr(self, 'collection'):
                self.collection.add(
                    ids=[problem_id],
                    embeddings=[embedding.tolist()],
                    documents=[problem_text],
                    metadatas=[metadata]
                )
                self.logger.info(f"Stored problem solution in cache: {problem_id[:8]}... (invariants: {len(solution_invariants)})")

        except Exception as e:
            self.logger.error(f"Failed to store problem solution: {e}")
            import traceback
            self.logger.debug(traceback.format_exc())
    
    def _get_existing_entry(self, problem_id: str) -> Optional[CacheEntry]:
        """
        获取已存在的缓存条目
        
        Args:
            problem_id: 问题ID
            
        Returns:
            缓存条目，如果不存在则返回 None
        """
        if not self.enabled or not hasattr(self, 'collection'):
            return None
        
        try:
            results = self.collection.get(ids=[problem_id])
            if results and results['ids'] and len(results['ids']) > 0:
                # 找到已存在的条目
                metadata = results['metadatas'][0]
                document = results['documents'][0]
                
                # 解析 JSON 字符串
                solution_invariants = metadata.get('solution_invariants', [])
                if isinstance(solution_invariants, str):
                    try:
                        solution_invariants = json.loads(solution_invariants)
                    except:
                        solution_invariants = [solution_invariants] if solution_invariants else []
                
                verification_results = metadata.get('verification_results', {})
                if isinstance(verification_results, str):
                    try:
                        verification_results = json.loads(verification_results)
                    except:
                        verification_results = {}
                
                features = metadata.get('features', {})
                if isinstance(features, str):
                    try:
                        features = json.loads(features)
                    except:
                        features = {}
                
                return CacheEntry(
                    problem_id=problem_id,
                    problem_text=document,
                    problem_features=features,
                    solution_code=metadata.get('solution_code', ''),
                    solution_invariants=solution_invariants if isinstance(solution_invariants, list) else [],
                    metadata=metadata,
                    timestamp=metadata.get('timestamp', 0),
                    verification_results=verification_results if isinstance(verification_results, dict) else {}
                )
        except Exception as e:
            self.logger.debug(f"Error checking existing entry: {e}")
        
        return None
    
    def get_cache_stats(self) -> Dict[str, Any]:
        """
        获取缓存统计信息

        Returns:
            缓存统计信息
        """
        if not self.enabled:
            return {'enabled': False}

        stats = {'enabled': True}

        try:
            if hasattr(self, 'collection'):  # ChromaDB
                count = self.collection.count()
                stats['total_entries'] = count
                stats['database_type'] = 'chroma'
        except Exception as e:
            self.logger.error(f"Failed to get cache stats: {e}")
            stats['error'] = str(e)

        return stats

    def clear_cache(self):
        """清空缓存"""
        if not self.enabled:
            return

        try:
            if hasattr(self, 'collection'):  # ChromaDB
                # ChromaDB 没有直接的清空方法，需要删除并重新创建集合
                collection_name = self.collection.name
                self.vector_db.delete_collection(name=collection_name)
                self.collection = self.vector_db.create_collection(name=collection_name)
                self.logger.info("Cache cleared successfully")
        except Exception as e:
            self.logger.error(f"Failed to clear cache: {e}")


# 使用示例和测试函数
def test_vector_cache_manager():
    """测试向量缓存管理器"""
    import tempfile
    import time

    # 创建临时配置
    config = {
        'cache': {
            'enabled': True,
            'vector_db': {
                'type': 'chroma',
                'chroma': {
                    'persist_directory': tempfile.mkdtemp(),
                    'collection_name': 'test_collection'
                }
            },
            'embedding': {
                'model_type': 'sentence_transformers',
                'sentence_transformers': {
                    'model_name': 'all-MiniLM-L6-v2',
                    'device': 'cpu'
                }
            },
            'similarity': {
                'threshold': 0.8,
                'top_k': 3
            },
            'strategy': {
                'problem_features': {
                    'include_loop_content': True,
                    'include_pre_condition': True,
                    'include_variables': True,
                    'include_loop_bound': True,
                    'include_execution_traces': True
                }
            }
        }
    }

    # 写入临时配置文件
    config_file = tempfile.NamedTemporaryFile(mode='w', suffix='.yaml', delete=False)
    yaml.dump(config, config_file)
    config_file.close()

    try:
        # 初始化缓存管理器
        cache_manager = VectorCacheManager(config_file.name)

        if not cache_manager.enabled:
            print("Cache manager not enabled, skipping test")
            return

        # 测试数据
        test_record = {
            'loop_content': 'while (x < 100) { x = x + 1; }',
            'pre_condition': 'x == 0',
            'current_vars': ['x'],
            'param_pre_vars': [],
            'loop_bound': 'x <= 100',
            'var_maps': [{'x': 0}, {'x': 1}, {'x': 2}]
        }

        # 存储测试解决方案
        cache_manager.store_problem_solution(
            record=test_record,
            loop_idx=0,
            solution_code='/*@ loop invariant x >= 0 && x <= 100; @*/ while (x < 100) { x = x + 1; }',
            solution_invariants=['x >= 0 && x <= 100'],
            verification_results={'syntax': True, 'valid': True, 'satisfy': True}
        )

        # 等待一下确保存储完成
        time.sleep(0.1)

        # 搜索相似问题
        similar_problems = cache_manager.search_similar_problems(test_record, 0)

        print(f"Found {len(similar_problems)} similar problems")
        for i, result in enumerate(similar_problems):
            print(f"  [{i+1}] Similarity: {result.similarity_score:.3f}")
            print(f"      Problem ID: {result.entry.problem_id}")

        # 获取统计信息
        stats = cache_manager.get_cache_stats()
        print(f"Cache stats: {stats}")

        print("Vector cache manager test completed successfully!")

    except Exception as e:
        print(f"Test failed: {e}")
        import traceback
        traceback.print_exc()

    finally:
        # 清理临时文件
        os.unlink(config_file.name)


if __name__ == '__main__':
    test_vector_cache_manager()