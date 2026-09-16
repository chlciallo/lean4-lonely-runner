# LRC n=5 形式化计划 v2（已按 Phase-0 dossier 修正，M1+M2 锁定）

## 范围锁定（用户批准）

- **M1（主交付）**：整数情形 `lrc5_int` —— 任意 ≤4 个互异正整数 D，
  ∃t>0, ∀d∈D, circ(t·d) ≥ 1/5。文献里实际证的定理本身。
- **M2（推论）**：有理数速度跑者版 `lonely_runner_five_rat`
  (v : Fin 5 → ℚ 单射 ⇒ 各跑者孤独时刻)。Galilean + 通分。
- **M3（二期，暂不启动）**：全实数版。需 BHK Lemma 8：
  Kronecker–Perron 子环面密度 + n=4 情形黑箱。与 M1 解耦。

## ⚠️ 已修正的错误

原方案"同步 Dirichlet + 紧性取极限"不成立：有理逼近的见证时刻
落在 (0,q) 随 q→∞ 无界；位置极限点在轨道闭包但不对应有限时刻。
边界 1/5 是本质的（紧实例 {1,2,3,4} 恰在边界）。→ 实数归约推给 M3。

## 选定证明：Barajas–Serra 2008 §3（arXiv:0710.4495）

|D|=4、p=5、N=5^{m+1}、m=max ν₅。全部离散，无需计算机穷举
（ℤ₅ 分情形是证明级符号演算；保留 decide 兜底）。

## 引理 DAG（dossier 逐条核实版）

**Discrete.lean（W1）**——模 N 基础设施：
- `residN x N = x % N`，`absModN x N = min (x%N) (N − x%N)`
- `level D j` = ν₅=j 的元素；`qdig m x` = 最高位 5 进制数字 : ZMod 5
- `runit x` = 单位部分 mod 5；`multLow m j = {1+k·5^{m−j}}`（j<m），`multTop={1,2,3,4}`
- B4 边界引理：非顶层 ν₅(d)<m、λ 单位 ⇒ |λd|_N ≥ 5^m ⟺ qdig(λd)∈{1,2,3}
  （边界点 4·5^m 不可能——ν₅ 论证，**不可省略**）
- B5 顶层自动好：ν₅(d)=m、5∤λ ⇒ |λd|_N ≥ 5^m
- B6 保持：ν₅(x)>j ⇒ ((1+k·5^{m−j})·x) % 5^{m+1} = x % 5^{m+1}
- B7 移位：ν₅(x)=j ⇒ qdig((1+k·5^{m−j})x) = qdig x + k·runit x (in ZMod 5)
- B7' 顶层：qdig(l·d) = l·runit d，l∈{1..4}
- B7'' 进位界：qdig((j+1)x) ∈ qdig(jx)+qdig(x)+{0,1}
- 桥接：circ(λd/N) = absModN(λd,N)/N（≥5^m ⇒ ≥1/5，t=λ/N）

**Filtering.lean（W2）**——B8 特化版降层引理：
- `filtered_multiplier`：i₀≤m，∀j<i₀, 2·|level j|≤4 ⇒ ∃λ，5∤λ，
  层 ≥i₀ 残数原样保持，层 <i₀ 的 qdig(λd)∈{1,2,3}
- 内部：降层归纳（处理层 i₀−1..0），每层 5 个 k 中坏者恰 2|D(j)|≤4<5
  ⇒ 有 k 全局好（对 ℤ₅ 的 Finset 鸽巢）

**IntCase.lean（W3）**——C1-C5 + 组装：
- C1 层数二分：m=0 平凡（λ=1）；中层均 ≤2 → filtered_multiplier(i₀=m)；
  残留 ⟹ |level 0|=3 ∧ |level m|=1（鸽舍：两非空+总4）
- C2 归一化：元素可取负（(N−d) 替换，|λ(N−d)|_N=|λd|_N）⇒ 残类∈{1,2}；
  鸽巢 ⇒ 主类 |A_s|∈{2,3}，剩余元素 r₅=±2s≠±s
- C3 |A_s|=3 数字追踪：非 3-弧 3 子集单轨道 {0,2,3}；j=2 强制；
  j=3 落入 {0,1,2}；共移入 {1,2,3}
- C4 |A_s|=2 + 单子存活：2-弧化后有 ≥2 个好 k（差 (js)⁻¹），
  单子坏 k 差 (js')⁻¹，s'≠±s ⇒ 必有幸存 k
- C5 弧移位引理：ℓ≤3 的 ℤ₅ 子集可共移入 {1,2,3}
- A5 gcd 归约：D/g，t'=t·g；A6 padding：|D|<4 补互异大数
- `lrc5_int` 汇总（含桥接到 circ）

**Rational.lean（W4）**——M2：
- `lrc5_rel_rat`：4 个非零有理相对速度 ⇒ ∃t>0 全 circ≥1/5
  （公分母 c + 绝对值 + lrc5_int，t = c·t₀）
- `lonely_runner_five_rat`：Fin 5 跑者版（succAbove 索引 + dist 桥）

## 工作包（4 agent 并行，陈述冻结后互不阻塞）

W1 Discrete → W2 Filtering、W3 IntCase、W4 Rational 可全并行
（下游只依赖冻结陈述）。M3 留作二期：需 Kronecker 子环面 + LRC₄。

## 验证门

1. 零 sorry/admit/axiom/native_decide/unsafe（`decide` 允许——内核级）
2. `#print axioms lrc5_int` 与 `lonely_runner_five_rat` = 三标准公理
3. STATEMENT.md 保真审查（陈述 ≡ Wills 原始整数版）

## 里程碑

M1 = `lrc5_int` 编译+审计过（最难，含 B8+C3/C4）
M2 = `lonely_runner_five_rat` 过
M3 = 二期（BHK 归约 + LRC₄ 黑箱）
