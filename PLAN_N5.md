# LRC n=5 形式化计划（Phase-0 文献回填完成，待批准）

## 目标定理

```lean
theorem lonely_runner_five (v : Fin 5 → ℝ) (hv : Function.Injective v) :
    ∀ i : Fin 5, ∃ t ≥ 0, ∀ j : Fin 5, j ≠ i →
      (1/5 : ℝ) ≤ dist ((t * v i : ℝ) : UnitAddCircle) ((t * v j : ℝ) : UnitAddCircle)
```

## 选定路线：Barajas–Serra 2008 §3（arXiv:0710.4495）

放弃 Bienia et al. 原文路线——B-S 论文把 n=5 写成素数筛引理的示范应用，
全部对象是有限/离散的，几乎不需要分析工具。这是已知最干净的 n=5 证明。

## 引理 DAG（三层）

```
[L1 离散层]                                 [L2 组合层]              [L3 解析层]
ZMod N 算术/残数 (x)_N, |x|_N          Prime Filtering Lemma      同步 Dirichlet
ν₅, q(x)=⌊x/5^m⌋ mod 5, r₅(x)   →    (归纳下降证明)          →   (Q⁴ 鸽巢,自证)
Λ_{j,5} 乘子族 + 作用公式 (2)(3)       Corollary 3                 circ Lipschitz 连续
桥接:|λd|_N≥N/5 ⇒ circ(λd/N)≥1/5      ℤ₅ 分情形压缩(ℓ-长度)        Bolzano–Weierstrass
```

**Phase A（整数情形主证明）**——对应 B-S §3:
- A1. m=0 退化情形：所有 d 为 mod 5 单位,λ=1 即证（|x|₅≥1=N/5 自动）
- A2. 若 |D₅(i)|≤2 ∀i<m:Corollary 3（禁集 F_d={0,4},|F|=2,∑≤4=p−1 ✓）
- A3. 仅剩 |D₅(0)|=3 ∧ |D₅(m)|=1（鸽舍：D₅(0),D₅(m) 非空,|D|=4）
- A4. A3 内部:乘 Λ₀,₅∪Λ_{m,5} 压缩 q(A) 避开 {0,4}——
  两个子情形 |A_s|=3 / |A_s|=2,用公式 (4)(5)(6) 分情形
  **逃生舱：此步量化空间本身有限(残类+q值 ∈ ℤ₅⁶),
  组合论证若卡住,内核 `decide` 穷举兜底(= 诚实的机器验证,
  对应 Cusick–Pomerance 当年的计算机检查,但走内核非 native_decide)**
- A5. gcd 归约：D' = D/gcd,见证 t' → t = t'/g
- A6. 汇总:`lrc5_int` — 任意 4 个互异正整数 D,∃t∈(0,1),∀d, circ(td)≥1/5
  （含 ≤4 元集合的 padding:补互异大数即可）

**Phase B（实数归约）**——绕开 Kronecker,走逼近+紧性：
- B1. 同步 Dirichlet:∀Q, ∃q≤Q⁴, ∀i, ∃pᵢ, |aᵢ−pᵢ/q|<1/(qQ)
  (四维鸽巢:把 {j·aᵢ mod 1}, j=0..Q⁴ 塞进 Q⁴ 个盒子)
- B2. 对每步 s:取逼近 p⁽ˢ⁾ᵢ/q_s,s 大时 pᵢ≠0 且互异
  （用 |aᵢ|>0、|aᵢ−aⱼ|>0 抗误差 1/(qQ)）
- B3. 对 {|pᵢ|} 去重+padding 成 4 元 → 用 lrc5_int 得 t*_s∈(0,1)
- B4. Bolzano–Weierstrass:t*_s→t̄;circ Lipschitz⇒circ(t̄aᵢ)≥1/5;
  t̄=0 时 circ=0 矛盾 ⇒ t̄>0

**Phase C（组装）**——复用 n=3 部件：
- C1. dist_unitAddCircle_eq_circ + dist_eq_circ_abs(已有)
- C2. Galilean:4 个相对速度 |vⱼ−vᵢ| 非零互异 ← hv 单射
- C3. Fin 5 分情形 × 主定理 lonely_runner_five

## 工作包划分（4 agent 并行）

| 包 | 文件 | 内容 | 预估 |
|---|---|---|---|
| W1 | `LRC5/Discrete.lean` | L1 全部 + (2)(3) 作用公式 | 中 |
| W2 | `LRC5/Filtering.lean` | Prime Filtering + Cor 3 | **难**（归纳下降） |
| W3 | `LRC5/CaseAnalysis.lean` | A3/A4 ℤ₅ 压缩 + A5/A6 整数情形汇总 | **最难**（decide 兜底） |
| W4 | `LRC5/Approx.lean` + `Main5.lean` | Phase B 全部 + Phase C | 中（标准分析） |

依赖序：W1 → W2,W3 可并行；W4 只需 lrc5_int 的**陈述**（骨架冻结后可同时开工）

## 验证门（同 n=3）+ 新增

- 零 sorry/admit/axiom/native_decide/unsafe（decide 允许,ElVec1o 用了
  native_decide——我们不让步,这是"内核级验证"的差异化声明）
- `#print axioms lonely_runner_five` = 三标准公理

## 风险登记（更新）

- R1 ℤ₅ 分情形在论文里是半页速写,有隐藏细节 → decide 兜底已设计
- R2 同步 Dirichlet 的 Finset 鸽巢在 mathlib 里的 API 契合度 → 预案:
  退到连续 pigeonhole 或直接构造性证明
- R3 Prime Filtering 的"最小 r"归纳 → 预案：改写成强归纳/良基递归
- R4 整体规模 ~1500-2500 行 → 里程碑切分:M1=整数情形过(最难),
  M2=归约过,M3=组装过终审

## 时间预估

诚实估计：骨架+冻结 1 轮,填充 2-4 轮 agent 迭代,终审 1 轮。
若 A4 走 decide 兜底则 W3 显著加速。
