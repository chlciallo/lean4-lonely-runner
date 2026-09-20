# Statement Fidelity — LRC(n=3, 4, 5)

防幻觉闸口：Lean 只保证"证明 ↔ 陈述"一致。"陈述 ↔ 想证的数学"在此审查。

# n=3 陈述保真档案

## 非形式化命题（定稿）

3 个跑者在单位圆周上，初始位置相同（0 点），各以两两不同的恒定实数
速度奔跑（速度可为负=反向跑）。则对每个跑者 i，存在时刻 t ≥ 0，使 i
沿圆周方向与其他每个跑者的距离都 ≥ 1/3。

## Lean 陈述

```lean
theorem lonely_runner_three (v : Fin 3 → ℝ) (hv : Function.Injective v) :
    ∀ i : Fin 3, ∃ t ≥ 0, ∀ j : Fin 3, j ≠ i →
      (1/3 : ℝ) ≤ dist ((t * v i : ℝ) : UnitAddCircle) ((t * v j : ℝ) : UnitAddCircle)
```

## 逐符号对照表

| 数学对象 | Lean 编码 | 保真度备注 |
|---|---|---|
| 单位圆周 | `UnitAddCircle` = `AddCircle 1` = ℝ/ℤ | mathlib 标准构造 ✓ |
| 跑者位置 | `(t * v i : ℝ) : UnitAddCircle`（实数积再嵌入圆周）| 与 formal-conjectures 一致 ✓ |
| 圆周距离 | `dist`（赋范群度量）= `‖↑x − ↑y‖` = `|x−y − round(x−y)|`（经 `UnitAddCircle.norm_eq`）| = 到最近整数距离 = 圆周短弧 ✓ |
| 速度两两不同 | `Function.Injective v` | 与 formal-conjectures 的 `Fin n ↪ ℝ` 等价 ✓ |
| "存在某时刻" | `∃ t ≥ 0` | 非"对一切 t"；每个 i 可有各自时刻 ✓ |
| 阈值 1/3 | `(1/3 : ℝ)`，非严格 `≤` | 与猜想一致；{0,1,2} 在 t=1/3 处取到等号 ✓ |

## 与 formal-conjectures 版的关系

其陈述以 `lonely` 为参数、由 `lonely_def` 刻画；我们是其 n=3 特例
（dist 条件内联展开，injective 替换 ↪ 入）。逻辑等价。

## 已知陷阱（已规避）

- 距离沿圆周度量（`UnitAddCircle` 的 dist)，不是直线距离 ✓
- 速度必须两两不同——`Injective` 保证 a,b > 0（差值非零）✓
- "∃ t ≥ 0" 而非 "∀ t" ✓
- 约定：我们的 n=3 = 文献中"k=2 动跑者"，阈值 1/3 ✓

# n=5 陈述保真档案（M1+M2）

## lrc5_int（主交付,M1）

```lean
theorem lrc5_int (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card ≤ 4) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1/5 : ℝ) ≤ circ (t * d)
```

对标:Wills 1967 原始整数版 / B-S Conjecture 1(|D|=4,χ_r≤5)。
- circ t·d = ‖td‖ 到最近整数距离 ✓(Circ.lean circ_eq)
- ≤4 而非 =4:内部 padding 归约,覆盖一切少元素情形
- 正整数非公因要求:内部 gcd 归约处理
- 文献约定:n=4 动跑者 = 5 总跑者 ⇒ 阈值 1/5 ✓

## lonely_runner_five_rat(M2)

```lean
theorem lonely_runner_five_rat (v : Fin 5 → ℚ) (hv : Function.Injective v) :
    ∀ i, ∃ t ≥ 0, ∀ j ≠ i, (1/5) ≤ dist (t·vᵢ : UnitAddCircle) (t·vⱼ)
```

- Galilean 归约:相对速度 vⱼ−vᵢ 非零有理 ⇒ 通分到整数 ⇒ lrc5_int
- 与 formal-conjectures 的 ℝ 版差异:仅限有理速度(M3 才到 ℝ)
- 签名微调:(v i : ℚ) 先升 ℝ 再进 UnitAddCircle

## 已知缺口(已闭合,M3 交付)

实数版需 BHK Lemma 8:Kronecker–Perron 子环面密度 + n=4 情形黑箱。
边界 1/5 本质(紧实例 {1,2,3,4}),朴素逼近不可行——dossier 已证伪。
**以上缺口已全部填上**——见下方 n=4 / n=5 实数版档案。

# n=4 陈述保真档案(M3 前置件)

## lrc4_int

```lean
theorem lrc4_int (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card ≤ 3) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1/4 : ℝ) ≤ circ (t * d)
```

- Renault 2004 附录论证的完整形式化:有限边界集取极值 + 半整数偏移再进入
- `card ≤ 3` 动跑者 + 1 静止 = n=4,阈值 1/4 ✓
- 强归纳于速度总和:全偶 ⇒ 减半递归;否则 mod 4 剩余分情形,
  `a ≡ 0 (mod 4)` 者进 Renault driver

## lrc4_rat_finset / lrc4_rel_rat

有理版经公共分母清分归约到 `lrc4_int`(与 lrc5 同模式)。

# n=5 实数版档案(M3 主交付)

## lonely_runner_five(最终定理)

```lean
theorem lonely_runner_five (v : Fin 5 → ℝ) (hv : Function.Injective v) :
    ∀ i : Fin 5, ∃ t ≥ 0, ∀ j : Fin 5, j ≠ i →
      (1/5 : ℝ) ≤ dist ((t * v i : ℝ) : UnitAddCircle) ((t * v j : ℝ) : UnitAddCircle)
```

- 与 formal-conjectures 的 LRC 条目同型(`Fin 5 → ℝ` 单射、`UnitAddCircle` dist)
- 速度为任意实数(含负),每个跑者可有各自的孤独时刻
- 归约:`lrc5_rel_real` 对 4 个非零相对速度两分——
  ① 存在公共比例 c>0 使所有 |wᵢ| = c·qᵢ(qᵢ∈ℚ):缩放到 `lrc5_int`
  ② 否则:ℚ-线性无关 ⇒ 子环面轨道稠密 ⇒ BHK 再进入论证
- 文献对标:BHK Lemma 8 的两分结构与原文逐行核对(含 OCR `≠`/`=` 勘误)

## 支撑件(M3/)

`flow_orbit_dense`(ℚ-无关 ⇒ 一参轨道稠密,遍历论+mFourier L²)、
`subtorusMap_range_eq_annihilator`(`M̄(u) = Ker(A)+ℤᵈ`)、
`orbit_dense_annihilator`(Kronecker–Perron 闭包刻画)、
`SimDirichlet.exists_delta_lt*`(同步 Dirichlet,自包含鸽巢)。

# n=6 陈述保真档案(独立审计通过 2026-09-18)

## 非形式化命题(定稿)

5 个正整数速度 v₁,…,v₅,存在实数 t 使 ⟨tvᵢ⟩ ∈ [1/6,5/6] ∀i
(Renault 2004, Thm 1.1;静止 runner + 5 动 = 6 跑者,阈值 1/6)。
等价 moving-runner 版:6 个两两不同速度的跑者,每人某时刻距他人 ≥ 1/6。

## lrc6_int(主交付)

```lean
theorem lrc6_int (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card ≤ 5) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1/6 : ℝ) ≤ circ (t * d)
```

- Finset 自带互异;`card ≤ 5`(card<5 经 lrc5_int,1/5 ≥ 1/6)
- `t > 0` 强于 Renault 的 ∃t∈ℝ(带对称 ⇒ 等价)
- `circ(t·d)` = ‖td‖ UnitAddCircle 范数 = ⟨td⟩ 到 {0,1} 距离
  ⟺ `safe6`:fract ∈ Icc(1/6,5/6) = Renault 的闭区间 ✓
- 结构:hfail(D=∅) ⇒ gcd 归约(安全时刻 t ↦ t/g 方向,已手推)⇒
  gcd=1 下剩余类分派:mult3∈{1,2,3} 穷尽;mult3=1 时 ±2-guards ∈{0,1,2}
  (even_le_three 恰好压到 2)→ prop5_4/prop6_6/prop4_1;mult3=2→prop3_1;
  mult3=3→lemma2_3

## lrc6_rel_rat / lonely_runner_six_rat

- `lrc6_rel_rat`:Fin 5 非零 ℚ 相对速度 ⇒ 公分母 B=∏den 清分到 ℤ ⇒
  |aᵢ| 进 lrc6_int ⇒ t = t₀·B(方向与 lrc5_rel_rat 同款)
- `lonely_runner_six_rat`:Fin 6 ↪ ℚ,∀i,∃t≥0,∀j≠i,
  dist(t·vᵢ, t·vⱼ) ≥ 1/6 —— 与 formal-conjectures
  `lonely_runner_conjecture` n=6 特例同构(仅速度域 ℚ⊂ℝ)
- 相对速度 wⱼ=vⱼ−vᵢ 非零(单射);dist=circ(t·w) 经
  `dist_unitAddCircle_eq_circ` + `circ_neg`

## 与 formal-conjectures / Renault 的逐符号对照

| 对象 | 锚点 | 本仓 | 判定 |
|---|---|---|---|
| 量词 | ∀r ∃t≥0 ∀r2≠r | ∀i ∃t,0≤t ∧ ∀j≠i | ✓ |
| 阈值 | 1/n(n=6 ⇒ 1/6) | (1/6:ℝ) 非严格 ≤ | ✓ |
| 距离 | dist on UnitAddCircle | dist(runner 版)/ circ(静止版) | ✓ |
| 整数版 | v_i 正整数,⟨tv⟩∈[1/6,5/6] | Finset ℕ 正元素,safe6 = Icc | ✓ |

## 已知缺口(范围声明,非 bug)

~~速度域限于 ℚ~~ —— 已于 2026-10-01 闭合:实数版 n=6 经 BHK Lemma 8
延伸落地(见下节)。

## lrc6_rel_real / lonely_runner_six(实数版,2026-10-01)

```lean
theorem lonely_runner_six (v : Fin 6 → ℝ) (hv : Function.Injective v) :
    ∀ i : Fin 6, ∃ t ≥ 0, ∀ j : Fin 6, j ≠ i →
      (1/6 : ℝ) ≤ dist ((t * v i : ℝ) : UnitAddCircle) ((t * v j : ℝ) : UnitAddCircle)
```

- 与 formal-conjectures 的 LRC 条目在 n=6 完全同型(`Fin 6 → ℝ` 单射、
  `UnitAddCircle` dist、阈值 1/6、∃t≥0)——不再有速度域限制
- 归约:`lrc6_rel_real` 对 5 个非零实相对速度两分(与 `lrc5_rel_real` 同款)——
  ① 存在公共 c 使所有 |wᵢ| = c·qᵢ:缩放到 `lrc6_rel_rat`
  ② 否则:`lrc6_real_of_irrational_ratio`(BHK Lemma 8 @ n=6,
     `LRC6/RealCase.lean`,移植自 `M3/BHK.lean` 的 n=5 实例化)
- BHK 步:`w ∈ kerSpanRat u` 等坐标碰撞(wᵢ=−wⱼ)⇒ |w| ≤ 4 个不同值 ⇒
  `lrc5_rat_finset`(≤4 正有理数,阈值 1/5,经 `lrc5_int`)⇒
  t·w ∈ annihilator ⇒ `orbit_dense_annihilator` 逼近进开立方体,
  δ = 11/60 ∈ (1/6, 1/5),得严格 `> 1/6`
- 文献对标:bhk.txt §4 行 619 原文:"the irrational case of Conjecture 1
  for n = 6 follows from the rational case of the conjecture for n = 5"——
  本仓的 `lrc5_int`(n=5 有理情形)正是该输入
- `t > 0`(`lrc6_rel_real`)强于官方 ∃t≥0;无理分支为严格 `> 1/6`,
  有理分支 `≥ 1/6`,合并 `≥ 1/6` ✓

# 反模型修正记录(陈述保真闸口的实际捕获)

| 原陈述 | 捕获方式 | 修正 |
|---|---|---|
| `kernel_coords_linearIndependent`(缺"ρ 是核基"前提) | 编译出 n=1 反模型(重复基向量) | 删除假陈述,替换为 `kernel_coords_linearIndependent_of_basis` |
| `exists_k_all_good`(缺正性前提) | 协议审查 | 补正性前提(冻结陈述修正先例) |
| `bhk_w_ne_zero`(前提自相矛盾的空引理) | 终审审计 | 标注未使用;真实非零性在 `hwne` 内联证明 |
| 无条件 `off a (-t) = -off a t`(at≡1/2 反例) | 编译失败 + 反例分析 | 加 `\|off a t\| < 1/4` 前提 |

# n=7 陈述保真档案(Barajas–Serra 2008,arXiv:0710.4495,EJC 15(1) R48)

## 非形式化命题(定稿)

6 个正整数速度 v₁,…,v₆,存在实数 t 使 ⟨tvᵢ⟩ ∈ [1/7,6/7] ∀i
(Barajas–Serra 2008;静止 runner + 6 动 = 7 跑者,阈值 1/7)。
等价 moving-runner 版:7 个两两不同速度的跑者,每人某时刻距他人 ≥ 1/7。

## lrc7_int(主交付,冻结)

```lean
theorem lrc7_int (D : Finset ℕ) (hpos : ∀ d ∈ D, 0 < d) (hcard : D.card ≤ 6) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ D, (1 / 7 : ℝ) ≤ circ (t * d)
```

- Finset 自带互异;`card ≤ 6`(card<6 经 lrc6_int,1/6 ≥ 1/7)
- `t > 0` 强于 BS 的 ∃t∈ℝ(带对称 ⇒ 等价)
- `circ(t·d)` = ‖td‖ UnitAddCircle 范数 = ⟨td⟩ 到 {0,1} 距离
  ⟺ `safe7`:fract ∈ Icc(1/7,6/7) = BS 的闭区间 ✓
- 结构(BS §2–§7):7-adic 赋值分层 level7,m=max ν;
  |A₀|≤3 → Λ₀-滤波(§7 Finite,`lrc7_m1`);
  |A₀|=4 → §5 `hc4`=`lrc7_case4`(λ'ⱼ=j·u'(1+7^{m−i₀}) 乘子,
    eq.8 中间元下界 + eq.9 进位链 + eq.10 multLow;
    |A_s|∈{2,3,4} 三分支 — 平移 prop4x/prop3ax/prop3bx/prop2ix/prop2iix
    有限证书 + `case4_finish` 统一收尾);
  |A₀|=5 → §6 `hc6`=`lrc7_case5m`(3-压缩 Lemma 9 + 编号 10/11 +
    分情形 case61–66 + normU7 QR-翻转);
  m=1 归约到有限 `decide` 证书

## lrc7_rel_rat / lonely_runner_seven_rat(冻结)

- `lrc7_rel_rat`:Fin 6 非零 ℚ 相对速度 ⇒ 公分母 B=∏den 清分到 ℤ ⇒
  |aᵢ| 进 lrc7_int ⇒ t = t₀·B(与 lrc6_rel_rat 同款)
- `lonely_runner_seven_rat`:Fin 7 ↪ ℚ,∀i,∃t≥0,∀j≠i,
  dist(t·vᵢ,t·vⱼ) ≥ 1/7 —— 与 formal-conjectures
  `lonely_runner_conjecture` n=7 特例同构(仅速度域 ℚ⊂ℝ)

## 与 Barajas–Serra / formal-conjectures 的逐符号对照

| 对象 | BS7 锚点 | 本仓 | 判定 |
|---|---|---|---|
| 量词 | ∃t ∀i ⟨tvᵢ⟩∈[1/7,6/7] | ∃t>0 ∀d∈D circ(t·d)≥1/7 | ✓ |
| 阈值 | 1/7 | (1/7:ℝ) 非严格 ≤ | ✓ |
| 距离 | ⟨·⟩ mod 1 | circ / dist | ✓ |
| 乘子 | λ=1+k·s⁻¹·7^m(Lemma 5) | lamP/lam 乘子 ∃ 式 | ✓ |

## 已知缺口(范围声明,非 bug)

~~速度域限于 ℚ~~ —— 已于 2026-09-20 闭合:实数版 n=7 经 BHK Lemma 8
延伸落地(见下节),`lrc6_rat_finset` 前提已补。

## lrc7_rel_real / lonely_runner_seven(实数版,2026-09-20)

```lean
theorem lonely_runner_seven (v : Fin 7 → ℝ) (hv : Function.Injective v) :
    ∀ i : Fin 7, ∃ t ≥ 0, ∀ j : Fin 7, j ≠ i →
      (1/7 : ℝ) ≤ dist ((t * v i : ℝ) : UnitAddCircle) ((t * v j : ℝ) : UnitAddCircle)
```

- 与 formal-conjectures 的 LRC 条目在 n=7 完全同型(`Fin 7 → ℝ` 单射、
  `UnitAddCircle` dist、阈值 1/7、∃t≥0)——不再有速度域限制
- 归约:`lrc7_rel_real` 对 6 个非零实相对速度两分(与 `lrc6_rel_real` 同款)——
  ① 存在公共 c 使所有 |wᵢ| = c·qᵢ:缩放到 `lrc7_rel_rat`
  ② 否则:`lrc7_real_of_irrational_ratio`(BHK Lemma 8 @ n=7,
     `LRC7/RealCase.lean`,移植自 `LRC6/RealCase.lean` 的 n=6 实例化)
- BHK 步:`w ∈ kerSpanRat u` 等坐标碰撞(wᵢ=−wⱼ)⇒ |w| ≤ 5 个不同值 ⇒
  `lrc6_rat_finset`(≤5 正有理数,阈值 1/6,经 `lrc6_int`)⇒
  t·w ∈ annihilator ⇒ `orbit_dense_annihilator` 逼近进开立方体,
  δ = 2/13 ∈ (1/7, 1/6),得严格 `> 1/7`
- `t > 0`(`lrc7_rel_real`)强于官方 ∃t≥0;无理分支为严格 `> 1/7`,
  有理分支 `≥ 1/7`,合并 `≥ 1/7` ✓

## 陈述保真要点(形式化中捕获的 BS 细节)

- **`hc4` 的 attainment 前提**:`hc4`/`lrc7_case4` 显式假设
  `∃d∈D, ν(d)=m` —— 这使"≤1 中间层元素"由计数
  (4+2+1 或 4+1+1+1 ≥ 7 > 6)自动成立,叶范围恰等于论文 §5。
- **|A_s|=2 的 (4,4) 陷阱**:extras 类对为 (4,4) 时,4-连续移位
  **不能**同时避开两个 extras(已用 Python 枚举验证)——论文
  WLOG 重选 `s:=4s` 将 (2,0,2) 类分布变为 (2,2,0),装配中
  显式执行 `¬(c₁=4 ∧ c₂=4)` 后调用 `quad_point_avoid`。
- **`hc6` 的 QR 规范化**:hc6 接口只给 `¬7∣d`;`runit7∈{1,2,4}`
  (QR(7))由叶内 `normU7` 符号翻转完成(r∉QR ⇒ −r∈QR,
  `absModN` 不变量经 `normU7_absModN` 传递)。
