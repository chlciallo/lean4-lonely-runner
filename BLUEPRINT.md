# Blueprint — Lonely Runner Conjecture, n = 3

目标：Lean 4 + mathlib 中证明三跑者情形的 Lonely Runner Conjecture，
零 sorry，`#print axioms` 仅含 [propext, Classical.choice, Quot.sound]。

## 归属修正（Phase 0 重要发现）

n=3（总共 3 个跑者，阈值 1/3）是 **Wills 1967** 证的——即"2 个动跑者"情形。
文献中常被引为 Betke–Wills 1972 的其实是 n=4（3 个动跑者，阈值 1/4）。
引用时注意约定：多数近期论文的 k = 动跑者数，阈值 1/(k+1)，我们的情形 = k=2。

## 证明路线（Phase 0 选定：实数速度直接证，不走数论）

主定理（对齐 formal-conjectures 的陈述形态）：

    ∀ v : Fin 3 → ℝ injective, ∀ i, ∃ t ≥ 0, ∀ j ≠ i,
      dist (t*vᵢ : UnitAddCircle) (t*vⱼ : UnitAddCircle) ≥ 1/3

归约链：Galilean 旋转系（跑者 i 相对静止）→ circ 对称性取 |·|
→ 两动跑者引理 → 两情形讨论。

## 引理 DAG

| 引理 | 文件 | 内容 | 依赖 | 状态 |
|---|---|---|---|---|
| `circ_eq` | Circ.lean | circ x = \|x − round x\| | norm_eq | ✅ |
| `circ_nonneg` | Circ.lean | 0 ≤ circ x | | ✅ |
| `circ_le_half` | Circ.lean | circ x ≤ 1/2 | | ✅ |
| `circ_add_int` | Circ.lean | circ(x+n) = circ x (n:ℤ) | | ✅ |
| `circ_neg` | Circ.lean | circ(−x) = circ x | | ✅ |
| `circ_abs` | Circ.lean | circ\|x\| = circ x | circ_neg | ✅ |
| `circ_half` | Circ.lean | circ(1/2) = 1/2 | circ_eq | ✅ |
| `circ_ge_third_iff` | Circ.lean | circ x ≥ 1/3 ↔ ∃k:ℤ, x∈[k+1/3,k+2/3] | circ_eq | ✅ |
| `covering` | Covering.lean | 区间 [x,x+L], L>2/3 ⇒ ∃ξ∈区间内, circ ξ ≥ 1/3（取 ξ = max(k₀+1/3, x), k₀=⌈x−2/3⌉） | circ_ge_third_iff | ✅ |
| `lonely_on_window` | TwoMoving.lean | b>0 ⇒ ∀t∈[1/(3b),2/(3b)], circ(t·b) ≥ 1/3 | circ_ge_third_iff | ✅ |
| `two_moving` | TwoMoving.lean | a,b>0 ⇒ ∃t>0, circ(ta)≥1/3 ∧ circ(tb)≥1/3。a=b 取 t=1/(2a)；b<a≤2b 取 t=1/(3b)；a>2b 用 covering+window | circ_half, covering, lonely_on_window, circ_ge_third_iff | ✅ |
| `dist_unitAddCircle_eq_circ` | Main.lean | dist (↑x) (↑y) = circ (x−y) | dist_eq_norm, coe_sub | ✅ |
| `lonely_runner_three` | Main.lean | 主定理：Fin 3 分情形 + two_moving | dist_…_eq_circ, two_moving, circ_abs, circ_neg | ✅ |

状态记号：✅ 未认领 / 🔄 进行中 / ✅ 已证 / ⛔ 卡住
