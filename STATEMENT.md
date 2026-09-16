# Statement Fidelity — LRC(n=3)

防幻觉闸口：Lean 只保证"证明 ↔ 陈述"一致。"陈述 ↔ 想证的数学"在此审查。

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
