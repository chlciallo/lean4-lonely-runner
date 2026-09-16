# Journal — Research07 / Lonely Runner k=3

Append-only，倒序（新的在最上）。每条 ≤5 行，写清"做了什么/结果/为什么"。

## 2026-09-16 Phase 1/2 完成,Phase 3 启动

- Phase 0 回报(df564d49):归属修正——n=3 是 Wills 1967,不是 Betke–Wills。
  选定证明:实数速度两情形直接证(MSE 2485587 / Chu Thm 3.2 路线),
  只需 Int.ceil + 区间隶属,不走数论。备选:Bézout 同余路线。
- API 核实:UnitAddCircle.norm_eq = |x − round x| 天然是"最近整数距离"。
- Phase 1:陈述冻结于 Research07/LRC3/*.lean,保真档案见 STATEMENT.md。
- Phase 2:骨架编译通过(全 sorry),引理 DAG 见 BLUEPRINT.md。
- Phase 3:派 3 个并行 subagent 按文件分治填 sorry(契约=陈述不可改,
  禁 sorry/axiom/native_decide,验收=各自文件零 sorry 编译过)。

## 2026-09-16 Phase 0 启动

- 基线 commit `c66e623`：脚手架 + 持久化层（BLUEPRINT/STATEMENT/JOURNAL)。
- 派 background subagent(df564d49）挖 LRC(3) 经典证明文献。
  契约：精确陈述 + Galilean 归约 + 最简完整证明 + 引理 DAG 建议 + 引文。

## 2026-09-16 立项

- 选题：LRC(k=3) 的 Lean 4 形式化。查重结论：所有证明助手零覆盖，
  formal-conjectures 仅有 sorry 陈述；数学界已证至 k≤12（计算辅助）。
- 环境：Lean 4.34.0 + mathlib v4.34.0（elan 4.2.4，缓存已拉，~11GB）。
- 方法论：LeanMarathon 式 blueprint + 契约 subagent + CI 门控；
  验收 = 编译通过 + axioms 干净 + STATEMENT.md 保真审查。
- 下一步：Phase 0，挖 k=3 最干净的经典证明文献。
