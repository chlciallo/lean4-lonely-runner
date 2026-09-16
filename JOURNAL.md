# Journal — Research07 / Lonely Runner k=3

Append-only，倒序（新的在最上）。每条 ≤5 行，写清"做了什么/结果/为什么"。

## 2026-09-16 立项

- 选题：LRC(k=3) 的 Lean 4 形式化。查重结论：所有证明助手零覆盖，
  formal-conjectures 仅有 sorry 陈述；数学界已证至 k≤12（计算辅助）。
- 环境：Lean 4.34.0 + mathlib v4.34.0（elan 4.2.4，缓存已拉，~11GB）。
- 方法论：LeanMarathon 式 blueprint + 契约 subagent + CI 门控；
  验收 = 编译通过 + axioms 干净 + STATEMENT.md 保真审查。
- 下一步：Phase 0，挖 k=3 最干净的经典证明文献。
