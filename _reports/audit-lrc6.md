# Audit — LRC n=6 (Renault 2004) statement fidelity

独立审计。审的不是推导(kernel 已验),是"声明的东西是不是 LRC n=6 本身"。
审计人:Devin orchestrator;日期:2026-09-18。

## 一、机械门

| 项 | 结果 | 证据 |
|---|---|---|
| `lake build` 全绿复跑 | PASS | 8959 jobs 全部 replay 校验通过(2026-09-18)。 |
| 禁用构造 grep | PASS | `\b(sorry\|admit\|native_decide\|unsafe\|axiom\|opaque\|implemented_by\|extern)\b` 全树扫描:仅注释/文档命中("unsafe arc"、交接注释 "fill the sorrys"),无代码级命中。`unsafe_arc`/`unsafe_flip` 为合法定理名,未被误报。 |
| `set_option` 审查 | PASS(附注) | 仅 `Lemma64.lean` `maxHeartbeats 400000`×2、`LRC5/IntCase` `synthInstance.maxSize 512`+`maxHeartbeats 8000000`——均为 elaboration 资源限,不削弱 kernel。无 `sorryAx`/`ofReduceBool`/`trustCompiler`。 |
| `#print axioms` 七定理 | PASS | build 日志 `Research07.Audit` 段:`lrc6_int`、`lrc6_rel_rat`、`lonely_runner_six_rat`、`prop3_1`、`prop4_1`、`prop5_4`、`prop6_6` 均 `[propext, Classical.choice, Quot.sound]`。 |
| scratch / `_dev` 不入树 | PASS | `Research07/Scratch.lean` 存在但无任何 import 指向它(sink leaf);`_dev/` 在包外无法被 import;伞 `Research07.lean` 仅 `import Research07.LRC6.Main` 引入 n=6。 |

## 二、声明保真

### 锚点(已拉取)

1. `google-deepmind/formal-conjectures@main`:
   `FormalConjectures/Wikipedia/LonelyRunnerConjecture.lean`
   ```lean
   theorem lonely_runner_conjecture (n : ℕ) (speed : Fin n ↪ ℝ)
       (lonely : Fin n → ℝ → Prop)
       (lonely_def : ∀ r t, lonely r t ↔ ∀ r2 : Fin n, r2 ≠ r →
           dist (t * speed r : UnitAddCircle) (t * speed r2) ≥ 1 / n)
       (r : Fin n) : ∃ t ≥ 0, lonely r t := sorry
   ```
   结构:∀ runner r,∃t≥0,∀r2≠r,dist(t·v_r,t·v_r2) ≥ 1/n。速度 `Fin n ↪ ℝ` 单射。

2. `_external/renault.txt`(Renault 2004 全文):摘要 + Thm 1.1:
   "if v1,…,v5 are positive integers, there exists a real t such that
   ⟨t v_i⟩ ∈ [1/6, 5/6] for each i ∈ {1,…,5}"。K+1-instance:K 个正整数速度,
   ⟨tv⟩∈[1/(K+1), K/(K+1)] —— 静止 runner 版 = "Conjecture k"。

### 维度 5:formal-conjectures 逐符号对照 — PASS

| 对象 | 官方 | 本仓 `lonely_runner_six_rat` | 判定 |
|---|---|---|---|
| 量词结构 | ∀r, ∃t≥0, ∀r2≠r | ∀i:Fin 6, ∃t, 0≤t ∧ ∀j≠i | 同构 ✓(每 runner 各自时刻) |
| 速度域 | `Fin n ↪ ℝ`(可负) | `Fin 6 → ℚ` + `Function.Injective` | ℚ⊂ℝ 限制——`_rat` 后缀约定,与 n=4/5 先例一致;整数核 `lrc6_int` = Renault Thm1.1 原文 |
| 位置编码 | `(t * speed r : UnitAddCircle)` | `(t * (v i : ℝ) : UnitAddCircle)` | 同字面 ✓ |
| 距离 | `dist` on `UnitAddCircle` | 同左 | `dist_unitAddCircle_eq_circ` 桥接,circ := ‖x‖=|x−round x| = 官方范数本身(非仅等价) ✓ |
| 阈值 | `1/n`,n=6 ⇒ 1/6 | `(1/6 : ℝ)` 非严格 ≤ | 同字面,非 1/5 非严格 > ✓ |
| 互异性 | embedding 单射 | `Function.Injective v` ⇒ 相对速度非零 | ✓ |

`lrc6_int` 对 Conjecture-5(静止版):`Finset ℕ` 自带互异;`∀d∈D,0<d` 正整数;`card ≤ 5` 覆盖 k≤5(card<5 经 `lrc5_int` 1/5≥1/6);`∃t>0` 强于 Renault 的 ∃t∈ℝ(band 对称 ⇒ 等价)。PASS。

### 维度 6:文献 + 本仓约定对齐 — PASS

- Renault ⟨tv_i⟩∈[1/6,5/6] 闭区间 ⟺ `safe6` 的 `Set.Icc (1/6) (5/6)` ⟺ `circ ≥ 1/6`(`circ_ge_sixth_fract`)。
- `hfail D := ∀t:ℝ, ∃d∈D, ¬safe6 d t` = Renault 的 "D = ∅"(D 为全体安全时刻集)。
- `hfail_exists_dvd`(l∈{2,…,6}) = Renault §2 "time t=1/l shows at least one speed is a multiple of l";l=6 时 {1/6,…,5/6} 恰好闭带边界,与非严格 ≤ 一致。
- STATEMENT.md 约定复核:阈值 1/n(n=总跑者)、`card ≤ n−1`、`circ` = UnitAddCircle 范数、`_int` 给 `t>0` / runner 版给 `t≥0` —— n=6 全部沿用,未偷换表述。

### 维度 7:有理 wrapper 方向 — PASS

`lrc6_rel_rat`:B=∏den>0 公分母,aᵢ=wᵢ·B∈ℤ\{0},D={|aᵢ|};`lrc6_int` 给 t₀>0 ⇒ t=t₀·B:
`circ(t·wᵢ)=circ(t₀·B·(aᵢ/B))=circ(t₀·aᵢ)=circ(t₀·|aᵢ|)≥1/6`。
与 `LRC5/Main.lean` 已验模式逐行同构(Fin 4→Fin 5、1/5→1/6)。真推论非循环:`lrc6_int` 不依赖 wrapper。
`lonely_runner_six_rat`:w_{j'}=v(succAbove j')−v_i 非零(单射)⇒ `lrc6_rel_rat`;`dist = circ(t·(v_i−v_j)) = circ(−t·w)=circ(t·w)` 方向正确。

### 维度 8:gcd 缩放方向(手推)— PASS

`lrc6_case`:D' = D.image(·/g),g=gcd>0。`hf' : hfail D'` 由 `hf (s/g)` 取坏 runner d,映为 d/g:`(d/g)·s = d·(s/g)`(`Nat.cast_div` 精确,因 g|d)。
手推逆否:D' 的安全时刻 s ⇒ circ(s·d/g)=circ((s/g)·d)≥1/6 ⇒ **s/g 是 D 的安全时刻** —— 与契约"D/g 的安全时间 t ⇒ D 的安全时间 t/g"一致,方向未反。`prop3_1` 内部 `hfail_div` 同款映射,一致。
D'.gcd=1 证明:g·gcd(D') | g(因 g·gcd(D') 整除每个 d 且整除 gcd(D)…`Finset.dvd_gcd` 归约)⇒ gcd(D')|1。`InjOn (·/g)` 于 g 倍数集成立 ⇒ card 保持 5。

### 维度 9:分派完备性 — PASS

`lrc6_case_gcd`(hgcd=1, hcard=5, hfail):
- `mult3_le_three` ⇒ S.card≤3;`hfail_exists_dvd(l=3)` ⇒ S.card≥1 ⇒ `interval_cases` 分 {1,2,3} 穷尽。
- S.card=3 → `lemma2_3`(签名匹配:S.card=3 = filter 计数)。S.card=2 → `prop3_1 hpos hcard hScard hf`(签名 `(D.filter (3∣·)).card = 2`,`set S` defeq)。
- S.card=1:v₁ 唯一 3 倍;`hfail_exists_dvd(l=6)` ⇒ w6∈S ⇒ w6=v₁ ⇒ 6|v₁。G=D∖{v₁},card=4,剩余类 ∈{±1,±2}(3∤d ⇒ mod6∈{1,2,4,5})。
- E=G 中偶数 = ±2-guards:`even_le_three`(l=2 界,hgcd=1 前提满足)⇒ E.card≤2 ⇒ `interval_cases` {0,1,2} 穷尽。
- E=0 → `prop5_4`(全部 ±1);E=1 → `prop6_6`(u 为 ±2,其余 ±1);E=2 → `prop4_1`。
- **prop4_1 签名 vs 调用点逐参核对**:签名 `(hp1..hp5: 0<vᵢ) (hv1: v₁≡0) (hv2..hv5: vᵢ≡eᵢ) (he2,he3: eᵢ=±2) (he4,he5: eᵢ=±1) (hf: hfail {v₁..v₅})`;调用传 `(hpos v₁)…(hpos v₅) (modEq_zero_iff_dvd.mpr hv₁6) hv₂m hv₃m hv₄m hv₅m he₂ he₃ he₄ he₅ (hDeq ▸ hf)`,顺序/隐参 e₂..e₅ 由 hvₘ 类型推断一致。`hDeq : D = {v₁..v₅}` 由 card=5 构造,五元互异(v₂v₃∈E 偶、v₄v₅∈G∖E 奇、均≠v₁)⇒ `hfail` 忠实传递。开发期"≥3 evens 实际=2"坑:此处 E.card≤2 先行,≥2 分支即 =2,无误。

## 三、判定

**总体:PASS(9/9 维度)。未发现陈述级 bug(无弱化/错位/可轻易满足),
无需冻结变更,无反模型产出。**

| 维度 | verdict |
|---|---|
| 1. lake build 全绿 | PASS(8959 jobs replay) |
| 2. 禁用构造 | PASS(token 边界;`unsafe_arc`/`unsafe_flip` 合法名;`maxHeartbeats`/`synthInstance.maxSize` 为资源项非 kernel 削弱) |
| 3. #print axioms 七定理 | PASS(全部 `[propext, Classical.choice, Quot.sound]`) |
| 4. scratch/_dev 隔离 | PASS(伞仅经 LRC6.Main;Scratch.lean 为 sink leaf) |
| 5. formal-conjectures 逐符号 | PASS(量词/阈值 1/6/UnitAddCircle dist/单射;唯一范围注记:速度域 ℚ⊂ℝ,`_rat` 约定,与 n=4/5 先例一致) |
| 6. 文献+本仓约定 | PASS(Renault Thm1.1 ⟨tv⟩∈[1/6,5/6] ↔ safe6 Icc;hfail↔D=∅;hfail_exists_dvd↔t=1/l;n=3/4/5 约定沿用) |
| 7. 有理 wrapper 方向 | PASS(t=t₀·B,与 LRC5 同模式;非循环) |
| 8. gcd 缩放方向 | PASS(手推:D/g 安全时刻 s ⇒ s/g 是 D 安全时刻;`hfail_div` 同款) |
| 9. 分派完备性 | PASS(mult3 {1,2,3} 穷尽;±2-guards {0,1,2} 穷尽,prop4_1 签名-实参严丝合缝) |

### 附带注记(非缺陷)

- `Research07/LRC6/Lemma64.lean:34` 有 `private lemma safe6`(ℝ 参数),与
  `Reduction.lean` 的 `def safe6`(ℕ runner)同名不同型;private 作用域,
  不影响头定理。
- `lrc6_int` 对 `card<5` 委托 `lrc5_int`(阈值 1/5⊂1/6),对 `|aᵢ|` 塌陷
  (相对速度绝对值重合)天然覆盖。
- `prop3_1` 内部自带 gcd 除法(`hfail_div`),不依赖 `hgcd=1`——调用处
  在 gcd=1 上下文,属冗余但无害的前提富余。

### 交付物

- 本报告:`_reports/audit-lrc6.md`
- `STATEMENT.md` 已加 n=6 档案段(沿用 countermodel 表格式;无新 countermodel 行——本次捕获 0)。
- `_dev/failures.md` 追加一行 clean-pass 记录。
- 结论:`lrc6_int` = Renault 2004 Thm 1.1 的忠实形式化;`lonely_runner_six_rat`
  = formal-conjectures `lonely_runner_conjecture` 在 n=6、ℚ 速度域的忠实特例。
