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

## 2026-09-16 Phase 3/4 完成 —— 定理证毕

- 三 agent 全部交付:Circ(7 引理)、Covering+TwoMoving(覆盖/窗口/两动跑者)、
  Main(桥接 + lonely_runner_three)。全量 build 零警告。
- 终审:`#print axioms lonely_runner_three` = [propext, Classical.choice,
  Quot.sound],无 sorryAx、无 ofReduceBool。证明为真。
- 备注:agent 纠正了蓝图中两处假设——mathlib 的 round 是向上取整
  (非 half-to-even);le_or_lt 在本版本不存在(用 lt_or_ge)。
- 归属:该情形为 Wills 1967(文献中 "k=2 动跑者"),Lean 首次形式化。

## 2026-09-16 目标升级:LRC n=5(4 动跑者,阈值 1/5)

- 用户拍板做 n=5。开工前先规划:Phase 0 文献深挖(Bienia et al.
  简化证明 / Cusick-Pomerance 1984 原始计算机辅助证明)+ n=4/n=5
  全证明助手查重终检,两个 subagent 后台运行中。
- mathlib 基础设施盘点(v4.34.0):
  * 有:Dirichlet 逼近(单实数版 exists_int_int_abs_mul_sub_le)、
    连分数/渐近分数、Int.ceil/fract/round 全套、AddCircle 基础
  * 无:同步 Dirichlet 逼近(多维 pigeonhole)、三距离定理
    (Steinhaus)、Kronecker/Weyl 密度定理——同步逼近大概率要自证

## 2026-09-16 n=5 路线定稿

- 查重终检:n=5 在所有证明助手中连陈述都无,干净空缺。
  n=4 nuance:ElVec1o 隐含覆盖整数核但无打包定理、无实数归约。
- 路线选定:Barajas–Serra 2008 (arXiv:0710.4495) §3 的 |D|=4 短证明
  ——素数筛引理 + ℤ₅ 有限分情形,优于 Bienia 原文(自足一页)。
- 关键设计:实数→整数归约不走 Kronecker(mathlib 没有),
  走同步 Dirichlet + Bolzano–Weierstrass 紧性转移,初等可证。
- ℤ₅ 分情形留了内核 decide 逃生舱(对应 Cusick–Pomerance 的
  计算机检查,但走内核而非 native_decide)。
- 计划全文见 PLAN_N5.md,等用户批准开工。

## 2026-09-16 n=5 骨架冻结,4 路并行开工

- dossier 修正:Dirichlet+紧性归约证伪(见证无界、边界本质)。
  M1=整数定理锁定,M2=有理跑者,M3=实数归约推二期。
- 骨架:LRC5/{Discrete,Filtering,IntCase,Main}.lean,17 sorry,
  陈述全冻结并编译过。关键 lemma:filtered_multiplier(降层),
  absModN_ge_iff_qdig(边界),residual_case(ℤ₅ 追踪),lrc5_int。
- 派 4 个 subagent_general 并行填充;验收=各文件零 sorry 编译。

## 2026-09-17 n=5 整数+有理情形证毕(全量零 sorry)

- W1 交付:Discrete.lean 10 个 sorry 全部由 in-flight agent 在会话结束前
  移植完成,编译干净。W3 续作:residual_case 经 digit_chase(有限 ℤ₅
  命题内核 decide)+ three_units 三分支落地;exists_multiplier4 按层数
  二分调用 filtered_multiplier / residual_case。
- lrc5_int:|D|≤4 → pad 至 4(新鲜值 >maxD)→ 除 gcd 得 gcd=1 →
  exists_multiplier4 出 λ(5∤λ)→ t=λ/(g·5^{m+1}),circ_ge_fifth 收尾。
- 终审:全量 build 8934 jobs 零错误;源码 sorry 扫描为空;
  Audit.lean 四定理 axioms=[propext, Classical.choice, Quot.sound]。
- lrc5_rel_rat / lonely_runner_five_rat 随之闭合——n=5 有理数版完成。
- 剩余:全实数版 lonely_runner_five 仍需 BHK/Kronecker 归约(二期 M3)。

## 2026-09-17 另一session完成填充,M1+M2 机器验证落地

- 本会话派出的 W1/W3 agent 中途崩溃(协议错误),另一 session 接续完成。
- 独立复核:全量 build 通过(8934 jobs),四定理公理全干净:
  lonely_runner_three / lrc5_int / lrc5_rel_rat / lonely_runner_five_rat
  均仅依赖 [propext, Classical.choice, Quot.sound]。零 sorry/native_decide。
- 定位:首个超平凡情形的 LRC 机器验证(全证明助手范围)。
- 残余:DiscreteWork.lean/Scratch.lean 草稿文件(不在 import 树);
  若干风格警告。待发刊前清理。

## 2026-09-17 M3 筹备 + 抬档项侦察启动

- 用户批准 M3 准备 + 抬档调研。三路侦察并行:
  A) BHK Lemma 8 完整重建 + Henze-Malikiosis 5.3 备选 + n=4 黑箱证明
  B) mathlib 生态盘点(Kronecker/子环面/同步逼近有无现成件)
  C) n=6(Renault 简化)与 n=7(B-S 正题)规模评估 + 查重
- 本地初查:mathlib 有 ClosedSubgroup 机器,无多维 Kronecker、
  无子环面分类、无同步 Dirichlet——M3 的分析件基本要自建。

## 2026-09-17 侦察情报汇总(2/3 已回)

### mathlib 生态盘点(关键发现)
- **同步 Dirichlet 已在 mathlib 门口**:`NormedAddCommGroup.exists_norm_nsmul_le`
  (WellApproximable.lean:322) 直接用于 `UnitAddTorus (Fin d)`,~100-200 行可得
  `∃j∈Icc 1 n, ∀i, ‖j•ξᵢ‖ ≤ (n+1)^{-1/d}`。
- **外部现成件**:ElVec1o/five-distance-sharp 有 `SimultaneousDirichlet.lean`(纯鸽巢
  ~120行,已克隆到 _external/ 核实,sorry-free,v4.30 需移植)。
- **ergodic_add_left_iff_denseRange_zsmul**(OfMinimal.lean:215):ℤ-轨道稠密↔遍历,
  接上 mFourierBasis 正交基即可证 n 维 Kronecker(~400-800行,mathlib 缺失)。
- **轨道闭包=关系格零化子**(Kronecker-Perron 子环面):MEDIUM-HARD ~800-1500行;
  有初等路线(关系格补基→子环面参数化→拉回独立情形)。
- **关键省事**:等坐标构造把4速降到≤3个非零整数速,lrc5_int 已覆盖
  card≤4——不需要单独形式化 n=4 定理!
- 闭子群分类/Pontryagin 全对偶 mathlib 缺失,但走直接路线可绕开。

### 抬档项评估
- n=6 via BHK:~12-20k行,❌不做。via Renault(Discrete Math 2004,9页):
  ~2000-3500行,模6同余类有限枚举——中等可做。
- n=7 via B-S正题:~5500-8000行,需离散层全面 p-参数化重构 +
  隐藏依赖 lrc6_int(它内部引用 n≤6 情形)。排序:n=6 → n=7。
- κ(V) 有限检查公式:~800-1500行,最便宜且最"mathlib 形状",
  自带"每实例可判定"推论。
- **查重终判**:n=6、n=7 在所有证明助手中零形式化——做任何一个都是世界首次。
- 计算验证线(k=7..13)全部靠未验证的 C++ 输出,无内核可检证书——
  我们的内核验证不与它们重复。

### 待回:文献 agent(BHK Lemma 8 完整重建 + n=4 证明)

## 2026-09-17 M3 骨架冻结 + 8路并行开工

- 规则修正:subagent_explore 只读,报告协议必须用 subagent_general
  (AGENTS.md 已写明;explore 交付物由 orchestrator 落盘)。
- M3 骨架冻结(全部 sorry 陈述编译通过):
  Relations(relLattice/kerSpan/kerSpanRat/kerSpanInt/annihilator + 4引理)
  Subtorus(subtorusMap + range=annihilator)
  FlowDense(flow_orbit_dense)
  OrbitClosure(orbit_dense_annihilator)
  BHK(bhk_w三件套 + lrc5_real_of_irrational_ratio)
  Dirichlet(两陈述) LRC4(lrc4_int/lrc4_rel_rat/lrc4_rat_finset)
  Main(lrc5_rel_real/lonely_runner_five)
- Kronecker.lean 按所有权拆三文件(一文件一agent)。
- 并行 agent:W5=6d65c149, W7b=d6180ae5, W6=c5d0b176, W7a=edd850e4,
  W7c=cd46338e, W8=300919df, W9=198ca837, W10=78f41dce
- 文献侦察:24e5010e(Renault s=3), 39d7801e(Henze-Malikiosis)

## 2026-09-17 W10 交付(首个完成包)

- e4265da0: lrc5_rel_real + lonely_runner_five 证毕(零 sorry),
  axioms 暂含 sorryAx(来自上游未填的 frozen 引理,收敛后自清)。
- 跨文件修复:Dirichlet.lean zmultiples→AddSubgroup.zmultiples(v4.34 限定符)。
- 已知散件:Research07/W6Scratch.lean(W6 反模型草稿,不被 import)。
- 连接错误阵亡4路已重启:W7c=cdd7aaee, W8=75e8b127, W9=d65d9e46。
  仍在跑:W5=6d65c149, W7b=d6180ae5, W6=c5d0b176, W7a=edd850e4。

## 2026-09-17 W9 交付

- d65d9e46: BHK.lean 4 sorry 全证。lrc5_real_of_irrational_ratio 的 sorryAx
  仅来自未收敛的上游签名(W6/W8)。
- 骨架瑕疵记录:bhk_w_ne_zero 的 hi/hj 方向写反(冻结陈述互斥、空真),
  正确论证(相邻比值对 + mediant 严格内部)已内联于主引理。教训:
  冻结陈述也要小样例 sanity-check。
- 实际用 δ=9/40;annihilator 成员证明走 AddCircle.coe_zsmul/zsmul_eq_mul。

## 2026-09-17 W7b+W7a 完成

- W7b Dirichlet 经核实完成(190行,全 delta/rem API + 双定理,零 sorry)。
- W7a Subtorus 证毕(390行):饱和子模→无挠商→对偶函数族的干净路径;
  subtorusMap_range_eq_annihilator 的 sorryAx 仅来自 W6 未收敛的
  kerSpan_eq_span_rat。
- W6 正在重构 Relations.lean(626行膨胀中,中途编译破损正常)。
- 重启第三次:W7c=2c701ed0(带前代归约笔记), W8=dbfd3a65。

## 2026-09-17 W6 交付 + 第二个冻结错误裁决

- c5d0b176: Relations.lean 3/4 证毕;kernel_coords_linearIndependent 原陈述
  被证伪(hρspan 不含独立性,坐标不唯一)——批准删除,以修正版
  kernel_coords_linearIndependent_of_basis(hρmem+hρind)替代,已证。
- 下游适配:W8 需两小引理(kerSpanInt→kerSpanRat 提升,ℤ-独立→ℚ-独立)。

## 2026-09-17 W7c+W8 交付(最难件落地)

- W7c 流版 Kronecker 证毕(339行):遍历论路线——
  ergodic_add_left_iff_denseRange_zsmul + mFourier L² 论证(离散Kronecker)
  + 截面返回映射(d≥1 取非零分量j, t₀=r/c_j 命中截面, 子环面离散密度)。
  mFourier 局部测度实例陷阱已记录。
- W8 orbit_dense_annihilator 证毕,公理三件套。
- **M3 全链只剩 W5 (lrc4_int/lrc4_rat)。**
