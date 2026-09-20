# lrc7-interfaces.md — LRC7 实现契约(orchestrator 冻结)

各单元共同遵守。基础设施已编译绿:
- `Research07.LRC7.Discrete`(已建,绿)
- `Research07.LRC7.Filtering`(已建,绿)
- `Research07.LRC5.Discrete`(residN/absModN/circ_mul_div_eq_absModN/absModN_neg)
- 论文文本:`_external/bs7-ejc.txt`(权威)+ `_external/bs7.txt`;报告:`_reports/bs7-structure.md`

## 硬约束

- 零 `sorry`/`admit`/`native_decide`/`unsafe`;`decide` 允许。
- `#print axioms` 仅 `[propext, Classical.choice, Quot.sound]`。
- 每个 agent 维护 `_reports/lrc7-<slug>.md` 增量报告(每 ~10 次工具调用追加;
  末段=结构化总结:接口、定理名、公理检查结果、未完成项)。
- 构建:`lake build Research07.LRC7.<Module>`。
- 命名冲突:一律带 `7` 后缀或本文件前缀;不要修改 LRC5/LRC6 任何文件。
- 失败/返工写 `_dev/failures.md` 一行。

## 语义坐标系

- `padicValNat 7 d` = ν₇(d);`runit7 d : ZMod 7` = 最低非零位;`qdig7 m x : ZMod 7` = 首位。
- `level7 D j`、`multLow7 m j`(={1+k·7^{m−j}})、`multTop7`。
- `absModN x N` = min(x%N, N−x%N);目标 `|λd|_N ≥ N/7` ⇔(ν<m)`qdig7 ∉ {0,6}`。
- 顶层元素(ν=m)任意单位 λ 均好:`absModN_top_ge7`。
- `cycIv i L` = ZMod 7 循环区间;`apLen X` = 覆盖长 ℓ(X);`apLen_le_iff`。
- `filtered7`(逐元素 F,层<i₀)+ `filtered7_good`({0,6} 形)+ `exists_top_scalar`(Λ_m)。
- `absModN_pow7_scale`(|7^a x|_{7^a·M}=7^a|x|_M);`circ_ge_seventh`(7∣M → circ≥1/7)。
- 差分建模:整数差 d_i−d_j 用 `subMod x y N := (x%N + N − y%N) % N`(ℕ 层,
  等价于 ZMod N 中 x−y 的剩余);qdig7 作用其上即可,负差自动 wrap。

## 单元契约

### U1 `Finite.lean`(slug: lrc7-finite)

```lean
theorem lrc7_m1 (A : Finset ℕ) (hA : A.card = 5)
    (hpos : ∀ d ∈ A, 0 < d) (hunit : ∀ d ∈ A, ¬ 7 ∣ d)
    (d6 : ℕ) (hd6 : padicValNat 7 d6 = 1) (hd6pos : 0 < d6) :
    ∃ lam M : ℕ, 0 < lam ∧ 0 < M ∧ 7 ∣ M ∧
      ∀ d ∈ A ∪ {d6}, M / 7 ≤ absModN (lam * d) M
```

方法(m=1,已外部复核):
- A 的 mod-49 ±-对类(5 个)二选一:
  - **非坏**:∃λ∈U_49,∀a:|λa|_49≥7 → M=49;d6 用 `absModN_top_ge7`(|λd6|_49≥7)。
  - **坏**:对集恰 63 个=3 个 U_49/{±1} 轨道(代表 {1,3,4,5,18},{1,4,6,10,11},
    {1,4,6,10,22})→ 对这些对集×符号提升 mod 98×d6∈{7,14,…,42}(mod 98,
    符号翻转后 6 值;12 值若直接枚举)枚举:∃λ∈{1..97}(允许非单位!)使
    |λa|_98≥14 ∀a → M=98。
- 反例警示:阶段2 的 λ **允许非单位**(如 λ=7);只查单位会假陈述。
- `decide` 实现;搜索量:对集 C(24,5)=42504 × ≤42λ;Z_98 ~数十万次小检。
  若 decide 超时:Bool 反射/按对集分块/先轨道归一。

### U2 `Case4.lean`(slug: lrc7-case4) §5

```lean
theorem lrc7_case_A4 (A : Finset ℕ) (hA : A.card = 4)
    (hpos : ∀ d ∈ A, 0 < d) (hunit : ∀ d ∈ A, padicValNat 7 d = 0)
    (hcls : ∀ d ∈ A, ((d : ZMod 7) ∈ ({1,2,4} : Finset (ZMod 7))))
    {m i0 : ℕ} (d5 : ℕ) (hd5pos : 0 < d5)
    (hd5 : padicValNat 7 d5 = i0) (hi0 : 0 < i0) (hi0m : i0 ≤ m) (hm : 0 < m) :
    ∃ lam : ℕ, ¬ 7 ∣ lam ∧
      (∀ d ∈ A, qdig7 m (lam * d) ∉ ({0,6} : Finset (ZMod 7))) ∧
      7 ^ m ≤ absModN (lam * d5) (7 ^ (m + 1))
```

方法(论文 §5):d5 = u·7^{i₀},u' = u⁻¹ mod 7^{m+1−i₀}
(用 `Nat.ModEq.pow_totient` 或 ZMod 单位构造 u'=u^{φ−1});
乘子族 λ'_j = j·u'·(1+7^{m−i₀}),1≤j≤5(eq.8:|λ'_j d5|_N ≥7^m,
需独立证明该剩余恒等式:λ'd5 ≡ j(7^{i₀}+7^m) mod 7^{m+1});
Λ₀={1+k·7^m} 保持 d5 剩余 verbatim(`residN_multLow7`,ν(d5)>0)。
按 |A_s|∈{4,3,2} 三案 digit-chase(eq.9 进位:`qdig7_add_one`;
eq.10 平移:`qdig7_multLow` j=0)。ℓ 用 `apLen`/`apLen_le_iff`。

### U3 `Compress.lean`(slug: lrc7-compress) §6 工具层

交付(命名建议,可调):
- `remark8_i`:对集 B 的 q-差分全部 ∈{0,6}(模型:subMod 差分的 qdig7)
  ⇒ 标量 k∈{1..6} 使 apLen (qdig-image (k·B)) ≤ k+1。允许 ZMod 7 有限检。
- `remark8_ii`:q-差分 ∈{0,1,5,6} ⇒ apLen ≤3。
- `lemma5`:apLen 三组和 ≤5 ⇒ ∃k∈{0..6}:q(λ_k·A)∩{0,6}=∅,
  除 (3,1,1)+ẽ∈{2,4} 例外形(例外形作为结论中的析取支返回)。
- `lemma6`:特定长度三元组 ⇒ 同上;带 ẽ 侧条件假设。
- `lemma12`:|A1|=3,|A2|=2 乘子计数(同文件)。
- ẽ 的接口与 `Differences.lean` 对齐:ẽ(d,d') : ZMod 7,
  参数为两整数,q-表达式 2q(d)−q(d') / 2q(d')−q(d) / q(d)−q(d') 按 r 关系;
  若签名分歧以 `Differences.lean` 为准(orchestrator 提供 `etd7`)。
全部 Z_7 有限检;AP 覆盖用 cycIv/apLen_le_iff。

### U4 `Differences.lean`(orchestrator 自建)

`e7 d d' : ℤ`/`etd7 d d' : ZMod 7`;Lemma 4(ẽ Λ_j 不变 + |ẽ−q(e)|≤1)、
Lemma 7(ẽ 回避)、Lemma 9(三元组压缩)、Lemma 10/11(编号)。

### U5 `Case5m.lean`(后续派单)§6.1–6.6 装配

### U6 `IntCase.lean`/`Main.lean`(orchestrator 自建)

外层递归 exists_multiplier7 + 冻结三定理。
