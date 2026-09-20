# lrc7-case4.md — LRC7 §5 |A|=4 实现报告

任务:`Research07/LRC7/Case4.lean`,定理 `lrc7_case_A4`(冻结签名见 lrc7-interfaces.md U2)。

## 段 1:启动 + 文献/接口吸收

已读:lrc7-interfaces.md(全部)、bs7-structure.md §5、bs7-ejc.txt §5(L345-433)、
bs7.txt §5(arXiv 版,L382-551,符号完整)、LRC7/Discrete.lean(全部)、
LRC7/Filtering.lean(全部)、LRC5/Discrete.lean(residN/absModN 定义)。

### 数学结构(论文 §5)
- A={d1..d4}⊂D7(0)(ν=0,剩余∈{1,2,4}),d5∈D7(i0),0<i0≤m,d5=u·7^{i0}。
- u'·u≡1 (mod 7^{m+1-i0});λ'_j=j·u'·(1+7^{m-i0}),1≤j≤5;λ_k=1+k·7^m,0≤k≤6。
- eq8:|λ'_j d5|_N = j(7^m+7^{i0}) ≥ N/7(residual identity λ'_j·d5≡j(7^{i0}+7^m))。
- eq10:q(λ_k·x)=q(x)+k·r(x),r=runit7。
- eq9:q(λ'_{j+1}d)∈q(λ'_jd)+q(λ'_1d)+{0,1} ⇒ q(λ'_jd)∈j·q(λ'_1d)+{0..j−1}。

### 关键推导(已独立验证)
- **eq8 证明**:d5=u·7^{i0},u'u≡1 mod 7^{m+1-i0} ⇒ λ'_j·d5≡j·7^{i0}(1+7^{m-i0})
  =j(7^{i0}+7^m) mod 7^{m+1}。i0<m:res=j7^{i0}+j7^m∈[7^m,6·7^m]⇒min≥7^m;
  i0=m:res=(2j mod7)·7^m,c∈{1..6}⇒min(c,7−c)≥1 ⇒≥7^m。✓
- **r(λ'_j·d)=c_j·r(d)**,c_j=λ'_j mod7=j·w,w:=u'(m>i0)或 2u'(m=i0)。
- **Λ0 收尾机制**:X⊆cycIv i L ⇒∃k0:X+k0·t⊆cycIv 1 L(取 k0t=1−i)。
  |As|=4:L=5,{k0} 单候选;|As|=3:L=4,{k0,k0+t⁻¹};|As|=2:L=2,{k0,k0+t⁻¹,k0+2t⁻¹,k0+3t⁻¹}。
- **d4 伴随(|As|=3)**:两候选对 d4 的 q 差=r4∈{2,4}≠±1={0,6} 间距 ⇒ 必有一好。✓(论文正确)
- **|As|=2 的 WLOG**:d3,d4 相对步长比 (r3,r4)∈{(2,2),(2,4)};(4,4) 经重命名 s→4s 消除
  (A4s 成新 As)。需 decide:z3+ir3,z4+ir4 对 i∈0..3 不同时坏。98 配置。
- **第二支(∀j ℓ 超界)传播**:
  - |As|=4:4 元 ℓ≥6 ⟺ 命中所有 2-区间 ⟺ X={x,x+2,x+4,x+6}(decideable)。
    j=3 后 b_i∈6i+{0,1,2};ℓ(X_3)≥6 锁 b 为差-2-AP;j=4 ⇒ X_4⊆长≤4 区间矛盾。
    (手工验证 8 个 b 构型全 ⊆{0..4}∪{1,2,3}∪{2,3,4}。)
  - |As|=3:3 元 ℓ≥5 ⟺ 命中所有 3-区间 ⟺ X∈{{x,x+1,x+4},{x,x+2,x+4}}。
    {0,1,4} 支:j=2 ⇒⊆cycIv 0 4 矛盾。{0,2,4} 支:j=3 锁 (b0,b2)=(2,5),j=4 ⇒⊆{1..4}。
  - |As|=2:2 元 ℓ≥3 ⟺ 距∉{0,1,6}。代表 {0,2}:j=3⇒(1,6)|(2,0)|(2,6);
    前两 j=4 ⇒ℓ≤2;(2,6) 支 j=4 锁 (3,1),j=5 ⇒ℓ≤2。{0,3}:j=2⇒(1,6);j=3⇒(1,3);
    j=5 用 q(5X)∈q(2X)+q(3X)+{0,1} ⇒{2,3}² ℓ≤2(需 `qdig7_add` 推广引理)。
- **平移等变性**:eq9 范围形式在 q_1→q_1+c 下等变(q_j→q_j+jc),故只需对
  规范化代表 {0,2,4,6}/{0,1,4}/{0,2,4}/{0,2}/{0,3} 证明。

## 段 2:待做
- Python 验证全部 Z7 decideable 引理
- Lean 骨架 + qdig7_add 引理 + u' 构造 + eq8
- 装配三案

## 段 3:Python 全验证通过(2026-10-XX)

`_dev/verify_case4.py`:全部断言数值验证 ✓。要点:
- (r3,r4)=(4,4) 确实失败(worst z3=6,z4=2)→ 必须 WLOG 重命名 s→4s(则 (4,4)→(2,2))。
- |As|=4 传播只有 4 个合法 b-构型(标记 a=(0,2,4,6) 下),全部 j=4 ⊆{2,3,4} 等区间。
- eq8 在 m∈{1,2,3} 全参数验证。

## Lean 设计定稿

全程避免 `apLen` 计算:用 `∃i, X⊆cycIv i L` 形式(apLen_le_iff 只在需要处桥接)。
"∀k 坏" ⇒ "X 命中所有 2-区间"(k↦cycIv(5−kt)2 满射)直接引理,无需补集。

### 所需新引理(Case4.lean 内部)
1. `qdig7_add`:(qdig((a+b)x)−qdig(ax)−qdig(bx)).val≤1 — add_one 推广,同法证。
2. 进位归纳:q_j(d)−j·q_1(d)∈cycIv 0 j(j≤5) — val≤1 逐次 + cycIv0j+{0,1}⊆cycIv0(j+1)。
3. `runit7` 在 ν=0 时 = (x:ZMod7);r(λ'_j·d)=c_j·r(d)。
4. `cycIv_add`:x∈cycIv i L ↔ x+a∈cycIv(i+a)L;`cycIv_compl`(univ∖cycIv i L=cycIv(i+L)(7−L))。
5. decide 载荷:shape4(2401)/shape3(343)/P4a(81×16)/P3a(8)/P3b(27×8)/P2i/P2ii/P2c(49×2)/P3c。
   范围量化用 `∀ b ∈ (S:Finset Z7), P`(decidableBall 只枚举 S)。
6. u'=u^{φ(7^{m+1-i0})−1}:u'u≡1(Nat.ModEq.pow_totient)。
7. eq8:λ'_j·d5≡j(7^{i0}+7^m) mod7^{m+1} ⇒ absModN≥7^m(分 i0<m/i0=m)。

### 装配流
lam=(1+k·7^m)·λ'_j;qdig7_multLow(j=0)+residN_multLow7(ν(λ'_jd5)=i0>0)。
case split:|As|∈{4,3,2}(鸽巢 max≥2);|As|=2 再分 ∃s(|As|=2∧|A2s|=2)/(2,1,1)。
