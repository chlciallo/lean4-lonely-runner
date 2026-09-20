/-
  Barajas–Serra §7, stage 2: for each of the 63 bad pair-sets `Q`, every
  `≤ 5`-subset `T` of the mod-98 lifts of `Q` and every `d6`-residue `r`,
  provided `T ∪ {r}` contains an odd element, some multiplier `λ ∈ {1,…,49}`
  pushes all of `T ∪ {r}` to distance `≥ 14 = 98/7`.

  Certificates are literal "uncovered-lift" tables `uTabQ<k>`: entry `(λ, U)`
  for residue `r` certifies `14 ≤ |λr|_98` and `U = {t ∈ lifts98 Q :
  |λt|_98 < 14}` (`uTabQ<k>_spec`).  The kernel enumeration
  (`stage2_Q<k>`) checks that no 5-subset `T` with odd `T ∪ {r}` meets every
  `U` in the table; arbitrary `T` of card `≤ 5` extend to 5-subsets first.
-/
import Research07.LRC7.FiniteBase

set_option maxRecDepth 1000000

/-- `Q_0 = {1, 3, 4, 5, 18}`, lifts [1, 3, 4, 5, 18, 31, 44, 45, 46, 48]. -/
private def uTabQ0 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(7, {1}), (16, {18, 31}), (21, {5}), (23, {4}), (30, {3, 46}), (31, {3, 44}), 
      (33, {3, 18}), (35, {3, 31, 45}), (45, {46, 48})}
  | 14 => {(5, {1, 18}), (8, {1, 48}), (9, {1, 44, 45}), (15, {45, 46}), (16, {18, 31}), 
      (17, {5, 18, 46}), (18, {5, 44}), (19, {5, 31, 46}), (23, {4}), (29, {3, 44}), 
      (30, {3, 46}), (33, {3, 18}), (39, {5, 45, 48}), (41, {5, 31, 48}), (43, {18, 48}), 
      (45, {46, 48})}
  | 21 => {(7, {1}), (15, {45, 46}), (16, {18, 31}), (21, {5}), (24, {4, 45}), (25, {4, 31}), 
      (27, {4, 18, 44}), (29, {3, 44}), (30, {3, 46}), (35, {3, 31, 45}), (43, {18, 48}), 
      (45, {46, 48})}
  | 28 => {(5, {1, 18}), (8, {1, 48}), (9, {1, 44, 45}), (15, {45, 46}), (16, {18, 31}), 
      (17, {5, 18, 46}), (18, {5, 44}), (19, {5, 31, 46}), (23, {4}), (29, {3, 44}), 
      (30, {3, 46}), (33, {3, 18}), (39, {5, 45, 48}), (41, {5, 31, 48}), (43, {18, 48}), 
      (45, {46, 48})}
  | 35 => {(7, {1}), (15, {45, 46}), (16, {18, 31}), (21, {5}), (23, {4}), (29, {3, 44}), 
      (30, {3, 46}), (33, {3, 18}), (35, {3, 31, 45}), (43, {18, 48})}
  | 42 => {(5, {1, 18}), (8, {1, 48}), (9, {1, 44, 45}), (15, {45, 46}), (16, {18, 31}), 
      (17, {5, 18, 46}), (18, {5, 44}), (19, {5, 31, 46}), (23, {4}), (29, {3, 44}), 
      (30, {3, 46}), (33, {3, 18}), (39, {5, 45, 48}), (41, {5, 31, 48}), (43, {18, 48}), 
      (45, {46, 48})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_0` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q0 :
    ∀ T ∈ (lifts98 {1, 3, 4, 5, 18}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ0 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ0_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ0 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {1, 3, 4, 5, 18}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_0 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {1, 3, 4, 5, 18}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {1, 3, 4, 5, 18}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {1, 3, 4, 5, 18}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q0 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ0_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_1 = {1, 3, 8, 19, 22}`, lifts [1, 3, 8, 19, 22, 27, 30, 41, 46, 48]. -/
private def uTabQ1 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(6, {1, 48}), (7, {1, 27, 41}), (9, {1, 22}), (17, {41, 46}), (18, {22, 27}), 
      (21, {19}), (23, {8, 30}), (24, {8, 41}), (25, {8, 27}), (35, {3}), (39, {30, 48}), 
      (45, {22, 46, 48})}
  | 14 => {(1, {1, 3, 8}), (3, {1, 3, 30}), (6, {1, 48}), (15, {19, 27, 46}), (16, {19, 30}), 
      (17, {41, 46}), (23, {8, 30}), (24, {8, 41}), (25, {8, 27}), (27, {22}), (30, {3, 46}), 
      (33, {3, 27, 30}), (37, {3, 8, 48}), (39, {30, 48}), (41, {19, 48}), (43, {41, 48})}
  | 21 => {(6, {1, 48}), (7, {1, 27, 41}), (17, {41, 46}), (21, {19}), (24, {8, 41}), 
      (25, {8, 27}), (27, {22}), (35, {3}), (39, {30, 48}), (43, {41, 48})}
  | 28 => {(1, {1, 3, 8}), (3, {1, 3, 30}), (6, {1, 48}), (15, {19, 27, 46}), (16, {19, 30}), 
      (17, {41, 46}), (23, {8, 30}), (24, {8, 41}), (25, {8, 27}), (27, {22}), (30, {3, 46}), 
      (33, {3, 27, 30}), (37, {3, 8, 48}), (39, {30, 48}), (41, {19, 48}), (43, {41, 48})}
  | 35 => {(6, {1, 48}), (7, {1, 27, 41}), (19, {41, 46}), (21, {19}), (23, {8, 30}), 
      (24, {8, 41}), (27, {22}), (35, {3}), (43, {41, 48})}
  | 42 => {(1, {1, 3, 8}), (3, {1, 3, 30}), (6, {1, 48}), (15, {19, 27, 46}), (16, {19, 30}), 
      (17, {41, 46}), (23, {8, 30}), (24, {8, 41}), (25, {8, 27}), (27, {22}), (30, {3, 46}), 
      (33, {3, 27, 30}), (37, {3, 8, 48}), (39, {30, 48}), (41, {19, 48}), (43, {41, 48})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_1` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q1 :
    ∀ T ∈ (lifts98 {1, 3, 8, 19, 22}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ1 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ1_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ1 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {1, 3, 8, 19, 22}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_1 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {1, 3, 8, 19, 22}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {1, 3, 8, 19, 22}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {1, 3, 8, 19, 22}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q1 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ1_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_2 = {1, 4, 6, 10, 11}`, lifts [1, 4, 6, 10, 11, 38, 39, 43, 45, 48]. -/
private def uTabQ2 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(21, {})}
  | 14 => {(3, {1, 4}), (4, {1, 48}), (5, {1, 38, 39}), (13, {1, 38, 45}), (16, {6, 43}), 
      (17, {6, 11}), (22, {4, 45}), (23, {4, 38, 43}), (25, {4, 39, 43}), (27, {4, 11}), 
      (29, {10}), (31, {6, 38}), (33, {6, 39}), (36, {11, 38}), (37, {45, 48}), 
      (41, {38, 43, 48}), (43, {39, 43, 48}), (45, {11, 39, 48}), (47, {4, 6, 48})}
  | 21 => {(21, {})}
  | 28 => {(3, {1, 4}), (4, {1, 48}), (5, {1, 38, 39}), (13, {1, 38, 45}), (16, {6, 43}), 
      (17, {6, 11}), (22, {4, 45}), (23, {4, 38, 43}), (25, {4, 39, 43}), (27, {4, 11}), 
      (29, {10}), (31, {6, 38}), (33, {6, 39}), (36, {11, 38}), (37, {45, 48}), 
      (41, {38, 43, 48}), (43, {39, 43, 48}), (45, {11, 39, 48}), (47, {4, 6, 48})}
  | 35 => {(21, {})}
  | 42 => {(3, {1, 4}), (4, {1, 48}), (5, {1, 38, 39}), (13, {1, 38, 45}), (16, {6, 43}), 
      (17, {6, 11}), (22, {4, 45}), (23, {4, 38, 43}), (25, {4, 39, 43}), (27, {4, 11}), 
      (29, {10}), (31, {6, 38}), (33, {6, 39}), (36, {11, 38}), (37, {45, 48}), 
      (41, {38, 43, 48}), (43, {39, 43, 48}), (45, {11, 39, 48}), (47, {4, 6, 48})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_2` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q2 :
    ∀ T ∈ (lifts98 {1, 4, 6, 10, 11}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ2 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ2_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ2 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {1, 4, 6, 10, 11}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_2 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {1, 4, 6, 10, 11}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {1, 4, 6, 10, 11}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {1, 4, 6, 10, 11}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q2 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ2_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_3 = {1, 4, 6, 10, 22}`, lifts [1, 4, 6, 10, 22, 27, 39, 43, 45, 48]. -/
private def uTabQ3 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(21, {})}
  | 14 => {(3, {1, 4}), (5, {1, 22, 39}), (6, {1, 48}), (13, {1, 22, 45}), (17, {6}), 
      (19, {10}), (23, {4, 43}), (24, {4, 45}), (27, {4, 22}), (36, {22, 27}), (37, {45, 48}), 
      (41, {43, 48}), (45, {22, 39, 48})}
  | 21 => {(21, {})}
  | 28 => {(3, {1, 4}), (5, {1, 22, 39}), (6, {1, 48}), (13, {1, 22, 45}), (17, {6}), 
      (19, {10}), (23, {4, 43}), (24, {4, 45}), (27, {4, 22}), (36, {22, 27}), (37, {45, 48}), 
      (41, {43, 48}), (45, {22, 39, 48})}
  | 35 => {(21, {})}
  | 42 => {(3, {1, 4}), (5, {1, 22, 39}), (6, {1, 48}), (13, {1, 22, 45}), (17, {6}), 
      (19, {10}), (23, {4, 43}), (24, {4, 45}), (27, {4, 22}), (36, {22, 27}), (37, {45, 48}), 
      (41, {43, 48}), (45, {22, 39, 48})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_3` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q3 :
    ∀ T ∈ (lifts98 {1, 4, 6, 10, 22}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ3 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ3_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ3 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {1, 4, 6, 10, 22}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_3 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {1, 4, 6, 10, 22}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {1, 4, 6, 10, 22}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {1, 4, 6, 10, 22}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q3 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ3_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_4 = {1, 4, 18, 20, 22}`, lifts [1, 4, 18, 20, 22, 27, 29, 31, 45, 48]. -/
private def uTabQ4 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(21, {})}
  | 14 => {(8, {1, 48}), (16, {18, 31}), (17, {18, 29}), (19, {20, 31}), (20, {20, 29}), 
      (23, {4}), (29, {20, 27}), (31, {22}), (33, {18, 27}), (37, {29, 45, 48}), 
      (39, {20, 45, 48}), (41, {29, 31, 48}), (43, {18, 48})}
  | 21 => {(21, {})}
  | 28 => {(8, {1, 48}), (16, {18, 31}), (17, {18, 29}), (19, {20, 31}), (20, {20, 29}), 
      (23, {4}), (29, {20, 27}), (31, {22}), (33, {18, 27}), (37, {29, 45, 48}), 
      (39, {20, 45, 48}), (41, {29, 31, 48}), (43, {18, 48})}
  | 35 => {(21, {})}
  | 42 => {(8, {1, 48}), (16, {18, 31}), (17, {18, 29}), (19, {20, 31}), (20, {20, 29}), 
      (23, {4}), (29, {20, 27}), (31, {22}), (33, {18, 27}), (37, {29, 45, 48}), 
      (39, {20, 45, 48}), (41, {29, 31, 48}), (43, {18, 48})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_4` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q4 :
    ∀ T ∈ (lifts98 {1, 4, 18, 20, 22}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ4 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ4_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ4 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {1, 4, 18, 20, 22}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_4 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {1, 4, 18, 20, 22}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {1, 4, 18, 20, 22}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {1, 4, 18, 20, 22}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q4 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ4_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_5 = {1, 5, 6, 19, 20}`, lifts [1, 5, 6, 19, 20, 29, 30, 43, 44, 48]. -/
private def uTabQ5 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(35, {})}
  | 14 => {(1, {1, 5, 6}), (5, {1, 19, 20}), (9, {1, 43, 44}), (11, {1, 19, 44}), 
      (13, {1, 30}), (15, {6, 19, 20}), (17, {5, 6, 29}), (19, {5, 20}), (22, {5, 44}), 
      (23, {30, 43}), (24, {20, 29}), (25, {20, 43}), (26, {19, 30}), (27, {29, 44}), 
      (29, {20, 30, 44}), (31, {6, 19, 44}), (32, {6, 43}), (33, {6, 30}), (45, {48})}
  | 21 => {(35, {})}
  | 28 => {(1, {1, 5, 6}), (5, {1, 19, 20}), (9, {1, 43, 44}), (11, {1, 19, 44}), 
      (13, {1, 30}), (15, {6, 19, 20}), (17, {5, 6, 29}), (19, {5, 20}), (22, {5, 44}), 
      (23, {30, 43}), (24, {20, 29}), (25, {20, 43}), (26, {19, 30}), (27, {29, 44}), 
      (29, {20, 30, 44}), (31, {6, 19, 44}), (32, {6, 43}), (33, {6, 30}), (45, {48})}
  | 35 => {(35, {})}
  | 42 => {(1, {1, 5, 6}), (5, {1, 19, 20}), (9, {1, 43, 44}), (11, {1, 19, 44}), 
      (13, {1, 30}), (15, {6, 19, 20}), (17, {5, 6, 29}), (19, {5, 20}), (22, {5, 44}), 
      (23, {30, 43}), (24, {20, 29}), (25, {20, 43}), (26, {19, 30}), (27, {29, 44}), 
      (29, {20, 30, 44}), (31, {6, 19, 44}), (32, {6, 43}), (33, {6, 30}), (45, {48})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_5` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q5 :
    ∀ T ∈ (lifts98 {1, 5, 6, 19, 20}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ5 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ5_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ5 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {1, 5, 6, 19, 20}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_5 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {1, 5, 6, 19, 20}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {1, 5, 6, 19, 20}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {1, 5, 6, 19, 20}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q5 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ5_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_6 = {1, 5, 8, 9, 13}`, lifts [1, 5, 8, 9, 13, 36, 40, 41, 44, 48]. -/
private def uTabQ6 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(35, {})}
  | 14 => {(3, {1, 36}), (4, {1, 48}), (5, {1, 40, 41}), (9, {1, 44}), (15, {13, 40}), 
      (16, {13, 36}), (17, {5, 40, 41}), (18, {5, 44}), (19, {5, 36, 41}), (25, {8}), 
      (27, {36, 40, 44}), (29, {41, 44}), (32, {9, 40}), (33, {9, 36}), (39, {5, 40, 48}), 
      (41, {5, 36, 48}), (43, {9, 41, 48}), (45, {9, 13, 48}), (47, {44, 48})}
  | 21 => {(35, {})}
  | 28 => {(3, {1, 36}), (4, {1, 48}), (5, {1, 40, 41}), (9, {1, 44}), (15, {13, 40}), 
      (16, {13, 36}), (17, {5, 40, 41}), (18, {5, 44}), (19, {5, 36, 41}), (25, {8}), 
      (27, {36, 40, 44}), (29, {41, 44}), (32, {9, 40}), (33, {9, 36}), (39, {5, 40, 48}), 
      (41, {5, 36, 48}), (43, {9, 41, 48}), (45, {9, 13, 48}), (47, {44, 48})}
  | 35 => {(35, {})}
  | 42 => {(3, {1, 36}), (4, {1, 48}), (5, {1, 40, 41}), (9, {1, 44}), (15, {13, 40}), 
      (16, {13, 36}), (17, {5, 40, 41}), (18, {5, 44}), (19, {5, 36, 41}), (25, {8}), 
      (27, {36, 40, 44}), (29, {41, 44}), (32, {9, 40}), (33, {9, 36}), (39, {5, 40, 48}), 
      (41, {5, 36, 48}), (43, {9, 41, 48}), (45, {9, 13, 48}), (47, {44, 48})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_6` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q6 :
    ∀ T ∈ (lifts98 {1, 5, 8, 9, 13}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ6 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ6_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ6 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {1, 5, 8, 9, 13}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_6 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {1, 5, 8, 9, 13}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {1, 5, 8, 9, 13}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {1, 5, 8, 9, 13}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q6 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ6_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_7 = {1, 5, 12, 19, 20}`, lifts [1, 5, 12, 19, 20, 29, 30, 37, 44, 48]. -/
private def uTabQ7 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(35, {})}
  | 14 => {(1, {1, 5, 12}), (9, {1, 12, 44}), (15, {19, 20}), (17, {5, 12, 29}), 
      (18, {5, 44}), (19, {5, 20}), (23, {30}), (25, {12, 20}), (27, {29, 44}), 
      (30, {20, 29}), (31, {19, 44}), (32, {12, 37}), (43, {48})}
  | 21 => {(35, {})}
  | 28 => {(1, {1, 5, 12}), (9, {1, 12, 44}), (15, {19, 20}), (17, {5, 12, 29}), 
      (18, {5, 44}), (19, {5, 20}), (23, {30}), (25, {12, 20}), (27, {29, 44}), 
      (30, {20, 29}), (31, {19, 44}), (32, {12, 37}), (43, {48})}
  | 35 => {(35, {})}
  | 42 => {(1, {1, 5, 12}), (9, {1, 12, 44}), (15, {19, 20}), (17, {5, 12, 29}), 
      (18, {5, 44}), (19, {5, 20}), (23, {30}), (25, {12, 20}), (27, {29, 44}), 
      (30, {20, 29}), (31, {19, 44}), (32, {12, 37}), (43, {48})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_7` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q7 :
    ∀ T ∈ (lifts98 {1, 5, 12, 19, 20}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ7 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ7_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ7 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {1, 5, 12, 19, 20}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_7 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {1, 5, 12, 19, 20}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {1, 5, 12, 19, 20}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {1, 5, 12, 19, 20}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q7 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ7_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_8 = {1, 6, 15, 16, 18}`, lifts [1, 6, 15, 16, 18, 31, 33, 34, 43, 48]. -/
private def uTabQ8 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(4, {1, 48}), (5, {1, 18}), (7, {1, 15, 43}), (17, {6, 18, 34}), (20, {15, 34}), 
      (21, {33}), (23, {34, 43}), (31, {6, 16}), (34, {6, 43}), (35, {31}), (37, {16, 48}), 
      (45, {15, 48})}
  | 14 => {(1, {1, 6}), (4, {1, 48}), (5, {1, 18}), (15, {6, 33}), (19, {15, 16, 31}), 
      (22, {18, 31}), (24, {16, 33}), (25, {16, 31, 43}), (27, {15, 18, 33}), (29, {34}), 
      (31, {6, 16}), (34, {6, 43}), (37, {16, 48}), (41, {31, 43, 48}), (45, {15, 48}), 
      (47, {6, 31, 48})}
  | 21 => {(1, {1, 6}), (4, {1, 48}), (7, {1, 15, 43}), (11, {1, 18}), (21, {33}), (29, {34}), 
      (31, {6, 16}), (34, {6, 43}), (35, {31}), (45, {15, 48})}
  | 28 => {(1, {1, 6}), (4, {1, 48}), (5, {1, 18}), (15, {6, 33}), (19, {15, 16, 31}), 
      (22, {18, 31}), (24, {16, 33}), (25, {16, 31, 43}), (27, {15, 18, 33}), (29, {34}), 
      (31, {6, 16}), (34, {6, 43}), (37, {16, 48}), (41, {31, 43, 48}), (45, {15, 48}), 
      (47, {6, 31, 48})}
  | 35 => {(1, {1, 6}), (4, {1, 48}), (5, {1, 18}), (7, {1, 15, 43}), (21, {33}), (29, {34}), 
      (34, {6, 43}), (35, {31}), (37, {16, 48})}
  | 42 => {(1, {1, 6}), (4, {1, 48}), (5, {1, 18}), (15, {6, 33}), (19, {15, 16, 31}), 
      (22, {18, 31}), (24, {16, 33}), (25, {16, 31, 43}), (27, {15, 18, 33}), (29, {34}), 
      (31, {6, 16}), (34, {6, 43}), (37, {16, 48}), (41, {31, 43, 48}), (45, {15, 48}), 
      (47, {6, 31, 48})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_8` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q8 :
    ∀ T ∈ (lifts98 {1, 6, 15, 16, 18}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ8 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ8_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ8 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {1, 6, 15, 16, 18}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_8 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {1, 6, 15, 16, 18}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {1, 6, 15, 16, 18}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {1, 6, 15, 16, 18}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q8 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ8_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_9 = {1, 8, 10, 17, 18}`, lifts [1, 8, 10, 17, 18, 31, 32, 39, 41, 48]. -/
private def uTabQ9 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(21, {})}
  | 14 => {(1, {1, 8, 10}), (2, {1, 48}), (3, {1, 31, 32}), (9, {1, 10, 32}), 
      (13, {1, 8, 31}), (15, {32, 39}), (18, {17, 32}), (19, {10, 31, 41}), (20, {10, 39}), 
      (23, {8, 17}), (24, {8, 41}), (25, {8, 31, 39}), (27, {18}), (29, {10, 17, 41}), 
      (31, {32, 41}), (37, {8, 32, 48}), (39, {10, 48}), (45, {39, 48}), (47, {31, 48})}
  | 21 => {(21, {})}
  | 28 => {(1, {1, 8, 10}), (2, {1, 48}), (3, {1, 31, 32}), (9, {1, 10, 32}), 
      (13, {1, 8, 31}), (15, {32, 39}), (18, {17, 32}), (19, {10, 31, 41}), (20, {10, 39}), 
      (23, {8, 17}), (24, {8, 41}), (25, {8, 31, 39}), (27, {18}), (29, {10, 17, 41}), 
      (31, {32, 41}), (37, {8, 32, 48}), (39, {10, 48}), (45, {39, 48}), (47, {31, 48})}
  | 35 => {(21, {})}
  | 42 => {(1, {1, 8, 10}), (2, {1, 48}), (3, {1, 31, 32}), (9, {1, 10, 32}), 
      (13, {1, 8, 31}), (15, {32, 39}), (18, {17, 32}), (19, {10, 31, 41}), (20, {10, 39}), 
      (23, {8, 17}), (24, {8, 41}), (25, {8, 31, 39}), (27, {18}), (29, {10, 17, 41}), 
      (31, {32, 41}), (37, {8, 32, 48}), (39, {10, 48}), (45, {39, 48}), (47, {31, 48})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_9` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q9 :
    ∀ T ∈ (lifts98 {1, 8, 10, 17, 18}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ9 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ9_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ9 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {1, 8, 10, 17, 18}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_9 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {1, 8, 10, 17, 18}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {1, 8, 10, 17, 18}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {1, 8, 10, 17, 18}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q9 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ9_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_10 = {1, 8, 17, 18, 20}`, lifts [1, 8, 17, 18, 20, 29, 31, 32, 41, 48]. -/
private def uTabQ10 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(21, {})}
  | 14 => {(1, {1, 8}), (9, {1, 32}), (15, {20, 32}), (18, {17, 32}), (19, {20, 31, 41}), 
      (20, {20, 29}), (23, {8, 17}), (25, {8, 20, 31}), (26, {8, 41}), (29, {17, 20, 41}), 
      (31, {32, 41}), (33, {18}), (45, {48})}
  | 21 => {(21, {})}
  | 28 => {(1, {1, 8}), (9, {1, 32}), (15, {20, 32}), (18, {17, 32}), (19, {20, 31, 41}), 
      (20, {20, 29}), (23, {8, 17}), (25, {8, 20, 31}), (26, {8, 41}), (29, {17, 20, 41}), 
      (31, {32, 41}), (33, {18}), (45, {48})}
  | 35 => {(21, {})}
  | 42 => {(1, {1, 8}), (9, {1, 32}), (15, {20, 32}), (18, {17, 32}), (19, {20, 31, 41}), 
      (20, {20, 29}), (23, {8, 17}), (25, {8, 20, 31}), (26, {8, 41}), (29, {17, 20, 41}), 
      (31, {32, 41}), (33, {18}), (45, {48})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_10` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q10 :
    ∀ T ∈ (lifts98 {1, 8, 17, 18, 20}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ10 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ10_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ10 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {1, 8, 17, 18, 20}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_10 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {1, 8, 17, 18, 20}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {1, 8, 17, 18, 20}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {1, 8, 17, 18, 20}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q10 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ10_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_11 = {1, 9, 10, 16, 19}`, lifts [1, 9, 10, 16, 19, 30, 33, 39, 40, 48]. -/
private def uTabQ11 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(7, {1}), (16, {19, 30}), (17, {40}), (18, {16, 33}), (19, {10, 16}), 
      (21, {9, 19, 33}), (23, {9, 30}), (31, {16, 19}), (35, {39}), (47, {19, 48})}
  | 14 => {(1, {1, 9, 10}), (2, {1, 48}), (3, {1, 30, 33}), (9, {1, 10, 33}), 
      (13, {1, 16, 30}), (16, {19, 30}), (17, {40}), (18, {16, 33}), (19, {10, 16}), 
      (23, {9, 30}), (25, {16, 39}), (29, {10, 30}), (31, {16, 19}), (38, {10, 39}), 
      (41, {19, 48}), (45, {9, 39, 48})}
  | 21 => {(7, {1}), (16, {19, 30}), (17, {40}), (18, {16, 33}), (21, {9, 19, 33}), 
      (29, {10, 30}), (31, {16, 19}), (35, {39}), (41, {19, 48})}
  | 28 => {(1, {1, 9, 10}), (2, {1, 48}), (3, {1, 30, 33}), (9, {1, 10, 33}), 
      (13, {1, 16, 30}), (16, {19, 30}), (17, {40}), (18, {16, 33}), (19, {10, 16}), 
      (23, {9, 30}), (25, {16, 39}), (29, {10, 30}), (31, {16, 19}), (38, {10, 39}), 
      (41, {19, 48}), (45, {9, 39, 48})}
  | 35 => {(7, {1}), (16, {19, 30}), (18, {16, 33}), (19, {10, 16}), (21, {9, 19, 33}), 
      (22, {9, 40}), (23, {9, 30}), (27, {33, 40}), (29, {10, 30}), (35, {39}), 
      (37, {16, 40, 48}), (41, {19, 48})}
  | 42 => {(1, {1, 9, 10}), (2, {1, 48}), (3, {1, 30, 33}), (9, {1, 10, 33}), 
      (13, {1, 16, 30}), (16, {19, 30}), (17, {40}), (18, {16, 33}), (19, {10, 16}), 
      (23, {9, 30}), (25, {16, 39}), (29, {10, 30}), (31, {16, 19}), (38, {10, 39}), 
      (41, {19, 48}), (45, {9, 39, 48})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_11` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q11 :
    ∀ T ∈ (lifts98 {1, 9, 10, 16, 19}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ11 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ11_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ11 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {1, 9, 10, 16, 19}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_11 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {1, 9, 10, 16, 19}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {1, 9, 10, 16, 19}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {1, 9, 10, 16, 19}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q11 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ11_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_12 = {1, 11, 12, 13, 20}`, lifts [1, 11, 12, 13, 20, 29, 36, 37, 38, 48]. -/
private def uTabQ12 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(2, {1, 48}), (7, {1, 13, 29}), (11, {1, 36}), (20, {20, 29}), (21, {37}), 
      (22, {13, 36}), (23, {13, 38}), (25, {12, 20}), (33, {12, 36}), (35, {11}), 
      (39, {20, 38, 48}), (47, {29, 48})}
  | 14 => {(9, {1, 11, 12}), (11, {1, 36}), (13, {1, 37, 38}), (15, {13, 20}), 
      (17, {11, 12, 29}), (18, {11, 38}), (19, {11, 20, 36}), (20, {20, 29}), (22, {13, 36}), 
      (23, {13, 38}), (25, {12, 20}), (27, {11, 29, 36}), (29, {20, 37}), (32, {12, 37}), 
      (33, {12, 36}), (43, {48})}
  | 21 => {(7, {1, 13, 29}), (11, {1, 36}), (15, {13, 20}), (20, {20, 29}), (21, {37}), 
      (22, {13, 36}), (25, {12, 20}), (31, {13, 38}), (35, {11}), (43, {48})}
  | 28 => {(9, {1, 11, 12}), (11, {1, 36}), (13, {1, 37, 38}), (15, {13, 20}), 
      (17, {11, 12, 29}), (18, {11, 38}), (19, {11, 20, 36}), (20, {20, 29}), (22, {13, 36}), 
      (23, {13, 38}), (25, {12, 20}), (27, {11, 29, 36}), (29, {20, 37}), (32, {12, 37}), 
      (33, {12, 36}), (43, {48})}
  | 35 => {(7, {1, 13, 29}), (15, {13, 20}), (20, {20, 29}), (21, {37}), (22, {13, 36}), 
      (23, {13, 38}), (33, {12, 36}), (35, {11}), (43, {48})}
  | 42 => {(9, {1, 11, 12}), (11, {1, 36}), (13, {1, 37, 38}), (15, {13, 20}), 
      (17, {11, 12, 29}), (18, {11, 38}), (19, {11, 20, 36}), (20, {20, 29}), (22, {13, 36}), 
      (23, {13, 38}), (25, {12, 20}), (27, {11, 29, 36}), (29, {20, 37}), (32, {12, 37}), 
      (33, {12, 36}), (43, {48})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_12` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q12 :
    ∀ T ∈ (lifts98 {1, 11, 12, 13, 20}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ12 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ12_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ12 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {1, 11, 12, 13, 20}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_12 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {1, 11, 12, 13, 20}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {1, 11, 12, 13, 20}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {1, 11, 12, 13, 20}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q12 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ12_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_13 = {1, 12, 15, 22, 23}`, lifts [1, 12, 15, 22, 23, 26, 27, 34, 37, 48]. -/
private def uTabQ13 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(35, {})}
  | 14 => {(1, {1, 12}), (2, {1, 48}), (3, {1, 34, 37}), (15, {26, 27}), (16, {12, 37}), 
      (17, {12, 23, 34}), (19, {15, 26}), (20, {15, 34}), (23, {26, 34}), (25, {12, 23, 27}), 
      (29, {27, 34, 37}), (30, {23, 26}), (31, {22}), (33, {12, 15, 27}), (37, {37, 48}), 
      (39, {15, 48}), (41, {12, 26, 48}), (43, {23, 34, 48}), (47, {23, 27, 48})}
  | 21 => {(35, {})}
  | 28 => {(1, {1, 12}), (2, {1, 48}), (3, {1, 34, 37}), (15, {26, 27}), (16, {12, 37}), 
      (17, {12, 23, 34}), (19, {15, 26}), (20, {15, 34}), (23, {26, 34}), (25, {12, 23, 27}), 
      (29, {27, 34, 37}), (30, {23, 26}), (31, {22}), (33, {12, 15, 27}), (37, {37, 48}), 
      (39, {15, 48}), (41, {12, 26, 48}), (43, {23, 34, 48}), (47, {23, 27, 48})}
  | 35 => {(35, {})}
  | 42 => {(1, {1, 12}), (2, {1, 48}), (3, {1, 34, 37}), (15, {26, 27}), (16, {12, 37}), 
      (17, {12, 23, 34}), (19, {15, 26}), (20, {15, 34}), (23, {26, 34}), (25, {12, 23, 27}), 
      (29, {27, 34, 37}), (30, {23, 26}), (31, {22}), (33, {12, 15, 27}), (37, {37, 48}), 
      (39, {15, 48}), (41, {12, 26, 48}), (43, {23, 34, 48}), (47, {23, 27, 48})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_13` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q13 :
    ∀ T ∈ (lifts98 {1, 12, 15, 22, 23}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ13 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ13_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ13 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {1, 12, 15, 22, 23}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_13 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {1, 12, 15, 22, 23}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {1, 12, 15, 22, 23}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {1, 12, 15, 22, 23}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q13 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ13_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_14 = {1, 12, 19, 22, 23}`, lifts [1, 12, 19, 22, 23, 26, 27, 30, 37, 48]. -/
private def uTabQ14 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(35, {})}
  | 14 => {(1, {1, 12}), (2, {1, 48}), (3, {1, 30, 37}), (17, {12, 23}), (19, {26}), 
      (20, {19, 30}), (24, {12, 37}), (27, {22}), (29, {27, 30, 37}), (33, {12, 27, 30}), 
      (37, {37, 48}), (39, {30, 48}), (43, {23, 48})}
  | 21 => {(35, {})}
  | 28 => {(1, {1, 12}), (2, {1, 48}), (3, {1, 30, 37}), (17, {12, 23}), (19, {26}), 
      (20, {19, 30}), (24, {12, 37}), (27, {22}), (29, {27, 30, 37}), (33, {12, 27, 30}), 
      (37, {37, 48}), (39, {30, 48}), (43, {23, 48})}
  | 35 => {(35, {})}
  | 42 => {(1, {1, 12}), (2, {1, 48}), (3, {1, 30, 37}), (17, {12, 23}), (19, {26}), 
      (20, {19, 30}), (24, {12, 37}), (27, {22}), (29, {27, 30, 37}), (33, {12, 27, 30}), 
      (37, {37, 48}), (39, {30, 48}), (43, {23, 48})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_14` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q14 :
    ∀ T ∈ (lifts98 {1, 12, 19, 22, 23}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ14 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ14_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ14 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {1, 12, 19, 22, 23}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_14 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {1, 12, 19, 22, 23}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {1, 12, 19, 22, 23}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {1, 12, 19, 22, 23}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q14 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ14_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_15 = {2, 3, 5, 11, 24}`, lifts [2, 3, 5, 11, 24, 25, 38, 44, 46, 47]. -/
private def uTabQ15 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(7, {})}
  | 14 => {(3, {2, 3}), (5, {2, 38}), (6, {2, 47}), (10, {11, 38}), (11, {44}), 
      (12, {24, 25}), (15, {46}), (23, {25, 38, 47}), (25, {24, 47}), (33, {3, 24}), 
      (39, {5, 25, 38}), (41, {5, 24, 38}), (43, {2, 25})}
  | 21 => {(7, {})}
  | 28 => {(3, {2, 3}), (5, {2, 38}), (6, {2, 47}), (10, {11, 38}), (11, {44}), 
      (12, {24, 25}), (15, {46}), (23, {25, 38, 47}), (25, {24, 47}), (33, {3, 24}), 
      (39, {5, 25, 38}), (41, {5, 24, 38}), (43, {2, 25})}
  | 35 => {(7, {})}
  | 42 => {(3, {2, 3}), (5, {2, 38}), (6, {2, 47}), (10, {11, 38}), (11, {44}), 
      (12, {24, 25}), (15, {46}), (23, {25, 38, 47}), (25, {24, 47}), (33, {3, 24}), 
      (39, {5, 25, 38}), (41, {5, 24, 38}), (43, {2, 25})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_15` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q15 :
    ∀ T ∈ (lifts98 {2, 3, 5, 11, 24}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ15 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ15_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ15 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {2, 3, 5, 11, 24}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_15 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {2, 3, 5, 11, 24}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {2, 3, 5, 11, 24}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {2, 3, 5, 11, 24}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q15 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ15_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_16 = {2, 3, 5, 19, 24}`, lifts [2, 3, 5, 19, 24, 25, 30, 44, 46, 47]. -/
private def uTabQ16 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(7, {})}
  | 14 => {(1, {2, 3, 5}), (3, {2, 3, 30}), (5, {2, 19}), (6, {2, 47}), (8, {24, 25}), 
      (9, {44}), (10, {19, 30}), (13, {30, 46}), (15, {19, 46}), (17, {5, 46}), 
      (23, {25, 30, 47}), (25, {24, 47}), (30, {3, 46}), (33, {3, 24, 30}), (37, {3, 5, 24}), 
      (39, {5, 25, 30}), (41, {5, 19, 24}), (43, {2, 25}), (45, {2, 24, 46})}
  | 21 => {(7, {})}
  | 28 => {(1, {2, 3, 5}), (3, {2, 3, 30}), (5, {2, 19}), (6, {2, 47}), (8, {24, 25}), 
      (9, {44}), (10, {19, 30}), (13, {30, 46}), (15, {19, 46}), (17, {5, 46}), 
      (23, {25, 30, 47}), (25, {24, 47}), (30, {3, 46}), (33, {3, 24, 30}), (37, {3, 5, 24}), 
      (39, {5, 25, 30}), (41, {5, 19, 24}), (43, {2, 25}), (45, {2, 24, 46})}
  | 35 => {(7, {})}
  | 42 => {(1, {2, 3, 5}), (3, {2, 3, 30}), (5, {2, 19}), (6, {2, 47}), (8, {24, 25}), 
      (9, {44}), (10, {19, 30}), (13, {30, 46}), (15, {19, 46}), (17, {5, 46}), 
      (23, {25, 30, 47}), (25, {24, 47}), (30, {3, 46}), (33, {3, 24, 30}), (37, {3, 5, 24}), 
      (39, {5, 25, 30}), (41, {5, 19, 24}), (43, {2, 25}), (45, {2, 24, 46})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_16` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q16 :
    ∀ T ∈ (lifts98 {2, 3, 5, 19, 24}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ16 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ16_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ16 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {2, 3, 5, 19, 24}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_16 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {2, 3, 5, 19, 24}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {2, 3, 5, 19, 24}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {2, 3, 5, 19, 24}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q16 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ16_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_17 = {2, 5, 6, 11, 16}`, lifts [2, 5, 6, 11, 16, 33, 38, 43, 44, 47]. -/
private def uTabQ17 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(3, {2, 33}), (4, {2, 47}), (5, {2, 38}), (7, {43}), (11, {44}), (12, {16, 33}), 
      (21, {5, 33, 47}), (33, {6, 33}), (35, {11}), (37, {5, 16})}
  | 14 => {(3, {2, 33}), (4, {2, 47}), (5, {2, 38}), (8, {11, 38}), (11, {44}), 
      (12, {16, 33}), (13, {16, 38}), (15, {6, 33}), (16, {6, 43}), (17, {5, 6, 11}), 
      (23, {38, 43, 47}), (25, {16, 43, 47}), (37, {5, 16}), (41, {5, 38, 43}), 
      (43, {2, 16, 43}), (45, {2, 11})}
  | 21 => {(3, {2, 33}), (4, {2, 47}), (7, {43}), (11, {44}), (12, {16, 33}), (13, {16, 38}), 
      (15, {6, 33}), (21, {5, 33, 47}), (35, {11})}
  | 28 => {(3, {2, 33}), (4, {2, 47}), (5, {2, 38}), (8, {11, 38}), (11, {44}), 
      (12, {16, 33}), (13, {16, 38}), (15, {6, 33}), (16, {6, 43}), (17, {5, 6, 11}), 
      (23, {38, 43, 47}), (25, {16, 43, 47}), (37, {5, 16}), (41, {5, 38, 43}), 
      (43, {2, 16, 43}), (45, {2, 11})}
  | 35 => {(4, {2, 47}), (5, {2, 38}), (7, {43}), (12, {16, 33}), (13, {16, 38}), 
      (15, {6, 33}), (20, {5, 44}), (21, {5, 33, 47}), (29, {44, 47}), (35, {11}), 
      (37, {5, 16}), (47, {2, 6, 44})}
  | 42 => {(3, {2, 33}), (4, {2, 47}), (5, {2, 38}), (8, {11, 38}), (11, {44}), 
      (12, {16, 33}), (13, {16, 38}), (15, {6, 33}), (16, {6, 43}), (17, {5, 6, 11}), 
      (23, {38, 43, 47}), (25, {16, 43, 47}), (37, {5, 16}), (41, {5, 38, 43}), 
      (43, {2, 16, 43}), (45, {2, 11})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_17` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q17 :
    ∀ T ∈ (lifts98 {2, 5, 6, 11, 16}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ17 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ17_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ17 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {2, 5, 6, 11, 16}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_17 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {2, 5, 6, 11, 16}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {2, 5, 6, 11, 16}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {2, 5, 6, 11, 16}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q17 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ17_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_18 = {2, 5, 8, 9, 13}`, lifts [2, 5, 8, 9, 13, 36, 40, 41, 44, 47]. -/
private def uTabQ18 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(35, {})}
  | 14 => {(3, {2, 36}), (4, {2, 47}), (5, {2, 40, 41}), (8, {13, 36}), (9, {44}), 
      (10, {9, 40}), (13, {8}), (15, {13, 40}), (33, {9, 36}), (39, {5, 40}), (41, {5, 36}), 
      (43, {2, 9, 41}), (45, {2, 9, 13})}
  | 21 => {(35, {})}
  | 28 => {(3, {2, 36}), (4, {2, 47}), (5, {2, 40, 41}), (8, {13, 36}), (9, {44}), 
      (10, {9, 40}), (13, {8}), (15, {13, 40}), (33, {9, 36}), (39, {5, 40}), (41, {5, 36}), 
      (43, {2, 9, 41}), (45, {2, 9, 13})}
  | 35 => {(35, {})}
  | 42 => {(3, {2, 36}), (4, {2, 47}), (5, {2, 40, 41}), (8, {13, 36}), (9, {44}), 
      (10, {9, 40}), (13, {8}), (15, {13, 40}), (33, {9, 36}), (39, {5, 40}), (41, {5, 36}), 
      (43, {2, 9, 41}), (45, {2, 9, 13})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_18` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q18 :
    ∀ T ∈ (lifts98 {2, 5, 8, 9, 13}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ18 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ18_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ18 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {2, 5, 8, 9, 13}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_18 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {2, 5, 8, 9, 13}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {2, 5, 8, 9, 13}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {2, 5, 8, 9, 13}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q18 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ18_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_19 = {2, 5, 8, 12, 20}`, lifts [2, 5, 8, 12, 20, 29, 37, 41, 44, 47]. -/
private def uTabQ19 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(35, {})}
  | 14 => {(4, {2, 47}), (11, {8, 44}), (12, {8, 41}), (13, {8, 37}), (15, {20}), 
      (18, {5, 44}), (23, {8, 47}), (27, {29, 44, 47}), (31, {41, 44, 47}), (33, {12}), 
      (43, {2, 41}), (45, {2, 37}), (47, {2, 29, 44})}
  | 21 => {(35, {})}
  | 28 => {(4, {2, 47}), (11, {8, 44}), (12, {8, 41}), (13, {8, 37}), (15, {20}), 
      (18, {5, 44}), (23, {8, 47}), (27, {29, 44, 47}), (31, {41, 44, 47}), (33, {12}), 
      (43, {2, 41}), (45, {2, 37}), (47, {2, 29, 44})}
  | 35 => {(35, {})}
  | 42 => {(4, {2, 47}), (11, {8, 44}), (12, {8, 41}), (13, {8, 37}), (15, {20}), 
      (18, {5, 44}), (23, {8, 47}), (27, {29, 44, 47}), (31, {41, 44, 47}), (33, {12}), 
      (43, {2, 41}), (45, {2, 37}), (47, {2, 29, 44})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_19` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q19 :
    ∀ T ∈ (lifts98 {2, 5, 8, 12, 20}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ19 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ19_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ19 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {2, 5, 8, 12, 20}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_19 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {2, 5, 8, 12, 20}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {2, 5, 8, 12, 20}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {2, 5, 8, 12, 20}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q19 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ19_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_20 = {2, 6, 8, 10, 13}`, lifts [2, 6, 8, 10, 13, 36, 39, 41, 43, 47]. -/
private def uTabQ20 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(3, {2, 36}), (7, {13, 41, 43}), (8, {13, 36}), (9, {10, 43}), (11, {8, 10, 36}), 
      (12, {8, 41}), (17, {6, 41}), (18, {6, 43}), (21, {47}), (35, {39}), (37, {8, 13}), 
      (47, {2, 6})}
  | 14 => {(3, {2, 36}), (4, {2, 47}), (5, {2, 39, 41}), (8, {13, 36}), (9, {10, 43}), 
      (10, {10, 39}), (13, {8}), (15, {6, 13, 39}), (17, {6, 41}), (18, {6, 43}), 
      (27, {36, 47}), (29, {10, 41, 47}), (33, {6, 36, 39}), (41, {36, 43}), 
      (45, {2, 13, 39}), (47, {2, 6})}
  | 21 => {(3, {2, 36}), (7, {13, 41, 43}), (8, {13, 36}), (13, {8}), (17, {6, 41}), 
      (18, {6, 43}), (21, {47}), (35, {39}), (39, {10, 43}), (41, {36, 43})}
  | 28 => {(3, {2, 36}), (4, {2, 47}), (5, {2, 39, 41}), (8, {13, 36}), (9, {10, 43}), 
      (10, {10, 39}), (13, {8}), (15, {6, 13, 39}), (17, {6, 41}), (18, {6, 43}), 
      (27, {36, 47}), (29, {10, 41, 47}), (33, {6, 36, 39}), (41, {36, 43}), 
      (45, {2, 13, 39}), (47, {2, 6})}
  | 35 => {(7, {13, 41, 43}), (8, {13, 36}), (9, {10, 43}), (13, {8}), (18, {6, 43}), 
      (21, {47}), (35, {39}), (41, {36, 43}), (47, {2, 6})}
  | 42 => {(3, {2, 36}), (4, {2, 47}), (5, {2, 39, 41}), (8, {13, 36}), (9, {10, 43}), 
      (10, {10, 39}), (13, {8}), (15, {6, 13, 39}), (17, {6, 41}), (18, {6, 43}), 
      (27, {36, 47}), (29, {10, 41, 47}), (33, {6, 36, 39}), (41, {36, 43}), 
      (45, {2, 13, 39}), (47, {2, 6})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_20` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q20 :
    ∀ T ∈ (lifts98 {2, 6, 8, 10, 13}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ20 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ20_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ20 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {2, 6, 8, 10, 13}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_20 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {2, 6, 8, 10, 13}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {2, 6, 8, 10, 13}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {2, 6, 8, 10, 13}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q20 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ20_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_21 = {2, 8, 12, 20, 22}`, lifts [2, 8, 12, 20, 22, 27, 29, 37, 41, 47]. -/
private def uTabQ21 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(35, {})}
  | 14 => {(1, {2, 8, 12}), (2, {2, 47}), (3, {2, 29, 37}), (8, {12, 37}), (9, {12, 22}), 
      (11, {8, 27}), (12, {8, 41}), (13, {8, 22, 37}), (18, {22, 27}), (23, {8, 47}), 
      (27, {22, 29, 47}), (31, {22, 41, 47}), (33, {12, 27}), (37, {8, 29, 37}), (39, {20}), 
      (41, {12, 29}), (43, {2, 41}), (45, {2, 22, 37}), (47, {2, 27, 29})}
  | 21 => {(35, {})}
  | 28 => {(1, {2, 8, 12}), (2, {2, 47}), (3, {2, 29, 37}), (8, {12, 37}), (9, {12, 22}), 
      (11, {8, 27}), (12, {8, 41}), (13, {8, 22, 37}), (18, {22, 27}), (23, {8, 47}), 
      (27, {22, 29, 47}), (31, {22, 41, 47}), (33, {12, 27}), (37, {8, 29, 37}), (39, {20}), 
      (41, {12, 29}), (43, {2, 41}), (45, {2, 22, 37}), (47, {2, 27, 29})}
  | 35 => {(35, {})}
  | 42 => {(1, {2, 8, 12}), (2, {2, 47}), (3, {2, 29, 37}), (8, {12, 37}), (9, {12, 22}), 
      (11, {8, 27}), (12, {8, 41}), (13, {8, 22, 37}), (18, {22, 27}), (23, {8, 47}), 
      (27, {22, 29, 47}), (31, {22, 41, 47}), (33, {12, 27}), (37, {8, 29, 37}), (39, {20}), 
      (41, {12, 29}), (43, {2, 41}), (45, {2, 22, 37}), (47, {2, 27, 29})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_21` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q21 :
    ∀ T ∈ (lifts98 {2, 8, 12, 20, 22}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ21 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ21_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ21 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {2, 8, 12, 20, 22}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_21 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {2, 8, 12, 20, 22}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {2, 8, 12, 20, 22}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {2, 8, 12, 20, 22}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q21 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ21_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_22 = {2, 9, 10, 11, 12}`, lifts [2, 9, 10, 11, 12, 37, 38, 39, 40, 47]. -/
private def uTabQ22 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(7, {})}
  | 14 => {(9, {10, 11, 12}), (11, {9, 10}), (12, {9, 40}), (13, {37, 38}), (15, {39, 40}), 
      (16, {12, 37}), (17, {11, 12, 40}), (18, {11, 38}), (19, {10, 11, 47}), (20, {10, 39}), 
      (25, {12, 39, 47}), (27, {11, 40, 47}), (29, {10, 37, 47}), (31, {38, 47}), 
      (33, {9, 12, 39}), (37, {37, 40}), (39, {10, 38, 40}), (41, {12, 38}), (47, {2})}
  | 21 => {(7, {})}
  | 28 => {(9, {10, 11, 12}), (11, {9, 10}), (12, {9, 40}), (13, {37, 38}), (15, {39, 40}), 
      (16, {12, 37}), (17, {11, 12, 40}), (18, {11, 38}), (19, {10, 11, 47}), (20, {10, 39}), 
      (25, {12, 39, 47}), (27, {11, 40, 47}), (29, {10, 37, 47}), (31, {38, 47}), 
      (33, {9, 12, 39}), (37, {37, 40}), (39, {10, 38, 40}), (41, {12, 38}), (47, {2})}
  | 35 => {(7, {})}
  | 42 => {(9, {10, 11, 12}), (11, {9, 10}), (12, {9, 40}), (13, {37, 38}), (15, {39, 40}), 
      (16, {12, 37}), (17, {11, 12, 40}), (18, {11, 38}), (19, {10, 11, 47}), (20, {10, 39}), 
      (25, {12, 39, 47}), (27, {11, 40, 47}), (29, {10, 37, 47}), (31, {38, 47}), 
      (33, {9, 12, 39}), (37, {37, 40}), (39, {10, 38, 40}), (41, {12, 38}), (47, {2})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_22` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q22 :
    ∀ T ∈ (lifts98 {2, 9, 10, 11, 12}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ22 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ22_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ22 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {2, 9, 10, 11, 12}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_22 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {2, 9, 10, 11, 12}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {2, 9, 10, 11, 12}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {2, 9, 10, 11, 12}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q22 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ22_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_23 = {2, 9, 10, 11, 24}`, lifts [2, 9, 10, 11, 24, 25, 38, 39, 40, 47]. -/
private def uTabQ23 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(7, {})}
  | 14 => {(3, {2}), (9, {10, 11}), (11, {9, 10}), (13, {38}), (15, {39, 40}), (16, {24, 25}), 
      (17, {11, 40}), (22, {9, 40}), (25, {24, 39, 47}), (29, {10, 24, 47}), (30, {10, 39}), 
      (33, {9, 24, 39}), (37, {24, 40})}
  | 21 => {(7, {})}
  | 28 => {(3, {2}), (9, {10, 11}), (11, {9, 10}), (13, {38}), (15, {39, 40}), (16, {24, 25}), 
      (17, {11, 40}), (22, {9, 40}), (25, {24, 39, 47}), (29, {10, 24, 47}), (30, {10, 39}), 
      (33, {9, 24, 39}), (37, {24, 40})}
  | 35 => {(7, {})}
  | 42 => {(3, {2}), (9, {10, 11}), (11, {9, 10}), (13, {38}), (15, {39, 40}), (16, {24, 25}), 
      (17, {11, 40}), (22, {9, 40}), (25, {24, 39, 47}), (29, {10, 24, 47}), (30, {10, 39}), 
      (33, {9, 24, 39}), (37, {24, 40})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_23` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q23 :
    ∀ T ∈ (lifts98 {2, 9, 10, 11, 24}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ23 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ23_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ23 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {2, 9, 10, 11, 24}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_23 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {2, 9, 10, 11, 24}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {2, 9, 10, 11, 24}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {2, 9, 10, 11, 24}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q23 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ23_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_24 = {2, 9, 13, 15, 16}`, lifts [2, 9, 13, 15, 16, 33, 34, 36, 40, 47]. -/
private def uTabQ24 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(35, {})}
  | 14 => {(9, {33, 34}), (10, {9, 40}), (13, {15, 16}), (15, {13, 33, 40}), (17, {34, 40}), 
      (18, {16, 33}), (20, {15, 34}), (25, {16, 47}), (29, {34, 47}), (37, {13, 16, 40}), 
      (39, {15, 33, 40}), (41, {36}), (47, {2})}
  | 21 => {(35, {})}
  | 28 => {(9, {33, 34}), (10, {9, 40}), (13, {15, 16}), (15, {13, 33, 40}), (17, {34, 40}), 
      (18, {16, 33}), (20, {15, 34}), (25, {16, 47}), (29, {34, 47}), (37, {13, 16, 40}), 
      (39, {15, 33, 40}), (41, {36}), (47, {2})}
  | 35 => {(35, {})}
  | 42 => {(9, {33, 34}), (10, {9, 40}), (13, {15, 16}), (15, {13, 33, 40}), (17, {34, 40}), 
      (18, {16, 33}), (20, {15, 34}), (25, {16, 47}), (29, {34, 47}), (37, {13, 16, 40}), 
      (39, {15, 33, 40}), (41, {36}), (47, {2})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_24` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q24 :
    ∀ T ∈ (lifts98 {2, 9, 13, 15, 16}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ24 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ24_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ24 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {2, 9, 13, 15, 16}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_24 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {2, 9, 13, 15, 16}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {2, 9, 13, 15, 16}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {2, 9, 13, 15, 16}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q24 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ24_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_25 = {2, 9, 22, 23, 24}`, lifts [2, 9, 22, 23, 24, 25, 26, 27, 40, 47]. -/
private def uTabQ25 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(3, {2}), (7, {27}), (9, {22, 23}), (10, {9, 40}), (17, {23, 40}), (19, {26, 47}), 
      (21, {9, 23, 47}), (26, {23, 26}), (35, {25}), (37, {24, 40})}
  | 14 => {(3, {2}), (9, {22, 23}), (10, {9, 40}), (11, {9, 26, 27}), (15, {26, 27, 40}), 
      (16, {24, 25}), (17, {23, 40}), (18, {22, 27}), (19, {26, 47}), (26, {23, 26}), 
      (29, {24, 27, 47}), (31, {22, 25, 47}), (33, {9, 24, 27}), (37, {24, 40}), 
      (39, {25, 40}), (41, {24, 26})}
  | 21 => {(3, {2}), (7, {27}), (10, {9, 40}), (13, {22, 23}), (17, {23, 40}), 
      (21, {9, 23, 47}), (26, {23, 26}), (35, {25}), (41, {24, 26})}
  | 28 => {(3, {2}), (9, {22, 23}), (10, {9, 40}), (11, {9, 26, 27}), (15, {26, 27, 40}), 
      (16, {24, 25}), (17, {23, 40}), (18, {22, 27}), (19, {26, 47}), (26, {23, 26}), 
      (29, {24, 27, 47}), (31, {22, 25, 47}), (33, {9, 24, 27}), (37, {24, 40}), 
      (39, {25, 40}), (41, {24, 26})}
  | 35 => {(1, {2, 9}), (2, {2, 47}), (5, {2, 22, 40}), (7, {27}), (9, {22, 23}), 
      (10, {9, 40}), (19, {26, 47}), (21, {9, 23, 47}), (26, {23, 26}), (35, {25}), 
      (37, {24, 40}), (41, {24, 26})}
  | 42 => {(3, {2}), (9, {22, 23}), (10, {9, 40}), (11, {9, 26, 27}), (15, {26, 27, 40}), 
      (16, {24, 25}), (17, {23, 40}), (18, {22, 27}), (19, {26, 47}), (26, {23, 26}), 
      (29, {24, 27, 47}), (31, {22, 25, 47}), (33, {9, 24, 27}), (37, {24, 40}), 
      (39, {25, 40}), (41, {24, 26})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_25` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q25 :
    ∀ T ∈ (lifts98 {2, 9, 22, 23, 24}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ25 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ25_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ25 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {2, 9, 22, 23, 24}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_25 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {2, 9, 22, 23, 24}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {2, 9, 22, 23, 24}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {2, 9, 22, 23, 24}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q25 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ25_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_26 = {2, 10, 16, 18, 23}`, lifts [2, 10, 16, 18, 23, 26, 31, 33, 39, 47]. -/
private def uTabQ26 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(7, {})}
  | 14 => {(1, {2, 10}), (2, {2, 47}), (3, {2, 31, 33}), (5, {2, 18, 39}), (8, {23, 26}), 
      (10, {10, 39}), (11, {10, 18, 26}), (15, {26, 33, 39}), (16, {18, 31}), (17, {18, 23}), 
      (23, {26, 47}), (27, {18, 33, 47}), (29, {10, 47}), (33, {18, 33, 39}), (37, {16}), 
      (39, {10, 33}), (41, {26, 31}), (45, {2, 26, 39}), (47, {2, 23, 31})}
  | 21 => {(7, {})}
  | 28 => {(1, {2, 10}), (2, {2, 47}), (3, {2, 31, 33}), (5, {2, 18, 39}), (8, {23, 26}), 
      (10, {10, 39}), (11, {10, 18, 26}), (15, {26, 33, 39}), (16, {18, 31}), (17, {18, 23}), 
      (23, {26, 47}), (27, {18, 33, 47}), (29, {10, 47}), (33, {18, 33, 39}), (37, {16}), 
      (39, {10, 33}), (41, {26, 31}), (45, {2, 26, 39}), (47, {2, 23, 31})}
  | 35 => {(7, {})}
  | 42 => {(1, {2, 10}), (2, {2, 47}), (3, {2, 31, 33}), (5, {2, 18, 39}), (8, {23, 26}), 
      (10, {10, 39}), (11, {10, 18, 26}), (15, {26, 33, 39}), (16, {18, 31}), (17, {18, 23}), 
      (23, {26, 47}), (27, {18, 33, 47}), (29, {10, 47}), (33, {18, 33, 39}), (37, {16}), 
      (39, {10, 33}), (41, {26, 31}), (45, {2, 26, 39}), (47, {2, 23, 31})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_26` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q26 :
    ∀ T ∈ (lifts98 {2, 10, 16, 18, 23}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ26 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ26_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ26 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {2, 10, 16, 18, 23}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_26 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {2, 10, 16, 18, 23}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {2, 10, 16, 18, 23}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {2, 10, 16, 18, 23}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q26 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ26_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_27 = {2, 11, 17, 18, 20}`, lifts [2, 11, 17, 18, 20, 29, 31, 32, 38, 47]. -/
private def uTabQ27 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(7, {29}), (8, {11, 38}), (9, {11, 32}), (12, {17, 32}), (21, {47}), (33, {18}), 
      (35, {11, 17, 31}), (39, {20, 38}), (45, {2, 11})}
  | 14 => {(1, {2, 11}), (2, {2, 47}), (8, {11, 38}), (9, {11, 32}), (12, {17, 32}), 
      (13, {31, 38}), (15, {20, 32}), (20, {20, 29}), (23, {17, 38, 47}), (25, {20, 31, 47}), 
      (29, {17, 20, 47}), (31, {32, 38, 47}), (33, {18}), (37, {29, 32}), (39, {20, 38}), 
      (47, {2, 29, 31})}
  | 21 => {(1, {2, 11}), (7, {29}), (8, {11, 38}), (11, {17, 18}), (12, {17, 32}), 
      (13, {31, 38}), (15, {20, 32}), (16, {18, 31}), (21, {47}), (35, {11, 17, 31}), 
      (39, {20, 38}), (43, {2, 18, 32})}
  | 28 => {(1, {2, 11}), (2, {2, 47}), (8, {11, 38}), (9, {11, 32}), (12, {17, 32}), 
      (13, {31, 38}), (15, {20, 32}), (20, {20, 29}), (23, {17, 38, 47}), (25, {20, 31, 47}), 
      (29, {17, 20, 47}), (31, {32, 38, 47}), (33, {18}), (37, {29, 32}), (39, {20, 38}), 
      (47, {2, 29, 31})}
  | 35 => {(1, {2, 11}), (7, {29}), (8, {11, 38}), (9, {11, 32}), (12, {17, 32}), 
      (13, {31, 38}), (15, {20, 32}), (21, {47}), (33, {18}), (35, {11, 17, 31})}
  | 42 => {(1, {2, 11}), (2, {2, 47}), (8, {11, 38}), (9, {11, 32}), (12, {17, 32}), 
      (13, {31, 38}), (15, {20, 32}), (20, {20, 29}), (23, {17, 38, 47}), (25, {20, 31, 47}), 
      (29, {17, 20, 47}), (31, {32, 38, 47}), (33, {18}), (37, {29, 32}), (39, {20, 38}), 
      (47, {2, 29, 31})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_27` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q27 :
    ∀ T ∈ (lifts98 {2, 11, 17, 18, 20}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ27 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ27_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ27 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {2, 11, 17, 18, 20}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_27 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {2, 11, 17, 18, 20}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {2, 11, 17, 18, 20}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {2, 11, 17, 18, 20}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q27 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ27_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_28 = {2, 12, 13, 17, 19}`, lifts [2, 12, 13, 17, 19, 30, 32, 36, 37, 47]. -/
private def uTabQ28 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(2, {2, 47}), (7, {13}), (9, {12, 32}), (19, {36, 47}), (21, {19, 37, 47}), 
      (24, {12, 37}), (25, {12, 47}), (35, {17}), (39, {30}), (47, {2, 19})}
  | 14 => {(1, {2, 12, 13}), (2, {2, 47}), (9, {12, 32}), (11, {17, 19, 36}), (12, {17, 32}), 
      (15, {13, 19, 32}), (17, {12, 17}), (19, {36, 47}), (22, {13, 36}), (24, {12, 37}), 
      (25, {12, 47}), (37, {13, 32, 37}), (39, {30}), (43, {2, 32}), (45, {2, 13, 37}), 
      (47, {2, 19})}
  | 21 => {(2, {2, 47}), (7, {13}), (21, {19, 37, 47}), (24, {12, 37}), (25, {12, 47}), 
      (27, {36, 47}), (35, {17}), (39, {30}), (43, {2, 32})}
  | 28 => {(1, {2, 12, 13}), (2, {2, 47}), (9, {12, 32}), (11, {17, 19, 36}), (12, {17, 32}), 
      (15, {13, 19, 32}), (17, {12, 17}), (19, {36, 47}), (22, {13, 36}), (24, {12, 37}), 
      (25, {12, 47}), (37, {13, 32, 37}), (39, {30}), (43, {2, 32}), (45, {2, 13, 37}), 
      (47, {2, 19})}
  | 35 => {(2, {2, 47}), (7, {13}), (9, {12, 32}), (10, {19, 30}), (13, {30, 37}), 
      (19, {36, 47}), (21, {19, 37, 47}), (24, {12, 37}), (33, {12, 30, 36}), (35, {17}), 
      (43, {2, 32}), (47, {2, 19})}
  | 42 => {(1, {2, 12, 13}), (2, {2, 47}), (9, {12, 32}), (11, {17, 19, 36}), (12, {17, 32}), 
      (15, {13, 19, 32}), (17, {12, 17}), (19, {36, 47}), (22, {13, 36}), (24, {12, 37}), 
      (25, {12, 47}), (37, {13, 32, 37}), (39, {30}), (43, {2, 32}), (45, {2, 13, 37}), 
      (47, {2, 19})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_28` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q28 :
    ∀ T ∈ (lifts98 {2, 12, 13, 17, 19}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ28 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ28_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ28 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {2, 12, 13, 17, 19}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_28 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {2, 12, 13, 17, 19}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {2, 12, 13, 17, 19}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {2, 12, 13, 17, 19}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q28 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ28_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_29 = {2, 13, 15, 16, 20}`, lifts [2, 13, 15, 16, 20, 29, 33, 34, 36, 47]. -/
private def uTabQ29 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(35, {})}
  | 14 => {(1, {2, 13}), (2, {2, 47}), (5, {2, 20}), (9, {33, 34}), (10, {20, 29}), 
      (11, {36}), (12, {16, 33}), (13, {15, 16}), (15, {13, 20, 33}), (17, {29, 34}), 
      (23, {13, 34, 47}), (25, {16, 20, 47}), (26, {15, 34}), (29, {20, 34, 47}), 
      (31, {13, 16, 47}), (37, {13, 16, 29}), (39, {15, 20, 33}), (43, {2, 16, 34}), 
      (47, {2, 29})}
  | 21 => {(35, {})}
  | 28 => {(1, {2, 13}), (2, {2, 47}), (5, {2, 20}), (9, {33, 34}), (10, {20, 29}), 
      (11, {36}), (12, {16, 33}), (13, {15, 16}), (15, {13, 20, 33}), (17, {29, 34}), 
      (23, {13, 34, 47}), (25, {16, 20, 47}), (26, {15, 34}), (29, {20, 34, 47}), 
      (31, {13, 16, 47}), (37, {13, 16, 29}), (39, {15, 20, 33}), (43, {2, 16, 34}), 
      (47, {2, 29})}
  | 35 => {(35, {})}
  | 42 => {(1, {2, 13}), (2, {2, 47}), (5, {2, 20}), (9, {33, 34}), (10, {20, 29}), 
      (11, {36}), (12, {16, 33}), (13, {15, 16}), (15, {13, 20, 33}), (17, {29, 34}), 
      (23, {13, 34, 47}), (25, {16, 20, 47}), (26, {15, 34}), (29, {20, 34, 47}), 
      (31, {13, 16, 47}), (37, {13, 16, 29}), (39, {15, 20, 33}), (43, {2, 16, 34}), 
      (47, {2, 29})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_29` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q29 :
    ∀ T ∈ (lifts98 {2, 13, 15, 16, 20}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ29 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ29_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ29 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {2, 13, 15, 16, 20}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_29 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {2, 13, 15, 16, 20}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {2, 13, 15, 16, 20}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {2, 13, 15, 16, 20}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q29 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ29_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_30 = {3, 4, 13, 17, 20}`, lifts [3, 4, 13, 17, 20, 29, 32, 36, 45, 46]. -/
private def uTabQ30 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(21, {})}
  | 14 => {(1, {3, 4, 13}), (4, {3, 46}), (5, {17, 20}), (8, {13, 36}), (10, {20, 29}), 
      (11, {17, 36, 45}), (13, {45, 46}), (17, {17, 29, 46}), (19, {20, 36, 46}), 
      (23, {4, 13, 17}), (25, {4, 20}), (26, {4, 45}), (27, {4, 29, 36}), (33, {3, 36}), 
      (39, {20, 45}), (41, {17, 29, 36}), (43, {32}), (45, {13, 46}), (47, {4, 29, 46})}
  | 21 => {(21, {})}
  | 28 => {(1, {3, 4, 13}), (4, {3, 46}), (5, {17, 20}), (8, {13, 36}), (10, {20, 29}), 
      (11, {17, 36, 45}), (13, {45, 46}), (17, {17, 29, 46}), (19, {20, 36, 46}), 
      (23, {4, 13, 17}), (25, {4, 20}), (26, {4, 45}), (27, {4, 29, 36}), (33, {3, 36}), 
      (39, {20, 45}), (41, {17, 29, 36}), (43, {32}), (45, {13, 46}), (47, {4, 29, 46})}
  | 35 => {(21, {})}
  | 42 => {(1, {3, 4, 13}), (4, {3, 46}), (5, {17, 20}), (8, {13, 36}), (10, {20, 29}), 
      (11, {17, 36, 45}), (13, {45, 46}), (17, {17, 29, 46}), (19, {20, 36, 46}), 
      (23, {4, 13, 17}), (25, {4, 20}), (26, {4, 45}), (27, {4, 29, 36}), (33, {3, 36}), 
      (39, {20, 45}), (41, {17, 29, 36}), (43, {32}), (45, {13, 46}), (47, {4, 29, 46})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_30` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q30 :
    ∀ T ∈ (lifts98 {3, 4, 13, 17, 20}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ30 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ30_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ30 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {3, 4, 13, 17, 20}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_30 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {3, 4, 13, 17, 20}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {3, 4, 13, 17, 20}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {3, 4, 13, 17, 20}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q30 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ30_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_31 = {3, 5, 9, 12, 15}`, lifts [3, 5, 9, 12, 15, 34, 37, 40, 44, 46]. -/
private def uTabQ31 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(5, {37, 40}), (7, {15}), (10, {9, 40}), (11, {9, 44}), (18, {5, 44}), 
      (21, {5, 9, 37}), (23, {9, 34}), (25, {12}), (35, {3}), (47, {44, 46})}
  | 14 => {(3, {3, 34, 37}), (4, {3, 46}), (5, {37, 40}), (6, {15, 34}), (10, {9, 40}), 
      (11, {9, 44}), (13, {15, 37, 46}), (15, {40, 46}), (18, {5, 44}), (19, {5, 15, 46}), 
      (23, {9, 34}), (25, {12}), (27, {15, 40, 44}), (31, {3, 44}), (39, {5, 15, 40}), 
      (47, {44, 46})}
  | 21 => {(7, {15}), (10, {9, 40}), (11, {9, 44}), (15, {40, 46}), (18, {5, 44}), 
      (21, {5, 9, 37}), (25, {12}), (35, {3}), (43, {9, 34})}
  | 28 => {(3, {3, 34, 37}), (4, {3, 46}), (5, {37, 40}), (6, {15, 34}), (10, {9, 40}), 
      (11, {9, 44}), (13, {15, 37, 46}), (15, {40, 46}), (18, {5, 44}), (19, {5, 15, 46}), 
      (23, {9, 34}), (25, {12}), (27, {15, 40, 44}), (31, {3, 44}), (39, {5, 15, 40}), 
      (47, {44, 46})}
  | 35 => {(5, {37, 40}), (7, {15}), (8, {12, 37}), (9, {12, 34, 44}), (10, {9, 40}), 
      (15, {40, 46}), (18, {5, 44}), (21, {5, 9, 37}), (23, {9, 34}), (35, {3}), 
      (41, {5, 12}), (47, {44, 46})}
  | 42 => {(3, {3, 34, 37}), (4, {3, 46}), (5, {37, 40}), (6, {15, 34}), (10, {9, 40}), 
      (11, {9, 44}), (13, {15, 37, 46}), (15, {40, 46}), (18, {5, 44}), (19, {5, 15, 46}), 
      (23, {9, 34}), (25, {12}), (27, {15, 40, 44}), (31, {3, 44}), (39, {5, 15, 40}), 
      (47, {44, 46})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_31` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q31 :
    ∀ T ∈ (lifts98 {3, 5, 9, 12, 15}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ31 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ31_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ31 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {3, 5, 9, 12, 15}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_31 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {3, 5, 9, 12, 15}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {3, 5, 9, 12, 15}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {3, 5, 9, 12, 15}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q31 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ31_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_32 = {3, 5, 11, 12, 17}`, lifts [3, 5, 11, 12, 17, 32, 37, 38, 44, 46]. -/
private def uTabQ32 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(7, {})}
  | 14 => {(4, {3, 46}), (10, {11, 38}), (11, {17, 44}), (13, {37, 38, 46}), 
      (19, {5, 11, 46}), (20, {5, 44}), (23, {17, 38}), (25, {12}), (27, {11, 44}), 
      (39, {5, 38}), (43, {32}), (45, {11, 37, 46}), (47, {44, 46})}
  | 21 => {(7, {})}
  | 28 => {(4, {3, 46}), (10, {11, 38}), (11, {17, 44}), (13, {37, 38, 46}), 
      (19, {5, 11, 46}), (20, {5, 44}), (23, {17, 38}), (25, {12}), (27, {11, 44}), 
      (39, {5, 38}), (43, {32}), (45, {11, 37, 46}), (47, {44, 46})}
  | 35 => {(7, {})}
  | 42 => {(4, {3, 46}), (10, {11, 38}), (11, {17, 44}), (13, {37, 38, 46}), 
      (19, {5, 11, 46}), (20, {5, 44}), (23, {17, 38}), (25, {12}), (27, {11, 44}), 
      (39, {5, 38}), (43, {32}), (45, {11, 37, 46}), (47, {44, 46})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_32` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q32 :
    ∀ T ∈ (lifts98 {3, 5, 11, 12, 17}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ32 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ32_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ32 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {3, 5, 11, 12, 17}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_32 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {3, 5, 11, 12, 17}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {3, 5, 11, 12, 17}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {3, 5, 11, 12, 17}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q32 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ32_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_33 = {3, 8, 9, 17, 24}`, lifts [3, 8, 9, 17, 24, 25, 32, 40, 41, 46]. -/
private def uTabQ33 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(2, {3, 46}), (7, {41}), (8, {24, 25}), (9, {32}), (21, {9}), (25, {8, 24}), 
      (35, {3, 17, 25}), (39, {25, 40}), (47, {25, 46})}
  | 14 => {(1, {3, 8, 9}), (2, {3, 46}), (5, {17, 40, 41}), (8, {24, 25}), (9, {32}), 
      (10, {9, 40}), (11, {8, 9, 17}), (13, {8, 46}), (19, {41, 46}), (25, {8, 24}), 
      (26, {8, 41}), (27, {25, 40}), (33, {3, 9, 24}), (41, {17, 24}), (45, {9, 24, 46}), 
      (47, {25, 46})}
  | 21 => {(2, {3, 46}), (3, {3, 32}), (6, {17, 32}), (7, {41}), (8, {24, 25}), (13, {8, 46}), 
      (15, {32, 40, 46}), (21, {9}), (25, {8, 24}), (27, {25, 40}), (35, {3, 17, 25}), 
      (41, {17, 24})}
  | 28 => {(1, {3, 8, 9}), (2, {3, 46}), (5, {17, 40, 41}), (8, {24, 25}), (9, {32}), 
      (10, {9, 40}), (11, {8, 9, 17}), (13, {8, 46}), (19, {41, 46}), (25, {8, 24}), 
      (26, {8, 41}), (27, {25, 40}), (33, {3, 9, 24}), (41, {17, 24}), (45, {9, 24, 46}), 
      (47, {25, 46})}
  | 35 => {(2, {3, 46}), (7, {41}), (8, {24, 25}), (9, {32}), (13, {8, 46}), (21, {9}), 
      (27, {25, 40}), (35, {3, 17, 25}), (41, {17, 24}), (47, {25, 46})}
  | 42 => {(1, {3, 8, 9}), (2, {3, 46}), (5, {17, 40, 41}), (8, {24, 25}), (9, {32}), 
      (10, {9, 40}), (11, {8, 9, 17}), (13, {8, 46}), (19, {41, 46}), (25, {8, 24}), 
      (26, {8, 41}), (27, {25, 40}), (33, {3, 9, 24}), (41, {17, 24}), (45, {9, 24, 46}), 
      (47, {25, 46})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_33` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q33 :
    ∀ T ∈ (lifts98 {3, 8, 9, 17, 24}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ33 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ33_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ33 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {3, 8, 9, 17, 24}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_33 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {3, 8, 9, 17, 24}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {3, 8, 9, 17, 24}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {3, 8, 9, 17, 24}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q33 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ33_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_34 = {3, 8, 11, 13, 15}`, lifts [3, 8, 11, 13, 15, 34, 36, 38, 41, 46]. -/
private def uTabQ34 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(21, {})}
  | 14 => {(3, {3, 34, 36}), (5, {38, 41}), (6, {15, 34}), (9, {11, 34}), (10, {11, 38}), 
      (16, {13, 36}), (25, {8}), (27, {11, 15, 36}), (33, {3, 15, 36}), (39, {15, 38}), 
      (41, {36, 38}), (43, {34, 41}), (47, {46})}
  | 21 => {(21, {})}
  | 28 => {(3, {3, 34, 36}), (5, {38, 41}), (6, {15, 34}), (9, {11, 34}), (10, {11, 38}), 
      (16, {13, 36}), (25, {8}), (27, {11, 15, 36}), (33, {3, 15, 36}), (39, {15, 38}), 
      (41, {36, 38}), (43, {34, 41}), (47, {46})}
  | 35 => {(21, {})}
  | 42 => {(3, {3, 34, 36}), (5, {38, 41}), (6, {15, 34}), (9, {11, 34}), (10, {11, 38}), 
      (16, {13, 36}), (25, {8}), (27, {11, 15, 36}), (33, {3, 15, 36}), (39, {15, 38}), 
      (41, {36, 38}), (43, {34, 41}), (47, {46})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_34` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q34 :
    ∀ T ∈ (lifts98 {3, 8, 11, 13, 15}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ34 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ34_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ34 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {3, 8, 11, 13, 15}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_34 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {3, 8, 11, 13, 15}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {3, 8, 11, 13, 15}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {3, 8, 11, 13, 15}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q34 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ34_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_35 = {3, 8, 11, 15, 18}`, lifts [3, 8, 11, 15, 18, 31, 34, 38, 41, 46]. -/
private def uTabQ35 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(21, {})}
  | 14 => {(3, {3, 31, 34}), (5, {18, 38, 41}), (8, {11, 38}), (9, {11, 34}), (11, {8, 18}), 
      (12, {8, 41}), (15, {46}), (16, {18, 31}), (20, {15, 34}), (23, {8, 34, 38}), 
      (25, {8, 31}), (27, {11, 15, 18}), (29, {3, 34, 41}), (31, {3, 38, 41}), 
      (33, {3, 15, 18}), (37, {3, 8}), (39, {15, 38}), (41, {31, 38}), (43, {18, 34, 41})}
  | 21 => {(21, {})}
  | 28 => {(3, {3, 31, 34}), (5, {18, 38, 41}), (8, {11, 38}), (9, {11, 34}), (11, {8, 18}), 
      (12, {8, 41}), (15, {46}), (16, {18, 31}), (20, {15, 34}), (23, {8, 34, 38}), 
      (25, {8, 31}), (27, {11, 15, 18}), (29, {3, 34, 41}), (31, {3, 38, 41}), 
      (33, {3, 15, 18}), (37, {3, 8}), (39, {15, 38}), (41, {31, 38}), (43, {18, 34, 41})}
  | 35 => {(21, {})}
  | 42 => {(3, {3, 31, 34}), (5, {18, 38, 41}), (8, {11, 38}), (9, {11, 34}), (11, {8, 18}), 
      (12, {8, 41}), (15, {46}), (16, {18, 31}), (20, {15, 34}), (23, {8, 34, 38}), 
      (25, {8, 31}), (27, {11, 15, 18}), (29, {3, 34, 41}), (31, {3, 38, 41}), 
      (33, {3, 15, 18}), (37, {3, 8}), (39, {15, 38}), (41, {31, 38}), (43, {18, 34, 41})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_35` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q35 :
    ∀ T ∈ (lifts98 {3, 8, 11, 15, 18}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ35 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ35_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ35 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {3, 8, 11, 15, 18}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_35 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {3, 8, 11, 15, 18}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {3, 8, 11, 15, 18}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {3, 8, 11, 15, 18}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q35 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ35_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_36 = {3, 8, 13, 17, 20}`, lifts [3, 8, 13, 17, 20, 29, 32, 36, 41, 46]. -/
private def uTabQ36 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(21, {})}
  | 14 => {(1, {3, 8, 13}), (2, {3, 46}), (8, {13, 36}), (9, {32}), (11, {8, 17, 36}), 
      (13, {8, 46}), (23, {8, 13, 17}), (26, {8, 41}), (27, {29, 36}), (33, {3, 36}), 
      (39, {20}), (45, {13, 46}), (47, {29, 46})}
  | 21 => {(21, {})}
  | 28 => {(1, {3, 8, 13}), (2, {3, 46}), (8, {13, 36}), (9, {32}), (11, {8, 17, 36}), 
      (13, {8, 46}), (23, {8, 13, 17}), (26, {8, 41}), (27, {29, 36}), (33, {3, 36}), 
      (39, {20}), (45, {13, 46}), (47, {29, 46})}
  | 35 => {(21, {})}
  | 42 => {(1, {3, 8, 13}), (2, {3, 46}), (8, {13, 36}), (9, {32}), (11, {8, 17, 36}), 
      (13, {8, 46}), (23, {8, 13, 17}), (26, {8, 41}), (27, {29, 36}), (33, {3, 36}), 
      (39, {20}), (45, {13, 46}), (47, {29, 46})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_36` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q36 :
    ∀ T ∈ (lifts98 {3, 8, 13, 17, 20}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ36 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ36_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ36 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {3, 8, 13, 17, 20}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_36 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {3, 8, 13, 17, 20}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {3, 8, 13, 17, 20}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {3, 8, 13, 17, 20}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q36 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ36_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_37 = {3, 10, 11, 13, 16}`, lifts [3, 10, 11, 13, 16, 33, 36, 38, 39, 46]. -/
private def uTabQ37 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(5, {38, 39}), (7, {13}), (11, {10, 36}), (20, {10, 39}), (21, {33}), 
      (25, {16, 39}), (26, {11, 38}), (35, {3, 11, 39}), (47, {46})}
  | 14 => {(3, {3, 33, 36}), (5, {38, 39}), (6, {16, 33}), (9, {10, 11, 33}), (11, {10, 36}), 
      (16, {13, 36}), (20, {10, 39}), (23, {13, 38}), (25, {16, 39}), (26, {11, 38}), 
      (27, {11, 33, 36}), (29, {3, 10}), (37, {3, 13, 16}), (39, {10, 33, 38}), 
      (41, {36, 38}), (47, {46})}
  | 21 => {(2, {3, 46}), (7, {13}), (11, {10, 36}), (13, {16, 38, 46}), (17, {11, 46}), 
      (20, {10, 39}), (21, {33}), (25, {16, 39}), (26, {11, 38}), (29, {3, 10}), 
      (35, {3, 11, 39}), (41, {36, 38})}
  | 28 => {(3, {3, 33, 36}), (5, {38, 39}), (6, {16, 33}), (9, {10, 11, 33}), (11, {10, 36}), 
      (16, {13, 36}), (20, {10, 39}), (23, {13, 38}), (25, {16, 39}), (26, {11, 38}), 
      (27, {11, 33, 36}), (29, {3, 10}), (37, {3, 13, 16}), (39, {10, 33, 38}), 
      (41, {36, 38}), (47, {46})}
  | 35 => {(5, {38, 39}), (7, {13}), (20, {10, 39}), (21, {33}), (26, {11, 38}), 
      (29, {3, 10}), (35, {3, 11, 39}), (41, {36, 38}), (43, {16, 39}), (47, {46})}
  | 42 => {(3, {3, 33, 36}), (5, {38, 39}), (6, {16, 33}), (9, {10, 11, 33}), (11, {10, 36}), 
      (16, {13, 36}), (20, {10, 39}), (23, {13, 38}), (25, {16, 39}), (26, {11, 38}), 
      (27, {11, 33, 36}), (29, {3, 10}), (37, {3, 13, 16}), (39, {10, 33, 38}), 
      (41, {36, 38}), (47, {46})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_37` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q37 :
    ∀ T ∈ (lifts98 {3, 10, 11, 13, 16}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ37 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ37_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ37 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {3, 10, 11, 13, 16}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_37 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {3, 10, 11, 13, 16}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {3, 10, 11, 13, 16}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {3, 10, 11, 13, 16}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q37 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ37_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_38 = {3, 10, 15, 22, 24}`, lifts [3, 10, 15, 22, 24, 25, 27, 34, 39, 46]. -/
private def uTabQ38 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(21, {})}
  | 14 => {(1, {3, 10}), (2, {3, 46}), (3, {3, 34}), (5, {22, 39}), (6, {15, 34}), 
      (9, {10, 22, 34}), (10, {10, 39}), (11, {10, 27}), (13, {15, 22, 46}), 
      (15, {27, 39, 46}), (17, {34, 46}), (18, {22, 27}), (19, {10, 15, 46}), (23, {25, 34}), 
      (27, {15, 22, 25}), (31, {3, 22, 25}), (39, {10, 15, 25}), (41, {24}), 
      (47, {25, 27, 46})}
  | 21 => {(21, {})}
  | 28 => {(1, {3, 10}), (2, {3, 46}), (3, {3, 34}), (5, {22, 39}), (6, {15, 34}), 
      (9, {10, 22, 34}), (10, {10, 39}), (11, {10, 27}), (13, {15, 22, 46}), 
      (15, {27, 39, 46}), (17, {34, 46}), (18, {22, 27}), (19, {10, 15, 46}), (23, {25, 34}), 
      (27, {15, 22, 25}), (31, {3, 22, 25}), (39, {10, 15, 25}), (41, {24}), 
      (47, {25, 27, 46})}
  | 35 => {(21, {})}
  | 42 => {(1, {3, 10}), (2, {3, 46}), (3, {3, 34}), (5, {22, 39}), (6, {15, 34}), 
      (9, {10, 22, 34}), (10, {10, 39}), (11, {10, 27}), (13, {15, 22, 46}), 
      (15, {27, 39, 46}), (17, {34, 46}), (18, {22, 27}), (19, {10, 15, 46}), (23, {25, 34}), 
      (27, {15, 22, 25}), (31, {3, 22, 25}), (39, {10, 15, 25}), (41, {24}), 
      (47, {25, 27, 46})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_38` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q38 :
    ∀ T ∈ (lifts98 {3, 10, 15, 22, 24}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ38 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ38_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ38 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {3, 10, 15, 22, 24}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_38 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {3, 10, 15, 22, 24}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {3, 10, 15, 22, 24}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {3, 10, 15, 22, 24}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q38 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ38_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_39 = {3, 12, 16, 18, 19}`, lifts [3, 12, 16, 18, 19, 30, 31, 33, 37, 46]. -/
private def uTabQ39 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(7, {})}
  | 14 => {(1, {3, 12}), (2, {3, 46}), (8, {12, 37}), (9, {12, 33}), (11, {18, 19}), 
      (12, {16, 33}), (15, {19, 33, 46}), (17, {12, 18, 46}), (19, {16, 31, 46}), 
      (22, {18, 31}), (23, {30}), (25, {12, 16, 31}), (27, {18, 33}), (31, {3, 16, 19}), 
      (37, {3, 16, 37}), (41, {12, 19, 31}), (43, {16, 18}), (45, {37, 46}), 
      (47, {19, 31, 46})}
  | 21 => {(7, {})}
  | 28 => {(1, {3, 12}), (2, {3, 46}), (8, {12, 37}), (9, {12, 33}), (11, {18, 19}), 
      (12, {16, 33}), (15, {19, 33, 46}), (17, {12, 18, 46}), (19, {16, 31, 46}), 
      (22, {18, 31}), (23, {30}), (25, {12, 16, 31}), (27, {18, 33}), (31, {3, 16, 19}), 
      (37, {3, 16, 37}), (41, {12, 19, 31}), (43, {16, 18}), (45, {37, 46}), 
      (47, {19, 31, 46})}
  | 35 => {(7, {})}
  | 42 => {(1, {3, 12}), (2, {3, 46}), (8, {12, 37}), (9, {12, 33}), (11, {18, 19}), 
      (12, {16, 33}), (15, {19, 33, 46}), (17, {12, 18, 46}), (19, {16, 31, 46}), 
      (22, {18, 31}), (23, {30}), (25, {12, 16, 31}), (27, {18, 33}), (31, {3, 16, 19}), 
      (37, {3, 16, 37}), (41, {12, 19, 31}), (43, {16, 18}), (45, {37, 46}), 
      (47, {19, 31, 46})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_39` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q39 :
    ∀ T ∈ (lifts98 {3, 12, 16, 18, 19}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ39 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ39_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ39 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {3, 12, 16, 18, 19}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_39 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {3, 12, 16, 18, 19}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {3, 12, 16, 18, 19}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {3, 12, 16, 18, 19}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q39 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ39_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_40 = {3, 12, 17, 18, 19}`, lifts [3, 12, 17, 18, 19, 30, 31, 32, 37, 46]. -/
private def uTabQ40 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(7, {})}
  | 14 => {(1, {3, 12}), (2, {3, 46}), (8, {12, 37}), (9, {12, 32}), (12, {17, 32}), 
      (15, {19, 32, 46}), (19, {31, 46}), (25, {12, 31}), (27, {18}), (31, {3, 19, 32}), 
      (37, {3, 32, 37}), (39, {30}), (45, {37, 46})}
  | 21 => {(7, {})}
  | 28 => {(1, {3, 12}), (2, {3, 46}), (8, {12, 37}), (9, {12, 32}), (12, {17, 32}), 
      (15, {19, 32, 46}), (19, {31, 46}), (25, {12, 31}), (27, {18}), (31, {3, 19, 32}), 
      (37, {3, 32, 37}), (39, {30}), (45, {37, 46})}
  | 35 => {(7, {})}
  | 42 => {(1, {3, 12}), (2, {3, 46}), (8, {12, 37}), (9, {12, 32}), (12, {17, 32}), 
      (15, {19, 32, 46}), (19, {31, 46}), (25, {12, 31}), (27, {18}), (31, {3, 19, 32}), 
      (37, {3, 32, 37}), (39, {30}), (45, {37, 46})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_40` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q40 :
    ∀ T ∈ (lifts98 {3, 12, 17, 18, 19}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ40 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ40_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ40 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {3, 12, 17, 18, 19}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_40 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {3, 12, 17, 18, 19}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {3, 12, 17, 18, 19}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {3, 12, 17, 18, 19}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q40 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ40_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_41 = {4, 5, 9, 16, 24}`, lifts [4, 5, 9, 16, 24, 25, 33, 40, 44, 45]. -/
private def uTabQ41 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(7, {})}
  | 14 => {(1, {4, 5, 9}), (3, {4, 33}), (4, {24, 25}), (5, {40}), (6, {16, 33}), 
      (9, {33, 44, 45}), (11, {9, 44, 45}), (13, {16, 45}), (19, {5, 16}), (23, {4, 9, 25}), 
      (25, {4, 16, 24}), (26, {4, 45}), (29, {24, 44}), (31, {16, 25, 44}), (38, {5, 44}), 
      (41, {5, 24}), (43, {9, 16, 25}), (45, {9, 24}), (47, {4, 25, 44})}
  | 21 => {(7, {})}
  | 28 => {(1, {4, 5, 9}), (3, {4, 33}), (4, {24, 25}), (5, {40}), (6, {16, 33}), 
      (9, {33, 44, 45}), (11, {9, 44, 45}), (13, {16, 45}), (19, {5, 16}), (23, {4, 9, 25}), 
      (25, {4, 16, 24}), (26, {4, 45}), (29, {24, 44}), (31, {16, 25, 44}), (38, {5, 44}), 
      (41, {5, 24}), (43, {9, 16, 25}), (45, {9, 24}), (47, {4, 25, 44})}
  | 35 => {(7, {})}
  | 42 => {(1, {4, 5, 9}), (3, {4, 33}), (4, {24, 25}), (5, {40}), (6, {16, 33}), 
      (9, {33, 44, 45}), (11, {9, 44, 45}), (13, {16, 45}), (19, {5, 16}), (23, {4, 9, 25}), 
      (25, {4, 16, 24}), (26, {4, 45}), (29, {24, 44}), (31, {16, 25, 44}), (38, {5, 44}), 
      (41, {5, 24}), (43, {9, 16, 25}), (45, {9, 24}), (47, {4, 25, 44})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_41` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q41 :
    ∀ T ∈ (lifts98 {4, 5, 9, 16, 24}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ41 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ41_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ41 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {4, 5, 9, 16, 24}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_41 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {4, 5, 9, 16, 24}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {4, 5, 9, 16, 24}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {4, 5, 9, 16, 24}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q41 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ41_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_42 = {4, 9, 10, 16, 24}`, lifts [4, 9, 10, 16, 24, 25, 33, 39, 40, 45]. -/
private def uTabQ42 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(7, {})}
  | 14 => {(1, {4, 9, 10}), (2, {4, 45}), (3, {4, 33}), (6, {16, 33}), (9, {10, 33, 45}), 
      (11, {9, 10, 45}), (13, {16, 45}), (17, {40}), (19, {10, 16}), (31, {16, 25}), 
      (38, {10, 39}), (41, {24}), (47, {4, 25})}
  | 21 => {(7, {})}
  | 28 => {(1, {4, 9, 10}), (2, {4, 45}), (3, {4, 33}), (6, {16, 33}), (9, {10, 33, 45}), 
      (11, {9, 10, 45}), (13, {16, 45}), (17, {40}), (19, {10, 16}), (31, {16, 25}), 
      (38, {10, 39}), (41, {24}), (47, {4, 25})}
  | 35 => {(7, {})}
  | 42 => {(1, {4, 9, 10}), (2, {4, 45}), (3, {4, 33}), (6, {16, 33}), (9, {10, 33, 45}), 
      (11, {9, 10, 45}), (13, {16, 45}), (17, {40}), (19, {10, 16}), (31, {16, 25}), 
      (38, {10, 39}), (41, {24}), (47, {4, 25})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_42` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q42 :
    ∀ T ∈ (lifts98 {4, 9, 10, 16, 24}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ42 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ42_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ42 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {4, 9, 10, 16, 24}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_42 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {4, 9, 10, 16, 24}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {4, 9, 10, 16, 24}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {4, 9, 10, 16, 24}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q42 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ42_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_43 = {4, 9, 13, 15, 22}`, lifts [4, 9, 13, 15, 22, 27, 34, 36, 40, 45]. -/
private def uTabQ43 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(3, {4, 34, 36}), (4, {22, 27}), (5, {22, 40}), (6, {15, 34}), (7, {13, 15, 27}), 
      (8, {13, 36}), (17, {34, 40}), (19, {15, 36}), (21, {9}), (25, {4, 27}), (31, {13, 22}), 
      (35, {45})}
  | 14 => {(1, {4, 9, 13}), (2, {4, 45}), (4, {22, 27}), (5, {22, 40}), (6, {15, 34}), 
      (9, {22, 34, 45}), (10, {9, 40}), (13, {15, 22, 45}), (17, {34, 40}), (25, {4, 27}), 
      (29, {27, 34}), (31, {13, 22}), (37, {13, 40, 45}), (39, {15, 40, 45}), (41, {36}), 
      (43, {9, 34})}
  | 21 => {(4, {22, 27}), (6, {15, 34}), (7, {13, 15, 27}), (17, {34, 40}), (21, {9}), 
      (25, {4, 27}), (29, {27, 34}), (31, {13, 22}), (35, {45}), (41, {36})}
  | 28 => {(1, {4, 9, 13}), (2, {4, 45}), (4, {22, 27}), (5, {22, 40}), (6, {15, 34}), 
      (9, {22, 34, 45}), (10, {9, 40}), (13, {15, 22, 45}), (17, {34, 40}), (25, {4, 27}), 
      (29, {27, 34}), (31, {13, 22}), (37, {13, 40, 45}), (39, {15, 40, 45}), (41, {36}), 
      (43, {9, 34})}
  | 35 => {(4, {22, 27}), (5, {22, 40}), (6, {15, 34}), (7, {13, 15, 27}), (21, {9}), 
      (29, {27, 34}), (35, {45}), (41, {36}), (47, {4, 27})}
  | 42 => {(1, {4, 9, 13}), (2, {4, 45}), (4, {22, 27}), (5, {22, 40}), (6, {15, 34}), 
      (9, {22, 34, 45}), (10, {9, 40}), (13, {15, 22, 45}), (17, {34, 40}), (25, {4, 27}), 
      (29, {27, 34}), (31, {13, 22}), (37, {13, 40, 45}), (39, {15, 40, 45}), (41, {36}), 
      (43, {9, 34})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_43` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q43 :
    ∀ T ∈ (lifts98 {4, 9, 13, 15, 22}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ43 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ43_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ43 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {4, 9, 13, 15, 22}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_43 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {4, 9, 13, 15, 22}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {4, 9, 13, 15, 22}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {4, 9, 13, 15, 22}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q43 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ43_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_44 = {4, 9, 17, 19, 23}`, lifts [4, 9, 17, 19, 23, 26, 30, 32, 40, 45]. -/
private def uTabQ44 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(7, {})}
  | 14 => {(1, {4, 9}), (2, {4, 45}), (3, {4, 30, 32}), (5, {17, 19, 40}), (6, {17, 32}), 
      (9, {23, 32, 45}), (13, {23, 30, 45}), (16, {19, 30}), (17, {17, 23, 40}), (19, {26}), 
      (25, {4, 23}), (27, {4, 40}), (29, {17, 30}), (31, {19, 32}), (32, {9, 40}), 
      (33, {9, 30}), (37, {32, 40, 45}), (39, {30, 40, 45}), (43, {9, 23, 32})}
  | 21 => {(7, {})}
  | 28 => {(1, {4, 9}), (2, {4, 45}), (3, {4, 30, 32}), (5, {17, 19, 40}), (6, {17, 32}), 
      (9, {23, 32, 45}), (13, {23, 30, 45}), (16, {19, 30}), (17, {17, 23, 40}), (19, {26}), 
      (25, {4, 23}), (27, {4, 40}), (29, {17, 30}), (31, {19, 32}), (32, {9, 40}), 
      (33, {9, 30}), (37, {32, 40, 45}), (39, {30, 40, 45}), (43, {9, 23, 32})}
  | 35 => {(7, {})}
  | 42 => {(1, {4, 9}), (2, {4, 45}), (3, {4, 30, 32}), (5, {17, 19, 40}), (6, {17, 32}), 
      (9, {23, 32, 45}), (13, {23, 30, 45}), (16, {19, 30}), (17, {17, 23, 40}), (19, {26}), 
      (25, {4, 23}), (27, {4, 40}), (29, {17, 30}), (31, {19, 32}), (32, {9, 40}), 
      (33, {9, 30}), (37, {32, 40, 45}), (39, {30, 40, 45}), (43, {9, 23, 32})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_44` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q44 :
    ∀ T ∈ (lifts98 {4, 9, 17, 19, 23}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ44 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ44_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ44 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {4, 9, 17, 19, 23}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_44 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {4, 9, 17, 19, 23}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {4, 9, 17, 19, 23}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {4, 9, 17, 19, 23}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q44 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ44_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_45 = {4, 10, 12, 17, 22}`, lifts [4, 10, 12, 17, 22, 27, 32, 37, 39, 45]. -/
private def uTabQ45 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(2, {4, 45}), (6, {17, 32}), (7, {27}), (17, {12, 17}), (19, {10}), (21, {37}), 
      (23, {4, 17}), (31, {22, 32}), (35, {17, 39, 45})}
  | 14 => {(2, {4, 45}), (3, {4, 32, 37}), (4, {22, 27}), (6, {17, 32}), (8, {12, 37}), 
      (13, {22, 37, 45}), (17, {12, 17}), (19, {10}), (23, {4, 17}), (27, {4, 22}), 
      (31, {22, 32}), (33, {12, 27, 39}), (37, {32, 37, 45}), (43, {32, 39}), 
      (45, {22, 37, 39}), (47, {4, 27})}
  | 21 => {(1, {4, 10, 12}), (2, {4, 45}), (6, {17, 32}), (7, {27}), (10, {10, 39}), 
      (17, {12, 17}), (21, {37}), (27, {4, 22}), (31, {22, 32}), (35, {17, 39, 45}), 
      (39, {10, 45}), (43, {32, 39})}
  | 28 => {(2, {4, 45}), (3, {4, 32, 37}), (4, {22, 27}), (6, {17, 32}), (8, {12, 37}), 
      (13, {22, 37, 45}), (17, {12, 17}), (19, {10}), (23, {4, 17}), (27, {4, 22}), 
      (31, {22, 32}), (33, {12, 27, 39}), (37, {32, 37, 45}), (43, {32, 39}), 
      (45, {22, 37, 39}), (47, {4, 27})}
  | 35 => {(2, {4, 45}), (6, {17, 32}), (7, {27}), (19, {10}), (21, {37}), (23, {4, 17}), 
      (27, {4, 22}), (35, {17, 39, 45}), (41, {12, 17}), (43, {32, 39})}
  | 42 => {(2, {4, 45}), (3, {4, 32, 37}), (4, {22, 27}), (6, {17, 32}), (8, {12, 37}), 
      (13, {22, 37, 45}), (17, {12, 17}), (19, {10}), (23, {4, 17}), (27, {4, 22}), 
      (31, {22, 32}), (33, {12, 27, 39}), (37, {32, 37, 45}), (43, {32, 39}), 
      (45, {22, 37, 39}), (47, {4, 27})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_45` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q45 :
    ∀ T ∈ (lifts98 {4, 10, 12, 17, 22}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ45 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ45_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ45 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {4, 10, 12, 17, 22}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_45 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {4, 10, 12, 17, 22}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {4, 10, 12, 17, 22}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {4, 10, 12, 17, 22}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q45 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ45_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_46 = {4, 10, 16, 18, 23}`, lifts [4, 10, 16, 18, 23, 26, 31, 33, 39, 45]. -/
private def uTabQ46 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(7, {})}
  | 14 => {(2, {4, 45}), (3, {4, 31, 33}), (4, {23, 26}), (5, {18, 39}), (16, {18, 31}), 
      (17, {18, 23}), (23, {4, 26}), (27, {4, 18, 33}), (29, {10}), (31, {16}), 
      (41, {26, 31}), (45, {26, 39}), (47, {4, 23, 31})}
  | 21 => {(7, {})}
  | 28 => {(2, {4, 45}), (3, {4, 31, 33}), (4, {23, 26}), (5, {18, 39}), (16, {18, 31}), 
      (17, {18, 23}), (23, {4, 26}), (27, {4, 18, 33}), (29, {10}), (31, {16}), 
      (41, {26, 31}), (45, {26, 39}), (47, {4, 23, 31})}
  | 35 => {(7, {})}
  | 42 => {(2, {4, 45}), (3, {4, 31, 33}), (4, {23, 26}), (5, {18, 39}), (16, {18, 31}), 
      (17, {18, 23}), (23, {4, 26}), (27, {4, 18, 33}), (29, {10}), (31, {16}), 
      (41, {26, 31}), (45, {26, 39}), (47, {4, 23, 31})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_46` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q46 :
    ∀ T ∈ (lifts98 {4, 10, 16, 18, 23}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ46 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ46_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ46 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {4, 10, 16, 18, 23}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_46 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {4, 10, 16, 18, 23}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {4, 10, 16, 18, 23}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {4, 10, 16, 18, 23}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q46 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ46_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_47 = {4, 11, 15, 23, 24}`, lifts [4, 11, 15, 23, 24, 25, 26, 34, 38, 45]. -/
private def uTabQ47 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(2, {4, 45}), (3, {4, 34}), (5, {38}), (7, {15}), (11, {26, 45}), (12, {24, 25}), 
      (21, {23}), (35, {11, 25, 45}), (37, {24, 45})}
  | 14 => {(1, {4, 11}), (2, {4, 45}), (3, {4, 34}), (5, {38}), (6, {15, 34}), (11, {26, 45}), 
      (12, {24, 25}), (17, {11, 23, 34}), (19, {11, 15, 26}), (25, {4, 23, 24}), 
      (29, {24, 34}), (30, {23, 26}), (33, {15, 24}), (37, {24, 45}), (43, {23, 25, 34}), 
      (47, {4, 23, 25})}
  | 21 => {(1, {4, 11}), (2, {4, 45}), (3, {4, 34}), (7, {15}), (10, {11, 38}), 
      (11, {26, 45}), (12, {24, 25}), (21, {23}), (29, {24, 34}), (31, {25, 38}), 
      (35, {11, 25, 45}), (41, {24, 26, 38})}
  | 28 => {(1, {4, 11}), (2, {4, 45}), (3, {4, 34}), (5, {38}), (6, {15, 34}), (11, {26, 45}), 
      (12, {24, 25}), (17, {11, 23, 34}), (19, {11, 15, 26}), (25, {4, 23, 24}), 
      (29, {24, 34}), (30, {23, 26}), (33, {15, 24}), (37, {24, 45}), (43, {23, 25, 34}), 
      (47, {4, 23, 25})}
  | 35 => {(1, {4, 11}), (2, {4, 45}), (5, {38}), (7, {15}), (12, {24, 25}), (15, {26, 45}), 
      (21, {23}), (29, {24, 34}), (35, {11, 25, 45}), (37, {24, 45})}
  | 42 => {(1, {4, 11}), (2, {4, 45}), (3, {4, 34}), (5, {38}), (6, {15, 34}), (11, {26, 45}), 
      (12, {24, 25}), (17, {11, 23, 34}), (19, {11, 15, 26}), (25, {4, 23, 24}), 
      (29, {24, 34}), (30, {23, 26}), (33, {15, 24}), (37, {24, 45}), (43, {23, 25, 34}), 
      (47, {4, 23, 25})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_47` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q47 :
    ∀ T ∈ (lifts98 {4, 11, 15, 23, 24}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ47 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ47_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ47 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {4, 11, 15, 23, 24}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_47 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {4, 11, 15, 23, 24}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {4, 11, 15, 23, 24}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {4, 11, 15, 23, 24}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q47 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ47_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_48 = {4, 12, 16, 20, 23}`, lifts [4, 12, 16, 20, 23, 26, 29, 33, 37, 45]. -/
private def uTabQ48 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(4, {23, 26}), (5, {20, 37}), (7, {29}), (16, {12, 37}), (21, {23, 33, 37}), 
      (23, {4, 26}), (31, {16}), (33, {12, 33}), (35, {45}), (45, {26, 37})}
  | 14 => {(1, {4, 12}), (2, {4, 45}), (4, {23, 26}), (5, {20, 37}), (10, {20, 29}), 
      (11, {26, 45}), (16, {12, 37}), (17, {12, 23, 29}), (23, {4, 26}), (27, {4, 29, 33}), 
      (31, {16}), (33, {12, 33}), (39, {20, 33, 45}), (41, {12, 26, 29}), (45, {26, 37}), 
      (47, {4, 23, 29})}
  | 21 => {(1, {4, 12}), (4, {23, 26}), (7, {29}), (16, {12, 37}), (21, {23, 33, 37}), 
      (29, {20, 37}), (31, {16}), (35, {45}), (45, {26, 37})}
  | 28 => {(1, {4, 12}), (2, {4, 45}), (4, {23, 26}), (5, {20, 37}), (10, {20, 29}), 
      (11, {26, 45}), (16, {12, 37}), (17, {12, 23, 29}), (23, {4, 26}), (27, {4, 29, 33}), 
      (31, {16}), (33, {12, 33}), (39, {20, 33, 45}), (41, {12, 26, 29}), (45, {26, 37}), 
      (47, {4, 23, 29})}
  | 35 => {(1, {4, 12}), (4, {23, 26}), (5, {20, 37}), (6, {16, 33}), (7, {29}), 
      (16, {12, 37}), (19, {16, 20, 26}), (21, {23, 33, 37}), (23, {4, 26}), (33, {12, 33}), 
      (35, {45}), (43, {16, 23})}
  | 42 => {(1, {4, 12}), (2, {4, 45}), (4, {23, 26}), (5, {20, 37}), (10, {20, 29}), 
      (11, {26, 45}), (16, {12, 37}), (17, {12, 23, 29}), (23, {4, 26}), (27, {4, 29, 33}), 
      (31, {16}), (33, {12, 33}), (39, {20, 33, 45}), (41, {12, 26, 29}), (45, {26, 37}), 
      (47, {4, 23, 29})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_48` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q48 :
    ∀ T ∈ (lifts98 {4, 12, 16, 20, 23}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ48 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ48_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ48 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {4, 12, 16, 20, 23}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_48 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {4, 12, 16, 20, 23}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {4, 12, 16, 20, 23}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {4, 12, 16, 20, 23}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q48 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ48_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_49 = {4, 17, 18, 19, 23}`, lifts [4, 17, 18, 19, 23, 26, 30, 31, 32, 45]. -/
private def uTabQ49 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(7, {})}
  | 14 => {(1, {4}), (5, {17, 18, 19}), (10, {19, 30}), (12, {17, 32}), (17, {17, 18, 23}), 
      (29, {17, 30}), (31, {19, 32}), (32, {18, 31}), (33, {18, 30}), (37, {32, 45}), 
      (39, {30, 45}), (43, {18, 23, 32}), (45, {26})}
  | 21 => {(7, {})}
  | 28 => {(1, {4}), (5, {17, 18, 19}), (10, {19, 30}), (12, {17, 32}), (17, {17, 18, 23}), 
      (29, {17, 30}), (31, {19, 32}), (32, {18, 31}), (33, {18, 30}), (37, {32, 45}), 
      (39, {30, 45}), (43, {18, 23, 32}), (45, {26})}
  | 35 => {(7, {})}
  | 42 => {(1, {4}), (5, {17, 18, 19}), (10, {19, 30}), (12, {17, 32}), (17, {17, 18, 23}), 
      (29, {17, 30}), (31, {19, 32}), (32, {18, 31}), (33, {18, 30}), (37, {32, 45}), 
      (39, {30, 45}), (43, {18, 23, 32}), (45, {26})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_49` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q49 :
    ∀ T ∈ (lifts98 {4, 17, 18, 19, 23}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ49 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ49_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ49 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {4, 17, 18, 19, 23}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_49 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {4, 17, 18, 19, 23}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {4, 17, 18, 19, 23}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {4, 17, 18, 19, 23}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q49 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ49_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_50 = {4, 18, 20, 22, 24}`, lifts [4, 18, 20, 22, 24, 25, 27, 29, 31, 45]. -/
private def uTabQ50 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(21, {})}
  | 14 => {(1, {4}), (5, {18, 20, 22}), (6, {18, 31}), (8, {24, 25}), (9, {22, 45}), 
      (10, {20, 29}), (11, {18, 27, 45}), (15, {20, 27, 45}), (17, {18, 29}), (18, {22, 27}), 
      (19, {20, 31}), (29, {20, 24, 27}), (31, {22, 25}), (33, {18, 24, 27}), 
      (37, {24, 29, 45}), (39, {20, 25, 45}), (41, {24, 29, 31}), (43, {18, 25}), 
      (45, {22, 24})}
  | 21 => {(21, {})}
  | 28 => {(1, {4}), (5, {18, 20, 22}), (6, {18, 31}), (8, {24, 25}), (9, {22, 45}), 
      (10, {20, 29}), (11, {18, 27, 45}), (15, {20, 27, 45}), (17, {18, 29}), (18, {22, 27}), 
      (19, {20, 31}), (29, {20, 24, 27}), (31, {22, 25}), (33, {18, 24, 27}), 
      (37, {24, 29, 45}), (39, {20, 25, 45}), (41, {24, 29, 31}), (43, {18, 25}), 
      (45, {22, 24})}
  | 35 => {(21, {})}
  | 42 => {(1, {4}), (5, {18, 20, 22}), (6, {18, 31}), (8, {24, 25}), (9, {22, 45}), 
      (10, {20, 29}), (11, {18, 27, 45}), (15, {20, 27, 45}), (17, {18, 29}), (18, {22, 27}), 
      (19, {20, 31}), (29, {20, 24, 27}), (31, {22, 25}), (33, {18, 24, 27}), 
      (37, {24, 29, 45}), (39, {20, 25, 45}), (41, {24, 29, 31}), (43, {18, 25}), 
      (45, {22, 24})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_50` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q50 :
    ∀ T ∈ (lifts98 {4, 18, 20, 22, 24}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ50 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ50_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ50 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {4, 18, 20, 22, 24}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_50 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {4, 18, 20, 22, 24}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {4, 18, 20, 22, 24}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {4, 18, 20, 22, 24}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q50 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ50_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_51 = {5, 8, 15, 20, 24}`, lifts [5, 8, 15, 20, 24, 25, 29, 34, 41, 44]. -/
private def uTabQ51 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(3, {29, 34}), (5, {20, 41}), (6, {15, 34}), (7, {15, 29, 41}), (9, {34, 44}), 
      (10, {20, 29}), (11, {8, 44}), (21, {5}), (25, {8, 20, 24}), (33, {15, 24}), (35, {25}), 
      (36, {8, 41})}
  | 14 => {(1, {5, 8}), (2, {5, 44}), (3, {29, 34}), (4, {24, 25}), (6, {15, 34}), 
      (9, {34, 44}), (11, {8, 44}), (13, {8, 15}), (15, {20}), (23, {8, 25, 34}), 
      (31, {25, 41, 44}), (33, {15, 24}), (36, {8, 41}), (41, {5, 24, 29}), 
      (43, {25, 34, 41}), (47, {25, 29, 44})}
  | 21 => {(3, {29, 34}), (6, {15, 34}), (7, {15, 29, 41}), (11, {8, 44}), (13, {8, 15}), 
      (15, {20}), (21, {5}), (35, {25}), (36, {8, 41}), (45, {15, 24})}
  | 28 => {(1, {5, 8}), (2, {5, 44}), (3, {29, 34}), (4, {24, 25}), (6, {15, 34}), 
      (9, {34, 44}), (11, {8, 44}), (13, {8, 15}), (15, {20}), (23, {8, 25, 34}), 
      (31, {25, 41, 44}), (33, {15, 24}), (36, {8, 41}), (41, {5, 24, 29}), 
      (43, {25, 34, 41}), (47, {25, 29, 44})}
  | 35 => {(6, {15, 34}), (7, {15, 29, 41}), (9, {34, 44}), (13, {8, 15}), (15, {20}), 
      (21, {5}), (33, {15, 24}), (35, {25}), (36, {8, 41})}
  | 42 => {(1, {5, 8}), (2, {5, 44}), (3, {29, 34}), (4, {24, 25}), (6, {15, 34}), 
      (9, {34, 44}), (11, {8, 44}), (13, {8, 15}), (15, {20}), (23, {8, 25, 34}), 
      (31, {25, 41, 44}), (33, {15, 24}), (36, {8, 41}), (41, {5, 24, 29}), 
      (43, {25, 34, 41}), (47, {25, 29, 44})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_51` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q51 :
    ∀ T ∈ (lifts98 {5, 8, 15, 20, 24}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ51 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ51_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ51 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {5, 8, 15, 20, 24}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_51 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {5, 8, 15, 20, 24}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {5, 8, 15, 20, 24}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {5, 8, 15, 20, 24}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q51 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ51_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_52 = {5, 8, 18, 19, 23}`, lifts [5, 8, 18, 19, 23, 26, 30, 31, 41, 44]. -/
private def uTabQ52 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(2, {5, 44}), (7, {41}), (9, {23, 44}), (10, {19, 30}), (21, {5, 19, 23}), 
      (33, {18, 30}), (35, {31}), (37, {5, 8}), (39, {5, 30}), (45, {26})}
  | 14 => {(1, {5, 8}), (2, {5, 44}), (3, {30, 31}), (5, {18, 19, 41}), (6, {18, 31}), 
      (9, {23, 44}), (10, {19, 30}), (12, {8, 41}), (25, {8, 23, 31}), (27, {18, 44}), 
      (29, {30, 41, 44}), (31, {19, 41, 44}), (33, {18, 30}), (39, {5, 30}), 
      (43, {18, 23, 41}), (45, {26})}
  | 21 => {(1, {5, 8}), (2, {5, 44}), (7, {41}), (10, {19, 30}), (21, {5, 19, 23}), 
      (27, {18, 44}), (35, {31}), (39, {5, 30}), (45, {26})}
  | 28 => {(1, {5, 8}), (2, {5, 44}), (3, {30, 31}), (5, {18, 19, 41}), (6, {18, 31}), 
      (9, {23, 44}), (10, {19, 30}), (12, {8, 41}), (25, {8, 23, 31}), (27, {18, 44}), 
      (29, {30, 41, 44}), (31, {19, 41, 44}), (33, {18, 30}), (39, {5, 30}), 
      (43, {18, 23, 41}), (45, {26})}
  | 35 => {(1, {5, 8}), (2, {5, 44}), (4, {23, 26}), (7, {41}), (9, {23, 44}), (10, {19, 30}), 
      (15, {19, 26}), (21, {5, 19, 23}), (23, {8, 26, 30}), (27, {18, 44}), (33, {18, 30}), 
      (35, {31})}
  | 42 => {(1, {5, 8}), (2, {5, 44}), (3, {30, 31}), (5, {18, 19, 41}), (6, {18, 31}), 
      (9, {23, 44}), (10, {19, 30}), (12, {8, 41}), (25, {8, 23, 31}), (27, {18, 44}), 
      (29, {30, 41, 44}), (31, {19, 41, 44}), (33, {18, 30}), (39, {5, 30}), 
      (43, {18, 23, 41}), (45, {26})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_52` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q52 :
    ∀ T ∈ (lifts98 {5, 8, 18, 19, 23}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ52 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ52_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ52 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {5, 8, 18, 19, 23}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_52 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {5, 8, 18, 19, 23}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {5, 8, 18, 19, 23}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {5, 8, 18, 19, 23}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q52 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ52_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_53 = {5, 11, 12, 17, 23}`, lifts [5, 11, 12, 17, 23, 26, 32, 37, 38, 44]. -/
private def uTabQ53 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(7, {})}
  | 14 => {(2, {5, 44}), (3, {32, 37}), (4, {23, 26}), (5, {17, 37, 38}), (6, {17, 32}), 
      (10, {11, 38}), (11, {17, 26, 44}), (13, {23, 37, 38}), (15, {26, 32}), 
      (19, {5, 11, 26}), (23, {17, 26, 38}), (27, {11, 44}), (29, {17, 37, 44}), 
      (31, {32, 38, 44}), (33, {12}), (39, {5, 38}), (43, {23, 32}), (45, {11, 26, 37}), 
      (47, {23, 44})}
  | 21 => {(7, {})}
  | 28 => {(2, {5, 44}), (3, {32, 37}), (4, {23, 26}), (5, {17, 37, 38}), (6, {17, 32}), 
      (10, {11, 38}), (11, {17, 26, 44}), (13, {23, 37, 38}), (15, {26, 32}), 
      (19, {5, 11, 26}), (23, {17, 26, 38}), (27, {11, 44}), (29, {17, 37, 44}), 
      (31, {32, 38, 44}), (33, {12}), (39, {5, 38}), (43, {23, 32}), (45, {11, 26, 37}), 
      (47, {23, 44})}
  | 35 => {(7, {})}
  | 42 => {(2, {5, 44}), (3, {32, 37}), (4, {23, 26}), (5, {17, 37, 38}), (6, {17, 32}), 
      (10, {11, 38}), (11, {17, 26, 44}), (13, {23, 37, 38}), (15, {26, 32}), 
      (19, {5, 11, 26}), (23, {17, 26, 38}), (27, {11, 44}), (29, {17, 37, 44}), 
      (31, {32, 38, 44}), (33, {12}), (39, {5, 38}), (43, {23, 32}), (45, {11, 26, 37}), 
      (47, {23, 44})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_53` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q53 :
    ∀ T ∈ (lifts98 {5, 11, 12, 17, 23}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ53 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ53_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ53 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {5, 11, 12, 17, 23}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_53 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {5, 11, 12, 17, 23}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {5, 11, 12, 17, 23}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {5, 11, 12, 17, 23}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q53 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ53_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_54 = {6, 8, 9, 15, 23}`, lifts [6, 8, 9, 15, 23, 26, 34, 40, 41, 43]. -/
private def uTabQ54 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(35, {})}
  | 14 => {(1, {6, 8, 9}), (2, {6, 43}), (3, {34}), (4, {23, 26}), (5, {40, 41}), 
      (10, {9, 40}), (11, {8, 9, 26}), (13, {8, 15, 23}), (15, {6, 26, 40}), 
      (19, {15, 26, 41}), (24, {8, 41}), (25, {8, 23, 43}), (27, {15, 40}), (31, {6, 41}), 
      (33, {6, 9, 15}), (37, {8, 40}), (41, {26, 43}), (45, {9, 15, 26}), (47, {6, 23})}
  | 21 => {(35, {})}
  | 28 => {(1, {6, 8, 9}), (2, {6, 43}), (3, {34}), (4, {23, 26}), (5, {40, 41}), 
      (10, {9, 40}), (11, {8, 9, 26}), (13, {8, 15, 23}), (15, {6, 26, 40}), 
      (19, {15, 26, 41}), (24, {8, 41}), (25, {8, 23, 43}), (27, {15, 40}), (31, {6, 41}), 
      (33, {6, 9, 15}), (37, {8, 40}), (41, {26, 43}), (45, {9, 15, 26}), (47, {6, 23})}
  | 35 => {(35, {})}
  | 42 => {(1, {6, 8, 9}), (2, {6, 43}), (3, {34}), (4, {23, 26}), (5, {40, 41}), 
      (10, {9, 40}), (11, {8, 9, 26}), (13, {8, 15, 23}), (15, {6, 26, 40}), 
      (19, {15, 26, 41}), (24, {8, 41}), (25, {8, 23, 43}), (27, {15, 40}), (31, {6, 41}), 
      (33, {6, 9, 15}), (37, {8, 40}), (41, {26, 43}), (45, {9, 15, 26}), (47, {6, 23})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_54` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q54 :
    ∀ T ∈ (lifts98 {6, 8, 9, 15, 23}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ54 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ54_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ54 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {6, 8, 9, 15, 23}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_54 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {6, 8, 9, 15, 23}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {6, 8, 9, 15, 23}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {6, 8, 9, 15, 23}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q54 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ54_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_55 = {6, 9, 15, 16, 23}`, lifts [6, 9, 15, 16, 23, 26, 33, 34, 40, 43]. -/
private def uTabQ55 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(35, {})}
  | 14 => {(1, {6, 9}), (2, {6, 43}), (4, {23, 26}), (5, {40}), (11, {9, 26}), 
      (13, {15, 16, 23}), (19, {15, 16, 26}), (24, {16, 33}), (25, {16, 23, 43}), (29, {34}), 
      (31, {6, 16}), (41, {26, 43}), (47, {6, 23})}
  | 21 => {(35, {})}
  | 28 => {(1, {6, 9}), (2, {6, 43}), (4, {23, 26}), (5, {40}), (11, {9, 26}), 
      (13, {15, 16, 23}), (19, {15, 16, 26}), (24, {16, 33}), (25, {16, 23, 43}), (29, {34}), 
      (31, {6, 16}), (41, {26, 43}), (47, {6, 23})}
  | 35 => {(35, {})}
  | 42 => {(1, {6, 9}), (2, {6, 43}), (4, {23, 26}), (5, {40}), (11, {9, 26}), 
      (13, {15, 16, 23}), (19, {15, 16, 26}), (24, {16, 33}), (25, {16, 23, 43}), (29, {34}), 
      (31, {6, 16}), (41, {26, 43}), (47, {6, 23})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_55` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q55 :
    ∀ T ∈ (lifts98 {6, 9, 15, 16, 23}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ55 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ55_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ55 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {6, 9, 15, 16, 23}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_55 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {6, 9, 15, 16, 23}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {6, 9, 15, 16, 23}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {6, 9, 15, 16, 23}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q55 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ55_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_56 = {6, 10, 15, 22, 24}`, lifts [6, 10, 15, 22, 24, 25, 27, 34, 39, 43]. -/
private def uTabQ56 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(21, {})}
  | 14 => {(1, {6, 10}), (2, {6, 43}), (3, {34}), (5, {22, 39}), (10, {10, 39}), 
      (11, {10, 27}), (13, {15, 22}), (15, {6, 27, 39}), (19, {10, 15}), (22, {22, 27}), 
      (31, {6, 22, 25}), (37, {24}), (47, {6, 25, 27})}
  | 21 => {(21, {})}
  | 28 => {(1, {6, 10}), (2, {6, 43}), (3, {34}), (5, {22, 39}), (10, {10, 39}), 
      (11, {10, 27}), (13, {15, 22}), (15, {6, 27, 39}), (19, {10, 15}), (22, {22, 27}), 
      (31, {6, 22, 25}), (37, {24}), (47, {6, 25, 27})}
  | 35 => {(21, {})}
  | 42 => {(1, {6, 10}), (2, {6, 43}), (3, {34}), (5, {22, 39}), (10, {10, 39}), 
      (11, {10, 27}), (13, {15, 22}), (15, {6, 27, 39}), (19, {10, 15}), (22, {22, 27}), 
      (31, {6, 22, 25}), (37, {24}), (47, {6, 25, 27})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_56` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q56 :
    ∀ T ∈ (lifts98 {6, 10, 15, 22, 24}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ56 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ56_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ56 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {6, 10, 15, 22, 24}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_56 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {6, 10, 15, 22, 24}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {6, 10, 15, 22, 24}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {6, 10, 15, 22, 24}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q56 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ56_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_57 = {6, 10, 18, 19, 24}`, lifts [6, 10, 18, 19, 24, 25, 30, 31, 39, 43]. -/
private def uTabQ57 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(3, {30, 31}), (6, {18, 31}), (7, {43}), (17, {6, 18}), (19, {10, 31}), (21, {19}), 
      (30, {10, 39}), (35, {25, 31, 39}), (37, {24})}
  | 14 => {(1, {6, 10}), (2, {6, 43}), (3, {30, 31}), (5, {18, 19, 39}), (6, {18, 31}), 
      (9, {10, 43}), (11, {10, 18, 19}), (15, {6, 19, 39}), (17, {6, 18}), (19, {10, 31}), 
      (23, {25, 30, 43}), (26, {19, 30}), (27, {18, 25}), (30, {10, 39}), (31, {6, 19, 25}), 
      (37, {24})}
  | 21 => {(1, {6, 10}), (3, {30, 31}), (4, {24, 25}), (6, {18, 31}), (7, {43}), 
      (17, {6, 18}), (21, {19}), (27, {18, 25}), (29, {10, 24, 30}), (30, {10, 39}), 
      (35, {25, 31, 39}), (45, {24, 39})}
  | 28 => {(1, {6, 10}), (2, {6, 43}), (3, {30, 31}), (5, {18, 19, 39}), (6, {18, 31}), 
      (9, {10, 43}), (11, {10, 18, 19}), (15, {6, 19, 39}), (17, {6, 18}), (19, {10, 31}), 
      (23, {25, 30, 43}), (26, {19, 30}), (27, {18, 25}), (30, {10, 39}), (31, {6, 19, 25}), 
      (37, {24})}
  | 35 => {(1, {6, 10}), (6, {18, 31}), (7, {43}), (13, {30, 31}), (19, {10, 31}), (21, {19}), 
      (27, {18, 25}), (30, {10, 39}), (35, {25, 31, 39}), (37, {24})}
  | 42 => {(1, {6, 10}), (2, {6, 43}), (3, {30, 31}), (5, {18, 19, 39}), (6, {18, 31}), 
      (9, {10, 43}), (11, {10, 18, 19}), (15, {6, 19, 39}), (17, {6, 18}), (19, {10, 31}), 
      (23, {25, 30, 43}), (26, {19, 30}), (27, {18, 25}), (30, {10, 39}), (31, {6, 19, 25}), 
      (37, {24})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_57` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q57 :
    ∀ T ∈ (lifts98 {6, 10, 18, 19, 24}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ57 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ57_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ57 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {6, 10, 18, 19, 24}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_57 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {6, 10, 18, 19, 24}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {6, 10, 18, 19, 24}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {6, 10, 18, 19, 24}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q57 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ57_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_58 = {6, 11, 13, 15, 24}`, lifts [6, 11, 13, 15, 24, 25, 34, 36, 38, 43]. -/
private def uTabQ58 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(21, {})}
  | 14 => {(2, {6, 43}), (4, {24, 25}), (5, {38}), (6, {15, 34}), (9, {11, 34, 43}), 
      (11, {36}), (15, {6, 13}), (17, {6, 11, 34}), (25, {24, 43}), (29, {24, 34}), 
      (37, {13, 24}), (43, {25, 34, 43}), (47, {6, 25})}
  | 21 => {(21, {})}
  | 28 => {(2, {6, 43}), (4, {24, 25}), (5, {38}), (6, {15, 34}), (9, {11, 34, 43}), 
      (11, {36}), (15, {6, 13}), (17, {6, 11, 34}), (25, {24, 43}), (29, {24, 34}), 
      (37, {13, 24}), (43, {25, 34, 43}), (47, {6, 25})}
  | 35 => {(21, {})}
  | 42 => {(2, {6, 43}), (4, {24, 25}), (5, {38}), (6, {15, 34}), (9, {11, 34, 43}), 
      (11, {36}), (15, {6, 13}), (17, {6, 11, 34}), (25, {24, 43}), (29, {24, 34}), 
      (37, {13, 24}), (43, {25, 34, 43}), (47, {6, 25})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_58` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q58 :
    ∀ T ∈ (lifts98 {6, 11, 13, 15, 24}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ58 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ58_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ58 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {6, 11, 13, 15, 24}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_58 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {6, 11, 13, 15, 24}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {6, 11, 13, 15, 24}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {6, 11, 13, 15, 24}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q58 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ58_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_59 = {6, 11, 13, 17, 24}`, lifts [6, 11, 13, 17, 24, 25, 32, 36, 38, 43]. -/
private def uTabQ59 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(21, {})}
  | 14 => {(1, {6, 11, 13}), (2, {6, 43}), (3, {32, 36}), (4, {24, 25}), (6, {17, 32}), 
      (9, {11, 32, 43}), (11, {17, 36}), (13, {38}), (15, {6, 13, 32}), (17, {6, 11, 17}), 
      (19, {11, 36}), (22, {13, 36}), (25, {24, 43}), (29, {17, 24}), (33, {6, 24, 36}), 
      (37, {13, 24, 32}), (43, {25, 32, 43}), (45, {11, 13, 24}), (47, {6, 25})}
  | 21 => {(21, {})}
  | 28 => {(1, {6, 11, 13}), (2, {6, 43}), (3, {32, 36}), (4, {24, 25}), (6, {17, 32}), 
      (9, {11, 32, 43}), (11, {17, 36}), (13, {38}), (15, {6, 13, 32}), (17, {6, 11, 17}), 
      (19, {11, 36}), (22, {13, 36}), (25, {24, 43}), (29, {17, 24}), (33, {6, 24, 36}), 
      (37, {13, 24, 32}), (43, {25, 32, 43}), (45, {11, 13, 24}), (47, {6, 25})}
  | 35 => {(21, {})}
  | 42 => {(1, {6, 11, 13}), (2, {6, 43}), (3, {32, 36}), (4, {24, 25}), (6, {17, 32}), 
      (9, {11, 32, 43}), (11, {17, 36}), (13, {38}), (15, {6, 13, 32}), (17, {6, 11, 17}), 
      (19, {11, 36}), (22, {13, 36}), (25, {24, 43}), (29, {17, 24}), (33, {6, 24, 36}), 
      (37, {13, 24, 32}), (43, {25, 32, 43}), (45, {11, 13, 24}), (47, {6, 25})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_59` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q59 :
    ∀ T ∈ (lifts98 {6, 11, 13, 17, 24}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ59 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ59_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ59 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {6, 11, 13, 17, 24}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_59 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {6, 11, 13, 17, 24}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {6, 11, 13, 17, 24}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {6, 11, 13, 17, 24}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q59 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ59_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_60 = {6, 13, 16, 19, 22}`, lifts [6, 13, 16, 19, 22, 27, 30, 33, 36, 43]. -/
private def uTabQ60 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(35, {})}
  | 14 => {(3, {30, 33, 36}), (4, {22, 27}), (5, {19, 22}), (6, {16, 33}), (8, {13, 36}), 
      (9, {22, 33, 43}), (10, {19, 30}), (11, {19, 27, 36}), (13, {16, 22, 30}), (17, {6}), 
      (19, {16, 36}), (23, {13, 30, 43}), (27, {22, 33, 36}), (29, {27, 30}), (37, {13, 16}), 
      (39, {30, 33, 43}), (41, {19, 36, 43}), (43, {16, 43}), (45, {13, 22})}
  | 21 => {(35, {})}
  | 28 => {(3, {30, 33, 36}), (4, {22, 27}), (5, {19, 22}), (6, {16, 33}), (8, {13, 36}), 
      (9, {22, 33, 43}), (10, {19, 30}), (11, {19, 27, 36}), (13, {16, 22, 30}), (17, {6}), 
      (19, {16, 36}), (23, {13, 30, 43}), (27, {22, 33, 36}), (29, {27, 30}), (37, {13, 16}), 
      (39, {30, 33, 43}), (41, {19, 36, 43}), (43, {16, 43}), (45, {13, 22})}
  | 35 => {(35, {})}
  | 42 => {(3, {30, 33, 36}), (4, {22, 27}), (5, {19, 22}), (6, {16, 33}), (8, {13, 36}), 
      (9, {22, 33, 43}), (10, {19, 30}), (11, {19, 27, 36}), (13, {16, 22, 30}), (17, {6}), 
      (19, {16, 36}), (23, {13, 30, 43}), (27, {22, 33, 36}), (29, {27, 30}), (37, {13, 16}), 
      (39, {30, 33, 43}), (41, {19, 36, 43}), (43, {16, 43}), (45, {13, 22})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_60` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q60 :
    ∀ T ∈ (lifts98 {6, 13, 16, 19, 22}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ60 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ60_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ60 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {6, 13, 16, 19, 22}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_60 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {6, 13, 16, 19, 22}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {6, 13, 16, 19, 22}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {6, 13, 16, 19, 22}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q60 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ60_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_61 = {6, 16, 19, 22, 23}`, lifts [6, 16, 19, 22, 23, 26, 27, 30, 33, 43]. -/
private def uTabQ61 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(35, {})}
  | 14 => {(1, {6}), (3, {30, 33}), (5, {19, 22}), (8, {23, 26}), (10, {19, 30}), 
      (11, {19, 26, 27}), (22, {22, 27}), (23, {26, 30, 43}), (27, {22, 33}), (29, {27, 30}), 
      (37, {16}), (41, {19, 26, 43}), (45, {22, 26})}
  | 21 => {(35, {})}
  | 28 => {(1, {6}), (3, {30, 33}), (5, {19, 22}), (8, {23, 26}), (10, {19, 30}), 
      (11, {19, 26, 27}), (22, {22, 27}), (23, {26, 30, 43}), (27, {22, 33}), (29, {27, 30}), 
      (37, {16}), (41, {19, 26, 43}), (45, {22, 26})}
  | 35 => {(35, {})}
  | 42 => {(1, {6}), (3, {30, 33}), (5, {19, 22}), (8, {23, 26}), (10, {19, 30}), 
      (11, {19, 26, 27}), (22, {22, 27}), (23, {26, 30, 43}), (27, {22, 33}), (29, {27, 30}), 
      (37, {16}), (41, {19, 26, 43}), (45, {22, 26})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_61` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q61 :
    ∀ T ∈ (lifts98 {6, 16, 19, 22, 23}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ61 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ61_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ61 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {6, 16, 19, 22, 23}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_61 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {6, 16, 19, 22, 23}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {6, 16, 19, 22, 23}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {6, 16, 19, 22, 23}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q61 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ61_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- `Q_62 = {6, 17, 20, 22, 23}`, lifts [6, 17, 20, 22, 23, 26, 27, 29, 32, 43]. -/
private def uTabQ62 : ℕ → Finset (ℕ × Finset ℕ)
  | 7 => {(2, {6, 43}), (3, {29, 32}), (7, {27, 29, 43}), (10, {20, 29}), (19, {20, 26}), 
      (21, {23}), (22, {22, 27}), (31, {6, 22, 32}), (33, {6, 27}), (35, {17}), 
      (39, {20, 43}), (45, {22, 26})}
  | 14 => {(1, {6}), (3, {29, 32}), (5, {17, 20, 22}), (6, {17, 32}), (8, {23, 26}), 
      (10, {20, 29}), (11, {17, 26, 27}), (13, {22, 23}), (19, {20, 26}), (22, {22, 27}), 
      (23, {17, 26, 43}), (27, {22, 29}), (29, {17, 20, 27}), (39, {20, 43}), 
      (43, {23, 32, 43}), (45, {22, 26})}
  | 21 => {(1, {6}), (3, {29, 32}), (7, {27, 29, 43}), (10, {20, 29}), (21, {23}), 
      (22, {22, 27}), (27, {22, 29}), (35, {17}), (39, {20, 43}), (45, {22, 26})}
  | 28 => {(1, {6}), (3, {29, 32}), (5, {17, 20, 22}), (6, {17, 32}), (8, {23, 26}), 
      (10, {20, 29}), (11, {17, 26, 27}), (13, {22, 23}), (19, {20, 26}), (22, {22, 27}), 
      (23, {17, 26, 43}), (27, {22, 29}), (29, {17, 20, 27}), (39, {20, 43}), 
      (43, {23, 32, 43}), (45, {22, 26})}
  | 35 => {(1, {6}), (7, {27, 29, 43}), (10, {20, 29}), (19, {20, 26}), (21, {23}), 
      (22, {22, 27}), (27, {22, 29}), (35, {17}), (37, {29, 32})}
  | 42 => {(1, {6}), (3, {29, 32}), (5, {17, 20, 22}), (6, {17, 32}), (8, {23, 26}), 
      (10, {20, 29}), (11, {17, 26, 27}), (13, {22, 23}), (19, {20, 26}), (22, {22, 27}), 
      (23, {17, 26, 43}), (27, {22, 29}), (29, {17, 20, 27}), (39, {20, 43}), 
      (43, {23, 32, 43}), (45, {22, 26})}
  | _ => ∅

/-- Kernel certificate: no 5-subset `T` of the lifts of `Q_62` with an
odd member of `T ∪ {r}` meets every uncovered set for `r`. -/
theorem stage2_Q62 :
    ∀ T ∈ (lifts98 {6, 17, 20, 22, 23}).powersetCard 5,
      ∀ r ∈ d6res, (∃ x ∈ insert r T, x % 2 = 1) →
        ∃ p ∈ uTabQ62 r, ∀ t ∈ T, t ∉ p.2 := by
  decide +kernel

/-- Each table entry is an honest coverage spec: `λ ∈ {1,…,49}`,
`14 ≤ |λr|_98`, and `U` is exactly the set of lifts left uncovered. -/
private theorem uTabQ62_spec : ∀ r ∈ d6res, ∀ p ∈ uTabQ62 r,
    p.1 ∈ Finset.Icc 1 49 ∧
      (∀ t ∈ lifts98 {6, 17, 20, 22, 23}, (t ∉ p.2 ↔ 14 ≤ absModN (p.1 * t) 98)) ∧
      14 ≤ absModN (p.1 * r) 98 := by
  decide

/-- `card ≤ 5` subsets extend to 5-subsets of the (10-element) lift set. -/
private theorem stage2_lift_62 {T : Finset ℕ}
    (hTsub : T ⊆ lifts98 {6, 17, 20, 22, 23}) (hcard : T.card ≤ 5)
    {r : ℕ} (hr : r ∈ d6res) (hodd : ∃ x ∈ insert r T, x % 2 = 1) :
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  have h10 : 5 ≤ (lifts98 {6, 17, 20, 22, 23}).card := by decide
  obtain ⟨T', hTT', hT'l, hT'c⟩ :=
    Finset.exists_subsuperset_card_eq hTsub hcard h10
  have hT'mem : T' ∈ (lifts98 {6, 17, 20, 22, 23}).powersetCard 5 :=
    Finset.mem_powersetCard.mpr ⟨hT'l, hT'c⟩
  have hodd' : ∃ x ∈ insert r T', x % 2 = 1 := by
    obtain ⟨x, hx, hxo⟩ := hodd
    rcases Finset.mem_insert.mp hx with hxr | hxT
    · exact ⟨x, Finset.mem_insert.mpr (Or.inl hxr), hxo⟩
    · exact ⟨x, Finset.mem_insert_of_mem (hTT' hxT), hxo⟩
  obtain ⟨p, hp, hpT⟩ := stage2_Q62 T' hT'mem r hr hodd'
  obtain ⟨hp1, hspec, hpr⟩ := uTabQ62_spec r hr p hp
  exact ⟨p.1, hp1, fun a ha =>
    (hspec a (hTsub ha)).mp (hpT a (hTT' ha)), hpr⟩

/-- **Stage 2.**  For each bad pair-set `Q`, each `≤5`-subset `T` of the
mod-98 lifts of `Q`, and each `d6` residue `r ∈ {7,…,42}`, *provided
`T ∪ {r}` contains an odd residue* (the paper's `gcd(D) = 1` side
condition — all-even configurations genuinely admit no good multiplier),
there is a multiplier `λ ∈ {1,…,49}` — possibly a non-unit — pushing
everything to distance `≥ 14 = 98/7`. -/
theorem stage2 : ∀ Q ∈ badSets49,
    ∀ T ∈ ((lifts98 Q).powerset.filter fun T => T.card ≤ 5),
    ∀ r ∈ d6res,
    (∃ x ∈ insert r T, x % 2 = 1) →
    ∃ lam ∈ Finset.Icc 1 49,
      (∀ a ∈ T, 14 ≤ absModN (lam * a) 98) ∧
        14 ≤ absModN (lam * r) 98 := by
  intro Q hQ T hT r hr hodd
  have hTsub : T ⊆ lifts98 Q :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
  have hTcard : T.card ≤ 5 := (Finset.mem_filter.mp hT).2
  simp only [badSets49, Finset.mem_insert, Finset.mem_singleton,
    Finset.notMem_empty, or_false] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact stage2_lift_0 hTsub hTcard hr hodd
  · exact stage2_lift_1 hTsub hTcard hr hodd
  · exact stage2_lift_2 hTsub hTcard hr hodd
  · exact stage2_lift_3 hTsub hTcard hr hodd
  · exact stage2_lift_4 hTsub hTcard hr hodd
  · exact stage2_lift_5 hTsub hTcard hr hodd
  · exact stage2_lift_6 hTsub hTcard hr hodd
  · exact stage2_lift_7 hTsub hTcard hr hodd
  · exact stage2_lift_8 hTsub hTcard hr hodd
  · exact stage2_lift_9 hTsub hTcard hr hodd
  · exact stage2_lift_10 hTsub hTcard hr hodd
  · exact stage2_lift_11 hTsub hTcard hr hodd
  · exact stage2_lift_12 hTsub hTcard hr hodd
  · exact stage2_lift_13 hTsub hTcard hr hodd
  · exact stage2_lift_14 hTsub hTcard hr hodd
  · exact stage2_lift_15 hTsub hTcard hr hodd
  · exact stage2_lift_16 hTsub hTcard hr hodd
  · exact stage2_lift_17 hTsub hTcard hr hodd
  · exact stage2_lift_18 hTsub hTcard hr hodd
  · exact stage2_lift_19 hTsub hTcard hr hodd
  · exact stage2_lift_20 hTsub hTcard hr hodd
  · exact stage2_lift_21 hTsub hTcard hr hodd
  · exact stage2_lift_22 hTsub hTcard hr hodd
  · exact stage2_lift_23 hTsub hTcard hr hodd
  · exact stage2_lift_24 hTsub hTcard hr hodd
  · exact stage2_lift_25 hTsub hTcard hr hodd
  · exact stage2_lift_26 hTsub hTcard hr hodd
  · exact stage2_lift_27 hTsub hTcard hr hodd
  · exact stage2_lift_28 hTsub hTcard hr hodd
  · exact stage2_lift_29 hTsub hTcard hr hodd
  · exact stage2_lift_30 hTsub hTcard hr hodd
  · exact stage2_lift_31 hTsub hTcard hr hodd
  · exact stage2_lift_32 hTsub hTcard hr hodd
  · exact stage2_lift_33 hTsub hTcard hr hodd
  · exact stage2_lift_34 hTsub hTcard hr hodd
  · exact stage2_lift_35 hTsub hTcard hr hodd
  · exact stage2_lift_36 hTsub hTcard hr hodd
  · exact stage2_lift_37 hTsub hTcard hr hodd
  · exact stage2_lift_38 hTsub hTcard hr hodd
  · exact stage2_lift_39 hTsub hTcard hr hodd
  · exact stage2_lift_40 hTsub hTcard hr hodd
  · exact stage2_lift_41 hTsub hTcard hr hodd
  · exact stage2_lift_42 hTsub hTcard hr hodd
  · exact stage2_lift_43 hTsub hTcard hr hodd
  · exact stage2_lift_44 hTsub hTcard hr hodd
  · exact stage2_lift_45 hTsub hTcard hr hodd
  · exact stage2_lift_46 hTsub hTcard hr hodd
  · exact stage2_lift_47 hTsub hTcard hr hodd
  · exact stage2_lift_48 hTsub hTcard hr hodd
  · exact stage2_lift_49 hTsub hTcard hr hodd
  · exact stage2_lift_50 hTsub hTcard hr hodd
  · exact stage2_lift_51 hTsub hTcard hr hodd
  · exact stage2_lift_52 hTsub hTcard hr hodd
  · exact stage2_lift_53 hTsub hTcard hr hodd
  · exact stage2_lift_54 hTsub hTcard hr hodd
  · exact stage2_lift_55 hTsub hTcard hr hodd
  · exact stage2_lift_56 hTsub hTcard hr hodd
  · exact stage2_lift_57 hTsub hTcard hr hodd
  · exact stage2_lift_58 hTsub hTcard hr hodd
  · exact stage2_lift_59 hTsub hTcard hr hodd
  · exact stage2_lift_60 hTsub hTcard hr hodd
  · exact stage2_lift_61 hTsub hTcard hr hodd
  · exact stage2_lift_62 hTsub hTcard hr hodd

