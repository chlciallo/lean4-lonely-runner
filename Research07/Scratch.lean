import Research07.LRC5.Filtering

set_option synthInstance.maxSize 400 in
example : ∀ q₁ q₂ q₃ c₁ c₂ c₃ : ZMod 5,
      (∃ a : ZMod 5,
        (2 * q₁ + c₁ = a ∨ 2 * q₁ + c₁ = a + 1 ∨ 2 * q₁ + c₁ = a + 2) ∧
        (2 * q₂ + c₂ = a ∨ 2 * q₂ + c₂ = a + 1 ∨ 2 * q₂ + c₂ = a + 2) ∧
        (2 * q₃ + c₃ = a ∨ 2 * q₃ + c₃ = a + 1 ∨ 2 * q₃ + c₃ = a + 2)) ∨
      (∀ c'₁ c'₂ c'₃ : ZMod 5, c'₁.val ≤ 1 → c'₂.val ≤ 1 → c'₃.val ≤ 1 →
        ∃ a : ZMod 5,
          (3 * q₁ + c₁ + c'₁ = a ∨ 3 * q₁ + c₁ + c'₁ = a + 1 ∨ 3 * q₁ + c₁ + c'₁ = a + 2) ∧
          (3 * q₂ + c₂ + c'₂ = a ∨ 3 * q₂ + c₂ + c'₂ = a + 1 ∨ 3 * q₂ + c₂ + c'₂ = a + 2) ∧
          (3 * q₃ + c₃ + c'₃ = a ∨ 3 * q₃ + c₃ + c'₃ = a + 1 ∨ 3 * q₃ + c₃ + c'₃ = a + 2)) := by
  decide
