import Mathlib
import Research07.M3.Relations
import Research07.M3.Subtorus
import Research07.M3.FlowDense

noncomputable section

-- Probe 1: kerSpanRat membership shape (is it (k i : ℚ) * x i?)
example {n : ℕ} (u : Fin n → ℝ) (x : Fin n → ℚ) (hx : x ∈ kerSpanRat u)
    (k : Fin n → ℤ) (hk : k ∈ relLattice u) :
    ∑ i, (k i : ℚ) * x i = 0 := hx k hk

-- Probe 2: kerSpanInt membership shape
example {n : ℕ} (u : Fin n → ℝ) (y : Fin n → ℤ) (hy : y ∈ kerSpanInt u)
    (k : Fin n → ℤ) (hk : k ∈ relLattice u) :
    ∑ i, k i * y i = 0 := hy k hk

-- Probe 3: basis of submodule over PID
example {n : ℕ} (u : Fin n → ℝ) :
    ∃ d : ℕ, Nonempty (Basis (Fin d) ℤ (kerSpanInt u)) :=
  Submodule.nonempty_basis_of_pid (Pi.basisFun ℤ (Fin n)) (kerSpanInt u)

-- Probe 4: LinearIndependent.map' with subtype
example {n d : ℕ} (u : Fin n → ℝ) (b : Basis (Fin d) ℤ (kerSpanInt u)) :
    LinearIndependent ℤ ((kerSpanInt u).subtype ∘ b) :=
  b.linearIndependent.map' (kerSpanInt u).subtype (kerSpanInt u).ker_subtype

-- Probe 5: map_sum on the circle coercion
example (f : Fin 3 → ℝ) :
    ((∑ i, f i : ℝ) : UnitAddCircle) = ∑ i, ((f i : ℝ) : UnitAddCircle) := by
  have h := map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) f Finset.univ
  simpa using h

-- Probe 6: AddCircle.coe_zsmul + zsmul_eq_mul chain
example (m : ℤ) (s : ℝ) :
    (((m : ℝ) * s : ℝ) : UnitAddCircle) = m • ((s : ℝ) : UnitAddCircle) := by
  rw [← zsmul_eq_mul, AddCircle.coe_zsmul]

-- Probe 7: Dense.closure_eq
example {X : Type*} [TopologicalSpace X] {s : Set X} (h : Dense s) :
    closure s = Set.univ := h.closure_eq

-- Probe 8: Set.range_comp
example {α β ι : Type*} (g : α → β) (f : ι → α) :
    Set.range (g ∘ f) = g '' Set.range f := Set.range_comp g f

-- Probe 9: mem_span_range_iff_exists_fun direction check
example {n d : ℕ} (v : Fin d → Fin n → ℝ) (x : Fin n → ℝ) :
    x ∈ Submodule.span ℝ (Set.range v) ↔ ∃ c : Fin d → ℝ, ∑ i, c i • v i = x :=
  Submodule.mem_span_range_iff_exists_fun

-- Probe 10: Rat.cast_intCast
example (z : ℤ) : ((z : ℚ) : ℝ) = (z : ℝ) := Rat.cast_intCast z

-- Probe 11: denominator product
example {n : ℕ} (x : Fin n → ℚ) : 0 < ∏ i, (x i).den :=
  Finset.prod_pos fun i _ => Rat.den_pos _

example {n : ℕ} (x : Fin n → ℚ) (i : Fin n) :
    (x i).den ∣ ∏ j, (x j).den :=
  Finset.dvd_prod_of_mem (Finset.mem_univ i)

-- Probe 12: subtorusMap applied
example {n d : ℕ} (ρ : Fin d → Fin n → ℤ) (x : Fin d → UnitAddCircle) (i : Fin n) :
    subtorusMap ρ x i = ∑ ℓ, (ρ ℓ i) • x ℓ := rfl

end
