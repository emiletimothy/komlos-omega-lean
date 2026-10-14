import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Finset.Lattice.Fold
import Komlos.NonpositiveSubspace
import Komlos.HessianDecomposition

/-!
# Anchor-subspace dimension accounting (Appendix B)

The anchor-subspace construction intersects several large subspaces of
`Fin n → ℝ`, each produced by `exists_nonpositive_subspace_of_trace`
(or its `P − D` specialization `exists_subspace_quadP_le`).  Each
subspace has dimension at least `n − θₖ · n`; this module supplies the
elementary dimension bookkeeping that the intersection still has
dimension at least `n − (∑ₖ θₖ) · n`, and packages the result as the
anchor-subspace existence lemma `anchor_subspace_of_intersection`.

The two-fold codimension inequality `finrank_inf_ge_add_sub` is the
only geometric input; everything else is linear arithmetic.
-/

namespace Komlos

/-- **Codimension inequality.** In the `n`-dimensional space
`Fin n → ℝ`, `dim (E ⊓ F) ≥ dim E + dim F − n`. -/
theorem finrank_inf_ge_add_sub {n : ℕ} (E F : Submodule ℝ (Fin n → ℝ)) :
    Module.finrank ℝ E + Module.finrank ℝ F - n ≤
      Module.finrank ℝ (E ⊓ F) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq E F
  have hsup : Module.finrank ℝ (E ⊔ F : Submodule ℝ (Fin n → ℝ)) ≤ n := by
    have h0 := Submodule.finrank_le (E ⊔ F)
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h0
  omega

/-- Real-valued form of `finrank_inf_ge_add_sub`, convenient for
`linarith`-based iteration. -/
theorem finrank_inf_ge_add_sub_real {n : ℕ} (E F : Submodule ℝ (Fin n → ℝ)) :
    (Module.finrank ℝ E : ℝ) + Module.finrank ℝ F - n ≤
      Module.finrank ℝ (E ⊓ F) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq E F
  have h' : (Module.finrank ℝ (E ⊔ F : Submodule ℝ (Fin n → ℝ)) : ℝ) +
        Module.finrank ℝ (E ⊓ F) =
      Module.finrank ℝ E + Module.finrank ℝ F := by
    exact_mod_cast h
  have hsup : (Module.finrank ℝ (E ⊔ F : Submodule ℝ (Fin n → ℝ)) : ℝ) ≤ n := by
    have h0 := Submodule.finrank_le (E ⊔ F)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h0
    exact_mod_cast h0
  linarith

/-- **Fivefold codimension inequality (natural-number form).** -/
theorem finrank_inf_inf_inf_inf_ge {n : ℕ}
    (E₁ E₂ E₃ E₄ E₅ : Submodule ℝ (Fin n → ℝ)) :
    Module.finrank ℝ E₁ + Module.finrank ℝ E₂ + Module.finrank ℝ E₃ +
        Module.finrank ℝ E₄ + Module.finrank ℝ E₅ - 4 * n ≤
      Module.finrank ℝ (E₁ ⊓ E₂ ⊓ E₃ ⊓ E₄ ⊓ E₅) := by
  have h45 := finrank_inf_ge_add_sub E₄ E₅
  have h345 := finrank_inf_ge_add_sub E₃ (E₄ ⊓ E₅)
  have h2345 := finrank_inf_ge_add_sub E₂ (E₃ ⊓ E₄ ⊓ E₅)
  have h12345 := finrank_inf_ge_add_sub E₁ (E₂ ⊓ E₃ ⊓ E₄ ⊓ E₅)
  omega

/-- **Fivefold codimension inequality (real-valued form).** -/
theorem finrank_inf_inf_inf_inf_ge_real {n : ℕ}
    (E₁ E₂ E₃ E₄ E₅ : Submodule ℝ (Fin n → ℝ)) :
    (Module.finrank ℝ E₁ : ℝ) + Module.finrank ℝ E₂ +
        Module.finrank ℝ E₃ + Module.finrank ℝ E₄ +
        Module.finrank ℝ E₅ - 4 * n ≤
      Module.finrank ℝ (E₁ ⊓ E₂ ⊓ E₃ ⊓ E₄ ⊓ E₅) := by
  have h45 := finrank_inf_ge_add_sub_real E₄ E₅
  have h345 := finrank_inf_ge_add_sub_real E₃ (E₄ ⊓ E₅)
  have h2345 := finrank_inf_ge_add_sub_real E₂ (E₃ ⊓ E₄ ⊓ E₅)
  have h12345 := finrank_inf_ge_add_sub_real E₁ (E₂ ⊓ E₃ ⊓ E₄ ⊓ E₅)
  linarith

/-- **General iteration over a `Finset`.** The infimum of an arbitrary
family of subspaces of `Fin n → ℝ` loses at most `n` dimensions per
member. -/
theorem finrank_finset_inf_ge {n : ℕ} {ι : Type*} (s : Finset ι)
    (E : ι → Submodule ℝ (Fin n → ℝ)) :
    (∑ i ∈ s, Module.finrank ℝ (E i)) - s.card * n ≤
      Module.finrank ℝ (s.inf E) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
      Finset.inf_insert]
    have h2 := finrank_inf_ge_add_sub (E a) (s.inf E)
    omega

/-- **Codimension-bound corollary.** If each `Eᵢ` has codimension at
most `cᵢ`, the intersection has codimension at most `∑ cᵢ`. -/
theorem finrank_intersection_ge_of_codim_bounds {n : ℕ}
    {E₁ E₂ E₃ E₄ E₅ : Submodule ℝ (Fin n → ℝ)} {c₁ c₂ c₃ c₄ c₅ : ℕ}
    (h₁ : (n : ℝ) - c₁ ≤ Module.finrank ℝ E₁)
    (h₂ : (n : ℝ) - c₂ ≤ Module.finrank ℝ E₂)
    (h₃ : (n : ℝ) - c₃ ≤ Module.finrank ℝ E₃)
    (h₄ : (n : ℝ) - c₄ ≤ Module.finrank ℝ E₄)
    (h₅ : (n : ℝ) - c₅ ≤ Module.finrank ℝ E₅) :
    (n : ℝ) - ((c₁ + c₂ + c₃ + c₄ + c₅ : ℕ) : ℝ) ≤
      Module.finrank ℝ (E₁ ⊓ E₂ ⊓ E₃ ⊓ E₄ ⊓ E₅) := by
  have h := finrank_inf_inf_inf_inf_ge_real E₁ E₂ E₃ E₄ E₅
  push_cast at h₁ h₂ h₃ h₄ h₅ ⊢
  linarith

/-- **Real-parameter codimension corollary.** If each `Eᵢ` has
dimension at least `n − θᵢ · n`, the intersection has dimension at
least `n − (∑ θᵢ) · n`. -/
theorem finrank_intersection_ge_of_theta_bounds {n : ℕ}
    {E₁ E₂ E₃ E₄ E₅ : Submodule ℝ (Fin n → ℝ)} {θ₁ θ₂ θ₃ θ₄ θ₅ : ℝ}
    (h₁ : (n : ℝ) - θ₁ * n ≤ Module.finrank ℝ E₁)
    (h₂ : (n : ℝ) - θ₂ * n ≤ Module.finrank ℝ E₂)
    (h₃ : (n : ℝ) - θ₃ * n ≤ Module.finrank ℝ E₃)
    (h₄ : (n : ℝ) - θ₄ * n ≤ Module.finrank ℝ E₄)
    (h₅ : (n : ℝ) - θ₅ * n ≤ Module.finrank ℝ E₅) :
    (n : ℝ) - (θ₁ + θ₂ + θ₃ + θ₄ + θ₅) * n ≤
      Module.finrank ℝ (E₁ ⊓ E₂ ⊓ E₃ ⊓ E₄ ⊓ E₅) := by
  have h := finrank_inf_inf_inf_inf_ge_real E₁ E₂ E₃ E₄ E₅
  have hsum : (θ₁ + θ₂ + θ₃ + θ₄ + θ₅) * n =
      θ₁ * n + θ₂ * n + θ₃ * n + θ₄ * n + θ₅ * n := by
    ring
  linarith

/-- **Anchor-subspace existence lemma (Appendix B).** Given five
existence statements of the shape produced by
`exists_nonpositive_subspace_of_trace` and `exists_subspace_quadP_le`
— a subspace `E` of dimension at least `n − θₖ · n` on which a
pointwise property `Pₖ` holds — the intersection
`E₁ ⊓ E₂ ⊓ E₃ ⊓ E₄ ⊓ E₅` is a single subspace of dimension at least
`n − (∑ₖ θₖ) · n` on which all five properties hold simultaneously. -/
theorem anchor_subspace_of_intersection {n : ℕ}
    {P₁ P₂ P₃ P₄ P₅ : (Fin n → ℝ) → Prop} {θ₁ θ₂ θ₃ θ₄ θ₅ : ℝ}
    (h₁ : ∃ E : Submodule ℝ (Fin n → ℝ),
      (n : ℝ) - θ₁ * n ≤ Module.finrank ℝ E ∧ ∀ h ∈ E, P₁ h)
    (h₂ : ∃ E : Submodule ℝ (Fin n → ℝ),
      (n : ℝ) - θ₂ * n ≤ Module.finrank ℝ E ∧ ∀ h ∈ E, P₂ h)
    (h₃ : ∃ E : Submodule ℝ (Fin n → ℝ),
      (n : ℝ) - θ₃ * n ≤ Module.finrank ℝ E ∧ ∀ h ∈ E, P₃ h)
    (h₄ : ∃ E : Submodule ℝ (Fin n → ℝ),
      (n : ℝ) - θ₄ * n ≤ Module.finrank ℝ E ∧ ∀ h ∈ E, P₄ h)
    (h₅ : ∃ E : Submodule ℝ (Fin n → ℝ),
      (n : ℝ) - θ₅ * n ≤ Module.finrank ℝ E ∧ ∀ h ∈ E, P₅ h) :
    ∃ E : Submodule ℝ (Fin n → ℝ),
      (n : ℝ) - (θ₁ + θ₂ + θ₃ + θ₄ + θ₅) * n ≤ Module.finrank ℝ E ∧
        (∀ h ∈ E, P₁ h) ∧ (∀ h ∈ E, P₂ h) ∧ (∀ h ∈ E, P₃ h) ∧
        (∀ h ∈ E, P₄ h) ∧ (∀ h ∈ E, P₅ h) := by
  obtain ⟨E₁, hdim1, hP1⟩ := h₁
  obtain ⟨E₂, hdim2, hP2⟩ := h₂
  obtain ⟨E₃, hdim3, hP3⟩ := h₃
  obtain ⟨E₄, hdim4, hP4⟩ := h₄
  obtain ⟨E₅, hdim5, hP5⟩ := h₅
  have hmem : ∀ {h : Fin n → ℝ}, h ∈ E₁ ⊓ E₂ ⊓ E₃ ⊓ E₄ ⊓ E₅ →
      h ∈ E₁ ∧ h ∈ E₂ ∧ h ∈ E₃ ∧ h ∈ E₄ ∧ h ∈ E₅ := by
    intro h hh
    simpa only [Submodule.mem_inf] using hh
  exact ⟨E₁ ⊓ E₂ ⊓ E₃ ⊓ E₄ ⊓ E₅,
    finrank_intersection_ge_of_theta_bounds hdim1 hdim2 hdim3 hdim4 hdim5,
    fun h hh => hP1 h (hmem hh).1,
    fun h hh => hP2 h (hmem hh).2.1,
    fun h hh => hP3 h (hmem hh).2.2.1,
    fun h hh => hP4 h (hmem hh).2.2.2.1,
    fun h hh => hP5 h (hmem hh).2.2.2.2⟩

end Komlos
