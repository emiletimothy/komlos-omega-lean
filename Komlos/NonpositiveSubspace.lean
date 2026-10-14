import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Spectral counting lemma for the Komlós problem

The key step in Appendix B is: given a symmetric positive-semidefinite matrix `Q`,
a nonnegative diagonal matrix `D`, and `θ` such that `Q j j ≤ θ * D j j` for every `j`,
there is a subspace of `ℝⁿ` of dimension at least `n - θ n` on which the quadratic
form of `Q - D` is nonpositive.

The proof normalizes the coordinates where `D` is positive by conjugating with
`D⁻¹ᐟ²`.  The resulting matrix `B` is positive semidefinite with trace at most
`θ · |S|`, so at most `θ · |S|` of its eigenvalues exceed `1`.  The span of the
eigenvectors with eigenvalue at most `1`, scaled back by `D¹ᐟ²`, together with the
coordinate directions where `D` vanishes, gives the desired subspace.
-/

namespace Komlos

open Matrix Finset BigOperators

/-- If a positive semidefinite matrix has a vanishing diagonal entry, the
corresponding row and column vanish. -/
theorem posSemidef_eq_zero_of_diag_eq_zero {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.PosSemidef) {j : Fin n} (hj : Q j j = 0) (i : Fin n) :
    Q i j = 0 ∧ Q j i = 0 := by
  have hstar : star (Pi.single j 1 : Fin n → ℝ) = Pi.single j 1 := by
    rw [← Pi.single_star, star_one]
  have h1 : star (Pi.single j 1 : Fin n → ℝ) ⬝ᵥ
      Q *ᵥ (Pi.single j 1 : Fin n → ℝ) = 0 := by
    rw [hstar, mulVec_single_one, single_dotProduct, one_mul]
    simpa using hj
  have hQv : Q *ᵥ (Pi.single j 1 : Fin n → ℝ) = 0 := hQ.dotProduct_mulVec_zero_iff.mp h1
  have hcol : ∀ i : Fin n, Q i j = 0 := fun i => by
    have h2 : (Q *ᵥ Pi.single j 1 : Fin n → ℝ) i = 0 := by rw [hQv]; rfl
    rw [mulVec_single_one] at h2
    simpa using h2
  refine ⟨hcol i, ?_⟩
  have hs : Q j i = Q i j := by
    have h := congr_fun (congr_fun hQ.1.eq j) i
    simp only [conjTranspose_apply, star_trivial] at h
    exact h.symm
  rw [hs, hcol i]

/-- **Spectral counting lemma** (Appendix B of the Komlós paper).

If `Q` is positive semidefinite, `D` is diagonal with nonnegative entries, and
`Q j j ≤ θ * D j j` for every `j`, then there is a subspace `E` of `ℝⁿ` of
dimension at least `n - θ n` on which the quadratic form of `Q - D` is
nonpositive. -/
theorem exists_nonpositive_subspace_of_trace {n : ℕ} {θ : ℝ}
    (Q D : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosSemidef) (hθ : 0 ≤ θ)
    (hDdiag : ∀ j, 0 ≤ D j j) (hD : Matrix.IsDiag D) (hQD : ∀ j, Q j j ≤ θ * D j j) :
    ∃ E : Submodule ℝ (Fin n → ℝ),
      (n : ℝ) - θ * n ≤ Module.finrank ℝ E ∧
      ∀ h ∈ E, dotProduct h ((Q - D).mulVec h) ≤ 0 := by
  classical
  set S : Finset (Fin n) := univ.filter fun j => 0 < D j j with hSdef
  have hS : ∀ j : Fin n, j ∈ S ↔ 0 < D j j := fun j => by
    simp only [hSdef, mem_filter, mem_univ, true_and]
  have hT : ∀ j : Fin n, j ∉ S → D j j = 0 ∧ Q j j = 0 := by
    intro j hj
    have hle : D j j ≤ 0 := le_of_not_gt ((hS j).not.mp hj)
    have hDj : D j j = 0 := le_antisymm hle (hDdiag j)
    refine ⟨hDj, ?_⟩
    have hle' : Q j j ≤ 0 := by
      have := hQD j
      rwa [hDj, mul_zero] at this
    exact le_antisymm hle' hQ.diag_nonneg
  have hcol0 : ∀ j : Fin n, j ∉ S → ∀ i : Fin n, Q i j = 0 := fun j hj =>
    fun i => (posSemidef_eq_zero_of_diag_eq_zero hQ (hT j hj).2 i).1
  have hrow0 : ∀ j : Fin n, j ∉ S → ∀ i : Fin n, Q j i = 0 := fun j hj =>
    fun i => (posSemidef_eq_zero_of_diag_eq_zero hQ (hT j hj).2 i).2
  have hQDrow0 : ∀ i : Fin n, i ∉ S → ∀ j : Fin n, (Q - D) i j = 0 := by
    intro i hi j
    show Q i j - D i j = 0
    by_cases hij : i = j
    · subst hij
      rw [hrow0 i hi i, (hT i hi).1, sub_self]
    · rw [hrow0 i hi j, hD hij, sub_zero]
  have hQDcol0 : ∀ j : Fin n, j ∉ S → ∀ i : Fin n, (Q - D) i j = 0 := by
    intro j hj i
    show Q i j - D i j = 0
    by_cases hij : i = j
    · subst hij
      rw [hcol0 i hj i, (hT i hj).1, sub_self]
    · rw [hcol0 j hj i, hD hij, sub_zero]
  -- Scale the coordinates where `D` is positive.
  set r : ↥S → ℝ := fun i => (Real.sqrt (D i.1 i.1))⁻¹ with hrdef
  set Rs : Matrix ↥S ↥S ℝ := diagonal r with hRsdef
  set Qs : Matrix ↥S ↥S ℝ := Q.submatrix Subtype.val Subtype.val with hQsdef
  have hr_ne : ∀ i : ↥S, r i ≠ 0 := by
    intro i
    have hpos : 0 < D i.1 i.1 := (hS i.1).mp i.2
    simp only [hrdef]
    exact inv_ne_zero (ne_of_gt (Real.sqrt_pos_of_pos hpos))
  have hrr : ∀ i : ↥S, r i * r i = (D i.1 i.1)⁻¹ := by
    intro i
    have hx : 0 ≤ D i.1 i.1 := le_of_lt ((hS i.1).mp i.2)
    show (Real.sqrt (D i.1 i.1))⁻¹ * (Real.sqrt (D i.1 i.1))⁻¹ = (D i.1 i.1)⁻¹
    rw [← pow_two, inv_pow, Real.sq_sqrt hx]
  set B : Matrix ↥S ↥S ℝ := Rs * Qs * Rs with hBdef
  have hQs : Qs.PosSemidef := hQ.submatrix Subtype.val
  have hB : B.PosSemidef := by
    have h := hQs.mul_mul_conjTranspose_same Rs
    have hR : Rsᴴ = Rs := by
      rw [hRsdef]
      exact (isHermitian_diagonal r).eq
    rwa [hR] at h
  set bas := hB.1.eigenvectorBasis with hbasdef
  set lam := hB.1.eigenvalues with hlamdef
  have hBeig : ∀ i : ↥S, B *ᵥ ⇑(bas i) = lam i • ⇑(bas i) :=
    fun i => hB.1.mulVec_eigenvectorBasis i
  have hlam : ∀ i : ↥S, 0 ≤ lam i := fun i => hB.eigenvalues_nonneg i
  -- The trace of `B` is at most `θ * |S|`.
  have htrace : B.trace ≤ θ * S.card := by
    have htr_eq : B.trace = ∑ i : ↥S, Q i.1 i.1 / D i.1 i.1 := by
      have ht : ∀ M : Matrix ↥S ↥S ℝ, M.trace = ∑ i, M i i := fun M => rfl
      rw [ht]
      apply Finset.sum_congr rfl
      intro i _
      calc B i i = r i * Q i.1 i.1 * r i := by
            rw [hBdef, hRsdef, hQsdef, mul_diagonal, diagonal_mul, submatrix_apply]
        _ = r i * r i * Q i.1 i.1 := mul_right_comm _ _ _
        _ = (D i.1 i.1)⁻¹ * Q i.1 i.1 := by rw [hrr i]
        _ = Q i.1 i.1 / D i.1 i.1 := inv_mul_eq_div _ _
    rw [htr_eq]
    calc ∑ i : ↥S, Q i.1 i.1 / D i.1 i.1
        ≤ ∑ _i : ↥S, θ := by
          apply Finset.sum_le_sum
          intro i _
          have hpos : 0 < D i.1 i.1 := (hS i.1).mp i.2
          rw [div_le_iff₀ hpos]
          exact hQD i.1
      _ = θ * S.card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm, Finset.card_univ,
            Fintype.card_coe]
  -- Eigenvalues exceeding `1` are bounded by `θ * |S|`.
  set J : Finset ↥S := univ.filter fun i => ¬ lam i ≤ 1 with hJdef
  set I : Finset ↥S := univ.filter fun i => lam i ≤ 1 with hIdef
  have hJcard : (J.card : ℝ) ≤ θ * S.card := by
    have h1 : ∀ i ∈ J, (1 : ℝ) ≤ lam i :=
      fun i hi => le_of_lt (not_le.mp (mem_filter.mp hi).2)
    calc (J.card : ℝ) = ∑ i ∈ J, (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ i ∈ J, lam i := Finset.sum_le_sum h1
      _ ≤ ∑ i : ↥S, lam i := Finset.sum_le_sum_of_subset_of_nonneg (subset_univ J)
            fun i _ _ => hlam i
      _ = B.trace := by
          rw [hlamdef]
          exact hB.1.trace_eq_sum_eigenvalues.symm
      _ ≤ θ * S.card := htrace
  have hsplit : I.card + J.card = S.card := by
    have hdisj' : Disjoint I J := by
      rw [hIdef, hJdef]
      exact disjoint_filter_filter_not _ _ _
    have hunion : I ∪ J = (univ : Finset ↥S) := by
      rw [hIdef, hJdef]
      exact filter_union_filter_not_eq _ univ
    rw [← Fintype.card_coe S, ← Finset.card_univ, ← hunion,
      Finset.card_union_of_disjoint hdisj']
  have hIcard : (S.card : ℝ) - θ * S.card ≤ I.card := by
    have hcast : (I.card : ℝ) + J.card = S.card := by exact_mod_cast hsplit
    linarith [hJcard]
  -- The low-eigenvalue eigenvectors are linearly independent.
  have hv_li : LinearIndependent ℝ fun i : ↥S => ⇑(bas i) := by
    have hinj : Function.Injective (WithLp.linearEquiv 2 ℝ (↥S → ℝ)).toLinearMap :=
      fun x y hxy =>
        (WithLp.linearEquiv 2 ℝ (↥S → ℝ)).injective hxy
    have hker : LinearMap.ker (WithLp.linearEquiv 2 ℝ (↥S → ℝ)).toLinearMap = ⊥ :=
      LinearMap.ker_eq_bot.mpr hinj
    have h2 := bas.toBasis.linearIndependent.map'
      (WithLp.linearEquiv 2 ℝ (↥S → ℝ)).toLinearMap hker
    have hbv : ⇑(WithLp.linearEquiv 2 ℝ (↥S → ℝ)).toLinearMap ∘ ⇑bas.toBasis =
        fun i : ↥S => ⇑(bas i) := by
      funext i
      rw [Function.comp_apply]
      show (WithLp.linearEquiv 2 ℝ (↥S → ℝ)).toLinearMap (bas.toBasis i) = ⇑(bas i)
      rw [bas.coe_toBasis]
      rfl
    rw [← hbv]
    exact h2
  -- The quadratic form of `B - I` is nonpositive on their span.
  set W : Submodule ℝ (↥S → ℝ) :=
    Submodule.span ℝ (Set.range fun i : ↥I => ⇑(bas i.1)) with hWdef
  have hWfin : Module.finrank ℝ W = I.card := by
    have hli : LinearIndependent ℝ fun i : ↥I => ⇑(bas i.1) := by
      have h := hv_li.comp (fun i : ↥I => i.1) Subtype.val_injective
      simpa [Function.comp_def] using h
    rw [hWdef, finrank_span_eq_card hli, Fintype.card_coe]
  have hWbound : ∀ z : ↥S → ℝ, z ∈ W → z ⬝ᵥ B *ᵥ z ≤ z ⬝ᵥ z := by
    intro z hz
    rw [hWdef, Finsupp.mem_span_range_iff_exists_finsupp] at hz
    obtain ⟨c, hc⟩ := hz
    have hz' : z = ∑ i ∈ c.support, c i • ⇑(bas i.1) := hc.symm
    have hortho : ∀ i j : ↥I,
        (⇑(bas i.1) : ↥S → ℝ) ⬝ᵥ ⇑(bas j.1) = if i = j then (1 : ℝ) else 0 := by
      intro i j
      rw [dotProduct_comm]
      have h0 := bas.inner_eq_ite i.1 j.1
      rw [EuclideanSpace.inner_eq_star_dotProduct] at h0
      rw [show star (⇑(bas i.1) : ↥S → ℝ) = ⇑(bas i.1) from
        funext fun _ => star_trivial _] at h0
      rw [h0]
      by_cases hij : i = j
      · rw [ite_eq_left (congrArg Subtype.val hij), ite_eq_left hij]
      · rw [ite_eq_right (fun h : i.1 = j.1 => hij (Subtype.ext h)),
          ite_eq_right hij]
    have hsum : ∀ a b' : ↥I → ℝ,
        (∑ i ∈ c.support, a i • ⇑(bas i.1)) ⬝ᵥ
          (∑ j ∈ c.support, b' j • ⇑(bas j.1))
        = ∑ i ∈ c.support, a i * b' i := by
      intro a b'
      rw [sum_dotProduct]
      apply Finset.sum_congr rfl
      intro i hi
      rw [dotProduct_sum, Finset.sum_eq_single i]
      · rw [smul_dotProduct, dotProduct_smul, hortho i i, ite_eq_left rfl]
        simp only [smul_eq_mul, mul_one]
      · intro j hj hji
        rw [smul_dotProduct, dotProduct_smul, hortho i j, ite_eq_right hji.symm]
        simp only [smul_eq_mul, mul_zero]
      · exact fun h => absurd hi h
    have hBz : B *ᵥ z = ∑ i ∈ c.support, (c i * lam i.1) • ⇑(bas i.1) := by
      rw [hz', ← mulVecLin_apply, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, mulVecLin_apply, hBeig, ← mul_smul]
    rw [hBz, hz', hsum c fun i => c i * lam i.1, hsum c c]
    apply Finset.sum_le_sum
    intro i _
    have hle : lam i.1 ≤ 1 := (mem_filter.mp i.2).2
    have hnn : 0 ≤ c i * c i := mul_self_nonneg _
    have key : (c i * c i) * lam i.1 ≤ (c i * c i) * 1 :=
      mul_le_mul_of_nonneg_left hle hnn
    rw [mul_one] at key
    calc c i * (c i * lam i.1) = (c i * c i) * lam i.1 := (mul_assoc _ _ _).symm
      _ ≤ c i * c i := key
  -- Embed the low-eigenvalue subspace back into `Fin n → ℝ` by `D¹ᐟ²` scaling.
  set EM : Matrix (Fin n) ↥S ℝ := fun j i => if j = i.1 then r i else 0 with hEMdef
  have hEMapply : ∀ z : ↥S → ℝ, ∀ j : Fin n,
      (EM *ᵥ z) j = if h : j ∈ S then r ⟨j, h⟩ * z ⟨j, h⟩ else 0 := by
    intro z j
    show (∑ i : ↥S, EM j i * z i) = if h : j ∈ S then r ⟨j, h⟩ * z ⟨j, h⟩ else 0
    by_cases hj : j ∈ S
    · rw [dite_eq_left hj]
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · have hEjj : EM j ⟨j, hj⟩ = r ⟨j, hj⟩ := by
          show (if j = (⟨j, hj⟩ : ↥S).1 then r ⟨j, hj⟩ else 0) = r ⟨j, hj⟩
          exact ite_eq_left rfl
        rw [hEjj]
      · intro k _ hk
        have hk0 : EM j k = 0 := by
          show (if j = k.1 then r k else 0) = 0
          exact ite_eq_right fun h : j = k.1 => hk (Subtype.ext h.symm)
        rw [hk0, zero_mul]
      · exact fun h => absurd (mem_univ _) h
    · rw [dite_eq_right hj]
      apply Finset.sum_eq_zero
      intro k _
      have hk0 : EM j k = 0 := by
        show (if j = k.1 then r k else 0) = 0
        exact ite_eq_right fun h : j = k.1 => hj (h ▸ k.2)
      rw [hk0, zero_mul]
  have hEME : ∀ M : Matrix (Fin n) (Fin n) ℝ, ∀ a b : ↥S,
      (EMᵀ * M * EM) a b = r a * M a.1 b.1 * r b := by
    intro M a b
    have hk0 : ∀ k : Fin n, k ≠ b.1 →
        (∑ l : Fin n, EM l a * M l k) * EM k b = 0 := by
      intro k hk
      have hkb : EM k b = 0 := by
        show (if k = b.1 then r b else 0) = 0
        exact ite_eq_right hk
      rw [hkb, mul_zero]
    have hl0 : ∀ l : Fin n, l ≠ a.1 → EM l a * M l b.1 = 0 := by
      intro l hl
      have hla : EM l a = 0 := by
        show (if l = a.1 then r a else 0) = 0
        exact ite_eq_right hl
      rw [hla, zero_mul]
    have hEaa : EM a.1 a = r a := by
      show (if a.1 = a.1 then r a else 0) = r a
      exact ite_eq_left rfl
    have hEbb : EM b.1 b = r b := by
      show (if b.1 = b.1 then r b else 0) = r b
      exact ite_eq_left rfl
    show (∑ k : Fin n, (∑ l : Fin n, EM l a * M l k) * EM k b) =
        r a * M a.1 b.1 * r b
    rw [Finset.sum_eq_single b.1 (fun k _ => hk0 k) (fun h => absurd (mem_univ _) h)]
    rw [Finset.sum_eq_single a.1 (fun l _ => hl0 l) (fun h => absurd (mem_univ _) h)]
    rw [hEaa, hEbb]
  have hEMQ : EMᵀ * Q * EM = B := by
    ext a b
    rw [hEME, hBdef, hRsdef, hQsdef, mul_diagonal, diagonal_mul, submatrix_apply]
  have hEMD : EMᵀ * D * EM = 1 := by
    ext a b
    rw [hEME]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq]
      have hpos : 0 < D a.1 a.1 := (hS a.1).mp a.2
      calc r a * D a.1 a.1 * r a = (r a * r a) * D a.1 a.1 := by ring
        _ = (D a.1 a.1)⁻¹ * D a.1 a.1 := by rw [hrr a]
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
    · have hne : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
      rw [hD hne, mul_zero, zero_mul, Matrix.one_apply_ne hab]
  set Ls : (↥S → ℝ) →ₗ[ℝ] (Fin n → ℝ) := EM.mulVecLin with hLsdef
  have hLs : ∀ z : ↥S → ℝ, Ls z = EM *ᵥ z := fun z => mulVecLin_apply EM z
  have hLs_inj : Function.Injective Ls := by
    intro x y hxy
    funext i
    have h := congr_fun hxy i.1
    simp only [hLs, hEMapply, dite_eq_left i.2] at h
    exact mul_left_cancel₀ (hr_ne ⟨i.1, i.2⟩) h
  -- The zero-`D` coordinate directions, as the range of the coordinate inclusion.
  set ιT : (↥Sᶜ → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun y j => if h : j ∈ Sᶜ then y ⟨j, h⟩ else 0
      map_add' := fun x y => funext fun j => by
        by_cases hj : j ∈ Sᶜ
        · simp only [Pi.add_apply, dite_eq_left hj]
        · simp only [Pi.add_apply, dite_eq_right hj, add_zero]
      map_smul' := fun r' y => funext fun j => by
        by_cases hj : j ∈ Sᶜ
        · simp only [Pi.smul_apply, dite_eq_left hj, RingHom.id_apply]
        · simp only [Pi.smul_apply, dite_eq_right hj, RingHom.id_apply,
            smul_zero] } with hιTdef
  have hιT : ∀ y : ↥Sᶜ → ℝ, ∀ j : Fin n,
      ιT y j = if h : j ∈ Sᶜ then y ⟨j, h⟩ else 0 := fun _ _ => rfl
  have hιT_inj : Function.Injective ιT := by
    intro x y hxy
    funext i
    have h := congr_fun hxy i.1
    simp only [hιT, dite_eq_left i.2] at h
    exact h
  set E_T : Submodule ℝ (Fin n → ℝ) := LinearMap.range ιT with hETdef
  have hET : ∀ x : Fin n → ℝ, x ∈ E_T ↔ ∀ j ∈ S, x j = 0 := by
    intro x
    constructor
    · intro hx j hj
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx
      rw [← hy, hιT, dite_eq_right (fun h => Finset.mem_compl.mp h hj)]
    · intro h
      refine ⟨fun i => x i.1, ?_⟩
      funext j
      rw [hιT]
      by_cases hj : j ∈ Sᶜ
      · rw [dite_eq_left hj]
      · rw [dite_eq_right hj]
        have hjS : j ∈ S := by simpa [Finset.mem_compl] using hj
        exact (h j hjS).symm
  refine ⟨W.map Ls ⊔ E_T, ?_, ?_⟩
  · have hdisj : W.map Ls ⊓ E_T = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      rw [Submodule.mem_inf] at hx
      obtain ⟨⟨z, -, hzx⟩, hxT⟩ := hx
      ext j
      show x j = 0
      by_cases hj : j ∈ S
      · exact (hET x).mp hxT j hj
      · rw [← hzx, hLs, hEMapply, dite_eq_right hj]
    have hfinW : Module.finrank ℝ (W.map Ls) = I.card := by
      rw [← hWfin, ← LinearMap.range_domRestrict]
      apply LinearMap.finrank_range_of_inj
      intro x y hxy
      simp only [LinearMap.domRestrict_apply] at hxy
      exact Subtype.ext (hLs_inj hxy)
    have hfinT : Module.finrank ℝ E_T = Sᶜ.card := by
      have h1 : Module.finrank ℝ E_T = Module.finrank ℝ (↥Sᶜ → ℝ) := by
        rw [hETdef]
        exact LinearMap.finrank_range_of_inj hιT_inj
      rw [h1, Module.finrank_pi, Fintype.card_coe]
    have hfin : Module.finrank ℝ ↥(W.map Ls ⊔ E_T) = I.card + Sᶜ.card := by
      have h2 := Submodule.finrank_sup_add_finrank_inf_eq (W.map Ls) E_T
      rw [hdisj, finrank_bot, add_zero, hfinW, hfinT] at h2
      exact h2
    have hcomp : (Sᶜ.card : ℝ) = (n : ℝ) - S.card := by
      have h1 : Sᶜ.card = n - S.card := by
        have h2 := Finset.card_compl S
        rwa [Fintype.card_fin] at h2
      have hsle' : S.card ≤ n := by
        have h := Finset.card_le_univ S
        rwa [Fintype.card_fin] at h
      rw [h1]
      exact Nat.cast_sub hsle'
    have hsle : S.card ≤ n := by
      have h := Finset.card_le_univ S
      rwa [Fintype.card_fin] at h
    have hstep : (S.card : ℝ) * θ ≤ (n : ℝ) * θ := by
      have h2 : (S.card : ℝ) ≤ n := by exact_mod_cast hsle
      exact mul_le_mul h2 le_rfl hθ (Nat.cast_nonneg _)
    rw [hfin]
    push_cast
    rw [hcomp]
    linarith [hIcard]
  · intro h hh
    rw [Submodule.mem_sup] at hh
    obtain ⟨w, hw, t, ht, hwt⟩ := hh
    rw [← hwt]
    have hsplit' : (Q - D) *ᵥ (w + t) = (Q - D) *ᵥ w + (Q - D) *ᵥ t :=
      mulVec_add _ _ _
    rw [hsplit', dotProduct_add, add_dotProduct, add_dotProduct]
    have htsupp : ∀ j ∈ S, t j = 0 := (hET t).mp ht
    have ht0 : (Q - D) *ᵥ t = 0 := by
      funext i
      rw [mulVec_apply_eq_sum]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j ∈ S
      · rw [htsupp j hj, mul_zero]
      · rw [hQDcol0 j hj i, zero_mul]
    have hwt_supp : ∀ i : Fin n, i ∉ S → ((Q - D) *ᵥ w) i = 0 := by
      intro i hi
      rw [mulVec_apply_eq_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [hQDrow0 i hi j, zero_mul]
    have h1 : t ⬝ᵥ (Q - D) *ᵥ t = 0 := by rw [ht0]; simp
    have h2 : t ⬝ᵥ (Q - D) *ᵥ w = 0 := by
      show ∑ i, t i * ((Q - D) *ᵥ w) i = 0
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : i ∈ S
      · rw [htsupp i hi, zero_mul]
      · rw [hwt_supp i hi, mul_zero]
    have h3 : w ⬝ᵥ (Q - D) *ᵥ t = 0 := by rw [ht0]; simp
    have h4 : w ⬝ᵥ (Q - D) *ᵥ w ≤ 0 := by
      obtain ⟨z, hzW, hzw⟩ := Submodule.mem_map.mp hw
      rw [← hzw, hLs]
      have hQz : (EM *ᵥ z) ⬝ᵥ Q *ᵥ (EM *ᵥ z) = z ⬝ᵥ B *ᵥ z := by
        rw [dotProduct_mulVec, vecMul_mulVec, ← dotProduct_mulVec,
          mulVec_mulVec, hEMQ]
      have hDz : (EM *ᵥ z) ⬝ᵥ D *ᵥ (EM *ᵥ z) = z ⬝ᵥ z := by
        rw [dotProduct_mulVec, vecMul_mulVec, ← dotProduct_mulVec,
          mulVec_mulVec, hEMD, one_mulVec]
      have hsubm : (Q - D) *ᵥ (EM *ᵥ z) = Q *ᵥ (EM *ᵥ z) - D *ᵥ (EM *ᵥ z) :=
        sub_mulVec _ _ _
      rw [hsubm, dotProduct_sub, hQz, hDz]
      exact sub_nonpos.mpr (hWbound z hzW)
    linarith

end Komlos
