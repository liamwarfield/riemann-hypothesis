module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentFrameComparison
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsEigenComponentPolynomial
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryTwistMinorScalar

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentOrbitComparison
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockTriangularOfProportionalMinors
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockTriangularOfProportionalMinors
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TriStep

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {N : ℕ}

theorem minorIJ_one_of_ne {I S : Finset (Fin N)} (hI : I ≠ S) :
    minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) I S = 0 := by
  by_cases e : I.card = S.card
  · have hs : ¬ I ⊆ S := fun hs => hI (Finset.eq_of_subset_of_card_le hs e.ge)
    obtain ⟨a, ha, has⟩ := Finset.not_subset.mp hs
    exact minorIJ_eq_zero_of_row _ ha fun c hc => Matrix.one_apply_ne fun h => has (h ▸ hc)
  · exact minorIJ_of_card_ne _ e

theorem minorIJ_one_self' (S : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
  rw [minorIJ_eq_det _ S S _ rfl rfl, Matrix.submatrix_one _ (S.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem det_submatrix_eq_zero (A : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N))
    (hA : ∀ I, I ≠ S → minorIJ A I S = 0) (f : Fin S.card → Fin N) (x : Fin S.card) (hx : f x ∉ S) :
    (A.submatrix f (S.orderEmbOfFin rfl)).det = 0 := by
  by_cases hf : Function.Injective f
  · let σ := Tuple.sort f
    have hm : StrictMono (f ∘ σ) :=
      (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
    have hc : (Finset.univ.image f).card = S.card := by
      rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    have hu : f ∘ σ = (Finset.univ.image f).orderEmbOfFin hc :=
      Finset.orderEmbOfFin_unique hc (fun y => Finset.mem_image_of_mem _ (Finset.mem_univ _)) hm
    have hI : Finset.univ.image f ≠ S := fun e => hx (e ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _))
    have h0 := hA _ hI
    rw [minorIJ_eq_det A _ S _ hc rfl, ← hu] at h0
    have h1 : A.submatrix (f ∘ σ) (S.orderEmbOfFin rfl) =
        (A.submatrix f (S.orderEmbOfFin rfl)).submatrix σ id := by
      ext a b; rfl
    rw [h1, Matrix.det_permute] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exfalso
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e] at h
    · exact h
  · obtain ⟨a, b, hab, hne⟩ : ∃ a b, f a = f b ∧ a ≠ b := by
      simpa [Function.Injective] using hf
    exact Matrix.det_zero_of_row_eq hne (by ext y; simp [hab])

theorem eq_zero_of_minors (B : Matrix (Fin N) (Fin N) ℂ) (hB : B.det ≠ 0) (S : Finset (Fin N))
    (hA : ∀ I, I ≠ S → minorIJ B I S = 0) (r c : Fin N) (hr : r ∉ S) (hc : c ∈ S) : B r c = 0 := by
  set e := S.orderEmbOfFin rfl with he
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hS : minorIJ B S S ≠ 0 := by
    intro h0
    have h1 := minorIJ_mul B⁻¹ B S S
    rw [Matrix.nonsing_inv_mul _ hu, minorIJ_one_self',
      Finset.sum_eq_single S (fun I _ hI => by rw [hA I hI, mul_zero]) (by simp), h0, mul_zero] at h1
    exact one_ne_zero h1
  rw [minorIJ_eq_det B S S _ rfl rfl] at hS
  let M := B.submatrix e e
  let v : Fin S.card → ℂ := fun y => B r (e y)
  have hcr : Matrix.cramer Mᵀ v = 0 := by
    funext x
    have h1 : Mᵀ.updateCol x v = (B.submatrix (Function.update e x r) e)ᵀ := by
      ext a b
      by_cases hb : b = x
      · subst hb; simp [Matrix.updateCol_apply, v]
      · simp [Matrix.updateCol_apply, hb, M, Function.update_of_ne hb]
    rw [Matrix.cramer_apply, h1, Matrix.det_transpose]
    exact det_submatrix_eq_zero B S hA _ x (by simpa using hr)
  have hv : Mᵀ.det • v = 0 := by rw [← Matrix.mulVec_cramer, hcr, Matrix.mulVec_zero]
  have hv0 : v = 0 := by
    rcases smul_eq_zero.mp hv with h | h
    · rw [Matrix.det_transpose] at h; exact absurd h hS
    · exact h
  have hr' : c ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact hc
  obtain ⟨y, rfl⟩ := hr'
  exact congrFun hv0 y

theorem triangular_of_minors_proportional : ∀ (N j : ℕ) (h g : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j h →
    IsBlockDiag j g → h.det ≠ 0 → g.det ≠ 0 →
    (∀ i : Fin N, IsProperStep N j i → ∃ μ : ℂ, ∀ I, minorIJ g I (stepCols N j i) = μ * minorIJ h I (stepCols N j i)) →
    (h⁻¹ * g).BlockTriangular id := by
  intro N j h g hj hh hg hdh hdg hμ
  have huh : IsUnit h.det := isUnit_iff_ne_zero.mpr hdh
  have hbd : IsBlockDiag j (h⁻¹ * g) := (hh.inv huh).mul hg
  have hdet : (h⁻¹ * g).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv]
    exact mul_ne_zero (by simpa using hdh) hdg
  have hstep : ∀ i : Fin N, IsProperStep N j i → ∀ r c : Fin N, r ∉ stepCols N j i → c ∈ stepCols N j i →
      (h⁻¹ * g) r c = 0 := by
    intro i hi r c hr hc
    obtain ⟨μ, hm⟩ := hμ i hi
    refine eq_zero_of_minors _ hdet _ (fun I hI => ?_) r c hr hc
    have h1 : minorIJ (h⁻¹ * g) I (stepCols N j i) =
        μ * minorIJ (h⁻¹ * h) I (stepCols N j i) := by
      rw [minorIJ_mul, minorIJ_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun I' _ => by rw [hm I']; ring
    rw [h1, Matrix.nonsing_inv_mul _ huh, minorIJ_one_of_ne hI, mul_zero]
  intro r s hrs
  have hsr : (s : ℕ) < r := hrs
  have hrN := r.2
  by_cases hb : ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)
  · by_cases hω : (r : ℕ) < N - j
    · have hi : (s : ℕ) + j < N := by omega
      refine hstep ⟨(s : ℕ) + j, hi⟩ ⟨?_, ?_⟩ r s ?_ ?_
      · simp only; omega
      · simp only; omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]; omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_neg (by omega)]; omega
    · have hs' : N - j ≤ (s : ℕ) := by
        by_contra hc; exact hω (hb.mpr (by omega))
      have hi : (s : ℕ) - (N - j) < N := by omega
      refine hstep ⟨(s : ℕ) - (N - j), hi⟩ ⟨?_, ?_⟩ r s ?_ ?_
      · simp only; omega
      · simp only; omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]; omega
      · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [if_pos (by omega)]; omega
  · exact hbd r s hb

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TriStep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockTriangularOfProportionalMinorsStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_triangular_of_proportional_minors : ∀ (N j : ℕ) (h g : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j h → IsBlockDiag j g → h.det ≠ 0 → g.det ≠ 0 → (∀ i : Fin N, IsProperStep N j i → ∃ μ : ℂ, ∀ I, minorIJ g I (stepCols N j i) = μ * minorIJ h I (stepCols N j i)) → (h⁻¹ * g).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TriStep.triangular_of_minors_proportional | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TriStep.triangular_of_minors_proportional | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TriStep.triangular_of_minors_proportional <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentOrbitComparison
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Same

section Cols

variable {N j : ℕ} {a b ca cb : Fin N}

theorem cols_next (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hcase : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) :
    stepCols N j b = insert cb (stepCols N j a) ∧ cb ∉ stepCols N j a ∧ ca ∈ stepCols N j a := by
  have hbN := b.2
  rcases hcase with h | h
  · have h1 : (a : ℕ) + 1 ≤ j := by omega
    have h2 : (b : ℕ) + 1 ≤ j := by omega
    simp only [lastCol, if_pos h1] at hca
    refine ⟨?_, ?_, ?_⟩
    · ext c
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1, if_pos h2,
        Finset.mem_insert, Fin.ext_iff]
      omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1]
      omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1]
      omega
  · have h1 : ¬ (a : ℕ) + 1 ≤ j := by omega
    have h2 : ¬ (b : ℕ) + 1 ≤ j := by omega
    simp only [lastCol, if_neg h1] at hca
    refine ⟨?_, ?_, ?_⟩
    · ext c
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h1, if_neg h2,
        Finset.mem_insert, Fin.ext_iff]
      omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h1]
      omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h1]
      omega

theorem cols_prev (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hcase : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) {a' : Fin N} (ha' : (a' : ℕ) + 1 = a) (hp : IsProperStep N j a') :
    stepCols N j a' = (stepCols N j a).erase ca := by
  have hbN := b.2
  have hp1 := hp.1
  rcases hcase with h | h
  · have h1 : (a : ℕ) + 1 ≤ j := by omega
    have h2 : (a' : ℕ) + 1 ≤ j := by omega
    simp only [lastCol, if_pos h1] at hca
    ext c
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1, if_pos h2,
      Finset.mem_erase, ne_eq, Fin.ext_iff]
    omega
  · have h1 : ¬ (a : ℕ) + 1 ≤ j := by omega
    have h2 : ¬ (a' : ℕ) + 1 ≤ j := by omega
    simp only [lastCol, if_neg h1] at hca
    ext c
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h1, if_neg h2,
      Finset.mem_erase, ne_eq, Fin.ext_iff]
    omega

theorem cols_first (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hcase : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (h0 : (a : ℕ) = 0 ∨ (a : ℕ) = j) :
    (stepCols N j a).erase ca = ∅ := by
  have hbN := b.2
  rw [Finset.eq_empty_iff_forall_notMem]
  intro c
  by_cases h1 : (a : ℕ) + 1 ≤ j
  · simp only [lastCol, if_pos h1] at hca
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1,
      Finset.mem_erase, ne_eq, Fin.ext_iff]
    omega
  · simp only [lastCol, if_neg h1] at hca
    simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h1,
      Finset.mem_erase, ne_eq, Fin.ext_iff]
    omega

theorem transv_blockDiag (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hcase : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := by
  have hbN := b.2
  have hs : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
    by_cases h1 : (a : ℕ) + 1 ≤ j
    · simp only [lastCol, if_pos h1] at hca
      omega
    · simp only [lastCol, if_neg h1] at hca
      omega
  intro r s h
  have hrs : r ≠ s := fun e => h (by rw [e])
  rw [Matrix.add_apply, Matrix.one_apply_ne hrs, zero_add, Matrix.single_apply_of_ne]
  rintro ⟨rfl, rfl⟩
  exact h hs.symm

theorem fac_next (hj : j ≤ N) (hb : (b : ℕ) = a + 1) (hcase : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hp : ¬ IsProperStep N j b) (h : Matrix (Fin N) (Fin N) ℂ) :
    Fib.facOf N j a h b = minorIJ h (stepCols N j b) (stepCols N j b) := by
  have hbN := b.2
  by_cases h1 : (b : ℕ) + 1 = j
  · have h2 : (a : ℕ) < j := by omega
    have e : stepCols N j b = wIdx N j := by
      ext c
      have := c.2
      simp only [stepCols, wIdx, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1.le]
      omega
    rw [e]
    simp only [Fib.facOf, if_pos h1, if_pos h2]
  · have h3 : (b : ℕ) + 1 = N := by
      by_contra h3
      exact hp ⟨h1, h3⟩
    have h4 : ¬ (b : ℕ) + 1 ≤ j := by omega
    have e : stepCols N j b = omIdx N j := by
      ext c
      simp only [stepCols, omIdx, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h4]
      omega
    rw [e]
    simp only [Fib.facOf, if_neg h1]

theorem fac_prev (hb : (b : ℕ) = a + 1) {a' : Fin N} (ha' : (a' : ℕ) + 1 = a) (hp : ¬ IsProperStep N j a')
    (h : Matrix (Fin N) (Fin N) ℂ) : Fib.facOf N j a h a' = 1 ∧ (a : ℕ) = j := by
  have hbN := b.2
  have h1 : (a' : ℕ) + 1 = j := by
    by_contra h1
    exact hp ⟨h1, by omega⟩
  have h2 : ¬ (a : ℕ) < j := by omega
  exact ⟨by simp only [Fib.facOf, if_pos h1, if_neg h2], by omega⟩

theorem fac_ne_zero (hj : j ≤ N) (i : Fin N) {h : Matrix (Fin N) (Fin N) ℂ} (hh : IsBlockDiag j h) (hd : h.det ≠ 0)
    (a : Fin N) : Fib.facOf N j a h i ≠ 0 := by
  have hN : 0 < N := by have := i.2; omega
  have hd' := GlobalTheory.CompanionTheory.Ar.PB.CPts.detFac_ne_zero hj (⟨N - 1, by omega⟩ : Fin N) hh hd
  have e1 : j ≤ N - 1 + 1 := by omega
  simp only [detFac, if_pos e1, show N - 1 + 1 = N by omega, if_true, if_pos hj] at hd'
  simp only [Fib.facOf]
  have := left_ne_zero_of_mul hd'
  have := right_ne_zero_of_mul hd'
  split_ifs <;> first | assumption | simp

end Cols

section Xi

variable {Ψ : Type} [DecidableEq Ψ] {N : ℕ}

theorem xi_sum (τ : Ψ) {a b : Fin N} (hb : (b : ℕ) = a + 1) (D : Fin N → ℝ) (D₀ : ℝ)
    (hD : ∀ a' : Fin N, (a' : ℕ) + 1 = a → D a' = D₀) (h0 : (a : ℕ) = 0 → D₀ = 0) :
    ∑ i, (xiCoef τ a (τ, i) : ℝ) * D i = D₀ + D b - 2 * D a := by
  have e : ∀ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * D i =
      (if (i : ℕ) + 1 = a then D i else 0) + (if i = b then D i else 0) - (if i = a then 2 * D i else 0) := by
    intro i
    have e1 : ((i : ℕ) = (a : ℕ) + 1) ↔ i = b := by rw [Fin.ext_iff, hb]
    simp only [xiCoef, if_true, e1]
    push_cast
    split_ifs <;> first | ring | simp
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 2
  by_cases ha : (a : ℕ) = 0
  · rw [h0 ha]
    exact Finset.sum_eq_zero fun i _ => if_neg (by omega)
  · have hlt := a.2
    rw [Finset.sum_eq_single (⟨a - 1, by omega⟩ : Fin N)]
    · rw [if_pos (show ((a : ℕ) - 1) + 1 = a by omega)]
      exact hD _ (show ((a : ℕ) - 1) + 1 = a by omega)
    · intro i _ hne
      refine if_neg fun e => hne (Fin.ext ?_)
      show (i : ℕ) = (a : ℕ) - 1
      omega
    · simp

end Xi

section Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

theorem log_fs_smul (d : K → ℤ) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((fsHerm ι d).h fun p => c p.1 * z p) =
      Real.log ((fsHerm ι d).h z) + ∑ k, (d k : ℝ) * Real.log ‖c k‖ := by
  have hn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hc k)
  rw [(fsHerm ι d).smul c z hc,
    Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hn k)) ((fsHerm ι d).pos z hz).ne',
    Real.log_prod (fun k _ => zpow_ne_zero _ (hn k)), add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => Real.log_zpow _ _

theorem dy_sum_some (M : FlagModel y Ψ N j) {p : Ψ × Fin N} {k₀ : K} (hk : M.blk p = some k₀) {c : K → ℂ}
    (hc : ∀ k, (∀ p', M.blk p' ≠ some k) → c k = 1) :
    ∑ k, (M.dy p k : ℝ) * Real.log ‖c k‖ = Real.log ‖c k₀‖ := by
  rw [Finset.sum_eq_single k₀]
  · have e : M.dy p k₀ = 1 := by
      unfold FlagModel.dy
      rw [dite_eq_right (fun h => h p hk), if_pos hk]
    rw [e]
    simp
  · intro k _ hne
    by_cases h : ∀ p', M.blk p' ≠ some k
    · rw [hc k h]
      simp
    · have e : M.dy p k = 0 := by
        unfold FlagModel.dy
        rw [dite_eq_right h, if_neg fun e => hne (by rw [hk] at e; exact (Option.some_injective _ e).symm)]
      rw [e]
      simp
  · simp

theorem dy_sum_none (M : FlagModel y Ψ N j) {p : Ψ × Fin N} (hp : M.blk p = none) {c : K → ℂ}
    (hc : ∀ k, (∀ p', M.blk p' ≠ some k) → c k = 1) :
    ∑ k, (M.dy p k : ℝ) * Real.log ‖c k‖ = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : ∀ p', M.blk p' ≠ some k
  · rw [hc k h]
    simp
  · have e : M.dy p k = 0 := by
      unfold FlagModel.dy
      rw [dite_eq_right h, if_neg fun e => by rw [hp] at e; exact absurd e (by simp)]
    rw [e]
    simp

theorem base_one (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {z z' : (Σ k, ι k) → ℂ} {c : K → ℂ}
    (hz' : z' = fun p => c p.1 * z p) (h₁ : ∀ k, basePart M.blk z ⟨k, F.c k⟩ = 1)
    (h₂ : ∀ k, basePart M.blk z' ⟨k, F.c k⟩ = 1) : ∀ k, (∀ p', M.blk p' ≠ some k) → c k = 1 := by
  intro k hk
  have a₁ : z ⟨k, F.c ⟨k, hk⟩⟩ = 1 := h₁ ⟨k, hk⟩
  have a₂ : z' ⟨k, F.c ⟨k, hk⟩⟩ = 1 := h₂ ⟨k, hk⟩
  rw [hz'] at a₂
  have a₃ : c k * z ⟨k, F.c ⟨k, hk⟩⟩ = 1 := a₂
  rwa [a₁, mul_one] at a₃

theorem base_eq {blk : Ψ × Fin N → Option K} {z z' : (Σ k, ι k) → ℂ} {c : K → ℂ}
    (hz' : z' = fun p => c p.1 * z p) (hc : ∀ k, (∀ p', blk p' ≠ some k) → c k = 1) :
    basePart blk z' = basePart blk z := by
  funext q
  show z' ⟨q.1.1, q.2⟩ = z ⟨q.1.1, q.2⟩
  rw [hz']
  show c q.1.1 * _ = _
  rw [hc _ q.1.2, one_mul]

theorem minors_prop (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {bp : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : bp ∈ mcPts (mCoordIdeal M.x)) (hF : M.IsFrame F) (hG : M.GoodAt F (mCoordIdeal bp)) {p : Ψ × Fin N} {k : K}
    (hk : M.blk p = some k) {z z' : (Σ k, ι k) → ℂ} {c : K → ℂ} (hz' : z' = fun q => c q.1 * z q)
    (hz : basePart M.blk z = bp) (hzb : basePart M.blk z' = bp) {g g' : Matrix (Fin N) (Fin N) ℂ}
    (hg : IsBlockDiag j g) (hg' : IsBlockDiag j g') (e : ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F p z g) (e' : ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F p z' g')
    (I : Finset (Fin N)) : minorIJ g' I (stepCols N j p.2) = c k * minorIJ g I (stepCols N j p.2) := by
  refine Ind.minor_eq_of_plk M hb hF hG hk hg' hg (fun m => ?_) I
  have a := e.2 k hk m
  have a' := e'.2 k hk m
  rw [hz] at a
  rw [hzb] at a'
  simp only [plk]
  rw [← a, ← a', hz']

theorem val_ups_ne (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {bp : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : bp ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal bp)) {p : Ψ × Fin N} (hp : M.blk p = none) :
    valAt M.x (F.υ p) bp ≠ 0 := by
  obtain ⟨h0, r1, r2⟩ := hG.2.2 p hp
  have e := (reg_mul hb r1 r2).2
  rw [mul_inv_cancel₀ h0] at e
  have e1 : valAt M.x (1 : M.Ω) bp = 1 := map_one (regVal M.x hb)
  rw [e1] at e
  exact left_ne_zero_of_mul (e ▸ one_ne_zero)

end Lines

section Scal

variable {N j : ℕ}

theorem minor_one (S : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) ℂ) S S = 1 := by
  unfold minorIJ
  rw [dite_eq_left rfl, Matrix.submatrix_one _ (S.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem exists_minor_ne (hj : j ≤ N) (i : Fin N) {h : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) :
    ∃ I, minorIJ h I (stepCols N j i) ≠ 0 := by
  by_contra hc
  push_neg at hc
  have e := (GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj).1 h⁻¹ h (stepCols N j i) (stepCols N j i)
  rw [Matrix.nonsing_inv_mul _ hd.isUnit, minor_one, Finset.sum_eq_zero fun I _ => by rw [hc I, mul_zero]] at e
  exact one_ne_zero e

theorem scal_eq (hj : j ≤ N) (i : Fin N) {h B : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) (hB : IsBlockDiag j B)
    (hBt : B.BlockTriangular id) {c : ℂ}
    (e : ∀ I, minorIJ (h * B) I (stepCols N j i) = c * minorIJ h I (stepCols N j i)) :
    c = ∏ x ∈ stepCols N j i, B x x := by
  obtain ⟨I, hI⟩ := exists_minor_ne hj i hd
  have a := e I
  rw [(GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j i hj).2.2.1 h B I hB hBt] at a
  apply mul_right_cancel₀ hI
  rw [← a, mul_comm]

end Scal

section Main

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def wt (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (F : FrameData ι Ψ N M.Ω M.blk)
    (bp : (Σ k, baseIdx ι M.blk k) → ℂ) (g : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) : ℝ :=
  if IsProperStep N j i then 0 else Real.log ‖valAt M.x (F.υ (τ, i)) bp * Fib.facOf N j a g i‖

theorem normRhs_eq (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (F : FrameData ι Ψ N M.Ω M.blk)
    (z₀ z₁ : (Σ k, ι k) → ℂ) (h : Matrix (Fin N) (Fin N) ℂ) {t : ℂ} (ht : t ≠ 0)
    (hv : ∀ i, ¬ IsProperStep N j i → valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) ≠ 0)
    (hf : ∀ i, Fib.facOf N j a h i ≠ 0) :
    normRhs M τ a F z₀ z₁ h t = Real.log ‖t‖ + ∑ i, (xiCoef τ a (τ, i) : ℝ) *
      (wt M τ a F (basePart M.blk z₀) h i + (1 / 2) * (Real.log ((fsHerm ι (M.dy (τ, i))).h z₀) +
        Real.log ((fsHerm ι (M.dy (τ, i))).h z₁))) := by
  have hu : ∀ i, (if IsProperStep N j i then (1 : ℂ) else
      valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) * Fib.facOf N j a h i) ≠ 0 := fun i => by
    split_ifs with hp
    · exact one_ne_zero
    · exact mul_ne_zero (hv i hp) (hf i)
  have hn : ∀ i, ‖(if IsProperStep N j i then (1 : ℂ) else
      valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) * Fib.facOf N j a h i) ^ xiCoef τ a (τ, i)‖ ≠ 0 :=
    fun i => norm_ne_zero_iff.2 (zpow_ne_zero _ (hu i))
  have e1 : Real.log ‖t * ∏ i : Fin N, (if IsProperStep N j i then (1 : ℂ) else
      valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) * Fib.facOf N j a h i) ^ xiCoef τ a (τ, i)‖ =
      Real.log ‖t‖ + ∑ i, (xiCoef τ a (τ, i) : ℝ) * wt M τ a F (basePart M.blk z₀) h i := by
    rw [norm_mul, norm_prod, Real.log_mul (norm_ne_zero_iff.2 ht)
      (Finset.prod_ne_zero_iff.2 fun i _ => hn i), Real.log_prod fun i _ => hn i]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_zpow, Real.log_zpow]
    simp only [wt]
    split_ifs <;> simp
  have e2 : ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h z₀) + Real.log ((fsHerm ι (M.dy p)).h z₁)) =
      ∑ i, (xiCoef τ a (τ, i) : ℝ) * (Real.log ((fsHerm ι (M.dy (τ, i))).h z₀) +
        Real.log ((fsHerm ι (M.dy (τ, i))).h z₁)) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
    · intro τ' _ hne
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [xiCoef, hne]
    · simp
  unfold normRhs
  rw [e2]
  refine (congrArg₂ (· + ·) e1 rfl).trans ?_
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, add_assoc]
  congr 2
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

end Main

section Thm

theorem normRhs_same : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (z₀ z₁ z₀' z₁' : (Σ k, ι k) → ℂ) (h h' : Matrix (Fin N) (Fin N) ℂ) (t t' : ℂ), basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) → (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) → basePart M.blk z₁ = basePart M.blk z₀ → M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → SameOrbit z₀ z₀' → SameOrbit z₁ z₁' → IsBlockDiag j h → h.det ≠ 0 → IsBlockDiag j h' → h'.det ≠ 0 → t ≠ 0 → t' ≠ 0 → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀ h) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀' h') → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁' (h' * (1 + Matrix.single cb ca t'))) → normRhs M τ a F z₀ z₁ h t = normRhs M τ a F z₀' z₁' h' t' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b k₀ ca cb hb hcase hk₀ hca hcb F z₀ z₁ z₀' z₁' h h' t t' hbp hn0 hn1 hb1 hF hG
    ho0 ho1 hh hd hh' hd' ht ht' e0 e1 e0' e1'
  have hj := M.j_le
  obtain ⟨c0, hc0, q0⟩ := orbit_symm ho0
  obtain ⟨c1, hc1, q1⟩ := orbit_symm ho1
  have ob0 := base_one M F q0 (e0 a).1 (e0' a).1
  have ob1 := base_one M F q1 (e1 a).1 (e1' a).1
  have bz0 : basePart M.blk z₀' = basePart M.blk z₀ := base_eq q0 ob0
  have bz1 : basePart M.blk z₁' = basePart M.blk z₀ := (base_eq q1 ob1).trans hb1
  have hT := transv_blockDiag (a := a) (b := b) (ca := ca) (cb := cb) hj hb hcase hca hcb
  have m0 : ∀ i k, M.blk (τ, i) = some k → ∀ I, minorIJ h' I (stepCols N j i) = c0 k * minorIJ h I (stepCols N j i) :=
    fun i k hk I => minors_prop M hbp hF hG hk q0 rfl bz0 hh hh' (e0 i) (e0' i) I
  have m1 : ∀ i k, M.blk (τ, i) = some k → ∀ I, minorIJ (h' * (1 + Matrix.single cb ca t')) I (stepCols N j i) =
      c1 k * minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j i) :=
    fun i k hk I => minors_prop M hbp hF hG hk q1 hb1 bz1 (hh.mul (hT t)) (hh'.mul (hT t')) (e1 i) (e1' i) I
  have hsome : ∀ i, IsProperStep N j i → ∃ k, M.blk (τ, i) = some k := fun i hi =>
    Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
  have tri : (h⁻¹ * h').BlockTriangular id := GlobalTheory.T.block_triangular_of_proportional_minors N j h h' hj hh hh' hd hd' fun i hi => by
    obtain ⟨k, hk⟩ := hsome i hi
    exact ⟨c0 k, m0 i k hk⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = h⁻¹ * h' := ⟨_, rfl⟩
  have hBt : B.BlockTriangular id := hBd ▸ tri
  have hBb : IsBlockDiag j B := hBd ▸ (hh.inv hd.isUnit).mul hh'
  have hhB : h' = h * B := by rw [hBd, Matrix.mul_nonsing_inv_cancel_left _ _ hd.isUnit]
  have hBdet : B.det ≠ 0 := fun e => hd' (by rw [hhB, Matrix.det_mul, e, mul_zero])
  have hdiag : ∀ c, B c c ≠ 0 := fun c => by
    rw [Matrix.det_of_upperTriangular hBt] at hBdet
    exact Finset.prod_ne_zero_iff.1 hBdet c (Finset.mem_univ c)
  have hΛ : ∀ S : Finset (Fin N), ∏ x ∈ S, B x x ≠ 0 := fun S => Finset.prod_ne_zero_iff.2 fun c _ => hdiag c
  have s0 : ∀ i k, M.blk (τ, i) = some k → c0 k = ∏ x ∈ stepCols N j i, B x x := fun i k hk =>
    scal_eq hj i hd hBb hBt fun I => by rw [← hhB]; exact m0 i k hk I
  have s1 : ∀ i k, M.blk (τ, i) = some k → i ≠ a → c1 k = ∏ x ∈ stepCols N j i, B x x := fun i k hk hi =>
    scal_eq hj i hd hBb hBt fun I => by
      have e := m1 i k hk I
      rw [GlobalTheory.T.elementary_twist_minor_other_steps N j a b ca cb hj hb hcase hca hcb h' t' i hi I,
        GlobalTheory.T.elementary_twist_minor_other_steps N j a b ca cb hj hb hcase hca hcb h t i hi I, hhB] at e
      exact e
  obtain ⟨-, p2⟩ := GlobalTheory.T.elementary_twist_minor_scalar N j a b ca cb hj hb hcase hca hcb h B t t' (c1 k₀) hd hBb hBt fun I => by
    rw [← hhB]; exact m1 a k₀ hk₀ I
  have hv : ∀ i, ¬ IsProperStep N j i → valAt M.x (F.υ (τ, i)) (basePart M.blk z₀) ≠ 0 := fun i hi =>
    val_ups_ne M hbp hG ((M.blk_none _).2 hi)
  have hv' : ∀ i, ¬ IsProperStep N j i → valAt M.x (F.υ (τ, i)) (basePart M.blk z₀') ≠ 0 := by
    rw [bz0]; exact hv
  rw [normRhs_eq M τ a F z₀ z₁ h ht hv (fun i => fac_ne_zero hj i hh hd a),
    normRhs_eq M τ a F z₀' z₁' h' ht' hv' (fun i => fac_ne_zero hj i hh' hd' a), bz0]
  have f0 : ∀ i, Real.log ((fsHerm ι (M.dy (τ, i))).h z₀') = Real.log ((fsHerm ι (M.dy (τ, i))).h z₀) +
      ∑ k, (M.dy (τ, i) k : ℝ) * Real.log ‖c0 k‖ := fun i => by
    rw [q0]; exact log_fs_smul _ hc0 hn0
  have f1 : ∀ i, Real.log ((fsHerm ι (M.dy (τ, i))).h z₁') = Real.log ((fsHerm ι (M.dy (τ, i))).h z₁) +
      ∑ k, (M.dy (τ, i) k : ℝ) * Real.log ‖c1 k‖ := fun i => by
    rw [q1]; exact log_fs_smul _ hc1 hn1
  obtain ⟨D, hD⟩ : ∃ D : Fin N → ℝ, D = fun i => wt M τ a F (basePart M.blk z₀) h' i -
      wt M τ a F (basePart M.blk z₀) h i + (1 / 2) * (∑ k, (M.dy (τ, i) k : ℝ) * Real.log ‖c0 k‖ +
        ∑ k, (M.dy (τ, i) k : ℝ) * Real.log ‖c1 k‖) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = ∏ x ∈ (stepCols N j a).erase ca, B x x := ⟨_, rfl⟩
  have hβ0 : β ≠ 0 := hβ ▸ hΛ _
  have hproper : ∀ i, IsProperStep N j i → i ≠ a → D i = Real.log ‖∏ x ∈ stepCols N j i, B x x‖ := fun i hi hia => by
    obtain ⟨k, hk⟩ := hsome i hi
    rw [hD]
    simp only [wt, if_pos hi]
    rw [dy_sum_some M hk ob0, dy_sum_some M hk ob1, s0 i k hk, s1 i k hk hia]
    ring
  have hprev : ∀ a' : Fin N, (a' : ℕ) + 1 = a → D a' = Real.log ‖β‖ := fun a' ha' => by
    have hne : a' ≠ a := fun e => by rw [e] at ha'; omega
    by_cases hp : IsProperStep N j a'
    · rw [hproper a' hp hne, cols_prev hj hb hcase hca ha' hp, hβ]
    · obtain ⟨g1, g2⟩ := fac_prev (j := j) hb ha' hp h
      obtain ⟨g3, -⟩ := fac_prev (j := j) hb ha' hp h'
      have hbl := (M.blk_none (τ, a')).2 hp
      rw [hD]
      simp only [wt, if_neg hp]
      rw [dy_sum_none M hbl ob0, dy_sum_none M hbl ob1, g1, g3, hβ, cols_first hj hb hcase hca (Or.inr g2)]
      simp
  have hzero : (a : ℕ) = 0 → Real.log ‖β‖ = 0 := fun h0 => by
    rw [hβ, cols_first hj hb hcase hca (Or.inl h0)]
    simp
  obtain ⟨cn, hcbn, hcam⟩ := cols_next hj hb hcase hca hcb
  have hDb : D b = Real.log ‖∏ x ∈ stepCols N j b, B x x‖ := by
    have hne : b ≠ a := fun e => by rw [e] at hb; omega
    by_cases hp : IsProperStep N j b
    · exact hproper b hp hne
    · have hbl := (M.blk_none (τ, b)).2 hp
      have e : Fib.facOf N j a h' b = Fib.facOf N j a h b * ∏ x ∈ stepCols N j b, B x x := by
        rw [fac_next hj hb hcase hp, fac_next hj hb hcase hp, hhB]
        exact (GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j b hj).2.2.1 h B _ hBb hBt
      rw [hD]
      simp only [wt, if_neg hp]
      rw [dy_sum_none M hbl ob0, dy_sum_none M hbl ob1, e, ← mul_assoc, norm_mul _ (∏ x ∈ stepCols N j b, B x x),
        Real.log_mul (norm_ne_zero_iff.2 (mul_ne_zero (hv b hp) (fac_ne_zero hj b hh hd a)))
          (norm_ne_zero_iff.2 (hΛ _))]
      ring
  have hap : IsProperStep N j a := by
    by_contra hp
    have := (M.blk_none (τ, a)).2 hp
    rw [hk₀] at this
    exact absurd this (by simp)
  have hDa : 2 * D a = Real.log ‖∏ x ∈ stepCols N j a, B x x‖ + Real.log ‖c1 k₀‖ := by
    rw [hD]
    simp only [wt, if_pos hap]
    rw [dy_sum_some M hk₀ ob0, dy_sum_some M hk₀ ob1, s0 a k₀ hk₀]
    ring
  have key := xi_sum τ hb D (Real.log ‖β‖) hprev hzero
  have hlogs : Real.log ‖c1 k₀‖ + Real.log ‖t‖ = Real.log ‖β‖ + (Real.log ‖t'‖ + Real.log ‖B cb cb‖) := by
    rw [← Real.log_mul (norm_ne_zero_iff.2 (hc1 k₀)) (norm_ne_zero_iff.2 ht),
      ← Real.log_mul (norm_ne_zero_iff.2 ht') (norm_ne_zero_iff.2 (hdiag cb)),
      ← Real.log_mul (norm_ne_zero_iff.2 hβ0) (mul_ne_zero (norm_ne_zero_iff.2 ht') (norm_ne_zero_iff.2 (hdiag cb))),
      ← norm_mul, ← norm_mul, ← norm_mul, p2, hβ]
  have hDb' : D b = Real.log ‖∏ x ∈ stepCols N j a, B x x‖ + Real.log ‖B cb cb‖ := by
    rw [hDb, cn, Finset.prod_insert hcbn, norm_mul, mul_comm,
      Real.log_mul (norm_ne_zero_iff.2 (hΛ _)) (norm_ne_zero_iff.2 (hdiag cb))]
  have hsum : ∑ i, (xiCoef τ a (τ, i) : ℝ) * D i = Real.log ‖t‖ - Real.log ‖t'‖ := by
    rw [key, hDb', hDa]
    linarith
  have hsplit : ∑ i, (xiCoef τ a (τ, i) : ℝ) * (wt M τ a F (basePart M.blk z₀) h' i +
      (1 / 2) * (Real.log ((fsHerm ι (M.dy (τ, i))).h z₀') + Real.log ((fsHerm ι (M.dy (τ, i))).h z₁'))) =
      ∑ i, (xiCoef τ a (τ, i) : ℝ) * (wt M τ a F (basePart M.blk z₀) h i +
        (1 / 2) * (Real.log ((fsHerm ι (M.dy (τ, i))).h z₀) + Real.log ((fsHerm ι (M.dy (τ, i))).h z₁))) +
      ∑ i, (xiCoef τ a (τ, i) : ℝ) * D i := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [f0 i, f1 i, hD]
    ring
  rw [hsplit, hsum]
  ring

end Thm

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Same
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentOrbitComparisonStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_orbit_comparison : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (z₀ z₁ z₀' z₁' : (Σ k, ι k) → ℂ) (h h' : Matrix (Fin N) (Fin N) ℂ) (t t' : ℂ), basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) → (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) → basePart M.blk z₁ = basePart M.blk z₀ → M.IsFrame F → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → SameOrbit z₀ z₀' → SameOrbit z₁ z₁' → IsBlockDiag j h → h.det ≠ 0 → IsBlockDiag j h' → h'.det ≠ 0 → t ≠ 0 → t' ≠ 0 → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀ h) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀' h') → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁' (h' * (1 + Matrix.single cb ca t'))) → normRhs M τ a F z₀ z₁ h t = normRhs M τ a F z₀' z₁' h' t' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Same.normRhs_same | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Same.normRhs_same | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Same.normRhs_same <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwoFramesOrbit
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Indep

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem orbit_ne {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z' z) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  intro k
  obtain ⟨i, hi⟩ := hz k
  exact ⟨i, mul_ne_zero (hc k) hi⟩

theorem eq_of_orbit_of_normalised {u v : (Σ k, ι k) → ℂ} (h : SameOrbit u v) (e : ∀ k, ι k)
    (hu : ∀ k, u ⟨k, e k⟩ = 1) (hv : ∀ k, v ⟨k, e k⟩ = 1) : u = v := by
  obtain ⟨c, hc, rfl⟩ := h
  have h1 : ∀ k, c k = 1 := fun k => by
    have h2 : c k * v ⟨k, e k⟩ = 1 := hu k
    rwa [hv k, mul_one] at h2
  funext p
  show c p.1 * v p = v p
  rw [h1 p.1, one_mul]

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem base_of_orbit (M : FlagModel y Ψ N j) {z z' : (Σ k, ι k) → ℂ} (ho : SameOrbit z z')
    (hz : basePart M.blk z ∈ mcPts (mCoordIdeal M.x)) :
    mCoordIdeal (basePart M.blk z') = mCoordIdeal (basePart M.blk z) ∧
      basePart M.blk z' ∈ mcPts (mCoordIdeal M.x) := by
  obtain ⟨c, hc, rfl⟩ := GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho
  have h := GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main (NonPluckerBlocks M.blk) (baseIdx ι M.blk) M.Ω M.x (basePart M.blk z)
    (fun k => c k.1) (fun k => hc k.1)
  exact ⟨h.1, (h.2 hz).1⟩

theorem normRhs_indep : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F F' : FrameData ι Ψ N M.Ω M.blk) (z₀ z₁ z₀' z₁' : (Σ k, ι k) → ℂ) (h h' : Matrix (Fin N) (Fin N) ℂ) (t t' : ℂ), basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) → (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) → basePart M.blk z₁ = basePart M.blk z₀ → M.IsFrame F → M.IsFrame F' → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → M.GoodAt F' (mCoordIdeal (basePart M.blk z₀')) → SameOrbit z₀ z₀' → SameOrbit z₁ z₁' → IsBlockDiag j h → h.det ≠ 0 → IsBlockDiag j h' → h'.det ≠ 0 → t ≠ 0 → t' ≠ 0 → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀ h) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F' (τ, i) z₀' h') → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F' (τ, i) z₁' (h' * (1 + Matrix.single cb ca t'))) → normRhs M τ a F z₀ z₁ h t = normRhs M τ a F' z₀' z₁' h' t' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b k₀ ca cb hab hstep hblk hca hcb F F' z₀ z₁ z₀' z₁' h h' t t' hmc hn₀ hn₁ hbase
    hF hF' hG hG' ho₀ ho₁ hh hd hh' hd' ht ht' hE₀ hE₁ hE₀' hE₁'
  obtain ⟨hid, hmc'⟩ := base_of_orbit M ho₀ hmc
  have hn₀' := orbit_ne (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho₀) hn₀
  have hn₁' := orbit_ne (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho₁) hn₁
  have hbase' : basePart M.blk z₁' = basePart M.blk z₀' := by
    have h1 : SameOrbit (basePart M.blk z₁') (basePart M.blk z₁) :=
      basePart_orbit M.blk (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm ho₁)
    rw [hbase] at h1
    exact eq_of_orbit_of_normalised
      (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_trans h1 (basePart_orbit M.blk ho₀)) F'.c (hE₁' a).1 (hE₀' a).1
  obtain ⟨w₀, w₁, S, hw₀, hw₁, hS, hSd, hX₀, hX₁, hnorm⟩ :=
    GlobalTheory.T.flag_adjacent_frame_comparison K ι Φ y Ψ N j M τ a b k₀ ca cb hab hstep hblk hca hcb F F' z₀' z₁' h' t' hmc' hn₀' hn₁' hbase'
      hF hF' (by rw [hid]; exact hG) hG' hh' hd' ht' hE₀' hE₁'
  rw [← hnorm]
  exact GlobalTheory.T.flag_adjacent_orbit_comparison K ι Φ y Ψ N j M τ a b k₀ ca cb hab hstep hblk hca hcb F z₀ z₁ w₀ w₁ h (S * h') t t' hmc hn₀ hn₁
    hbase hF hG (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_trans ho₀ (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm hw₀))
    (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_trans ho₁ (GlobalTheory.CompanionTheory.Ar.PB.WSq.orbit_symm hw₁)) hh hd (hS.mul hh')
    (by rw [Matrix.det_mul]; exact mul_ne_zero hSd hd') ht ht' hE₀ hE₁ hX₀ hX₁

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Indep
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwoFramesOrbitStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_adjacent_two_frames_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F F' : FrameData ι Ψ N M.Ω M.blk) (z₀ z₁ z₀' z₁' : (Σ k, ι k) → ℂ) (h h' : Matrix (Fin N) (Fin N) ℂ) (t t' : ℂ), basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) → (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) → (∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0) → basePart M.blk z₁ = basePart M.blk z₀ → M.IsFrame F → M.IsFrame F' → M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) → M.GoodAt F' (mCoordIdeal (basePart M.blk z₀')) → SameOrbit z₀ z₀' → SameOrbit z₁ z₁' → IsBlockDiag j h → h.det ≠ 0 → IsBlockDiag j h' → h'.det ≠ 0 → t ≠ 0 → t' ≠ 0 → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀ h) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))) → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F' (τ, i) z₀' h') → (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F' (τ, i) z₁' (h' * (1 + Matrix.single cb ca t'))) → normRhs M τ a F z₀ z₁ h t = normRhs M τ a F' z₀' z₁' h' t' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Indep.normRhs_indep | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Indep.normRhs_indep | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Indep.normRhs_indep <;> assumption)
end
