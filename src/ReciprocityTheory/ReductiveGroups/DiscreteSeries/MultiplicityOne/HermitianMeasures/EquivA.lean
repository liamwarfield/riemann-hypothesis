module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.HaarUp

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.PsiGen
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem psiGen_norm (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (g : Mat k r) :
    ‖Formalism.MainNotions.S.psiGen k r z c g‖ = 1 := by
  unfold Formalism.MainNotions.S.psiGen
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

open Formalism.QuantumDeterminants.WeylGroupFacts in
theorem ellA_mul {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {m m' : Mat k r}
    (hm : m ∈ Nset k r) (hm' : m' ∈ Nset k r) (a : Fin r) :
    Formalism.MainNotions.S.ellA k r z (m * m') a = Formalism.MainNotions.S.ellA k r z m a + Formalism.MainNotions.S.ellA k r z m' a := by
  have hc := ((nset_iff m).1 hm).2
  have hc' := ((nset_iff m').1 hm').2
  have hi : (Formalism.QuantumDeterminants.eI k r a).val < r := a.isLt
  unfold Formalism.MainNotions.S.ellA
  split_ifs with h
  · exact mul_apply_add hc hc' _ _ hi
      (show (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩).val ≤ r + k by show a.val + 1 ≤ r + k; omega)
      (show (Formalism.QuantumDeterminants.eI k r a).val < (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩).val by
        show a.val < a.val + 1; omega)
      (Or.inl (show (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h⟩).val ≤ (Formalism.QuantumDeterminants.eI k r a).val + 1 by
        show a.val + 1 ≤ a.val + 1; omega))
  · simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : r ≤ q.val ∧ q.val ≤ r + k
    · rw [mul_apply_add hc hc' _ _ hi hq.2
        (show (Formalism.QuantumDeterminants.eI k r a).val < q.val by show a.val < q.val; omega)
        (Or.inr (show r ≤ (Formalism.QuantumDeterminants.eI k r a).val + 1 by show r ≤ a.val + 1; omega)), add_mul]
    · have hz0 : z q = 0 := hz q (by omega)
      rw [hz0, mul_zero, mul_zero, mul_zero, add_zero]

open Formalism.QuantumDeterminants.WeylGroupFacts in
theorem ellA_conj {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h m : Mat k r}
    (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) (a : Fin r) :
    Formalism.MainNotions.S.ellA k r z (h * m * h⁻¹) a = Formalism.MainNotions.S.ellA k r z m a := by
  have hb := uw_block hh
  have hb' := uw_block (uw_inv hh)
  have hz' : h⁻¹ *ᵥ z = z := (uw_inv hh).2.2
  have hrow : ∀ p, h (Formalism.QuantumDeterminants.eI k r a) p = if Formalism.QuantumDeterminants.eI k r a = p then 1 else 0 :=
    fun p => hb.2 _ p (Or.inl (show (Formalism.QuantumDeterminants.eI k r a).val < r from a.isLt))
  unfold Formalism.MainNotions.S.ellA
  split_ifs with h1
  · have hcol : ∀ q, h⁻¹ q (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h1⟩) =
        if q = Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h1⟩ then 1 else 0 :=
      fun q => hb'.1 q _ (Or.inl (show (Formalism.QuantumDeterminants.eI k r ⟨a.val + 1, h1⟩).val < r from h1))
    rw [mul_apply_of_col _ _ _ hcol, mul_apply_of_row _ _ _ hrow]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulVec_apply_of_row _ _ hrow, hz']

theorem psiGen_mul {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin r → ℂ) {m m' : Mat k r}
    (hm : m ∈ Nset k r) (hm' : m' ∈ Nset k r) :
    Formalism.MainNotions.S.psiGen k r z c (m * m') = Formalism.MainNotions.S.psiGen k r z c m * Formalism.MainNotions.S.psiGen k r z c m' := by
  unfold Formalism.MainNotions.S.psiGen
  rw [← Complex.exp_add]
  have e : ∑ a, c a * Formalism.MainNotions.S.ellA k r z (m * m') a =
      (∑ a, c a * Formalism.MainNotions.S.ellA k r z m a) + ∑ a, c a * Formalism.MainNotions.S.ellA k r z m' a := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ellA_mul hz hm hm' a, mul_add]
  rw [e, Complex.add_re, Complex.ofReal_add, mul_add]

theorem psiGen_conj {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin r → ℂ) {h m : Mat k r}
    (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) :
    Formalism.MainNotions.S.psiGen k r z c (h * m * h⁻¹) = Formalism.MainNotions.S.psiGen k r z c m := by
  unfold Formalism.MainNotions.S.psiGen
  have e : ∑ a, c a * Formalism.MainNotions.S.ellA k r z (h * m * h⁻¹) a = ∑ a, c a * Formalism.MainNotions.S.ellA k r z m a :=
    Finset.sum_congr rfl fun a _ => by rw [ellA_conj hz hh hm a]
  rw [e]

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
end
end

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ} {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

theorem equivA_measurable_rmulF (a : Mat k r) : Measurable (rmulF a : Mt k r → Mt k r) := by
  have : Continuous (rmulF a : Mt k r → Mt k r) := by
    unfold rmulF
    exact Continuous.matrix_mul continuous_id continuous_const
  exact this.measurable

theorem equivA_measurable_conjM (a : Mat k r) : Measurable (conjM a : Mt k r → Mt k r) := by
  have : Continuous (conjM a : Mt k r → Mt k r) := by
    unfold conjM
    exact Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const
  exact this.measurable

open Formalism.QuantumDeterminants.WeylGroupFacts in
theorem shift_measurePreserving (hSF : HaarUniqueSF) (hCW : ClosedW) (hHW : HaarWExists) (hCN : ClosedN)
    (hHN : HaarNExists) (hc : ConjInvRaw) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {μW μN : Measure (Mt k r)} (hW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Nset k r) μN)
    {h₀ m₀ : Mat k r} (hh₀ : h₀ ∈ UWset k r z) (hm₀ : m₀ ∈ Nset k r) :
    MeasurePreserving (fun p : Mt k r × Mt k r =>
      Prod.mk (α := Mt k r) (β := Mt k r) (Matrix.of p.1 * h₀ : Mat k r) (h₀⁻¹ * Matrix.of p.2 * h₀ * m₀ : Mat k r))
      (μW.prod μN) (μW.prod μN) := by
  have hW' := isHaarOn_fourier_of_isHaarOn_main hSF hCW hHW hz hT hW
  have hN' := haarUp_N hSF hCN hHN hN
  have hσW : SigmaFinite μW := hW.1
  have hσN : SigmaFinite μN := hN.1
  have hi : h₀⁻¹ ∈ UWset k r z := uw_inv hh₀
  have hu : IsUnit h₀.det := isUnit_of_uh hh₀.1
  have hconj := conjInv_N hSF hCN hHN hc hz hT hN h₀⁻¹ hi
  have h1 : MeasurePreserving (rmulF h₀ : Mt k r → Mt k r) μW μW :=
    ⟨equivA_measurable_rmulF h₀, hW'.right h₀ hh₀⟩
  have h2 : MeasurePreserving (fun x : Mt k r => rmulF m₀ (conjM h₀⁻¹ x)) μN μN :=
    (⟨equivA_measurable_rmulF m₀, hN'.right m₀ hm₀⟩ : MeasurePreserving (rmulF m₀ : Mt k r → Mt k r) μN μN).comp
      ⟨equivA_measurable_conjM h₀⁻¹, hconj⟩
  have h3 := h1.prod h2
  convert h3 using 1
  funext p
  simp only [Prod.map, rmulF, conjM, Matrix.nonsing_inv_nonsing_inv _ hu]
  rfl

open Formalism.QuantumDeterminants.WeylGroupFacts in
theorem integrand_shift (hCW : ClosedW) (hCN : ClosedN) (hUN : UWNormal) {z : Fin (2 * r + k + 1) → ℂ}
    (hz : inWb k r z) (c : Fin r → ℂ)
    {π : Lap.Mat k r → (Vp →L[ℂ] Vp)} (hπ : Formalism.MainNotions.S.IsURepOn (UWset k r z) π) (f : Lap.Mat k r → ℂ) (ξ : Vp)
    {h₀ m₀ g h m : Mat k r} (hh₀ : h₀ ∈ UWset k r z) (hm₀ : m₀ ∈ Nset k r) (hh : h ∈ UWset k r z)
    (hm : m ∈ Nset k r) :
    f (h * m * (h₀ * m₀ * g)) • Lap.chiInv (Formalism.MainNotions.S.psiGen k r z c) π h m ξ =
      Formalism.MainNotions.S.psiGen k r z c m₀ • π h₀ (f (h * h₀ * (h₀⁻¹ * m * h₀ * m₀) * g) •
        Lap.chiInv (Formalism.MainNotions.S.psiGen k r z c) π (h * h₀) (h₀⁻¹ * m * h₀ * m₀) ξ) := by
  have hi : h₀⁻¹ ∈ UWset k r z := uw_inv hh₀
  have hhi : h⁻¹ ∈ UWset k r z := uw_inv hh
  have hu : IsUnit h₀.det := isUnit_of_uh hh₀.1
  have hii : h₀⁻¹⁻¹ = h₀ := Matrix.nonsing_inv_nonsing_inv _ hu
  have hcN : h₀⁻¹ * m * h₀ ∈ Nset k r := by
    have := (hUN k r z hz h₀⁻¹ hi m hm).1
    rwa [hii] at this
  have hψ : Formalism.MainNotions.S.psiGen k r z c (h₀⁻¹ * m * h₀ * m₀) =
      Formalism.MainNotions.S.psiGen k r z c m * Formalism.MainNotions.S.psiGen k r z c m₀ := by
    rw [psiGen_mul hz c hcN hm₀]
    congr 1
    have := psiGen_conj hz c hi hm
    rwa [hii] at this
  have hmat : h * h₀ * (h₀⁻¹ * m * h₀ * m₀) * g = h * m * (h₀ * m₀ * g) := by
    have e : h₀ * h₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    calc h * h₀ * (h₀⁻¹ * m * h₀ * m₀) * g = h * (h₀ * h₀⁻¹) * m * (h₀ * m₀ * g) := by
          simp only [Matrix.mul_assoc]
      _ = h * m * (h₀ * m₀ * g) := by rw [e, Matrix.mul_one]
  have hπ1 : π h₀ (π (h * h₀)⁻¹ ξ) = π h⁻¹ ξ := by
    rw [Matrix.mul_inv_rev, hπ.1.2 _ hi _ hhi, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
      ← hπ.1.2 _ hh₀ _ hi, Matrix.mul_nonsing_inv _ hu, hπ.1.1, one_apply_eq_self]
  have hn : Formalism.MainNotions.S.psiGen k r z c m₀ * star (Formalism.MainNotions.S.psiGen k r z c m₀) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, psiGen_norm]
    simp
  unfold Lap.chiInv
  have key : ∀ F : ℂ, F * star (Formalism.MainNotions.S.psiGen k r z c m) = Formalism.MainNotions.S.psiGen k r z c m₀ *
      (F * (star (Formalism.MainNotions.S.psiGen k r z c m₀) * star (Formalism.MainNotions.S.psiGen k r z c m))) := fun F => by
    linear_combination (-(F * star (Formalism.MainNotions.S.psiGen k r z c m))) * hn
  rw [hmat, hψ, map_smul, map_smul, hπ1]
  simp only [smul_smul, star_mul]
  congr 1
  exact key _

end ReciprocityTheory.ChartRestriction.DS.Mult1.S0.A
