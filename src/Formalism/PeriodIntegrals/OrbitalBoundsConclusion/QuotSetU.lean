module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.IsCompactInterUnitBox
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.ExistsModularFunction
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotSetU
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.GPolar
open Matrix
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace PI.QuotSetU.UnitaryGroupMassFormula

open PI PI.QuotSetU

lemma uh_right {k r : ℕ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : g * Hpk k r * gᴴ = Hpk k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have h1 : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    calc (Hpk k r * gᴴ * Hpk k r) * g = Hpk k r * (gᴴ * Hpk k r * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hpk_mul_self]
  have h2 : g * (Hpk k r * gᴴ * Hpk k r) = 1 := mul_eq_one_comm.mp h1
  calc g * Hpk k r * gᴴ = g * Hpk k r * gᴴ * (Hpk k r * Hpk k r) := by
        rw [hpk_mul_self, Matrix.mul_one]
    _ = g * (Hpk k r * gᴴ * Hpk k r) * Hpk k r := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h2, Matrix.one_mul]

lemma uh_conjTranspose {k r : ℕ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : gᴴ ∈ UH (Hpk k r) := by
  show gᴴᴴ * Hpk k r * gᴴ = Hpk k r
  rw [Matrix.conjTranspose_conjTranspose]
  exact uh_right hg

theorem unitary_group_polar_decomposition : PolarUH := by
  intro k r g hg
  have hHH : Hpk k r * Hpk k r = 1 := hpk_mul_self k r
  have hHt : (Hpk k r)ᴴ = Hpk k r := hpk_conjTranspose k r
  have hA0 : 0 ≤ gᴴ * g := (posSemidef_conjTranspose_mul_self g).nonneg
  have hAt : (gᴴ * g)ᴴ = gᴴ * g := (Matrix.nonneg_iff_posSemidef.mp hA0).isHermitian.eq
  have hAHA : (gᴴ * g) * Hpk k r * (gᴴ * g) = Hpk k r := by
    have h : (gᴴ * g)ᴴ * Hpk k r * (gᴴ * g) = Hpk k r := uh_mul (uh_conjTranspose hg) hg
    rwa [hAt] at h
  have hS0 : 0 ≤ CFC.sqrt (gᴴ * g) := CFC.sqrt_nonneg _
  have hSS : CFC.sqrt (gᴴ * g) * CFC.sqrt (gᴴ * g) = gᴴ * g := CFC.sqrt_mul_sqrt_self _ hA0
  set S := CFC.sqrt (gᴴ * g) with hS
  have hSt : Sᴴ = S := (Matrix.nonneg_iff_posSemidef.mp hS0).isHermitian.eq
  have hgdet : IsUnit g.det := uh_det hg
  have hAdet : IsUnit (gᴴ * g).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose]
    exact hgdet.star.mul hgdet
  have hSdet : IsUnit S.det := by
    have h : IsUnit (S.det * S.det) := by rw [← Matrix.det_mul, hSS]; exact hAdet
    exact isUnit_of_mul_isUnit_left h
  have hT0 : 0 ≤ Hpk k r * S * Hpk k r := by
    have h := star_left_conjugate_nonneg hS0 (Hpk k r)
    rwa [Matrix.star_eq_conjTranspose, hHt] at h
  have hSinvt : (S⁻¹)ᴴ = S⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hSt]
  have hSinv0 : 0 ≤ S⁻¹ := by
    have h := star_left_conjugate_nonneg hS0 S⁻¹
    rwa [Matrix.star_eq_conjTranspose, hSinvt, Matrix.mul_assoc, Matrix.mul_nonsing_inv S hSdet,
      Matrix.mul_one] at h
  have hsq : (Hpk k r * S * Hpk k r) * (Hpk k r * S * Hpk k r) = S⁻¹ * S⁻¹ := by
    have h1 : Hpk k r * S * Hpk k r * (Hpk k r * S * Hpk k r) = Hpk k r * (gᴴ * g) * Hpk k r := by
      calc Hpk k r * S * Hpk k r * (Hpk k r * S * Hpk k r)
          = Hpk k r * S * (Hpk k r * Hpk k r) * S * Hpk k r := by simp only [Matrix.mul_assoc]
        _ = Hpk k r * (S * S) * Hpk k r := by rw [hHH, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = Hpk k r * (gᴴ * g) * Hpk k r := by rw [hSS]
    have h2 : S⁻¹ * S⁻¹ = (gᴴ * g)⁻¹ := by rw [← Matrix.mul_inv_rev, hSS]
    have h3 : Hpk k r * (gᴴ * g) * Hpk k r * (gᴴ * g) = 1 := by
      calc Hpk k r * (gᴴ * g) * Hpk k r * (gᴴ * g)
          = Hpk k r * ((gᴴ * g) * Hpk k r * (gᴴ * g)) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hAHA, hHH]
    rw [h1, h2, (Matrix.inv_eq_left_inv h3).symm]
  have hTS : Hpk k r * S * Hpk k r = S⁻¹ := (CFC.mul_self_eq_mul_self_iff _ _ hT0 hSinv0).mp hsq
  have hSU : S ∈ UH (Hpk k r) := by
    show Sᴴ * Hpk k r * S = Hpk k r
    rw [hSt]
    have h5 : S * (Hpk k r * S * Hpk k r) = 1 := by rw [hTS, Matrix.mul_nonsing_inv S hSdet]
    calc S * Hpk k r * S = S * Hpk k r * S * (Hpk k r * Hpk k r) := by rw [hHH, Matrix.mul_one]
      _ = S * (Hpk k r * S * Hpk k r) * Hpk k r := by simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [h5, Matrix.one_mul]
  refine ⟨g * S⁻¹, S, uh_mul hg (uh_inv hSU), ?_, hSU, hSt, ?_⟩
  · rw [Matrix.conjTranspose_mul, hSinvt]
    calc S⁻¹ * gᴴ * (g * S⁻¹) = S⁻¹ * (gᴴ * g) * S⁻¹ := by simp only [Matrix.mul_assoc]
      _ = S⁻¹ * S * (S * S⁻¹) := by rw [← hSS]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.nonsing_inv_mul S hSdet, Matrix.mul_nonsing_inv S hSdet, Matrix.one_mul]
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul S hSdet, Matrix.mul_one]

theorem unitary_group_modular_function_trivial : TrivG := by
  exact trivG_of unitary_group_polar_decomposition maximal_compact_isCompact

end PI.QuotSetU.UnitaryGroupMassFormula

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.QuotSetUOf
open MeasureTheory Matrix

namespace PI.QuotSetU.UnitaryGroupMassFormula

open PI PI.QuotSetU

theorem quotSetU_of (hUH : UHGroup) (hSub : SsetSub) (hSG : SsetGroup) (hMod : ModExists)
    (hTG : TrivG) (hTS : TrivS) : PI.QuotSetU := by
  intro k r z hz hT
  refine ⟨hUH k r, hSG k r z hz hT, hSub k r z, ?_, ?_⟩
  · intro μG hμ
    obtain ⟨D, hD, hD1⟩ := hMod _ _ (hUH k r)
    exact hD1 (hTG k r D hD) μG hμ
  · intro μS hμ
    obtain ⟨D, hD, hD1⟩ := hMod _ _ (hSG k r z hz hT)
    exact hD1 (hTS k r z hz hT D hD) μS hμ

end PI.QuotSetU.UnitaryGroupMassFormula
end

open PI.QuotSetU.UnitaryGroupMassFormula in
theorem quotient_measure_unitary_group : PI.QuotSetU :=
  quotSetU_of unitary_hermitian_group siegel_set_subset (SW.sGroup_of unitary_weyl_compact) exists_modular_function unitary_group_modular_function_trivial
    (SW.trivS_of (SW.sGroup_of unitary_weyl_compact) unitary_weyl_compact SW.nilpotent_subgroup SW.unipotent_radical_contracting)
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGGenRatio
theorem generic_ratio_bound : Formalism.L2.SG.GGMirabolic.GenericRatioOfBound := by
  unfold Formalism.L2.SG.GGMirabolic.GenericRatioOfBound
  intro hMir hCard
  unfold Formalism.L2.SG.GGMirabolic.GenericRatio
  intro F _ _ k ψ₀ hψ V _ _ _ π hirr hgen
  have hb := hMir F k ψ₀ hψ V π hirr hgen
  rw [hCard F k]
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hqR : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
  have hx : ∀ i ∈ Finset.Ico 1 k, (1 : ℝ) < (Fintype.card F : ℝ) ^ i := by
    intro i hi
    have hi1 : i ≠ 0 := by
      simp only [Finset.mem_Ico] at hi
      omega
    exact one_lt_pow₀ hqR hi1
  have hsum : ∑ i ∈ Finset.Ico 1 k, i = k * (k - 1) / 2 := by
    rw [← Finset.sum_range_id]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk]
      simp
  have hP : 0 < ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) :=
    Finset.prod_pos fun i hi => sub_pos.mpr (hx i hi)
  have hcast : ((∏ i ∈ Finset.Ico 1 k, (Fintype.card F ^ i - 1) : ℕ) : ℝ)
      = ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hPD : ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) ≤ (Module.finrank ℂ V : ℝ) := by
    rw [← hcast]
    exact_mod_cast hb
  have hR : ∏ i ∈ Finset.Ico 1 k, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)⁻¹
      = (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) / ∏ i ∈ Finset.Ico 1 k, ((Fintype.card F : ℝ) ^ i - 1) := by
    rw [← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have h1 := hx i hi
    have h0 : (Fintype.card F : ℝ) ^ i ≠ 0 := (lt_trans one_pos h1).ne'
    have h2 : (Fintype.card F : ℝ) ^ i - 1 ≠ 0 := (sub_pos.mpr h1).ne'
    field_simp
  rw [hR, Nat.cast_pow]
  gcongr
  all_goals first
    | exact hPD
    | exact hP.le
    | exact hP
    | positivity
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GGCardUni
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCardinality.UniMatUpper
namespace PI.GGCardUniWork

open Finset Matrix Formalism.L2.SG.GGMirabolic

variable {F : Type} [Field F] [Fintype F] {k : ℕ}

abbrev Pairs (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}

def uniMat (f : Pairs k → F) : Matrix (Fin k) (Fin k) F :=
  fun i j => if i = j then 1 else if h : i < j then f ⟨(i, j), h⟩ else 0

theorem uniMat_upper (f : Pairs k → F) : (uniMat f).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  simp [uniMat, ne_of_gt hji, not_lt.mpr hji.le]

theorem uniMat_det (f : Pairs k → F) : (uniMat f).det = 1 := by
  rw [Matrix.det_of_upperTriangular (uniMat_upper f)]
  simp [uniMat]

noncomputable def uniGL (f : Pairs k → F) : GL (Fin k) F :=
  GeneralLinearGroup.mkOfDetNeZero (uniMat f) (by rw [uniMat_det]; exact one_ne_zero)

theorem uniGL_coe (f : Pairs k → F) : ((uniGL f : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) = uniMat f := rfl

theorem isUni_uniGL (f : Pairs k → F) : IsUni k (uniGL f) := by
  unfold IsUni
  refine ⟨fun i => ?_, fun i j h => ?_⟩
  · simp [uniGL_coe, uniMat]
  · simp [uniGL_coe, uniMat, ne_of_gt h, not_lt.mpr h.le]

noncomputable def uniEquiv : {x : GL (Fin k) F // IsUni k x} ≃ (Pairs k → F) where
  toFun x p := (x.1 : Matrix (Fin k) (Fin k) F) p.1.1 p.1.2
  invFun f := ⟨uniGL f, isUni_uniGL f⟩
  left_inv x := by
    obtain ⟨x, hd, hl⟩ := x
    apply Subtype.ext
    apply GeneralLinearGroup.ext
    intro i j
    simp only [uniGL_coe, uniMat]
    by_cases h : i = j
    · subst h; simp [hd i]
    · by_cases h' : i < j
      · simp [h, h']
      · have : j < i := lt_of_le_of_ne (not_lt.mp h') (Ne.symm h)
        simp [h, h', hl i j this]
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    have h1 : i ≠ j := ne_of_lt h
    simp [uniGL_coe, uniMat, h1, h]

theorem card_pairs (k : ℕ) : Fintype.card (Pairs k) = k * (k - 1) / 2 := by
  have hI : ∀ j : Fin k, (∑ i : Fin k, if i < j then 1 else 0) = (j : ℕ) := fun j => by
    rw [← Finset.card_filter]
    rw [show (Finset.univ.filter fun i : Fin k => i < j) = Finset.Iio j by ext i; simp]
    exact Fin.card_Iio j
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  simp only [hI]
  have h3 : ∑ j : Fin k, (j : ℕ) = ∑ j ∈ Finset.range k, j := Fin.sum_univ_eq_sum_range (fun i => i) k
  rw [h3, Finset.sum_range_id]

theorem cardUni : CardUni := by
  intro F _ _ k
  unfold cardU
  rw [Nat.card_congr (uniEquiv (F := F) (k := k)), Nat.card_eq_fintype_card, Fintype.card_fun,
    card_pairs]

end PI.GGCardUniWork
end

theorem mirabolic_card_unipotent : Formalism.L2.SG.GGMirabolic.CardUni := PI.GGCardUniWork.cardUni
end
