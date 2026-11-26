module

public import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdCons
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.OmegaDensityUnique
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeGap.HCFdegRGap
noncomputable section

namespace PI.UnitaryGroupMassFormula.HCFdegRGap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

def HCFdegRGap : Prop :=
  ∀ (cd : CDHaar) (s : (n : ℕ) → (Fin n → Bool) → NNReal), Formalism.MainNotions.RT.cdScaleTieR cd s →
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (h : ℝ),
    1 ≤ (Finset.univ.filter (fun a => ε a = true)).card →
    1 ≤ (Finset.univ.filter (fun a => ε a = false)).card →
    Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.GapAtLeast ε lam h →
    32 * (N : ℝ) * ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) *
      ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) + 2 < h →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H), IsDS ε lam σ → w ≠ 0 →
      fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w = Formalism.QuantumDeterminants.fdegHC lam

end PI.UnitaryGroupMassFormula.HCFdegRGap
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeGap.HCFdegRGapHolds
noncomputable section

open MeasureTheory

namespace PI.UnitaryGroupMassFormula.HCFdegRGap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

def signEquiv {N : ℕ} (ε : Fin N → Bool) :
    Fin (Fintype.card {a // ε a = true}) ⊕ Fin (Fintype.card {a // ¬ ε a = true}) ≃ Fin N :=
  (Equiv.sumCongr (Fintype.equivFin _).symm (Fintype.equivFin _).symm).trans
    (Equiv.sumCompl (fun a => ε a = true))

theorem signEquiv_inl {N : ℕ} (ε : Fin N → Bool) (i) : ε (signEquiv ε (Sum.inl i)) = true := by
  have h := ((Fintype.equivFin {a // ε a = true}).symm i).2
  simpa [signEquiv] using h

theorem signEquiv_inr {N : ℕ} (ε : Fin N → Bool) (j) : ε (signEquiv ε (Sum.inr j)) = false := by
  have h := ((Fintype.equivFin {a // ¬ ε a = true}).symm j).2
  simpa [signEquiv] using h

theorem muCD_eq_smul (cd : CDHaar) (s : (n : ℕ) → (Fin n → Bool) → NNReal)
    (hc : Formalism.MainNotions.RT.cdScaleTieR cd s) {N : ℕ} (ε : Fin N → Bool) :
    ReciprocityTheory.ChartRestriction.DS.muCD ε = (s N ε : ENNReal) • Formalism.REAL.muG ε := by
  ext A hA
  rw [ReciprocityTheory.ChartRestriction.DS.muCD_eq_cd_vol cd (signEquiv ε) (signEquiv_inl ε) (signEquiv_inr ε) A hA,
    hc N ε _ _ (signEquiv ε) (signEquiv_inl ε) (signEquiv_inr ε) A hA]

theorem card_add_card {N : ℕ} (ε : Fin N → Bool) :
    (Finset.univ.filter (fun a => ε a = true)).card + (Finset.univ.filter (fun a => ε a = false)).card = N := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have h1 : ∀ a : Fin N, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a
    cases ε a <;> simp
  simp only [h1]
  simp

theorem thrStar_lt {N : ℕ} (ε : Fin N → Bool) (hp : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε)
    (hq : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε) {h : ℝ}
    (hh : 32 * (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) + 2 < h) :
    ReciprocityTheory.ChartRestriction.DS.thrStar ε + 1 < h := by
  have hpN : ReciprocityTheory.ChartRestriction.DS.pOf ε ≤ N := by
    unfold ReciprocityTheory.ChartRestriction.DS.pOf
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hpR : (1 : ℝ) ≤ (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) := by exact_mod_cast hp
  have hqR : (1 : ℝ) ≤ (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) := by exact_mod_cast hq
  have hN : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := le_trans hpR hN
  have hm : ((ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℕ) : ℝ) ≤ (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) := by
    have : ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε * ReciprocityTheory.ChartRestriction.DS.qOf ε := by
      unfold ReciprocityTheory.ChartRestriction.DS.S7.q0
      exact le_trans (min_le_left _ _) (Nat.le_mul_of_pos_right _ (by omega))
    exact_mod_cast this
  have hm1 : (1 : ℝ) ≤ ((ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℕ) : ℝ) := by
    have : 1 ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := by
      unfold ReciprocityTheory.ChartRestriction.DS.S7.q0
      exact le_min hp hq
    exact_mod_cast this
  have h2m : (0 : ℝ) ≤ 2 * ((ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℕ) : ℝ) := by positivity
  have hsq : Real.sqrt (2 * ((ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℕ) : ℝ)) ≤ 2 * ((ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℕ) : ℝ) := by
    nlinarith [Real.sq_sqrt h2m, Real.sqrt_nonneg (2 * ((ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℕ) : ℝ)),
      sq_nonneg (Real.sqrt (2 * ((ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℕ) : ℝ)) - 1)]
  have hA : (N : ℝ) * ((ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℕ) : ℝ) ≤
      (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hm (by positivity)
  have hB : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤
      (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) := by
    rw [mul_assoc]
    exact le_mul_of_one_le_left (by positivity) hN1
  have hC : (0 : ℝ) ≤ (N : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) := by positivity
  unfold ReciprocityTheory.ChartRestriction.DS.thrStar
  rw [← lt_sub_iff_add_lt, max_lt_iff]
  constructor <;> linarith

theorem fdeg_cd_gap {n : ℕ} {ε : Fin n → Bool} (hp : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf ε)
    (hq : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf ε) {lam : Fin n → ℝ} (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ}
    (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hh : ReciprocityTheory.ChartRestriction.DS.thrStar ε + 1 < h)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) {v : H} (hv : v ≠ 0) :
    fdegOf (ReciprocityTheory.ChartRestriction.DS.muCD ε) σ v = ReciprocityTheory.ChartRestriction.DS.dimVlam lam := by
  have : CompleteSpace H := hσ.1
  have hq0 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := le_min hp hq
  have h8 : 8 * (n : ℝ) * ReciprocityTheory.ChartRestriction.DS.S7.q0 ε < h := by
    have h1 := le_max_right
      ((n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) + 1)
      (16 * (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)))
    have h2 : 0 ≤ 8 * Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) := by positivity
    have h3 : 0 ≤ (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) := by positivity
    unfold ReciprocityTheory.ChartRestriction.DS.thrStar at hh
    linarith
  have hΨ : ∀ μ : Fin n → ℝ, ReciprocityTheory.ChartRestriction.DS.S7.IsHCParam μ → ReciprocityTheory.ChartRestriction.DS.GapAtLeast ε μ h →
      ∃ (T : ReciprocityTheory.ChartRestriction.DS.S7.KType ε (ReciprocityTheory.ChartRestriction.DS.lowK ε μ))
        (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), ReciprocityTheory.ChartRestriction.DS.IsPsiFor ε μ T Ψ := by
    intro μ hμ hgμ
    obtain ⟨T⟩ := ReciprocityTheory.ChartRestriction.DS.HW.kType_exists ε μ hμ
    obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.DS.Lap.LemK.exists_isMu hμ
    exact ⟨T, _, (ReciprocityTheory.ChartRestriction.DS.Lap.Base.psiFor _ _ μ h T m hμ hm hgμ hq0 h8).1⟩
  exact ReciprocityTheory.ChartRestriction.DS.fdCons_cd hp hq hlam hgap hh hΨ hσ hv

theorem hCFdegRGap_holds : HCFdegRGap := by
  intro cd s hc N ε lam h hp hq hlam hgap hh H _ _ σ w hσ hw
  rw [← muCD_eq_smul cd s hc ε]
  exact fdeg_cd_gap hp hq hlam hgap (thrStar_lt ε hp hq hh) hσ hw

end PI.UnitaryGroupMassFormula.HCFdegRGap
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeGap.DimensionBoundOfGapUniform
noncomputable section

namespace PI.UnitaryGroupMassFormula.HCFdegRGap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S MeasureTheory Matrix

theorem gap_big {p q N ep0 h0 : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hN : N = p + q)
    (he1 : Real.exp (-N) ≤ ep0) (he2 : ep0 < 1 / 2)
    (hh : 8192 * min p q * (p * q) ^ 3 * Real.log N / ep0 ^ 2 ≤ h0) :
    32 * N * p * q + 2 < h0 := by
  have hN2 : (2 : ℝ) ≤ N := by linarith
  have hlog2 := Real.log_two_gt_d9
  have hlog : (0.69 : ℝ) < Real.log N :=
    lt_of_lt_of_le (by norm_num at hlog2 ⊢; linarith) (Real.log_le_log (by norm_num) hN2)
  have hep : 0 < ep0 := lt_of_lt_of_le (Real.exp_pos _) he1
  have hmin : 1 ≤ min p q := le_min hp hq
  have hpq : 1 ≤ p * q := by nlinarith
  have hpq3 : (p * q) ^ 2 ≤ (p * q) ^ 3 := by nlinarith
  have hsum : p + q ≤ 2 * (p * q) := by nlinarith
  set X := 8192 * min p q * (p * q) ^ 3 * Real.log N with hXdef
  have hX : 8192 * 0.69 * (p * q) ^ 3 ≤ X := by
    have h3 : 0 ≤ (p * q) ^ 3 := by positivity
    have h4 : (1 : ℝ) * 0.69 ≤ min p q * Real.log N := mul_le_mul hmin hlog.le (by norm_num) (by linarith)
    rw [hXdef]
    nlinarith
  have hdiv : 4 * X ≤ X / ep0 ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have h5 : ep0 ^ 2 ≤ 1 / 4 := by nlinarith
    have hXpos : 0 ≤ X := le_trans (by positivity) hX
    nlinarith
  rw [hN]
  nlinarith

end PI.UnitaryGroupMassFormula.HCFdegRGap
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeGap.DimensionFamilyOfWeylMultiplicity
noncomputable section

open MeasureTheory

namespace PI.UnitaryGroupMassFormula.HCFdegRGap

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.StandardLattice

theorem dsigEx_at (D : D7) (hd : dsigTie D) (ρ : D.what₂.Tau)
    (hex : ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
      IsDS (epsSH D.R) (lamSH D.R (D.hc ρ)) σ) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
      IsDS (epsSH D.R) (lamSH D.R (D.hc ρ)) σ ∧
      IsFdeg ((D.s.cdScale _ (epsSH D.R) : ENNReal) • Formalism.REAL.muG (epsSH D.R)) σ (D.dsig ρ) := by
  obtain ⟨H, i1, i2, σ, hσ⟩ := hex
  haveI : CompleteSpace H := hσ.1
  obtain ⟨d, hd0, hdI⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS _ σ hσ
  have hc : (0 : ℝ) < (D.s.cdScale _ (epsSH D.R) : ℝ) := D.s.cdScale_pos _ _
  have hF : IsFdeg ((D.s.cdScale _ (epsSH D.R) : ENNReal) • Formalism.REAL.muG (epsSH D.R)) σ
      (d / (D.s.cdScale _ (epsSH D.R) : ℝ)) := by
    refine ⟨div_pos hd0 hc, fun v w v' w' => ⟨(hdI v w v' w').1.smul_measure ENNReal.coe_ne_top, ?_⟩⟩
    rw [MeasureTheory.integral_smul_measure, (hdI v w v' w').2, ENNReal.coe_toReal]
    have hc' : ((D.s.cdScale _ (epsSH D.R) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hd' : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    rw [Complex.real_smul]
    push_cast
    field_simp
  have key := hd ρ H σ _ hσ hF
  refine ⟨H, i1, i2, σ, hσ, ?_⟩
  rw [← key]
  exact hF

end PI.UnitaryGroupMassFormula.HCFdegRGap
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesExistence.LowKMultOneG
namespace Formalism.MainNotions.BesselDiscreteSeries

theorem lowest_K_type_mult_one_of_gaps : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOneG := by
  intro N ε lam H _ _ σ hp hσ h hg hthr
  have : CompleteSpace H := hσ.1
  exact (ReciprocityTheory.ChartRestriction.DS.isDS_props_of_gap N ε lam hp h hg hthr H σ hσ).2.1

end Formalism.MainNotions.BesselDiscreteSeries
end

noncomputable section

open MeasureTheory

namespace Formalism.MainNotions.GappedMultiplicityBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.StandardLattice PI.UnitaryGroupMassFormula.HCFdegRGap

theorem thrDS_lt {N : ℕ} (ε : Fin N → Bool) {h : ℝ}
    (hh : 32 * (N : ℝ) * ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) *
      ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) + 2 < h) :
    Formalism.MainNotions.GapDS.thrDS ε < h := by
  have h0 : (0 : ℝ) ≤ (N : ℝ) * ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) *
      ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) := by positivity
  show (N : ℝ) * ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) *
      ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) + 1 < h
  linarith

theorem finrank_lowK_eqG (hW : DiscreteSeriesWeylDimension.WeylForK) (hL : DiscreteSeriesWeylDimension.LowKMultOneG) {N : ℕ} (ε : Fin N → Bool)
    (lam : Fin N → ℝ) (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (hDS : IsDS ε lam σ) (h : ℝ)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hthr : Formalism.MainNotions.GapDS.thrDS ε < h) :
    ((Module.finrank ℂ (lowKSub ε lam σ) : ℕ) : ℝ) = StandardLattice.dTau ε lam := by

  obtain ⟨S, hS⟩ := hDS.2.2.2.2.2.1
  have hset : {S' : Submodule ℂ H | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S'} = {S} := by
    ext S'
    constructor
    · intro hS'
      exact hL N ε lam H σ hlam hDS h hg hthr S' S hS' hS
    · intro hS'
      rw [Set.mem_singleton_iff] at hS'
      rw [hS']
      exact hS
  have hsub : lowKSub ε lam σ = S := by
    show sSup {S' : Submodule ℂ H | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S'} = S
    rw [hset, sSup_singleton]

  have hKU : Formalism.REAL.Kset ε ⊆ UJset ε := by
    intro g hg
    have hg' : g ∈ Matrix.unitaryGroup (Fin N) ℂ ∧ g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * g := hg
    obtain ⟨hu, hc⟩ := hg'
    have h1 : star g * g = 1 := by
      first
        | exact unitary.star_mul_self_of_mem hu
        | exact Unitary.star_mul_self_of_mem hu
        | exact (Matrix.mem_unitaryGroup_iff').mp hu
    rw [Matrix.star_eq_conjTranspose] at h1
    show Matrix.conjTranspose g * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε
    rw [mul_assoc, ← hc, ← mul_assoc, h1, one_mul]
  have hU := hDS.2.2.1
  have hK : IsURepOn (Formalism.REAL.Kset ε) σ := by
    unfold IsURepOn Formalism.QuantumDeterminants.IsCRepOn
    exact ⟨⟨hU.1.1, fun a ha b hb => hU.1.2 a (hKU ha) b (hKU hb)⟩,
      fun g hg v => hU.2.1 g (hKU hg) v, fun v => (hU.2.2 v).mono hKU⟩
  have hpt : ∀ a, (Formalism.QuantumDeterminants.lowK ε lam + Formalism.REAL.rhoC ε) a = lam a + StandardLattice.rhoN ε a := by
    intro a
    simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, sub_add_cancel]
    rfl
  rw [hsub, hW N ε (Formalism.QuantumDeterminants.lowK ε lam) H σ S hK hS]
  simp only [hpt]
  rfl

theorem theorem_three_of_gap_bound (s : (n : ℕ) → (Fin n → Bool) → NNReal)
    (hf : ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (h : ℝ),
      1 ≤ (Finset.univ.filter (fun a => ε a = true)).card →
      1 ≤ (Finset.univ.filter (fun a => ε a = false)).card →
      Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      32 * (N : ℝ) * ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) *
        ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) + 2 < h →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H), IsDS ε lam σ → w ≠ 0 →
        fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w = Formalism.QuantumDeterminants.fdegHC lam)
    (hW : DiscreteSeriesWeylDimension.WeylForK) (hL : DiscreteSeriesWeylDimension.LowKMultOneG) : Formalism.MainNotions.RT.DiscreteSeriesDegreeBoundsAtScale s := by
  intro N ε lam ep0 h0 H _ _ σ w p q hp hq hlam hgap he1 he2 hh0 hDS hw
  have hNpq : (N : ℝ) = p + q := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun a => ε a = true)
    have h' : (Finset.univ.filter (fun a => ε a = true)).card +
        (Finset.univ.filter (fun a => ε a = false)).card = N := by simpa using this
    show (N : ℝ) = ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) +
      ((Finset.univ.filter (fun a => ε a = false)).card : ℝ)
    have h'' := congrArg (fun x : ℕ => (x : ℝ)) h'
    push_cast at h''
    linarith
  have hbig : 32 * (N : ℝ) * p * q + 2 < h0 := gap_big hp hq hNpq he1 he2 hh0
  have hp' : 1 ≤ (Finset.univ.filter (fun a => ε a = true)).card := by
    have h : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => ε a = true)).card : ℝ) := hp
    exact_mod_cast h
  have hq' : 1 ≤ (Finset.univ.filter (fun a => ε a = false)).card := by
    have h : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => ε a = false)).card : ℝ) := hq
    exact_mod_cast h
  have hfw := hf N ε lam h0 hp' hq' hlam hgap hbig H σ w hDS hw
  have hτ := finrank_lowK_eqG hW hL ε lam hlam σ hDS h0 hgap (thrDS_lt ε hbig)
  have hep : 0 < ep0 := lt_of_lt_of_le (Real.exp_pos _) he1
  have hnn := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.fdegHC_nonneg lam hlam
  rw [hfw, hτ]
  refine ⟨by nlinarith, ?_⟩
  have hle := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.fdegHC_le_dTau ε lam hlam
  have hτ0 : 0 < StandardLattice.dTau ε lam := StandardLattice.formalDegreeFactor_pos_of_strictAnti ε lam hlam.1
  have hexp : p * q = ((StandardLattice.nPlus ε * StandardLattice.nMinus ε : ℕ) : ℝ) := by push_cast; rfl
  rw [hexp, Real.rpow_natCast]
  have hp1 : 1 ≤ StandardLattice.nPlus ε := by
    have h : (1 : ℝ) ≤ ((StandardLattice.nPlus ε : ℕ) : ℝ) := hp
    exact_mod_cast h
  have hq1 : 1 ≤ StandardLattice.nMinus ε := by
    have h : (1 : ℝ) ≤ ((StandardLattice.nMinus ε : ℕ) : ℝ) := hq
    exact_mod_cast h
  have hN := StandardLattice.count_plus_add_count_minus N ε
  have hL1 := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.lamAbs_ge_one lam hlam (by omega)
  have hpq : (1 : ℝ) ≤ 3 * p * q := by nlinarith
  have hX : StandardLattice.lamAbs lam ≤ 3 * p * q * StandardLattice.lamAbs lam := by nlinarith
  have hpow : StandardLattice.lamAbs lam ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) ≤
      (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) :=
    pow_le_pow_left₀ (by linarith) hX _
  have hpos : 0 ≤ (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) :=
    pow_nonneg (by nlinarith) _
  calc Formalism.QuantumDeterminants.fdegHC lam ≤ StandardLattice.dTau ε lam * StandardLattice.lamAbs lam ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) := hle
    _ ≤ StandardLattice.dTau ε lam * (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) :=
        mul_le_mul_of_nonneg_left hpow hτ0.le
    _ ≤ 4 * StandardLattice.dTau ε lam * (3 * p * q * StandardLattice.lamAbs lam) ^ (StandardLattice.nPlus ε * StandardLattice.nMinus ε) := by nlinarith

theorem theorem_three_of_weyl_gapped_multiplicity (hW : DiscreteSeriesWeylDimension.WeylForK) (hL : DiscreteSeriesWeylDimension.LowKMultOneG) : Formalism.MainNotions.RT.DiscreteSeriesDegreeBoundsAllScales :=
  fun cd s hc => theorem_three_of_gap_bound s (PI.UnitaryGroupMassFormula.HCFdegRGap.hCFdegRGap_holds cd s hc) hW hL

theorem theorem_three_rows_of_real_place (D : D7) (hc : cdScaleTie D) (hdt : dsigTie D) (hW : DiscreteSeriesWeylDimension.WeylForK)
    (hL : DiscreteSeriesWeylDimension.LowKMultOneG) : StandardLattice.SigmaDegreeTwoSidedBoundOfGap D := by
  have hAll : StandardLattice.DiscreteSeriesDegreeBoundsOfGap D := Formalism.MainNotions.RT.theorem_three_under_scale_of_general (theorem_three_of_weyl_gapped_multiplicity hW hL) D hc
  intro ep0 he1 he2 ρ hgap
  have hHC := line_param_harish_chandra D ρ
  have hp : ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) = (pY D : ℝ) := by
    have : (Finset.univ.filter (fun a => epsSH D.R a = true)).card = nPlus (epsSH D.R) := rfl
    rw [this, sign_vector_eq_line_sign, count_plus_finCast, count_plus_line_sign]
  have hq : ((Finset.univ.filter (fun a => epsSH D.R a = false)).card : ℝ) = (qY D : ℝ) := by
    have : (Finset.univ.filter (fun a => epsSH D.R a = false)).card = nMinus (epsSH D.R) := rfl
    rw [this, sign_vector_eq_line_sign, count_minus_finCast, count_minus_line_sign]
  have hN : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [dimS_eq]
  have hg' : Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamSH D.R (D.hc ρ)) (spectralGapLowerBound D ep0) := by
    rw [sign_vector_eq_line_sign, param_vector_eq_line_param]; exact gapAtLeast_finCast _ _ _ _ hgap
  have hp1 : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) := by
    rw [hp]; exact_mod_cast (signature_counts_ge_one D).1
  have hq1 : (1 : ℝ) ≤ ((Finset.univ.filter (fun a => epsSH D.R a = false)).card : ℝ) := by
    rw [hq]; exact_mod_cast (signature_counts_ge_one D).2
  have hsum : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) =
      ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) +
        ((Finset.univ.filter (fun a => epsSH D.R a = false)).card : ℝ) := by
    have h' := congrArg (fun x : ℕ => (x : ℝ)) (card_add_card (epsSH D.R))
    push_cast at h' ⊢
    linarith
  have hbig := gap_big (h0 := spectralGapLowerBound D ep0) hp1 hq1 hsum (by rw [hN]; exact he1) he2
    (le_of_eq (by rw [hp, hq, hN]; unfold spectralGapLowerBound; rw [Nat.cast_min]))
  have hq0 : ((ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) : ℕ) : ℝ) ≤
      ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) := by
    have : ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) ≤ (Finset.univ.filter (fun a => epsSH D.R a = true)).card :=
      min_le_left _ _
    exact_mod_cast this
  have hmax : max (2 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ))
      (8 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) : ℝ)) < spectralGapLowerBound D ep0 := by
    generalize ((Finset.univ.filter (fun a => epsSH D.R a = true)).card : ℝ) = p at *
    generalize ((Finset.univ.filter (fun a => epsSH D.R a = false)).card : ℝ) = q at *
    generalize ((ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) : ℕ) : ℝ) = r at *
    generalize ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = n at *
    have hpq : 1 ≤ p * q := by nlinarith
    have hn : 1 ≤ n := by linarith
    have hrpq : r ≤ p * q := by nlinarith
    rw [max_lt_iff]
    constructor
    · nlinarith
    · nlinarith
  have hEx := dsigEx_at D hdt ρ
    (ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_exists_large_gap _ (epsSH D.R) _ hHC (spectralGapLowerBound D ep0) hg' (Or.inr hmax))
  obtain ⟨H, i1, i2, σ, hDS, hF⟩ := hEx
  have hcs : CompleteSpace H := hDS.1
  have hnt : Nontrivial H := hDS.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : H)
  have hdt' := finrank_lowK_eqG hW hL (epsSH D.R) (lamSH D.R (D.hc ρ)) hHC σ hDS (spectralGapLowerBound D ep0) hg'
    (thrDS_lt (epsSH D.R) hbig)
  have key := hAll _ (epsSH D.R) (lamSH D.R (D.hc ρ)) ep0 (spectralGapLowerBound D ep0) H σ w
    (by rw [hp]; exact_mod_cast (signature_counts_ge_one D).1) (by rw [hq]; exact_mod_cast (signature_counts_ge_one D).2) hHC hg'
    (by rw [hN]; exact he1) he2
    (by rw [hp, hq, hN]; unfold spectralGapLowerBound; rw [Nat.cast_min]) hDS hw
  rw [formal_degree_of_eq _ σ _ hF w hw, hp, hq, hdt'] at key
  rw [← dimV_eq_fdegHC _ hHC.1] at key
  rw [sign_vector_eq_line_sign, param_vector_eq_line_param, dim_weyl_finCast, formal_degree_finCast, abs_param_sup_finCast] at key
  refine ⟨key.1, ?_⟩
  have e : ((pY D : ℝ) * (qY D : ℝ)) = ((pY D * qY D : ℕ) : ℝ) := by push_cast; rfl
  rw [e, Real.rpow_natCast] at key
  exact key.2

theorem theorem_three_family_of_gapped_multiplicity {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (hL : DiscreteSeriesWeylDimension.LowKMultOneG) :
    Formalism.MainNotions.flipTwoThree.fam0 Fm Formalism.MainNotions.StandardLattice.SigmaDegreeTwoSidedBoundOfGap :=
  ⟨0, fun x _ _ i => theorem_three_rows_of_real_place (Fm.D x i) (Fm.ties x i).cdScale_tie (Fm.ties x i).dsig_tie
    weylForK_closed hL⟩

theorem explicit_bound_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Formalism.MainNotions.flipTwoThree.fam0 Fm Formalism.MainNotions.StandardLattice.SigmaDegreeTwoSidedBoundOfGap :=
  theorem_three_family_of_gapped_multiplicity Fm Formalism.MainNotions.BesselDiscreteSeries.lowest_K_type_mult_one_of_gaps

end Formalism.MainNotions.GappedMultiplicityBounds

end
