module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipReal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPf
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

open Formalism.L2.SG.Full

def Gr {D : D7} (X : HidaSetting D) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    Matrix (Kap X) (Kap X) X.B.I.E :=
  Bm' X * M * Bm X

def RatApprox : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (M : GL (Fin X.B.I.n) X.B.I.E), M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J →
    ∀ k : ℕ, 1 ≤ k → ∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, ∀ P : InfinitePlace X.B.I.F → Matrix (Kap X) (Kap X) ℂ,
      (∀ v, InPat (lvk X) k (P v) ∧
        InPat (lvk X) 1 ((Gr X (↑M⁻¹ : Matrix _ _ _)).map (X.B.I.φ v) * P v * (Gr X (M : Matrix _ _ _)).map (X.B.I.φ v)) ∧
        (P v)ᴴ * JBv X v = -(JBv X v * P v)) →
      ∃ Y : Matrix (Kap X) (Kap X) X.B.I.E, InPat (lvk X) k Y ∧
        InPat (lvk X) 1 (Gr X (↑M⁻¹ : Matrix _ _ _) * Y * Gr X (M : Matrix _ _ _)) ∧ Yᴴ * JB X = -(JB X * Y) ∧
        (∃ A : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E), Y = (d : X.B.I.E) • A.map (fun a => (a : X.B.I.E))) ∧
        ∀ v i j, ‖(Y.map (X.B.I.φ v) - P v) i j‖ ≤ C

def RatMem : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (M : GL (Fin X.B.I.n) X.B.I.E),
    M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J → (∀ y, X.crd (t.lin y) = (M : Matrix _ _ _) *ᵥ X.crd y) →
    ∃ d : ℕ, 1 ≤ d ∧ ∀ Z : Matrix (Kap X) (Kap X) X.B.I.E, InPat (lvk X) 1 Z →
      InPat (lvk X) 1 (Gr X (↑M⁻¹ : Matrix _ _ _) * Z * Gr X (M : Matrix _ _ _)) → Zᴴ * JB X = -(JB X * Z) →
      (∃ A : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E), Z = (d : X.B.I.E) • A.map (fun a => (a : X.B.I.E))) →
      ∃ s ∈ ROinf t, ∀ v, Mv X v s = (cay (2 * D.R.rS + 2) Z).map (X.B.I.φ v)

end Formalism.L2.SG.TermOp.Vanish
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyInt
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepIntOf
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.WuDecay Formalism.L2.SG.WuDecayPf
open scoped InnerProductSpace ComplexConjugate ENNReal NNReal Classical
open Matrix

namespace Formalism.L2.SG.RealObj.StepIntOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} (X : HidaSetting D)

end Defs

def StIntOfLint : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf),
    ∫⁻ x, ‖X.Wu u x‖ₑ * ‖X.Wu u' (γ⁻¹ * x)‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤ →
      Formalism.L2.SG.TermOp.OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Set.univ (X.Wu u) (X.Wu u') γ

end Formalism.L2.SG.RealObj.StepIntOf

namespace Formalism.L2.SG.RealObj.StepIntOf.Steps

open Formalism.L2.SG.RealObj.StepIntOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem norm_rank_one_le {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (v : V) (w : V') :
    ‖Formalism.L2.SG.TermOp.rk1 v w‖ ≤ ‖v‖ * ‖w‖ := by
  unfold Formalism.L2.SG.TermOp.rk1
  rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]

theorem stIntOfLint : StIntOfLint := by
  intro D X u u' γ hfin
  unfold Formalism.L2.SG.TermOp.OOInt
  rw [integrableOn_univ]
  have hW : Continuous (X.Wu u) := (X.Wu_spec u).2.2.1
  have hW' : Continuous (X.Wu u') := (X.Wu_spec u').2.2.1
  have hW'' : Continuous fun x : X.B.I.Ginf => X.Wu u' (γ⁻¹ * x) := hW'.comp (continuous_const.mul continuous_id)
  have hc : Continuous fun x : X.B.I.Ginf => Formalism.L2.SG.TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x)) := by
    rw [continuous_clm_apply]
    intro ξ
    simp only [Formalism.L2.SG.TermOp.rankOneInnerOperator_apply]
    exact (hW''.inner continuous_const).smul hW
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin
  simp only []
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_rank_one_le _ _)

end Formalism.L2.SG.RealObj.StepIntOf.Steps

namespace Formalism.L2.SG.RealObj.StepIntOf.Theta

open Formalism.L2.SG.RealObj.StepIntOf

section

variable {D : D7} (X : HidaSetting D)

end

end Formalism.L2.SG.RealObj.StepIntOf.Theta

namespace Formalism.L2.SG.RealObj.StepIntOf

end Formalism.L2.SG.RealObj.StepIntOf
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.EnergyInt

def LocOrbG : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ → ∀ v : InfinitePlace X.B.I.F,
      ∫⁻ x, ‖X.Wloc u v x‖ₑ * ‖X.Wloc u' v ((γ v)⁻¹ * x)‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε v)) < ⊤

def StepIntG : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ →
      TermOp.OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Set.univ (X.Wu u) (X.Wu u') γ

theorem lint_prod {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) :
    ∫⁻ x, ‖X.Wu u x‖ₑ * ‖X.Wu u' (γ⁻¹ * x)‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      ∏ v, ∫⁻ x, ‖X.Wloc u v x‖ₑ * ‖X.Wloc u' v ((γ v)⁻¹ * x)‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε v)) := by
  have hm : ∀ v, Measurable (fun x : Formalism.REAL.UJ (X.B.I.ε v) =>
      ‖X.Wloc u v x‖ₑ * ‖X.Wloc u' v ((γ v)⁻¹ * x)‖ₑ) := by
    intro v
    exact ((X.Wloc_cont u v).enorm.measurable).mul
      (((X.Wloc_cont u' v).comp (continuous_const.mul continuous_id)).enorm.measurable)
  rw [← Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.lintegral_pi_prod (fun v => Formalism.REAL.muG (X.B.I.ε v)) _ hm]
  simp_rw [Formalism.L2.SG.Pf.WuDec.enorm_Wu, ← Finset.prod_mul_distrib]
  rfl

theorem stepIntG_of_loc (h : LocOrbG) : StepIntG := by
  intro D hG X u u' sc hsc c hc γ hγ
  apply Formalism.L2.SG.RealObj.StepIntOf.Steps.stIntOfLint D X u u' γ
  rw [lint_prod]
  exact ENNReal.prod_lt_top fun v _ => h D hG X u u' sc hsc c hc γ hγ v

end Formalism.L2.SG.RealObj.EnergyInt
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductFormulaHolds
noncomputable section

open MeasureTheory Topology NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem good_eq {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) :
    Good X u u' = Set.univ.pi fun _ => GoodLoc (r := D.R.rS) (Tw u) (Tw u') := by
  ext y
  first
  | (simp only [Good, GoodLoc, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq])
  | (simp only [Good, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq]; rfl)
  | (simp [Good, GoodLoc])
  | (show _ ↔ _; exact Iff.rfl)

theorem product_formula_holds : P5 := by
  intro hJac hDC hSM hU hNH hR D X u u' sc hsc
  have hep : ∀ v a b, hJ (X.B.I.ε v) (eV X v a) (pV X v b) = if a = b then 1 else 0 := fun v a b =>
    (hJ_X X v _ _).trans (by rw [X.ef]; split_ifs <;> simp)
  have hpp : ∀ v a b, hJ (X.B.I.ε v) (pV X v a) (pV X v b) = 0 := fun v a b =>
    (hJ_X X v _ _).trans (by rw [X.ff]; simp)
  have hzp : ∀ w v b, hJ (X.B.I.ε v) (zV X w v) (pV X v b) = 0 := fun w v b => by
    have h0 : hJ (X.B.I.ε v) (pV X v b) (zV X w v) = 0 :=
      (hJ_X X v _ _).trans (by rw [(X.zu_orth w b).2]; simp)
    rw [hJ_cj, h0, map_zero]
  have hSH : ∀ w v, IsHaarS (SLoc (X.B.I.ε v) (eV X v) (zV X w v)) (muSv X w v) := fun w v =>
    hNH _ _ _ _ _ _ _ _ _ _ (frameLoc_X X w u v) (hep v) (hpp v) (hzp w v) _ _ (muNv_haar X w v) (muHv_haar X w v)
  haveI : ∀ w v, SigmaFinite (muSv X w v) := fun w v => (hSH w v).1.1
  obtain ⟨κ, hκ0, hκT, hκ⟩ := muS_eq X u (fun v => inferInstance)
  obtain ⟨κ', hκ'0, hκ'T, hκ'⟩ := muS_eq X u' (fun v => inferInstance)
  have hsec := fun v => hSM _ _ _ _ _ _ _ _ _ sc (frameLoc_X X u u' v) hsc
  choose hs hsm hss using hsec
  have hjl := fun v => hJac _ _ _ _ _ _ _ _ _ sc (frameLoc_X X u u' v) hsc _ _ (hSH u v) (hSH u' v) (hs v) (hss v)
  choose Cv hCv hDis using hjl
  have hloc : ∀ v, Formalism.REAL.muG (X.B.I.ε v) =
      ((nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (Cv v)).prod ((muSv X u v).prod (muSv X u' v))).map
        (phiLoc (X.B.I.ε v) (hs v)) := fun v =>
    muG_eq_map _ _ _ _ _ _ _ (hsm v) _ (hDis v)
  set Cp : ℝ := ∏ v, Cv v with hCp
  have hCp0 : 0 < Cp := Finset.prod_pos fun v _ => hCv v
  have hκr : 0 < κ.toReal := ENNReal.toReal_pos hκ0 hκT
  have hκr' : 0 < κ'.toReal := ENNReal.toReal_pos hκ'0 hκ'T
  refine ⟨Cp / (κ.toReal * κ'.toReal), div_pos hCp0 (mul_pos hκr hκr'), fun φ hφ => ?_⟩
  have hpf := prod_formula (fun v => Formalism.REAL.muG (X.B.I.ε v)) (fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (Cv v))
    (muSv X u) (muSv X u') hs hsm hloc φ hφ
  change ∫⁻ x, φ x ∂(Measure.pi fun v => Formalism.REAL.muG (X.B.I.ε v)) = _
  rw [hpf]

  have hwm : ∀ v, Measurable fun c : Fin (D.R.rS + 1) → ℂ => ENNReal.ofReal (Cv v * wtLoc D.R.k (Tw u) (Tw u') c) :=
    fun v => ENNReal.measurable_ofReal.comp (measurable_const.mul (wtLoc_cont D.R.k (Tw u) (Tw u')).measurable)
  have hν : Measure.pi (fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (Cv v)) =
      ((dcInf X).restrict (Good X u u')).withDensity
        (fun c => ∏ v, ENNReal.ofReal (Cv v * wtLoc D.R.k (Tw u) (Tw u') (c v))) := by
    unfold nuLoc
    haveI : SigmaFinite (dcLoc (r := D.R.rS)) := by unfold dcLoc; infer_instance
    rw [PiM.pi_withDensity _ _ hwm (fun v x => ENNReal.ofReal_ne_top), ← Measure.restrict_pi_pi, good_eq]
    rfl
  set H : (Cinf X) → X.B.I.Ginf := fun c v => hs v (c v) with hHd
  have hHm : Measurable H := Measurable.of_eval fun v => (hsm v).comp (measurable_pi_apply v)
  set Fc : Cinf X → ℝ≥0∞ := fun c => ∫⁻ s, ∫⁻ s', φ (s * H c * s'⁻¹) ∂Measure.pi (muSv X u') ∂Measure.pi (muSv X u)
    with hFc
  have hFm : Measurable Fc := by
    have h1 : Measurable fun q : (Cinf X × X.B.I.Ginf) × X.B.I.Ginf => φ (q.1.2 * H q.1.1 * q.2⁻¹) :=
      hφ.comp (((measurable_snd.comp measurable_fst).mul (hHm.comp (measurable_fst.comp measurable_fst))).mul
        measurable_snd.inv)
    exact h1.lintegral_prod_right'.lintegral_prod_right'
  rw [show (∫⁻ c, ∫⁻ s, ∫⁻ s', φ (s * (fun v => hs v (c v)) * s'⁻¹) ∂Measure.pi (muSv X u') ∂Measure.pi (muSv X u)
      ∂Measure.pi fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (Cv v)) = ∫⁻ c, Fc c
      ∂Measure.pi fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (Cv v) from rfl,
    hν, lintegral_withDensity_eq_lintegral_mul _
      (f := fun c : Cinf X => ∏ v, ENNReal.ofReal (Cv v * wtLoc D.R.k (Tw u) (Tw u') (c v)))
      (Finset.measurable_prod _ fun v _ => (hwm v).comp (measurable_pi_apply v)) hFm]
  have hGm : MeasurableSet (Good X u u') := by
    rw [good_eq]; exact MeasurableSet.univ_pi fun v => measurableSet_goodLoc _ _
  refine setLIntegral_congr_fun hGm fun c hc => ?_
  simp only [Pi.mul_apply]
  have hcv : ∀ v, c v ∈ GoodLoc (r := D.R.rS) (Tw u) (Tw u') := fun v => by
    rw [good_eq, Set.mem_univ_pi] at hc; exact hc v

  have hW : ∏ v, ENNReal.ofReal (Cv v * wtLoc D.R.k (Tw u) (Tw u') (c v)) = ENNReal.ofReal (Cp * wt X u u' c) := by
    rw [← ENNReal.ofReal_prod_of_nonneg fun v _ => mul_nonneg (hCv v).le (wtLoc_nonneg _ _ _ (hcv v)),
      Finset.prod_mul_distrib]
    rfl

  have hex := hR D X u u' sc hsc c hc
  have hh : HasDiag X u u' sc c (hOf X u u' sc c) := by
    unfold hOf; rw [dite_eq_left hex]; exact hex.choose_spec
  have hdc := fun v => hDC _ _ _ _ _ _ _ _ _ sc (frameLoc_X X u u' v) (c v) (hcv v) (hs v (c v)) (hOf X u u' sc c v)
    (hss v (c v) (hcv v)) (hh v)
  choose t ht t' ht' htt using hdc
  have hofe : hOf X u u' sc c = t * H c * t'⁻¹ := funext fun v => htt v
  have hrt : (Measure.pi (muSv X u)).map (fun x => x * t) = Measure.pi (muSv X u) :=
    PiM.pi_map_mul_right _ t fun v => hU _ _ _ _ _ _ _ _ _ (frameLoc_X X u u' v) _ (hSH u v) (t v) (ht v)
  have hrt' : (Measure.pi (muSv X u')).map (fun x => x * t') = Measure.pi (muSv X u') :=
    PiM.pi_map_mul_right _ t' fun v => hU _ _ _ _ _ _ _ _ _ (frameLoc_X X u' u v) _ (hSH u' v) (t' v) (ht' v)
  have hsw : ∫⁻ s, ∫⁻ s', φ (s * hOf X u u' sc c * s'⁻¹) ∂Measure.pi (muSv X u') ∂Measure.pi (muSv X u) = Fc c := by
    rw [hofe]; exact dc_switch _ _ φ hφ (H c) t t' hrt hrt'

  have hinner : ∀ s, Measurable fun s' : X.B.I.Ginf => φ (s * hOf X u u' sc c * s'⁻¹) := fun s =>
    hφ.comp (measurable_const.mul measurable_inv)
  have hG2 : Measurable fun s : X.B.I.Ginf => ∫⁻ s', φ (s * hOf X u u' sc c * s'⁻¹) ∂Measure.pi (muSv X u') :=
    (hφ.comp ((measurable_fst.mul measurable_const).mul measurable_snd.inv)).lintegral_prod_right'
  have hmu : ∫⁻ s, ∫⁻ s', φ (s * hOf X u u' sc c * s'⁻¹) ∂muS X u' ∂muS X u = κ * κ' * Fc c := by
    rw [hκ, hκ', lintegral_smul_measure]
    simp only [lintegral_smul_measure, smul_eq_mul]
    rw [lintegral_const_mul' _ _ hκ'T, hsw]
    ring
  have hwc : 0 ≤ wt X u u' c := by
    unfold wt
    exact Finset.prod_nonneg fun v _ => wtLoc_nonneg D.R.k _ _ (hcv v)
  have hk : κ * κ' = ENNReal.ofReal (κ.toReal * κ'.toReal) := by
    rw [ENNReal.ofReal_mul hκr.le, ENNReal.ofReal_toReal hκT, ENNReal.ofReal_toReal hκ'T]
  rw [hmu, hW, hk, ← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg (div_pos hCp0 (mul_pos hκr hκr')).le hwc)]
  congr 2
  field_simp

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabNDenseSteps
noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB

section Defs

variable {D : D7} (X : HidaSetting D)

abbrev RA : Type := X.B.I.E ⊗[X.B.I.F] Af X.B.I.F

abbrev ic : X.B.I.E →+* RA X := Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)

instance inv2 : Invertible (2 : RA X) :=
  (Invertible.map (ic X) (2 : X.B.I.E)).copy 2 (map_ofNat (ic X) 2).symm

def Bf : Matrix (Fin X.B.I.n) (Kap X) (RA X) := (Bm X).map (ic X)
def Bf' : Matrix (Kap X) (Fin X.B.I.n) (RA X) := (Bm' X).map (ic X)
def JBf : Matrix (Kap X) (Kap X) (RA X) := (JB X).map (ic X)

def Mf (x : X.B.I.Gf) : Matrix (Kap X) (Kap X) (RA X) := Bf' X * X.B.I.fmat x * Bf X

def Cg {α β : Type*} (c : ℕ) (A : Matrix α β (RA X)) : Prop :=
  ∀ i j, ∃ t ∈ IntAf X.B.I.F X.B.I.E, A i j = (c : RA X) * t

end Defs

def NfPat : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (x : X.B.I.Gf), x ∈ X.NfinU u → InPat (lvk X) 1 (Mf X x - 1)

def NfOfPat : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (x : X.B.I.Gf), InPat (lvk X) 1 (Mf X x - 1) → x ∈ X.NfinU u

def CayInvR : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (x : X.B.I.Gf), InPat (lvk X) 1 (Mf X x - 1) →
    ∃ Z : Matrix (Kap X) (Kap X) (RA X), InPat (lvk X) 1 Z ∧
      Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) Z * JBf X = -(JBf X * Z) ∧ cay (2 * D.R.rS + 2) Z = Mf X x

def SkewApprox : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Z : Matrix (Kap X) (Kap X) (RA X)), InPat (lvk X) 1 Z →
    Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) Z * JBf X = -(JBf X * Z) → ∀ c : ℕ, 1 ≤ c →
      ∃ Y : Matrix (Kap X) (Kap X) X.B.I.E, InPat (lvk X) 1 Y ∧ Yᴴ * JB X = -(JB X * Y) ∧
        Cg X c (Y.map (ic X) - Z)

def CayCont : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Z : Matrix (Kap X) (Kap X) (RA X)) (c : ℕ), 1 ≤ c →
    ∃ c' : ℕ, 1 ≤ c' ∧ ∀ Z' : Matrix (Kap X) (Kap X) (RA X), Cg X c' (Z' - Z) →
      Cg X c (cay (2 * D.R.rS + 2) Z' - cay (2 * D.R.rS + 2) Z)

def KgOfClose : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (x : X.B.I.Gf) (g : ℕ), 1 ≤ g →
    ∃ c : ℕ, 1 ≤ c ∧ ∀ y : X.B.I.Gf, Cg X c (Mf X y - Mf X x) → x⁻¹ * y ∈ X.B.I.Kg g

end Formalism.L2.SG.Pf.SlabNDensePf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabNDenseRat
noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB

section CayInv

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [Invertible (2 : K)]

theorem half_add_half' (M : Matrix ι ι K) : (⅟2 : K) • M + (⅟2 : K) • M = M := by
  rw [← add_smul, invOf_two_add_invOf_two, one_smul]

theorem cay_eq {N : ℕ} {Z : Matrix ι ι K} (hN : ((⅟2 : K) • Z) ^ N = 0) :
    cay N Z = (1 + (⅟2 : K) • Z) * geo N ((⅟2 : K) • Z) := by
  set Y : Matrix ι ι K := (⅟2 : K) • Z with hY
  set G := geo N Y with hG
  have hBG : (1 - Y) * G = 1 := by rw [hG, geo, mul_neg_geom_sum, hN, sub_zero]
  have e1 : G = 1 + Y * G := by
    have := hBG
    rw [Matrix.sub_mul, Matrix.one_mul] at this
    rw [← this]; abel
  have e2 : Z = Y + Y := by rw [hY, half_add_half']
  have e3 : cay N Z = 1 + Z * G := rfl
  rw [e3, Matrix.add_mul, Matrix.one_mul]
  calc 1 + Z * G = (1 + Y * G) + Y * G := by rw [e2, Matrix.add_mul]; abel
    _ = G + Y * G := by rw [← e1]

theorem cay_neg_mul {N : ℕ} {Z : Matrix ι ι K} (hN : ((⅟2 : K) • Z) ^ N = 0) : cay N (-Z) * cay N Z = 1 := by
  have hN' : ((⅟2 : K) • -Z) ^ N = 0 := by rw [smul_neg, neg_pow, hN, mul_zero]
  rw [cay_eq hN, cay_eq hN', smul_neg]
  set Y : Matrix ι ι K := (⅟2 : K) • Z with hY
  have h1 : geo N (-Y) * (1 + Y) = 1 := by
    have := geom_sum_mul_neg (-Y) N
    rw [sub_neg_eq_add] at this
    rw [geo, this, neg_pow, hN, mul_zero, sub_zero]
  have h2 : (1 - Y) * geo N Y = 1 := by rw [geo, mul_neg_geom_sum, hN, sub_zero]
  calc (1 + -Y) * geo N (-Y) * ((1 + Y) * geo N Y) = (1 - Y) * (geo N (-Y) * (1 + Y)) * geo N Y := by
        rw [← sub_eq_add_neg]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, h2]

end CayInv

def mkUJ {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : Formalism.REAL.inUJ ε g) : Formalism.REAL.UJ ε :=
  ⟨⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, mul_comm_one (by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, Formalism.REAL.Jm_mul_self]),
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, Formalism.REAL.Jm_mul_self]⟩, hg⟩

section RatEl

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

abbrev N0 (D : D7) : ℕ := 2 * D.R.rS + 2

theorem lvk_lt (k : Kap X) : lvk X k < N0 D := by show lvk X k < 2 * D.R.rS + 2; have := lvk_le X k; omega

theorem nil_of_pat {K : Type*} [CommRing K] {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) K}
    (hY : InPat (lvk X) k Y) (c : K) : (c • Y) ^ N0 D = 0 :=
  pow_eq_zero_of_inPat hk (lvk_lt X) (inPat_smul c hY)

def gE (Y : Matrix (Kap X) (Kap X) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
  Bm X * cay (N0 D) Y * Bm' X

theorem gE_mul {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y) :
    gE X (-Y) * gE X Y = 1 := by
  unfold gE
  have e : Bm X * cay (N0 D) (-Y) * Bm' X * (Bm X * cay (N0 D) Y * Bm' X) =
      Bm X * (cay (N0 D) (-Y) * ((Bm' X * Bm X) * cay (N0 D) Y)) * Bm' X := by simp only [Matrix.mul_assoc]
  rw [e, Bm'_mul_Bm, Matrix.one_mul, cay_neg_mul (nil_of_pat X hk hY _), Matrix.mul_one, Bm_mul_Bm']

theorem gE_mul' {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y) :
    gE X Y * gE X (-Y) = 1 := by
  have := gE_mul X hk (inPat_neg hY)
  rwa [neg_neg] at this

theorem cT_eq {m p : Type} (M : Matrix m p X.B.I.E) : Formalism.UG.cT (starRingEnd X.B.I.E) M = Mᴴ := by
  ext i j
  simp only [Formalism.UG.cT, conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
  rfl

theorem gE_unitary {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : (gE X Y)ᴴ * X.B.I.J * gE X Y = X.B.I.J := by
  have hc := cay_unitary hYs (nil_of_pat X hk hY (⅟2 : X.B.I.E))
  have hh : (Bm' X)ᴴ * (Bm X)ᴴ = 1 := by rw [← conjTranspose_mul, Bm_mul_Bm', conjTranspose_one]
  have hJB := JB_eq X
  unfold gE
  calc (Bm X * cay (N0 D) Y * Bm' X)ᴴ * X.B.I.J * (Bm X * cay (N0 D) Y * Bm' X)
      = (Bm' X)ᴴ * ((cay (N0 D) Y)ᴴ * ((Bm X)ᴴ * X.B.I.J * Bm X) * cay (N0 D) Y) * Bm' X := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (Bm' X)ᴴ * (Bm X)ᴴ * X.B.I.J * (Bm X * Bm' X) := by
        rw [← hJB, hc, hJB]; simp only [Matrix.mul_assoc]
    _ = X.B.I.J := by rw [hh, Bm_mul_Bm', Matrix.one_mul, Matrix.mul_one]

def gGL {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y) :
    GL (Fin X.B.I.n) X.B.I.E :=
  ⟨gE X Y, gE X (-Y), gE_mul' X hk hY, gE_mul X hk hY⟩

theorem gGL_mem {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : gGL X hk hY ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J := by
  show Formalism.UG.cT (starRingEnd X.B.I.E) (gE X Y) * X.B.I.J * gE X Y = X.B.I.J
  rw [cT_eq]
  exact gE_unitary X hk hY hYs

theorem sig_eq : (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E) = starRingEnd X.B.I.E := RingHom.ext fun _ => rfl

theorem gE_real (v : InfinitePlace X.B.I.F) (Y : Matrix (Kap X) (Kap X) X.B.I.E) :
    (X.B.I.P v)⁻¹ * (gE X Y).map (X.B.I.φ v) * X.B.I.P v =
      Bv X v * cay (N0 D) (Y.map (X.B.I.φ v)) * Bv' X v := by
  unfold gE Bv Bv'
  rw [Matrix.map_mul, Matrix.map_mul, cay_map]
  simp only [Matrix.mul_assoc]

theorem skew_map (v : InfinitePlace X.B.I.F) {Y : Matrix (Kap X) (Kap X) X.B.I.E}
    (hYs : Yᴴ * JB X = -(JB X * Y)) :
    (Y.map (X.B.I.φ v))ᴴ * JBv X v = -(JBv X v * Y.map (X.B.I.φ v)) := by
  rw [JBv, map_conjTranspose, ← Matrix.map_mul, hYs, ← Matrix.map_mul, Matrix.map_neg]
  exact fun a => map_neg _ a

theorem inUJ_real {k : ℕ} (hk : 1 ≤ k) (v : InfinitePlace X.B.I.F) {Y : Matrix (Kap X) (Kap X) X.B.I.E}
    (hY : InPat (lvk X) k Y) (hYs : Yᴴ * JB X = -(JB X * Y)) :
    Formalism.REAL.inUJ (X.B.I.ε v) ((X.B.I.P v)⁻¹ * (gE X Y).map (X.B.I.φ v) * X.B.I.P v) := by
  rw [gE_real]
  unfold Formalism.REAL.inUJ
  have hc := cay_unitary (skew_map X v hYs) (nil_of_pat X hk (inPat_map (X.B.I.φ v) hY) (⅟2 : ℂ))
  have hh : (Bv' X v)ᴴ * (Bv X v)ᴴ = 1 := by rw [← conjTranspose_mul, Bv_mul_Bv', conjTranspose_one]
  calc (Bv X v * cay (N0 D) (Y.map (X.B.I.φ v)) * Bv' X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) *
        (Bv X v * cay (N0 D) (Y.map (X.B.I.φ v)) * Bv' X v)
      = (Bv' X v)ᴴ * ((cay (N0 D) (Y.map (X.B.I.φ v)))ᴴ * ((Bv X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Bv X v) *
        cay (N0 D) (Y.map (X.B.I.φ v))) * Bv' X v := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (Bv' X v)ᴴ * ((Bv X v)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Bv X v) * Bv' X v := by rw [Bv_gram, hc]
    _ = ((Bv' X v)ᴴ * (Bv X v)ᴴ) * Formalism.REAL.Jm (X.B.I.ε v) * (Bv X v * Bv' X v) := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε v) := by rw [hh, Bv_mul_Bv', Matrix.one_mul, Matrix.mul_one]

def gA {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : X.B.I.GA :=
  (fun v => mkUJ (X.B.I.ε v) _ (inUJ_real X hk v hY hYs),
    Formalism.L2.SG.ColsDim.ratHom X.B.I.cm.sig X.B.I.J (Af X.B.I.F)
      ⟨gGL X hk hY, by rw [sig_eq]; exact gGL_mem X hk hY hYs⟩)

theorem gA_GF {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : gA X hk hY hYs ∈ X.B.I.GFset :=
  ⟨gGL X hk hY, gGL_mem X hk hY hYs, fun v => rfl, rfl⟩

theorem Mv_gA {k : ℕ} (hk : 1 ≤ k) (v : InfinitePlace X.B.I.F) {Y : Matrix (Kap X) (Kap X) X.B.I.E}
    (hY : InPat (lvk X) k Y) (hYs : Yᴴ * JB X = -(JB X * Y)) :
    Mv X v (gA X hk hY hYs).1 = cay (N0 D) (Y.map (X.B.I.φ v)) := by
  unfold Mv
  show Bv' X v * ((X.B.I.P v)⁻¹ * (gE X Y).map (X.B.I.φ v) * X.B.I.P v) * Bv X v = _
  rw [gE_real]
  simp only [← Matrix.mul_assoc, Bv'_mul_Bv, Matrix.one_mul]
  rw [Matrix.mul_assoc, Bv'_mul_Bv, Matrix.mul_one]

theorem gA_ninf {k : ℕ} (hk : 1 ≤ k) {Y : Matrix (Kap X) (Kap X) X.B.I.E} (hY : InPat (lvk X) k Y)
    (hYs : Yᴴ * JB X = -(JB X * Y)) : (gA X hk hY hYs).1 ∈ X.NinfU u := by
  intro v
  apply inN_of_pat X u v
  have := Mv_gA X hk v hY hYs
  unfold Mv at this
  rw [this]
  exact inPat_mono hk (cay_sub_one _ (inPat_map (X.B.I.φ v) hY))

end RatEl
end Formalism.L2.SG.Pf.SlabNDensePf
end
end
