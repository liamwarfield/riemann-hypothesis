module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsStandardBasesLatticeAtPlaceOfAdaptedBases
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtLinAdaptedCoefEqStandardSeries
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardBasesHyperbolicPairOrthonormal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.JetTdegEqDegree
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeries

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedFamilyStandardBasesIntegrality
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitIdentityAllOfIntegralClassHostLog
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExpFactorAllOrbitsEqProdOrbits
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExpFactorAllOrbitsEqProdOrbits
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)

namespace GlobalTheory.ExpFacOrbits

theorem expFactor_allOrbits : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (R : Finset (OrbitPlaces.Pl D)) {M N N' : ℕ} (eA : Fin M ≃ R × Fin N)
    (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (hbe : constantCoeff be = 0), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (mvExp ((-1 : ℂ_[p]) • Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be)) =
      product_zeroth_first_parts.expS ℂ_[p] (OrbitPlaces.beAll D p (N0 := N) (N1 := N') R (fun _ => -1) (fun _ => be)) := by
  intro D p _ R M N N' eA be hbe
  classical
  set a : ZV (nP D p) M N' → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] := fun y =>
    X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) with ha_def
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero (fun y => constantCoeff_X _)
  have hlin : ∀ ab : Fin M × Fin N', (fun s : ZMod (nP D p) =>
      Formalism.DworkPowerSeriesWeights.linSub (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) (s, ab.1, ab.2)) =
      fun s => (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p]) := fun ab =>
    funext fun s => Formalism.DworkPowerSeriesWeights.OrbMul.linSub_idM (s, ab.1, ab.2)
  have hX : ∀ ab : Fin M × Fin N', HasSubst (fun s : ZMod (nP D p) =>
      (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p])) := fun ab =>
    hasSubst_of_constantCoeff_zero (fun s => constantCoeff_X _)
  have hB : Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be =
      ∑ ab : Fin M × Fin N', subst (fun s : ZMod (nP D p) =>
        (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p])) be := by
    unfold Formalism.DworkPowerSeriesWeights.bSum
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [hlin ab]
  have hcc : constantCoeff ((-1 : ℂ_[p]) •
      Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hB, Finset.smul_sum, map_sum]
    refine Finset.sum_eq_zero fun ab _ => ?_
    rw [MvPowerSeries.constantCoeff_smul, constantCoeff_subst_eq_zero (hX ab) (fun s => constantCoeff_X _) hbe,
      smul_zero]
  rw [Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' ha hcc]
  show mvExp _ = mvExp _
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hB, ← coe_substAlgHom ha, map_smul, map_sum, coe_substAlgHom ha]
  have hterm : ∀ ab : Fin M × Fin N', subst a (subst (fun s : ZMod (nP D p) =>
        (X (s, ab.1, ab.2) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p])) be) =
      subst (fun s : ZMod (nP D p) =>
        (X (OrbitPlaces.orbMap D p (eA ab.1).1 s, (eA ab.1).2, ab.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) be := by
    intro ab
    rw [subst_comp_subst_apply (hX ab) ha]
    congr 1
    funext s
    rw [subst_X ha]
  simp_rw [hterm]
  unfold OrbitPlaces.beAll
  simp only [← Finset.smul_sum]
  congr 1
  rw [Fintype.sum_prod_type]
  rw [Equiv.sum_comp eA (fun x : R × Fin N => ∑ b : Fin N', subst (fun s : ZMod (nP D p) =>
        (X (OrbitPlaces.orbMap D p x.1 s, x.2, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) be)]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_coe_sort R (fun r => ∑ a : Fin N, ∑ b : Fin N', subst (fun s : ZMod (nP D p) =>
        (X (OrbitPlaces.orbMap D p r s, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) be)

end GlobalTheory.ExpFacOrbits
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExpFactorAllOrbitsEqProdOrbitsStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expFactor_allOrbits_eq_prod_orbits : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (R : Finset (OrbitPlaces.Pl D)) {M N N' : ℕ} (eA : Fin M ≃ R × Fin N)
    (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (hbe : constantCoeff be = 0), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (mvExp ((-1 : ℂ_[p]) • Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be)) =
      product_zeroth_first_parts.expS ℂ_[p] (OrbitPlaces.beAll D p (N0 := N) (N1 := N') R (fun _ => -1) (fun _ => be)) := by
  first | exact @GlobalTheory.ExpFacOrbits.expFactor_allOrbits | exact GlobalTheory.ExpFacOrbits.expFactor_allOrbits | (intros; apply GlobalTheory.ExpFacOrbits.expFactor_allOrbits <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicPairAdditiveCoordsLinearForms
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicPairAdditiveCoordsLinearForms
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)
noncomputable section

namespace GlobalTheory.KerStd.HypOrbit

open Formalism.InvariantFactorPaths.G7 (lgF at1)

theorem lg_flin {p : ℕ} [Fact p.Prime] (hl : 2 ≤ p) {τ m : Type} [Fintype m] (c : m → ℂ_[p]) (v : m → MvPowerSeries τ ℂ_[p])
    (hv : ∀ k, constantCoeff (v k) = 0) :
    PowerSeries.subst (Formalism.L2.Th1.C.flin (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) c v) (lgF ℂ_[p] p) =
      ∑ k, C (c k) * PowerSeries.subst (v k) (lgF ℂ_[p] p) := by
  unfold Formalism.L2.Th1.C.flin
  have hA : constantCoeff (∑ k, C (c k) * PowerSeries.subst (v k) (lgF ℂ_[p] p)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, constantCoeff_C]
    exact Finset.sum_eq_zero fun k _ => by
      rw [PowerSeries.constantCoeff_subst_eq_zero (hv k) _ (Formalism.L2.Th1.D.Pair.cc_lgF hl), mul_zero]
  rw [← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (Formalism.L2.Th1.D.expSpec ℂ_[p] p hl).1)
    (PowerSeries.HasSubst.of_constantCoeff_zero hA), (Formalism.L2.Th1.D.expSpec ℂ_[p] p hl).2.1,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero hA)]

theorem cc_flin {p : ℕ} [Fact p.Prime] (hl : 2 ≤ p) {τ m : Type} [Fintype m] (c : m → ℂ_[p]) (v : m → MvPowerSeries τ ℂ_[p])
    (hv : ∀ k, constantCoeff (v k) = 0) :
    constantCoeff (Formalism.L2.Th1.C.flin (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) c v) = 0 := by
  unfold Formalism.L2.Th1.C.flin
  have hA : constantCoeff (∑ k, C (c k) * PowerSeries.subst (v k) (lgF ℂ_[p] p)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, constantCoeff_C]
    exact Finset.sum_eq_zero fun k _ => by
      rw [PowerSeries.constantCoeff_subst_eq_zero (hv k) _ (Formalism.L2.Th1.D.Pair.cc_lgF hl), mul_zero]
  exact PowerSeries.constantCoeff_subst_eq_zero hA _ (Formalism.L2.Th1.D.expSpec ℂ_[p] p hl).1

theorem hypZ_of_inHyp : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {M N N' r : ℕ} (eA : Fin M ≃ R × Fin N)
    (f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p) (Θ : MvPowerSeries (Fin r) ℂ_[p]), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (Formalism.L2.Th1.D.thetaInZ (d := nP D p) p (MaximalUnramifiedExtension p).subtype σ om oms
        (subst (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' =>
            (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) :
              MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p]))
          (Formalism.L2.Th1.Top.inHyp p f f'
            (subst (fun i : Fin r => (Formalism.InvariantFactorPaths.G7.at1 i (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) Θ)))) =
      subst (hypZ D p σ om oms R f f') Θ := by
  intro D p _ hp σ om oms R M N N' r eA f f' Θ
  have hl : 2 ≤ p := by omega
  have hcl : PowerSeries.constantCoeff (lgF ℂ_[p] p) = 0 := Formalism.L2.Th1.D.Pair.cc_lgF hl
  have hA0 : HasSubst (fun i : Fin r => (at1 i (lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun i => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i hcl
  have hu : ∀ k : ((R × Fin (nP D p / 2)) × Fin N × Fin N') ⊕ ((R × Fin (nP D p / 2)) × Fin N × Fin N'),
      constantCoeff ((Sum.elim (fun e => (X (false, e) : MvPowerSeries (Bool × ((R × Fin (nP D p / 2)) × Fin N × Fin N')) ℂ_[p]))
        (fun e => X (true, e))) k) = 0 := by
    intro k; cases k <;> simp
  have hhc : HasSubst (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) (MaximalUnramifiedExtension p).subtype f f') :=
    hasSubst_of_constantCoeff_zero fun i => cc_flin hl _ _ hu

  have hL : ∀ i : Fin r, subst (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) (MaximalUnramifiedExtension p).subtype f f')
      (at1 i (lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p]) =
      ∑ e : (R × Fin (nP D p / 2)) × Fin N × Fin N',
        (C ((f e i : MaximalUnramifiedExtension p) : ℂ_[p]) * at1 (false, e) (lgF ℂ_[p] p) +
          C ((f' e i : MaximalUnramifiedExtension p) : ℂ_[p]) * at1 (true, e) (lgF ℂ_[p] p)) := by
    intro i
    rw [Formalism.L2.Th1.D.Pair.subst_single_var hhc]
    unfold Formalism.L2.Th1.E.hypCoord
    rw [lg_flin hl _ _ hu, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    rfl

  set ren1 := (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' =>
            (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) :
              MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p])) with hren1
  set Y := (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) with hYdef
  have hR : HasSubst ren1 := hasSubst_of_constantCoeff_zero fun x => constantCoeff_X _
  have hX : HasSubst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) :=
    hasSubst_of_constantCoeff_zero (CofactorConverse.cc_xOfZ hl _ σ om oms)
  have hY : HasSubst Y := hasSubst_of_constantCoeff_zero fun y => constantCoeff_X _
  have hRX0 : ∀ x, constantCoeff (subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) (ren1 x)) = 0 :=
    fun x => constantCoeff_subst_eq_zero hX (CofactorConverse.cc_xOfZ hl _ σ om oms) (constantCoeff_X _)
  have hRX : HasSubst (fun x => subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) (ren1 x)) :=
    hasSubst_of_constantCoeff_zero hRX0
  set W := (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' => subst Y
    (subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms) (ren1 x))) with hWdef
  have hW : HasSubst W := hasSubst_of_constantCoeff_zero fun x =>
    constantCoeff_subst_eq_zero hY (fun y => constantCoeff_X _) (hRX0 x)
  have hcomp : ∀ g : MvPowerSeries (Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N') ℂ_[p], subst Y (subst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms)
      (subst ren1 g)) = subst W g := by
    intro g
    rw [subst_comp_subst_apply hR hX, subst_comp_subst_apply hRX hY]
  have hLf : HasSubst (fun i : Fin r => subst (Formalism.L2.Th1.E.hypCoord (lgF ℂ_[p] p) (Formalism.L2.Th1.D.expF ℂ_[p] p) (MaximalUnramifiedExtension p).subtype f f')
      (at1 i (lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun i => constantCoeff_subst_eq_zero hhc (fun i => cc_flin hl _ _ hu)
      (Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i hcl)

  have hWx : ∀ (c : Bool) (e : (R × Fin (nP D p / 2)) × Fin N × Fin N'), subst W (at1 (c, e) (lgF ℂ_[p] p)) =
      ∑ s : ZMod (nP D p), C ((MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY σ om oms (c, e.1.2) s)) *
        (X (OrbitPlaces.orbMap D p e.1.1 s, e.2.1, e.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) := by
    intro c e
    rw [Formalism.L2.Th1.D.Pair.subst_single_var hW]
    simp only [hWdef, hren1]
    rw [subst_X hX]
    have ha : PowerSeries.HasSubst (Formalism.L2.Th1.D.xOfZ (d := nP D p) (N0 := M) (N1 := N') p (MaximalUnramifiedExtension p).subtype σ om oms
        (c, e.1.2, eA.symm (e.1.1, e.2.1), e.2.2)) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (CofactorConverse.cc_xOfZ hl _ σ om oms _)
    rw [← Formalism.L2.Th1.D.Pair.subst_subst1 hY ha]
    have hlog := CofactorConverse.log_xOfZ (d := nP D p) hl (MaximalUnramifiedExtension p).subtype σ om oms (eA.symm (e.1.1, e.2.1)) e.2.2 (c, e.1.2)
    simp only at hlog
    rw [hlog]
    unfold CofactorConverse.linP
    rw [← coe_substAlgHom hY]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul]
    simp only [coe_substAlgHom hY, subst_C]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [subst_X hY]
    simp only [hYdef, Equiv.apply_symm_apply]
  have hEv : ∀ (k : Fin (nP D p / 2)) (q : OrbitPlaces.Pl D) (a : Fin N) (b : Fin N'),
      (∑ s : ZMod (nP D p), C ((MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY σ om oms (false, k) s)) *
        (X (OrbitPlaces.orbMap D p q s, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) =
      linEv D p σ (oms k) q a b := by
    intro k q a b
    unfold linEv
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY
    by_cases hs : s.val % 2 = 0 <;> simp [hs]
  have hOd : ∀ (k : Fin (nP D p / 2)) (q : OrbitPlaces.Pl D) (a : Fin N) (b : Fin N'),
      (∑ s : ZMod (nP D p), C ((MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY σ om oms (true, k) s)) *
        (X (OrbitPlaces.orbMap D p q s, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) =
      linOd D p σ (om k) q a b := by
    intro k q a b
    unfold linOd
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.pXY
    by_cases hs : s.val % 2 = 0 <;> simp [hs]
  unfold Formalism.L2.Th1.D.thetaInZ Formalism.L2.Th1.Top.inHyp
  rw [hcomp, subst_comp_subst_apply hA0 hhc, subst_comp_subst_apply hLf hW]
  congr 1
  funext i
  rw [hL i]

  rw [← coe_substAlgHom hW]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_add (f := _), map_mul]
  simp only [coe_substAlgHom hW, subst_C, hWx, hEv, hOd]
  rfl

end GlobalTheory.KerStd.HypOrbit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperbolicPairAdditiveCoordsLinearFormsStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitPlaces_thetaSeries_subst_orbMap_eq : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p)
    (R : Finset (OrbitPlaces.Pl D)) {M N N' r : ℕ} (eA : Fin M ≃ R × Fin N)
    (f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p) (Θ : MvPowerSeries (Fin r) ℂ_[p]), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (Formalism.L2.Th1.D.thetaInZ (d := nP D p) p (MaximalUnramifiedExtension p).subtype σ om oms
        (subst (fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' =>
            (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) :
              MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p]))
          (Formalism.L2.Th1.Top.inHyp p f f'
            (subst (fun i : Fin r => (Formalism.InvariantFactorPaths.G7.at1 i (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) Θ)))) =
      subst (hypZ D p σ om oms R f f') Θ := by
  first | exact @GlobalTheory.KerStd.HypOrbit.hypZ_of_inHyp | exact GlobalTheory.KerStd.HypOrbit.hypZ_of_inHyp | (intros; apply GlobalTheory.KerStd.HypOrbit.hypZ_of_inHyp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitIdentityAllOfIntegralClassHostLog
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd
namespace IntegralSeriesSubstitution
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)

theorem orb_bijective (D : D7) (p : ℕ) (R : Finset (OrbitPlaces.Pl D)) (hR : OrbitPlaces.IsReps D p R) :
    Function.Bijective (fun x : R × ZMod (nP D p) => OrbitPlaces.orbMap D p x.1 x.2) := by
  constructor
  · rintro ⟨⟨r, hr⟩, s⟩ ⟨⟨r', hr'⟩, s'⟩ h
    simp only at h
    have h1 : ∃ e : ℕ, posPl D p r e = OrbitPlaces.orbMap D p r s := ⟨s.val, rfl⟩
    have h2 : ∃ e : ℕ, posPl D p r' e = OrbitPlaces.orbMap D p r s := ⟨s'.val, h.symm⟩
    obtain ⟨r0, -, huniq⟩ := hR (OrbitPlaces.orbMap D p r s)
    have hrr : r = r' := (huniq r ⟨hr, h1⟩).trans (huniq r' ⟨hr', h2⟩).symm
    subst hrr
    have hs : s = s' := PI.OrbJet.OrbW.orbMap_inj D p r h
    subst hs
    rfl
  · intro z
    obtain ⟨r, ⟨hr, e, he⟩, -⟩ := hR z
    refine ⟨(⟨r, hr⟩, (e : ZMod (nP D p))), ?_⟩
    show OrbitPlaces.orbMap D p r (e : ZMod (nP D p)) = z
    exact (PI.OrbJet.OrbW.posPl_eq_orbMap D p r e).symm.trans he

theorem subst_entLog_orb (D : D7) (p : ℕ) [Fact p.Prime] {M N N' : ℕ} (κ : Fin M → OrbitPlaces.Pl D × Fin N)
    (y : ZV (nP D p) M N') :
    subst (fun y' : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (κ y'.2.1).1 y'.1, (κ y'.2.1).2, y'.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (entLog (K := ℂ_[p]) p y) = OrbitPlaces.logPl D p (OrbitPlaces.orbMap D p (κ y.2.1).1 y.1, (κ y.2.1).2, y.2.2) := by
  obtain ⟨s, a', b⟩ := y
  have hY : HasSubst (fun s' : ZMod (nP D p) => (X (s', a', b) : MvPowerSeries (ZV (nP D p) M N') ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hπ : HasSubst (fun y' : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (κ y'.2.1).1 y'.1, (κ y'.2.1).2, y'.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hY2 : HasSubst (fun s' : ZMod (nP D p) => (X (s', (κ a').2, b) : MvPowerSeries (ZV (nP D p) N N') ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hP : HasSubst (X ∘ ⇑(PI.OrbJet.AU.pE D p (κ a').1 (Fin N × Fin N')) :
      ZMod (nP D p) × Fin N × Fin N' → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hE := PI.OrbJet.AU.rename_jet D p (β := Fin N × Fin N') (κ a').1 (s, (κ a').2, b)
  rw [Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel.jetLogG_eq_entLog p (nP D p) N N' (s, (κ a').2, b),
    GlobalTheory.KerStd.CofactorConverse.entLog_eq_letLog, MvPowerSeries.rename_eq_subst,
    subst_comp_subst_apply hY2 hP] at hE
  show _ = PI.OrbJet.logPl D p (PI.OrbJet.AU.pE D p (κ a').1 (Fin N × Fin N') (s, (κ a').2, b))
  rw [← hE, GlobalTheory.KerStd.CofactorConverse.entLog_eq_letLog, subst_comp_subst_apply hY hπ]
  congr 1
  funext s'
  rw [subst_X hπ, subst_X hP]
  rfl

theorem integral_subst_X_of_injective {K : Type} [NormedField K] {σ τ : Type} [Finite σ] (φ : σ → τ)
    (hφ : Function.Injective φ) {U : MvPowerSeries σ K} (hU : Integral U) :
    Integral (subst (fun x => (X (φ x) : MvPowerSeries τ K)) U) := by
  classical
  let e : σ ↪ τ := ⟨φ, hφ⟩
  have h : subst (fun x => (X (φ x) : MvPowerSeries τ K)) U = rename e U := by
    rw [rename_eq_subst]; rfl
  intro n
  rw [h]
  by_cases hn : ∃ m, Finsupp.embDomain e m = n
  · obtain ⟨m, rfl⟩ := hn
    rw [coeff_embDomain_rename]
    exact hU m
  · rw [coeff_rename_eq_zero]
    · simp
    · rintro ⟨m, hm⟩
      exact hn ⟨m, by rw [Finsupp.embDomain_eq_mapDomain]; exact hm⟩

theorem sumE_reindex {K : Type} [Field K] {R ι : Type} [Fintype R] [Fintype ι] {M N N' : ℕ} (eA : Fin M ≃ R × Fin N)
    (be : MvPowerSeries (Fin 2) K) :
    subst (fun x : Bool × (R × ι) × Fin N × Fin N' =>
        (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) : MvPowerSeries (Bool × ι × Fin M × Fin N') K))
      (Formalism.L2.Th1.D.sumE (ι := R × ι) (N0 := N) (N1 := N') be) = Formalism.L2.Th1.D.sumE (ι := ι) (N0 := M) (N1 := N') be := by
  have hρ : HasSubst (fun x : Bool × (R × ι) × Fin N × Fin N' =>
      (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) : MvPowerSeries (Bool × ι × Fin M × Fin N') K)) :=
    hasSubst_of_constantCoeff_zero fun x => constantCoeff_X _
  unfold Formalism.L2.Th1.D.sumE
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coe_substAlgHom hρ, map_sum]
  let E : (R × ι) × Fin N × Fin N' ≃ ι × Fin M × Fin N' :=
    { toFun := fun e => (e.1.2, eA.symm (e.1.1, e.2.1), e.2.2)
      invFun := fun e => (((eA e.2.1).1, e.1), (eA e.2.1).2, e.2.2)
      left_inv := fun ⟨⟨r, k⟩, a, b⟩ => by simp
      right_inv := fun ⟨k, a, b⟩ => by simp }
  refine Fintype.sum_equiv E _ _ fun e => ?_
  rw [coe_substAlgHom, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun a => constantCoeff_X _) hρ]
  congr 1
  funext a
  rw [subst_X hρ]
  split_ifs <;> rfl

theorem orbitIdentity_all_of_integralClass_hostLog : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → OrbitPlaces.OrbOK D p → ∀ (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (ζ : MaximalUnramifiedExtension p), BeData p (nP D p) σ F (cob F (phFF p g2 g3 s2 ε)) om oms ζ → ∀ (R : Finset (OrbitPlaces.Pl D)), OrbitPlaces.IsReps D p R → ∀ (N N' r : ℕ) (f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p), HypPair σ f f' → ∀ (Θ : MvPowerSeries (Fin r) ℂ_[p]), HostLog p g2 g3 s2 ε Θ → ∀ (ep : ℂ_[p]) (Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (hypZ D p σ om oms R f f') Θ → OrbitPlaces.ThetaExpansionAllPlaces D p R ep (fun _ => -1) (fun _ => beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ) Th := by
  intro D p _ g2 g3 s2 ε σ F hC hO om oms ζ hB R hR N N' r f f' hH Θ hΘ ep Th hTh
  obtain ⟨h5, hg2, hg3, hε, hth, hσ, hF, hN⟩ := hC
  have hBd := hB
  obtain ⟨-, -, hF1, hF2, hOw, hTr, hζ⟩ := hB
  have hI := (HostLog.iff_phSum p g2 g3 s2 ε Θ).1 hΘ
  obtain ⟨U0, Φ, hU0, hΦ0, hsim, hEq⟩ := Formalism.L2.Th1.Top.HypShape_of Formalism.L2.Th1.Top.CalcC_proof p h5 g2 g3 ε s2
    hg2 hg3 hε hth σ hσ F hF hN N N' (R × Fin (nP D p / 2)) (Fin r) f f' hH _ hI

  let M := Fintype.card R * N
  let eA : Fin M ≃ R × Fin N :=
    finProdFinEquiv.symm.trans ((Fintype.equivFin R).symm.prodCongr (Equiv.refl _))
  let rv : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' → Bool × Fin (nP D p / 2) × Fin M × Fin N' :=
    fun x => (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2)
  have hrv : Function.Injective rv := by
    rintro ⟨c, ⟨a1, k⟩, a2, b⟩ ⟨c', ⟨a1', k'⟩, a2', b'⟩ h
    simp only [rv, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have h3' := congrArg eA h3
    simp only [Equiv.apply_symm_apply, Prod.mk.injEq] at h3'
    rw [h1, h2, h3'.1, h3'.2, h4]
  let ρs : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' → MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p] :=
    fun x => X (rv x)
  have hρs : HasSubst ρs := hasSubst_of_constantCoeff_zero fun x => constantCoeff_X _
  have hU0' : Integral (subst ρs U0) := integral_subst_X_of_injective rv hrv hU0
  have hΦ0' : constantCoeff (subst ρs Φ) = 0 :=
    constantCoeff_subst_eq_zero hρs (fun x => constantCoeff_X _) hΦ0
  have hsE := sumE_reindex (ι := Fin (nP D p / 2)) (N' := N') eA (map (MaximalUnramifiedExtension p).subtype (cob F (phFF p g2 g3 s2 ε)))
  have hρe : ρs = fun x : Bool × (R × Fin (nP D p / 2)) × Fin N × Fin N' =>
      (X (x.1, x.2.1.2, eA.symm (x.2.1.1, x.2.2.1), x.2.2.2) : MvPowerSeries (Bool × Fin (nP D p / 2) × Fin M × Fin N') ℂ_[p]) := rfl
  rw [← hρe] at hsE
  have hsim' : Formalism.InvariantFactorPaths.G7.Simeq (subst ρs Φ)
      (Formalism.L2.Th1.D.sumE (ι := Fin (nP D p / 2)) (N0 := M) (N1 := N') (map (MaximalUnramifiedExtension p).subtype (cob F (phFF p g2 g3 s2 ε)))) := by
    rw [← hsE]
    refine ⟨?_, ?_⟩
    · rw [← subst_sub hρs]
      exact constantCoeff_subst_eq_zero hρs (fun x => constantCoeff_X _) hsim.1
    · rw [← subst_sub hρs, ← Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hρs hsim.1]
      exact integral_subst_X_of_injective rv hrv hsim.2
  obtain ⟨U, hU, hUeq⟩ := Formalism.L2.Th1.D.b0 (MaximalUnramifiedExtension p) ℂ_[p] p (nP D p) M N' σ (MaximalUnramifiedExtension p).subtype hσ (fun a => rfl)
    hO.two hO.even F hF _ hF1 hF2 (Fin (nP D p / 2)) om oms hOw hTr ζ hζ (subst ρs U0) (subst ρs Φ) hU0' hΦ0' hsim'

  obtain ⟨g, hg0, hg1, hg2⟩ := Formalism.DworkPowerSeriesWeights.generalized_log_inverse.{0, 0} ℂ_[p] p (Fact.out)
    (ZV (nP D p) M N') (fun y => (y.1 - 2, y.2.1, y.2.2))
  have hent := (Formalism.DworkPowerSeriesWeights.logarithm_weight_comparison.{0} ℂ_[p] p (nP D p) M N').2.1
  have hgE : ∀ y, subst g (entLog (K := ℂ_[p]) p y) = X y := fun y => by rw [hent]; exact hg1 y
  have hfun : entLog (K := ℂ_[p]) (d := nP D p) (N0 := M) (N1 := N') p =
      Formalism.DworkPowerSeriesWeights.genLog p (fun y : ZV (nP D p) M N' => (y.1 - 2, y.2.1, y.2.2)) := funext hent
  have hEg : ∀ y, subst (entLog (K := ℂ_[p]) (d := nP D p) (N0 := M) (N1 := N') p) (g y) = X y := fun y => by
    rw [hfun]; exact hg2 y
  have hZ := hUeq g hg0 hgE
  have hR1 : mvExp (-subst ρs Φ) * subst ρs U0 = subst ρs (Formalism.L2.Th1.Top.inHyp p f f'
      (subst (fun i : Fin r => (Formalism.InvariantFactorPaths.G7.at1 i (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) : MvPowerSeries (Fin r) ℂ_[p])) Θ)) := by
    rw [hEq, subst_mul hρs, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hρs (by rw [map_neg, hΦ0, neg_zero]),
      Formalism.L2.Th1.D.BiextensionSums.subst_neg' hρs]

  let πv : ZV (nP D p) M N' → OrbitPlaces.Pl D × Fin N × Fin N' :=
    fun y => (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2)
  have hπv : Function.Injective πv := by
    rintro ⟨s, a, b⟩ ⟨s', a', b'⟩ h
    simp only [πv, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hb := (orb_bijective D p R hR).1 (a₁ := ((eA a).1, s)) (a₂ := ((eA a').1, s')) h1
    simp only [Prod.mk.injEq] at hb
    have ha : eA a = eA a' := Prod.ext hb.1 h2
    rw [hb.2, eA.injective ha, h3]
  let πs : ZV (nP D p) M N' → MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] := fun y => X (πv y)
  have hπs : HasSubst πs := hasSubst_of_constantCoeff_zero fun x => constantCoeff_X _
  have hgs : HasSubst g := hasSubst_of_constantCoeff_zero hg0
  have hbe0 : constantCoeff (beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ) = 0 :=
    Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel.constant_coeff_zero_of_vanishing_alt p (nP D p) (GlobalTheory.KerStd.bHyps_of_beStd p (nP D p) _ h5 hO.two hO.even
      ⟨σ, F, _, om, oms, ζ, hBd, rfl⟩).2.2.1
  have hπe : πs = fun y : ZV (nP D p) M N' =>
      (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) := rfl
  have hc := GlobalTheory.T.orbitPlaces_thetaSeries_subst_orbMap_eq D p h5 σ om oms R eA f f' Θ
  rw [← hρe, ← hπe] at hc
  have hA := congrArg (subst πs) hZ
  rw [hR1, hc] at hA
  rw [Formalism.DworkPowerSeriesWeights.thetaZ, subst_mul hπs] at hA
  have hlin : subst (Formalism.DworkPowerSeriesWeights.linSub Formalism.DworkPowerSeriesWeights.idM) (subst g U) = subst g U := by
    have : (Formalism.DworkPowerSeriesWeights.linSub Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → MvPowerSeries (ZV (nP D p) M N') ℂ_[p]) = X :=
      funext fun x => Formalism.DworkPowerSeriesWeights.OrbMul.linSub_idM x
    rw [this, subst_self]; rfl
  rw [hlin, subst_comp_subst_apply hgs hπs] at hA
  have hexp := GlobalTheory.T.expFactor_allOrbits_eq_prod_orbits D p R (N' := N') eA (beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ) hbe0
  rw [← hπe] at hexp
  rw [show (MvPowerSeries.map (MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.beMean p σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ)) =
    beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ from rfl] at hA
  rw [hexp] at hA

  have hlog : HasSubst (OrbitPlaces.logPl D p (β := Fin N × Fin N')) :=
    hasSubst_of_constantCoeff_zero (PI.OrbJet.AU.cc_log D p)
  refine ⟨subst πs U, integral_subst_X_of_injective πv hπv hU, ?_⟩
  have hCX : HasSubst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
      (C ep * X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun v => by simp
  have h1 : subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => C ep * OrbitPlaces.logPl D p v) Th =
      subst (OrbitPlaces.logPl D p (β := Fin N × Fin N')) (subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
        (C ep * X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th) := by
    rw [subst_comp_subst_apply hCX hlog]
    congr 1
    funext v
    rw [subst_mul hlog, subst_C, subst_X hlog]
  rw [h1, hTh, hA, subst_mul hlog]
  congr 1
  have hπg : HasSubst (fun y => subst πs (g y)) :=
    hasSubst_of_constantCoeff_zero fun y => constantCoeff_subst_eq_zero hπs (fun x => constantCoeff_X _) (hg0 y)
  rw [subst_comp_subst_apply hπg hlog]
  congr 1
  funext y
  have hlgE : HasSubst (entLog (K := ℂ_[p]) (d := nP D p) (N0 := M) (N1 := N') p) := by
    exact hasSubst_of_constantCoeff_zero fun v => by
      rw [← Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel.jetLogG_eq_entLog]
      exact Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel.cc_jetLogG p (nP D p) v
  rw [subst_comp_subst_apply hπs hlog]
  have e : (fun y' => subst (OrbitPlaces.logPl D p (β := Fin N × Fin N')) (πs y')) =
      fun y' => subst πs (entLog (K := ℂ_[p]) p y') := by
    funext y'
    rw [subst_X hlog]
    exact (subst_entLog_orb D p (N' := N') (fun a => ((eA a).1, (eA a).2)) y').symm
  rw [e, ← subst_comp_subst_apply hlgE hπs, hEg, subst_X hπs]

end IntegralSeriesSubstitution
end GlobalTheory.KerStd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitIdentityAllOfIntegralClassHostLogStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitIdentity_all_of_integralClass_hostLog_alt : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → OrbitPlaces.OrbOK D p → ∀ (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p) (ζ : MaximalUnramifiedExtension p), BeData p (nP D p) σ F (cob F (phFF p g2 g3 s2 ε)) om oms ζ → ∀ (R : Finset (OrbitPlaces.Pl D)), OrbitPlaces.IsReps D p R → ∀ (N N' r : ℕ) (f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p), HypPair σ f f' → ∀ (Θ : MvPowerSeries (Fin r) ℂ_[p]), HostLog p g2 g3 s2 ε Θ → ∀ (ep : ℂ_[p]) (Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (hypZ D p σ om oms R f f') Θ → OrbitPlaces.ThetaExpansionAllPlaces D p R ep (fun _ => -1) (fun _ => beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ) Th := by
  first | exact @GlobalTheory.KerStd.IntegralSeriesSubstitution.orbitIdentity_all_of_integralClass_hostLog | exact GlobalTheory.KerStd.IntegralSeriesSubstitution.orbitIdentity_all_of_integralClass_hostLog | (intros; apply GlobalTheory.KerStd.IntegralSeriesSubstitution.orbitIdentity_all_of_integralClass_hostLog <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfInertPrimeEllipticCurveLocalData
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfInertPrimeEllipticCurveLocalData
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem BeData.exists_of_curveData : ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p)
    (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → ∀ (d : ℕ) [NeZero d], Even d →
    ∃ (om oms : Fin (d / 2) → MaximalUnramifiedExtension p) (ζ : MaximalUnramifiedExtension p), BeData p d σ F (cob F (phFF p g2 g3 s2 ε)) om oms ζ := by
  intro p _ g2 g3 s2 ε σ F hC d _ hd
  obtain ⟨-, hg2, hg3, hε, hth, hσ, hF, hN⟩ := hC
  have hff := Formalism.L2.Th1.D.FAux.ffs (l := p) Formalism.L2.Th1.D.first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  have hp : p.Prime := Fact.out
  have hd0 : d ≠ 0 := NeZero.ne d
  have h1 : 1 < p ^ d := Nat.one_lt_pow hd0 hp.one_lt
  obtain ⟨ζ, hζ⟩ := Formalism.L2.Th1.D.kurRoots p (p ^ d - 1) (by omega) (fun hdv => by
    have h2 : p ∣ p ^ d := dvd_pow_self p hd0
    have h3 : p ∣ 1 := by
      have := Nat.dvd_sub h2 hdv
      rwa [Nat.sub_sub_self h1.le] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 h3))
  obtain ⟨om, oms, hO, hT⟩ := Formalism.L2.Th1.D.trDualExists (MaximalUnramifiedExtension p) p d σ hσ hd ζ hζ
  exact ⟨om, oms, ζ, hσ, hF, hff.1, hff.2.1, hO, hT, hζ⟩

end GlobalTheory.KerStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfInertPrimeEllipticCurveLocalDataStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_of_inertPrimeEllipticCurveLocalData : ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → ∀ (d : ℕ) [NeZero d], Even d → ∃ (om oms : Fin (d / 2) → MaximalUnramifiedExtension p) (ζ : MaximalUnramifiedExtension p), BeData p d σ F (cob F (phFF p g2 g3 s2 ε)) om oms ζ := by
  first | exact @GlobalTheory.KerStd.BeData.exists_of_curveData | exact GlobalTheory.KerStd.BeData.exists_of_curveData | (intros; apply GlobalTheory.KerStd.BeData.exists_of_curveData <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedFamilyStandardBasesIntegrality
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem normalisedFamily_standardBases_integrality : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), HostAt B χ p lam → OrbitPlaces.OrbOK D p → ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → ∃ (ep : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 ∧ BeStd p (nP D p) be ∧ ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → ∀ R, OrbitPlaces.IsReps D p R → OrbitPlaces.ThetaExpansionAllPlaces D p R ep (fun _ => -1) (fun _ => be) (stdSer D lam (fun _ => 1) P P' G) := by
  intro D cc δ B χ p _ lam hA hO hCS
  obtain ⟨c, g2, g3, s2, ε, σ, F, hc, hCD, hH⟩ := hA
  obtain ⟨om, oms, ζ, hBD⟩ := GlobalTheory.T.exists_of_inertPrimeEllipticCurveLocalData p g2 g3 s2 ε σ F hCD (nP D p) hO.even
  refine ⟨c, beOf p (nP D p) σ (cob F (phFF p g2 g3 s2 ε)) om oms ζ, hc,
    ⟨σ, F, cob F (phFF p g2 g3 s2 ε), om, oms, ζ, hBD, rfl⟩, ?_⟩
  intro N N' L L' P P' hAdm hP hP' G hG R hR
  obtain ⟨r, b, hb, ho, hint⟩ := hH N N' L L' hAdm
  obtain ⟨f, f', hf, heq⟩ := GlobalTheory.T.standardSeries_scaled_eq_orthonormalSeries_hyperbolicSubst D p lam σ hCD.2.2.2.2.2.1 hO hCS om oms hBD.2.2.2.2.1 hBD.2.2.2.2.2.1
    R hR N N' L L' P P' hAdm hP hP' r b hb ho
  exact GlobalTheory.T.orbitIdentity_all_of_integralClass_hostLog_alt D p g2 g3 s2 ε σ F hCD hO om oms ζ hBD R hR N N' r f f' hf (thOrth D lam c b G) (hint G hG) c
    (stdSer D lam (fun _ => 1) P P' G) (heq c G)

end GlobalTheory.KerStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedFamilyStandardBasesIntegralityStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFamily_standardBases_integrality_alt : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), HostAt B χ p lam → OrbitPlaces.OrbOK D p → ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → ∃ (ep : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 ∧ BeStd p (nP D p) be ∧ ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → ∀ R, OrbitPlaces.IsReps D p R → OrbitPlaces.ThetaExpansionAllPlaces D p R ep (fun _ => -1) (fun _ => be) (stdSer D lam (fun _ => 1) P P' G) := by
  first | exact @GlobalTheory.KerStd.normalisedFamily_standardBases_integrality | exact GlobalTheory.KerStd.normalisedFamily_standardBases_integrality | (intros; apply GlobalTheory.KerStd.normalisedFamily_standardBases_integrality <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleKernelSeriesInertPrimeNonConjugateFrob
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem exists_beFam_evenConditionsInert_of_kerEnt : Formalism.L2.KerInert.AlgTAll → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam) → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.Hyp → t.Adapted → 3 ≤ D.host.splitBound → ∃ ep be, BeFam D ep be ∧ OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be (fun _ _ => -1)) Y := by
  intro hAlg hHost D L hT Gi Gl K Y cX ex t hHyp hAd h3
  have hOrb := (Formalism.MainNotions.DIV.Inh.orbit_admissible_of_split_bound D h3).1
  have key : ∀ w : D.what₂.places.Pl, ∃ (e : ℂ_[D.what₂.places.resChar w])
      (b : MvPowerSeries (ZMod (nP D (D.what₂.places.resChar w))) ℂ_[D.what₂.places.resChar w]),
      ((IsResidueClassZero D (D.what₂.places.resChar w) ∧ HEv D (D.what₂.places.resChar w)) ∨ IsSg D (D.what₂.places.resChar w)) →
      ‖e‖ = 1 ∧ BeStd (D.what₂.places.resChar w) (nP D (D.what₂.places.resChar w)) b ∧
      ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
        (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E),
        admitted D N N' L L' → StdBases D (t.ent.lam w) L P → StdBases D (t.ent.lam w) L' P' →
        ∀ G, IsComb D t.B.tor (t.B.eNat t.χ) (t.ent.lam w) L L' G → ∀ R, OrbitPlaces.IsReps D (D.what₂.places.resChar w) R →
          OrbitPlaces.ThetaExpansionAllPlaces D (D.what₂.places.resChar w) R e (fun _ => -1) (fun _ => b) (stdSer D (t.ent.lam w) (fun _ => 1) P P' G) := by
    intro w
    by_cases hc : (IsResidueClassZero D (D.what₂.places.resChar w) ∧ HEv D (D.what₂.places.resChar w)) ∨ IsSg D (D.what₂.places.resChar w)
    · have hO := hOrb _ (D.what₂.places.resChar_prime w) hc
      have hH := hHost D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok (D.what₂.places.resChar w) (t.ent.lam w) hO.five
        (hc.imp_left And.left)
      obtain ⟨e, b, he, hb, hB⟩ := GlobalTheory.T.normalisedFamily_standardBases_integrality_alt D t.cc t.δ t.B t.χ _ (t.ent.lam w) hH hO (hc.imp_left (And.imp_right HEv.ne_zero))
      exact ⟨e, b, fun _ => ⟨he, hb, hB⟩⟩
    · exact ⟨1, 0, fun h => absurd h hc⟩
  choose ep be hbe using key
  refine ⟨ep, fun w _ => be w, ?_, ?_⟩
  · intro w hc
    obtain ⟨he, hb, -⟩ := hbe w hc
    exact ⟨he, fun _ => hb⟩
  · intro u μ w hLev hc R hR
    obtain ⟨he, hb, hB⟩ := hbe w hc
    have hO := hOrb _ (D.what₂.places.resChar_prime w) hc
    refine ⟨⟨he, fun _ _ => Or.inr rfl, fun _ _ => GlobalTheory.T.standard_series_b_conditions_large_prime _ _ _ hO.five hO.two hO.even hb⟩, ?_⟩
    intro i hi _ c c'
    have hAdPl : Formalism.L2.Ker.AdPl D w := by
      rcases hc with h | h
      · exact Or.inl h.1
      · exact Or.inr (Or.inl h)
    obtain ⟨Pm, hBas, -, hConj, hTh⟩ := hAd w hAdPl u μ hLev
    have hcomb := GlobalTheory.Ggeo.KerComb.comb_of_tied hAlg D L hT Gi Gl K Y cX ex t hHyp u μ w hLev i hi c c'
    have hS : ∀ j, j ≤ D.R.m → ∀ c, StdBases D (t.ent.lam w) ((t.O u μ).lat j c).1 (Pm j c) := fun j hj c =>
      GlobalTheory.T.isStandardBasesLatticeAtPlace_of_adapted_bases D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat j c).2.1 (fun τ => hBas j hj c τ)
        (fun τ τ' h => hConj j hj c τ τ' h)
    show OrbitPlaces.ThetaExpansionAllPlaces D _ R (ep w) (fun _ => -1) (fun _ => be w) (t.ent.Th u μ w i c c')
    rw [hTh i hi c c', GlobalTheory.T.atLin_adaptedCoef_eq_standardSeries]
    exact hB _ _ _ _ _ _ hcomb.1 (hS i hi.le c) (hS (i + 1) hi c') _ hcomb.2 R hR

end GlobalTheory.KerStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleKernelSeriesInertPrimeNonConjugateFrobStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleKernelSeries_inertPrime_nonConjugateFrobenius : Formalism.L2.KerInert.AlgTAll → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam) → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.Hyp → t.Adapted → 3 ≤ D.host.splitBound → ∃ ep be, BeFam D ep be ∧ OrbitPlaces.EvenConditionsInert (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be (fun _ _ => -1)) Y := by
  first | exact @GlobalTheory.KerStd.exists_beFam_evenConditionsInert_of_kerEnt | exact GlobalTheory.KerStd.exists_beFam_evenConditionsInert_of_kerEnt | (intros; apply GlobalTheory.KerStd.exists_beFam_evenConditionsInert_of_kerEnt <;> assumption)
end
