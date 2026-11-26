module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.CoordFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.LatticeOfEntriesIntegral
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeFinK

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeMaxCpt
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MaximalCompactConjugacy.Assembly
noncomputable section

namespace PI.BridgeMaxCptWork

open NumberField IsDedekindDomain Matrix
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge

theorem conj_unitary_iff {n : ℕ} (P θ : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) :
    ((P⁻¹ * θ * P)ᴴ * (P⁻¹ * θ * P) = 1) ↔
      θᴴ * ((P⁻¹)ᴴ * P⁻¹) * θ = (P⁻¹)ᴴ * P⁻¹ := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPi : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have hPi' : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have hH : Pᴴ * (P⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hPi, Matrix.conjTranspose_one]
  have hH' : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hPi', Matrix.conjTranspose_one]
  have e1 : (P⁻¹ * θ * P)ᴴ * (P⁻¹ * θ * P) = Pᴴ * (θᴴ * ((P⁻¹)ᴴ * P⁻¹) * θ) * P := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e1]
  constructor
  · intro h
    calc θᴴ * ((P⁻¹)ᴴ * P⁻¹) * θ
        = (P⁻¹)ᴴ * Pᴴ * (θᴴ * ((P⁻¹)ᴴ * P⁻¹) * θ) * (P * P⁻¹) := by
          rw [hH', hPi', Matrix.one_mul, Matrix.mul_one]
      _ = (P⁻¹)ᴴ * (Pᴴ * (θᴴ * ((P⁻¹)ᴴ * P⁻¹) * θ) * P) * P⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * P⁻¹ := by rw [h, Matrix.mul_one]
  · intro h
    rw [h, ← Matrix.mul_assoc, hH, Matrix.one_mul, hPi]

theorem kinf_iff (hR : PI.AdBridgeSteps.RealK) (I : AutInst) (e : I.GA ≃ₜ* HAd I)
    (hb : IsBridge I e) (x : I.GA) : (∀ v, x.1 v ∈ KinfV I v) ↔ e x ∈ KinfHA I := by
  have key : ∀ v, (x.1 v ∈ KinfV I v ↔
      ((hmat I (e x)).map (thetaV I v))ᴴ * majV I v * (hmat I (e x)).map (thetaV I v) =
        majV I v) := by
    intro v
    have hu : uMat (x.1 v) = (I.P v)⁻¹ * (hmat I (e x)).map (thetaV I v) * I.P v := (hb x).1 v
    have hP : IsUnit (I.P v) := by
      by_contra hP
      have h0 : (I.P v)⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _
        (fun h => hP ((Matrix.isUnit_iff_isUnit_det _).mpr h))
      have hU : IsUnit (uMat (x.1 v)) := Units.isUnit _
      rw [hu, h0, zero_mul, zero_mul] at hU
      haveI : Subsingleton (Matrix (Fin I.n) (Fin I.n) ℂ) :=
        subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hU)
      exact hP (by rw [Subsingleton.elim (I.P v) 1]; exact isUnit_one)
    have hk : Formalism.REAL.inUJ (I.ε v) (uMat (x.1 v)) := (x.1 v).2
    have h1 := hR I.n (I.ε v) (uMat (x.1 v)) hk
    calc x.1 v ∈ KinfV I v ↔ (uMat (x.1 v))ᴴ * uMat (x.1 v) = 1 := h1.symm
      _ ↔ _ := by rw [hu]; exact conj_unitary_iff _ _ hP
  show (∀ v, x.1 v ∈ KinfV I v) ↔ ∀ v, ((hmat I (e x)).map (thetaV I v))ᴴ * majV I v *
    (hmat I (e x)).map (thetaV I v) = majV I v
  exact forall_congr' key

theorem kf_iff (hF : PI.AdBridgeSteps.FinK) (I : AutInst) (e : I.GA ≃ₜ* HAd I)
    (hb : IsBridge I e) (x : I.GA) : x.2 ∈ I.Kset ↔ e x ∈ KfHA I := by
  have h := hF I (e x)
  rw [← (hb x).2] at h
  exact h

theorem mem_KGA_iff (hR : PI.AdBridgeSteps.RealK) (hF : PI.AdBridgeSteps.FinK) (I : AutInst)
    (e : I.GA ≃ₜ* HAd I) (hb : IsBridge I e) (x : I.GA) : x ∈ KGA I ↔ e x ∈ KHA I := by
  show ((∀ v, x.1 v ∈ KinfV I v) ∧ x.2 ∈ I.Kset) ↔ (e x ∈ KinfHA I ∧ e x ∈ KfHA I)
  exact and_congr (kinf_iff hR I e hb x) (kf_iff hF I e hb x)

theorem bridgeMaxCpt_of (hR : PI.AdBridgeSteps.RealK) (hF : PI.AdBridgeSteps.FinK) :
    ∀ I : AutInst, AdBridgeK I := by
  intro I e hb
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_KGA_iff hR hF I e hb x).1 hx
  · intro hy
    refine ⟨e.symm y, (mem_KGA_iff hR hF I e hb _).2 ?_, by simp⟩
    simpa using hy

end PI.BridgeMaxCptWork
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RealFieldComparison.JmMulApply
namespace PI.UnitaryGroupMassFormula.BridgeRealK

open Matrix

lemma jm_eq {n : ℕ} (ε : Fin n → Bool) :
    Formalism.REAL.Jm ε = Matrix.diagonal (fun a => if ε a then (1 : ℂ) else -1) := rfl

lemma sgn_mul_self {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    (if ε a then (1 : ℂ) else -1) * (if ε a then (1 : ℂ) else -1) = 1 := by
  cases ε a <;> simp

lemma jm_mul_jm {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  rw [jm_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  exact sgn_mul_self ε a

lemma jm_mul_apply {n : ℕ} (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (Formalism.REAL.Jm ε * k) a b = (if ε a then (1 : ℂ) else -1) * k a b := by
  rw [jm_eq, Matrix.diagonal_mul]

lemma mul_jm_apply {n : ℕ} (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    (k * Formalism.REAL.Jm ε) a b = k a b * (if ε b then (1 : ℂ) else -1) := by
  rw [jm_eq, Matrix.mul_diagonal]

lemma comm_iff {n : ℕ} (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Jm ε * k = k * Formalism.REAL.Jm ε ↔ ∀ a b, ε a ≠ ε b → k a b = 0 := by
  constructor
  · intro h a b hab
    have e := congrFun (congrFun h a) b
    rw [jm_mul_apply, mul_jm_apply] at e
    cases ha : ε a <;> cases hb : ε b
    · exact absurd (ha.trans hb.symm) hab
    · simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] at e
      have h2 : (2 : ℂ) * k a b = 0 := by linear_combination -e
      simpa using h2
    · simp only [ha, hb, Bool.false_eq_true, ↓reduceIte] at e
      have h2 : (2 : ℂ) * k a b = 0 := by linear_combination e
      simpa using h2
    · exact absurd (ha.trans hb.symm) hab
  · intro h
    ext a b
    rw [jm_mul_apply, mul_jm_apply]
    by_cases hab : ε a = ε b
    · rw [hab, mul_comm]
    · rw [h a b hab]; simp

theorem realK : PI.AdBridgeSteps.RealK := by
  intro n ε k hk
  unfold Formalism.REAL.inUJ at hk
  rw [← comm_iff]
  constructor
  · intro hu
    have hu' : k * kᴴ = 1 := mul_eq_one_comm.mp hu
    calc Formalism.REAL.Jm ε * k = (k * kᴴ) * Formalism.REAL.Jm ε * k := by rw [hu', Matrix.one_mul]
      _ = k * (kᴴ * Formalism.REAL.Jm ε * k) := by simp only [Matrix.mul_assoc]
      _ = k * Formalism.REAL.Jm ε := by rw [hk]
  · intro hc
    calc kᴴ * k = kᴴ * k * (Formalism.REAL.Jm ε * Formalism.REAL.Jm ε) := by rw [jm_mul_jm, Matrix.mul_one]
      _ = kᴴ * (k * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by simp only [Matrix.mul_assoc]
      _ = kᴴ * (Formalism.REAL.Jm ε * k) * Formalism.REAL.Jm ε := by rw [hc]
      _ = (kᴴ * Formalism.REAL.Jm ε * k) * Formalism.REAL.Jm ε := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hk, jm_mul_jm]

end PI.UnitaryGroupMassFormula.BridgeRealK
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeRealK
theorem adelic_compact_real_places : PI.AdBridgeSteps.RealK := PI.UnitaryGroupMassFormula.BridgeRealK.realK
end

theorem adelic_maximal_compact : ∀ I : Formalism.MainNotions.S.AutInst, Formalism.L2.SG.AdBridge.AdBridgeK I :=
  PI.BridgeMaxCptWork.bridgeMaxCpt_of adelic_compact_real_places adelic_compact_finite_places
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.ContinuousOfHAInf
noncomputable section

namespace PI.InvTopW

open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge PI.AdBridgeSteps

variable (I : AutInst)

instance tens_isTopRing : IsTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :=
  haveI : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) := ⟨rfl⟩
  IsModuleTopology.isTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) _

instance hAd_isTopGroup : IsTopologicalGroup (HAd I) :=
  inferInstanceAs (IsTopologicalGroup (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J))

end PI.InvTopW
end
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeRatPts
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalPointsComparison.BridgeApplyEqOfComp
noncomputable section

namespace Formalism.L2.SG.AdBridge

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)

private theorem thetaV_inclR' (I : AutInst) (v : InfinitePlace I.F) (y : I.E) :
    thetaV I v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) y) = I.φ v y := by
  simp [thetaV, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

private theorem tauF_inclR' (I : AutInst) (y : I.E) :
    tauF I (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) y) = Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) y := by
  simp [tauF, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Formalism.UG.inclE]

private theorem map_inclR_map_thetaV (I : AutInst) (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) I.E) :
    (M.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F))).map (thetaV I v) = M.map (I.φ v) := by
  ext i j
  simp only [Matrix.map_apply, thetaV_inclR']

private theorem map_inclR_map_tauF (I : AutInst) (M : Matrix (Fin I.n) (Fin I.n) I.E) :
    (M.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F))).map (tauF I) = M.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := by
  ext i j
  simp only [Matrix.map_apply, tauF_inclR']

theorem bridge_apply_eq_of_comp (I : AutInst) (e : I.GA ≃ₜ* HAd I) (he : IsBridge I e)
    (x : I.GA) (h : HAd I) (h1 : ∀ v, uMat (x.1 v) = ofHAInf I h v)
    (h2 : I.fmat x.2 = ofHAFin I h) : e x = h := by
  have hs : e (e.symm h) = h := by
    first
    | exact e.apply_symm_apply h
    | simp
  have hB := he (e.symm h)
  rw [hs] at hB
  obtain ⟨h1', h2'⟩ := hB
  have hx : x = e.symm h := by
    refine Prod.ext (funext fun v => ?_) ?_
    · exact Subtype.ext (Units.ext ((h1 v).trans (h1' v).symm))
    · exact Subtype.ext (Units.ext (h2.trans h2'.symm))
  rw [hx, hs]

theorem sigR_inclR_star (I : AutInst) (y : I.E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig
              (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) y) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (starRingEnd I.E y) := by
  first
  | (simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Formalism.BasicNotions.CMData.sig]; done)
  | rfl

theorem bc_inclR_mem_HR (I : AutInst) (γ : GL (Fin I.n) I.E)
    (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) :
    Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) γ ∈
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J := by
  have hγ' : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * (γ : Matrix (Fin I.n) (Fin I.n) I.E) = I.J := hγ
  have key : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F))) =
      (Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E)).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, sigR_inclR_star]
  show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F))) *
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.J
  rw [key, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, ← Matrix.map_mul, ← Matrix.map_mul, hγ']

theorem adBridgeGF_main (I : AutInst) : AdBridgeGF I := by
  unfold AdBridgeGF
  intro e he
  ext h
  constructor
  · rintro ⟨x, hxG, rfl⟩
    obtain ⟨γ, hγ, hinf, hfin⟩ := hxG
    have hmem := bc_inclR_mem_HR I γ hγ
    let h0 : HAd I := (⟨Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) γ, hmem⟩ :
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J)
    have hm0 : hmat I h0 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) := rfl
    have hx : e x = h0 := by
      apply bridge_apply_eq_of_comp I e he x h0
      · intro v
        rw [hinf v]
        unfold ofHAInf
        rw [hm0, map_inclR_map_thetaV]
      · rw [hfin]
        unfold ofHAFin
        rw [hm0, map_inclR_map_tauF]
    rw [hx]
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h0 ∈
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFin (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J
    exact Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩
  · intro hh
    have hh' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h ∈
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HFin (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J := hh
    obtain ⟨γ, hγ, hγh⟩ := Subgroup.mem_map.mp hh'
    have hm : hmat I h = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)) := by
      show ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h :
        GL (Fin I.n) ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) ⊗[I.F] I.E)) = _
      rw [← hγh]
      rfl
    have hs : e (e.symm h) = h := by
      first
      | exact e.apply_symm_apply h
      | simp
    refine ⟨e.symm h, ?_, hs⟩
    simp only [Formalism.MainNotions.S.AutInst.GFset, Set.mem_setOf_eq]
    refine ⟨γ, hγ, fun v => ?_, ?_⟩
    · rw [(he (e.symm h)).1 v, hs]
      unfold ofHAInf
      rw [hm, map_inclR_map_thetaV]
    · rw [(he (e.symm h)).2, hs]
      unfold ofHAFin
      rw [hm, map_inclR_map_tauF]

end Formalism.L2.SG.AdBridge
end
end

theorem adelic_rational_points : ∀ I : Formalism.MainNotions.S.AutInst, Formalism.L2.SG.AdBridge.AdBridgeGF I :=
  Formalism.L2.SG.AdBridge.adBridgeGF_main
end

namespace Formalism.L2.SG.Closed

theorem AdBridgeIso_holds (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.SG.AdBridge.AdBridgeIso I :=
  Formalism.L2.SG.Pf.adelic_isomorphism_exists (I := I)

theorem AdBridgeGF_holds (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.SG.AdBridge.AdBridgeGF I := adelic_rational_points I

theorem AdBridgeK_holds (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.SG.AdBridge.AdBridgeK I := adelic_maximal_compact I

theorem adelic_isomorphism_statement (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.SG.AdBridge.AdelicIsomorphism I :=
  Formalism.L2.SG.Pf.adelic_isomorphism_of_parts (I := I) (adelic_rational_points I) (adelic_maximal_compact I)

end Formalism.L2.SG.Closed
