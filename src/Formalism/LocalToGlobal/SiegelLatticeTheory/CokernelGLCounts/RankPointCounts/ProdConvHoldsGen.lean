module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdFull
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXTyped
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqWire
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocFramePrim
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolVFinal

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvCut
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)

def AlConvC : Prop :=
  Multipliable (fun v : OrdX X => alX X u u' v.1) ∧ 0 < ∏' v : OrdX X, alX X u u' v.1

end Formalism.L2.SG.Pf.ProdConvCut

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.ProdConvCut

end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvOfVolLocPos
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.ProdConvCut

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)

def VolOneAEC : Prop :=
  {v : PlX X | ¬ (localVolumeUnit X ψ v = 1 ∧ ZZX X u u' ψ v = 1 ∧ (∀ l, PPX X u u' ψ l v = 1) ∧ jacX X v = 1)}.Finite

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalFactorsPosTypicalGeneral
noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.ProdConvCut2

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.MassDataX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem local_factors_pos_typical_general {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (ψ : AddChar (AF X.B.I.F) ℂ)
    (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w)
    (u u' : D.what₂.Word) (v : PlX X) (hv : TypAt X v) : 0 < MX X u u' ψ v ∧ 0 < localVolumeUnit X ψ v := by
  let p : TypX X := ⟨v, hv⟩
  have : Submodule.IsFullLattice X.B.I.E X.B.I.L :=
    { toIsLattice := Submodule.IsLattice.of_fg X.B.I.E X.B.I.L_fg
      span_eq_top := X.B.I.L_span }
  have hL := locTieX_of X ψ u (hloc u) (Formalism.L2.SG.Pf.LocVolPrim.primX X u locFramePrim)
  have hL' := locTieX_of X ψ u' (hloc u') (Formalism.L2.SG.Pf.LocVolPrim.primX X u' locFramePrim)
  have hTF := Formalism.L2.SG.Pf.typFacts_holds X hb u u'
  have h := locMassTyp X.B.I.cm.sig X.B.I.J ψ v (gAt X v) (frameOf X u) (frameOf X u')
    (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
    ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, hψ, hs⟩ _ _
    (MassDataLevelSSteps.FrameW.frameOf_isStd X u) (MassDataLevelSSteps.FrameW.frameOf_isStd X u')
    (Formalism.L2.SG.Pf.MassDataX.SDL.sdLocX_holds X v) (Formalism.L2.SG.Pf.NcX.OmVSt.unramAt_of_cm X.B.I.cm v)
    ⟨X.B.I.L, inferInstance, rfl⟩ (hTF p).1
    (gAt_mem X p) (hTF p).2.1 (hTF p).2.2.1 (hTF p).2.2.2.2
    _ (hL v).1 _ (hL v).2.1 (hL v).2.2.1 _ (hL' v).2.1 (hL' v).2.2.1 (hL v).2.2.2 (hL' v).2.2.2
  have hpos := div_pos (mul_pos (gv_pos X p (kg_sub_kv X p) subset_rfl)
      (gv_pos X p (kg_sub_knat X p u) (knat_sub_kv X p u)))
      (mul_pos (sv_pos X u p (kg_sub_kv X p) subset_rfl) (sv_pos X u' p (kg_sub_kv X p) subset_rfl))
  have hR : 0 < MX X u u' ψ v / localVolumeUnit X ψ v := by
    unfold MX localVolumeUnit OmX
    rw [if_pos hv, if_pos hv]
    exact lt_of_lt_of_eq hpos h.symm
  have hU0 : 0 ≤ localVolumeUnit X ψ v := ENNReal.toReal_nonneg
  rcases div_pos_iff.1 hR with ⟨h1, h2⟩ | ⟨-, h2⟩
  · exact ⟨h1, h2⟩
  · exact absurd h2 (not_lt.2 hU0)

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnramifiedFactorEqOne
noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcVal
  Formalism.L2.SG.Pf.NcVal.VolOrdW Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.SG.TypedSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem absV_prod {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (s : Finset ι)
    (f : ι → Fv F v) : absV v (∏ i ∈ s, f i) = ∏ i ∈ s, absV v (f i) := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.prod_empty]
    exact absV_one v
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, absV_mul, ih]

theorem absV_alp_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (h1 : absV v (dV v) = 1)
    (r : ℕ) (i : Fin (r + 1)) : absV v (alp v r i) = 1 := by
  rw [absV_alp, h1, Real.one_rpow]

section Vols

variable {X} {ψ}

theorem zz_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) : ZZX X u u' ψ v = 1 := by
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH1, -, hO1⟩ := hN v hv (Fin (D.R.rS + 1) × Fin (D.R.rS + 1))
  have := hH1
  have hsetZ : ZZOrd (E := X.B.I.E) v D.R.rS =
      Set.univ.pi fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) =>
        {c | sc (E := X.B.I.E) v (alp v D.R.rS p.1 * alp v D.R.rS p.2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [ZZOrd, locZ, Set.mem_pi, Prod.forall]
  unfold ZZX volS
  rw [if_neg hv, hsetZ, SdW.boxScaleL_holds v (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) hfin
    (sdE (E := X.B.I.E) ψ v (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)))
    (fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => alp v D.R.rS p.1 * alp v D.R.rS p.2)
    (fun p => mul_ne_zero (alp_ne_zero v D.R.rS p.1) (alp_ne_zero v D.R.rS p.2)), hO1, h1, one_pow, one_mul]
  refine Finset.prod_eq_one fun p _ => ?_
  rw [absV_mul, absV_alp_one v h1, absV_alp_one v h1]
  norm_num

theorem uo_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) :
    (sdE (E := X.B.I.E) ψ v (UIdx D.R.rS) (UO (E := X.B.I.E) v D.R.rS)).toReal = 1 := by
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH2, -, hO2⟩ := hN v hv (UIdx D.R.rS)
  have := hH2
  have hsetU : UO (E := X.B.I.E) v D.R.rS =
      Set.univ.pi fun q : UIdx D.R.rS =>
        {c | sc (E := X.B.I.E) v ((alp v D.R.rS q.1.1)⁻¹ * alp v D.R.rS q.1.2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [UO, Set.mem_pi]
  rw [hsetU, SdW.boxScaleL_holds v (UIdx D.R.rS) hfin (sdE (E := X.B.I.E) ψ v (UIdx D.R.rS))
    (fun q : UIdx D.R.rS => (alp v D.R.rS q.1.1)⁻¹ * alp v D.R.rS q.1.2)
    (fun q => mul_ne_zero (inv_ne_zero (alp_ne_zero v D.R.rS q.1.1)) (alp_ne_zero v D.R.rS q.1.2)), hO2, h1,
    one_pow, one_mul]
  refine Finset.prod_eq_one fun q _ => ?_
  rw [absV_mul, absV_inv v (alp_ne_zero v D.R.rS q.1.1), absV_alp_one v h1, absV_alp_one v h1]
  norm_num

theorem unramified_factor_eq_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) : localVolumeUnit X ψ v = 1 := by
  obtain ⟨hH2, hS2, -⟩ := hN v hv (UIdx D.R.rS)
  have := hH2
  have := hS2
  unfold localVolumeUnit volU
  rw [if_neg hv, localVolumeOrdinary, Measure.prod_prod, ENNReal.toReal_mul, uo_one hN hv h1, one_mul]

theorem pp_one (hN : SdNormDV X ψ) {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) (l : Fin (D.R.rS + 1)) :
    PPX X u u' ψ l v = 1 := by
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH, -, hO⟩ := hN v hv Unit
  have := hH
  have hset : (fun c : Unit → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E => c ()) ⁻¹' PPOrd (E := X.B.I.E) v D.R.rS l =
      Set.univ.pi fun _ : Unit => {c | sc (E := X.B.I.E) v (alp v D.R.rS l ^ 2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [PPOrd, Set.mem_pi]
    exact ⟨fun h i => h, fun h => h ()⟩
  unfold PPX volC
  rw [if_neg hv, hset, SdW.boxScaleL_holds v Unit hfin (sdE (E := X.B.I.E) ψ v Unit)
    (fun _ : Unit => alp v D.R.rS l ^ 2) (fun _ => pow_ne_zero _ (alp_ne_zero v D.R.rS l)), hO, h1, one_pow, one_mul]
  refine Finset.prod_eq_one fun q _ => ?_
  rw [absV_pow, absV_alp_one v h1]
  norm_num

theorem jac_one {v : PlX X} (hv : ¬ TypAt X v) (h1 : absV v (dV v) = 1) : jacX X v = 1 := by
  unfold jacX jacS
  refine Finset.prod_eq_one fun l _ => ?_
  rw [if_neg hv, mul_one, absV_prod]
  rw [Finset.prod_eq_one fun i _ => by rw [absV_pow, absV_alp_one v h1, one_pow]]
  norm_num

end Vols

theorem VolOneAEC_holds (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) : VolOneAEC X u u' ψ := by
  have hN : SdNormDV X ψ := sdNormDV_of X ψ (annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different) hψ hs
  have hT : Set.Finite {v : PlX X | TypAt X v} := (typSet X.B.I.F (D.host.g 0) (D.host.g 1)).finite_toSet
  have hI := differentIdeal_ne_zero' X.B.I.F
  have hD := Ideal.hasFiniteMulSupport hI
  refine (hT.union hD).subset fun v hv => ?_
  by_contra hnot
  simp only [Set.mem_union, Set.mem_setOf_eq, Function.mem_mulSupport, not_or, not_not] at hnot
  obtain ⟨htyp, hmax⟩ := hnot
  have h1 : absV v (dV v) = 1 := by rw [absV_dV, hmax, map_one, Nat.cast_one, inv_one]
  exact hv ⟨unramified_factor_eq_one hN htyp h1, zz_one u u' hN htyp h1, fun l => pp_one u u' hN htyp h1 l, jac_one htyp h1⟩

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AbsNormGeTwo
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol
  Formalism.L2.SG.DataInst Formalism.L2.SG.Pf.ProdConvCut Formalism.L2.SG.Pf.AlTie

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word)

theorem etaV_pm (v : PlX X) :
    ((etaV (E := X.B.I.E) v : ℤ) : ℝ) = 1 ∨ ((etaV (E := X.B.I.E) v : ℤ) : ℝ) = -1 := by
  unfold etaV
  split_ifs <;> simp

theorem absNorm_ge_two (v : PlX X) : (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast h2

private theorem exp_bounds_prod_one_sub_pow_div (q η : ℝ) (hq : 2 ≤ q) (hη : η = 1 ∨ η = -1) (k a N : ℕ) (hk : 1 ≤ k)
    (ha : k ≤ a) :
    Real.exp (-(4 * q⁻¹ ^ k)) ≤ ∏ i ∈ Finset.Icc a N, (1 - η ^ i / q ^ i) ∧
      ∏ i ∈ Finset.Icc a N, (1 - η ^ i / q ^ i) ≤ Real.exp (2 * q⁻¹ ^ k) := by
  have hq0 : 0 < q := by linarith
  have hx0 : 0 ≤ q⁻¹ := inv_nonneg.mpr hq0.le
  have hxq : q⁻¹ * q = 1 := inv_mul_cancel₀ hq0.ne'
  have hx2 : q⁻¹ ≤ 1 / 2 := by nlinarith [mul_le_mul_of_nonneg_left hq hx0]
  have hterm : ∀ i : ℕ, |η ^ i / q ^ i| = q⁻¹ ^ i := by
    intro i
    rw [abs_div, abs_pow, abs_pow, abs_of_pos hq0, inv_pow]
    rcases hη with rfl | rfl <;> simp
  have hsum : ∑ i ∈ Finset.Icc a N, q⁻¹ ^ i ≤ 2 * q⁻¹ ^ k := by
    have h1 : ∑ i ∈ Finset.Icc a N, q⁻¹ ^ i ≤ q⁻¹ ^ a / (1 - q⁻¹) := by
      have hI : Finset.Icc a N = Finset.Ico a (N + 1) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hI]
      exact geom_sum_Ico_le_of_lt_one hx0 (by linarith)
    have h2 : q⁻¹ ^ a / (1 - q⁻¹) ≤ 2 * q⁻¹ ^ a := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (pow_nonneg hx0 a) (by linarith : (0 : ℝ) ≤ 1 / 2 - q⁻¹)]
    have h3 : q⁻¹ ^ a ≤ q⁻¹ ^ k := pow_le_pow_of_le_one hx0 (by linarith) ha
    linarith
  constructor
  · have hfac : ∀ i ∈ Finset.Icc a N, Real.exp (-(2 * q⁻¹ ^ i)) ≤ 1 - η ^ i / q ^ i := by
      intro i hi
      have hi1 : i ≠ 0 := by
        have := (Finset.mem_Icc.mp hi).1
        omega
      have hy0 : 0 ≤ q⁻¹ ^ i := pow_nonneg hx0 i
      have hy : q⁻¹ ^ i ≤ 1 / 2 := le_trans (pow_le_of_le_one hx0 (by linarith) hi1) hx2
      have hle : η ^ i / q ^ i ≤ q⁻¹ ^ i := (abs_le.mp (le_of_eq (hterm i))).2
      have he : 1 + 2 * q⁻¹ ^ i ≤ Real.exp (2 * q⁻¹ ^ i) := by
        linarith [Real.add_one_le_exp (2 * q⁻¹ ^ i)]
      have hEF : Real.exp (-(2 * q⁻¹ ^ i)) * Real.exp (2 * q⁻¹ ^ i) = 1 := by
        rw [← Real.exp_add]
        simp
      have hE0 : 0 < Real.exp (-(2 * q⁻¹ ^ i)) := Real.exp_pos _
      have hE12 : Real.exp (-(2 * q⁻¹ ^ i)) * (1 + 2 * q⁻¹ ^ i) ≤ 1 := by
        calc Real.exp (-(2 * q⁻¹ ^ i)) * (1 + 2 * q⁻¹ ^ i)
            ≤ Real.exp (-(2 * q⁻¹ ^ i)) * Real.exp (2 * q⁻¹ ^ i) := mul_le_mul_of_nonneg_left he hE0.le
          _ = 1 := hEF
      have hc : 1 ≤ (1 + 2 * q⁻¹ ^ i) * (1 - q⁻¹ ^ i) := by nlinarith
      calc Real.exp (-(2 * q⁻¹ ^ i))
          ≤ Real.exp (-(2 * q⁻¹ ^ i)) * ((1 + 2 * q⁻¹ ^ i) * (1 - q⁻¹ ^ i)) := le_mul_of_one_le_right hE0.le hc
        _ = (Real.exp (-(2 * q⁻¹ ^ i)) * (1 + 2 * q⁻¹ ^ i)) * (1 - q⁻¹ ^ i) := by ring
        _ ≤ 1 * (1 - q⁻¹ ^ i) := mul_le_mul_of_nonneg_right hE12 (by linarith)
        _ ≤ 1 - η ^ i / q ^ i := by linarith
    calc Real.exp (-(4 * q⁻¹ ^ k))
        ≤ Real.exp (∑ i ∈ Finset.Icc a N, -(2 * q⁻¹ ^ i)) := by
          apply Real.exp_le_exp.mpr
          rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
          linarith
      _ = ∏ i ∈ Finset.Icc a N, Real.exp (-(2 * q⁻¹ ^ i)) := Real.exp_sum _ _
      _ ≤ ∏ i ∈ Finset.Icc a N, (1 - η ^ i / q ^ i) :=
          Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos _).le) hfac
  · have hfac : ∀ i ∈ Finset.Icc a N, 1 - η ^ i / q ^ i ≤ Real.exp (q⁻¹ ^ i) := by
      intro i _
      have := (abs_le.mp (le_of_eq (hterm i))).1
      linarith [Real.add_one_le_exp (q⁻¹ ^ i)]
    have hnn : ∀ i ∈ Finset.Icc a N, 0 ≤ 1 - η ^ i / q ^ i := by
      intro i _
      have := (abs_le.mp (le_of_eq (hterm i))).2
      have hy : q⁻¹ ^ i ≤ 1 := pow_le_one₀ hx0 (by linarith)
      linarith
    calc ∏ i ∈ Finset.Icc a N, (1 - η ^ i / q ^ i)
        ≤ ∏ i ∈ Finset.Icc a N, Real.exp (q⁻¹ ^ i) := Finset.prod_le_prod₀ hnn hfac
      _ = Real.exp (∑ i ∈ Finset.Icc a N, q⁻¹ ^ i) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (2 * q⁻¹ ^ k) := Real.exp_le_exp.mpr hsum

theorem aP_bounds (hk : 1 ≤ D.R.k) (v : PlX X) (T : ℕ) :
    Real.exp (-(4 * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k)) ≤ aP (E := X.B.I.E) v D.R.k X.B.I.n T ∧
      aP (E := X.B.I.E) v D.R.k X.B.I.n T ≤ Real.exp (2 * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k) := by
  unfold aP
  exact exp_bounds_prod_one_sub_pow_div _ _ (absNorm_ge_two X v) (etaV_pm X v) _ _ _ hk (by split_ifs <;> omega)

private theorem exp_bounds_mul_of_exp_bounds (a b y : ℝ) (hy : 0 ≤ y)
    (ha : Real.exp (-(4 * y)) ≤ a ∧ a ≤ Real.exp (2 * y)) (hb : Real.exp (-(4 * y)) ≤ b ∧ b ≤ Real.exp (2 * y)) :
    (Real.exp (-(8 * y)) ≤ a ∧ a ≤ Real.exp (4 * y)) ∧
      (Real.exp (-(8 * y)) ≤ a * b ∧ a * b ≤ Real.exp (4 * y)) := by
  have ha0 : 0 ≤ a := le_trans (Real.exp_pos _).le ha.1
  have hb0 : 0 ≤ b := le_trans (Real.exp_pos _).le hb.1
  refine ⟨⟨le_trans (Real.exp_le_exp.mpr (by linarith)) ha.1, le_trans ha.2 (Real.exp_le_exp.mpr (by linarith))⟩, ?_, ?_⟩
  · calc Real.exp (-(8 * y)) = Real.exp (-(4 * y)) * Real.exp (-(4 * y)) := by
          rw [← Real.exp_add]
          ring_nf
      _ ≤ a * b := mul_le_mul ha.1 hb.1 (Real.exp_pos _).le ha0
  · calc a * b ≤ Real.exp (2 * y) * Real.exp (2 * y) := mul_le_mul ha.2 hb.2 hb0 (Real.exp_pos _).le
      _ = Real.exp (4 * y) := by
          rw [← Real.exp_add]
          ring_nf

theorem alX_bounds (hk : 1 ≤ D.R.k) (v : PlX X) :
    Real.exp (-(8 * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k)) ≤ alX X u u' v ∧
      alX X u u' v ≤ Real.exp (4 * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k) := by
  have h := exp_bounds_mul_of_exp_bounds _ _ ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k) (by positivity)
    (aP_bounds X hk v (Tw u)) (aP_bounds X hk v (Tw u'))
  unfold alX
  split_ifs
  · exact h.1
  · exact h.2

theorem summable_qk (hk2 : 2 ≤ D.R.k) :
    Summable fun v : PlX X => (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k := by
  have hP := Formalism.L2.SG.Pf.placesOver_holds D
  set s := D.R.k with hs
  set a : PlF D → ℝ := fun p => (Formalism.L2.SG.DataCut.qP p ^ s)⁻¹ with ha
  have ha0 : ∀ p, 0 ≤ a p := fun p => inv_nonneg.2 (pow_nonneg (Formalism.L2.SG.DataCut.qP_nonneg p) _)
  have hsum : ∀ S : Finset (PlF D), ∑ p ∈ S, a p ≤ 3 * (D.R.f : ℝ) * ((2 : ℝ) ^ s)⁻¹ := by
    intro S
    exact Formalism.FourierDecayAlt.P.DensitySumsAndDomination.densSum (PlF D) S Formalism.L2.SG.DataCut.qP Loc.resChar D.R.f s hk2
      (fun p _ => ⟨(D.s.atP p).ellPrime.out, hP.1 p⟩)
      (fun m => hP.2 m _ (fun p hp => (Finset.mem_filter.1 hp).2))
  have haS : Summable a := summable_of_sum_le ha0 hsum
  have h1 : Summable fun v : PlX X => a (plEquiv X v) := (plEquiv X).summable_iff.2 haS
  refine h1.congr fun v => ?_
  show (Formalism.L2.SG.DataCut.qP (plEquiv X v) ^ s)⁻¹ = _
  have hq : Formalism.L2.SG.DataCut.qP (plEquiv X v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    rw [← absNorm_plEquiv X v]
    exact Formalism.L2.SG.Pf.LocModel.qPl_eq _
  rw [hq, inv_pow]

theorem AlConvC_holds : AlConvC X u u' := by
  have hk2 : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hk1 : 1 ≤ D.R.k := by omega
  have hpos : ∀ v, 0 < alX X u u' v := fun v => lt_of_lt_of_le (Real.exp_pos _) (alX_bounds X u u' hk1 v).1
  have hlog : Summable fun v : PlX X => Real.log (alX X u u' v) := by
    refine Summable.of_norm_bounded ((summable_qk X hk2).mul_left 8) fun v => ?_
    rw [Real.norm_eq_abs, abs_le]
    obtain ⟨b1, b2⟩ := alX_bounds X u u' hk1 v
    have h1 := Real.log_le_log (Real.exp_pos _) b1
    have h2 := Real.log_le_log (hpos v) b2
    rw [Real.log_exp] at h1 h2
    have hy0 : 0 ≤ (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ ^ D.R.k :=
      pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _
    constructor <;> linarith
  have hlogO : Summable fun v : OrdX X => Real.log (alX X u u' v.1) :=
    hlog.comp_injective (i := fun v : OrdX X => v.1) Subtype.val_injective
  have hposO : ∀ v : OrdX X, 0 < alX X u u' v.1 := fun v => hpos v.1
  refine ⟨Real.multipliable_of_summable_log hposO hlogO, ?_⟩
  rw [← Real.rexp_tsum_eq_tprod hposO hlogO]
  exact Real.exp_pos _

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvNewHoldsGen
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalPositivity
noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.LocalPositivity

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcVal
  Formalism.L2.SG.Pf.NcVal.VolOrdW Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.SG.TypedSets

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem pos_of_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 < a / b) : 0 < a ∧ 0 < b := by
  rcases div_pos_iff.1 h with h' | h'
  · exact h'
  · exact absurd ha (not_le.2 h'.1)

theorem localVolumeUnit_pos_and_ZZX_pos (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ)
    (hTT : (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]) (hg : ∀ v, TypAt X v → 0 < gAt X v) (v : PlX X) :
    0 < localVolumeUnit X ψ v ∧ 0 < ZZX X u u' ψ v := by
  have hU : 0 ≤ localVolumeUnit X ψ v := ENNReal.toReal_nonneg
  have hZ : 0 ≤ ZZX X u u' ψ v := ENNReal.toReal_nonneg
  by_cases hv : TypAt X v
  · have e := volTypV_holds X u u' ψ hψ hs hTT v hv
    exact pos_of_div hU hZ (by rw [e]; exact pow_pos (by exact_mod_cast hg v hv) _)
  · have e := volOrdV_holds X u u' ψ hψ hs v hv
    exact pos_of_div hU hZ (by rw [e]; exact Real.rpow_pos_of_pos (absV_pos v (dV_ne_zero v)) _)

theorem pp_pos_ord (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) {v : PlX X} (hv : ¬ TypAt X v)
    (l : Fin (D.R.rS + 1)) : 0 < PPX X u u' ψ l v := by
  have hN : SdNormDV X ψ := sdNormDV_of X ψ (annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different) hψ hs
  have hfin : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  obtain ⟨hH, -, hO⟩ := hN v hv Unit
  have := hH
  have hset : (fun c : Unit → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E => c ()) ⁻¹' PPOrd (E := X.B.I.E) v D.R.rS l =
      Set.univ.pi fun _ : Unit => {c | sc (E := X.B.I.E) v (alp v D.R.rS l ^ 2) * c ∈ OEv (E := X.B.I.E) v} := by
    ext z
    simp [PPOrd, Set.mem_pi]
    exact ⟨fun h i => h, fun h => h ()⟩
  unfold PPX volC
  rw [if_neg hv, hset, SdW.boxScaleL_holds v Unit hfin (sdE (E := X.B.I.E) ψ v Unit)
    (fun _ : Unit => alp v D.R.rS l ^ 2) (fun _ => pow_ne_zero _ (alp_ne_zero v D.R.rS l)), hO]
  refine mul_pos (pow_pos (absV_pos v (dV_ne_zero v)) _) (Finset.prod_pos fun q _ => ?_)
  exact inv_pos.2 (pow_pos (absV_pos v (pow_ne_zero _ (alp_ne_zero v D.R.rS l))) 2)

theorem jac_pos (hg : ∀ v, TypAt X v → 0 < gAt X v) (v : PlX X) : 0 < jacX X v := by
  unfold jacX jacS
  refine Finset.prod_pos fun l _ => ?_
  have hx : (∏ i ∈ Finset.univ.filter (fun i : Fin (D.R.rS + 1) => (i : ℕ) ≤ (l : ℕ)), alp v D.R.rS i ^ 2) *
      (if TypAt X v then ((gAt X v : Fv X.B.I.F v)⁻¹) ^ ((l : ℕ) + 1) else 1) ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (alp_ne_zero v D.R.rS i)) ?_
    split_ifs with ht
    · refine pow_ne_zero _ (inv_ne_zero ?_)
      exact_mod_cast (hg v ht).ne'
    · exact one_ne_zero
  exact pow_pos (pow_pos (absV_pos v hx) 2) 2

end Formalism.L2.SG.Pf.LocalPositivity
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvNewTies
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.ProdConvCut

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)

def ProdConvNew : Prop :=
  (∀ v, (TypAt X v → 0 < MX X u u' ψ v) ∧ 0 < localVolumeUnit X ψ v ∧ 0 < ZZX X u u' ψ v ∧ (∀ l, 0 < PPX X u u' ψ l v) ∧
    0 < alX X u u' v) ∧
  True ∧ True ∧
  Multipliable (fun v : OrdX X => localVolumeUnit X ψ v.1) ∧ 0 < ∏' v : OrdX X, localVolumeUnit X ψ v.1 ∧
  Multipliable (ZZX X u u' ψ) ∧ 0 < ∏' v : PlX X, ZZX X u u' ψ v ∧
  (∀ l, Multipliable (PPX X u u' ψ l) ∧ 0 < ∏' v : PlX X, PPX X u u' ψ l v) ∧
  Multipliable (fun v : OrdX X => alX X u u' v.1) ∧ 0 < ∏' v : OrdX X, alX X u u' v.1 ∧
  Multipliable (jacX X) ∧ 0 < ∏' v : PlX X, jacX X v

private theorem multipliable_and_tprod_pos_of_finite_mulSupport {ι : Type*} (f : ι → ℝ) (hpos : ∀ i, 0 < f i) (hfin : (Function.mulSupport f).Finite) :
    Multipliable f ∧ 0 < ∏' i, f i := by
  refine ⟨multipliable_of_hasFiniteMulSupport hfin, ?_⟩
  rw [tprod_eq_prod' (s := hfin.toFinset) (by simp)]
  exact Finset.prod_pos fun i _ => hpos i

theorem prodConvNew_of (h1 : VolOneAEC X u u' ψ)
    (hpos : ∀ v, 0 < localVolumeUnit X ψ v ∧ 0 < ZZX X u u' ψ v ∧ (∀ l, 0 < PPX X u u' ψ l v) ∧ 0 < jacX X v)
    (hM : ∀ v, TypAt X v → 0 < MX X u u' ψ v) (hal : ∀ v, 0 < alX X u u' v) (h3 : AlConvC X u u') :
    ProdConvNew X u u' ψ := by
  have hS : ∀ g : PlX X → ℝ, (∀ v, g v ≠ 1 → ¬ (localVolumeUnit X ψ v = 1 ∧ ZZX X u u' ψ v = 1 ∧
      (∀ l, PPX X u u' ψ l v = 1) ∧ jacX X v = 1)) → (Function.mulSupport g).Finite :=
    fun g hg => h1.subset fun v hv => hg v hv
  have hU : (Function.mulSupport fun v : OrdX X => localVolumeUnit X ψ v.1).Finite := by
    refine (h1.preimage Subtype.val_injective.injOn).subset fun v hv => ?_
    intro h
    exact hv h.1
  have hZ := hS (ZZX X u u' ψ) fun v hv h => hv h.2.1
  have hP : ∀ l, (Function.mulSupport (PPX X u u' ψ l)).Finite := fun l => hS _ fun v hv h => hv (h.2.2.1 l)
  have hJ := hS (jacX X) fun v hv h => hv h.2.2.2
  have rU := multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v : OrdX X => (hpos v.1).1) hU
  have rZ := multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v => (hpos v).2.1) hZ
  have rJ := multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v => (hpos v).2.2.2) hJ
  exact ⟨fun v => ⟨hM v, (hpos v).1, (hpos v).2.1, (hpos v).2.2.1, hal v⟩, trivial, trivial, rU.1, rU.2, rZ.1, rZ.2,
    fun l => multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v => (hpos v).2.2.1 l) (hP l), h3.1, h3.2, rJ.1, rJ.2⟩

theorem prodConvNew_gen (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ)
    (hs : IsStdChar ψ) (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w)
    (hpos : ∀ v, (¬ TypAt X v → 0 < localVolumeUnit X ψ v) ∧ 0 < ZZX X u u' ψ v ∧ (∀ l, 0 < PPX X u u' ψ l v) ∧
      0 < jacX X v) :
    ProdConvNew X u u' ψ := by
  have hk : 1 ≤ D.R.k := Formalism.MainNotions.S.k_pos (D := D)
  refine prodConvNew_of X u u' ψ (VolOneAEC_holds (X := X) (u := u) (u' := u') (ψ := ψ) hψ hs) (fun v => ⟨?_, (hpos v).2.1,
    (hpos v).2.2.1, (hpos v).2.2.2⟩) (fun v h => (local_factors_pos_typical_general X hb ψ hψ hs hloc u u' v h).1)
    (fun v => lt_of_lt_of_le (Real.exp_pos _) (alX_bounds (X := X) (u := u) (u' := u') hk v).1)
    (AlConvC_holds (X := X) (u := u) (u' := u'))
  by_cases h : TypAt X v
  · exact (local_factors_pos_typical_general X hb ψ hψ hs hloc u u' v h).2
  · exact (hpos v).1 h

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PpPosTypGen
noncomputable section

open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.ProdConvCut2

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcVal
  Formalism.L2.SG.Pf.NcVal.VolOrdW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pp_pos_typ_gen {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (ψ : AddChar (AF X.B.I.F) ℂ)
    (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) (u u' : D.what₂.Word) (v : PlX X) (hv : TypAt X v)
    (l : Fin (D.R.rS + 1)) : 0 < PPX X u u' ψ l v := by
  have hTF := Formalism.L2.SG.Pf.typFacts_holds X hb u u' ⟨v, hv⟩

  have hnt : X.B.I.cm.sig ≠ AlgHom.id X.B.I.F X.B.I.E := by
    have hmax : v.asIdeal.IsMaximal := v.isMaximal
    obtain ⟨P, hPmax, -⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 X.B.I.E) v.asIdeal
      (by
        rw [(RingHom.injective_iff_ker_eq_bot _).mp
          (FaithfulSMul.algebraMap_injective (𝓞 X.B.I.F) (𝓞 X.B.I.E))]
        exact bot_le)
    obtain ⟨θ, t, htθ, hnot⟩ := X.B.I.cm.cmUnram.2.2 P hPmax
    intro h
    apply hnot
    have hθ : (t : X.B.I.E) = θ := by
      have h1 : X.B.I.cm.sig (θ : X.B.I.E) = star (θ : X.B.I.E) := rfl
      rw [h, AlgHom.id_apply] at h1
      have htθ' : (t : X.B.I.E) = star (θ : X.B.I.E) := htθ
      rw [htθ', ← h1]
    have : θ - t = 0 := by ext; simp [hθ]
    rw [this]
    exact P.zero_mem

  have hid : ∃ x : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E, x * x = x ∧ x ≠ 0 ∧ x ≠ 1 := by
    by_contra h
    have he := hTF.2.2.1
    unfold etaV at he
    rw [if_neg h] at he
    exact absurd he (by decide)
  have hS : PI.UnitaryGroupMassFormula.LocJacTyp.SplitHyp X.B.I.cm.sig v := ⟨X.B.I.cm.deg2, hnt, hid⟩
  have hg : 0 < gAt X v := hTF.1.pos
  have hA := SdW.sdFromAnn_holds ψ v (dV v) hψ X.B.I.cm.deg2 (dV_ne_zero v)
    (annX_of X ψ Formalism.L2.SG.Pf.conductor_inverse_different hψ hs v) Unit
  haveI := hA.1
  have hP := PI.UnitaryGroupMassFormula.LocJacTyp.parabolic_volume X.B.I.cm.sig v (gAt X v) D.R.rS (Tw u) (Tw u')
    (absV v (dV v) ^ Fintype.card Unit) hS hg hTF.2.2.2.1 (sdE (E := X.B.I.E) ψ v Unit) hA.1 hA.2.2 l
  have hP' : ((sdE (E := X.B.I.E) ψ v Unit) ((fun c : Unit → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E => c ()) ⁻¹'
      PPTyp X.B.I.cm.sig v (gAt X v) D.R.rS (Tw u) (Tw u') l)).toReal =
      absV v (dV v) ^ Fintype.card Unit * PI.LocJacTyp.absV v (gAt X v : Fv X.B.I.F v) ^ 3 *
        (PI.LocJacTyp.absV v (PI.LocJacTyp.alp v D.R.rS l) ^ 4)⁻¹ := hP
  unfold PPX volC
  rw [if_pos hv, hP']
  have hd : 0 < absV v (dV v) := absV_pos v (dV_ne_zero v)
  have hgv : (gAt X v : Fv X.B.I.F v) ≠ 0 := by exact_mod_cast hg.ne'
  have h1 : 0 < PI.LocJacTyp.absV v (gAt X v : Fv X.B.I.F v) := PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v hgv
  have ha : PI.LocJacTyp.alp v D.R.rS l ≠ 0 := alp_ne_zero v D.R.rS l
  have h2 : 0 < PI.LocJacTyp.absV v (PI.LocJacTyp.alp v D.R.rS l) := PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v ha
  positivity

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol

theorem level_congr_mod_sq (D : D7) (u u' : D.what₂.Word) :
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD Formalism.MainNotions.S.Lat.gS D ^ 2] := by
  have h : Formalism.MainNotions.S.Lat.gS D ^ 2 ∣ D.modT := by unfold Formalism.MainNotions.S.Lat.gS; exact D.gg_dvd_modT
  exact (D.T_modEq_of_dvd u h).trans (D.T_modEq_of_dvd u' h).symm

theorem prodConvNew_holds_gen {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ)
    (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w) (u u' : D.what₂.Word) : ProdConvNew X u u' ψ := by
  have hg : ∀ v, TypAt X v → 0 < gAt X v := fun v hv =>
    (Formalism.L2.SG.Pf.typFacts_holds X hb u u' ⟨v, hv⟩).1.pos
  have hUZ := Formalism.L2.SG.Pf.LocalPositivity.localVolumeUnit_pos_and_ZZX_pos X u u' ψ hψ hs (level_congr_mod_sq D u u') hg
  refine prodConvNew_gen X u u' ψ hb hψ hs hloc fun v => ⟨fun _ => (hUZ v).1, (hUZ v).2, fun l => ?_,
    Formalism.L2.SG.Pf.LocalPositivity.jac_pos X hg v⟩
  by_cases hv : TypAt X v
  · exact pp_pos_typ_gen X hb ψ hψ hs u u' v hv l
  · exact Formalism.L2.SG.Pf.LocalPositivity.pp_pos_ord X u u' ψ hψ hs hv l

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol

theorem prodConv_holds_gen {D : D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ)
    (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w) (u u' : D.what₂.Word) : ProdConv X u u' ψ :=
  prodConvNew_holds_gen X hb ψ hψ hs hloc u u'

theorem prodConv_holds {D : D7} (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u u' : D.what₂.Word) : ProdConv T.X u u' T.ψ :=
  prodConv_holds_gen T.X T.hb T.ψ T.ψ_char T.ψ_std T.locCompat u u'

theorem prodConvAll_holds : Formalism.L2.SG.PoincareAmplitudeLowerBounds.ProdConvAll :=
  fun _ T u u' _ _ => prodConv_holds T u u'

theorem prodConv_onTied :
    Formalism.L2.SG.NGAnalytic.MassDataLemmas.OnTied fun _ X _ _ u u' _ ψ => ProdConv X u u' ψ := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' _ hb X0 ψ hT
  exact prodConv_holds_gen X hb ψ hT.2.1 hT.2.2.1 hT.2.2.2.2.1 u u'

end Formalism.L2.SG.Pf.ProdConvCut2
