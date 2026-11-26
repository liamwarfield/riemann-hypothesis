module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfD
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Transfer
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianSumFrames
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal Classical
open Matrix

namespace Formalism.L2.SG.RealObj.EnergyCut

open Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem tens_onb (u' : D.what₂.Word) :
    Orthonormal ℂ (fun i : (∀ v, Fin (Module.finrank ℂ (X.Vloc u' v))) =>
      X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v))) ∧
    ⊤ ≤ Submodule.span ℂ (Set.range (fun i : (∀ v, Fin (Module.finrank ℂ (X.Vloc u' v))) =>
      X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v)))) := by
  set b := fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) with hb
  set e := fun i : (∀ v, Fin (Module.finrank ℂ (X.Vloc u' v))) => X.tensU u' (fun v => b v (i v)) with he
  have hon : Orthonormal ℂ e := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [he, X.tensU_inner]
    have hloc : ∀ v, ⟪b v (i v), b v (j v)⟫_ℂ = if i v = j v then 1 else 0 := fun v =>
      (orthonormal_iff_ite.1 (b v).orthonormal) (i v) (j v)
    simp only [hloc]
    by_cases hij : i = j
    · subst hij; simp
    · obtain ⟨v, hv⟩ := Function.ne_iff.1 hij
      rw [if_neg hij]
      exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)
  refine ⟨hon, ?_⟩
  have hmem : ∀ x, X.tensU u' x ∈ Submodule.span ℂ (Set.range e) := by
    intro x
    have hp : X.tensU u' x = ∑ i, ⟪e i, X.tensU u' x⟫_ℂ • e i := by
      apply Formalism.L2.SG.RealObj.RankOneTensors.eq_of_inner_tens (X.tensU u') (X.tensU_span u')
      intro z
      rw [inner_sum, show ⟪X.tensU u' z, X.tensU u' x⟫_ℂ = ∏ v, ⟪z v, x v⟫_ℂ from X.tensU_inner u' z x]
      have hterm : ∀ i, ⟪X.tensU u' z, ⟪e i, X.tensU u' x⟫_ℂ • e i⟫_ℂ =
          ∏ v, (⟪z v, b v (i v)⟫_ℂ * ⟪b v (i v), x v⟫_ℂ) := by
        intro i
        rw [inner_smul_right]
        simp only [he, X.tensU_inner]
        rw [Finset.prod_mul_distrib, mul_comm]
      simp only [hterm]
      rw [← Fintype.prod_sum (fun v j => ⟪z v, b v j⟫_ℂ * ⟪b v j, x v⟫_ℂ)]
      exact Finset.prod_congr rfl fun v _ => ((b v).sum_inner_mul_inner (z v) (x v)).symm
    rw [hp]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [← X.tensU_span u', Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact hmem x

theorem hilbert_schmidt_tensor_product_factor (u u' : D.what₂.Word) (γ : X.B.I.Ginf) :
    hs2 (OOinf X u u' γ) = ∏ v, hs2 (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
      Jv (Formalism.REAL.muG (X.B.I.ε v)) (X.Wloc u v) (X.Wloc u' v) (γ v)) := by
  obtain ⟨hon, hsp⟩ := tens_onb X u'
  let B := OrthonormalBasis.mk hon hsp
  have hB : ∀ i, B i = X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v)) := fun i => by
    simp [B]
  have hF := Formalism.L2.SG.RealObj.RankOneTensors.OOFactor_holds X u u' γ
  unfold hs2
  rw [Formalism.L2.SG.RealObj.InfCut.hsb_indep (stdOrthonormalBasis ℂ (X.Vpi u')) B]
  simp only [hB, hF, Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u) (X.tensU_inner u), ← Finset.prod_pow]
  rw [Fintype.prod_sum]

def GoodV (u u' : D.what₂.Word) : Set (Fin (D.R.rS + 1) → ℂ) :=
  {cv | (∀ l, cv l ≠ 0) ∧ 0 < Gv (Tw (D := D) u) (Tw (D := D) u') (Matrix.diagonal cv)}

def wtV (u u' : D.what₂.Word) (cv : Fin (D.R.rS + 1) → ℂ) : ℝ :=
  Gv (Tw (D := D) u) (Tw (D := D) u') (Matrix.diagonal cv) ^ (D.R.k - 1) * JacV (Matrix.diagonal cv)

def dcV : Measure (Fin (D.R.rS + 1) → ℂ) := Measure.pi fun _ => (2 : ℝ≥0∞) • (volume : Measure ℂ)

def JvX (u u' : D.what₂.Word) (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) :
    X.Vloc u' v →L[ℂ] X.Vloc u v :=
  haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
  Jv (Formalism.REAL.muG (X.B.I.ε v)) (X.Wloc u v) (X.Wloc u' v) g

theorem gv_diag_cont (u u' : D.what₂.Word) :
    Continuous (fun cv : Fin (D.R.rS + 1) → ℂ => Gv (Tw (D := D) u) (Tw (D := D) u') (Matrix.diagonal cv)) := by
  simp only [Gv, Dl, le_refl, Nat.le_succ, ↓reduceDIte]
  fun_prop

theorem goodV_meas (u u' : D.what₂.Word) : MeasurableSet (GoodV u u') := by
  have h1 : IsOpen {cv : Fin (D.R.rS + 1) → ℂ | ∀ l, cv l ≠ 0} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  have h2 : IsOpen {cv : Fin (D.R.rS + 1) → ℂ |
      0 < Gv (Tw (D := D) u) (Tw (D := D) u') (Matrix.diagonal cv)} :=
    isOpen_lt continuous_const (gv_diag_cont u u')
  exact (h1.inter h2).measurableSet

theorem good_eq_pi (u u' : D.what₂.Word) : Good X u u' = Set.pi Set.univ (fun _ => GoodV u u') := by
  ext c
  simp [Good, GoodV, Set.mem_pi]

theorem wtV_nonneg (u u' : D.what₂.Word) {cv : Fin (D.R.rS + 1) → ℂ} (h : cv ∈ GoodV u u') :
    0 ≤ wtV u u' cv := by
  unfold wtV JacV
  exact mul_nonneg (pow_nonneg h.2.le _) (Finset.prod_nonneg fun _ _ => sq_nonneg _)

theorem wtV_cont (u u' : D.what₂.Word) : Continuous (wtV u u') := by
  have hJ : Continuous (fun cv : Fin (D.R.rS + 1) → ℂ => JacV (Matrix.diagonal cv)) := by
    unfold JacV
    refine continuous_finsetProd _ fun l hl => ?_
    have h : l ≤ D.R.rS + 1 := (Finset.mem_Icc.mp hl).2.trans (Nat.le_succ _)
    simp only [modC, Dl, dif_pos h]
    fun_prop
  unfold wtV
  exact ((gv_diag_cont u u').pow _).mul hJ

end Formalism.L2.SG.RealObj.EnergyCut
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPf
noncomputable section

open NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.RealObj.InfCut

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

def StepPtRepDiag : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ (i0 : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k), PtRepExists X u u' sc i0 i0

namespace PtRepPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem hJ_crd (v : InfinitePlace X.B.I.F) (x y : (VS D).V) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd x)) (rv X.B.I v (X.crd y)) = X.B.I.φ v (X.ιE.symm ((VS D).hT x y)) := by
  rw [← Formalism.L2.SG.PoincareInHH.Cut.hform_crd (X := X) x y]
  first
  | rw [RingEquiv.symm_apply_apply]
  | simp only [RingEquiv.symm_apply_apply]
  | simp
  exact PI.ScPiFrameW.hJ_rv X.B.I v (X.crd x) (X.crd y)

def frU (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Fr (X.B.I.ε v) D.R.rS D.R.k where
  e := fun a => rv X.B.I v (X.eR a)
  fd := fun a => rv X.B.I v (X.fR a)
  z := rv X.B.I v (X.zR u)
  wb := X.wfr u v
  T := Tw u
  T_pos := by unfold Tw; exact_mod_cast (D.mem u).A.T_prime.pos
  card := by have h1 := X.n_eq; have h2 := Formalism.MainNotions.S.dimS_eq D.R; omega
  ee := fun a b => by
    show hJ _ (rv X.B.I v (X.crd (X.eX a))) (rv X.B.I v (X.crd (X.eX b))) = 0
    rw [hJ_crd, X.ee, map_zero, map_zero]
  ff := fun a b => by
    show hJ _ (rv X.B.I v (X.crd (X.fY a))) (rv X.B.I v (X.crd (X.fY b))) = 0
    rw [hJ_crd, X.ff, map_zero, map_zero]
  ef := fun a b => by
    show hJ _ (rv X.B.I v (X.crd (X.eX a))) (rv X.B.I v (X.crd (X.fY b))) = _
    rw [hJ_crd, X.ef]
    split_ifs <;> simp
  ez := fun a => by
    show hJ _ (rv X.B.I v (X.crd (X.eX a))) (rv X.B.I v (X.crd (X.zu u))) = 0
    rw [hJ_crd, (X.zu_orth u a).1, map_zero, map_zero]
  fz := fun a => by
    show hJ _ (rv X.B.I v (X.crd (X.fY a))) (rv X.B.I v (X.crd (X.zu u))) = 0
    rw [hJ_crd, (X.zu_orth u a).2, map_zero, map_zero]
  zz := by
    show hJ _ (rv X.B.I v (X.crd (X.zu u))) (rv X.B.I v (X.crd (X.zu u))) = _
    rw [hJ_crd, X.zu_norm, map_neg, map_neg, map_natCast, map_natCast]
    simp [Tw]
  ww := X.wfr_on u v
  ew := fun a i => ((X.wfr_perp u v i).1 a).1
  fw := fun a i => ((X.wfr_perp u v i).1 a).2
  zw := fun i => (X.wfr_perp u v i).2

theorem zhatO_zhatO {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : ZhatO (ZhatO Z) = Z := by
  ext a b
  simp only [Formalism.L2.SG.RealObj.ZhatO, ← mul_assoc, ← mul_pow]
  norm_num

theorem famSc_one {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : famSc 1 e z = fam e z := by
  funext a
  simp only [Formalism.L2.SG.RealObj.famSc, Complex.ofReal_one, one_pow, inv_one, one_smul]

end PtRepPf


open PtRepPf in
theorem real_point_representative_diagonal : StepPtRepDiag := by
  intro D X u u' sc hsc i0 w hw
  have hloc := fun v => locMain (frU X u v) (frU X u' v) rfl (i0 v) (ZhatO (ptC X v w)) (hw v) sc hsc
  choose g hgZ φ hφ hD using hloc
  have hω : ∀ v, hJ (X.B.I.ε v) (X.wfr u' v (i0 v)) (X.wfr u' v (i0 v)) = 1 := fun v => by
    rw [X.wfr_on, if_pos rfl]
  refine ⟨g, fun v => ?_, 1, fun v => rotU (X.B.I.ε v) (X.wfr u' v (i0 v)) (hω v) (φ v) (hφ v), ?_, ?_, ?_⟩
  · show ZhatO (Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat (g v))) = ptC X v w
    simp only [frm, famSc_one]
    rw [show Zhat (X.B.I.ε v) (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)))
        (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (uMat (g v)) = ZhatO (ptC X v w) from hgZ v,
      zhatO_zhatO]
  · intro v x _
    show uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) *ᵥ rv X.B.I v x = rv X.B.I v x
    simp [uMat]
  · intro v x hx
    rw [rotU_mulVec]
    have h0 : hJ (X.B.I.ε v) (X.wfr u' v (i0 v)) (rv X.B.I v x) = 0 := by
      rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hx
      · exact (frU X u' v).we (i0 v) a
      · exact (frU X u' v).wf (i0 v) a
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact (frU X u' v).wz (i0 v)
    rw [h0, mul_zero, zero_smul, add_zero]
  · intro v
    have hm1 : Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u v) v 1 = 1 := by
      ext a b
      show hJ (X.B.I.ε v) (X.wfr u v a) (uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) *ᵥ X.wfr u v b) = _
      simp [uMat, X.wfr_on, Matrix.one_apply]
    have hm2 : Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u' v) v
        (fun v => rotU (X.B.I.ε v) (X.wfr u' v (i0 v)) (hω v) (φ v) (hφ v)) =
        Matrix.diagonal fun i => if i = i0 v then φ v else 1 := by
      ext a b
      show hJ (X.B.I.ε v) (X.wfr u' v a)
        (uMat (rotU (X.B.I.ε v) (X.wfr u' v (i0 v)) (hω v) (φ v) (hφ v)) *ᵥ X.wfr u' v b) = _
      rw [rotU_mulVec, hJ_add_right, hJ_smul_right, X.wfr_on, X.wfr_on, X.wfr_on, diagonal_apply]
      by_cases hab : a = b
      · subst hab
        by_cases ha : a = i0 v
        · subst ha; simp
        · simp [ha, Ne.symm ha]
      · by_cases hb : b = i0 v
        · subst hb; simp [hab]
        · simp [hab, hb, Ne.symm hb]
    rw [hm1, hm2]
    exact hD v

theorem real_point_representative_exists : StepPtRep := real_point_representative_diagonal

end Formalism.L2.SG.RealObj.InfCut
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepRealHolds
namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

theorem StepReal_holds : StepReal :=
  stepReal_of_witt (fun _ _ ε x y hG hnd => Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.witt_of_gram ε x y hG hnd)

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DetUpMatSub
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LintegralMulRightOfMap
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

namespace JL

def RightInvS : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' : ℝ),
    FrameLoc ε k e z z' T T' →
    ∀ μ : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μ →
    ∀ s ∈ SLoc ε e z, μ.map (fun x => x * s) = μ

theorem frameLoc_swap {n r k : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ} {T T' : ℝ}
    (hF : FrameLoc ε k e z z' T T') : FrameLoc ε k e z' z T' T :=
  ⟨hF.dim, hF.k_pos, hF.sig, hF.e_li, hF.ee, hF.ez', hF.ez, hF.zz', hF.zz, hF.T'_pos, hF.T_pos⟩

theorem lintegral_mul_right_of_map {n : ℕ} {ε : Fin n → Bool} (μ : Measure (Formalism.REAL.UJ ε))
    (t : Formalism.REAL.UJ ε) (hμ : μ.map (fun x => x * t) = μ) (F : Formalism.REAL.UJ ε → ℝ≥0∞) :
    ∫⁻ x, F (x * t) ∂μ = ∫⁻ x, F x ∂μ := by
  have hE : MeasurableEmbedding (fun x : Formalism.REAL.UJ ε => x * t) :=
    (MeasurableEquiv.mulRight t).measurableEmbedding
  calc ∫⁻ x, F (x * t) ∂μ = ∫⁻ x, F x ∂(μ.map (fun x => x * t)) := (hE.lintegral_map F).symm
    _ = ∫⁻ x, F x ∂μ := by rw [hμ]

theorem inner_dc {n : ℕ} {ε : Fin n → Bool} (μS μS' : Measure (Formalism.REAL.UJ ε))
    (s₁ s₁' g : Formalism.REAL.UJ ε) (h₁ : μS.map (fun x => x * s₁) = μS)
    (h₁' : μS'.map (fun x => x * s₁') = μS') (φ : Formalism.REAL.UJ ε → ℝ≥0∞) :
    ∫⁻ s, ∫⁻ s', φ (s * (s₁ * g * s₁'⁻¹) * s'⁻¹) ∂μS' ∂μS = ∫⁻ s, ∫⁻ s', φ (s * g * s'⁻¹) ∂μS' ∂μS := by
  have key : ∀ s s' : Formalism.REAL.UJ ε,
      φ (s * (s₁ * g * s₁'⁻¹) * s'⁻¹) = φ ((s * s₁) * g * (s' * s₁')⁻¹) := by
    intro s s'
    congr 1
    group
  have inner : ∀ x : Formalism.REAL.UJ ε,
      ∫⁻ s', φ (x * g * (s' * s₁')⁻¹) ∂μS' = ∫⁻ s', φ (x * g * s'⁻¹) ∂μS' := fun x =>
    lintegral_mul_right_of_map μS' s₁' h₁' (fun y => φ (x * g * y⁻¹))
  simp_rw [key, inner]
  exact lintegral_mul_right_of_map μS s₁ h₁ (fun x => ∫⁻ s', φ (x * g * s'⁻¹) ∂μS')

theorem measurableSet_goodLoc (r : ℕ) (T T' : ℝ) : MeasurableSet (GoodLoc (r := r) T T') := by
  have hD : ∀ l, Continuous fun c : Fin (r + 1) → ℂ => Dl (Matrix.diagonal c) l := by
    intro l
    by_cases h : l ≤ r + 1
    · simp only [Dl, dif_pos h]
      exact (continuous_id.matrix_diagonal.matrix_submatrix _ _).matrix_det
    · simp only [Dl, dif_neg h]
      exact continuous_const
  have hG : Continuous fun c : Fin (r + 1) → ℂ => Gv T T' (Matrix.diagonal c) := by
    simp only [Gv]
    exact ((hD (r + 1)).norm.pow 2).sub (continuous_const.mul ((hD r).norm.pow 2))
  have h0 : MeasurableSet {c : Fin (r + 1) → ℂ | ∀ l, c l ≠ 0} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun l => (measurable_pi_apply l) (measurableSet_singleton 0).compl
  unfold GoodLoc
  rw [Set.ofPred_and]
  exact h0.inter (measurableSet_lt measurable_const hG.measurable)

end JL

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

theorem hJ_adj {n : ℕ} {ε : Fin n → Bool} (s : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    hJ ε x (uMat s *ᵥ y) = hJ ε (uMat s⁻¹ *ᵥ x) y := by
  have hU : (uMat s)ᴴ * Formalism.REAL.Jm ε * uMat s = Formalism.REAL.Jm ε := s.2
  have hinv : uMat s * uMat s⁻¹ = 1 := by
    simp [Formalism.MainNotions.S.uMat]
  have hJc : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    rw [Pi.star_apply]
    split_ifs <;> simp
  have h1 : (uMat s)ᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat s⁻¹ := by
    calc (uMat s)ᴴ * Formalism.REAL.Jm ε = (uMat s)ᴴ * Formalism.REAL.Jm ε * (uMat s * uMat s⁻¹) := by
          rw [hinv, Matrix.mul_one]
      _ = Formalism.REAL.Jm ε * uMat s⁻¹ := by rw [← Matrix.mul_assoc, hU]
  have key : (uMat s⁻¹)ᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat s := by
    have h2 := congrArg Matrix.conjTranspose h1
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJc] at h2
    exact h2.symm
  simp only [Formalism.L2.SG.HidaSetting.hJ, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, key]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealHermitianForms
noncomputable section

open Matrix Finset
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.RealHermitianForms

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.MainNotions.S

section Form

variable {n : ℕ} (ε : Fin n → Bool)

theorem hJ_uj (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) : hJ ε (uMat g *ᵥ x) (uMat g *ᵥ y) = hJ ε x y := by
  have hg : Formalism.REAL.inUJ ε (uMat g) := g.2
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  unfold Formalism.REAL.inUJ at hg
  rw [hg]

theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  simp [uMat]

theorem uMat_mul (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem hJ_inv_r (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    hJ ε x (uMat g⁻¹ *ᵥ y) = hJ ε (uMat g *ᵥ x) y := by
  rw [← hJ_uj ε g x (uMat g⁻¹ *ᵥ y), mulVec_mulVec, uMat_mul_inv, one_mulVec]

end Form

section Eich

variable {n : ℕ} (ε : Fin n → Bool)

end Eich

section Frame

variable {n r : ℕ} (ε : Fin n → Bool)

end Frame

end Formalism.L2.SG.RealObj.InfCut.RealHermitianForms
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHLie
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

theorem exp_mulVec_of_zero {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) (h : A *ᵥ v = 0) :
    NormedSpace.exp A *ᵥ v = v := by
  letI : SeminormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hpow : ∀ n : ℕ, A ^ (n + 1) *ᵥ v = 0 := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  let L0 : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] (Fin d → ℂ) :=
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => Matrix.add_mulVec M N v
      map_smul' := fun c M => by ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] }
  let L : Matrix (Fin d) (Fin d) ℂ →L[ℂ] (Fin d → ℂ) := LinearMap.toContinuousLinearMap L0
  have hL : ∀ M, L M = M *ᵥ v := fun M => rfl
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ), ← hL, L.map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℂ) A)]
  rw [tsum_eq_single 0]
  · simp [hL]
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [hL, Matrix.smul_mulVec, hpow m, smul_zero]

theorem adjH_def {k r : ℕ} (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Formalism.MainNotions.BridgeCSB.adjH X = Hpk k r * Xᴴ * Hpk k r := rfl

theorem exp_mem_UH {k r : ℕ} {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hX : Hpk k r * Xᴴ * Hpk k r + X = 0) (t : ℝ) : NormedSpace.exp ((t : ℂ) • X) ∈ UH (Hpk k r) := by
  rw [Formalism.MainNotions.BridgeCSB.mem_UH_iff, Formalism.MainNotions.BridgeCSB.adjH_exp_gen, Formalism.MainNotions.BridgeCSB.adjH_smul]
  have ha : Formalism.MainNotions.BridgeCSB.adjH X = -X := eq_neg_of_add_eq_zero_left hX
  rw [ha, Complex.star_def, Complex.conj_ofReal, smul_neg, ← Matrix.exp_add_of_commute]
  · rw [neg_add_cancel, NormedSpace.exp_zero]
  · exact (Commute.refl _).neg_left

theorem adj_of_lie {k r : ℕ} {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UH (Hpk k r)) : Hpk k r * Xᴴ * Hpk k r + X = 0 := by
  have hadj : Formalism.MainNotions.BridgeCSB.adjH X = -X := by
    apply Formalism.MainNotions.BridgeCSB.exp_smul_inj
    intro t
    have hU := hX t
    have h1 : Formalism.MainNotions.BridgeCSB.adjH (NormedSpace.exp ((t : ℂ) • X)) = (NormedSpace.exp ((t : ℂ) • X))⁻¹ :=
      (Matrix.inv_eq_left_inv ((Formalism.MainNotions.BridgeCSB.mem_UH_iff _).1 hU)).symm
    rw [Formalism.MainNotions.BridgeCSB.adjH_exp_gen, Formalism.MainNotions.BridgeCSB.adjH_smul, Complex.star_def, Complex.conj_ofReal,
      ← Matrix.exp_neg] at h1
    rw [h1, smul_neg]
  rw [← adjH_def, hadj, neg_add_cancel]

theorem lieG : LieG := by
  intro k r
  ext X
  constructor
  · intro hX
    exact adj_of_lie hX
  · intro hX t
    exact exp_mem_UH hX t

theorem col_zero {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (j : Fin d)
    (h : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) *ᵥ bvec j = bvec j) : X *ᵥ bvec j = 0 := by
  funext i
  have hij : X i j = 0 := by
    refine Formalism.MainNotions.BridgeCSB.entry_zero_of_const' X i j (bvec j i) fun t => ?_
    have := congrFun (h t) i
    rw [← this, Matrix.mulVec, dotProduct]
    simp [bvec, Pi.single_apply]
  rw [Matrix.mulVec, dotProduct]
  simp [bvec, Pi.single_apply, hij]

theorem lieWb : LieWb := by
  intro k r
  ext X
  constructor
  · intro hX
    refine ⟨adj_of_lie fun t => (hX t).1, fun a => ⟨?_, ?_⟩⟩
    · exact col_zero _ fun t => ((hX t).2 a).1
    · exact col_zero _ fun t => ((hX t).2 a).2
  · rintro ⟨hX, hk⟩ t
    refine ⟨exp_mem_UH hX t, fun a => ⟨?_, ?_⟩⟩
    · exact exp_mulVec_of_zero _ _ (by rw [Matrix.smul_mulVec, (hk a).1, smul_zero])
    · exact exp_mulVec_of_zero _ _ (by rw [Matrix.smul_mulVec, (hk a).2, smul_zero])

end Formalism.L2.SG.Pf.BH
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyIntTor
noncomputable section

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice

namespace Formalism.L2.SG.RealObj.EnergyIntTor

variable {k r : ℕ}

theorem tE_eq_one_of_mem_middle_block (μ : ℂ) (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) : tE μ k r i = 1 := by
  unfold Formalism.L2.SG.Pf.Choice.tE
  rw [if_neg (by omega), if_neg (by omega)]

theorem torS_apply (μ : ℂ) (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    (torS μ k r * m * torS μ⁻¹ k r) i j = tE μ k r i * m i j * tE μ⁻¹ k r j := by
  have e1 : torS μ k r = Matrix.diagonal (tE μ k r) := rfl
  have e2 : torS μ⁻¹ k r = Matrix.diagonal (tE μ⁻¹ k r) := rfl
  rw [e1, e2, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem tor_comm (μ : ℂ) {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : torS μ k r * h = h * torS μ k r := by
  have hb := WeylGroupFacts.uw_block hh
  ext i j
  rw [torS_eq, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hb.2 i j hi]
    by_cases hij : i = j
    · subst hij; simp [mul_comm]
    · simp [hij]
  · by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hb.1 i j hj]
      by_cases hij : i = j
      · subst hij; simp [mul_comm]
      · simp [hij]
    · rw [tE_eq_one_of_mem_middle_block μ i (by omega) (by omega), tE_eq_one_of_mem_middle_block μ j (by omega) (by omega), one_mul, mul_one]

theorem tor_conj_uw {μ : ℂ} (hμ : μ ≠ 0) {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    torS μ k r * h * torS μ⁻¹ k r = h := by
  rw [tor_comm μ hh, Matrix.mul_assoc, torS_mul_inv μ hμ, Matrix.mul_one]

theorem tor_mulVec_wb (μ : ℂ) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : torS μ k r *ᵥ z = z := by
  funext i
  rw [show torS μ k r = Matrix.diagonal (tE μ k r) from rfl, Matrix.mulVec_diagonal]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [hz i h, mul_zero]
  · push_neg at h
    rw [tE_eq_one_of_mem_middle_block μ i h.1 h.2, one_mul]

theorem ell_tor {μ : ℂ} (hμ : μ ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ell k r z (torS μ k r * m * torS μ⁻¹ k r) = μ * ell k r z m := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with ha
  · rw [torS_apply, tE_eI, show eI k r ⟨a.val + 1, ha⟩ = eI k r ⟨a.val + 1, ha⟩ from rfl, tE_eI]
    simp only []
    have e : r - (a : ℕ) = (r - ((a : ℕ) + 1)) + 1 := by omega
    rw [e, pow_succ, inv_pow]
    field_simp
  · have hv : (torS μ k r * m * torS μ⁻¹ k r) *ᵥ z = torS μ k r *ᵥ (m *ᵥ z) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tor_mulVec_wb μ⁻¹ hz]
    rw [hv, torS_eq, Matrix.mulVec_diagonal, tE_eI]
    have e : r - (a : ℕ) = 1 := by have := a.isLt; omega
    rw [e, pow_one]

theorem psi_tor {μ : ℂ} (hμ : μ ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    psi k r z c (torS μ k r * m * torS μ⁻¹ k r) = psi k r z (c * μ) m := by
  unfold Formalism.QuantumDeterminants.psi
  rw [ell_tor hμ hz m, ← mul_assoc]

theorem tor_mem_UH {μ : ℂ} (hμ : μ ≠ 0) : torS μ k r ∈ UH (Hpk k r) := torS_gram μ hμ

theorem UH_mul {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ UH (Hpk k r))
    (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul, show bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b by
    simp only [Matrix.mul_assoc], ha', hb']

theorem tor_conj_N {μ : ℂ} (hμ : μ ≠ 0) {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Nset k r) : torS μ k r * a * torS μ⁻¹ k r ∈ Nset k r := by
  obtain ⟨hU, hc1, hc2⟩ := ha
  refine ⟨UH_mul (UH_mul (tor_mem_UH hμ) hU) (tor_mem_UH (inv_ne_zero hμ)), fun b i hbi => ?_, fun i j h1 h2 h3 => ?_⟩
  · rw [torS_apply, hc1 b i hbi]
    split_ifs with h
    · subst h; rw [mul_one, tE_mul_inv μ hμ]
    · simp
  · rw [torS_apply, hc2 i j h1 h2 h3]
    split_ifs with h
    · subst h; rw [mul_one, tE_mul_inv μ hμ]
    · simp

end Formalism.L2.SG.RealObj.EnergyIntTor
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNMul
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.ChiNMul

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem gB_ne_zero : X.B.g ≠ 0 := by
  rw [X.g_eq]; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero

theorem hfe : ∀ a b : Fin D.R.rS, a ≠ b → ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) (X.e0 b)) := by
  intro a b hab
  rw [hA_symm]
  have := (X.gramIntegral b a).2.2
  rw [if_neg (Ne.symm hab), sub_zero] at this
  exact Z_sig X.B.I X.B.g this

theorem hfz : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) X.z0) := fun a => ((X.formsAtZero).2 a).2

theorem e_step' {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset)
    (hc1 : ∀ a : Fin D.R.rS, (X.B.I.fmat x - 1) *ᵥ X.e0 a ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1}))
    (a : Fin D.R.rS) : ∀ v ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1 + 1}),
      (X.B.I.fmat x - 1) *ᵥ v ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1}) :=
  pres1 X.B.I hx X.B.g _ _ (by
    rintro _ ⟨b, hb, rfl⟩
    have hb' : b.1 < a.1 + 1 := hb
    exact Mo_mono X.B.I (Set.image_mono (lt_sub (by omega))) (hc1 b)) (mL_Mo X.B.I)

theorem nxt_cong' {y : X.B.I.Gf} (hcy : Formalism.L2.SG.NormCut.NCong X y) (a : Fin D.R.rS) :
    (X.B.I.fmat y - 1) *ᵥ nxt X.e0 X.z0 a ∈ Mo X.B.I X.B.g (X.e0 '' {b | b.1 < a.1 + 1}) := by
  unfold nxt
  split_ifs with h
  · exact hcy.1 ⟨a.1 + 1, h⟩
  · refine Mo_mono X.B.I ?_ hcy.2
    rintro _ ⟨b, rfl⟩
    have := b.2
    exact ⟨b, show b.1 < a.1 + 1 by omega, rfl⟩

theorem chiN_mul {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hcx : Formalism.L2.SG.NormCut.NCong X x)
    (hcy : Formalism.L2.SG.NormCut.NCong X y) : chiN X (x * y) = chiN X x * chiN X y := by
  unfold chiN
  refine psi_mul_of_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (gB_ne_zero X) ?_
  have hf0 : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Z_sum X.B.I X.B.g _ _ fun a _ => ?_
  exact term_Z X.B.I X.B.g _ _ (nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 (hfe X) (hfz X) a)
    (Me_Q X.B.I X.B.g X.e0 X.f0 hf0 (hfe X) a (e_step' X hx hcx.1 a _ (nxt_cong' X hcy a)))

theorem chiN_one : chiN X 1 = 1 := by
  unfold chiN
  refine psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (gB_ne_zero X) ?_
  simp only [show X.B.I.fmat 1 = 1 from rfl, Matrix.one_mulVec]
  exact Z_sum X.B.I X.B.g _ _ fun a _ => nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 (hfe X) (hfz X) a

end Formalism.L2.SG.Pf.ChiNMul

namespace Formalism.L2.SG.NormCut

section ChiNOut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

theorem chiN_colDiff (w : D.what₂.Word) (h h' : Hfin X w)
    (hk : ((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset) :
    chiN X (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) = 1 := by
  have s := colStab X w h h' hk
  unfold chiN
  refine psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int (Formalism.L2.SG.Pf.ChiNMul.gB_ne_zero X) ?_
  refine Z_sum X.B.I X.B.g _ _ fun a _ => ?_
  have hf0 : X.f0 a ∈ X.B.I.Lf := (X.vectorsInLattice.1 a).2
  have hd : X.B.I.fmat (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) *ᵥ nxt X.e0 X.z0 a -
      nxt X.e0 X.z0 a ∈ mL X.B.I X.B.g := by
    unfold nxt; split_ifs
    · exact s.1 _
    · exact s.2
  rw [show X.B.I.fmat (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) *ᵥ nxt X.e0 X.z0 a =
    nxt X.e0 X.z0 a + (X.B.I.fmat (((h : X.B.I.Gf) * X.xu w)⁻¹ * ((h' : X.B.I.Gf) * X.xu w)) *ᵥ nxt X.e0 X.z0 a -
      nxt X.e0 X.z0 a) by abel, hA_add_right]
  exact Z_add X.B.I X.B.g (nxt_Z X.B.I X.B.g X.e0 X.f0 X.z0 (Formalism.L2.SG.Pf.ChiNMul.hfe X)
    (Formalism.L2.SG.Pf.ChiNMul.hfz X) a) (mL_Qs X.B.I X.B.g hf0 hd)

theorem chiNIndep_of_frameTie (hTF : FrameTie X u u' F0 F0') : ChiNIndep F0 F0' cs cs' := by
  intro t ρ ρ' hρ hρ' _
  have hb : cs.lamOf (cs.base t.lam) = t.lam := cs.base_lam _ t.mem
  have hb' : cs'.lamOf (cs'.base t.lam') = t.lam' := cs'.base_lam _ t.mem'
  have k1K := Formalism.L2.SG.Pf.colLatK X cs ρ (cs.base t.lam) (hρ.trans hb.symm)
  have k2K := Formalism.L2.SG.Pf.colLatK X cs' (cs'.base t.lam') ρ' (hb'.trans hρ'.symm)
  have κK := Formalism.L2.SG.Pf.termK X cs cs' (F0 := F0) (F0' := F0') t
  have κN := adm_norm_of_fixed_frames cs cs' hTF (Formalism.L2.SG.Pf.termK X cs cs') (Formalism.L2.SG.Pf.modGAt X) t
  have k1N := ncong_colDiff u _ _ k1K
  have k2N := ncong_colDiff u' _ _ k2K
  have hκ : kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt =
      (((cs.h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ((cs.h (cs.base t.lam) : X.B.I.Gf) * X.xu u)) *
        kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt *
        (((cs'.h (cs'.base t.lam') : X.B.I.Gf) * X.xu u')⁻¹ * ((cs'.h ρ' : X.B.I.Gf) * X.xu u')) := by
    unfold kOf; group
  rw [hκ, Formalism.L2.SG.Pf.ChiNMul.chiN_mul X (K_mul X.B.I k1K κK) (ncong_mul X k1K k1N κN) k2N,
    Formalism.L2.SG.Pf.ChiNMul.chiN_mul X k1K k1N κN, chiN_colDiff u _ _ k1K, chiN_colDiff u' _ _ k2K, one_mul,
    mul_one]

end ChiNOut

end Formalism.L2.SG.NormCut
end
end
