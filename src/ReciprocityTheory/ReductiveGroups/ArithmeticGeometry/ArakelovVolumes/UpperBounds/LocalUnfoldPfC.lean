module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldPfB
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldPfA
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')

def Φ (z : V (nd X)) : V (nd X) := D.zOf (cpt X (rmul x1' b1) z)

def β (z : V (nd X)) : Frame X.Ψ r := D.bOf (cpt X (rmul x1' b1) z)

theorem cell_zero (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) :
    cpt X (rmul x1' b1) 0 ∈ ExtFPf.cell D := by
  have h0 : cpt X (rmul x1' b1) 0 = rmul x1' b1 := by
    funext τ
    show (mat (rmul x1' b1) τ * mat (nmat X 0) τ : Matrix (Fin r) (Fin r) ℂ) = rmul x1' b1 τ
    rw [IW.nmat_zero, Matrix.mul_one]
    rfl
  have hx0 : cpt X x1' 0 = x1' := by
    funext τ
    show (mat x1' τ * mat (nmat X 0) τ : Matrix (Fin r) (Fin r) ℂ) = x1' τ
    rw [IW.nmat_zero, Matrix.mul_one]
    rfl
  have hdom : x1' ∈ X.dom := IW.orth_mem_dom X x1' ho'
  have hO : (0 : V (nd X)) ∈ OmF X x1' := by
    show cpt X x1' 0 ∈ X.dom
    rw [hx0]
    exact hdom
  have hu := (D.uniq 0 hO b1 hb1).1
  rw [hx0] at hu
  rw [h0]
  exact ⟨OntoS.dom_rmul X hdom hb1, hu⟩

theorem exists_ball (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) :
    ∃ ρ1 : ℝ, 0 < ρ1 ∧ ∀ z ∈ Metric.ball (0 : V (nd X)) ρ1, cpt X (rmul x1' b1) z ∈ ExtFPf.cell D := by
  have hopen : IsOpen {z : V (nd X) | cpt X (rmul x1' b1) z ∈ ExtFPf.cell D} := by
    have h1 := ExF.isOpen_OmF (X := X) (rmul x1' b1)
    have h2 : IsOpen {z : V (nd X) | D.Δ (cpt X (rmul x1' b1) z) ≠ 0} :=
      isOpen_ne_fun (D.hΔ.continuous.comp (MI.continuous_cpt (X := X) _)) continuous_const
    exact h1.inter h2
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen 0 (cell_zero X b1 D ho' hb1)
  exact ⟨ρ, hρ, fun z hz => hball hz⟩

theorem split {z : V (nd X)} (hz : cpt X (rmul x1' b1) z ∈ ExtFPf.cell D) :
    Φ X b1 D z ∈ OmF X x1' ∧ β X b1 D z ∈ Bor X.Ψ r ∧
      cpt X (rmul x1' b1) z = rmul (cpt X x1' (Φ X b1 D z)) (β X b1 D z) :=
  D.split _ hz.1 hz.2

private theorem eq_of_unipotent_lower_mul_eq_upper {n : ℕ} (A C B1 B2 N1 N2 : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A.det)
    (hB1 : IsUnit B1.det) (hB2 : IsUnit B2.det) (hB1t : B1.BlockTriangular id) (hB2t : B2.BlockTriangular id)
    (hN1t : N1.BlockTriangular OrderDual.toDual) (hN2t : N2.BlockTriangular OrderDual.toDual)
    (hd1 : ∀ a, N1 a a = 1) (hd2 : ∀ a, N2 a a = 1) (h1 : A * N1 = C * B1) (h2 : A * N2 = C * B2) :
    N1 = N2 := by
  have hN2u : IsUnit N2.det := by
    rw [Matrix.det_of_lowerTriangular N2 hN2t]
    simp [hd2]
  have h3 : N1 * B1⁻¹ = N2 * B2⁻¹ := by
    have e : A * (N1 * B1⁻¹) = A * (N2 * B2⁻¹) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, h2, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB1,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB2]
    have e' := congrArg (fun M => A⁻¹ * M) e
    rwa [Matrix.nonsing_inv_mul_cancel_left _ _ hA, Matrix.nonsing_inv_mul_cancel_left _ _ hA] at e'
  have hk : N2⁻¹ * N1 = B2⁻¹ * B1 := by
    have e3 : N1 = N1 * B1⁻¹ * B1 := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB1, Matrix.mul_one]
    rw [e3, h3, Matrix.mul_assoc N2, ← Matrix.mul_assoc N2⁻¹, Matrix.nonsing_inv_mul _ hN2u, Matrix.one_mul]
  have hPlow : (N2⁻¹ * N1).BlockTriangular OrderDual.toDual := by
    haveI := Matrix.invertibleOfIsUnitDet N2 hN2u
    exact (Matrix.blockTriangular_inv_of_blockTriangular hN2t).mul hN1t
  have hPup : (N2⁻¹ * N1).BlockTriangular id := by
    haveI := Matrix.invertibleOfIsUnitDet B2 hB2
    rw [hk]
    exact (Matrix.blockTriangular_inv_of_blockTriangular hB2t).mul hB1t
  have hoff : ∀ a c, a ≠ c → (N2⁻¹ * N1) a c = 0 := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h | h
    · exact hPlow (show OrderDual.toDual c < OrderDual.toDual a from h)
    · exact hPup h
  have hN1 : N1 = N2 * (N2⁻¹ * N1) := (Matrix.mul_nonsing_inv_cancel_left N2 N1 hN2u).symm
  have hsum : ∀ a c, (N2 * (N2⁻¹ * N1)) a c = N2 a c * (N2⁻¹ * N1) c c := by
    intro a c
    rw [Matrix.mul_apply, Finset.sum_eq_single c (fun k _ hk => by rw [hoff k c hk, mul_zero]) (by simp)]
  have hPd : ∀ c, (N2⁻¹ * N1) c c = 1 := by
    intro c
    have e := congrFun (congrFun hN1 c) c
    rw [hsum, hd1, hd2, one_mul] at e
    exact e.symm
  ext a c
  have e := congrFun (congrFun hN1 a) c
  rw [hsum, hPd, mul_one] at e
  exact e

theorem Φ_injOn (hx1 : rmul x1' b1 ∈ X.dom) :
    Set.InjOn (Φ X b1 D) {z | cpt X (rmul x1' b1) z ∈ ExtFPf.cell D} := by
  intro z1 hz1 z2 hz2 hΦ
  obtain ⟨-, hB1, e1⟩ := split X b1 D hz1
  obtain ⟨-, hB2, e2⟩ := split X b1 D hz2
  rw [hΦ] at e1
  have hlow : ∀ (z : V (nd X)) (τ : X.Ψ), (mat (nmat X z) τ).BlockTriangular OrderDual.toDual := by
    intro z τ a c hac
    have hac' : a < c := hac
    simp [mat, nmat, not_lt.2 hac'.le, hac'.ne]
  have hdiag : ∀ (z : V (nd X)) (τ : X.Ψ) (a : Fin r), mat (nmat X z) τ a a = 1 := by
    intro z τ a
    simp [mat, nmat]
  have hup : ∀ b ∈ Bor X.Ψ r, ∀ τ : X.Ψ, (mat b τ).BlockTriangular id := by
    intro b hb τ a c hac
    exact (hb τ).2 a c hac
  have hN : ∀ τ, mat (nmat X z1) τ = mat (nmat X z2) τ := by
    intro τ
    exact eq_of_unipotent_lower_mul_eq_upper (mat (rmul x1' b1) τ) (mat (cpt X x1' (Φ X b1 D z2)) τ) (mat (β X b1 D z1) τ)
      (mat (β X b1 D z2) τ) _ _ (isUnit_iff_ne_zero.2 (hx1 τ).1) (isUnit_iff_ne_zero.2 (hB1 τ).1)
      (isUnit_iff_ne_zero.2 (hB2 τ).1) (hup _ hB1 τ) (hup _ hB2 τ) (hlow z1 τ) (hlow z2 τ)
      (hdiag z1 τ) (hdiag z2 τ) (congrFun e1 τ) (congrFun e2 τ)
  ext i
  obtain ⟨⟨τ, ⟨⟨a, c⟩, hac⟩⟩, rfl⟩ : ∃ e : Ent X, Fintype.equivFin (Ent X) e = i :=
    ⟨(Fintype.equivFin (Ent X)).symm i, (Fintype.equivFin (Ent X)).apply_symm_apply i⟩
  have e := congrFun (congrFun (hN τ) a) c
  simpa [mat, nmat, hac] using e

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')

theorem cpt_diff (x : Frame X.Ψ r) : Differentiable ℂ (cpt X x) := by
  exact (OntoB.cd_cpt X x).differentiable (by simp)

def Uc : Set (V (nd X)) := (cpt X (rmul x1' b1)) ⁻¹' ExtFPf.cell D

theorem isOpen_Uc : IsOpen (Uc X b1 D) := by
  have hcell : IsOpen (ExtFPf.cell D) :=
    (FourierCoefficientDomain.isOpen_dom (X := X)).inter (D.hΔ.continuous.isOpen_preimage _ isOpen_compl_singleton)
  exact (cpt_diff X _).continuous.isOpen_preimage _ hcell

theorem Φ_diffOn : DifferentiableOn ℂ (Φ X b1 D) (Uc X b1 D) := by
  exact D.hz.comp (cpt_diff X _).differentiableOn fun z hz => hz

theorem Φ_cdOn : ContDiffOn ℂ ∞ (Φ X b1 D) (Uc X b1 D) := by
  refine contDiffOn_piLp' 2 fun i => ?_
  have hi : DifferentiableOn ℂ (fun x => (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin (nd X)) i) (Φ X b1 D x))
      (Uc X b1 D) :=
    (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin (nd X)) i).differentiable.comp_differentiableOn (Φ_diffOn X b1 D)
  exact ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn (nd X) _ _ (isOpen_Uc X b1 D) hi

theorem jac_bound {ρ0 : ℝ} (hsub : Metric.closedBall (0 : V (nd X)) ρ0 ⊆ Uc X b1 D) :
    ∃ Kj : ℝ, ∀ z ∈ Metric.closedBall (0 : V (nd X)) ρ0, |(fderiv ℝ (Φ X b1 D) z).det| ≤ Kj := by
  have hcd : ContDiffOn ℝ ∞ (Φ X b1 D) (Uc X b1 D) := (Φ_cdOn X b1 D).restrict_scalars ℝ
  have hfd : ContinuousOn (fun z => fderiv ℝ (Φ X b1 D) z) (Uc X b1 D) :=
    hcd.continuousOn_fderiv_of_isOpen (isOpen_Uc X b1 D) (by simp)
  have hdet : ContinuousOn (fun z => (fderiv ℝ (Φ X b1 D) z).det) (Uc X b1 D) :=
    ContinuousLinearMap.continuous_det.comp_continuousOn hfd
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : V (nd X)) ρ0).exists_bound_of_continuousOn (hdet.mono hsub)
  exact ⟨C, fun z hz => by simpa [Real.norm_eq_abs] using hC z hz⟩

theorem dens_bound {ρ0 : ℝ} (hsub : Metric.closedBall (0 : V (nd X)) ρ0 ⊆ Uc X b1 D) :
    ∃ Kd : ℝ, ∀ z ∈ Metric.closedBall (0 : V (nd X)) ρ0, densF X x1' (Φ X b1 D z) ≤ Kd := by
  have hΦc : ContinuousOn (Φ X b1 D) (Uc X b1 D) := (Φ_diffOn X b1 D).continuousOn
  have hmaps : Set.MapsTo (Φ X b1 D) (Uc X b1 D) (OmF X x1') := fun z hz => (split X b1 D hz).1
  have hc : ContinuousOn (fun z => densF X x1' (Φ X b1 D z)) (Uc X b1 D) :=
    (OntoB.densF_continuousOn (X := X) (x0 := x1')).comp hΦc hmaps
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : V (nd X)) ρ0).exists_bound_of_continuousOn (hc.mono hsub)
  exact ⟨C, fun z hz => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC z hz)⟩

def Tset (x1 : Frame X.Ψ r) (ρ : ℝ) : Set (Frame X.Ψ r) :=
  (fun p : V (nd X) × Frame X.Ψ r => rmul (cpt X x1 p.1) p.2) '' (Metric.ball 0 ρ ×ˢ Bor X.Ψ r)

theorem Tset_eq {ρ : ℝ} (hsub : Metric.ball (0 : V (nd X)) ρ ⊆ Uc X b1 D) :
    Tset X (rmul x1' b1) ρ = KU.Sset X x1' (Φ X b1 D '' Metric.ball 0 ρ) := by
  have hTmem : ∀ {y c : Frame X.Ψ r}, c ∈ Bor X.Ψ r →
      (rmul y c ∈ Tset X (rmul x1' b1) ρ ↔ y ∈ Tset X (rmul x1' b1) ρ) := fun hc =>
    KU.rmul_mem_S X (x0 := rmul x1' b1) (FF := Metric.ball 0 ρ) hc
  ext y
  constructor
  · rintro ⟨⟨z, b⟩, ⟨hz, hb⟩, rfl⟩
    have hs := split X b1 D (hsub hz)
    show rmul (cpt X (rmul x1' b1) z) b ∈ _
    rw [KU.rmul_mem_S X hb, hs.2.2]
    exact ⟨(Φ X b1 D z, β X b1 D z), ⟨⟨z, hz, rfl⟩, hs.2.1⟩, rfl⟩
  · rintro ⟨⟨w, b⟩, ⟨⟨z, hz, rfl⟩, hb⟩, rfl⟩
    have hs := split X b1 D (hsub hz)
    show rmul (cpt X x1' (Φ X b1 D z)) b ∈ Tset X (rmul x1' b1) ρ
    rw [hTmem hb, ← MI.rmul_invF X (y := cpt X x1' (Φ X b1 D z)) hs.2.1, ← hs.2.2,
      hTmem (MI.invF_mem' X hs.2.1)]
    exact ⟨(z, ExtFPf.oneF X), ⟨hz, ExtFPf.oneF_mem X⟩, ExtFPf.rmul_oneF X _⟩

theorem meas_image {ρ : ℝ} (hsub : Metric.ball (0 : V (nd X)) ρ ⊆ Uc X b1 D) (hx1 : rmul x1' b1 ∈ X.dom) :
    MeasurableSet (Φ X b1 D '' Metric.ball 0 ρ) := by
  exact measurableSet_ball.image_of_continuousOn_injOn ((Φ_diffOn X b1 D).continuousOn.mono hsub)
    ((Φ_injOn X b1 D hx1).mono hsub)

theorem meas_Tset (ho' : IsOrth X x1') {ρ : ℝ} (hsub : Metric.ball (0 : V (nd X)) ρ ⊆ Uc X b1 D)
    (hx1 : rmul x1' b1 ∈ X.dom) : MeasurableSet (Tset X (rmul x1' b1) ρ) := by
  rw [Tset_eq X b1 D hsub]
  exact KU.meas_S X ho' (meas_image X b1 D hsub hx1)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
end

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.LUB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  {x1' : Frame X.Ψ r} (b1 : Frame X.Ψ r) (D : ExtFPf.LUData X x1')

def uL (x1' b1 x : Frame X.Ψ r) : Frame X.Ψ r := fun τ =>
  (mat x1' τ * (mat b1 τ)⁻¹ * (mat x1' τ)⁻¹ * mat x τ : Matrix (Fin r) (Fin r) ℂ)

def vL (x1' b1 x : Frame X.Ψ r) : Frame X.Ψ r := fun τ =>
  (mat x1' τ * mat b1 τ * (mat x1' τ)⁻¹ * mat x τ : Matrix (Fin r) (Fin r) ℂ)

theorem cont_uL : Continuous (uL X x1' b1) := by
  unfold uL
  exact continuous_pi fun τ => Continuous.matrix_mul continuous_const (continuous_apply τ)

variable {X b1}

theorem mat_uL (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (uL X x1' b1 x) τ = mat x1' τ * (mat b1 τ)⁻¹ * (mat x1' τ)⁻¹ * mat x τ := rfl

private lemma det_mat_ne_zero_of_isOrth {x : Frame X.Ψ r} (ho : IsOrth X x) (τ : X.Ψ) : (mat x τ).det ≠ 0 := by
  intro h0
  have hg := ho τ
  have e : gram τ.1 X.Gm (mat x τ) =
      (mat x τ).transpose * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ) := by
    ext a b
    simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hd := congrArg Matrix.det hg
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at hd
  refine (Finset.prod_ne_zero_iff.mpr fun a _ => ?_) hd.symm
  unfold sgn
  split_ifs <;> norm_num

theorem uL_cpt (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) (z : V (nd X)) (b : Frame X.Ψ r) :
    uL X x1' b1 (rmul (cpt X (rmul x1' b1) z) b) = rmul (cpt X x1' z) b := by
  funext τ
  have hA := isUnit_iff_ne_zero.mpr (det_mat_ne_zero_of_isOrth ho' τ)
  have hB := isUnit_iff_ne_zero.mpr (hb1 τ).1
  have e : ∀ x b : Frame X.Ψ r, mat (rmul x b) τ = mat x τ * mat b τ := fun _ _ => rfl
  show mat (uL X x1' b1 (rmul (cpt X (rmul x1' b1) z) b)) τ = mat (rmul (cpt X x1' z) b) τ
  rw [mat_uL]
  simp only [cpt, e, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hA, Matrix.nonsing_inv_mul_cancel_left _ _ hB]

theorem vL_uL (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) (x : Frame X.Ψ r) :
    vL X x1' b1 (uL X x1' b1 x) = x := by
  funext τ
  have hA := isUnit_iff_ne_zero.mpr (det_mat_ne_zero_of_isOrth ho' τ)
  have hB := isUnit_iff_ne_zero.mpr (hb1 τ).1
  have e : ∀ y : Frame X.Ψ r,
      mat (vL X x1' b1 y) τ = mat x1' τ * mat b1 τ * (mat x1' τ)⁻¹ * mat y τ := fun _ => rfl
  show mat (vL X x1' b1 (uL X x1' b1 x)) τ = mat x τ
  rw [e, mat_uL]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hA, Matrix.mul_nonsing_inv_cancel_left _ _ hB,
    Matrix.mul_nonsing_inv_cancel_left _ _ hA]

theorem vL_cpt (ho' : IsOrth X x1') (z : V (nd X)) (b : Frame X.Ψ r) :
    vL X x1' b1 (rmul (cpt X x1' z) b) = rmul (cpt X (rmul x1' b1) z) b := by
  funext τ
  have hA := isUnit_iff_ne_zero.mpr (det_mat_ne_zero_of_isOrth ho' τ)
  have e : ∀ x b : Frame X.Ψ r, mat (rmul x b) τ = mat x τ * mat b τ := fun _ _ => rfl
  have e2 : ∀ y : Frame X.Ψ r,
      mat (vL X x1' b1 y) τ = mat x1' τ * mat b1 τ * (mat x1' τ)⁻¹ * mat y τ := fun _ => rfl
  show mat (vL X x1' b1 (rmul (cpt X x1' z) b)) τ = mat (rmul (cpt X (rmul x1' b1) z) b) τ
  rw [e2]
  simp only [cpt, e, Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ hA]

theorem Tset_eq_pre (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) {ρ : ℝ}
    (hO : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x1') :
    Tset X (rmul x1' b1) ρ = uL X x1' b1 ⁻¹' (ExtFPf.cell D ∩ D.zOf ⁻¹' Metric.ball 0 ρ) := by
  ext x
  constructor
  · rintro ⟨⟨z, b⟩, ⟨hz, hb⟩, rfl⟩
    simp only [Set.mem_preimage, Set.mem_inter_iff]
    rw [uL_cpt ho' hb1]
    obtain ⟨hΔ, hzz, -⟩ := D.uniq z (hO hz) b hb
    exact ⟨⟨OntoS.dom_rmul X (hO hz) hb, hΔ⟩, by rw [hzz]; exact hz⟩
  · rintro ⟨hcell, hzb⟩
    obtain ⟨-, hbm, e⟩ := D.split _ hcell.1 hcell.2
    refine ⟨⟨D.zOf (uL X x1' b1 x), D.bOf (uL X x1' b1 x)⟩, ⟨hzb, hbm⟩, ?_⟩
    simp only
    rw [← vL_cpt (b1 := b1) ho', ← e, vL_uL ho' hb1]

include D in
theorem isOpen_Tset (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) {ρ : ℝ}
    (hO : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x1') : IsOpen (Tset X (rmul x1' b1) ρ) := by
  rw [Tset_eq_pre D ho' hb1 hO]
  exact (D.hz.continuousOn.isOpen_inter_preimage (ExtFPf.isOpen_cell D) Metric.isOpen_ball).preimage
    (cont_uL X b1)

private lemma lact_lact_eq_lact_mul (γ δ : GL (Fin r) E) (x : Frame X.Ψ r) :
    lact γ (lact δ x) = lact (γ * δ) x := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    ((γ * δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

private lemma lact_one_upper_bounds (x : Frame X.Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = mat x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem sat_eq (x1 : Frame X.Ψ r) (ρ : ℝ) :
    {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ, x = lact γ (rmul (cpt X x1 z') b)} =
      ⋃ γ : X.Γ, lact γ.1⁻¹ ⁻¹' Tset X x1 ρ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, Tset, Set.mem_image, Set.mem_prod,
    Prod.exists]
  constructor
  · rintro ⟨γ, hγ, b, hb, z', hz', rfl⟩
    refine ⟨⟨γ, hγ⟩, z', b, ⟨hz', hb⟩, ?_⟩
    show _ = lact γ⁻¹ (lact γ _)
    rw [lact_lact_eq_lact_mul, inv_mul_cancel, lact_one_upper_bounds]
  · rintro ⟨⟨γ, hγ⟩, z', b, ⟨hz', hb⟩, h⟩
    refine ⟨γ, hγ, b, hb, z', hz', ?_⟩
    have h' : lact γ (lact γ⁻¹ x) = lact γ (rmul (cpt X x1 z') b) := by
      rw [← h]
    rw [lact_lact_eq_lact_mul, mul_inv_cancel, lact_one_upper_bounds] at h'
    exact h'

include D in
theorem isOpen_sat (ho' : IsOrth X x1') (hb1 : b1 ∈ Bor X.Ψ r) {ρ : ℝ}
    (hO : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x1') :
    IsOpen {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ,
      x = lact γ (rmul (cpt X (rmul x1' b1) z') b)} := by
  rw [sat_eq]
  refine isOpen_iUnion fun γ => ?_
  have hc : Continuous (fun x : Frame X.Ψ r => lact γ.1⁻¹ x) :=
    continuous_pi fun τ => Continuous.matrix_mul continuous_const (continuous_apply τ)
  exact (isOpen_Tset D ho' hb1 hO).preimage hc

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.LUB
