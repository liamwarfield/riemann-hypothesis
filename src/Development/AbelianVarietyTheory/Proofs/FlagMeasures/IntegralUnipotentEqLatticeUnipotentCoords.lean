module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaCOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HbApply

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordEquivSymmApply
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDomGrp

variable {D : D7} (X : HidaSetting D)

theorem vecOf_apply (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    vecOf X c = ∑ i, c i • X.bas (ci X i) := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.funCongrLeft_apply, Module.Basis.equivFun_symm_apply]
  rw [← (ci X).sum_comp]
  simp

theorem crdH_vecOf (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) : crdH X (vecOf X c) = c := by
  funext i
  simp only [crdH, vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, LinearEquiv.funCongrLeft_apply]
  simp

theorem vecOf_crdH (y : (VS D).V) : vecOf X (crdH X y) = y := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  conv_rhs => rw [← X.bas.equivFun.symm_apply_apply y]
  congr 1

variable {X} in
theorem n_vecOf {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E}
    (hγ : ∀ y, crdH X (n y) = γ *ᵥ crdH X y) (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    n (vecOf X c) = vecOf X (γ *ᵥ c) := by
  conv_lhs => rw [← vecOf_crdH X (n (vecOf X c)), hγ, crdH_vecOf]

theorem crdH_eq_crd (y : (VS D).V) (i : Fin (2 * D.R.rS + D.R.k + 1)) :
    crdH X y i = X.ιE (X.crd y (ci X i)) := by
  simp [crdH, HidaSetting.crd, crdOf]

theorem sig_apply (a : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) a = star a := rfl

theorem hT_vecOf (a b : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    (VS D).hT (vecOf X a) (vecOf X b) = GlobalTheory.SgAlg.form (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) b a := by
  rw [vecOf_apply, vecOf_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    GlobalTheory.SgAlg.form, dotProduct, Matrix.mulVec, sig_apply, Jc, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply]
  ring

theorem Jc_det_ne_zero : (Jc X).det ≠ 0 := by
  have h : Jc X = (X.B.I.J.map X.ιE).submatrix (ci X) (ci X) := by
    ext i j
    simp [Jc, X.J_eq]
  rw [h, Matrix.det_submatrix_equiv_self]
  intro h0
  apply X.B.I.J_det
  apply X.ιE.injective
  rw [map_zero]
  exact (RingHom.map_det X.ιE.toRingHom X.B.I.J).trans h0

def coordEquiv : (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) ≃ₗ[D.host.E] (VS D).V :=
  (LinearEquiv.funCongrLeft D.host.E D.host.E (ci X).symm).trans X.bas.equivFun.symm

theorem coordEquiv_apply (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) : coordEquiv X c = vecOf X c := rfl

theorem coordEquiv_symm_apply (y : (VS D).V) : (coordEquiv X).symm y = crdH X y := by
  apply (coordEquiv X).injective
  rw [LinearEquiv.apply_symm_apply, coordEquiv_apply, vecOf_crdH]

theorem exists_mat (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    ∃ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, ∀ y, crdH X (n y) = γ *ᵥ crdH X y := by
  refine ⟨LinearMap.toMatrix' (((coordEquiv X).symm.toLinearMap ∘ₗ n.toLinearMap) ∘ₗ (coordEquiv X).toLinearMap), fun y => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  simp [coordEquiv_symm_apply, coordEquiv_apply, vecOf_crdH]

theorem exists_equiv (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E) (hU : GlobalTheory.SgAlg.IsUn (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) γ) :
    ∃ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, ∀ y, crdH X (n y) = γ *ᵥ crdH X y := by
  have hdet : IsUnit γ.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply Jc_det_ne_zero X
    have := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact this.symm
  have h1 : γ⁻¹ * γ = 1 := Matrix.nonsing_inv_mul γ hdet
  have h2 : γ * γ⁻¹ = 1 := Matrix.mul_nonsing_inv γ hdet
  refine ⟨(coordEquiv X).symm.trans ((Matrix.toLin'OfInv h1 h2).trans (coordEquiv X)), fun y => ?_⟩
  simp only [LinearEquiv.trans_apply, coordEquiv_symm_apply, coordEquiv_apply, Matrix.toLin'OfInv_apply,
    Matrix.toLin'_apply, crdH_vecOf]
  rfl

end GlobalTheory.CovDomGrp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryCoordinateMatrixRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryCoordinateMatrixRealPlace
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDomGrp

theorem coordMat_place : ∀ {D : D7} (X : HidaSetting D) {x : X.B.I.GA} (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), Formalism.L2.SG.TermOp.RatLink X x n → (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → ∀ τ : D.what₂.Tau, γ.map (embS D τ) = (X.B.I.P (vOf X τ) * uMat (x.1 (vOf X τ)) * (X.B.I.P (vOf X τ))⁻¹).submatrix (ci X) (ci X) := by
  intro D X x n γ hR hγ τ
  obtain ⟨M, -, h1, -, h4⟩ := hR
  have hPu : IsUnit (X.B.I.P (vOf X τ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit (vOf X τ))
  have hP : X.B.I.P (vOf X τ) * uMat (x.1 (vOf X τ)) * (X.B.I.P (vOf X τ))⁻¹ =
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ (vOf X τ)) := by
    rw [h1 (vOf X τ)]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one]

  have hN : ∀ c, γ *ᵥ c = (((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map X.ιE).submatrix (ci X) (ci X)) *ᵥ c := by
    intro c
    have hc := hγ (vecOf X c)
    rw [crdH_vecOf] at hc
    rw [← hc]
    funext i
    rw [crdH_eq_crd, h4]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.submatrix_apply, Matrix.map_apply]
    rw [← (ci X).sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← crdH_eq_crd, crdH_vecOf]
  have hγe : γ = ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map X.ιE).submatrix (ci X) (ci X) :=
    Matrix.toLin'.injective (LinearMap.ext fun c => by rw [Matrix.toLin'_apply, Matrix.toLin'_apply]; exact hN c)
  rw [hP, hγe]
  ext i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, X.φ_eq]
  congr 1
  simp [vOf]

end GlobalTheory.CovDomGrp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryCoordinateMatrixRealPlaceStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalIsometry_coordinateMatrix_realPlace : ∀ {D : D7} (X : HidaSetting D) {x : X.B.I.GA} (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), Formalism.L2.SG.TermOp.RatLink X x n → (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → ∀ τ : D.what₂.Tau, γ.map (embS D τ) = (X.B.I.P (vOf X τ) * uMat (x.1 (vOf X τ)) * (X.B.I.P (vOf X τ))⁻¹).submatrix (ci X) (ci X) := by
  first | exact @GlobalTheory.CovDomGrp.coordMat_place | exact GlobalTheory.CovDomGrp.coordMat_place | (intros; apply GlobalTheory.CovDomGrp.coordMat_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelTransportConjPlaceMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelTransportConjPlaceMatrices
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDomGrp.Transp

theorem besselModelTransportMatrix_mul_right {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    A0 X C w * (X.B.I.P (vOf X (tauOf D w)) * C.Q (tauOf D w)).submatrix (ci X) id = 1 := by
  have hu : IsUnit (X.B.I.P (vOf X (tauOf D w))).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit _)
  have h1 : (X.B.I.P (vOf X (tauOf D w)))⁻¹ * X.B.I.P (vOf X (tauOf D w)) = 1 := Matrix.nonsing_inv_mul _ hu
  obtain ⟨hQ, -, -, -⟩ := C.isT (tauOf D w)
  rw [A0, ← submatrix_mul _ _ id (ci X) id (ci X).bijective]
  have : C.Qi (tauOf D w) * (X.B.I.P (vOf X (tauOf D w)))⁻¹ * (X.B.I.P (vOf X (tauOf D w)) * C.Q (tauOf D w)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (X.B.I.P _), h1, Matrix.one_mul, hQ]
  rw [this, submatrix_id_id]

theorem besselModelTransportMatrix_inv_eq_frame {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    (A0 X C w)⁻¹ = (X.B.I.P (vOf X (tauOf D w)) * C.Q (tauOf D w)).submatrix (ci X) id :=
  Matrix.inv_eq_right_inv (besselModelTransportMatrix_mul_right X C w)

theorem besselModelTransportMatrix_conj_realPoint {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (s : X.B.I.Ginf) (w : InfinitePlace D.host.E) :
    A0 X C w * ((X.B.I.P (vOf X (tauOf D w)) * uMat (s (vOf X (tauOf D w))) * (X.B.I.P (vOf X (tauOf D w)))⁻¹).submatrix (ci X) (ci X))
      * (A0 X C w)⁻¹ = Formalism.L2.SG.RealObj.trG (C.Q (tauOf D w)) (C.Qi (tauOf D w)) (s (vOf X (tauOf D w))) := by
  have hu : IsUnit (X.B.I.P (vOf X (tauOf D w))).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit _)
  have h1 : (X.B.I.P (vOf X (tauOf D w)))⁻¹ * X.B.I.P (vOf X (tauOf D w)) = 1 := Matrix.nonsing_inv_mul _ hu
  rw [besselModelTransportMatrix_inv_eq_frame, A0, ← submatrix_mul _ _ id (ci X) (ci X) (ci X).bijective,
    ← submatrix_mul _ _ id (ci X) id (ci X).bijective, submatrix_id_id, Formalism.L2.SG.RealObj.trG]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc _ (X.B.I.P _) (uMat _ * _), h1, Matrix.one_mul,
    ← Matrix.mul_assoc (X.B.I.P _)⁻¹ (X.B.I.P _) (C.Q _), h1, Matrix.one_mul]

theorem transp : ∀ {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (s : X.B.I.Ginf) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ τ, γ.map (embS D τ) = (X.B.I.P (vOf X τ) * uMat (s (vOf X τ)) * (X.B.I.P (vOf X τ))⁻¹).submatrix (ci X) (ci X)) → ∀ w : InfinitePlace D.host.E, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w) := by
  intro D X θ C s γ hγ w
  have key := besselModelTransportMatrix_conj_realPoint X C s w
  rw [← hγ] at key
  unfold Ac Gm cjw trX
  split_ifs with hd
  · rw [show w.embedding = embS D (tauOf D w) from hd, key]
    rfl
  · rw [ModelIso.embedding_of_not_direct w hd]
    have hg : γ.map (ComplexEmbedding.conjugate (embS D (tauOf D w))) = (γ.map (embS D (tauOf D w))).map (starRingEnd ℂ) := by
      ext i j; simp [ComplexEmbedding.conjugate_coe_eq]
    have hinv : ((A0 X C w).map star)⁻¹ = ((A0 X C w)⁻¹).map (starRingEnd ℂ) := by
      apply Matrix.inv_eq_right_inv
      rw [show (A0 X C w).map star = (A0 X C w).map (starRingEnd ℂ) from rfl, ← Matrix.map_mul, besselModelTransportMatrix_inv_eq_frame, besselModelTransportMatrix_mul_right,
        Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hg, hinv, show (A0 X C w).map star = (A0 X C w).map (starRingEnd ℂ) from rfl, ← Matrix.map_mul, ← Matrix.map_mul, key]
    ext i j
    simp

end GlobalTheory.CovDomGrp.Transp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelTransportConjPlaceMatricesStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselModelTransport_conj_placeMatrices : ∀ {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (s : X.B.I.Ginf) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ τ, γ.map (embS D τ) = (X.B.I.P (vOf X τ) * uMat (s (vOf X τ)) * (X.B.I.P (vOf X τ))⁻¹).submatrix (ci X) (ci X)) → ∀ w : InfinitePlace D.host.E, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w) := by
  first | exact @GlobalTheory.CovDomGrp.Transp.transp | exact GlobalTheory.CovDomGrp.Transp.transp | (intros; apply GlobalTheory.CovDomGrp.Transp.transp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeCoordinatesImageIffPreserved
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeCoordinatesImageIffPreserved
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDomGrp

theorem latMap_Lc_iff : ∀ {D : D7} (X : HidaSetting D) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → (GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X ↔ Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0) := by
  intro D X n γ hγ
  have key : GlobalTheory.SgGlob.latMap γ (Lc X) =
      (Formalism.HermitianLatticesTheory.gmap n (VS D).L0).comap ((vecOf X).restrictScalars (𝓞 D.host.E)) := by
    ext c
    simp only [GlobalTheory.SgGlob.latMap, Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, Submodule.mem_comap, Lc,
      LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨c', hc', rfl⟩
      exact ⟨vecOf X c', hc', n_vecOf hγ c'⟩
    · rintro ⟨y, hy, hny⟩
      refine ⟨crdH X y, by rw [vecOf_crdH]; exact hy, ?_⟩
      rw [← hγ, hny, crdH_vecOf]
  have hsurj : Function.Surjective ((vecOf X).restrictScalars (𝓞 D.host.E)) := fun y =>
    ⟨crdH X y, vecOf_crdH X y⟩
  rw [key]
  exact (Submodule.comap_injective_of_surjective hsurj).eq_iff

end GlobalTheory.CovDomGrp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeCoordinatesImageIffPreservedStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLatticeCoordinates_image_iff_preserved : ∀ {D : D7} (X : HidaSetting D) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → (GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X ↔ Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0) := by
  first | exact @GlobalTheory.CovDomGrp.latMap_Lc_iff | exact GlobalTheory.CovDomGrp.latMap_Lc_iff | (intros; apply GlobalTheory.CovDomGrp.latMap_Lc_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometrySubOneOrthogonalLeCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometrySubOneOrthogonalLeCoordinates
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDomGrp

variable {D : D7} (X : HidaSetting D)

theorem eOf_Pc_apply (u : D.what₂.Word) (i : Fin (2 * D.R.rS + D.R.k + 1)) (a : Fin D.R.rS) :
    GlobalTheory.SgAlg.eOf (Pc X u) i a = crdH X (X.eX a) i := by
  simp [GlobalTheory.SgAlg.eOf, Pc]

theorem Xsp_Fu_eq_span (u : D.what₂.Word) :
    Formalism.MainNotions.S.Lat.Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (Set.range X.eX) := by
  show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
  rw [X.Fu_e]

theorem vecOf_eOf_mulVec (u : D.what₂.Word) (c : Fin D.R.rS → D.host.E) :
    vecOf X (GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c) = ∑ a, c a • X.eX a := by
  have hcol : GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c = ∑ a, c a • crdH X (X.eX a) := by
    ext i
    simp [Matrix.mulVec, dotProduct, eOf_Pc_apply, Finset.sum_apply, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hcol, map_sum]
  simp only [map_smul, vecOf_crdH]

theorem cT_eOf_mulVec_apply (u : D.what₂.Word) (v : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) (a : Fin D.R.rS) :
    ((GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (GlobalTheory.SgAlg.eOf (Pc X u)) * Jc X) *ᵥ v) a
      = (VS D).hT (X.eX a) (vecOf X v) := by
  rw [← Matrix.mulVec_mulVec]
  conv_rhs => rw [← vecOf_crdH X (X.eX a), hT_vecOf]
  simp only [GlobalTheory.SgAlg.form, GlobalTheory.SgAlg.cT, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Matrix.map_apply, eOf_Pc_apply]

theorem mem_orth_span_iff (y : (VS D).V) :
    y ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Submodule.span D.host.E (Set.range X.eX)) ↔
      ∀ a, (VS D).hT (X.eX a) y = 0 := by
  simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h a
    exact h _ (Submodule.subset_span ⟨a, rfl⟩)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact h a
    | zero => simp
    | add x z _ _ hx hz => simp [hx, hz]
    | smul c x _ hx => simp [hx]

theorem orth_cond_iff_coord : ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → ((∀ v, (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (GlobalTheory.SgAlg.eOf (Pc X u)) * Jc X) *ᵥ v = 0 → ∃ c, γ *ᵥ v - v = GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c) ↔ ∀ x ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Formalism.MainNotions.S.Lat.Xsp (lf D (X.Fu u))), n x - x ∈ Formalism.MainNotions.S.Lat.Xsp (lf D (X.Fu u))) := by
  intro D X u n γ hγ
  have inj : Function.Injective (vecOf X) := fun a b h => by
    simpa [crdH_vecOf] using congrArg (crdH X) h
  have hperp : ∀ v, (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (GlobalTheory.SgAlg.eOf (Pc X u)) * Jc X) *ᵥ v = 0 ↔
      ∀ a, (VS D).hT (X.eX a) (vecOf X v) = 0 := by
    intro v
    constructor
    · intro h a
      have h' := congrFun h a
      rwa [cT_eOf_mulVec_apply] at h'
    · intro h
      funext a
      rw [cT_eOf_mulVec_apply]
      exact h a
  have himg : ∀ v c, (γ *ᵥ v - v = GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c ↔
      n (vecOf X v) - vecOf X v = ∑ a, c a • X.eX a) := by
    intro v c
    rw [← vecOf_eOf_mulVec X u c, n_vecOf hγ, ← map_sub]
    exact inj.eq_iff.symm
  rw [Xsp_Fu_eq_span X u]
  constructor
  · intro H x hx
    rw [mem_orth_span_iff X x] at hx
    obtain ⟨c, hc⟩ := H (crdH X x) ((hperp _).2 (by simpa [vecOf_crdH] using hx))
    rw [himg, vecOf_crdH] at hc
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨c, hc.symm⟩
  · intro H v hv
    have hx : vecOf X v ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Submodule.span D.host.E (Set.range X.eX)) :=
      (mem_orth_span_iff X (vecOf X v)).2 ((hperp v).1 hv)
    have hm := H _ hx
    rw [Submodule.mem_span_range_iff_exists_fun] at hm
    obtain ⟨c, hc⟩ := hm
    exact ⟨c, (himg v c).2 hc.symm⟩

end GlobalTheory.CovDomGrp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometrySubOneOrthogonalLeCoordinatesStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_sub_one_orthogonal_le_coordinates : ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → ((∀ v, (GlobalTheory.SgAlg.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (GlobalTheory.SgAlg.eOf (Pc X u)) * Jc X) *ᵥ v = 0 → ∃ c, γ *ᵥ v - v = GlobalTheory.SgAlg.eOf (Pc X u) *ᵥ c) ↔ ∀ x ∈ Formalism.MainNotions.S.Lat.orth (VS D) (Formalism.MainNotions.S.Lat.Xsp (lf D (X.Fu u))), n x - x ∈ Formalism.MainNotions.S.Lat.Xsp (lf D (X.Fu u))) := by
  first | exact @GlobalTheory.CovDomGrp.orth_cond_iff_coord | exact GlobalTheory.CovDomGrp.orth_cond_iff_coord | (intros; apply GlobalTheory.CovDomGrp.orth_cond_iff_coord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHermitianIsometryMatrixIffMemIsometries
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHermitianIsometryMatrixIffMemIsometries
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDomGrp

theorem form_mulVec_mulVec {E : Type} [CommRing E] (σ : E →+* E) {m : ℕ} (J γ : Matrix (Fin m) (Fin m) E)
    (x y : Fin m → E) :
    GlobalTheory.SgAlg.form σ J (γ *ᵥ x) (γ *ᵥ y) = GlobalTheory.SgAlg.form σ (GlobalTheory.SgAlg.cT σ γ * J * γ) x y := by
  have h : (fun i => σ ((γ *ᵥ y) i)) = (fun i => σ (y i)) ᵥ* GlobalTheory.SgAlg.cT σ γ := by
    funext i
    simp [GlobalTheory.SgAlg.cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  simp only [GlobalTheory.SgAlg.form]
  rw [h, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem form_single_single {E : Type} [CommRing E] (σ : E →+* E) {m : ℕ} (M : Matrix (Fin m) (Fin m) E)
    (i j : Fin m) : GlobalTheory.SgAlg.form σ M (Pi.single j 1) (Pi.single i 1) = M i j := by
  simp [GlobalTheory.SgAlg.form, dotProduct, Pi.single_apply, Matrix.mulVec_single]

theorem isUn_iff_mem_isom {D : D7} (X : HidaSetting D) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E)
    (hγ : ∀ y, crdH X (n y) = γ *ᵥ crdH X y) :
    GlobalTheory.SgAlg.IsUn (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) γ ↔ n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
  constructor
  · intro hU
    change ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y
    intro x y
    rw [← vecOf_crdH X x, ← vecOf_crdH X y, n_vecOf hγ, n_vecOf hγ, hT_vecOf, hT_vecOf,
      form_mulVec_mulVec, hU]
  · intro hn
    have hn' : ∀ x y, (VS D).hT (n x) (n y) = (VS D).hT x y := hn
    ext i j
    rw [← form_single_single _ (GlobalTheory.SgAlg.cT _ γ * Jc X * γ) i j, ← form_mulVec_mulVec,
      ← hT_vecOf X, ← n_vecOf hγ, ← n_vecOf hγ, hn', hT_vecOf, form_single_single]

end GlobalTheory.CovDomGrp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHermitianIsometryMatrixIffMemIsometriesStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHermitianIsometryMatrix_iff_mem_isometries : ∀ {D : D7} (X : HidaSetting D) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → (GlobalTheory.SgAlg.IsUn (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) γ ↔ n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) := by
  first | exact @GlobalTheory.CovDomGrp.isUn_iff_mem_isom | exact GlobalTheory.CovDomGrp.isUn_iff_mem_isom | (intros; apply GlobalTheory.CovDomGrp.isUn_iff_mem_isom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFrameUnitriangularIffFlagPreserved
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFrameUnitriangularIffFlagPreserved
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CovDomGrp

variable {D : D7} (X : HidaSetting D)

theorem crdH_injective : Function.Injective (crdH X) := by
  intro y y' h
  rw [← vecOf_crdH X y, h, vecOf_crdH]

theorem mul_eOf_Pc_apply (u : D.what₂.Word)
    (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E)
    (i : Fin (2 * D.R.rS + D.R.k + 1)) (a : Fin D.R.rS) :
    (γ * GlobalTheory.SgAlg.eOf (Pc X u)) i a = (γ *ᵥ crdH X (X.eX a)) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, GlobalTheory.SgAlg.eOf, Pc]

theorem eOf_Pc_mul_apply (u : D.what₂.Word) (ν : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (i : Fin (2 * D.R.rS + D.R.k + 1)) (a : Fin D.R.rS) :
    (GlobalTheory.SgAlg.eOf (Pc X u) * ν) i a = crdH X (∑ b, ν b a • X.eX b) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coordEquiv_symm_apply, map_sum]
  simp [Matrix.mul_apply, GlobalTheory.SgAlg.eOf, Pc, coordEquiv_symm_apply, Finset.sum_apply, mul_comm]

theorem xflag_Fu (u : D.what₂.Word) (j : ℕ) :
    Formalism.MainNotions.S.Lat.Xflag (lf D (X.Fu u)) j = Submodule.span D.host.E (X.eX '' {i | i.1 < j}) := by
  show (X.Fu u).Xa j = _
  unfold FlagG.Xa
  rw [X.Fu_e]

theorem flag_iff {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E) :
    (∀ y, crdH X (n y) = γ *ᵥ crdH X y) →
    ((∃ ν, GlobalTheory.SgAlg.IsUp ν ∧ γ * GlobalTheory.SgAlg.eOf (Pc X u) = GlobalTheory.SgAlg.eOf (Pc X u) * ν) ↔
      ∀ j, ∀ x ∈ Formalism.MainNotions.S.Lat.Xflag (lf D (X.Fu u)) (j + 1), n x - x ∈ Formalism.MainNotions.S.Lat.Xflag (lf D (X.Fu u)) j) := by
  intro hγ
  have hcol : ∀ ν : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E,
      γ * GlobalTheory.SgAlg.eOf (Pc X u) = GlobalTheory.SgAlg.eOf (Pc X u) * ν ↔ ∀ a, n (X.eX a) = ∑ b, ν b a • X.eX b := by
    intro ν
    constructor
    · intro h a
      apply crdH_injective X
      funext i
      rw [← eOf_Pc_mul_apply, ← h, mul_eOf_Pc_apply, hγ]
    · intro h
      ext i a
      rw [mul_eOf_Pc_apply, eOf_Pc_mul_apply, ← h, hγ]
  simp only [xflag_Fu]
  constructor
  · rintro ⟨ν, hν, h⟩
    have h1 := (hcol ν).1 h
    have hstep : ∀ a : Fin D.R.rS,
        n (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {i | i.1 < a.1}) := by
      intro a
      rw [h1 a]
      have hs : ∑ b, ν b a • X.eX b - X.eX a = ∑ b, (ν b a - if b = a then 1 else 0) • X.eX b := by
        simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
      rw [hs]
      refine Submodule.sum_mem _ fun b _ => ?_
      rcases lt_trichotomy b a with hb | rfl | hb
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
      · simp [(hν b b).2 rfl]
      · simp [(hν b a).1 hb, hb.ne']
    intro j x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      have hij : i.1 ≤ j := Nat.lt_succ_iff.mp hi
      have hsub : {k : Fin D.R.rS | k.1 < i.1} ⊆ {k : Fin D.R.rS | k.1 < j} :=
        fun k (hk : k.1 < i.1) => (lt_of_lt_of_le hk hij : k.1 < j)
      exact Submodule.span_mono (Set.image_mono hsub) (hstep i)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      convert Submodule.add_mem _ hx hy using 1
      abel
    | smul c x _ hx =>
      rw [map_smul]
      convert Submodule.smul_mem _ c hx using 1
      rw [smul_sub]
  · intro h
    have ha : ∀ a : Fin D.R.rS, ∃ l ∈ Finsupp.supported D.host.E D.host.E {i : Fin D.R.rS | i.1 < a.1},
        Finsupp.linearCombination D.host.E X.eX l = n (X.eX a) - X.eX a := by
      intro a
      rw [← Finsupp.mem_span_image_iff_linearCombination]
      exact h a.1 (X.eX a) (Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩)
    choose l hl hl2 using ha
    refine ⟨fun b a => l a b + if b = a then 1 else 0, ?_, (hcol _).2 fun a => ?_⟩
    · intro i j
      constructor
      · intro hji
        have h0 : l j i = 0 := (Finsupp.mem_supported' _ _).1 (hl j) i (fun hh => absurd (hh : i.1 < j.1) (not_lt.2 (le_of_lt hji)))
        simp [h0, (ne_of_lt hji).symm]
      · rintro rfl
        have h0 : l i i = 0 := (Finsupp.mem_supported' _ _).1 (hl i) i (fun hh => lt_irrefl i.1 hh)
        simp [h0]
    · have hlc := hl2 a
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hlc
      simp only [add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, hlc]
      abel

end GlobalTheory.CovDomGrp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFrameUnitriangularIffFlagPreservedStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFrame_unitriangular_iff_flag_preserved : ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → ((∃ ν, GlobalTheory.SgAlg.IsUp ν ∧ γ * GlobalTheory.SgAlg.eOf (Pc X u) = GlobalTheory.SgAlg.eOf (Pc X u) * ν) ↔ ∀ j, ∀ x ∈ Formalism.MainNotions.S.Lat.Xflag (lf D (X.Fu u)) (j + 1), n x - x ∈ Formalism.MainNotions.S.Lat.Xflag (lf D (X.Fu u)) j) := by
  first | exact @GlobalTheory.CovDomGrp.flag_iff | exact GlobalTheory.CovDomGrp.flag_iff | (intros; apply GlobalTheory.CovDomGrp.flag_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentEqLatticeUnipotentCoords
noncomputable section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDomGrp

theorem nO_eq_nLam_coords : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), (∀ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, (GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) → ∃ s ∈ NOinf X u, ∀ w, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w)) ∧ (∀ s ∈ NOinf X u, ∃ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, (GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) ∧ ∀ w, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w)) := by
  intro D X θ C u
  have key : ∀ (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) →
      ((GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) ↔
        n ∈ Formalism.MainNotions.S.Lat.NLam (VS D).L0 (lf D (X.Fu u))) := by
    intro n γ hγ
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨⟨(GlobalTheory.T.isHermitianIsometryMatrix_iff_mem_isometries X n γ hγ).1 h1, (GlobalTheory.T.selfDualLatticeCoordinates_image_iff_preserved X n γ hγ).1 h4⟩, (GlobalTheory.T.isotropicFrame_unitriangular_iff_flag_preserved X u n γ hγ).1 h2,
        (GlobalTheory.T.isometry_sub_one_orthogonal_le_coordinates X u n γ hγ).1 h3⟩
    · rintro ⟨⟨h1, h4⟩, h2, h3⟩
      exact ⟨⟨(GlobalTheory.T.isHermitianIsometryMatrix_iff_mem_isometries X n γ hγ).2 h1, (GlobalTheory.T.isotropicFrame_unitriangular_iff_flag_preserved X u n γ hγ).2 h2, (GlobalTheory.T.isometry_sub_one_orthogonal_le_coordinates X u n γ hγ).2 h3⟩,
        (GlobalTheory.T.selfDualLatticeCoordinates_image_iff_preserved X n γ hγ).2 h4⟩
  refine ⟨fun γ hγ => ?_, fun s hs => ?_⟩
  · obtain ⟨n, hn⟩ := exists_equiv X γ hγ.1.1
    have hnL := (key n γ hn).1 hγ
    obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n hnL.1.1
    exact ⟨x.1, (Formalism.L2.SG.Pf.NcReal.JX.NOf.noratC_holds X u x.1).2 ⟨x, n, hx, rfl, hnL⟩,
      GlobalTheory.T.besselModelTransport_conj_placeMatrices X C x.1 γ (GlobalTheory.T.rationalIsometry_coordinateMatrix_realPlace X n γ hx hn)⟩
  · obtain ⟨x, n, hx, rfl, hnL⟩ := (Formalism.L2.SG.Pf.NcReal.JX.NOf.noratC_holds X u s).1 hs
    obtain ⟨γ, hγ⟩ := exists_mat X n
    exact ⟨γ, (key n γ hγ).2 hnL, GlobalTheory.T.besselModelTransport_conj_placeMatrices X C x.1 γ (GlobalTheory.T.rationalIsometry_coordinateMatrix_realPlace X n γ hx hγ)⟩

end GlobalTheory.CovDomGrp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentEqLatticeUnipotentCoordsStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotent_eq_latticeUnipotent_coords : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), (∀ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, (GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) → ∃ s ∈ NOinf X u, ∀ w, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w)) ∧ (∀ s ∈ NOinf X u, ∃ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, (GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) ∧ ∀ w, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w)) := by
  first | exact @GlobalTheory.CovDomGrp.nO_eq_nLam_coords | exact GlobalTheory.CovDomGrp.nO_eq_nLam_coords | (intros; apply GlobalTheory.CovDomGrp.nO_eq_nLam_coords <;> assumption)
end
