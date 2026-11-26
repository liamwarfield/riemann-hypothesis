module

public import Formalism.LocalToGlobal.GlobalTheory.CoefficientMapSurjective
public import Formalism.LocalToGlobal.GlobalTheory.NfAllSmulSelfRe

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.WeightLevelZeroEqOne
section -- merged from Formalism.LocalToGlobal.GlobalTheory.ActAllCancelInv
noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Alg

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem actAll_one (lam : ι → DomWeight n) (p : MvPolynomial (ι × Fin n × Fin n) K) :
    Formalism.MainNotions.flipTwoThree.actAll lam (fun _ => (1 : Matrix (Fin n) (Fin n) K)) p = p := by
  unfold Formalism.MainNotions.flipTwoThree.actAll
  simp only [Matrix.det_one, _root_.one_zpow, Finset.prod_const_one, one_smul]
  have e : (fun v : ι × Fin n × Fin n =>
      ∑ b, MvPolynomial.C ((1 : Matrix (Fin n) (Fin n) K) b v.2.1) * MvPolynomial.X (v.1, b, v.2.2)) = MvPolynomial.X := by
    funext v
    rw [Finset.sum_eq_single v.2.1]
    · simp
    · intro b _ hb; simp [Matrix.one_apply_ne hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [e, MvPolynomial.aeval_X_left_apply]

def actL (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) K) :
    MvPolynomial (ι × Fin n × Fin n) K →ₗ[K] MvPolynomial (ι × Fin n × Fin n) K :=
  (∏ τ, (g τ).det ^ (lam τ).detShift) •
    (MvPolynomial.aeval (fun v : ι × Fin n × Fin n =>
      ∑ b, MvPolynomial.C (g v.1 b v.2.1) * MvPolynomial.X (v.1, b, v.2.2))).toLinearMap

theorem actAll_inv_cancel (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (p : MvPolynomial (ι × Fin n × Fin n) K) :
    Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p) = p := by
  rw [actAll_comp]
  simp only [← Units.val_mul, inv_mul_cancel, Units.val_one]
  exact actAll_one lam p

theorem actAll_cancel_inv (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (p : MvPolynomial (ι × Fin n × Fin n) K) :
    Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      (Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p) = p := by
  rw [actAll_comp]
  simp only [← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact actAll_one lam p

theorem actAll_mem_TSpan [CharZero K] (lam : ι → DomWeight n) (h : ι → GL (Fin n) K)
    {p : MvPolynomial (ι × Fin n × Fin n) K} (hp : p ∈ Formalism.MainNotions.flipTwoThree.TSpan K lam) :
    Formalism.MainNotions.flipTwoThree.actAll lam (fun τ => ((h τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p ∈ Formalism.MainNotions.flipTwoThree.TSpan K lam := by
  rw [Formalism.L2.GlobalTheoryTheory.TraceIntegrality.translate_span_eq] at hp ⊢
  have h1 := Formalism.L2.GlobalTheoryTheory.TraceIntegrality.rhoEquiv_symm_coe lam h⁻¹ ⟨p, hp⟩
  have e : (fun τ => (((h⁻¹ τ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)⁻¹) =
      fun τ => ((h τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    funext τ
    rw [Pi.inv_apply, Matrix.coe_units_inv, Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnits_det_units (h τ))]
  rw [e] at h1
  rw [← h1]
  exact Submodule.coe_mem _

end Alg

variable {D : D7} {u : D.what₂.Word} (T : Forms0 D u)

def coT (g : (D.mem u).C.cls 0 → D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL) :
    ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.mem u).C.cls 0 → Pol0 D) :=
  LinearMap.pi fun c => (actL ((D.fm u).lam 0) (fun τ => ((g c τ : GL (Fin (D.R.N 0)) D.what₂.LL) :
    Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL))).comp ((LinearMap.proj c).comp (co0 T))

theorem coT_apply (g : (D.mem u).C.cls 0 → D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL) (x : ((D.fm u).lat 0).V)
    (c : (D.mem u).C.cls 0) :
    coT T g x c = Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0)
      (fun τ => ((g c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)) (co0 T x c) := rfl

theorem coT_injective (g : (D.mem u).C.cls 0 → D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL) :
    Function.Injective (coT T g) := by
  intro x y h
  apply coefficient_map_injective T
  funext c
  have h1 := congrArg (fun F => Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0)
    (fun τ => (((g c τ)⁻¹ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)) (F c)) h
  simp only [coT_apply, actAll_inv_cancel] at h1
  exact h1

theorem coT_range (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c))
    (g : (D.mem u).C.cls 0 → D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL) (F : (D.mem u).C.cls 0 → Pol0 D) :
    (∃ x, coT T g x = F) ↔ ∀ c, F c ∈ Formalism.MainNotions.flipTwoThree.TSpan D.what₂.LL ((D.fm u).lam 0) := by
  constructor
  · rintro ⟨x, rfl⟩ c
    rw [coT_apply]
    exact actAll_mem_TSpan _ _ (coefficient_map_mem_span T x c)
  · intro hF
    obtain ⟨x, hx⟩ := coefficient_map_surjective T hst (fun c => Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0)
      (fun τ => (((g c τ)⁻¹ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)) (F c))
      (fun c => actAll_mem_TSpan _ (fun τ => (g c τ)⁻¹) (hF c))
    refine ⟨x, funext fun c => ?_⟩
    rw [coT_apply, hx]
    exact actAll_cancel_inv _ _ _

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GramNDetNe
section -- merged from Formalism.LocalToGlobal.GlobalTheory.SigDEqStar
noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem sigD_eq_star (a : D.host.E) : sigD D a = star a := rfl

def rhoC (D : D7) (τ : D.what₂.Tau) : D.host.E →+* D.what₂.LL :=
  D.embE.comp ((sigD D : D.host.E →+* D.host.E).comp
    (D.host.sigmaOf (D.eTau τ : D.R.GG) : D.host.E →+* D.host.E))

theorem rhoC_conj (s : D.what₂.LL →+* ℂ) (τ : D.what₂.Tau) (a : D.host.E) :
    s (rhoC D τ a) = starRingEnd ℂ (embS D s τ a) := by
  unfold rhoC embS
  simp only [RingHom.coe_comp, Function.comp_apply]
  have hs : ∀ b : D.host.E, (sigD D : D.host.E →+* D.host.E) b = star b := fun b => sigD_eq_star b
  rw [hs]
  first
    | exact NumberField.IsCMField.complexEmbedding_complexConj (s.comp D.embE) _
    | exact NumberField.IsCMField.complexEmbedding_complexConj _ (s.comp D.embE) _
    | (erw [NumberField.IsCMField.complexEmbedding_complexConj]; rfl)
    | exact (NumberField.IsCMField.complexEmbedding_complexConj (K := D.host.E) (φ := s.comp D.embE) _)
    | (simp only [NumberField.IsCMField.complexEmbedding_star]; rfl)
    | exact NumberField.IsCMField.complexEmbedding_star _ (s.comp D.embE) _
    | exact NumberField.IsCMField.complexConj_apply_apply (s.comp D.embE) _
    | exact (NumberField.IsCMField.complexEmbedding_complexConj (s.comp D.embE) _ : _)

theorem exists_im_ne (φ : D.host.E →+* ℂ) : ∃ t : D.host.E, (φ t).im ≠ 0 := by
  by_contra h
  push_neg at h
  have hr : NumberField.ComplexEmbedding.IsReal φ := by
    first
      | (rw [NumberField.ComplexEmbedding.isReal_iff]; ext t; simp [Complex.conj_eq_iff_im, h t])
      | (intro t; simp [Complex.conj_eq_iff_im, h t])
      | (ext t; simp [Complex.conj_eq_iff_im, h t])
  have hc : (NumberField.InfinitePlace.mk φ).IsComplex := by
    first
      | exact NumberField.IsTotallyComplex.isComplex _
      | exact IsTotallyComplex.isComplex _
      | exact NumberField.InfinitePlace.IsTotallyComplex.isComplex _
  exact (NumberField.InfinitePlace.isComplex_mk_iff.mp hc) hr

def crd (y : (D.sp.X 0).V) : Fin (D.R.N 0) → D.host.E :=
  fun i => (D.sp.X 0).frame.repr y ((finCongr (rankN D 0 (Nat.zero_le _))).symm i)

theorem gramN_herm : (gramN D 0 (Nat.zero_le _))ᴴ = gramN D 0 (Nat.zero_le _) := by
  unfold gramN
  rw [Matrix.conjTranspose_reindex]
  congr 1
  first
    | exact (D.sp.X 0).gram_isHermitian
    | exact (D.sp.X 0).isHermitian_gram
    | exact (D.sp.X 0).gram_herm
    | exact (D.sp.X 0).gram_conjTranspose
    | exact (D.sp.X 0).herm
    | (ext i j; exact (D.sp.X 0).herm _ _)
    | (ext i j; exact (D.sp.X 0).herm.eq _ _)
    | (ext i j; exact LinearMap.IsSymm.eq (D.sp.X 0).herm _ _)

theorem hT_crd (y : (D.sp.X 0).V) :
    (D.sp.X 0).hT y y = star (crd y) ⬝ᵥ (gramN D 0 (Nat.zero_le _) *ᵥ crd y) := by
  unfold crd gramN
  have hy := (D.sp.X 0).frame.sum_repr y
  conv_lhs => rw [← hy]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  simp only [dotProduct, Matrix.mulVec, Matrix.reindex_apply, Matrix.submatrix_apply, Pi.star_apply, Finset.mul_sum]
  rw [← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]
  simp only [Equiv.symm_apply_apply]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]
  simp only [Equiv.symm_apply_apply, Formalism.BasicNotions.HSpace.gram]
  apply Finset.sum_congr rfl
  intro l _
  first
    | ring1
    | (clear hy; generalize ((D.sp.X 0).frame.repr y) k = a; generalize ((D.sp.X 0).frame.repr y) l = b; generalize (D.sp.X 0).hT ((D.sp.X 0).frame k) ((D.sp.X 0).frame l) = h1; generalize (D.sp.X 0).hT ((D.sp.X 0).frame l) ((D.sp.X 0).frame k) = h2; done)

variable {u : D.what₂.Word} (B : ColBase D u)

def Mb (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL :=
  fun j i => (B.Q c τ).b.repr (B.bc c τ ((D.sp.X 0).frame ((finCongr (rankN D 0 (Nat.zero_le _))).symm i)))
    ((B.eQ c τ).symm j)

theorem repr_bc (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (y : (D.sp.X 0).V) (j : Fin (D.R.N 0)) :
    (B.Q c τ).b.repr (B.bc c τ y) ((B.eQ c τ).symm j) = (Mb B c τ *ᵥ fun i => B.rho τ (crd y i)) j := by
  unfold Mb crd
  conv_lhs => rw [← (D.sp.X 0).frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, B.bc_smul, LinearMap.map_smulₛₗ, map_smulₛₗ, map_smul, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, RingHom.id_apply]
  rw [← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]
  simp only [Equiv.symm_apply_apply]
  change (Finsupp.applyAddHom ((B.eQ c τ).symm j))
    (∑ x, B.rho τ ((D.sp.X 0).frame.repr y x) •
      (B.Q c τ).b.repr (B.bc c τ ((D.sp.X 0).frame x))) = _
  rw [map_sum (Finsupp.applyAddHom ((B.eQ c τ).symm j) : _ →+ D.what₂.LL)]
  simp only [Finsupp.applyAddHom_apply, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  first
    | ring1
    | (simp only [RingHom.id_apply]; ring1)
    | (rw [mul_comm]; rfl)
    | done

def Ymat (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ :=
  Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹ * (Mb B c τ).map v.embedding

theorem fcoord_bc (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (y : (D.sp.X 0).V)
    (j : Fin (D.R.N 0)) :
    Formalism.HermitianLatticesTheory.fcoord (B.Q c τ).b (B.Q c τ).X v (B.bc c τ y) ((B.eQ c τ).symm j) =
      (Ymat B v c τ *ᵥ fun i => v.embedding (B.rho τ (crd y i))) j := by
  have hv : (fun i => v.embedding (B.rho τ (crd y i))) = fun i => v.embedding (B.rho τ (crd y i)) := rfl
  rw [Ymat, ← Matrix.mulVec_mulVec]
  unfold Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, ← (B.eQ c τ).symm.sum_comp]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [repr_bc, RingHom.map_mulVec]
  rfl

theorem maj_bc (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (y : (D.sp.X 0).V) :
    Formalism.HermitianLatticesTheory.majAt (B.Q c τ).b (B.Q c τ).X v (B.bc c τ y) (B.bc c τ y) =
      star (Ymat B v c τ *ᵥ fun i => v.embedding (B.rho τ (crd y i))) ⬝ᵥ
        (Ymat B v c τ *ᵥ fun i => v.embedding (B.rho τ (crd y i))) := by
  unfold Formalism.HermitianLatticesTheory.majAt
  rw [← (B.eQ c τ).symm.sum_comp]
  simp only [fcoord_bc]
  first
    | rfl
    | simp [dotProduct]
    | simp [Matrix.dotProduct]

theorem gram_Y (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    (Ymat B v c τ)ᴴ * Ymat B v c τ = (gramN D 0 (Nat.zero_le _)).map (v.embedding.comp (B.rho τ)) := by
  obtain ⟨t, ht⟩ := exists_im_ne (v.embedding.comp (B.rho τ))
  refine gram_of_norm (v.embedding.comp (B.rho τ)) (host_emb_star D _) _ _ gramN_herm t ht fun x => ?_
  let y : (D.sp.X 0).V := (D.sp.X 0).frame.equivFun.symm fun a => x (finCongr (rankN D 0 (Nat.zero_le _)) a)
  have hy : crd y = x := by
    funext i
    show (D.sp.X 0).frame.repr y _ = _
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    simp
  have h := B.bc_norm c τ v y
  rw [maj_bc, hT_crd, hy] at h
  exact h

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem map_inv_mat {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : A.det ≠ 0) :
    A⁻¹.map f = (A.map f)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA), Matrix.map_one _ (map_zero f) (map_one f)]

variable {D : D7}

theorem gramN_det_ne : (gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  unfold gramN
  rw [Matrix.det_reindex_self]
  exact Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Cc.gram_det_ne (D.sp.X 0) (D.sp.X 0).frame

variable {u : D.what₂.Word} (B : ColBase D u)

theorem Mb_det_ne (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : (Mb B c τ).det ≠ 0 := by
  intro h0
  have hY := congrArg Matrix.det (gram_Y B (InfinitePlace.mk D.what₂.embLL) c τ)
  have e1 : (Ymat B (InfinitePlace.mk D.what₂.embLL) c τ).det = 0 := by
    rw [Ymat, Matrix.det_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]
  rw [Matrix.det_mul, e1, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hY
  exact gramN_det_ne (((InfinitePlace.mk D.what₂.embLL).embedding.comp (B.rho τ)).injective (by rw [← hY, map_zero]))

def gC (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : GL (Fin (D.R.N 0)) D.what₂.LL :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Mb B c τ * ((gramN D 0 (Nat.zero_le _)).map (B.rho τ))⁻¹) (by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact mul_ne_zero (Mb_det_ne B c τ) (inv_ne_zero ((map_ne_zero _).2 gramN_det_ne)))

theorem gC_coe (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ((gC B c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL) =
      Mb B c τ * ((gramN D 0 (Nat.zero_le _)).map (B.rho τ))⁻¹ := rfl

def Zc (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ :=
  Ymat B v c τ * ((gramN D 0 (Nat.zero_le _)).map (v.embedding.comp (B.rho τ)))⁻¹

theorem R_gC (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹ *
      ((gC B c τ : GL (Fin (D.R.N 0)) D.what₂.LL) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL).map v.embedding =
      Zc B v c τ := by
  have hd : ((gramN D 0 (Nat.zero_le _)).map (B.rho τ)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 gramN_det_ne
  rw [gC_coe, Matrix.map_mul, map_inv_mat _ _ hd, Matrix.map_map, Zc, Ymat, Matrix.mul_assoc]
  rfl

theorem Y_det_ne (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : (Ymat B v c τ).det ≠ 0 := by
  intro h0
  have hY := congrArg Matrix.det (gram_Y B v c τ)
  rw [Matrix.det_mul, h0, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hY
  exact gramN_det_ne ((v.embedding.comp (B.rho τ)).injective (by rw [← hY, map_zero]))

theorem Zc_det_ne (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : (Zc B v c τ).det ≠ 0 := by
  rw [Zc, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact mul_ne_zero (Y_det_ne B v c τ) (inv_ne_zero ((map_ne_zero _).2 gramN_det_ne))

theorem Zc_on (hB : B.rho = rhoC D) (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ((Zc B v c τ)ᵀ)ᴴ * (gramN D 0 (Nat.zero_le _)).map (embS D v.embedding τ) * (Zc B v c τ)ᵀ = 1 := by
  set P := (gramN D 0 (Nat.zero_le _)).map (v.embedding.comp (B.rho τ)) with hPdef
  set Y := Ymat B v c τ
  set G' := (gramN D 0 (Nat.zero_le _)).map (embS D v.embedding τ)
  have hYP : Yᴴ * Y = P := gram_Y B v c τ
  have hGs : ∀ i j, star (gramN D 0 (Nat.zero_le _) j i) = gramN D 0 (Nat.zero_le _) i j := fun i j => by
    have := congrFun (congrFun (gramN_herm (D := D)) i) j
    rwa [Matrix.conjTranspose_apply] at this
  have hP : Pᴴ = P := by
    ext i j
    rw [Matrix.conjTranspose_apply, hPdef, Matrix.map_apply, Matrix.map_apply, ← hGs i j, RingHom.comp_apply,
      RingHom.comp_apply]
    have h1 := host_emb_star D (v.embedding.comp (B.rho τ)) (gramN D 0 (Nat.zero_le _) j i)
    simp only [RingHom.comp_apply] at h1
    rw [h1]
    rfl
  have hG' : G'ᵀ = P := by
    ext i j
    simp only [G', hPdef, Matrix.transpose_apply, Matrix.map_apply, RingHom.comp_apply]
    rw [hB, rhoC_conj, ← host_emb_star D (embS D v.embedding τ), hGs j i]
  have hdY : IsUnit Y.det := isUnit_iff_ne_zero.2 (Y_det_ne B v c τ)
  have hdYh : IsUnit Yᴴ.det := by rw [Matrix.det_conjTranspose]; exact hdY.star
  have hdP : IsUnit P.det := by rw [← hYP, Matrix.det_mul]; exact hdYh.mul hdY
  have key : Zc B v c τ * G'ᵀ * (Zc B v c τ)ᴴ = 1 := by
    rw [hG', Zc, ← hPdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hP]
    calc Y * P⁻¹ * P * (P⁻¹ * Yᴴ) = Y * (P⁻¹ * P) * P⁻¹ * Yᴴ := by simp only [Matrix.mul_assoc]
      _ = Y * P⁻¹ * Yᴴ := by rw [Matrix.nonsing_inv_mul _ hdP, Matrix.mul_one]
      _ = Y * (Y⁻¹ * (Yᴴ)⁻¹) * Yᴴ := by rw [← hYP, Matrix.mul_inv_rev]
      _ = (Y * Y⁻¹) * ((Yᴴ)⁻¹ * Yᴴ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hdY, Matrix.nonsing_inv_mul _ hdYh, Matrix.mul_one]
  have ht : ((Zc B v c τ)ᵀ)ᴴ * G' * (Zc B v c τ)ᵀ = (Zc B v c τ * G'ᵀ * (Zc B v c τ)ᴴ)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rfl
  rw [ht, key, Matrix.transpose_one]

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

noncomputable section

open NumberField Matrix

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem norm_sq_prod_zpow {ι : Type} [Fintype ι] (d : ι → ℂ) (k : ι → ℤ) :
    ‖∏ τ, d τ ^ k τ‖ ^ 2 = ∏ τ, ‖d τ‖ ^ (2 * k τ) := by
  rw [norm_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [norm_zpow, ← zpow_natCast, ← _root_.zpow_mul]
  congr 1
  push_cast
  ring

variable {D : D7} {u : D.what₂.Word} (T : Forms0 D u) (B : ColBase D u)

theorem weight_level_zero_eq_one (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c)) (c : (D.mem u).C.cls 0) : (D.mem u).C.wt 0 c = 1 := by
  have : Nat.card ((D.mem u).C.stab 0 c) = 1 := by
    haveI := hst c
    exact Nat.card_eq_one_iff_unique.2 ⟨hst c, ⟨1⟩⟩
  simp [Formalism.BasicNotions.ColumnChain.wt, this]

def oc (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) :
    Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D v.embedding)) :=
  (⟨fun τ => (Zc B v c τ)ᵀ, fun τ => by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.2 (Zc_det_ne B v c τ)⟩ :
    {y : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ // ∀ τ, IsUnit (y τ).det})

theorem oc_on (hB : B.rho = rhoC D) (v : InfinitePlace D.what₂.LL) (c : (D.mem u).C.cls 0) : (oc B v c).IsON :=
  fun τ => Or.inl (Zc_on B hB v c τ)

def termN (v : InfinitePlace D.what₂.LL) (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0)
    (o : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D v.embedding))) : ℝ :=
  ((D.mem u).C.wt 0 c).re * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (lamT u 0) τ)) *
    (Formalism.L2.Forms.nfAll ((D.fm u).lam 0) (subP o.1 (MvPolynomial.map v.embedding (co0 T x c)))
      (subP o.1 (MvPolynomial.map v.embedding (co0 T x c)))).re

theorem normTie_at (v : InfinitePlace D.what₂.LL) (x : ((D.fm u).lat 0).V)
    (o : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D v.embedding))) (ho : o.IsON) :
    (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re = ∑ c, termN T v x c o := by
  have h := T.norm0 v.embedding x (co0 T x) (fun c z => pol_spec T x c z) o ho
  rw [InfinitePlace.mk_embedding] at h
  exact h


open Classical in
theorem exists_single (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c)) (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    ∃ xc, co0 T xc = Pi.single c (co0 T x c) := by
  classical
  refine coefficient_map_surjective T hst _ fun c' => ?_
  by_cases h : c' = c
  · subst h; rw [Pi.single_eq_same]; exact coefficient_map_mem_span T x c'
  · rw [Pi.single_eq_of_ne h]; exact Submodule.zero_mem _

open Classical in
theorem termN_single (v : InfinitePlace D.what₂.LL) (x xc : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0)
    (hxc : co0 T xc = Pi.single c (co0 T x c)) (o : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D v.embedding))) :
    ∑ c', termN T v xc c' o = termN T v x c o := by
  classical
  rw [Finset.sum_eq_single c]
  · unfold termN; rw [hxc, Pi.single_eq_same]
  · intro c' _ hc'
    unfold termN
    rw [hxc, Pi.single_eq_of_ne hc', map_zero, map_zero, ← nfAll_eq, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.nfAll_zero_left, Complex.zero_re,
      mul_zero]
  · intro h; exact absurd (Finset.mem_univ c) h

theorem termN_indep (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c)) (v : InfinitePlace D.what₂.LL)
    (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0)
    (o o' : Frames (gramC (gramN D 0 (Nat.zero_le _)) (embS D v.embedding))) (ho : o.IsON) (ho' : o'.IsON) :
    termN T v x c o = termN T v x c o' := by
  obtain ⟨xc, hxc⟩ := exists_single T hst x c
  rw [← termN_single T v x xc c hxc o, ← termN_single T v x xc c hxc o', ← normTie_at T v xc o ho,
    ← normTie_at T v xc o' ho']

theorem termN_oc (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c)) (v : InfinitePlace D.what₂.LL)
    (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    termN T v x c (oc B v c) =
      (Formalism.MainNotions.flipTwoThree.nfAll ((D.fm u).lam 0)
        (Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Zc B v c τ) (MvPolynomial.map v.embedding (co0 T x c)))
        (Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Zc B v c τ) (MvPolynomial.map v.embedding (co0 T x c)))).re := by
  rw [actAll_eq_subP, nfAll_smul_self_re, norm_sq_prod_zpow]
  unfold termN
  rw [weight_level_zero_eq_one hst c, Complex.one_re, one_mul]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun τ _ => ?_) rfl
  have e1 : ((oc B v c).1 τ) = (Zc B v c τ)ᵀ := rfl
  rw [e1, Matrix.det_transpose, lamT_zero]
  rfl

theorem coT_term (v : InfinitePlace D.what₂.LL) (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
              (MvPolynomial.map v.embedding (coT T (gC B) x c)) =
      Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Zc B v c τ) (MvPolynomial.map v.embedding (co0 T x c)) := by
  rw [coT_apply, map_actAll, actAll_comp]
  congr 1
  funext τ
  exact R_gC B v c τ

theorem inf_coT (hB : B.rho = rhoC D) (hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c))
    (hne : Nonempty ((D.mem u).C.cls 0)) :
    ∀ (v : InfinitePlace D.what₂.LL) x,
      (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x x).re =
        ∑ c, (Formalism.MainNotions.flipTwoThree.nfAll ((D.fm u).lam 0)
          (Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (coT T (gC B) x c)))
          (Formalism.MainNotions.flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => Matrix.reindex (B.eQ c τ) (B.eQ c τ) ((B.Q c τ).X v)⁻¹)
            (MvPolynomial.map v.embedding (coT T (gC B) x c)))).re := by
  intro v x
  obtain ⟨c0⟩ := hne
  rw [normTie_at T v x (oc B v c0) (oc_on B hB v c0)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [coT_term, ← termN_oc T B hst v x c]
  exact termN_indep T hst v x c _ _ (oc_on B hB v c0) (oc_on B hB v c)

end Formalism.L2.GlobalTheoryTheory.ColValS
end
end

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.L2.GlobalTheoryTheory.ColValS

open Formalism.UG Formalism.UG.CS Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Herm Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Comp Formalism.MainNotions.GlobalTheoryTheory.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FinCo {D : D7} {u : D.what₂.Word} (T : Formalism.L2.Forms.Forms0 D u) (B : ColBase D u) : Prop :=
  ∀ w : D.what₂.places.Pl, ∃ γ : (D.mem u).C.cls 0 → D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL,
    (∀ c τ, flipTwoThree.LocBasis D w (B.Q c τ) (B.eQ c τ) (γ c τ)) ∧
    ∀ x, x ∈ locW D.what₂.places w ((D.fm u).lat 0).L ↔
      ∀ c, flipTwoThree.actAll ((D.fm u).lam 0) (fun τ => (γ c τ)⁻¹) (coT T (gC B) x c) ∈ flipTwoThree.IntSpanAt D w ((D.fm u).lam 0)

theorem colRest_of_fin {D : D7} (F : Formalism.L2.Forms.ColsTiedSym D) (h3 : flipTwoThree.adm3 D) (u : D.what₂.Word) (B : ColBase D u)
    (hB : B.rho = rhoC D) (hfin : FinCo (F.forms u).to0 B) : ColRest B := by
  have hst : ∀ c, Subsingleton ((D.mem u).C.stab 0 c) := by
    exact h3 u
  have hne : Nonempty ((D.mem u).C.cls 0) := classes_level_zero_nonempty F u
  exact ⟨coT (F.forms u).to0 (gC B), coT_injective (T := (F.forms u).to0) _, coT_range (T := (F.forms u).to0) hst _,
    hfin, inf_coT (T := (F.forms u).to0) (B := B) hB hst hne⟩

theorem colValOfTiedS_of_fin
    (h : ∀ D : D7, ∀ F : Formalism.L2.Forms.ColsTiedSym D, flipTwoThree.adm3 D → ∀ (u : D.what₂.Word) (B : ColBase D u),
      B.rho = rhoC D → FinCo (F.forms u).to0 B) :
    Formalism.MainNotions.RT.ColumnValuationFromTwistCompatibility :=
  colValOfTiedS_of_rest' fun D F h3 u => ⟨rhoC D, fun B hB => colRest_of_fin F h3 u B hB (h D F h3 u B hB)⟩

end Formalism.L2.GlobalTheoryTheory.ColValS
