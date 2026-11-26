module

public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteResidueField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerEqIntegralOfAe
open Formalism.BasicNotions Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta NumberField MeasureTheory Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem inner_eq_integral_of_ae {α : Type} [MeasurableSpace α] {m : Measure α} (f g : Lp ℂ 2 m) (f' g' : α → ℂ)
    (hf : f =ᵐ[m] f') (hg : g =ᵐ[m] g') : ⟪f, g⟫_ℂ = ∫ x, star (f' x) * g' x ∂m := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf, hg] with x h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]
  rfl

theorem eq_smul_of_eval {α A E V : Type} [MeasurableSpace α] {m : Measure α} [AddCommGroup E] [Module ℂ E]
    (W : Submodule ℂ (Lp ℂ 2 m)) (φ : E → V → α → ℂ) (p : V → V → ℂ)
    (hS : ∀ T T', ∃ k : ℂ, ∀ v v', ∫ x, star (φ T v x) * φ T' v' x ∂m = k * p v v')
    (v₁ v₀ : V) (hp : p v₁ v₁ = 1) (j' : E ≃ₗ[ℂ] W) (hj' : ∀ T, ((j' T : W) : Lp ℂ 2 m) =ᵐ[m] φ T v₁)
    (e : A → E) (j : A → W) (a : ℂ) (hj : ∀ F, ((j F : W) : Lp ℂ 2 m) =ᵐ[m] fun x => a * φ (e F) v₀ x) (F : A) :
    j F = (a * p v₁ v₀) • j' (e F) := by
  have hmix : ∀ T : E, ⟪j' T, j F⟫_ℂ = (a * p v₁ v₀) * ⟪j' T, j' (e F)⟫_ℂ := by
    intro T
    obtain ⟨k, hk⟩ := hS T (e F)
    have h1 := inner_eq_integral_of_ae _ _ _ _ (hj' T) (hj F)
    have h2 := inner_eq_integral_of_ae _ _ _ _ (hj' T) (hj' (e F))
    rw [hk, hp, mul_one] at h2
    have h3 : ∫ x, star (φ T v₁ x) * (a * φ (e F) v₀ x) ∂m = a * ∫ x, star (φ T v₁ x) * φ (e F) v₀ x ∂m := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    rw [h3, hk] at h1
    rw [Submodule.coe_inner, Submodule.coe_inner, h1, h2]
    ring
  obtain ⟨T, hT⟩ := j'.surjective (j F - (a * p v₁ v₀) • j' (e F))
  have hz : ⟪j F - (a * p v₁ v₀) • j' (e F), j F - (a * p v₁ v₀) • j' (e F)⟫_ℂ = 0 := by
    conv_lhs => enter [2]; rw [← hT]
    rw [inner_sub_right, inner_smul_right, hmix, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem exists_conj_scalar {A W H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup W] [Module ℂ W] [AddCommGroup H]
    [Module ℂ H] (s : W →ₗ⋆[ℂ] H) (j f : A →ₗ[ℂ] W) (hj : Function.Injective j) (β : ℂ) (h : ∀ F, j F = β • f F) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ F, s (f F) = κ • s (j F) := by
  by_cases h0 : β = 0
  · refine ⟨1, one_ne_zero, fun F => ?_⟩
    have hF : j F = 0 := by rw [h, h0, zero_smul]
    have hF0 : F = 0 := hj (hF.trans (map_zero j).symm)
    subst hF0
    simp
  · refine ⟨(starRingEnd ℂ β)⁻¹, inv_ne_zero ((map_ne_zero _).2 h0), fun F => ?_⟩
    rw [h, LinearMap.map_smulₛₗ, smul_smul, inv_mul_cancel₀ ((map_ne_zero _).2 h0), one_smul]

theorem sEEofTT_eq_smul_conjHH : ∀ (D : D7) (S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar) (M : DSModel (D.sp.Y 0) S) (E : Submodule ℂ (MMap M)) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp St) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0))) (ι : GA D (D.sp.Y 0) ≃* St.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ), (∀ T ∈ E, ∀ T' ∈ E, ∃ c : ℂ, ∀ v v' : M.Vec, ∫ x, star (T v (ι.symm x * t)) * T' v' (ι.symm x * t) ∂(muX St) = c * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ) → EvalTieT M μ 𝓕 E St G ι t c → ∀ (e : D.what₂.EE →ₗ[ℂ] E) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St G) (v₀ : M.Vec) (a : ℂ), (∀ F, ((j F : EEC St G) : L2X St) =ᵐ[muX St] fun x => a * ev M v₀ (e F : MMap M) (ι.symm x * t)) → ∃ κ₀ : ℂ, κ₀ ≠ 0 ∧ ∀ F, sEEofTT M μ 𝓕 E St G ι t c (e F) = κ₀ • conjHH St G (j F) := by
  intro D S M E St G μ 𝓕 ι t c hS hT e j v₀ a hj
  have hv := hT.choose_spec.1
  have hj' := fun T => (hT.choose_spec.2.choose_spec T).1
  have hp : ∏ τ, ⟪(hT.choose τ : M.H τ), (hT.choose τ : M.H τ)⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K, hv τ]
    simp
  have hkey := eq_smul_of_eval (m := muX St) (EEC St G) (fun (T : E) (v : M.Vec) x => (T : MMap M) v (ι.symm x * t))
    (fun v v' => ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ) (fun T T' => hS T T.2 T' T'.2) hT.choose v₀ hp
    hT.choose_spec.2.choose hj' e j a hj
  have hs : sEEofTT M μ 𝓕 E St G ι t c
      = (conjHH St G).toLinearMap.comp hT.choose_spec.2.choose.toLinearMap := dif_pos hT
  rw [hs]
  exact exists_conj_scalar (conjHH St G).toLinearMap j.toLinearEquiv.toLinearMap
    (hT.choose_spec.2.choose.toLinearMap.comp e) j.injective _ hkey

end GlobalTheory.Mem.SJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CxFactsOfPrims
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
open Formalism.IndefR.CxPass
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem cxFacts_of_prims : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ), A3.fam3.Ok3 n → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → CxFacts (R.toCx3 F) F.cr (F.eV (R.toCx3 F).zs) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F n hOk hSep hC hP
  let X := R.toCx3 F
  have hKR : X.KFormR := RealDat3.kFormR_of (F := F) hC.base.models
  have hKL : X.KFormL := RealDat3.kFormL_of (F := F) hC.base.models
  have hJR : X.JIsoR F.cv := RealDat3.jIsoR_of (F := F) hC.base.models
  have hJL : X.JIsoL F.cv := RealDat3.jIsoL_of (F := F) hC.base.models
  have hStable : X.zs.Stable :=
    CxData.cutStable X hKR hKL
      (definite_kernel_stable hKR hP.gEquiv.1 hP.hecke.1.choose_spec)
      (lift_kernel_stable hKL hP.gEquiv.2 hP.hecke.2.choose_spec)
      (definite_adjoint_closed hOk hP.heckeR hKR hJR)
      (lift_adjoint_closed hOk hP.heckeL hKL hJL)
  have hWF : (F.fc X.zs).Df1.WF :=
    A3.side_well_formed hOk F.P1 F.ψ1 X.zs hStable hP.block hSep
  have hPos : X.H4pos := ⟨fun _ => hP.posScal.1, hP.posScal.2, RealDat.nP_pos⟩
  have hRatZ : X.RatZ :=
    Formalism.IndefR.Rat.ratZOfTests X F.cv hKR hKL hJR hJL hP.rowTest hP.liftTest
  have hRat : X.RatLev F.cr F.cv true :=
    rationality_at_level_of_equivariance hOk hKR hJR hRatZ hP.gUnit.1 hP.gEquiv.1 true
  have hDn : X.DnLev F.cv true :=
    descent_of_types hOk hKR hJR hRatZ hP.gUnit.1 hP.gEquiv.1 hP.h2P hP.levE.1 hP.levE.2 true
  have hUp : X.UpLev F.cv true :=
    upper_level_of_types hOk hKR hJR hP.gUnit.1 hP.gEquiv.1 hP.levE.1 hP.levE.2 true
  have hGood : X.CoordinatesInGoodPart F.cr F.cv true := definite_coordinates_in_good_part X true
  have hIso : X.IsoR F.cr true := definite_isometry_of_norms hOk hJR ⟨rfl, rfl⟩ true
  have hSubspaces : X.CrdZ F.cr true := definite_coordinates_in_subspaces X true
  have hRows : X.H2 F.cr true ∧ X.H4 F.cr true :=
    cutRows (X := X) F.cr F.cv true hWF hPos hIso hSubspaces hGood hRat hDn hUp
      (RealDat3.thmBop_of (F := F) hP.thmB true) (hP.sumE true)
  exact
    { wf := hWF
      h2 := hRows.1
      pos := hPos
      theta := X.theta_eV F.cr F.cv (F.eV X.zs) hJR hRat hDn hUp hGood (EvTie.evTie_of_ok hOk F X) _ }

end GlobalTheory.Mem.SJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsImNeZeroOfTotallyComplex
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem exists_im_ne_zero_of_totallyComplex {K : Type} [Field K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ) :
    ∃ a, (σ a).im ≠ 0 := by
  by_contra h
  push Not at h
  refine IsTotallyComplex.complexEmbedding_not_isReal σ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext a
  exact Complex.conj_eq_iff_im.2 (h a)

theorem lin_single_cpt {K : Type} [Field K] (σ : K →+* ℂ) {d : ℕ} {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (e : (Fin d → K) ≃ₗ[K] V) (j : V →ₛₗ[σ] W) (x : Fin d → K) :
    lin (fun k => j (e (Pi.single k 1))) (cpt σ x) = j (e x) := by
  rw [lin_apply]
  conv_rhs => rw [pi_eq_sum_univ' x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smulₛₗ, cpt]

theorem rows_eq_rows_level : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t), CxFacts X cr eV → R.RRTie cr → (∀ F, M.eR F ∈ X.EEl true) ∧ (∀ e ∈ X.EEl true, ∃ F, M.eR F = e) ∧ ∀ F, ‖M.eR F‖ = Real.sqrt (X.nP true) * ‖F‖ := by
  intro D Bs A X fc s R cr M eV hX hT
  obtain ⟨L, hT⟩ := hT
  have hn : 0 < X.nP true := hX.pos.2.2 true
  let g := lin (fun k => D.jEE (R.eRR (Pi.single k 1)))
  have hg : ∀ x, g (cpt D.what₂.embLL x) = D.jEE (R.eRR x) := lin_single_cpt _ R.eRR D.jEE
  have hsurj : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← D.jEE_basis.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨cpt D.what₂.embLL (R.eRR.symm (D.div.RR.b i)), by rw [hg, R.eRR.apply_symm_apply]⟩
  have key : ∀ z, M.eR (g z) = X.iC cr true Bs.μ0 (cjv s z) := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← lin_basis (X.iC cr true Bs.μ0), lin_apply, lin_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, M.eR_eq]
    congr 2
    funext i
    by_cases h : i = k <;> simp [cpt, h]
  have hcc : ∀ z : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ, cjv s (cjv s z) = z := by
    intro z
    funext i
    cases s <;> simp [cjv, cj]
  refine ⟨fun F => ?_, fun e he => ?_, fun F => ?_⟩
  · obtain ⟨z, rfl⟩ := hsurj F
    rw [key, ← hX.h2.2.2]
    exact ⟨_, rfl⟩
  · rw [← hX.h2.2.2] at he
    obtain ⟨z, rfl⟩ := he
    exact ⟨g (cjv s z), by rw [key, hcc]⟩
  · obtain ⟨z, rfl⟩ := hsurj F
    rw [key]
    have hd : DenseRange (cpt D.what₂.embLL : (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → D.what₂.LL) → _) :=
      DenseRange.piMap (fun _ => denseRange_of_im_ne_zero D.what₂.embLL (exists_im_ne_zero_of_totallyComplex _))
    have hcj : Continuous (cj s) := by
      cases s
      · exact continuous_id
      · exact Complex.continuous_conj
    have hcv : Continuous fun z : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ => cjv s z :=
      continuous_pi fun i => hcj.comp (continuous_apply i)
    have h1 : Continuous fun z => ‖X.iC cr true Bs.μ0 (cjv s z)‖ :=
      ((LinearMap.continuous_of_finiteDimensional (X.iC cr true Bs.μ0)).comp hcv).norm
    have h2 : Continuous fun z => Real.sqrt (X.nP true) * ‖g z‖ :=
      continuous_const.mul (LinearMap.continuous_of_finiteDimensional g).norm
    refine hd.induction_on z (isClosed_eq h1 h2) fun x => ?_
    have hv : cjv s (cpt D.what₂.embLL x) = cpt Bs.v0.embedding x := by
      funext i
      simp [cjv, cpt, R.twist]
    have hXE : X.XE cr true Bs.v0 = frameOf (X.gramE cr true) := by
      simp [CxData.XE, rowXE, rowFrame, spliceFrame]
    have hli : LinearIndependent ℂ fun i => X.iC cr true Bs.μ0 (Pi.single i 1) :=
      li_of_lin_injective (by rw [lin_basis]; exact hX.h2.1)
    have hm := majAt_gram_smul (X.XE cr true) Bs.v0 _ hli _ (inv_pos.2 hn) hXE x x
    rw [lin_basis] at hm
    rw [hv, hg, ← D.jEE_norm, ← R.v0, normAt_sq_eq_majAt_re, hT.metric, hm, inner_self_eq_norm_sq_to_K,
      ← Real.sqrt_mul hn.le]
    erw [show ((((X.nP true)⁻¹ : ℝ) : ℂ) * ((‖X.iC cr true Bs.μ0 (cpt Bs.v0.embedding x)‖ : ℝ) : ℂ) ^ 2).re =
      (X.nP true)⁻¹ * ‖X.iC cr true Bs.μ0 (cpt Bs.v0.embedding x)‖ ^ 2 by norm_cast]
    rw [mul_inv_cancel_left₀ hn.ne', Real.sqrt_sq (norm_nonneg _)]

end GlobalTheory.Mem.SJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMapReferenceTupleGoodPartOntoRows
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem kOf_apply_self_on {K : Type} [Field K] (σ : K →+* ℂ) (a : K) : kOf σ (σ a) = a := by
  unfold kOf
  have h : ∃ b : K, σ b = σ a := ⟨a, rfl⟩
  rw [dite_eq_left h]
  exact σ.injective h.choose_spec

theorem relMat_self_on {E : Type} [AddCommGroup E] [Module ℂ E] {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] E)
    (hf : Function.Injective f) : relMat f f = 1 := by
  ext i k
  have h : ∃ y, f y = f (Pi.single k 1) := ⟨_, rfl⟩
  have : solve f (f (Pi.single k 1)) = Pi.single k 1 := by
    unfold solve
    rw [dite_eq_left h]
    exact hf h.choose_spec
  simp only [relMat, Matrix.of_apply, this, Matrix.one_apply, Pi.single_apply]

theorem kMat_one_on {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} : kMat σ (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  ext i k
  simp only [kMat, Matrix.map_apply, Matrix.one_apply]
  split_ifs
  · simpa using kOf_apply_self_on σ 1
  · simpa using kOf_apply_self_on σ 0

theorem thetaMap_referenceTuple_goodPart_onto_rows : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t), CxFacts X cr eV → R.IotaRd cr → R.ReadingFormsSpanGoodSubspace → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D Bs A X fc s R cr eV hF hI hV
  have h1 : X.rowMat cr true Bs.μ0 = 1 := by
    unfold CxData.rowMat CxData.rowMatC
    rw [relMat_self_on _ hF.h2.1, kMat_one_on]
  rw [eq_top_iff, ← D.jEE_basis.2, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨x, hx⟩ := R.eRR.surjective (D.div.RR.b i)
  obtain ⟨y, hy⟩ := hF.wf.Pq_surj Bs.μ0 x
  refine ⟨R.jV y, ?_, ?_⟩
  · have : R.jV y ∈ Submodule.span ℂ (Set.range R.jV) := Submodule.subset_span ⟨y, rfl⟩
    rw [hV] at this
    exact this
  · have := hI y
    rw [h1, Matrix.one_mulVec] at this
    exact this.trans (congrArg D.jEE ((congrArg R.eRR hy).trans hx))

end GlobalTheory.Mem.SJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeamExLinCpt
noncomputable section

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem seamEx_lin_cpt {K E : Type} [Field K] [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ) {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] E) (x : Fin n → K) :
    lin (fun k => j (Pi.single k 1)) (cpt σ x) = j x := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lin, cpt, Fintype.linearCombination_apply, map_sum, LinearMap.map_smulₛₗ]

theorem seamEx_coords {K V E ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup E] [Module ℂ E]
    (σ : K →+* ℂ) {n : ℕ} (j : V →ₛₗ[σ] E) (b : Module.Basis ι K V) (e : (Fin n → K) ≃ₗ[K] V)
    (hb : LinearIndependent ℂ (fun i => j (b i)) ∧ Submodule.span ℂ (Set.range (fun i => j (b i))) = ⊤) :
    ∃ c : E ≃ₗ[ℂ] (Fin n → ℂ), ∀ x, c.symm (cpt σ x) = j (e x) := by
  let g : (Fin n → K) →ₛₗ[σ] E := j.comp e.toLinearMap
  let f : (Fin n → ℂ) →ₗ[ℂ] E := lin (fun k => g (Pi.single k 1))
  have hf : ∀ x, f (cpt σ x) = j (e x) := fun x => seamEx_lin_cpt σ g x
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hb.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨cpt σ (e.symm (b i)), by rw [hf]; simp⟩
  haveI : Module.Finite K V := Module.Finite.equiv e
  haveI : Finite ι := Module.Finite.finite_basis b
  haveI : Fintype ι := Fintype.ofFinite ι
  let B : Module.Basis ι ℂ E := Module.Basis.mk hb.1 hb.2.ge
  haveI : Module.Finite ℂ E := Module.Finite.of_basis B
  have hr : Module.finrank ℂ (Fin n → ℂ) = Module.finrank ℂ E := by
    rw [Module.finrank_eq_card_basis B, ← Module.finrank_eq_card_basis b, ← e.finrank_eq]
    simp
  have hinj : Function.Injective f := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).2 hsurj
  exact ⟨(LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).symm, hf⟩

theorem seam_nonempty (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs)
    (s : Bool) (R : Read D X fc s) (cr : Crd A fc) : Nonempty (Seam R cr) := by
  choose cφ hφ using fun u => seamEx_coords D.what₂.embLL (D.jN u) (D.div.Nu u).b (R.eNu u) (D.jN_basis u)
  obtain ⟨c, hc⟩ := seamEx_coords D.what₂.embLL D.jEE D.div.RR.b R.eRR D.jEE_basis
  refine ⟨{ cφ := cφ
            cF := lin (fun k => R.jV (Pi.single k 1))
            eR :=
              { toFun := fun F => X.iC cr true Bs.μ0 (cjv s (c F))
                map_add' := fun F G => ?_
                map_smul' := fun a F => ?_ }
            cφ_eq := hφ
            cF_eq := fun y => seamEx_lin_cpt _ _ y
            eR_eq := fun y => ?_ }⟩
  · rw [← map_add (f := _)]
    congr 1
    funext i
    simp [cjv]
  · rw [← map_smul]
    congr 1
    funext i
    simp [cjv]
  · show X.iC cr true Bs.μ0 (cjv s (c _)) = _
    rw [← hc, LinearEquiv.apply_symm_apply]
    congr 1
    funext i
    simp [cjv, cpt, R.twist]

end GlobalTheory.Mem.SJ

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainTieAndV0Onto
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem chainTie_and_v0Onto :
    ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool)
      (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr), (R.DcPt → M.ChainTie) ∧ (R.ReadingFormsSpanGoodSubspace → M.GoodPartHasComplexCoordinates) := by
  intro D Bs A X fc s R cr M
  refine ⟨fun h u x y => ?_, fun h => ?_⟩
  · rw [M.cφ_eq, M.cF_eq]
    exact (h u x y).symm
  · unfold Seam.GoodPartHasComplexCoordinates
    rw [← h]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, rfl⟩
    exact ⟨_, M.cF_eq y⟩

end GlobalTheory.Mem.SJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadOfMatrixTie
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem sharp_iota_eq (D : D7) (μ : D.what₂.Tup) : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
  unfold RowSide.iota Rows.Data.iota
  rw [PrimeDegreeVariant.sharp_downTo]
  rfl

theorem exists_read_of_matrix_tie (D : D7) {Bs : DefBase D.what₂.LL} {A : DefAmb Bs} (X : CxData A)
    (fc : DefSub A → DefFace Bs) (cr : Crd A fc) (μ : D.what₂.Tup) (hμ : μ = D.what₂.mu0)
    (hv : Bs.v0 = InfinitePlace.mk D.what₂.embLL) {n : ℕ}
    (jA : (Fin n → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb μ)
    (H E : Matrix (Fin n) (Fin n) D.what₂.LL) (V : Matrix (Fin n) (Fin ((fc X.zs).Df1.nV Bs.μ0)) D.what₂.LL)
    (wU : D.what₂.Word → (fc X.zs).Dc.Mem)
    (eNu : ∀ u, (Fin ((fc X.zs).Dc.a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V)
    (eRR : (Fin (X.data cr true).D → D.what₂.LL) ≃ₗ[D.what₂.LL] D.div.RR.V)
    (hF : FormsTie D.what₂.embLL (W := (RowSide.sharp D).Amb μ) jA H E ((RowSide.sharp D).eOp μ))
    (hE : LinearMap.range E.mulVecLin = LinearMap.range V.mulVecLin)
    (hι : ∀ y, (RowSide.sharp D).iota μ (jA (V.mulVec y)) =
      (RowSide.sharp D).jEE (eRR (((X.data cr true).ι Bs.μ0).mulVec (((fc X.zs).Df1.Pq Bs.μ0).mulVec y))))
    (hNu : ∀ u, ∃ L, HLatTie (D.div.Nu u) L ((fc X.zs).Dc.Xc (wU u)) (eNu u)) :
    ∃ Rd : Read D X fc (twAt D.what₂.embLL Bs.v0), HEq Rd.wU wU ∧ HEq Rd.eNu eNu ∧ HEq Rd.eRR eRR ∧
      (∀ y, HEq (Rd.jV y) (jA (V.mulVec y))) ∧ Rd.ReadingFormsSpanGoodSubspace ∧ Rd.IotaRd cr ∧ Rd.NuTie ∧
      ((∃ L, HLatTie D.div.RR L (X.data cr true).XE eRR) → Rd.RRTie cr) ∧
      ((∀ (u : D.what₂.Word) (x : Fin ((fc X.zs).Dc.a (wU u)) → D.what₂.LL)
          (y : Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL),
          D.what₂.embLL ((fc X.zs).Dc.Pt (wU u) Bs.μ0 x y) =
            D.what₂.perCol u μ (D.jN u (eNu u x)) (jA (V.mulVec y))) → Rd.DcPt) := by
  subst hμ
  refine ⟨⟨wU, eNu, eRR, jA.comp V.mulVecLin, hv, fun a => ?_⟩, HEq.rfl, HEq.rfl, HEq.rfl, fun _ => HEq.rfl,
    ?_, fun y => ?_, hNu, fun h => h, fun h => h⟩
  · rw [emb_eq D.what₂.embLL Bs.v0 a, sgAt_mk D.what₂.embLL hv]
  · exact (GlobalTheory.range_op_eq_span_of_formsTie D.what₂.embLL (W := (RowSide.sharp D).Amb D.what₂.mu0) jA H E _ V hF hE).symm
  · have h := hι y
    rw [sharp_iota_eq] at h
    exact h

end GlobalTheory.Mem.SJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ICCptEq
noncomputable section

namespace GlobalTheory.Mem.SJ.RowB

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem iC_cpt_eq {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  have hx : x = ∑ k, x k • (Pi.single k 1 : Fin ((lv (fc X.zs) b).dQ t) → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [CxData.iC, lin, Fintype.linearCombination_apply, map_sum, LinearMap.map_smulₛₗ, cpt, RingHom.id_apply]

theorem theta_eq : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t), CxFacts X cr eV → R.IotaRd cr → ∀ y : Fin ((fc X.zs).Df1.nV Bs.μ0) → D.what₂.LL, X.Θ Bs.μ0 (X.jR Bs.μ0 (eV Bs.μ0 y)) = M.eR (D.what₂.iota D.what₂.mu0 (M.cF (cpt D.what₂.embLL y))) := by
  intro D Bs A X fc s R cr M eV hF hI y
  rw [M.cF_eq, hI y, M.eR_eq, X.rowMat_base cr true hF.h2, Matrix.one_mulVec, iC_cpt_eq, hF.theta y]
  rfl

end GlobalTheory.Mem.SJ.RowB

end
end

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ.KernelJoin

theorem heq_of_reindex {K W Mem : Type} [Field K] (a : Mem → ℕ) {V : W → Type} [∀ u, AddCommGroup (V u)]
    [∀ u, Module K (V u)] {Z : Mem → Type} {Y : W → Type} (b : ∀ x, Fin (a x) → Z x) (g : ∀ u, V u → Y u)
    (w w' : W → Mem) (ν : ∀ u, (Fin (a (w u)) → K) ≃ₗ[K] V u) (ν' : ∀ u, (Fin (a (w' u)) → K) ≃ₗ[K] V u)
    (hw : w = w') (hν : HEq ν ν') (h : ∀ u i, HEq (b (w' u) i) (g u (ν' u (Pi.single i 1)))) :
    ∀ u i, HEq (b (w u) i) (g u (ν u (Pi.single i 1))) := by
  subst hw
  cases hν
  exact h

theorem smul_apply_eq_of_eq {A B : Type} [AddCommGroup B] [Module ℂ B] (f : A → B) {a a' : A} (h : a = a')
    (k κ : ℂ) {b : B} (hb : f a' = κ • b) : k • f a = (k * κ) • b := by
  rw [h, hb, mul_smul]

end GlobalTheory.Mem.SJ.KernelJoin
