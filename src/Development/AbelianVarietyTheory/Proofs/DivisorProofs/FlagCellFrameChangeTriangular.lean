module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelField
noncomputable section

namespace GlobalTheory.FlagMod.LowRank

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

section Alg

theorem initSpan_low {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {m : ℕ} (hm : m ≤ 1) {v v' : Fin m → N}
    (h : initSpan R v m = initSpan R v' m) (i : ℕ) : initSpan R v i = initSpan R v' i := by
  rcases i with _ | i
  · simp [initSpan]
  · have e : {j : Fin m | (j : ℕ) < i + 1} = {j : Fin m | (j : ℕ) < m} := by
      ext j; have := j.2; simp only [Set.mem_ofPred_eq]; omega
    unfold initSpan at h ⊢
    rw [e, h]

end Alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Red

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem initSpan_frVec_top {S : Type} [CommRing S] [Algebra c.F S] (P : FrPt Xo c S) (M : MChart Y)
    (h : ⊤ ≤ (frX P ≫ Y.j) ⁻¹ᵁ M.U) (σ : E →+* ℂ) :
    initSpan S (frVec Y P rfl σ) (Dw.mult σ) = eigLie c (frX P ≫ Y.j) σ := by
  obtain ⟨Λ₀⟩ := MChart.nonempty_lift E H Dw l Xo c O β Y M S (ev _ M.U h) (frX P) (frX_snd P)
    (spMap_ev _ M.hU h).symm
  let Λ : M.Lift (ev _ M.U h) P.x := frX_fst P ▸ Λ₀
  have eΛ : Λ.xF = frX P := eq_frX P Λ.xF_fst Λ.xF_snd
  have hv : ∀ j, Λ.Vec ((vec M _ h).symm (frVec Y P rfl σ j)) (P.u σ j) := fun j =>
    (vec_iff_toModel h Λ eΛ (frX_fst P) rfl _ (P.tan σ j)).2 (LinearEquiv.apply_symm_apply _ _).symm
  have heig := GlobalTheory.Reg.isEigAt_iff_eig E H Dw l Xo c O β Y M S _ P.x Λ σ
  obtain ⟨hex, htan, hco⟩ := GlobalTheory.Reg.vec_bijective E H Dw l Xo c O β Y M S _ P.x Λ
  refine le_antisymm (Submodule.span_le.2 ?_) fun v hv' => ?_
  · rintro _ ⟨j, -, rfl⟩
    rw [← (vec M _ h).apply_symm_apply (frVec Y P rfl σ j)]
    exact (vec_mem_eigLie M _ h σ _).2 ((heig _ _ (hv j)).1 (P.eig σ j))
  · obtain ⟨cv, rfl⟩ := (vec M _ h).surjective v
    obtain ⟨w, hw⟩ := (hex cv).exists
    obtain ⟨a, ha⟩ := (P.basis σ w (htan cv w hw) ((heig cv w hw).2 ((vec_mem_eigLie M _ h σ _).1 hv'))).exists
    have h4 := (VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M S _ P.x Λ _ _ (P.u σ) a w hv).1 ha
    refine mem_initSpan.2 ⟨a, fun j hj => absurd j.2 (not_lt.2 hj), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← (hco w (htan cv w hw)).unique h4 hw, map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]

def ofFrames (hm : ∀ σ, Dw.mult σ ≤ 1) (F : Frames Y (𝟙 Y.X)) (hF : F.TopEigen) : FlagModel Y where
  YY := Y.X
  π := 𝟙 _
  proper := inferInstance
  normal := Y.normal
  flat := by rw [Category.id_comp]; exact Y.flat
  F := F
  dense := by
    have : IsIso (genMap (Y := Y) (𝟙 Y.X)) :=
      ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by rw [Category.id_comp, pullback.condition]),
        by apply pullback.hom_ext <;> simp only [genMap, Category.assoc, pullback.lift_fst, pullback.lift_snd,
          Category.comp_id, Category.id_comp],
        by apply pullback.hom_ext <;> simp only [genMap, Category.assoc, pullback.lift_fst, pullback.lift_snd,
          Category.comp_id, Category.id_comp]⟩
    exact Y.jQ_dense.preimage (genMap (Y := Y) (𝟙 Y.X)).homeomorph.isOpenMap
  top := hF
  rep S _ _ P := by
    refine ⟨frX P ≫ Y.j, ⟨Category.comp_id _, fun S' _ _ ψ P' hP k z' ez hz hx σ i => ?_⟩,
      fun z hz => (Category.comp_id _).symm.trans hz.1⟩
    refine initSpan_low (hm σ) ?_ i
    rw [hF S' _ (frX_snd P') z' hx k hz σ]
    exact initSpan_frVec_top P' _ (F.inM hz hx) σ
  fin K _ _ z := (Set.finite_singleton z).subset fun z' ⟨hx, _⟩ => by simpa using hx

end Red

section Frames

variable {O : Type} [CommRing O] {β : O →+* c.F}

structure Proj (β : O →+* c.F) where
  m : (E →+* ℂ) → ℕ
  a : ∀ σ, Fin (m σ) → 𝓞 E
  κ : ∀ σ, Fin (m σ) → O
  spec : ∀ σ (R : Type) [CommRing R] [Algebra c.F R] (n : ℕ) (ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) R),
    (∀ b : 𝓞 E, ρ b * (∑ k, algebraMap c.F R (β (κ σ k)) • ρ (a σ k)) =
      algebraMap c.F R (embK c σ b) • ∑ k, algebraMap c.F R (β (κ σ k)) • ρ (a σ k)) ∧
    ∀ x : Fin n → R, (∀ b : 𝓞 E, (ρ b).mulVec x = algebraMap c.F R (embK c σ b) • x) →
      (∑ k, algebraMap c.F R (β (κ σ k)) • ρ (a σ k)).mulVec x = x

theorem nonempty_proj_id : Nonempty (Proj (RingHom.id c.F)) := by
  have hemb : Function.Injective (embF (E := E) c) := fun τ τ' h =>
    RingHom.ext fun a => congrArg Subtype.val (RingHom.congr_fun h a)
  choose m a κ h using GlobalTheory.exists_eigen_projector_ringOfIntegers E c.F (embF c) hemb
  exact ⟨⟨m, a, κ, h⟩⟩

variable {Y : Model Xo c β} {S : Type} [CommRing S]

def str (x : Sp S ⟶ Y.X) : O →+* S := (ev (x ≫ Y.s) ⊤ le_top).comp (toΓ O)

theorem str_eq {x : Sp S ⟶ Y.X} {g : O →+* S} (h : x ≫ Y.s = spMap g) : str x = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((spMap_ev_top _).trans h))

theorem ev_str (M : MChart Y) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (o : O) :
    ev x M.U h (str (tau M.hU) o) = str x o := by
  have : str x = (ev x M.U h).comp (str (tau M.hU)) := str_eq (by
    rw [← spMap_comp', str, spMap_ev_top, ← Category.assoc]
    exact congrArg (· ≫ Y.s) (spMap_ev x M.hU h).symm)
  rw [this]; rfl

theorem str_gen [Algebra c.F S] {y : Sp S ⟶ Xo.XF c} (hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (o : O) :
    str (y ≫ Y.j) o = algebraMap c.F S (β o) := by
  rw [str_eq (g := (algebraMap c.F S).comp β) (by
    rw [Model.j, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over,
      ← Category.assoc, hy, spMap_comp'])]
  rfl

variable (p : Proj β)

def pm (M : MChart Y) (σ : E →+* ℂ) : Matrix (Fin M.n) (Fin M.n) Γ(Y.X, M.U) :=
  ∑ k, str (tau M.hU) (p.κ σ k) • M.ρ (p.a σ k)

theorem pm_map (M : MChart Y) (σ : E →+* ℂ) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) :
    (pm p M σ).map (ev x M.U h) = ∑ k, str x (p.κ σ k) • (M.ρ (p.a σ k)).map (ev x M.U h) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pm, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, ev_str]

theorem vec_pm (M : MChart Y) (σ : E →+* ℂ) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (cv : Fin M.n → S) :
    vec M x h (((pm p M σ).map (ev x M.U h)).mulVec cv) =
      ∑ k, str x (p.κ σ k) • actR Y.t.act (p.a σ k) (vec M x h cv) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pm_map, Matrix.sum_mulVec, map_sum]
  simp only [Matrix.smul_mulVec, map_smul, actR_vec]

theorem pm_gen [Algebra c.F S] (M : MChart Y) (σ : E →+* ℂ) {y : Sp S ⟶ Xo.XF c}
    (hy : y ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (h : ⊤ ≤ (y ≫ Y.j) ⁻¹ᵁ M.U) :
    (∀ cv, M.Eig (ev _ M.U h) σ cv ↔ ((pm p M σ).map (ev _ M.U h)).mulVec cv = cv) ∧
      (pm p M σ).map (ev _ M.U h) * (pm p M σ).map (ev _ M.U h) = (pm p M σ).map (ev _ M.U h) := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.Reg.MChart.exists_ringHom_rho E H Dw l Xo c O _ Y M
  obtain ⟨h1, h2⟩ := p.spec σ S M.n ((ev _ M.U h).mapMatrix.comp ρ)
  simp only [RingHom.comp_apply, RingHom.mapMatrix_apply, hρ, ← str_gen (Y := Y) hy, ← pm_map] at h1 h2
  refine ⟨fun cv => ⟨h2 cv, fun hx b => ?_⟩, ?_⟩
  · have := congrArg (fun A => Matrix.mulVec A cv) (h1 b)
    simpa only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, hx] using this
  · ext i j
    have := h2 (fun k => (pm p M σ).map (ev _ M.U h) k j) (fun b => by
      funext k
      exact congrFun (congrFun (h1 b) k) j)
    exact congrFun this i

def GenIn (Y : Model Xo c β) : Prop :=
  ∀ M : MChart Y, ∃ (L : Type) (_ : Field L) (_ : Algebra c.F L) (y : Sp L ⟶ Xo.XF c)
    (h : ⊤ ≤ (y ≫ Y.j) ⁻¹ᵁ M.U), y ≫ pullback.snd _ _ = spMap (algebraMap c.F L) ∧
      Function.Injective (ev (y ≫ Y.j) M.U h)


variable (Y) in
structure ECh where
  M : GChart Y
  V : Y.X.Opens
  le : V ≤ M.U
  u : ∀ σ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult σ)) Γ(Y.X, V)
  w : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin M.n) Γ(Y.X, V)
  wu : ∀ σ, w σ * u σ = 1
  uw : ∀ σ, u σ * w σ = (pm p M.toMChart σ).map (resG Y.X le)

variable {p}

theorem ECh.fix_iff (k : ECh Y p) (σ : E →+* ℂ) (z : Sp S ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ k.V) (h : ⊤ ≤ z ⁻¹ᵁ k.M.U)
    (cv : Fin k.M.n → S) : ((pm p k.M.toMChart σ).map (ev z _ h)).mulVec cv = cv ↔
      ∃ a, ((k.u σ).map (ev z _ hz)).mulVec a = cv := by
  have e : (pm p k.M.toMChart σ).map (ev z _ h) = (k.u σ).map (ev z _ hz) * (k.w σ).map (ev z _ hz) := by
    rw [← Matrix.map_mul, k.uw]
    ext i j
    exact (ev_res z _ hz h _).symm
  rw [e, ← Matrix.mulVec_mulVec]
  refine ⟨fun h => ⟨_, h⟩, ?_⟩
  rintro ⟨a, rfl⟩
  rw [Matrix.mulVec_mulVec (M := (k.w σ).map _), ← Matrix.map_mul, k.wu, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.one_mulVec]


end Frames

section Gen

theorem exists_field (A : Type) [CommRing A] [IsDomain A] :
    ∃ (L : Type) (_ : Field L) (f : A →+* L), Function.Injective f :=
  ⟨FractionRing A, inferInstance, algebraMap _ _, IsFractionRing.injective _ _⟩

theorem genIn_of {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    (h : ∀ (M : MChart Y) (L : Type) [Field L] (f : Γ(Y.X, M.U) →+* L), Function.Injective f →
      ∃ (_ : Algebra c.F L) (y : Sp L ⟶ Xo.XF c),
      y ≫ pullback.snd _ _ = spMap (algebraMap c.F L) ∧ y ≫ Y.j = spMap f ≫ tau M.hU) :
    GenIn Y := fun M => by
  have := M.dom
  obtain ⟨L, _, f, hf⟩ := exists_field Γ(Y.X, M.U)
  obtain ⟨A, y, h1, h2⟩ := h M L f hf
  have hU : ⊤ ≤ (y ≫ Y.j) ⁻¹ᵁ M.U := h2 ▸ le_preimage_comp _ (tau_le M.hU le_rfl)
  refine ⟨L, inferInstance, A, y, hU, h1, ?_⟩
  rw [ev_congr h2 _ _ (h2 ▸ hU), ev_spMap_tau]
  exact hf

theorem spec_generic {A L : Type} [CommRing A] [Field L] (f : A →+* L) (hf : Function.Injective f)
    (q : PrimeSpectrum L) (t : PrimeSpectrum A) : PrimeSpectrum.comap f q ⤳ t := by
  refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
  obtain rfl : q = ⊥ := Subsingleton.elim _ _
  show Ideal.comap f ⊥ ≤ _
  rw [Ideal.comap_bot_of_injective _ hf]
  exact bot_le

theorem genIn_id (Y : Model Xo c (RingHom.id c.F)) : GenIn Y := genIn_of fun M L _ f hi => by
  have := M.dom
  have := Y.jQ_open
  have : IsIso (spMap (RingHom.id c.F)) := by
    rw [show spMap (RingHom.id c.F) = 𝟙 _ from Spec.map_id _]; infer_instance
  have : IsOpenImmersion Y.j := by unfold Model.j; infer_instance
  have hd : Dense (Set.range Y.j) := by
    have := (pullback.fst Y.s (spMap (RingHom.id c.F))).homeomorph.surjective.denseRange.comp Y.jQ_dense
      (pullback.fst Y.s (spMap (RingHom.id c.F))).homeomorph.continuous
    refine this.mono ?_
    rintro _ ⟨t, rfl⟩
    exact ⟨t, Scheme.Hom.comp_apply _ _ _⟩
  let z : Sp L ⟶ Y.X := spMap f ≫ tau M.hU
  have hr : Set.range z ⊆ Set.range Y.j := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hd.inter_open_nonempty (Set.range (tau M.hU))
      M.hU.fromSpec.isOpenEmbedding.isOpen_range ⟨_, (⊥ : PrimeSpectrum Γ(Y.X, M.U)), rfl⟩
    have hs : spMap f q ⤳ t := spec_generic f hi q t
    rw [Scheme.Hom.comp_apply]
    exact (hs.map (tau M.hU).continuous).mem_open Y.j.isOpenEmbedding.isOpen_range ht
  let A : Algebra c.F L := (str z).toAlgebra
  refine ⟨A, IsOpenImmersion.lift Y.j z hr, ?_, IsOpenImmersion.lift_fac _ _ _⟩
  have e : Y.j ≫ Y.s = pullback.snd _ _ := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over,
      show spMap (RingHom.id c.F) = 𝟙 _ from Spec.map_id _, Category.comp_id]
  rw [← e, ← Category.assoc, IsOpenImmersion.lift_fac]
  exact (spMap_ev_top _).symm

end Gen

end GlobalTheory.FlagMod.LowRank
end
end

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

theorem exists_ringEquiv {A : Type} [CommRing A] {Z : Scheme.{0}} (κ : Sp A ⟶ Z) [IsOpenImmersion κ] :
    ∃ θ : A ≃+* Γ(Z, κ.opensRange), spMap θ.toRingHom ≫ κ = (isAffineOpen_opensRange κ).fromSpec := by
  let e := IsOpenImmersion.isoOfRangeEq (isAffineOpen_opensRange κ).fromSpec κ
    (isAffineOpen_opensRange κ).range_fromSpec
  let e' : CommRingCat.of A ≅ Γ(Z, κ.opensRange) := (Scheme.Spec.preimageIso (X := .op _) (Y := .op _) e).unop
  refine ⟨e'.commRingCatIsoToRingEquiv, ?_⟩
  have : spMap e'.commRingCatIsoToRingEquiv.toRingHom = e.hom := Scheme.Spec.map_preimage e.hom
  rw [this]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

structure Atlas (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) where
  B : Type
  fin : Finite B
  k : B → ECh Y p
  aff : ∀ b, IsAffineOpen (k b).V
  cov : ∀ x : Y.X, ∃ b, x ∈ (k b).V
  N : ℕ
  A : ∀ b, Matrix (Fin (N + 1)) (Fin (k b).M.n) Γ(Y.X, (k b).V)
  C : ∀ b, Matrix (Fin (k b).M.n) (Fin (N + 1)) Γ(Y.X, (k b).V)
  CA : ∀ b, C b * A b = 1
  tw : ∀ (S : Type) [CommRing S] (x : Sp S ⟶ Y.X) (b b' : B) (h : ⊤ ≤ x ⁻¹ᵁ (k b).V) (h' : ⊤ ≤ x ⁻¹ᵁ (k b').V)
    (hM : ⊤ ≤ x ⁻¹ᵁ ((k b').M.U ⊓ (k b).M.U)), ∃ a : Sˣ, (A b).map (ev x _ h) =
      (a : S) • ((A b').map (ev x _ h') * (chg (k b').M.toMChart (k b).M.toMChart).map (ev x _ hM))

variable {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)} (A : Atlas Y p)

namespace Atlas

abbrev V (b : A.B) : Y.X.affineOpens := ⟨(A.k b).V, A.aff b⟩

def alpha (b : A.B) : c.F →+* Γ(Y.X, (A.V b).1) := str (tau (A.aff b))

def cv (b : A.B) : Let Dw.mult → Fin (A.N + 1) → Γ(Y.X, (A.V b).1) :=
  fun z r => (A.A b * (A.k b).u z.1) r z.2

def Dv (b : A.B) : Let Dw.mult → Fin (A.N + 1) → Γ(Y.X, (A.V b).1) :=
  fun z r => ((A.k b).w z.1 * A.C b) z.2 r

end Atlas

variable {A}

structure Cells (A : Atlas Y p) {Z : Scheme.{0}} (π : Z ⟶ Y.X)
    (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1))
    (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) : Prop where
  proper : IsProper π
  normal : Geo.Tor.IsNormalScheme Z
  plk : HasPlk (RingHom.id c.F) A.V A.alpha A.cv π g κ
  cover : ∀ z : Z, ∃ b w, z ∈ Set.range (κ b w)
  ext : ∀ (W : Scheme.{0}) (a a' : W ⟶ Z), a ≫ π = a' ≫ π → (∀ en, a ≫ g en = a' ≫ g en) → a = a'

def cellMat (U : Y.X.affineOpens) (σ : E →+* ℂ) : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) (CR Dw.mult U) :=
  Matrix.of (cell MvPolynomial.X σ)

theorem det_cellMat (U : Y.X.affineOpens) (σ : E →+* ℂ) : (cellMat (Dw := Dw) U σ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [cellMat, cell]
  · intro i j hij
    have h1 : ¬ j < i := not_lt.2 (le_of_lt hij)
    have h2 : i ≠ j := ne_of_lt hij
    simp [cellMat, cell, h1, h2]


variable (A) in
abbrev cC (b : A.B) : Γ(Y.X, (A.k b).V) →+* CR Dw.mult (A.V b) := MvPolynomial.C


variable (A) in
def uC (b : A.B) (w : Pm Dw.mult) (σ : E →+* ℂ) :
    Matrix (Fin (A.k b).M.n) (Fin (Dw.mult σ)) (CR Dw.mult (A.V b)) :=
  (((A.k b).u σ).map (cC A b)).submatrix id (w σ) * cellMat (A.V b) σ


variable (A) in
def wC (b : A.B) (w : Pm Dw.mult) (σ : E →+* ℂ) :
    Matrix (Fin (Dw.mult σ)) (Fin (A.k b).M.n) (CR Dw.mult (A.V b)) :=
  (cellMat (A.V b) σ)⁻¹ * (((A.k b).w σ).map (cC A b)).submatrix (w σ) id

theorem wC_mul_uC (b : A.B) (w : Pm Dw.mult) (σ : E →+* ℂ) : wC A b w σ * uC A b w σ = 1 := by
  have h1 : (((A.k b).w σ).map (cC A b)).submatrix (w σ) id * (((A.k b).u σ).map (cC A b)).submatrix id (w σ) = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, ← Matrix.map_mul, (A.k b).wu,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.submatrix_one_equiv]
  have h2 : IsUnit (cellMat (Dw := Dw) (A.V b) σ).det := by rw [det_cellMat]; exact isUnit_one
  calc wC A b w σ * uC A b w σ
      = (cellMat (A.V b) σ)⁻¹ * ((((A.k b).w σ).map (cC A b)).submatrix (w σ) id *
          (((A.k b).u σ).map (cC A b)).submatrix id (w σ)) * cellMat (A.V b) σ := by
        simp only [wC, uC, Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.mul_one, Matrix.nonsing_inv_mul _ h2]

variable {Z : Scheme.{0}} {π : Z ⟶ Y.X} {g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)}
  {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ)


variable (κ) in
def cellθ (k : A.B × Pm Dw.mult) : CR Dw.mult (A.V k.1) ≃+* Γ(Z, (κ k.1 k.2).opensRange) :=
  (exists_ringEquiv (κ k.1 k.2)).choose

theorem spMap_cellθ (k : A.B × Pm Dw.mult) :
    spMap (cellθ κ k).toRingHom ≫ κ k.1 k.2 = (isAffineOpen_opensRange (κ k.1 k.2)).fromSpec :=
  (exists_ringEquiv (κ k.1 k.2)).choose_spec

include hZ in
theorem cell_le (k : A.B × Pm Dw.mult) : (κ k.1 k.2).opensRange ≤ π ⁻¹ᵁ (A.k k.1).M.U := by
  rintro _ ⟨y, rfl⟩
  have e : κ k.1 k.2 ≫ π = cbase Dw.mult (A.V k.1) := hZ.plk.base _ _
  have h : (κ k.1 k.2 ≫ π) y ∈ ((A.V k.1).1 : Set Y.X) := by
    rw [e, cbase, Scheme.Hom.comp_apply]
    exact (A.V k.1).2.range_fromSpec.le ⟨_, rfl⟩
  exact (A.k k.1).le (by rw [Scheme.Hom.comp_apply] at h; exact h)

def FlagCellFrameChangeTriangular : Prop :=
  ∀ (k k' : A.B × Pm Dw.mult) (σ : E →+* ℂ), ∃ B : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ))
      Γ(Z, (κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange), B.BlockTriangular id ∧
    (chg (A.k k.1).M.toMChart (A.k k'.1).M.toMChart).map
        (π.appLE ((A.k k.1).M.U ⊓ (A.k k'.1).M.U) ((κ k.1 k.2).opensRange ⊓ (κ k'.1 k'.2).opensRange)
          (inf_le_inf (cell_le hZ k) (cell_le hZ k'))).hom *
      ((uC A k'.1 k'.2 σ).map (cellθ κ k')).map (resG Z inf_le_right) =
      ((uC A k.1 k.2 σ).map (cellθ κ k)).map (resG Z inf_le_left) * B

def cellFrames (ht : FlagCellFrameChangeTriangular hZ) : Frames Y π where
  J := A.B × Pm Dw.mult
  U k := (κ k.1 k.2).opensRange
  cover := eq_top_iff.2 fun z _ => by
    obtain ⟨b, w, h⟩ := hZ.cover z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(b, w), h⟩
  M k := (A.k k.1).M
  le := cell_le hZ
  u k σ := (uC A k.1 k.2 σ).map (cellθ κ k)
  split k σ := ⟨(wC A k.1 k.2 σ).map (cellθ κ k), by
    rw [← Matrix.map_mul, wC_mul_uC, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  tri := ht

end GlobalTheory.FlagMod.FieldFlag
