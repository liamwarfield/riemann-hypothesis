module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.CxPts
open scoped ComplexOrder

namespace GlobalTheory.LieMet

attribute [local instance] Over.cartesianMonoidalCategory

section Gram

variable {M : Type} [AddCommGroup M] [Module ℂ M] {n : Type} [Fintype n]

def gramOf (h : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (u : n → M) : Matrix n n ℂ := of fun a b => h (u b) (u a)

theorem form_sum (h : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (u : n → M) (v w : n → ℂ) :
    h (∑ a, v a • u a) (∑ a, w a • u a) = star w ⬝ᵥ gramOf h u *ᵥ v := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul,
    dotProduct, mulVec, gramOf, of_apply, Pi.star_apply, Finset.mul_sum, RCLike.star_def]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

def diagForm (b : Module.Basis n ℂ M) (a : n → ℝ) : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => ∑ i, a i * (b.repr v i * starRingEnd ℂ (b.repr w i)))
    (fun _ _ _ => by simp [add_mul, mul_add, Finset.sum_add_distrib])
    (fun _ _ _ => by
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun _ _ _ => by simp [mul_add, Finset.sum_add_distrib])
    (fun _ _ _ => by simp [Finset.mul_sum, mul_left_comm])

theorem diagForm_apply (b : Module.Basis n ℂ M) (a : n → ℝ) (v w : M) :
    diagForm b a v w = ∑ i, a i * (b.repr v i * starRingEnd ℂ (b.repr w i)) := rfl

theorem diagForm_symm (b : Module.Basis n ℂ M) (a : n → ℝ) (v w : M) :
    diagForm b a w v = starRingEnd ℂ (diagForm b a v w) := by
  simp [diagForm_apply, mul_comm]

theorem diagForm_pos (b : Module.Basis n ℂ M) {a : n → ℝ} (ha : ∀ i, 0 < a i) {v : M} (hv : v ≠ 0) :
    0 < (diagForm b a v v).re := by
  obtain ⟨i, hi⟩ := DFunLike.ne_iff.1 (b.repr.map_ne_zero_iff.2 hv)
  simp only [diagForm_apply, Complex.mul_conj, ← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
  exact Finset.sum_pos' (fun j _ => mul_nonneg (ha j).le (Complex.normSq_nonneg _))
    ⟨i, Finset.mem_univ _, mul_pos (ha i) (Complex.normSq_pos.2 hi)⟩

variable [DecidableEq n]

def dualGram (M : Matrix n n ℂ) : Matrix n n ℂ := M⁻¹ᵀ

theorem dualGram_posDef {A : Matrix n n ℂ} (hA : A.PosDef) : (dualGram A).PosDef := hA.inv.transpose

theorem dualGram_conj (A T : Matrix n n ℂ) : dualGram (Tᴴ * A * T) = (T⁻¹ᵀ)ᴴ * dualGram A * T⁻¹ᵀ := by
  simp only [dualGram, Matrix.mul_inv_rev, transpose_mul, Matrix.mul_assoc, ← conjTranspose_nonsing_inv]
  rfl

theorem dualGram_smul_one {a : ℂ} (ha : a ≠ 0) : dualGram (a • (1 : Matrix n n ℂ)) = a⁻¹ • 1 := by
  rw [dualGram, inv_eq_left_inv (B := a⁻¹ • 1) (by simp [smul_smul, ha]), transpose_smul, transpose_one]

end Gram

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}}
  {t : SAB H X} {t' : SAB H X'} {S S' : Type} [CommRing S] [CommRing S'] {x : Sp S ⟶ X}

def tanOf {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) : TanM x t.G := mkT (ovT hv) (smT_zero_ovT hv)

@[simp] theorem left_tanOf {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) : (tv (tanOf hv)).left = v := rfl

theorem isTan_tv (v : TanM x t.G) : IsTanAtG t x (tv v).left := isTanAtG_of (t := t) (tv v) (tv_mem v)

theorem tan_ext {v w : TanM x t.G} (h : (tv v).left = (tv w).left) : v = w := tanM_ext (Over.OverMorphism.ext h)

theorem isComb_iff {m : ℕ} (u : Fin m → TanM x t.G) (a : Fin m → S) (w : TanM x t.G) :
    IsCombAtG t x (fun i => (tv (u i)).left) a (tv w).left ↔ w = ∑ i, a i • u i := by
  have e : tv (∑ i, a i • u i) = combT x (fun i => tv (u i)) a := by
    classical
    unfold combT
    induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
    | empty => rfl
    | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, tv_add, ih]; rfl
  refine (isCombAtG_iff t x (fun i => tv (u i)) a _).trans ?_
  rw [← e]
  exact ⟨fun h => (tan_ext h).symm, fun h => h ▸ rfl⟩

section Push

variable {f : X' ⟶ X} (m : SABMap t' t f) (x' : Sp S ⟶ X') (hx : x' ≫ f = x)


include hx in
theorem isTan_push {v : Sp (DualNumber S) ⟶ t'.G.left} (hv : IsTanAtG t' x' v) : IsTanAtG t x (v ≫ m.φ) := by
  subst hx
  exact ⟨by rw [Category.assoc, m.cart.1.w, ← Category.assoc, hv.1, Category.assoc],
    by rw [← Category.assoc, hv.2]; exact (grpPull_one m.cart (Over.mk x')).symm⟩

def pushL : TanM x' t'.G →ₗ[S] TanM x t.G where
  toFun v := tanOf (isTan_push m x' hx (isTan_tv v))
  map_add' v w := tan_ext (by
    subst hx
    have e : (overAt x' (DualNumber S)).hom ≫ f = (overAt (x' ≫ f) (DualNumber S)).hom := Category.assoc _ _ _
    have key : ∀ (g : Sp (DualNumber S) ⟶ X) (e : (overAt x' (DualNumber S)).hom ≫ f = g) (a b : Over.mk g ⟶ t.G),
        a.left = (tv v).left ≫ m.φ → b.left = (tv w).left ≫ m.φ → (a * b).left = (tv v * tv w).left ≫ m.φ := by
      rintro _ rfl a b ha hb
      exact m.cart.2 _ _ _ a b ha hb
    exact (key _ e _ _ rfl rfl).symm)
  map_smul' a v := tan_ext (Category.assoc _ _ _)

theorem pushL_bijective : Function.Bijective (pushL m x' hx) := by
  refine ⟨fun v w h => tan_ext (m.cart.1.hom_ext (congrArg (fun z => (tv z).left) h)
    ((isTan_tv v).1.trans (isTan_tv w).1.symm)), fun w => ?_⟩
  subst hx
  have hw : (tv w).left ≫ t.G.hom = (spMap (algebraMap S (DualNumber S)) ≫ x') ≫ f :=
    (isTan_tv w).1.trans (Category.assoc _ _ _).symm
  have e : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 (Sp S) := by
    rw [← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x => by simp [TrivSqZeroExt.algebraMap_eq_inl]))
  refine ⟨tanOf (v := m.cart.1.lift _ _ hw) ⟨m.cart.1.lift_snd _ _ _, m.cart.1.hom_ext ?_ ?_⟩,
    tan_ext (m.cart.1.lift_fst _ _ _)⟩
  · rw [Category.assoc, m.cart.1.lift_fst, (isTan_tv w).2]
    exact grpPull_one m.cart (Over.mk x')
  · rw [Category.assoc, m.cart.1.lift_snd, ← Category.assoc, e, Category.id_comp]
    exact (Over.w (1 : Over.mk x' ⟶ t'.G)).symm

def pushE : TanM x' t'.G ≃ₗ[S] TanM x t.G := LinearEquiv.ofBijective _ (pushL_bijective m x' hx)

theorem left_pushE (v : TanM x' t'.G) : (tv (pushE m x' hx v)).left = (tv v).left ≫ m.φ := rfl

theorem pushE_act (a : 𝓞 E) (v : TanM x' t'.G) :
    pushE m x' hx (actR t'.act a v) = actR t.act a (pushE m x' hx v) :=
  tan_ext (by
    show ((tv v).left ≫ (t'.act.act a).left) ≫ m.φ = ((tv v).left ≫ m.φ) ≫ (t.act.act a).left
    rw [Category.assoc, Category.assoc, m.act])

end Push

theorem isTan_map (φ : S →+* S') {x' : Sp S' ⟶ X} (hx : spMap φ ≫ x = x') {v : Sp (DualNumber S) ⟶ t.G.left}
    (hv : IsTanAtG t x v) : IsTanAtG t x' (spMap (dualMap φ) ≫ v) := by
  subst hx
  constructor
  · rw [Category.assoc, hv.1, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
  · have e : spMap (TrivSqZeroExt.fstHom S' S' S').toRingHom ≫ spMap (dualMap φ) =
        spMap φ ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext (RingHom.ext fun a => by simp [dualMap])
    rw [← Category.assoc, e, Category.assoc, hv.2]
    exact congrArg (fun z => z.left)
      (MonObj.comp_one (M := t.G) (Over.homMk (U := Over.mk (spMap φ ≫ x)) (V := Over.mk x) (spMap φ) rfl))

def IsEig {y : Sp ℂ ⟶ X} (ρ : E →+* ℂ) (v : TanM y t.G) : Prop := ∀ a : 𝓞 E, actR t.act a v = ρ a • v

def IsBlockMetric {y : Sp ℂ ⟶ X} (h : TanM y t.G →ₗ[ℂ] TanM y t.G →ₗ⋆[ℂ] ℂ) : Prop :=
  (∀ v w, h w v = starRingEnd ℂ (h v w)) ∧ (∀ v, v ≠ 0 → 0 < (h v v).re) ∧
    ∀ (ρ ρ' : E →+* ℂ) v w, ρ ≠ ρ' → IsEig ρ v → IsEig ρ' w → h v w = 0

theorem IsBlockMetric.gram_posDef {y : Sp ℂ ⟶ X} {h : TanM y t.G →ₗ[ℂ] TanM y t.G →ₗ⋆[ℂ] ℂ} (hh : IsBlockMetric h)
    {n : Type} [Fintype n] {u : n → TanM y t.G} (hu : LinearIndependent ℂ u) : (gramOf h u).PosDef := by
  refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun v hv => ?_⟩
  · ext a b
    exact (hh.1 _ _).symm
  · rw [← form_sum]
    refine Complex.pos_iff.2 ⟨hh.2.1 _ fun h0 => hv (funext (Fintype.linearIndependent_iff.1 hu v h0)), ?_⟩
    exact (Complex.conj_eq_iff_im.1 (hh.1 _ _).symm).symm

instance finite_tanM (y : Sp ℂ ⟶ X) : Module.Finite ℂ (TanM y t.G) := by
  obtain ⟨n, D, hD, h⟩ := LieLocBasis.exists_lie_basis_stable E H X t ℂ y
  have e : spMap (RingHom.id ℂ) ≫ y = y := by
    rw [show spMap (RingHom.id ℂ) = 𝟙 _ from Spec.map_id _, Category.id_comp]
  refine Module.finite_def.2 (Submodule.fg_def.2 ⟨Set.range fun i => tanOf (isTan_map _ e (hD i)),
    Set.finite_range _, top_unique fun w _ => ?_⟩)
  have h' := h ℂ (RingHom.id ℂ) (tv w).left
  rw [e] at h'
  obtain ⟨a, ha, -⟩ := h' (isTan_tv w)
  rw [(isComb_iff (fun i => tanOf (isTan_map _ e (hD i))) a w).1 ha]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)


variable (t) in
theorem exists_isBlockMetric (y : Sp ℂ ⟶ X) : ∃ h : TanM y t.G →ₗ[ℂ] TanM y t.G →ₗ⋆[ℂ] ℂ, IsBlockMetric h := by
  classical
  let χ : (E →+* ℂ) → (𝓞 E →+* ℂ) := fun τ => τ.comp (algebraMap (𝓞 E) E)
  obtain ⟨α, hα, -⟩ := exists_sepElt (RingHom.id ℂ) χ fun _ _ => rfl
  let g := diagForm (Module.finBasis ℂ (TanM y t.G)) fun _ => 1
  let e := proj (actR (x0 := y) t.act) χ α
  have he : ∀ ρ v, IsEig ρ v → ∀ τ, τ ≠ ρ → e τ v = 0 := fun ρ v hv τ hτ => by
    have := proj_sum_eig (actR (x0 := y) t.act) χ α hα (Pi.single ρ v) (fun τ' a => by
      by_cases h : τ' = ρ
      · subst h; rw [Pi.single_eq_same]; exact hv a
      · simp [Pi.single_eq_of_ne h]) τ
    rwa [Finset.sum_pi_single', if_pos (Finset.mem_univ _), Pi.single_eq_of_ne hτ] at this
  have hf : ∀ v w, (∑ τ, (g.compl₂ (e τ)).comp (e τ)) v w = ∑ τ, g (e τ v) (e τ w) := fun v w => by
    simp [LinearMap.sum_apply]
  refine ⟨∑ τ, (g.compl₂ (e τ)).comp (e τ), fun v w => ?_, fun v hv => ?_, fun ρ ρ' v w h hv hw => ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [hf, hf, map_sum]
    exact Finset.sum_congr rfl fun τ _ => diagForm_symm _ _ _ _
  · obtain ⟨τ, hτ⟩ : ∃ τ, e τ v ≠ 0 := by
      by_contra! h
      have := LinearMap.congr_fun (sum_proj (actR (x0 := y) t.act) χ α hα) v
      rw [LinearMap.sum_apply, Finset.sum_eq_zero fun τ _ => h τ] at this
      exact hv this.symm
    rw [hf, Complex.re_sum]
    refine Finset.sum_pos' (fun τ' _ => ?_) ⟨τ, Finset.mem_univ _, diagForm_pos _ (fun _ => one_pos) hτ⟩
    by_cases h : e τ' v = 0
    · simp [h]
    · exact (diagForm_pos _ (fun _ => one_pos) h).le
  · rw [hf]
    refine Finset.sum_eq_zero fun τ _ => ?_
    by_cases h1 : τ = ρ
    · rw [he ρ' w hw τ (h1 ▸ h), map_zero]
    · rw [he ρ v hv τ h1, map_zero, LinearMap.zero_apply]

variable {k : Type} [CommRing k] {Z : Scheme.{0}} {p : Z ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem spMap_evHom {V : Z.affineOpens} {y : CxPts p σ} (hy : y ∈ ptsIn p σ V.1) :
    spMap (evHom hy) ≫ LogKS.chart V = y.1 := GlobalTheory.Points.specMap_valMap_fromSpec V.2 y.1 hy

def valAt (f : Z ⟶ X) {V : Z.affineOpens} (v : TanM (LogKS.chart V ≫ f) t.G) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ V.1) : TanM (y.1 ≫ f) t.G :=
  tanOf (isTan_map (evHom hy) (by rw [← Category.assoc, spMap_evHom]) (isTan_tv v))

def IsLieMetric (t : SAB H X) (f : Z ⟶ X) (R : AnRead p σ D)
    (h : ∀ y : CxPts p σ, TanM (y.1 ≫ f) t.G →ₗ[ℂ] TanM (y.1 ≫ f) t.G →ₗ⋆[ℂ] ℂ) : Prop :=
  (∀ y, IsBlockMetric (h y)) ∧ ∀ (V : Z.affineOpens) (v w : TanM (LogKS.chart V ≫ f) t.G),
    ∃ g : CxPts p σ → ℂ, R.SmoothOn (ptsIn p σ V.1) (fun y => (g y).re) ∧
      R.SmoothOn (ptsIn p σ V.1) (fun y => (g y).im) ∧
      ∀ y (hy : y ∈ ptsIn p σ V.1), g y = h y (valAt f v hy) (valAt f w hy)

theorem smoothOn_dim_zero (hD : D = 0) (R : AnRead p σ D) (T : Set (CxPts p σ)) (g : CxPts p σ → ℝ) :
    R.SmoothOn T g := fun i => by
  subst hD
  exact contDiffOn_const.congr fun v _ => congrArg (g ∘ (R.chart i).e.symm) (Subsingleton.elim v 0)

theorem isLieMetric_dim_zero (hD : D = 0) (f : Z ⟶ X) (R : AnRead p σ D)
    {h : ∀ y : CxPts p σ, TanM (y.1 ≫ f) t.G →ₗ[ℂ] TanM (y.1 ≫ f) t.G →ₗ⋆[ℂ] ℂ} (hh : ∀ y, IsBlockMetric (h y)) :
    IsLieMetric t f R h := by
  classical
  exact ⟨hh, fun V v w => ⟨fun y => if hy : y ∈ ptsIn p σ V.1 then h y (valAt f v hy) (valAt f w hy) else 0,
    smoothOn_dim_zero hD R _ _, smoothOn_dim_zero hD R _ _, fun y hy => dif_pos hy⟩⟩

end GlobalTheory.LieMet
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTuple
noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure RowsRest (B : Base) (C : Cols B) where
  muAt : B.places.Pl → C.Tup
  muAt_conj : ∀ w, muAt (B.places.conj w) = muAt w
  muTw : B.places.Pl → C.Tup
  muTw_conj : ∀ w, muTw (B.places.conj w) = muTw w
  muAt_or : ∀ w, muAt w = C.mu0 ∨ muAt w = muTw w
  EE : Type
  [instEE : NormedAddCommGroup EE]
  [instEEi : InnerProductSpace ℂ EE]
  [instEEf : FiniteDimensional ℂ EE]
  Drows : ℕ
  onb : OrthonormalBasis (Fin Drows) ℂ EE
  Dall : ℕ
  delp : ℝ
  delp_le_one : delp ≤ 1
  D_eq : (Drows : ℝ) = (1 - delp) * Dall
  EE0 : Type
  [instEE0 : NormedAddCommGroup EE0]
  [instEE0i : InnerProductSpace ℂ EE0]
  [instEE0f : FiniteDimensional ℂ EE0]
  D0 : ℕ
  onb0 : OrthonormalBasis (Fin D0) ℂ EE0
  FT : Type
  [instFT : Fintype FT]
  [instFTd : DecidableEq FT]
  ft : Fin Drows → FT
  ft0 : Fin D0 → FT
  Amb : C.Tup → Type
  [instAmb : ∀ μ, NormedAddCommGroup (Amb μ)]
  [instAmbi : ∀ μ, InnerProductSpace ℂ (Amb μ)]
  [instAmbf : ∀ μ, FiniteDimensional ℂ (Amb μ)]
  Mult : C.Tup → ℕ → Type
  [instMult : ∀ μ j, NormedAddCommGroup (Mult μ j)]
  [instMulti : ∀ μ j, InnerProductSpace ℂ (Mult μ j)]
  [instMultf : ∀ μ j, FiniteDimensional ℂ (Mult μ j)]
  multZero : ∀ μ, Mult μ 0 ≃ₗᵢ[ℂ] EE
  multTop : ∀ μ, Mult μ B.R.m ≃ₗᵢ[ℂ] Amb μ
  io : ∀ μ j, Mult μ (j + 1) →ₗ[ℂ] Mult μ j
  Mtilde : ∀ μ, Rows.OLat B.O (B.embLL.comp B.OtoLL) (Amb μ)
  eOp : ∀ μ, Amb μ →ₗ[ℂ] Amb μ
  eOp_idem : ∀ μ, eOp μ ∘ₗ eOp μ = eOp μ
  eOp_sa : ∀ μ, (eOp μ).IsSymmetric
  Mu : B.Word → Type
  [instMu : ∀ u, NormedAddCommGroup (Mu u)]
  [instMui : ∀ u, InnerProductSpace ℂ (Mu u)]
  [instMuf : ∀ u, FiniteDimensional ℂ (Mu u)]
  perCol : ∀ u (μ : C.Tup), Mu u → Amb μ → ℂ
  Bu : ∀ u, Mu u → EE → ℂ
  ze : B.Word → C.Tup → B.LLˣ
  rowsRest_wordColumnUnit_baseTuple : ∀ u, ze u C.mu0 = 1
  Mj : ℕ → Type
  [instMj : ∀ j, NormedAddCommGroup (Mj j)]
  [instMji : ∀ j, InnerProductSpace ℂ (Mj j)]
  [instMjf : ∀ j, FiniteDimensional ℂ (Mj j)]
  MjLat : ∀ j, Rows.OLat B.O (B.embLL.comp B.OtoLL) (Mj j)
  kaBig : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ
  kaSmall : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ
  Mt : C.Tup → ℕ → Type
  [instMt : ∀ μ j, NormedAddCommGroup (Mt μ j)]
  [instMti : ∀ μ j, InnerProductSpace ℂ (Mt μ j)]
  [instMtf : ∀ μ j, FiniteDimensional ℂ (Mt μ j)]
  MtLat : ∀ μ j, Rows.OLat B.O (B.embLL.comp B.OtoLL) (Mt μ j)
  MtL : C.Tup → ℕ → Type
  [instMtL : ∀ μ j, AddCommGroup (MtL μ j)]
  [instMtLm : ∀ μ j, Module B.LL (MtL μ j)]
  jMt : ∀ μ j, MtL μ j →ₛₗ[B.embLL] Mt μ j
  jMt_basis : ∀ μ j, ∀ b : Module.Basis (Module.Free.ChooseBasisIndex B.LL (MtL μ j)) B.LL (MtL μ j),
    LinearIndependent ℂ (fun i => jMt μ j (b i)) ∧ Submodule.span ℂ (Set.range (fun i => jMt μ j (b i))) = ⊤
  MtLat_sub : ∀ μ j, ∀ x ∈ (MtLat μ j).gen, x ∈ Set.range (jMt μ j)
  eMt : ∀ μ j, Mt μ j →ₗ[ℂ] Mt μ j
  eMt_idem : ∀ μ j, eMt μ j ∘ₗ eMt μ j = eMt μ j
  eMt_sa : ∀ μ j, (eMt μ j).IsSymmetric
  eMt_LL : ∀ μ j (x : MtL μ j), ∃ y : MtL μ j, jMt μ j y = eMt μ j (jMt μ j x)
  thetaP : ∀ μ j, Mt μ j →ₗ[ℂ] Mj j
  isot : ∀ j, FT → Submodule ℂ (Mj j)
  lamP : C.Tup → ℕ → FT → ℝ
  Ij : C.Tup → ℕ → B.places.Pl → ℤ
  jw : C.Tup → ℕ → B.places.Pl → ℤ
  etaJ : ℕ → B.places.Pl → ℚ
  etaJ_nonneg : ∀ j w, 0 ≤ etaJ j w
  shaLen : ℕ → ℕ → ℚ
  shaLen_nonneg : ∀ l e, 0 ≤ shaLen l e
  eMu : ∀ u, Mu u ≃ₗ[ℂ] (C.mem u).A.Mram
  eMt0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] Amb C.mu0
  perCol_base_eq_PtilCol : ∀ u (φ : Mu u) (F : Amb C.mu0),
    perCol u C.mu0 φ F = (C.mem u).P.PtilCol ((eMu u φ : (C.mem u).A.Mram) :
      (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) ((eMt0 u).symm F)
  Bu_linL : ∀ u (F : EE), IsLinearMap ℂ (fun φ : Mu u => Bu u φ F)
  Bu_linR : ∀ u (φ : Mu u), IsLinearMap ℂ (fun F : EE => Bu u φ F)
  eMtTw : ∀ u μ, (C.PTw u μ).Mt ≃ₗ[ℂ] Amb μ
  perCol_tie : ∀ u μ, μ ≠ C.mu0 → ∀ (φ : Mu u) (F : Amb μ), perCol u μ φ F =
    (C.PTw u μ).PtilCol (C.e0Tw u μ ((eMu u φ : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ))
      ((eMtTw u μ).symm F)
  eMu_isom : ∀ u (φ ψ : Mu u), inner ℂ φ ψ =
    (C.fm u).ipC 0 ((eMu u φ : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ)
      ((eMu u ψ : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ)

attribute [instance] RowsRest.instEE RowsRest.instEEi RowsRest.instEEf RowsRest.instEE0 RowsRest.instEE0i RowsRest.instEE0f RowsRest.instFT RowsRest.instFTd RowsRest.instAmb RowsRest.instAmbi RowsRest.instAmbf RowsRest.instMult RowsRest.instMulti RowsRest.instMultf RowsRest.instMu RowsRest.instMui RowsRest.instMuf RowsRest.instMj RowsRest.instMji RowsRest.instMjf RowsRest.instMt RowsRest.instMti RowsRest.instMtf RowsRest.instMtL RowsRest.instMtLm

@[reducible] def RowsRest.what₂ {B : Base} {C : Cols B} (W : RowsRest B C) : Rows.Data B.R where
  LL := B.LL
  embLL := B.embLL
  places := B.places
  O := B.O
  OtoLL := B.OtoLL
  Tau := Tau B.R
  card_Tau := card_Tau B.host
  Tup := C.Tup
  mu0 := C.mu0
  muStar := C.muStar
  muStar' := C.muStar'
  Dstar := B.Dstar
  restRowsFiniteGroupCard := B.toPre.restRowsFiniteGroupCard
  restRowsFiniteGroupCard_pos := B.toPre.restRowsFiniteGroupCard_pos
  Word := B.Word
  muAt := W.muAt
  muAt_conj := W.muAt_conj
  muTw := W.muTw
  muTw_conj := W.muTw_conj
  muAt_or := W.muAt_or
  EE := W.EE
  Drows := W.Drows
  onb := W.onb
  Dall := W.Dall
  delp := W.delp
  delp_le_one := W.delp_le_one
  D_eq := W.D_eq
  EE0 := W.EE0
  D0 := W.D0
  onb0 := W.onb0
  FT := W.FT
  ft := W.ft
  ft0 := W.ft0
  Amb := W.Amb
  Mult := W.Mult
  multZero := W.multZero
  multTop := W.multTop
  io := W.io
  Mtilde := W.Mtilde
  eOp := W.eOp
  eOp_idem := W.eOp_idem
  eOp_sa := W.eOp_sa
  Mu := W.Mu
  perCol := W.perCol
  Bu := W.Bu
  ze := W.ze
  rowsRest_wordColumnUnit_baseTuple := W.rowsRest_wordColumnUnit_baseTuple
  Mj := W.Mj
  MjLat := W.MjLat
  kaBig := W.kaBig
  kaSmall := W.kaSmall
  Mt := W.Mt
  MtLat := W.MtLat
  MtL := W.MtL
  jMt := W.jMt
  jMt_basis := W.jMt_basis
  MtLat_sub := W.MtLat_sub
  eMt := W.eMt
  eMt_idem := W.eMt_idem
  eMt_sa := W.eMt_sa
  eMt_LL := W.eMt_LL
  thetaP := W.thetaP
  isot := W.isot
  lamP := W.lamP
  Ij := W.Ij
  jw := W.jw
  etaJ := W.etaJ
  etaJ_nonneg := W.etaJ_nonneg
  shaLen := W.shaLen
  shaLen_nonneg := W.shaLen_nonneg

instance {B : Base} {C : Cols B} (W : RowsRest B C) : NumberField W.what₂.LL := B.nfLL
instance {B : Base} {C : Cols B} (W : RowsRest B C) : StarRing W.what₂.LL := B.starLL

end GlobalTheory.Mem

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ResCharThetaJetPlaceDegOne
noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

structure GJStage (B : Base) (C : Cols B) where
  vol : @HSpace B.host.E _ _ B.host.cmStar → ℝ
  vol_pos : ∀ W, 0 < vol W
  cd : CDHaar
  jet : ThetaJet B.R B.host
  jetU : jet.Sit → B.Word
  jetL : ∀ i, (C.mem (jetU i)).C.cls (jet.jOf i - 1)
  jetL' : ∀ i, (C.mem (jetU i)).C.cls (jet.jOf i)
  jetW : jet.Sit → B.places.Pl
  jetW_l : ∀ i, B.places.resChar (jetW i) = (jet.loc i).l
  jetTau : ∀ i, ZMod (jet.loc i).d → (Tau B.R)
  jetW1 : jet.Sit1 → B.places.Pl
  resChar_thetaJetPlaceDegOne : ∀ i, B.places.resChar (jetW1 i) = (jet.loc1 i).l
  jetTau1 : jet.Sit1 → (Tau B.R)
  jetU1 : jet.Sit1 → B.Word
  jetL1 : ∀ i, (C.mem (jetU1 i)).C.cls (jet.j1Of i - 1)
  jetL1' : ∀ i, (C.mem (jetU1 i)).C.cls (jet.j1Of i)
  gx : GlobalExtra B.LL (Tau B.R)
  gat : ∀ u (w : B.places.Pl), GIdx B.host (C.mem u).A.T (B.places.resChar w) →
    Formalism.MainNotions.G.GAtP (B.places.resChar w)
  gat_d : ∀ u w h, (gat u w h).d = Module.finrank ℂ (C.mem u).A.Mu0

end GlobalTheory.Mem

end
end
