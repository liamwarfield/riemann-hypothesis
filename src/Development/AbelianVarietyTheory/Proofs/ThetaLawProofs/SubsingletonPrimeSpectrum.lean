module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding IsTan
open ReciprocityTheory.ChartRestriction.G.Chart (sp IsTan fstD scaleD prodPts isTan_iff isLieComb_iff comp_one' isTan_mul isTan_one
  isTan_scale)
open GlobalTheory.SqZero
open TrivSqZeroExt (inl inr)

namespace GlobalTheory.UnifDifferential

attribute [local instance] Over.cartesianMonoidalCategory

section Pull

variable {R : Type} [CommRing R] {A : Over (Spec (CommRingCat.of R))}
  {S S' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']

def pullFn (y : sp (R₀ := R) S ⟶ A) (U : A.left.Opens) (h : ⊤ ≤ y.left ⁻¹ᵁ U) (f : Γ(A.left, U)) : S :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((y.left.appLE U ⊤ h).hom f)

theorem pullFn_comp (φ : S →ₐ[R] S') (y : sp (R₀ := R) S ⟶ A) (y' : sp (R₀ := R) S' ⟶ A)
    (e : y' = Chart.spMap φ ≫ y) (U : A.left.Opens) (h : ⊤ ≤ y.left ⁻¹ᵁ U)
    (h' : ⊤ ≤ y'.left ⁻¹ᵁ U) (f : Γ(A.left, U)) :
    pullFn y' U h' f = φ (pullFn y U h f) := by
  subst e
  have e : (Chart.spMap φ ≫ y).left.appLE U ⊤ h' =
      y.left.appLE U ⊤ h ≫ (Spec.map (CommRingCat.ofHom (φ : S →+* S'))).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom (φ : S →+* S'))) y.left U ⊤ ⊤ h le_rfl).symm
  have e2 := congrArg (fun k => k.hom ((y.left.appLE U ⊤ h).hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (φ : S →+* S')))
  unfold pullFn
  rw [e]
  exact e2

theorem le_preimage_comp (φ : S →ₐ[R] S') (y : sp (R₀ := R) S ⟶ A) (y' : sp (R₀ := R) S' ⟶ A)
    (e : y' = Chart.spMap φ ≫ y) (U : A.left.Opens) (h : ⊤ ≤ y.left ⁻¹ᵁ U) :
    ⊤ ≤ y'.left ⁻¹ᵁ U := by
  subst e
  exact fun x _ => h (Set.mem_univ ((Chart.spMap φ).left x))

theorem le_preimage_of_comp [Subsingleton (PrimeSpectrum S)] [Nontrivial S'] (φ : S →ₐ[R] S')
    (y : sp (R₀ := R) S ⟶ A) (y' : sp (R₀ := R) S' ⟶ A)
    (e : y' = Chart.spMap φ ≫ y) (U : A.left.Opens) (h : ⊤ ≤ y'.left ⁻¹ᵁ U) :
    ⊤ ≤ y.left ⁻¹ᵁ U := by
  subst e
  intro x _
  obtain ⟨x'⟩ : Nonempty (PrimeSpectrum S') := inferInstance
  have := h (Set.mem_univ x')
  have hx : (Chart.spMap φ).left x' = x := Subsingleton.elim (α := PrimeSpectrum S) _ _
  change y.left ((Chart.spMap φ).left x') ∈ U at this
  rwa [hx] at this

end Pull

theorem subsingleton_primeSpectrum (K M : Type) [Field K] [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M]
    [IsCentralScalar K M] : Subsingleton (PrimeSpectrum (TrivSqZeroExt K M)) := by
  have h : ∀ z : PrimeSpectrum (TrivSqZeroExt K M), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha
        (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  refine ⟨fun x y => ?_⟩
  ext a
  rw [h, h]

variable {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))} [GrpObj A]

theorem snd_pullFn_mul {v v' : sp (R₀ := K) (DualNumber K) ⟶ A} (hv : IsTan v) (hv' : IsTan v')
    (U : A.left.Opens) (h : ⊤ ≤ (v * v').left ⁻¹ᵁ U) :
    ∃ (h₁ : ⊤ ≤ v.left ⁻¹ᵁ U) (h₂ : ⊤ ≤ v'.left ⁻¹ᵁ U), ∀ f : Γ(A.left, U),
      (pullFn (v * v') U h f).snd = (pullFn v U h₁ f).snd + (pullFn v' U h₂ f).snd := by
  let E := TrivSqZeroExt K (Fin 2 → K)
  have : Subsingleton (PrimeSpectrum E) := subsingleton_primeSpectrum K _
  let e : Fin 2 → E := fun i => inr (Pi.single i 1)
  have he : ∀ i j, e i * e j = 0 := fun i j => TrivSqZeroExt.inr_mul_inr _ _ _
  have ax : ∀ c : Fin 2 → K, ∀ a b : Fin 2, (inr (c a) : DualNumber K) * inr (c b) = 0 :=
    fun c a b => TrivSqZeroExt.inr_mul_inr _ _ _
  let q : (Fin 2 → K) → (E →ₐ[K] DualNumber K) := fun c =>
    vecTo (Algebra.ofId K _) (fun a => inr (c a)) (ax c)
  have hq : ∀ c a, q c (e a) = inr (c a) := fun c a => vecTo_single _ _ _ _
  have hqs : ∀ c (x : E), (q c x).snd = x.snd 0 * c 0 + x.snd 1 * c 1 := fun c x => by
    refine (congrArg TrivSqZeroExt.snd (vecTo_apply _ _ (ax c) x)).trans ?_
    simp [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]
  have hid : ∀ (t : DualNumber K) (ht : t * t = 0), t = inr 1 → epsTo K t ht = AlgHom.id K _ :=
    fun t ht h => DualNumber.algHom_ext (by rw [epsTo_eps, h]; rfl)
  let p : sp (R₀ := K) E ⟶ A :=
    (Chart.spMap (epsTo K (e 0) (he 0 0)) ≫ v) * (Chart.spMap (epsTo K (e 1) (he 1 1)) ≫ v')
  have e₀ : v * v' = Chart.spMap (q ![1, 1]) ≫ p := by
    simp only [p, MonObj.comp_mul, ← Category.assoc, Chart.spMap_comp, comp_epsTo]
    rw [hid _ _ (by simp [hq]), hid _ _ (by simp [hq]), Chart.spMap_id, Category.id_comp, Category.id_comp]
  have e₁ : v = Chart.spMap (q ![1, 0]) ≫ p := by
    simp only [p, MonObj.comp_mul, ← Category.assoc, Chart.spMap_comp, comp_epsTo]
    rw [hid _ _ (by simp [hq]), epsTo_zero_comp hv' _ (by simp [hq]), Chart.spMap_id, Category.id_comp,
      _root_.mul_one]
  have e₂ : v' = Chart.spMap (q ![0, 1]) ≫ p := by
    simp only [p, MonObj.comp_mul, ← Category.assoc, Chart.spMap_comp, comp_epsTo]
    rw [epsTo_zero_comp hv _ (by simp [hq]), hid _ _ (by simp [hq]), Chart.spMap_id, Category.id_comp,
      _root_.one_mul]
  have hp := le_preimage_of_comp _ _ _ e₀ U h
  refine ⟨le_preimage_comp _ _ _ e₁ U hp, le_preimage_comp _ _ _ e₂ U hp, fun f => ?_⟩
  rw [pullFn_comp _ _ _ e₀ U hp, pullFn_comp _ _ _ e₁ U hp, pullFn_comp _ _ _ e₂ U hp, hqs, hqs, hqs]
  simp

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem isDiff_mul {w w' : Fin g → ℂ} {v v' : epsR ℂ ⟶ A} (hv : IsTan v) (hv' : IsTan v')
    (h : u.IsDiff w v) (h' : u.IsDiff w' v') : u.IsDiff (w + w') (v * v') := by
  intro U hU f
  obtain ⟨h₁, h₂, e⟩ := snd_pullFn_mul hv hv' U hU
  rw [map_add (f := _), ← h U h₁ f, ← h' U h₂ f]
  exact e f

theorem isDiff_scale {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} (h : u.IsDiff w v) (c : ℂ) :
    u.IsDiff (c • w) (Chart.spMap (scaleD c) ≫ v) := by
  intro U hU f
  have : Subsingleton (PrimeSpectrum (DualNumber ℂ)) := subsingleton_primeSpectrum ℂ ℂ
  have hU' := le_preimage_of_comp (scaleD c) v _ rfl U hU
  rw [map_smul, ← h U hU' f]
  refine (congrArg TrivSqZeroExt.snd (pullFn_comp (scaleD c) v _ rfl U hU' hU f)).trans ?_
  rw [scaleD_eq]
  simp [epsTo, dualTo_apply, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl, pullFn, mul_comm]

theorem isDiff_one : u.IsDiff 0 (1 : epsR ℂ ⟶ A) := by
  intro U hU f
  rw [map_zero]
  refine (congrArg TrivSqZeroExt.snd
    (pullFn_comp (scaleD (0 : ℂ)) (1 : epsR ℂ ⟶ A) 1 (comp_one' _).symm U hU hU f)).trans ?_
  rw [scaleD_eq]
  simp [epsTo, dualTo_apply, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl]

theorem isDiff_prod : ∀ {n : ℕ} (W : Fin n → Fin g → ℂ) (v : Fin n → (epsR ℂ ⟶ A)),
    (∀ i, IsTan (v i)) → (∀ i, u.IsDiff (W i) (v i)) →
      IsTan (List.ofFn v).prod ∧ u.IsDiff (∑ i, W i) (List.ofFn v).prod := by
  intro n
  induction n with
  | zero =>
      intro W v _ _
      rw [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.sum_empty]
      exact ⟨isTan_one, isDiff_one u⟩
  | succ n ih =>
      intro W v hv h
      obtain ⟨h₁, h₂⟩ := ih (fun i => W i.succ) (fun i => v i.succ)
        (fun i => hv i.succ) (fun i => h i.succ)
      rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
      exact ⟨isTan_mul (hv 0) h₁, isDiff_mul u (hv 0) h₁ (h 0) h₂⟩

end Unif

theorem isDiff_of_isLieComb :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g n : ℕ) (u : HolUnif A L g) (W : Fin n → (Fin g → ℂ))
      (v : Fin n → (epsR ℂ ⟶ A)) (c : Fin n → ℂ) (w : epsR ℂ ⟶ A), (∀ i, IsTangent (v i)) →
      (∀ i, u.IsDiff (W i) (v i)) → IsLieComb c v w → u.IsDiff (∑ i, c i • W i) w := by
  intro A _ L g n u W v c w hv h hw
  rw [(isLieComb_iff c v w).1 hw]
  exact (isDiff_prod u (fun i => c i • W i) _ (fun i => isTan_scale (c i) ((isTan_iff _).2 (hv i)))
    (fun i => isDiff_scale u (h i) (c i))).2

end GlobalTheory.UnifDifferential
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolUnifReparam
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

noncomputable def holUnifReparam {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (e : (Fin g → ℂ) → ℂ) (he : Differentiable ℂ e) (hne : ∀ z, e z ≠ 0) :
    HolUnif A L g where
  ex z := u.ex (φ z)
  ex_add z w := by rw [map_add (f := _), u.ex_add]
  ex_onto := u.ex_onto.comp φ.surjective
  Λ := u.Λ.comap (φ.toLinearMap.restrictScalars ℤ)
  ker z := u.ker (φ z)
  discrete := by
    haveI := u.discrete
    have hc : Continuous (fun z : Fin g → ℂ => φ z) := φ.toContinuousLinearEquiv.continuous
    refine DiscreteTopology.of_continuous_injective
      (f := fun x : u.Λ.comap (φ.toLinearMap.restrictScalars ℤ) => (⟨φ x.1, x.2⟩ : u.Λ))
      ((hc.comp continuous_subtype_val).subtype_mk _) ?_
    intro x y h
    exact Subtype.ext (φ.injective (congrArg Subtype.val h))
  full := by
    have h1 : ((u.Λ.comap (φ.toLinearMap.restrictScalars ℤ) : Submodule ℤ (Fin g → ℂ)) : Set (Fin g → ℂ)) =
        (φ.symm.toLinearMap.restrictScalars ℝ) '' (u.Λ : Set (Fin g → ℂ)) := by
      ext z
      constructor
      · intro hz
        exact ⟨φ z, hz, φ.symm_apply_apply z⟩
      · rintro ⟨w, hw, rfl⟩
        show φ (φ.symm w) ∈ u.Λ
        rwa [φ.apply_symm_apply]
    rw [h1, ← Submodule.map_span, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact φ.symm.surjective
  hol U f := by
    have hc : Differentiable ℂ (fun z : Fin g → ℂ => φ z) := φ.toContinuousLinearEquiv.differentiable
    exact ⟨(u.hol U f).1.preimage hc.continuous, (u.hol U f).2.comp hc.differentiableOn (fun _ hz => hz)⟩
  fr i z := u.fr i (φ z) / e z
  fr_hol i := by
    have hc : Differentiable ℂ (fun z : Fin g → ℂ => φ z) := φ.toContinuousLinearEquiv.differentiable
    have h1 : DifferentiableOn ℂ (fun z => u.fr i (φ z)) {z | ⊤ ≤ (u.ex (φ z)).left ⁻¹ᵁ L.U i} :=
      (u.fr_hol i).comp hc.differentiableOn (fun _ hz => hz)
    have h2 : Differentiable ℂ (fun z => (e z)⁻¹) := he.inv hne
    simp only [div_eq_mul_inv]
    exact h1.mul h2.differentiableOn
  fr_ne i z hz := div_ne_zero (u.fr_ne i _ hz) (hne z)
  fr_compat i j z hz := by
    rw [u.fr_compat i j _ hz, mul_div_assoc]

theorem exists_holUnif_reparam :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (e : (Fin g → ℂ) → ℂ), Differentiable ℂ e → (∀ z, e z ≠ 0) → e 0 = 1 → ∃ u' : HolUnif A L g, (∀ z, u'.ex z = u.ex (φ z)) ∧ (∀ z, z ∈ u'.Λ ↔ φ z ∈ u.Λ) ∧ (∀ rig, u.IsRig rig → u'.IsRig rig) ∧ (∀ s θ, u.IsFn s θ → u'.IsFn s (fun z => e z * θ (φ z))) ∧ ∀ w v, u.IsDiff (φ w) v → u'.IsDiff w v := by
  intro A _ L g u φ e he hne h0
  refine ⟨holUnifReparam u φ e he hne, fun _ => rfl, fun _ => Iff.rfl, ?_, ?_, ?_⟩
  · intro rig hr j hj
    show u.fr _ (φ 0) / e 0 = _
    rw [map_zero, h0, div_one]
    exact hr j hj
  · intro s θ hs i z hz
    have h := hs i (φ z) hz
    show valAt' (u.ex (φ z)).left _ _ = e z * θ (φ z) * (u.fr i (φ z) / e z)
    rw [h]
    have := hne z
    field_simp
  · intro w v hv U h f
    rw [hv U h f]
    have key := φ.toContinuousLinearEquiv.comp_right_fderiv
      (f := fun z => valAt' (u.ex z).left U f) (x := 0)
    have h2 := congrArg (fun T => T w) key
    simp only [map_zero] at h2
    exact h2.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieCombIffProd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PowLie

variable {R : Type} [CommRing R]

def sc (c : R) : epsR R ⟶ epsR R :=
  Over.homMk (spMap (epsScaleR c)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl])

def zeroPt (R : Type) [CommRing R] : 𝟙_ (Over (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.PowLie.isTangent_iff {G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [GrpObj G]
    (w : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent w ↔ _root_.GlobalTheory.PowLie.zeroPt R ≫ w = η[G] := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent
  constructor
  · intro h
    ext
    simpa [_root_.GlobalTheory.PowLie.zeroPt] using h
  · intro h
    simpa [_root_.GlobalTheory.PowLie.zeroPt] using congrArg Over.Hom.left h

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.PowLie.isLieComb_iff_prod {G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [GrpObj G] [IsCommMonObj G]
    {n : ℕ} (c : Fin n → R) (v : Fin n → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G)) (w : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieComb c v w ↔ w = ∏ i, _root_.GlobalTheory.PowLie.sc (c i) ≫ v i := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieComb
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    ext
    simp [_root_.GlobalTheory.PowLie.sc, hu i]
  · intro hw
    refine ⟨fun i => _root_.GlobalTheory.PowLie.sc (c i) ≫ v i, fun i => by
      simp [_root_.GlobalTheory.PowLie.sc], ?_⟩
    rw [List.prod_ofFn]
    exact hw

attribute [local instance] Over.cartesianMonoidalCategory in
private theorem finset_prod_comp_of_isMonHom {X M N : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [MonObj M] [IsCommMonObj M]
    [MonObj N] [IsCommMonObj N] {κ : Type*} (s : Finset κ) (f : κ → (X ⟶ M)) (h : M ⟶ N)
    [IsMonHom h] : (∏ i ∈ s, f i) ≫ h = ∏ i ∈ s, f i ≫ h :=
  map_prod (IsMonHom.monoidHom h X) f s

attribute [local instance] Over.cartesianMonoidalCategory in
private theorem zeroPt_comp_one {G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [GrpObj G] :
    _root_.GlobalTheory.PowLie.zeroPt R ≫ (1 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G) = η[G] := by
  rw [comp_one, Hom.one_def]
  simp

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.PowLie.isLieBasis_pow : ∀ (R : Type) [CommRing R] (G' G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)) [GrpObj G']
    [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (j g : ℕ) (p : _root_.ReciprocityTheory.ChartRestriction.G.Out.IsPowGrp G' G j)
    (v : Fin g → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G)), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v → ∃ v' : Fin (j * g) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G'),
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v' ∧ ∀ (i i' : Fin j) (k : Fin g),
        v' (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1 := by
  intro R _ G' G _ _ _ _ j g p v hv
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis at hv ⊢
  obtain ⟨htan, huniq⟩ := hv
  have hmon : ∀ i, IsMonHom (p.pr i) := p.hom
  let v' : Fin (j * g) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G') := fun m =>
    Fan.IsLimit.lift p.lim (fun i' =>
      if (finProdFinEquiv.symm m).1 = i' then v (finProdFinEquiv.symm m).2 else 1)
  have hv' : ∀ (i i' : Fin j) (k : Fin g),
      v' (finProdFinEquiv (i, k)) ≫ p.pr i' = if i = i' then v k else 1 := by
    intro i i' k
    exact (Fan.IsLimit.fac p.lim _ i').trans (by simp only [Equiv.symm_apply_apply])
  have hpr : ∀ (w : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G') (i : Fin j), _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent w → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent (w ≫ p.pr i) := by
    intro w i hw
    rw [_root_.GlobalTheory.PowLie.isTangent_iff] at hw ⊢
    rw [← Category.assoc, hw, IsMonHom.one_hom]
  have hcomb : ∀ (c : Fin (j * g) → R) (i' : Fin j),
      (∏ m, _root_.GlobalTheory.PowLie.sc (c m) ≫ v' m) ≫ p.pr i' =
        ∏ k, _root_.GlobalTheory.PowLie.sc (c (finProdFinEquiv (i', k))) ≫ v k := by
    intro c i'
    rw [finset_prod_comp_of_isMonHom, ← finProdFinEquiv.prod_comp, Fintype.prod_prod_type]
    have hterm : ∀ (i : Fin j) (k : Fin g),
        (_root_.GlobalTheory.PowLie.sc (c (finProdFinEquiv (i, k))) ≫ v' (finProdFinEquiv (i, k))) ≫
            p.pr i' =
          if i = i' then _root_.GlobalTheory.PowLie.sc (c (finProdFinEquiv (i, k))) ≫ v k else 1 := by
      intro i k
      rw [Category.assoc, hv']
      split_ifs <;> simp [comp_one]
    simp only [hterm]
    rw [Fintype.prod_eq_single i' (fun i hi => by simp [hi])]
    simp
  refine ⟨v', ⟨fun m => ?_, fun w hw => ?_⟩, hv'⟩
  · obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective m
    rw [_root_.GlobalTheory.PowLie.isTangent_iff]
    refine Fan.IsLimit.hom_ext p.lim _ _ fun i' => ?_
    change (_root_.GlobalTheory.PowLie.zeroPt R ≫ v' (finProdFinEquiv (i, k))) ≫ p.pr i' =
      η[G'] ≫ p.pr i'
    rw [Category.assoc, hv', IsMonHom.one_hom]
    split_ifs
    · exact (_root_.GlobalTheory.PowLie.isTangent_iff _).1 (htan k)
    · exact zeroPt_comp_one
  · choose cc hcc hcc' using fun i => huniq (w ≫ p.pr i) (hpr w i hw)
    refine ⟨fun m => cc (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2, ?_, ?_⟩
    · beta_reduce
      rw [_root_.GlobalTheory.PowLie.isLieComb_iff_prod]
      refine Fan.IsLimit.hom_ext p.lim _ _ fun i' => ?_
      change w ≫ p.pr i' = (∏ m, _) ≫ p.pr i'
      rw [hcomb, (_root_.GlobalTheory.PowLie.isLieComb_iff_prod _ _ _).1 (hcc i')]
      simp
    · intro c' hc'
      rw [_root_.GlobalTheory.PowLie.isLieComb_iff_prod] at hc'
      funext m
      obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective m
      have h := hcc' i (fun k => c' (finProdFinEquiv (i, k))) (by
        beta_reduce
        rw [_root_.GlobalTheory.PowLie.isLieComb_iff_prod, hc', hcomb])
      simpa using congrFun h k

end GlobalTheory.PowLie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusProdSec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxSection

theorem res_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : W ≤ V) (a : Γ(X, U)) :
    (Y.presheaf.map (homOfLE h).op).hom ((f.appLE U V e).hom a) = (f.appLE U W (h.trans e)).hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens} (h : U' ≤ U)
    (e : W ≤ f ⁻¹ᵁ U') (e' : W ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    (f.appLE U' W e).hom ((X.presheaf.map (homOfLE h).op).hom a) = (f.appLE U W e').hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

noncomputable def prodSec {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (t : K → L.Sec) : (LB.LinComb L φ (fun _ => 1)).Sec where
  f jj := ∏ i, ((φ i).appLE _ (LB.wchart L φ jj) (LB.wchart_le L φ jj i)).hom ((t i).f (jj i))
  compat jj jj' := by
    have hg : @Units.val Γ(Y, LB.wchart L φ jj ⊓ LB.wchart L φ jj') _
        ((LB.LinComb L φ (fun _ => 1)).g jj jj') =
        ∏ i, ((φ i).appLE (L.U (jj i) ⊓ L.U (jj' i)) (LB.wchart L φ jj ⊓ LB.wchart L φ jj')
          (le_inf (inf_le_left.trans (LB.wchart_le L φ jj i))
            (inf_le_right.trans (LB.wchart_le L φ jj' i)))).hom (L.g (jj i) (jj' i) : Γ(X, _)) := by
      simp only [LB.LinComb, zpow_one, Units.coe_prod]
      rfl
    change (Y.presheaf.map (homOfLE (inf_le_left :
        LB.wchart L φ jj ⊓ LB.wchart L φ jj' ≤ LB.wchart L φ jj)).op).hom (∏ i, _) =
      @Units.val Γ(Y, LB.wchart L φ jj ⊓ LB.wchart L φ jj') _
        ((LB.LinComb L φ (fun _ => 1)).g jj jj') *
      (Y.presheaf.map (homOfLE (inf_le_right :
        LB.wchart L φ jj ⊓ LB.wchart L φ jj' ≤ LB.wchart L φ jj')).op).hom (∏ i, _)
    rw [hg, map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have e := congrArg ((φ i).appLE (L.U (jj i) ⊓ L.U (jj' i)) (LB.wchart L φ jj ⊓ LB.wchart L φ jj')
          (le_inf (inf_le_left.trans (LB.wchart_le L φ jj i))
            (inf_le_right.trans (LB.wchart_le L φ jj' i)))).hom ((t i).compat (jj i) (jj' i))
    rw [map_mul] at e
    refine (res_appLE _ _ _ _).trans (((appLE_res _ _ _ _ _).symm.trans e).trans ?_)
    congr 1
    exact (appLE_res _ _ _ _ _).trans (res_appLE _ _ _ _).symm

theorem mem_basicOpen_prod {Y : Scheme.{0}} {K : Type} [Fintype K] {W : Y.Opens} (a : K → Γ(Y, W))
    {y : Y} (hy : y ∈ W) (h : ∀ i, y ∈ Y.basicOpen (a i)) : y ∈ Y.basicOpen (∏ i, a i) := by
  rw [Scheme.mem_basicOpen _ _ y hy, map_prod]
  exact IsUnit.prod_univ_iff.2 fun i => (Scheme.mem_basicOpen _ _ y hy).1 (h i)

theorem mem_nonzeroLocus_prodSec {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (t : K → L.Sec) (y : Y) (h : ∀ i, φ i y ∈ Out.nonzeroLocus (t i)) :
    y ∈ Out.nonzeroLocus (prodSec L φ t) := by
  choose k hk using fun i => TopologicalSpace.Opens.mem_iSup.1 (h i)
  have hy : y ∈ LB.wchart L φ k := Set.mem_iInter.2 fun i => X.basicOpen_le _ (hk i)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, mem_basicOpen_prod _ hy fun i => ?_⟩
  exact (Scheme.basicOpen_appLE (φ i) _ _ (LB.wchart_le L φ k i) _).ge ⟨hy, hk i⟩

theorem exists_point_powObj {S : Scheme.{0}} (G : Over S) (s : S) :
    ∀ (n : ℕ) (x : Fin n → G.left), (∀ i, G.hom (x i) = s) →
      ∃ y : (Out.powObj G n).left, (Out.powObj G n).hom y = s ∧
        ∀ i, (Out.powPr G i).left y = x i := by
  intro n
  induction n with
  | zero =>
    intro _ _
    exact ⟨s, rfl, fun i => i.elim0⟩
  | succ n ih =>
    intro x hx
    obtain ⟨z, hz, hz'⟩ := ih (fun i => x i.succ) (fun i => hx i.succ)
    obtain ⟨y, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom)
      (g := (Out.powObj G n).hom) (x 0) z ((hx 0).trans hz.symm)
    refine ⟨y, ?_, fun i => Fin.cases ?_ (fun i => ?_) i⟩
    · change G.hom (pullback.fst G.hom (Out.powObj G n).hom y) = s
      rw [h1, hx]
    · exact h1
    · change (Out.powPr G i).left (pullback.snd G.hom (Out.powObj G n).hom y) = _
      rw [h2, hz']

theorem exists_point {S : Scheme.{0}} {G' G : Over S} {n : ℕ} (pr : Fin n → (G' ⟶ G))
    (lim : IsLimit (Fan.mk G' pr)) (s : S) (x : Fin n → G.left) (hx : ∀ i, G.hom (x i) = s) :
    ∃ y : G'.left, G'.hom y = s ∧ ∀ i, (pr i).left y = x i := by
  obtain ⟨z, hz, hz'⟩ := exists_point_powObj G s n x hx
  let m : Out.powObj G n ⟶ G' := lim.lift (Fan.mk (Out.powObj G n) (Out.powPr G (n := n)))
  have hm : ∀ i, m ≫ pr i = Out.powPr G i := fun i => lim.fac _ ⟨i⟩
  refine ⟨m.left z, ?_, fun i => ?_⟩
  · rw [← Scheme.Hom.comp_apply, Over.w m, hz]
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hm, hz']

theorem exists_boxSec : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : Out.IsPowGrp G' G j) (L : LB G.left) (t : Fin j → L.Sec), L.IsLB → ∃ t' : (Out.boxLB L p.pr).Sec, (∀ (jj : Fin j → L.ι) (h : ∀ i, (Out.boxLB L p.pr).U jj ≤ (p.pr i).left ⁻¹ᵁ L.U (jj i)), t'.f jj = ∏ i, ((p.pr i).left.appLE _ _ (h i)).hom ((t i).f (jj i))) ∧ ∀ s : S, (∀ i, ∃ x : G.left, G.hom x = s ∧ x ∈ Out.nonzeroLocus (t i)) → ∃ y : G'.left, G'.hom y = s ∧ y ∈ Out.nonzeroLocus t' := by
  intro S G' G _ _ j p L t _
  refine ⟨prodSec L (fun i => (p.pr i).left) t, fun _ _ => rfl, fun s hs => ?_⟩
  choose x hx hx' using hs
  obtain ⟨y, hy, hy'⟩ := exists_point p.pr p.lim s x hx
  exact ⟨y, hy, mem_nonzeroLocus_prodSec L _ t y fun i => (hy' i).symm ▸ hx' i⟩

end GlobalTheory.BoxSection
end
