module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSmallGenHeightsNonneg
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionRegularLocalRing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGenericFibreOfSnc
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGenericFibreOfSnc
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem exists_mul_pow_mem (T : Set Ω) {f : Ω} (hf0 : f ≠ 0) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℚ (insert f⁻¹ T)) (hf : f ∈ Algebra.adjoin ℚ T) :
    ∃ n : ℕ, x * f ^ n ∈ Algebra.adjoin ℚ T := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact ⟨1, by simpa [hf0] using (Algebra.adjoin ℚ T).one_mem⟩
    · exact ⟨0, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r => exact ⟨0, by simpa using (Algebra.adjoin ℚ T).algebraMap_mem r⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : (x + y) * f ^ (n + m) = x * f ^ n * f ^ m + y * f ^ m * f ^ n := by ring
    rw [this]
    exact add_mem (mul_mem hn (pow_mem hf m)) (mul_mem hm (pow_mem hf n))
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    have : x * y * f ^ (n + m) = x * f ^ n * (y * f ^ m) := by ring
    rw [this]
    exact mul_mem hn hm

theorem isLocalization_away (A S : Subalgebra ℚ Ω) (hle : A ≤ S) (f : A) (hf0 : (f : Ω) ≠ 0)
    (hinv : (f : Ω)⁻¹ ∈ S) (hs : ∀ x ∈ S, ∃ n : ℕ, x * (f : Ω) ^ n ∈ A) :
    @IsLocalization.Away A _ f S _ (Subalgebra.inclusion hle).toRingHom.toAlgebra := by
  letI := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  have hmap : ∀ a : A, ((algebraMap A S a : S) : Ω) = a := fun a => rfl
  have hunit : IsUnit (algebraMap A S f) := by
    refine IsUnit.of_mul_eq_one (⟨(f : Ω)⁻¹, hinv⟩ : S) ?_
    apply Subtype.ext
    rw [Subalgebra.coe_mul, hmap]
    exact mul_inv_cancel₀ hf0
  refine IsLocalization.Away.mk _ hunit ?_ ?_
  · rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := hs x hx
    refine ⟨n, ⟨x * (f : Ω) ^ n, hn⟩, ?_⟩
    apply Subtype.ext
    rw [hmap, Subalgebra.coe_mul, Subalgebra.coe_pow, hmap]
  · intro a b hab
    refine ⟨0, ?_⟩
    have : (a : Ω) = b := by rw [← hmap a, ← hmap b, hab]
    rw [Subtype.ext this]

theorem smooth_of_cover (A : Subalgebra ℚ Ω) {m : ℕ} (f a : Fin m → Ω) (hf : ∀ l, f l ∈ A) (ha : ∀ l, a l ∈ A)
    (hsum : ∑ l, a l * f l = 1) (S : Fin m → Subalgebra ℚ Ω) (hle : ∀ l, A ≤ S l)
    (hinv : ∀ l, f l ≠ 0 → (f l)⁻¹ ∈ S l) (hs : ∀ l, f l ≠ 0 → ∀ x ∈ S l, ∃ n : ℕ, x * f l ^ n ∈ A)
    (hsm : ∀ l, f l ≠ 0 → Algebra.Smooth ℚ (S l)) : Algebra.Smooth ℚ A := by
  let s : Set A := {x | (x : Ω) ≠ 0 ∧ ∃ l, (x : Ω) = f l}
  have hspan : Ideal.span s = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : A) = ∑ l, (⟨a l, ha l⟩ : A) * (⟨f l, hf l⟩ : A) := by
      apply Subtype.ext
      rw [Subalgebra.coe_one, ← hsum, AddSubmonoidClass.coe_finsetSum]
      rfl
    rw [h1]
    refine Ideal.sum_mem _ fun l _ => ?_
    by_cases h0 : f l = 0
    · have : (⟨f l, hf l⟩ : A) = 0 := Subtype.ext h0
      rw [this, mul_zero]
      exact Ideal.zero_mem _
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨h0, l, rfl⟩)
  rw [← RingHom.smooth_algebraMap]
  refine RingHom.OfLocalizationSpanTarget.ofIsLocalization RingHom.Smooth.ofLocalizationSpanTarget
    RingHom.Smooth.respectsIso _ s hspan ?_
  rintro ⟨x, hx0, l, hl⟩
  have hx0' : f l ≠ 0 := hl ▸ hx0
  letI alg := (Subalgebra.inclusion (hle l)).toRingHom.toAlgebra
  have hloc : IsLocalization.Away x (S l) :=
    isLocalization_away A (S l) (hle l) x hx0 (hl ▸ hinv l hx0') (hl ▸ hs l hx0')
  refine ⟨S l, inferInstance, alg, hloc, ?_⟩
  have hcomp : (algebraMap A (S l)).comp (algebraMap ℚ A) = algebraMap ℚ (S l) := Subsingleton.elim _ _
  rw [hcomp]
  exact RingHom.smooth_algebraMap.mpr (hsm l hx0')

theorem smoothGenericFibreM_of_isSncModel (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type)
    [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ) (bd : Ideal (MRing J))
    (h : Cmp.IsSncModel y e bd) : SmoothGenericFibreM y := by
  intro c hc
  obtain ⟨m, f, a, hf, ha, hsum, hS⟩ := h c hc
  exact smooth_of_cover _ f a hf ha hsum (fun l => Algebra.adjoin ℚ (insert (f l)⁻¹ _))
    (fun l => Algebra.adjoin_mono (Set.subset_insert _ _))
    (fun l _ => Algebra.subset_adjoin (Set.mem_insert _ _))
    (fun l h0 x hx => exists_mul_pow_mem _ h0 hx (hf l))
    (fun l h0 => (hS l h0 _ rfl).1)

end GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGenericFibreOfSncStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_generic_fibre_of_snc : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ) (bd : Ideal (MRing J)), Cmp.IsSncModel y e bd → SmoothGenericFibreM y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth.smoothGenericFibreM_of_isSncModel | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth.smoothGenericFibreM_of_isSncModel | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncSmooth.smoothGenericFibreM_of_isSncModel <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionalSpecializes
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionalSpecializes
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

section Transport

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R']
  {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R' E']

theorem exists_lie_transport (c : R →+* R') {x : Sp R ⟶ S} {y : Sp R' ⟶ S} (h : spMap c ≫ x = y)
    (M : LieModel G x E) (M' : LieModel G y E') :
    ∃ j : E →ₛₗ[c] E', ∀ e, (M'.pt (j e)).left = spMap (dualMap c) ≫ (M.pt e).left := by
  subst h
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear S G R R' c x E E' M M'
  refine ⟨j, fun e => ?_⟩
  have := hj e
  rw [Category.comp_id] at this
  exact this

theorem lie_transport_induction [Smooth G.hom] (c : R →+* R') {x : Sp R ⟶ S} {y : Sp R' ⟶ S}
    (h : spMap c ≫ x = y) (M : LieModel G x E) (M' : LieModel G y E') (j : E →ₛₗ[c] E')
    (hj : ∀ e, (M'.pt (j e)).left = spMap (dualMap c) ≫ (M.pt e).left) {P : E' → Prop} (zero : P 0)
    (base : ∀ e, P (j e)) (smul : ∀ (s : R') n, P n → P (s • n))
    (add : ∀ n n', P n → P n' → P (n + n')) (n : E') : P n := by
  subst h
  letI : Algebra R R' := c.toAlgebra
  letI : Module R E' := Module.compHom E' c
  haveI : IsScalarTower R R' E' := ⟨fun a b v => by
    change (c a * b) • v = c a • (b • v)
    rw [mul_smul]⟩
  let jl : E →ₗ[R] E' :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun r e => j.map_smulₛₗ r e }
  have hb : IsBaseChange R' jl := GlobalTheory.T.lie_model_isBaseChange S G R R' x E E' M M' jl (fun e => by
    rw [Category.comp_id]
    exact hj e)
  exact hb.inductionOn n base smul add

end Transport

theorem lat_form_regular_generizes : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (f : Module.Dual Ω Li) (p q : Cpt ξ),
    IsCptGen ξ → q.1 ⤳ p.1 → (∀ e ∈ M.lat p, f e ∈ regAt ξ p) → ∀ e ∈ M.lat q, f e ∈ regAt ξ q := by
  intro X G _ _ _ Ω _ ξ Li _ _ M f p q _ hqp hf e he
  let c : X.presheaf.stalk p.1 →+* X.presheaf.stalk q.1 := (X.presheaf.stalkSpecializes hqp).hom
  have hc : spMap c ≫ X.fromSpecStalk p.1 = X.fromSpecStalk q.1 :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hqp
  have hgen : ∀ s, genMap ξ q (c s) = genMap ξ p s :=
    fun s => LieTangent.genMap_specializes p q.2 hqp s
  obtain ⟨E, _, _, ⟨Mp⟩⟩ := lieModel_exists X G (X.presheaf.stalk p.1) (X.fromSpecStalk p.1)
  obtain ⟨E', _, _, ⟨Mq⟩⟩ := lieModel_exists X G (X.presheaf.stalk q.1) (X.fromSpecStalk q.1)
  obtain ⟨j, hj⟩ := exists_lie_transport c hc Mp Mq
  obtain ⟨jp, hjp⟩ := exists_lie_transport (genMap ξ p) (LieTangent.spec_genMap ξ p) Mp M
  obtain ⟨jq, hjq⟩ := exists_lie_transport (genMap ξ q) (LieTangent.spec_genMap ξ q) Mq M

  have hcomp : ∀ e₀, jq (j e₀) = jp e₀ := by
    intro e₀
    refine M.inj (Over.OverMorphism.ext ?_)
    rw [hjq, hj, hjp, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    refine RingHom.ext fun a => ?_
    ext <;> simp [hgen]

  have hmem : ∀ e₀, jp e₀ ∈ M.lat p := fun e₀ =>
    (M.mem_lat_iff p _).2 ⟨Mp.pt e₀, Mp.tan e₀, hjp e₀⟩

  obtain ⟨v, hv⟩ := (M.mem_lat_iff q e).1 he
  obtain ⟨ε, rfl⟩ := Mq.onto v hv.1
  have he' : e = jq ε := M.inj (Over.OverMorphism.ext (hv.2.trans (hjq ε).symm))
  subst he'
  refine lie_transport_induction c hc Mp Mq j hj (P := fun n => f (jq n) ∈ regAt ξ q) ?_ ?_ ?_ ?_ ε
  · simpa using zero_mem (regAt ξ q)
  · intro e₀
    obtain ⟨s, hs⟩ := hf _ (hmem e₀)
    rw [hcomp]
    exact ⟨c s, (hgen s).trans hs⟩
  · intro s n hn
    have : f (jq (s • n)) = genMap ξ q s * f (jq n) := by
      rw [jq.map_smulₛₗ, map_smul, smul_eq_mul]
    change f (jq (s • n)) ∈ regAt ξ q
    rw [this]
    exact mul_mem ⟨s, rfl⟩ hn
  · intro n n' hn hn'
    change f (jq (n + n')) ∈ regAt ξ q
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem hn hn'

end GlobalTheory.CompanionTheory.Ar.RootHt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionalSpecializesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_functional_specializes : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (f : Module.Dual Ω Li) (p q : Cpt ξ),
    IsCptGen ξ → q.1 ⤳ p.1 → (∀ e ∈ M.lat p, f e ∈ regAt ξ p) → ∀ e ∈ M.lat q, f e ∈ regAt ξ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.lat_form_regular_generizes | exact GlobalTheory.CompanionTheory.Ar.RootHt.lat_form_regular_generizes | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.lat_form_regular_generizes <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorExtendsDvr
section -- merged from Development.WeilBound.CoreStatements.AmpleLineBundles.TangentVectorExtendsOverIntegers
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace CoverDenseAlt

theorem dualMap_comp_dualMap' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
  ext a <;> simp [dualMap]

theorem dualMap_comp_epsMul_ample_line_bundles {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (s : R) :
    (dualMap f).comp (GlobalTheory.CompanionTheory.Ar.epsMul s) = (GlobalTheory.CompanionTheory.Ar.epsMul (f s)).comp (dualMap f) := by
  ext a <;> simp [dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem spMap_comp_spMap_ample_line_bundles {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (g : R' →+* R'') : spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem tangent_vector_extends_over_integers : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (S : Scheme.{0}) (x : Sp O ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (E : Type) [AddCommGroup E] [Module O E] (M : LieModel G x E) (v : epsAt (spMap (algebraMap O K) ≫ x) ⟶ G), IsTanAt G _ v → (∀ (P : Ideal O) [P.IsMaximal] (c : Localization.AtPrime P →+* K), c.comp (algebraMap O _) = algebraMap O K → ∃ w : epsAt (spMap (algebraMap O (Localization.AtPrime P)) ≫ x) ⟶ G, IsTanAt G _ w ∧ v.left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ w.left) → ∃ e, (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt e).left) := by
  intro O K _ _ _ _ _ S x G _ _ _ E _ _ M v hv hloc
  obtain ⟨EK, _, _, ⟨MK⟩⟩ := lieModel_exists S G K (spMap (algebraMap O K) ≫ x)
  obtain ⟨jK, hjK, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S G O K (algebraMap O K) x E EK M MK
  obtain ⟨eK, rfl⟩ := MK.onto v hv
  let I : Ideal O :=
    { carrier := {a | ∃ e, jK e = algebraMap O K a • eK}
      add_mem' := by
        rintro a b ⟨e, he⟩ ⟨e', he'⟩
        exact ⟨e + e', by rw [map_add (f := _), he, he', map_add (f := _), add_smul]⟩
      zero_mem' := ⟨0, by rw [map_zero, map_zero, zero_smul]⟩
      smul_mem' := by
        rintro a b ⟨e, he⟩
        refine ⟨a • e, ?_⟩
        rw [jK.map_smulₛₗ, he, smul_eq_mul, map_mul, mul_smul] }
  suffices h1 : (1 : O) ∈ I by
    obtain ⟨e, he⟩ := h1
    rw [map_one, one_smul] at he
    refine ⟨e, ?_⟩
    rw [← he]
    exact hjK e
  by_contra h1
  obtain ⟨P, hP, hIP⟩ := I.exists_le_maximal ((Ideal.ne_top_iff_one I).2 h1)
  have hunit : ∀ y : P.primeCompl, IsUnit (algebraMap O K y) := by
    intro y
    refine IsUnit.mk0 _ ?_
    intro h0
    have h2 : (y : O) = 0 := IsFractionRing.injective O K (by rw [h0, map_zero])
    exact y.2 (h2 ▸ P.zero_mem)
  let c : Localization.AtPrime P →+* K := IsLocalization.lift hunit
  have hc : c.comp (algebraMap O (Localization.AtPrime P)) = algebraMap O K := IsLocalization.lift_comp hunit
  obtain ⟨w, hw, hvw⟩ := hloc P c hc
  obtain ⟨EP, _, _, ⟨MP⟩⟩ := lieModel_exists S G (Localization.AtPrime P)
    (spMap (algebraMap O (Localization.AtPrime P)) ≫ x)
  obtain ⟨jP, hjP, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S G O (Localization.AtPrime P)
    (algebraMap O (Localization.AtPrime P)) x E EP M MP
  obtain ⟨eP, rfl⟩ := MP.onto w hw
  letI : Module O EP := Module.compHom EP (algebraMap O (Localization.AtPrime P))
  haveI : IsScalarTower O (Localization.AtPrime P) EP := ⟨fun a b m => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let β : E →ₗ[O] EP :=
    { toFun := jP
      map_add' := map_add jP
      map_smul' := fun a e => by
        rw [jP.map_smulₛₗ]
        rfl }
  have hbc : IsBaseChange (Localization.AtPrime P) β :=
    (LieProj.lie_finite_projective_baseChange S G O x E M).2.2 (Localization.AtPrime P) EP MP β
      (fun e => by
        have h2 := hjP e
        simp only [LieModel.Lifts, Category.comp_id] at h2
        exact h2)
  haveI : IsLocalizedModule P.primeCompl β :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl (Localization.AtPrime P) β).2 hbc
  obtain ⟨⟨e, s⟩, hes⟩ := IsLocalizedModule.surj P.primeCompl β eP
  have hes' : jP e = algebraMap O (Localization.AtPrime P) (s : O) • eP := hes.symm
  have hmem : (s : O) ∈ I := by
    refine ⟨e, ?_⟩
    apply MK.inj
    apply Over.OverMorphism.ext
    have h1 := hjK e
    have h2 := hjP e
    simp only [LieModel.Lifts, Category.comp_id] at h1 h2
    have h3 : (MK.pt (jK e)).left = spMap (dualMap c) ≫ (MP.pt (jP e)).left := by
      rw [h1, h2, ← Category.assoc, spMap_comp_spMap_ample_line_bundles, dualMap_comp_dualMap', hc]
    rw [h3, hes', MP.smul, MK.smul, hvw, ← Category.assoc, ← Category.assoc]
    congr 1
    have h4 := spMap_comp_spMap_ample_line_bundles (GlobalTheory.CompanionTheory.Ar.epsMul (algebraMap O (Localization.AtPrime P) (s : O))) (dualMap c)
    have h5 := spMap_comp_spMap_ample_line_bundles (dualMap c) (GlobalTheory.CompanionTheory.Ar.epsMul (c (algebraMap O (Localization.AtPrime P) (s : O))))
    rw [← RingHom.comp_apply c, hc] at h5
    simp only [spMap] at h4 h5 ⊢
    rw [h4, dualMap_comp_epsMul_ample_line_bundles, h5]
    rw [← RingHom.comp_apply c, hc]
  exact s.2 (hIP hmem)

end CoverDenseAlt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorExtendsDvr
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_lifts_of_local : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (S : Scheme.{0}) (x : Sp O ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (E : Type) [AddCommGroup E] [Module O E] (M : LieModel G x E) (v : epsAt (spMap (algebraMap O K) ≫ x) ⟶ G), IsTanAt G _ v → (∀ (P : Ideal O) [P.IsMaximal] (c : Localization.AtPrime P →+* K), c.comp (algebraMap O _) = algebraMap O K → ∃ w : epsAt (spMap (algebraMap O (Localization.AtPrime P)) ≫ x) ⟶ G, IsTanAt G _ w ∧ v.left = spMap (dualMap c) ≫ w.left) → ∃ e, (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt e).left) :=
  @CoverDenseAlt.tangent_vector_extends_over_integers

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorExtendsDvrStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_vector_extends_dvr : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (S : Scheme.{0}) (x : Sp O ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (E : Type) [AddCommGroup E] [Module O E] (M : LieModel G x E) (v : epsAt (spMap (algebraMap O K) ≫ x) ⟶ G), IsTanAt G _ v → (∀ (P : Ideal O) [P.IsMaximal] (c : Localization.AtPrime P →+* K), c.comp (algebraMap O _) = algebraMap O K → ∃ w : epsAt (spMap (algebraMap O (Localization.AtPrime P)) ≫ x) ⟶ G, IsTanAt G _ w ∧ v.left = spMap (dualMap c) ≫ w.left) → ∃ e, (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap O K)) ≫ (M.pt e).left) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lieModel_lifts_of_local | exact GlobalTheory.CompanionTheory.Ar.lieModel_lifts_of_local | (intros; apply GlobalTheory.CompanionTheory.Ar.lieModel_lifts_of_local <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingCoordsReindexed
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingCoordsReindexed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

namespace GlobalTheory.CompanionTheory.Ar.Chg

private lemma valAt_unique_lemma {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of ℂ) ⟶ X) {b : Ω} {r r' : ℂ}
    (h1 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z b r) (h2 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z b r') : r = r' := by
  obtain ⟨hs, s, hs1, hs2⟩ := h1
  obtain ⟨hs', s', hs1', hs2'⟩ := h2
  have hs1'' : GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hs⟩ s' = b := hs1'
  have e0 : GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hs⟩ (s - s') = 0 :=
    (map_sub _ s s').trans (by rw [hs1, hs1'', sub_self])
  have hnu : ¬ IsUnit (s - s') := by
    intro hu
    have hu' := hu.map (GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hs⟩)
    exact not_isUnit_zero ((congrArg IsUnit e0).mp hu')
  have e1 : (Scheme.stalkClosedPointTo z).hom (s - s') = r - r' := by
    rw [← hs2, ← hs2']
    exact map_sub _ _ _
  by_contra hne
  apply hnu
  apply (Scheme.isLocalHom_stalkClosedPointTo z).map_nonunit
  exact (congrArg IsUnit e1).mpr (sub_ne_zero.mpr hne).isUnit

private lemma valAt_mul_lemma_2 {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of ℂ) ⟶ X) {b b' : Ω} {r r' : ℂ}
    (h1 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z b r) (h2 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z b' r') :
    GlobalTheory.CompanionTheory.Ar.ValAt ξ z (b * b') (r * r') ∧ GlobalTheory.CompanionTheory.Ar.ValAt ξ z 1 1 := by
  obtain ⟨hs, s, hs1, hs2⟩ := h1
  obtain ⟨hs', s', hs1', hs2'⟩ := h2
  have hs1'' : GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hs⟩ s' = b' := hs1'
  exact ⟨⟨hs, s * s', (map_mul _ s s').trans (congrArg₂ (· * ·) hs1 hs1''),
      (map_mul _ s s').trans (congrArg₂ (· * ·) hs2 hs2')⟩,
    ⟨hs, 1, map_one _, map_one _⟩⟩

theorem coordsAt_blkV : ∀ (X X₀ : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (h : X ⟶ X₀) (i : Ω₀ →+* Ω) (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)), GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i → CoordTie ℤ ξ₀ (fun c' : (k : K₀) → J₀ k => ∏ k, y₀ ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (a : Ω₀) (r : ℂ), ValAt ξ₀ (z ≫ h) a r → ValAt ξ z (i a) r) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → CoordsAt ξ₀ y₀ (z ≫ h) (fun p => w (blkV bk bx p)) := by
  classical
  intro X X₀ Ω Ω₀ _ _ ξ ξ₀ h i K₀ K _ _ J₀ J _ _ y₀ y bk bx hdom htie hgen hy hval z w hw
  unfold GlobalTheory.CompanionTheory.Ar.Dominates at hdom
  have hpt : ∀ (a b : PrimeSpectrum Ω₀), a = b := fun a b =>
    PrimeSpectrum.ext ((Ideal.eq_bot_of_prime a.asIdeal).trans (Ideal.eq_bot_of_prime b.asIdeal).symm)
  have hsp : GlobalTheory.CompanionTheory.Ar.genPt ξ₀ ⤳ GlobalTheory.CompanionTheory.Ar.centre (z ≫ h) := by
    have h2 := (hgen (GlobalTheory.CompanionTheory.Ar.centre z)).map h.continuous
    have e1 : h (GlobalTheory.CompanionTheory.Ar.genPt ξ) = GlobalTheory.CompanionTheory.Ar.genPt ξ₀ := by
      have hh := congrArg (fun f => f (IsLocalRing.closedPoint Ω)) hdom
      simp only [Scheme.Hom.comp_apply] at hh
      exact hh.trans (congrArg ξ₀ (hpt _ _))
    have e2 : h (GlobalTheory.CompanionTheory.Ar.centre z) = GlobalTheory.CompanionTheory.Ar.centre (z ≫ h) :=
      (Scheme.Hom.comp_apply z h _).symm
    rw [← e1, ← e2]
    exact h2
  unfold GlobalTheory.CompanionTheory.Ar.CoordsAt at hw ⊢
  obtain ⟨hw1, hw2⟩ := hw
  refine ⟨fun k => ?_, fun k c hc => ?_⟩
  · obtain ⟨c', hc'⟩ := hw1 (bk k)
    refine ⟨(bx k).symm c', ?_⟩
    simpa [GlobalTheory.CompanionTheory.Ar.Chg.blkV] using hc'
  · simp only [GlobalTheory.CompanionTheory.Ar.Chg.blkV] at hc ⊢
    obtain ⟨hyne, hrat⟩ := hw2 (bk k) (bx k c) hc
    have hy0c : y₀ ⟨k, c⟩ ≠ 0 := fun h0 => hyne (by rw [hy, h0, map_zero])
    refine ⟨hy0c, fun j => ?_⟩
    obtain ⟨c', hc'0, hc'reg⟩ := htie.cover ⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩
    dsimp only at hc'0 hc'reg
    have hprod : ∀ c'' : (k' : K₀) → J₀ k', (∏ k', y₀ ⟨k', c'' k'⟩) =
        y₀ ⟨k, c'' k⟩ * ∏ k' ∈ ({k}ᶜ : Finset K₀), y₀ ⟨k', c'' k'⟩ :=
      fun c'' => Fintype.prod_eq_mul_prod_compl k _
    have hQ : ∏ k' ∈ ({k}ᶜ : Finset K₀), y₀ ⟨k', c' k'⟩ ≠ 0 := by
      intro h0
      apply hc'0
      rw [hprod c', h0, mul_zero]
    have hd : y₀ ⟨k, c' k⟩ ≠ 0 := by
      intro h0
      apply hc'0
      rw [hprod c', h0, zero_mul]
    have hrat0 : ∀ j' : J₀ k, y₀ ⟨k, j'⟩ / y₀ ⟨k, c' k⟩ ∈
        GlobalTheory.CompanionTheory.Ar.regAt ξ₀ ⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩ := by
      intro j'
      have hm := hc'reg (Function.update c' k j')
      have hrest : ∏ k' ∈ ({k}ᶜ : Finset K₀), y₀ ⟨k', Function.update c' k j' k'⟩ =
          ∏ k' ∈ ({k}ᶜ : Finset K₀), y₀ ⟨k', c' k'⟩ := by
        apply Finset.prod_congr rfl
        intro k' hk'
        rw [Function.update_of_ne (by simpa using hk')]
      rw [hprod (Function.update c' k j'), hprod c', hrest, Function.update_self,
        mul_div_mul_right _ _ hQ] at hm
      exact hm
    obtain ⟨sj, hsj⟩ := RingHom.mem_range.mp (hrat0 j)
    obtain ⟨sc, hsc⟩ := RingHom.mem_range.mp (hrat0 c)
    have hvalc : GlobalTheory.CompanionTheory.Ar.ValAt ξ₀ (z ≫ h) (y₀ ⟨k, c⟩ / y₀ ⟨k, c' k⟩)
        ((Scheme.stalkClosedPointTo (z ≫ h)).hom sc) := ⟨hsp, sc, hsc, rfl⟩
    have hvalc' := hval z _ _ hvalc
    obtain ⟨rd, hrd, -⟩ := hrat (bx k (c' k))
    rw [hy, hy, ← map_div₀] at hrd
    obtain ⟨hprodv, hone⟩ := valAt_mul_lemma_2 ξ z hvalc' hrd
    rw [← map_mul, div_mul_div_comm, mul_comm (y₀ ⟨k, c⟩), div_self (mul_ne_zero hd hy0c),
      map_one] at hprodv
    have h1 := valAt_unique_lemma ξ z hprodv hone
    have hv : (Scheme.stalkClosedPointTo (z ≫ h)).hom sc ≠ 0 := left_ne_zero_of_mul_eq_one h1
    have hunit : IsUnit sc := (Scheme.isLocalHom_stalkClosedPointTo (z ≫ h)).map_nonunit _ (Ne.isUnit hv)
    let sci : X₀.presheaf.stalk (↑(⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩ : GlobalTheory.CompanionTheory.Ar.Cpt ξ₀)) :=
      ↑hunit.unit⁻¹
    have hsci : sci * sc = 1 := by
      have hinv := hunit.unit.inv_mul
      rw [IsUnit.unit_spec] at hinv
      exact hinv
    have hgsci : GlobalTheory.CompanionTheory.Ar.genMap ξ₀ ⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩ sci *
        (y₀ ⟨k, c⟩ / y₀ ⟨k, c' k⟩) = 1 := by
      rw [← hsc, ← map_mul, hsci, map_one]
    have hs₀ : GlobalTheory.CompanionTheory.Ar.genMap ξ₀ ⟨GlobalTheory.CompanionTheory.Ar.centre (z ≫ h), hsp⟩ (sj * sci) =
        y₀ ⟨k, j⟩ / y₀ ⟨k, c⟩ := by
      rw [map_mul, hsj, eq_inv_of_mul_eq_one_left hgsci]
      field_simp
    have hex : GlobalTheory.CompanionTheory.Ar.ValAt ξ₀ (z ≫ h) (y₀ ⟨k, j⟩ / y₀ ⟨k, c⟩)
        ((Scheme.stalkClosedPointTo (z ≫ h)).hom (sj * sci)) := ⟨hsp, _, hs₀, rfl⟩
    have hex' := hval z _ _ hex
    obtain ⟨r, hr, hwr⟩ := hrat (bx k j)
    rw [hy, hy, ← map_div₀] at hr
    have hrr := valAt_unique_lemma ξ z hr hex'
    refine ⟨r, ?_, hwr⟩
    rw [hrr]
    exact hex

end GlobalTheory.CompanionTheory.Ar.Chg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingCoordsReindexedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominating_coords_reindexed : ∀ (X X₀ : Scheme.{0}) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (h : X ⟶ X₀) (i : Ω₀ →+* Ω) (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)), GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ h i → CoordTie ℤ ξ₀ (fun c' : (k : K₀) → J₀ k => ∏ k, y₀ ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (a : Ω₀) (r : ℂ), ValAt ξ₀ (z ≫ h) a r → ValAt ξ z (i a) r) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → CoordsAt ξ₀ y₀ (z ≫ h) (fun p => w (blkV bk bx p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Chg.coordsAt_blkV | exact GlobalTheory.CompanionTheory.Ar.Chg.coordsAt_blkV | (intros; apply GlobalTheory.CompanionTheory.Ar.Chg.coordsAt_blkV <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPositiveHermitianLine
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPositiveHermitianLine
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FS

open MvPolynomial Filter Topology
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.FubiniStudyLeviForm

theorem log_rho_eq_phi (I : Type) [Fintype I] :
    (fun z : I → ℂ => Real.log ((fsMetric («ι» := I)).ρ z)) = FubiniLevi.phi := by
  funext z
  change Real.log ‖WithLp.toLp 2 z‖ = _
  rw [EuclideanSpace.norm_eq, Real.log_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [FubiniLevi.phi, FubiniLevi.sqSum, PiLp.toLp_apply]
  ring

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem exists_block_ne {z w : (Σ k, J k) → ℂ} (hw : ∀ c : K → ℂ, w ≠ torusSmul c z) :
    ∃ k, ∀ c : ℂ, (fun i => w ⟨k, i⟩) ≠ fun i => c * z ⟨k, i⟩ := by
  by_contra h
  push_neg at h
  choose c hc using h
  exact hw c (funext fun p => by
    obtain ⟨k, i⟩ := p
    exact congrFun (hc k) i)

theorem levi_fsMulti_pos {z w : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hw : ∀ c : K → ℂ, w ≠ torusSmul c z) :
    0 < ReciprocityTheory.ChartRestriction.G.Geo.leviForm (fun y => Real.log ((fsMulti J).h y)) z w := by
  classical
  obtain ⟨k₀, hk₀⟩ := exists_block_ne hw
  set F : K → ((Σ k, J k) → ℂ) → ℝ :=
    fun k y => Real.log ((fsMetric («ι» := J k)).ρ (fun i => y ⟨k, i⟩)) with hF
  have hev : (fun y => Real.log ((fsMulti J).h y)) =ᶠ[𝓝 z] fun y => ∑ k ∈ Finset.univ, F k y := by
    have hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, hi⟩ := hz k
      exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
        fun y hy => ⟨i, hy⟩
    filter_upwards [Filter.eventually_all.mpr hopen] with y hy
    have hpos : ∀ k, 0 < (fsMetric («ι» := J k)).ρ (fun i => y ⟨k, i⟩) := fun k => by
      obtain ⟨i, hi⟩ := hy k
      exact (fsMetric («ι» := J k)).pos _ fun h0 => hi (congrFun h0 i)
    simp only [fsMulti, HermLine.ofMetrics, zpow_one, hF]
    exact Real.log_prod fun k _ => (hpos k).ne'
  have hk0 : ∀ k, (fun i => z ⟨k, i⟩) ≠ 0 := fun k h0 => by
    obtain ⟨i, hi⟩ := hz k
    exact hi (congrFun h0 i)
  have hφ : ∀ k, ContDiffAt ℝ 2 (fun u => Real.log ((fsMetric («ι» := J k)).ρ u)) (blockProj J k z) := by
    intro k
    have hne : blockProj J k z ≠ 0 := hk0 k
    have hsm := HilbertSamuel.ProjLine.isSmoothMetric_fs (J := J k)
    have hρ : ContDiffAt ℝ 2 (fsMetric («ι» := J k)).ρ (blockProj J k z) :=
      (hsm.contDiffAt (isOpen_ne.mem_nhds hne)).of_le (WithTop.coe_le_coe.2 le_top)
    exact hρ.log ((fsMetric («ι» := J k)).pos _ hne).ne'
  have hFk : ∀ k, F k = (fun u => Real.log ((fsMetric («ι» := J k)).ρ u)) ∘ blockProj J k := fun k => rfl
  have hC : ∀ k, ContDiffAt ℝ 2 (F k) z := fun k =>
    hFk k ▸ (hφ k).comp z ((blockProj J k).restrictScalars ℝ).contDiff.contDiffAt
  have hL : ∀ k v, ReciprocityTheory.AnForm.levi (F k) z v = ReciprocityTheory.ChartRestriction.G.Geo.leviForm (fun u => Real.log ((fsMetric («ι» := J k)).ρ u))
      (fun i => z ⟨k, i⟩) (fun i => v ⟨k, i⟩) := fun k v => by
    rw [hFk, ReciprocityTheory.AnForm.levi_comp v ((blockProj J k).analyticAt z) (hφ k), (blockProj J k).fderiv]
    rfl
  have hnn : ∀ k v, 0 ≤ ReciprocityTheory.AnForm.levi (F k) z v := fun k v => by
    rw [hL]
    exact HilbertSamuel.ProjLine.leviForm_log_fs_nonneg (hk0 k) _
  have hpos : 0 < ReciprocityTheory.AnForm.levi (F k₀) z w := by
    rw [hL, log_rho_eq_phi]
    exact FubiniLevi.levi_phi_pos_of_ne (hz k₀) hk₀
  have hsum := levi_sum_nonneg F (fun k => hC k) hnn w (Finset.univ.erase k₀)
  change 0 < ReciprocityTheory.AnForm.levi _ z w
  rw [ReciprocityTheory.AnForm.levi_congr hev]
  have hsplit : (fun y => ∑ k ∈ Finset.univ, F k y) =
      fun y => F k₀ y + 1 * ∑ k ∈ Finset.univ.erase k₀, F k y := by
    funext y
    rw [_root_.one_mul]
    exact (Finset.add_sum_erase Finset.univ (fun k => F k y) (Finset.mem_univ k₀)).symm
  rw [hsplit, ReciprocityTheory.AnForm.levi_add_smul 1 (hC k₀) hsum.1 w]
  linarith [hsum.2]

theorem isPositiveRel_fsMulti (P : Ideal (MRing J)) : IsPositiveRel P (fsMulti J) :=
  ⟨FsLineSmooth.proof K J, fun _ hz _ _ hw => levi_fsMulti_pos hz.1 hw⟩

theorem isConjInvariantH_fsMulti : IsConjInvariantH (fsMulti J) := by
  intro z
  simp [fsMulti, HermLine.ofMetrics, fsMetric, EuclideanSpace.norm_eq]

def chartForm (c : ∀ k, J k) : MRing J := ∏ k, X ⟨k, c k⟩

theorem isMultiHomog_chartForm (c : ∀ k, J k) :
    IsMultiHomog (chartForm c) fun k => ((fsMulti J).a k).toNat := by
  classical
  have h := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_xpow c (fun _ : K => 1)
  simpa [chartForm, fsMulti, HermLine.ofMetrics, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow] using h

theorem chartForm_le (c : ∀ k, J k) (z : (Σ k, J k) → ℂ) :
    ‖eval z (map (Int.castRingHom ℂ) (chartForm c))‖ ≤ (fsMulti J).h z := by
  have e : eval z (map (Int.castRingHom ℂ) (chartForm c)) = ∏ k, z ⟨k, c k⟩ := by
    simp [chartForm, map_prod]
  rw [e, norm_prod]
  simp only [fsMulti, HermLine.ofMetrics, zpow_one]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => ?_
  exact PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨k, i⟩)) (c k)

theorem exists_chartForm_notMem {Q : Ideal (MRing J)} (hQ : IsMultiProjPrime Q) :
    ∃ c, chartForm c ∉ Q := by
  choose c hc using hQ.2.2
  refine ⟨c, fun h => ?_⟩
  obtain ⟨k, -, hk⟩ := (hQ.1.prod_mem_iff).1 h
  exact hc k hk

theorem heights_fsMulti {II : IntersectionSystem} (hII : IsIntersectionSystem II) {W : Ideal (MRing J)}
    (hW : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W 1) : 0 ≤ II K J W 1 ![fsMulti J] := by
  classical
  let e := Fintype.equivFin (∀ k, J k)
  refine HilbertSamuel.SmallGenHeightsNonneg.proof K J ⊥ (fsMulti J) II _ (fun j => chartForm (e.symm j)) hII
    (FsLineSmooth.proof K J) (fun k => ?_) (fun j => isMultiHomog_chartForm _) (fun Q hQ _ => ?_)
    (fun j z _ => chartForm_le _ z) W hW bot_le
  · show (0 : ℤ) ≤ 1
    exact zero_le_one
  · obtain ⟨c, hc⟩ := exists_chartForm_notMem hQ
    exact ⟨e c, by simpa using hc⟩

end GlobalTheory.CompanionTheory.Ar.FS

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

theorem exists_fubiniStudy_line :
    ∀ (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)),
      IsFullIntersectionSystem II → ∃ A : HermLine J, (∀ k, A.a k = 1) ∧ IsPositiveRel P A ∧ IsConjInvariantH A ∧
        ∀ W : Ideal (MRing J), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W 1 → 0 ≤ II K J W 1 ![A] :=
  fun _ _ _ _ _ P hII => ⟨GroundTheory.Heights₂.Heights.fsMulti _, fun _ => rfl, FS.isPositiveRel_fsMulti P,
    FS.isConjInvariantH_fsMulti, fun _ hW => FS.heights_fsMulti hII.1 hW⟩

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPositiveHermitianLineStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_positive_hermitian_line : ∀ (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)), IsFullIntersectionSystem II → ∃ A : HermLine J, (∀ k, A.a k = 1) ∧ IsPositiveRel P A ∧ IsConjInvariantH A ∧ ∀ W : Ideal (MRing J), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar W 1 → 0 ≤ II K J W 1 ![A] := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_fubiniStudy_line | exact GlobalTheory.CompanionTheory.Ar.exists_fubiniStudy_line | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_fubiniStudy_line <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RationalRelationInChartIdeal
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RationalRelationInChartIdeal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartDehom

theorem den_mul_algebraMap {F : Type} [Field F] [CharZero F] (q : ℚ) :
    (q.den : F) * algebraMap ℚ F q = (q.num : F) := by
  have hd : (q.den : F) ≠ 0 := by exact_mod_cast q.den_nz
  rw [eq_ratCast, Rat.cast_def]
  field_simp

theorem exists_homog {K : Type} [Fintype K] {J : K → Type} {Ω : Type} [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {Q : Type} [CommRing Q] (ρ : MvPolynomial (Σ k, J k) ℤ →+* Q)
    (τ : MvPolynomial (Σ k, J k) ℚ →+* Q)
    (hρ : ∀ k, ρ (X ⟨k, c k⟩) = 1) (hX : ∀ p, ρ (X p) = τ (X p))
    (hQ : ∀ q : ℚ, (q.den : Q) * τ (MvPolynomial.C q) = (q.num : Q))
    (G : MvPolynomial (Σ k, J k) ℚ) :
    ∃ (N : ℤ) (D : K → ℕ) (H : MvPolynomial (Σ k, J k) ℤ), N ≠ 0 ∧
      mConeMap y H = MvPolynomial.C (N : Ω) *
        (∏ k, (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) ^ D k) *
        MvPolynomial.C (aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G) ∧
      ρ H = (N : Q) * τ G := by
  classical
  set u : (Σ k, J k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩ with hu
  set w : K → MvPolynomial K Ω := fun k => MvPolynomial.C (y ⟨k, c k⟩) * X k with hw
  let M : (K → ℕ) → MvPolynomial (Σ k, J k) ℤ := fun D => ∏ k, X ⟨k, c k⟩ ^ D k
  have hXc : ∀ p, mConeMap y (X p) = MvPolynomial.C (y p) * X p.1 := by
    intro p; simp [mConeMap]
  have hMc : ∀ D, mConeMap y (M D) = ∏ k, w k ^ D k := by
    intro D
    simp only [M, map_prod, map_pow, hXc, hw]
  have hMρ : ∀ D, ρ (M D) = 1 := by
    intro D
    simp only [M, map_prod, map_pow, hρ, one_pow, Finset.prod_const_one]
  have hW : ∀ D E : K → ℕ, (∏ k, w k ^ D k) * ∏ k, w k ^ E k = ∏ k, w k ^ (D + E) k := by
    intro D E
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  have hS : ∀ a, ∏ k, w k ^ (Pi.single a 1 : K → ℕ) k = w a := by
    intro a
    rw [Finset.prod_eq_single a (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
    simp
  have hCc : ∀ n : ℤ, mConeMap y (MvPolynomial.C n) = MvPolynomial.C (n : Ω) := by
    intro n
    have h := (mConeMap y).commutes n
    simpa [MvPolynomial.algebraMap_eq] using h
  have hCρ : ∀ n : ℤ, ρ (MvPolynomial.C n) = (n : Q) := fun n =>
    eq_intCast (ρ.comp MvPolynomial.C) n
  induction G using MvPolynomial.induction_on with
  | C q =>
    refine ⟨q.den, 0, MvPolynomial.C q.num, by exact_mod_cast q.den_nz, ?_, ?_⟩
    · rw [hCc, aeval_C]
      simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one]
      rw [_root_.mul_one, ← map_mul]
      congr 1
      have := den_mul_algebraMap (F := Ω) q
      push_cast
      exact this.symm
    · rw [hCρ]
      have := hQ q
      push_cast
      exact this.symm
  | add f g hf hg =>
    obtain ⟨N₁, D₁, H₁, h₁, c₁, r₁⟩ := hf
    obtain ⟨N₂, D₂, H₂, h₂, c₂, r₂⟩ := hg
    refine ⟨N₁ * N₂, D₁ + D₂,
      MvPolynomial.C N₂ * H₁ * M D₂ + MvPolynomial.C N₁ * H₂ * M D₁, mul_ne_zero h₁ h₂, ?_, ?_⟩
    · rw [map_add (f := _), map_mul, map_mul, map_mul, map_mul, c₁, c₂, hMc, hMc, hCc, hCc, ← hW, map_add (f := _),
        map_add]
      push_cast
      rw [MvPolynomial.C_mul]
      ring
    · rw [map_add (f := _), map_mul, map_mul, map_mul, map_mul, r₁, r₂, hMρ, hMρ, hCρ, hCρ, map_add (f := _)]
      push_cast
      ring
  | mul_X f p hf =>
    obtain ⟨N, D, H, h, c₁, r₁⟩ := hf
    refine ⟨N, D + Pi.single p.1 1, H * X p, h, ?_, ?_⟩
    · have hp : MvPolynomial.C (y p) * X p.1 = MvPolynomial.C (u p) * w p.1 := by
        rw [hw]
        simp only
        rw [← _root_.mul_assoc, ← MvPolynomial.C_mul, hu]
        simp only
        rw [div_mul_cancel₀ _ (hy p.1)]
      rw [map_mul, c₁, hXc, hp, ← hW, hS, map_mul, aeval_X, MvPolynomial.C_mul]
      ring
    · rw [map_mul, map_mul, r₁, hX]
      ring

theorem map_mem_chartIdeal : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ G : MvPolynomial (Σ k, J k) ℚ,
    aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G = (0 : Ω) →
    map (algebraMap ℚ ℂ) G ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := by
  intro K _ J _ Ω _ _ y c hy G hG
  classical
  set A : Ideal (MvPolynomial (Σ k, J k) ℂ) :=
    Ideal.span (Set.range fun k => (X ⟨k, c k⟩ - 1 : MvPolynomial (Σ k, J k) ℂ)) with hA
  let π := Ideal.Quotient.mk A
  let ρ : MvPolynomial (Σ k, J k) ℤ →+* (MvPolynomial (Σ k, J k) ℂ ⧸ A) :=
    π.comp (MvPolynomial.map (Int.castRingHom ℂ))
  let τ : MvPolynomial (Σ k, J k) ℚ →+* (MvPolynomial (Σ k, J k) ℂ ⧸ A) :=
    π.comp (MvPolynomial.map (algebraMap ℚ ℂ))
  have hρ : ∀ k, ρ (X ⟨k, c k⟩) = 1 := by
    intro k
    have h : π (X ⟨k, c k⟩) = π 1 :=
      Ideal.Quotient.eq.mpr (Ideal.subset_span ⟨k, rfl⟩)
    simpa [ρ] using h
  have hX : ∀ p, ρ (X p) = τ (X p) := by
    intro p
    simp [ρ, τ]
  have hQ : ∀ q : ℚ, (q.den : MvPolynomial (Σ k, J k) ℂ ⧸ A) * τ (MvPolynomial.C q) =
      (q.num : MvPolynomial (Σ k, J k) ℂ ⧸ A) := by
    intro q
    have h := congrArg (fun a : ℂ => π (MvPolynomial.C a)) (den_mul_algebraMap (F := ℂ) q)
    simpa [τ] using h
  obtain ⟨N, D, H, hN, hc, hr⟩ := exists_homog y c hy ρ τ hρ hX hQ G
  have hHP : H ∈ mCoordIdeal y := by
    rw [mCoordIdeal, RingHom.mem_ker, hc, hG]
    simp
  have h1 : MvPolynomial.map (Int.castRingHom ℂ) H ∈ pC (mCoordIdeal y) :=
    Ideal.subset_span ⟨H, hHP, rfl⟩
  have h2 : MvPolynomial.map (Int.castRingHom ℂ) H -
      MvPolynomial.C (N : ℂ) * MvPolynomial.map (algebraMap ℚ ℂ) G ∈ A := by
    refine Ideal.Quotient.eq.mp ?_
    have : π (MvPolynomial.C (N : ℂ)) = (N : MvPolynomial (Σ k, J k) ℂ ⧸ A) := by simp
    rw [map_mul, this]
    exact hr
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have h3 : MvPolynomial.C (N : ℂ) * MvPolynomial.map (algebraMap ℚ ℂ) G ∈
      ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := by
    have ha : MvPolynomial.map (Int.castRingHom ℂ) H ∈
        ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := Ideal.mem_sup_left h1
    have hb : MvPolynomial.map (Int.castRingHom ℂ) H -
        MvPolynomial.C (N : ℂ) * MvPolynomial.map (algebraMap ℚ ℂ) G ∈
        ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := Ideal.mem_sup_right h2
    simpa using Ideal.sub_mem _ ha hb
  have h4 := Ideal.mul_mem_left _ (MvPolynomial.C (N : ℂ)⁻¹) h3
  rwa [← _root_.mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hN', MvPolynomial.C_1, _root_.one_mul] at h4

end GlobalTheory.CompanionTheory.Ar.ChartDehom
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RationalRelationInChartIdealStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_relation_in_chart_ideal : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ G : MvPolynomial (Σ k, J k) ℚ,
    aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G = (0 : Ω) →
    map (algebraMap ℚ ℂ) G ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartDehom.map_mem_chartIdeal | exact GlobalTheory.CompanionTheory.Ar.ChartDehom.map_mem_chartIdeal | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartDehom.map_mem_chartIdeal <;> assumption)
end
end
