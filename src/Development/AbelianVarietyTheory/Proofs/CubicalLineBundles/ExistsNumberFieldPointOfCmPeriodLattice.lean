module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmTensorSmoothOfRelativeDimension

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CountablePointsOfOnto
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CMCount

theorem eq_top_of_countable {V L : Type} [AddCommGroup V] [Module ℂ V] [Countable L] (W : Submodule ℂ V) (P : L → V)
    (h : ∀ z, ∃ a, z - P a ∈ W) : W = ⊤ := by
  by_contra hW
  obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hW)
  choose a ha using h
  have : Function.Injective fun c : ℂ => a (c • v) := fun c d e => by
    by_contra hne
    have h1 := W.sub_mem (ha (c • v)) (ha (d • v))
    simp only at e
    rw [e, sub_sub_sub_cancel_right, ← sub_smul] at h1
    exact hv ((W.smul_mem_iff (sub_ne_zero.2 hne)).1 h1)
  have : Countable ℂ := this.countable
  exact not_countable (Complex.ofReal_injective.countable)

theorem exists_basis {V L J : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [AddCommGroup L]
    (b : Module.Basis J ℤ L) (P : L →+ V) (hi : Function.Injective P) (hd : DiscreteTopology P.range)
    (hs : Submodule.span ℝ (Set.range P) = ⊤) : ∃ B : Module.Basis J ℝ V, ∀ i, B i = P (b i) := by
  let Λ : Submodule ℤ V := LinearMap.range P.toIntLinearMap
  have : DiscreteTopology Λ := hd
  have : IsZLattice ℝ Λ := ⟨hs⟩
  refine ⟨(b.map (LinearEquiv.ofInjective P.toIntLinearMap hi)).ofZLatticeBasis ℝ Λ, fun i => ?_⟩
  rw [Module.Basis.ofZLatticeBasis_apply]
  rfl

theorem exists_real_equiv {V L : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [AddCommGroup L]
    (P P' : L →+ V) (hi : Function.Injective P) (hd : DiscreteTopology P.range)
    (hs : Submodule.span ℝ (Set.range P) = ⊤) (hi' : Function.Injective P') (hd' : DiscreteTopology P'.range)
    (hs' : Submodule.span ℝ (Set.range P') = ⊤) : ∃ h : V ≃ₗ[ℝ] V, ∀ a, P' a = h (P a) := by
  let Λ : Submodule ℤ V := LinearMap.range P.toIntLinearMap
  have : DiscreteTopology Λ := hd
  have : IsZLattice ℝ Λ := ⟨hs⟩
  have : Module.Free ℤ L := Module.Free.of_equiv (LinearEquiv.ofInjective P.toIntLinearMap hi).symm
  let b := Module.Free.chooseBasis ℤ L
  obtain ⟨B, hB⟩ := exists_basis b P hi hd hs
  obtain ⟨B', hB'⟩ := exists_basis b P' hi' hd' hs'
  refine ⟨B.equiv B' (Equiv.refl _), fun a => ?_⟩
  have : P'.toIntLinearMap = ((B.equiv B' (Equiv.refl _)).toLinearMap.restrictScalars ℤ).comp P.toIntLinearMap :=
    b.ext fun i => by simp [← hB, ← hB']
  exact LinearMap.congr_fun this a

theorem exists_complex_equiv {U V I : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [Module ℝ U] [Module ℝ V] [IsScalarTower ℝ ℂ U] [IsScalarTower ℝ ℂ V]
    (h : V ≃ₗ[ℝ] V) (F F' : I → (U →ₗ[ℂ] V)) (s : Set U) (hs : Submodule.span ℝ s = ⊤)
    (hF : ⨆ j, LinearMap.range (F j) = ⊤) (e : ∀ j, ∀ x ∈ s, F' j x = h (F j x)) :
    ∃ h' : V ≃ₗ[ℂ] V, ∀ v, h' v = h v := by
  have e' : ∀ j x, F' j x = h (F j x) := fun j x =>
    LinearMap.congr_fun (LinearMap.ext_on (f := (F' j).restrictScalars ℝ)
      (g := h.toLinearMap.comp ((F j).restrictScalars ℝ)) hs (e j)) x
  have hc : ∀ (c : ℂ) v, h (c • v) = c • h v := fun c v => by
    have hv : v ∈ ⨆ j, LinearMap.range (F j) := hF ▸ Submodule.mem_top
    induction hv using Submodule.iSup_induction' with
    | mem j x hx =>
      obtain ⟨x, rfl⟩ := hx
      rw [← map_smul, ← e', ← e', map_smul]
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]
  exact ⟨{ h.toAddEquiv with map_smul' := hc }, fun _ => rfl⟩

theorem exists_compare {S S' : Scheme.{0}} {G : Over S} {A B : Over S'} [GrpObj G] [GrpObj A] [GrpObj B] {f : S' ⟶ S}
    {α : A.left ⟶ G.left} {β : B.left ⟶ G.left} (hA : IsGrpPullback A G f α) (hB : IsGrpPullback B G f β) :
    ∃ κ : A ⟶ B, IsMonHom κ ∧ ∀ (T : Over S') (z : T ⟶ B), ∃ y : T ⟶ A, y ≫ κ = z := by
  let κ : A ⟶ B := Over.homMk (hB.1.lift α A.hom hA.1.w) (hB.1.lift_snd ..)
  have hκ : κ.left ≫ β = α := hB.1.lift_fst ..
  refine ⟨κ, isMonHom_of_mul κ fun T x y => ?_, fun T z => ?_⟩
  · let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk (x.left ≫ α) (by
      rw [Category.assoc, hA.1.w, Over.w_assoc]; rfl)
    let y₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk (y.left ≫ α) (by
      rw [Category.assoc, hA.1.w, Over.w_assoc]; rfl)
    refine Over.OverMorphism.ext (hB.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [← hB.2 T (x ≫ κ) (y ≫ κ) x₀ y₀ (by simp [x₀, hκ]) (by simp [y₀, hκ]), hA.2 T x y x₀ y₀ rfl rfl,
      Over.comp_left, Category.assoc, hκ]
  · refine ⟨Over.homMk (hA.1.lift (z.left ≫ β) T.hom (by rw [Category.assoc, hB.1.w, Over.w_assoc]))
      (hA.1.lift_snd ..), Over.OverMorphism.ext (hB.1.hom_ext ?_ ?_)⟩
    · simp [hκ]
    · rw [Over.w, Over.w]

theorem exists_linear_onto {A B : Over (Sp ℂ)} [GrpObj A] [GrpObj B] {A₀ : Over (Sp ℂ)} [GrpObj A₀]
    (h₀ : IsAbelianScheme A₀) (hB : IsAbelianScheme B) {L₀ : LB A₀.left} {L : LB B.left} {g₀ g : ℕ}
    (u₀ : HolUnif A₀ L₀ g₀) (u : HolUnif B L g)
    (d₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v) (d₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)
    (κ : A ⟶ B) [IsMonHom κ] (hκ : ∀ (T : Over (Sp ℂ)) (z : T ⟶ B), ∃ y : T ⟶ A, y ≫ κ = z)
    {I : Type} (ψ : I → (A₀ ⟶ A)) (hψ : ∀ i, IsMonHom (ψ i)) (ho : OntoAt ψ (𝟙 (Sp ℂ))) :
    ∃ F : I → ((Fin g₀ → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ j, ∀ x ∈ u₀.Λ, F j x ∈ u.Λ) ∧
      ∀ z, ∃ w ∈ ⨆ j, LinearMap.range (F j), z - w ∈ u.Λ := by
  choose F hF hΛ _ using fun j => HomLinear.exists_linear_of_isMonHom A₀ B h₀ hB L₀ L g₀ g u₀ u d₁ d₂ (ψ j ≫ κ) (by have := hψ j; infer_instance)
  refine ⟨F, hΛ, fun z => ?_⟩
  have key : ∀ l : List (𝟙_ (Over (Sp ℂ)) ⟶ A), (∀ y ∈ l, ∃ w ∈ ⨆ j, LinearMap.range (F j), y ≫ κ = u.ex w) →
      ∃ w ∈ ⨆ j, LinearMap.range (F j), l.prod ≫ κ = u.ex w := by
    intro l
    induction l with
    | nil => exact fun _ => ⟨0, Submodule.zero_mem _, by rw [(u.ker 0).2 u.Λ.zero_mem, List.prod_nil, MonObj.one_comp]⟩
    | cons y l ih =>
      intro h
      obtain ⟨w, hw, e⟩ := h y (by simp)
      obtain ⟨w', hw', e'⟩ := ih fun y hy => h y (by simp [hy])
      exact ⟨w + w', Submodule.add_mem _ hw hw', by rw [List.prod_cons, MonObj.mul_comp, e, e', u.ex_add]⟩
  obtain ⟨y, hy⟩ := hκ _ (u.ex z)
  obtain ⟨n, i, x, e⟩ := ho y
  obtain ⟨w, hw, e'⟩ := key (List.ofFn fun m => x m ≫ ψ (i m)) fun y hy => by
    obtain ⟨m, rfl⟩ := (List.mem_ofFn' _ _).1 hy
    obtain ⟨a, ha⟩ := u₀.ex_onto (x m)
    refine ⟨F (i m) a, Submodule.mem_iSup_of_mem (i m) ⟨a, rfl⟩, ?_⟩
    rw [hF, ha]
    exact Category.assoc ..
  refine ⟨w, hw, (u.ker _).1 ?_⟩
  have h1 : u.ex z = u.ex w := by rw [← hy, ← e', e]
  have h2 := u.ex_add (z - w) w
  rw [sub_add_cancel, h1] at h2
  exact mul_eq_right.1 h2.symm

end GlobalTheory.CMCount

namespace GlobalTheory

open CMCount

theorem countable_points_of_onto : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (P₀ : Out.PolAV (Sp ℂ)), Set.Countable {y : Sp ℂ ⟶ Xo.X | y ≫ Xo.s = spMap (algebraMap (KA l) ℂ) ∧ ∃ (t : SAB H (Sp ℂ)) (_ : SABMap t Xo.univ.t y) (n : ℕ) (ψ : Fin n → (P₀.A ⟶ t.G)), (∀ i, IsMonHom (ψ i)) ∧ OntoAt ψ (𝟙 (Sp ℂ))} := by
  intro hU hL E _ _ _ H D l Xo g ty FU P₀
  obtain ⟨rig, hrig⟩ := P₀.rigid
  obtain ⟨u₀, -⟩ := hU P₀ rig hrig
  obtain ⟨s, hsΛ, hs, hli⟩ := exists_linearIndependent ℝ (u₀.Λ : Set (Fin P₀.g → ℂ))
  rw [u₀.full] at hs
  have : Finite s := hli.finite
  have : Countable (𝓞 E) := Finsupp.Countable.of_moduleFinite (R := ℤ)
  have : ∀ i, Countable (FU.Di i).La := fun i =>
    have := (FU.Di i).fin
    Finsupp.Countable.of_moduleFinite (R := 𝓞 E)
  let R : (Sp ℂ ⟶ Xo.X) → (Σ i : Fin FU.n, Σ n : ℕ, Fin n → s → (FU.Di i).La) → Prop := fun y c =>
    ∃ P, IsPeriod (FU.Di c.1) ty P ∧ FU.u c.1 P = y ∧ ∃ F : Fin c.2.1 → ((Fin P₀.g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      ⨆ j, LinearMap.range (F j) = ⊤ ∧ ∀ j (x : s), F j x = P (c.2.2 j x)
  have huniq : ∀ c, {y | R y c}.Subsingleton := by
    rintro ⟨i, n, c⟩ _ ⟨P, hP, rfl, F, hF, e⟩ _ ⟨P', hP', rfl, F', -, e'⟩
    obtain ⟨h, hh⟩ := exists_real_equiv P P' hP.2.1 hP.2.2.1 hP.2.2.2.1 hP'.2.1 hP'.2.2.1 hP'.2.2.2.1
    obtain ⟨h', hh'⟩ := exists_complex_equiv h F F' s hs hF fun j x hx => by
      rw [e j ⟨x, hx⟩, e' j ⟨x, hx⟩, hh]
    exact (FU.fibre i P P' hP hP').2 ⟨LinearEquiv.refl _ _, h', fun _ _ => rfl, fun a _ => ⟨0, by simp⟩,
      fun a => ⟨0, by simp⟩, fun a => by rw [hh']; exact hh a⟩
  refine (Set.countable_iUnion fun c => (huniq c).countable).mono ?_
  rintro y ⟨hy, t, m, n, ψ, hψ, ho⟩
  obtain ⟨i, P, hP, rfl⟩ := FU.onto y hy
  obtain ⟨Q, φ, -, hQ, hQL, -⟩ := exists_polAV_pullback_of_isLocalRing E H _ Xo.univ.t Xo.univ.proper Xo.univ.ample
    Xo.univ.ktriv ℂ (FU.u i P)
  obtain ⟨u, -, -, Φ, -, d₁, d₂, -, -, hΦ, -⟩ := familyUnif_fibre_theta hU hL.weil E H D l Xo _ g ty FU i P hP Q φ hQ hQL
  obtain ⟨κ, hκ, hκ'⟩ := exists_compare m.cart hQ
  obtain ⟨F, hF, hF'⟩ := exists_linear_onto P₀.isAb Q.isAb u₀ u d₁ d₂ κ hκ' ψ hψ ho
  have hm : ∀ j (x : s), ∃ a, P a = Φ.symm (F j x) := fun j x =>
    (hΦ _).1 (by rw [Φ.apply_symm_apply]; exact hF j x (hsΛ x.2))
  choose c hc using hm
  refine Set.mem_iUnion.2 ⟨⟨i, n, c⟩, P, hP, rfl, fun j => Φ.symm.toLinearMap ∘ₗ F j, ?_, fun j x => (hc j x).symm⟩
  refine eq_top_of_countable _ P fun z => ?_
  obtain ⟨w, hw, hz⟩ := hF' (Φ z)
  obtain ⟨a, ha⟩ := (hΦ (z - Φ.symm w)).1 (by rwa [map_sub, Φ.apply_symm_apply])
  refine ⟨a, ?_⟩
  rw [ha, sub_sub_cancel]
  simp only [LinearMap.range_comp, ← Submodule.map_iSup]
  exact Submodule.mem_map_of_mem hw

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldPointOfCountable
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_numberField_factor (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k]
    {k₀ A : Type} [Field k₀] [CommRing A] (j : k₀ →+* k) (α : k₀ →+* A) (hα : α.FiniteType)
    (ψ : A →+* ℂ) (hψ : ∀ a, ψ (α a) = (j a : ℂ)) (halg : ∀ c, IsAlgebraic k (ψ c)) :
    ∃ (K₁ : IntermediateField ℚ ℂ) (hk : k ≤ K₁) (ψ₁ : A →+* K₁), FiniteDimensional ℚ K₁ ∧
      ψ₁.comp α = (IntermediateField.inclusion hk).toRingHom.comp j ∧
      (algebraMap K₁ ℂ).comp ψ₁ = ψ := by
  letI := α.toAlgebra
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (self := hα)
  haveI : Finite (ψ '' (t : Set A)) := (t.finite_toSet.image _).to_subtype
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (ψ '' (t : Set A))) := by
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨x, -, rfl⟩
    exact ((halg x).restrictScalars ℚ).isIntegral
  let K₁ : IntermediateField ℚ ℂ := k ⊔ IntermediateField.adjoin ℚ (ψ '' (t : Set A))
  have hk : k ≤ K₁ := le_sup_left
  have hmem : ∀ x, ψ x ∈ K₁ := by
    intro x
    have hx : x ∈ Algebra.adjoin k₀ (t : Set A) := ht ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      exact (le_sup_right : _ ≤ K₁) (IntermediateField.subset_adjoin ℚ _ ⟨x, hx, rfl⟩)
    | algebraMap r =>
      change ψ (α r) ∈ K₁
      rw [hψ]; exact hk (j r).2
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨K₁, hk, ψ.codRestrict K₁ hmem, IntermediateField.finiteDimensional_sup _ _, ?_, ?_⟩
  · ext a
    exact hψ a
  · rfl

theorem exists_fg_le_range_subset {k : Type} [Field k] [Algebra k ℂ] (R : Subalgebra k ℂ) (hR : R.FG)
    {X : Scheme.{0}} (y : Sp R ⟶ X) (U : X.Opens)
    (hU : (spMap R.val.toRingHom ≫ y) (IsLocalRing.closedPoint ℂ) ∈ U) :
    ∃ (R' : Subalgebra k ℂ) (h : R ≤ R'), R'.FG ∧
      Set.range (spMap (Subalgebra.inclusion h).toRingHom ≫ y) ⊆ (U : Set X) := by
  classical
  let p : PrimeSpectrum R := PrimeSpectrum.comap R.val.toRingHom (IsLocalRing.closedPoint ℂ)
  have hp : p ∈ ((y ⁻¹ᵁ U : (Sp R).Opens) : Set (Sp R)) := hU
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := p) (u := ((y ⁻¹ᵁ U : (Sp R).Opens) : Set (Sp R))) hp (y ⁻¹ᵁ U).2
  have hr0 : (r : ℂ) ≠ 0 := by
    intro h
    have : r = 0 := Subtype.ext h
    subst this
    exact hr (Ideal.zero_mem _)
  obtain ⟨t, ht⟩ := hR
  have hle : R ≤ Algebra.adjoin k (↑(insert (r : ℂ)⁻¹ t) : Set ℂ) := by
    conv_lhs => rw [← ht]
    exact Algebra.adjoin_mono (by simp)
  refine ⟨_, hle, ⟨_, rfl⟩, ?_⟩
  rintro _ ⟨q, rfl⟩
  have hq : PrimeSpectrum.comap (Subalgebra.inclusion hle).toRingHom q ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
    intro h
    have h' : Subalgebra.inclusion hle r ∈ q.asIdeal := h
    have hu : (r : ℂ)⁻¹ ∈ Algebra.adjoin k (↑(insert (r : ℂ)⁻¹ t) : Set ℂ) :=
      Algebra.subset_adjoin (by simp)
    have h1 : Subalgebra.inclusion hle r * ⟨_, hu⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hr0)
    exact q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ Ideal.mul_mem_right _ _ h'))
  exact hsub hq

theorem exists_numberField_point_of_countable :
    ∀ (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (R : Subalgebra k ℂ), R.FG → ∀ (k₀ : Type) [Field k₀] (j : k₀ →+* k) (X : Scheme.{0}) (s : X ⟶ Sp k₀) [LocallyOfFiniteType s] (y : Sp R ⟶ X), y ≫ s = spMap ((algebraMap k R).comp j) → Set.Countable (Set.range fun ρ : R →ₐ[k] ℂ => spMap ρ.toRingHom ≫ y) →
  ∃ (K₁ : IntermediateField ℚ ℂ) (hk : k ≤ K₁) (y₁ : Sp K₁ ⟶ X), FiniteDimensional ℚ K₁ ∧ y₁ ≫ s = spMap ((IntermediateField.inclusion hk).toRingHom.comp j) ∧ spMap (algebraMap K₁ ℂ) ≫ y₁ = spMap R.val.toRingHom ≫ y := by
  intro k _ R hR k₀ _ j X s _ y hy hc
  have hcomp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g => (Spec.map_comp _ _).symm
  have hinj : ∀ {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B}, spMap f = spMap g → f = g :=
    fun h => congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((spMap R.val.toRingHom ≫ y) (IsLocalRing.closedPoint ℂ))) isOpen_univ
  obtain ⟨R', hle, hR', hsub⟩ := exists_fg_le_range_subset R hR y U hxU
  have hU' : IsAffineOpen U := hU
  let A : Type := Γ(X, U)
  let i : Sp A ⟶ X := hU'.fromSpec
  haveI : IsOpenImmersion i := hU'.isOpenImmersion_fromSpec
  have hsub' : Set.range (spMap (Subalgebra.inclusion hle).toRingHom ≫ y) ⊆ Set.range i :=
    hsub.trans hU'.range_fromSpec.ge
  obtain ⟨φ, hφ⟩ : ∃ φ : A →+* R', spMap φ ≫ i = spMap (Subalgebra.inclusion hle).toRingHom ≫ y := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift i _ hsub')
    exact ⟨φ.hom, (congrArg (· ≫ i) hφ).trans (IsOpenImmersion.lift_fac _ _ _)⟩
  obtain ⟨α, hα⟩ : ∃ α : k₀ →+* A, spMap α = i ≫ s := by
    obtain ⟨α, hα⟩ := Spec.map_surjective (i ≫ s)
    exact ⟨α.hom, hα⟩
  have hft : α.FiniteType := by
    have : LocallyOfFiniteType (spMap α) := by rw [hα]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hφα : φ.comp α = (Subalgebra.inclusion hle).toRingHom.comp ((algebraMap k R).comp j) := by
    apply hinj
    rw [← hcomp, hα, ← Category.assoc, hφ, Category.assoc, hy, hcomp]
  have hcnt : Set.Countable ((fun ψ : A →+* ℂ => spMap ψ ≫ i) ⁻¹'
      (Set.range fun ρ : R →ₐ[k] ℂ => spMap ρ.toRingHom ≫ y)) :=
    hc.preimage_of_injOn fun a _ b _ h => hinj ((cancel_mono i).1 h)
  have halg : ∀ c, IsAlgebraic k ((R'.val.toRingHom.comp φ) c) := by
    intro c
    refine IsAlgebraic.algHom R'.val (a := φ c) ?_
    refine (specialisation_numberField_and_countable_values k R' hR' (φ c) 1 one_ne_zero).2
      _ (hcnt.image fun ψ => ψ c) fun ρ => ⟨ρ.toRingHom.comp φ, ⟨ρ.comp (Subalgebra.inclusion hle), ?_⟩, rfl⟩
    change spMap (ρ.toRingHom.comp (Subalgebra.inclusion hle).toRingHom) ≫ y = spMap (ρ.toRingHom.comp φ) ≫ i
    rw [← hcomp, ← hcomp, Category.assoc, Category.assoc, hφ]
  obtain ⟨K₁, hk, ψ₁, hfd, h1, h2⟩ := exists_numberField_factor k j α hft (R'.val.toRingHom.comp φ)
    (fun a => congrArg Subtype.val (RingHom.congr_fun hφα a)) halg
  refine ⟨K₁, hk, spMap ψ₁ ≫ i, hfd, ?_, ?_⟩
  · rw [Category.assoc, ← hα, hcomp, h1]
  · rw [← Category.assoc, hcomp, h2, ← hcomp, Category.assoc, hφ, ← Category.assoc, hcomp]
    rfl

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldPointOfCmPeriodLattice
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.PointAlg

section Points

variable {S S' X : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}

theorem prod_left (h : IsGrpPullback G' G f φ) {t' : X ⟶ S'} {t : X ⟶ S} (e : t' ≫ f = t) {n : ℕ}
    (x' : Fin n → (Over.mk t' ⟶ G')) (x : Fin n → (Over.mk t ⟶ G)) (hx : ∀ i, (x' i).left ≫ φ = (x i).left) :
    (List.ofFn x').prod.left ≫ φ = (List.ofFn x).prod.left := by
  subst e
  have h1 := map_list_prod (pushHom h (Over.mk t')) (List.ofFn x')
  rw [List.map_ofFn] at h1
  have h2 : (pushHom h (Over.mk t')) ∘ x' = x := funext fun i => Over.OverMorphism.ext (hx i)
  rw [h2] at h1
  exact congrArg (fun z => z.left) h1


omit [GrpObj G] [GrpObj G'] in
theorem exists_lift_pt (h : IsPullback φ G'.hom G.hom f) {t' : X ⟶ S'} (x : X ⟶ G.left) (e : x ≫ G.hom = t' ≫ f) :
    ∃ x' : Over.mk t' ⟶ G', x'.left ≫ φ = x :=
  ⟨Over.homMk (h.lift x t' e) (h.lift_snd _ _ _), h.lift_fst _ _ _⟩


omit [GrpObj G] [GrpObj G'] in
theorem pt_ext (h : IsPullback φ G'.hom G.hom f) {T : Over S'} {x y : T ⟶ G'} (e : x.left ≫ φ = y.left ≫ φ) : x = y :=
  Over.OverMorphism.ext (h.hom_ext e ((Over.w x).trans (Over.w y).symm))

theorem exists_lift_hom {H : Over S} {H' : Over S'} [GrpObj H] [GrpObj H'] {ψ : H'.left ⟶ H.left}
    (hG : IsGrpPullback G' G f φ) (hH : IsGrpPullback H' H f ψ) (w : G ⟶ H) [IsMonHom w] :
    ∃ w' : G' ⟶ H', IsMonHom w' ∧ w'.left ≫ ψ = φ ≫ w.left := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hG (isGrpPullback_pullback G f)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (isGrpPullback_pullback H f) hH
  refine ⟨a.hom ≫ (Over.pullback f).map w ≫ b.hom, inferInstance, ?_⟩
  have e : ((Over.pullback f).map w).left ≫ pullback.fst H.hom f = pullback.fst G.hom f ≫ w.left :=
    pullback.lift_fst _ _ _
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', e, ← Category.assoc, ha']

theorem onto_lift {B : Over S} {B' : Over S'} {β : B'.left ⟶ B.left} (hB : IsPullback β B'.hom B.hom f)
    (hG : IsGrpPullback G' G f φ) {n : ℕ} (w : Fin n → (B ⟶ G)) (w' : Fin n → (B' ⟶ G'))
    (hw : ∀ i, (w' i).left ≫ φ = β ≫ (w i).left) {t' : X ⟶ S'} {t : X ⟶ S} (e : t' ≫ f = t)
    (h : ∀ y : Over.mk t ⟶ G, ∃ x : Fin n → (Over.mk t ⟶ B), y = (List.ofFn fun i => x i ≫ w i).prod)
    (y : Over.mk t' ⟶ G') : ∃ x : Fin n → (Over.mk t' ⟶ B'), y = (List.ofFn fun i => x i ≫ w' i).prod := by
  subst e
  obtain ⟨x, hx⟩ := h (pushPt hG.1.w y)
  choose x' hx' using fun i => exists_lift_pt hB (t' := t') (x i).left (Over.w (x i))
  refine ⟨x', pt_ext hG.1 ?_⟩
  rw [prod_left hG rfl _ (fun i => x i ≫ w i) fun i => by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hw, ← Category.assoc, hx'], ← hx]
  rfl

end Points

theorem isAbelianScheme_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsAbelianScheme G) :
    ∀ n : ℕ, IsAbelianScheme (Out.powObj G n)
  | 0 => by
    have := hG.comm
    have : IsIso (Out.powObj G 0).hom := inferInstanceAs (IsIso (𝟙 S))
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstanceAs (GeometricallyConnected (𝟙 S))⟩
  | n + 1 => AbelianSchemeGerms.isAbelianScheme_powObj G hG n

theorem onto_of_onto {R : Type} [CommRing R] [IsDomain R] (σ : R →+* ℂ) (hσ : Function.Injective σ)
    {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {n : ℕ}
    (w : Fin n → (B ⟶ A))
    (h : ∀ y : Over.mk (spMap σ) ⟶ A, ∃ x : Fin n → (Over.mk (spMap σ) ⟶ B), y = (List.ofFn fun i => x i ≫ w i).prod)
    (t : Sp ℂ ⟶ Sp R) (y : Over.mk t ⟶ A) :
    ∃ x : Fin n → (Over.mk t ⟶ B), y = (List.ofFn fun i => x i ≫ w i).prod := by
  have := hA.comm
  have key : ∀ {T : Over (Sp R)} (x : T ⟶ Out.powObj B n),
      x ≫ (List.ofFn fun i => Out.powPr B i ≫ w i).prod = (List.ofFn fun i => (x ≫ Out.powPr B i) ≫ w i).prod := by
    intro T x
    have h1 := map_list_prod (preHom (G := A) x) (List.ofFn fun i => Out.powPr B i ≫ w i)
    rw [List.map_ofFn] at h1
    refine h1.trans ?_
    congr 2
  obtain ⟨x, hx⟩ := (OntoSurj.surjective_of_onto_complex_points R σ hσ A (Out.powObj B n)
    (List.ofFn fun i => Out.powPr B i ≫ w i).prod hA (isAbelianScheme_pow B hB n) fun y => by
      obtain ⟨x, hx⟩ := h y
      refine ⟨(Out.powIsLimit B n).lift (Fan.mk _ x), ?_⟩
      rw [key, hx]
      congr 2
      funext i
      exact congrArg (· ≫ w i) ((Out.powIsLimit B n).fac (Fan.mk _ x) ⟨i⟩).symm).2 ℂ t y
  exact ⟨fun i => x ≫ Out.powPr B i, by rw [hx, key]⟩

theorem map_sum_eq_prod {V Q : Type} [AddCommGroup V] [Group Q] (e : V → Q) (he : ∀ z w, e (z + w) = e z * e w)
    {n : ℕ} (z : Fin n → V) : e (∑ i, z i) = (List.ofFn fun i => e (z i)).prod := by
  induction n with
  | zero =>
    have := he 0 0
    rw [add_zero] at this
    simpa using this.symm
  | succ n ih => rw [Fin.sum_univ_succ, he, ih, List.ofFn_succ, List.prod_cons]


set_option maxHeartbeats 1000000 in
theorem exists_numberField_point_of_cmLat : CMCurve → CMPoint → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (p q : ℕ), Nonempty (CMLat hP p q) → ∃ (K₁ : IntermediateField ℚ ℂ) (hk : KA l ≤ K₁) (y : Sp K₁ ⟶ Xo.X), FiniteDimensional ℚ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe := by
  intro hC hPt hT hL E _ _ _ H D l Xo g ty FU i Pe hP p q ⟨Z⟩
  have hd := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg H.d_prime.pos
  obtain ⟨M, _, w, P, v, hw, hg, hv, -, hcm, -⟩ := hC H.d (by omega) H.d_prime.squarefree (by omega) K h2 hr
  have := PureType.finiteDimensional_base l
  let k : IntermediateField ℚ ℂ := M ⊔ KA l
  have hk : KA l ≤ k := le_sup_right
  have hfin : FiniteDimensional ℚ k := inferInstance
  let f : 𝓞 M →+* k := (IntermediateField.inclusion (le_sup_left : M ≤ k)).toRingHom.comp (algebraMap (𝓞 M) M)
  obtain ⟨P₀, π, hg₀, hπ, hL₀⟩ := PureType.exists_baseChange hL.polBaseChange (spMap f) P
  obtain ⟨PC, ψ, hgC, hψ, hLC⟩ := PureType.exists_baseChange hL.polBaseChange (spMap (algebraMap k ℂ)) P₀
  obtain ⟨v₀, hv₀, -⟩ := PureType.exists_tangent_over f hπ (hv.1 0)
  obtain ⟨u₀, hu⟩ := PureType.exists_isThetaUnif hT PC
  have hLL : LBIso PC.L (P.L.pull (ψ ≫ π)) :=
    LBIso.trans PC.isLB (pull_isLB P₀.isLB ψ) (pull_isLB P.isLB _) hLC
      (LBIso.chartPull (Geo.Tor.chartPullPull P₀.L ψ ψ rfl) (chartPullSame P.L _ _ _ ψ fun _ => rfl) hL₀)
  obtain ⟨c, hc0, hc⟩ := hcm PC (ψ ≫ π) ⟨hgC.trans hg₀, (hψ.comp hπ).congr (spMap_comp_spMap _ _) rfl, hLL.symm⟩ u₀
  rw [hw] at hc
  obtain ⟨R, hR, -, y, t, m, vR, φ, hy, hj, -, -, hφ⟩ := hPt E H D l Xo g ty FU i Pe hP k hk hfin P₀ v₀ (hg₀.trans hg) hv₀
    PC ψ u₀ c (hgC.trans (hg₀.trans hg)) hψ hLC hu hc0 hc (fun _ => ∅) (fun _ => Set.finite_empty) ⊥ Subalgebra.fg_bot
  obtain ⟨ε, a, ha⟩ := exists_pure_vectors_periods_span E H _ g ty Pe hP p q Z
  have hρ : ∀ ρ : R →ₐ[k] ℂ, spMap ρ.toRingHom ≫ spMap (algebraMap k R) = spMap (algebraMap k ℂ) := fun ρ =>
    (spMap_comp_spMap _ _).trans (congrArg _ ρ.comp_algebraMap)
  have hB := isGrpPullback_pullback P₀.A (spMap (algebraMap k R))
  have hA : IsAbelianScheme t.G := by
    have := Xo.univ.proper
    have : IsProper t.G.hom := MorphismProperty.of_isPullback m.cart.1 this
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ t.semi
  have onto := onto_of_onto R.val.toRingHom Subtype.val_injective hA
    (Out.TLinPf.isAb_pullback (spMap (algebraMap k R)) P₀.A P₀.isAb) (fun n => φ (ε n) (a n)) fun y' => by
      obtain ⟨z, hz⟩ := FU.ex_onto i Pe hP (Over.homMk (y'.left ≫ m.φ) (by
        rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w y']
        exact hj))
      obtain ⟨b, rfl⟩ := ha z
      choose x hx using fun n => exists_lift_pt (G := P₀.A) (G' := (Over.pullback (spMap (algebraMap k R))).obj P₀.A) hB.1 (t' := spMap R.val.toRingHom)
        ((u₀.ex fun _ => c * b n).left ≫ ψ) (by
          rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w, hρ]
          exact Category.id_comp _)
      refine ⟨x, pt_ext m.cart.1 ?_⟩
      rw [prod_left m.cart hj _ (fun n => FU.ex i Pe (b n • Pe (a n))) fun n =>
        (Category.assoc _ _ _).trans ((hφ (ε n)).2 (a n) (b n) (x n).left (hx n) (Over.w (x n))),
        ← map_sum_eq_prod _ (FU.ex_add i Pe hP), hz]
      rfl
  have hs : Smooth Xo.s := by
    have := Xo.smooth
    exact SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨K₁, hk₁, y₁, h₁, h₂, h₃⟩ := exists_numberField_point_of_countable k R hR (KA l)
    (IntermediateField.inclusion hk).toRingHom Xo.X Xo.s y hy (by
      refine (countable_points_of_onto hT hL E H D l Xo g ty FU PC).mono ?_
      rintro _ ⟨ρ, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [Category.assoc, hy, spMap_comp_spMap]
        exact congrArg spMap (RingHom.ext fun x => ρ.commutes _)
      obtain ⟨t', ⟨m'⟩⟩ : ∃ t' : SAB H (Sp ℂ), Nonempty (SABMap t' Xo.univ.t (spMap ρ.toRingHom ≫ y)) := by
        obtain ⟨_, _, _, _, _, m', -⟩ := sabPull Out.CubePf.cubePull (spMap ρ.toRingHom ≫ y) Xo.univ.t
        exact ⟨_, ⟨m'⟩⟩
      let κ := m.cart.1.lift m'.φ (t'.G.hom ≫ spMap ρ.toRingHom) (by rw [m'.cart.1.w, Category.assoc])
      have hγ : IsGrpPullback t'.G t.G (spMap ρ.toRingHom) κ :=
        m.cart.cancel (m'.cart.congr rfl (m.cart.1.lift_fst _ _ _).symm) (m.cart.1.lift_snd _ _ _)
      let β := hB.1.lift ψ (PC.A.hom ≫ spMap ρ.toRingHom) (by rw [hψ.1.w, Category.assoc, hρ])
      have hβ : IsGrpPullback PC.A _ (spMap ρ.toRingHom) β :=
        hB.cancel (hψ.congr (hρ ρ).symm (hB.1.lift_fst _ _ _).symm) (hB.1.lift_snd _ _ _)
      choose w' hw₁ hw₂ using fun n => @exists_lift_hom _ _ _ _ _ _ _ _ _ _ _ _ _ hβ hγ (φ (ε n) (a n))
        ((hφ (ε n)).1.1 (a n))
      refine ⟨t', m', _, w', hw₁, fun y' => ?_⟩
      obtain ⟨x, hx⟩ := onto_lift hβ.1 hγ _ w' hw₂ (Category.id_comp _) (onto _) y'
      exact ⟨_, id, x, hx⟩)
  exact ⟨K₁, hk.trans hk₁, y₁, h₁, h₂, h₃.trans hj⟩

end GlobalTheory.PointAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldPointOfCmPeriodLatticeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numberField_point_of_cmPeriodLattice : CMCurve → CMPoint → ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (p q : ℕ), Nonempty (CMLat hP p q) → ∃ (K₁ : IntermediateField ℚ ℂ) (hk : KA l ≤ K₁) (y : Sp K₁ ⟶ Xo.X), FiniteDimensional ℚ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe := by
  first | exact @GlobalTheory.PointAlg.exists_numberField_point_of_cmLat | exact GlobalTheory.PointAlg.exists_numberField_point_of_cmLat | (intros; apply GlobalTheory.PointAlg.exists_numberField_point_of_cmLat <;> assumption)
end
