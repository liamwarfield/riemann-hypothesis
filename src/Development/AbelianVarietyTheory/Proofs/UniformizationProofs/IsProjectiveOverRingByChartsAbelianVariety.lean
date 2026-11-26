module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfFinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecNonzeroLocusEqOfIsAffineOpenOfFactorial
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_sec_nonzeroLocus_eq_of_isAffineOpen_of_factorial :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated], (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∀ U : X.Opens, IsAffineOpen U → (U : Set X).Nonempty → ∃ (L : LB X) (s : LB.Sec L), L.IsLB ∧ nonzeroLocus s = U :=
  fun X _ _ _ hX U hU hne => GlobalTheory.T.exists_nonzeroLocus_eq_affineOpen_locallyFactorial X U hU hne hX

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinFlatChartOfOpenImmersion
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct

namespace GlobalTheory.Unif

theorem finFlatChart_of_openImmersion {X Y Z S B : Scheme.{0}} (f : X ⟶ B) (s : S ⟶ B)
    (j : Y ⟶ X) [IsOpenImmersion j] (i : Z ⟶ S) [IsOpenImmersion i] (p : Y ⟶ Z)
    [IsFinite p] [Flat p] [Surjective p] [Nonempty Z] (h : p ≫ i ≫ s = j ≫ f) :
    ∃ (W : X.Opens) (V : S.Opens) (π : W.toScheme ⟶ V.toScheme), (W : Set X).Nonempty ∧
      IsFinite π ∧ Flat π ∧ Surjective π ∧ π ≫ V.ι ≫ s = W.ι ≫ f := by
  obtain ⟨y, -⟩ := p.surjective (Classical.arbitrary Z)
  refine ⟨j.opensRange, i.opensRange, j.isoOpensRange.inv ≫ p ≫ i.isoOpensRange.hom,
    ⟨j y, y, rfl⟩, inferInstance, inferInstance, inferInstance, ?_⟩
  simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι_assoc, h]
  rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι_assoc]

theorem exists_finFlat_away (R A : Type) [CommRing R] [CommRing A] [IsDomain R]
    [IsNoetherianRing R] (φ : R →+* A) (hφ : φ.Finite) (hi : Function.Injective φ) :
    ∃ (Y Z : Scheme.{0}) (j : Y ⟶ Spec (CommRingCat.of A)) (i : Z ⟶ Spec (CommRingCat.of R))
      (p : Y ⟶ Z), IsOpenImmersion j ∧ IsOpenImmersion i ∧ IsFinite p ∧ Flat p ∧ Surjective p ∧
      Nonempty Z ∧ p ≫ i = j ≫ Spec.map (CommRingCat.ofHom φ) := by
  algebraize [φ]
  have : Module.FinitePresentation R A := Module.finitePresentation_of_finite R A
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors R) (LocalizedModule.mkLinearMap (nonZeroDivisors R) A) (FractionRing R)
  have hfree' : Module.Free (Localization.Away r) (Localization.Away r ⊗[R] A) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers r) A)
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R (Localization.Away r) A)
  have h1 : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
    rw [IsFinite.SpecMap_iff]; exact hφ
  have h2 : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    ⟨hφ.to_isIntegral.comap_surjective hi⟩
  have h3 : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) :=
    inferInstance
  have hd : IsDomain (Localization.Away r) :=
    IsLocalization.isDomain_localization (Submonoid.powers_le.mpr hr)
  refine ⟨_, _, _, _, _, MorphismProperty.of_isPullback hpb h3, h3,
    MorphismProperty.of_isPullback hpb.flip h1, ?_, MorphismProperty.of_isPullback hpb.flip h2,
    inferInstanceAs (Nonempty (PrimeSpectrum (Localization.Away r))), hpb.w⟩
  rw [Flat.SpecMap_iff]
  exact (RingHom.flat_algebraMap_iff (R := Localization.Away r)
    (S := Localization.Away r ⊗[R] A)).mpr inferInstance

theorem exists_finite_flat_chart : ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f], ∃ (g : ℕ) (W : X.Opens) (V : (Spec (CommRingCat.of (MvPolynomial (Fin g) K))).Opens) (π : W.toScheme ⟶ V.toScheme), (W : Set X).Nonempty ∧ IsFinite π ∧ Flat π ∧ Surjective π ∧ π ≫ V.ι ≫ (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K)))) = W.ι ≫ f := by
  intro K _ X _ f _
  obtain ⟨_, ⟨U, hU, rfl⟩, hξ, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  replace hU : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨_, hξ⟩⟩
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (hU.fromSpec ≫ f)
  have hft : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  have hft' : ψ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft
  letI : Algebra K Γ(X, U) := ψ.hom.toAlgebra
  have : Algebra.FiniteType K Γ(X, U) := hft'
  obtain ⟨g, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K Γ(X, U)
  obtain ⟨Y, Z, j, i, p, _, _, _, _, _, _, h⟩ :=
    exists_finFlat_away _ _ φ.toRingHom hfin hinj
  refine ⟨g, finFlatChart_of_openImmersion f _ (j ≫ hU.fromSpec) i p ?_⟩
  rw [reassoc_of% h, Category.assoc, ← hψ, ← Spec.map_comp]
  congr 2
  ext x
  exact φ.commutes x

end GlobalTheory.Unif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLbIsoPullAffineSpace
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.PicAffineSpace

theorem form_smul_comm {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] [Module.Invertible B M]
    (φ : M →ₗ[B] B) (s m : M) : φ s • m = φ m • s := by
  have h := congrArg (fun z => TensorProduct.lid B M (φ.rTensor M z))
    (Module.Invertible.tmul_comm (R := B) (m₁ := s) (m₂ := m))
  simpa using h

theorem exists_pairing_notMem {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Invertible A M] (P : Ideal A) (hP : P ≠ ⊤) : ∃ (φ : M →ₗ[A] A) (m : M), φ m ∉ P := by
  by_contra h
  push Not at h
  apply hP
  rw [Ideal.eq_top_iff_one]
  obtain ⟨z, hz⟩ := (Module.Invertible.bijective (R := A) (M := M)).2 1
  rw [← hz]
  clear hz
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul φ m => simpa using h φ m
  | add x y hx hy => rw [map_add (f := _)]; exact P.add_mem hx hy

theorem exists_generator_away {A B M σ : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] (E : MvPolynomial σ A ≃+* B) [AddCommGroup M] [Module B M] [Module.Invertible B M]
    (P : Ideal A) (hP : P ≠ ⊤) :
    ∃ (s : M) (a : A), a ∉ P ∧ ∀ m : M, ∃ r : B, E (MvPolynomial.C a) • m = r • s := by
  letI : Algebra A B := ((E : MvPolynomial σ A →+* B).comp (algebraMap A _)).toAlgebra
  obtain ⟨M₀, hM₀⟩ := (pic_mapAlgebra_mvPolynomial_bijective A σ).2
    (CommRing.Pic.mapRingHom (E.symm : B →+* MvPolynomial σ A) (CommRing.Pic.mk B M))
  have h : CommRing.Pic.mapAlgebra A B M₀ = CommRing.Pic.mk B M := by
    have := congrArg (CommRing.Pic.mapRingHom (E : MvPolynomial σ A →+* B)) hM₀
    rw [← CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapRingHom_mapRingHom,
      CommRing.Pic.mapRingHom_mapRingHom, RingEquiv.comp_symm, CommRing.Pic.mapRingHom_id_apply] at this
    rw [← CommRing.Pic.mapRingHom_algebraMap]
    exact this
  obtain ⟨e⟩ : Nonempty (B ⊗[A] M₀ ≃ₗ[B] M) := CommRing.Pic.mk_eq_mk_iff.mp h
  obtain ⟨φ, m₀, hφ⟩ := exists_pairing_notMem (M := M₀) P hP
  let ψ : M →ₗ[B] B := (TensorProduct.AlgebraTensorModule.rid A B B).toLinearMap ∘ₗ
    φ.baseChange B ∘ₗ e.symm.toLinearMap
  refine ⟨e (1 ⊗ₜ m₀), φ m₀, hφ, fun m => ⟨ψ m, ?_⟩⟩
  rw [← form_smul_comm]
  congr 1
  simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.rid_tmul]
  rw [Algebra.smul_def, _root_.mul_one]
  rfl

variable {X Y : Scheme.{0}}

theorem exists_lbIso_pull_of_local (p : Y ⟶ X) (e : X ⟶ Y) (he : e ≫ p = 𝟙 X) {N : LB Y} (hN : N.IsLB)
    (hu : ∀ V : X.Opens, IsAffineOpen V → ∀ u : Γ(Y, p ⁻¹ᵁ V)ˣ, ∃ v : Γ(X, V)ˣ, u = pullU p V v)
    (hl : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ s : ∀ i, Γ(Y, p ⁻¹ᵁ U ⊓ N.U i)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (i j : N.ι), p (f z) ∈ U → f z ∈ N.U i → f z ∈ N.U j →
        gm f z _ (s i) = gm f z _ (N.g i j) * gm f z _ (s j)) :
    ∃ N₀ : LB X, N₀.IsLB ∧ LBIso N (N₀.pull p) := by
  choose U hU s hs using hl
  have hep : ∀ x : X, p (e x) = x := fun x => congrArg (fun q => q x) he
  have base : ∀ (W : X.Opens) (u : Γ(Y, p ⁻¹ᵁ W)ˣ) (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z), p (f z) ∈ W →
      gm ((f ≫ p) ≫ e) z _ u = gm f z _ u := by
    intro W u Z f z hz
    obtain ⟨V, hV, hx, hVW⟩ : ∃ V : X.Opens, IsAffineOpen V ∧ p (f z) ∈ V ∧ V ≤ W := by
      obtain ⟨_, ⟨V, hV, rfl⟩, hx, hVW⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hz W.isOpen
      exact ⟨V, hV, hx, hVW⟩
    obtain ⟨v, hv⟩ := hu V hV (res (p.preimage_mono hVW) u)
    have hx' : p (((f ≫ p) ≫ e) z) ∈ V := (congrArg (· ∈ V) (hep (p (f z)))).mpr hx
    rw [← gm_res f z (p.preimage_mono hVW) hx, ← gm_res _ z (p.preimage_mono hVW) hx', hv,
      gm_pull _ _ _ _ hx, gm_pull _ _ _ _ hx', Category.assoc, he, Category.comp_id]
  have quot : ∀ x y : X, ∃ h : Γ(Y, p ⁻¹ᵁ (U x ⊓ U y))ˣ, ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (i : N.ι),
      p (f z) ∈ U x → p (f z) ∈ U y → f z ∈ N.U i →
        gm f z _ h = gm f z _ (s y i) * (gm f z _ (s x i))⁻¹ := by
    intro x y
    let W : N.ι → Y.Opens := fun i => p ⁻¹ᵁ (U x ⊓ U y) ⊓ N.U i
    have l₁ : ∀ i, W i ≤ p ⁻¹ᵁ U x ⊓ N.U i := fun i _ hz => ⟨hz.1.1, hz.2⟩
    have l₂ : ∀ i, W i ≤ p ⁻¹ᵁ U y ⊓ N.U i := fun i _ hz => ⟨hz.1.2, hz.2⟩
    have v : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (i : N.ι), f z ∈ W i →
        gm f z (W i) (res (l₂ i) (s y i) * (res (l₁ i) (s x i))⁻¹) =
          gm f z _ (s y i) * (gm f z _ (s x i))⁻¹ := fun Z f z i hz => by
      rw [map_mul, map_inv, gm_res f z _ hz, gm_res f z _ hz]
    obtain ⟨h, hh⟩ := glue_unit (p ⁻¹ᵁ (U x ⊓ U y)) W (fun _ => inf_le_left) (fun z hz => by
        obtain ⟨i, hi⟩ := exists_chart hN z
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hz, hi⟩)
      (fun i => res (l₂ i) (s y i) * (res (l₁ i) (s x i))⁻¹) (fun i j z hz => by
        rw [v _ _ z i hz.1, v _ _ z j hz.2, hs x _ (𝟙 Y) z i j hz.1.1.1 hz.1.2 hz.2.2,
          hs y _ (𝟙 Y) z i j hz.1.1.2 hz.1.2 hz.2.2, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel,
          _root_.one_mul])
    refine ⟨h, fun Z f z i hx hy hi => ?_⟩
    have hz : f z ∈ W i := ⟨⟨hx, hy⟩, hi⟩
    rw [← v Z f z i hz, ← hh i, gm_res f z _ hz]
  choose h hh using quot
  have l : ∀ x y, U x ⊓ U y ≤ e ⁻¹ᵁ (p ⁻¹ᵁ (U x ⊓ U y)) := fun x y z hz =>
    (congrArg (· ∈ U x ⊓ U y) (hep z)).mpr hz
  let N₀ : LB X := ⟨X, U, fun x y => res (l x y) (pullU e _ (h x y))⟩
  have g₀ : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (x y : X), f z ∈ U x → f z ∈ U y →
      gm f z (U x ⊓ U y) (N₀.g x y) = gm (f ≫ e) z _ (h x y) := fun Z f z x y hx hy =>
    (gm_res f z (l x y) ⟨hx, hy⟩ _).trans (gm_pull f e z _ (l x y ⟨hx, hy⟩) _)
  have coc : ∀ (z : X) (a b c : X), z ∈ U a → z ∈ U b → z ∈ U c →
      gm (𝟙 X) z (U a ⊓ U b) (N₀.g a b) * gm (𝟙 X) z (U b ⊓ U c) (N₀.g b c) =
        gm (𝟙 X) z (U a ⊓ U c) (N₀.g a c) := by
    intro z a b c ha hb hc
    obtain ⟨i, hi⟩ := exists_chart hN (e z)
    have m : ∀ d, z ∈ U d → p ((𝟙 X ≫ e) z) ∈ U d := fun d hd => (congrArg (· ∈ U d) (hep z)).mpr hd
    rw [g₀ _ _ z a b ha hb, g₀ _ _ z b c hb hc, g₀ _ _ z a c ha hc,
      hh a b _ _ z i (m a ha) (m b hb) hi, hh b c _ _ z i (m b hb) (m c hc) hi,
      hh a c _ _ z i (m a ha) (m c hc) hi, mul_comm, _root_.mul_assoc, inv_mul_cancel_left]
  refine ⟨N₀, ⟨top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hU x⟩,
    fun a => unit_ext fun z hz => ?_, fun a b c => unit_ext fun z hz => ?_⟩, ?_⟩
  · rw [gm_res _ z _ hz, map_one]
    exact mul_eq_left.1 (coc z a a a hz hz hz)
  · exact (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res _ z _ hz _) (gm_res _ z _ hz _)).trans
      ((coc z a b c hz.1.1 hz.1.2 hz.2).trans (gm_res _ z _ hz _).symm))
  · have lw : ∀ (J : (N₀.pull p).ι) (k : N.ι), (N₀.pull p).U J ⊓ N.U k ≤ p ⁻¹ᵁ U (J PUnit.unit) ⊓ N.U k :=
      fun J k z hz => ⟨mem_pull.1 hz.1, hz.2⟩
    refine ⟨⟨fun q => (res (lw q.1 q.2) (s (q.1 PUnit.unit) q.2))⁻¹⟩, (isGen_iff _).2 ?_⟩
    intro Z f z x y k k' hx hy hk hk'
    have w : ∀ (a : X) (i : N.ι), p (f z) ∈ U a → f z ∈ N.U i →
        gw (L := N₀) (⟨fun q => (res (lw q.1 q.2) (s (q.1 PUnit.unit) q.2))⁻¹⟩ : LB.Iso N (N₀.pull p)) f z a i =
          (gm f z _ (s a i))⁻¹ := fun a i ha hi =>
      (map_inv _ _).trans (congrArg (·⁻¹) (gm_res f z (lw (fun _ => a) i) ⟨mem_pull.2 ha, hi⟩ _))
    have e₁ := (g₀ Z (f ≫ p) z x y hx hy).trans ((base (U x ⊓ U y) _ Z f z ⟨hx, hy⟩).trans (hh x y Z f z k hx hy hk))
    rw [w x k hx hk, w y k' hy hk']
    refine Eq.trans ?_ (congrArg (fun t => t * _ * _) e₁).symm
    rw [hs y Z f z k k' hy hk hk']
    have grp : ∀ {G : Type} [CommGroup G] (a b c : G), a⁻¹ = b * c * a⁻¹ * b⁻¹ * c⁻¹ := fun a b c => by
      rw [_root_.mul_assoc, ← mul_inv, mul_right_comm, mul_inv_cancel, _root_.one_mul]
    exact grp _ _ _

theorem exists_local_generator (p : Y ⟶ X) {N : LB Y} (hN : N.IsLB) {V : X.Opens}
    (hV : IsAffineOpen (p ⁻¹ᵁ V)) [IsDomain Γ(X, V)] [IsIntegrallyClosed Γ(X, V)] {σ : Type}
    (E : MvPolynomial σ Γ(X, V) ≃+* Γ(Y, p ⁻¹ᵁ V)) (hE : ∀ a, E (MvPolynomial.C a) = (p.app V).hom a)
    {x : X} (hx : x ∈ V) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ s : ∀ i, Γ(Y, p ⁻¹ᵁ U ⊓ N.U i)ˣ,
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (i j : N.ι), p (f z) ∈ U → f z ∈ N.U i → f z ∈ N.U j →
        gm f z _ (s i) = gm f z _ (N.g i j) * gm f z _ (s j) := by
  haveI := SecOn.invertible hN hV
  obtain ⟨s, a, ha, hs⟩ := exists_generator_away (M := SecOn N (p ⁻¹ᵁ V)) E
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.germ V x hx).hom)
    (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
  rw [hE] at hs
  have l : ∀ i, p ⁻¹ᵁ X.basicOpen a ⊓ N.U i ≤ p ⁻¹ᵁ V ⊓ N.U i := fun i =>
    inf_le_inf_right _ (p.preimage_mono (X.basicOpen_le a))
  have hu : ∀ i, IsUnit (rs Y (l i) (GlobalTheory.LB.coord s i)) := fun i =>
    Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      obtain ⟨b, hb, hyb⟩ := hV.exists_basicOpen_le (V := p ⁻¹ᵁ X.basicOpen a ⊓ N.U i) ⟨y, hy⟩ (l i hy).1
      have hi : Y.basicOpen b ≤ N.U i := hb.trans inf_le_right
      obtain ⟨n, t, ht⟩ := SecOn.exists_pow_smul_eq_restrict hN hV.isCompact hV.isQuasiSeparated b
        (Y.basicOpen_le b) rfl ((SecOn.chart hN i hi).symm 1)
      obtain ⟨r, hr⟩ := hs t
      have h₁ := congrArg (fun m => SecOn.chart hN i hi (SecOn.restrict N (Y.basicOpen_le b) m)) hr
      simp only [LinearMap.map_smulₛₗ, ← ht, map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul,
        _root_.mul_one] at h₁
      have u₁ : IsUnit (rs Y (Y.basicOpen_le b) b) := Y.toRingedSpace.isUnit_res_basicOpen b
      have u₂ : IsUnit (rs Y (Y.basicOpen_le b) ((p.app V).hom a)) := by
        have hle : Y.basicOpen b ≤ Y.basicOpen ((p.app V).hom a) := by
          rw [← Scheme.preimage_basicOpen]
          exact hb.trans inf_le_left
        have := (Y.toRingedSpace.isUnit_res_basicOpen ((p.app V).hom a)).map (rs Y hle)
        exact (congrArg IsUnit (rs_rs (Y.basicOpen_le _) hle _)).mp this
      have u₃ := isUnit_of_mul_isUnit_right (h₁ ▸ u₂.mul (u₁.pow n))
      have e₁ : SecOn.chart hN i hi (SecOn.restrict N (Y.basicOpen_le b) s) =
          rs Y hb (rs Y (l i) (GlobalTheory.LB.coord s i)) := by
        rw [SecOn.chart_apply, SecOn.coord_restrict, rs_rs, rs_rs]
      rw [e₁] at u₃
      exact (congrArg IsUnit (TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hb) y hyb _)).mp
        (u₃.map (Y.presheaf.germ _ y hyb).hom)
  refine ⟨X.basicOpen a, (X.mem_basicOpen a x hx).2 (IsLocalRing.notMem_maximalIdeal.1 ha),
    fun i => (hu i).unit, fun Z f z i j h hi hj => ?_⟩
  let O := p ⁻¹ᵁ X.basicOpen a ⊓ N.U i ⊓ N.U j
  have hz : f z ∈ O := ⟨⟨h, hi⟩, hj⟩
  have l₁ : O ≤ p ⁻¹ᵁ X.basicOpen a ⊓ N.U i := inf_le_left
  have l₂ : O ≤ p ⁻¹ᵁ X.basicOpen a ⊓ N.U j := inf_le_inf_right _ inf_le_left
  have l₃ : O ≤ N.U i ⊓ N.U j := inf_le_inf_right _ inf_le_right
  have : res l₁ (hu i).unit = res l₃ (N.g i j) * res l₂ (hu j).unit := Units.ext <|
    (rs_rs (l i) l₁ _).trans ((SecOn.compat s i j _ (l₂.trans (l j)) l₃).trans
      (congrArg _ (rs_rs (l j) l₂ _).symm))
  rw [← gm_res f z l₁ hz, this, map_mul, gm_res f z _ hz, gm_res f z _ hz]

theorem exists_ringEquiv_mvPolynomial {K σ : Type} [CommRing K] {f : X ⟶ Spec (CommRingCat.of K)}
    {p : Y ⟶ X} {f' : Y ⟶ Spec (CommRingCat.of (MvPolynomial σ K))}
    (H : IsPullback p f' f (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial σ K)))))
    {V : X.Opens} (hV : IsAffineOpen V) :
    ∃ E : MvPolynomial σ Γ(X, V) ≃+* Γ(Y, p ⁻¹ᵁ V), ∀ a, E (MvPolynomial.C a) = (p.app V).hom a := by
  letI := cstAlgebra f V
  letI : Algebra (MvPolynomial σ K) (MvPolynomial σ Γ(X, V)) := MvPolynomial.algebraMvPolynomial
  have h₁ := isPushout_cst H hV (V' := p ⁻¹ᵁ V) rfl
  have h₂ := CommRingCat.isPushout_iff_isPushout.mpr
    (inferInstance : Algebra.IsPushout K (MvPolynomial σ K) Γ(X, V) (MvPolynomial σ Γ(X, V)))
  refine ⟨(IsPushout.isoIsPushout _ _ h₂ h₁).commRingCatIsoToRingEquiv, fun a => ?_⟩
  have := congrArg (fun q => q.hom a) (IsPushout.inr_isoIsPushout_hom _ _ h₂ h₁)
  rw [Scheme.Hom.app_eq_appLE]
  exact this

end GlobalTheory.PicAffineSpace

namespace GlobalTheory

open PicAffineSpace

theorem exists_lbIso_pull_affineSpace : ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))) [IsIntegral X.left] [IsLocallyNoetherian X.left], (∀ x : X.left, UniqueFactorizationMonoid (X.left.presheaf.stalk x)) → ∀ (g : ℕ) (N : LB (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K)))) ⊗ X).left), N.IsLB → ∃ N₀ : LB X.left, N₀.IsLB ∧ LBIso N (N₀.pull (snd _ X).left) := by
  intro K _ X _ _ hX g N hN
  let A : Over (Spec (CommRingCat.of K)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K))))
  have H : IsPullback (snd A X).left (fst A X).left X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K)))) :=
    (IsPullback.of_hasPullback A.hom X.hom).flip
  let z : MvPolynomial (Fin g) K →ₐ[K] K := MvPolynomial.aeval fun _ => 0
  let e : X.left ⟶ (A ⊗ X).left := H.lift (𝟙 _) (X.hom ≫ Spec.map (CommRingCat.ofHom z.toRingHom)) (by
    rw [Category.id_comp, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : z.toRingHom.comp (algebraMap K (MvPolynomial (Fin g) K)) = RingHom.id K :=
      RingHom.ext fun a => z.commutes a
    rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id])
  refine exists_lbIso_pull_of_local (snd A X).left e (H.lift_fst _ _ _) hN (fun V hV u => ?_) fun x => ?_
  · obtain ⟨E, hE⟩ := exists_ringEquiv_mvPolynomial H hV
    obtain ⟨r, hr, h⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp (u.isUnit.map E.symm)
    refine ⟨hr.unit, Units.ext ?_⟩
    exact ((E.apply_symm_apply _).symm.trans (congrArg E h)).trans (hE r)
  · obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ :=
      X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    haveI : Nonempty V := ⟨⟨x, hx⟩⟩
    haveI := isIntegrallyClosed_sections_of_stalks (Y := X.left)
      (fun y => haveI := hX y; inferInstance) hV
    obtain ⟨E, hE⟩ := exists_ringEquiv_mvPolynomial H hV
    exact exists_local_generator _ hN (isAffineOpen_preimage_of_isPullback H hV) E hE hx

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianProjective

section General

variable {S : Scheme.{0}}

theorem isPullback_whiskerRight {W V : Over S} (π : W ⟶ V) (B : Over S) :
    IsPullback (fst W B).left (π ▷ B).left π.left (fst V B).left := by
  refine (IsPullback.of_right (h₁₁ := (π ▷ B).left) (v₁₁ := pullback.fst W.hom B.hom)
    (h₂₁ := π.left) (v₁₂ := pullback.fst V.hom B.hom) ?_ (Over.whiskerRight_left_fst π)
    (IsPullback.of_hasPullback V.hom B.hom).flip).flip
  rw [Over.whiskerRight_left_snd, Over.w]
  exact (IsPullback.of_hasPullback W.hom B.hom).flip

theorem isPullback_slice {W V B : Over S} (π : W ⟶ V) (y : 𝟙_ (Over S) ⟶ B) :
    IsPullback (lift (𝟙 W) (toUnit W ≫ y)).left π.left (π ▷ B).left (lift (𝟙 V) (toUnit V ≫ y)).left := by
  refine IsPullback.of_right ?_ ?_ (isPullback_whiskerRight π B)
  · rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, Over.id_left, Over.id_left]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    ext1
    · simp
    · simp [← Category.assoc]

theorem isIso_transl_left {B : Over S} [GrpObj B] (x : 𝟙_ (Over S) ⟶ B) :
    IsIso ((toUnit B ≫ x) * 𝟙 B) := by
  refine ⟨(toUnit B ≫ x)⁻¹ * 𝟙 B, ?_, ?_⟩ <;>
    simp [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]

theorem isIso_transl_right {B : Over S} [GrpObj B] (x : 𝟙_ (Over S) ⟶ B) :
    IsIso (𝟙 B * (toUnit B ≫ x)) := by
  refine ⟨𝟙 B * (toUnit B ≫ x)⁻¹, ?_, ?_⟩ <;>
    simp [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]

theorem eq_genericPoint {W V : Scheme.{0}} [IsIntegral W] (π : W ⟶ V) [IsFinite π] (w : W)
    (h : π w = π (genericPoint W)) : w = genericPoint W := by
  obtain ⟨O, hO, hOw⟩ := isDiscrete_iff_forall_exists_isOpen.mp (π.isDiscrete_preimage_singleton (π w)) w rfl
  have hw : w ∈ O ∩ π ⁻¹' {π w} := by rw [hOw]; rfl
  have hg : genericPoint W ∈ O ∩ π ⁻¹' {π w} :=
    ⟨(genericPoint_specializes w).mem_open hO hw.1, h.symm⟩
  rw [hOw] at hg
  exact hg.symm

theorem exists_point {K : Type} [Field K] [IsAlgClosed K] (X : Over (Spec (CommRingCat.of K)))
    [LocallyOfFiniteType X.hom] {Z : Set X.left} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X, ∀ p, x.left p ∈ Z := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  obtain ⟨c, hcZ, hc⟩ := nonempty_inter_closedPoints hne hZ
  refine ⟨Over.homMk (pointOfClosedPoint X.hom c hc) (pointOfClosedPoint_comp X.hom c hc), fun p => ?_⟩
  exact (pointOfClosedPoint_apply X.hom c hc p).symm ▸ hcZ

theorem ufd_stalk {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    [Smooth f] (x : X) : UniqueFactorizationMonoid (X.presheaf.stalk x) :=
  have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth K f x
  uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing
    exists_hasProjectiveDimensionLE_of_isRegularLocalRing
    isPrincipal_map_away_of_hasProjectiveDimensionLE _

theorem smooth_affineSpace (K : Type) [Field K] (g : ℕ) :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.2 {}

end General

section Family

variable {K : Type} [Field K] {W V B : Over (Spec (CommRingCat.of K))}

theorem exists_sec_fibre {N : LB (V ⊗ B).left} {N₀ : LB B.left} (hN : N.IsLB) (hN₀ : N₀.IsLB)
    (H : LBIso N (N₀.pull (snd V B).left)) (n : N.Sec) (v : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ V) :
    ∃ t : N₀.Sec, nonzeroLocus t = (lift (toUnit B ≫ v) (𝟙 B)).left ⁻¹ᵁ nonzeroLocus n := by
  have e : 𝟙 B.left = (lift (toUnit B ≫ v) (𝟙 B)).left ≫ (snd V B).left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have H' : LBIso (N.pull (lift (toUnit B ≫ v) (𝟙 B)).left) (N₀.pull (𝟙 B.left)) :=
    LBIso.chartPull (GlobalTheory.chartPullPull N _) (chartPullSame N₀ _ _ _ _ fun _ => e) H
  have H'' : LBIso N₀ (N.pull (lift (toUnit B ≫ v) (𝟙 B)).left) :=
    LBIso.trans hN₀ (pull_isLB hN₀ _) (pull_isLB hN _)
      (LBIso.symm (GlobalTheory.lbIso_of_chartPull (GlobalTheory.chartPullPull N₀ (𝟙 _)) hN₀)) (LBIso.symm H')
  obtain ⟨t, ht⟩ := GlobalTheory.exists_sec_nonzeroLocus_eq_of_lbIso hN₀ (pull_isLB hN _) H'' (GlobalTheory.secPull n _)
  exact ⟨t, ht.trans (GlobalTheory.nonzeroLocus_secPull n _)⟩

variable [GrpObj B]

theorem fibre_le (π : W ⟶ V) (a : W ⟶ B) (U : B.left.Opens) (O : (V ⊗ B).left.Opens)
    (hO : ∀ x, x ∈ O → ∀ z, (π ▷ B).left z = x → z ∈ ((fst W B ≫ a) * snd W B).left ⁻¹ᵁ U)
    (w : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ W) :
    (lift (toUnit B ≫ w ≫ π) (𝟙 B)).left ⁻¹ᵁ O ≤ ((toUnit B ≫ w ≫ a) * 𝟙 B).left ⁻¹ᵁ U := by
  intro b hb
  have e₁ : lift (toUnit B ≫ w) (𝟙 B) ≫ π ▷ B = lift (toUnit B ≫ w ≫ π) (𝟙 B) := by simp
  have e₂ : lift (toUnit B ≫ w) (𝟙 B) ≫ ((fst W B ≫ a) * snd W B) = (toUnit B ≫ w ≫ a) * 𝟙 B := by
    simp [MonObj.comp_mul]
  have h := hO _ hb ((lift (toUnit B ≫ w) (𝟙 B)).left b) (by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e₁])
  rw [← e₂, Over.comp_left]
  exact h

theorem exists_fibre_mem [IsAlgClosed K] [IsIntegral B.left] [IsIntegral W.left] [LocallyOfFiniteType W.hom]
    (π : W ⟶ V) [IsFinite π.left] (a : W ⟶ B) [IsOpenImmersion a.left] (U : B.left.Opens)
    (hU : (U : Set B.left).Nonempty) (O : (V ⊗ B).left.Opens)
    (hO : ∀ x, (∀ z, (π ▷ B).left z = x → z ∈ ((fst W B ≫ a) * snd W B).left ⁻¹ᵁ U) → x ∈ O)
    (y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B) :
    ∃ w : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ W,
      ∀ p, y.left p ∈ (lift (toUnit B ≫ w ≫ π) (𝟙 B)).left ⁻¹ᵁ O := by
  have hg : genericPoint W.left ∈ (π ≫ lift (𝟙 V) (toUnit V ≫ y)).left ⁻¹ᵁ O := by
    refine hO _ fun z hz => ?_
    obtain ⟨w', rfl, hw'⟩ := Scheme.exists_preimage_of_isPullback (isPullback_slice π y)
      z (π.left (genericPoint W.left)) (by rw [hz, Over.comp_left, Scheme.Hom.comp_apply])
    obtain rfl := eq_genericPoint π.left w' hw'
    have e : lift (𝟙 W) (toUnit W ≫ y) ≫ ((fst W B ≫ a) * snd W B) = a ≫ (𝟙 B * (toUnit B ≫ y)) := by
      simp [MonObj.comp_mul, ← Category.assoc]
    have := isIso_transl_right y
    have : IsIso (𝟙 B * (toUnit B ≫ y)).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (𝟙 B * (toUnit B ≫ y))))
    change ((lift (𝟙 W) (toUnit W ≫ y)).left ≫ ((fst W B ≫ a) * snd W B).left) _ ∈ U
    rw [← Over.comp_left, e, Over.comp_left, genericPoint_eq_of_isOpenImmersion]
    exact ((genericPoint_spec B.left).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  obtain ⟨w, hw⟩ := exists_point W (Z := ((π ≫ lift (𝟙 V) (toUnit V ≫ y)).left ⁻¹ᵁ O : W.left.Opens))
    (TopologicalSpace.Opens.isOpen _).isLocallyClosed ⟨_, hg⟩
  refine ⟨w, fun p => ?_⟩
  have e : y ≫ lift (toUnit B ≫ w ≫ π) (𝟙 B) = w ≫ π ≫ lift (𝟙 V) (toUnit V ≫ y) := by
    ext1
    · simp [← Category.assoc]
    · simp [← Category.assoc]
  have h := hw p
  change (y.left ≫ (lift (toUnit B ≫ w ≫ π) (𝟙 B)).left) p ∈ O
  rw [← Over.comp_left, e, Over.comp_left]
  exact h

end Family

theorem exists_affine_loci (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B]
    (hB : IsAbelianScheme B) : ∃ (N₀ : LB B.left) (I : Type) (t : I → N₀.Sec), N₀.IsLB ∧
      (⨆ i, nonzeroLocus (t i) = ⊤) ∧ ∀ i, IsAffineOpen (nonzeroLocus (t i)) := by
  have := hB.smooth
  have := hB.proper
  have : GeometricallyIntegral B.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian B.hom
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : B.left.IsSeparated := ⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    B.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint B.left)) isOpen_univ
  obtain ⟨L, s, hL, hs⟩ := GlobalTheory.exists_sec_nonzeroLocus_eq_of_isAffineOpen_of_factorial B.left (ufd_stalk B.hom) U hU ⟨_, hxU⟩
  obtain ⟨g, W₀, V₀, π₀, hW, hfin, hflat, -, hπ⟩ := GlobalTheory.Unif.exists_finite_flat_chart K B.left B.hom
  let A : Over (Spec (CommRingCat.of K)) :=
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin g) K))))
  have : Smooth A.hom := smooth_affineSpace K g
  have : IsIntegral A.left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of (MvPolynomial (Fin g) K))))
  have : IsAffine A.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin g) K))))
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  let W : Over (Spec (CommRingCat.of K)) := Over.mk (W₀.ι ≫ B.hom)
  let V : Over (Spec (CommRingCat.of K)) := Over.mk (V₀.ι ≫ A.hom)
  let π : W ⟶ V := Over.homMk π₀ hπ
  let a : W ⟶ B := Over.homMk W₀.ι rfl
  let j : V ⟶ A := Over.homMk V₀.ι rfl
  have : IsFinite π.left := hfin
  have : Flat π.left := hflat
  have : IsOpenImmersion a.left := inferInstanceAs (IsOpenImmersion W₀.ι)
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion V₀.ι)
  have : Nonempty W.left := ⟨⟨hW.choose, hW.choose_spec⟩⟩
  have : IsIntegral W.left := isIntegral_of_isOpenImmersion a.left
  have : LocallyOfFiniteType W.hom := inferInstanceAs (LocallyOfFiniteType (W₀.ι ≫ B.hom))
  have : IsFinite (π ▷ B).left := MorphismProperty.of_isPullback (isPullback_whiskerRight π B) ‹_›
  have : Flat (π ▷ B).left := MorphismProperty.of_isPullback (isPullback_whiskerRight π B) ‹_›
  have hj : IsOpenImmersion (j ▷ B).left := MorphismProperty.of_isPullback (isPullback_whiskerRight j B) ‹_›
  have : Smooth (A ⊗ B).hom := inferInstanceAs (Smooth (pullback.fst A.hom B.hom ≫ A.hom))
  have : QuasiCompact (A ⊗ B).hom := inferInstanceAs (QuasiCompact (pullback.fst A.hom B.hom ≫ A.hom))
  have : IsLocallyNoetherian (A ⊗ B).left := LocallyOfFiniteType.isLocallyNoetherian (A ⊗ B).hom
  have : CompactSpace (A ⊗ B).left := QuasiCompact.compactSpace_of_compactSpace (A ⊗ B).hom
  have : IsIntegral (A ⊗ B).left :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.fst A.hom B.hom)
  have : IsLocallyNoetherian (V ⊗ B).left :=
    LocallyOfFiniteType.isLocallyNoetherian (j ▷ B).left
  obtain ⟨N, n, hN, hn⟩ := GlobalTheory.FlatNorm.exists_norm_lb _ _ (π ▷ B).left (L.pull ((fst W B ≫ a) * snd W B).left)
    (GlobalTheory.secPull s _) (pull_isLB hL _)
  rw [GlobalTheory.nonzeroLocus_secPull, hs] at hn
  obtain ⟨N', hN', hφ⟩ := GlobalTheory.exists_lineBundle_extension _ _ (j ▷ B).left hj (ufd_stalk (A ⊗ B).hom) N hN
  obtain ⟨N₀, hN₀, hψ⟩ := GlobalTheory.exists_lbIso_pull_affineSpace K B (ufd_stalk B.hom) g N' hN'
  have e : (snd V B).left = (j ▷ B).left ≫ (snd A B).left := by
    rw [← Over.comp_left, whiskerRight_snd]
  have H : LBIso N (N₀.pull (snd V B).left) :=
    LBIso.trans hN (pull_isLB hN' _) (pull_isLB hN₀ _) (LBIso.symm hφ)
      (LBIso.chartPull (GlobalTheory.chartPullPull N' _) (chartPullSame N₀ _ _ _ _ fun _ => e) hψ)
  choose t ht using fun w : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ W => exists_sec_fibre hN hN₀ H n (w ≫ π)
  refine ⟨N₀, _, t, hN₀, ?_, fun w => ?_⟩
  · by_contra hne
    have hc : ((⨆ i, nonzeroLocus (t i) : B.left.Opens) : Set B.left)ᶜ.Nonempty :=
      Set.nonempty_compl.2 fun h => hne (TopologicalSpace.Opens.ext h)
    obtain ⟨y, hy⟩ := exists_point B (TopologicalSpace.Opens.isOpen _).isClosed_compl.isLocallyClosed hc
    obtain ⟨w, hw⟩ := exists_fibre_mem π a U ⟨_, hxU⟩ (nonzeroLocus n) (fun x => (hn x).2) y
    refine hy (IsLocalRing.closedPoint K) (TopologicalSpace.Opens.mem_iSup.2 ⟨w, ?_⟩)
    rw [ht]
    exact hw _
  · have hle : nonzeroLocus (t w) ≤ ((toUnit B ≫ w ≫ a) * 𝟙 B).left ⁻¹ᵁ U :=
      (ht w).trans_le (fibre_le π a U (nonzeroLocus n) (fun x => (hn x).1) w)
    have := isIso_transl_left (w ≫ a)
    have : IsIso ((toUnit B ≫ w ≫ a) * 𝟙 B).left :=
      inferInstanceAs (IsIso ((Over.forget _).map ((toUnit B ≫ w ≫ a) * 𝟙 B)))
    have h := GlobalTheory.isAffineOpen_nonzeroLocus_inf hN₀ (t w) (hU.preimage ((toUnit B ≫ w ≫ a) * 𝟙 B).left)
    rwa [inf_eq_left.2 hle] at h

theorem isProjBy_of_isAbelianScheme : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom := by
  intro K _ _ B _ _ hB
  have := hB.proper
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  obtain ⟨N₀, I, t, hN₀, hc, ha⟩ := exists_affine_loci K B hB
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun i => (nonzeroLocus (t i) : Set B.left))
    (fun i => (nonzeroLocus (t i)).isOpen) fun x _ => by
      have hx : x ∈ ⨆ i, nonzeroLocus (t i) := by rw [hc]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 hx)
  have hne : F.Nonempty := by
    obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ (η[B].left (IsLocalRing.closedPoint K))))
    exact ⟨i, hi⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne.card_pos.ne'
  let e : Fin (m + 1) ≃ F := (F.equivFinOfCardEq hm).symm
  obtain ⟨d, -, n', s, hs⟩ := veryAmpleBy_pw_of_affine_loci K B.left B.hom N₀ m (fun k => t (e k)) hN₀
    (top_unique fun x _ => by
      obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
      refine TopologicalSpace.Opens.mem_iSup.2 ⟨e.symm ⟨i, hi⟩, ?_⟩
      rw [Equiv.apply_symm_apply]
      exact hx)
    fun k => ha _
  exact ⟨_, isLB_pw hN₀ _, n', s, hs⟩

end GlobalTheory.AbelianProjective
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVarietyStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom := by
  first | exact @GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme | exact GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme | (intros; apply GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme <;> assumption)
end
