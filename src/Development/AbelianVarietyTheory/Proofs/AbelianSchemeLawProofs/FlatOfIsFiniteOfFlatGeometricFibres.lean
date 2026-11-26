module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FlatOfFlatFibresDvr
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FiniteFibreFlat

open TensorProduct IsLocalRing

section Algebra

theorem lTensor_map_injective {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M]
    (p : Ideal R) :
    Function.Injective ((p.map (algebraMap R A)).subtype.lTensor M) := by
  let I := p.map (algebraMap R A)
  let c : p →ₗ[R] I :=
    { toFun := fun r => ⟨algebraMap R A r, Ideal.mem_map_of_mem _ r.2⟩
      map_add' := fun r s => Subtype.ext (by simp)
      map_smul' := fun r s => Subtype.ext (by simp [Algebra.smul_def]) }
  let φ : M ⊗[R] p →ₗ[R] M ⊗[A] I :=
    TensorProduct.mapOfCompatibleSMul A R R M I ∘ₗ c.lTensor M
  have hφ : ∀ m r, φ (m ⊗ₜ r) = m ⊗ₜ[A] c r := fun _ _ => rfl
  have hsurj : ∀ x, x ∈ LinearMap.range φ := by
    intro x
    induction x with
    | add a b ha hb => exact add_mem ha hb
    | tmul m i =>
      obtain ⟨i, hi⟩ := i
      induction hi using Submodule.span_induction generalizing m with
      | mem x hx =>
        obtain ⟨r, hr, rfl⟩ := hx
        exact ⟨m ⊗ₜ ⟨r, hr⟩, rfl⟩
      | zero =>
        change m ⊗ₜ[A] (0 : I) ∈ _
        rw [tmul_zero]
        exact zero_mem _
      | add x y hx hy ihx ihy =>
        change m ⊗ₜ[A] ((⟨x, hx⟩ : I) + ⟨y, hy⟩) ∈ _
        rw [tmul_add]
        exact add_mem (ihx m) (ihy m)
      | smul a x hx ih =>
        change m ⊗ₜ[A] (a • (⟨x, hx⟩ : I)) ∈ _
        rw [← smul_tmul]
        exact ih _
  have hcomp : ∀ y, TensorProduct.rid A M (I.subtype.lTensor M (φ y)) =
      TensorProduct.rid R M (p.subtype.lTensor M y) := by
    intro y
    induction y with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul m r => simp [hφ, c]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj x
  have h0 := hcomp y
  rw [hx, map_zero, eq_comm, map_eq_zero_iff _ (TensorProduct.rid R M).injective,
    map_eq_zero_iff _ (Module.Flat.lTensor_preserves_injective_linearMap p.subtype
      p.injective_subtype)] at h0
  rw [h0, map_zero]

theorem free_of_flat_reduction {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M]
    [Module.Finite A M] (p : Ideal R) (hp : p.map (algebraMap R A) ≤ maximalIdeal A)
    [Module.Flat (A ⧸ p.map (algebraMap R A)) ((A ⧸ p.map (algebraMap R A)) ⊗[A] M)] :
    Module.Free A M := by
  set I := p.map (algebraMap R A) with hI
  have := Module.finitePresentation_of_finite A M
  have hrel : LocalFlat.RelationsLift I M :=
    LocalFlat.relationsLift_of_flat (C := A ⧸ I) Ideal.Quotient.mk_surjective Ideal.mk_ker
      (TensorProduct.mk A (A ⧸ I) M 1) (TensorProduct.mk_surjective A M (A ⧸ I)
        Ideal.Quotient.mk_surjective) (LinearMap.ker_tensorProductMk M)
  apply Module.free_of_maximalIdeal_rTensor_injective
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj, injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hrel (maximalIdeal A) (maximalIdeal A).subtype x (by rw [hx]; simp)
  let e := Submodule.comapSubtypeEquivOfLe hp
  have hy : I.subtype.lTensor M (e.toLinearMap.lTensor M y) = 0 := by
    rw [← hx, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply]
    rfl
  rw [map_eq_zero_iff _ (lTensor_map_injective p)] at hy
  have : y = 0 := (LinearEquiv.lTensor M e).injective (hy.trans (map_zero _).symm)
  rw [this, map_zero]

theorem flat_of_flat_fibres {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsNoetherianRing A] [Module.Finite A B]
    [Module.Flat R B]
    (H : ∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C),
      (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B)) :
    Module.Flat A B := by
  refine Module.flat_of_isLocalized_maximal A B (fun P _ => Localization.AtPrime P ⊗[A] B)
    (fun P _ => TensorProduct.mk A (Localization.AtPrime P) B 1) fun P _ => ?_
  let A' := Localization.AtPrime P
  let p : Ideal R := (maximalIdeal A').comap (algebraMap R A')
  let I := p.map (algebraMap R A')
  have h1 : Module.Flat R (B ⊗[A] A') := Module.Flat.trans R B (B ⊗[A] A')
  have h2 : Module.Flat R (A' ⊗[A] B) :=
    Module.Flat.of_linearEquiv
      ((Algebra.TensorProduct.comm A A' B).restrictScalars R).toLinearEquiv
  have h3 : Module.Flat (A' ⧸ I) ((A' ⧸ I) ⊗[A] B) := by
    let ψ : R →+* A' ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap R A')
    have hψ₁ : p ≤ RingHom.ker ψ := fun r hr =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)
    have hψ₂ : p.primeCompl ≤ (IsUnit.submonoid (A' ⧸ I)).comap ψ := by
      intro r hr
      have : IsUnit (algebraMap R A' r) := by
        by_contra h
        exact hr h
      exact this.map (Ideal.Quotient.mk I)
    refine H p.ResidueField (A' ⧸ I) (algebraMap R _) (Ideal.ResidueField.lift p ψ hψ₁ hψ₂) ?_
    ext r
    exact (Ideal.ResidueField.lift_algebraMap p ψ hψ₁ hψ₂ r).symm
  have h4 : Module.Flat (A' ⧸ I) ((A' ⧸ I) ⊗[A'] (A' ⊗[A] B)) :=
    Module.Flat.of_linearEquiv
      (AlgebraTensorModule.cancelBaseChange A A' (A' ⧸ I) (A' ⧸ I) B)
  have h5 : Module.Free A' (A' ⊗[A] B) :=
    free_of_flat_reduction p Ideal.map_comap_le
  have h6 : Module.Flat A' (A' ⊗[A] B) := Module.Flat.of_free
  exact Module.Flat.trans A A' (A' ⊗[A] B)

end Algebra

open FibreFlat

variable {X Y S S' : Scheme.{0}} {f : X ⟶ Y}

theorem flatOver_of_comp_base {S₀ : Scheme.{0}} {g : Y ⟶ S₀} {u : S₀ ⟶ S} {t : S' ⟶ S₀}
    (H : FlatOver f (g ≫ u) (t ≫ u)) : FlatOver f g t :=
  fun _ _ a b j h sq e => H a b j h sq (by rw [← Category.assoc, e, Category.assoc])

theorem flatOver_descend {S'' : Scheme.{0}} {g : Y ⟶ S} {t : S' ⟶ S} (σ : S'' ⟶ S')
    [Surjective σ] [Flat σ] [QuasiCompact σ] (H : FlatOver f g (σ ≫ t)) : FlatOver f g t := by
  intro W Z a b j h sq e
  haveI := flat_descendsAlong_fpqc
  have sq1 := IsPullback.of_hasPullback b (pullback.fst h σ)
  have h1 : Flat (pullback.snd b (pullback.fst h σ)) :=
    H _ _ _ (pullback.snd h σ) (sq1.paste_horiz sq)
      (by rw [Category.assoc, e, ← Category.assoc, pullback.condition, Category.assoc])
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Flat)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq1.flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h1

set_option backward.isDefEq.respectTransparency false in
theorem flat_of_flatOver_fields (f : X ⟶ Y) (g : Y ⟶ S) (hY : IsLocallyNoetherian Y)
    (h1 : Flat (f ≫ g)) (h2 : IsFinite f)
    (H : ∀ (k : Type) [Field k] (t : Spec (CommRingCat.of k) ⟶ S), FlatOver f g t) :
    Flat f := by
  wlog hS : ∃ R, S = Spec R generalizing X Y S
  · refine IsZariskiLocalAtTarget.of_openCover (S.affineCover.pullback₁ g) fun i => ?_
    let u := S.affineCover.f i
    have sq := IsPullback.of_hasPullback f (pullback.fst g u)
    have sq' := IsPullback.of_hasPullback g u
    refine this (pullback.snd f (pullback.fst g u)) (pullback.snd g u)
      (LocallyOfFiniteType.isLocallyNoetherian (pullback.fst g u))
      (MorphismProperty.of_isPullback (sq.paste_vert sq') h1) inferInstance
      (fun k _ t => flatOver_of_comp_base (u := u) ?_) ⟨_, rfl⟩
    rw [← pullback.condition]
    exact (H k _).target sq
  obtain ⟨R, rfl⟩ := hS
  wlog hA : ∃ A, Y = Spec A generalizing X Y
  · refine IsZariskiLocalAtTarget.of_openCover Y.affineCover fun i => ?_
    have sq := IsPullback.of_hasPullback f (Y.affineCover.f i)
    have e : pullback.snd f (Y.affineCover.f i) ≫ Y.affineCover.f i ≫ g =
        pullback.fst f (Y.affineCover.f i) ≫ f ≫ g := by
      rw [← Category.assoc, ← sq.w, Category.assoc]
    exact this (pullback.snd f (Y.affineCover.f i))
      (LocallyOfFiniteType.isLocallyNoetherian (Y.affineCover.f i)) inferInstance
      (Y.affineCover.f i ≫ g) (by rw [e]; infer_instance) (fun k _ t => (H k t).target sq) ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hA
  wlog hX : ∃ B, X = Spec B generalizing X
  · haveI hX' : IsAffine X := isAffine_of_isAffineHom f
    rw [← MorphismProperty.cancel_left_of_respectsIso @Flat X.isoSpec.inv]
    exact this (X.isoSpec.inv ≫ f) inferInstance (by rw [Category.assoc]; infer_instance)
      (fun k _ t => (H k t).source _) ⟨_, rfl⟩
  obtain ⟨B, rfl⟩ := hX
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp] at h1
  rw [Flat.SpecMap_iff] at h1 ⊢
  rw [IsFinite.SpecMap_iff] at h2
  rw [isLocallyNoetherian_Spec] at hY
  letI : Algebra R A := g.hom.toAlgebra
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra R B := (g ≫ f).hom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Flat R B := h1
  haveI : Module.Finite A B := h2
  refine flat_of_flat_fibres (R := R) (A := A) (B := B) fun k C _ _ _ t h e => ?_
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A C B)
  have := H k (Spec.map (CommRingCat.ofHom t)) _ _ _ (Spec.map (CommRingCat.ofHom h)) sq.flip
    (by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext1
      exact e)
  rw [Flat.SpecMap_iff] at this
  exact RingHom.flat_algebraMap_iff.mp this

end FiniteFibreFlat

theorem flat_of_isFinite_of_flat_geometric_fibres :
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFiniteType Y.hom → IsFinite f.left → (∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S), Flat ((Over.pullback t).map f).left) → Flat f.left := by
  intro S _ X Y f h1 h2 h3 H
  refine FiniteFibreFlat.flat_of_flatOver_fields f.left Y.hom
    (LocallyOfFiniteType.isLocallyNoetherian Y.hom) (by rwa [Over.w]) h3 fun k _ t => ?_
  exact FiniteFibreFlat.flatOver_descend
    (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
    (FibreFlat.flatOver_of_pullback f _ (H _ _))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace AbelianQuotient

variable {S : Scheme.{0}}

lemma exists_desc {X Y Z : Over S} (p : X ⟶ Y) [Flat p.left] [Surjective p.left]
    [QuasiCompact p.left] (f : X ⟶ Z)
    (h : ∀ (W : Over S) (a b : W ⟶ X), a ≫ p = b ≫ p → a ≫ f = b ≫ f) :
    ∃ β : Y ⟶ Z, p ≫ β = f := by
  have hc : ∀ {W : Scheme.{0}} (g g' : W ⟶ X.left), g ≫ p.left = g' ≫ p.left →
      g ≫ f.left = g' ≫ f.left := by
    intro W g g' hg
    have hw : g' ≫ X.hom = g ≫ X.hom := by
      rw [← Over.w p, ← Category.assoc, ← hg, Category.assoc]
    have := h (Over.mk (g ≫ X.hom)) (Over.homMk g rfl) (Over.homMk g' hw)
      (Over.OverMorphism.ext hg)
    exact congrArg CommaMorphism.left this
  have hfac := EffectiveEpi.fac p.left f.left hc
  exact ⟨Over.homMk (EffectiveEpi.desc p.left f.left hc) (by
    rw [← cancel_epi p.left, ← Category.assoc, hfac, Over.w, Over.w]),
    Over.OverMorphism.ext hfac⟩

lemma flat_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Flat f.left] [hg : Flat g.left] : Flat (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @Flat) hf hg (Over.w f).symm (Over.w g).symm

lemma surjective_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Surjective f.left] [hg : Surjective g.left] : Surjective (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  have : MorphismProperty.IsStableUnderComposition @Surjective.{0} :=
    ⟨fun _ _ _ _ => inferInstance⟩
  exact MorphismProperty.pullbackMap (P := @Surjective) hf hg (Over.w f).symm (Over.w g).symm

lemma quasiCompact_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : QuasiCompact f.left] [hg : QuasiCompact g.left] : QuasiCompact (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @QuasiCompact) hf hg (Over.w f).symm (Over.w g).symm

theorem exists_grpObj {A H Q : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj H] (i : H ⟶ A)
    [IsMonHom i] (q : A ⟶ Q) [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hq : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q) :
    ∃ _ : GrpObj Q, IsCommMonObj Q ∧ IsMonHom q ∧ IsPullback i (toUnit H) q η[Q] := by
  have rel : ∀ {W : Over S} (a b : W ⟶ A), a ≫ q = b ≫ q ↔ ∃ t : W ⟶ H, a = (t ≫ i) * b := by
    intro W a b
    constructor
    · intro h
      refine ⟨hq.lift a b h ≫ fst H A, ?_⟩
      have h1 := hq.lift_fst a b h
      rw [comp_mul, hq.lift_snd] at h1
      rw [Category.assoc, h1]
    · rintro ⟨t, rfl⟩
      have := lift t b ≫= hq.w
      simpa [comp_mul, ← Category.assoc] using this
  have := flat_tensorHom q q
  have := surjective_tensorHom q q
  have := quasiCompact_tensorHom q q
  have := FlatQuotient.epi_of_flat_surjective q
  have := FlatQuotient.epi_tensorHom q q
  have := FlatQuotient.epi_tensorHom (q ⊗ₘ q) q
  obtain ⟨m, hm⟩ := exists_desc (q ⊗ₘ q) (μ[A] ≫ q) (by
    intro W a b h
    obtain ⟨s, hs⟩ := (rel (a ≫ fst A A) (b ≫ fst A A)).1 (by simpa using h =≫ fst Q Q)
    obtain ⟨t, ht⟩ := (rel (a ≫ snd A A) (b ≫ snd A A)).1 (by simpa using h =≫ snd Q Q)
    rw [← Category.assoc, ← Category.assoc, rel]
    refine ⟨s * t, ?_⟩
    rw [MonObj.mul_eq_mul, comp_mul, comp_mul, hs, ht, mul_comp, _root_.mul_mul_mul_comm])
  obtain ⟨n, hn⟩ := exists_desc q (GrpObj.inv ≫ q) (by
    intro W a b h
    obtain ⟨s, hs⟩ := (rel a b).1 h
    rw [← Category.assoc, ← Category.assoc, rel]
    refine ⟨s⁻¹, ?_⟩
    rw [← Hom.inv_def, ← Hom.inv_def, hs, GrpObj.inv_comp, mul_inv])
  have key : ∀ {W : Over S} (a b : W ⟶ A), lift (a ≫ q) (b ≫ q) ≫ m = (a * b) ≫ q := by
    intro W a b
    rw [← lift_map, Category.assoc, hm, Hom.mul_def, Category.assoc]
  letI : MonObj Q :=
    { one := η[A] ≫ q
      mul := m
      one_mul := by
        rw [← cancel_epi (λ_ Q).inv, ← cancel_epi q]
        have := key (1 : A ⟶ A) (𝟙 A)
        rw [_root_.one_mul] at this
        rw [Iso.inv_hom_id, Category.comp_id]
        refine Eq.trans ?_ (this.trans (Category.id_comp _))
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext <;> simp [Hom.one_def]
      mul_one := by
        rw [← cancel_epi (ρ_ Q).inv, ← cancel_epi q]
        have := key (𝟙 A) (1 : A ⟶ A)
        rw [_root_.mul_one] at this
        rw [Iso.inv_hom_id, Category.comp_id]
        refine Eq.trans ?_ (this.trans (Category.id_comp _))
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        ext <;> simp [Hom.one_def]
      mul_assoc := by
        rw [← cancel_epi ((q ⊗ₘ q) ⊗ₘ q)]
        have h1 : ((q ⊗ₘ q) ⊗ₘ q) ≫ m ▷ Q = (μ[A] ▷ A) ≫ (q ⊗ₘ q) := by
          rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
            hm, Category.comp_id, Category.id_comp]
        have h2 : ((q ⊗ₘ q) ⊗ₘ q) ≫ (α_ Q Q Q).hom ≫ Q ◁ m =
            (α_ A A A).hom ≫ (A ◁ μ[A]) ≫ (q ⊗ₘ q) := by
          rw [associator_naturality_assoc]
          congr 1
          ext <;> simp [hm]
        rw [reassoc_of% h1, reassoc_of% h2, hm, MonObj.mul_assoc_assoc] }
  have hhom : IsMonHom q := ⟨rfl, hm.symm⟩
  letI : GrpObj Q :=
    { inv := n
      left_inv := by
        rw [← cancel_epi q, comp_lift_assoc, hn, Category.comp_id]
        have := key GrpObj.inv (𝟙 A)
        rw [Category.id_comp] at this
        refine this.trans ?_
        rw [Hom.mul_def, GrpObj.left_inv, comp_toUnit_assoc, Category.assoc]
        rfl
      right_inv := by
        rw [← cancel_epi q, comp_lift_assoc, hn, Category.comp_id]
        have := key (𝟙 A) GrpObj.inv
        rw [Category.id_comp] at this
        refine this.trans ?_
        rw [Hom.mul_def, GrpObj.right_inv, comp_toUnit_assoc, Category.assoc]
        rfl }
  refine ⟨inferInstance, ⟨?_⟩, hhom, ?_⟩
  · rw [← cancel_epi (q ⊗ₘ q), BraidedCategory.braiding_naturality_assoc, ← IsMonHom.mul_hom,
      IsCommMonObj.mul_comm_assoc]
  · have hk : IsPullback (lift (𝟙 H) (toUnit H ≫ η[A])) (toUnit H) (snd H A) η[A] := by
      refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ fst H A) ?_ ?_ ?_⟩⟩
      · intro s
        ext
        · simp
        · simp [s.condition, toUnit_unique (toUnit _) s.snd]
      · intro s
        exact toUnit_unique _ _
      · intro s l h1 _
        simp [← h1]
    have := hk.flip.paste_vert hq.flip
    have e : lift (𝟙 H) (toUnit H ≫ η[A]) ≫ ((fst H A ≫ i) * snd H A) = i := by
      simp [comp_mul, ← Hom.one_def]
    rw [e] at this
    exact this.flip

lemma isReduced_of_flat_of_surjective {X Y : Scheme.{0}} (p : X ⟶ Y) [Flat p] [Surjective p]
    [IsReduced X] : IsReduced Y := by
  have (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    obtain ⟨x, rfl⟩ := p.surjective y
    exact isReduced_of_injective (p.stalkMap x).hom
      (faithfullyFlat_stalkMap_of_flat p x).injective
  exact isReduced_of_isReduced_stalk Y

lemma geometricallyReduced_of_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z) [Flat p]
    [Surjective p] [h : GeometricallyReduced (p ≫ f)] : GeometricallyReduced f := by
  refine ⟨fun K _ y W a b hW => ?_⟩
  have : IsReduced (pullback p a) :=
    h.geometrically_isReduced y _ _ ((IsPullback.of_hasPullback p a).paste_vert hW)
  exact isReduced_of_flat_of_surjective (pullback.snd p a)

lemma geometricallyConnected_of_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z)
    [Surjective p] [h : GeometricallyConnected (p ≫ f)] : GeometricallyConnected f := by
  refine ⟨fun K _ y W a b hW => ?_⟩
  have : ConnectedSpace ↥(pullback p a) :=
    h.geometrically_connectedSpace y _ _ ((IsPullback.of_hasPullback p a).paste_vert hW)
  exact (pullback.snd p a).surjective.connectedSpace (pullback.snd p a).continuous

lemma smooth_of_grpObj_of_flat (Q : Over S) [GrpObj Q] [Flat Q.hom]
    [LocallyOfFinitePresentation Q.hom] [GeometricallyReduced Q.hom] : Smooth Q.hom := by
  refine Smooth.of_smooth_fiberToSpecResidueField _ fun y => ?_
  letI : GrpObj (Over.mk Q.hom) := inferInstanceAs (GrpObj Q)
  letI : GrpObj (Over.mk (pullback.snd Q.hom (S.fromSpecResidueField y))) :=
    Over.grpObjMkPullbackSnd
  exact smooth_of_grpObj (K := S.residueField y) (pullback.snd Q.hom (S.fromSpecResidueField y))

end AbelianQuotient

open AbelianQuotient in
theorem quotient_isAbelianScheme_of_quotientScheme :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f →
      GeometricallyIntegral f) →
    (∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Spec (CommRingCat.of R)))
      (H : Over (Spec (CommRingCat.of R))) [GrpObj H] (i : H ⟶ P.A), IsMonHom i → Mono i →
      IsFinite H.hom → Flat H.hom →
      ∃ (Q : Over (Spec (CommRingCat.of R))) (q : P.A ⟶ Q), IsFinite q.left ∧ Flat q.left ∧
        Surjective q.left ∧ IsSeparated Q.hom ∧ LocallyOfFiniteType Q.hom ∧
        IsPullback ((fst H P.A ≫ i) * snd H P.A) (snd H P.A) q q) →
    QuotientSt := by
  intro hint hquot R _ _ P H _ i hi hmono hfin hflat
  obtain ⟨Q, q, h1, h2, h3, h4, h5, hq⟩ := hquot R P H i hi hmono hfin hflat
  have := P.isAb.comm
  obtain ⟨inst, hcomm, hhom, hker⟩ := exists_grpObj i q hq
  refine ⟨Q, inst, ?_, q, hhom, h1, h2, h3, hker⟩
  have hw : q.left ≫ Q.hom = P.A.hom := Over.w q
  have := P.isAb.smooth
  have := P.isAb.proper
  have := P.isAb.geomConnected
  have := hint _ _ P.A.hom P.isAb.smooth P.isAb.geomConnected
  have : Flat (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyReduced (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyConnected (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have := flat_of_comp_of_flat_of_surjective q.left Q.hom
  have := UniversallyClosed.of_comp_surjective q.left Q.hom
  have := geometricallyReduced_of_comp q.left Q.hom
  have : LocallyOfFinitePresentation Q.hom := inferInstance
  exact ⟨hcomm, smooth_of_grpObj_of_flat Q, ⟨⟩, geometricallyConnected_of_comp q.left Q.hom⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace FiniteFlatKilled

section Algebra

open TensorProduct WithConv Coalgebra

variable {R B C F : Type*} [CommRing R] [CommRing C] [CommRing F] [Algebra R C] [Algebra R F]

section Coalg

variable [AddCommGroup B] [Module R B] [Coalgebra R B] [IsCocomm R B]

variable (B) in
def postcomp (h : C →ₐ[R] F) : WithConv (B →ₗ[R] C) →+* WithConv (B →ₗ[R] F) where
  toFun f := toConv (h.toLinearMap ∘ₗ f.ofConv)
  map_one' := by ext c; simp
  map_mul' f g := by
    rw [LinearMap.algHom_comp_convMul_distrib]
  map_zero' := by ext c; simp
  map_add' f g := by ext c; simp

variable [Algebra C F] [IsScalarTower R C F]

theorem pow_card_eq_one {ι : Type*} [Fintype ι] (b : Module.Basis ι C F) (τ : F ≃ₐ[C] F)
    (x : WithConv (B →ₗ[R] F)) (hx : IsUnit x) (u : WithConv (B →ₗ[R] C))
    (h : postcomp B (τ.toAlgHom.restrictScalars R) x =
      x * postcomp B (IsScalarTower.toAlgHom R C F) u) :
    u ^ Fintype.card ι = 1 := by
  classical
  letI : Algebra (WithConv (B →ₗ[R] C)) (WithConv (B →ₗ[R] F)) :=
    (postcomp B (IsScalarTower.toAlgHom R C F)).toAlgebra
  have hsmul : ∀ (g : WithConv (B →ₗ[R] C)) (f : WithConv (B →ₗ[R] F)),
      g • f = postcomp B (IsScalarTower.toAlgHom R C F) g * f := fun _ _ => rfl
  let e : WithConv (B →ₗ[R] F) ≃ₗ[WithConv (B →ₗ[R] C)] (ι → WithConv (B →ₗ[R] C)) :=
    { toFun := fun f i => toConv ((b.coord i).restrictScalars R ∘ₗ f.ofConv)
      invFun := fun g => toConv (∑ i,
        (LinearMap.toSpanSingleton C F (b i)).restrictScalars R ∘ₗ (g i).ofConv)
      map_add' := fun f g => by ext i c; simp
      map_smul' := fun g f => by
        ext i c
        rw [hsmul]
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [(ℛ R c).convMul_apply]
        simp only [LinearMap.comp_apply]
        rw [(ℛ R c).convMul_apply]
        simp [postcomp, ← Algebra.smul_def]
      left_inv := fun f => by
        ext c
        simp
      right_inv := fun g => by
        ext i c
        simp [Finsupp.single_apply] }
  let b' := Module.Basis.ofEquivFun e
  let τ' : WithConv (B →ₗ[R] F) ≃ₐ[WithConv (B →ₗ[R] C)] WithConv (B →ₗ[R] F) :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (postcomp B (τ.toAlgHom.restrictScalars R))
      (postcomp B (τ.symm.toAlgHom.restrictScalars R)) (by ext f c; simp [postcomp]) (by ext f c; simp [postcomp]))
      (fun g => by
        ext c
        exact τ.commutes (g c))
  have h1 : τ' x = x * algebraMap _ _ u := h
  have h2 := Algebra.norm_eq_of_algEquiv τ' x
  rw [h1, map_mul, Algebra.norm_algebraMap_of_basis b'] at h2
  exact (hx.map (Algebra.norm (WithConv (B →ₗ[R] C)))).mul_left_cancel (by rw [h2, mul_one])

end Coalg

variable [CommRing B] [HopfAlgebra R B]

theorem mul_comp_antipode (u : B →ₐ[R] C) :
    toConv u * toConv (u.comp (HopfAlgebra.antipodeAlgHom R B)) = 1 := by
  have h : toConv (AlgHom.id R B) * toConv (HopfAlgebra.antipodeAlgHom R B) = 1 :=
    mul_inv_cancel (toConv (AlgHom.id R B))
  have h2 := AlgHom.comp_convMul_distrib u (toConv (AlgHom.id R B))
    (toConv (HopfAlgebra.antipodeAlgHom R B))
  rw [h] at h2
  apply ofConv_injective
  refine h2.symm.trans ?_
  ext c
  simp

variable [IsCocomm R B]

theorem point_pow_card {ι : Type*} [Fintype ι] (b : Module.Basis ι C (C ⊗[R] B))
    (u : B →ₐ[R] C) : toConv u ^ Fintype.card ι = 1 := by
  let x : WithConv (B →ₐ[R] C ⊗[R] B) := toConv Algebra.TensorProduct.includeRight
  let T : (B →ₐ[R] C) → (C ⊗[R] B →ₐ[C] C ⊗[R] B) := fun v =>
    Algebra.TensorProduct.lift (Algebra.ofId C _)
      (x * toConv ((IsScalarTower.toAlgHom R C (C ⊗[R] B)).comp v)).ofConv
      fun _ _ => Commute.all _ _
  have hTx : ∀ v, ((T v).restrictScalars R).comp x.ofConv =
      (x * toConv ((IsScalarTower.toAlgHom R C (C ⊗[R] B)).comp v)).ofConv := fun v => by
    ext c
    simp [T, x]
  have hTy : ∀ v w : B →ₐ[R] C, ((T v).restrictScalars R).comp
      ((IsScalarTower.toAlgHom R C (C ⊗[R] B)).comp w) =
      (IsScalarTower.toAlgHom R C (C ⊗[R] B)).comp w := fun v w => by
    ext c
    exact (T v).commutes (w c)
  have hTT : ∀ v w : B →ₐ[R] C, toConv v * toConv w = 1 → (T v).comp (T w) = AlgHom.id _ _ := by
    intro v w hvw
    refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
    change ((T v).restrictScalars R).comp (((T w).restrictScalars R).comp x.ofConv) = x.ofConv
    have h3 := AlgHom.comp_convMul_distrib (IsScalarTower.toAlgHom R C (C ⊗[R] B))
      (toConv v) (toConv w)
    have h4 : (IsScalarTower.toAlgHom R C (C ⊗[R] B)).comp
        (1 : WithConv (B →ₐ[R] C)).ofConv = (1 : WithConv (B →ₐ[R] C ⊗[R] B)).ofConv := by
      ext c
      simp
    rw [hvw, h4] at h3
    rw [hTx, AlgHom.comp_convMul_distrib, hTx, ofConv_toConv, hTy, toConv_ofConv, mul_assoc,
      ← ofConv_injective h3, mul_one]
  let τ : C ⊗[R] B ≃ₐ[C] C ⊗[R] B :=
    AlgEquiv.ofAlgHom (T u) (T (u.comp (HopfAlgebra.antipodeAlgHom R B)))
      (hTT _ _ (mul_comp_antipode u)) (hTT _ _ (by rw [mul_comm]; exact mul_comp_antipode u))
  have hx : IsUnit (toConv x.ofConv.toLinearMap) := by
    refine IsUnit.of_mul_eq_one
      (toConv (x.ofConv.comp (HopfAlgebra.antipodeAlgHom R B)).toLinearMap) ?_
    exact congrArg (fun f : WithConv (B →ₐ[R] C ⊗[R] B) => toConv f.ofConv.toLinearMap)
      (mul_comp_antipode x.ofConv)
  have key := pow_card_eq_one b τ _ hx (toConv u.toLinearMap)
    (congrArg (fun f : B →ₐ[R] C ⊗[R] B => toConv f.toLinearMap) (hTx u))
  apply ofConv_injective
  apply AlgHom.toLinearMap_injective
  apply toConv_injective
  rw [AlgHom.toLinearMap_convPow, AlgHom.toLinearMap_convOne]
  exact key

theorem comp_convPow (h : C →ₐ[R] F) (f : WithConv (B →ₐ[R] C)) (n : ℕ) :
    h.comp (f ^ n).ofConv = (toConv (h.comp f.ofConv) ^ n).ofConv := by
  induction n with
  | zero => ext c; simp
  | succ n ih => rw [pow_succ, pow_succ, AlgHom.comp_convMul_distrib, ih]

theorem exists_id_pow_eq_one [Module.Finite R B] [Module.Flat R B] :
    ∃ N : ℕ, 1 ≤ N ∧ toConv (AlgHom.id R B) ^ N = 1 := by
  obtain ⟨d, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := B)
  refine ⟨d.factorial, d.factorial_pos, ?_⟩
  apply ofConv_injective
  ext c
  refine Module.eq_of_localization_maximal (R := B) (fun P _ => Localization.AtPrime P)
    (fun P _ => Algebra.linearMap B (Localization.AtPrime P)) _ _ (fun m hm => ?_)
  let C := Localization.AtPrime m
  let u : B →ₐ[R] C := IsScalarTower.toAlgHom R B C
  haveI : Module.Free C (C ⊗[R] B) := Module.free_of_flat_of_isLocalRing
  have h1 := point_pow_card (Module.finBasis C (C ⊗[R] B)) u
  rw [Fintype.card_fin] at h1
  haveI : Nontrivial (C ⊗[R] B) :=
    (Algebra.TensorProduct.lift (AlgHom.id C C) u fun _ _ => Commute.all _ _).toRingHom.domain_nontrivial
  have hpos : 0 < Module.finrank C (C ⊗[R] B) :=
    (Module.finrank_pos_iff_of_free C (C ⊗[R] B)).2 inferInstance
  have hle : Module.finrank C (C ⊗[R] B) ≤ d := by
    have hsp : Submodule.span C (Set.range fun i => (1 : C) ⊗ₜ[R] s i) = ⊤ := by
      have := Submodule.baseChange_span (R := R) C (Set.range s)
      rw [hs, Submodule.baseChange_top, ← Set.range_comp] at this
      exact this.symm
    simpa using finrank_le_of_span_eq_top hsp
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hpos hle
  have h2 := comp_convPow u (toConv (AlgHom.id R B)) d.factorial
  rw [ofConv_toConv, AlgHom.comp_id, hk, pow_mul (toConv u), h1, one_pow, ← hk] at h2
  have h3 := congr($h2 c)
  refine h3.trans ?_
  exact IsScalarTower.algebraMap_apply R B C _

end Algebra

section Scheme

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TensorProduct WithConv

attribute [local instance] Over.cartesianMonoidalCategory

theorem isCocomm_of_mul_comm {R B : Type*} [CommRing R] [CommRing B] [Bialgebra R B]
    (h : ∀ f g : WithConv (B →ₐ[R] B ⊗[R] B), f * g = g * f) : Coalgebra.IsCocomm R B := by
  let l : WithConv (B →ₐ[R] B ⊗[R] B) := toConv Algebra.TensorProduct.includeLeft
  let r : WithConv (B →ₐ[R] B ⊗[R] B) := toConv Algebra.TensorProduct.includeRight
  have h1 : (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map l.ofConv r.ofConv) =
      AlgHom.id R (B ⊗[R] B) := by
    ext <;> simp [l, r, ← Algebra.TensorProduct.one_def]
  have h2 : (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map r.ofConv l.ofConv) =
      (Algebra.TensorProduct.comm R B B).toAlgHom := by
    ext <;> simp [l, r, ← Algebra.TensorProduct.one_def]
  have h3 := congrArg ofConv (h r l)
  rw [AlgHom.convMul_def, AlgHom.convMul_def, ofConv_toConv, ofConv_toConv, ← AlgHom.comp_assoc,
    ← AlgHom.comp_assoc, h1, h2] at h3
  exact ⟨LinearMap.ext fun c => congr($h3 c)⟩

theorem exists_id_pow_eq_one_of_isFinite_of_flat (R : Type) [CommRing R]
    (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [IsCommMonObj H] (hf : IsFinite H.hom)
    (hfl : Flat H.hom) : ∃ N : ℕ, 1 ≤ N ∧ 𝟙 H ^ N = 1 := by
  have haff : IsAffine H.left := isAffine_of_isAffineHom H.hom
  obtain ⟨A, ⟨e⟩⟩ := (essImage_hopfSpec (G := Grp.mk H)).2 haff
  let B : Type := A.unop
  letI : HopfAlgebra R B := A.unop.hopfAlgebra
  let G : Over (Spec (CommRingCat.of R)) :=
    (Spec (CommRingCat.of B)).asOver (Spec (CommRingCat.of R))
  letI : GrpObj G := instGrpObjSpecAsOverSpec (R := CommRingCat.of R) (A := CommRingCat.of B)
  let i : G ≅ H := (Grp.forget _).mapIso e
  haveI : IsMonHom i.hom := e.hom.hom.isMonHom_hom
  obtain ⟨j, hj, hw⟩ : ∃ j : Spec (CommRingCat.of B) ⟶ H.left, IsIso j ∧
      Spec.map (CommRingCat.ofHom (algebraMap R B)) = j ≫ H.hom :=
    ⟨i.hom.left, inferInstanceAs (IsIso ((Over.forget _).map i.hom)), (Over.w i.hom).symm⟩
  haveI : Module.Finite R B := by
    have h1 : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
      rw [hw]; infer_instance
    rw [IsFinite.SpecMap_iff] at h1
    exact RingHom.finite_algebraMap.1 h1
  haveI : Module.Flat R B := by
    have h1 : Flat (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
      rw [hw]; infer_instance
    rw [Flat.SpecMap_iff] at h1
    exact RingHom.flat_algebraMap_iff.1 h1
  haveI : Coalgebra.IsCocomm R B := isCocomm_of_mul_comm fun f g => by
    let φ := (Spec.mapMulEquiv (R := R) (S := B) (T := B ⊗[R] B)).trans
      (Hom.mulEquivCongrRight i _)
    apply φ.injective
    rw [map_mul, map_mul, mul_comm]
  obtain ⟨N, hN, h⟩ := exists_id_pow_eq_one (R := R) (B := B)
  refine ⟨N, hN, ?_⟩
  have h1 := congrArg (Spec.mapMulEquiv (R := R) (S := B) (T := B)) h
  rw [map_pow, map_one] at h1
  have h2 : Spec.mapMulEquiv (R := R) (S := B) (T := B) (toConv (AlgHom.id R B)) = 𝟙 G := by
    ext1
    exact Spec.map_id _
  have h3 : 𝟙 G ^ N = 1 := h2 ▸ h1
  rw [← cancel_epi i.hom, MonObj.comp_pow, MonObj.comp_one, Category.comp_id,
    ← Category.id_comp i.hom, ← MonObj.pow_comp, h3, MonObj.one_comp]

theorem main : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (H : Over (Spec (CommRingCat.of R)))
    [GrpObj H] [IsCommMonObj H], IsFinite H.hom → Flat H.hom → ∃ N : ℕ, 1 ≤ N ∧ 𝟙 H ^ N = 1 :=
  fun R _ _ H _ _ hf hfl => exists_id_pow_eq_one_of_isFinite_of_flat R H hf hfl

end Scheme

end FiniteFlatKilled

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrdegEqOfLocallyIsStandardSmoothOfRelativeDimens
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem trdeg_eq_of_locally_isStandardSmoothOfRelativeDimension {K B : Type} [Field K]
    [CommRing B] [IsDomain B] [Algebra K B] {g : ℕ}
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap K B)) :
    Algebra.trdeg K B = g := by
  obtain ⟨s, hs, hP⟩ := h
  obtain ⟨t, hts, ht⟩ : ∃ t ∈ s, t ≠ 0 := by
    by_contra! hz
    have hbot : Ideal.span s = ⊥ := Ideal.span_eq_bot.mpr hz
    exact top_ne_bot (hs.symm.trans hbot)
  have hPt := hP t hts
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at hPt
  have hle : Submonoid.powers t ≤ nonZeroDivisors B :=
    powers_le_nonZeroDivisors_of_noZeroDivisors ht
  have : IsDomain (Localization.Away t) := IsLocalization.isDomain_localization hle
  have : Algebra.IsStandardSmooth K (Localization.Away t) := hPt.isStandardSmooth
  have hdim : ringKrullDim (Localization.Away t) = g :=
    AffinePoints.ringKrullDim_eq_of_isStandardSmooth (K := K)
  obtain ⟨d, hd1, hd2⟩ := exists_ringKrullDim_eq_and_trdeg_eq K (Localization.Away t)
  have hdg : d = g := by
    rw [hdim] at hd1
    exact_mod_cast hd1.symm
  have : FaithfulSMul B (Localization.Away t) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hle)
  have : Algebra.IsAlgebraic B (Localization.Away t) :=
    IsLocalization.isAlgebraic _ (Submonoid.powers t)
  have : FaithfulSMul K B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap K B).injective
  rw [← trdeg_eq_of_isAlgebraic_top K B (Localization.Away t), hd2, hdg]

theorem trdeg_eq_of_smoothOfRelativeDimension :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (B : Type) [CommRing B] [Nontrivial B] [Algebra K B] (j : Spec (CommRingCat.of B) ⟶ X), IsOpenImmersion j → j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K B)) → Algebra.trdeg K B = g := by
  intro K _ X _ f g hf B _ _ _ j hj hjf
  have : IsIntegral (Spec (CommRingCat.of B)) := isIntegral_of_isOpenImmersion j
  have : IsDomain B := (affine_isIntegral_iff (CommRingCat.of B)).mp this
  have h0 : SmoothOfRelativeDimension (0 + g) (j ≫ f) := inferInstance
  rw [Nat.zero_add, hjf] at h0
  have hloc := (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension g)).mp h0
  exact trdeg_eq_of_locally_isStandardSmoothOfRelativeDimension hloc

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.EqCompSectionOfSurjectiveAppTop
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.eq_comp_section_of_surjective_appTop {X T Y : Scheme.{0}} [IsAffine Y] (p : X ⟶ T)
    (ε : T ⟶ X) (g : X ⟶ Y) (h : ε ≫ p = 𝟙 T) (hs : Function.Surjective p.appTop.hom) :
    g = p ≫ ε ≫ g := by
  refine ext_of_isAffine ?_
  ext a
  obtain ⟨b, hb⟩ := hs (g.appTop.hom a)
  have hεp : ε.appTop.hom (p.appTop.hom b) = b := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, h]
    simp
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rw [← hb, hεp]

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.local_rigidity : ∀ (X T Y : Scheme.{0}) (p : X ⟶ T) (ε : T ⟶ X) (g : X ⟶ Y), ε ≫ p = 𝟙 T → UniversallyClosed p → (∀ V : T.Opens, Function.Surjective (p.app V).hom) → ∀ (t : T) (y : Y), (∀ x : X, p x = t → g x = y) → ∃ V : T.Opens, t ∈ V ∧ (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ ε ≫ g := by
  intro X T Y p ε g h hp hsurj t y hfib
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  have hZ : IsClosed (p '' (g ⁻¹ᵁ W : Set X)ᶜ) :=
    p.isClosedMap _ (g ⁻¹ᵁ W).isOpen.isClosed_compl
  let V : T.Opens := ⟨(p '' (g ⁻¹ᵁ W : Set X)ᶜ)ᶜ, hZ.isOpen_compl⟩
  have htV : t ∈ V := by
    rintro ⟨x, hx, rfl⟩
    exact hx (show g x ∈ W from (hfib x rfl).symm ▸ hyW)
  have hsub : p ⁻¹ᵁ V ≤ g ⁻¹ᵁ W := by
    intro x hx
    by_contra hxW
    exact hx ⟨x, hxW, rfl⟩
  have hεV : V ≤ ε ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    intro s hs
    change p (ε s) ∈ V
    rw [← Scheme.Hom.comp_apply, h]
    exact hs
  haveI : IsAffine W := hW
  refine ⟨V, htV, ?_⟩
  have hsec : ε.resLE (p ⁻¹ᵁ V) V hεV ≫ p ∣_ V = 𝟙 V.toScheme := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, h]
    simp
  have hsV : Function.Surjective (p ∣_ V).appTop.hom := by
    rw [morphismRestrict_appTop]
    have hiso := ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage p V ⊤)).op)
    exact hiso.2.comp (hsurj (V.ι ''ᵁ ⊤))
  have key := congrArg (· ≫ W.ι)
    (_root_.GlobalTheory.eq_comp_section_of_surjective_appTop (p ∣_ V) (ε.resLE (p ⁻¹ᵁ V) V hεV)
      (g.resLE W (p ⁻¹ᵁ V) hsub) hsec hsV)
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι] at key
  rw [key, Scheme.Hom.resLE_comp_ι_assoc, ← Category.assoc (p ∣_ V), morphismRestrict_ι,
    Category.assoc]

end GlobalTheory
end
