module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismLiftSystemPresentsOfHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismLiftSystemPresentsOfHom
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LiftSys.Glue

open Opposite Limits

theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem spMap_surjective {A B : Type} [CommRing A] [CommRing B] (q : A →+* B)
    (hq : Function.Surjective q) (hn : ∀ a, q a = 0 → a * a = 0) : Function.Surjective (spMap q) := by
  intro p
  have hker : RingHom.ker q ≤ p.asIdeal := by
    intro x hx
    have hx2 := hn x (RingHom.mem_ker.1 hx)
    exact (p.isPrime.mem_or_mem (by rw [hx2]; exact p.asIdeal.zero_mem)).elim id id
  haveI := p.isPrime
  haveI : (Ideal.map q p.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hq hker
  refine ⟨⟨Ideal.map q p.asIdeal, this⟩, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap q (Ideal.map q p.asIdeal) = p.asIdeal
  rw [Ideal.comap_map_of_surjective _ hq, sup_eq_left]
  intro x hx
  exact hker (by simpa [RingHom.mem_ker] using hx)

theorem exists_affine {X₀ : Scheme.{0}} {x : X₀} {U : X₀.Opens} (hx : x ∈ U) :
    ∃ W : X₀.affineOpens, x ∈ W.1 ∧ W.1 ≤ U := by
  obtain ⟨W, hW, hxW, hWU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X₀.isBasis_affineOpens) hx
  exact ⟨⟨W, hW⟩, hxW, hWU⟩

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀}

abbrev cov {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} (h : S.Presents s i)
    (hc : ∀ x : X, ∃ (U : X₀.affineOpens) (z : Sp (S.F.obj (op U))), h.y (op U) z = x) :
    X.OpenCover where
  I₀ := X₀.affineOpens
  X U := Sp (S.F.obj (op U))
  f U := h.y (op U)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun x ↦ by obtain ⟨U, z, hz⟩ := hc x; exact ⟨U, z, hz⟩, fun U ↦ h.isOpen _⟩

def dir {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} (h : S.Presents s i)
    (hc : ∀ x : X, ∃ (U : X₀.affineOpens) (z : Sp (S.F.obj (op U))), h.y (op U) z = x)
    (hd : ∀ (U V : X₀.affineOpens) (a : Sp (S.F.obj (op U))) (b : Sp (S.F.obj (op V))),
      h.y (op U) a = h.y (op V) b → ∃ (W : X₀.affineOpens) (_ : W ≤ U) (_ : W ≤ V)
        (c : Sp (S.F.obj (op W))), h.y (op W) c = h.y (op U) a) :
    (cov h hc).LocallyDirected where
  trans {U V} a := spMap (mp S.F a.op : S.F.obj (op V) →+* S.F.obj (op U))
  trans_id U := by
    haveI := h.isOpen (op U)
    rw [← cancel_mono (h.y (op U))]
    exact (h.nat _).trans (Category.id_comp _).symm
  trans_comp {U V W} a b := by
    haveI := h.isOpen (op W)
    rw [← cancel_mono (h.y (op W))]
    rw [Category.assoc, h.nat, h.nat, h.nat]
  w {U V} a := h.nat a.op
  directed {U V} x := by
    haveI := h.isOpen (op U)
    haveI := h.isOpen (op V)
    obtain ⟨W, hWU, hWV, c, hcW⟩ := hd U V (pullback.fst (h.y (op U)) (h.y (op V)) x)
      (pullback.snd (h.y (op U)) (h.y (op V)) x)
      (by rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply])
    refine ⟨W, homOfLE hWU, homOfLE hWV, c, ?_⟩
    apply (pullback.fst (h.y (op U)) (h.y (op V)) ≫ h.y (op U)).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc]
    change (spMap _ ≫ h.y (op U)) c = _
    rw [h.nat, hcW, Scheme.Hom.comp_apply]
  property_trans {U V} a := by
    haveI := h.isOpen (op V)
    haveI : IsOpenImmersion (spMap (mp S.F a.op : S.F.obj (op V) →+* S.F.obj (op U)) ≫ h.y (op V)) := by
      rw [h.nat]; exact h.isOpen _
    exact IsOpenImmersion.of_comp _ (h.y (op V))

theorem presents_hom : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (Y : Scheme.{0}) (t : Y ⟶ Sp R) (j : X₀ ⟶ Y), IsPullback i s₀ s (spMap π) → S.Presents t j → S'.Presents s i → (∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b)) → ∃ f : X ⟶ Y, f ≫ t = s ∧ i ≫ f = j := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ S S' X s i Y t j hpb hY hX hψ
  obtain ⟨ψ, hψp, hψn⟩ := hψ

  have hsurU : ∀ U, Function.Surjective (spMap (S'.p U)) := fun U ↦
    spMap_surjective _ (S'.surj U) fun b hb ↦ by
      have hb' := (S'.ker U b).1 hb
      have : b * b ∈ (I.map (algebraMap R (S'.F.obj U))) ^ 2 := by
        rw [pow_two]; exact Ideal.mul_mem_mul hb' hb'
      rwa [map_sq hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  have hπs : Function.Surjective (spMap π) := spMap_surjective π hπ fun a ha ↦ by
    have ha' : a ∈ I := hk ▸ RingHom.mem_ker.2 ha
    have : a * a ∈ I ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha' ha'
    rwa [hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this

  haveI : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom π) hπ
  haveI hic : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip inferInstance
  have hinj : Function.Injective i := i.isClosedEmbedding.injective
  have hisurj : Function.Surjective i :=
    (MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) hpb.flip ⟨hπs⟩).surj

  have hrng : ∀ (U : X₀.affineOpens) (z : Sp (S'.F.obj (op U))), ∃ x₀ ∈ U.1, hX.y (op U) z = i x₀ := by
    intro U z
    obtain ⟨w, rfl⟩ := hsurU (op U) z
    refine ⟨affPt s₀ U w, U.2.range_fromSpec.le ⟨w, rfl⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, hX.red (op U), Scheme.Hom.comp_apply]
  have hcov : ∀ (U : X₀.affineOpens) (x₀ : X₀), x₀ ∈ U.1 → ∃ z : Sp (S'.F.obj (op U)), hX.y (op U) z = i x₀ := by
    intro U x₀ hx
    obtain ⟨w, hw⟩ : x₀ ∈ Set.range (affPt s₀ U) := U.2.range_fromSpec.ge hx
    refine ⟨spMap (S'.p (op U)) w, ?_⟩
    change (spMap (S'.p (op U)) ≫ hX.y (op U)) w = i x₀
    rw [hX.red (op U), Scheme.Hom.comp_apply]
    exact congrArg i hw
  have hc : ∀ x : X, ∃ (U : X₀.affineOpens) (z : Sp (S'.F.obj (op U))), hX.y (op U) z = x := by
    intro x
    obtain ⟨x₀, rfl⟩ := hisurj x
    obtain ⟨U, hxU, -⟩ := exists_affine (show x₀ ∈ (⊤ : X₀.Opens) from trivial)
    obtain ⟨z, hz⟩ := hcov U x₀ hxU
    exact ⟨U, z, hz⟩
  have hd : ∀ (U V : X₀.affineOpens) (a : Sp (S'.F.obj (op U))) (b : Sp (S'.F.obj (op V))),
      hX.y (op U) a = hX.y (op V) b → ∃ (W : X₀.affineOpens) (_ : W ≤ U) (_ : W ≤ V)
        (c : Sp (S'.F.obj (op W))), hX.y (op W) c = hX.y (op U) a := by
    intro U V a b hab
    obtain ⟨x₀, hxU, ha⟩ := hrng U a
    obtain ⟨x₁, hxV, hb⟩ := hrng V b
    have e : x₀ = x₁ := hinj (ha.symm.trans (hab.trans hb))
    subst e
    obtain ⟨W, hxW, hWle⟩ := exists_affine (show x₀ ∈ U.1 ⊓ V.1 from ⟨hxU, hxV⟩)
    obtain ⟨c, hc'⟩ := hcov W x₀ hxW
    exact ⟨W, le_inf_iff.1 hWle |>.1, le_inf_iff.1 hWle |>.2, c, hc'.trans ha.symm⟩
  letI := dir hX hc hd
  let 𝒰 := cov hX hc
  let g : ∀ U : 𝒰.I₀, 𝒰.X U ⟶ Y := fun U ↦
    spMap (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)) ≫ hY.y (op U)
  have hg : ∀ {U V : 𝒰.I₀} (a : U ⟶ V), 𝒰.trans a ≫ g V = g U := by
    intro U V a
    change spMap (mp S'.F a.op : S'.F.obj (op V) →+* S'.F.obj (op U)) ≫
      spMap (ψ (op V) : S.F.obj (op V) →+* S'.F.obj (op V)) ≫ hY.y (op V) = _
    rw [← Category.assoc, ← spMap_comp₂]
    have e : (mp S'.F a.op : S'.F.obj (op V) →+* S'.F.obj (op U)).comp
        (ψ (op V) : S.F.obj (op V) →+* S'.F.obj (op V)) =
        (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)).comp
          (mp S.F a.op : S.F.obj (op V) →+* S.F.obj (op U)) :=
      RingHom.ext fun b ↦ hψn (op V) (op U) a.op b
    rw [e, spMap_comp₂, Category.assoc, hY.nat a.op]
  refine ⟨𝒰.glueMorphismsOfLocallyDirected g hg, 𝒰.hom_ext _ _ fun U ↦ ?_, ?_⟩
  · rw [𝒰.map_glueMorphismsOfLocallyDirected_assoc g hg U]
    change (spMap (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)) ≫ hY.y (op U)) ≫ t = hX.y (op U) ≫ s
    rw [Category.assoc, hY.base, hX.base, ← spMap_comp₂]
    exact congrArg spMap (RingHom.ext fun r ↦ (ψ (op U)).commutes r)
  · let 𝒱 : X₀.OpenCover := Scheme.Cover.mkOfCovers X₀.affineOpens (fun U ↦ Sp (Sec s₀ U.1))
      (fun U ↦ affPt s₀ U)
      (fun x ↦ by
        obtain ⟨U, hxU, -⟩ := exists_affine (show x ∈ (⊤ : X₀.Opens) from trivial)
        obtain ⟨w, hw⟩ : x ∈ Set.range (affPt s₀ U) := U.2.range_fromSpec.ge hxU
        exact ⟨U, w, hw⟩)
      (fun U ↦ IsAffineOpen.isOpenImmersion_fromSpec U.2)
    refine 𝒱.hom_ext _ _ fun U ↦ ?_
    change affPt s₀ U ≫ i ≫ _ = affPt s₀ U ≫ j
    rw [← Category.assoc, show affPt s₀ U ≫ i = _ from (hX.red (op U)).symm,
      show affPt s₀ U ≫ j = _ from (hY.red (op U)).symm, Category.assoc]
    change spMap (S'.p (op U)) ≫ 𝒰.f U ≫ _ = _
    rw [𝒰.map_glueMorphismsOfLocallyDirected g hg U]
    change spMap (S'.p (op U)) ≫ spMap (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)) ≫ hY.y (op U) = _
    rw [← Category.assoc, ← spMap_comp₂]
    exact congrArg (· ≫ hY.y (op U)) (congrArg spMap (RingHom.ext fun b ↦ hψp (op U) b))

end GlobalTheory.LiftSys.Glue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismLiftSystemPresentsOfHomStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_morphism_liftSystemPresents_of_hom : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (Y : Scheme.{0}) (t : Y ⟶ Sp R) (j : X₀ ⟶ Y), IsPullback i s₀ s (spMap π) → S.Presents t j → S'.Presents s i → (∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b)) → ∃ f : X ⟶ Y, f ≫ t = s ∧ i ≫ f = j := by
  first | exact @GlobalTheory.LiftSys.Glue.presents_hom | exact GlobalTheory.LiftSys.Glue.presents_hom | (intros; apply GlobalTheory.LiftSys.Glue.presents_hom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppOfFlatBaseChangeEqualised
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppOfFlatBaseChangeEqualised
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.AffDesc

open TensorProduct

theorem appLE_eq_of_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem isoPushout_desc_tmul {R0 A B : Type} [CommRing R0] [CommRing A] [CommRing B] [Algebra R0 A]
    [Algebra R0 B] {D : CommRingCat.{0}} (u : CommRingCat.of A ⟶ D) (v : CommRingCat.of B ⟶ D)
    (w : CommRingCat.ofHom (algebraMap R0 A) ≫ u = CommRingCat.ofHom (algebraMap R0 B) ≫ v) (a : A) (b : B) :
    ((CommRingCat.isPushout_tensorProduct R0 A B).isoPushout.hom ≫ pushout.desc u v w).hom (a ⊗ₜ b) =
      u.hom a * v.hom b := by
  have e : a ⊗ₜ[R0] b = Algebra.TensorProduct.includeLeftRingHom a *
      Algebra.TensorProduct.includeRight.toRingHom b := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [e, map_mul]
  have h1 := congrArg (fun φ => φ.hom a)
    ((CommRingCat.isPushout_tensorProduct R0 A B).inl_isoPushout_hom =≫ pushout.desc u v w)
  have h2 := congrArg (fun φ => φ.hom b)
    ((CommRingCat.isPushout_tensorProduct R0 A B).inr_isoPushout_hom =≫ pushout.desc u v w)
  simp only [Category.assoc, pushout.inl_desc, pushout.inr_desc, CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.hom_ofHom] at h1 h2
  rw [← h1, ← h2]
  rfl

theorem appLE_apply_appLE {X Y Y' Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X ⟶ Y') (g' : Y' ⟶ Z)
    (h : f ≫ g = f' ≫ g') (U : Z.Opens) (V : Y.Opens) (V' : Y'.Opens) (W : X.Opens) (e₁ : V ≤ g ⁻¹ᵁ U)
    (e₂ : W ≤ f ⁻¹ᵁ V) (e₁' : V' ≤ g' ⁻¹ᵁ U) (e₂' : W ≤ f' ⁻¹ᵁ V') (x : Γ(Z, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) = (f'.appLE V' W e₂').hom ((g'.appLE U V' e₁').hom x) := by
  have a := Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂
  have b := Scheme.Hom.appLE_comp_appLE f' g' U V' W e₁' e₂'
  have c := appLE_eq_of_eq h U W (by rw [Scheme.Hom.comp_preimage]; exact le_trans e₂ (Scheme.Hom.preimage_mono f e₁))
    (by rw [Scheme.Hom.comp_preimage]; exact le_trans e₂' (Scheme.Hom.preimage_mono f' e₁'))
  exact congrArg (fun φ => CommRingCat.Hom.hom φ x) (a.trans (c.trans b.symm))

theorem appTop_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) : f.appTop = f.appLE ⊤ ⊤ le_top :=
  Scheme.Hom.app_eq_appLE f

end GlobalTheory.Mum.AffDesc

namespace GlobalTheory.Mum.AffDesc
open TensorProduct

theorem mem_range_app_of_flat : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Flat y → IsPullback p q y π → ∀ r : pullback p p ⟶ pullback π π, r ≫ pullback.fst π π = pullback.fst p p ≫ q → r ≫ pullback.snd π π = pullback.snd p p ≫ q → IsPullback r (pullback.fst p p ≫ p) (pullback.fst π π ≫ π) y → (∀ x : Γ(S, ⊤), (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x → x ∈ Set.range π.appTop.hom) → ∀ V : Y.Opens, IsAffineOpen V → ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom := by
  intro R _ S Y Z π y p q hπ hy H r h1 h2 hP hx V hV f hf
  classical
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace π
  haveI : QuasiSeparatedSpace S := (quasiSeparated_iff_quasiSeparatedSpace π).1 inferInstance
  haveI : CompactSpace (pullback π π : Scheme) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst π π ≫ π)
  have hUY1 : p ⁻¹ᵁ V = q ⁻¹ᵁ ⊤ ⊓ p ⁻¹ᵁ V := by simp
  have hUY2 : pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V) = r ⁻¹ᵁ ⊤ ⊓ (pullback.fst p p ≫ p) ⁻¹ᵁ V := by
    simp [Scheme.Hom.comp_preimage]
  have i1 := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H.flip (US := ⊤) (UX := ⊤) (UT := V)
    le_top le_top hUY1 (isAffineOpen_top _) hV isCompact_univ isQuasiSeparated_univ
  have m2 := mono_pushoutSection_of_isCompact_of_flat_right hP (US := ⊤) (UX := ⊤) (UT := V)
    le_top le_top hUY2 (isAffineOpen_top _) hV isCompact_univ
  letI aB : Algebra Γ(Sp R, ⊤) Γ(S, ⊤) := (π.appLE ⊤ ⊤ le_top).hom.toAlgebra
  letI aA : Algebra Γ(Sp R, ⊤) Γ(Y, V) := (y.appLE ⊤ V le_top).hom.toAlgebra
  letI aC : Algebra Γ(Sp R, ⊤) Γ(pullback π π, ⊤) := ((pullback.fst π π ≫ π).appLE ⊤ ⊤ le_top).hom.toAlgebra
  haveI : Module.Flat Γ(Sp R, ⊤) Γ(Y, V) := y.flat_appLE (isAffineOpen_top _) hV le_top
  let ΦB := (CommRingCat.isPushout_tensorProduct Γ(Sp R, ⊤) Γ(S, ⊤) Γ(Y, V)).isoPushout.hom ≫
    pushoutSection H.flip (US := ⊤) (UX := ⊤) (UT := V) le_top le_top hUY1
  let ΦC := (CommRingCat.isPushout_tensorProduct Γ(Sp R, ⊤) Γ(pullback π π, ⊤) Γ(Y, V)).isoPushout.hom ≫
    pushoutSection hP (US := ⊤) (UX := ⊤) (UT := V) le_top le_top hUY2
  have hB : Function.Surjective ΦB.hom := by
    have : IsIso ΦB := by dsimp only [ΦB]; infer_instance
    exact (ConcreteCategory.bijective_of_isIso ΦB).2
  have hC : Function.Injective ΦC.hom := by
    have : Mono ΦC := by dsimp only [ΦC]; infer_instance
    exact (ConcreteCategory.mono_iff_injective_of_preservesPullback ΦC).1 this
  have fB : ∀ (b : Γ(S, ⊤)) (a : Γ(Y, V)), ΦB.hom (b ⊗ₜ a) =
      (q.appLE ⊤ (p ⁻¹ᵁ V) (by simp)).hom b * (p.appLE V (p ⁻¹ᵁ V) le_rfl).hom a :=
    fun b a => isoPushout_desc_tmul _ _ _ b a
  have fC : ∀ (c : Γ(pullback π π, ⊤)) (a : Γ(Y, V)), ΦC.hom (c ⊗ₜ a) =
      (r.appLE ⊤ (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp)).hom c *
        ((pullback.fst p p ≫ p).appLE V (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp [Scheme.Hom.comp_preimage])).hom a :=
    fun c a => isoPushout_desc_tmul _ _ _ c a
  have k1 : ∀ x, (pullback.fst π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) x) =
      ((pullback.fst π π ≫ π).appLE ⊤ ⊤ le_top) x := fun x =>
    congrArg (fun φ => CommRingCat.Hom.hom φ x) (Scheme.Hom.appLE_comp_appLE (pullback.fst π π) π ⊤ ⊤ ⊤ le_top le_top)
  have k2 : ∀ x, (pullback.snd π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) x) =
      ((pullback.fst π π ≫ π).appLE ⊤ ⊤ le_top) x := fun x =>
    (congrArg (fun φ => CommRingCat.Hom.hom φ x) (Scheme.Hom.appLE_comp_appLE (pullback.snd π π) π ⊤ ⊤ ⊤ le_top le_top)).trans
      (congrArg (fun φ => CommRingCat.Hom.hom φ x) (appLE_eq_of_eq (pullback.condition (f := π) (g := π)).symm _ _ _ _))
  let d : Γ(S, ⊤) →ₗ[Γ(Sp R, ⊤)] Γ(pullback π π, ⊤) :=
    { toFun := fun x => (pullback.fst π π).appLE ⊤ ⊤ le_top x - (pullback.snd π π).appLE ⊤ ⊤ le_top x
      map_add' := fun x x' => by simp only [map_add (f := _)]; abel
      map_smul' := fun c x => by
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, k1, k2, RingHom.id_apply]
        ring }
  have hex : Function.Exact (Algebra.linearMap Γ(Sp R, ⊤) Γ(S, ⊤)) d := by
    intro x
    constructor
    · intro h0
      have e0 : (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x := by
        rw [appTop_eq_appLE, appTop_eq_appLE]; exact sub_eq_zero.1 h0
      obtain ⟨c, hc⟩ := hx x e0
      refine ⟨c, ?_⟩
      rw [appTop_eq_appLE] at hc
      exact hc
    · rintro ⟨c, rfl⟩
      show (pullback.fst π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) c) -
        (pullback.snd π π).appLE ⊤ ⊤ le_top ((π.appLE ⊤ ⊤ le_top) c) = 0
      rw [k1, k2, sub_self]
  have hex' := Module.Flat.rTensor_exact Γ(Y, V) hex
  have hEq : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  have c1 : ∀ b, ((pullback.fst p p).app (p ⁻¹ᵁ V)).hom ((q.appLE ⊤ (p ⁻¹ᵁ V) (by simp)).hom b) =
      (r.appLE ⊤ (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp)).hom ((pullback.fst π π).appLE ⊤ ⊤ le_top b) :=
    fun b => by
      rw [Scheme.Hom.app_eq_appLE]
      exact appLE_apply_appLE (pullback.fst p p) q r (pullback.fst π π) h1.symm ⊤ (p ⁻¹ᵁ V) ⊤
        (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp) le_rfl le_top (by simp) b
  have c2 : ∀ b, ((pullback.snd p p).appLE _ _ hEq.ge).hom ((q.appLE ⊤ (p ⁻¹ᵁ V) (by simp)).hom b) =
      (r.appLE ⊤ (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp)).hom ((pullback.snd π π).appLE ⊤ ⊤ le_top b) :=
    fun b => appLE_apply_appLE (pullback.snd p p) q r (pullback.snd π π) h2.symm ⊤ (p ⁻¹ᵁ V) ⊤
      (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp) hEq.ge le_top (by simp) b
  have c3 : ∀ a, ((pullback.fst p p).app (p ⁻¹ᵁ V)).hom ((p.appLE V (p ⁻¹ᵁ V) le_rfl).hom a) =
      ((pullback.fst p p ≫ p).appLE V (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp [Scheme.Hom.comp_preimage])).hom a :=
    fun a => by
      rw [Scheme.Hom.app_eq_appLE]
      exact congrArg (fun φ => CommRingCat.Hom.hom φ a)
        (Scheme.Hom.appLE_comp_appLE (pullback.fst p p) p V (p ⁻¹ᵁ V) (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) le_rfl le_rfl)
  have c4 : ∀ a, ((pullback.snd p p).appLE _ _ hEq.ge).hom ((p.appLE V (p ⁻¹ᵁ V) le_rfl).hom a) =
      ((pullback.fst p p ≫ p).appLE V (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) (by simp [Scheme.Hom.comp_preimage])).hom a :=
    fun a => (congrArg (fun φ => CommRingCat.Hom.hom φ a)
      (Scheme.Hom.appLE_comp_appLE (pullback.snd p p) p V (p ⁻¹ᵁ V) (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) le_rfl hEq.ge)).trans
      (congrArg (fun φ => CommRingCat.Hom.hom φ a) (appLE_eq_of_eq (pullback.condition (f := p) (g := p)).symm V
        (pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V)) _ _))
  have key : ∀ t, ΦC.hom (d.rTensor Γ(Y, V) t) = ((pullback.fst p p).app (p ⁻¹ᵁ V)).hom (ΦB.hom t) -
      ((pullback.snd p p).appLE _ _ hEq.ge).hom (ΦB.hom t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b a =>
      rw [LinearMap.rTensor_tmul, fC, fB, map_mul, map_mul, c1, c2, c3, c4]
      change (r.appLE _ _ _).hom ((pullback.fst π π).appLE ⊤ ⊤ le_top b - (pullback.snd π π).appLE ⊤ ⊤ le_top b) * _ = _
      rw [map_sub, sub_mul]
    | add t t' ht ht' =>
      rw [map_add (f := _), map_add (f := _), ht, ht', map_add (f := _), map_add (f := _), map_add (f := _)]
      abel
  obtain ⟨t, rfl⟩ := hB f
  have hz : d.rTensor Γ(Y, V) t = 0 := hC (by rw [key, map_zero, hf hEq, sub_self])
  obtain ⟨s, rfl⟩ := (hex' t).1 hz
  clear hf hz key
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul c a =>
    rw [LinearMap.rTensor_tmul, fB]
    refine ⟨(y.appLE ⊤ V le_top).hom c * a, ?_⟩
    rw [map_mul, Scheme.Hom.app_eq_appLE]
    congr 1
    exact appLE_apply_appLE p y q π H.w ⊤ V ⊤ (p ⁻¹ᵁ V) le_top le_rfl le_top (by simp) c
  | add s s' hs hs' =>
    obtain ⟨u, hu⟩ := hs
    obtain ⟨u', hu'⟩ := hs'
    exact ⟨u + u', by rw [map_add (f := _), hu, hu', map_add (f := _), map_add (f := _)]⟩

end GlobalTheory.Mum.AffDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeAppOfFlatBaseChangeEqualisedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_app_of_flat_baseChange_equalised : ∀ (R : Type) [CommRing R] (S Y Z : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Flat y → IsPullback p q y π → ∀ r : pullback p p ⟶ pullback π π, r ≫ pullback.fst π π = pullback.fst p p ≫ q → r ≫ pullback.snd π π = pullback.snd p p ≫ q → IsPullback r (pullback.fst p p ≫ p) (pullback.fst π π ≫ π) y → (∀ x : Γ(S, ⊤), (pullback.fst π π).appTop.hom x = (pullback.snd π π).appTop.hom x → x ∈ Set.range π.appTop.hom) → ∀ V : Y.Opens, IsAffineOpen V → ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom := by
  first | exact @GlobalTheory.Mum.AffDesc.mem_range_app_of_flat | exact GlobalTheory.Mum.AffDesc.mem_range_app_of_flat | (intros; apply GlobalTheory.Mum.AffDesc.mem_range_app_of_flat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureGenericFibreSpreadsFgSubalgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureGenericFibreSpreadsFgSubalgebra
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LevelSpread

theorem exists_ring {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] (R₁ : Subalgebra o₁ Ω₁)
    {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (κ : o₁ →+* o₂)
    (hR₁ : R₁.FG) (hfr : ∀ x : Ω₁, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b) [FiniteDimensional Ω₁ Ω₂]
    (hκ : (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) :
    ∃ (R : Subalgebra o₂ Ω₂) (h : R₁ →+* R), R.FG ∧ (∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧
      ∀ a, ((h a : R) : Ω₂) = algebraMap Ω₁ Ω₂ a := by
  obtain ⟨s, hs⟩ := hR₁
  let B := Module.finBasis Ω₁ Ω₂
  let T : Set Ω₂ := (algebraMap Ω₁ Ω₂) '' (s : Set Ω₁) ∪ Set.range B
  let R : Subalgebra o₂ Ω₂ := Algebra.adjoin o₂ T
  have hT : T.Finite := (s.finite_toSet.image _).union (Set.finite_range _)
  have mem : ∀ a ∈ R₁, algebraMap Ω₁ Ω₂ a ∈ R := by
    intro a ha
    rw [← hs] at ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (Or.inl ⟨x, hx, rfl⟩)
    | algebraMap r =>
      have := congrArg (fun f => f r) hκ
      simp only [RingHom.comp_apply] at this
      rw [← this]; exact R.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let h : R₁ →+* R := ((algebraMap Ω₁ Ω₂).comp R₁.val.toRingHom).codRestrict R (fun a => mem a a.2)
  refine ⟨R, h, Subalgebra.fg_def.2 ⟨T, hT, rfl⟩, ?_, fun a => rfl⟩
  let D : Ω₂ → Prop := fun x => ∃ a ∈ R, ∃ b ∈ R, x = a / b
  have Dmem : ∀ x ∈ R, D x := fun x hx => ⟨x, hx, 1, R.one_mem, (div_one x).symm⟩
  have Dadd : ∀ x y, D x → D y → D (x + y) := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    by_cases hb0 : b = 0
    · exact ⟨c, hc, d, hd, by simp [hb0]⟩
    by_cases hd0 : d = 0
    · exact ⟨a, ha, b, hb, by simp [hd0]⟩
    exact ⟨a * d + b * c, add_mem (mul_mem ha hd) (mul_mem hb hc), b * d, mul_mem hb hd, div_add_div _ _ hb0 hd0⟩
  have Dmul : ∀ x y, D x → D y → D (x * y) := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    exact ⟨a * c, mul_mem ha hc, b * d, mul_mem hb hd, div_mul_div_comm _ _ _ _⟩
  have Dbase : ∀ c : Ω₁, D (algebraMap Ω₁ Ω₂ c) := by
    intro c
    obtain ⟨a, ha, b, hb, rfl⟩ := hfr c
    exact ⟨_, mem a ha, _, mem b hb, map_div₀ _ _ _⟩
  intro x
  rw [← B.sum_repr x]
  refine Finset.sum_induction _ D Dadd (Dmem 0 R.zero_mem) fun i _ => ?_
  rw [Algebra.smul_def]
  exact Dmul _ _ (Dbase _) (Dmem _ (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)))

theorem step {Ω : Type} [Field Ω] {A B : Type} [CommRing A] [CommRing B] (a : A →+* Ω) (b : B →+* Ω)
    (g : A →+* B) (hg : b.comp g = a) (Q : PolAV (Sp Ω)) (P : PolAV (Sp A)) (φ : Q.A.left ⟶ P.A.left)
    (hQ : IsGrpPullback Q.A P.A (spMap a) φ) (eQ : LBIso Q.L (P.L.pull φ)) :
    ∃ φ' : Q.A.left ⟶ (StrictPull.polPull P (spMap g)).A.left,
      φ' ≫ pullback.fst P.A.hom (spMap g) = φ ∧ φ' ≫ pullback.snd P.A.hom (spMap g) = Q.A.hom ≫ spMap b ∧
      IsGrpPullback Q.A (StrictPull.polPull P (spMap g)).A (spMap b) φ' ∧
      LBIso Q.L ((StrictPull.polPull P (spMap g)).L.pull φ') := by
  have e : spMap b ≫ spMap g = spMap a := by rw [← hg, ← Spec.map_comp]; rfl
  let φ' : Q.A.left ⟶ (StrictPull.polPull P (spMap g)).A.left :=
    pullback.lift φ (Q.A.hom ≫ spMap b) (by rw [hQ.1.w, Category.assoc, e])
  have h1 : φ' ≫ pullback.fst P.A.hom (spMap g) = φ := pullback.lift_fst _ _ _
  refine ⟨φ', h1, pullback.lift_snd _ _ _, IsGrpPullback.cancel (isGrpPullback_pullback P.A (spMap g)) (hQ.congr e.symm h1.symm)
    (pullback.lift_snd _ _ _), ?_⟩
  exact LBIso.trans Q.isLB (pull_isLB P.isLB _) (pull_isLB (StrictPull.polPull P (spMap g)).isLB _) eQ
    (GenSpread.lbIso_pull_pull P.isLB φ' h1.symm)

theorem stepBase {S₁ S : Scheme.{0}} (P₁ : PolAV S₁) (P : PolAV S) (t : S ⟶ S₁) (ψ : P.A.left ⟶ P₁.A.left)
    (hP : IsGrpPullback P.A P₁.A t ψ) (eP : LBIso P.L (P₁.L.pull ψ)) {S' : Scheme.{0}} (f : S' ⟶ S) :
    IsGrpPullback (StrictPull.polPull P f).A P₁.A (f ≫ t) (pullback.fst P.A.hom f ≫ ψ) ∧
      LBIso (StrictPull.polPull P f).L (P₁.L.pull (pullback.fst P.A.hom f ≫ ψ)) :=
  ⟨(isGrpPullback_pullback P.A f).comp hP,
    LBIso.trans (pull_isLB P.isLB _) (pull_isLB (pull_isLB P₁.isLB ψ) _) (pull_isLB P₁.isLB _)
      (GenSpread.lbIso_pullback eP _) (GenSpread.lbIso_pull_pull P₁.isLB _ rfl).symm⟩

theorem indep_cast {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} {n m K : ℕ} (h : n = m)
    (y : Fin m → (T ⟶ A))
    (H : ∀ c c' : Fin m → Fin K, linComb y (fun i => (c i : ℕ)) = linComb y (fun i => (c' i : ℕ)) → c = c') :
    ∀ c c' : Fin n → Fin K, linComb (fun i => y (Fin.cast h i)) (fun i => (c i : ℕ)) =
      linComb (fun i => y (Fin.cast h i)) (fun i => (c' i : ℕ)) → c = c' := by
  subst h; exact H

theorem level_spreads : ∀ {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] (R₁ : Subalgebra o₁ Ω₁) (P₁ : PolAV (Sp R₁)) {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [ArithBase o₂ Ω₂] [Algebra Ω₁ Ω₂] (κ : o₁ →+* o₂) (Q : PolAV (Sp Ω₂)) (φ : Q.A.left ⟶ P₁.A.left) (K : ℕ) (ze : o₂ˣ), R₁.FG → (∀ x : Ω₁, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b) → FiniteDimensional Ω₁ Ω₂ → (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) → IsUnit (K : o₂) → Q.g = P₁.g → IsGrpPullback Q.A P₁.A (spMap ((algebraMap Ω₁ Ω₂).comp R₁.val.toRingHom)) φ → LBIso Q.L (P₁.L.pull φ) → Nonempty (Out.Level Q K (unitOn (Units.map (algebraMap o₂ Ω₂ : o₂ →* Ω₂) ze))) → ∃ (R : Subalgebra o₂ Ω₂) (h : R₁ →+* R) (P : PolAV (Sp R)) (ψ : P.A.left ⟶ P₁.A.left), R.FG ∧ (∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ (∀ a, ((h a : R) : Ω₂) = algebraMap Ω₁ Ω₂ a) ∧ P.g = P₁.g ∧ IsGrpPullback P.A P₁.A (spMap h) ψ ∧ LBIso P.L (P₁.L.pull ψ) ∧ Nonempty (Out.Level P K (unitOn ((Units.map (algebraMap o₂ R : o₂ →* R)) ze))) := by
  intro o₁ Ω₁ _ _ _ R₁ P₁ o₂ Ω₂ _ _ _ hB _ κ Q φ K ze hR₁ hfr hfd hκ hK hg hQ eQ hlev
  obtain ⟨lev⟩ := hlev
  have := hB.ded
  obtain ⟨R₀, h₀, hR₀, hfr₀, hh₀⟩ := exists_ring R₁ κ hR₁ hfr hκ
  let a₁ : R₁ →+* Ω₂ := (algebraMap Ω₁ Ω₂).comp R₁.val.toRingHom
  have c₀ : (algebraMap R₀ Ω₂).comp h₀ = a₁ := RingHom.ext hh₀
  let P₀ := StrictPull.polPull P₁ (spMap h₀)
  obtain ⟨φ₀, -, -, hQ₀, eQ₀⟩ := step a₁ (algebraMap R₀ Ω₂) h₀ c₀ Q P₁ φ hQ eQ
  have hP₀ : IsGrpPullback P₀.A P₁.A (spMap h₀) (pullback.fst P₁.A.hom (spMap h₀)) := isGrpPullback_pullback P₁.A _
  have eP₀ : LBIso P₀.L (P₁.L.pull (pullback.fst P₁.A.hom (spMap h₀))) := lbIso_refl P₀.isLB
  have := GenSpread.isFractionRing_of_forall_div hfr₀
  have := GenSpread.isNoetherianRing_of_fg hR₀
  have := P₀.isAb.smooth
  have := P₀.isAb.proper

  choose b hb Hpt using fun i => GenSpread.exists_hom (𝟙 (Sp R₀)) P₀.A.hom (φ := spMap (algebraMap R₀ Ω₂))
    (p₀ := 𝟙 (Sp Ω₂)) (IsPullback.of_vert_isIso ⟨by simp⟩) ((lev.pt i).left ≫ φ₀)
    (by rw [Category.assoc, hQ₀.1.w, Over.w_assoc]; simp)
  obtain ⟨R₂, g₂, le₂, hR₂, c₂, u₂, -, -, -⟩ := GenSpread.exists_shrink hR₀ b hb hQ₀.1
  let P₂ := StrictPull.polPull P₀ (spMap g₂)
  obtain ⟨φ₂, hφ₂, w₂, hQ₂, eQ₂⟩ := step (algebraMap R₀ Ω₂) (algebraMap R₂ Ω₂) g₂ c₂ Q P₀ φ₀ hQ₀ eQ₀
  obtain ⟨hP₂, eP₂⟩ := stepBase P₁ P₀ _ _ hP₀ eP₀ (spMap g₂)
  have es₂ : spMap (algebraMap R₂ Ω₂) ≫ spMap g₂ = spMap (algebraMap R₀ Ω₂) := by
    rw [← c₂, ← Spec.map_comp]; rfl
  have pts : ∀ i, ∃ y : baseOver (Sp R₂) ⟶ P₂.A, (lev.pt i).left ≫ φ₂ = spMap (algebraMap R₂ Ω₂) ≫ y.left := by
    intro i
    obtain ⟨u, hu, hu'⟩ := Hpt i R₂ g₂ (u₂ i) (Sp R₂) (spMap g₂) (𝟙 _) (by simp)
    have q₂ := IsPullback.of_hasPullback P₀.A.hom (spMap g₂)
    refine ⟨Over.homMk (q₂.lift u (𝟙 _) (by simpa using hu)) (q₂.lift_snd _ _ _), q₂.hom_ext ?_ ?_⟩
    · exact (Category.assoc _ _ _).trans ((congrArg ((lev.pt i).left ≫ ·) hφ₂).trans ((hu' _ es₂).symm.trans
        ((congrArg (spMap (algebraMap R₂ Ω₂) ≫ ·) (q₂.lift_fst _ _ _)).symm.trans (Category.assoc _ _ _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg ((lev.pt i).left ≫ ·) w₂).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ spMap (algebraMap R₂ Ω₂)) (Over.w (lev.pt i))).trans ((Category.id_comp _).trans
        ((Category.comp_id _).symm.trans ((congrArg (spMap (algebraMap R₂ Ω₂) ≫ ·) (q₂.lift_snd _ _ _)).symm.trans
        (Category.assoc _ _ _).symm))))))
  choose y hy using pts
  have hfr₂ : ∀ x : Ω₂, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hfr₀ x
    exact ⟨a, le₂ ha, b, le₂ hb, e⟩
  have := GenSpread.isFractionRing_of_forall_div hfr₂
  have := GenSpread.isNoetherianRing_of_fg hR₂
  have := P₂.isAb.proper
  obtain ⟨d, hd, Hi⟩ := GlobalTheory.T.exists_pointIndependence_spread_to_geometricFibres R₂ Ω₂ P₂.A Q.A φ₂ inferInstance hQ₂ _ K y lev.pt hy fun c c' h => by
    refine lev.indep (AlgebraicClosure Ω₂) (spMap (algebraMap Ω₂ _)) c c' ?_
    rw [← GenSpread.comp_linComb, ← GenSpread.comp_linComb, h]
  obtain ⟨R₃, g₃, le₃, hR₃, c₃, u₃, -, -, -⟩ :=
    GenSpread.exists_shrink hR₂ (fun _ : PUnit => d) (fun _ => hd) hQ₂.1
  let P₃ := StrictPull.polPull P₂ (spMap g₃)
  obtain ⟨φ₃, hφ₃, w₃, hQ₃, eQ₃⟩ := step (algebraMap R₂ Ω₂) (algebraMap R₃ Ω₂) g₃ c₃ Q P₂ φ₂ hQ₂ eQ₂
  obtain ⟨hP₃, eP₃⟩ := stepBase P₁ P₂ _ _ hP₂ eP₂ (spMap g₃)
  have es₃ : spMap (algebraMap R₃ Ω₂) ≫ spMap g₃ = spMap (algebraMap R₂ Ω₂) := by
    rw [← c₃, ← Spec.map_comp]; rfl
  have q₃ := IsPullback.of_hasPullback P₂.A.hom (spMap g₃)
  let y' : Fin (2 * Q.g) → (baseOver (Sp R₃) ⟶ P₃.A) := fun i =>
    Over.homMk (q₃.lift (spMap g₃ ≫ (y i).left) (𝟙 _) (by simp)) (q₃.lift_snd _ _ _)
  have hy' : ∀ i, (y' i).left ≫ pullback.fst P₂.A.hom (spMap g₃) = spMap g₃ ≫ (y i).left := fun i =>
    q₃.lift_fst _ _ _
  have hy₃ : ∀ i, (lev.pt i).left ≫ φ₃ = spMap (algebraMap R₃ Ω₂) ≫ (y' i).left := by
    intro i
    refine q₃.hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg ((lev.pt i).left ≫ ·) hφ₃).trans ((hy i).trans
        ((by rw [reassoc_of% es₃] : spMap (algebraMap R₂ Ω₂) ≫ (y i).left =
          spMap (algebraMap R₃ Ω₂) ≫ spMap g₃ ≫ (y i).left).trans
        ((congrArg (spMap (algebraMap R₃ Ω₂) ≫ ·) (hy' i)).symm.trans (Category.assoc _ _ _).symm))))
    · exact (Category.assoc _ _ _).trans ((congrArg ((lev.pt i).left ≫ ·) w₃).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ spMap (algebraMap R₃ Ω₂)) (Over.w (lev.pt i))).trans ((Category.id_comp _).trans
        ((Category.comp_id _).symm.trans ((congrArg (spMap (algebraMap R₃ Ω₂) ≫ ·) (q₃.lift_snd _ _ _)).symm.trans
        (Category.assoc _ _ _).symm))))))
  have Hi₃ := Hi R₃ g₃ (u₃ ⟨⟩) P₃.A (pullback.fst _ _) y' (isGrpPullback_pullback P₂.A (spMap g₃)) hy'
  have hfr₃ : ∀ x : Ω₂, ∃ a ∈ R₃, ∃ b ∈ R₃, x = a / b := fun x => by
    obtain ⟨a, ha, b, hb, e⟩ := hfr₂ x
    exact ⟨a, le₃ ha, b, le₃ hb, e⟩
  have := GenSpread.isFractionRing_of_forall_div hfr₃
  have := GenSpread.isNoetherianRing_of_fg hR₃
  have hgg : 2 * P₃.g = 2 * Q.g := congrArg (2 * ·) hg.symm
  obtain ⟨lev', -⟩ := GlobalTheory.T.isLevelStructure_of_generic_of_fibrewise_indep abelianSchemeLaws_all.1 R₃ Ω₂ P₃ Q φ₃ hQ₃ eQ₃ hg.symm K
    (Units.map (algebraMap o₂ R₃ : o₂ →* R₃) ze) (Units.map (algebraMap o₂ Ω₂ : o₂ →* Ω₂) ze)
    (by simpa using hK.map (algebraMap o₂ R₃)) rfl lev (fun i => y' (Fin.cast hgg i))
    (fun i₀ i hi => by obtain rfl : i₀ = Fin.cast hgg i := Fin.ext hi; exact hy₃ _)
    (fun F _ _ s c c' h => indep_cast hgg _ (Hi₃ F s) c c' h)
  have hh : ∀ a, (((g₃.comp (g₂.comp h₀)) a : R₃) : Ω₂) = algebraMap Ω₁ Ω₂ a := fun a =>
    (RingHom.congr_fun c₃ _).trans ((RingHom.congr_fun c₂ _).trans (hh₀ a))
  have hsp : spMap g₃ ≫ spMap g₂ ≫ spMap h₀ = spMap (g₃.comp (g₂.comp h₀)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  exact ⟨R₃, g₃.comp (g₂.comp h₀), P₃, _, hR₃, hfr₃, hh, rfl, hP₃.congr hsp rfl, eP₃, ⟨lev'⟩⟩

end GlobalTheory.LevelSpread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureGenericFibreSpreadsFgSubalgebraStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelStructure_genericFibre_spreads_fg_subalgebra : ∀ {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] (R₁ : Subalgebra o₁ Ω₁) (P₁ : PolAV (Sp R₁)) {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [ArithBase o₂ Ω₂] [Algebra Ω₁ Ω₂] (κ : o₁ →+* o₂) (Q : PolAV (Sp Ω₂)) (φ : Q.A.left ⟶ P₁.A.left) (K : ℕ) (ze : o₂ˣ), R₁.FG → (∀ x : Ω₁, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b) → FiniteDimensional Ω₁ Ω₂ → (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) → IsUnit (K : o₂) → Q.g = P₁.g → IsGrpPullback Q.A P₁.A (spMap ((algebraMap Ω₁ Ω₂).comp R₁.val.toRingHom)) φ → LBIso Q.L (P₁.L.pull φ) → Nonempty (Out.Level Q K (unitOn (Units.map (algebraMap o₂ Ω₂ : o₂ →* Ω₂) ze))) → ∃ (R : Subalgebra o₂ Ω₂) (h : R₁ →+* R) (P : PolAV (Sp R)) (ψ : P.A.left ⟶ P₁.A.left), R.FG ∧ (∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ (∀ a, ((h a : R) : Ω₂) = algebraMap Ω₁ Ω₂ a) ∧ P.g = P₁.g ∧ IsGrpPullback P.A P₁.A (spMap h) ψ ∧ LBIso P.L (P₁.L.pull ψ) ∧ Nonempty (Out.Level P K (unitOn ((Units.map (algebraMap o₂ R : o₂ →* R)) ze))) := by
  first | exact @GlobalTheory.LevelSpread.level_spreads | exact GlobalTheory.LevelSpread.level_spreads | (intros; apply GlobalTheory.LevelSpread.level_spreads <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIffValEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.ScaleAtModel

open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt GlobalTheory.ZH.TestVal GlobalTheory.ThetaDvr.Scale

theorem isUnit_iff_val_eq {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) {s y : FractionRing V} (hs : s ≠ 0) {w : V}
    (hw : y = s * algebraMap V (FractionRing V) w)
    (hle : v (algebraMap (FractionRing V) F s) ≤ v (algebraMap (FractionRing V) F y)) :
    IsUnit w ↔ v (algebraMap (FractionRing V) F y) = v (algebraMap (FractionRing V) F s) := by
  have inj := IsFractionRing.injective V (FractionRing V)
  constructor
  · intro hu
    by_contra hne
    have hlt := lt_of_le_of_ne hle (fun h => hne h.symm)
    obtain ⟨w'', hw'', hm⟩ := GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hs hle
    have e : w'' = w := by
      apply inj
      have : s * (algebraMap V (FractionRing V) w'' - algebraMap V (FractionRing V) w) = 0 := by
        linear_combination hw - hw''
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hs)
    exact (IsLocalRing.mem_maximalIdeal _).1 (e ▸ hm hlt) hu
  · intro heq
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero, AddValuation.map_zero] at heq
      exact hs ((map_eq_zero_iff _ (algebraMap (FractionRing V) F).injective).1 ((AddValuation.top_iff v).1 heq.symm))
    obtain ⟨w', hw', -⟩ := GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hy0 heq.le
    have e : s * (algebraMap V (FractionRing V) (w * w') - 1) = 0 := by
      rw [map_mul]; linear_combination -hw' - (algebraMap V (FractionRing V) w') * hw
    have e' : w * w' = 1 := inj (by rw [map_one]; exact sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_left hs))
    exact IsUnit.of_mul_eq_one w' e'


open MonObj in
attribute [local instance] gtGroup in
theorem scale_at_model : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → IsUnit ((S.r * S.N : ℕ) : V) →
    ∀ (σ : S.R →+* FractionRing V) (A : PolAV (Sp (FractionRing V))) (φ : A.A.left ⟶ ρ.P.A.left),
    IsGrpPullback A.A ρ.P.A (spMap σ) φ → LBIso A.L (ρ.P.L.pull φ) →
    ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (D : DegData V (maximalIdeal V)) (U : Unif (maximalIdeal V) D A G), (∃ a, σ ⟨S.th a, S.th_mem a⟩ ≠ 0) →
    ∃ (s : FractionRing V) (v : S.Gam → V), s ≠ 0 ∧
      (∀ a, σ ⟨S.th a, S.th_mem a⟩ = s * algebraMap V (FractionRing V) (v a)) ∧
      (∀ a, ∃ (pk : QkPt D.toPre (AlgebraicClosure (FractionRing V)) (S.r * S.N)) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A),
        QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) (S.r * S.N) pk x ∧
        x.left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp σ) ≫ (ρ.pt a).left) ∧
      (∀ a (pk : QkPt D.toPre (AlgebraicClosure (FractionRing V)) (S.r * S.N)) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A),
        QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) (S.r * S.N) pk x →
        x.left ≫ φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp σ) ≫ (ρ.pt a).left →
        (IsUnit (v a) → ∃ z, pk.y = (S.r * S.N) • z) ∧
        ((∃ z, pk.y = (S.r * S.N) • z) → ∃ b : S.Gam, ρ.n • b = 0 ∧ IsUnit (v (a + b)))) := by
  intro o' Ω _ _ _ S ρ V _ _ _ _ hc hu σ A φ cart lb G _ _ semi D U hne
  obtain ⟨hL, hL₂, -⟩ := GlobalTheory.allSixLaws
  obtain ⟨H, h₁, h₂, h₃, h₄⟩ := GlobalTheory.ZH.TestVal.hyps hL hL₂
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨v, hv, -⟩ := GlobalTheory.ValClosure.exists_valuation_closure V ϖ hϖ
  have hm := odd_level' ρ
  have hA : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hB := D.tau_bimult
  choose Q hQ using QForm.exists_QVal hϖ D
  obtain ⟨x, hx, xadd, xinj, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points σ cart
  obtain ⟨rig, e, hrig, he, hsec⟩ := GlobalTheory.ThetaDvr.frames σ cart lb x hx
  obtain ⟨t, ht⟩ := hsec 1 ρ.th₁
  obtain ⟨w₀, hw₀⟩ := EvalZero.exists_normW U.toUnifPre rig hrig
  obtain ⟨th, ϑ, hE, hP, hgen⟩ := exists_prim_generator H h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ _ v hv A G
    semi U w₀ hw₀.1
  have key := val_theta H h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ _ v hv A G semi U w₀ rig hw₀ th ϑ hE hP
    _ hm hu
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq H V _ hA D A G semi U
    (AlgebraicClosure (FractionRing V)) _ hm.pos
  obtain ⟨r, hr⟩ := hgen t
  obtain ⟨sc, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (FractionRing V)))).inv).2 r
  set F := AlgebraicClosure (FractionRing V) with hF
  set iK := algebraMap (FractionRing V) F with hiK
  set y₀ : S.R →+* F := iK.comp σ with hy₀
  have tv : ∀ a z J, Good A.L z J → cst (R := V) F z sc *
      @id ((TF (R := V) F).left.presheaf.stalk z) (sA th (ptSecT A.A (x a)).left z J) =
      cst (R := V) F z (y₀ ⟨S.th a, S.th_mem a⟩) * @id ((TF (R := V) F).left.presheaf.stalk z)
        (val (powFrame A.A A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ =>
    (ThetaCompare.sval_smul hr (x a) hJ).symm.trans (ht a _ (by
      have b := ρ.th_val a
      rw [← powFrame_one' (ρ.pt a) (ρ.fr a)] at b
      exact b) z J hJ)
  have uniq : ∀ a (x' : TFK (R := V) F ⟶ A.A), x'.left ≫ φ = spMap (iK.comp σ) ≫ (ρ.pt a).left → x' = x a :=
    fun a x' h' => by
      apply Over.OverMorphism.ext
      exact cart.1.hom_ext (h'.trans (hx a).symm) ((Over.w x').trans (Over.w (x a)).symm)
  have h0 : sc ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := hne
    apply ha
    obtain ⟨z⟩ := CoefBasic.exists_pt (R := V) (F := F)
    obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TFK (R := V) F).left) A.isLB z
    have := tv a z J hJ
    rw [h0, CoefBasic.cst_eq, CoefBasic.cst_eq, map_zero, zero_mul] at this
    have z0 : y₀ ⟨S.th a, S.th_mem a⟩ = 0 :=
      CoefBasic.cstH_inj (R := V) z (((Units.mul_left_eq_zero _).1 this.symm).trans (map_zero _).symm)
    exact (map_eq_zero_iff _ iK.injective).1 z0
  have tv' : ∀ a z J, Good A.L z J → sA th (ptSecT A.A (x a)).left z J =
      @id ((TFK (R := V) F).left.presheaf.stalk z)
        (cst (R := V) F z (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩)) *
        (val (powFrame A.A A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ => by
    have b := congrArg (CoefBasic.cstH (R := V) z sc⁻¹ * ·) (tv a z J hJ)
    simp only [CoefBasic.cst_eq, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, _root_.one_mul] at b
    rw [CoefBasic.cst_eq]
    exact b
  have hvs : v sc ≠ ⊤ := v.ne_top_iff.2 h0
  have split : ∀ a, v (y₀ ⟨S.th a, S.th_mem a⟩) = v sc + v (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩) := fun a => by
    rw [← v.map_mul, ← _root_.mul_assoc, mul_inv_cancel₀ h0, _root_.one_mul]
  have nz : ∀ a, v (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩) = 0 ↔ v (y₀ ⟨S.th a, S.th_mem a⟩) = v sc := fun a => by
    rw [split a]
    constructor
    · intro h; rw [h, add_zero]
    · intro h
      obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hvs
      rw [← hs] at h
      have e1 := congrArg (((-s : ℚ) : WithTop ℚ) + ·) h
      simp only [← add_assoc, ← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero, zero_add] at e1
      exact e1

  have low : ∀ b, v sc ≤ v (y₀ ⟨S.th b, S.th_mem b⟩) := fun b => by
    obtain ⟨q, hq⟩ := f₂ (x b) (he b).1
    have hk := (key q _ ((f₁ _ _).2 hq.symm)).1 _ _ (he b) (tv' b)
    have lo : (0 : WithTop ℚ) ≤ v (sc⁻¹ * y₀ ⟨S.th b, S.th_mem b⟩) := by
      have := hk.1 0 fun χ => by
        by_cases c : (S.r * S.N) • χ + q.y = 0
        · rw [c, QForm.Q_zero hϖ D hQ]; simp
        · exact div_nonneg (Int.cast_nonneg (zero_le_one.trans (QForm.Q_pos hϖ D hQ c))) (Nat.cast_nonneg _)
      simpa using this
    rw [split b]; exact le_add_of_nonneg_right lo
  have dvd : ∀ b (q : QkPt D.toPre F (S.r * S.N)), QkToAkU U.toUnifPre F (S.r * S.N) q (x b) →
      v (y₀ ⟨S.th b, S.th_mem b⟩) = v sc → ∃ z, q.y = (S.r * S.N) • z := fun b q hq h =>
    ((key q _ hq).1 _ _ (he b) (tv' b)).2 ((nz b).2 h)

  obtain ⟨j, hj, hrj⟩ := ρ.r_eq
  have hnd : ρ.n ∣ S.r * S.N := by
    rw [hrj, ρ.N_eq]
    exact Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
  have coset : ∀ a (q : QkPt D.toPre F (S.r * S.N)), QkToAkU U.toUnifPre F (S.r * S.N) q (x a) →
      (∃ z, q.y = (S.r * S.N) • z) → ∃ a', ρ.n • (a' - a) = 0 ∧ v (y₀ ⟨S.th a', S.th_mem a'⟩) = v sc := by
    rintro a q hq₁ ⟨z, hz'⟩
    let q₀ : QkPt D.toPre F (S.r * S.N) := qkMk hB 0 (q.g + iota hB _ (-z)) (by
      rw [smul_add, qk_nsmul hB, ← map_nsmul, ← map_add (f := _), smul_neg, ← hz', add_neg_cancel])
    have e₀ : f q = f q₀ := (f₃ _ _).2 ((equiv_iff hB _ _).2 ⟨-z, by
      rw [smul_neg, ← hz', add_neg_cancel]; rfl, rfl⟩)
    obtain ⟨q', x', hy', hx', hpow, hval⟩ :=
      (key q₀ (x a) ((f₁ _ _).2 (((f₁ _ _).1 hq₁).trans e₀))).2 ρ.n ρ.n_prime.two_le hnd (by simp [q₀])
    obtain ⟨a', rfl⟩ := xonto x' (hx' w₀ hw₀.1).1
    have := A.isAb.comm
    let X : Multiplicative S.Gam →* (TFK (R := V) F ⟶ A.A) :=
      MonoidHom.mk' (fun a => x a.toAdd) fun a b => xadd _ _
    refine ⟨a', xinj ?_, (nz a').1 (hval _ _ (he a') (tv' a'))⟩
    have b : X ((Multiplicative.ofAdd a' * (Multiplicative.ofAdd a)⁻¹) ^ ρ.n) = X 1 := by
      rw [map_pow, map_mul, map_inv, map_one]; exact hpow
    rw [sub_eq_add_neg]
    exact b

  have q0 : QkToAkU U.toUnifPre F (S.r * S.N)
      (qkMk hB 0 0 (by rw [smul_zero, map_zero]) : QkPt D.toPre F (S.r * S.N)) (f (qkMk hB 0 0 (by rw [smul_zero, map_zero]))) :=
    (f₁ _ _).2 rfl
  obtain ⟨a₁, ha₁⟩ := xonto _ (q0 w₀ hw₀.1).1
  obtain ⟨a₀, -, ha₀⟩ := coset a₁ _ (ha₁ ▸ q0) ⟨0, by simp⟩
  set s := σ ⟨S.th a₀, S.th_mem a₀⟩ with hs_def
  have hs0 : s ≠ 0 := by
    intro h
    have : v (y₀ ⟨S.th a₀, S.th_mem a₀⟩) = ⊤ := by
      show v (iK s) = ⊤
      rw [h, map_zero, AddValuation.map_zero]
    exact hvs (ha₀.symm.trans this)
  have hle : ∀ b, v (iK s) ≤ v (iK (σ ⟨S.th b, S.th_mem b⟩)) := fun b => by
    have h1 : v (iK s) = v sc := ha₀
    rw [h1]; exact low b
  choose w hw using fun b => (GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hs0 (hle b))
  have hw' : ∀ b, σ ⟨S.th b, S.th_mem b⟩ = s * algebraMap V (FractionRing V) (w b) := fun b => by
    rw [(hw b).1, mul_comm]
  have unit_iff : ∀ b, IsUnit (w b) ↔ v (y₀ ⟨S.th b, S.th_mem b⟩) = v sc := fun b => by
    rw [← ha₀]
    exact isUnit_iff_val_eq hϖ hv hs0 (hw' b) (hle b)
  refine ⟨s, w, hs0, hw', fun a => ?_, fun a pk x' hpk hx' => ?_⟩
  · obtain ⟨q, hq⟩ := f₂ (x a) (he a).1
    exact ⟨q, x a, (f₁ _ _).2 hq.symm, hx a⟩
  · obtain rfl := uniq a x' hx'
    refine ⟨fun hu' => dvd a pk hpk ((unit_iff a).1 hu'), fun hd => ?_⟩
    obtain ⟨a', hn, hv'⟩ := coset a pk hpk hd
    refine ⟨a' - a, hn, ?_⟩
    rw [add_sub_cancel]
    exact (unit_iff a').2 hv'

end GlobalTheory.Poinc.ScaleAtModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMvPolynomialLiftConductorCoeffs
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMvPolynomialLiftConductorCoeffs
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_mvPolynomial_lift_of_mem_conductor :
    ∀ (R R' ν : Type) [CommRing R] [CommRing R'] [Algebra R R'] (c : Ideal R), (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ G ∈ (c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R'), ∃ H : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) H = 0 ∧ MvPolynomial.map (algebraMap R R') H = G := by
  intro R R' ν _ _ _ c hc G hG
  have key : ∀ z ∈ c.map (algebraMap R R'), ∃ y ∈ c, algebraMap R R' y = z := by
    intro z hz
    refine Submodule.span_induction (p := fun z _ => ∃ y ∈ c, algebraMap R R' y = z)
      ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · exact ⟨0, c.zero_mem, map_zero _⟩
    · rintro _ _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, c.add_mem ha hb, map_add _ _ _⟩
    · rintro r _ _ ⟨a, ha, rfl⟩
      obtain ⟨y, hy, h⟩ := hc a ha r
      exact ⟨y, hy, by rw [h, smul_eq_mul, mul_comm]⟩
  rw [MvPolynomial.mem_map_C_iff] at hG
  choose y hy hyG using fun m => key _ (hG m)
  refine ⟨∑ m ∈ G.support, MvPolynomial.monomial m (y m), ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [MvPolynomial.map_monomial, Ideal.Quotient.eq_zero_iff_mem.mpr (hy m), map_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      conv_rhs => rw [G.as_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [MvPolynomial.map_monomial, hyG]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMvPolynomialLiftConductorCoeffsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mvPolynomial_lift_conductor_coeffs : ∀ (R R' ν : Type) [CommRing R] [CommRing R'] [Algebra R R'] (c : Ideal R), (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ G ∈ (c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R'), ∃ H : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) H = 0 ∧ MvPolynomial.map (algebraMap R R') H = G := by
  first | exact @GlobalTheory.exists_mvPolynomial_lift_of_mem_conductor | exact GlobalTheory.exists_mvPolynomial_lift_of_mem_conductor | (intros; apply GlobalTheory.exists_mvPolynomial_lift_of_mem_conductor <;> assumption)
end
end
