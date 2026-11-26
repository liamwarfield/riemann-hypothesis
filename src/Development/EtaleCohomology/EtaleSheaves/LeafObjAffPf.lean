module

public import Development.EtaleCohomology.EtaleSheaves.LeafTensQIsoPf
public import Development.EtaleCohomology.EtaleSheaves.EtaleEmbedding.EmbedOfLines
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.ResMapNsmulHomotopy

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafObjAffPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct
open LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut LateralTheory.E.LeafDescendFPPf LateralTheory.E.LeafObjFPPf

namespace LateralTheory.E.LeafObjAffPf

theorem desc_spec (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] (A : Type) [CommRing A]
    [Algebra Ω A] [Algebra.FinitePresentation Ω A] :
    Desc k (Spec.map (CommRingCat.ofHom (algebraMap Ω A))) := by
  let P := Algebra.Presentation.ofFinitePresentation Ω A
  let R : Subalgebra k Ω := Algebra.adjoin k P.coeffs
  have : P.HasCoeffs R := ⟨fun x hx => ⟨⟨x, Algebra.subset_adjoin hx⟩, rfl⟩⟩
  let B := P.ModelOfHasCoeffs R
  let e : Ω ⊗[R] B ≃ₐ[Ω] A := P.tensorModelOfHasCoeffsEquiv R
  have hR : R.FG := ⟨P.finite_coeffs.toFinset, by simp [R]⟩
  let gB : CommRingCat.of B ⟶ CommRingCat.of A :=
    CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e.toRingEquiv.toCommRingCatIso.hom
  have hpo : IsPushout (CommRingCat.ofHom (algebraMap R Ω)) (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (algebraMap Ω A)) gB := by
    refine (CommRingCat.isPushout_tensorProduct R Ω B).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      e.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
    · simp
    · simp
    · ext x
      change e (x ⊗ₜ 1) = algebraMap Ω A x
      simpa [Algebra.TensorProduct.algebraMap_apply] using e.commutes x
    · simp [gB]
  refine ⟨R, hR, Spec (CommRingCat.of B), Spec.map (CommRingCat.ofHom (algebraMap R B)), _, ?_,
    (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip⟩
  refine ⟨?_, inferInstance, inferInstance⟩
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

theorem desc_of_iso (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}}
    (i : X ≅ Y) (g : Y ⟶ Sp Ω) (h : Desc k g) : Desc k (i.hom ≫ g) := by
  obtain ⟨R, hR, D, q, v, hq, hpb⟩ := h
  exact ⟨R, hR, D, q, i.hom ≫ v, hq,
    hpb.of_iso i.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)⟩

theorem LeafObjAff_of : LeafObjAff := by
  intro k _ Ω _ _ X f hX hf
  obtain ⟨h1, h2, h3⟩ := hf
  let g : Spec Γ(X, ⊤) ⟶ Spec (CommRingCat.of Ω) := X.isoSpec.inv ≫ f
  let φ := Spec.preimage g
  letI : Algebra Ω Γ(X, ⊤) := φ.hom.toAlgebra
  have hg : LocallyOfFinitePresentation g := inferInstance
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap Ω Γ(X, ⊤))) = g := Spec.map_preimage g
  have hfp : Algebra.FinitePresentation Ω Γ(X, ⊤) := by
    rw [← Spec.map_preimage g, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at hg
    exact hg
  have := desc_spec k (Ω := Ω) Γ(X, ⊤)
  rw [hφ] at this
  have hf' : f = X.isoSpec.hom ≫ g := by simp [g]
  rw [hf']
  exact desc_of_iso k X.isoSpec g this

end LateralTheory.E.LeafObjAffPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafNSysGlueOf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.NeighbourhoodSystemGluing
open LateralTheory.E.LeafSHSysPf

theorem cocone_u_eq {R : CommRingCat.{0}} {J : Type} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (u : ∀ j, R ⟶ D.obj j) (hu : ∀ {j j' : J} (g : j ⟶ j'), u j ≫ D.map g = u j')
    (c : Cocone D) (j j' : J) : u j ≫ c.ι.app j = u j' ≫ c.ι.app j' := by
  have h1 := c.w (IsFiltered.leftToMax j j')
  have h2 := c.w (IsFiltered.rightToMax j j')
  rw [← h1, ← h2, ← Category.assoc, ← Category.assoc, hu, hu]

theorem LeafNSysGlue_of (hR : LeafRingSys) : LeafNSysGlue := by
  intro _ B U x
  let 𝒰 := U.left.affineOpenCover
  let R := 𝒰.X (𝒰.idx x)
  let ι : Spec R ⟶ U.left := 𝒰.f (𝒰.idx x)
  obtain ⟨y, hy⟩ := 𝒰.covers x
  obtain ⟨J, _, _, D, u, hu, het, hq, c, ⟨hc⟩, hcof⟩ := hR R y
  have hE : ∀ j, Etale (Spec.map (u j) ≫ ι ≫ U.hom) := fun j => by
    have : Etale (Spec.map (u j)) := HasRingHomProperty.Spec_iff.2 (het j)
    have : Etale U.hom := U.prop
    infer_instance
  let V : J → B.Etale := fun j => MorphismProperty.Over.mk ⊤ (Spec.map (u j) ≫ ι ≫ U.hom) (hE j)
  let a : ∀ j, V j ⟶ U := fun j => MorphismProperty.Over.homMk (Spec.map (u j) ≫ ι) (by show (Spec.map (u j) ≫ ι) ≫ U.hom = Spec.map (u j) ≫ ι ≫ U.hom; rw [Category.assoc]) trivial
  let tr : ∀ {j j' : J} (_ : j ⟶ j'), V j' ⟶ V j := fun {j j'} g =>
    MorphismProperty.Over.homMk (Spec.map (D.map g))
      (by show Spec.map (D.map g) ≫ Spec.map (u j) ≫ ι ≫ U.hom = Spec.map (u j') ≫ ι ≫ U.hom; rw [← Spec.map_comp_assoc, hu]) trivial
  let j0 : J := (IsFiltered.nonempty (C := J)).some
  exact ⟨{
    J := J
    D := D
    V := V
    a := a
    e := fun j => Iso.refl _
    tr := tr
    tr_a := fun g => by
      apply MorphismProperty.Over.Hom.ext
      show Spec.map (D.map g) ≫ Spec.map _ ≫ ι = Spec.map _ ≫ ι
      rw [← Spec.map_comp_assoc, hu]
    tr_spec := fun g => by
      show 𝟙 _ ≫ Spec.map (D.map g) ≫ 𝟙 _ = _
      simp
    hx := fun j => by
      obtain ⟨q, hq⟩ := hq j
      refine ⟨q, ?_⟩
      rw [← hy]
      show ι (Spec.map (u j) q) = ι y
      congr 1
    c := c
    hc := hc
    cof := hcof
    t := Spec.map (c.ι.app j0) ≫ Spec.map (u j0) ≫ ι
    ht := fun j => by
      show _ = Spec.map (c.ι.app j) ≫ 𝟙 _ ≫ Spec.map (u j) ≫ ι
      rw [Category.id_comp, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, cocone_u_eq D u hu c j0 j] }⟩

end LateralTheory.E.NeighbourhoodSystemGluing
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LineChartPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.LineChartPf

attribute [local instance] MvPolynomial.gradedAlgebra

def eU : {j : Fin 2 // j ≠ 0} ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := ⟨1, by decide⟩
  left_inv := by
    rintro ⟨j, hj⟩
    apply Subtype.ext
    fin_cases j
    · exact absurd rfl hj
    · rfl
  right_inv := by intro; rfl

def awayEquiv : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)
    (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ) ≃+* Polynomial ℤ :=
  (GlobalTheory.ProjSpace.polyEquivAway ℤ 1 0).symm.trans
    ((MvPolynomial.renameEquiv ℤ eU).trans (MvPolynomial.uniqueAlgEquiv ℤ PUnit.{1})).toRingEquiv

def projectiveLineAffineChartOverIntegers : Spec (CommRingCat.of (Polynomial ℤ)) ⟶ P1 :=
  Spec.map awayEquiv.toCommRingCatIso.hom ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X 0)
      (MvPolynomial.isHomogeneous_X ℤ 0) one_pos

instance : IsOpenImmersion projectiveLineAffineChartOverIntegers := by
  unfold projectiveLineAffineChartOverIntegers
  haveI : IsIso (Spec.map awayEquiv.toCommRingCatIso.hom) := inferInstance
  haveI : IsOpenImmersion (Spec.map awayEquiv.toCommRingCatIso.hom) := IsOpenImmersion.of_isIso _
  exact IsOpenImmersion.comp (Spec.map awayEquiv.toCommRingCatIso.hom) (Proj.awayι _ _ _ _)

def zIso : Spec (CommRingCat.of ℤ) ≅ ⊤_ Scheme := specZIsTerminal.uniqueUpToIso terminalIsTerminal

theorem tensor_C (R : Type) [CommRing R] (a : R) :
    (polyEquivTensor ℤ R).symm (a ⊗ₜ[ℤ] (1 : Polynomial ℤ)) = Polynomial.C a := by
  rw [polyEquivTensor_symm_apply_tmul, ← Polynomial.C_1, Polynomial.sum_C_index (by simp)]
  simp

theorem LineChart_of : LateralTheory.E.EmbedPf.LineChart := by
  intro L S l hl R _ j0 hj0
  obtain ⟨_, f, hsq⟩ := hl
  let m := pullback.map (Spec.map (CommRingCat.ofHom (algebraMap ℤ R)))
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Polynomial ℤ))))
    (terminal.from S) (terminal.from P1) j0 projectiveLineAffineChartOverIntegers zIso.hom
    (terminal.hom_ext _ _) (terminal.hom_ext _ _)
  let E := (polyEquivTensor ℤ R).toRingEquiv.toCommRingCatIso
  refine ⟨Spec.map E.inv ≫ (pullbackSpecIso ℤ R (Polynomial ℤ)).inv ≫ m ≫ hsq.flip.isoPullback.inv,
    inferInstance, ?_⟩
  simp only [Category.assoc, IsPullback.isoPullback_inv_fst, m, pullback.lift_fst,
    pullbackSpecIso_inv_fst_assoc]
  have key : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := R) (B := Polynomial ℤ)) ≫ E.inv =
      CommRingCat.ofHom Polynomial.C := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact tensor_C R a
  rw [← Spec.map_comp_assoc, key]

end LateralTheory.E.LineChartPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.ChartBCNnmPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.GeometricData LateralTheory.E.ProjectiveLineCharts₂

namespace LateralTheory.E.ChartBC_nnmPf

theorem res_bijective {X : Scheme.{0}} {U V : X.Opens} (h : U ≤ V) (h' : V ≤ U) :
    Function.Bijective (X.presheaf.map (homOfLE h).op) := by
  obtain rfl := le_antisymm h h'
  have : (homOfLE h) = 𝟙 U := rfl
  rw [this, op_id, X.presheaf.map_id]
  exact Function.bijective_id

theorem pushout_gen {Z X Y P : CommRingCat.{0}} {f : Z ⟶ X} {g : Z ⟶ Y} {i : X ⟶ P} {j : Y ⟶ P}
    (h : IsPushout f g i j) (R : Subring P) (hi : ∀ x, i x ∈ R) (hj : ∀ y, j y ∈ R) (p : P) : p ∈ R := by
  let i' : X ⟶ CommRingCat.of R := CommRingCat.ofHom (i.hom.codRestrict R hi)
  let j' : Y ⟶ CommRingCat.of R := CommRingCat.ofHom (j.hom.codRestrict R hj)
  have w' : f ≫ i' = g ≫ j' := by
    ext z
    have := congrArg (fun φ => φ.hom z) h.w
    simpa [i', j'] using this
  let σ := h.desc i' j' w'
  have hσ : σ ≫ CommRingCat.ofHom R.subtype = 𝟙 P := by
    apply h.hom_ext
    · rw [h.inl_desc_assoc]; ext; rfl
    · rw [h.inr_desc_assoc]; ext; rfl
  have := congrArg (fun φ => φ.hom p) hσ
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_id,
    RingHom.id_apply] at this
  rw [← this]; exact (σ.hom p).2

theorem restrict_appTop_eq {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) :
    Y.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).le).op ≫ (f ∣_ U).appTop =
      f.app U ≫ X.presheaf.map (homOfLE (Scheme.Opens.ι_image_top (f ⁻¹ᵁ U)).le).op := by
  rw [morphismRestrict_appTop]
  have e := f.naturality (homOfLE (Scheme.Opens.ι_image_top U).le).op
  calc _ = (Y.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).le).op ≫ f.app (U.ι ''ᵁ ⊤)) ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op := (Category.assoc _ _ _).symm
    _ = _ := by rw [e, Category.assoc, ← Functor.map_comp]; rfl

theorem snd_eq {A : Type} [CommRing A] {L : Scheme.{0}} (l : L ⟶ Spec (CommRingCat.of A)) (V : L.Opens) :
    (V.ι ≫ l).appTop = l.appLE ⊤ V le_top ≫ L.presheaf.map (homOfLE (Scheme.Opens.ι_image_top V).le).op := by
  unfold Scheme.Hom.appLE
  rw [Category.assoc, ← Functor.map_comp]
  rfl

theorem ChartBC_of : ChartBC := by
  intro A _ L l f hf W x hW hsx
  have hpb := IsPullback.paste_vert (isPullback_morphismRestrict f W) hf
  have : IsAffine W.toScheme := hW
  have hA : IsAffineOpen (f ⁻¹ᵁ W) := IsAffine.of_isPullback hpb
  refine ⟨hA, ?_⟩
  have : IsAffine (f ⁻¹ᵁ W).toScheme := hA
  have hpo := isPushout_appTop_of_isPullback hpb
  let ψ := L.presheaf.map (homOfLE (Scheme.Opens.ι_image_top (f ⁻¹ᵁ W)).le).op
  have hψ := res_bijective (X := L) (Scheme.Opens.ι_image_top (f ⁻¹ᵁ W)).le
    (Scheme.Opens.ι_image_top (f ⁻¹ᵁ W)).ge
  let R : Subring Γ((f ⁻¹ᵁ W).toScheme, ⊤) :=
    (Polynomial.eval₂RingHom (rA l (f ⁻¹ᵁ W)) (f.app W x)).range.map ψ.hom
  intro t
  have ht : ψ t ∈ R := pushout_gen hpo R ?_ ?_ (ψ t)
  · obtain ⟨r, ⟨q, rfl⟩, hr⟩ := Subring.mem_map.mp ht
    exact ⟨q, hψ.1 hr⟩
  · intro w
    obtain ⟨w0, rfl⟩ := (res_bijective (X := P1) (Scheme.Opens.ι_image_top W).le
      (Scheme.Opens.ι_image_top W).ge).2 w
    have h1 : (f ∣_ W).appTop (P1.presheaf.map (homOfLE (Scheme.Opens.ι_image_top W).le).op w0) =
        ψ (f.app W w0) := congrArg (fun φ => φ.hom w0) (restrict_appTop_eq f W)
    erw [h1]
    obtain ⟨q, rfl⟩ := hsx w0
    refine Subring.mem_map.mpr ⟨_, ⟨q.map (Int.castRingHom A), rfl⟩, ?_⟩
    congr 1
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map, Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂]
    congr 1; exact RingHom.ext_int _ _
  · intro a
    refine Subring.mem_map.mpr ⟨_, ⟨Polynomial.C ((Scheme.ΓSpecIso (CommRingCat.of A)).hom a), rfl⟩, ?_⟩
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, snd_eq]
    simp only [rA, RingHom.comp_apply]
    erw [Iso.hom_inv_id_apply]
    rfl

end LateralTheory.E.ChartBC_nnmPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafZModInjFlatPf
open TensorProduct

namespace LateralTheory.E.LeafZModInjFlatPf

universe v

theorem flat_of_injective_of_ann {R : Type v} [CommRing R] [IsPrincipalIdealRing R]
    (hP : ∀ a : R, ∃ b : R, b * a = 0 ∧ ∀ r : R, r * b = 0 → ∃ s : R, r = s * a)
    (M : Type v) [AddCommGroup M] [Module R M] (hM : Module.Injective R M) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I _
  obtain ⟨a, rfl⟩ : ∃ a : R, I = Ideal.span {a} :=
    ⟨_, (Ideal.span_singleton_generator I).symm⟩
  have ha : a ∈ Ideal.span ({a} : Set R) := Ideal.mem_span_singleton_self a
  have key : ∀ x : Ideal.span ({a} : Set R) ⊗[R] M, ∃ m : M, x = (⟨a, ha⟩ : Ideal.span ({a} : Set R)) ⊗ₜ m := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul i n =>
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 i.2
      refine ⟨s • n, ?_⟩
      rw [← smul_tmul]
      congr 1
      ext
      simp [smul_eq_mul, hs]
    | add x y hx hy =>
      obtain ⟨m1, rfl⟩ := hx
      obtain ⟨m2, rfl⟩ := hy
      exact ⟨m1 + m2, (tmul_add _ _ _).symm⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨m, rfl⟩ := key x
  simp at hx
  obtain ⟨b, hba, hb⟩ := hP a
  have well : ∀ r r' : R, r * b = r' * b → r • m = r' • m := by
    intro r r' h
    obtain ⟨s, hs⟩ := hb (r - r') (by rw [sub_mul, h, sub_self])
    rw [← sub_eq_zero, ← sub_smul, hs, mul_smul, hx, smul_zero]
  let f : Ideal.span ({b} : Set R) → R := fun x => Classical.choose (Ideal.mem_span_singleton'.1 x.2)
  have hf : ∀ x, f x * b = x := fun x => Classical.choose_spec (Ideal.mem_span_singleton'.1 x.2)
  let g : Ideal.span ({b} : Set R) →ₗ[R] M :=
    { toFun := fun x => f x • m
      map_add' := fun x y => by
        rw [← add_smul]; apply well; rw [hf, add_mul, hf, hf]; rfl
      map_smul' := fun c x => by
        rw [RingHom.id_apply, smul_smul]; apply well; rw [hf, mul_assoc, hf]; rfl }
  obtain ⟨g', hg'⟩ := Module.Baer.of_injective hM _ g
  have hm : m = b • g' 1 := by
    rw [← map_smul, smul_eq_mul, mul_one, hg' b (Ideal.mem_span_singleton_self b)]
    show m = f _ • m
    conv_lhs => rw [← one_smul R m]
    apply well; rw [hf, one_mul]
  rw [hm, ← smul_tmul]
  have : b • (⟨a, ha⟩ : Ideal.span ({a} : Set R)) = 0 := by ext; simp [smul_eq_mul, hba]
  rw [this, zero_tmul]

theorem zmod_ann (q : ℕ) [NeZero q] :
    ∀ a : ZMod q, ∃ b : ZMod q, b * a = 0 ∧ ∀ r : ZMod q, r * b = 0 → ∃ s, r = s * a := by
  intro a
  set d := Nat.gcd a.val q with hd
  have hdq : d ∣ q := Nat.gcd_dvd_right _ _
  have hda : d ∣ a.val := Nat.gcd_dvd_left _ _
  have hq0 : q ≠ 0 := NeZero.ne q
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hq0)
  refine ⟨((q / d : ℕ) : ZMod q), ?_, ?_⟩
  · conv_lhs => rw [← ZMod.natCast_zmod_val a]
    rw [← Nat.cast_mul]
    obtain ⟨t, ht⟩ := hda
    have : q / d * a.val = q * t := by
      rw [ht, ← mul_assoc, Nat.div_mul_cancel hdq]
    rw [this, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  · intro r hr
    rw [← ZMod.natCast_zmod_val r, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hr
    have hqd : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hdq) hd0
    have h2 : d * (q / d) ∣ r.val * (q / d) := by rwa [Nat.mul_div_cancel' hdq]
    obtain ⟨t, ht⟩ := Nat.dvd_of_mul_dvd_mul_right hqd h2
    refine ⟨a⁻¹ * t, ?_⟩
    rw [← ZMod.natCast_zmod_val r, ht, Nat.cast_mul, hd, ← ZMod.mul_inv_eq_gcd]
    ring

instance pir_zmod (q : ℕ) : IsPrincipalIdealRing (ZMod q) :=
  IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod q)) ZMod.intCast_surjective

instance pir_ulift (q : ℕ) : IsPrincipalIdealRing (ULift.{1} (ZMod q)) :=
  IsPrincipalIdealRing.of_surjective (ULift.ringEquiv.{0, 1} (R := ZMod q)).symm
    (ULift.ringEquiv.{0, 1} (R := ZMod q)).symm.surjective

theorem ulift_ann (q : ℕ) [NeZero q] :
    ∀ a : ULift.{1} (ZMod q), ∃ b, b * a = 0 ∧ ∀ r, r * b = 0 → ∃ s, r = s * a := by
  intro a
  obtain ⟨b, hba, hb⟩ := zmod_ann q a.down
  refine ⟨ULift.up b, ULift.ext hba, fun r hr => ?_⟩
  obtain ⟨s, hs⟩ := hb r.down (congrArg ULift.down hr)
  exact ⟨ULift.up s, ULift.ext hs⟩

theorem LeafZModInjFlat_of : LateralTheory.E.LeafTensQIsoPf.LeafZModInjFlat := by
  intro q _ M _ _ hM
  exact flat_of_injective_of_ann (ulift_ann q) M hM

end LateralTheory.E.LeafZModInjFlatPf
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafLiftNonconstOf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.E4

namespace LateralTheory.E.NonconstantLift

theorem dim_affine {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) :
    ringKrullDim Γ(X, U) = topologicalKrullDim (U : Set X) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  symm
  exact IsHomeomorph.topologicalKrullDim_eq _ (hU.isoSpec.hom.homeomorph).isHomeomorph

theorem appTop_eq {k Ω : Type} [Field k] [Field Ω] (f : CommRingCat.of k ⟶ CommRingCat.of Ω)
    (g : Sp Ω ⟶ Sp k) (hg : g = Spec.map f) (e) : g.appLE ⊤ ⊤ e = (Spec.map f).appTop := by
  subst hg
  first
  | exact Scheme.Hom.appLE_eq_app _
  | (simp only [Scheme.Hom.appLE]; exact (CategoryTheory.Category.comp_id _).trans rfl)
  | (simp only [Scheme.Hom.appLE]; erw [CategoryTheory.Functor.map_id, Category.comp_id]; rfl)
  | (simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]; convert Category.comp_id _ using 2; exact (Subsingleton.elim _ _ : (homOfLE e).op = 𝟙 _) ▸ rfl)

theorem stalk_inj {X : Scheme.{0}} [IsIntegral X] {x : X} (hx : x = genericPoint X) {T : CommRingCat}
    [Nontrivial T] (f : X.presheaf.stalk x ⟶ T) : Function.Injective f.hom := by
  subst hx
  exact (f.hom : X.functionField →+* T).injective

theorem key {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p]
    {Ω : Type} [Field Ω] [Algebra k Ω] (φ : Sp Ω ⟶ X)
    (hφ : φ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hη : ∀ z, φ z = genericPoint X) {U : X.Opens} (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    ∃ R : Subalgebra k Ω, R.FG ∧ ringKrullDim R = ringKrullDim Γ(X, U) := by
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hne)
  have hle : (⊤ : (Sp Ω).Opens) ≤ φ ⁻¹ᵁ U := fun z _ => by
    show φ z ∈ U
    rw [hη z]; exact hηU
  have hU' : U ≤ p ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let α : k →+* Γ(X, U) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U hU').hom
  let ψ : Γ(X, U) →+* Ω := (φ.appLE U ⊤ hle ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom
  have hcomp : ψ.comp α = algebraMap k Ω := by
    have h1 : p.appLE ⊤ U hU' ≫ φ.appLE U ⊤ hle =
        (Spec.map (CommRingCat.ofHom (algebraMap k Ω))).appTop := by
      rw [Scheme.Hom.appLE_comp_appLE]
      exact appTop_eq _ _ hφ _
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U hU' ≫ φ.appLE U ⊤ hle ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom (algebraMap k Ω) := by
      rw [reassoc_of% h1, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    ext a
    simpa [α, ψ] using congrArg (fun g => (CommRingCat.Hom.hom g) a) h2
  have hinj : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro s hs
    have hs' : (φ.appLE U ⊤ hle).hom s = 0 := by
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom hs
      simpa [ψ] using this
    obtain ⟨z⟩ : Nonempty (Sp Ω) := inferInstance
    have h3 := Scheme.Hom.germ_stalkMap_apply φ U z (hle trivial) s
    have h4 : (X.presheaf.germ U (φ z) (hle trivial)).hom s = 0 := by
      apply stalk_inj (hη z) (φ.stalkMap z)
      rw [h3, map_zero]
      have := congrArg ((Sp Ω).presheaf.germ ⊤ z (show z ∈ (⊤ : (Sp Ω).Opens) from Set.mem_univ z)).hom hs'
      simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply, map_zero] at this
      erw [TopCat.Presheaf.germ_res_apply] at this
      exact this
    exact germ_injective_of_isIntegral X (φ z) (hle trivial) (by rw [map_zero]; exact h4)
  let _ : Algebra k Γ(X, U) := α.toAlgebra
  let ψa : Γ(X, U) →ₐ[k] Ω := { ψ with commutes' := fun a => DFunLike.congr_fun hcomp a }
  have hft : α.FiniteType := by
    have := Scheme.Hom.finiteType_appLE p (isAffineOpen_top (Sp k)) hU hU'
    exact RingHom.FiniteType.comp this (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)
  have : Algebra.FiniteType k Γ(X, U) := hft
  refine ⟨ψa.range, ?_, ?_⟩
  · rw [← Algebra.map_top]
    exact Subalgebra.FG.map _ Algebra.FiniteType.out
  · exact (ringKrullDim_eq_of_ringEquiv (AlgEquiv.ofInjective ψa hinj).toRingEquiv).symm

theorem dim_contra {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p]
    {Ω : Type} [Field Ω] [Algebra k Ω]
    (hdim : ∀ R : Subalgebra k Ω, R.FG → ringKrullDim R < topologicalKrullDim X) (φ : Sp Ω ⟶ X)
    (hφ : φ ≫ p = Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    (hη : ∀ z, φ z = genericPoint X) : False := by
  have hU : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U := fun x => by
    obtain ⟨W, hW, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    exact ⟨W, hW, hx⟩
  choose V hV hxV using hU
  have hlt : ∀ x, topologicalKrullDim (V x : Set X) < topologicalKrullDim X := fun x => by
    obtain ⟨R, hR, hRd⟩ := key p φ hφ hη (hV x) ⟨x, hxV x⟩
    rw [← dim_affine (hV x), ← hRd]
    exact hdim R hR
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  have hne : t.Nonempty := by
    obtain ⟨x⟩ : Nonempty X := inferInstance
    obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨i, hi⟩
  have hle : topologicalKrullDim X ≤ t.sup' hne (fun i => topologicalKrullDim (V i : Set X)) := by
    apply GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen
    intro x
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨V i, (V i).isOpen, hx, Finset.le_sup' (fun i => topologicalKrullDim (V i : Set X)) hi⟩
  exact lt_irrefl _ (hle.trans_lt ((Finset.sup'_lt_iff hne).2 fun i _ => hlt i))

theorem LeafLiftNonconst_of : LateralTheory.E.QuotientFieldNonconstantLift.LeafLiftNonconst := by
  intro k _ _ X _ p _ Ω _ _ _ hdim C0 c0 e hc0 he hgen y
  by_contra! hcon
  obtain ⟨_, _, _⟩ := id hc0
  have hsnd : ∀ a, e a = (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) p) (pullback.lift c0 e he.symm a) := fun a => by
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
  have hconst : ∀ a, e a = genericPoint X := by
    obtain ⟨b, hb⟩ := hgen
    intro a
    rw [← hb, hsnd a, hsnd b, hcon a, hcon b]
  have : JacobsonSpace C0 := LocallyOfFiniteType.jacobsonSpace c0
  obtain ⟨a0, -, ha0⟩ := nonempty_inter_closedPoints (Z := Set.univ) ⟨y, trivial⟩
    isClosed_univ.isLocallyClosed
  have hcl : IsClosed ({a0} : Set C0) := by simpa [closedPoints] using ha0
  exact dim_contra p hdim (pointOfClosedPoint c0 a0 hcl ≫ e)
    (by rw [Category.assoc, he, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp])
    (fun z => by rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply, hconst])

end LateralTheory.E.NonconstantLift
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafPreTensLocInjPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped DirectSum TensorProduct

namespace LateralTheory.E.LeafPreTensLocInjPf
open LateralTheory.E.LeafTensMonoPf LateralTheory.E.LeafTwPairExistsPf LateralTheory.E.LeafPairExtPf2

section
variable {R : Type} [CommRing R]

theorem sec_sgl_zero (F : Shv R) {s : ℤ} (hs : s ≠ 0) {U : Scheme.{0}} (a : Sec ((sgl F).X s) U) : a = 0 := by
  have hZ : IsZero ((sgl F).X s) := HomologicalComplex.isZero_single_obj_X _ _ _ _ hs
  have h1 : (𝟙 ((sgl F).X s)) = 0 := hZ.eq_of_src _ _
  have h2 : Sec.map (𝟙 ((sgl F).X s)) a = a := rfl
  rw [← h2, h1]
  rfl

theorem tens_zero_left (F : Shv R) {J : Cx R} {s t : ℤ} (hs : s ≠ 0) {U : Scheme.{0}}
    (z : Sec ((sgl F).X s) U ⊗[ULift.{1} R] Sec (J.X t) U) : z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul a b => rw [sec_sgl_zero F hs a, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

abbrev p0 (w : ℤ) : {p : ℤ × ℤ // p.1 + p.2 = w} := ⟨(0, w), by simp⟩

theorem tens_single (F : Shv R) {J : Cx R} {U : Scheme.{0}} {w : ℤ} (x : Tens (sgl F) J U w) :
    x = DirectSum.of _ (p0 w) (x (p0 w)) := by
  classical
  ext p
  by_cases hp : p = p0 w
  · subst hp; simp
  · rw [DirectSum.of_eq_of_ne _ _ _ hp]
    have : p.1.1 ≠ 0 := by
      intro h; apply hp; apply Subtype.ext; ext
      · exact h
      · simp; have := p.2; omega
    exact tens_zero_left F this _

theorem tens_res_of {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (t : Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) :
    Tens.res g w (DirectSum.of _ p t) =
      DirectSum.of _ p (TensorProduct.map ((I.X p.1.1).obj.map g.op).hom ((J.X p.1.2).obj.map g.op).hom t) := by
  classical
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  unfold Tens.res
  rw [DirectSum.lmap_lof]
  rfl

theorem lift_of {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (t : Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) :
    μ.lift U w (DirectSum.of _ p t) = TensorProduct.lift (μ.mul U p.1.1 p.1.2 w p.2) t := by
  classical
  unfold Pair.lift
  exact DirectSum.toModule_lof (ULift.{1} R)
    (M := fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p t

end

section
variable {R : Type} [CommRing R]
theorem tens_res_comp {I J : Cx R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (w : ℤ) (z : Tens I J U w) :
    Tens.res (k ≫ g) w z = Tens.res k w (Tens.res g w z) := by
  classical
  have : (Tens.res (I := I) (J := J) (k ≫ g) w) = (Tens.res k w).comp (Tens.res g w) := by
    apply DirectSum.linearMap_ext; intro p
    apply TensorProduct.ext'; intro a b
    simp [Tens.res]
  exact LinearMap.congr_fun this z
end

theorem LeafPreTensLocInj_of (hS : LeafTw0LocSplit) : LeafPreTensLocInj := by
  intro q _ i T τ hτ U w x hx
  classical
  obtain ⟨S, hS0⟩ := TensorProduct.exists_finset (x (p0 w))
  set a : Fin S.card → Sec ((sgl (tw q 0)).X 0) U := fun k => (S.equivFin.symm k).1.1 with ha
  set b : Fin S.card → Sec ((res _ (tw q i)).X w) U := fun k => (S.equivFin.symm k).1.2 with hb
  have hxp : x (p0 w) = ∑ k, a k ⊗ₜ[ULift.{1} (ZMod q)] b k := by
    rw [hS0, ← Finset.sum_coe_sort S]
    exact (Equiv.sum_comp S.equivFin.symm (fun i : S => i.1.1 ⊗ₜ[ULift.{1} (ZMod q)] i.1.2)).symm
  have hx' : x = DirectSum.of _ (p0 w) (∑ k, a k ⊗ₜ[ULift.{1} (ZMod q)] b k) := by
    rw [← hxp]; exact tens_single _ x
  set y : Tens (res _ (tw q 0)) (res _ (tw q i)) U w :=
    DirectSum.of _ (p0 w) (∑ k, Sec.map ((resAug (tw q 0)).f 0) (a k) ⊗ₜ[ULift.{1} (ZMod q)] b k) with hydef
  have hy : τ.lift U w y = 0 := by
    rw [← hx, hx', hydef, lift_of, lift_of]
    simp [pre]
  refine loc_trans (hτ.2 U w y hy) ?_
  intro V g hg
  refine loc_trans (hS q V S.card (fun k => Sec.res g (a k))) ?_
  rintro W k ⟨e, c, hac, he⟩
  suffices h : Tens.res (k ≫ g) w x = 0 from
    ⟨⊤, GrothendieckTopology.top_mem _ W, fun W' k' _ => by dsimp only; rw [Category.assoc, tens_res_comp, h, map_zero]⟩
  set bb : Sec ((res _ (tw q i)).X w) W := ∑ j, c j • Sec.res (k ≫ g) (b j) with hbb
  have hres : Tens.res (k ≫ g) w x = DirectSum.of _ (p0 w) (e ⊗ₜ[ULift.{1} (ZMod q)] bb) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx', tens_res_of, map_sum]
    congr 1
    rw [hbb, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.map_tmul, ← TensorProduct.smul_tmul]
    congr 1
    show Sec.res (k ≫ g) (a j) = c j • e
    rw [res_comp]; exact hac j
  have hy0 : Tens.res (k ≫ g) w y =
      DirectSum.of _ (p0 w) (Sec.map ((resAug (tw q 0)).f 0) e ⊗ₜ[ULift.{1} (ZMod q)] bb) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hydef, tens_res_of, map_sum]
    congr 1
    rw [hbb, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.map_tmul, ← TensorProduct.smul_tmul]
    congr 1
    show Sec.res (k ≫ g) (Sec.map ((resAug (tw q 0)).f 0) (a j)) = c j • Sec.map ((resAug (tw q 0)).f 0) e
    rw [res_map, res_comp, hac j]
    exact map_smul (((resAug (tw q 0)).f 0).hom.app (op W)).hom (c j) e
  have hg0 : Tens.res (k ≫ g) w y = 0 := by rw [tens_res_comp, hg, map_zero]
  have ht : Sec.map ((resAug (tw q 0)).f 0) e ⊗ₜ[ULift.{1} (ZMod q)] bb = 0 :=
    DirectSum.of_injective (p0 w) (hy0.symm.trans (hg0.trans (map_zero _).symm))
  rw [hres]
  rcases he with he | ⟨r, hr⟩
  · rw [he, TensorProduct.zero_tmul, map_zero]
  · have hbb0 : bb = 0 := by
      have := congrArg (fun z => TensorProduct.lid (ULift.{1} (ZMod q)) _ (TensorProduct.map r LinearMap.id z)) ht
      simpa [hr] using this
    rw [hbb0, TensorProduct.tmul_zero, map_zero]

end LateralTheory.E.LeafPreTensLocInjPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.KummerFields
section -- merged from Development.EtaleCohomology.EtaleSheaves.KummerFields.H0Naturality
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H2CurveOrder.KummerH0Surjection
open CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafKumFieldPf.H0Naturality

set_option backward.isDefEq.respectTransparency false in
theorem resι_nat {F G : Shv ℤ} (φ : F ⟶ G) : resι ℤ F ≫ (resMap ℤ φ).f 0 = φ ≫ resι ℤ G := by
  have h := congrArg (fun f => HomologicalComplex.Hom.f f 0)
    (InjectiveResolution.desc_commutes φ (injectiveResolution G) (injectiveResolution F))
  simp only [HomologicalComplex.comp_f] at h
  simp only [resι, resMap, InjectiveResolution.ι'_f_zero, InjectiveResolution.cochainComplexXIso]
  rw [HomologicalComplex.extendMap_f _ _ (i := 0) (by rfl)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h]
  first | rfl | simp | (congr 1)

theorem free_ext (X : Scheme.{0}) {I : Shv ℤ}
    (f g : (free ℤ).obj ((sch.obj X).obj (op (SimplexCategory.mk 0))) ⟶ I)
    (h : (f.hom.app (op X)).hom (freeGen ℤ _ X (𝟙 X)) = (g.hom.app (op X)).hom (freeGen ℤ _ X (𝟙 X))) : f = g := by
  have key : ∀ (η : (freeP ℤ).obj ((sch.obj X).obj (op (SimplexCategory.mk 0))) ⟶ I.obj) (U : Scheme.{0}) (x : U ⟶ X),
      (η.app (op U)).hom (ModuleCat.freeMk (ULift.up x)) =
        (I.obj.map x.op).hom ((η.app (op X)).hom (ModuleCat.freeMk (ULift.up (𝟙 X)))) := by
    intro η U x
    have := congrArg (fun m => m.hom (ModuleCat.freeMk (ULift.up (𝟙 X)))) (η.naturality x.op)
    refine Eq.trans ?_ this
    rw [ModuleCat.hom_comp]
    erw [LinearMap.comp_apply]
    congr 1
    erw [ModuleCat.free_map_apply]
    congr 2
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ I.2
  refine NatTrans.ext (funext fun U => ModuleCat.free_hom_ext fun ⟨x⟩ => ?_)
  have h1 := key (toSheafify _ _ ≫ f.hom) U.unop x
  have h2 := key (toSheafify _ _ ≫ g.hom) U.unop x
  refine h1.trans (h2.trans ?_).symm
  congr 1
  exact h.symm

theorem coc_ext (X : Scheme.{0}) (G : Shv ℤ) (a b : Cocycle ((chains ℤ).obj (sch.obj X)) (res ℤ G) 0)
    (h : ev a.1 0 0 (by simp) X (𝟙 X) = ev b.1 0 0 (by simp) X (𝟙 X)) : a = b := by
  apply Cocycle.ext
  apply Cochain.ext
  intro p q hpq
  obtain rfl : p = q := by omega
  rcases lt_trichotomy p 0 with hp | rfl | hp
  · apply IsZero.eq_of_tgt
    exact HomologicalComplex.isZero_extend_X _ _ _ (fun i => by show ((i:ℕ):ℤ) ≠ p; omega)
  · have e := free_ext X ((chainsXIso ℤ (sch.obj X) 0).inv ≫ a.1.v 0 0 (by simp))
      ((chainsXIso ℤ (sch.obj X) 0).inv ≫ b.1.v 0 0 (by simp)) h
    have := congrArg ((chainsXIso ℤ (sch.obj X) 0).hom ≫ ·) e
    simpa using this
  · apply IsZero.eq_of_src
    exact HomologicalComplex.isZero_extend_X _ _ _ (fun i => by show -((i:ℕ):ℤ) ≠ p; omega)

theorem ev_post (X : Scheme.{0}) {F G : Shv ℤ} (φ : F ⟶ G) (α : Cocycle ((chains ℤ).obj (sch.obj X)) (res ℤ F) 0) :
    ev (zcomp α (Cocycle.ofHom (resMap ℤ φ)) (add_zero 0)).1 0 0 (by simp) X (𝟙 X) =
      (((resMap ℤ φ).f 0).hom.app (op X)).hom (ev α.1 0 0 (by simp) X (𝟙 X)) := by
  simp only [ev, zcomp, Cocycle.mk, Cochain.comp_zero_cochain_v, Cocycle.ofHom, Cochain.ofHom_v]
  rfl

theorem etale_degree_zero_cohomology_natural_in_sheaf (hA9 : A9) : EtaleDegreeZeroCohomologyNaturallyIsoToSections := by
  intro _
  choose e he using fun F : Shv ℤ => (hA9 ℤ F).2
  refine ⟨e, ?_⟩
  intro F G φ X s
  obtain ⟨α, hα, hαv⟩ := (he F).2 X s
  obtain ⟨β, hβ, hβv⟩ := (he G).2 X (Sec.map φ s)
  rw [← hα, ← hβ]
  show CohomologyClass.mk (zcomp α (Cocycle.ofHom (resMap ℤ φ)) (add_zero 0)) = _
  congr 1
  apply coc_ext
  rw [hβv, ev_post, hαv]
  have := congrArg (fun m => (m.hom.app (op X)).hom s) (resι_nat φ)
  exact this
end LateralTheory.E.LeafKumFieldPf.H0Naturality
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.KummerFields.GmSecSurj
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H2CurveOrder.LeafKumSeqPf LateralTheory.E.H2CurveOrder.KummerH0Surjection

namespace LateralTheory.E.LeafKumFieldPf.GmSecSurj

def unitsEquivHom (A : Type) [CommRing A] : (Multiplicative ℤ →* A) ≃ Aˣ where
  toFun f := (zpowersHom Aˣ).symm f.toHomUnits
  invFun u := (Units.coeHom A).comp (zpowersHom Aˣ u)
  left_inv f := by ext; simp
  right_inv u := by ext; simp

abbrev LR : CommRingCat.{0} := CommRingCat.of (AddMonoidAlgebra ℤ ℤ)

def homUnits (A : CommRingCat.{0}) : (LR ⟶ A) ≃ Aˣ :=
  ({ toFun := fun f => f.hom, invFun := CommRingCat.ofHom, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl } : (LR ⟶ A) ≃ (AddMonoidAlgebra ℤ ℤ →+* A)).trans <|
    (RingHom.equivIntAlgHom _ _).trans <| (AddMonoidAlgebra.lift ℤ A ℤ).symm.trans (unitsEquivHom A)

theorem homUnits_val (A : CommRingCat.{0}) (ψ : LR ⟶ A) :
    ((homUnits A ψ : Aˣ) : A) = ψ.hom (AddMonoidAlgebra.of ℤ ℤ (Multiplicative.ofAdd 1)) := by
  simp [homUnits, unitsEquivHom]
  rfl

theorem homUnits_nat {A B : CommRingCat.{0}} (ψ : LR ⟶ A) (h : A ⟶ B) :
    homUnits B (ψ ≫ h) = Units.map h.hom.toMonoidHom (homUnits A ψ) := by
  ext
  simp [homUnits_val]

abbrev P : Scheme.{0}ᵒᵖ ⥤ Type 1 := Scheme.Γ ⋙ unitsF ⋙ forget _

def repr : P.RepresentableBy (Spec LR) where
  homEquiv {X} := (ΓSpec.adjunction.homEquiv X (op LR)).symm.trans <|
    ({ toFun := fun φ => φ.unop, invFun := fun φ => φ.op, left_inv := fun _ => rfl, right_inv := fun _ => rfl } :
      (Scheme.Γ.rightOp.obj X ⟶ op LR) ≃ (LR ⟶ Γ(X, ⊤))).trans <| (homUnits _).trans <|
      Additive.ofMul.trans Equiv.ulift.symm
  homEquiv_comp {X X'} f g := by
    simp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_left_symm]
    exact congrArg (fun u => ULift.up (Additive.ofMul u)) (homUnits_nat _ (Scheme.Γ.map f.op))

theorem isSheaf_P : Presieve.IsSheaf Scheme.etaleTopology.{0} P := by
  have : Scheme.etaleTopology.{0}.Subcanonical :=
    GrothendieckTopology.Subcanonical.of_le Scheme.etaleTopology_le_proetaleTopology
  have : P.IsRepresentable := repr.isRepresentable
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable P

theorem isSheaf_units : Presheaf.IsSheaf Scheme.etaleTopology.{0} (Scheme.Γ ⋙ unitsF) :=
  (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).mpr
    ((isSheaf_iff_isSheaf_of_type _ _).mpr isSheaf_P)

theorem LeafGmSecSurj_of : LateralTheory.E.H2CurveOrder.KummerH0Surjection.LeafGmSecSurj := by
  intro B _ y
  have := isIso_toSheafify Scheme.etaleTopology.{0} isSheaf_units
  let g := (toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ unitsF)).app (op (Spec (CommRingCat.of B)))
  refine ⟨((inv g).hom y).down, ?_⟩
  show g.hom ((inv g).hom y) = y
  change (inv g ≫ g).hom y = y
  rw [IsIso.inv_hom_id]
  rfl

end LateralTheory.E.LeafKumFieldPf.GmSecSurj
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafKumFieldPf

open LateralTheory.E.E4

theorem kumMu : LateralTheory.E.H2CurveOrder.LeafKumSeqPf.LeafKumMu := fun hy =>
  LateralTheory.E.H2CurveOrder.LeafKumMuPf.LeafKumMu_of hy.2.2.2.2.2.2.1 hy.2.2.2.2.2.2.2.2.1
    LateralTheory.E.H2CurveOrder.muUnits hy

theorem etale_kummer_sequence_degree_zero_global_sections : LateralTheory.E.H2CurveOrder.LeafKumSeqPf.KummerUnitsSurjectH0 := fun hy =>
  LateralTheory.E.H2CurveOrder.KummerH0Surjection.etale_kummer_degree_zero_cohomology_of_sections_and_units_surjective LateralTheory.E.H2CurveOrder.kumSecSurj
    (LateralTheory.E.LeafKumFieldPf.H0Naturality.etale_degree_zero_cohomology_natural_in_sheaf hy.2.2.2.2.2.2.2.1)
    LateralTheory.E.LeafKumFieldPf.GmSecSurj.LeafGmSecSurj_of hy

theorem kumSeq : LateralTheory.E.LeafKumCut.LeafKumSeq :=
  LateralTheory.E.H2CurveOrder.LeafKumSeqPf.LeafKumSeq_of kumMu etale_kummer_sequence_degree_zero_global_sections

end LateralTheory.E.LeafKumFieldPf
end
end
