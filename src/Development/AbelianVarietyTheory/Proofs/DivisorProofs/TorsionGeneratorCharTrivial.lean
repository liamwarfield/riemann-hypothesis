module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointLocallyConstantComplexAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointLocallyConstantComplexAbelian
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionLocal

lemma comp_pow_overScheme_grpObj {A T : Over (Sp ℂ)} [GrpObj A] (f : T ⟶ A) (g : A ⟶ A) :
    ∀ n : ℕ, f ≫ g ^ n = (f ≫ g) ^ n
  | 0 => by simp [MonObj.comp_one]
  | n + 1 => by rw [pow_succ, pow_succ, MonObj.comp_mul, comp_pow_overScheme_grpObj f g n]

theorem locally_eq_const_of_pow_eq_one : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (N : ℕ), 1 ≤ N →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ^ N = 1 →
    ∀ t : T.left, ∃ (U : T.left.Opens) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A), t ∈ U ∧ U.ι ≫ x.left = U.ι ≫ T.hom ≫ y.left := by
  intro A _ hA N hN T x hx t
  have hunit : IsUnit ((N : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have h : IsUnit ((N : ℂ)) := (Nat.cast_ne_zero.mpr (by omega)).isUnit
    simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  obtain ⟨-, hfin, het, -⟩ := abelianScheme_id_pow_finite_etale_surjective (Sp ℂ) A N hA hunit
  set f : A ⟶ A := (𝟙 A) ^ N with hf
  have hTu : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)
  have hxf : x.left ≫ f.left = T.hom ≫ η[A].left := by
    have h1 : x ≫ f = toUnit T ≫ η[A] := by
      rw [hf, comp_pow_overScheme_grpObj, Category.comp_id, hx]; rfl
    have h2 := congrArg (fun h => h.left) h1
    simpa [hTu] using h2
  haveI : IsFinite f.left := hfin
  haveI : Etale f.left := het
  haveI := hA.smooth
  have hη : η[A].left ≫ A.hom = 𝟙 _ := by simpa using Over.w η[A]
  have hfw : f.left ≫ A.hom = A.hom := Over.w f
  have hpt : T.hom t = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
  set a := x.left t with ha_def
  have hfa : f.left a = η[A].left (IsLocalRing.closedPoint ℂ) := by
    rw [ha_def, ← Scheme.Hom.comp_apply, hxf, Scheme.Hom.comp_apply, hpt]
  have he : IsClosed ({η[A].left (IsLocalRing.closedPoint ℂ)} : Set A.left) :=
    ((pointEquivClosedPoint A.hom) ⟨η[A].left, hη⟩).2
  haveI : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have ha : IsClosed ({a} : Set A.left) := by
    rw [isClosed_singleton_iff_locallyOfFiniteType]
    have h1 : LocallyOfFiniteType (A.left.fromSpecResidueField (f.left a)) :=
      isClosed_singleton_iff_locallyOfFiniteType.mp (hfa ▸ he)
    have h2 : LocallyOfFiniteType (Spec.map (f.left.residueFieldMap a)) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      exact RingHom.FiniteType.of_finite (residueFieldMap_finite_of_locallyQuasiFinite f.left a)
    have h3 : LocallyOfFiniteType (A.left.fromSpecResidueField a ≫ f.left) := by
      rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]; infer_instance
    exact locallyOfFiniteType_of_comp _ f.left
  let y0 : Sp ℂ ⟶ A.left := pointOfClosedPoint A.hom a ha
  have hy0 : y0 ≫ A.hom = 𝟙 _ := pointOfClosedPoint_comp A.hom a ha
  let y : 𝟙_ (Over (Sp ℂ)) ⟶ A := Over.homMk y0 (by simpa using hy0)
  have hy0f : y0 ≫ f.left = η[A].left := by
    refine ext_of_apply_closedPoint_eq A.hom ?_ hη ?_
    · rw [Category.assoc, hfw, hy0]
    · show f.left (pointOfClosedPoint A.hom a ha (IsLocalRing.closedPoint ℂ)) = _
      exact (congrArg f.left (pointOfClosedPoint_apply A.hom a ha _)).trans hfa
  have hg : x.left ≫ f.left = (T.hom ≫ y0) ≫ f.left := by
    rw [hxf, Category.assoc, hy0f]
  have hψ := Spec.map_preimage (T.left.fromSpecResidueField t ≫ T.hom)
  set ψ := Spec.preimage (T.left.fromSpecResidueField t ≫ T.hom)
  have hr : (residueFieldIsoBase A.hom a ha).inv ≫ x.left.residueFieldMap t = ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, SpecMap_residueFieldIsoBase_inv]
    erw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]
    rw [Over.w x]
  have k : T.left.fromSpecResidueField t ≫ x.left = T.left.fromSpecResidueField t ≫ T.hom ≫ y0 := by
    rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← hψ]
    simp only [y0, pointOfClosedPoint, ← Category.assoc, ← Spec.map_comp]
    rw [← hr, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  let g : T.left ⟶ pullback f.left f.left := pullback.lift x.left (T.hom ≫ y0) hg
  have kg : T.left.fromSpecResidueField t ≫ g =
      (T.left.fromSpecResidueField t ≫ x.left) ≫ pullback.diagonal f.left := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, k]
  refine ⟨g ⁻¹ᵁ (pullback.diagonal f.left).opensRange, y, ?_, ?_⟩
  · show g t ∈ Set.range (pullback.diagonal f.left)
    have hk := congrArg (fun h => h (IsLocalRing.closedPoint (T.left.residueField t))) kg
    refine ⟨_, ((Scheme.Hom.comp_apply _ _ _).symm.trans hk.symm).trans
      ((Scheme.Hom.comp_apply _ _ _).trans ?_)⟩
    exact congrArg g (Scheme.fromSpecResidueField_apply t _)
  · set U := g ⁻¹ᵁ (pullback.diagonal f.left).opensRange
    have hle : Set.range (U.ι ≫ g) ⊆ Set.range (pullback.diagonal f.left) := by
      rintro _ ⟨u, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact u.2
    have hl := IsOpenImmersion.lift_fac (pullback.diagonal f.left) (U.ι ≫ g) hle
    have h1 := congrArg (· ≫ pullback.fst f.left f.left) hl
    have h2 := congrArg (· ≫ pullback.snd f.left f.left) hl
    simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id, g,
      pullback.lift_fst, pullback.lift_snd] at h1 h2
    show U.ι ≫ x.left = U.ι ≫ T.hom ≫ y0
    rw [← h1, h2]

end GlobalTheory.TorsionLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointLocallyConstantComplexAbelianStatement
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoint_locally_constant_complexAbelian : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (N : ℕ), 1 ≤ N → ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ^ N = 1 →
    ∀ t : T.left, ∃ (U : T.left.Opens) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A), t ∈ U ∧ U.ι ≫ x.left = U.ι ≫ T.hom ≫ y.left := by
  first | exact @GlobalTheory.TorsionLocal.locally_eq_const_of_pow_eq_one | exact GlobalTheory.TorsionLocal.locally_eq_const_of_pow_eq_one | (intros; apply GlobalTheory.TorsionLocal.locally_eq_const_of_pow_eq_one <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGeneratorLambdaPullbackComplexPointOfEqOnOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGeneratorLambdaPullbackComplexPointOfEqOnOpen
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PointDesc

theorem hasGen_of_comp {X Y Z : Scheme.{0}} {L : LB X} (f : Y ⟶ X) (h : Z ⟶ Y) (m : Z ⟶ X)
    (hm : h ≫ f = m) (H : HasGen (L.pull f)) : HasGen (L.pull m) := by
  obtain ⟨t, ht⟩ := H
  subst hm
  exact ⟨LB.pullGen L (fun _ : PUnit => f) (fun _ => 1) t h,
    DVR.pullGen_isGen L (fun _ : PUnit => f) (fun _ => 1) t ht h⟩

theorem hasGen_pull_pull {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (h : Z ⟶ Y)
    (H : HasGen (L.pull (h ≫ f))) : HasGen ((L.pull f).pull h) := by
  obtain ⟨t, ht⟩ := H
  exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hL _) (pull_isLB (pull_isLB hL f) h)
    (GlobalTheory.FamRep.lbIso_pull_pull hL f h).symm t ht

theorem hasGen_lam_pull_of_eq_on_open : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A) (U : T.left.Opens) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) (t : T.left), t ∈ U →
      U.ι ≫ x.left = U.ι ≫ T.hom ≫ y.left → HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → HasGen ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ y)).left) := by
  intro A _ hA M hM T x U y t ht hU H
  have hL : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _

  let x0 : U.toScheme := ⟨t, ht⟩
  let K : Type := U.toScheme.residueField x0
  letI : Field K := inferInstanceAs (Field (U.toScheme.residueField x0))
  let q : Sp K ⟶ U.toScheme := U.toScheme.fromSpecResidueField x0
  let p : Sp K ⟶ T.left := q ≫ U.ι
  let φ := Spec.preimage (p ≫ T.hom)
  let β : ℂ →+* K := φ.hom
  have hβ : spMap β = p ≫ T.hom := Spec.map_preimage _
  let Tk : Over (Sp ℂ) := Over.mk (spMap β)
  let pk : Tk ⟶ T := Over.homMk p hβ.symm
  have hxy : pk ≫ x = toUnit Tk ≫ y := by
    ext1
    simp only [Over.comp_left, Over.homMk_left, pk, Over.toUnit_left]
    show (q ≫ U.ι) ≫ x.left = Tk.hom ≫ y.left
    simp only [Tk, Over.mk_hom, hβ, p, Category.assoc, hU]
  let e : A ⟶ A ⊗ 𝟙_ (Over (Sp ℂ)) := lift (𝟙 A) (toUnit A)
  let g := lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ y)
  have sq : (A ◁ pk) ≫ lift (fst A T) (snd A T ≫ x) = fst A Tk ≫ e ≫ g := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [e, g]
    · simp only [Category.assoc, lift_snd, e, g, lift_fst_assoc, lift_snd_assoc]
      rw [whiskerLeft_snd_assoc, hxy, ← Category.assoc, ← Category.assoc]
      congr 1
      exact toUnit_unique _ _
  have H₁ : HasGen ((abelian₂ A M).pull ((fst A Tk).left ≫ (e ≫ g).left)) :=
    hasGen_of_comp _ (A ◁ pk).left _ (by rw [← Over.comp_left, sq, Over.comp_left]) H
  have H₂ := hasGen_pull_pull hL (e ≫ g).left (fst A Tk).left H₁
  have hpb : IsPullback (fst A Tk).left (snd A Tk).left A.hom (spMap β) := IsPullback.of_hasPullback _ _
  obtain ⟨u, hu⟩ := GlobalTheory.FieldTriv.exists_gen_of_field_extension ℂ K β A hA _ (fst A Tk).left (snd A Tk).left hpb
    ((abelian₂ A M).pull (e ≫ g).left) (pull_isLB hL _) H₂
  refine hasGen_of_comp (e ≫ g).left (fst A (𝟙_ (Over (Sp ℂ)))).left _ ?_ ⟨u, hu⟩
  rw [← Over.comp_left]
  congr 1
  rw [← Category.assoc]
  have : fst A (𝟙_ (Over (Sp ℂ))) ≫ e = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [e]
    · simp only [e, Category.assoc, lift_snd, Category.id_comp]
      exact toUnit_unique _ _
  rw [this, Category.id_comp]

end GlobalTheory.PointDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGeneratorLambdaPullbackComplexPointOfEqOnOpenStatement
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGenerator_lambdaPullback_complexPoint_of_eqOnOpen : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A) (U : T.left.Opens) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A) (t : T.left), t ∈ U →
      U.ι ≫ x.left = U.ι ≫ T.hom ≫ y.left → HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → HasGen ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ y)).left) := by
  first | exact @GlobalTheory.PointDesc.hasGen_lam_pull_of_eq_on_open | exact GlobalTheory.PointDesc.hasGen_lam_pull_of_eq_on_open | (intros; apply GlobalTheory.PointDesc.hasGen_lam_pull_of_eq_on_open <;> assumption)
end
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem torsion_point_comp_eq_one : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left) (f : A ⟶ A) (N : ℕ), M.IsLB → 1 ≤ N →
    (∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ A, HasGen ((abelian₂ A M).pull (lift (fst A (𝟙_ (Over (Sp ℂ)))) (snd A (𝟙_ (Over (Sp ℂ))) ≫ y)).left) → y ≫ f = 1) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ^ N = 1 → HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → x ≫ f = 1 := by
  intro A _ hA M f N hM hN hf T x hx hgen
  apply Over.OverMorphism.ext
  apply AlgebraicGeometry.Scheme.hom_ext_of_forall
  intro t
  obtain ⟨U, y, htU, hU⟩ := GlobalTheory.T.torsionPoint_locally_constant_complexAbelian A hA N hN T x hx t
  have hy : y ≫ f = 1 := hf y (GlobalTheory.T.hasGenerator_lambdaPullback_complexPoint_of_eqOnOpen A hA M hM T x U y t htU hU hgen)
  refine ⟨U, htU, ?_⟩
  have h1 : (1 : T ⟶ A) = toUnit T ≫ (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) := (comp_one _).symm
  have h2 : (toUnit T).left = T.hom := by
    simpa using Over.w (toUnit T)
  rw [h1, ← hy]
  simp only [Over.comp_left, h2]
  rw [← Category.assoc, hU, Category.assoc, Category.assoc]

end GlobalTheory
