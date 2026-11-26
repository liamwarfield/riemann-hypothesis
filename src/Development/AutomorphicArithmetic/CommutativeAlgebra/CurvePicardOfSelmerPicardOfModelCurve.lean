module

public import Development.EtaleCohomology.EtaleSheaves.PartDiagCut
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveFunctionField
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.HasExtInstances
public import Development.AutomorphicArithmetic.CommutativeAlgebra.BaseChangeCurveFunctionFieldCompOfNormal
public import Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteKummerSelmerOfCharts

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.SurjectiveOfIsPullbackSpecFieldExt
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.surjective_of_isPullback_spec_field_ext :
    ∀ (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → Surjective u := by
  intro k L _ _ _ C X c u x hpb
  have hs : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k L))) := by
    rw [surjective_iff]
    intro p
    obtain ⟨q⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstanceAs (Nonempty (PrimeSpectrum L))
    refine ⟨q, ?_⟩
    exact Subsingleton.elim (α := PrimeSpectrum k) _ _
  exact MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hs
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.BaseChangeAffineSectionsSubalgebraTensor
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private lemma scal {k : Type} [Field k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k)
    [Algebra k C.functionField]
    (h : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) =
      (C.fromSpecStalk (genericPoint C)) ≫ c)
    (W : C.Opens) [Nonempty W] :
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c.appLE ⊤ W le_top ≫ C.germToFunctionField W =
      CommRingCat.ofHom (algebraMap k C.functionField) := by
  have h1 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k C.functionField))
  rw [h, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop] at h1
  have hm : (Spec (C.presheaf.stalk (genericPoint C))).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk (genericPoint C))).Opens) ≤ ⊤)).op = 𝟙 _ :=
    (Spec (C.presheaf.stalk (genericPoint C))).presheaf.map_id _
  have h2 : CommRingCat.ofHom (algebraMap k C.functionField) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c.appTop ≫ C.presheaf.germ ⊤ (genericPoint C) trivial := by
    rw [← cancel_mono (Scheme.ΓSpecIso (C.presheaf.stalk (genericPoint C))).inv]
    refine h1.trans ?_
    simp only [Category.assoc]
    erw [hm, Category.comp_id]
  rw [h2]
  simp only [Scheme.Hom.appLE, Category.assoc]
  congr 2
  exact C.presheaf.germ_res (homOfLE le_top) (genericPoint C) _

theorem UpperTheory.baseChange_affine_sections_subalgebra_tensor :
    ∀ (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ (W : C.Opens) [Nonempty W], IsAffineOpen W → ∀ B : Subalgebra k C.functionField, (B : Set C.functionField) = Set.range (C.germToFunctionField W) → IsAffineOpen (u ⁻¹ᵁ W) ∧ ∃ e : L ⊗[k] B ≃+* Γ(X, u ⁻¹ᵁ W), (∀ (a : Γ(C, W)) (b : B), (b : C.functionField) = C.germToFunctionField W a → e ((1 : L) ⊗ₜ[k] b) = u.app W a) ∧ ∀ l : L, e (l ⊗ₜ[k] (1 : B)) = x.appLE ⊤ (u ⁻¹ᵁ W) le_top ((Scheme.ΓSpecIso (CommRingCat.of L)).inv l) := by
  intro k L _ _ _ C X _ c u x H _ hK W _ hW B hB
  have hu : IsAffineHom u := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  refine ⟨hW.preimage u, ?_⟩
  let g0 : Γ(C, W) →+* C.functionField := (C.germToFunctionField W).hom
  have hinj : Function.Injective g0 := C.germToFunctionField_injective W
  have hmem : ∀ a, g0 a ∈ B := fun a => by
    have : g0 a ∈ (B : Set C.functionField) := by rw [hB]; exact ⟨a, rfl⟩
    exact this
  let g1 : Γ(C, W) →+* B := g0.codRestrict B hmem
  have hbij : Function.Bijective g1 := by
    refine ⟨fun a a' h => hinj (congrArg Subtype.val h), fun b => ?_⟩
    have : (b : C.functionField) ∈ (B : Set C.functionField) := b.2
    rw [hB] at this
    obtain ⟨a, ha⟩ := this
    exact ⟨a, Subtype.ext ha⟩
  let gB : Γ(C, W) ≃+* B := RingEquiv.ofBijective g1 hbij
  let iB : CommRingCat.of B ≅ Γ(C, W) := gB.symm.toCommRingCatIso
  have hP := (GroundTheory.Arith.SchemeCoh.isPushout_app_of_isPullback H hW).flip
  have hT := CommRingCat.isPushout_tensorProduct k L B
  have hP' : IsPushout (CommRingCat.ofHom (algebraMap k L)) (CommRingCat.ofHom (algebraMap k B))
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appLE ⊤ (u ⁻¹ᵁ W) le_top)
      (iB.hom ≫ u.app W) := by
    refine hP.of_iso (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) iB.symm (Iso.refl _)
      (Scheme.ΓSpecIso_naturality _) ?_ (by simp) (by simp)
    rw [← Iso.inv_comp_eq]
    ext r
    exact congr($(scal c hK W).hom r)
  let E := IsPushout.isoIsPushout _ _ hT hP'
  refine ⟨E.commRingCatIsoToRingEquiv, ?_, ?_⟩
  · intro a b hab
    have h1 := congr($(IsPushout.inr_isoIsPushout_hom _ _ hT hP').hom b)
    have h2 : iB.hom b = a := by
      apply hinj
      have h3 := congrArg Subtype.val (gB.apply_symm_apply b)
      exact h3.trans hab
    rw [← h2]
    exact h1
  · intro l
    have h1 := congr($(IsPushout.inl_isoIsPushout_hom _ _ hT hP').hom l)
    exact h1
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IsFunctionFieldFractionRingOfDedekindFiniteType
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

theorem UpperTheory.isFunctionField_fractionRing_of_dedekind_finiteType :
    ∀ (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → IsFunctionField k (FractionRing B) := by
  intro k B _ _ _ _ _ hB
  have hdim : ringKrullDim B = 1 := by
    apply eq_of_le_of_not_lt ?_ fun h' ↦ hB ?_
    · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
      infer_instance
    · have h'' : ringKrullDim B ≤ 0 := Order.le_of_lt_succ h'
      rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
      exact Ring.KrullDimLE.isField_of_isDomain
  exact GroundTheory.Arith.SchemeCoh.isFunctionField_of_ringKrullDim_eq_one k B (FractionRing B) hdim
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IsFunctionFieldAndChartsOfIsCurveOfIsUnit
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IsFunctionFieldAndChartCoverOfIsCurve
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IsChartAffineSectionsOfIsCurve
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private theorem ded_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) [IsDedekindDomain S] :
    IsDedekindDomain R := by
  have : IsDomain R := Function.Injective.isDomain (e : R →+* S) e.injective
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv S e.symm
  have : Ring.DimensionLEOne R := Ring.DimensionLEOne.of_ringEquiv e
  have : IsIntegrallyClosed R := IsIntegrallyClosed.of_equiv e.symm
  exact { }

private theorem base_comp {k : Type} [Field k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k)
    [Algebra k C.functionField]
    (hgen : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c)
    (W : C.Opens) [Nonempty W] :
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom ≫ CommRingCat.ofHom (algebraMap k C.functionField) =
      c.appLE ⊤ W le_top ≫ C.germToFunctionField W := by
  rw [← Scheme.ΓSpecIso_naturality, hgen]
  simp only [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop, Scheme.germToFunctionField]
  simp only [Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Iso.inv_hom_id, Category.comp_id]
  rfl

private theorem pre_ne {X Y : Scheme.{0}} (u : X ⟶ Y) (hu : Surjective u) (W : Y.Opens)
    (h : (W : Set Y).Nonempty) : ((u ⁻¹ᵁ W : X.Opens) : Set X).Nonempty := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨y, rfl⟩ := hu.surj w
  exact ⟨y, hw⟩

theorem UpperTheory.isChart_affine_sections_of_isCurve :
    ∀ (k : Type) [Field k] [IsAlgClosed k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ (W : C.Opens) [Nonempty W], IsAffineOpen W → ∀ B : Subalgebra k C.functionField, (B : Set C.functionField) = Set.range (C.germToFunctionField W) → IsChart B := by
  intro k _ _ C _ c hc _ hgen W _ hW B hB
  have hWne : (W : Set C).Nonempty := ⟨_, (Classical.arbitrary W).2⟩
  obtain ⟨hC1, -⟩ := UpperTheory.isDedekindDomain_affine_sections_of_isCurve k c hc
  obtain ⟨hded, hnf⟩ := hC1 W hW hWne
  let f : Γ(C, W) →+* C.functionField := (C.germToFunctionField W).hom
  have hmem : ∀ a, f a ∈ B := by
    intro a
    have : f a ∈ (B : Set C.functionField) := by
      rw [hB]; exact ⟨a, rfl⟩
    exact this
  let h : Γ(C, W) ≃+* B := RingEquiv.ofBijective
    (RingHom.codRestrict (σS := Subalgebra k C.functionField) f B hmem)
    ⟨fun a b hab => Scheme.germToFunctionField_injective C W (congrArg Subtype.val hab),
     fun b => by
      have hb : (b : C.functionField) ∈ (B : Set C.functionField) := b.2
      rw [hB] at hb
      obtain ⟨a, ha⟩ := hb
      exact ⟨a, Subtype.ext ha⟩⟩
  have hh : ∀ a, (h a : C.functionField) = f a := fun a => rfl
  unfold IsChart
  refine ⟨?_, ded_of_equiv h.symm, fun hf => hnf (MulEquiv.isField hf h.toMulEquiv), ?_, ?_⟩
  · haveI : LocallyOfFiniteType c := @IsProper.toLocallyOfFiniteType _ _ _ hc.2.1
    have g0 := c.finiteType_appLE (isAffineOpen_top (Sp k)) hW le_top
    have gi : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (fun y => ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom y, by simp⟩)
    have g2 := (g0.comp gi).comp_surjective (g := (h : Γ(C, W) →+* B)) h.surjective
    rw [← RingHom.finiteType_algebraMap]
    convert g2
    ext x
    have := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom x)) (base_comp c hgen W)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [← hh] at this
    simpa using this
  · have hfr := functionField_isFractionRing_of_isAffineOpen C W hW
    have := (IsFractionRing.isFractionRing_iff_of_base_ringEquiv C.functionField h).mp hfr
    have heq : ((algebraMap Γ(C, W) C.functionField).comp h.symm.toRingHom).toAlgebra =
        (inferInstance : Algebra B C.functionField) := by
      apply Algebra.algebra_ext
      intro b
      obtain ⟨a, rfl⟩ := h.surjective b
      show algebraMap Γ(C, W) _ (h.symm (h a)) = (h a : C.functionField)
      rw [h.symm_apply_apply]
      rfl
    rw [heq] at this
    exact this
  · intro L _ _ _
    have hp := IsPullback.of_hasPullback c (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    obtain ⟨hX, e, -, -⟩ := UpperTheory.baseChange_affine_sections_subalgebra_tensor k L c _ _ hp hgen W hW B hB
    have hsurj := UpperTheory.surjective_of_isPullback_spec_field_ext k L c _ _ hp
    obtain ⟨hX1, -⟩ := UpperTheory.isDedekindDomain_affine_sections_of_isCurve L _ (UpperTheory.isCurve_pullback_of_isCurve_baseChange k L c hc)
    obtain ⟨hd2, hn2⟩ := hX1 _ hX (pre_ne _ hsurj W hWne)
    exact ⟨ded_of_equiv e, fun hf => hn2 (MulEquiv.isField hf e.symm.toMulEquiv)⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IsFunctionFieldOfDedekindFiniteTypeFractionRing
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.isFunctionField_of_dedekind_finiteType_fractionRing :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K), IsDedekindDomain B → Algebra.FiniteType k B → ¬ IsField B → IsFractionRing B K → IsFunctionField k K := by
  intro k K _ _ _ B hD hF hB hFr
  have hdim : ringKrullDim B = 1 := by
    apply eq_of_le_of_not_lt ?_ fun h' ↦ hB ?_
    · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
      infer_instance
    · have h'' : ringKrullDim B ≤ 0 := Order.le_of_lt_succ h'
      rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
      exact Ring.KrullDimLE.isField_of_isDomain
  exact GroundTheory.Arith.SchemeCoh.isFunctionField_of_ringKrullDim_eq_one k B K hdim
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFunctionFieldHomGermOfSurjective
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.exists_functionField_hom_germ_of_surjective :
    ∀ {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X] (u : X ⟶ C), Surjective u → ∃ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ C.fromSpecStalk (genericPoint C) = X.fromSpecStalk (genericPoint X) ≫ u ∧ ∀ (W : C.Opens) [Nonempty W] [Nonempty (u ⁻¹ᵁ W)] (a : Γ(C, W)), φ (C.germToFunctionField W a) = X.germToFunctionField (u ⁻¹ᵁ W) (u.app W a) := by
  intro C X _ _ u hu
  have hgX : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  have hcl : closure ({u (genericPoint X)} : Set C) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    have h1 := image_closure_subset_closure_image (s := ({genericPoint X} : Set X)) u.continuous
    rw [Set.image_singleton, hgX, Set.image_univ,
      (Surjective.surj (f := u)).range_eq] at h1
    exact h1
  have hsp : u (genericPoint X) ⤳ genericPoint C := by
    rw [specializes_iff_mem_closure, hcl]
    trivial
  refine ⟨(C.presheaf.stalkSpecializes hsp ≫ u.stalkMap (genericPoint X)).hom, ?_, ?_⟩
  · rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
  · intro W _ _ a
    have hmem : u (genericPoint X) ∈ W :=
      ((genericPoint_spec X).mem_open_set_iff (u ⁻¹ᵁ W).isOpen).mpr (by simpa using ‹Nonempty (u ⁻¹ᵁ W)›)
    change (u.stalkMap (genericPoint X)).hom ((C.presheaf.stalkSpecializes hsp).hom
      ((C.presheaf.germ W (genericPoint C) _).hom a)) = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply (hy := _) (h := hsp)]
    exact Scheme.Hom.germ_stalkMap_apply u W (genericPoint X) hmem a
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TensorFractionRingExistsMulEqOfDenominator
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.tensor_fractionRing_exists_mul_eq_of_denominator :
    ∀ (k L K : Type) [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K] (B : Subalgebra k K), IsFractionRing B K → ∀ t : L ⊗[k] K, ∃ (s : L ⊗[k] B) (β : B), β ≠ 0 ∧ t * ((1 : L) ⊗ₜ[k] (β : K)) = inc L B s := by
  intro k L K _ _ _ _ _ B hB t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 1, one_ne_zero, by simp⟩
  | tmul l κ =>
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := B) κ
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : (b : K) ≠ 0 := fun h0 => hb0 (Subtype.ext h0)
    refine ⟨l ⊗ₜ[k] a, b, hb0, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp only [inc, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val]
    congr 1
    rw [← hab]
    change (a : K) / (b : K) * b = a
    field_simp
  | add x y hx hy =>
    obtain ⟨s1, β1, h1, e1⟩ := hx
    obtain ⟨s2, β2, h2, e2⟩ := hy
    refine ⟨s1 * ((1 : L) ⊗ₜ[k] β2) + s2 * ((1 : L) ⊗ₜ[k] β1), β1 * β2, mul_ne_zero h1 h2, ?_⟩
    have i1 : inc L B ((1 : L) ⊗ₜ[k] β2) = (1 : L) ⊗ₜ[k] (β2 : K) := by simp [inc]
    have i2 : inc L B ((1 : L) ⊗ₜ[k] β1) = (1 : L) ⊗ₜ[k] (β1 : K) := by simp [inc]
    have split : (1 : L) ⊗ₜ[k] ((β1 * β2 : B) : K) =
        ((1 : L) ⊗ₜ[k] (β1 : K)) * ((1 : L) ⊗ₜ[k] (β2 : K)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, Subalgebra.coe_mul]
    rw [map_add (f := _), map_mul, map_mul, i1, i2, ← e1, ← e2, split]
    ring
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSubalgebraEqRangeGermToFunctionField
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.exists_subalgebra_eq_range_germToFunctionField :
    ∀ (k : Type) [Field k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k) [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ (W : C.Opens) [Nonempty W], ∃ B : Subalgebra k C.functionField, (B : Set C.functionField) = Set.range (C.germToFunctionField W) := by
  intro k _ C _ c _ h W _
  have hη : genericPoint C ∈ (⊤ : C.Opens) := trivial
  have key : CommRingCat.ofHom (algebraMap k C.functionField) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c.appTop ≫ C.presheaf.germ ⊤ (genericPoint C) hη := by
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of k)).hom, ← Scheme.ΓSpecIso_naturality, h]
    simp only [Scheme.Hom.comp_appTop, Category.assoc, Iso.hom_inv_id_assoc]
    congr 1
    rw [Scheme.fromSpecStalk_appTop]
    have e1 : (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk (genericPoint C))).Opens) ≤ ⊤)) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [e1, op_id, CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc]
    exact congrArg (C.presheaf.germ ⊤ (genericPoint C) _ ≫ ·) (Iso.inv_hom_id _) |>.trans
      (Category.comp_id _)
  refine ⟨{ (C.germToFunctionField W).hom.range with algebraMap_mem' := ?_ }, ?_⟩
  · intro r
    refine ⟨C.presheaf.map (homOfLE le_top).op (c.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)), ?_⟩
    have hr := congrArg (fun f => f.hom r) key
    simp only [CommRingCat.hom_ofHom, CommRingCat.comp_apply] at hr
    rw [hr]
    exact C.presheaf.germ_res_apply (homOfLE le_top) _ _ _
  · rfl
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiniteNonemptyAffineCoverOfIntegral
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.exists_finite_nonempty_affine_cover_of_integral :
    ∀ (C : Scheme.{0}) [CompactSpace C] [IsIntegral C], ∃ (n : ℕ) (U : Fin n → C.Opens), (∀ i, IsAffineOpen (U i)) ∧ (∀ i, Nonempty (U i)) ∧ (0 < n) ∧ ∀ y : C, ∃ i, y ∈ U i := by
  intro C _ _
  have hex : ∀ y : C, ∃ W : C.Opens, IsAffineOpen W ∧ y ∈ W := fun y => by
    obtain ⟨W, hW, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
    exact ⟨W, hW, hy⟩
  choose W hWa hyW using hex
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set C))
    (fun y => (W y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, hyW y⟩)
  obtain ⟨y0⟩ := (inferInstance : Nonempty C)
  have htne : t.Nonempty := by
    obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y0))
    exact ⟨i, hi⟩
  refine ⟨t.card, fun i => W (t.equivFin.symm i), fun i => hWa _,
    fun i => ⟨⟨_, hyW _⟩⟩, Finset.card_pos.2 htne, fun y => ?_⟩
  obtain ⟨i, hi, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  refine ⟨t.equivFin ⟨i, hi⟩, ?_⟩
  simpa using hy
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.BaseChangeFunctionFieldHomGenericPointComp
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.baseChange_functionField_hom_genericPoint_comp :
    ∀ (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X] (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ C.fromSpecStalk (genericPoint C) = X.fromSpecStalk (genericPoint X) ≫ u → ∃ f : L →+* X.functionField, (∀ r : k, f (algebraMap k L r) = φ (algebraMap k C.functionField r)) ∧ ∀ (V : X.Opens) [Nonempty V] (l : L), X.germToFunctionField V (x.appLE ⊤ V le_top ((Scheme.ΓSpecIso (CommRingCat.of L)).inv l)) = f l := by
  intro k L _ _ _ C X _ _ c u x hpb _ hc φ hφ
  let F : CommRingCat.of L ⟶ X.functionField :=
    (Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial
  have hx : X.fromSpecStalk (genericPoint X) ≫ x = Spec.map F := by
    have h1 := Scheme.toSpecΓ_naturality x
    have h2 : x = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appTop) := by
      rw [Spec.map_comp, ← Category.assoc, ← h1, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    rw [h2, ← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
    simp only [F, Category.assoc]
  have key : ∀ (V : X.Opens) (hV : genericPoint X ∈ V),
      x.appLE ⊤ V le_top ≫ X.presheaf.germ V (genericPoint X) hV =
        x.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := by
    intro V hV
    rw [← x.appLE_map (V := ⊤) (V' := V) le_top (homOfLE le_top).op, Category.assoc,
      X.presheaf.germ_res, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  refine ⟨F.hom, ?_, ?_⟩
  · intro r
    have hsq : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField) ≫ CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap k L) ≫ F) := by
      rw [Spec.map_comp, Spec.map_comp, hc, ← Category.assoc, hφ, Category.assoc, hpb.w,
        ← Category.assoc, hx]
    have := congrArg (fun g => g.hom r) (Spec.map_injective hsq)
    simpa using this.symm
  · intro V _ l
    have hV : genericPoint X ∈ V :=
      ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
    have := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom l)) (key V hV)
    simpa [F] using this
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private theorem exists_tensor_lift {k L K M : Type} [Field k] [Field L] [Field K] [CommRing M] [Algebra k L] [Algebra k K]
    (f : L →+* M) (g : K →+* M) (h : ∀ r : k, f (algebraMap k L r) = g (algebraMap k K r)) :
    ∃ θ : L ⊗[k] K →+* M, ∀ l a, θ (l ⊗ₜ[k] a) = f l * g a := by
  letI : Algebra k M := (g.comp (algebraMap k K)).toAlgebra
  let f' : L →ₐ[k] M := { f with commutes' := fun r => h r }
  let g' : K →ₐ[k] M := { g with commutes' := fun r => rfl }
  exact ⟨(Algebra.TensorProduct.productMap f' g').toRingHom, fun l a => by simp [f', g']⟩

private theorem core (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X]
    (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L)
    (hpb : IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [Algebra k C.functionField]
    (hK : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c)
    {n : ℕ} (U : Fin n → C.Opens) (hUa : ∀ i, IsAffineOpen (U i)) [hne : ∀ i, Nonempty (U i)]
    (hUc : ∀ y : C, ∃ i, y ∈ U i) (hn : 0 < n)
    (B : Fin n → Subalgebra k C.functionField)
    (hB : ∀ i, (B i : Set C.functionField) = Set.range (C.germToFunctionField (U i)))
    (hfr : ∀ i, IsFractionRing (B i) C.functionField) :
    ∃ θ : L ⊗[k] C.functionField →+* X.functionField,
      Spec.map (CommRingCat.ofHom (θ.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ (C.fromSpecStalk (genericPoint C)) = (X.fromSpecStalk (genericPoint X)) ≫ u ∧ Function.Injective θ ∧ (∀ h : X.functionField, ∃ a b, b ≠ 0 ∧ h * θ b = θ a) ∧ ∀ y : X, ∃ (i : Fin n) (m : Ideal (L ⊗[k] B i)), m.IsPrime ∧ ∀ s ∉ m, ∃ w : (X.presheaf.stalk y)ˣ, algebraMap (X.presheaf.stalk y) X.functionField w = θ (inc L (B i) s) := by
  have hsurj := UpperTheory.surjective_of_isPullback_spec_field_ext k L c u x hpb
  obtain ⟨φ, hφgen, hφgerm⟩ := UpperTheory.exists_functionField_hom_germ_of_surjective u hsurj
  obtain ⟨f, hfk, hfx⟩ := UpperTheory.baseChange_functionField_hom_genericPoint_comp k L c u x hpb hK φ hφgen
  obtain ⟨θ, hθ⟩ := exists_tensor_lift f φ hfk
  have hne' : ∀ i, Nonempty (u ⁻¹ᵁ U i) := by
    intro i
    obtain ⟨⟨z, hz⟩⟩ := hne i
    obtain ⟨y, rfl⟩ := hsurj.surj z
    exact ⟨⟨y, hz⟩⟩
  have chart : ∀ i, IsAffineOpen (u ⁻¹ᵁ U i) ∧ ∃ e : L ⊗[k] B i ≃+* Γ(X, u ⁻¹ᵁ U i),
      ∀ s, θ (inc L (B i) s) = X.germToFunctionField (u ⁻¹ᵁ U i) (e s) := by
    intro i
    haveI := hne' i
    obtain ⟨hV, e, he1, he2⟩ := UpperTheory.baseChange_affine_sections_subalgebra_tensor k L c u x hpb hK (U i) (hUa i) (B i) (hB i)
    refine ⟨hV, e, fun s => ?_⟩
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul l b =>
      obtain ⟨a, ha⟩ : (b : C.functionField) ∈ Set.range (C.germToFunctionField (U i)) := by
        rw [← hB i]
        exact b.2
      have hsplit : l ⊗ₜ[k] b = (l ⊗ₜ[k] (1 : B i)) * ((1 : L) ⊗ₜ[k] b) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [show inc L (B i) (l ⊗ₜ[k] b) = l ⊗ₜ[k] (b : C.functionField) from rfl, hθ, hsplit,
        map_mul, map_mul, he1 a b ha.symm, he2 l, hfx, ← hφgerm (U i) a, ha]
    | add s t hs ht => simp only [map_add (f := _), hs, ht]
  have hcomp : θ.comp Algebra.TensorProduct.includeRight.toRingHom = φ := by
    ext a
    simp [Algebra.TensorProduct.includeRight_apply, hθ]
  have hinj : Function.Injective θ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨hV0, e0, he0⟩ := chart ⟨0, hn⟩
    haveI := hne' ⟨0, hn⟩
    obtain ⟨s, β, hβ, hs⟩ := UpperTheory.tensor_fractionRing_exists_mul_eq_of_denominator k L C.functionField (B ⟨0, hn⟩) (hfr _) t
    have h1 : θ (inc L (B ⟨0, hn⟩) s) = 0 := by rw [← hs, map_mul, ht, zero_mul]
    rw [he0] at h1
    have h2 : e0 s = 0 :=
      X.germToFunctionField_injective _ (h1.trans (map_zero _).symm)
    have h3 : s = 0 := e0.injective (h2.trans (map_zero e0).symm)
    rw [h3, map_zero] at hs
    have hβ' : (β : C.functionField) ≠ 0 := fun h => hβ (Subtype.ext h)
    have hu : IsUnit ((1 : L) ⊗ₜ[k] (β : C.functionField)) := by
      refine ⟨⟨1 ⊗ₜ[k] (β : C.functionField), 1 ⊗ₜ[k] (β : C.functionField)⁻¹, ?_, ?_⟩, rfl⟩
      · rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hβ']
        rfl
      · rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, inv_mul_cancel₀ hβ']
        rfl
    exact hu.mul_left_eq_zero.mp hs
  refine ⟨θ, by rw [hcomp]; exact hφgen, hinj, ?_, ?_⟩
  · intro h
    obtain ⟨hV, e, he⟩ := chart ⟨0, hn⟩
    haveI := hne' ⟨0, hn⟩
    haveI := functionField_isFractionRing_of_isAffineOpen X _ hV
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors Γ(X, u ⁻¹ᵁ U ⟨0, hn⟩)) h
    refine ⟨inc L (B ⟨0, hn⟩) (e.symm p), inc L (B ⟨0, hn⟩) (e.symm q), ?_, ?_⟩
    · intro h0
      have h4 := congrArg θ h0
      rw [he, map_zero, e.apply_symm_apply] at h4
      have h5 : (q : Γ(X, u ⁻¹ᵁ U ⟨0, hn⟩)) = 0 :=
        X.germToFunctionField_injective _ (h4.trans (map_zero _).symm)
      exact nonZeroDivisors.coe_ne_zero q h5
    · rw [he, he, e.apply_symm_apply, e.apply_symm_apply]
      exact hpq
  · intro y
    obtain ⟨i, hi⟩ := hUc (u y)
    haveI := hne' i
    obtain ⟨hV, e, he⟩ := chart i
    have hy : y ∈ u ⁻¹ᵁ U i := hi
    refine ⟨i, (hV.primeIdealOf ⟨y, hy⟩).asIdeal.comap e.toRingHom, inferInstance, fun s hs => ?_⟩
    have hsP : e s ∉ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := hs
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hy⟩
    haveI := hV.isLocalization_stalk ⟨y, hy⟩
    refine ⟨(IsLocalization.map_units (X.presheaf.stalk y)
      (⟨e s, hsP⟩ : (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl)).unit, ?_⟩
    rw [he]
    exact Scheme.algebraMap_germ_eq_germToFunctionField X hy (e s)

theorem UpperTheory.isFunctionField_and_chart_cover_of_isCurve :
    ∀ (k : Type) [Field k] [IsAlgClosed k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → IsFunctionField k C.functionField ∧ ∃ (n : ℕ) (B : Fin n → Subalgebra k C.functionField), (∀ i, IsChart (B i)) ∧ ∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra k L], ∃ (X : Scheme.{0}) (_ : IsIntegral X) (u : X ⟶ C) (x : X ⟶ Sp L) (θ : L ⊗[k] C.functionField →+* X.functionField), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) ∧ (∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) ∧ Spec.map (CommRingCat.ofHom (θ.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ (C.fromSpecStalk (genericPoint C)) = (X.fromSpecStalk (genericPoint X)) ≫ u ∧ Function.Injective θ ∧ (∀ h : X.functionField, ∃ a b, b ≠ 0 ∧ h * θ b = θ a) ∧ ∀ y : X, ∃ (i : Fin n) (m : Ideal (L ⊗[k] B i)), m.IsPrime ∧ ∀ s ∉ m, ∃ w : (X.presheaf.stalk y)ˣ, algebraMap (X.presheaf.stalk y) X.functionField w = θ (inc L (B i) s) := by
  intro k _ _ C _ c hcurve _ hK
  have hprop : IsProper c := hcurve.2.1
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  obtain ⟨n, U, hUa, hUne, hn, hUc⟩ := UpperTheory.exists_finite_nonempty_affine_cover_of_integral C
  haveI : ∀ i, Nonempty (U i) := hUne
  have hex : ∀ i, ∃ B : Subalgebra k C.functionField,
      (B : Set C.functionField) = Set.range (C.germToFunctionField (U i)) :=
    fun i => UpperTheory.exists_subalgebra_eq_range_germToFunctionField k c hK (U i)
  choose B hB using hex
  have hchart : ∀ i, IsChart (B i) :=
    fun i => UpperTheory.isChart_affine_sections_of_isCurve k c hcurve hK (U i) (hUa i) (B i) (hB i)
  refine ⟨UpperTheory.isFunctionField_of_dedekind_finiteType_fractionRing k C.functionField (B ⟨0, hn⟩) (hchart _).2.1 (hchart _).1
    (hchart _).2.2.1 (hchart _).2.2.2.1, n, B, hchart, ?_⟩
  intro L _ _ _
  let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have hpb : IsPullback (pullback.fst c g) (pullback.snd c g) c g := IsPullback.of_hasPullback c g
  have hcurve' := UpperTheory.isCurve_pullback_of_isCurve_baseChange k L c hcurve
  haveI hXint : IsIntegral (pullback c g) := hcurve'.1
  have hstalk := (UpperTheory.isDedekindDomain_affine_sections_of_isCurve L (pullback.snd c g) hcurve').2
  obtain ⟨θ, h1, h2, h3, h4⟩ := core k L c (pullback.fst c g) (pullback.snd c g) hpb hK U hUa hUc hn
    B hB (fun i => (hchart i).2.2.2.1)
  exact ⟨pullback c g, hXint, pullback.fst c g, pullback.snd c g, θ, hpb, hstalk, h1, h2, h3, h4⟩
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private lemma UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.inc_injective {k K L : Type} [Field k] [Field K] [Algebra k K] [Field L] [Algebra k L]
    (B : Subalgebra k K) : Function.Injective (inc L B) := by
  exact Module.Flat.lTensor_preserves_injective_linearMap (R := k) (M := L) B.val.toLinearMap Subtype.val_injective

private lemma UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.solve {E : Type*} [Field E] {f S T A D : E} {q : ℕ} (hS : S ≠ 0) (hD : D ≠ 0)
    (h : f * (S * D ^ q) = T * A ^ q) : f = T * S⁻¹ * (A * D⁻¹) ^ q := by
  have hDq : D ^ q ≠ 0 := pow_ne_zero _ hD
  rw [mul_pow, inv_pow]
  field_simp
  linear_combination h

theorem UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit :
    Hyps → ∀ (q : ℕ) [NeZero q], ∀ (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → IsFunctionField k C.functionField ∧ Charts k C.functionField q := by
  intro hH q _ k _ _ hq C _ c hc _ hgen
  obtain ⟨hff, n, B, hB, hX⟩ := UpperTheory.isFunctionField_and_chart_cover_of_isCurve k c hc hgen
  refine ⟨hff, n, B, hB, ?_⟩
  intro L _ _ _ F hF hloc
  obtain ⟨X, hXi, u, x, θ, hpb, hic, hcomm, hθ, hfrac, hloc'⟩ := hX L
  have hθF : θ F ≠ 0 := (map_ne_zero_iff θ hθ).mpr hF
  have key := UpperTheory.baseChange_curve_functionField_comp_of_normal hH q k L hq c hc u x hpb hic
    (θ.comp Algebra.TensorProduct.includeRight.toRingHom) hcomm (Units.mk0 (θ F) hθF) (by
      intro y
      obtain ⟨i, m, hm, hw⟩ := hloc' y
      obtain ⟨M, hM, hmM⟩ := Ideal.exists_le_maximal m hm.ne_top
      obtain ⟨s, t, a, b, hs, ht, ha, hb, he⟩ := hloc i M hM
      obtain ⟨ws, hws⟩ := hw s (fun h => hs (hmM h))
      obtain ⟨wt, hwt⟩ := hw t (fun h => ht (hmM h))
      have hinc := UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.inc_injective (L := L) (B i)
      have hne : ∀ z : L ⊗[k] ↥(B i), z ≠ 0 → θ (inc L (B i) z) ≠ 0 := fun z hz =>
        (map_ne_zero_iff θ hθ).mpr ((map_ne_zero_iff _ hinc).mpr hz)
      have hs0 : s ≠ 0 := fun h => hs (h ▸ M.zero_mem)
      have hA := hne a ha
      have hD := hne b hb
      have hS := hne s hs0
      refine ⟨wt * ws⁻¹, Units.mk0 (θ (inc L (B i) a) * (θ (inc L (B i) b))⁻¹) (mul_ne_zero hA (inv_ne_zero hD)), ?_⟩
      have h1 := congrArg θ he
      simp only [map_mul, map_pow] at h1
      rw [Units.val_mk0, Units.val_mk0, Units.val_mul, map_mul, map_units_inv, hws, hwt]
      exact UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.solve hS hD h1)
  obtain ⟨f, h, hfh⟩ := key
  rw [Units.val_mk0] at hfh
  obtain ⟨a, b, hb, hab⟩ := hfrac ↑h
  have hθb : θ b ≠ 0 := (map_ne_zero_iff θ hθ).mpr hb
  refine ⟨f, a, b, ?_, hb, ?_⟩
  · intro ha
    rw [ha, map_zero] at hab
    exact mul_ne_zero h.ne_zero hθb hab
  · apply hθ
    rw [map_mul, map_mul, map_pow, map_pow, ← hab, hfh]
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Algebra.TensorProduct.includeRight_apply]
    ring
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteKummerSelmerOfFiniteExtension
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteKernelPowClassesOfPrimitiveRoot
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

private lemma mem_range_of_fixed {K K' : Type} [Field K] [Field K'] [Algebra K K'] [FiniteDimensional K K']
    (q : ℕ) (hq : (q : K) ≠ 0) (σ₀ : K' →ₐ[K] AlgebraicClosure K) (c : K') (d : K) (hd : d ≠ 0)
    (hc : c ^ q = algebraMap K K' d)
    (hfix : ∀ σ : K' →ₐ[K] AlgebraicClosure K, σ c = σ₀ c) : c ∈ (algebraMap K K').range := by
  have hsep : (minpoly K c).Separable := by
    refine (Polynomial.separable_X_pow_sub_C d hq hd).of_dvd (minpoly.dvd K c ?_)
    simp [hc]
  have hsplit : ((minpoly K c).map (algebraMap K (AlgebraicClosure K))).Splits := IsAlgClosed.splits _
  have hroot : (minpoly K c).rootSet (AlgebraicClosure K) = {σ₀ c} := by
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly]
    ext y
    constructor
    · rintro ⟨σ, rfl⟩
      exact hfix σ
    · rintro rfl
      exact ⟨σ₀, rfl⟩
  have hcard := Polynomial.card_rootSet_eq_natDegree hsep hsplit
  rw [← minpoly.natDegree_eq_one_iff, ← hcard, Fintype.card_eq_one_iff]
  refine ⟨⟨σ₀ c, by rw [hroot]; rfl⟩, fun y => Subtype.ext ?_⟩
  have hy : (y : AlgebraicClosure K) ∈ ({σ₀ c} : Set (AlgebraicClosure K)) := hroot ▸ y.2
  exact hy

theorem UpperTheory.finite_kernel_powClasses_of_primitive_root :
    ∀ (K K' : Type) [Field K] [Field K'] [Algebra K K'] [FiniteDimensional K K'] (q : ℕ) [NeZero q], (∃ ζ : K, IsPrimitiveRoot ζ q) → FinCls q {a : Kˣ | ∃ b : K', algebraMap K K' (a : K) = b ^ q} := by
  intro K K' _ _ _ _ q _ ⟨ζ, hζ⟩
  classical
  haveI := hζ.neZero'
  have hq : ((q : ℕ) : K) ≠ 0 := NeZero.ne _
  have hq0 : q ≠ 0 := NeZero.ne q
  let σ₀ : K' →ₐ[K] AlgebraicClosure K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let S : Set Kˣ := {a : Kˣ | ∃ b : K', algebraMap K K' (a : K) = b ^ q}
  let bb : Kˣ → K' := fun a => if h : ∃ b : K', algebraMap K K' (a : K) = b ^ q then h.choose else 1
  have hbb : ∀ a ∈ S, algebraMap K K' (a : K) = bb a ^ q := by
    intro a ha
    have ha' : ∃ b : K', algebraMap K K' (a : K) = b ^ q := ha
    simp only [bb, dif_pos ha']
    exact ha'.choose_spec
  have hbb0 : ∀ a ∈ S, bb a ≠ 0 := by
    intro a ha h0
    have h := hbb a ha
    rw [h0, zero_pow hq0] at h
    exact a.ne_zero ((algebraMap K K').injective (by rw [h, map_zero]))
  let sig : Kˣ → (K' →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K := fun a σ => σ (bb a) / σ₀ (bb a)
  have hsig : ∀ a ∈ S, ∀ σ, sig a σ ∈ Polynomial.nthRootsFinset q (1 : AlgebraicClosure K) := by
    intro a ha σ
    rw [Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hq0)]
    have h1 : σ (bb a) ^ q = σ₀ (bb a) ^ q := by
      rw [← map_pow, ← map_pow, ← hbb a ha, AlgHom.commutes, AlgHom.commutes]
    have h2 : σ₀ (bb a) ≠ 0 := (map_ne_zero σ₀).mpr (hbb0 a ha)
    simp only [sig, div_pow, h1, div_self (pow_ne_zero _ h2)]
  have hfin : (sig '' S).Finite := by
    refine (Set.Finite.pi (t := fun _ => (Polynomial.nthRootsFinset q (1 : AlgebraicClosure K) : Set _))
      (fun _ => Finset.finite_toSet _)).subset ?_
    rintro _ ⟨a, ha, rfl⟩
    exact Set.mem_univ_pi.mpr (fun σ => hsig a ha σ)
  let rep : ((K' →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K) → Kˣ :=
    fun f => if h : ∃ a ∈ S, sig a = f then h.choose else 1
  refine ⟨hfin.toFinset.image rep, ?_⟩
  intro a ha
  have hex : ∃ a' ∈ S, sig a' = sig a := ⟨a, ha, rfl⟩
  have htS : rep (sig a) ∈ S ∧ sig (rep (sig a)) = sig a := by
    simp only [rep, dif_pos hex]
    exact hex.choose_spec
  refine ⟨rep (sig a), Finset.mem_image.mpr ⟨sig a, hfin.mem_toFinset.mpr ⟨a, ha, rfl⟩, rfl⟩, ?_⟩
  set t := rep (sig a) with ht
  have hat := hbb0 a ha
  have htt := hbb0 t htS.1
  let c : K' := bb a / bb t
  have hc : c ^ q = algebraMap K K' ((a : K) / (t : K)) := by
    rw [map_div₀, hbb a ha, hbb t htS.1, div_pow]
  have hd : (a : K) / (t : K) ≠ 0 := div_ne_zero a.ne_zero t.ne_zero
  have hfix : ∀ σ : K' →ₐ[K] AlgebraicClosure K, σ c = σ₀ c := by
    intro σ
    have e := congrFun htS.2 σ
    simp only [sig] at e
    have h1 : σ (bb t) ≠ 0 := (map_ne_zero σ).mpr htt
    have h2 : σ₀ (bb t) ≠ 0 := (map_ne_zero σ₀).mpr htt
    have h3 : σ₀ (bb a) ≠ 0 := (map_ne_zero σ₀).mpr hat
    simp only [c, map_div₀]
    rw [div_eq_div_iff h1 h2]
    rw [div_eq_div_iff h2 h3] at e
    linear_combination -e
  obtain ⟨e, he⟩ := mem_range_of_fixed q hq σ₀ c _ hd hc hfix
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [map_zero] at he
    exact div_ne_zero hat htt he.symm
  refine ⟨Units.mk0 e he0, ?_⟩
  ext
  apply (algebraMap K K').injective
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, map_mul, map_pow, he, hc, map_div₀]
  have : algebraMap K K' (t : K) ≠ 0 := (map_ne_zero _).mpr t.ne_zero
  field_simp
end

open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

private theorem functionField_isAlgebraic_of_tower (k K K' : Type) [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
    [Algebra K K'] [IsScalarTower k K K'] [IsFunctionField k K] [IsFunctionField k K'] :
    Algebra.IsAlgebraic K K' := by
  have h := trdeg_add_eq k K (A := K')
  rw [trdeg_eq_one (k := k) (K := K), trdeg_eq_one (k := k) (K := K')] at h
  have hfin : Algebra.trdeg K K' < Cardinal.aleph0 :=
    lt_of_le_of_lt (h ▸ le_add_self) Cardinal.one_lt_aleph0
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hfin
  rw [hn] at h
  have hn0 : n = 0 := by
    have : ((1 + n : ℕ) : Cardinal) = ((1 : ℕ) : Cardinal) := by push_cast; exact h
    have := Nat.cast_injective this
    omega
  rw [← trdeg_eq_zero_iff, hn, hn0, Nat.cast_zero]

theorem UpperTheory.finite_kummerSelmer_of_finite_extension :
    ∀ (k K K' : Type) [Field k] [IsAlgClosed k] [Field K] [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] [IsFunctionField k K] [IsFunctionField k K'] (q : ℕ) [NeZero q], IsUnit (q : k) → FinCls q (SelAll k K' q) → FinCls q (SelAll k K q) := by
  classical
  intro k K K' _ _ _ _ _ _ _ _ _ _ q _ hq hK'
  have := functionField_isAlgebraic_of_tower k K K'
  have : Algebra.EssFiniteType k K' := essFiniteType
  have : Algebra.EssFiniteType K K' := Algebra.EssFiniteType.of_comp k K K'
  have : Module.Finite K K' := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have : NeZero (q : k) := ⟨hq.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k q
  obtain ⟨T0, hT0⟩ := UpperTheory.finite_kernel_powClasses_of_primitive_root K K' q
    ⟨algebraMap k K ζ, hζ.map_of_injective (algebraMap k K).injective⟩
  obtain ⟨T', hT'⟩ := hK'
  let φ : Kˣ →* K'ˣ := Units.map (algebraMap K K' : K →* K')
  have hφ : ∀ x : Kˣ, ((φ x : K'ˣ) : K') = algebraMap K K' (x : K) := fun x => rfl
  have himg : ∀ f ∈ SelAll k K q, φ f ∈ SelAll k K' q := by
    intro f hf w
    have hw := (Place.liesOver_comap w).ord_algebraMap (f : K)
    show (q : ℤ) ∣ w.ord ((φ f : K'ˣ) : K')
    rw [hφ, hw]
    exact Dvd.dvd.mul_left (hf _) _
  let g : K'ˣ → Kˣ := fun t' =>
    if h : ∃ f ∈ SelAll k K q, ∃ u : K'ˣ, φ f = t' * u ^ q then h.choose else 1
  refine ⟨Finset.image₂ (· * ·) (T'.image g) T0, ?_⟩
  intro f hf
  obtain ⟨t', ht', u, hu⟩ := hT' (φ f) (himg f hf)
  have hex : ∃ f ∈ SelAll k K q, ∃ u : K'ˣ, φ f = t' * u ^ q := ⟨f, hf, u, hu⟩
  have hg : g t' = hex.choose := dif_pos hex
  obtain ⟨_, u0, hu0⟩ := hex.choose_spec
  set f0 := hex.choose
  have hmem : f * f0⁻¹ ∈ {a : Kˣ | ∃ b : K', algebraMap K K' (a : K) = b ^ q} := by
    refine ⟨((u * u0⁻¹ : K'ˣ) : K'), ?_⟩
    rw [← hφ, map_mul, map_inv, hu, hu0]
    push_cast
    rw [mul_pow, inv_pow]
    field_simp
  obtain ⟨s, hs, w, hw⟩ := hT0 _ hmem
  refine ⟨f0 * s, Finset.mem_image₂.mpr ⟨f0, Finset.mem_image.mpr ⟨t', ht', hg⟩, s, hs, rfl⟩, w, ?_⟩
  rw [mul_assoc, ← hw, mul_comm f, mul_inv_cancel_left]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.FinitePicTorsionOfFiniteKummerSelmer
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

private theorem finite_bad_places (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
    [Algebra.FiniteType k B] [IsFunctionField k (FractionRing B)] :
    {v : Place k (FractionRing B) | ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring}.Finite := by
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k B).FG)
  refine (Set.Finite.biUnion s.finite_toSet (fun g _ =>
    Place.finite_ord_ne_zero (k := k) (algebraMap B (FractionRing B) g))).subset ?_
  intro v hv
  by_contra hcon
  apply hv
  simp only [Set.mem_iUnion, not_exists] at hcon
  have hmem : ∀ g ∈ s, algebraMap B (FractionRing B) g ∈ v.ring := by
    intro g hg
    by_cases g0 : algebraMap B (FractionRing B) g = 0
    · rw [g0]; exact zero_mem _
    · have h0 : v.ord (algebraMap B (FractionRing B) g) = 0 := by
        by_contra hne
        exact hcon g hg hne
      exact (v.ord_nonneg_iff g0).1 h0.ge
  intro b
  have hb : b ∈ Algebra.adjoin k (s : Set B) := hs ▸ Algebra.mem_top
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact hmem x hx
  | algebraMap r =>
    rw [← IsScalarTower.algebraMap_apply k B (FractionRing B)]
    exact v.algebraMap_mem r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

private theorem dvd_ord_of_mem_sel (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
    [IsFunctionField k (FractionRing B)] (q : ℕ) (v : Place k (FractionRing B))
    (hv : ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring) (f : (FractionRing B)ˣ)
    (hf : f ∈ LateralTheory.E.LeafPicCut.sel B q) : (q : ℤ) ∣ v.ord (f : FractionRing B) := by
  have hk : ∀ c : k, algebraMap k (FractionRing B) c ∈ (algebraMap B (FractionRing B)).range :=
    fun c => ⟨algebraMap k B c, (IsScalarTower.algebraMap_apply k B (FractionRing B) c).symm⟩
  obtain ⟨I, hI⟩ := hf
  have hvP := Place.ofHeightOneSpectrum_center B hk v hv
  have hval := Place.valuation_ofHeightOneSpectrum B hk (Place.center B v hv)
  rw [hvP] at hval
  have h1 := v.valuation_eq_exp_neg_ord f.ne_zero
  rw [hval, GlobalTheory.Idele.valuation_eq_exp_neg_count _ f.ne_zero, WithZero.exp_inj, neg_inj] at h1
  have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors B) (f : FractionRing B) =
      ((I : FractionalIdeal (nonZeroDivisors B) (FractionRing B))) ^ q := by
    have := congrArg (fun J : (FractionalIdeal (nonZeroDivisors B) (FractionRing B))ˣ =>
      (J : FractionalIdeal (nonZeroDivisors B) (FractionRing B))) hI
    simpa using this.symm
  rw [hspan, FractionalIdeal.count_pow] at h1
  exact ⟨_, h1.symm⟩

theorem UpperTheory.finite_pic_torsion_of_finite_kummerSelmer :
    LateralTheory.E.LeafPicCut.LeafSelPic → ∀ (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] [IsFunctionField k (FractionRing B)] (q : ℕ) [NeZero q], FinCls q (SelAll k (FractionRing B) q) → Finite {c : CommRing.Pic B // c ^ q = 1} := by
  intro hS k B _ _ _ _ _ _ q _ hT
  have hfin : Finite (LateralTheory.E.LeafPicCut.selQ B q) := by
    have : Finite {v : Place k (FractionRing B) |
        ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring} := (finite_bad_places k B).to_subtype
    let φ : LateralTheory.E.LeafPicCut.sel B q →
        ({v : Place k (FractionRing B) | ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring} → ZMod q) :=
      fun f v => ((v.1.ord ((f.1 : (FractionRing B)ˣ) : FractionRing B) : ℤ) : ZMod q)
    let r := Function.invFun φ
    have hall : ∀ f : LateralTheory.E.LeafPicCut.sel B q,
        (f.1 / (r (φ f)).1 : (FractionRing B)ˣ) ∈ SelAll k (FractionRing B) q := by
      intro f v
      have hdiv : v.ord (((f.1 / (r (φ f)).1 : (FractionRing B)ˣ)) : FractionRing B) =
          v.ord (f.1 : FractionRing B) - v.ord ((r (φ f)).1 : FractionRing B) := by
        rw [Units.val_div_eq_div_val, v.ord_div f.1.ne_zero (r (φ f)).1.ne_zero]
      rw [hdiv]
      by_cases hv : ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring
      · exact dvd_sub (dvd_ord_of_mem_sel k B q v hv _ f.2) (dvd_ord_of_mem_sel k B q v hv _ (r (φ f)).2)
      · have h := congrFun (Function.invFun_eq (f := φ) ⟨f, rfl⟩) ⟨v, hv⟩
        exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h
    obtain ⟨T, hT⟩ := hT
    choose t ht u hu using fun f => hT _ (hall f)
    refine Finite.of_injective (β := ({v : Place k (FractionRing B) |
        ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring} → ZMod q) × T)
      (fun x => (φ x.out, ⟨t x.out, ht x.out⟩)) ?_
    intro x y hxy
    have h1 : φ x.out = φ y.out := congrArg Prod.fst hxy
    have h2 : t x.out = t y.out := congrArg (fun p => (p.2 : T).1) hxy
    have hx := hu x.out
    have hy := hu y.out
    rw [div_eq_iff_eq_mul'] at hx hy
    rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' y, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    refine ⟨(u x.out)⁻¹ * u y.out, ?_⟩
    simp only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hx, hy, h1, h2, mul_pow, inv_pow]
    group
  have key : Finite {c : ClassGroup B // c ^ q = 1} := hS B q hfin
  exact Finite.of_equiv _ (@Equiv.subtypeEquiv _ _ (fun c : ClassGroup B => c ^ q = 1) (fun c : CommRing.Pic B => c ^ q = 1)
    (ClassGroup.equivPic B).toEquiv (fun c => by
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_pow, MulEquiv.map_eq_one_iff]))
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.curve_picard_of_selmerPicard_of_modelCurve :
    LateralTheory.E.LeafPicCut.LeafSelPic → LateralTheory.E.LeafCurveVCut.LeafModelCurve → LateralTheory.E.E4.LeafPic := by
  intro hSel hModel hH q _ k B _ _ _ _ _ _ hq
  by_cases hB : IsField B
  · letI := hB.toField
    haveI : Subsingleton (CommRing.Pic B) := inferInstance
    exact Finite.of_subsingleton
  · haveI hK : IsFunctionField k (FractionRing B) := UpperTheory.isFunctionField_fractionRing_of_dedekind_finiteType k B hB
    obtain ⟨u, hu, hfd⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := FractionRing B)
    obtain ⟨C0, c0, x, ψ, hc, hx, hψ⟩ := hModel k (FractionRing B) u hu hfd
    haveI : IsIntegral C0 := hc.1
    obtain rfl : x = genericPoint C0 := hx.eq (genericPoint_spec C0)
    letI : Algebra k C0.functionField :=
      (CommRingCat.ofHom (algebraMap k (FractionRing B)) ≫ Spec.preimage ψ).hom.toAlgebra
    letI : Algebra (FractionRing B) C0.functionField := (Spec.preimage ψ).hom.toAlgebra
    haveI : IsScalarTower k (FractionRing B) C0.functionField := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have heq : Spec.map (CommRingCat.ofHom (algebraMap k C0.functionField)) =
        C0.fromSpecStalk (genericPoint C0) ≫ c0 := by
      change Spec.map (CommRingCat.ofHom (algebraMap k (FractionRing B)) ≫ Spec.preimage ψ) = _
      rw [Spec.map_comp, Spec.map_preimage, hψ]
    obtain ⟨hF, hch⟩ := UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit hH q k hq c0 hc heq
    haveI := hF
    exact UpperTheory.finite_pic_torsion_of_finite_kummerSelmer hSel k B q
      (UpperTheory.finite_kummerSelmer_of_finite_extension k (FractionRing B) C0.functionField q hq (UpperTheory.finite_kummerSelmer_of_charts k _ q hch))
