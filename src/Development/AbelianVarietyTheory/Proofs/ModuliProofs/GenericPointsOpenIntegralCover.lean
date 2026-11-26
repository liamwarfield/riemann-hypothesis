module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyMorphismFromVeryDenseGraphs
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardBasisPolarisationPowerZeroEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverBaseChangeOfProperQuasiProjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteFlatSurjectiveMulByNAbelianScheme

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCompleteDVRPointGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCompleteDVRPointGenericPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.GenTrait

theorem charZero_functionField (Z : Scheme.{0}) [IsIntegral Z] (W : Type) [CommRing W] [CharZero W]
    (f : Sp W ⟶ Z) : CharZero Z.functionField := by
  have h1 : CharZero Γ(Z, ⊤) :=
    RingHom.charZero (f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  exact charZero_of_injective_ringHom (Z.germToFunctionField_injective ⊤)

theorem exists_trait_genericPoint : ∀ (Z : Scheme.{0}) [IsIntegral Z] (W : Type) [CommRing W] [IsDomain W] [CharZero W] (_ : Sp W ⟶ Z), ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R), GlobalTheory.LN.CDvr R ∧ ∃ χ : Sp R ⟶ Z, ∀ y, χ y = genericPoint Z := by
  intro Z _ W _ _ _ f
  have := charZero_functionField Z W f
  refine ⟨PowerSeries Z.functionField, inferInstance, inferInstance, inferInstance, ?_,
    spMap (algebraMap Z.functionField (PowerSeries Z.functionField)) ≫
      Z.fromSpecStalk (genericPoint Z), fun y => ?_⟩
  · exact ⟨inferInstance, by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance,
      algebraRat.charZero _⟩
  · rw [Scheme.Hom.comp_apply]
    have hy : ∀ p : PrimeSpectrum Z.functionField, p = IsLocalRing.closedPoint Z.functionField :=
      fun p => Subsingleton.elim _ _
    exact (congrArg (Z.fromSpecStalk (genericPoint Z)) (hy _)).trans
      Scheme.fromSpecStalk_closedPoint

end GlobalTheory.GenTrait
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCompleteDVRPointGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_point_genericPoint : ∀ (Z : Scheme.{0}) [IsIntegral Z] (W : Type) [CommRing W] [IsDomain W] [CharZero W] (_ : Sp W ⟶ Z), ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R), GlobalTheory.LN.CDvr R ∧ ∃ χ : Sp R ⟶ Z, ∀ y, χ y = genericPoint Z := by
  first | exact @GlobalTheory.GenTrait.exists_trait_genericPoint | exact GlobalTheory.GenTrait.exists_trait_genericPoint | (intros; apply GlobalTheory.GenTrait.exists_trait_genericPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAmpleCechLineBundleDisjointUnionPushforward
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAmpleCechLineBundleDisjointUnionPushforward
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.ModelSum

noncomputable section

namespace GlobalTheory.ModelSum.UnionAmple

variable {Z Z' : Scheme.{0}}

theorem gs_eq_stalkMap (r : Z' ⟶ Z) (z : Z') (U : Z.Opens) (h : r z ∈ U) (a : Γ(Z, U)) :
    gs r z U a = (r.stalkMap z).hom (gs (𝟙 Z) (r z) U a) := by
  rw [gs_eq r z U h, gs_eq (𝟙 Z) (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r U z h a).symm

theorem gs_id_of_gs (f : Z' ⟶ Z) [IsOpenImmersion f] (y : Z') {U : Z.Opens} (h : f y ∈ U) {a b : Γ(Z, U)}
    (e : gs f y U a = gs f y U b) : gs (𝟙 Z) (f y) U a = gs (𝟙 Z) (f y) U b := by
  rw [gs_eq_stalkMap f y U h, gs_eq_stalkMap f y U h] at e
  exact (ConcreteCategory.bijective_of_isIso (f.stalkMap y)).1 e

theorem gm_id_of_gm (f : Z' ⟶ Z) [IsOpenImmersion f] (y : Z') {U : Z.Opens} (h : f y ∈ U) {a b : Γ(Z, U)ˣ}
    (e : gm f y U a = gm f y U b) : gm (𝟙 Z) (f y) U a = gm (𝟙 Z) (f y) U b := by
  apply Units.ext
  rw [← gs_unit (𝟙 Z) (f y) U h, ← gs_unit (𝟙 Z) (f y) U h]
  apply gs_id_of_gs f y h
  rw [gs_unit f y U h, gs_unit f y U h, e]

theorem gs_push (f : Z' ⟶ Z) [IsOpenImmersion f] (y : Z') {U : Z'.Opens} (h : y ∈ U) (a : Γ(Z', U)) :
    gs f y (f ''ᵁ U) ((f.appIso U).inv.hom a) = gs (𝟙 Z') y U a := by
  have h' : f y ∈ f ''ᵁ U := ⟨y, h, rfl⟩
  have e : (f.app (f ''ᵁ U)).hom ((f.appIso U).inv.hom a) =
      (Z'.presheaf.map (homOfLE (f.preimage_image_eq U).le).op).hom a :=
    congrArg (fun q => q.hom a) (f.appIso_inv_app U)
  rw [← gs_res (𝟙 Z') y (f.preimage_image_eq U).le h' a, ← e, gs_pull (𝟙 Z') f y (f ''ᵁ U) h', Category.id_comp]

structure Part (f : Z' ⟶ Z) (A : LB Z') (C : LB Z) (e : A.ι → C.ι) : Prop where
  inj : Function.Injective e
  mem : ∀ i y, f y ∈ C.U (e i) ↔ y ∈ A.U i
  sub : ∀ i x, x ∈ C.U (e i) → x ∈ Set.range f
  surj : ∀ p y, f y ∈ C.U p → ∃ i, e i = p
  g : ∀ i j y, y ∈ A.U i → y ∈ A.U j →
    gm f y (C.U (e i) ⊓ C.U (e j)) (C.g (e i) (e j)) = gm (𝟙 Z') y (A.U i ⊓ A.U j) (A.g i j)

theorem gm_pushLB (f : Z' ⟶ Z) [IsOpenImmersion f] (A : LB Z') (i j : A.ι) (y : Z') (hi : y ∈ A.U i) (hj : y ∈ A.U j) :
    gm f y (f ''ᵁ A.U i ⊓ f ''ᵁ A.U j) ((pushLB f A).g i j) = gm (𝟙 Z') y (A.U i ⊓ A.U j) (A.g i j) := by
  have hm : f y ∈ f ''ᵁ A.U i ⊓ f ''ᵁ A.U j := ⟨⟨y, hi, rfl⟩, ⟨y, hj, rfl⟩⟩
  have hm' : y ∈ A.U i ⊓ A.U j := ⟨hi, hj⟩
  refine (gm_res f y _ hm _).trans (Units.ext ?_)
  exact (gs_unit f y _ (image_inf_le f _ _ hm) _).symm.trans ((gs_push f y hm' _).trans (gs_unit _ y _ hm' _))

theorem part_left (f : Z' ⟶ Z) [IsOpenImmersion f] (A : LB Z') (B : LB Z) (hB : ∀ p y, f y ∉ B.U p) :
    Part f A (sumLB (pushLB f A) B) Sum.inl := by
  refine ⟨Sum.inl_injective, ?_, ?_, ?_, gm_pushLB f A⟩
  · intro i y
    exact f.apply_mem_image_iff
  · rintro i x ⟨y, _, hy⟩
    exact ⟨y, hy⟩
  · intro p y hp
    rcases p with i | p
    · exact ⟨i, rfl⟩
    · exact (hB p y hp).elim

theorem part_right (f : Z' ⟶ Z) [IsOpenImmersion f] (A : LB Z') (B : LB Z) (hB : ∀ p y, f y ∉ B.U p) :
    Part f A (sumLB B (pushLB f A)) Sum.inr := by
  refine ⟨Sum.inr_injective, ?_, ?_, ?_, gm_pushLB f A⟩
  · intro i y
    exact f.apply_mem_image_iff
  · rintro i x ⟨y, _, hy⟩
    exact ⟨y, hy⟩
  · intro p y hp
    rcases p with p | i
    · exact (hB p y hp).elim
    · exact ⟨i, rfl⟩

variable {f : Z' ⟶ Z} {A : LB Z'} {C : LB Z} {e : A.ι → C.ι}

theorem Part.cocycle (h : Part f A C e) (hA : A.IsLB) (y : Z') {p q r : C.ι} (hp : f y ∈ C.U p) (hq : f y ∈ C.U q)
    (hr : f y ∈ C.U r) : gm f y _ (C.g p q) * gm f y _ (C.g q r) = gm f y _ (C.g p r) := by
  obtain ⟨i, rfl⟩ := h.surj p y hp
  obtain ⟨j, rfl⟩ := h.surj q y hq
  obtain ⟨k, rfl⟩ := h.surj r y hr
  rw [h.mem] at hp hq hr
  rw [h.g _ _ _ hp hq, h.g _ _ _ hq hr, h.g _ _ _ hp hr]
  exact gm_cocycle hA (𝟙 Z') y hp hq hr

theorem mem_wchart {X : Scheme.{0}} (L : LB X) (J : Fin 1 → L.ι) (x : X) :
    x ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) J ↔ x ∈ L.U (J 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem gs_zero' {X Y : Scheme.{0}} (r : Y ⟶ X) (z : Y) (U : X.Opens) : gs r z U 0 = 0 := by
  by_cases h : r z ∈ U
  · rw [gs_eq r z U h, map_zero, map_zero]
  · exact dif_neg h

theorem Part.exists_local [IsOpenImmersion f] (h : Part f A C e) {d : ℕ} (s : H0 A d) (J : Fin 1 → C.ι) :
    ∃ t : Γ(Z, LB.wchart C (fun _ : Fin 1 => 𝟙 Z) J),
      (∀ i y, e i = J 0 → y ∈ A.U i → gs f y _ t = gs (𝟙 Z') y _ (s.f fun _ => i)) ∧
      ∀ x, x ∉ Set.range f → gs (𝟙 Z) x _ t = 0 := by
  by_cases hJ : ∃ i, e i = J 0
  · obtain ⟨i, hi⟩ := hJ
    have le : LB.wchart C (fun _ : Fin 1 => 𝟙 Z) J ≤ f ''ᵁ LB.wchart A (fun _ : Fin 1 => 𝟙 Z') fun _ => i := by
      intro x hx
      have hx' := (mem_wchart C J x).1 hx
      rw [← hi] at hx'
      obtain ⟨y, rfl⟩ := h.sub i x hx'
      exact ⟨y, (mem_wchart A _ y).2 ((h.mem i y).1 hx'), rfl⟩
    refine ⟨(Z.presheaf.map (homOfLE le).op).hom ((f.appIso _).inv.hom (s.f fun _ => i)), fun i' y hi' hy => ?_,
      fun x hx => dif_neg fun hx' => hx ?_⟩
    · obtain rfl : i' = i := h.inj (hi'.trans hi.symm)
      have hm : f y ∈ LB.wchart C (fun _ : Fin 1 => 𝟙 Z) J :=
        (mem_wchart C J _).2 (hi ▸ (h.mem i' y).2 hy)
      exact (gs_res f y le hm _).trans (gs_push f y ((mem_wchart A _ y).2 hy) _)
    · obtain ⟨y, -, hy⟩ := le hx'
      exact ⟨y, hy⟩
  · exact ⟨0, fun i y hi _ => (hJ ⟨i, hi⟩).elim, fun x _ => gs_zero' _ _ _⟩

theorem Part.exists_sec [IsOpenImmersion f] (h : Part f A C e) {d : ℕ} (s : H0 A d) :
    ∃ t : H0 C d, nonzeroLocus t = f ''ᵁ nonzeroLocus s := by
  choose t ht h0 using h.exists_local s
  refine ⟨⟨t, fun J J' => fn_ext fun x hx => ?_⟩, ?_⟩
  · by_cases hf : x ∈ Set.range f
    · obtain ⟨y, rfl⟩ := hf
      apply gs_id_of_gs f y hx
      have h1 := (mem_wchart C J _).1 hx.1
      have h2 := (mem_wchart C J' _).1 hx.2
      obtain ⟨i, hi⟩ := h.surj _ y h1
      obtain ⟨i', hi'⟩ := h.surj _ y h2
      have k1 : y ∈ A.U i := (h.mem i y).1 (hi ▸ h1)
      have k2 : y ∈ A.U i' := (h.mem i' y).1 (hi' ▸ h2)
      have w1 := (mem_wchart A (fun _ => i) y).2 k1
      have w2 := (mem_wchart A (fun _ => i') y).2 k2
      have hm : (𝟙 Z' : Z' ⟶ Z') y ∈ LB.wchart A (fun _ : Fin 1 => 𝟙 Z') (fun _ => i) ⊓
        LB.wchart A (fun _ : Fin 1 => 𝟙 Z') (fun _ => i') := ⟨w1, w2⟩
      have c := congrArg (gs (𝟙 Z') y _) (s.compat (fun _ => i) (fun _ => i'))
      have c' := (gs_res (𝟙 Z') y inf_le_left hm _).symm.trans (c.trans ((gs_mul _ y _ hm _ _).trans
        (congrArg₂ (· * ·) ((gs_unit _ y _ hm _).trans
          (congrArg Units.val (gm_linComb A _ _ (𝟙 Z') y _ _ w1 w2))) (gs_res (𝟙 Z') y inf_le_right hm _))))
      refine ((gs_res f y inf_le_left hx _).trans (ht J i y hi k1)).trans (c'.trans (Eq.symm ?_))
      refine (gs_mul f y _ hx _ _).trans (congrArg₂ (· * ·) ((gs_unit f y _ hx _).trans
        (congrArg Units.val ((gm_linComb C _ _ f y J J' hx.1 hx.2).trans ?_)))
        ((gs_res f y inf_le_right hx _).trans (ht J' i' y hi' k2)))
      refine Finset.prod_congr rfl fun k _ => congrArg (· ^ (d : ℤ)) ?_
      obtain rfl : k = 0 := Subsingleton.elim _ _
      rw [Category.comp_id, Category.comp_id, ← hi, ← hi']
      exact h.g i i' y k1 k2
    · refine ((gs_res _ x inf_le_left hx _).trans (h0 J x hf)).trans (Eq.symm ?_)
      refine (gs_mul _ x _ hx _ _).trans ?_
      exact mul_eq_zero_of_right _ ((gs_res _ x inf_le_right hx _).trans (h0 J' x hf))
  · have key : ∀ (J : Fin 1 → C.ι) (y : Z'), f y ∈ LB.wchart C (fun _ : Fin 1 => 𝟙 Z) J →
        (f y ∈ Z.basicOpen (t J) ↔ IsUnit (gs f y _ (t J))) := fun J y hy => by
      rw [gs_eq_stalkMap f y _ hy, isUnit_map_iff, gs_eq (𝟙 Z) (f y) _ hy]
      exact Z.mem_basicOpen _ _ hy
    have key' : ∀ (j : Fin 1 → A.ι) (y : Z') (hy : y ∈ LB.wchart A (fun _ : Fin 1 => 𝟙 Z') j),
        (y ∈ Z'.basicOpen (s.f j) ↔ IsUnit (gs (𝟙 Z') y _ (s.f j))) := fun j y hy => by
      exact (Z'.mem_basicOpen _ _ hy).trans (iff_of_eq (congrArg IsUnit (gs_eq (𝟙 Z') y _ hy (s.f j)).symm))
    ext x
    constructor
    · intro hx
      obtain ⟨J, hJ⟩ := Opens.mem_iSup.1 hx
      have hw : x ∈ LB.wchart C (fun _ : Fin 1 => 𝟙 Z) J := Z.basicOpen_le _ hJ
      by_cases hf : x ∈ Set.range f
      · obtain ⟨y, rfl⟩ := hf
        have h1 := (mem_wchart C J _).1 hw
        obtain ⟨i, hi⟩ := h.surj _ y h1
        have k1 : y ∈ A.U i := (h.mem i y).1 (hi ▸ h1)
        have u := (key J y hw).1 hJ
        rw [ht J i y hi k1] at u
        exact ⟨y, Opens.mem_iSup.2 ⟨fun _ => i, (key' _ y ((mem_wchart A _ y).2 k1)).2 u⟩, rfl⟩
      · have u : IsUnit (gs (𝟙 Z) x _ (t J)) := by
          rw [gs_eq (𝟙 Z) x _ hw]
          exact (Z.mem_basicOpen _ _ hw).1 hJ
        rw [h0 J x hf] at u
        exact (not_isUnit_zero u).elim
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hy
      obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
      have hw : y ∈ LB.wchart A (fun _ : Fin 1 => 𝟙 Z') (fun _ => i) := Z'.basicOpen_le _ hj
      have k1 : y ∈ A.U i := (mem_wchart A _ y).1 hw
      have u := (key' _ y hw).1 hj
      rw [← ht (fun _ => e i) i y rfl k1] at u
      exact Opens.mem_iSup.2 ⟨fun _ => e i, (key _ y ((mem_wchart C _ _).2 ((h.mem i y).2 k1))).2 u⟩

theorem Part.ample_at [IsOpenImmersion f] (h : Part f A C e) (ha : AmpleFam A) (y : Z') :
    ∃ (d : ℕ) (s : H0 C d), 1 ≤ d ∧ f y ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s) := by
  obtain ⟨d, s, hd, hy, haf⟩ := ha y
  obtain ⟨t, ht⟩ := h.exists_sec s
  refine ⟨d, t, hd, ?_, ?_⟩
  · rw [ht]; exact ⟨y, hy, rfl⟩
  · rw [ht]; exact haf.image_of_isOpenImmersion f

theorem sumLB_isLB_ampleFam : ∀ (Z Z₁ Z₂ : Scheme.{0}) (f₁ : Z₁ ⟶ Z) (f₂ : Z₂ ⟶ Z) [IsOpenImmersion f₁]
    [IsOpenImmersion f₂] (A₁ : LB Z₁) (A₂ : LB Z₂), IsCompl (Set.range f₁) (Set.range f₂) → A₁.IsLB → A₂.IsLB →
    AmpleFam A₁ → AmpleFam A₂ →
    (sumLB (pushLB f₁ A₁) (pushLB f₂ A₂)).IsLB ∧ AmpleFam (sumLB (pushLB f₁ A₁) (pushLB f₂ A₂)) := by
  intro Z Z₁ Z₂ f₁ f₂ _ _ A₁ A₂ hc h₁ h₂ a₁ a₂
  have dj : ∀ y₁ y₂, f₁ y₁ ≠ f₂ y₂ := fun y₁ y₂ e =>
    Set.disjoint_left.1 hc.disjoint ⟨y₁, rfl⟩ ⟨y₂, e.symm⟩
  have cov : ∀ x : Z, (∃ y, f₁ y = x) ∨ ∃ y, f₂ y = x := fun x =>
    show x ∈ Set.range f₁ ⊔ Set.range f₂ from hc.sup_eq_top.ge trivial
  have P₁ := part_left f₁ A₁ (pushLB f₂ A₂) fun p y ⟨y', _, e⟩ => dj y y' e.symm
  have P₂ := part_right f₂ A₂ (pushLB f₁ A₁) fun p y ⟨y', _, e⟩ => dj y' y e
  set C := sumLB (pushLB f₁ A₁) (pushLB f₂ A₂)
  have co : ∀ (x : Z) (p q r : C.ι), x ∈ C.U p → x ∈ C.U q → x ∈ C.U r →
      gm (𝟙 Z) x _ (C.g p q) * gm (𝟙 Z) x _ (C.g q r) = gm (𝟙 Z) x _ (C.g p r) := by
    intro x p q r hp hq hr
    have hm : x ∈ C.U p ⊓ C.U q ⊓ C.U r := ⟨⟨hp, hq⟩, hr⟩
    have l1 : C.U p ⊓ C.U q ⊓ C.U r ≤ C.U p ⊓ C.U q := inf_le_left
    have l2 : C.U p ⊓ C.U q ⊓ C.U r ≤ C.U q ⊓ C.U r := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have l3 : C.U p ⊓ C.U q ⊓ C.U r ≤ C.U p ⊓ C.U r := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    rw [← gm_res (𝟙 Z) x l1 hm, ← gm_res (𝟙 Z) x l2 hm, ← gm_res (𝟙 Z) x l3 hm, ← map_mul]
    rcases cov x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · apply gm_id_of_gm f₁ y hm
      rw [map_mul, gm_res _ y l1 hm, gm_res _ y l2 hm, gm_res _ y l3 hm]
      exact P₁.cocycle h₁ y hp hq hr
    · apply gm_id_of_gm f₂ y hm
      rw [map_mul, gm_res _ y l1 hm, gm_res _ y l2 hm, gm_res _ y l3 hm]
      exact P₂.cocycle h₂ y hp hq hr
  refine ⟨⟨top_le_iff.1 fun x _ => ?_, fun p => unit_ext fun x hx => ?_, fun p q r => unit_ext fun x hx => ?_⟩,
    fun x => ?_⟩
  · rcases cov x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · obtain ⟨i, hi⟩ := exists_chart h₁ y
      exact Opens.mem_iSup.2 ⟨_, (P₁.mem i y).2 hi⟩
    · obtain ⟨i, hi⟩ := exists_chart h₂ y
      exact Opens.mem_iSup.2 ⟨_, (P₂.mem i y).2 hi⟩
  · rw [gm_res _ x _ hx, map_one]
    exact mul_eq_left.1 (co x p p p hx hx hx)
  · rw [map_mul, gm_res _ x _ hx, gm_res _ x _ hx, gm_res _ x _ hx]
    exact co x p q r hx.1.1 hx.1.2 hx.2
  · rcases cov x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact P₁.ample_at a₁ y
    · exact P₂.ample_at a₂ y

end GlobalTheory.ModelSum.UnionAmple

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAmpleCechLineBundleDisjointUnionPushforwardStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmpleCechLineBundle_disjointUnion_pushforward : ∀ (Z Z₁ Z₂ : Scheme.{0}) (f₁ : Z₁ ⟶ Z) (f₂ : Z₂ ⟶ Z) [IsOpenImmersion f₁] [IsOpenImmersion f₂] (A₁ : LB Z₁) (A₂ : LB Z₂), IsCompl (Set.range f₁) (Set.range f₂) → A₁.IsLB → A₂.IsLB → AmpleFam A₁ → AmpleFam A₂ → (sumLB (pushLB f₁ A₁) (pushLB f₂ A₂)).IsLB ∧ AmpleFam (sumLB (pushLB f₁ A₁) (pushLB f₂ A₂)) := by
  first | exact @GlobalTheory.ModelSum.UnionAmple.sumLB_isLB_ampleFam | exact GlobalTheory.ModelSum.UnionAmple.sumLB_isLB_ampleFam | (intros; apply GlobalTheory.ModelSum.UnionAmple.sumLB_isLB_ampleFam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasTransitionCompatibleFramesOfNoCompleteDVRPoin
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasTransitionCompatibleFramesOfNoCompleteDVRPoin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ModelSum

def noTraitZero {X : Scheme.{0}} (M : LB X) : M.Sec := ⟨fun _ => 0, by simp⟩

theorem noTrait_gs_zero {Y X : Scheme.{0}} (r : Y ⟶ X) (y : Y) (U : X.Opens) : gs r y U 0 = 0 := by
  unfold gs
  split_ifs <;> simp

theorem lin_noTraitZero {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (c : Fin n → Γ(T'.left, ⊤)) : GlobalTheory.LN.Lin G L N h (fun _ => noTraitZero _) c (noTraitZero _) := by
  intro z J _
  refine (noTrait_gs_zero _ _ _).trans (Finset.sum_eq_zero fun i _ => ?_).symm
  exact (congrArg _ (noTrait_gs_zero _ _ _)).trans (mul_zero _)

theorem noTrait_exists_gl_det_eq {R : Type*} [CommRing R] {n : ℕ} (hn : 1 ≤ n) (u : Rˣ) :
    ∃ M : GL (Fin n) R, Matrix.GeneralLinearGroup.det M = u := by
  have hd : (Matrix.diagonal (Function.update (fun _ : Fin n => (1 : R)) ⟨0, hn⟩ u.val)).det = u.val := by
    rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  refine ⟨Matrix.GeneralLinearGroup.mk'' _ (by rw [hd]; exact u.isUnit), Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact hd

theorem hasFrames_rank_of_isEmpty (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A : LB Z) (n n' : ℕ) (r s : ℤ)
    (hn : 1 ≤ n') (hZ : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → IsEmpty (Sp W ⟶ Z))
    (h : HasFrames G L N A n r s) : HasFrames G L N A n' r s := by
  obtain ⟨th, b, h₁, -⟩ := h
  refine ⟨th, fun _ _ => noTraitZero _, fun i j => ?_, fun i W _ _ _ hW χ _ => ((hZ W hW).false (χ ≫ (A.U i).ι)).elim⟩
  obtain ⟨c, M, h₂, -, h₃⟩ := h₁ i j
  obtain ⟨M', hM⟩ := noTrait_exists_gl_det_eq hn (Matrix.GeneralLinearGroup.det M)
  exact ⟨c, M', h₂, fun k => ⟨noTraitZero _, lin_noTraitZero G L N _ _, lin_noTraitZero G L N _ _⟩, by rw [hM]; exact h₃⟩

end GlobalTheory.ModelSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasTransitionCompatibleFramesOfNoCompleteDVRPoinStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasTransitionCompatibleFrames_of_no_completeDVR_points : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A : LB Z) (n n' : ℕ) (r s : ℤ), 1 ≤ n' → (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → IsEmpty (Sp W ⟶ Z)) → HasFrames G L N A n r s → HasFrames G L N A n' r s := by
  first | exact @GlobalTheory.ModelSum.hasFrames_rank_of_isEmpty | exact GlobalTheory.ModelSum.hasFrames_rank_of_isEmpty | (intros; apply GlobalTheory.ModelSum.hasFrames_rank_of_isEmpty <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsComplOpenImmersions
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsComplOpenImmersions
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ProjSpace

private theorem isImmersion_coprod_map {X Y X' Y' : Scheme.{0}} (f : X ⟶ X') (g : Y ⟶ Y')
    [IsImmersion f] [IsImmersion g] : IsImmersion (coprod.map f g) := by
  refine IsZariskiLocalAtTarget.of_openCover (coprodOpenCover.{0, 0} X' Y') ?_
  rintro (⟨⟩ | ⟨⟩)
  · change IsImmersion (pullback.snd (coprod.map f g) coprod.inl)
    have h := (isPullback_inl_inl_coprodMap f g).flip
    rw [← Iso.inv_hom_id_assoc h.isoPullback (pullback.snd _ _), h.isoPullback_hom_snd]
    infer_instance
  · change IsImmersion (pullback.snd (coprod.map f g) coprod.inr)
    have h := (isPullback_inr_inr_coprodMap f g).flip
    rw [← Iso.inv_hom_id_assoc h.isoPullback (pullback.snd _ _), h.isoPullback_hom_snd]
    infer_instance

theorem _root_.GlobalTheory.ProjSpace.isQProjOver_of_isCompl : ∀ (R : Type) [CommRing R] (X X₁ X₂ : Scheme.{0})
    (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R), IsOpenImmersion f₁ → IsOpenImmersion f₂ →
    IsCompl (Set.range f₁) (Set.range f₂) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (f₁ ≫ s) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (f₂ ≫ s) →
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver s := by
  intro R _ X X₁ X₂ f₁ f₂ s h₁ h₂ hc q₁ q₂
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver at q₁ q₂ ⊢
  obtain ⟨N₁, i₁, hi₁, hq₁, e₁⟩ := q₁
  obtain ⟨N₂, i₂, hi₂, hq₂, e₂⟩ := q₂
  have hP := _root_.GlobalTheory.ProjSpace.isProjOver_coprodDesc (_root_.GlobalTheory.ProjSpace.isProjOver_pspace_str R N₁)
    (_root_.GlobalTheory.ProjSpace.isProjOver_pspace_str R N₂)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver at hP
  obtain ⟨M, j, hj, ej⟩ := hP
  have hc' : IsCompl f₁.opensRange f₂.opensRange :=
    ⟨disjoint_iff.mpr (SetLike.coe_injective (by simpa using hc.inf_eq_bot)),
      codisjoint_iff.mpr (SetLike.coe_injective (by simpa using hc.sup_eq_top))⟩
  obtain ⟨hX⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl f₁ f₂ hc'
  let e : X₁ ⨿ X₂ ≅ X := (coprodIsCoprod X₁ X₂).coconePointUniqueUpToIso hX
  have he₁ : coprod.inl ≫ e.hom = f₁ :=
    (coprodIsCoprod X₁ X₂).comp_coconePointUniqueUpToIso_hom hX ⟨WalkingPair.left⟩
  have he₂ : coprod.inr ≫ e.hom = f₂ :=
    (coprodIsCoprod X₁ X₂).comp_coconePointUniqueUpToIso_hom hX ⟨WalkingPair.right⟩
  have hcomp : (e.inv ≫ coprod.map i₁ i₂ ≫ j) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R M = s := by
    rw [Category.assoc, Category.assoc, ej, Iso.inv_comp_eq]
    apply coprod.hom_ext
    · rw [coprod.inl_map_assoc, coprod.inl_desc, ← Category.assoc, he₁, e₁]
    · rw [coprod.inr_map_assoc, coprod.inr_desc, ← Category.assoc, he₂, e₂]
  haveI := isImmersion_coprod_map i₁ i₂
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R M
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N₁
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N₂
  haveI : CompactSpace X₁ := (quasiCompact_iff_compactSpace (f₁ ≫ s)).mp (by rw [← e₁]; infer_instance)
  haveI : CompactSpace X₂ := (quasiCompact_iff_compactSpace (f₂ ≫ s)).mp (by rw [← e₂]; infer_instance)
  haveI : CompactSpace X := ⟨by
    rw [← Set.top_eq_univ, ← hc.sup_eq_top]
    exact (isCompact_range f₁.continuous).union (isCompact_range f₂.continuous)⟩
  haveI : QuasiCompact s := (quasiCompact_iff_compactSpace s).mpr inferInstance
  haveI : QuasiCompact ((e.inv ≫ coprod.map i₁ i₂ ≫ j) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R M) := by
    rw [hcomp]; infer_instance
  exact ⟨M, e.inv ≫ coprod.map i₁ i₂ ≫ j, inferInstance,
    QuasiCompact.of_comp _ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R M), hcomp⟩

end GlobalTheory.ProjSpace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsComplOpenImmersionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQProjOver_of_isCompl_openImmersions : ∀ (R : Type) [CommRing R] (X X₁ X₂ : Scheme.{0}) (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X) (s : X ⟶ Sp R), IsOpenImmersion f₁ → IsOpenImmersion f₂ → IsCompl (Set.range f₁) (Set.range f₂) → IsQProjOver (f₁ ≫ s) → IsQProjOver (f₂ ≫ s) → IsQProjOver s := by
  first | exact @GlobalTheory.ProjSpace.isQProjOver_of_isCompl | exact GlobalTheory.ProjSpace.isQProjOver_of_isCompl | (intros; apply GlobalTheory.ProjSpace.isQProjOver_of_isCompl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

noncomputable section

namespace GlobalTheory.ModelSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem range_desc {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Set.range (coprod.desc f g) = Set.range f ∪ Set.range g := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨x | x, rfl⟩ := (coprodMk _ _).surjective x
    · exact .inl ⟨x, by rw [coprodMk_inl, ← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
    · exact .inr ⟨x, by rw [coprodMk_inr, ← Scheme.Hom.comp_apply, coprod.inr_desc]⟩
  · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨(coprod.inl : X ⟶ X ⨿ Y) x, by rw [← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
    · exact ⟨(coprod.inr : Y ⟶ X ⨿ Y) x, by rw [← Scheme.Hom.comp_apply, coprod.inr_desc]⟩

theorem isOpenImmersion_desc {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (h : Disjoint (Set.range f) (Set.range g)) : IsOpenImmersion (coprod.desc f g) := by
  let α : ∀ i : ULift.{0} WalkingPair, (i.1.casesOn X Y : Scheme.{0}) ⟶ Z := fun i => match i with
    | ⟨.left⟩ => f
    | ⟨.right⟩ => g
  have : ∀ i, IsOpenImmersion (α i) := by rintro ⟨_ | _⟩ <;> assumption
  have h₁ : IsOpenImmersion (Sigma.desc α) := isOpenImmersion_sigmaDesc _ α (by
    rintro ⟨_ | _⟩ ⟨_ | _⟩ hij
    exacts [(hij rfl).elim, h, h.symm, (hij rfl).elim])
  have e : (coprodIsoSigma X Y).inv ≫ coprod.desc f g = Sigma.desc α := by
    refine Sigma.hom_ext _ _ ?_
    rintro ⟨_ | _⟩
    · rw [← Category.assoc, ι_left_coprodIsoSigma_inv, coprod.inl_desc, Sigma.ι_desc]
    · rw [← Category.assoc, ι_right_coprodIsoSigma_inv, coprod.inr_desc, Sigma.ι_desc]
  rw [(Iso.inv_comp_eq _).1 e]
  infer_instance

theorem isOpenImmersion_map {X Y X' Y' : Scheme.{0}} (f : X ⟶ X') (g : Y ⟶ Y') [IsOpenImmersion f] [IsOpenImmersion g] :
    IsOpenImmersion (coprod.map f g) := by
  have e : coprod.map f g = coprod.desc (f ≫ coprod.inl) (g ≫ coprod.inr) := by ext <;> simp
  rw [e]
  refine isOpenImmersion_desc _ _ (Set.disjoint_left.2 ?_)
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  exact inr_ne_inl _ _ (f x) (g y) hy

theorem isDominant_map {X Y X' Y' : Scheme.{0}} (f : X ⟶ X') (g : Y ⟶ Y') [IsDominant f] [IsDominant g] :
    IsDominant (coprod.map f g) := by
  refine ⟨fun z => ?_⟩
  obtain ⟨x | x, rfl⟩ := (coprodMk _ _).surjective z
  · rw [coprodMk_inl]
    refine closure_mono ?_ (image_closure_subset_closure_image (coprod.inl : X' ⟶ X' ⨿ Y').continuous
      ⟨x, f.denseRange x, rfl⟩)
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨(coprod.inl : X ⟶ X ⨿ Y) y, by rw [← Scheme.Hom.comp_apply, coprod.inl_map, Scheme.Hom.comp_apply]⟩
  · rw [coprodMk_inr]
    refine closure_mono ?_ (image_closure_subset_closure_image (coprod.inr : Y' ⟶ X' ⨿ Y').continuous
      ⟨x, g.denseRange x, rfl⟩)
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨(coprod.inr : Y ⟶ X ⨿ Y) y, by rw [← Scheme.Hom.comp_apply, coprod.inr_map, Scheme.Hom.comp_apply]⟩

theorem mem_inl_or_inr {X Y : Scheme.{0}} (z : (X ⨿ Y : Scheme.{0})) :
    z ∈ Set.range (coprod.inl : X ⟶ X ⨿ Y) ∨ z ∈ Set.range (coprod.inr : Y ⟶ X ⨿ Y) :=
  (isCompl_range_inl_inr X Y).sup_eq_top.ge (Set.mem_univ z)

theorem isNormalScheme_coprod {X Y : Scheme.{0}} (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (hY : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (X ⨿ Y) := by
  have key : ∀ {A : Scheme.{0}} (f : A ⟶ X ⨿ Y) [IsOpenImmersion f], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme A → ∀ a,
      IsDomain ((X ⨿ Y).presheaf.stalk (f a)) ∧ IsIntegrallyClosed ((X ⨿ Y).presheaf.stalk (f a)) := by
    intro A f _ hA a
    obtain ⟨h₁, h₂⟩ := hA a
    let e := (asIso (f.stalkMap a)).commRingCatIsoToRingEquiv
    exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩
  intro z
  obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ := mem_inl_or_inr z
  exacts [key _ hX x, key _ hY x]

theorem isReduced_of_isNormalScheme {X : Scheme.{0}} (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : IsReduced X :=
  have := fun x => (hX x).1
  isReduced_of_isReduced_stalk X

theorem noetherianSpace_of_isProjOver {O : Type} [CommRing O] [IsNoetherianRing O] {Z : Scheme.{0}} {s : Z ⟶ Sp O}
    (h : IsProjOver s) : TopologicalSpace.NoetherianSpace Z := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsProper (PSpace.str O N) := isProper_str O N
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str O N)
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str O N)
  have : IsNoetherian Z := {}
  infer_instance

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

section
variable {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''}

theorem map_comp {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} (m' : SABMap t'' t' g) (m : SABMap t' t f)
    (h : g ≫ f = k) : Nonempty (SABMap t'' t k) := by
  subst h
  exact ⟨(ObjMaps.exists_sab_comp m m').choose⟩

theorem map_cancel {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} (n : SABMap t'' t k) (m : SABMap t' t f)
    (h : g ≫ f = k) : Nonempty (SABMap t'' t' g) := by
  subst h
  exact ⟨(ObjMaps.exists_sab_cancel m n).choose⟩

theorem proper_of_map {f : S' ⟶ S} (m : SABMap t' t f) (h : IsProper t.G.hom) : IsProper t'.G.hom :=
  MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 h

theorem lbIso_of_map {f : S' ⟶ S} (m : SABMap t' t f) : LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, g, -⟩ := m.lin
  exact ⟨w, g⟩

theorem range_subset_abLocus {f : S' ⟶ S} (m : SABMap t' t f) (h : IsProper t'.G.hom) : Set.range f ⊆ abLocus t.G := by
  rintro _ ⟨x, rfl⟩
  exact (abLocus_pullback abLocusOne t.semi m.cart.1 x).2 fun _ _ _ _ _ => inferInstance

theorem genericPoints_subset_abLocus {f : S' ⟶ S} [IsDominant f] [TopologicalSpace.NoetherianSpace S']
    (m : SABMap t' t f) (h : IsProper t'.G.hom) : genericPoints S ⊆ abLocus t.G :=
  (genericPoints_subset_range_of_isDominant f).trans (range_subset_abLocus m h)

end

def HasModel {O : Type} [CommRing O] {M : Scheme.{0}} (sM : M ⟶ Sp O) (tM : SAB H M) (m n : ℕ) (r s : ℤ) : Prop :=
  ∃ C : ZOn sM tM m, C.amp.n = n ∧ C.amp.r = r ∧ C.amp.s = s

variable {O : Type} [CommRing O] {M : Scheme.{0}} {sM : M ⟶ Sp O} {tM : SAB H M} {m n : ℕ} {r s : ℤ}

theorem hasModel_of_maps {Y Z : Scheme.{0}} (a : Y ⟶ M) [IsOpenImmersion a] [IsDominant a] (j : Y ⟶ Z)
    [IsOpenImmersion j] [IsDominant j] (z : Z ⟶ Sp O) (h₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) (h₂ : IsProjOver z) (h₃ : Flat z)
    (t : SAB H Z) (h₄ : IsQProjOver (t.G.hom ≫ z)) (h₅ : Models.Good t) (h : j ≫ z = a ≫ sM) {tY : SAB H Y}
    (m₁ : SABMap tY tM a) (m₂ : SABMap tY t j) (A : LN.AmpFrames t.G t.PP.L (m ^ 2)) :
    HasModel sM tM m A.n A.r A.s := by
  obtain ⟨tW, ⟨k⟩⟩ := exists_pull a.isoOpensRange.inv tY
  obtain ⟨k₁⟩ := map_comp k m₁ a.isoOpensRange_inv_comp
  obtain ⟨k₂⟩ := map_comp k m₂ rfl
  exact ⟨⟨Z, z, ⟨fun x => (h₁ x).1, fun x => (h₁ x).2⟩, h₂, h₃, t, h₄, h₅, a.opensRange, a.denseRange, a.isoOpensRange.inv ≫ j, inferInstance, inferInstance,
    by rw [Category.assoc, h, ← Category.assoc, a.isoOpensRange_inv_comp], tW, k₁, k₂, A⟩, rfl, rfl, rfl⟩

theorem isDominant_ι {X : Scheme.{0}} {W : X.Opens} (h : Dense (W : Set X)) : IsDominant W.ι :=
  ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩

theorem HasModel.shrink (h : HasModel sM tM m n r s) {V : Scheme.{0}} (i : V ⟶ M) [IsOpenImmersion i] [IsDominant i]
    {tV : SAB H V} (k : SABMap tV tM i) : HasModel (i ≫ sM) tV m n r s := by
  obtain ⟨C, rfl, rfl, rfl⟩ := h
  have := isDominant_ι C.dense
  have := C.j_open
  have := C.j_dom
  have : IsDominant (pullback.fst i C.W.ι) := isDominant_pullback_fst_of_isOpenMap _ _ i.isOpenEmbedding.isOpenMap
  have : IsDominant (pullback.snd i C.W.ι) := by
    have := isDominant_pullback_fst_of_isOpenMap i C.W.ι C.W.ι.isOpenEmbedding.isOpenMap
    rw [← pullbackSymmetry_hom_comp_fst]; infer_instance
  obtain ⟨tY, ⟨p⟩⟩ := exists_pull (pullback.snd i C.W.ι) C.tW
  obtain ⟨p₁⟩ := map_comp p C.m₁ rfl
  obtain ⟨p₂⟩ := map_cancel p₁ k pullback.condition
  obtain ⟨p₃⟩ := map_comp p C.m₂ rfl
  exact hasModel_of_maps (pullback.fst i C.W.ι) (pullback.snd i C.W.ι ≫ C.j) C.s (fun x => ⟨C.normal.1 x, C.normal.2 x⟩) C.proj C.flat C.t C.qproj C.good
    (by rw [Category.assoc, C.j_over, pullback.condition_assoc]) p₂ p₃ C.amp

theorem HasModel.grow {V : Scheme.{0}} (i : V ⟶ M) [IsOpenImmersion i] [IsDominant i]
    {tV : SAB H V} (k : SABMap tV tM i) (h : HasModel (i ≫ sM) tV m n r s) : HasModel sM tM m n r s := by
  obtain ⟨C, rfl, rfl, rfl⟩ := h
  have := isDominant_ι C.dense
  have := C.j_open
  have := C.j_dom
  obtain ⟨p⟩ := map_comp C.m₁ k rfl
  exact hasModel_of_maps (C.W.ι ≫ i) C.j C.s (fun x => ⟨C.normal.1 x, C.normal.2 x⟩) C.proj C.flat C.t C.qproj C.good
    (by rw [Category.assoc, C.j_over]) p C.m₂ C.amp

theorem hasModel_of_isEmpty [IsEmpty M] : HasModel sM tM m n r s := by
  have hp : ∀ {X : Scheme.{0}} [IsEmpty X] (f : X ⟶ Sp O), IsProjOver f := fun {X} _ f =>
    ProjSpace.isProjOver_of_disjoint_cover f (fun i : Empty => i.elim) (Subsingleton.elim _ _)
      (fun i => i.elim) fun i => i.elim
  have : IsEmpty tM.G.left := ⟨fun x => isEmptyElim (tM.G.hom x)⟩
  obtain ⟨k, -⟩ := ObjMaps.exists_sab_id tM
  obtain ⟨A, -, rfl, rfl, rfl⟩ := exists_ampFrames (G := tM.G) (L := tM.PP.L) (N := m ^ 2)
    (A := ⟨PEmpty, fun i => i.elim, fun i => i.elim⟩) (n := n) (r := r) (s := s)
    ⟨Subsingleton.elim _ _, fun i => i.elim, fun i => i.elim⟩ (fun z => isEmptyElim z)
    ⟨fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim⟩
  refine hasModel_of_maps (𝟙 M) (𝟙 M) sM (fun x => isEmptyElim x) (hp _) inferInstance tM ?_
    ⟨⟨⊤, Subsingleton.elim _ _, ?_⟩, fun x => isEmptyElim x, fun x => isEmptyElim x⟩ rfl k k A
  · obtain ⟨N, i, hi, e⟩ := hp (tM.G.hom ≫ sM)
    exact ⟨N, i, inferInstance, inferInstance, e⟩
  · have : IsEmpty (⊤ : M.Opens).toScheme := ⟨fun x => isEmptyElim x.1⟩
    infer_instance

theorem good_of_two {Z Z₁ Z₂ : Scheme.{0}} {f₁ : Z₁ ⟶ Z} {f₂ : Z₂ ⟶ Z} [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    {t : SAB H Z} {t₁ : SAB H Z₁} {t₂ : SAB H Z₂} (n₁ : SABMap t₁ t f₁) (n₂ : SABMap t₂ t f₂)
    (h : ∀ z, z ∈ Set.range f₁ ∨ z ∈ Set.range f₂) (g₁ : Models.Good t₁) (g₂ : Models.Good t₂) : Models.Good t := by
  let Y : Bool → Scheme.{0} := fun b => match b with | true => Z₁ | false => Z₂
  let f : ∀ b, Y b ⟶ Z := fun b => match b with | true => f₁ | false => f₂
  let u : ∀ b, SAB H (Y b) := fun b => match b with | true => t₁ | false => t₂
  let k : ∀ b, SABMap (u b) t (f b) := fun b => match b with | true => n₁ | false => n₂
  have ho : ∀ b, IsOpenImmersion (f b) := by rintro (_ | _) <;> assumption
  have hc : ∀ z, ∃ b, z ∈ Set.range (f b) := fun z => (h z).elim (fun h => ⟨true, h⟩) fun h => ⟨false, h⟩
  have hg : ∀ b, Models.Good (u b) := by rintro (_ | _) <;> assumption
  exact ⟨GlobalTheory.T.abelianLocus_isOpen_of_openImmersion_cover E H Z t _ Y f u k ho hc fun b => (hg b).1, GlobalTheory.T.fibresSplit_of_openImmersion_cover E H Z t _ Y f u k ho hc fun b => (hg b).2.1,
    GlobalTheory.T.hasFibrewiseTheta_of_openImmersion_cover E H Z t _ Y f u k ho hc fun b => (hg b).2.2⟩

theorem qproj_of_two {Z Z₁ Z₂ : Scheme.{0}} {f₁ : Z₁ ⟶ Z} {f₂ : Z₂ ⟶ Z} [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    {t : SAB H Z} {t₁ : SAB H Z₁} {t₂ : SAB H Z₂} (n₁ : SABMap t₁ t f₁) (n₂ : SABMap t₂ t f₂)
    (h : IsCompl (Set.range f₁) (Set.range f₂)) (z : Z ⟶ Sp O) (g₁ : IsQProjOver (t₁.G.hom ≫ f₁ ≫ z))
    (g₂ : IsQProjOver (t₂.G.hom ≫ f₂ ≫ z)) : IsQProjOver (t.G.hom ≫ z) := by
  have key : ∀ {Y : Scheme.{0}} {f : Y ⟶ Z} {u : SAB H Y} (k : SABMap u t f),
      Set.range k.φ = t.G.hom ⁻¹' Set.range f := fun {Y f u} k => by
    rw [← Scheme.Pullback.range_fst, SABMap.φ, ← k.cart.1.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, k.cart.1.isoPullback.hom.surjective.range_eq, Set.image_univ]
  refine GlobalTheory.T.isQProjOver_of_isCompl_openImmersions O _ _ _ n₁.φ n₂.φ _ (MorphismProperty.of_isPullback (P := @IsOpenImmersion) n₁.cart.1.flip ‹_›)
    (MorphismProperty.of_isPullback (P := @IsOpenImmersion) n₂.cart.1.flip ‹_›) ?_ ?_ ?_
  · rw [key, key]
    exact h.map (CompleteLatticeHom.setPreimage t.G.hom)
  · rwa [← Category.assoc, n₁.cart.1.w, Category.assoc]
  · rwa [← Category.assoc, n₂.cart.1.w, Category.assoc]

theorem amp_of_two {Z Z₁ Z₂ : Scheme.{0}} {f₁ : Z₁ ⟶ Z} {f₂ : Z₂ ⟶ Z} [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    {t : SAB H Z} {t₁ : SAB H Z₁} {t₂ : SAB H Z₂} (n₁ : SABMap t₁ t f₁) (n₂ : SABMap t₂ t f₂)
    (h : IsCompl (Set.range f₁) (Set.range f₂)) {N : ℕ} (A₁ : LN.AmpFrames t₁.G t₁.PP.L N)
    (A₂ : LN.AmpFrames t₂.G t₂.PP.L N) (hn : A₂.n = A₁.n) (hr : A₂.r = A₁.r) (hs : A₂.s = A₁.s) :
    ∃ A : LN.AmpFrames t.G t.PP.L N, A.n = A₁.n ∧ A.r = A₁.r ∧ A.s = A₁.s := by
  have key : ∀ {Y : Scheme.{0}} {f : Y ⟶ Z} [IsOpenImmersion f] {u : SAB H Y} (k : SABMap u t f)
      (A : LN.AmpFrames u.G u.PP.L N), HasFrames t.G t.PP.L N (pushLB f A.A) A.n A.r A.s := fun {Y f _ u} k A =>
    GlobalTheory.T.transitionFrames_push_openImmersion_image _ _ _ _ f k.φ _ _ t.PP.isLB u.PP.isLB k.cart.1 (lbIso_of_map k)
      (fun x hx => (abLocus_pullback abLocusOne t.semi k.cart.1 x).1 hx) N _ _ _ _ (hasFrames_of_ampFrames A)
  have h₂ := key n₂ A₂
  rw [hn, hr, hs] at h₂
  obtain ⟨a, b⟩ := GlobalTheory.T.isAmpleCechLineBundle_disjointUnion_pushforward Z Z₁ Z₂ f₁ f₂ A₁.A A₂.A h A₁.isLB A₂.isLB A₁.ample A₂.ample
  obtain ⟨A, -, e⟩ := exists_ampFrames a b (GlobalTheory.T.hasFrames_disjointUnionCechData Z _ _ N _ _ _ _ _ (fun i j => le_bot_iff.1 (by
    rintro _ ⟨⟨x, -, rfl⟩, y, -, e⟩
    exact (Set.disjoint_left.1 h.disjoint ⟨x, rfl⟩ ⟨y, e⟩).elim)) (key n₁ A₁) h₂)
  exact ⟨A, e⟩

theorem HasModel.sum [IsNoetherianRing O] [IsReduced M] (hp : IsProper tM.G.hom) {V₁ V₂ : Scheme.{0}} (i₁ : V₁ ⟶ M)
    (i₂ : V₂ ⟶ M) [IsOpenImmersion i₁] [IsOpenImmersion i₂] (hd : Disjoint (Set.range i₁) (Set.range i₂))
    (hu : Dense (Set.range i₁ ∪ Set.range i₂)) {t₁ : SAB H V₁} {t₂ : SAB H V₂} (k₁ : SABMap t₁ tM i₁)
    (k₂ : SABMap t₂ tM i₂) (h₁ : HasModel (i₁ ≫ sM) t₁ m n r s) (h₂ : HasModel (i₂ ≫ sM) t₂ m n r s) :
    HasModel sM tM m n r s := by
  obtain ⟨C₁, rfl, rfl, rfl⟩ := h₁
  obtain ⟨C₂, hn, hr, hs⟩ := h₂
  have := isDominant_ι C₁.dense
  have := C₁.j_open
  have := C₁.j_dom
  have := isDominant_ι C₂.dense
  have := C₂.j_open
  have := C₂.j_dom
  have := C₁.flat
  have := C₂.flat
  have o₀ := isOpenImmersion_desc i₁ i₂ hd
  have d₀ : IsDominant (coprod.desc i₁ i₂) := ⟨by rwa [DenseRange, range_desc]⟩
  have o₁ := isOpenImmersion_map C₁.W.ι C₂.W.ι
  have d₁ := isDominant_map C₁.W.ι C₂.W.ι
  let a := coprod.map C₁.W.ι C₂.W.ι ≫ coprod.desc i₁ i₂
  have o₂ := isOpenImmersion_map C₁.j (𝟙 C₂.W.toScheme)
  have d₂ := isDominant_map C₁.j (𝟙 C₂.W.toScheme)
  have o₃ := isOpenImmersion_map (𝟙 C₁.Z) C₂.j
  have d₃ := isDominant_map (𝟙 C₁.Z) C₂.j
  have hZ := isNormalScheme_coprod (fun x => ⟨C₁.normal.1 x, C₁.normal.2 x⟩) (fun x => ⟨C₂.normal.1 x, C₂.normal.2 x⟩)
  have hP := ProjSpace.isProjOver_coprodDesc C₁.proj C₂.proj
  have := noetherianSpace_of_isProjOver hP
  have := isReduced_of_isNormalScheme hZ
  have : TopologicalSpace.NoetherianSpace (C₁.W.toScheme ⨿ C₂.W.toScheme : Scheme.{0}) :=
    (coprod.map C₁.j (𝟙 C₂.W.toScheme) ≫ coprod.map (𝟙 C₁.Z) C₂.j).isOpenEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace C₁.W.toScheme :=
    (coprod.inl : _ ⟶ C₁.W.toScheme ⨿ C₂.W.toScheme).isOpenEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace C₂.W.toScheme :=
    (coprod.inr : _ ⟶ C₁.W.toScheme ⨿ C₂.W.toScheme).isOpenEmbedding.isInducing.noetherianSpace
  obtain ⟨tY, ⟨p⟩⟩ := exists_pull a tM
  obtain ⟨q₁⟩ := map_comp C₁.m₁ k₁ rfl
  obtain ⟨q₂⟩ := map_comp C₂.m₁ k₂ rfl
  obtain ⟨p₁⟩ := map_cancel (g := coprod.inl) q₁ p (by rw [coprod.inl_map_assoc, coprod.inl_desc])
  obtain ⟨p₂⟩ := map_cancel (g := coprod.inr) q₂ p (by rw [coprod.inr_map_assoc, coprod.inr_desc])
  have pY := proper_of_map p hp
  obtain ⟨t', ⟨u₀⟩, ⟨u₁⟩⟩ := GlobalTheory.T.exists_abelianTriple_glue_two_open_immersions E H _ _ _ _ (coprod.map C₁.j (𝟙 C₂.W.toScheme)) coprod.inl coprod.inl C₁.j _ _ _
    p₁ C₁.m₂ o₂ inferInstance (isPullback_inl_inl_coprodMap _ _).flip (fun x => by
      obtain h | ⟨y, rfl⟩ := mem_inl_or_inr x
      · exact .inr h
      · exact .inl ⟨(coprod.inr : _ ⟶ C₁.W.toScheme ⨿ C₂.W.toScheme) y, by
          rw [← Scheme.Hom.comp_apply, coprod.inr_map, Category.id_comp]⟩)
    ⟨isReduced_of_isOpenImmersion a, fun _ _ _ _ _ _ _ => inferInstance⟩
    ⟨isReduced_of_isNormalScheme (fun x => ⟨C₁.normal.1 x, C₁.normal.2 x⟩), genericPoints_subset_abLocus C₁.m₂ (proper_of_map q₁ hp)⟩
  obtain ⟨v₂⟩ := map_comp (k := coprod.inr) p₂ u₀ (by simp)
  obtain ⟨t, ⟨w₀⟩, ⟨w₂⟩⟩ := GlobalTheory.T.exists_abelianTriple_glue_two_open_immersions E H _ _ _ _ (coprod.map (𝟙 C₁.Z) C₂.j) coprod.inr coprod.inr C₂.j _ _ _
    v₂ C₂.m₂ o₃ inferInstance (isPullback_inr_inr_coprodMap _ _).flip (fun x => by
      obtain ⟨y, rfl⟩ | h := mem_inl_or_inr x
      · exact .inl ⟨(coprod.inl : _ ⟶ C₁.Z ⨿ C₂.W.toScheme) y, by
          rw [← Scheme.Hom.comp_apply, coprod.inl_map, Category.id_comp]⟩
      · exact .inr h)
    ⟨isReduced_of_isOpenImmersion (coprod.map (𝟙 C₁.Z) C₂.j), genericPoints_subset_abLocus u₀ pY⟩
    ⟨isReduced_of_isNormalScheme (fun x => ⟨C₂.normal.1 x, C₂.normal.2 x⟩), genericPoints_subset_abLocus C₂.m₂ (proper_of_map q₂ hp)⟩
  obtain ⟨w₁⟩ := map_comp (k := coprod.inl) u₁ w₀ (by simp)
  obtain ⟨w⟩ := map_comp u₀ w₀ rfl
  obtain ⟨A, e₁, e₂, e₃⟩ := amp_of_two w₁ w₂ (isCompl_range_inl_inr _ _) C₁.amp C₂.amp hn hr hs
  rw [← e₁, ← e₂, ← e₃]
  refine hasModel_of_maps a _ (coprod.desc C₁.s C₂.s) hZ hP ?_ t
    (qproj_of_two w₁ w₂ (isCompl_range_inl_inr _ _) _ (by rw [coprod.inl_desc]; exact C₁.qproj)
      (by rw [coprod.inr_desc]; exact C₂.qproj))
    (good_of_two w₁ w₂ mem_inl_or_inr C₁.good C₂.good) ?_ p w A
  · have : IsZariskiLocalAtSource @Flat := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_openCover (P := @Flat) (coprodOpenCover.{0, 0} C₁.Z C₂.Z) ?_
    rintro (_ | _)
    · exact (coprod.inl_desc C₁.s C₂.s).symm ▸ C₁.flat
    · exact (coprod.inr_desc C₁.s C₂.s).symm ▸ C₂.flat
  · refine coprod.hom_ext ?_ ?_
    · simp only [a, Category.assoc, coprod.inl_map_assoc, coprod.inl_desc, coprod.inl_desc_assoc, Category.id_comp,
        C₁.j_over]
    · simp only [a, Category.assoc, coprod.inr_map_assoc, coprod.inr_desc, coprod.inr_desc_assoc, Category.id_comp,
        C₂.j_over]

theorem hasModel_sup [IsNoetherianRing O] [IsReduced M] (hp : IsProper tM.G.hom) {I : Type} (V : I → M.Opens)
    (hd : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (h : ∀ i (t : SAB H (V i).toScheme), SABMap t tM (V i).ι → HasModel ((V i).ι ≫ sM) t m n r s) (S : Finset I) :
    ∀ t : SAB H (S.sup V).toScheme, SABMap t tM (S.sup V).ι → HasModel ((S.sup V).ι ≫ sM) t m n r s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro t _
    have : IsEmpty ((∅ : Finset I).sup V).toScheme := ⟨fun x => x.2⟩
    exact hasModel_of_isEmpty
  | insert a S ha ih =>
    intro t k
    have l₁ : V a ≤ (insert a S).sup V := Finset.le_sup (Finset.mem_insert_self a S)
    have l₂ : S.sup V ≤ (insert a S).sup V := Finset.sup_mono (Finset.subset_insert a S)
    have hD : Disjoint (V a) (S.sup V) := Finset.disjoint_sup_right.2 fun j hj => hd a j fun e => ha (e ▸ hj)
    obtain ⟨t₁, ⟨k₁⟩⟩ := exists_pull (M.homOfLE l₁) t
    obtain ⟨t₂, ⟨k₂⟩⟩ := exists_pull (M.homOfLE l₂) t
    obtain ⟨q₁⟩ := map_comp k₁ k (M.homOfLE_ι l₁)
    obtain ⟨q₂⟩ := map_comp k₂ k (M.homOfLE_ι l₂)
    refine HasModel.sum (proper_of_map k hp) (M.homOfLE l₁) (M.homOfLE l₂) (Set.disjoint_left.2 ?_) (fun x => ?_) k₁ k₂
      (by rw [Scheme.homOfLE_ι_assoc]; exact h a t₁ q₁) (by rw [Scheme.homOfLE_ι_assoc]; exact ih t₂ q₂)
    · rintro _ ⟨x, rfl⟩ ⟨y, e⟩
      have e' : y.1 = x.1 := (Scheme.homOfLE_apply l₂ y).symm.trans ((congrArg Subtype.val e).trans (Scheme.homOfLE_apply l₁ x))
      exact hD.le_bot (⟨x.2, e' ▸ y.2⟩ : x.1 ∈ V a ⊓ S.sup V)
    · refine subset_closure ?_
      obtain hx | hx : x.1 ∈ V a ∨ x.1 ∈ S.sup V := (Finset.sup_insert (s := S) (f := V) (b := a)).le x.2
      · exact .inl ⟨⟨x.1, hx⟩, Subtype.ext (by simp)⟩
      · exact .inr ⟨⟨x.1, hx⟩, Subtype.ext (by simp)⟩

theorem rank_eq (hL : Out.Laws) (hL' : Out.Laws2) (hp : IsProper tM.G.hom) (hA : Out.RelAmple tM.G tM.PP.L)
    (hK : Out.KTriv tM.G tM.PP.L) {g : ℕ} (hg : SmoothOfRelativeDimension g tM.G.hom) {R : Type} [CommRing R]
    [IsLocalRing R] {y : Sp R ⟶ M} {t' : SAB H (Sp R)} (k : SABMap t' tM y) {Z : Scheme.{0}} {t : SAB H Z}
    {χ : Sp R ⟶ Z} (k' : SABMap t' t χ) {N : ℕ} {T : Over Z} (h : Over.mk χ ⟶ T)
    (b : Fin n → LB.Sec (Out.LPow t.G t.PP.L (N : ℤ) T)) (hb : LN.BasisAlong t.G t.PP.L N h b) : n = max 1 (N ^ g) := by
  obtain ⟨b', hb'⟩ := GlobalTheory.T.pulledSectionsFormBasis_id_of_pulledSectionsFormBasis Z _ _ N n _ _ h b t.PP.isLB hb
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_sectionPower_transport_cartesian_square Z _ t.G t'.G χ k'.φ _ _ t.PP.isLB t'.PP.isLB k'.cart.1 (lbIso_of_map k') N
  let e₀ := e (Over.mk (𝟙 (Sp R))) (Over.mk χ) (Iso.refl _) rfl
  have hb₀ : LN.BasisAlong t'.G t'.PP.L N (𝟙 (Over.mk (𝟙 (Sp R)))) (fun i => e₀.symm (b' i)) := fun σ => by
    have key : ∀ c, LN.Lin t'.G t'.PP.L N (𝟙 (Over.mk (𝟙 (Sp R)))) (fun i => e₀.symm (b' i)) c σ ↔
        LN.Lin t.G t.PP.L N (𝟙 (Over.mk χ)) b' c (e₀ σ) := fun c => by
      have := he _ _ _ _ (Iso.refl _) (Iso.refl _) rfl rfl (𝟙 (Over.mk (𝟙 (Sp R)))) (𝟙 (Over.mk χ)) rfl n
        (fun i => e₀.symm (b' i)) c σ
      refine this.trans ?_
      rw [show (fun i => e _ _ (Iso.refl _) rfl (e₀.symm (b' i))) = b' from funext fun i => e₀.apply_symm_apply _]
    simp only [key]
    exact hb' _
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  obtain ⟨w, gw, -⟩ := k.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := M) (U := ⊤)
    (x := y (IsLocalRing.closedPoint R)) trivial
  have hy : ∀ x, y x ∈ U := fun x =>
    (congrArg (fun V => x ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem y hc)).mpr trivial
  have am := relAmple_pull k.cart.1 tM.PP.isLB t'.PP.isLB ((isGen_iff w).1 gw) U hU hy hA
  have kt := kTriv_pull k.cart tM.PP.isLB t'.PP.isLB ((isGen_iff w).1 gw) hK
  obtain ⟨-, ws, gs', -⟩ := t'.sym
  let P : Out.PolAV (Sp R) :=
    { A := t'.G, g := g, L := t'.PP.L, isLB := t'.PP.isLB, ample := am, ktriv := kt
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback k.cart.1 hg
      isAb := ⟨inferInstance, inferInstance, proper_of_map k hp, ‹_›⟩
      rigid := ⟨t'.PP.rig, t'.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  obtain rfl | hN := Nat.eq_zero_or_pos N
  · rw [GlobalTheory.T.card_basis_polarisation_power_zero_eq_one hL.globalFns R P n _ hb₀, max_eq_left (pow_le_one₀ le_rfl zero_le_one)]
  · rw [GlobalTheory.T.card_pulledSectionsFormBasis_eq_pow_dim hL hL' R P N n _ hN hb₀, max_eq_right (Nat.one_le_pow _ _ hN)]

theorem hasModel_rank (hL : Out.Laws) (hL' : Out.Laws2) (hp : IsProper tM.G.hom) (hA : Out.RelAmple tM.G tM.PP.L)
    (hK : Out.KTriv tM.G tM.PP.L) {g : ℕ} (hg : SmoothOfRelativeDimension g tM.G.hom) {V : Scheme.{0}} {i : V ⟶ M}
    {tV : SAB H V} (k : SABMap tV tM i) {sV : V ⟶ Sp O} (C : ZOn sV tV m) [IsIntegral C.Z]
    (A : LN.AmpFrames C.t.G C.t.PP.L (m ^ 2)) : HasModel sV tV m (max 1 ((m ^ 2) ^ g)) A.r A.s := by
  suffices h : HasFrames C.t.G C.t.PP.L (m ^ 2) A.A (max 1 ((m ^ 2) ^ g)) A.r A.s by
    obtain ⟨A', -, e⟩ := exists_ampFrames A.isLB A.ample h
    exact ⟨{ C with amp := A' }, e⟩
  by_cases hT : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], LN.CDvr W → IsEmpty (Sp W ⟶ C.Z)
  · exact GlobalTheory.T.hasTransitionCompatibleFrames_of_no_completeDVR_points _ _ _ _ _ _ _ _ _ (le_max_left _ _) hT (hasFrames_of_ampFrames A)
  push Not at hT
  obtain ⟨W, _, _, _, hW, ⟨χ₀⟩⟩ := hT
  have := hW.2.2
  obtain ⟨R, _, _, _, hR, χ, hχ⟩ := GlobalTheory.T.exists_completeDVR_point_genericPoint C.Z W χ₀
  have := C.j_open
  have := C.j_dom
  have hj : Set.range χ ⊆ Set.range C.j := by
    rintro _ ⟨y, rfl⟩
    rw [hχ]
    exact ((genericPoint_spec C.Z).mem_open_set_iff C.j.isOpenEmbedding.isOpen_range).2
      (by rw [Set.univ_inter]; exact C.j.denseRange.nonempty_iff.2 inferInstance |>.elim fun x => ⟨_, x, rfl⟩)
  obtain ⟨a, ha⟩ := exists_chart A.isLB (genericPoint C.Z)
  have hU : Set.range χ ⊆ Set.range (A.A.U a).ι := by
    rintro _ ⟨y, rfl⟩
    rw [hχ, Scheme.Opens.range_ι]
    exact ha
  obtain ⟨t', ⟨p⟩⟩ := exists_pull (IsOpenImmersion.lift C.j χ hj) C.tW
  obtain ⟨q⟩ := map_comp C.m₁ k rfl
  obtain ⟨p₁⟩ := map_comp p q rfl
  obtain ⟨p₂⟩ := map_comp (k := IsOpenImmersion.lift (A.A.U a).ι χ hU ≫ (A.A.U a).ι) p C.m₂
    (by rw [IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac])
  have hb := (A.trait a R hR (IsOpenImmersion.lift (A.A.U a).ι χ hU) (by
    rintro _ ⟨y, rfl⟩
    exact range_subset_abLocus p₂ (proper_of_map p₁ hp) ⟨_, rfl⟩)).2
  rw [← rank_eq hL hL' hp hA hK hg p₁ p₂ _ _ hb]
  exact hasFrames_of_ampFrames A

end GlobalTheory.ModelSum

namespace GlobalTheory

open ModelSum ZM in
theorem Models.nonempty_zOn_of_components : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (O : Type) [CommRing O] [IsNoetherianRing O] (MM : Scheme.{0}) (sM : MM ⟶ Sp O) (tM : SAB H MM) (m : ℕ), IsReduced MM → LocallyOfFiniteType sM → QuasiCompact sM → (∀ ξ ∈ genericPoints MM, ∃ (V : Scheme.{0}) (i : V ⟶ MM) (tV : SAB H V) (_ : SABMap tV tM i) (C : ZOn (i ≫ sM) tV m), IsOpenImmersion i ∧ ξ ∈ Set.range i ∧ IsIntegral V ∧ IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1) → (∃ g, SmoothOfRelativeDimension g tM.G.hom) → Out.Laws → Out.Laws2 → IsProper tM.G.hom → Out.RelAmple tM.G tM.PP.L → Out.KTriv tM.G tM.PP.L → Nonempty (ZOn sM tM m) := by
  intro E _ _ _ H O _ _ M sM tM m hr hf hq h ⟨g, hg⟩ hL hL' hp hA hK
  have : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian sM
  have : CompactSpace M := QuasiCompact.compactSpace_of_compactSpace sM
  have : IsNoetherian M := {}
  have hfin : (genericPoints M).Finite := genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have : Fintype (genericPoints M) := hfin.fintype
  choose V i tV k C ho hm hV hZ hs hC using fun ξ : genericPoints M => h ξ.1 ξ.2
  obtain ⟨r, hb⟩ := (Set.finite_range fun ξ => (C ξ).amp.r).bddAbove
  have gen : ∀ ξ x, ξ.1 ⤳ i ξ x := fun ξ x => by
    obtain ⟨v, hv⟩ := hm ξ
    have e : i ξ (genericPoint (V ξ)) = ξ.1 := eq_of_specializes_of_mem_genericPoints ξ.2
      (hv ▸ (genericPoint_specializes v).map (i ξ).continuous)
    exact e ▸ (genericPoint_specializes x).map (i ξ).continuous
  have key := hasModel_sup (sM := sM) (m := m) (n := max 1 ((m ^ 2) ^ g)) (r := r) (s := 1) hp
    (fun ξ => (i ξ).opensRange) (fun ξ ζ hne => disjoint_iff_inf_le.2 (by
      rintro _ ⟨⟨x, rfl⟩, hy⟩
      obtain ⟨c, hc⟩ := (gen ξ x).mem_open (i ζ).opensRange.2 hy
      exact (hne (Subtype.ext (eq_of_specializes_of_mem_genericPoints ξ.2 (hc ▸ gen ζ c)).symm)).elim))
    (fun ξ t q => by
      obtain ⟨A, rfl, e⟩ := hC ξ r (hb ⟨ξ, rfl⟩)
      obtain ⟨q'⟩ := map_cancel q (k ξ) (i ξ).isoOpensRange_inv_comp
      have := (hasModel_rank hL hL' hp hA hK hg (k ξ) (C ξ) A).shrink (i ξ).isoOpensRange.inv q'
      rwa [← Category.assoc, (i ξ).isoOpensRange_inv_comp, e] at this) Finset.univ
  obtain ⟨t, ⟨q⟩⟩ := exists_pull (Finset.univ.sup fun ξ => (i ξ).opensRange : M.Opens).ι tM
  have := isDominant_ι (W := Finset.univ.sup fun ξ => (i ξ).opensRange)
    ((dense_iff_closure_eq.2 (genericPoints.closure (α := M))).mono fun ξ hξ =>
      Finset.le_sup (f := fun ξ => (i ξ).opensRange) (Finset.mem_univ ⟨ξ, hξ⟩) (hm ⟨ξ, hξ⟩))
  exact ⟨(HasModel.grow _ q (key t q)).choose⟩

end GlobalTheory

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_points_open_integral_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (O : Type) [CommRing O] [IsNoetherianRing O] (MM : Scheme.{0}) (sM : MM ⟶ Sp O) (tM : SAB H MM) (m : ℕ), IsReduced MM → LocallyOfFiniteType sM → QuasiCompact sM → (∀ ξ ∈ genericPoints MM, ∃ (V : Scheme.{0}) (i : V ⟶ MM) (tV : SAB H V) (_ : SABMap tV tM i) (C : ZOn (i ≫ sM) tV m), IsOpenImmersion i ∧ ξ ∈ Set.range i ∧ IsIntegral V ∧ IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1) → (∃ g, SmoothOfRelativeDimension g tM.G.hom) → Out.Laws → Out.Laws2 → IsProper tM.G.hom → Out.RelAmple tM.G tM.PP.L → Out.KTriv tM.G tM.PP.L → Nonempty (ZOn sM tM m) := by
  first | exact @GlobalTheory.Models.nonempty_zOn_of_components | exact GlobalTheory.Models.nonempty_zOn_of_components | (intros; apply GlobalTheory.Models.nonempty_zOn_of_components <;> assumption)
end
