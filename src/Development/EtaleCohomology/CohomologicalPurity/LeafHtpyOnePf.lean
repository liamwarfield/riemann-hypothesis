module

public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut
public import Development.EtaleCohomology.CohomologicalPurity.LeafLocPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafPurPf

@[expose] public section

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafHtpyOnePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.CohomologicalPurity.Thom

namespace HtpyOnePf

theorem pull_bij_of_iso {R : Type} [CommRing R] (F : Shv R) {E E' : Spc} (a : E ⟶ E') [IsIso a] (n : ℤ) :
    Function.Bijective (pull R a F n) :=
  Function.bijective_iff_has_inverse.2 ⟨pull R (inv a) F n,
    fun x => by rw [← pull_comp, IsIso.inv_hom_id, pull_id],
    fun x => by rw [← pull_comp, IsIso.hom_inv_id, pull_id]⟩

theorem eqv_of_sq {R : Type} [CommRing R] (F : Shv R) {E1 E2 E3 E4 : Spc} (f : E1 ⟶ E2) (g : E3 ⟶ E4)
    (a : E3 ⟶ E1) (b : E4 ⟶ E2) [IsIso a] [IsIso b] (w : a ≫ f = g ≫ b) (hg : Eqv R g F) : Eqv R f F := by
  intro n
  have h1 : (pull R a F n) ∘ (pull R f F n) = (pull R g F n) ∘ (pull R b F n) := by
    funext x; simp only [Function.comp_apply]; rw [← pull_comp, ← pull_comp, w]
  have h2 : Function.Bijective ((pull R a F n) ∘ (pull R f F n)) := by
    rw [h1]; exact (hg n).comp (pull_bij_of_iso F b n)
  exact (Function.Bijective.of_comp_iff' (pull_bij_of_iso F a n) _).1 h2

theorem off_span (A : Type) [CommRing A] (x : A) :
    off A (Ideal.span {x}) = PrimeSpectrum.basicOpen x := by
  apply TopologicalSpace.Opens.ext
  change (PrimeSpectrum.zeroLocus ((Ideal.span {x} : Ideal A) : Set A))ᶜ = _
  rw [PrimeSpectrum.zeroLocus_span]; exact (PrimeSpectrum.basicOpen_eq_zeroLocus_compl x).symm

theorem off_span_C (A : Type) [CommRing A] (x : A) :
    off (Polynomial A) ((Ideal.span {x}).map Polynomial.C) = PrimeSpectrum.basicOpen (C x) := by
  rw [Ideal.map_span, Set.image_singleton]; exact off_span _ _

attribute [local instance] Polynomial.algebra in
theorem away_poly (A : Type) [CommRing A] (x : A) :
    IsLocalization.Away (C x) (Polynomial (Localization.Away x)) := by
  have := Polynomial.isLocalization (Submonoid.powers x) (Localization.Away x)
  rw [Submonoid.map_powers] at this
  exact this

theorem sq (A : Type) [CommRing A] (x : A)
    (h : off (Polynomial A) ((Ideal.span {x}).map Polynomial.C) ≤
      Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A (Ideal.span {x})) :
    ∃ (eT : Spec (CommRingCat.of (Polynomial (Localization.Away x))) ≅
        (off (Polynomial A) ((Ideal.span {x}).map Polynomial.C)).toScheme)
      (eB : Spec (CommRingCat.of (Localization.Away x)) ≅ (off A (Ideal.span {x})).toScheme),
      eT.hom ≫ (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h =
        Spec.map (CommRingCat.ofHom (Polynomial.C : Localization.Away x →+* _)) ≫ eB.hom := by
  letI : Algebra (Polynomial A) (Polynomial (Localization.Away x)) := Polynomial.algebra A (Localization.Away x)
  have := away_poly A x
  let jB := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x)))
  let jT := Spec.map (CommRingCat.ofHom (algebraMap (Polynomial A) (Polynomial (Localization.Away x))))
  have : IsOpenImmersion jT := IsOpenImmersion.of_isLocalization (C x)
  have rB : Set.range jB = Set.range (off A (Ideal.span {x})).ι := by
    rw [Scheme.Opens.range_ι, off_span]
    exact PrimeSpectrum.localization_away_comap_range _ x
  have rT : Set.range jT = Set.range (off (Polynomial A) ((Ideal.span {x}).map Polynomial.C)).ι := by
    rw [Scheme.Opens.range_ι, off_span_C]
    exact PrimeSpectrum.localization_away_comap_range _ (C x)
  refine ⟨IsOpenImmersion.isoOfRangeEq jT _ rT, IsOpenImmersion.isoOfRangeEq jB _ rB, ?_⟩
  rw [← cancel_mono (off A (Ideal.span {x})).ι, Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
    IsOpenImmersion.isoOfRangeEq_hom_fac, ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
  simp only [jT, jB, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a : 2
  simp [Polynomial.algebraMap_def]

end HtpyOnePf

theorem LeafHtpyOne_of : LeafHtpyOne := by
  intro _ c4 q _ A _ x hq h i
  obtain ⟨eT, eB, w⟩ := HtpyOnePf.sq A x h
  have hqB : IsUnit ((q : ℕ) : Localization.Away x) := by
    simpa using hq.map (algebraMap A (Localization.Away x))
  refine HtpyOnePf.eqv_of_sq _ _ (sch.map (Spec.map (CommRingCat.ofHom (Polynomial.C : Localization.Away x →+* _))))
    (sch.map eT.hom) (sch.map eB.hom) ?_ (c4 q (Localization.Away x) hqB i)
  rw [← Functor.map_comp, ← Functor.map_comp, w]

end LateralTheory.CohomologicalPurity.Thom
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafFstHocPf
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def LeafDiscPb : Prop := ∀ {A Y G : PSh} (f : A ⟶ Y) (g : G ⟶ Y),
  ∃ e : disc.obj (pullback f g) ≅ pullback (disc.map f) (disc.map g), e.hom ≫ pullback.fst _ _ = disc.map (pullback.fst f g)

def DiscreteSimplicialPresheafPreservesCoproducts : Prop := ∀ (A : Type) (X : A → PSh) (c : Cofan X), Nonempty (IsColimit c) →
  Nonempty (IsColimit (Cofan.mk (disc.obj c.pt) fun a => disc.map (c.inj a)))

def LeafUnivSum : Prop := ∀ (A : Type) (X : A → PSh) (c : Cofan X), Nonempty (IsColimit c) → ∀ {Y G : PSh} (f : c.pt ⟶ Y)
  (g : G ⟶ Y), Nonempty (IsColimit (Cofan.mk (pullback f g)
    fun a => pullback.map (c.inj a ≫ f) g f g (c.inj a) (𝟙 G) (𝟙 Y) (by simp) (by simp)))

instance discPres (n : SimplexCategoryᵒᵖ) {K : Type} [SmallCategory K] (G : K ⥤ PSh) :
    PreservesLimit G (disc ⋙ (evaluation _ _).obj n) :=
  preservesLimit_of_natIso G (NatIso.ofComponents (fun X => Iso.refl X) (fun _ => rfl) : 𝟭 PSh ≅ disc ⋙ (evaluation _ _).obj n)

instance discPresC (n : SimplexCategoryᵒᵖ) {K : Type} [SmallCategory K] (G : K ⥤ PSh) :
    PreservesColimit G (disc ⋙ (evaluation _ _).obj n) :=
  preservesColimit_of_natIso G (NatIso.ofComponents (fun X => Iso.refl X) (fun _ => rfl) : 𝟭 PSh ≅ disc ⋙ (evaluation _ _).obj n)

instance {K : Type} [SmallCategory K] (G : K ⥤ PSh) : PreservesLimit G disc := preservesLimit_of_evaluation _ _ fun _ => inferInstance
instance {K : Type} [SmallCategory K] (G : K ⥤ PSh) : PreservesColimit G disc := preservesColimit_of_evaluation _ _ fun _ => inferInstance

theorem leafDiscPb : LeafDiscPb := fun f g => ⟨PreservesPullback.iso disc f g, PreservesPullback.iso_hom_fst _ _ _⟩

theorem leafDiscSum_ryrx : DiscreteSimplicialPresheafPreservesCoproducts := fun _ X c ⟨h⟩ =>
  ⟨(isColimitMapCoconeCofanMkEquiv disc X c.inj).1 (isColimitOfPreserves disc h)⟩

theorem eqv_sum (hS : LeafSum) {R : Type} [CommRing R] (F : Shv R) {A : Type} {E' E : A → Spc} (c' : Cofan E')
    (c : Cofan E) (h' : Nonempty (IsColimit c')) (h : Nonempty (IsColimit c)) (f : c'.pt ⟶ c.pt)
    (fa : ∀ a, E' a ⟶ E a) (hf : ∀ a, c'.inj a ≫ f = fa a ≫ c.inj a) (he : ∀ a, Eqv R (fa a) F) : Eqv R f F := fun n => by
  have k : (fun x a => pull R (c'.inj a) F n x) ∘ pull R f F n =
      (fun (y : ∀ a, H R (E a) F n) a => pull R (fa a) F n (y a)) ∘ (fun x a => pull R (c.inj a) F n x) := by
    funext x a
    simp only [Function.comp]
    rw [← pull_comp, ← pull_comp, hf]
  have bp : Function.Bijective (fun (y : ∀ a, H R (E a) F n) a => pull R (fa a) F n (y a)) :=
    ⟨fun y z e => funext fun a => (he a n).1 (congrFun e a),
     fun w => ⟨fun a => ((he a n).2 (w a)).choose, funext fun a => ((he a n).2 (w a)).choose_spec⟩⟩
  have b2 := bp.comp (hS R F A E c h n)
  rw [← k] at b2
  exact (Function.Bijective.of_comp_iff' (hS R F A E' c' h' n) _).1 b2

theorem inj_aug {J : Type} [SmallCategory J] (D : J ⥤ PSh) {Y : PSh} (c : ∀ j, D.obj j ⟶ Y) (hc : Coc D c)
    (n : SimplexCategoryᵒᵖ) (σ : Fin (n.unop.len + 1) ⥤ J) : inj D n σ ≫ (aug c hc).app n = c (σ.obj 0) := by
  have e : σ.map (homOfLE (Fin.zero_le (0 : Fin (n.unop.len + 1)))) = 𝟙 _ := σ.map_id _
  ext U x
  change (c (σ.obj 0)).app U ((D.map (σ.map (homOfLE (Fin.zero_le 0)))).app U x) = (c (σ.obj 0)).app U x
  rw [e, D.map_id]
  rfl

theorem etale_first_hocolim_descent_of_discrete_pullback_sum (hL : LeafLevel) (hS : LeafSum) (hP : LeafDiscPb) (hD : DiscreteSimplicialPresheafPreservesCoproducts) (hU : LeafUnivSum) :
    LeafFstHoc := by
  intro hA3 R _ F J _ D Y G g c hc hj
  apply hA3
  intro n
  have e1 : disc.map ((pullback.fst (aug c hc) (disc.map g)).app n) =
      disc.map (pullbackObjIso (aug c hc) (disc.map g) n).hom ≫
        disc.map (pullback.fst ((aug c hc).app n) ((disc.map g).app n)) := by
    rw [← disc.map_comp, pullbackObjIso_hom_comp_fst]
  rw [e1]
  refine eqv_comp (eqv_iso _ _) ?_
  obtain ⟨hLc⟩ := hL J D n
  have hU' := hU _ _ _ ⟨hLc⟩ ((aug c hc).app n) ((disc.map g).app n)
  refine eqv_sum hS F _ _ (hD _ _ _ hU') (hD _ _ _ ⟨hLc⟩) _
    (fun σ => disc.map (pullback.fst (inj D n σ ≫ (aug c hc).app n) ((disc.map g).app n))) ?_ ?_
  · intro σ
    show disc.map _ ≫ disc.map _ = disc.map _ ≫ disc.map _
    refine ((disc.map_comp _ _).symm.trans (congrArg disc.map ?_)).trans (disc.map_comp _ _)
    set_option synthInstance.maxHeartbeats 200000 in
      exact pullback.lift_fst _ _ _
  · intro σ
    have h0 := hj (σ.obj 0)
    obtain ⟨e, he⟩ := hP (c (σ.obj 0)) g
    have E := inj_aug D c hc n σ
    have key : ∀ f (_ : f = c (σ.obj 0)), Eqv R (disc.map (pullback.fst f g)) F := by
      rintro f rfl
      rw [← he]
      exact eqv_comp (eqv_iso _ _) h0
    exact key _ E

theorem LeafFstHoc_of (hL : LeafLevel) (hS : LeafSum) (hU : LeafUnivSum) : LeafFstHoc :=
  etale_first_hocolim_descent_of_discrete_pullback_sum hL hS leafDiscPb leafDiscSum_ryrx hU

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafHsSumPfR
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def LeafDblSum : Prop := ∀ (X : Scheme.{0}) (U : X.Opens) (A : Type) (E : A → PSh) (c : Cofan E), Nonempty (IsColimit c) →
  ∀ (π : c.pt ⟶ yoneda.obj X) (π' : ∀ a, E a ⟶ yoneda.obj X)
  (h : ∀ a, disc.map (c.inj a) ≫ disc.map π = disc.map (π' a)),
  Nonempty (IsColimit (Cofan.mk (dbl (abv U (E := disc.obj c.pt) (disc.map π)))
    fun a => dbl.map (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a))))

def LeafDiscSumH : Prop := ∀ (A : Type) (E : A → PSh) (c : Cofan E), Nonempty (IsColimit c) →
  Nonempty (IsColimit (Cofan.mk (disc.obj c.pt) fun a => disc.map (c.inj a)))

theorem leafDiscSumH : LeafDiscSumH := fun A E c hc =>
  ⟨isColimitCofanMkObjOfIsColimit disc E (fun a => c.inj a)
    (hc.some.ofIsoColimit (Cofan.ext (Iso.refl _) (fun _ => by simp)))⟩

def LeafPbSum : Prop := ∀ (X : Scheme.{0}) (U : X.Opens) (A : Type) (E : A → PSh) (c : Cofan E), Nonempty (IsColimit c) →
  ∀ (π : c.pt ⟶ yoneda.obj X) (π' : ∀ a, E a ⟶ yoneda.obj X)
  (h : ∀ a, disc.map (c.inj a) ≫ disc.map π = disc.map (π' a)),
  Nonempty (IsColimit (Cofan.mk (abv U (E := disc.obj c.pt) (disc.map π)).left
    fun a => (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)).left))

theorem dbl_inl_map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc (f := P'.hom) (g := P'.hom) _ _ _

theorem dbl_inl_map_assoc {P' P : Arrow Spc} (φ : P' ⟶ P) {Z : Spc} (h : dbl P ⟶ Z) :
    dbl.inl P' ≫ dbl.map φ ≫ h = φ.right ≫ dbl.inl P ≫ h := by
  rw [← Category.assoc, dbl_inl_map, Category.assoc]

theorem dbl_inr_map_assoc {P' P : Arrow Spc} (φ : P' ⟶ P) {Z : Spc} (h : dbl P ⟶ Z) :
    dbl.inr P' ≫ dbl.map φ ≫ h = φ.right ≫ dbl.inr P ≫ h := by
  rw [← Category.assoc, dbl.inr_map, Category.assoc]

def dbl_cofan {A : Type} {P : Arrow Spc} (Q : A → Arrow Spc) (φ : ∀ a, Q a ⟶ P)
    (hl : IsColimit (Cofan.mk P.left fun a => (φ a).left)) (hr : IsColimit (Cofan.mk P.right fun a => (φ a).right)) :
    IsColimit (Cofan.mk (dbl P) fun a => dbl.map (φ a)) := by
  refine Cofan.IsColimit.mk _ (fun s => pushout.desc (Cofan.IsColimit.desc hr fun a => dbl.inl (Q a) ≫ s.inj a)
      (Cofan.IsColimit.desc hr fun a => dbl.inr (Q a) ≫ s.inj a) ?_) ?_ ?_
  · refine Cofan.IsColimit.hom_ext hl _ _ fun a => ?_
    have w := Arrow.w (φ a)
    have f1 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inl (Q a) ≫ s.inj a) = dbl.inl (Q a) ≫ s.inj a :=
      Cofan.IsColimit.fac hr _ a
    have f2 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inr (Q a) ≫ s.inj a) = dbl.inr (Q a) ≫ s.inj a :=
      Cofan.IsColimit.fac hr _ a
    change ((φ a).left ≫ P.hom) ≫ _ = ((φ a).left ≫ P.hom) ≫ _
    rw [w, Category.assoc, Category.assoc, f1, f2, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ s.inj a) (pushout.condition (f := (Q a).hom) (g := (Q a).hom))
  · intro s a
    have f1 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inl (Q a) ≫ s.inj a) = dbl.inl (Q a) ≫ s.inj a := by
      simpa using Cofan.IsColimit.fac hr (fun a => dbl.inl (Q a) ≫ s.inj a) a
    have f2 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inr (Q a) ≫ s.inj a) = dbl.inr (Q a) ≫ s.inj a := by
      simpa using Cofan.IsColimit.fac hr (fun a => dbl.inr (Q a) ≫ s.inj a) a
    apply pushout.hom_ext (f := (Q a).hom) (g := (Q a).hom)
    · exact (dbl_inl_map_assoc (φ a) _).trans ((congrArg _ (pushout.inl_desc _ _ _)).trans f1)
    · exact (dbl_inr_map_assoc (φ a) _).trans ((congrArg _ (pushout.inr_desc _ _ _)).trans f2)
  · intro s m hm
    apply pushout.hom_ext
    · refine Eq.trans ?_ (pushout.inl_desc _ _ _).symm
      refine Cofan.IsColimit.hom_ext hr _ _ fun a => ?_
      have f1 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inl (Q a) ≫ s.inj a) = dbl.inl (Q a) ≫ s.inj a := by
        simpa using Cofan.IsColimit.fac hr (fun a => dbl.inl (Q a) ≫ s.inj a) a
      refine Eq.trans ?_ f1.symm
      exact (dbl_inl_map_assoc (φ a) m).symm.trans (congrArg _ (hm a))
    · refine Eq.trans ?_ (pushout.inr_desc _ _ _).symm
      refine Cofan.IsColimit.hom_ext hr _ _ fun a => ?_
      have f2 : (φ a).right ≫ Cofan.IsColimit.desc hr (fun a => dbl.inr (Q a) ≫ s.inj a) = dbl.inr (Q a) ≫ s.inj a := by
        simpa using Cofan.IsColimit.fac hr (fun a => dbl.inr (Q a) ≫ s.inj a) a
      refine Eq.trans ?_ f2.symm
      exact (dbl_inr_map_assoc (φ a) m).symm.trans (congrArg _ (hm a))

theorem leafDblSum_of (hP : LeafPbSum) : LeafDblSum := fun X U A E c hc π π' h =>
  ⟨dbl_cofan _ _ (hP X U A E c hc π π' h).some (leafDiscSumH A E c hc).some⟩

theorem LeafHsSum_of_dbl (hS : LeafSum) (hD : LeafDblSum) (hd : LeafDiscSumH) : LeafHsSum := by
  intro q X U A E c hc π π' h n i
  have S1 := hS (ZMod q) (tw q i) A _ _ (hD X U A E c hc π π' h) n
  have S2 := hS (ZMod q) (tw q i) A _ _ (hd A E c hc) n
  constructor
  · intro x y e
    apply Subtype.ext
    apply S1.1
    funext a
    exact congrArg Subtype.val (congrFun e a)
  · intro y
    obtain ⟨x, hx⟩ := S1.2 (fun a => (y a).1)
    have hx' : ∀ a, pull _ (dbl.map (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a))) (tw q i) n x
        = (y a).1 := fun a => congrFun hx a
    have m : x ∈ Hs q (abv U (E := disc.obj c.pt) (disc.map π)) n i := by
      refine AddMonoidHom.mem_ker.mpr ?_
      apply S2.1
      funext a
      have e := dbl.inr_map (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a))
      have y0 : pull _ (dbl.inr _) (tw q i) n (y a).1 = 0 := (y a).2
      have e2 : disc.map (c.inj a) ≫ dbl.inr (abv U (E := disc.obj c.pt) (disc.map π)) =
          dbl.inr _ ≫ dbl.map (abvRel U (disc.map (c.inj a)) (disc.map (π' a)) (disc.map π) (h a)) := e.symm
      have key : pull _ (disc.map (c.inj a) ≫ dbl.inr (abv U (E := disc.obj c.pt) (disc.map π))) (tw q i) n x = 0 := by
        exact (congrArg (fun f => pull (ZMod q) f (tw q i) n x) e2).trans ((pull_comp _ _ _ _ _ _).trans
          ((congrArg (pull (ZMod q) (dbl.inr _) (tw q i) n) (hx' a)).trans y0))
      exact ((pull_comp _ _ _ _ _ _).symm.trans key).trans (map_zero _).symm
    exact ⟨⟨x, m⟩, funext fun a => Subtype.ext (hx' a)⟩

end LateralTheory.CohomologicalPurity.TubeCut

namespace LateralTheory.CohomologicalPurity.TubeCut

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafHsContPfFive
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

theorem opnMap_tri {X'' X' X : Scheme.{0}} {g : X'' ⟶ X} (a : X'' ⟶ X') (b : X' ⟶ X) (e : g = a ≫ b)
    (U'' : X''.Opens) (U' : X'.Opens) (U : X.Opens) (h : U'' ≤ g ⁻¹ᵁ U) (h1 : U'' ≤ a ⁻¹ᵁ U') (h2 : U' ≤ b ⁻¹ᵁ U) :
    opnMap g U'' U h = opnMap a U'' U' h1 ≫ opnMap b U' U h2 := by
  subst e; exact opnMap_comp _ _ _ _ _ h1 h2 h

theorem fgt_pull (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (x : Hs q P n i) :
    Hs.fgt q P' n i (Hs.pull q φ n i x) = pull _ φ.right (tw q i) n (Hs.fgt q P n i x) := by
  change pull _ (dbl.inl P') _ n (pull _ (dbl.map φ) _ n x.1) = pull _ φ.right _ n (pull _ (dbl.inl P) _ n x.1)
  rw [← pull_comp, ← pull_comp, dbl.inl_map']

theorem res_pull (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) (n i : ℤ) (y : Ht q P.right n i) :
    pull _ P'.hom (tw q i) n (pull _ φ.right (tw q i) n y) = pull _ φ.left (tw q i) n (pull _ P.hom (tw q i) n y) := by
  rw [← pull_comp, ← pull_comp, ← Arrow.w φ]

theorem pull_left_comp (q : ℕ) {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) (n i : ℤ) (y : Ht q P.left n i) :
    pull _ (φ ≫ ψ).left (tw q i) n y = pull _ φ.left (tw q i) n (pull _ ψ.left (tw q i) n y) := by
  rw [Arrow.comp_left, pull_comp]

theorem pull_right_comp (q : ℕ) {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) (n i : ℤ) (y : Ht q P.right n i) :
    pull _ (φ ≫ ψ).right (tw q i) n y = pull _ φ.right (tw q i) n (pull _ ψ.right (tw q i) n y) := by
  rw [Arrow.comp_right, pull_comp]

theorem leafHsFive : LeafHsFive := by
  intro a1 b1 hBd q A B _ _ φ I hq J _ _ D s t hc he i hO n
  obtain ⟨δ, hδ⟩ := hBd
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have hqB : IsUnit (q : B) := by simpa using hq.map φ
  have hqj : ∀ j, IsUnit (q : D.obj j) := fun j => by simpa using hq.map (s.app j).hom
  have hsn : ∀ {j k : J} (f : j ⟶ k), s.app k = s.app j ≫ D.map f := fun f => by simpa using s.naturality f
  have htn : ∀ {j k : J} (f : j ⟶ k), D.map f ≫ t.app k = t.app j := fun f => by simpa using t.naturality f
  have hD : ∀ {j k : J} (f : j ⟶ k), off (D.obj k) (I.map (s.app k).hom) ≤
      Spec.map (D.map f) ⁻¹ᵁ off (D.obj j) (I.map (s.app j).hom) := by
    intro j k f
    have e1 := off_map (s.app k).hom I
    have e2 := off_map (s.app j).hom I
    simp only [CommRingCat.ofHom_hom] at e1 e2
    rw [e1, e2, hsn f, Spec.map_comp]
    intro x hx; exact hx
  have hT : ∀ j, off B (I.map φ) ≤ Spec.map (t.app j) ⁻¹ᵁ off (D.obj j) (I.map (s.app j).hom) := by
    intro j
    have e1 := off_map φ I
    have e2 := off_map (s.app j).hom I
    simp only [CommRingCat.ofHom_hom] at e2
    rw [e1, e2, ← he j, Spec.map_comp]
    intro x hx; exact hx
  have eT : ∀ {j k : J} (f : j ⟶ k), Spec.map (t.app j) = Spec.map (t.app k) ≫ Spec.map (D.map f) := fun f => by
    rw [← Spec.map_comp, htn f]
  have eD : ∀ {j k l : J} (f : j ⟶ k) (g : k ⟶ l), Spec.map (D.map (f ≫ g)) = Spec.map (D.map g) ≫ Spec.map (D.map f) :=
    fun f g => by rw [← Spec.map_comp, ← Functor.map_comp]
  have sc : ∀ k : ℤ, (∀ x : Ht q (opn (off B (I.map φ))).right k i, ∃ j, ∃ y : Ht q (opn (off (D.obj j) (I.map (s.app j).hom))).right k i,
      pull _ (opnMap (Spec.map (t.app j)) _ _ (hT j)).right (tw q i) k y = x) ∧
      ∀ j (y : Ht q (opn (off (D.obj j) (I.map (s.app j).hom))).right k i),
        pull _ (opnMap (Spec.map (t.app j)) _ _ (hT j)).right (tw q i) k y = 0 →
        ∃ (l : J) (f : j ⟶ l), pull _ (opnMap (Spec.map (D.map f)) _ _ (hD f)).right (tw q i) k y = 0 :=
    fun k => spec_cont b1 q D t hc hqB hqj k i
  have ex := fun {X : Scheme.{0}} (V : X.Opens) (k : ℤ) => hδ.1 q (opn V) (opn_mono V) k i
  constructor
  · intro x
    obtain ⟨j1, y1, hy1'⟩ := (sc (m + 1)).1 (Hs.fgt q _ (m + 1) i x)
    have h2 : pull _ (opnMap (Spec.map (t.app j1)) _ _ (hT j1)).left (tw q i) (m + 1)
        (pull _ (opn (off (D.obj j1) (I.map (s.app j1).hom))).hom (tw q i) (m + 1) y1) = 0 := by
      rw [← res_pull, hy1']
      exact (ex _ (m + 1)).1.apply_apply_eq_zero x
    obtain ⟨k, f, h', hk⟩ := (hO (m + 1)).2 j1 (hT j1) _ h2
    have h3 : pull _ (opn (off (D.obj k) (I.map (s.app k).hom))).hom (tw q i) (m + 1)
        (pull _ (opnMap (Spec.map (D.map f)) _ _ h').right (tw q i) (m + 1) y1) = 0 := by
      rw [res_pull]; exact hk
    obtain ⟨z, hz⟩ := ((ex (off (D.obj k) (I.map (s.app k).hom)) (m + 1)).1 _).1 h3
    have h4 : Hs.fgt q _ (m + 1) i (x - Hs.pull q (opnMap (Spec.map (t.app k)) _ _ (hT k)) (m + 1) i z) = 0 := by
      rw [map_sub, fgt_pull, hz, ← pull_right_comp,
        ← opnMap_tri (Spec.map (t.app k)) (Spec.map (D.map f)) (eT f) _ _ _ (hT j1) (hT k) h', hy1', sub_self]
    obtain ⟨w, hw⟩ := ((ex (off B (I.map φ)) m).2.2 _).1 h4
    obtain ⟨j2, h2', w2, hw2⟩ := (hO m).1 w
    refine ⟨IsFiltered.max k j2, hT _,
      Hs.pull q (opnMap (Spec.map (D.map (IsFiltered.leftToMax k j2))) _ _ (hD _)) (m + 1) i z +
      δ q _ m i (pull _ (opnMap (Spec.map (D.map (IsFiltered.rightToMax k j2))) _ _ (hD _)).left (tw q i) m w2), ?_⟩
    rw [map_add (f := _), ← Hs.pull_comp',
      ← opnMap_tri (Spec.map (t.app _)) (Spec.map (D.map (IsFiltered.leftToMax k j2))) (eT _) _ _ _ (hT k) (hT _) (hD _),
      hδ.2.1 q _ _ _ (opn_mono _) (opn_mono _), ← pull_left_comp,
      ← opnMap_tri (Spec.map (t.app _)) (Spec.map (D.map (IsFiltered.rightToMax k j2))) (eT _) _ _ _ h2' (hT _) (hD _),
      hw2, hw]
    abel
  · intro j h y hy
    have hf : pull _ (opnMap (Spec.map (t.app j)) _ _ h).right (tw q i) (m + 1) (Hs.fgt q _ (m + 1) i y) = 0 := by
      rw [← fgt_pull, hy, map_zero]
    obtain ⟨k, f, hk⟩ := (sc (m + 1)).2 j _ (by exact hf)
    have h5 : Hs.fgt q _ (m + 1) i (Hs.pull q (opnMap (Spec.map (D.map f)) _ _ (hD f)) (m + 1) i y) = 0 := by
      rw [fgt_pull]; exact hk
    obtain ⟨w, hw⟩ := ((ex (off (D.obj k) (I.map (s.app k).hom)) m).2.2 _).1 h5
    have h6 : δ q _ m i (pull _ (opnMap (Spec.map (t.app k)) _ _ (hT k)).left (tw q i) m w) = 0 := by
      rw [← hδ.2.1 q _ _ (opnMap (Spec.map (t.app k)) _ _ (hT k)) (opn_mono _) (opn_mono _), hw, ← Hs.pull_comp',
        ← opnMap_tri (Spec.map (t.app k)) (Spec.map (D.map f)) (eT f) _ _ _ h (hT k) (hD f), hy]
    obtain ⟨v, hv⟩ := ((ex (off B (I.map φ)) m).2.1 _).1 h6
    obtain ⟨j3, v3, hv3'⟩ := (sc m).1 v
    have h7 : pull _ (opnMap (Spec.map (t.app (IsFiltered.max k j3))) _ _ (hT _)).left (tw q i) m
        (pull _ (opnMap (Spec.map (D.map (IsFiltered.leftToMax k j3))) _ _ (hD _)).left (tw q i) m w -
          pull _ (opn (off (D.obj (IsFiltered.max k j3)) (I.map (s.app _).hom))).hom (tw q i) m
            (pull _ (opnMap (Spec.map (D.map (IsFiltered.rightToMax k j3))) _ _ (hD _)).right (tw q i) m v3)) = 0 := by
      rw [map_sub, sub_eq_zero, ← pull_left_comp,
        ← opnMap_tri (Spec.map (t.app _)) (Spec.map (D.map (IsFiltered.leftToMax k j3))) (eT _) _ _ _ (hT k) (hT _) (hD _),
        ← res_pull, ← pull_right_comp,
        ← opnMap_tri (Spec.map (t.app _)) (Spec.map (D.map (IsFiltered.rightToMax k j3))) (eT _) _ _ _ (hT j3) (hT _) (hD _),
        hv3', hv]
    obtain ⟨r, g, h8, hr⟩ := (hO m).2 _ (hT _) _ h7
    refine ⟨r, f ≫ IsFiltered.leftToMax k j3 ≫ g, hD _, ?_⟩
    rw [map_sub, sub_eq_zero] at hr
    rw [opnMap_tri (Spec.map (D.map (IsFiltered.leftToMax k j3 ≫ g))) (Spec.map (D.map f)) (eD _ _) _ _ _ _ (hD _) (hD f),
      Hs.pull_comp', ← hw,
      opnMap_tri (Spec.map (D.map g)) (Spec.map (D.map (IsFiltered.leftToMax k j3))) (eD _ _) _ _ _ _ h8 (hD _),
      Hs.pull_comp', hδ.2.1 q _ _ _ (opn_mono _) (opn_mono _), hδ.2.1 q _ _ _ (opn_mono _) (opn_mono _), hr,
      ← res_pull]
    exact (ex _ m).2.1.apply_apply_eq_zero _

theorem leafHsCont_of' (hB : LeafBd) (hE : LeafExc) (hO : LeafOffCont) : LeafHsCont :=
  leafHsCont_of hB hE hO leafHsFive

end LateralTheory.CohomologicalPurity
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafTauOf
section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafTauResPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i')
    (a : Ht q E' n i) :
    pull _ f (tw q i') n' (Ht.cast h1 h2 a) = Ht.cast h1 h2 (pull _ f (tw q i) n a) := by
  subst h1; subst h2; rfl

theorem pull_cpow (h : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hI : Inv q E') (x : Ht q E' 2 1) :
    ∀ k : ℕ, pull _ f (tw q k) (2 * k) (cpow q x k) = cpow q (pull _ f (tw q 1) 2 x) k
  | 0 => by
    rw [cpow_zero, cpow_zero, pull_cast, (h q).2.1 f hI]
  | k + 1 => by
    rw [cpow_succ, cpow_succ, pull_cast, (h q).1, pull_cpow h q f hI x k]

theorem hyp_pull (h : DivisorNaturality) (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R] (hI : Inv q (PR (d + 1) 0 R)) :
    pull _ (pr d R).hom (tw q 1) 2 (hyp q (d + 1) 0 R) = hyp q (d + 1) 1 R := by
  change pull _ (prod.map (Pj.incl (d + 1)) (𝟙 (sp R)) : PR (d + 1) 1 R ⟶ PR (d + 1) 0 R) (tw q 1) 2
    (c1 q (prod.fst ≫ Pj.line (d + 1) 0)) = c1 q (prod.fst ≫ Pj.line (d + 1) 1)
  rw [(h q).2.2.1 _ _ hI, prod.map_fst_assoc, Pj.incl_line]

theorem tauRes_unit (H : Hyp) (hG : LeafGeo) (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R]
    (hq : IsUnit (q : R)) (m : ℕ) (n i : ℤ) a :
    pull _ (pr d R).hom (tw q i) n (poly q (d + 1) 0 R m n i a) = poly q (d + 1) 1 R m n i a := by
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hI := hG.2.1 q (d + 1) 0 R hq
  change pull _ (prod.map (Pj.incl (d + 1)) (𝟙 (sp R)) : PR (d + 1) 1 R ⟶ PR (d + 1) 0 R) (tw q i) n
    (poly q (d + 1) 0 R m n i a) = _
  unfold poly
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pull_cast, (h6 q).1, pull_cpow h6 q _ hI, ← pull_comp, prod.map_snd, Category.comp_id]
  congr 3
  exact hyp_pull h6 q d R hI

theorem LeafTau_ofU (hBd : LeafBd) (hG : LeafGeo) (hPB : LeafPB) (hTl : LeafTail)
    (hU : LeafTauU) (hT : LeafTauTop) : LeafTau := by
  have hL := tauLin
  have hF := tauFgt
  intro H q _ d R _ hq
  have hR' := tauRes_unit H hG q d R hq
  obtain ⟨δ, hδ, -, -⟩ := hBd
  have hm : Mono (pr d R).hom := hG.1 d R
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hUb := hU hPB hTl H q d R hq
  have hPB' := hPB H.1 h6 H.2.2.2.2.2.2.2.2.2.2.1 q (d + 1) R hq
  have hpoly0 := poly_zero hL
  have hres0 : ∀ n i (σ : Hs q (pr d R) n i), pull _ (pr d R).hom (tw q i) n (Hs.fgt q _ n i σ) = 0 :=
    fun n i σ => ((hδ q _ hm n i).1 _).2 ⟨σ, rfl⟩
  have hinj : ∀ n i, Function.Injective (Hs.fgt q (pr d R) n i) := by
    intro N i
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by ring⟩
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro σ hσ
    obtain ⟨u, rfl⟩ := ((hδ q _ hm n i).2.2 σ).1 hσ
    obtain ⟨a, ha⟩ := (hUb n i).2 u
    exact ((hδ q _ hm n i).2.1 u).2 ⟨poly q (d + 1) 0 R d n i a, (hR' d n i a).trans ha⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := (hUb (2 * d) d).2 (pull _ (pr d R).hom (tw q d) _ (cpow q (hyp q (d + 1) 0 R) d))
    have hy : pull _ (pr d R).hom (tw q d) _
        (cpow q (hyp q (d + 1) 0 R) d + poly q (d + 1) 0 R d (2 * d) d (0 - b)) = 0 := by
      refine (map_add _ _ _).trans ?_
      rw [hR' d (2 * d) d (0 - b), hL, hpoly0, zero_sub, ← hb]
      exact add_neg_cancel _
    obtain ⟨τ, hτ⟩ := ((hδ q _ hm _ _).1 _).1 hy
    refine ⟨τ, ⟨0 - b, hτ⟩, ?_⟩
    rintro τ' ⟨a', ha'⟩
    have e1 := hres0 _ _ τ'
    rw [ha'] at e1
    have e2 := (map_add (pull _ (pr d R).hom (tw q d) (2 * d)) _ _).symm.trans e1
    rw [hR' d (2 * d) d a'] at e2
    have hab : a' = 0 - b := (hUb _ _).1 (by
      rw [hL, hpoly0, zero_sub, hb]
      exact eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans e2))
    apply hinj
    rw [ha', hτ, hab]
  · rintro τ ⟨a, ha⟩ n i
    constructor
    · intro x y hxy
      obtain ⟨ex, hex, hex'⟩ := hT H q d R n i x a
      obtain ⟨ey, hey, hey'⟩ := hT H q d R n i y a
      have h1 := congrArg (Hs.fgt q (pr d R) (n + 2 * d) (i + d)) hxy
      dsimp only at h1
      have fx := hF h6 q (pr d R) n (2 * d) i d (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n x) τ
      have fy := hF h6 q (pr d R) n (2 * d) i d (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n y) τ
      rw [ha] at fx fy
      replace h1 := hex'.symm.trans (fx.symm.trans (h1.trans (fy.trans hey')))
      have h2 := congrFun ((hPB' _ _).1 h1) (Fin.last d)
      rw [hex, hey] at h2
      exact cast_inj _ _ h2
    · intro σ
      obtain ⟨c, hc⟩ := (hPB' (n + 2 * d) (i + d)).2 (Hs.fgt q (pr d R) (n + 2 * d) (i + d) σ)
      have k1 : n + 2 * (d : ℤ) - 2 * (((Fin.last d : Fin (d + 1)) : ℕ) : ℤ) = n := by
        simp only [Fin.val_last]; ring
      have k2 : i + (d : ℤ) - (((Fin.last d : Fin (d + 1)) : ℕ) : ℤ) = i := by
        simp only [Fin.val_last]; ring
      refine ⟨Ht.cast k1 k2 (c (Fin.last d)), ?_⟩
      obtain ⟨e, he, he'⟩ := hT H q d R n i (Ht.cast k1 k2 (c (Fin.last d))) a
      have hlast : (e - c) (Fin.last d) = 0 := by
        rw [Pi.sub_apply, he, cast_cast, sub_self]
      have hsnoc : poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) (e - c) =
          poly q (d + 1) 0 R d (n + 2 * d) (i + d) (fun j : Fin d => (e - c) j.castSucc) := by
        unfold poly
        rw [Fin.sum_univ_castSucc, hlast]
        simp only [map_zero, AddMonoidHom.zero_apply, cast_zero, add_zero]
        rfl
      have hd : poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) (e - c) =
          Hs.fgt q (pr d R) (n + 2 * d) (i + d) (Hs.act q (P := pr d R) (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) _ _
            (Ht.cast k1 k2 (c (Fin.last d)))) τ - σ) := by
        have hfx := hF h6 q (pr d R) n (2 * d) i d
          (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n (Ht.cast k1 k2 (c (Fin.last d)))) τ
        rw [ha] at hfx
        rw [hL, map_sub, hc]
        exact congrArg (fun t : Ht q (pr d R).right (n + 2 * d) (i + d) => t - Hs.fgt q (pr d R) (n + 2 * d) (i + d) σ)
          (he'.symm.trans hfx.symm)
      have hg : (fun j : Fin d => (e - c) j.castSucc) = 0 := (hUb _ _).1 (by
        rw [hpoly0, ← hR', ← hsnoc, hd]
        exact hres0 _ _ _)
      rw [hg, hpoly0] at hsnoc
      rw [hsnoc] at hd
      replace hd := hd.symm
      rw [map_sub] at hd
      exact hinj _ _ (sub_eq_zero.mp hd)

end LateralTheory.CohomologicalPurity.Thom
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ThomClassRestriction

theorem LeafTau_of (hBd : LeafBd) (hG : LeafGeo) (hPB : LeafPB) (hTl : LeafTail)
    (hU : LeafTauU) (hT : LeafTauTop) : LeafTau :=
  LeafTau_ofU hBd hG hPB hTl hU hT

end LateralTheory.CohomologicalPurity.Thom.ThomClassRestriction
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.IsPullbackOfApp
section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafCokIsoPf
noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

def LeafFreePb : Prop := ∀ (R : Type) [CommRing R] {A' A B' B : PSh} (t : A' ⟶ B') (l : A' ⟶ A) (r : B' ⟶ B)
  (b : A ⟶ B), IsPullback t l r b → Mono r → Mono b →
  IsPullback ((free R).map t) ((free R).map l) ((free R).map r) ((free R).map b)

theorem isIso_cokernel_map_of_pb_epi {C : Type*} [Category C] [Abelian C] {X₁ X₂ X₃ X₄ : C}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (sq : IsPullback t l r b)
    (he : Epi (biprod.desc r b)) : IsIso (cokernel.map _ _ _ _ sq.w) := by
  have := Abelian.mono_cokernel_map_of_isPullback sq
  have : Epi (cokernel.map _ _ _ _ sq.w) := by
    have h1 : biprod.desc r b ≫ cokernel.π b = (biprod.fst : X₂ ⊞ X₃ ⟶ X₂) ≫ (r ≫ cokernel.π b) := by
      ext <;> simp
    have h3 : Epi (r ≫ cokernel.π b) := by
      have : Epi ((biprod.fst : X₂ ⊞ X₃ ⟶ X₂) ≫ (r ≫ cokernel.π b)) := by rw [← h1]; infer_instance
      exact epi_of_epi (biprod.fst : X₂ ⊞ X₃ ⟶ X₂) _
    have h2 : cokernel.π t ≫ cokernel.map _ _ _ _ sq.w = r ≫ cokernel.π b := by simp
    rw [← h2] at h3
    exact epi_of_epi (cokernel.π t) _
  exact isIso_of_mono_of_epi _

theorem transport_sq {C : Type*} [Category C] [Abelian C] {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : C}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    {t' : Y₁ ⟶ Y₂} {l' : Y₁ ⟶ Y₃} {r' : Y₂ ⟶ Y₄} {b' : Y₃ ⟶ Y₄}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃) (e₄ : X₄ ≅ Y₄)
    (ht : t = e₁.hom ≫ t' ≫ e₂.inv) (hl : l = e₁.hom ≫ l' ≫ e₃.inv)
    (hr : r = e₂.hom ≫ r' ≫ e₄.inv) (hb : b = e₃.hom ≫ b' ≫ e₄.inv)
    (sq : IsPullback t' l' r' b') (he : Epi (biprod.desc r' b')) :
    IsPullback t l r b ∧ Epi (biprod.desc r b) := by
  subst ht hl hr hb
  refine ⟨sq.of_iso e₁.symm e₂.symm e₃.symm e₄.symm (by simp) (by simp) (by simp) (by simp), ?_⟩
  have : biprod.desc (e₂.hom ≫ r' ≫ e₄.inv) (e₃.hom ≫ b' ≫ e₄.inv) =
      (biprod.mapIso e₂ e₃).hom ≫ biprod.desc r' b' ≫ e₄.inv := by
    ext <;> simp
  rw [this]
  infer_instance

theorem leafCokIso_of (hF : LeafFreePb) : LeafCokIso := by
  intro q P' P φ hpb hc n
  by_cases hn : ∃ p : ℕ, -(p : ℤ) = n
  · obtain ⟨p, rfl⟩ := hn
    have h : ComplexShape.embeddingDownNat.f p = -(p : ℤ) := rfl
    have key : ∀ {E' E : Spc} (f : E' ⟶ E), ((chains (ZMod q)).map f).f (-(p : ℤ)) =
        (HomologicalComplex.extendXIso _ _ h).hom ≫ (free (ZMod q)).map (f.app (op (SimplexCategory.mk p))) ≫
          (HomologicalComplex.extendXIso _ _ h).inv := by
      intro E' E f
      change (HomologicalComplex.extendMap ((chainsN (ZMod q)).map f) _).f _ = _
      rw [HomologicalComplex.extendMap_f _ _ h]
      rfl
    have hpb' : IsPullback (P'.hom.app (op (SimplexCategory.mk p))) (φ.left.app (op (SimplexCategory.mk p)))
        (φ.right.app (op (SimplexCategory.mk p))) (P.hom.app (op (SimplexCategory.mk p))) :=
      hpb.map ((evaluation _ _).obj (op (SimplexCategory.mk p)))
    have mr : Mono (φ.right.app (op (SimplexCategory.mk p))) := by
      have := hc.1; rw [NatTrans.mono_iff_mono_app] at this; exact this _
    have mb : Mono (P.hom.app (op (SimplexCategory.mk p))) := by
      have := hc.2.1; rw [NatTrans.mono_iff_mono_app] at this; exact this _
    obtain ⟨h1, h2⟩ := transport_sq _ _ _ _ (key P'.hom) (key φ.left) (key φ.right) (key P.hom)
      (hF (ZMod q) _ _ _ _ hpb' mr mb) (hc.2.2 _)
    exact isIso_cokernel_map_of_pb_epi h1 h2
  · push Not at hn
    have hz : ∀ E : Spc, IsZero (((chains (ZMod q)).obj E).X n) := fun E =>
      HomologicalComplex.isZero_extend_X _ _ _ (fun i => hn i)
    have hA : IsZero (cokernel ((chains (ZMod q)).map P'.hom |>.f n)) :=
      IsZero.of_epi (cokernel.π _) (hz _)
    have hB : IsZero (cokernel ((chains (ZMod q)).map P.hom |>.f n)) :=
      IsZero.of_epi (cokernel.π _) (hz _)
    exact ⟨0, hA.eq_of_src _ _, hB.eq_of_src _ _⟩

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem fin_pb {α β γ δ M : Type*} [AddCommMonoid M] (t : α → β) (l : α → γ) (r : β → δ) (b : γ → δ)
    (w : ∀ a, r (t a) = b (l a)) (hpb : ∀ x y, r x = b y → ∃ a, t a = x ∧ l a = y)
    (ht : Function.Injective t) (hr : Function.Injective r) (hb : Function.Injective b)
    (x : β →₀ M) (y : γ →₀ M) (h : Finsupp.mapDomain r x = Finsupp.mapDomain b y) :
    ∃ z : α →₀ M, Finsupp.mapDomain t z = x ∧ Finsupp.mapDomain l z = y := by
  classical
  have hsupp : ∀ s ∈ x.support, s ∈ Set.range t := by
    intro s hs
    have h1 : (Finsupp.mapDomain r x) (r s) ≠ 0 := by
      rw [Finsupp.mapDomain_apply_of_injective hr]; exact Finsupp.mem_support_iff.1 hs
    rw [h] at h1
    have h2 : r s ∈ (Finsupp.mapDomain b y).support := Finsupp.mem_support_iff.2 h1
    have h3 := Finsupp.mapDomain_support h2
    obtain ⟨c, -, hc⟩ := Finset.mem_image.1 h3
    obtain ⟨a, ha, -⟩ := hpb s c hc.symm
    exact ⟨a, ha⟩
  refine ⟨x.comapDomain t ht.injOn, ?_, ?_⟩
  · exact Finsupp.mapDomain_comapDomain t ht x hsupp
  · apply Finsupp.mapDomain_injective hb
    rw [← Finsupp.mapDomain_comp]
    have : b ∘ l = r ∘ t := funext fun a => (w a).symm
    rw [this, Finsupp.mapDomain_comp, Finsupp.mapDomain_comapDomain t ht x hsupp, h]

theorem isPullback_of_app {J C : Type*} [Category J] [Category C] {A B X Y : J ⥤ C}
    {t : A ⟶ B} {l : A ⟶ X} {r : B ⟶ Y} {b : X ⟶ Y} (w : t ≫ r = l ≫ b)
    (h : ∀ j, IsPullback (t.app j) (l.app j) (r.app j) (b.app j)) : IsPullback t l r b :=
  IsPullback.of_isLimit' ⟨w⟩ (evaluationJointlyReflectsLimits _ fun j =>
    (isLimitMapConePullbackConeEquiv ((evaluation J C).obj j) w).symm (h j).isLimit)

theorem modfree_pb (R : Type) [CommRing R] {A' A B' B : Type} (t : A' ⟶ B') (l : A' ⟶ A) (r : B' ⟶ B)
    (b : A ⟶ B) (hpb : IsPullback t l r b) (hr : Function.Injective r) (hb : Function.Injective b) :
    IsPullback ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map t))
      ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map l))
      ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map r))
      ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map b)) := by
  obtain ⟨w, hinj, hex⟩ := (Types.isPullback_iff _ _ _ _).1 hpb
  have ht : Function.Injective t := fun x y h => hinj x y ⟨h, hb (by
    have := ConcreteCategory.congr_hom w x; have h2 := ConcreteCategory.congr_hom w y; simp only [ConcreteCategory.comp_apply, types_comp_apply] at this h2
    rw [← this, ← h2, h])⟩
  have hw : ∀ a : ULift.{1} A', ULift.up (r (t a.down)) = ULift.up (b (l a.down)) := fun a => by
    have := ConcreteCategory.congr_hom w a.down; simp only [ConcreteCategory.comp_apply, types_comp_apply] at this; rw [this]
  have sq : (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map t) ≫
      (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map r) =
      (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map l) ≫
      (ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map b) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, w]
  refine IsPullback.of_map (forget (ModuleCat (ULift.{1} R))) sq ?_
  rw [Types.isPullback_iff]
  refine ⟨congrArg (forget _).map sq, ?_, ?_⟩
  · rintro x y ⟨h1, -⟩
    have hu : Function.Injective (uliftFunctor.{1}.map t) := fun a c h =>
      ULift.ext (ht (congrArg ULift.down h))
    exact Finsupp.mapDomain_injective hu h1
  · intro x y h
    exact fin_pb (uliftFunctor.{1}.map t) (uliftFunctor.{1}.map l) (uliftFunctor.{1}.map r)
      (uliftFunctor.{1}.map b) hw
      (fun x y h => by
        obtain ⟨a, ha1, ha2⟩ := hex x.down y.down (congrArg ULift.down h)
        exact ⟨ULift.up a, ULift.ext ha1, ULift.ext ha2⟩)
      (fun a c h => ULift.ext (ht (congrArg ULift.down h)))
      (fun a c h => ULift.ext (hr (congrArg ULift.down h)))
      (fun a c h => ULift.ext (hb (congrArg ULift.down h))) x y h

theorem leafFreePb : LeafFreePb := by
  intro R _ A' A B' B t l r b hpb hr hb
  have hP : IsPullback ((freeP R).map t) ((freeP R).map l) ((freeP R).map r) ((freeP R).map b) := by
    refine isPullback_of_app (by rw [← Functor.map_comp, ← Functor.map_comp, hpb.w]) fun U => ?_
    have hrU : Mono (r.app U) := by rw [NatTrans.mono_iff_mono_app] at hr; exact hr U
    have hbU : Mono (b.app U) := by rw [NatTrans.mono_iff_mono_app] at hb; exact hb U
    exact modfree_pb R _ _ _ _ (hpb.map ((evaluation _ _).obj U))
      ((mono_iff_injective _).1 hrU) ((mono_iff_injective _).1 hbU)
  exact hP.map (presheafToSheaf _ _)

theorem LeafCokIso_of : LeafCokIso := leafCokIso_of leafFreePb

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafBdAddPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem etale_section_boundary_of_mem_addSubgroup_closure {R : Type} [CommRing R] (K : Cx R) {Y : Scheme.{0}} (U' : Y.Opens) (n : ℤ)
    (a : Sec (K.X n) Y) (ha : a ∈ AddSubgroup.closure {a | Bd K U' n a}) : Bd K U' n a := by
  induction ha using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, map_zero _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb0, hb⟩ := hx
    obtain ⟨c, hc0, hc⟩ := hy
    refine ⟨b + c, ?_, ?_⟩
    · show ((K.X (n-1)).obj.map U'.ι.op).hom (b + c) = 0
      rw [map_add (f := _), show ((K.X (n-1)).obj.map U'.ι.op).hom b = 0 from hb0, show ((K.X (n-1)).obj.map U'.ι.op).hom c = 0 from hc0, add_zero]
    · show ((K.d (n - 1) n).hom.app (op Y)).hom (b + c) = x + y
      rw [map_add (f := _)]; rw [← hb, ← hc]
  | neg x _ hx =>
    obtain ⟨b, hb0, hb⟩ := hx
    refine ⟨-b, ?_, ?_⟩
    · show ((K.X (n-1)).obj.map U'.ι.op).hom (-b) = 0
      rw [map_neg]; rw [show ((K.X (n-1)).obj.map U'.ι.op).hom b = 0 from hb0, neg_zero]
    · show ((K.d (n - 1) n).hom.app (op Y)).hom (-b) = -x
      rw [map_neg]; rw [← hb]

theorem LeafBdAdd_of : LeafBdAdd := by
  intro R _ K X U n W a ha
  exact etale_section_boundary_of_mem_addSubgroup_closure K _ n a ha

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafTopPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem etale_sheaf_sections_restrict_restrict_eq_restrict_comp {R : Type} [CommRing R] {F : Shv R} {Y Z W : Scheme.{0}} (f : Y ⟶ Z) (g : Z ⟶ W) (a : Sec F W) :
    Sec.res f (Sec.res g a) = Sec.res (f ≫ g) a := by
  show (F.obj.map f.op).hom ((F.obj.map g.op).hom a) = (F.obj.map (f ≫ g).op).hom a
  rw [op_comp, Functor.map_comp]; rfl

theorem etale_sheaf_sections_restriction_of_zero_eq_zero {R : Type} [CommRing R] {F : Shv R} {Y Z : Scheme.{0}} (f : Y ⟶ Z) :
    Sec.res f (0 : Sec F Z) = 0 := by
  show (F.obj.map f.op).hom 0 = 0
  exact map_zero _

theorem etale_sheaf_sections_map_restrict_comm {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {Y Z : Scheme.{0}} (f : Y ⟶ Z) (a : Sec F Z) :
    Sec.map φ (Sec.res f a) = Sec.res f (Sec.map φ a) := by
  show (φ.hom.app (op Y)).hom ((F.obj.map f.op).hom a) = (G.obj.map f.op).hom ((φ.hom.app (op Z)).hom a)
  have h := φ.hom.naturality f.op
  exact congrArg (fun ψ => ψ.hom a) h

theorem LeafTop_of : LeafTop := by
  intro R _ K X U n c' hc'
  obtain ⟨h1, h2⟩ := (mem_Zc c').1 hc'
  refine ⟨Sec.res X.topIso.inv c', (mem_Zc _).2 ⟨?_, ?_⟩, ?_⟩
  · have : IsIso (⊤ : X.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
    have e : U.ι ≫ X.topIso.inv = inv ((⊤ : X.Opens).ι ∣_ U) ≫ ((⊤ : X.Opens).ι ⁻¹ᵁ U).ι := by
      rw [← cancel_mono X.topIso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
        Scheme.topIso_hom, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    rw [etale_sheaf_sections_restrict_restrict_eq_restrict_comp, e, ← etale_sheaf_sections_restrict_restrict_eq_restrict_comp, h1, etale_sheaf_sections_restriction_of_zero_eq_zero]
  · rw [etale_sheaf_sections_map_restrict_comm, h2, etale_sheaf_sections_restriction_of_zero_eq_zero]
  · intro V
    rw [etale_sheaf_sections_restrict_restrict_eq_restrict_comp]
    congr 1
    rw [← cancel_mono X.topIso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, Scheme.topIso_hom,
      Scheme.homOfLE_ι]

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafPrdHocPfX
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem sq (AN : LeafActNat) (a6 : DivisorNaturality) (q : ℕ) [NeZero q] {X : Scheme.{0}} (U : X.Opens) {E' E : Spc} (f : E' ⟶ E)
    (π' : E' ⟶ sch.obj X) (π : E ⟶ sch.obj X) (h : f ≫ π = π') {n m i k : ℤ} (x : Ht q E n i) (b : Hs q (opn U) m k) :
    Hs.pull q (abvRel U f π' π h) _ _ (Hs.act q (P := abv U π) x (Hs.pull q (abvMap U π) _ _ b)) =
      Hs.act q (P := abv U π') (pull _ f _ _ x) (Hs.pull q (abvMap U π') _ _ b) := by
  have e := AN a6 q _ _ (abvRel U f π' π h) n m i k x (Hs.pull q (abvMap U π) _ _ b)
  rw [← hs_pull_comp, abvRel_abvMap] at e
  exact e

theorem prd_sum (S : LeafSum) (HS : LeafHsSum) (AN : LeafActNat) (a6 : DivisorNaturality) (q : ℕ) [NeZero q] {X : Scheme.{0}}
    (U : X.Opens) {A : Type} (E : A → PSh) (P : PSh) (g : ∀ a, E a ⟶ P) (t : IsColimit (Cofan.mk P g))
    (π : P ⟶ yoneda.obj X) (π' : ∀ a, E a ⟶ yoneda.obj X) (h : ∀ a, g a ≫ π = π' a) {m k : ℤ} (b : Hs q (opn U) m k)
    (hb : ∀ a, Prd q U (E := disc.obj (E a)) (disc.map (π' a)) b) :
    Prd q U (E := disc.obj P) (disc.map π) b := by
  intro n i
  have h' : ∀ a, disc.map ((Cofan.mk P g).inj a) ≫ disc.map π = disc.map (π' a) := fun a => by
    rw [← disc.map_comp]; exact congrArg disc.map (h a)
  have tS : IsColimit (Cofan.mk (disc.obj P) fun a => disc.map (g a)) := isColimitCofanMkObjOfIsColimit disc E g t
  have hΦ := S (ZMod q) (tw q i) A (fun a => disc.obj (E a)) _ ⟨tS⟩ n
  have hΨ := HS q X U A E (Cofan.mk P g) ⟨t⟩ π π' h' (n + m) (i + k)
  have hP : Function.Bijective (Pi.map fun a (x : Ht q (disc.obj (E a)) n i) =>
      Hs.act q (P := abv U (disc.map (π' a))) x (Hs.pull q (abvMap U (disc.map (π' a))) _ _ b)) :=
    Function.Bijective.piMap fun a => hb a n i
  refine (Function.Bijective.of_comp_iff' hΨ _).1 ?_
  convert hP.comp hΦ using 1
  all_goals try rfl
  funext x
  funext a
  exact sq AN a6 q U _ _ _ (h' a) x b

theorem inj_aug_RPrdH {J : Type} [SmallCategory J] (D : J ⥤ PSh) {X : Scheme.{0}} (c : ∀ j, D.obj j ⟶ yoneda.obj X)
    (hc : Coc D c) (N : SimplexCategoryᵒᵖ) (σ : Fin (N.unop.len + 1) ⥤ J) :
    inj D N σ ≫ ((aug c hc).app N : (hoc D).obj N ⟶ yoneda.obj X) = c (σ.obj 0) := by
  ext U x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (hc _ _ (σ.map (homOfLE (Fin.zero_le 0)))) U) x

theorem LeafPrdHoc_of (lvl : LeafPrdLevel) (L : LeafLevel) (S : LeafSum) (HS : LeafHsSum) (AN : LeafActNat) :
    LeafPrdHoc := by
  intro hyp q _ J _ D X U c hc m k b hb
  refine lvl hyp q X U _ (aug c hc) m k b fun N => ?_
  exact prd_sum S HS AN hyp.2.2.2.2.1 q U (fun σ : Fin (N.unop.len + 1) ⥤ J => D.obj (σ.obj 0)) ((hoc D).obj N)
    (inj D N) (L J D N).some ((aug c hc).app N : (hoc D).obj N ⟶ yoneda.obj X)
    (fun σ : Fin (N.unop.len + 1) ⥤ J => c (σ.obj 0)) (inj_aug_RPrdH D c hc N) b
    (fun σ : Fin (N.unop.len + 1) ⥤ J => hb (σ.obj 0))

end LateralTheory.CohomologicalPurity.TubeCut
end
end
