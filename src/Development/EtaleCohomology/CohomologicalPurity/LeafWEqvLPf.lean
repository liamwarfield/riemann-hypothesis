module

public import Development.EtaleCohomology.CohomologicalPurity.LeafExcIdentPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafExcDegPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafExactPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafDictPf

@[expose] public section

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafWEqvLPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

abbrev Uo (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)) : Scheme.{0} :=
  (off (MvPolynomial (Fin d) R) I).toScheme

abbrev Gm : Scheme.{0} := Spec (CommRingCat.of (LaurentPolynomial ℤ))

def gmU (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)) : Uo d R I ⨯ Gm ⟶ Uo d R I := prod.fst

def LeafWGm : Prop := ∀ (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)),
  Smooth (gmU d R I) ∧ Surjective (gmU d R I)

def LeafWTors : Prop := ∀ (d : ℕ) (R : Type) [CommRing R] (I : Ideal (MvPolynomial (Fin d) R)),
  Ideal.span (Set.range MvPolynomial.X) = I →
  ∃ e : pullback (wb d R) (pr d R).hom ≅ cech (gmU d R I),
  ∀ g : (opn (off (MvPolynomial (Fin d) R) I)).left ⟶ pullback (wb d R) (pr d R).hom,
  g ≫ pullback.fst _ _ = (opn (off (MvPolynomial (Fin d) R) I)).hom ≫ wa d R → g ≫ e.hom ≫ cechAug (gmU d R I) = 𝟙 _

theorem eqv_of_iso (R : Type) [CommRing R] {E E' : Spc} (e : E ≅ E') (F : Shv R) : Eqv R e.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem eqv_comp (R : Type) [CommRing R] {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') (F : Shv R)
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := by
  intro n
  have : ⇑(pull R (f ≫ g) F n) = ⇑(pull R f F n) ∘ ⇑(pull R g F n) := funext fun x => pull_comp R f g F n x
  rw [this]; exact (hf n).comp (hg n)

theorem eqv_of_section (R : Type) [CommRing R] {E E' : Spc} (g : E ⟶ E') (s : E' ⟶ E) (F : Shv R)
    (h : g ≫ s = 𝟙 _) (hs : Eqv R s F) : Eqv R g F := by
  intro n
  have hid : ∀ x, pull R g F n (pull R s F n x) = x := fun x => by rw [← pull_comp, h, pull_id]
  have hsurj : Function.Surjective (pull R g F n) := fun x => ⟨_, hid x⟩
  refine ⟨fun a b hab => ?_, hsurj⟩
  obtain ⟨a', rfl⟩ := (hs n).2 a
  obtain ⟨b', rfl⟩ := (hs n).2 b
  rw [hid, hid] at hab; rw [hab]

theorem LeafWEqvL_of (hGm : LeafWGm) (hT : LeafWTors) : LeafWEqvL := by
  intro hH q _ d R _ I hI hq g hg i
  obtain ⟨e, he⟩ := hT d R I hI
  obtain ⟨hsm, hsu⟩ := hGm d R I
  have hA2 : Eqv _ (cechAug (gmU d R I)) (tw q i) := hH.2.1 _ (gmU d R I) (tw q i)
  exact eqv_of_section _ g _ _ (he g hg) (eqv_comp _ _ _ _ (eqv_of_iso _ e _) hA2)

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafTailNervePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def UtsR (m : ℕ) : CommRingCat.{0} ⥤ Type where
  obj A := Fin m → Aˣ
  map f := TypeCat.ofHom fun u i => Units.map f.hom.toMonoidHom (u i)
  map_id A := by ext u i; rfl
  map_comp f g := by ext u i; rfl

def Uts (m : ℕ) : Scheme.{0}ᵒᵖ ⥤ Type := Scheme.Γ ⋙ UtsR m

def evP (n : SimplexCategoryᵒᵖ) (A B : Spc) : (A ⨯ B).obj n ≅ A.obj n ⨯ B.obj n :=
  PreservesLimitPair.iso ((evaluation SimplexCategoryᵒᵖ (Scheme.{0}ᵒᵖ ⥤ Type)).obj n) A B

@[reassoc] theorem evalProdIso_hom_naturality (n : SimplexCategoryᵒᵖ) {A B A' B' : Spc} (f : A ⟶ A') (g : B ⟶ B') :
    (prod.map f g).app n ≫ (evP n A' B').hom = (evP n A B).hom ≫ prod.map (f.app n) (g.app n) := by
  simp only [evP, PreservesLimitPair.iso_hom]
  exact prodComparison_natural ((evaluation SimplexCategoryᵒᵖ (Scheme.{0}ᵒᵖ ⥤ Type)).obj n) f g

def LeafNerveSplit : Prop := ∀ (d : ℕ) (n : SimplexCategoryᵒᵖ),
  ∃ (a₁ : (Pj (d + 1) 1).obj n ≅ (Pj (d + 1) 1).obj (op (SimplexCategory.mk 0)) ⨯ Uts n.unop.len)
    (a₀ : (Pj d 0).obj n ≅ (Pj d 0).obj (op (SimplexCategory.mk 0)) ⨯ Uts n.unop.len),
    (Pj.tail d).app n ≫ a₀.hom = a₁.hom ≫ prod.map ((Pj.tail d).app (op (SimplexCategory.mk 0))) (𝟙 _)

def LeafUnitsRep : Prop := ∀ (R : Type) [CommRing R] (m : ℕ),
  ∃ (R' : Type) (_ : CommRing R') (_ : R →+* R'),
    Nonempty (Uts m ⨯ yoneda.obj (Spec (CommRingCat.of R)) ≅ yoneda.obj (Spec (CommRingCat.of R')))

theorem evalProdIso_inv_naturality (n : SimplexCategoryᵒᵖ) {A B A' B' : Spc} (f : A ⟶ A') (g : B ⟶ B') :
    (evP n A B).inv ≫ (prod.map f g).app n = prod.map (f.app n) (g.app n) ≫ (evP n A' B').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← evalProdIso_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem LeafTailNerve_of (hN : LeafNerveSplit) (hU : LeafUnitsRep) : LeafTailNerve := by
  intro d R _ n
  obtain ⟨R', _, ψ, ⟨r⟩⟩ := hU R n.unop.len
  obtain ⟨a₁, a₀, w⟩ := hN d n
  let r' : Uts n.unop.len ⨯ (sp R).obj n ≅ (sp R').obj (op (SimplexCategory.mk 0)) := r
  let f₁ : (PR (d + 1) 1 R).obj n ≅ (PR (d + 1) 1 R').obj (op (SimplexCategory.mk 0)) :=
    evP n _ _ ≪≫ prod.mapIso a₁ (Iso.refl _) ≪≫ prod.associator _ _ _ ≪≫ prod.mapIso (Iso.refl _) r' ≪≫
      (evP (op (SimplexCategory.mk 0)) (Pj (d + 1) 1) (sp R')).symm
  let f₀ : (PR d 0 R).obj n ≅ (PR d 0 R').obj (op (SimplexCategory.mk 0)) :=
    evP n _ _ ≪≫ prod.mapIso a₀ (Iso.refl _) ≪≫ prod.associator _ _ _ ≪≫ prod.mapIso (Iso.refl _) r' ≪≫
      (evP (op (SimplexCategory.mk 0)) (Pj d 0) (sp R')).symm
  have w1 : (Pj.tail d).app n ≫ a₀.hom ≫ prod.fst = a₁.hom ≫ prod.fst ≫ (Pj.tail d).app (op (SimplexCategory.mk 0)) := by
    rw [reassoc_of% w]; simp
  have w2 : (Pj.tail d).app n ≫ a₀.hom ≫ prod.snd = a₁.hom ≫ prod.snd := by
    rw [reassoc_of% w]; simp
  refine ⟨R', inferInstance, ψ, f₁, f₀, ?_⟩
  simp only [f₁, f₀, Iso.trans_hom, Iso.symm_hom, prod.mapIso_hom, Iso.refl_hom, Category.assoc]
  erw [evalProdIso_inv_naturality, evalProdIso_hom_naturality_assoc]
  congr 1
  simp only [← Category.assoc]
  congr 1
  apply prod.hom_ext
  · simp [w1, w2]
  · simp [w1, w2]

end LateralTheory.CohomologicalPurity.Thom
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafFreeCokInjPf
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
namespace LateralTheory.CohomologicalPurity

theorem exact_app_of_π {R : Type} [CommRing R] {F G : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (f : F ⟶ G)
    (V : Scheme.{0}ᵒᵖ) (m : G.obj V) (hm : (cokernel.π f).app V m = 0) : ∃ n, f.app V n = m := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.Exact := S.exact_of_g_is_cokernel (cokernelIsCokernel f)
  have h2 := hS.map ((evaluation _ _).obj V)
  rw [ShortComplex.moduleCat_exact_iff] at h2
  exact h2 m hm

theorem mapDomain_apply_eq_sum {α β M : Type*} [AddCommMonoid M] [DecidableEq β] (v : α →₀ M) (f : α → β) (t : β) :
    Finsupp.mapDomain f v t = ∑ a ∈ v.support with f a = t, v a := by
  classical
  unfold Finsupp.mapDomain
  rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.single_apply]

theorem core {α β γ M : Type*} [AddCommMonoid M] (v : α →₀ M) (f : α → β) (r : α → γ)
    (Q : β → Prop) (P : γ → Prop)
    (hv : ∀ t, ¬ Q t → Finsupp.mapDomain f v t = 0)
    (hQ : ∀ a, Q (f a) → P (r a))
    (hP : ∀ a₁ a₂, f a₁ = f a₂ → P (r a₁) → P (r a₂))
    (h : ∀ a₁ ∈ v.support, ∀ a₂ ∈ v.support, f a₁ = f a₂ → r a₁ = r a₂ ∨ P (r a₁)) :
    ∀ z, ¬ P z → Finsupp.mapDomain r v z = 0 := by
  classical
  intro z hz
  rw [mapDomain_apply_eq_sum]
  set s' := v.support.filter (fun a => r a = z)
  rw [← Finset.sum_fiberwise_of_maps_to (s := s') (t := s'.image f) (g := f)
    (fun a ha => Finset.mem_image_of_mem f ha)]
  refine Finset.sum_eq_zero fun t ht => ?_
  obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.1 ht
  have ha₀' := Finset.mem_filter.1 ha₀
  have hQ0 : ¬ Q (f a₀) := fun hq => hz (ha₀'.2 ▸ hQ a₀ hq)
  have e : (s'.filter fun a => f a = f a₀) = v.support.filter (fun a => f a = f a₀) := by
    ext a
    simp only [s', Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rcases h a h1 a₀ ha₀'.1 h3 with e | p
      · rw [e, ha₀'.2]
      · exact absurd (ha₀'.2 ▸ hP a a₀ h3 p) hz
  rw [e]
  have := mapDomain_apply_eq_sum v f (f a₀)
  rw [hv _ hQ0] at this
  convert this.symm

theorem exists_covering_finset {T : Scheme.{0}} {ι : Type*} (s : Finset ι)
    (Pr : ι → ∀ ⦃V : Scheme.{0}⦄, (V ⟶ T) → Prop)
    (hPr : ∀ p ∈ s, ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g → Pr p g) :
    ∃ S ∈ Scheme.etaleTopology T, ∀ p ∈ s, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g → Pr p g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, Scheme.etaleTopology.top_mem T, by simp⟩
  | insert q s hq ih =>
    obtain ⟨S₁, h₁, H₁⟩ := ih (fun p hp => hPr p (Finset.mem_insert_of_mem hp))
    obtain ⟨S₂, h₂, H₂⟩ := hPr q (Finset.mem_insert_self q s)
    refine ⟨S₁ ⊓ S₂, Scheme.etaleTopology.intersection_covering h₁ h₂, ?_⟩
    intro p hp V g hg
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact H₂ g hg.2
    · exact H₁ p hp g hg.1

theorem mem_range_mapDomain {α β M : Type*} [AddCommMonoid M] (u : α → β) (w : β →₀ M)
    (hw : ∀ z, (¬ ∃ x, u x = z) → w z = 0) : ∃ n : α →₀ M, Finsupp.mapDomain u n = w := by
  have hmem : w ∈ Finsupp.supported M ℕ (u '' Set.univ) := by
    rw [Finsupp.mem_supported]
    intro z hz
    by_contra hc
    exact (Finsupp.mem_support_iff.1 hz) (hw z (fun ⟨x, hx⟩ => hc ⟨x, trivial, hx⟩))
  rw [← Finsupp.lmapDomain_supported] at hmem
  obtain ⟨n, _, hn⟩ := hmem
  exact ⟨n, hn⟩

theorem leafFreeCokInj : LeafFreeCokInj := by
  intro R _ A' B' A B i' i a b w h1 h3
  have key : ∀ (T : Scheme.{0}) (z : (cokernel ((freeP R).map i')).obj (op T)),
      (pcok R i' i a b w).app (op T) z = 0 → Presheaf.equalizerSieve z 0 ∈ Scheme.etaleTopology T := by
    intro T z hz
    obtain ⟨v, rfl⟩ := π_app_surj R i' (op T) z
    rw [pcok_π_apply] at hz
    obtain ⟨n, hn⟩ := exact_app_of_π _ _ _ hz
    have hn' : Finsupp.mapDomain (fun x : ULift.{1} (A.obj (op T)) => ULift.up (i.app (op T) x.down)) n =
        Finsupp.mapDomain (fun x : ULift.{1} (B'.obj (op T)) => ULift.up (b.app (op T) x.down)) v := hn
    let Pr : (ULift.{1} (B'.obj (op T)) × ULift.{1} (B'.obj (op T))) → ∀ ⦃V : Scheme.{0}⦄, (V ⟶ T) → Prop :=
      fun p V g => b.app (op T) p.1.down = b.app (op T) p.2.down →
        B'.map g.op p.1.down = B'.map g.op p.2.down ∨
          ∃ x : A.obj (op V), i.app (op V) x = b.app (op V) (B'.map g.op p.1.down)
    obtain ⟨S, hS, HS⟩ := exists_covering_finset (v.support ×ˢ v.support) Pr (by
      intro p _
      by_cases he : b.app (op T) p.1.down = b.app (op T) p.2.down
      · obtain ⟨S, hS, H⟩ := h3 T p.1.down p.2.down he
        exact ⟨S, hS, fun V g hg _ => H g hg⟩
      · exact ⟨⊤, Scheme.etaleTopology.top_mem T, fun V g _ he' => absurd he' he⟩)
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V g hg
    show (cokernel ((freeP R).map i')).map g.op _ = (cokernel ((freeP R).map i')).map g.op 0
    rw [map_zero, ← NatTrans.naturality_apply]
    have hcore := core v (fun x : ULift.{1} (B'.obj (op T)) => (ULift.up.{1} (b.app (op T) x.down) : ULift.{1} (B.obj (op T))))
      (fun x : ULift.{1} (B'.obj (op T)) => ULift.up (B'.map g.op x.down))
      (fun t : ULift.{1} (B.obj (op T)) => ∃ x, i.app (op T) x = t.down) (fun z => ∃ x', i'.app (op V) x' = z.down)
      (by
        intro t ht
        have := Finsupp.mapDomain_notin_range n t (by
          rintro ⟨x, hx⟩
          exact ht ⟨x.down, congrArg ULift.down hx⟩)
        exact (DFunLike.congr_fun hn' t).symm.trans this)
      (by
        rintro a₀ ⟨x, hx⟩
        obtain ⟨x', hx'⟩ := h1 T a₀.down x hx
        exact ⟨A'.map g.op x', by rw [NatTrans.naturality_apply, hx']⟩)
      (by
        rintro a₁ a₂ he ⟨x', hx'⟩
        have he' : b.app (op T) a₁.down = b.app (op T) a₂.down := congrArg ULift.down he
        refine h1 V (B'.map g.op a₂.down) (a.app (op V) x') ?_
        have := ConcreteCategory.congr_hom (NatTrans.congr_app w (op V)) x'
        simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at this
        rw [← this, hx', NatTrans.naturality_apply, NatTrans.naturality_apply, he'])
      (by
        intro a₁ ha₁ a₂ ha₂ he
        rcases HS (a₁, a₂) (Finset.mem_product.2 ⟨ha₁, ha₂⟩) g hg (congrArg ULift.down he) with e | ⟨x, hx⟩
        · left; exact congrArg ULift.up e
        · right; exact h1 V _ x hx)
    obtain ⟨n', hn''⟩ := mem_range_mapDomain (fun x : ULift.{1} (A'.obj (op V)) => ULift.up (i'.app (op V) x.down)) _
      (fun z hz => hcore z (fun ⟨x', hx'⟩ => hz ⟨ULift.up x', congrArg ULift.up hx' |>.trans rfl⟩))
    have e2 : ((freeP R).obj B').map g.op v = ((freeP R).map i').app (op V) n' := hn''.symm
    rw [e2]
    exact π_freeP_apply R i' (op V) n'
  constructor
  intro X x y hxy
  cases X with | op T =>
  refine Scheme.etaleTopology.superset_covering ?_ (key T (x - y) (by rw [map_sub, hxy, sub_self]))
  intro V g hg
  have hg' : (cokernel ((freeP R).map i')).map g.op (x - y) = (cokernel ((freeP R).map i')).map g.op 0 := hg
  rw [map_sub, map_zero, sub_eq_zero] at hg'
  exact hg'

theorem LeafFreeCokInj_of : LeafFreeCokInj := leafFreeCokInj

end LateralTheory.CohomologicalPurity
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafTailRep0OfVec
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

def Vo (N k : ℕ) : PSh := vecCat N k ⋙ Cat.objects

def voTail (d : ℕ) : Vo (d + 1) 1 ⟶ Vo d 0 where
  app U := TypeCat.ofHom fun v => (Vec.tail d U.unop).obj v
  naturality _ _ _ := rfl

def nerve0 (N k : ℕ) : (Pj N k).obj (op (SimplexCategory.mk 0)) ≅ Vo N k :=
  NatIso.ofComponents (fun U =>
    { hom := TypeCat.ofHom fun (F : ComposableArrows (Vec N k U.unop) 0) => F.obj 0
      inv := TypeCat.ofHom fun v => ComposableArrows.mk₀ (C := Vec N k U.unop) v
      hom_inv_id := by
        ext F
        exact ComposableArrows.ext₀ rfl
      inv_hom_id := rfl })
    (fun _ => rfl)

def LeafRepVec : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (_ : R →+* A),
    I.FG ∧ ∃ (h : off (Polynomial A) (I.map Polynomial.C) ≤
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I)
      (e₁ : Vo (d + 1) 1 ⨯ yoneda.obj (Spec (CommRingCat.of R)) ≅ yoneda.obj (off (Polynomial A) (I.map Polynomial.C)).toScheme)
      (e₂ : Vo d 0 ⨯ yoneda.obj (Spec (CommRingCat.of R)) ≅ yoneda.obj (off A I).toScheme),
      prod.map (voTail d) (𝟙 _) ≫ e₂.hom =
        e₁.hom ≫ yoneda.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)

theorem LeafTailRep0_of_vec (hV : LeafRepVec) : LeafTailRep0 := by
  intro d R _
  obtain ⟨A, _, I, φ, hI, h, f₁, f₂, w⟩ := hV d R
  let E := (evaluation SimplexCategoryᵒᵖ PSh).obj (op (SimplexCategory.mk 0))
  let sq : E.obj (sp R) ≅ yoneda.obj (Spec (CommRingCat.of R)) := Iso.refl _
  refine ⟨A, inferInstance, I, φ, hI, h,
    PreservesLimitPair.iso E _ _ ≪≫ prod.mapIso (nerve0 (d + 1) 1) sq ≪≫ f₁,
    PreservesLimitPair.iso E _ _ ≪≫ prod.mapIso (nerve0 d 0) sq ≪≫ f₂, ?_⟩
  simp only [Iso.trans_hom, PreservesLimitPair.iso_hom, prod.mapIso_hom, Category.assoc]
  change E.map (prod.map _ _) ≫ _ = _
  rw [prodComparison_natural_assoc, prod.map_map_assoc, ← w, prod.map_map_assoc]
  rfl

def LeafRepPt : Prop := ∀ (d : ℕ) (R : Type) [CommRing R],
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (_ : R →+* A),
    I.FG ∧ ∃ (h : off (Polynomial A) (I.map Polynomial.C) ≤
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I)
      (E₁ : ∀ U : Scheme.{0}, Vec (d + 1) 1 U × (U ⟶ Spec (CommRingCat.of R)) ≃
        (U ⟶ (off (Polynomial A) (I.map Polynomial.C)).toScheme))
      (E₂ : ∀ U : Scheme.{0}, Vec d 0 U × (U ⟶ Spec (CommRingCat.of R)) ≃ (U ⟶ (off A I).toScheme)),
      (∀ {V U : Scheme.{0}} (f : V ⟶ U) v g, E₁ V ((Vec.map _ _ f).obj v, f ≫ g) = f ≫ E₁ U (v, g)) ∧
      (∀ {V U : Scheme.{0}} (f : V ⟶ U) v g, E₂ V ((Vec.map _ _ f).obj v, f ≫ g) = f ≫ E₂ U (v, g)) ∧
      ∀ (U : Scheme.{0}) v g, E₂ U ((Vec.tail d U).obj v, g) =
        E₁ U (v, g) ≫ (Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h

def isoOfPt {F G : PSh} {X : Scheme.{0}} (E : ∀ U : Scheme.{0}, F.obj (op U) × G.obj (op U) ≃ (U ⟶ X))
    (hE : ∀ {V U : Scheme.{0}} (f : V ⟶ U) a b, E V (F.map f.op a, G.map f.op b) = f ≫ E U (a, b)) :
    F ⨯ G ≅ yoneda.obj X :=
  FunctorToTypes.binaryProductIso F G ≪≫
    NatIso.ofComponents (fun U => (E U.unop).toIso) (fun f => by
      ext ⟨a, b⟩
      exact hE f.unop a b)

theorem LeafRepVec_of (hP : LeafRepPt) : LeafRepVec := by
  intro d R _
  obtain ⟨A, _, I, φ, hI, h, E₁, E₂, n₁, n₂, sq⟩ := hP d R
  refine ⟨A, inferInstance, I, φ, hI, h, isoOfPt (F := Vo (d + 1) 1) E₁ (fun f a b => n₁ f a b),
    isoOfPt (F := Vo d 0) E₂ (fun f a b => n₂ f a b), ?_⟩
  have key : prod.map (voTail d) (𝟙 (yoneda.obj (Spec (CommRingCat.of R)))) ≫
      (FunctorToTypes.binaryProductIso _ _).hom = (FunctorToTypes.binaryProductIso _ _).hom ≫
      FunctorToTypes.prod.lift (FunctorToTypes.prod.fst ≫ voTail d) FunctorToTypes.prod.snd := by
    apply (cancel_mono (FunctorToTypes.binaryProductIso _ _).inv).1
    apply Limits.prod.hom_ext <;> simp <;> rw [← Category.assoc, FunctorToTypes.binaryProductIso_hom_comp_fst]
  simp only [isoOfPt, Iso.trans_hom]
  rw [reassoc_of% key, Category.assoc]
  congr 1
  ext U ⟨v, g⟩
  exact sq U.unop v g

theorem LeafTailRep0_of (hP : LeafRepPt) : LeafTailRep0 := LeafTailRep0_of_vec (LeafRepVec_of hP)

end LateralTheory.CohomologicalPurity.Thom
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafWCovPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

theorem wincl_mono (d : ℕ) : Mono (Wincl d) := by
  have h : ∀ n, Mono ((Wincl d).app n) := by
    intro n
    have : ∀ U, Mono (((Wincl d).app n).app U) := by
      intro U
      rw [mono_iff_injective]
      intro F G hFG
      change (F : ComposableArrows (WVec d U.unop) _) ⋙ WVec.incl d U.unop = G ⋙ WVec.incl d U.unop at hFG
      exact CategoryTheory.Functor.hext (fun i => Subtype.ext (congrArg (fun K => K.obj i) hFG))
        (fun i j a => Functor.hcongr_hom hFG a)
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app _

theorem wb_mono (d : ℕ) (R : Type) [CommRing R] : Mono (wb d R) := by
  have := wincl_mono d
  unfold wb; infer_instance

def LocCov {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) : Prop :=
  ∀ (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}) (x : (E.obj n).obj (op X)), ∃ (ι : Type) (O : ι → X.Opens),
    iSup O = ⊤ ∧ ∀ i, (∃ y, (f.app n).app (op (O i : Scheme.{0})) y = (E.obj n).map (O i).ι.op x) ∨
      (∃ y, (g.app n).app (op (O i : Scheme.{0})) y = (E.obj n).map (O i).ι.op x)

def LeafCovLoc : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Mono f → Mono g →
  LocCov f g → Cover2 R f g

def LeafWLoc : Prop := ∀ (d : ℕ) (R : Type) [CommRing R], LocCov (wb d R) (pr d R).hom

theorem LeafWCov_of (hG : LeafGeo) (hC : LeafCovLoc) (hW : LeafWLoc) : LeafWCov := by
  intro _ q _ d R _ _
  exact hC (ZMod q) (wb d R) (pr d R).hom (wb_mono d R) (hG.1 d R) (hW d R)

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafConeCokPf
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem isIso_cokMap_f {R : Type} [CommRing R] {K L K' L' : Cx R} (f : K ⟶ L) (f' : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (comm : f ≫ b = a ≫ f') (n : ℤ)
    (h : IsIso (cokernel.map _ _ _ _ (sqw comm n))) : IsIso ((cokernel.map f f' a b comm).f n) := by
  let E := HomologicalComplex.eval (Shv R) (ComplexShape.up ℤ) n
  let e1 : (cokernel f).X n ≅ cokernel (f.f n) := PreservesCokernel.iso E f
  let e2 : (cokernel f').X n ≅ cokernel (f'.f n) := PreservesCokernel.iso E f'
  have h1 : (cokernel.π f).f n ≫ e1.hom = cokernel.π (f.f n) := PreservesCokernel.π_iso_hom E f
  have h2 : (cokernel.π f').f n ≫ e2.hom = cokernel.π (f'.f n) := PreservesCokernel.π_iso_hom E f'
  have hep : Epi ((cokernel.π f).f n) := by
    have e : (cokernel.π f).f n = cokernel.π (f.f n) ≫ e1.inv := by
      rw [← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [e]; infer_instance
  have key : (cokernel.map f f' a b comm).f n ≫ e2.hom = e1.hom ≫ cokernel.map _ _ _ _ (sqw comm n) := by
    rw [← cancel_epi ((cokernel.π f).f n), reassoc_of% h1, ← HomologicalComplex.comp_f_assoc]
    simp [cokernel.map, h2]
  have key' : (cokernel.map f f' a b comm).f n = e1.hom ≫ cokernel.map _ _ _ _ (sqw comm n) ≫ e2.inv := by
    rw [← Category.assoc, ← key, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [key']; infer_instance

theorem shortExact_cok {R : Type} [CommRing R] {K L : Cx R} (f : K ⟶ L) (hf : ∀ n, Mono (f.f n)) :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact := by
  have : Mono f := HomologicalComplex.mono_of_mono_f _ hf
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)) inferInstance inferInstance

theorem leafConeCok_of : LeafConeCok := by
  intro R _ K L K' L' f f' a b comm hf hf' hc
  let S1 := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let S2 := ShortComplex.mk f' (cokernel.π f') (cokernel.condition f')
  let φ : S1 ⟶ S2 := ⟨a, b, cokernel.map f f' a b comm, comm.symm, by simp [S1, S2]⟩
  have q1 := mappingCone.quasiIso_descShortComplex (shortExact_cok f hf)
  have q2 := mappingCone.quasiIso_descShortComplex (shortExact_cok f' hf')
  have hcomp : ∀ n, IsIso (φ.τ₃.f n) := fun n => isIso_cokMap_f f f' a b comm n (hc n)
  have : IsIso φ.τ₃ := HomologicalComplex.Hom.isIso_of_components _
  have hm := mappingCone.map_descShortComplex S1 S2 φ
  have : QuasiIso (mappingCone.descShortComplex S1 ≫ φ.τ₃) := inferInstance
  have : QuasiIso (mappingCone.map f f' a b comm ≫ mappingCone.descShortComplex S2) := by
    change QuasiIso (mappingCone.map S1.f S2.f φ.τ₁ φ.τ₂ φ.comm₁₂.symm ≫ mappingCone.descShortComplex S2)
    rw [hm]; infer_instance
  exact (quasiIso_iff_comp_right _ (mappingCone.descShortComplex S2)).1 this

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafAugInjPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def EtaleOpenCovSieve : Prop := ∀ (T : Scheme.{0}) (S : Sieve T),
  (∀ t : T, ∃ V : T.Opens, t ∈ V ∧ S V.ι) → S ∈ Scheme.etaleTopology.{0} T

def EtaleAugInjAt : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R] (n : ℕ)
    (T : Scheme.{0}ᵒᵖ) (x : ((((chainsP R).obj (hoc (D ⋙ yoneda))).X n).obj T)),
    Cyc _ n T x → Bdy _ n T ((((chainsP R).map (aug _ hc)).f n).app T |>.hom x) →
    ∀ t : T.unop, ∃ V : T.unop.Opens, t ∈ V ∧
      Bdy _ n (op (V : Scheme.{0})) (((((chainsP R).obj (hoc (D ⋙ yoneda))).X n).map V.ι.op).hom x)

theorem bdy_res {R : Type} [CommRing R] (K : PCx R) (n : ℕ) {U V : Scheme.{0}} (g : V ⟶ U) (x : (K.X n).obj (op U))
    (h : Bdy K n (op U) x) : Bdy K n (op V) (((K.X n).map g.op).hom x) := by
  obtain ⟨y, rfl⟩ := h
  refine ⟨((K.X (n + 1)).map g.op).hom y, ?_⟩
  have := (K.d (n + 1) n).naturality g.op
  exact (ConcreteCategory.congr_hom this y).symm.trans rfl |>.symm ▸ rfl

def bdySieve {R : Type} [CommRing R] (K : PCx R) (n : ℕ) (T : Scheme.{0}) (x : (K.X n).obj (op T)) : Sieve T where
  arrows U f := Bdy K n (op U) (((K.X n).map f.op).hom x)
  downward_closed {U V} f hf g := by
    have e : ((K.X n).map (g ≫ f).op).hom x = ((K.X n).map g.op).hom (((K.X n).map f.op).hom x) := by
      rw [op_comp, Functor.map_comp]; rfl
    rw [e]; exact bdy_res K n g _ hf

theorem EtaleAugInj_of_openCovSieve (hc0 : EtaleOpenCovSieve) (ha : EtaleAugInjAt) : LeafAugInj := by
  intro J _ D X c ho hcov hdir hc R _ n T x hx hb
  refine ⟨bdySieve _ n T.unop x, hc0 _ _ fun t => ?_, fun U f hf => hf⟩
  obtain ⟨V, hV, h⟩ := ha J D X c ho hcov hdir hc R n T x hx hb t
  exact ⟨V, hV, h⟩

theorem etaleOpenCovSieve : EtaleOpenCovSieve := by
  intro T S h
  choose V hV hS using h
  apply Scheme.zariskiTopology_le_etaleTopology
  rw [Scheme.zariskiTopology, Scheme.mem_grothendieckTopology_iff]
  refine ⟨Scheme.Cover.mkOfCovers T (fun t => (V t : Scheme.{0})) (fun t => (V t).ι)
    (fun x => ⟨x, ⟨x, hV x⟩, by simp⟩), ?_⟩
  rintro Y g ⟨i⟩
  exact hS i

theorem EtaleAugInj_of_augInjAt (ha : EtaleAugInjAt) : LeafAugInj := EtaleAugInj_of_openCovSieve etaleOpenCovSieve ha

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafDblCokPf
noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem chainsXIso_nat (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p))) =
      ((chains R).map f).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom := by
  have h : ComplexShape.embeddingDownNat.f p = -(p : ℤ) := rfl
  change _ = (HomologicalComplex.extendMap ((chainsN R).map f) _).f _ ≫ _
  rw [HomologicalComplex.extendMap_f _ _ h]
  simp only [chainsXIso]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

instance freePresSpan (R : Type) [CommRing R] : PreservesColimitsOfShape WalkingSpan (free R) := by
  have : PreservesColimitsOfShape WalkingSpan (ModuleCat.free.{1} (ULift.{1} R)) :=
    (ModuleCat.adj (ULift.{1} R)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape WalkingSpan (freeP R) := by
    unfold freeP; infer_instance
  unfold free; infer_instance

theorem free_isPushout (R : Type) [CommRing R] (P : Arrow Spc) (p : ℕ) :
    IsPushout ((free R).map (P.hom.app (op (SimplexCategory.mk p))))
      ((free R).map (P.hom.app (op (SimplexCategory.mk p))))
      ((free R).map ((dbl.inl P).app (op (SimplexCategory.mk p))))
      ((free R).map ((dbl.inr P).app (op (SimplexCategory.mk p)))) := by
  have h0 : IsPushout P.hom P.hom (dbl.inl P) (dbl.inr P) := IsPushout.of_hasPushout P.hom P.hom
  have h1 := h0.map ((evaluation _ PSh).obj (op (SimplexCategory.mk p)))
  exact h1.map (free R)

theorem chains_isPushout (R : Type) [CommRing R] (P : Arrow Spc) (p : ℕ) :
    IsPushout (((chains R).map P.hom).f (-(p : ℤ))) (((chains R).map P.hom).f (-(p : ℤ)))
      (((chains R).map (dbl.inl P)).f (-(p : ℤ))) (((chains R).map (dbl.inr P)).f (-(p : ℤ))) :=
  (free_isPushout R P p).of_iso' (chainsXIso R _ p) (chainsXIso R _ p) (chainsXIso R _ p)
    (chainsXIso R _ p) (chainsXIso_nat R _ p) (chainsXIso_nat R _ p)
    (chainsXIso_nat R _ p) (chainsXIso_nat R _ p)

theorem leafDblCok_of : LeafDblCok := by
  intro R _ P _ n
  by_cases hn : ∃ p : ℕ, -(p : ℤ) = n
  · obtain ⟨p, rfl⟩ := hn
    exact isIso_cokernel_map_of_isPushout (chains_isPushout R P p)
  · push Not at hn
    have hz : ∀ E : Spc, IsZero (((chains R).obj E).X n) := fun E =>
      HomologicalComplex.isZero_extend_X _ _ _ (fun i => hn i)
    have hc : ∀ {E E' : Spc} (f : E ⟶ E'), IsZero (cokernel (((chains R).map f).f n)) := fun f => by
      rw [IsZero.iff_id_eq_zero]
      exact coequalizer.hom_ext ((hz _).eq_of_src _ _)
    exact ⟨⟨0, (hc _).eq_of_src _ _, (hc _).eq_of_src _ _⟩⟩

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafChPushPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

section
variable (R : Type) [CommRing R]

instance pcFreeP : PreservesColimitsOfShape WalkingSpan (freeP R) := by
  have : PreservesColimitsOfShape WalkingSpan (ModuleCat.free (ULift.{1} R)) :=
    (ModuleCat.adj (ULift.{1} R)).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape WalkingSpan (uliftFunctor.{1, 0} ⋙ ModuleCat.free (ULift.{1} R)) :=
    inferInstance
  unfold freeP; infer_instance

instance pcFree : PreservesColimitsOfShape WalkingSpan (free R) := by
  unfold free; infer_instance

instance pcWhisk : PreservesColimitsOfShape WalkingSpan ((SimplicialObject.whiskering _ _).obj (free R)) := by
  unfold SimplicialObject.whiskering; infer_instance

instance preservesSpanColimitsFaceMapComplex : PreservesColimitsOfShape WalkingSpan (AlgebraicTopology.alternatingFaceMapComplex (Shv R)) := by
  refine HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun n => ?_)
  have e : AlgebraicTopology.alternatingFaceMapComplex (Shv R) ⋙ HomologicalComplex.eval _ _ n ≅
      (evaluation _ _).obj (op (SimplexCategory.mk n)) :=
    NatIso.ofComponents (fun X => Iso.refl _) (fun f => by
      dsimp; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  exact preservesColimitsOfShape_of_natIso e.symm

instance pcExt : PreservesColimitsOfShape WalkingSpan
    (ComplexShape.embeddingDownNat.extendFunctor (Shv R)) := by
  refine HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun i => ?_)
  by_cases h : ∃ j, ComplexShape.embeddingDownNat.f j = i
  · obtain ⟨j, hj⟩ := h
    have e : ComplexShape.embeddingDownNat.extendFunctor (Shv R) ⋙ HomologicalComplex.eval _ _ i ≅
        HomologicalComplex.eval _ _ j :=
      NatIso.ofComponents (fun K => K.extendXIso _ hj) (fun f => by
        change (HomologicalComplex.extendMap f _).f i ≫ _ = _ ≫ f.f j
        rw [HomologicalComplex.extendMap_f _ _ hj]; simp)
    exact preservesColimitsOfShape_of_natIso e.symm
  · refine Functor.preservesColimitsOfShape_of_isZero _ ?_ _
    rw [Functor.isZero_iff]
    intro K
    exact K.isZero_extend_X _ i (fun j hj => h ⟨j, hj⟩)

instance pcChains : PreservesColimitsOfShape WalkingSpan (chains R) := by
  unfold chains chainsN; infer_instance

end

theorem LeafChPush_of : LeafChPush := by
  intro q P
  set_option synthInstance.maxHeartbeats 200000 in
    have h : IsPushout P.hom P.hom (dbl.inl P) (dbl.inr P) := IsPushout.of_hasPushout _ _
    exact (chains (ZMod q)).map_isPushout h

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafFreeCovPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.FreeCovPf

variable {X : Scheme.{0}} (U V : X.Opens)

def pieces : Bool → Scheme.{0}
  | true => U.toScheme
  | false => V.toScheme

def incl : (b : Bool) → pieces U V b ⟶ (U ⊔ V : X.Opens).toScheme
  | true => X.homOfLE le_sup_left
  | false => X.homOfLE le_sup_right

theorem cover_mem :
    Sieve.ofArrows (pieces U V) (incl U V) ∈ Scheme.etaleTopology.{0} (U ⊔ V : X.Opens).toScheme := by
  apply Precoverage.generate_mem_toGrothendieck
  refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun x => ?_, fun b => ?_⟩
  · have hx : x.1 ∈ U ⊔ V := x.2
    rcases (TopologicalSpace.Opens.mem_sup.1 hx) with h | h
    · exact ⟨true, ⟨⟨x.1, h⟩, Subtype.ext (Scheme.homOfLE_apply (le_sup_left : U ≤ U ⊔ V) _)⟩⟩
    · exact ⟨false, ⟨⟨x.1, h⟩, Subtype.ext (Scheme.homOfLE_apply (le_sup_right : V ≤ U ⊔ V) _)⟩⟩
  · cases b
    · exact (inferInstance : Etale (X.homOfLE (le_sup_right : V ≤ U ⊔ V)))
    · exact (inferInstance : Etale (X.homOfLE (le_sup_left : U ≤ U ⊔ V)))

theorem sec_zero (R : Type) [CommRing R] (Zs : Shv R) (z : Zs.obj.obj (op (U ⊔ V : X.Opens).toScheme))
    (h : ∀ b, Zs.obj.map (incl U V b).op z = 0) : z = 0 := by
  have e := Presheaf.IsSheaf.hom_ext_ofArrows Zs.property (incl U V) (cover_mem U V)
    (E := ModuleCat.of (ULift.{1} R) (ULift.{1} R))
    (x := ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ z)) (y := 0) (fun b => by
      ext1
      apply LinearMap.ext_ring
      simp [h b])
  have := congrArg (fun φ => φ.hom (1 : ULift.{1} R)) e
  simpa using this

theorem main (R : Type) [CommRing R] :
    Epi (biprod.desc ((free R).map (yoneda.map (X.homOfLE (le_sup_left : U ≤ U ⊔ V))))
      ((free R).map (yoneda.map (X.homOfLE (le_sup_right : V ≤ U ⊔ V))))) := by
  apply Preadditive.epi_of_cancel_zero
  intro Zs g hg
  have ha := congrArg (fun k => biprod.inl ≫ k) hg
  have hb := congrArg (fun k => biprod.inr ≫ k) hg
  simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, comp_zero] at ha hb
  let adj := sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  let W := (U ⊔ V : X.Opens).toScheme
  let g' := adj.homEquiv _ _ g
  let z := g'.app (op W) (ModuleCat.freeMk (ULift.up (𝟙 W)))
  have hval : ∀ (T : Scheme.{0}) (t : T ⟶ W),
      g'.app (op T) (ModuleCat.freeMk (ULift.up t : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op T)))) = Zs.obj.map t.op z := by
    intro T t
    have := congrArg (fun φ => φ.hom (ModuleCat.freeMk (ULift.up (𝟙 W) : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op W))))) (g'.naturality t.op)
    have key : ((freeP R).obj (yoneda.obj W)).map t.op (ModuleCat.freeMk (ULift.up (𝟙 W) : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op W)))) = ModuleCat.freeMk (ULift.up t : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op T))) := by
      simp [freeP, ModuleCat.freeMk, ModuleCat.free]
      erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rfl
    exact (congrArg (fun v => (g'.app (op T)) v) key).symm.trans this
  have h0 : ∀ (P : PSh), adj.homEquiv _ _ (0 : (presheafToSheaf _ _).obj ((freeP R).obj P) ⟶ Zs) = 0 := by
    intro P
    rw [Adjunction.homEquiv_unit]
    simp
  have hres : ∀ {Y : Scheme.{0}} (i : Y ⟶ W), (free R).map (yoneda.map i) ≫ g = 0 → Zs.obj.map i.op z = 0 := by
    intro Y i hi
    have h1 : adj.homEquiv _ _ ((presheafToSheaf _ _).map ((freeP R).map (yoneda.map i)) ≫ g) =
        (freeP R).map (yoneda.map i) ≫ g' :=
      adj.homEquiv_naturality_left _ _
    have hi' : (presheafToSheaf _ _).map ((freeP R).map (yoneda.map i)) ≫ g = 0 := hi
    rw [hi', h0] at h1
    have h2 := congrArg (fun φ => (φ.app (op Y)).hom (ModuleCat.freeMk (ULift.up (𝟙 Y) : uliftFunctor.{1, 0}.obj ((yoneda.obj Y).obj (op Y))))) h1
    have key : ((freeP R).map (yoneda.map i)).app (op Y) (ModuleCat.freeMk (ULift.up (𝟙 Y) : uliftFunctor.{1, 0}.obj ((yoneda.obj Y).obj (op Y)))) = ModuleCat.freeMk (ULift.up i : uliftFunctor.{1, 0}.obj ((yoneda.obj W).obj (op Y))) := by
      simp [freeP, ModuleCat.freeMk, ModuleCat.free]
      erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rfl
    rw [← hval]
    exact ((congrArg (fun v => (g'.app (op Y)) v) key).symm.trans h2.symm)
  have hz : z = 0 := sec_zero U V R Zs z (fun b => by
    cases b
    · exact hres _ hb
    · exact hres _ ha)
  have hg' : g' = 0 := by
    apply NatTrans.ext
    funext T
    induction T using Opposite.rec with | op T => ?_
    apply ModuleCat.free_hom_ext
    rintro ⟨t⟩
    erw [hval T t]
    rw [hz, map_zero]
    rfl
  exact (adj.homEquiv _ _).injective (hg'.trans (h0 _).symm)

theorem LeafFreeCov_of : LateralTheory.CohomologicalPurity.Thom.LeafFreeCov := fun R _ _ U V => main U V R

end LateralTheory.CohomologicalPurity.FreeCovPf
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.FinLeafBd
namespace LateralTheory.Fin.LeafBd
theorem etale_boundary_monomorphism_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafMono := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafMono_of
theorem etale_relative_boundary_pushout_property_holds : LateralTheory.CohomologicalPurity.Bd.LeafPush := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafPush_of
theorem etale_boundary_good_pair_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafGood := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafGood_of
theorem etale_boundary_connecting_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafDelta := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafDelta_of
theorem etale_boundary_exact_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafExact := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafExact_of
theorem etale_boundary_generator_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafGen := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafGen_of
theorem etale_boundary_image_hom_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafImgHom := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafImgHom_of <;> first | exact etale_boundary_generator_of_thom_isomorphism
theorem etale_boundary_image_of_thom_isomorphism : LateralTheory.CohomologicalPurity.Bd.LeafImg := by
  apply LateralTheory.CohomologicalPurity.Bd.LeafImg_of <;> first | exact etale_boundary_image_hom_of_thom_isomorphism
theorem etale_boundary_map_of_thom_isomorphism : LateralTheory.CohomologicalPurity.LeafBd := by
  apply LateralTheory.CohomologicalPurity.Bd.goal_of <;> first | exact etale_boundary_monomorphism_of_thom_isomorphism | exact etale_relative_boundary_pushout_property_holds | exact etale_boundary_good_pair_of_thom_isomorphism | exact etale_boundary_connecting_of_thom_isomorphism | exact etale_boundary_exact_of_thom_isomorphism | exact etale_boundary_generator_of_thom_isomorphism | exact etale_boundary_image_hom_of_thom_isomorphism | exact etale_boundary_image_of_thom_isomorphism
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafBd := etale_boundary_map_of_thom_isomorphism
end LateralTheory.Fin.LeafBd
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafMLevPf
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

abbrev levF (n : SimplexCategoryᵒᵖ) : Spc ⥤ Spc := (evaluation SimplexCategoryᵒᵖ PSh).obj n ⋙ disc

theorem LeafMLev_of : LeafMLev := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro P' P φ n
  let F := levF n
  have hc : F.map (P'.hom ≫ φ.right) = F.map P'.hom ≫ F.map φ.right := F.map_comp _ _
  let a : disc.obj ((MM φ).obj n) ≅ MM ((lev n).map φ) :=
    (PreservesPushout.iso F P'.hom (P'.hom ≫ φ.right)).symm ≪≫ pushout.congrHom rfl hc
  let b : disc.obj ((dbl P).obj n) ≅ dbl ((lev n).obj P) :=
    (PreservesPushout.iso F P.hom P.hom).symm
  refine ⟨a, b, ?_⟩
  rw [← Iso.inv_comp_eq]
  change (pushout.congrHom rfl hc).inv ≫ (PreservesPushout.iso F P'.hom (P'.hom ≫ φ.right)).hom ≫ F.map (gM φ) ≫
    (PreservesPushout.iso F P.hom P.hom).inv = gM ((lev n).map φ)
  apply pushout.hom_ext
  · rw [pushout.congrHom_inv, pushout.inl_desc_assoc, Category.id_comp]
    erw [PreservesPushout.inl_iso_hom_assoc, ← F.map_comp_assoc, pushout.inl_desc, pushout.inl_desc, F.map_comp_assoc]
    erw [PreservesPushout.inl_iso_inv]
    rfl
  · rw [pushout.congrHom_inv, pushout.inr_desc_assoc, Category.id_comp]
    erw [PreservesPushout.inr_iso_hom_assoc, ← F.map_comp_assoc, pushout.inr_desc, pushout.inr_desc]
    erw [PreservesPushout.inr_iso_inv]
    rfl

end LateralTheory.CohomologicalPurity.TubeCut
end
end

section -- merged from Development.EtaleCohomology.CohomologicalPurity.LeafEvPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.KummerTheory.FlasquePf

namespace LateralTheory.CohomologicalPurity.DictPf

section
variable {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}}

theorem ev_res' (m : (free R).obj (yoneda.obj X) ⟶ G) {V : Scheme.{0}} (h : V ⟶ X) :
    (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V h) = Sec.res h (ev m) := by
  calc (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V h)
      = (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V ((yoneda.obj X).map h.op (𝟙 X))) := by simp
    _ = (m.hom.app (op V)).hom (Sec.res h (freeGen R (yoneda.obj X) X (𝟙 X))) := by rw [freeGen_res]
    _ = Sec.res h (ev m) := by
      have := congrArg (fun φ => ModuleCat.Hom.hom φ (freeGen R (yoneda.obj X) X (𝟙 X))) (m.hom.naturality h.op)
      exact this

theorem eq_ofSec (m : (free R).obj (yoneda.obj X) ⟶ G) : m = ofSec G (ev m) := by
  apply ((sheafificationAdjunction _ _).homEquiv _ G).injective
  unfold ofSec
  rw [Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext V
  apply ModuleCat.free_hom_ext
  intro x
  change (m.hom.app V).hom (freeGen R (yoneda.obj X) V.unop x.down) = _
  rw [ev_res']
  unfold toG
  symm
  change ModuleCat.freeDesc _ (ModuleCat.freeMk x) = _
  refine (ModuleCat.freeDesc_apply _ _).trans ?_
  rfl

end

theorem LeafEv_of : LeafEv := by
  intro R _ G X
  refine ⟨?_, ?_, ?_⟩
  · intro m m' h
    rw [eq_ofSec m, eq_ofSec m', h]
  · intro m m'
    rfl
  · intro Y f m
    change (m.hom.app (op Y)).hom ((((free R).map (yoneda.map f)).hom.app (op Y)).hom
      (freeGen R (yoneda.obj Y) Y (𝟙 Y))) = _
    rw [freeGen_map]
    simp only [yoneda_map_app]
    exact ev_res' m f

end LateralTheory.CohomologicalPurity.DictPf
end
end
