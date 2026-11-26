module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.IsNilpotentOfIsNilDP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallDescentH1Surjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.TagIso
section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.AcycOfCoprod
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh

namespace FubiniStudyChowHeightFormula₂.Adr

universe v u v' u'

def Acyc (R : Type) [CommRing R] (D : Type u) [Category.{v} D] : Prop :=
  Nonempty D ∧ ∀ M : CommAlgCat.{0} R, (∀ g : D → M, (∀ a b (_ : a ⟶ b), g b = g a) → ∀ a b, g a = g b) ∧
    (∀ c : H1 ((Functor.const D).obj M), c = 0) ∧ ∀ c : H2 ((Functor.const D).obj M), c = 0

section Contract

variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D]

def cm (M : CommAlgCat.{0} R) (G : D ⥤ D) :
    CoefMap (RingHom.id R) ((Functor.const D).obj M) ((Functor.const D).obj M) where
  G := G
  α _ := RingHom.id M
  naturality _ _ := rfl
  smul _ _ _ := rfl

theorem cm_zigzag (M : CommAlgCat.{0} R) {G G' : D ⥤ D} (h : Zigzag G G') :
    (∀ g : D → M, (∀ a b (_ : a ⟶ b), g b = g a) → ∀ a, g (G.obj a) = g (G'.obj a)) ∧
    (∀ c, (cm M G).pull1 c = (cm M G').pull1 c) ∧ ∀ c, (cm M G).pull2 c = (cm M G').pull2 c := by
  have one : ∀ {G G' : D ⥤ D} (_ : G ⟶ G'),
      (∀ g : D → M, (∀ a b (_ : a ⟶ b), g b = g a) → ∀ a, g (G.obj a) = g (G'.obj a)) ∧
      (∀ c, (cm M G).pull1 c = (cm M G').pull1 c) ∧ ∀ c, (cm M G).pull2 c = (cm M G').pull2 c :=
    fun {G G'} θ ↦ ⟨fun g hg a ↦ (hg _ _ (θ.app a)).symm,
      (cm M G).pullCohomologyOne_eq_of_natTrans (cm M G') θ fun _ _ ↦ rfl,
      (cm M G).pullCohomologyTwo_eq_of_natTrans (cm M G') θ fun _ _ ↦ rfl⟩
  induction h with
  | refl => exact ⟨fun _ _ _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩
  | tail _ hz ih =>
    rcases hz with ⟨⟨θ⟩⟩ | ⟨⟨θ⟩⟩
    · exact ⟨fun g hg a ↦ (ih.1 g hg a).trans ((one θ).1 g hg a), fun c ↦ (ih.2.1 c).trans ((one θ).2.1 c),
        fun c ↦ (ih.2.2 c).trans ((one θ).2.2 c)⟩
    · exact ⟨fun g hg a ↦ (ih.1 g hg a).trans ((one θ).1 g hg a).symm,
        fun c ↦ (ih.2.1 c).trans ((one θ).2.1 c).symm, fun c ↦ (ih.2.2 c).trans ((one θ).2.2 c).symm⟩

theorem acyc_of_zigzag (d : D) (h : Zigzag (𝟭 D) ((Functor.const D).obj d)) : Acyc R D := by
  refine ⟨⟨d⟩, fun M ↦ ?_⟩
  obtain ⟨h0, h1, h2⟩ := cm_zigzag M h
  refine ⟨fun g hg a b ↦ (h0 g hg a).trans (h0 g hg b).symm, fun c ↦ ?_, fun c ↦ ?_⟩
  · refine ((CoefMap.pullCohomologyOne_id c).symm.trans (h1 c)).trans ?_
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
    refine ⟨0, ?_⟩
    rw [map_zero]
    funext T T' φ
    exact (Z1.id f d).symm
  · refine ((CoefMap.pullCohomologyTwo_id c).symm.trans (h2 c)).trans ?_
    obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
    rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero]
    refine ⟨fun _ _ _ ↦ (z.1 d d d (𝟙 d) (𝟙 d) : M), ?_⟩
    funext T T' T'' φ ψ
    exact sub_add_cancel (z.1 d d d (𝟙 d) (𝟙 d) : M) (z.1 d d d (𝟙 d) (𝟙 d) : M)

theorem acyc_of_coprod (d : D) (P : D → D) (i : ∀ a, a ⟶ P a) (j : ∀ a, d ⟶ P a)
    (h : ∀ a b (φ : a ⟶ P b), ∃! ψ : P a ⟶ P b, i a ≫ ψ = φ ∧ j a ≫ ψ = j b) : Acyc R D := by
  choose m hm hu using h
  let Q : D ⥤ D :=
    { obj := P
      map := fun {a b} φ ↦ m a b (φ ≫ i b)
      map_id := fun a ↦ (hu a a _ (𝟙 _) ⟨by simp, by simp⟩).symm
      map_comp := fun {a b c} φ ψ ↦ (hu a c _ _ ⟨by
        rw [← Category.assoc, (hm a b _).1, Category.assoc, (hm b c _).1, Category.assoc], by
        rw [← Category.assoc, (hm a b _).2, (hm b c _).2]⟩).symm }
  let θ : 𝟭 D ⟶ Q := { app := i, naturality := fun a b φ ↦ (hm a b _).1.symm }
  let η : (Functor.const D).obj d ⟶ Q :=
    { app := j, naturality := fun a b φ ↦ (Category.id_comp _).trans (hm a b _).2.symm }
  exact acyc_of_zigzag d ((Zigzag.of_hom θ).trans (Zigzag.of_inv η))

end Contract

section Comma

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {G : C' ⥤ C} {T : C}

theorem Acyc.zero (h : Acyc R (CostructuredArrow G T)) (M : CommAlgCat.{0} R) (g : ∀ S, (G.obj S ⟶ T) → M)
    (hg : ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T), g S (G.map ψ ≫ c) = g S' c) : ∃ m, ∀ S c, g S c = m := by
  obtain ⟨⟨a⟩, h⟩ := h
  refine ⟨g a.left a.hom, fun S c ↦ (h M).1 (fun b ↦ g b.left b.hom) (fun b b' φ ↦ ?_) (CostructuredArrow.mk c) a⟩
  exact (hg _ _ φ.left b'.hom).symm.trans (congrArg _ (CostructuredArrow.w φ))

theorem Acyc.one (h : Acyc R (CostructuredArrow G T)) (M : CommAlgCat.{0} R)
    (f : ∀ S S', (S ⟶ S') → (G.obj S' ⟶ T) → M)
    (hf : ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S'') (c : G.obj S'' ⟶ T),
      f S S'' (φ ≫ ψ) c = f S S' φ (G.map ψ ≫ c) + f S' S'' ψ c) :
    ∃ v : ∀ S, (G.obj S ⟶ T) → M, ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T), f S S' ψ c = v S' c - v S (G.map ψ ≫ c) := by
  let f' : Z1 ((Functor.const (CostructuredArrow G T)).obj M) :=
    ⟨fun a b φ ↦ (f a.left b.left φ.left b.hom : M), fun a b c φ ψ ↦
      (hf _ _ _ φ.left ψ.left c.hom).trans
        (congrArg (fun t ↦ f _ _ φ.left t + f _ _ ψ.left c.hom) (CostructuredArrow.w ψ))⟩
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 ((h.2 M).2.1 (H1.mk _ f'))
  exact ⟨fun S c ↦ g (CostructuredArrow.mk c), fun S S' ψ c ↦
    (congrFun (congrFun (congrFun hg (CostructuredArrow.mk (G.map ψ ≫ c))) (CostructuredArrow.mk c))
      (CostructuredArrow.homMk ψ rfl)).symm⟩

theorem Acyc.two (h : Acyc R (CostructuredArrow G T)) (M : CommAlgCat.{0} R)
    (z : ∀ S S' S'', (S ⟶ S') → (S' ⟶ S'') → (G.obj S'' ⟶ T) → M)
    (hz : ∀ S S' S'' S''' (φ : S ⟶ S') (ψ : S' ⟶ S'') (χ : S'' ⟶ S''') (c : G.obj S''' ⟶ T),
      z S S' S'' φ ψ (G.map χ ≫ c) + z S S'' S''' (φ ≫ ψ) χ c = z S S' S''' φ (ψ ≫ χ) c + z S' S'' S''' ψ χ c) :
    ∃ w : ∀ S S', (S ⟶ S') → (G.obj S' ⟶ T) → M, ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S'') (c : G.obj S'' ⟶ T),
      z S S' S'' φ ψ c = w S S' φ (G.map ψ ≫ c) - w S S'' (φ ≫ ψ) c + w S' S'' ψ c := by
  let z' : Z2 ((Functor.const (CostructuredArrow G T)).obj M) :=
    ⟨fun a b c φ ψ ↦ (z a.left b.left c.left φ.left ψ.left c.hom : M), fun a b c e φ ψ χ ↦
      (congrArg (fun t ↦ z _ _ _ φ.left ψ.left t + z _ _ _ (φ.left ≫ ψ.left) χ.left e.hom)
        (CostructuredArrow.w χ)).symm.trans (hz _ _ _ _ φ.left ψ.left χ.left e.hom)⟩
  obtain ⟨g, hg⟩ := H2.mk_eq_zero.1 ((h.2 M).2.2 (H2.mk _ z'))
  let w : ∀ S S', (S ⟶ S') → (G.obj S' ⟶ T) → M := fun S S' ψ c ↦
    g (CostructuredArrow.mk (G.map ψ ≫ c)) (CostructuredArrow.mk c) (CostructuredArrow.homMk ψ rfl)
  have hw : ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T) (c₀ : G.obj S ⟶ T) (e : G.map ψ ≫ c = c₀),
      (g (CostructuredArrow.mk c₀) (CostructuredArrow.mk c) (CostructuredArrow.homMk ψ e) : M) = w S S' ψ c := by
    intro S S' ψ c c₀ e
    subst e
    rfl
  refine ⟨w, fun S S' S'' φ ψ c ↦ ?_⟩
  have k := congrFun (congrFun (congrFun (congrFun (congrFun hg
    (CostructuredArrow.mk (G.map φ ≫ G.map ψ ≫ c))) (CostructuredArrow.mk (G.map ψ ≫ c))) (CostructuredArrow.mk c))
      (CostructuredArrow.homMk φ rfl)) (CostructuredArrow.homMk ψ rfl)
  rw [← hw S S'' (φ ≫ ψ) c (G.map φ ≫ G.map ψ ≫ c) (by simp)]
  exact k.symm

end Comma

section QA

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']

theorem qa1 (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (h : ∀ T, Acyc R (CostructuredArrow G T)) :
    Function.Bijective (CoefMap.restrict F G).pull1 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    let g' : ∀ S, F.obj (G.obj S) := g
    have hg' : ∀ S S' (ψ : S ⟶ S'), f.1 _ _ (G.map ψ) = g' S' - mp F (G.map ψ) (g' S) := fun S S' ψ ↦
      (congrFun (congrFun (congrFun hg S) S') ψ).symm
    have ex : ∀ T, ∃ m : F.obj T, ∀ S (c : G.obj S ⟶ T), f.1 _ _ c + mp F c (g' S) = m := fun T ↦
      (h T).zero _ _ fun S S' ψ c ↦ by
        simp only [Z1.comp f, hg', mp_comp, map_sub]; ring
    choose m hm using ex
    refine H1.mk_eq_zero.2 ⟨m, ?_⟩
    funext T T' φ
    obtain ⟨a⟩ := (h T).1
    let c : G.obj a.left ⟶ T := a.hom
    rw [amitsur_d0_apply, ← hm T _ c, ← hm T' _ (c ≫ φ)]
    simp only [Z1.comp f, mp_comp, map_add (f := _)]; ring
  · intro c
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    let f' : ∀ S S', (S ⟶ S') → F.obj (G.obj S') := f.1
    have hf : ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S''),
        f' S S'' (φ ≫ ψ) = mp F (G.map ψ) (f' S S' φ) + f' S' S'' ψ := fun S S' S'' φ ψ ↦ f.2 φ ψ
    have ex : ∀ T, ∃ v : ∀ S, (G.obj S ⟶ T) → F.obj T, ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T),
        -mp F c (f' S S' ψ) = v S' c - v S (G.map ψ ≫ c) := fun T ↦
      (h T).one _ (fun S S' ψ c ↦ -mp F c (f' S S' ψ)) fun S S' S'' φ ψ c ↦ by
        simp only [hf, mp_comp, map_add (f := _)]; ring
    choose v hv using ex
    have ex : ∀ T T' (φ : T ⟶ T'), ∃ m : F.obj T', ∀ S (c : G.obj S ⟶ T),
        v T' S (c ≫ φ) - mp F φ (v T S c) = m := fun T T' φ ↦
      (h T).zero _ _ fun S S' ψ c ↦ by
        have e1 := hv T' S S' ψ (c ≫ φ)
        have e2 := congrArg (mp F φ) (hv T S S' ψ c)
        simp only [mp_comp, map_sub, map_neg, Category.assoc] at e1 e2 ⊢
        linear_combination e1 - e2
    choose m hm using ex
    refine ⟨H1.mk _ ⟨m, fun T T' T'' φ ψ ↦ ?_⟩, ?_⟩
    · obtain ⟨a⟩ := (h T).1
      let c : G.obj a.left ⟶ T := a.hom
      rw [← hm T T'' _ _ c, ← hm T T' _ _ c, ← hm T' T'' _ _ (c ≫ φ)]
      simp only [mp_comp, map_sub, Category.assoc]; ring
    · rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]
      refine ⟨fun S ↦ v _ S (𝟙 _), ?_⟩
      funext S S' ψ
      have e1 := hm _ _ (G.map ψ) S (𝟙 _)
      have e2 := hv _ S S' ψ (𝟙 _)
      rw [Category.id_comp] at e1
      rw [Category.comp_id, mp_id] at e2
      change v _ S' (𝟙 _) - mp F (G.map ψ) (v _ S (𝟙 _)) = m _ _ (G.map ψ) - f' S S' ψ
      linear_combination e1 - e2

theorem qa2 (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (h : ∀ T, Acyc R (CostructuredArrow G T)) :
    Function.Bijective (CoefMap.restrict F G).pull2 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
    rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    let f : ∀ S S', (S ⟶ S') → F.obj (G.obj S') := g
    have hf : ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S''), z.1 _ _ _ (G.map φ) (G.map ψ) =
        mp F (G.map ψ) (f S S' φ) - f S S'' (φ ≫ ψ) + f S' S'' ψ := fun S S' S'' φ ψ ↦
      (congrFun (congrFun (congrFun (congrFun (congrFun hg S) S') S'') φ) ψ).symm
    have ex : ∀ T, ∃ v : ∀ S, (G.obj S ⟶ T) → F.obj T, ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T),
        z.1 _ _ _ (G.map ψ) c - mp F c (f S S' ψ) = v S' c - v S (G.map ψ ≫ c) := fun T ↦
      (h T).one _ (fun S S' ψ c ↦ z.1 _ _ _ (G.map ψ) c - mp F c (f S S' ψ)) fun S S' S'' φ ψ c ↦ by
        have e := z.2 (G.map φ) (G.map ψ) c
        simp only [hf, mp_comp, map_add (f := _), map_sub, Functor.map_comp] at e ⊢
        linear_combination e
    choose v hv using ex
    have ex : ∀ T T' (φ : T ⟶ T'), ∃ m : F.obj T', ∀ S (c : G.obj S ⟶ T),
        z.1 _ _ _ c φ - mp F φ (v T S c) + v T' S (c ≫ φ) = m := fun T T' φ ↦
      (h T).zero _ _ fun S S' ψ c ↦ by
        have e := z.2 (G.map ψ) c φ
        have e1 := hv T' S S' ψ (c ≫ φ)
        have e2 := congrArg (mp F φ) (hv T S S' ψ c)
        simp only [mp_comp, map_sub, Category.assoc] at e1 e2 ⊢
        linear_combination e + e1 - e2
    choose m hm using ex
    refine H2.mk_eq_zero.2 ⟨m, ?_⟩
    funext T T' T'' φ ψ
    obtain ⟨a⟩ := (h T).1
    let c : G.obj a.left ⟶ T := a.hom
    have e := z.2 c φ ψ
    rw [d1_apply, ← hm T T'' _ _ c, ← hm T T' _ _ c, ← hm T' T'' _ _ (c ≫ φ)]
    simp only [mp_comp, map_sub, map_add (f := _), Category.assoc]
    linear_combination e
  · intro c
    obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
    let y : ∀ S S' S'', (S ⟶ S') → (S' ⟶ S'') → F.obj (G.obj S'') := z.1
    have hy : ∀ S S' S'' S''' (φ : S ⟶ S') (ψ : S' ⟶ S'') (χ : S'' ⟶ S'''),
        mp F (G.map χ) (y _ _ _ φ ψ) + y _ _ _ (φ ≫ ψ) χ = y _ _ _ φ (ψ ≫ χ) + y _ _ _ ψ χ :=
      fun S S' S'' S''' φ ψ χ ↦ z.2 φ ψ χ
    have ex : ∀ T, ∃ w : ∀ S S', (S ⟶ S') → (G.obj S' ⟶ T) → F.obj T,
        ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S'') (c : G.obj S'' ⟶ T),
          mp F c (y _ _ _ φ ψ) = w S S' φ (G.map ψ ≫ c) - w S S'' (φ ≫ ψ) c + w S' S'' ψ c := fun T ↦
      (h T).two _ (fun S S' S'' φ ψ c ↦ mp F c (y _ _ _ φ ψ)) fun S S' S'' S''' φ ψ χ c ↦ by
        simp only [mp_comp, ← map_add (f := _), hy]
    choose w hw using ex
    have ex : ∀ T T' (φ : T ⟶ T'), ∃ x : ∀ S, (G.obj S ⟶ T) → F.obj T', ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T),
        mp F φ (w T S S' ψ c) - w T' S S' ψ (c ≫ φ) = x S' c - x S (G.map ψ ≫ c) := fun T T' φ ↦
      (h T).one _ (fun S S' ψ c ↦ mp F φ (w T S S' ψ c) - w T' S S' ψ (c ≫ φ)) fun S S' S'' ψ χ c ↦ by
        have e1 := hw T' S S' S'' ψ χ (c ≫ φ)
        have e2 := congrArg (mp F φ) (hw T S S' S'' ψ χ c)
        simp only [mp_comp, map_sub, map_add (f := _), Category.assoc] at e1 e2 ⊢
        linear_combination e2 - e1
    choose x hx using ex
    have ex : ∀ T T' T'' (φ : T ⟶ T') (φ' : T' ⟶ T''), ∃ m : F.obj T'', ∀ S (c : G.obj S ⟶ T),
        mp F φ' (x T T' φ S c) + x T' T'' φ' S (c ≫ φ) - x T T'' (φ ≫ φ') S c = m := fun T T' T'' φ φ' ↦
      (h T).zero _ _ fun S S' ψ c ↦ by
        have e1 := congrArg (mp F φ') (hx T T' φ S S' ψ c)
        have e2 := hx T' T'' φ' S S' ψ (c ≫ φ)
        have e3 := hx T T'' (φ ≫ φ') S S' ψ c
        simp only [mp_comp, map_sub, Category.assoc] at e1 e2 e3 ⊢
        linear_combination e1 + e2 - e3
    choose m hm using ex
    refine ⟨H2.mk _ ⟨m, fun T T' T'' T''' φ ψ χ ↦ ?_⟩, ?_⟩
    · obtain ⟨a⟩ := (h T).1
      let c : G.obj a.left ⟶ T := a.hom
      rw [← hm T T' T'' _ _ _ c, ← hm T T'' T''' _ _ _ c, ← hm T T' T''' _ _ _ c, ← hm T' T'' T''' _ _ _ (c ≫ φ)]
      simp only [mp_comp, map_sub, map_add (f := _), Category.assoc]; ring
    · rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk]
      refine ⟨fun S S' ψ ↦ x _ _ (G.map ψ) S (𝟙 _) - w _ S S' ψ (𝟙 _), ?_⟩
      funext S S' S'' φ ψ
      have e1 := hm _ _ _ (G.map φ) (G.map ψ) S (𝟙 _)
      have e2 := hw _ S S' S'' φ ψ (𝟙 _)
      have e3 := hx _ _ (G.map ψ) S S' φ (𝟙 _)
      rw [Category.id_comp] at e1 e3
      rw [Category.comp_id] at e2 e3
      rw [mp_id] at e2
      change mp F (G.map ψ) (x _ _ (G.map φ) S (𝟙 _) - w _ S S' φ (𝟙 _)) -
        (x _ _ (G.map (φ ≫ ψ)) S (𝟙 _) - w _ S S'' (φ ≫ ψ) (𝟙 _)) + (x _ _ (G.map ψ) S' (𝟙 _) - w _ S' S'' ψ (𝟙 _)) =
        m _ _ _ (G.map φ) (G.map ψ) - y _ _ _ φ ψ
      rw [map_sub, G.map_comp]
      linear_combination e1 + e2 - e3

end QA

end FubiniStudyChowHeightFormula₂.Adr
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

universe v u v' u' v'' u''

section General

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
  {C'' : Type u''} [Category.{v''} C'']

theorem restrict_pull1 (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C'' ⥤ C') (c : GlobalTheory.CatCoh.H1 F) :
    (CoefMap.restrict (G ⋙ F) H).pull1 ((CoefMap.restrict F G).pull1 c) =
      (CoefMap.restrict F (H ⋙ G)).pull1 c := by
  rw [← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ (𝟙 _) (fun T b => by simp [CoefMap.comp, CoefMap.restrict, mp] <;> rfl) c

theorem restrict_pull2 (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : C'' ⥤ C') (c : GlobalTheory.CatCoh.H2 F) :
    (CoefMap.restrict (G ⋙ F) H).pull2 ((CoefMap.restrict F G).pull2 c) =
      (CoefMap.restrict F (H ⋙ G)).pull2 c := by
  rw [← CoefMap.pullCohomologyTwo_comp]
  exact CoefMap.pullCohomologyTwo_eq_of_natTrans _ _ (𝟙 _) (fun T b => by simp [CoefMap.comp, CoefMap.restrict, mp] <;> rfl) c

end General

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}
  {γ : DividedPowers I} {s : X ⟶ Sp R} {K : Type} {U : K → X.Opens}

def toSmall (γ : DividedPowers I) (s : X ⟶ Sp R) (U : K → X.Opens) :
    Tag γ s U ⥤ (IsSmall γ s U).FullSubcategory where
  obj S := ⟨S.T, S.k, S.le⟩
  map f := ⟨f.f⟩

section Comma

variable {T : (IsSmall γ s U).FullSubcategory}

theorem comma_le (a : CostructuredArrow (toSmall γ s U) T) : ⊤ ≤ T.obj.x ⁻¹ᵁ U a.left.k :=
  Thick.Hom.le_preimage a.hom.hom a.left.le

def selfObj (k : K) (h : ⊤ ≤ T.obj.x ⁻¹ᵁ U k) : CostructuredArrow (toSmall γ s U) T :=
  CostructuredArrow.mk (Y := (⟨T.obj, k, h⟩ : Tag γ s U)) (𝟙 T)

def toSelf (a : CostructuredArrow (toSmall γ s U) T) (k : K) (h : ⊤ ≤ T.obj.x ⁻¹ᵁ U k)
    (e : U a.left.k ≤ U k) : a ⟶ selfObj k h :=
  CostructuredArrow.homMk (⟨a.hom.hom, e⟩ : Tag.Hom _ _) (Category.comp_id _)

theorem toSelf_unique {a : CostructuredArrow (toSmall γ s U) T} {k : K} {h : ⊤ ≤ T.obj.x ⁻¹ᵁ U k}
    (f g : a ⟶ selfObj k h) : f = g := by
  have hf := CostructuredArrow.w f
  have hg := CostructuredArrow.w g
  apply CostructuredArrow.hom_ext
  revert hf hg
  rcases f with ⟨⟨f1, l1⟩, fr, fw⟩
  rcases g with ⟨⟨g1, l2⟩, gr, gw⟩
  intro hf hg
  simp [selfObj, toSmall] at hf hg ⊢
  have e : f1 = g1 := congrArg (fun q => q.hom) (hf.trans hg.symm)
  subst e
  rfl

def selfFun (m : CostructuredArrow (toSmall γ s U) T → K) (h : ∀ a, ⊤ ≤ T.obj.x ⁻¹ᵁ U (m a))
    (mono : ∀ a b, (a ⟶ b) → U (m a) ≤ U (m b)) :
    CostructuredArrow (toSmall γ s U) T ⥤ CostructuredArrow (toSmall γ s U) T where
  obj a := selfObj (m a) (h a)
  map {a b} f := toSelf _ _ _ (mono a b f)
  map_id _ := toSelf_unique _ _
  map_comp _ _ := toSelf_unique _ _

private theorem pull1_restrict_const_eq_of_natTrans {D : Type u} [Category.{v} D] (M : CommAlgCat.{0} R) (Φ Ψ : D ⥤ D)
    (θ : Φ ⟶ Ψ) (c : GlobalTheory.CatCoh.H1 ((Functor.const D).obj M)) :
    (CoefMap.restrict ((Functor.const D).obj M) Φ).pull1 c =
      (CoefMap.restrict ((Functor.const D).obj M) Ψ).pull1 c :=
  CoefMap.pullCohomologyOne_eq_of_natTrans (CoefMap.restrict ((Functor.const D).obj M) Φ)
    (CoefMap.restrict ((Functor.const D).obj M) Ψ :
      CoefMap (RingHom.id R) ((Functor.const D).obj M) (Φ ⋙ (Functor.const D).obj M))
    θ (fun _ _ => rfl) c

private theorem pull2_restrict_const_eq_of_natTrans {D : Type u} [Category.{v} D] (M : CommAlgCat.{0} R) (Φ Ψ : D ⥤ D)
    (θ : Φ ⟶ Ψ) (c : GlobalTheory.CatCoh.H2 ((Functor.const D).obj M)) :
    (CoefMap.restrict ((Functor.const D).obj M) Φ).pull2 c =
      (CoefMap.restrict ((Functor.const D).obj M) Ψ).pull2 c :=
  CoefMap.pullCohomologyTwo_eq_of_natTrans (CoefMap.restrict ((Functor.const D).obj M) Φ)
    (CoefMap.restrict ((Functor.const D).obj M) Ψ :
      CoefMap (RingHom.id R) ((Functor.const D).obj M) (Φ ⋙ (Functor.const D).obj M))
    θ (fun _ _ => rfl) c

private theorem pull1_restrict_id {D : Type u} [Category.{v} D] (F : D ⥤ CommAlgCat.{0} R)
    (c : GlobalTheory.CatCoh.H1 F) : (CoefMap.restrict F (𝟭 D)).pull1 c = c := by
  have e := CoefMap.pullCohomologyOne_eq_of_natTrans (CoefMap.id F) (CoefMap.restrict F (𝟭 D)) (𝟙 _)
    (fun _ b => by simp [CoefMap.restrict, CoefMap.id, mp] <;> rfl) c
  rw [CoefMap.pullCohomologyOne_id] at e
  exact e.symm

private theorem pull2_restrict_id {D : Type u} [Category.{v} D] (F : D ⥤ CommAlgCat.{0} R)
    (c : GlobalTheory.CatCoh.H2 F) : (CoefMap.restrict F (𝟭 D)).pull2 c = c := by
  have e := CoefMap.pullCohomologyTwo_eq_of_natTrans (CoefMap.id F) (CoefMap.restrict F (𝟭 D)) (𝟙 _)
    (fun _ b => by simp [CoefMap.restrict, CoefMap.id, mp] <;> rfl) c
  rw [CoefMap.pullCohomologyTwo_id] at e
  exact e.symm

private theorem H2_discrete_punit_eq_zero (F : Discrete PUnit.{1} ⥤ CommAlgCat.{0} R) (c : GlobalTheory.CatCoh.H2 F) :
    c = 0 := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  rw [H2.mk_eq_zero]
  refine ⟨fun a b φ => z.1 a b b φ (𝟙 b), ?_⟩
  funext a b d φ ψ
  rcases a with ⟨⟨⟩⟩
  rcases b with ⟨⟨⟩⟩
  rcases d with ⟨⟨⟩⟩
  obtain rfl : φ = 𝟙 _ := Subsingleton.elim _ _
  obtain rfl : ψ = 𝟙 _ := Subsingleton.elim _ _
  simp [d1_apply, mp]

private theorem pull1_restrict_const_const_eq_zero {D : Type u} [Category.{v} D] (M : CommAlgCat.{0} R) (x : D)
    (c : GlobalTheory.CatCoh.H1 ((Functor.const D).obj M)) :
    (CoefMap.restrict ((Functor.const D).obj M) ((Functor.const D).obj x)).pull1 c = 0 := by
  have e := restrict_pull1 ((Functor.const D).obj M) ((Functor.const (Discrete PUnit.{1})).obj x)
    ((Functor.const D).obj ⟨⟨⟩⟩) c
  rw [H1.eq_zero_of_isInitial _ (T₀ := (⟨⟨⟩⟩ : Discrete PUnit.{1}))
    (Limits.IsInitial.ofUniqueHom (fun _ => Discrete.eqToHom (Subsingleton.elim _ _))
      (fun _ _ => Subsingleton.elim _ _))
    ((CoefMap.restrict ((Functor.const D).obj M) ((Functor.const (Discrete PUnit.{1})).obj x)).pull1 c),
    map_zero] at e
  exact e.symm

private theorem pull2_restrict_const_const_eq_zero {D : Type u} [Category.{v} D] (M : CommAlgCat.{0} R) (x : D)
    (c : GlobalTheory.CatCoh.H2 ((Functor.const D).obj M)) :
    (CoefMap.restrict ((Functor.const D).obj M) ((Functor.const D).obj x)).pull2 c = 0 := by
  have e := restrict_pull2 ((Functor.const D).obj M) ((Functor.const (Discrete PUnit.{1})).obj x)
    ((Functor.const D).obj ⟨⟨⟩⟩) c
  rw [H2_discrete_punit_eq_zero _
    ((CoefMap.restrict ((Functor.const D).obj M) ((Functor.const (Discrete PUnit.{1})).obj x)).pull2 c),
    map_zero] at e
  exact e.symm

theorem acyc_toSmall (hinf : ∀ k l, ∃ m, U m = U k ⊓ U l) (T : (IsSmall γ s U).FullSubcategory) :
    Acyc R (CostructuredArrow (toSmall γ s U) T) := by
  obtain ⟨k0, h0⟩ := T.property
  choose m2 hm2 using fun (a : CostructuredArrow (toSmall γ s U) T) => hinf a.left.k k0
  have h2 : ∀ a, ⊤ ≤ T.obj.x ⁻¹ᵁ U (m2 a) := by
    intro a
    rw [hm2 a]
    intro p hp
    exact ⟨comma_le a hp, h0 hp⟩
  let S1 := selfFun (T := T) (fun a => a.left.k) comma_le (fun a b f => Tag.Hom.le f.left)
  let S2 := selfFun (T := T) m2 h2 (fun a b f => by
    rw [hm2 a, hm2 b]
    exact inf_le_inf_right _ (Tag.Hom.le f.left))
  let θ1 : 𝟭 _ ⟶ S1 :=
    { app := fun a => toSelf a _ (comma_le a) le_rfl
      naturality := fun _ _ _ => toSelf_unique _ _ }
  let θ2 : S2 ⟶ S1 :=
    { app := fun a => toSelf (selfObj (m2 a) (h2 a)) a.left.k (comma_le a)
        (show U (m2 a) ≤ U a.left.k by rw [hm2 a]; exact inf_le_left)
      naturality := fun _ _ _ => toSelf_unique _ _ }
  let θ3 : S2 ⟶ (Functor.const _).obj (selfObj k0 h0) :=
    { app := fun a => toSelf (selfObj (m2 a) (h2 a)) k0 h0
        (show U (m2 a) ≤ U k0 by rw [hm2 a]; exact inf_le_right)
      naturality := fun _ _ _ => toSelf_unique (k := k0) (h := h0) _ _ }
  refine ⟨⟨selfObj k0 h0⟩, fun M => ⟨?_, ?_, ?_⟩⟩
  · intro g hg
    have key : ∀ a, g a = g (selfObj k0 h0) := fun a =>
      (hg _ _ (θ1.app a)).symm.trans ((hg _ _ (θ2.app a)).trans (hg _ _ (θ3.app a)).symm)
    intro a b
    exact (key a).trans (key b).symm
  · intro c
    exact (pull1_restrict_id _ c).symm.trans ((pull1_restrict_const_eq_of_natTrans M _ _ θ1 c).trans
      ((pull1_restrict_const_eq_of_natTrans M _ _ θ2 c).symm.trans ((pull1_restrict_const_eq_of_natTrans M _ _ θ3 c).trans
        (pull1_restrict_const_const_eq_zero M _ c))))
  · intro c
    exact (pull2_restrict_id _ c).symm.trans ((pull2_restrict_const_eq_of_natTrans M _ _ θ1 c).trans
      ((pull2_restrict_const_eq_of_natTrans M _ _ θ2 c).symm.trans ((pull2_restrict_const_eq_of_natTrans M _ _ θ3 c).trans
        (pull2_restrict_const_const_eq_zero M _ c))))

end Comma

theorem tag_pull1 (hcov : ⨆ k, U k = ⊤) (hinf : ∀ k l, ∃ m, U m = U k ⊓ U l) :
    Function.Bijective (CoefMap.restrict (O γ s) (Tag.forget γ s U)).pull1 := by
  have key : ⇑(CoefMap.restrict (O γ s) (Tag.forget γ s U)).pull1 =
      ⇑(CoefMap.restrict ((IsSmall γ s U).ι ⋙ O γ s) (toSmall γ s U)).pull1 ∘
        ⇑(CoefMap.restrict (O γ s) (IsSmall γ s U).ι).pull1 :=
    funext fun c => (restrict_pull1 (O γ s) (IsSmall γ s U).ι (toSmall γ s U) c).symm
  rw [key]
  exact (qa1 _ _ (fun T => acyc_toSmall hinf T)).comp
    (SmallDescent.pull1_bijective R I γ X s K U hcov)

private theorem pull2_restrict_isSmall_bijective_of_cover (hcov : ⨆ k, U k = ⊤) :
    Function.Bijective (CoefMap.restrict (O γ s) (IsSmall γ s U).ι).pull2 := by
  apply Desc.pull2_bijective
  · intro T b
    obtain ⟨L, l, hl⟩ := SmallDescent.exists_isLoc T b
    obtain ⟨hu, hsurj, hker, hfac⟩ := hl
    refine ⟨L, l, hu, ?_, hker, ?_⟩
    · intro y
      obtain ⟨n, N, h⟩ := hsurj y
      exact ⟨N, n, h⟩
    · intro S u hu'
      obtain ⟨ψ, hψ⟩ := hfac S u hu'
      exact ⟨ψ, hψ, fun ψ' h' =>
        SmallDescent.IsLoc.hom_ext ⟨hu, hsurj, hker, hfac⟩ (h'.trans hψ.symm)⟩
  · intro S S' a hS
    exact SmallDescent.isSmall_of_hom a hS
  · intro T
    obtain ⟨σ, hσ, hσs⟩ := SmallDescent.exists_cover hcov T
    refine ⟨σ.card, fun i => (σ.equivFin.symm i : T.B), ?_, ?_⟩
    · have hr : Set.range (fun i => (σ.equivFin.symm i : T.B)) = (σ : Set T.B) := by
        ext x
        constructor
        · rintro ⟨i, rfl⟩
          exact (σ.equivFin.symm i).2
        · intro hx
          exact ⟨σ.equivFin ⟨x, hx⟩, by simp⟩
      rw [hr]
      exact hσ
    · intro i S u hu
      exact hσs _ (σ.equivFin.symm i).2 S u hu

theorem tag_pull2 (hcov : ⨆ k, U k = ⊤) (hinf : ∀ k l, ∃ m, U m = U k ⊓ U l) :
    Function.Bijective (CoefMap.restrict (O γ s) (Tag.forget γ s U)).pull2 := by
  have key : ⇑(CoefMap.restrict (O γ s) (Tag.forget γ s U)).pull2 =
      ⇑(CoefMap.restrict ((IsSmall γ s U).ι ⋙ O γ s) (toSmall γ s U)).pull2 ∘
        ⇑(CoefMap.restrict (O γ s) (IsSmall γ s U).ι).pull2 :=
    funext fun c => (restrict_pull2 (O γ s) (IsSmall γ s U).ι (toSmall γ s U) c).symm
  rw [key]
  exact (qa2 _ _ (fun T => acyc_toSmall hinf T)).comp (pull2_restrict_isSmall_bijective_of_cover hcov)

end FubiniStudyChowHeightFormula₂.Adr
end
end

section -- merged from Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.IsDPMorphismId
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R : Type} [CommRing R] {I : Ideal R} {X X₀ : Scheme.{0}}

def NT (κ : DividedPowers I) {s : X ⟶ Sp R} {K : Type} (U : K → X.Opens) : ObjectProperty (Tag (dp0 R) s U) :=
  fun S ↦ InN κ S.T

theorem isDPMorphism_id {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) :
    IsDPMorphism δ δ (RingHom.id B) := (DPMorphism.id δ).isDPMorphism

structure Red (κ : DividedPowers I) {R₀ : Type} [CommRing R₀] (π : R →+* R₀) (s : X ⟶ Sp R) (s₀ : X₀ ⟶ Sp R₀)
    (i : X₀ ⟶ X) : Prop where
  nil : IsNilDP κ
  surj : Function.Surjective π
  ker : RingHom.ker π = I
  pb : IsPullback i s₀ s (spMap π)

variable {κ : DividedPowers I} {R₀ : Type} [CommRing R₀] {π : R →+* R₀} {s : X ⟶ Sp R} {s₀ : X₀ ⟶ Sp R₀}
  {i : X₀ ⟶ X} (h : Red κ π s s₀ i)

namespace Red

include h

theorem mor : IsMor (dp0 R) s κ (s₀ ≫ spMap π) (RingHom.id R) i := by
  refine IsMor.of_dividedPowersZeroIdeal κ ?_
  rw [GlobalTheory.Cris.spMap_id, Category.comp_id]
  exact h.pb.w

theorem surjective : Function.Surjective i := by
  have hnil : ∀ x ∈ I, ∃ N : ℕ, x ^ N = 0 := by
    intro x hx
    obtain ⟨N, hN⟩ := h.nil
    refine ⟨N, ?_⟩
    have := hN (List.replicate N (1, x))
      (by
        intro p hp
        rw [List.eq_of_mem_replicate hp]
        exact hx)
      (by simp)
    simpa [List.map_replicate, List.prod_replicate, κ.dpow_one hx] using this
  have hsurj : Function.Surjective (spMap π) := by
    intro p
    have hp : p ∈ Set.range (PrimeSpectrum.comap π) := by
      open PrimeSpectrum in rw [range_comap_of_surjective _ π h.surj, h.ker]
      change (I : Set R) ⊆ (p : PrimeSpectrum R).asIdeal
      intro x hx
      obtain ⟨N, hN⟩ := hnil x hx
      exact p.isPrime.mem_of_pow_mem N (by rw [hN]; exact p.asIdeal.zero_mem)
    exact hp
  have hS : AlgebraicGeometry.Surjective (spMap π) := (AlgebraicGeometry.surjective_iff _).mpr hsurj
  exact (AlgebraicGeometry.surjective_iff i).mp
    (MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) h.pb.flip hS)

theorem le_of_le {U V : X.Opens} (e : i ⁻¹ᵁ U ≤ i ⁻¹ᵁ V) : U ≤ V := by
  intro x hx
  obtain ⟨y, rfl⟩ := h.surjective x
  exact (show y ∈ i ⁻¹ᵁ V from e (show y ∈ i ⁻¹ᵁ U from hx))

theorem inN_obj (T : Thick κ (s₀ ≫ spMap π)) : InN κ (h.mor.obj T) := by
  show ∃ δ' : DividedPowers (T.J ⊔ Ideal.map (algebraMap R T.B) I),
    T.δ.IsDPMorphism δ' (RingHom.id T.B) ∧ κ.IsDPMorphism δ' (algebraMap R T.B)
  rw [sup_eq_left.mpr T.dp.ideal_comp]
  exact ⟨T.δ, isDPMorphism_id T.δ, T.dp⟩

end Red

section Up

variable (S : Thick (dp0 R) s)

abbrev big (I : Ideal R) : Ideal S.B := S.J ⊔ I.map (algebraMap R S.B)

def rho (I : Ideal R) : S.B₀ →+* S.B ⧸ big S I :=
  RingHom.liftOfSurjective S.π S.surj ⟨Ideal.Quotient.mk _, fun b hb ↦
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left ((S.ker b).1 hb))⟩

theorem rho_π (I : Ideal R) (b : S.B) : rho S I (S.π b) = Ideal.Quotient.mk _ b :=
  RingHom.liftOfSurjective_comp_apply _ _ _ b

def Red.sig : R₀ →+* S.B ⧸ big S I :=
  RingHom.liftOfSurjective π h.surj ⟨(Ideal.Quotient.mk _).comp (algebraMap R S.B), fun r hr ↦
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (h.ker ▸ hr)))⟩

theorem Red.sig_π (r : R) : h.sig S (π r) = Ideal.Quotient.mk _ (algebraMap R S.B r) :=
  RingHom.liftOfSurjective_comp_apply _ _ _ r

def Red.pt : Sp (S.B ⧸ big S I) ⟶ X₀ :=
  h.pb.lift (spMap (rho S I) ≫ S.x) (spMap (h.sig S)) (by
    rw [Category.assoc, S.w, ← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun r ↦ (rho_π S I _).trans (h.sig_π S r).symm)

theorem Red.pt_i : h.pt S ≫ i = spMap (rho S I) ≫ S.x := h.pb.lift_fst _ _ _

theorem Red.pt_s : h.pt S ≫ s₀ = spMap (h.sig S) := h.pb.lift_snd _ _ _

@[reducible] def Red.up (hS : InN κ S) : Thick κ (s₀ ≫ spMap π) where
  B := S.B
  J := big S I
  δ := hS.choose
  nil := nil_sup κ S.δ _ _ rfl hS.choose_spec.1 hS.choose_spec.2 h.nil S.nil
  dp := hS.choose_spec.2
  B₀ := S.B ⧸ big S I
  π := Ideal.Quotient.mk _
  surj := Ideal.Quotient.mk_surjective
  ker _ := Ideal.Quotient.eq_zero_iff_mem
  x := h.pt S
  w := by
    rw [← Category.assoc, h.pt_s, ← GlobalTheory.Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun r ↦ h.sig_π S r

variable {S}

def Red.rh {T : Thick κ (s₀ ≫ spMap π)} (f : S ⟶ h.mor.obj T) : S.B →+* T.B :=
  (f.φ : S.B →+* (h.mor.obj T).B)

theorem Red.rh_algebraMap {T : Thick κ (s₀ ≫ spMap π)} (f : S ⟶ h.mor.obj T) (r : R) :
    h.rh f (algebraMap R S.B r) = algebraMap R T.B r := f.φ.commutes r

def Red.upTo (hS : InN κ S) {T : Thick κ (s₀ ≫ spMap π)} (f : S ⟶ h.mor.obj T) : h.up S hS ⟶ T where
  φ := { (h.rh f) with commutes' := h.rh_algebraMap f }
  φ₀ := Ideal.Quotient.lift _ (T.π.comp (h.rh f)) fun b hb ↦ (T.ker _).2 (by
    have : big S I ≤ T.J.comap (h.rh f) := sup_le (fun b hb ↦ f.mem hb)
      (Ideal.map_le_iff_le_comap.2 fun r hr ↦ by
        change h.rh f (algebraMap R S.B r) ∈ T.J
        rw [h.rh_algebraMap]
        exact T.dp.1 (Ideal.mem_map_of_mem _ hr))
    exact this hb)
  comm _ := rfl
  dp := isDPMorphism_sup κ S.δ _ _ rfl hS.choose_spec.1 hS.choose_spec.2 T.δ _ f.dp (by
    change IsDPMorphism κ T.δ ((h.rh f).comp (algebraMap R S.B))
    rw [show (h.rh f).comp (algebraMap R S.B) = algebraMap R T.B from RingHom.ext (h.rh_algebraMap f)]
    exact T.dp)
  pt := by
    refine h.pb.hom_ext ?_ ?_
    · change (_ ≫ h.pt S) ≫ i = _
      rw [Category.assoc, h.pt_i, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp]
      refine Eq.trans ?_ f.pt
      congr 2
      refine RingHom.ext fun b ↦ ?_
      obtain ⟨b, rfl⟩ := S.surj b
      rw [RingHom.comp_apply, rho_π]
      exact (f.comm b).symm
    · change (_ ≫ h.pt S) ≫ s₀ = _
      have : Mono (spMap π) := by
        have : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ h.surj
        infer_instance
      rw [← cancel_mono (spMap π), Category.assoc, Category.assoc, ← Category.assoc (h.pt S), h.pt_s,
        Category.assoc, T.w, ← GlobalTheory.Cris.spMap_comp, ← GlobalTheory.Cris.spMap_comp]
      congr 1
      refine RingHom.ext fun r ↦ ?_
      simp only [RingHom.comp_apply]
      rw [h.sig_π]
      exact congrArg T.π (h.rh_algebraMap f r)

def Red.unit (hS : InN κ S) : S ⟶ h.mor.obj (h.up S hS) where
  φ := { RingHom.id S.B with commutes' := fun _ ↦ rfl }
  φ₀ := rho S I
  comm := rho_π S I
  dp := hS.choose_spec.1
  pt := (h.pt_i S).symm

end Up

variable {K : Type} (U : K → X.Opens)

abbrev redOpen (i : X₀ ⟶ X) : K → X₀.Opens := fun k ↦ i ⁻¹ᵁ U k

def Red.G : Tag κ (s₀ ≫ spMap π) (redOpen U i) ⥤ (NT κ U (s := s)).FullSubcategory where
  obj T := ⟨⟨h.mor.obj T.T, T.k, T.le⟩, h.inN_obj T.T⟩
  map f := ObjectProperty.homMk (⟨h.mor.functor.map (Tag.Hom.f f), h.le_of_le (Tag.Hom.le f)⟩ : Tag.Hom _ _)
  map_id _ := ObjectProperty.hom_ext _ (Tag.Hom.ext (Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl)))
  map_comp _ _ := ObjectProperty.hom_ext _ (Tag.Hom.ext (Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl)))

def Red.H : (NT κ U (s := s)).FullSubcategory ⥤ Tag κ (s₀ ≫ spMap π) (redOpen U i) where
  obj S := ⟨h.up S.obj.T S.property, S.obj.k, (h.unit S.property).le_preimage S.obj.le⟩
  map {S S'} f := ⟨h.upTo S.property (Tag.Hom.f f.hom ≫ h.unit S'.property),
    fun _ hp ↦ Tag.Hom.le f.hom hp⟩
  map_id _ := Tag.Hom.ext (Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl))
  map_comp f g := by
    refine Tag.Hom.ext (Thick.Hom.ext' (AlgHom.ext fun b ↦ ?_))
    exact (rfl : (Tag.Hom.f g.hom).φ ((Tag.Hom.f f.hom).φ b) = (Tag.Hom.f g.hom).φ ((Tag.Hom.f f.hom).φ b))

abbrev FN (κ : DividedPowers I) (s : X ⟶ Sp R) (U : K → X.Opens) :
    (NT κ U (s := s)).FullSubcategory ⥤ CommAlgCat.{0} R :=
  (NT κ U).ι ⋙ Tag.forget (dp0 R) s U ⋙ O (dp0 R) s

def Red.cG : CoefMap (RingHom.id R) (FN κ s U) (Tag.forget κ _ (redOpen U i) ⋙ O κ (s₀ ≫ spMap π)) where
  G := h.G U
  α T := RingHom.id T.T.B
  naturality _ _ := rfl
  smul T r b := (Algebra.smul_def (A := T.T.B) r b).symm

def Red.cH : CoefMap (RingHom.id R) (Tag.forget κ _ (redOpen U i) ⋙ O κ (s₀ ≫ spMap π)) (FN κ s U) where
  G := h.H U
  α S := RingHom.id S.obj.T.B
  naturality _ _ := rfl
  smul _ _ _ := rfl

def Red.η : 𝟭 _ ⟶ h.H U ⋙ h.G U where
  app S := ObjectProperty.homMk
    (⟨h.unit S.property, le_rfl⟩ : Tag.Hom S.obj ((h.G U).obj ((h.H U).obj S)).obj)
  naturality S S' f := by
    refine ObjectProperty.hom_ext _ (Tag.Hom.ext (Thick.Hom.ext' (AlgHom.ext fun b ↦ ?_)))
    exact (rfl : (Tag.Hom.f f.hom).φ b = (Tag.Hom.f f.hom).φ b)

def Red.ε : h.G U ⋙ h.H U ⟶ 𝟭 _ where
  app T := (⟨h.upTo (h.inN_obj T.T) (𝟙 _), le_rfl⟩ : Tag.Hom ((h.H U).obj ((h.G U).obj T)) T)
  naturality S S' f := by
    refine Tag.Hom.ext (Thick.Hom.ext' (AlgHom.ext fun b ↦ ?_))
    exact (rfl : (Tag.Hom.f f).φ b = (Tag.Hom.f f).φ b)

theorem Red.cG_pull1 : Function.Bijective (h.cG U).pull1 := by
  refine Function.bijective_iff_has_inverse.2 ⟨(h.cH U).pull1, fun c ↦ ?_, fun c ↦ ?_⟩
  · rw [← CoefMap.pullCohomologyOne_comp]
    exact ((CoefMap.id _).pullCohomologyOne_eq_of_natTrans ((h.cG U).comp (h.cH U)) (h.η U) (fun _ b ↦ (rfl : b = b)) c).symm.trans
      (CoefMap.pullCohomologyOne_id c)
  · rw [← CoefMap.pullCohomologyOne_comp]
    exact (((h.cH U).comp (h.cG U)).pullCohomologyOne_eq_of_natTrans (CoefMap.id _) (h.ε U) (fun _ b ↦ (rfl : b = b)) c).trans
      (CoefMap.pullCohomologyOne_id c)

theorem Red.cG_pull2 : Function.Bijective (h.cG U).pull2 := by
  refine Function.bijective_iff_has_inverse.2 ⟨(h.cH U).pull2, fun c ↦ ?_, fun c ↦ ?_⟩
  · rw [← CoefMap.pullCohomologyTwo_comp]
    exact ((CoefMap.id _).pullCohomologyTwo_eq_of_natTrans ((h.cG U).comp (h.cH U)) (h.η U) (fun _ b ↦ (rfl : b = b)) c).symm.trans
      (CoefMap.pullCohomologyTwo_id c)
  · rw [← CoefMap.pullCohomologyTwo_comp]
    exact (((h.cH U).comp (h.cG U)).pullCohomologyTwo_eq_of_natTrans (CoefMap.id _) (h.ε U) (fun _ b ↦ (rfl : b = b)) c).trans
      (CoefMap.pullCohomologyTwo_id c)

end FubiniStudyChowHeightFormula₂.Adr
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}

abbrev chartOpen (s : X ⟶ Sp R) : Chart s → X.Opens := fun U ↦ U.1.1

theorem exists_lev {B : Type} [CommRing B] {J : Ideal B} {δ : DividedPowers J} (h : IsNilDP δ) :
    ∃ n, 1 ≤ n ∧ IsLev δ n := by
  obtain ⟨N, h⟩ := h
  refine ⟨N + 1, by omega, Ideal.span_eq_bot.2 ?_⟩
  rintro _ ⟨l, hl, hN, rfl⟩
  exact h l hl (by omega)

variable {κ : DividedPowers I} {s : X ⟶ Sp R}

theorem acyc_NT (T : Tag (dp0 R) s (chartOpen s)) :
    Acyc R (CostructuredArrow (NT κ (chartOpen s)).ι T) := by
  obtain ⟨n, hn, hT⟩ := exists_lev T.T.nil
  obtain ⟨a₀⟩ := exists_lift T.k T.T T.le
  let D := CostructuredArrow (NT κ (chartOpen s)).ι T
  let mk : ∀ (S : Thick (dp0 R) s) (_ : InN κ S) (_ : ⊤ ≤ S.x ⁻¹ᵁ T.k.1.1) (_ : S ⟶ T.T), D := fun S hS h c ↦
    CostructuredArrow.mk (Y := (⟨⟨S, T.k, h⟩, hS⟩ : (NT κ (chartOpen s)).FullSubcategory))
      (⟨c, le_rfl⟩ : Tag.Hom (⟨S, T.k, h⟩ : Tag (dp0 R) s (chartOpen s)) T)
  let c : ∀ a : D, a.left.obj.T ⟶ T.T := fun a ↦ Tag.Hom.f a.hom
  have hk : ∀ a : D, chartOpen s a.left.obj.k ≤ chartOpen s T.k := fun a ↦ Tag.Hom.le a.hom
  have hle : ∀ a : D, ⊤ ≤ a.left.obj.T.x ⁻¹ᵁ T.k.1.1 := fun a p hp ↦ hk a (a.left.obj.le hp)
  let u : ∀ {a b : D}, (a ⟶ b) → (a.left.obj.T ⟶ b.left.obj.T) := fun f ↦ Tag.Hom.f f.left.hom
  have hu : ∀ {a b : D} (f : a ⟶ b), u f ≫ c b = c a := fun f ↦
    congrArg Tag.Hom.f (CostructuredArrow.w f)
  have ext : ∀ {a b : D} (f g : a ⟶ b), u f = u g → f = g := fun f g h ↦
    CostructuredArrow.hom_ext _ _ (ObjectProperty.hom_ext _ (Tag.Hom.ext h))
  let hom : ∀ (a b : D) (φ : a.left.obj.T ⟶ b.left.obj.T) (_ : chartOpen s a.left.obj.k ≤ chartOpen s b.left.obj.k)
      (_ : φ ≫ c b = c a), a ⟶ b := fun a b φ h e ↦
    CostructuredArrow.homMk (ObjectProperty.homMk (⟨φ, h⟩ : Tag.Hom _ _)) (Tag.Hom.ext e)
  choose P i j hP hl hun using fun a : D ↦ exists_coprod T.k a.left.obj.T a.left.property (hle a) n hn
  choose q hq using fun a : D ↦ (hun a T.T hT (c a) a₀).exists
  let d : D := mk _ (bas_inN T.k) (bas_le T.k.1) a₀
  let Q : D → D := fun a ↦ mk (P a) (hP a) ((i a).le_preimage (hle a)) (q a)
  refine acyc_of_coprod d Q (fun a ↦ hom a (Q a) (i a) (hk a) (hq a).1)
    (fun a ↦ hom d (Q a) (j a) le_rfl (hq a).2) fun a b φ ↦ ?_
  obtain ⟨ψ, hψ, hψ'⟩ := hun a (P b) (hl b) (u φ) (j b)
  have e : ψ ≫ q b = q a := by
    refine (hun a T.T hT (c a) a₀).unique ⟨?_, ?_⟩ (hq a)
    · rw [← Category.assoc, hψ.1]; exact hu φ
    · rw [← Category.assoc, hψ.2]; exact (hq b).2
  refine ⟨hom (Q a) (Q b) ψ le_rfl e, ⟨ext _ _ hψ.1, ext _ _ hψ.2⟩, fun χ hχ ↦ ext _ _ ?_⟩
  exact hψ' (u χ) ⟨congrArg u hχ.1, congrArg u hχ.2⟩

section Final

variable {R₀ : Type} [CommRing R₀] {π : R →+* R₀} {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {i : X₀ ⟶ X}

theorem red_cover (hs : Smooth s) (i : X₀ ⟶ X) : ⨆ k, redOpen (chartOpen s) i k = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, chart_cover hs, Scheme.Hom.preimage_top]

theorem red_inf (hs : IsSeparated s) (i : X₀ ⟶ X) (k l : Chart s) :
    ∃ m, redOpen (chartOpen s) i m = redOpen (chartOpen s) i k ⊓ redOpen (chartOpen s) i l := by
  obtain ⟨m, hm⟩ := chart_inf hs k l
  exact ⟨m, by change i ⁻¹ᵁ m.1.1 = _; rw [hm]; rfl⟩

theorem Red.pull1 (h : Red κ π s s₀ i) (hs : Smooth s) (hs' : IsSeparated s) : Function.Bijective h.mor.pull1 := by
  have a := tag_pull1 (γ := dp0 R) (s := s) (chart_cover hs) (chart_inf hs')
  have b := qa1 (Tag.forget (dp0 R) s (chartOpen s) ⋙ O (dp0 R) s) (NT κ (chartOpen s)).ι acyc_NT
  have c := h.cG_pull1 (chartOpen s)
  have d := tag_pull1 (γ := κ) (s := s₀ ≫ spMap π) (red_cover hs i) (red_inf hs' i)
  refine (Function.Bijective.of_comp_iff' d _).1 ?_
  convert c.comp (b.comp a) using 1
  funext z
  obtain ⟨z, rfl⟩ := H1.mk_surjective _ z
  rfl

theorem Red.pull2 (h : Red κ π s s₀ i) (hs : Smooth s) (hs' : IsSeparated s) : Function.Bijective h.mor.pull2 := by
  have a := tag_pull2 (γ := dp0 R) (s := s) (chart_cover hs) (chart_inf hs')
  have b := qa2 (Tag.forget (dp0 R) s (chartOpen s) ⋙ O (dp0 R) s) (NT κ (chartOpen s)).ι acyc_NT
  have c := h.cG_pull2 (chartOpen s)
  have d := tag_pull2 (γ := κ) (s := s₀ ≫ spMap π) (red_cover hs i) (red_inf hs' i)
  refine (Function.Bijective.of_comp_iff' d _).1 ?_
  convert c.comp (b.comp a) using 1
  funext z
  obtain ⟨z, rfl⟩ := H2.mk_surjective _ z
  rfl

end Final

theorem crystallineDeRham : GlobalTheory.Published.CrystallineDeRham := fun _ _ _ _ hκ _ _ _ hπ hI _ _ _ _ _ hs hs' _ hp _ ↦
  ⟨Red.pull1 ⟨hκ, hπ, hI, hp⟩ hs hs', Red.pull2 ⟨hκ, hπ, hI, hp⟩ hs hs'⟩

end FubiniStudyChowHeightFormula₂.Adr
