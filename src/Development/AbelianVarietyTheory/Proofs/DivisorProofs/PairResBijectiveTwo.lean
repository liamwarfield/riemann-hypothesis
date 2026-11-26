module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingsAgreeOnSubfieldNe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCoboundaryOfBasisFunctor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneFormsCocycleRestrictSubCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneFormsCocycleRestrictSubCoboundary
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR.FormExt

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem exists_cocycle_restrict_sub_eq_coboundary : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Surjective (CoefMap.restrict (FormExt.omExt F) G).pull1 → (∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), β' t t'' (a ≫ b) = p1 F (G.map b) (β' t t' a) + β' t' t'' b) → ∃ β : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), β T T'' (φ ≫ ψ) = p1 F ψ (β T T' φ) + β T' T'' ψ) ∧ ∃ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), β _ _ (G.map a) - β' t t' a = θ' t' - p1 F (G.map a) (θ' t)) := by
  intro R _ C _ C' _ F G hsurj β' hβ'
  let f' : Z1 (G ⋙ omExt F) := ⟨fun t t' a ↦ (TrivSqZeroExt.inr (β' t t' a) : (omExt F).obj (G.obj t')),
    fun t t' t'' a b ↦ by
      apply TrivSqZeroExt.ext
      · show (0 : F.obj (G.obj t'')) = (extMap F (G.map b) (TrivSqZeroExt.inr (β' t t' a))).fst + 0
        rw [fst_extMap]; simp
      · show β' t t'' (a ≫ b) = (extMap F (G.map b) (TrivSqZeroExt.inr (β' t t' a))).snd + β' t' t'' b
        rw [snd_extMap, hβ']; rfl⟩
  obtain ⟨h0, hh⟩ := hsurj (H1.mk _ f')
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ h0
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hh
  obtain ⟨g, hg⟩ := hh
  refine ⟨fun T T' φ ↦ (f.1 T T' φ).snd, fun T T' T'' φ ψ ↦ ?_, fun t ↦ (g t).snd, fun t t' a ↦ ?_⟩
  · have e := congrArg TrivSqZeroExt.snd (Z1.comp f φ ψ)
    have e2 : TrivSqZeroExt.snd (mp (omExt F) ψ (f.1 T T' φ) + f.1 T' T'' ψ) =
        p1 F ψ (f.1 T T' φ).snd + (f.1 T' T'' ψ).snd := by
      show (extMap F ψ (f.1 T T' φ)).snd + (f.1 T' T'' ψ).snd = _
      exact congrArg (· + (f.1 T' T'' ψ).snd) (snd_extMap F ψ (f.1 T T' φ))
    exact e.trans e2
  · have e := congrArg TrivSqZeroExt.snd (congrFun (congrFun (congrFun hg t) t') a)
    have e2 : (g t').snd - p1 F (G.map a) (g t).snd = (f.1 _ _ (G.map a)).snd - β' t t' a :=
      calc (g t').snd - p1 F (G.map a) (g t).snd
          = (g t').snd - (extMap F (G.map a) (g t)).snd :=
            congrArg (fun z ↦ (g t').snd - z) (snd_extMap F (G.map a) (g t)).symm
        _ = TrivSqZeroExt.snd (d0 (G ⋙ omExt F) g t t' a) := rfl
        _ = _ := e
        _ = (f.1 _ _ (G.map a)).snd - β' t t' a := rfl
    exact e2.symm

end GlobalTheory.CechDR.FormExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneFormsCocycleRestrictSubCoboundaryStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oneForms_cocycle_restrict_sub_coboundary : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Surjective (CoefMap.restrict (FormExt.omExt F) G).pull1 → (∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), β' t t'' (a ≫ b) = p1 F (G.map b) (β' t t' a) + β' t' t'' b) → ∃ β : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), β T T'' (φ ≫ ψ) = p1 F ψ (β T T' φ) + β T' T'' ψ) ∧ ∃ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), β _ _ (G.map a) - β' t t' a = θ' t' - p1 F (G.map a) (θ' t)) := by
  first | exact @GlobalTheory.CechDR.FormExt.exists_cocycle_restrict_sub_eq_coboundary | exact GlobalTheory.CechDR.FormExt.exists_cocycle_restrict_sub_eq_coboundary | (intros; apply GlobalTheory.CechDR.FormExt.exists_cocycle_restrict_sub_eq_coboundary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaFirstOrderCocycleLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaFirstOrderCocycleLift
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem pullHyp2_restrict_injective {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C)
    (h2 : Function.Injective (CoefMap.restrict F G).pull2)
    (h1 : Function.Surjective (CoefMap.restrict F G).pull1)
    (hc : ∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
        κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) →
      ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R],
        (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) →
        ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T))
    (hf : Function.Surjective (pullGlob1 (CoefMap.restrict F G)))
    (hs : ∀ (T : C) (x : Om R (F.obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm F 2 u x = 0) → x = 0) :
    Function.Injective (pullHyp2 (CoefMap.restrict F G)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, rfl⟩ := Hyp2.mk_surjective F x
  rw [pullHyp2_mk, Hyp2.mk_eq_zero] at hx
  obtain ⟨⟨f₀, θ₀⟩, hfe⟩ := hx
  obtain ⟨f', rfl⟩ : ∃ f' : ∀ (t t' : C') (_ : t ⟶ t'), F.obj (G.obj t'), (f' : C1 (G ⋙ F)) = f₀ :=
    ⟨f₀, rfl⟩
  obtain ⟨θ', rfl⟩ : ∃ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (θ' : A0 (G ⋙ F)) = θ₀ := ⟨θ₀, rfl⟩
  have hz : ∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''),
      mp F (G.map b) (f' t t' a) - f' t t'' (a ≫ b) + f' t' t'' b =
        c.1.1 _ _ _ (G.map a) (G.map b) :=
    fun t t' t'' a b ↦ congrArg (fun y : Tot2 (G ⋙ F) ↦ y.1 t t' t'' a b) hfe
  have ha : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'),
      θ' t' - p1 F (G.map a) (θ' t) - D R _ (f' t t' a) = c.1.2.1 _ _ (G.map a) :=
    fun t t' a ↦ (congrArg (fun y : Tot2 (G ⋙ F) ↦ y.2.1 t t' a) hfe).trans (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t' _)
  have hη : ∀ t, dOne R _ (θ' t) = c.1.2.2 (G.obj t) :=
    fun t ↦ (congrArg (fun y : Tot2 (G ⋙ F) ↦ y.2.2 t) hfe).trans (qOm_restrict F G t _)

  have hz0 : H2.mk F ⟨c.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1⟩ = 0 := h2 (by
    rw [CoefMap.pullCohomologyTwo_class, map_zero]
    exact H2.mk_eq_zero.2 ⟨f', by funext t t' t'' a b; exact hz a b⟩)
  obtain ⟨f, hfz⟩ := H2.mk_eq_zero.1 hz0
  have hf1 : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      mp F ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = c.1.1 T T' T'' φ ψ :=
    fun T T' T'' φ ψ ↦ congrFun (congrFun (congrFun (congrFun (congrFun hfz T) T') T'') φ) ψ

  let u : Z1 (G ⋙ F) := ⟨fun t t' a ↦ f' t t' a - f _ _ (G.map a), fun t t' t'' a b ↦ by
    have e1 := hz a b
    have e2 := hf1 (G.map a) (G.map b)
    rw [← G.map_comp] at e2
    show f' t t'' (a ≫ b) - f _ _ (G.map (a ≫ b)) =
      mp F (G.map b) (f' t t' a - f _ _ (G.map a)) + (f' t' t'' b - f _ _ (G.map b))
    rw [map_sub]
    linear_combination e2 - e1⟩
  obtain ⟨g₀, hg₀⟩ := h1 (H1.mk _ u)
  obtain ⟨g, rfl⟩ := H1.mk_surjective F g₀
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hg₀
  obtain ⟨h₀, hh'⟩ := hg₀
  obtain ⟨h', rfl⟩ : ∃ h' : ∀ t, F.obj (G.obj t), (h' : C0 (G ⋙ F)) = h₀ := ⟨h₀, rfl⟩
  have hfu : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), f' t t' a =
      f _ _ (G.map a) + g.1 _ _ (G.map a) - (h' t' - mp F (G.map a) (h' t)) := fun t t' a ↦ by
    have e : h' t' - mp F (G.map a) (h' t) = g.1 _ _ (G.map a) - (f' t t' a - f _ _ (G.map a)) :=
      congrFun (congrFun (congrFun hh' t) t') a
    linear_combination e
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : C1 F, ∀ T T' φ, f₁ T T' φ = f T T' φ + g.1 T T' φ := ⟨_, fun _ _ _ ↦ rfl⟩
  have hf1' : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      mp F ψ (f₁ T T' φ) - f₁ T T'' (φ ≫ ψ) + f₁ T' T'' ψ = c.1.1 T T' T'' φ ψ := fun T T' T'' φ ψ ↦ by
    rw [hf₁, hf₁, hf₁, map_add (f := _)]
    linear_combination hf1 φ ψ - Z1.comp g φ ψ

  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : A1 F, ∀ T T' φ, a₁ T T' φ = c.1.2.1 T T' φ + D R _ (f₁ T T' φ) :=
    ⟨_, fun _ _ _ ↦ rfl⟩
  have hac : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a₁ T T'' (φ ≫ ψ) = p1 F ψ (a₁ T T' φ) + a₁ T' T'' ψ := fun T T' T'' φ ψ ↦ by
    have e := cechDeRhamTotalCocyclesTwo.one c φ ψ
    rw [← hf1' φ ψ, map_add (f := _), map_sub] at e
    rw [ha₁, ha₁, ha₁, map_add (f := _), p1_D, e]
    abel
  obtain ⟨θ'', hθ''⟩ : ∃ θ'' : ∀ t, Ω[F.obj (G.obj t)⁄R], ∀ t, θ'' t = θ' t + D R _ (h' t) :=
    ⟨_, fun _ ↦ rfl⟩
  have hres : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), a₁ _ _ (G.map a) = θ'' t' - p1 F (G.map a) (θ'' t) :=
    fun t t' a ↦ by
      have e := ha a
      rw [hfu a] at e
      simp only [map_add (f := _), map_sub] at e
      rw [ha₁, hθ'', hθ'', hf₁]
      simp only [map_add (f := _), p1_D]
      linear_combination (norm := abel1) -e
  obtain ⟨θ, hθ⟩ := hc a₁ hac θ'' hres

  let ω' : Glob1 (G ⋙ F) := ⟨fun t ↦ θ (G.obj t) - θ'' t, fun t t' a ↦ by
    have e1 := hθ (G.map a)
    have e2 := hres a
    show θ (G.obj t') - θ'' t' = p1 F (G.map a) (θ (G.obj t) - θ'' t)
    rw [map_sub]
    linear_combination (norm := abel1) e2 - e1⟩
  obtain ⟨ω, hω⟩ := hf ω'
  have hωG : ∀ t, ω.1 (G.obj t) = θ (G.obj t) - θ'' t := fun t ↦
    (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t _).symm.trans (congrArg (fun y : Glob1 (G ⋙ F) ↦ y.1 t) hω)
  obtain ⟨θ₁, hθ₁⟩ : ∃ θ₁ : A0 F, ∀ T, θ₁ T = θ T - ω.1 T := ⟨_, fun _ ↦ rfl⟩
  have hθ1 : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), a₁ T T' φ = θ₁ T' - p1 F φ (θ₁ T) := fun T T' φ ↦ by
    rw [hθ₁, hθ₁, map_sub, ← ω.2 φ, hθ φ]; abel
  have hθ1G : ∀ t, θ₁ (G.obj t) = θ'' t := fun t ↦ by rw [hθ₁, hωG]; abel

  obtain ⟨η₂, hη₂⟩ : ∃ η₂ : W0 F 2, ∀ T, η₂ T = c.1.2.2 T - dOne R _ (θ₁ T) := ⟨_, fun _ ↦ rfl⟩
  have hη2 : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η₂ T' = pOm F 2 φ (η₂ T) := fun T T' φ ↦ by
    have e1 := cechDeRhamTotalCocyclesTwo.two c φ
    have e2 := congrArg (dOne R _) (hθ1 φ)
    rw [ha₁] at e2
    simp only [map_add (f := _), map_sub, dOne_D, add_zero] at e2
    rw [hη₂, hη₂, map_sub, pOm_dOne]
    linear_combination (norm := abel1) e1 + e2
  have hη2G : ∀ t, η₂ (G.obj t) = 0 := fun t ↦ by
    rw [hη₂, hθ1G, hθ'', map_add (f := _), dOne_D, add_zero, ← hη t, sub_self]
  have hη0 : ∀ T, η₂ T = 0 := fun T ↦ hs T _ fun t u ↦ by rw [← hη2 u, hη2G]
  refine Hyp2.mk_eq_zero.2 ⟨(f₁, θ₁), Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_⟩
  · exact hf1' φ ψ
  · have e := hθ1 φ
    rw [ha₁] at e
    show θ₁ T' - p1 F φ (θ₁ T) - D R _ (f₁ T T' φ) = c.1.2.1 T T' φ
    linear_combination (norm := abel1) -e
  · have e := hη0 T
    rw [hη₂] at e
    exact (sub_eq_zero.1 e).symm

end GlobalTheory.CechDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaFirstOrderCocycleLiftStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comma_first_order_cocycle_lift : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Injective (CoefMap.restrict F G).pull2 → Function.Surjective (CoefMap.restrict F G).pull1 → (∀ κ : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = p1 F ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - p1 F (G.map a) (θ' t)) → ∃ θ : A0 F, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - p1 F φ (θ T)) → Function.Surjective (pullGlob1 (CoefMap.restrict F G)) → (∀ (T : C) (x : Om R (F.obj T) 2), (∀ t (u : T ⟶ G.obj t), pOm F 2 u x = 0) → x = 0) → Function.Injective (pullHyp2 (CoefMap.restrict F G)) := by
  first | exact @GlobalTheory.CechDR.pullHyp2_restrict_injective | exact GlobalTheory.CechDR.pullHyp2_restrict_injective | (intros; apply GlobalTheory.CechDR.pullHyp2_restrict_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormsTwoCocycleCoboundaryOfRestrict
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormsTwoCocycleCoboundaryOfRestrict
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR.FormExt

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem inr_add_inr_eq {A M : Type} [AddCommGroup A] [AddCommGroup M] {x y z w : M}
    (h : x + y = z + w) :
    (TrivSqZeroExt.inr x : TrivSqZeroExt A M) + TrivSqZeroExt.inr y =
      TrivSqZeroExt.inr z + TrivSqZeroExt.inr w := by
  rw [← TrivSqZeroExt.inr_add, ← TrivSqZeroExt.inr_add, h]

theorem inr_sub_add_inr_eq {A M : Type} [AddCommGroup A] [AddCommGroup M] {x y z w : M}
    (h : x - y + z = w) :
    (TrivSqZeroExt.inr x : TrivSqZeroExt A M) - TrivSqZeroExt.inr y + TrivSqZeroExt.inr z =
      TrivSqZeroExt.inr w := by
  rw [← TrivSqZeroExt.inr_sub, ← TrivSqZeroExt.inr_add, h]

theorem snd_sub_add {A M : Type} [AddCommGroup A] [AddCommGroup M] (a b c : TrivSqZeroExt A M) :
    (a - b + c).snd = a.snd - b.snd + c.snd := by
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub]

theorem mp_omExt_inr {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    {T T' : C} (φ : T ⟶ T') (x : Ω[F.obj T⁄R]) :
    mp (omExt F) φ (TrivSqZeroExt.inr x : (omExt F).obj T) =
      (TrivSqZeroExt.inr (p1 F φ x) : (omExt F).obj T') :=
  TrivSqZeroExt.ext ((fst_extMap F φ _).trans (by rw [TrivSqZeroExt.fst_inr, map_zero]; rfl))
    ((snd_extMap F φ _).trans (by rw [TrivSqZeroExt.snd_inr]; rfl))

theorem coboundary_of_restrict_forms : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Injective (CoefMap.restrict (FormExt.omExt F) G).pull2 → (∀ κ : A2 F, (∀ ⦃T T' T'' T''' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''), p1 F χ (κ T T' T'' φ ψ) + κ T T'' T''' (φ ≫ ψ) χ = κ T T' T''' φ (ψ ≫ χ) + κ T' T'' T''' ψ χ) → ∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), κ _ _ _ (G.map a) (G.map b) = p1 F (G.map b) (β' t t' a) - β' t t'' (a ≫ b) + β' t' t'' b) → ∃ β : A1 F, ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T' T'' φ ψ = p1 F ψ (β T T' φ) - β T T'' (φ ≫ ψ) + β T' T'' ψ) := by
  intro R _ C _ C' _ F G hinj κ hκ β' hβ'
  let z : Z2 (omExt F) := ⟨fun T T' T'' φ ψ ↦ TrivSqZeroExt.inr (κ T T' T'' φ ψ),
    fun T T' T'' T''' φ ψ χ ↦ by
      simp only []
      rw [mp_omExt_inr]
      exact inr_add_inr_eq (hκ φ ψ χ)⟩
  have h0 : (CoefMap.restrict (omExt F) G).pull2 (H2.mk (omExt F) z) = 0 := by
    rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero]
    refine ⟨fun t t' a ↦ (TrivSqZeroExt.inr (β' t t' a) : (omExt F).obj (G.obj t')), ?_⟩
    funext t t' t'' a b
    exact (congrArg (fun x : TrivSqZeroExt (F.obj (G.obj t'')) Ω[F.obj (G.obj t'')⁄R] ↦
      x - TrivSqZeroExt.inr (β' t t'' (a ≫ b)) + TrivSqZeroExt.inr (β' t' t'' b))
      (mp_omExt_inr F (G.map b) (β' t t' a))).trans (inr_sub_add_inr_eq (hβ' a b).symm)
  have h1 : H2.mk (omExt F) z = 0 := hinj (h0.trans (map_zero _).symm)
  obtain ⟨f, hf⟩ := H2.mk_eq_zero.1 h1
  refine ⟨fun T T' φ ↦ (f T T' φ).snd, fun T T' T'' φ ψ ↦ ?_⟩
  have e := congrArg TrivSqZeroExt.snd
    (congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') φ) ψ)
  have e2 := (snd_sub_add (mp (omExt F) ψ (f T T' φ)) (f T T'' (φ ≫ ψ)) (f T' T'' ψ)).symm.trans
    (e.trans (TrivSqZeroExt.snd_inr _ _))
  rw [show (mp (omExt F) ψ (f T T' φ)).snd = p1 F ψ (f T T' φ).snd from snd_extMap F ψ _] at e2
  exact e2.symm

end GlobalTheory.CechDR.FormExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormsTwoCocycleCoboundaryOfRestrictStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneForms_twoCocycle_coboundary_of_restrict : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Injective (CoefMap.restrict (FormExt.omExt F) G).pull2 → (∀ κ : A2 F, (∀ ⦃T T' T'' T''' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''), p1 F χ (κ T T' T'' φ ψ) + κ T T'' T''' (φ ≫ ψ) χ = κ T T' T''' φ (ψ ≫ χ) + κ T' T'' T''' ψ χ) → ∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), κ _ _ _ (G.map a) (G.map b) = p1 F (G.map b) (β' t t' a) - β' t t'' (a ≫ b) + β' t' t'' b) → ∃ β : A1 F, ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T' T'' φ ψ = p1 F ψ (β T T' φ) - β T T'' (φ ≫ ψ) + β T' T'' ψ) := by
  first | exact @GlobalTheory.CechDR.FormExt.coboundary_of_restrict_forms | exact GlobalTheory.CechDR.FormExt.coboundary_of_restrict_forms | (intros; apply GlobalTheory.CechDR.FormExt.coboundary_of_restrict_forms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocalisationAtElementsTrivSqZeroExtForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocalisationAtElementsTrivSqZeroExtForms
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR

theorem mOm_eq_exteriorPowerMapOver {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] {α : A →+* B}
    (h : SemiHom (RingHom.id R) α) (e : ∀ a, α a = algebraMap A B a) (j : ℕ) (x : Om R A j) :
    h.mOm j x = GlobalTheory.exteriorPowerMapOver B j (KaehlerDifferential.map R R A B) x := by
  let L : Om R A j →ₗ[A] Om R B j :=
    { toFun := h.mOm j
      map_add' := map_add _
      map_smul' := fun a y ↦ by
        rw [h.mOm_smul, RingHom.id_apply, e]; exact algebraMap_smul B a _ }
  have hL : L = GlobalTheory.exteriorPowerMapOver B j (KaehlerDifferential.map R R A B) := by
    apply exteriorPower.linearMap_ext
    ext1 v
    rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply,
      GlobalTheory.exteriorPowerMapOver_ιMulti]
    apply Subtype.ext
    change h.mDR _ = _
    rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
      ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
    congr 1
    refine congrArg List.ofFn (funext fun i ↦ ?_)
    exact (h.mDR_ι (v i)).trans (congrArg _ (h.oneFormMap_eq_kaehlerDifferential_map e (v i)))
  exact LinearMap.congr_fun hL x

end GlobalTheory.CechDR

namespace GlobalTheory.CechDR.FormExtJ

attribute [local instance] opModJ isCentralScalarJ isScalarTowerJ

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ)

theorem surj_keyJ {T T' : C} (l : T ⟶ T') (c : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j))
    (y : TrivSqZeroExt (F.obj T') (Om R (F.obj T') j)) (a₀ : F.obj T) (η₀ : Om R (F.obj T) j)
    (k₁ k₂ : ℕ) (ha : y.fst * mp F l (c.fst ^ k₁) = mp F l a₀)
    (hη : mp F l (c.fst ^ k₂) • y.snd = pOm F j l η₀) :
    y * extMapJ F j l c ^ (k₁ + k₂ + 1) = extMapJ F j l (TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀)) := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, fst_extMapJ, fst_extMapJ]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, map_mul,
      map_pow] at ha ⊢
    linear_combination (mp F l c.fst) ^ (k₂ + 1) * ha
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, snd_extMapJ, fst_extMapJ, snd_extMapJ]
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
      TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add, map_add, map_nsmul,
      pOm_smul, map_mul, map_pow, op_smul_eq_smul, Nat.pred_succ] at ha hη ⊢
    rw [← hη, ← ha]
    module

theorem ker_keyJ {T : C} (c x : TrivSqZeroExt (F.obj T) (Om R (F.obj T) j)) (m₁ m₂ : ℕ)
    (h₁ : c.fst ^ m₁ * x.fst = 0) (h₂ : c.fst ^ m₂ • x.snd = 0) : c ^ (m₁ + m₂ + 1) * x = 0 := by
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow, TrivSqZeroExt.fst_zero]
    linear_combination c.fst ^ (m₂ + 1) * h₁
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _),
      TrivSqZeroExt.fst_pow, TrivSqZeroExt.snd_zero, op_smul_eq_smul, Nat.pred_succ]
    linear_combination (norm := module) c.fst ^ (m₁ + 1) • h₂ + h₁ • ((m₁ + m₂ + 1) • c.fst ^ m₂ • c.snd)

theorem hasLoc_omjExt (H : Desc.HasLoc F) : Desc.HasLoc (omjExt F j) := by
  intro T c
  obtain ⟨T', l, h1, h2, h3, h4⟩ := H T c.fst
  letI : Algebra (F.obj T) (F.obj T') := (mp F l : F.obj T →+* F.obj T').toAlgebra
  haveI : IsScalarTower R (F.obj T) (F.obj T') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((mp F l).commutes r).symm
  haveI := FormExt.isLocalization_of_data F l c.fst h1 h2 h3
  haveI : Algebra.FormallyEtale (F.obj T) (F.obj T') :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers c.fst)
  have hb := GlobalTheory.TopForm.isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale R (F.obj T) (F.obj T')) j
  haveI := (isLocalizedModule_iff_isBaseChange (Submonoid.powers c.fst) (F.obj T') _).2 hb
  have hp : ∀ ω, pOm F j l ω =
      GlobalTheory.exteriorPowerMapOver (F.obj T') j (KaehlerDifferential.map R R (F.obj T) (F.obj T')) ω :=
    mOm_eq_exteriorPowerMapOver _ (fun _ ↦ rfl) j
  have hs : ∀ (a : F.obj T) (η : Om R (F.obj T') j), a • η = mp F l a • η := fun a η ↦
    (algebraMap_smul (F.obj T') a η).symm
  refine ⟨T', l, (isUnit_mp_omjExt_iff F j l c).2 h1, fun y ↦ ?_, fun x hx ↦ ?_,
    fun S u hu ↦ h4 S u ((isUnit_mp_omjExt_iff F j u c).1 hu)⟩
  · obtain ⟨⟨a₀, _, k₁, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers c.fst) y.fst
    obtain ⟨⟨η₀, _, k₂, rfl⟩, hη⟩ := IsLocalizedModule.surj (Submonoid.powers c.fst)
      (GlobalTheory.exteriorPowerMapOver (F.obj T') j (KaehlerDifferential.map R R (F.obj T) (F.obj T'))) y.snd
    change y.fst * mp F l (c.fst ^ k₁) = mp F l a₀ at ha
    change (c.fst ^ k₂) • y.snd = _ at hη
    rw [hs, ← hp] at hη
    refine ⟨k₁ + k₂ + 1, TrivSqZeroExt.inl (a₀ * c.fst ^ (k₂ + 1)) +
      TrivSqZeroExt.inr ((k₁ + k₂ + 1) • (a₀ * c.fst ^ k₂) • c.snd + c.fst ^ (k₁ + 1) • η₀), ?_⟩
    exact surj_keyJ F j l c y a₀ η₀ k₁ k₂ ha hη
  · have e1 : mp F l x.fst = 0 := (fst_extMapJ F j l x).symm.trans (congrArg TrivSqZeroExt.fst hx)
    have e2 : GlobalTheory.exteriorPowerMapOver (F.obj T') j
        (KaehlerDifferential.map R R (F.obj T) (F.obj T')) x.snd = 0 :=
      (hp _).symm.trans ((snd_extMapJ F j l x).symm.trans (congrArg TrivSqZeroExt.snd hx))
    obtain ⟨m₁, h₁⟩ := h3 _ e1
    obtain ⟨⟨_, m₂, rfl⟩, h₂⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers c.fst)
      (f := GlobalTheory.exteriorPowerMapOver (F.obj T') j (KaehlerDifferential.map R R (F.obj T) (F.obj T')))
      (x₁ := x.snd) (x₂ := 0) (by rw [e2, map_zero])
    rw [smul_zero, Submonoid.smul_def] at h₂
    exact ⟨m₁ + m₂ + 1, ker_keyJ F j c x m₁ m₂ h₁ h₂⟩

end GlobalTheory.CechDR.FormExtJ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocalisationAtElementsTrivSqZeroExtFormsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasLocalisationAtElements_trivSqZeroExtForms : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ), Desc.HasLoc F → Desc.HasLoc (FormExtJ.omjExt F j) := by
  first | exact @GlobalTheory.CechDR.FormExtJ.hasLoc_omjExt | exact GlobalTheory.CechDR.FormExtJ.hasLoc_omjExt | (intros; apply GlobalTheory.CechDR.FormExtJ.hasLoc_omjExt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaSecondOrderCocycleLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaSecondOrderCocycleLift
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem pullHyp2_restrict_surjective : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Surjective (CoefMap.restrict F G).pull2 → (∀ κ : A2 F, (∀ ⦃T T' T'' T''' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''), p1 F χ (κ T T' T'' φ ψ) + κ T T'' T''' (φ ≫ ψ) χ = κ T T' T''' φ (ψ ≫ χ) + κ T' T'' T''' ψ χ) → ∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), κ _ _ _ (G.map a) (G.map b) = p1 F (G.map b) (β' t t' a) - β' t t'' (a ≫ b) + β' t' t'' b) → ∃ β : A1 F, ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T' T'' φ ψ = p1 F ψ (β T T' φ) - β T T'' (φ ≫ ψ) + β T' T'' ψ) → (∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), β' t t'' (a ≫ b) = p1 F (G.map b) (β' t t' a) + β' t' t'' b) → ∃ β : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), β T T'' (φ ≫ ψ) = p1 F ψ (β T T' φ) + β T' T'' ψ) ∧ ∃ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), β _ _ (G.map a) - β' t t' a = θ' t' - p1 F (G.map a) (θ' t)) → (∀ κ : W1 F 2, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = pOm F 2 ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Om R (F.obj (G.obj t)) 2, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - pOm F 2 (G.map a) (θ' t)) → ∃ θ : W0 F 2, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - pOm F 2 φ (θ T)) → (∀ η' : ∀ t, Om R (F.obj (G.obj t)) 2, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), η' t' = pOm F 2 (G.map a) (η' t)) → ∃ η : W0 F 2, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η T' = pOm F 2 φ (η T)) ∧ ∀ t, η (G.obj t) = η' t) → (∀ (T : C) (x : Om R (F.obj T) 3), (∀ t (u : T ⟶ G.obj t), pOm F 3 u x = 0) → x = 0) → Function.Surjective (pullHyp2 (CoefMap.restrict F G)) := by
  intro R _ C _ C' _ F G hO hκ hl h2 he hs c'
  obtain ⟨c', rfl⟩ := Hyp2.mk_surjective _ c'
  obtain ⟨h0, hh⟩ := hO (H2.mk _ ⟨c'.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c'.2).1⟩)
  obtain ⟨z, rfl⟩ := H2.mk_surjective F h0
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hh
  obtain ⟨y', hy'⟩ := hh
  let z' : ∀ (t t' t'' : C') (_ : t ⟶ t') (_ : t' ⟶ t''), F.obj (G.obj t'') := c'.1.1
  let a' : ∀ (t t' : C') (_ : t ⟶ t'), Ω[F.obj (G.obj t')⁄R] := c'.1.2.1
  let η' : ∀ t : C', Om R (F.obj (G.obj t)) 2 := c'.1.2.2
  let y : ∀ (t t' : C') (_ : t ⟶ t'), F.obj (G.obj t') := y'
  have hz : ∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), z.1 _ _ _ (G.map a) (G.map b) =
      z' t t' t'' a b + (mp F (G.map b) (y t t' a) - y t t'' (a ≫ b) + y t' t'' b) := by
    intro t t' t'' a b
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hy' t) t') t'') a) b
    change mp F (G.map b) (y t t' a) - y t t'' (a ≫ b) + y t' t'' b =
      z.1 _ _ _ (G.map a) (G.map b) - z' t t' t'' a b at e
    rw [e]; ring
  let a2 : ∀ (t t' : C') (_ : t ⟶ t'), Ω[F.obj (G.obj t')⁄R] := fun t t' a ↦ a' t t' a - D R _ (y t t' a)
  have ha2 : ∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), a2 t t'' (a ≫ b) =
      p1 F (G.map b) (a2 t t' a) + a2 t' t'' b + D R _ (z.1 _ _ _ (G.map a) (G.map b)) := by
    intro t t' t'' a b
    have e : a' t t'' (a ≫ b) = p1 F (G.map b) (a' t t' a) + a' t' t'' b +
      D R _ (z' t t' t'' a b) := cechDeRhamTotalCocyclesTwo.one c' a b
    simp only [a2]
    rw [e, hz, map_sub, p1_D]
    simp only [map_add (f := _), map_sub]
    abel

  obtain ⟨a₀, ha₀⟩ := hκ (fun T T' T'' φ ψ ↦ -D R _ (z.1 T T' T'' φ ψ)) (by
      intro T T' T'' T''' φ ψ χ
      have e := z.2 φ ψ χ
      simp only [p1_D, map_neg]
      rw [← neg_add, ← neg_add, ← map_add (f := _), ← map_add (f := _), e]) a2 (by
      intro t t' t'' a b
      beta_reduce
      rw [ha2]; abel)
  have ha₀' : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a₀ T T'' (φ ≫ ψ) = p1 F ψ (a₀ T T' φ) + a₀ T' T'' ψ + D R _ (z.1 T T' T'' φ ψ) := by
    intro T T' T'' φ ψ
    have e := ha₀ φ ψ
    beta_reduce at e
    linear_combination (norm := abel1) e
  obtain ⟨β, hβ, θ', hθ'⟩ := hl (fun t t' a ↦ a₀ _ _ (G.map a) - a2 t t' a) (by
      intro t t' t'' a b
      beta_reduce
      rw [G.map_comp, ha2, ha₀']
      simp only [a2, map_sub]
      abel)
  let a : A1 F := fun T T' φ ↦ a₀ T T' φ - β T T' φ
  have ha : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ + D R _ (z.1 T T' T'' φ ψ) := by
    intro T T' T'' φ ψ
    simp only [a]
    rw [ha₀', hβ, map_sub]
    abel
  have haG : ∀ ⦃t t' : C'⦄ (b : t ⟶ t'), a _ _ (G.map b) =
      a2 t t' b - (θ' t' - p1 F (G.map b) (θ' t)) := by
    intro t t' b
    have e := hθ' b
    beta_reduce at e
    simp only [a]
    linear_combination (norm := abel1) -e
  let η3 : ∀ t : C', Om R (F.obj (G.obj t)) 2 := fun t ↦ η' t - dOne R _ (θ' t)
  have hη3 : ∀ ⦃t t' : C'⦄ (b : t ⟶ t'), dOne R _ (a _ _ (G.map b)) =
      η3 t' - pOm F 2 (G.map b) (η3 t) := by
    intro t t' b
    have e : η' t' = pOm F 2 (G.map b) (η' t) + dOne R _ (a' t t' b) := cechDeRhamTotalCocyclesTwo.two c' b
    simp only [η3]
    rw [haG, e]
    simp only [a2, map_sub, dOne_D, pOm_dOne]
    abel
  obtain ⟨η₀, hη₀⟩ := h2 (fun T T' φ ↦ dOne R _ (a T T' φ)) (by
      intro T T' T'' φ ψ
      beta_reduce
      rw [ha, map_add (f := _), map_add (f := _), dOne_D, pOm_dOne, add_zero]) η3 hη3
  obtain ⟨ε, hε, hεG⟩ := he (fun t ↦ η3 t - η₀ (G.obj t)) (by
      intro t t' b
      beta_reduce
      have e1 := hη3 b
      have e2 := hη₀ (G.map b)
      beta_reduce at e2
      rw [map_sub]
      linear_combination (norm := abel1) e2 - e1)
  let η : W0 F 2 := fun T ↦ η₀ T + ε T
  have hη : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η T' = pOm F 2 φ (η T) + dOne R _ (a T T' φ) := by
    intro T T' φ
    have e := hη₀ φ
    beta_reduce at e
    simp only [η]
    rw [hε φ, e, map_add (f := _)]
    abel
  have hηG : ∀ t, η (G.obj t) = η3 t := by
    intro t
    simp only [η]
    rw [hεG t]
    abel
  have hclosed : ∀ T, dTwo R _ (η T) = 0 := by
    intro T
    refine hs T _ fun t u ↦ ?_
    have e : pOm F 2 u (η T) = η3 t - dOne R _ (a _ _ u) := by
      rw [← hηG, hη u]; abel
    have e3 : dTwo R _ (η' t) = 0 := cechDeRhamTotalCocyclesTwo.closed c' t
    rw [pOm_dTwo, e]
    simp only [η3, map_sub, dTwo_dOne, e3, sub_zero]
  let c : cechDeRhamTotalCocyclesTwo F := ⟨(z.1, a, η), mem_cechDeRhamTotalCocyclesTwo_iff.2 ⟨z.2, ha, hη, hclosed⟩⟩
  refine ⟨Hyp2.mk F c, ?_⟩
  rw [pullHyp2_mk, Hyp2.mk_eq_mk]
  refine ⟨(y, fun t ↦ -θ' t), Tot2.ext (fun t t' t'' b b' ↦ ?_) (fun t t' b ↦ ?_) fun t ↦ ?_⟩
  · change mp F (G.map b') (y t t' b) - y t t'' (b ≫ b') + y t' t'' b' =
      z.1 _ _ _ (G.map b) (G.map b') - z' t t' t'' b b'
    rw [hz]; ring
  · change -θ' t' - p1 F (G.map b) (-θ' t) - D R _ (y t t' b) =
      q1 (CoefMap.restrict F G) t' (a _ _ (G.map b)) - c'.1.2.1 t t' b
    have e4 : q1 (CoefMap.restrict F G) t' (a _ _ (G.map b)) =
        a2 t t' b - (θ' t' - p1 F (G.map b) (θ' t)) := (cechDeRhamCoefMapOneForms_restrictAlongFunctor F G t' _).trans (haG b)
    rw [e4]
    change -θ' t' - p1 F (G.map b) (-θ' t) - D R _ (y t t' b) =
      a2 t t' b - (θ' t' - p1 F (G.map b) (θ' t)) - a' t t' b
    simp only [a2, map_neg]
    abel
  · change dOne R _ (-θ' t) = qOm (CoefMap.restrict F G) 2 t (η (G.obj t)) - c'.1.2.2 t
    have e5 : qOm (CoefMap.restrict F G) 2 t (η (G.obj t)) = η3 t :=
      (qOm_restrict F G t _).trans (hηG t)
    rw [e5]
    change dOne R _ (-θ' t) = η3 t - η' t
    simp only [η3, map_neg]
    abel

end GlobalTheory.CechDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommaSecondOrderCocycleLiftStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comma_second_order_cocycle_lift : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Surjective (CoefMap.restrict F G).pull2 → (∀ κ : A2 F, (∀ ⦃T T' T'' T''' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''), p1 F χ (κ T T' T'' φ ψ) + κ T T'' T''' (φ ≫ ψ) χ = κ T T' T''' φ (ψ ≫ χ) + κ T' T'' T''' ψ χ) → ∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), κ _ _ _ (G.map a) (G.map b) = p1 F (G.map b) (β' t t' a) - β' t t'' (a ≫ b) + β' t' t'' b) → ∃ β : A1 F, ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T' T'' φ ψ = p1 F ψ (β T T' φ) - β T T'' (φ ≫ ψ) + β T' T'' ψ) → (∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), β' t t'' (a ≫ b) = p1 F (G.map b) (β' t t' a) + β' t' t'' b) → ∃ β : A1 F, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), β T T'' (φ ≫ ψ) = p1 F ψ (β T T' φ) + β T' T'' ψ) ∧ ∃ θ' : ∀ t, Ω[F.obj (G.obj t)⁄R], ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), β _ _ (G.map a) - β' t t' a = θ' t' - p1 F (G.map a) (θ' t)) → (∀ κ : W1 F 2, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = pOm F 2 ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Om R (F.obj (G.obj t)) 2, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - pOm F 2 (G.map a) (θ' t)) → ∃ θ : W0 F 2, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - pOm F 2 φ (θ T)) → (∀ η' : ∀ t, Om R (F.obj (G.obj t)) 2, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), η' t' = pOm F 2 (G.map a) (η' t)) → ∃ η : W0 F 2, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η T' = pOm F 2 φ (η T)) ∧ ∀ t, η (G.obj t) = η' t) → (∀ (T : C) (x : Om R (F.obj T) 3), (∀ t (u : T ⟶ G.obj t), pOm F 3 u x = 0) → x = 0) → Function.Surjective (pullHyp2 (CoefMap.restrict F G)) := by
  first | exact @GlobalTheory.CechDR.pullHyp2_restrict_surjective | exact GlobalTheory.CechDR.pullHyp2_restrict_surjective | (intros; apply GlobalTheory.CechDR.pullHyp2_restrict_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleHigherFormsExtendAlongFunctor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleHigherFormsExtendAlongFunctor
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory

theorem compat_forms_extend : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), ∀ (j : ℕ), (∀ (T : C) (x : (FormExtJ.omjExt F j).obj T), (∀ t (u : T ⟶ G.obj t), mp (FormExtJ.omjExt F j) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (FormExtJ.omjExt F j).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (FormExtJ.omjExt F j) (G.map a) (s t u)) → ∃ x : (FormExtJ.omjExt F j).obj T, ∀ t u, mp (FormExtJ.omjExt F j) u x = s t u) → (∀ η' : ∀ t, Om R (F.obj (G.obj t)) j, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), η' t' = pOm F j (G.map a) (η' t)) → ∃ η : W0 F j, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η T' = pOm F j φ (η T)) ∧ ∀ t, η (G.obj t) = η' t) := by
  intro R _ C _ C' _ F G j hsep hglue η' hη'
  obtain ⟨g, hg, hgG⟩ := compat_family_extend (FormExtJ.omjExt F j) G hsep hglue
    (fun t ↦ (TrivSqZeroExt.inr (η' t) : (FormExtJ.omjExt F j).obj (G.obj t)))
    (fun t t' a ↦ by rw [FormExtJ.mp_omjExt_inr, ← hη' a])
  refine ⟨fun T ↦ (g T).snd, fun T T' φ ↦ ?_, fun t ↦ ?_⟩
  · show (g T').snd = pOm F j φ (g T).snd
    rw [hg φ, FormExtJ.snd_mp_omjExt]
  · show (g (G.obj t)).snd = η' t
    rw [hgG t]
    rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleHigherFormsExtendAlongFunctorStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatible_higherForms_extend_along_functor : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), ∀ (j : ℕ), (∀ (T : C) (x : (FormExtJ.omjExt F j).obj T), (∀ t (u : T ⟶ G.obj t), mp (FormExtJ.omjExt F j) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (FormExtJ.omjExt F j).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (FormExtJ.omjExt F j) (G.map a) (s t u)) → ∃ x : (FormExtJ.omjExt F j).obj T, ∀ t u, mp (FormExtJ.omjExt F j) u x = s t u) → (∀ η' : ∀ t, Om R (F.obj (G.obj t)) j, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), η' t' = pOm F j (G.map a) (η' t)) → ∃ η : W0 F j, (∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η T' = pOm F j φ (η T)) ∧ ∀ t, η (G.obj t) = η' t) := by
  first | exact @GlobalTheory.compat_forms_extend | exact GlobalTheory.compat_forms_extend | (intros; apply GlobalTheory.compat_forms_extend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherFormsOneCocycleCoboundaryOfRestrict
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherFormsOneCocycleCoboundaryOfRestrict
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechDR.FormExtJ

attribute [local instance] opModJ isCentralScalarJ isScalarTowerJ

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (j : ℕ)

abbrev inrJ {T : C} (x : Om R (F.obj T) j) : (omjExt F j).obj T := TrivSqZeroExt.inr x

theorem inrJ_add {T : C} (x y : Om R (F.obj T) j) : inrJ F j (x + y) = inrJ F j x + inrJ F j y :=
  TrivSqZeroExt.inr_add _ x y

theorem inrJ_sub {T : C} (x y : Om R (F.obj T) j) : inrJ F j (x - y) = inrJ F j x - inrJ F j y :=
  TrivSqZeroExt.inr_sub _ x y

theorem snd_subJ {T : C} (a b : (omjExt F j).obj T) :
    TrivSqZeroExt.snd (a - b) = TrivSqZeroExt.snd a - TrivSqZeroExt.snd b :=
  TrivSqZeroExt.snd_sub a b

theorem oneCocycle_coboundary_of_restrict_coboundary {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type}
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (j : ℕ)
    (hinj : Function.Injective (CoefMap.restrict (FormExtJ.omjExt F j) G).pull1)
    (κ : W1 F j) (hκ : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''),
      κ T T'' (φ ≫ ψ) = pOm F j ψ (κ T T' φ) + κ T' T'' ψ)
    (θ' : ∀ t, Om R (F.obj (G.obj t)) j)
    (hθ' : ∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - pOm F j (G.map a) (θ' t)) :
    ∃ θ : W0 F j, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - pOm F j φ (θ T) := by
  let E := omjExt F j
  let f : Z1 E := ⟨fun T T' φ ↦ inrJ F j (κ T T' φ), fun T T' T'' φ ψ ↦ by
    change inrJ F j (κ T T'' (φ ≫ ψ)) = mp E ψ (inrJ F j (κ T T' φ)) + inrJ F j (κ T' T'' ψ)
    rw [mp_omjExt_inr, hκ φ ψ, inrJ_add]⟩
  have hpull : (CoefMap.restrict E G).pull1 (H1.mk E f) = (CoefMap.restrict E G).pull1 0 := by
    rw [map_zero, CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
    refine ⟨fun t ↦ inrJ F j (θ' t), ?_⟩
    funext t t' a
    change inrJ F j (θ' t') - mp E (G.map a) (inrJ F j (θ' t)) = inrJ F j (κ _ _ (G.map a))
    rw [mp_omjExt_inr, hθ' a, inrJ_sub]
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 (hinj hpull)
  refine ⟨fun T ↦ (g T).snd, fun T T' φ ↦ ?_⟩
  have e := congrArg TrivSqZeroExt.snd (congrFun (congrFun (congrFun hg T) T') φ)
  rw [amitsur_d0_apply, snd_subJ, snd_mp_omjExt] at e
  exact e.symm

end GlobalTheory.CechDR.FormExtJ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherFormsOneCocycleCoboundaryOfRestrictStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.higherForms_oneCocycle_coboundary_of_restrict : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), ∀ (j : ℕ), Function.Injective (CoefMap.restrict (FormExtJ.omjExt F j) G).pull1 → (∀ κ : W1 F j, (∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T'' (φ ≫ ψ) = pOm F j ψ (κ T T' φ) + κ T' T'' ψ) → ∀ θ' : ∀ t, Om R (F.obj (G.obj t)) j, (∀ ⦃t t' : C'⦄ (a : t ⟶ t'), κ _ _ (G.map a) = θ' t' - pOm F j (G.map a) (θ' t)) → ∃ θ : W0 F j, ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), κ T T' φ = θ T' - pOm F j φ (θ T)) := by
  first | exact @GlobalTheory.CechDR.FormExtJ.oneCocycle_coboundary_of_restrict_coboundary | exact GlobalTheory.CechDR.FormExtJ.oneCocycle_coboundary_of_restrict_coboundary | (intros; apply GlobalTheory.CechDR.FormExtJ.oneCocycle_coboundary_of_restrict_coboundary <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CechDR

open FormExt FormExtJ

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem pairRes_bijective_two {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') : Function.Bijective (pullHyp2 (pairRes φ s')) := by
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hcov := _root_.GlobalTheory.CechDR.pair_cover_affine φ s'
  have hdir := _root_.GlobalTheory.CechDR.exists_pair_below_two φ s'

  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') (pairFst φ) H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s') (pairFst φ) H hcov hdir
  have hv2 := GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor (OAff s') (pairFst φ) H hcov hdir

  have hs1 := _root_.GlobalTheory.CechDR.form_eq_zero_of_basis_cover s' (pairFst φ) hcov
  have hg1 := _root_.GlobalTheory.CechDR.FormExt.glue_one_forms s' (pairFst φ) hcov hdir
  have unitE : ∀ {S S' : AffOp X'} (u : S ⟶ S') (b : (OAff s').obj S),
      IsUnit (mp (omExt (OAff s')) u (TrivSqZeroExt.inl b)) → IsUnit (mp (OAff s') u b) :=
    fun u b h ↦ ((isUnit_mp_omExt_iff (OAff s') u _).1 h)
  have HE := hasLoc_omExt (OAff s') H
  have hcovE : ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (omExt (OAff s')).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (omExt (OAff s')) u (b i)) →
          ∃ (t : (Pair φ)ᵒᵖ) (v : T ⟶ (pairFst φ).obj t) (w : (pairFst φ).obj t ⟶ S), v ≫ w = u :=
    fun T ↦ by
      obtain ⟨n, b, hb, h⟩ := hcov T
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S u hu ↦ h i S u (unitE u _ hu)⟩
  have hdirE : ∀ (t₁ t₂ : (Pair φ)ᵒᵖ) (S : AffOp X'), ((pairFst φ).obj t₁ ⟶ S) →
      ((pairFst φ).obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (omExt (OAff s')).obj S),
        Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'),
          IsUnit (mp (omExt (OAff s')) u (b i)) →
            ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty ((pairFst φ).obj t₃ ⟶ S') :=
    fun t₁ t₂ S a₁ a₂ ↦ by
      obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S a₁ a₂
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inl_eq_top (OAff s') hb,
        fun i S' u hu ↦ h i S' u (unitE u _ hu)⟩
  have hsE := _root_.GlobalTheory.sep_of_factoring_cover (omExt (OAff s')) (pairFst φ) HE hcovE
  have hgE := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (omExt (OAff s')) (pairFst φ) HE hcovE hdirE
  have hvE := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (omExt (OAff s')) (pairFst φ) HE hcovE hdirE

  have hcovJ : ∀ j : ℕ, ∀ T : AffOp X', ∃ (n : ℕ) (b : Fin n → (omjExt (OAff s') j).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X') (u : T ⟶ S),
        IsUnit (mp (omjExt (OAff s') j) u (b i)) →
          ∃ (t : (Pair φ)ᵒᵖ) (v : T ⟶ (pairFst φ).obj t) (w : (pairFst φ).obj t ⟶ S), v ≫ w = u :=
    fun j T ↦ by
      obtain ⟨n, b, hb, h⟩ := hcov T
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inlJ_eq_top (OAff s') j hb,
        fun i S u hu ↦ h i S u ((isUnit_mp_omjExt_iff (OAff s') j u _).1 hu)⟩
  have hdirJ : ∀ j : ℕ, ∀ (t₁ t₂ : (Pair φ)ᵒᵖ) (S : AffOp X'), ((pairFst φ).obj t₁ ⟶ S) →
      ((pairFst φ).obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (omjExt (OAff s') j).obj S),
        Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : AffOp X') (u : S ⟶ S'),
          IsUnit (mp (omjExt (OAff s') j) u (b i)) →
            ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty ((pairFst φ).obj t₃ ⟶ S') :=
    fun j t₁ t₂ S a₁ a₂ ↦ by
      obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S a₁ a₂
      exact ⟨n, fun i ↦ TrivSqZeroExt.inl (b i), span_inlJ_eq_top (OAff s') j hb,
        fun i S' u hu ↦ h i S' u ((isUnit_mp_omjExt_iff (OAff s') j u _).1 hu)⟩
  have hsJ := fun j ↦ _root_.GlobalTheory.sep_of_factoring_cover (omjExt (OAff s') j) (pairFst φ)
    (GlobalTheory.T.hasLocalisationAtElements_trivSqZeroExtForms (OAff s') j H) (hcovJ j)
  have hgJ := fun j ↦ _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (omjExt (OAff s') j) (pairFst φ)
    (GlobalTheory.T.hasLocalisationAtElements_trivSqZeroExtForms (OAff s') j H) (hcovJ j) (hdirJ j)
  have hs3 : ∀ (T : AffOp X') (x : Om R' ((OAff s').obj T) 3),
      (∀ t (u : T ⟶ (pairFst φ).obj t), pOm (OAff s') 3 u x = 0) → x = 0 := by
    intro T x hx
    have h0 : (TrivSqZeroExt.inr x : (omjExt (OAff s') 3).obj T) = 0 :=
      hsJ 3 T _ fun t u ↦ (mp_omjExt_inr (OAff s') 3 u x).trans (by rw [hx t u]; exact TrivSqZeroExt.inr_zero _)
    simpa using congrArg TrivSqZeroExt.snd h0

  have b1 : Function.Bijective (pairRes φ s').pull1 :=
    ⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
      _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩
  have bg := _root_.GlobalTheory.restrict_glob1_bijective _ _ hs1 hg1
  have hs2 := _root_.GlobalTheory.CechDR.twoForm_sep_of_basis s' (pairFst φ) hcov
  refine ⟨GlobalTheory.T.comma_first_order_cocycle_lift _ _ (GlobalTheory.T.comma_descent_injective _ _ hs hg hv) b1.2
      (_root_.GlobalTheory.cocycle_one_forms_coboundary_of_restrict _ _ hs1 hg1) bg.2 hs2,
    GlobalTheory.T.comma_second_order_cocycle_lift _ _ (GlobalTheory.T.comma_descent_restriction_equiv _ _ hs hg hv hv2)
      (GlobalTheory.T.oneForms_twoCocycle_coboundary_of_restrict _ _ (GlobalTheory.T.comma_descent_injective _ _ hsE hgE hvE))
      (GlobalTheory.T.exists_oneForms_cocycle_restrict_sub_coboundary _ _ (_root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hsE hgE hvE))
      (GlobalTheory.T.higherForms_oneCocycle_coboundary_of_restrict _ _ 2 (_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ (hsJ 2) (hgJ 2)))
      (GlobalTheory.T.compatible_higherForms_extend_along_functor _ _ 2 (hsJ 2) (hgJ 2)) hs3⟩

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}
variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ)

theorem existsUnique_isPull2 (c : HH2 s) : ∃! c', IsPull2 h c c' := by
  obtain ⟨c', hc, hu⟩ := (pairRes_bijective_two φ s').existsUnique (pullHyp2 (pairPull h) c)
  exact ⟨c', hc.symm, fun y hy ↦ hu y hy.symm⟩

def pairResEquiv2 (φ : X' ⟶ X) (s' : X' ⟶ Sp R') : HH2 s' ≃ₗ[R'] Hyp2 (OPair φ s') :=
  LinearEquiv.ofBijective (pullHyp2 (pairRes φ s')) (pairRes_bijective_two φ s')

def pullHH2 : HH2 s →ₛₗ[σ] HH2 s' :=
  (pairResEquiv2 φ s').symm.toLinearMap.comp (pullHyp2 (pairPull h))

theorem isPull2_pullHH2 (c : HH2 s) : IsPull2 h c (pullHH2 h c) :=
  ((pairResEquiv2 φ s').apply_symm_apply _).symm

theorem IsPull2.eq_pullHH2 {c : HH2 s} {c' : HH2 s'} (e : IsPull2 h c c') : c' = pullHH2 h c :=
  (existsUnique_isPull2 h c).unique e (isPull2_pullHH2 h c)

end GlobalTheory.CechDR
