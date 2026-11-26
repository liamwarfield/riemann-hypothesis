module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallDescentH1Surjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictUpwardClosedSubcategoryPull1Bijective
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.Desc


open Classical in
theorem restrict_upwardClosed_subcategory_pull1_bijective : ∀ (R : Type) [CommRing R] (C : Type 1) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (P : ObjectProperty C), (∀ S S', (S ⟶ S') → P S → P S') →
    (∀ T, Desc.Sep F fun S (_ : T ⟶ S) ↦ P S) → (∀ T, Desc.Glue F fun S (_ : T ⟶ S) ↦ P S) →
    (∀ T, Desc.Van1 F fun S (_ : T ⟶ S) ↦ P S) → Function.Bijective (CoefMap.restrict F P.ι).pull1 := by
  intro R _ C _ F P hP sep glue van
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
    obtain ⟨g₀, hg⟩ := hc
    let g : ∀ S, P S → F.obj S := fun S hS ↦ g₀ ⟨S, hS⟩
    have hg' : ∀ (S S' : C) (hS : P S) (hS' : P S') (ψ : S ⟶ S'),
        g S' hS' - mp F ψ (g S hS) = f.1 S S' ψ := fun S S' hS hS' ψ ↦
      congrFun (congrFun (congrFun hg ⟨S, hS⟩) ⟨S', hS'⟩) (ObjectProperty.homMk ψ)
    have h1 : ∀ T : C, ∃ x : F.obj T, ∀ S (u : T ⟶ S) (hS : P S),
        mp F u x = g S hS - f.1 T S u := by
      intro T
      obtain ⟨x, hx⟩ := glue T (fun S u ↦ if hS : P S then g S hS - f.1 T S u else 0)
        fun S S' u ψ hS ↦ by
          have hS' := hP _ _ ψ hS
          simp only [dif_pos hS, dif_pos hS', map_sub]
          have k1 := Z1.comp f u ψ
          have k2 := hg' S S' hS hS' ψ
          linear_combination k2 - k1
      exact ⟨x, fun S u hS ↦ by rw [hx S u hS, dif_pos hS]⟩
    choose x hx using h1
    refine H1.mk_eq_zero.2 ⟨x, ?_⟩
    funext T T' φ
    rw [amitsur_d0_apply]
    refine (sub_eq_zero.1 (sep T' _ fun S u hS ↦ ?_)).symm
    have k1 := Z1.comp f φ u
    have k2 := hx T' S u hS
    have k3 := hx T S (φ ≫ u) hS
    rw [mp_comp] at k3
    simp only [map_sub]
    linear_combination k3 - k2 - k1
  · intro c
    obtain ⟨y, rfl⟩ := H1.mk_surjective _ c
    let z : ∀ S S', (S ⟶ S') → F.obj S' := fun S S' ψ ↦
      if h : P S then y.1 ⟨S, h⟩ ⟨S', hP _ _ ψ h⟩ (ObjectProperty.homMk ψ) else 0
    have hz : ∀ S S' S'' (ψ : S ⟶ S') (χ : S' ⟶ S''), P S →
        z S S'' (ψ ≫ χ) = mp F χ (z S S' ψ) + z S' S'' χ := by
      intro S S' S'' ψ χ hp
      have hp' := hP _ _ ψ hp
      simp only [z, dif_pos hp, dif_pos hp']
      exact y.2 (T := ⟨S, hp⟩) (T' := ⟨S', hp'⟩) (T'' := ⟨S'', hP _ _ χ hp'⟩)
        (ObjectProperty.homMk ψ) (ObjectProperty.homMk χ)
    have hzy : ∀ (S S' : P.FullSubcategory) (ψ : S ⟶ S'), z S.obj S'.obj ψ.hom = y.1 S S' ψ := by
      intro S S' ψ
      simp only [z, dif_pos S.property]
      rfl
    have h1 : ∀ T : C, ∃ b : ∀ S, (T ⟶ S) → F.obj S, (∀ S S' u ψ, P S →
        b S' (u ≫ ψ) - mp F ψ (b S u) = z S S' ψ) ∧ (P T → ∀ S u, b S u = z T S u) := by
      intro T
      by_cases hp : P T
      · exact ⟨fun S u ↦ z T S u, fun S S' u ψ _ ↦ by
          have := hz _ _ _ u ψ hp
          linear_combination this, fun _ _ _ ↦ rfl⟩
      · obtain ⟨b, hb⟩ := van T (fun S S' _ ψ ↦ z S S' ψ) fun S S' S'' u ψ χ h ↦ hz _ _ _ ψ χ h
        exact ⟨b, hb, fun h ↦ absurd h hp⟩
    choose b hb hb' using h1
    have h2 : ∀ T T' (φ : T ⟶ T'), ∃ x : F.obj T', ∀ S (u : T' ⟶ S), P S →
        mp F u x = b T S (φ ≫ u) - b T' S u := by
      intro T T' φ
      refine glue T' _ fun S S' u ψ hp ↦ ?_
      have k1 := hb T _ _ (φ ≫ u) ψ hp
      have k2 := hb T' _ _ u ψ hp
      simp only [map_sub, Category.assoc] at k1 ⊢
      linear_combination k1 - k2
    choose f hf using h2
    refine ⟨H1.mk F ⟨f, fun T T' T'' φ ψ ↦ sub_eq_zero.1 (sep T'' _ fun S u hp ↦ ?_)⟩, ?_⟩
    · have k1 := hf _ _ (φ ≫ ψ) S u hp
      have k2 := hf _ _ φ S (ψ ≫ u) hp
      have k3 := hf _ _ ψ S u hp
      simp only [map_sub, map_add (f := _), mp_comp, Category.assoc] at k1 k2 ⊢
      linear_combination k1 - k2 - k3
    · rw [CoefMap.pullCohomologyOne_class]
      congr 1
      refine Subtype.ext ?_
      funext S S' ψ
      have k1 := hf _ _ ψ.hom _ (𝟙 _) S'.property
      rw [hb' _ S.property, hb' _ S'.property, mp_id, Category.comp_id] at k1
      have k2 := hz _ _ _ (𝟙 S'.obj) (𝟙 S'.obj) S'.property
      rw [Category.id_comp, mp_id] at k2
      rw [← hzy]
      change f _ _ ψ.hom = _
      linear_combination k1 + k2

end GlobalTheory.CatCoh.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePointPairsCommaAcyclicDegreeLeTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePointPairsCommaAcyclicDegreeLeTwo
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CatCoh.Desc

universe v u

section Retract

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
  {T : C} (P : ∀ S, (T ⟶ S) → Prop) (Q : C → Prop) (hQ : ∀ S, (T ⟶ S) → Q S)
  (G : ∀ S, Q S → C) (θ : ∀ S h, S ⟶ G S h)
  (p : ∀ S (u : T ⟶ S), G T (hQ T (𝟙 T)) ⟶ G S (hQ S u))
  (m : ∀ S S' (h : Q S) (h' : Q S'), (S ⟶ S') → (G S h ⟶ G S' h'))
  (hp : ∀ S u, θ T (hQ T (𝟙 T)) ≫ p S u = u ≫ θ S (hQ S u))
  (hθ : ∀ S S' h h' (ψ : S ⟶ S'), θ S h ≫ m S S' h h' ψ = ψ ≫ θ S' h')
  (hpm : ∀ S S' u (ψ : S ⟶ S'), p S u ≫ m S S' _ _ ψ = p S' (u ≫ ψ))
  (hmm : ∀ S S' S'' h h' h'' (ψ : S ⟶ S') (χ : S' ⟶ S''),
    m S S' h h' ψ ≫ m S' S'' h' h'' χ = m S S'' h h'' (ψ ≫ χ))
  (bij : ∀ S h, Function.Bijective (mp F (θ S h)))
  (h0 : P _ (θ T (hQ T (𝟙 T))))


include hQ bij h0 in
theorem sep_of_retract : Sep F P := by
  intro x hx
  refine (bij T (hQ T (𝟙 T))).1 ?_
  rw [hx _ _ h0, map_zero]


include hp bij h0 in
theorem glue_of_retract : Glue F P := by
  intro s hs
  obtain ⟨x, hx⟩ := (bij T (hQ T (𝟙 T))).2 (s _ (θ T (hQ T (𝟙 T))))
  refine ⟨x, fun S u hu ↦ (bij S (hQ S u)).1 ?_⟩
  rw [← mp_comp, ← hp, mp_comp, hx, ← hs _ _ _ _ h0, hp, hs _ _ _ _ hu]


include hp hθ hpm bij h0 in
theorem cocycleOne_vanishing_of_natural_additive_retract : Van1 F P := by
  intro a ha
  have e : ∀ S (h : Q S) y, mp F (θ S h) (Function.surjInv (bij S h).2 y) = y :=
    fun S h y ↦ Function.surjInv_eq (bij S h).2 y
  refine ⟨fun S u ↦ Function.surjInv (bij S (hQ S u)).2
    (a _ _ (θ T (hQ T (𝟙 T))) (p S u) - a _ _ u (θ S (hQ S u))), fun S S' u ψ hu ↦ ?_⟩
  refine (bij S' (hQ S' (u ≫ ψ))).1 ?_
  rw [map_sub, e, ← mp_comp, ← hθ S S' (hQ S u) (hQ S' (u ≫ ψ)) ψ, mp_comp, e]
  have k1 := ha _ _ _ _ (p S u) (m S S' _ (hQ S' (u ≫ ψ)) ψ) h0
  have k2 := ha _ _ _ u ψ (θ S' (hQ S' (u ≫ ψ))) hu
  have k3 := ha _ _ _ u (θ S (hQ S u)) (m S S' _ (hQ S' (u ≫ ψ)) ψ) hu
  rw [hpm, hp] at k1
  rw [hθ] at k3
  simp only [map_sub]
  linear_combination k1 - k3 + k2


include hp hθ hpm hmm bij h0 in
theorem cocycleTwo_vanishing_of_natural_additive_retract : Van2 F P := by
  intro z hz
  have e : ∀ S (h : Q S) y, mp F (θ S h) (Function.surjInv (bij S h).2 y) = y :=
    fun S h y ↦ Function.surjInv_eq (bij S h).2 y
  refine ⟨fun S S' u ψ ↦ Function.surjInv (bij S' (hQ S' (u ≫ ψ))).2
    (z _ _ _ u ψ (θ S' (hQ S' (u ≫ ψ))) - z _ _ _ u (θ S (hQ S u)) (m S S' _ (hQ S' (u ≫ ψ)) ψ) +
      z _ _ _ (θ T (hQ T (𝟙 T))) (p S u) (m S S' _ (hQ S' (u ≫ ψ)) ψ)),
    fun S S' S'' u ψ χ hu ↦ ?_⟩
  refine (bij S'' (hQ S'' (u ≫ ψ ≫ χ))).1 ?_
  rw [map_add (f := _), map_sub, e, e, ← mp_comp,
    ← hθ S' S'' (hQ S' (u ≫ ψ)) (hQ S'' (u ≫ ψ ≫ χ)) χ, mp_comp, e]
  have c1 := hz _ _ _ _ _ (p S u) (m S S' _ (hQ S' (u ≫ ψ)) ψ)
    (m S' S'' _ (hQ S'' (u ≫ ψ ≫ χ)) χ) h0
  have c2 := hz _ _ _ _ u (θ S (hQ S u)) (m S S' _ (hQ S' (u ≫ ψ)) ψ)
    (m S' S'' _ (hQ S'' (u ≫ ψ ≫ χ)) χ) hu
  have c3 := hz _ _ _ _ u ψ (θ S' (hQ S' (u ≫ ψ))) (m S' S'' _ (hQ S'' (u ≫ ψ ≫ χ)) χ) hu
  have c4 := hz _ _ _ _ u ψ χ (θ S'' (hQ S'' (u ≫ ψ ≫ χ))) hu
  rw [hpm, hmm, hp] at c1
  rw [hθ, hmm] at c2
  rw [hθ] at c3
  simp only [map_add (f := _), map_sub]
  linear_combination c3 - c4 - c2 + c1

end Retract

end GlobalTheory.CatCoh.Desc

namespace GlobalTheory.PDForm

open KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR
  GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.SmoothLift GlobalTheory.CatCoh.Desc

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}} {t : X ⟶ Sp R}
  {Y : Scheme.{0}} {i : X ⟶ Y}

theorem le_preimage_of_hom {T S : (IsSm κ t i).FullSubcategory} (u : T ⟶ S) {V : Y.Opens}
    (hV : ⊤ ≤ (T.obj.T.x ≫ i) ⁻¹ᵁ V) : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V := by
  intro z _
  rw [← u.hom.1.pt, Category.assoc, Scheme.Hom.comp_preimage]
  exact hV trivial

def cutPr (hY : ∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (V : Y.affineOpens) (S : (IsSm κ t i).FullSubcategory) (h : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1) :
    (IsSm κ t i).FullSubcategory :=
  ⟨⟨S.obj.T, S.obj.U ⊓ V.1, Or.inl (by
    rcases S.obj.hU with hU | hU
    · exact hY _ _ hU V.2
    · rw [hU, top_inf_eq]; exact V.2), fun z _ ↦ ⟨S.obj.mem trivial, h trivial⟩⟩, ⟨V, h⟩⟩

theorem cutPr_aff (hY : ∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (V : Y.affineOpens) (S : (IsSm κ t i).FullSubcategory) (h : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1) :
    IsAffineOpen (cutPr hY V S h).obj.U := by
  rcases S.obj.hU with hU | hU
  · exact hY _ _ hU V.2
  · change IsAffineOpen (S.obj.U ⊓ V.1)
    rw [hU, top_inf_eq]; exact V.2

def prHom {S S' : (IsSm κ t i).FullSubcategory} (φ : S.obj.T ⟶ S'.obj.T) (h : S'.obj.U ≤ S.obj.U) :
    S ⟶ S' :=
  ObjectProperty.homMk ⟨φ, h⟩

theorem prHom_ext {S S' : (IsSm κ t i).FullSubcategory} {f g : S ⟶ S'} (h : f.hom.1 = g.hom.1) :
    f = g :=
  ObjectProperty.hom_ext _ (Subtype.ext h)

theorem isSm_acyclic (hY : ∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (T : (IsSm κ t i).FullSubcategory) :
    Desc.Sep ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
    Desc.Glue ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
    Desc.Van1 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
    Desc.Van2 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) := by
  obtain ⟨V, hV⟩ := T.property
  have hQ : ∀ S (u : T ⟶ S), ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1 := fun S u ↦ le_preimage_of_hom u hV
  let θ : ∀ (S : (IsSm κ t i).FullSubcategory) (h : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1), S ⟶ cutPr hY V S h := fun S h ↦ prHom (𝟙 S.obj.T) inf_le_left
  let p : ∀ S (u : T ⟶ S), cutPr hY V T (hQ T (𝟙 T)) ⟶ cutPr hY V S (hQ S u) :=
    fun S u ↦ prHom u.hom.1 (inf_le_inf_right _ u.hom.2)
  let m : ∀ (S S' : (IsSm κ t i).FullSubcategory) (h : ⊤ ≤ (S.obj.T.x ≫ i) ⁻¹ᵁ V.1)
      (h' : ⊤ ≤ (S'.obj.T.x ≫ i) ⁻¹ᵁ V.1), (S ⟶ S') → (cutPr hY V S h ⟶ cutPr hY V S' h') :=
    fun S S' h h' ψ ↦ prHom ψ.hom.1 (inf_le_inf_right _ ψ.hom.2)
  have hp : ∀ S u, θ T (hQ T (𝟙 T)) ≫ p S u = u ≫ θ S (hQ S u) :=
    fun S u ↦ prHom_ext ((Category.id_comp _).trans (Category.comp_id _).symm)
  have hθ : ∀ S S' h h' (ψ : S ⟶ S'), θ S h ≫ m S S' h h' ψ = ψ ≫ θ S' h' :=
    fun S S' h h' ψ ↦ prHom_ext ((Category.id_comp _).trans (Category.comp_id _).symm)
  have hpm : ∀ S S' u (ψ : S ⟶ S'), p S u ≫ m S S' _ _ ψ = p S' (u ≫ ψ) :=
    fun S S' u ψ ↦ prHom_ext rfl
  have hmm : ∀ S S' S'' h h' h'' (ψ : S ⟶ S') (χ : S' ⟶ S''),
      m S S' h h' ψ ≫ m S' S'' h' h'' χ = m S S'' h h'' (ψ ≫ χ) :=
    fun S S' S'' h h' h'' ψ χ ↦ prHom_ext rfl
  have bij : ∀ S h, Function.Bijective (mp ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (θ S h)) :=
    fun S h ↦ ⟨fun a b hab ↦ hab, fun y ↦ ⟨y, rfl⟩⟩
  have h0 := cutPr_aff hY V T (hQ T (𝟙 T))
  exact ⟨sep_of_retract _ _ _ hQ _ θ bij h0, glue_of_retract _ _ _ hQ _ θ p hp bij h0,
    cocycleOne_vanishing_of_natural_additive_retract _ _ _ hQ _ θ p m hp hθ hpm bij h0,
    cocycleTwo_vanishing_of_natural_additive_retract _ _ _ hQ _ θ p m hp hθ hpm hmm bij h0⟩

theorem isSm_acyclic_two : (∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I)
    (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y),
    (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) →
    ∀ T : (IsSm κ t i).FullSubcategory,
      Desc.Sep ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
      Desc.Glue ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧
      Desc.Van1 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U)) ∧
    ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R)
      (Y : Scheme.{0}) (i : X ⟶ Y),
    (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) →
    ∀ T : (IsSm κ t i).FullSubcategory,
      Desc.Van2 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) :=
  ⟨fun _ _ _ _ _ _ _ _ hY T ↦ ⟨(isSm_acyclic hY T).1, (isSm_acyclic hY T).2.1, (isSm_acyclic hY T).2.2.1⟩,
    fun _ _ _ _ _ _ _ _ hY T ↦ (isSm_acyclic hY T).2.2.2⟩

end GlobalTheory.PDForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePointPairsCommaAcyclicDegreeLeTwoStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affinePointPairs_comma_acyclic_degree_le_two : (∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y), (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) → ∀ T : (IsSm κ t i).FullSubcategory, Desc.Sep ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧ Desc.Glue ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧ Desc.Van1 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U)) ∧ ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y), (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) → ∀ T : (IsSm κ t i).FullSubcategory, Desc.Van2 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) := by
  first | exact @GlobalTheory.PDForm.isSm_acyclic_two | exact GlobalTheory.PDForm.isSm_acyclic_two | (intros; apply GlobalTheory.PDForm.isSm_acyclic_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCohomologyRestrictAffinePointPairsBij
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCohomologyRestrictAffinePointPairsBij
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.SmallPairs

variable {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) {X : Scheme.{0}} (t : X ⟶ Sp R)
  {Y : Scheme.{0}} (i : X ⟶ Y)

def cov (V : Y.affineOpens) : X.Opens := i ⁻¹ᵁ V.1

theorem iSup_cov : ⨆ V, cov i V = ⊤ := by
  simp only [cov]
  rw [← Scheme.Hom.preimage_iSup, AlgebraicGeometry.iSup_affineOpens_eq_top Y]
  simp

abbrev SC : Type 1 := (IsSmall κ t (cov i)).FullSubcategory

abbrev PC : Type 1 := (IsSm κ t i).FullSubcategory

def fgt : PC κ t i ⥤ SC κ t i where
  obj a := ⟨a.obj.T, by obtain ⟨V, hV⟩ := a.property; exact ⟨V, hV⟩⟩
  map f := ObjectProperty.homMk f.hom.1

def sec : SC κ t i ⥤ PC κ t i where
  obj T := ⟨⟨T.obj, ⊤, Or.inr rfl, by simp⟩, by obtain ⟨V, hV⟩ := T.property; exact ⟨V, hV⟩⟩
  map f := ObjectProperty.homMk ⟨f.hom, le_rfl⟩

abbrev OS : SC κ t i ⥤ CommAlgCat.{0} R := (IsSmall κ t (cov i)).ι ⋙ O κ t

abbrev OP : PC κ t i ⥤ CommAlgCat.{0} R := ((IsSm κ t i).ι ⋙ Pr.fgt κ t i) ⋙ O κ t

def nS : CoefMap (RingHom.id R) (OS κ t i) (OP κ t i) where
  G := fgt κ t i
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def kP : CoefMap (RingHom.id R) (OP κ t i) (OS κ t i) where
  G := sec κ t i
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def θP : fgt κ t i ⋙ sec κ t i ⟶ 𝟭 (PC κ t i) where
  app a := ObjectProperty.homMk ⟨𝟙 a.obj.T, le_top⟩
  naturality a b f :=
    ObjectProperty.hom_ext _ (Subtype.ext ((Category.comp_id f.hom.1).trans (Category.id_comp f.hom.1).symm))

def θS : sec κ t i ⋙ fgt κ t i ⟶ 𝟭 (SC κ t i) where
  app T := ObjectProperty.homMk (𝟙 T.obj)
  naturality _ _ f := ObjectProperty.hom_ext _ ((Category.comp_id f.hom).trans (Category.id_comp f.hom).symm)

theorem kn1 (c : H1 (OP κ t i)) : (nS κ t i).pull1 ((kP κ t i).pull1 c) = c := by
  rw [← CoefMap.pullCohomologyOne_comp, CoefMap.pullCohomologyOne_eq_of_natTrans _ (CoefMap.id _) (θP κ t i)
    (fun T b ↦ mp_id (O κ t) T.obj.T b), CoefMap.pullCohomologyOne_id]

theorem nk1 (c : H1 (OS κ t i)) : (kP κ t i).pull1 ((nS κ t i).pull1 c) = c := by
  rw [← CoefMap.pullCohomologyOne_comp, CoefMap.pullCohomologyOne_eq_of_natTrans _ (CoefMap.id _) (θS κ t i)
    (fun T b ↦ mp_id (O κ t) T.obj b), CoefMap.pullCohomologyOne_id]

theorem kn2 (c : H2 (OP κ t i)) : (nS κ t i).pull2 ((kP κ t i).pull2 c) = c := by
  rw [← CoefMap.pullCohomologyTwo_comp, CoefMap.pullCohomologyTwo_eq_of_natTrans _ (CoefMap.id _) (θP κ t i)
    (fun T b ↦ mp_id (O κ t) T.obj.T b), CoefMap.pullCohomologyTwo_id]

theorem nk2 (c : H2 (OS κ t i)) : (kP κ t i).pull2 ((nS κ t i).pull2 c) = c := by
  rw [← CoefMap.pullCohomologyTwo_comp, CoefMap.pullCohomologyTwo_eq_of_natTrans _ (CoefMap.id _) (θS κ t i)
    (fun T b ↦ mp_id (O κ t) T.obj b), CoefMap.pullCohomologyTwo_id]

theorem fac1 (c : H1 (O κ t)) : (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull1 c =
    (nS κ t i).pull1 ((CoefMap.restrict (O κ t) (IsSmall κ t (cov i)).ι).pull1 c) := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c; rfl

theorem fac2 (c : H2 (O κ t)) : (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull2 c =
    (nS κ t i).pull2 ((CoefMap.restrict (O κ t) (IsSmall κ t (cov i)).ι).pull2 c) := by
  obtain ⟨f, rfl⟩ := H2.mk_surjective _ c; rfl

end GlobalTheory.PDForm.SmallPairs

namespace GlobalTheory.PDForm

open SmallPairs

theorem pull_isSm_bijective (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y) :
    Function.Bijective (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull1 ∧
      Function.Bijective (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull2 := by
  have b1 := SmallDescent.pull1_bijective R I κ X t Y.affineOpens (cov i) (iSup_cov i)
  have b2 := small_descent_H2_bijective R I κ X t Y.affineOpens (cov i) (iSup_cov i)
  have n1 : Function.Bijective (nS κ t i).pull1 :=
    Function.bijective_iff_has_inverse.2 ⟨(kP κ t i).pull1, nk1 κ t i, kn1 κ t i⟩
  have n2 : Function.Bijective (nS κ t i).pull2 :=
    Function.bijective_iff_has_inverse.2 ⟨(kP κ t i).pull2, nk2 κ t i, kn2 κ t i⟩
  refine ⟨?_, ?_⟩
  · have e : ⇑(CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull1 =
        ⇑(nS κ t i).pull1 ∘ ⇑(CoefMap.restrict (O κ t) (IsSmall κ t (cov i)).ι).pull1 := funext (fac1 κ t i)
    rw [e]; exact n1.comp b1
  · have e : ⇑(CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull2 =
        ⇑(nS κ t i).pull2 ∘ ⇑(CoefMap.restrict (O κ t) (IsSmall κ t (cov i)).ι).pull2 := funext (fac2 κ t i)
    rw [e]; exact n2.comp b2

end GlobalTheory.PDForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCohomologyRestrictAffinePointPairsBijStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineCohomology_restrict_affinePointPairs_bijective : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y), Function.Bijective (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull1 ∧ Function.Bijective (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull2 := by
  first | exact @GlobalTheory.PDForm.pull_isSm_bijective | exact GlobalTheory.PDForm.pull_isSm_bijective | (intros; apply GlobalTheory.PDForm.pull_isSm_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraCoefficientsRestrictionBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraCoefficientsRestrictionBijective
open CategoryTheory GlobalTheory.CxCoh GlobalTheory.CatCoh

set_option autoImplicit false

namespace GlobalTheory.CxCoh.AlgDict

universe u

variable {R : Type} [CommRing R] {C : Type u} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem singleComplex_mem_cocyclesOne_iff_algebraFunctor (c : (Cx.single (Coef.ofAlg F)).T1) :
    c ∈ (Cx.single (Coef.ofAlg F)).Z1 ↔ c.1 ∈ Z1 F := by
  change (Cx.single (Coef.ofAlg F)).D1 c = 0 ↔ _
  constructor
  · intro h T T' T'' φ ψ
    have := congrFun (congrFun (congrFun (congrFun (congrFun (congrArg Prod.fst h) T) T') T'') φ) ψ
    change mp F ψ (c.1 T T' φ) - c.1 T T'' (φ ≫ ψ) + c.1 T' T'' ψ = 0 at this
    linear_combination -this
  · intro h
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    funext T T' T'' φ ψ
    change mp F ψ (c.1 T T' φ) - c.1 T T'' (φ ≫ ψ) + c.1 T' T'' ψ = 0
    rw [h φ ψ]; ring

theorem singleComplex_mem_cocyclesTwo_iff_algebraFunctor (c : (Cx.single (Coef.ofAlg F)).T2) :
    c ∈ (Cx.single (Coef.ofAlg F)).Z2 ↔ c.1 ∈ Z2 F :=
  ⟨fun h _ _ _ _ φ ψ χ ↦ h.1 _ _ _ _ φ ψ χ,
    fun h ↦ ⟨fun _ _ _ _ φ ψ χ ↦ h φ ψ χ, fun _ _ _ _ _ ↦ Subsingleton.elim _ _,
      fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ Subsingleton.elim _ _⟩⟩

variable {C' : Type u} [Category.{0} C'] (G : C' ⥤ C)

theorem h1_injective (hi : Function.Injective (CoefMap.restrict F G).pull1) :
    Function.Injective ((Cx.single (Coef.ofAlg F)).resMap G).h1 := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hz : z.1.1 ∈ Z1 F := (singleComplex_mem_cocyclesOne_iff_algebraFunctor F z.1).1 z.2
  change (QuotientAddGroup.mk (((Cx.single (Coef.ofAlg F)).resMap G).z1 z) :
    ((Cx.single (Coef.ofAlg F)).res G).H1) = 0 at hc
  rw [QuotientAddGroup.eq_zero_iff] at hc
  obtain ⟨g, hg⟩ := hc
  have h0 : (CoefMap.restrict F G).pull1 (H1.mk F ⟨z.1.1, hz⟩) = (CoefMap.restrict F G).pull1 0 := by
    rw [map_zero, CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
    exact ⟨g, congrArg Prod.fst hg⟩
  obtain ⟨g', hg'⟩ := H1.mk_eq_zero.1 (hi h0)
  rw [QuotientAddGroup.eq_zero_iff]
  exact ⟨g', Prod.ext hg' (Subsingleton.elim _ _)⟩

theorem h1_surjective (hs : Function.Surjective (CoefMap.restrict F G).pull1) :
    Function.Surjective ((Cx.single (Coef.ofAlg F)).resMap G).h1 := by
  intro c'
  obtain ⟨z', rfl⟩ := QuotientAddGroup.mk_surjective c'
  have hz' : z'.1.1 ∈ Z1 (G ⋙ F) := (singleComplex_mem_cocyclesOne_iff_algebraFunctor (G ⋙ F) z'.1).1 z'.2
  obtain ⟨c, hc⟩ := hs (H1.mk _ ⟨z'.1.1, hz'⟩)
  obtain ⟨f, rfl⟩ := H1.mk_surjective F c
  rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk] at hc
  obtain ⟨g, hg⟩ := hc
  refine ⟨QuotientAddGroup.mk ⟨(f.1, fun _ ↦ 0), (singleComplex_mem_cocyclesOne_iff_algebraFunctor F _).2 f.2⟩, ?_⟩
  change (QuotientAddGroup.mk (((Cx.single (Coef.ofAlg F)).resMap G).z1 _) :
    ((Cx.single (Coef.ofAlg F)).res G).H1) = QuotientAddGroup.mk z'
  rw [QuotientAddGroup.eq]
  refine ⟨-g, Prod.ext ?_ (Subsingleton.elim _ _)⟩
  rw [map_neg]
  funext T T' φ
  have := congrFun (congrFun (congrFun hg T) T') φ
  change -(d0 (G ⋙ F) g T T' φ) = -(f.1 _ _ (G.map φ)) + z'.1.1 T T' φ
  rw [this]
  change -((f.1 _ _ (G.map φ)) - z'.1.1 T T' φ) = _
  abel

theorem h2_injective (hi : Function.Injective (CoefMap.restrict F G).pull2) :
    Function.Injective ((Cx.single (Coef.ofAlg F)).resMap G).h2 := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hz : z.1.1 ∈ Z2 F := (singleComplex_mem_cocyclesTwo_iff_algebraFunctor F z.1).1 z.2
  change (QuotientAddGroup.mk (((Cx.single (Coef.ofAlg F)).resMap G).z2 z) :
    ((Cx.single (Coef.ofAlg F)).res G).H2) = 0 at hc
  rw [QuotientAddGroup.eq_zero_iff] at hc
  obtain ⟨g, hg⟩ := hc
  have h0 : (CoefMap.restrict F G).pull2 (H2.mk F ⟨z.1.1, hz⟩) = (CoefMap.restrict F G).pull2 0 := by
    rw [map_zero, CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero]
    exact ⟨g.1, congrArg Prod.fst hg⟩
  obtain ⟨g', hg'⟩ := H2.mk_eq_zero.1 (hi h0)
  rw [QuotientAddGroup.eq_zero_iff]
  exact ⟨(g', fun _ ↦ 0), Prod.ext hg' (Subsingleton.elim _ _)⟩

theorem h2_surjective (hs : Function.Surjective (CoefMap.restrict F G).pull2) :
    Function.Surjective ((Cx.single (Coef.ofAlg F)).resMap G).h2 := by
  intro c'
  obtain ⟨z', rfl⟩ := QuotientAddGroup.mk_surjective c'
  have hz' : z'.1.1 ∈ Z2 (G ⋙ F) := (singleComplex_mem_cocyclesTwo_iff_algebraFunctor (G ⋙ F) z'.1).1 z'.2
  obtain ⟨c, hc⟩ := hs (H2.mk _ ⟨z'.1.1, hz'⟩)
  obtain ⟨f, rfl⟩ := H2.mk_surjective F c
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hc
  obtain ⟨g, hg⟩ := hc
  refine ⟨QuotientAddGroup.mk ⟨(f.1, fun _ _ _ ↦ 0, fun _ ↦ 0), (singleComplex_mem_cocyclesTwo_iff_algebraFunctor F _).2 f.2⟩, ?_⟩
  change (QuotientAddGroup.mk (((Cx.single (Coef.ofAlg F)).resMap G).z2 _) :
    ((Cx.single (Coef.ofAlg F)).res G).H2) = QuotientAddGroup.mk z'
  rw [QuotientAddGroup.eq]
  refine ⟨(-g, fun _ ↦ 0), Prod.ext ?_ (Subsingleton.elim _ _)⟩
  funext T T' T'' φ ψ
  have := congrFun (congrFun (congrFun (congrFun (congrFun hg T) T') T'') φ) ψ
  change d1 (G ⋙ F) (-g) T T' T'' φ ψ = -(f.1 _ _ _ (G.map φ) (G.map ψ)) + z'.1.1 T T' T'' φ ψ
  rw [map_neg, Pi.neg_apply, Pi.neg_apply, Pi.neg_apply, Pi.neg_apply, Pi.neg_apply, this]
  change -((f.1 _ _ _ (G.map φ) (G.map ψ)) - z'.1.1 T T' T'' φ ψ) = _
  abel

end GlobalTheory.CxCoh.AlgDict

theorem GlobalTheory.CxCoh.single_algebra_restriction_bijective : ∀ (R : Type) [CommRing R] (C C' : Type 1) [Category.{0} C]
    [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C),
    Function.Bijective (CoefMap.restrict F G).pull1 → Function.Bijective (CoefMap.restrict F G).pull2 →
    ((Cx.single (Coef.ofAlg F)).resMap G).PullbackBijectiveDegreesOneTwo :=
  fun _ _ _ _ _ _ F G h1 h2 ↦
    ⟨⟨AlgDict.h1_injective F G h1.1, AlgDict.h1_surjective F G h1.2⟩,
      AlgDict.h2_injective F G h2.1, AlgDict.h2_surjective F G h2.2⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraCoefficientsRestrictionBijectiveStatement
open CategoryTheory GlobalTheory.CxCoh GlobalTheory.CatCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebra_coefficients_restriction_bijective : ∀ (R : Type) [CommRing R] (C C' : Type 1) [Category.{0} C] [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Bijective (CoefMap.restrict F G).pull1 → Function.Bijective (CoefMap.restrict F G).pull2 → ((Cx.single (Coef.ofAlg F)).resMap G).PullbackBijectiveDegreesOneTwo := by
  first | exact @GlobalTheory.CxCoh.single_algebra_restriction_bijective | exact GlobalTheory.CxCoh.single_algebra_restriction_bijective | (intros; apply GlobalTheory.CxCoh.single_algebra_restriction_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCohomologyComputedOnAffinePairs
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDForm.AffPair

section

variable {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) {X : Scheme.{0}} (t : X ⟶ Sp R)
  {Y : Scheme.{0}} (i : X ⟶ Y)

def smAff : ObjectProperty (IsSm κ t i).FullSubcategory := fun S ↦ IsAffineOpen S.obj.U

theorem smAff_up (S S' : (IsSm κ t i).FullSubcategory) (f : S ⟶ S') (h : smAff κ t i S) :
    smAff κ t i S' := by
  rcases S'.obj.hU with h' | h'
  · exact h'
  · have e : S'.obj.U = S.obj.U := le_antisymm f.hom.2 (h' ▸ le_top)
    change IsAffineOpen S'.obj.U
    rw [e]
    exact h

abbrev coefSm : (IsSm κ t i).FullSubcategory ⥤ CommAlgCat.{0} R := (IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t

def toIter : EE κ t i ⥤ (smAff κ t i).FullSubcategory where
  obj a := ⟨⟨a.obj, ⟨⟨a.obj.U, a.property⟩, a.obj.mem⟩⟩, a.property⟩
  map f := ⟨⟨f.hom⟩⟩

def ofIter : (smAff κ t i).FullSubcategory ⥤ EE κ t i where
  obj a := ⟨a.obj.obj, a.property⟩
  map f := ⟨f.hom.hom⟩

def mapTo : CoefMap (RingHom.id R) ((smAff κ t i).ι ⋙ coefSm κ t i) (pE κ t i ⋙ O κ t) where
  G := toIter κ t i
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def mapOf : CoefMap (RingHom.id R) (pE κ t i ⋙ O κ t) ((smAff κ t i).ι ⋙ coefSm κ t i) where
  G := ofIter κ t i
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

theorem mapTo_pull1 : Function.Bijective (mapTo κ t i).pull1 := by
  refine Function.bijective_iff_has_inverse.2 ⟨(mapOf κ t i).pull1, fun c ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := H1.mk_surjective _ c; rfl
  · obtain ⟨a, rfl⟩ := H1.mk_surjective _ c; rfl

theorem mapTo_pull2 : Function.Bijective (mapTo κ t i).pull2 := by
  refine Function.bijective_iff_has_inverse.2 ⟨(mapOf κ t i).pull2, fun c ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := H2.mk_surjective _ c; rfl
  · obtain ⟨a, rfl⟩ := H2.mk_surjective _ c; rfl

end

end GlobalTheory.PDForm.AffPair

namespace GlobalTheory.PDForm


open AffPair in
theorem crystallineCohomology_computed_on_affinePairs : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y),
    (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) →
    ((Cx.single (Coef.ofAlg (O κ t))).resMap (pE κ t i)).PullbackBijectiveDegreesOneTwo := by
  intro R _ I κ X t Y i hY
  have ha := GlobalTheory.T.crystallineCohomology_restrict_affinePointPairs_bijective R I κ X t Y i
  have hc := GlobalTheory.T.affinePointPairs_comma_acyclic_degree_le_two.1 R I κ X t Y i hY
  have hc2 := GlobalTheory.T.affinePointPairs_comma_acyclic_degree_le_two.2 R I κ X t Y i hY
  have h1 : Function.Bijective (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull1 :=
    Desc.restrict_upwardClosed_subcategory_pull1_bijective R _ (coefSm κ t i) (smAff κ t i) (smAff_up κ t i)
      (fun T ↦ (hc T).1) (fun T ↦ (hc T).2.1) fun T ↦ (hc T).2.2
  have h2 : Function.Bijective (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull2 :=
    ⟨Desc.pull_restrict_small_injective (coefSm κ t i) (smAff κ t i) (smAff_up κ t i)
      (fun T ↦ (hc T).1) (fun T ↦ (hc T).2.1) fun T ↦ (hc T).2.2,
    Desc.descent_H2_surjective (coefSm κ t i) (smAff κ t i) (smAff_up κ t i)
      (fun T ↦ (hc T).1) (fun T ↦ (hc T).2.1) (fun T ↦ (hc T).2.2) hc2⟩
  refine GlobalTheory.T.algebra_coefficients_restriction_bijective R _ _ (O κ t) (pE κ t i) ?_ ?_
  · have h := (mapTo_pull1 κ t i).comp (h1.comp ha.1)
    have e : ⇑(CoefMap.restrict (O κ t) (pE κ t i)).pull1 = (mapTo κ t i).pull1 ∘
        (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull1 ∘
        (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull1 := by
      funext c
      obtain ⟨a, rfl⟩ := H1.mk_surjective _ c; rfl
    rw [e]
    exact h
  · have h := (mapTo_pull2 κ t i).comp (h2.comp ha.2)
    have e : ⇑(CoefMap.restrict (O κ t) (pE κ t i)).pull2 = (mapTo κ t i).pull2 ∘
        (CoefMap.restrict (coefSm κ t i) (smAff κ t i).ι).pull2 ∘
        (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull2 := by
      funext c
      obtain ⟨a, rfl⟩ := H2.mk_surjective _ c; rfl
    rw [e]
    exact h

end GlobalTheory.PDForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCohomologyComputedOnAffinePairsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackBijective12_resMap_of_affine_inter : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y), (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) → ((Cx.single (Coef.ofAlg (O κ t))).resMap (pE κ t i)).PullbackBijectiveDegreesOneTwo := by
  first | exact @GlobalTheory.PDForm.crystallineCohomology_computed_on_affinePairs | exact GlobalTheory.PDForm.crystallineCohomology_computed_on_affinePairs | (intros; apply GlobalTheory.PDForm.crystallineCohomology_computed_on_affinePairs <;> assumption)
end
