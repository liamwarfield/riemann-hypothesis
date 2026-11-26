module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointExtend
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovBy
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

def CovBy {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (Φ : C → Prop) (S : C) : Prop :=
  ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧
    ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → Φ S'

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsInvertibleLocusOfBasisFunctor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsInvertibleLocusOfBasisFunctor
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh.Desc

theorem sec_of_basis_unit : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u e) → s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : ∀ S, (T ⟶ S) → F.obj S, Desc.IsSec F (fun S u ↦ IsUnit (mp F u e)) x ∧ ∀ t (u : T ⟶ G.obj t), IsUnit (mp F u e) → x (G.obj t) u = s t u := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T e s hs
  have uniq : ∀ (S : C) (y : F.obj S), (∀ t (w : S ⟶ G.obj t), mp F w y = 0) → y = 0 := by
    intro S y hy
    obtain ⟨n, b, hb, hb'⟩ := hcov S
    refine sep_std (H := H) (hb := hb) y fun S'' u' ⟨i, hi⟩ ↦ ?_
    obtain ⟨t, v, w, rfl⟩ := hb' i S'' u' hi
    rw [mp_comp, hy t v, map_zero]
  have hex : ∀ S (u : T ⟶ S), ∃ y : F.obj S, IsUnit (mp F u e) →
      ∀ t (w : S ⟶ G.obj t), mp F w y = s t (u ≫ w) := by
    intro S u
    by_cases h : IsUnit (mp F u e)
    · obtain ⟨y, hy⟩ := glue_comma_of_basis F G H hcov hdir S (fun t w ↦ s t (u ≫ w))
        fun t t' w a ↦ by
          rw [← Category.assoc]
          exact hs t t' (u ≫ w) a (isUnit_comp w h)
      exact ⟨y, fun _ ↦ hy⟩
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  choose x hx using hex
  refine ⟨x, fun S S' u ψ hu ↦ sub_eq_zero.1 (uniq S' _ fun t w ↦ ?_), fun t u hu ↦ ?_⟩
  · rw [map_sub, hx S' (u ≫ ψ) (isUnit_comp ψ hu) t w, ← mp_comp, hx S u hu t (ψ ≫ w),
      Category.assoc, sub_self]
  · have := hx (G.obj t) u hu t (𝟙 _)
    rwa [mp_id, Category.comp_id] at this

end GlobalTheory.CatCoh.Desc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsInvertibleLocusOfBasisFunctorStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_invertibleLocus_of_basisFunctor : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u e) → s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : ∀ S, (T ⟶ S) → F.obj S, Desc.IsSec F (fun S u ↦ IsUnit (mp F u e)) x ∧ ∀ t (u : T ⟶ G.obj t), IsUnit (mp F u e) → x (G.obj t) u = s t u := by
  first | exact @GlobalTheory.CatCoh.Desc.sec_of_basis_unit | exact GlobalTheory.CatCoh.Desc.sec_of_basis_unit | (intros; apply GlobalTheory.CatCoh.Desc.sec_of_basis_unit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfUpwardFamilyStandardCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfUpwardFamilyStandardCover
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

theorem sep_of_covBy : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (t : C') (Sg : ∀ t', (t ⟶ t') → Prop), (∀ t' t'' (a : t ⟶ t') (b : t' ⟶ t''), Sg t' a → Sg t'' (a ≫ b)) → Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), Sg t' a ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) → Desc.Sep (G ⋙ F) Sg := by
  intro R _ C _ C' _ F G _ _ H _ t Sg _ hcov
  obtain ⟨n, b, hb, hc⟩ := hcov
  intro x hx
  refine Desc.sep_std H hb x fun S u ⟨i, hi⟩ ↦ ?_
  obtain ⟨t', a, ha, ⟨w⟩⟩ := hc i S u hi
  have e : u = G.map a ≫ w := Subsingleton.elim _ _
  have h0 : mp F (G.map a) x = 0 := hx t' a ha
  rw [e, mp_comp, h0, map_zero]

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfUpwardFamilyStandardCoverStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_upwardFamily_standardCover : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (t : C') (Sg : ∀ t', (t ⟶ t') → Prop), (∀ t' t'' (a : t ⟶ t') (b : t' ⟶ t''), Sg t' a → Sg t'' (a ≫ b)) → Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), Sg t' a ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) → Desc.Sep (G ⋙ F) Sg := by
  first | exact @GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.sep_of_covBy | exact GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.sep_of_covBy | (intros; apply GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.sep_of_covBy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleUpwardFamilyIsCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleUpwardFamilyIsCoboundary
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CatCoh.Desc.Basis

theorem oneCocycle_upwardFamily_isCoboundary : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (t : C') (Sg : ∀ t', (t ⟶ t') → Prop), (∀ t' t'' (a : t ⟶ t') (b : t' ⟶ t''), Sg t' a → Sg t'' (a ≫ b)) → Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), Sg t' a ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) → Desc.Van1 (G ⋙ F) Sg := by
  intro R _ C _ C' _ F G _ _ H hdir t₀ Sg hSg hcovT
  classical
  intro y hy

  let Q : C' → Prop := fun t ↦ ∃ a : t₀ ⟶ t, Sg t a
  have hQ : ∀ t t', Q t → (t ⟶ t') → Q t' := fun t t' ⟨a, ha⟩ b ↦ ⟨a ≫ b, hSg t t' a b ha⟩

  let yb : ∀ t t' : C', F.obj (G.obj t') := fun t t' ↦
    if h : Q t ∧ Nonempty (t ⟶ t') then y t t' h.1.choose h.2.some else 0
  have hyb : ∀ t t' (u : t₀ ⟶ t) (a : t ⟶ t'), Sg t u → y t t' u a = yb t t' := by
    intro t t' u a hu
    have h : Q t ∧ Nonempty (t ⟶ t') := ⟨⟨u, hu⟩, ⟨a⟩⟩
    simp only [yb, dif_pos h]
    exact congrArg₂ (y t t') (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  have hyc : ∀ t t' t'', Q t → ∀ (a : t ⟶ t') (b : t' ⟶ t''),
      yb t t'' = mp F (G.map b) (yb t t') + yb t' t'' := by
    rintro t t' t'' ⟨u, hu⟩ a b
    rw [← hyb t t'' u (a ≫ b) hu, ← hyb t t' u a hu, ← hyb t' t'' (u ≫ a) b (hSg t t' u a hu)]
    exact hy t t' t'' u a b hu

  obtain ⟨n, b, hb, hcT⟩ := hcovT
  have hpt : ∀ i : Fin n, ∃ p : C', Q p ∧ ∀ S (u : G.obj t₀ ⟶ S),
      IsUnit (mp F u (b i)) → Nonempty (G.obj p ⟶ S) := by
    intro i
    obtain ⟨T', l, hl, -, -, huniv⟩ := H (G.obj t₀) (b i)
    obtain ⟨p, a, ha, ⟨w⟩⟩ := hcT i T' l hl
    exact ⟨p, ⟨a, ha⟩, fun S u hu ↦ by obtain ⟨m, -⟩ := huniv S u hu; exact ⟨w ≫ m⟩⟩
  choose p hpQ hp using hpt

  have hc0 : ∀ i j : Fin n, ∃ x : ∀ S, F.obj S, (∀ S, Nonempty (G.obj (p i) ⟶ S) →
      Nonempty (G.obj (p j) ⟶ S) → ∀ t S' (ψ : S ⟶ S') (w : G.obj t ⟶ S'), Nonempty (p i ⟶ t) →
        Nonempty (p j ⟶ t) → mp F ψ (x S) = mp F w (yb (p j) t - yb (p i) t)) ∧
      (∀ S S' (ψ : S ⟶ S'), Nonempty (G.obj (p i) ⟶ S) → Nonempty (G.obj (p j) ⟶ S) →
        x S' = mp F ψ (x S)) := by
    intro i j
    refine exists_glue_points F G H hdir (p i) (p j) _ fun t t' a ⟨ai⟩ ⟨aj⟩ ↦ ?_
    rw [map_sub, hyc (p j) t t' (hpQ j) aj a, hyc (p i) t t' (hpQ i) ai a]
    ring
  choose c hc hc' using hc0
  have hs : ∀ i j, IsSec F (fun S u ↦ IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j)))
      (fun S (_ : G.obj t₀ ⟶ S) ↦ c i j S) := fun i j S S' u ψ h ↦
    hc' i j S S' ψ (hp i S u h.1) (hp j S u h.2)
  have hcc : ∀ i j k S (u : G.obj t₀ ⟶ S), IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) →
      IsUnit (mp F u (b k)) → c j k S - c i k S + c i j S = 0 := by
    intro i j k S u hi hj hk
    refine eq_zero_of_local₃ F G H hdir (hp i S u hi) (hp j S u hj) (hp k S u hk) _
      fun t S' ψ ai aj ak ⟨w⟩ ↦ ?_
    rw [map_add (f := _), map_sub, hc j k S (hp j S u hj) (hp k S u hk) t S' ψ w aj ak,
      hc i k S (hp i S u hi) (hp k S u hk) t S' ψ w ai ak,
      hc i j S (hp i S u hi) (hp j S u hj) t S' ψ w ai aj]
    simp only [map_sub]
    ring
  obtain ⟨e, he, he'⟩ := Desc.cech1 H hb (fun i j S (_ : G.obj t₀ ⟶ S) ↦ c i j S) hs hcc
  have he'' : ∀ i j S (u : G.obj t₀ ⟶ S), IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) →
      c i j S = e j S u - e i S u := he'

  have hX0 : ∀ i (t : C') (_ : Q t), ∃ x : ∀ S, F.obj S, (∀ S, Nonempty (G.obj t ⟶ S) →
      Nonempty (G.obj (p i) ⟶ S) → ∀ t' S' (ψ : S ⟶ S') (w : G.obj t' ⟶ S'), Nonempty (t ⟶ t') →
        Nonempty (p i ⟶ t') → mp F ψ (x S) = mp F w (yb (p i) t' - yb t t')) ∧
      (∀ S S' (ψ : S ⟶ S'), Nonempty (G.obj t ⟶ S) → Nonempty (G.obj (p i) ⟶ S) →
        x S' = mp F ψ (x S)) := by
    intro i t ht
    refine exists_glue_points F G H hdir t (p i) _ fun t' t'' a ⟨a0⟩ ⟨ai⟩ ↦ ?_
    rw [map_sub, hyc (p i) t' t'' (hpQ i) ai a, hyc t t' t'' ht a0 a]
    ring
  choose X hX hX' using hX0

  have indep : ∀ t (ht : Q t) (u : G.obj t₀ ⟶ G.obj t) S (ψ : G.obj t ⟶ S) i j,
      IsUnit (mp F (u ≫ ψ) (b i)) → IsUnit (mp F (u ≫ ψ) (b j)) →
      X i t ht S - e i S (u ≫ ψ) = X j t ht S - e j S (u ≫ ψ) := by
    intro t ht u S ψ i j hi hj
    have key : X i t ht S - X j t ht S + c i j S = 0 :=
      eq_zero_of_local₃ F G H hdir ⟨ψ⟩ (hp i S _ hi) (hp j S _ hj) _ fun t' S' χ a0 ai aj ⟨w⟩ ↦ by
        rw [map_add (f := _), map_sub, hX i t ht S ⟨ψ⟩ (hp i S _ hi) t' S' χ w a0 ai,
          hX j t ht S ⟨ψ⟩ (hp j S _ hj) t' S' χ w a0 aj,
          hc i j S (hp i S _ hi) (hp j S _ hj) t' S' χ w ai aj]
        simp only [map_sub]
        ring
    linear_combination key - he'' i j S (u ≫ ψ) hi hj

  have hg0 : ∀ t (ht : Q t) (u : G.obj t₀ ⟶ G.obj t), ∃ x : F.obj (G.obj t), ∀ S (ψ : G.obj t ⟶ S) i,
      IsUnit (mp F (u ≫ ψ) (b i)) → mp F ψ x = X i t ht S - e i S (u ≫ ψ) := by
    intro t ht u
    let σ : ∀ S, (G.obj t ⟶ S) → F.obj S := fun S ψ ↦
      if h : ∃ i, IsUnit (mp F (u ≫ ψ) (b i)) then X h.choose t ht S - e h.choose S (u ≫ ψ) else 0
    have hσ : ∀ S ψ i, IsUnit (mp F (u ≫ ψ) (b i)) → σ S ψ = X i t ht S - e i S (u ≫ ψ) := by
      intro S ψ i hi
      have h : ∃ i, IsUnit (mp F (u ≫ ψ) (b i)) := ⟨i, hi⟩
      simp only [σ, dif_pos h]
      exact indep t ht u S ψ _ i h.choose_spec hi
    obtain ⟨x, hx⟩ := glue_std H (span_map_eq_top F u hb) σ fun S S' ψ χ ⟨i, hi⟩ ↦ by
      have hi' : IsUnit (mp F (u ≫ ψ) (b i)) := by rw [mp_comp]; exact hi
      have hi'' : IsUnit (mp F (u ≫ ψ ≫ χ) (b i)) := by
        rw [← Category.assoc, mp_comp]; exact hi'.map _
      rw [hσ S' (ψ ≫ χ) i hi'', hσ S ψ i hi', map_sub, ← hX' i t ht S S' χ ⟨ψ⟩ (hp i S _ hi'),
        ← he i S S' (u ≫ ψ) χ hi', Category.assoc]
    exact ⟨x, fun S ψ i hi ↦ by
      rw [hx S ψ ⟨i, by rw [mp_comp] at hi; exact hi⟩, hσ S ψ i hi]⟩
  choose g hg using hg0
  refine ⟨fun t' a ↦ if h : Sg t' a then g t' ⟨a, h⟩ (G.map a) else 0, fun t t' u a hu ↦ ?_⟩
  have hu' : Sg t' (u ≫ a) := hSg t t' u a hu
  have ht : Q t := ⟨u, hu⟩
  have ht' : Q t' := ⟨u ≫ a, hu'⟩
  dsimp only
  rw [dif_pos hu', dif_pos hu, G.map_comp]
  change g t' ht' (G.map u ≫ G.map a) - mp F (G.map a) (g t ht (G.map u)) = y t t' u a
  rw [hyb t t' u a hu]
  refine sub_eq_zero.1 (sep_std H (span_map_eq_top F (G.map u ≫ G.map a) hb) _ fun S χ ⟨i, hi⟩ ↦ ?_)
  have hi' : IsUnit (mp F ((G.map u ≫ G.map a) ≫ χ) (b i)) := by rw [mp_comp]; exact hi
  have hi'' : IsUnit (mp F (G.map u ≫ G.map a ≫ χ) (b i)) := by rw [← Category.assoc]; exact hi'
  rw [map_sub, map_sub, hg t' ht' (G.map u ≫ G.map a) S χ i hi', ← mp_comp,
    hg t ht (G.map u) S (G.map a ≫ χ) i hi'', Category.assoc]
  have key : X i t' ht' S - X i t ht S - mp F χ (yb t t') = 0 :=
    eq_zero_of_local F G H hdir ⟨χ⟩ (hp i S _ hi') _ fun t'' S' ψ ⟨a'⟩ ai ⟨w⟩ ↦ by
      rw [map_sub, map_sub, hX i t' ht' S ⟨χ⟩ (hp i S _ hi') t'' S' ψ w ⟨a'⟩ ai,
        hX i t ht S ⟨G.map a ≫ χ⟩ (hp i S _ hi') t'' S' ψ w ⟨a ≫ a'⟩ ai, ← mp_comp,
        (Subsingleton.elim _ _ : χ ≫ ψ = G.map a' ≫ w), mp_comp, hyc t t' t'' ht a a']
      simp only [map_sub, map_add (f := _)]
      ring
  linear_combination key

end GlobalTheory.CatCoh.Desc.Basis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleUpwardFamilyIsCoboundaryStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.van1_of_covBy_upward_sieve : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (t : C') (Sg : ∀ t', (t ⟶ t') → Prop), (∀ t' t'' (a : t ⟶ t') (b : t' ⟶ t''), Sg t' a → Sg t'' (a ≫ b)) → Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), Sg t' a ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) → Desc.Van1 (G ⋙ F) Sg := by
  first | exact @GlobalTheory.CatCoh.Desc.Basis.oneCocycle_upwardFamily_isCoboundary | exact GlobalTheory.CatCoh.Desc.Basis.oneCocycle_upwardFamily_isCoboundary | (intros; apply GlobalTheory.CatCoh.Desc.Basis.oneCocycle_upwardFamily_isCoboundary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedSectionUpwardFamilyStandardCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedSectionUpwardFamilyStandardCover
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

theorem glue_upward_of_cov : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (t : C') (Sg : ∀ t', (t ⟶ t') → Prop), (∀ t' t'' (a : t ⟶ t') (b : t' ⟶ t''), Sg t' a → Sg t'' (a ≫ b)) → Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), Sg t' a ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) → Desc.Glue (G ⋙ F) Sg := by
  intro R _ C _ C' _ F G _ _ H hdir t Sg hup hcov s hs
  have key : ∀ (t₁ t₂ : C') (a₁ : t ⟶ t₁) (a₂ : t ⟶ t₂), Sg t₁ a₁ → Sg t₂ a₂ → ∀ (S : C)
      (w₁ : G.obj t₁ ⟶ S) (w₂ : G.obj t₂ ⟶ S), mp F w₁ (s t₁ a₁) = mp F w₂ (s t₂ a₂) := by
    intro t₁ t₂ a₁ a₂ h₁ h₂ S w₁ w₂
    refine sub_eq_zero.1 (Basis.eq_zero_of_local F G H hdir ⟨w₁⟩ ⟨w₂⟩ _
      fun t₃ S' ψ ⟨b₁⟩ ⟨b₂⟩ ⟨g⟩ ↦ ?_)
    have e1 : mp F ψ (mp F w₁ (s t₁ a₁)) = mp F g (s t₃ (a₁ ≫ b₁)) := by
      rw [hs t₁ t₃ a₁ b₁ h₁, ← mp_comp]
      change _ = mp F g (mp F (G.map b₁) _)
      rw [← mp_comp F (G.map b₁) g, Subsingleton.elim (G.map b₁ ≫ g) (w₁ ≫ ψ)]
    have e2 : mp F ψ (mp F w₂ (s t₂ a₂)) = mp F g (s t₃ (a₂ ≫ b₂)) := by
      rw [hs t₂ t₃ a₂ b₂ h₂, ← mp_comp]
      change _ = mp F g (mp F (G.map b₂) _)
      rw [← mp_comp F (G.map b₂) g, Subsingleton.elim (G.map b₂ ≫ g) (w₂ ≫ ψ)]
    have e3 : a₁ ≫ b₁ = a₂ ≫ b₂ := Subsingleton.elim _ _
    rw [map_sub, e1, e2, e3, sub_self]
  obtain ⟨n, b, hb, hb'⟩ := hcov
  have hex : ∀ S (u : G.obj t ⟶ S), ∃ y : F.obj S, (∃ i, IsUnit (mp F u (b i))) →
      ∃ (t' : C') (a : t ⟶ t') (w : G.obj t' ⟶ S), Sg t' a ∧ mp F w (s t' a) = y := by
    intro S u
    by_cases h : ∃ i, IsUnit (mp F u (b i))
    · obtain ⟨i, hi⟩ := h
      obtain ⟨t', a, ha, ⟨w⟩⟩ := hb' i S u hi
      exact ⟨mp F w (s t' a), fun _ ↦ ⟨t', a, w, ha, rfl⟩⟩
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  choose σ hσ using hex
  obtain ⟨x, hx⟩ := glue_std (H := H) (hb := hb) σ fun S S' u ψ hp ↦ by
    obtain ⟨t₁, a₁, w₁, h₁, e₁⟩ := hσ S u hp
    obtain ⟨i, hi⟩ := hp
    have hi' : IsUnit (mp F (u ≫ ψ) (b i)) := by rw [mp_comp]; exact hi.map _
    obtain ⟨t₂, a₂, w₂, h₂, e₂⟩ := hσ S' (u ≫ ψ) ⟨i, hi'⟩
    rw [← e₁, ← e₂, ← mp_comp]
    exact key _ _ _ _ h₂ h₁ _ _ _
  refine ⟨x, fun t' a ha ↦ ?_⟩
  change mp F (G.map a) x = s t' a
  refine sub_eq_zero.1 (sep_std H (Basis.span_map_eq_top F (G.map a) hb) _ fun S' ψ ⟨i, hi⟩ ↦ ?_)
  have hi' : IsUnit (mp F (G.map a ≫ ψ) (b i)) := by rw [mp_comp]; exact hi
  obtain ⟨t₂, a₂, w₂, h₂, e₂⟩ := hσ S' (G.map a ≫ ψ) ⟨i, hi'⟩
  rw [map_sub, ← mp_comp, hx _ _ ⟨i, hi'⟩, ← e₂, key t₂ t' a₂ a h₂ ha S' w₂ ψ, sub_self]

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedSectionUpwardFamilyStandardCoverStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glued_section_upwardFamily_standardCover : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (t : C') (Sg : ∀ t', (t ⟶ t') → Prop), (∀ t' t'' (a : t ⟶ t') (b : t' ⟶ t''), Sg t' a → Sg t'' (a ≫ b)) → Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), Sg t' a ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) → Desc.Glue (G ⋙ F) Sg := by
  first | exact @GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.glue_upward_of_cov | exact GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.glue_upward_of_cov | (intros; apply GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.glue_upward_of_cov <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleInvertibleLocusIsCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleInvertibleLocusIsCoboundary
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.Desc.Basis

theorem oneCocycle_invertibleLocus_isCoboundary : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u e) → g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T e y hy
  obtain ⟨L, l, hl, -, -, huniv⟩ := H T e
  have hunit : ∀ t (w : L ⟶ G.obj t), IsUnit (mp F (l ≫ w) e) := by
    intro t w
    rw [mp_comp]
    exact hl.map _
  obtain ⟨gL, hgL⟩ := oneCocycle_coboundary_comma_localBasis F G H hcov hdir L (fun t t' w a ↦ y t t' (l ≫ w) a)
    (fun t t' t'' w a b ↦ by
      have h := hy t t' t'' (l ≫ w) a b (hunit t w)
      rw [Category.assoc] at h
      exact h)
  classical
  refine ⟨fun t u ↦ if h : ∃ w : L ⟶ G.obj t, l ≫ w = u then gL t h.choose else 0, ?_⟩
  have hg : ∀ t (u : T ⟶ G.obj t) (w : L ⟶ G.obj t), l ≫ w = u →
      (if h : ∃ w : L ⟶ G.obj t, l ≫ w = u then gL t h.choose else 0) = gL t w := by
    intro t u w hw
    have h : ∃ w : L ⟶ G.obj t, l ≫ w = u := ⟨w, hw⟩
    rw [dite_eq_left h]
    exact congrArg (gL t) (Subsingleton.elim _ _)
  intro t t' u a hu
  obtain ⟨w, hw, -⟩ := huniv (G.obj t) u hu
  have hw' : l ≫ (w ≫ G.map a) = u ≫ G.map a := by rw [← Category.assoc, hw]
  simp only []
  rw [hg t u w hw, hg t' (u ≫ G.map a) (w ≫ G.map a) hw', hgL t t' w a, hw]

end GlobalTheory.CatCoh.Desc.Basis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleInvertibleLocusIsCoboundaryStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneCocycle_invertibleLocus_isCoboundary_alt : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u e) → g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a := by
  first | exact @GlobalTheory.CatCoh.Desc.Basis.oneCocycle_invertibleLocus_isCoboundary | exact GlobalTheory.CatCoh.Desc.Basis.oneCocycle_invertibleLocus_isCoboundary | (intros; apply GlobalTheory.CatCoh.Desc.Basis.oneCocycle_invertibleLocus_isCoboundary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCoboundaryOnUnitLocusPiece
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCoboundaryOnUnitLocusPiece
open CategoryTheory GlobalTheory.CatCoh

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis


open Classical in
theorem coboundary_on_piece : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (p : C') (v : T ⟶ G.obj p), (∀ (S : C) (u : T ⟶ S), IsUnit (mp F u e) → Nonempty (G.obj p ⟶ S)) → ∀ (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp F (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b := by
  intro R _ C _ C' _ F G _ _ H hdir T e p v he z hz
  have cov : ∀ (t : C') (u : T ⟶ G.obj t), IsUnit (mp F u e) →
      CovBy F (fun S ↦ ∃ (t' : C') (_ : t ⟶ t'), Nonempty (p ⟶ t') ∧ Nonempty (G.obj t' ⟶ S))
        (G.obj t) := by
    intro t u hu
    obtain ⟨w⟩ := he _ u hu
    obtain ⟨n, b, hb, h⟩ := hdir t p (G.obj t) (𝟙 _) w
    refine ⟨n, b, hb, fun i S' u' hi ↦ ?_⟩
    obtain ⟨t₃, ⟨a⟩, h2, h3⟩ := h i S' u' hi
    exact ⟨t₃, a, h2, h3⟩
  have up : ∀ (t t' t'' : C') (_ : t ⟶ t') (_ : t' ⟶ t''), Nonempty (p ⟶ t') → Nonempty (p ⟶ t'') :=
    fun _ _ _ _ b ⟨α⟩ ↦ ⟨α ≫ b⟩
  exact coboundary_of_restrict (G ⋙ F) (E := fun t ↦ T ⟶ G.obj t) (fun u a ↦ u ≫ G.map a)
    (fun _ _ _ ↦ Subsingleton.elim _ _) (fun t u ↦ IsUnit (mp F u e))
    (fun t _ ↦ Nonempty (p ⟶ t)) (fun _ _ _ a h ↦ isUnit_comp (G.map a) h)
    (fun t u hu ↦ sep_of_covBy F G H hdir t (fun t' _ ↦ Nonempty (p ⟶ t')) (up t) (cov t u hu))
    (fun t u hu ↦ GlobalTheory.T.exists_glued_section_upwardFamily_standardCover F G H hdir t (fun t' _ ↦ Nonempty (p ⟶ t')) (up t) (cov t u hu))
    (fun t u hu ↦ GlobalTheory.T.van1_of_covBy_upward_sieve F G H hdir t (fun t' _ ↦ Nonempty (p ⟶ t')) (up t) (cov t u hu))
    z (fun t t' t'' t''' u a b c _ ↦ hz t t' t'' t''' u a b c)
    (fun t t' _ a ↦ if h : Nonempty (p ⟶ t) then z p t t' v h.some a else 0)
    (fun t t' t'' u a b hp ↦ by
      have hp' := up t t t' (𝟙 t) a hp
      simp only [dif_pos hp, dif_pos hp']
      have k := hz p t t' t'' v hp.some a b
      rw [Subsingleton.elim (v ≫ G.map hp.some) u,
        Subsingleton.elim (hp.some ≫ a) hp'.some] at k
      change mp F (G.map b) (z p t t' v hp.some a) - z p t t'' v hp.some (a ≫ b) +
        z p t' t'' v hp'.some b = z t t' t'' u a b
      linear_combination k)

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCoboundaryOnUnitLocusPieceStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoCocycle_coboundary_on_unitLocus_piece : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (p : C') (v : T ⟶ G.obj p), (∀ (S : C) (u : T ⟶ S), IsUnit (mp F u e) → Nonempty (G.obj p ⟶ S)) → ∀ (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp F (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b := by
  first | exact @GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.coboundary_on_piece | exact GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.coboundary_on_piece | (intros; apply GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.coboundary_on_piece <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisObjectsUnitLociCoverAboveStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisObjectsUnitLociCoverAbove
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry KaehlerDifferential in
private lemma covBy_of_covBy_localizations {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (P : C → Prop) (hLoc : _root_.GlobalTheory.CatCoh.Desc.HasLoc F) (T : C)
    {n : ℕ} (c : Fin n → F.obj T) (hc : Ideal.span (Set.range c) = ⊤)
    (h : ∀ (j : Fin n) (L : C) (l : T ⟶ L), IsUnit (_root_.GlobalTheory.CatCoh.mp F l (c j)) →
      (∀ (S : C) (w : T ⟶ S), IsUnit (_root_.GlobalTheory.CatCoh.mp F w (c j)) → ∃! v, l ≫ v = w) →
      _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy F P L) :
    _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy F P T := by
  have hL := fun j => hLoc T (c j)
  choose L l hlu hsurj hker huniv using hL
  have hcov := fun j => h j (L j) (l j) (hlu j) (huniv j)
  unfold _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy at hcov
  choose m e he hP using hcov
  choose N x hx using fun j k => hsurj j (e j k)
  let b' : (Σ j : Fin n, Fin (m j)) → F.obj T := fun p => x p.1 p.2 * c p.1
  have hspan' : Ideal.span (Set.range b') = ⊤ := by
    rw [← Ideal.radical_eq_top, eq_top_iff, ← hc, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    have h1 : (1 : F.obj (L j)) ∈ Ideal.span (Set.range (e j)) := by
      rw [he j]; exact Submodule.mem_top
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    choose N' s hs using fun k => hsurj j (r k)
    have hq : ∀ k, ∃ q, (∑ k', (N' k' + N j k')) = N' k + N j k + q := fun k =>
      Nat.exists_eq_add_of_le (Finset.single_le_sum (f := fun k' => N' k' + N j k')
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
    choose q hq using hq
    have hterm : ∀ k, _root_.GlobalTheory.CatCoh.mp F (l j) (s k * x j k * c j ^ q k) =
        (r k • e j k) * _root_.GlobalTheory.CatCoh.mp F (l j) (c j) ^ (∑ k', (N' k' + N j k')) := by
      intro k
      rw [map_mul, map_mul, map_pow, ← hs k, ← hx j k, hq k, pow_add, pow_add, smul_eq_mul]
      ring
    have hz : _root_.GlobalTheory.CatCoh.mp F (l j)
        (c j ^ (∑ k', (N' k' + N j k')) - ∑ k, s k * x j k * c j ^ q k) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_mul, hr,
        one_mul, map_pow, sub_self]
    obtain ⟨M, hM⟩ := hker j _ hz
    refine ⟨M + (∑ k', (N' k' + N j k')) + 1, ?_⟩
    have h2 : c j ^ M * c j ^ (∑ k', (N' k' + N j k')) =
        c j ^ M * ∑ k, s k * x j k * c j ^ q k := by
      rw [← sub_eq_zero, ← mul_sub]; exact hM
    have h3 : c j ^ (M + (∑ k', (N' k' + N j k')) + 1) =
        ∑ k, (c j ^ M * s k * c j ^ q k) * b' ⟨j, k⟩ := by
      rw [pow_succ, pow_add, h2, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [b']
      ring
    rw [h3]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨⟨j, k⟩, rfl⟩)
  unfold _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy
  let eqv := Fintype.equivFin (Σ j : Fin n, Fin (m j))
  refine ⟨Fintype.card (Σ j : Fin n, Fin (m j)), b' ∘ eqv.symm, ?_, ?_⟩
  · rw [Set.range_comp, eqv.symm.range_eq_univ, Set.image_univ]
    exact hspan'
  · intro i S w hw
    change IsUnit (_root_.GlobalTheory.CatCoh.mp F w
      (x (eqv.symm i).1 (eqv.symm i).2 * c (eqv.symm i).1)) at hw
    generalize eqv.symm i = p at hw
    obtain ⟨j, k⟩ := p
    rw [map_mul, IsUnit.mul_iff] at hw
    obtain ⟨hxw, hcw⟩ := hw
    obtain ⟨v, hv, -⟩ := huniv j S w hcw
    apply hP j k S v
    have hfac : _root_.GlobalTheory.CatCoh.mp F w (x j k) = _root_.GlobalTheory.CatCoh.mp F v (e j k) *
        (_root_.GlobalTheory.CatCoh.mp F v (_root_.GlobalTheory.CatCoh.mp F (l j) (c j))) ^ (N j k) := by
      rw [← hv, _root_.GlobalTheory.CatCoh.mp_comp, ← hx j k, map_mul, map_pow]
    rw [hfac, IsUnit.mul_iff] at hxw
    exact hxw.1


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry KaehlerDifferential in
theorem _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.covBy_unit_above : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → _root_.GlobalTheory.CatCoh.Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (_root_.GlobalTheory.CatCoh.mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (_root_.GlobalTheory.CatCoh.mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (n : ℕ) (d : Fin n → F.obj T), Ideal.span (Set.range d) = ⊤ → ∀ (t : C') (u : T ⟶ G.obj t), _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), (∃ i, IsUnit (_root_.GlobalTheory.CatCoh.mp F (u ≫ G.map a) (d i))) ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) := by
  intro R _ C _ C' _ F G _ _ hLoc hbasis hB T n d hd t u
  apply covBy_of_covBy_localizations F _ hLoc (G.obj t)
    (fun j => _root_.GlobalTheory.CatCoh.mp F u (d j)) (_root_.GlobalTheory.CatCoh.Desc.Basis.span_map_eq_top F u hd)
  intro j L l hl _
  obtain ⟨m, e, he, hfac⟩ := hbasis L
  apply covBy_of_covBy_localizations F _ hLoc L e he
  intro k L' l' hl' _
  obtain ⟨t'', v₁, v₂, -⟩ := hfac k L' l' hl'
  obtain ⟨p, f, hf, hP⟩ := hB t t'' L' (l ≫ l') v₂
  unfold _root_.GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.CovBy
  refine ⟨p, f, hf, ?_⟩
  intro i S'' z hz
  obtain ⟨t₃, ⟨c₁⟩, ⟨c₂⟩, ⟨w⟩⟩ := hP i S'' z hz
  refine ⟨t₃, c₁, ⟨j, ?_⟩, ⟨w⟩⟩
  have hunit : IsUnit (_root_.GlobalTheory.CatCoh.mp F (u ≫ l ≫ v₁ ≫ G.map c₂) (d j)) := by
    rw [_root_.GlobalTheory.CatCoh.mp_comp]
    exact _root_.GlobalTheory.CatCoh.Desc.isUnit_comp (v₁ ≫ G.map c₂) hl
  rwa [show u ≫ G.map c₁ = u ≫ l ≫ v₁ ≫ G.map c₂ from Subsingleton.elim _ _]

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basisObjects_unitLoci_cover_above : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (n : ℕ) (d : Fin n → F.obj T), Ideal.span (Set.range d) = ⊤ → ∀ (t : C') (u : T ⟶ G.obj t), Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), (∃ i, IsUnit (mp F (u ≫ G.map a) (d i))) ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) := by
  first | exact @GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.covBy_unit_above | exact GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.covBy_unit_above | (intros; apply GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.covBy_unit_above <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCommaCoboundaryOfStandardCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCommaCoboundaryOfStandardCover
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CatCoh.Desc


open Classical in
theorem twoCocycle_comma_coboundary_of_standardCover : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (n : ℕ) (d : Fin n → F.obj T), Ideal.span (Set.range d) = ⊤ → ∀ (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp F (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → (∀ i : Fin n, ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u (d i)) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), (∃ i, IsUnit (mp F u (d i))) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b := by
  intro R _ C _ C' _ F G _ _ H hcov hfil T n d hd z hz hy
  choose y hy using hy
  have hu : ∀ {t t' : C'} {u : T ⟶ G.obj t} (a : t ⟶ t') {x : F.obj T}, IsUnit (mp F u x) →
      IsUnit (mp F (u ≫ G.map a) x) := fun a _ h ↦ isUnit_comp _ h
  have h1 := fun i j : Fin n ↦ GlobalTheory.T.oneCocycle_invertibleLocus_isCoboundary_alt F G H hcov hfil T (d i * d j)
    (fun t t' u a ↦ y j t t' u a - y i t t' u a) fun t t' t'' u a b h ↦ by
      rw [map_mul, IsUnit.mul_iff] at h
      rw [map_sub]
      linear_combination hy i t t' t'' u a b h.1 - hy j t t' t'' u a b h.2
  choose β hβ' using h1
  have hβ : ∀ i j t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u (d i)) →
      IsUnit (mp F u (d j)) →
      β i j t' (u ≫ G.map a) - mp F (G.map a) (β i j t u) = y j t t' u a - y i t t' u a :=
    fun i j t t' u a hi hj ↦ hβ' i j t t' u a (by rw [map_mul]; exact hi.mul hj)
  have h2 := fun i j k : Fin n ↦ GlobalTheory.T.sections_invertibleLocus_of_basisFunctor F G H hcov hfil T (d i * d j * d k)
    (fun t u ↦ β j k t u - β i k t u + β i j t u) fun t t' u a h ↦ by
      rw [map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff] at h
      rw [map_add (f := _), map_sub]
      linear_combination hβ j k t t' u a h.1.2 h.2 - hβ i k t t' u a h.1.1 h.2 +
        hβ i j t t' u a h.1.1 h.1.2
  choose x hx' hxs' using h2
  have hx : ∀ i j k, IsSec F (fun S u ↦ (IsUnit (mp F u (d i)) ∧ IsUnit (mp F u (d j))) ∧
      IsUnit (mp F u (d k))) (x i j k) := fun i j k S S' u ψ h ↦
    hx' i j k S S' u ψ (by
      show IsUnit _
      rw [map_mul, map_mul]; exact (h.1.1.mul h.1.2).mul h.2)
  have hxs : ∀ i j k t (u : T ⟶ G.obj t), IsUnit (mp F u (d i)) → IsUnit (mp F u (d j)) →
      IsUnit (mp F u (d k)) → x i j k (G.obj t) u = β j k t u - β i k t u + β i j t u :=
    fun i j k t u hi hj hk ↦ hxs' i j k t u (by rw [map_mul, map_mul]; exact (hi.mul hj).mul hk)
  obtain ⟨e, he, he'⟩ := cech2 H hd x hx (fun l i j k S u hl hi hj hk ↦ by
    obtain ⟨m, b, hb, hb'⟩ := hcov S
    refine sep_std H hb _ fun S' ψ ⟨r, hr⟩ ↦ ?_
    obtain ⟨t, v, w, rfl⟩ := hb' r S' ψ hr
    have hl' := isUnit_comp v hl
    have hi' := isUnit_comp v hi
    have hj' := isUnit_comp v hj
    have hk' := isUnit_comp v hk
    rw [mp_comp, map_sub (mp F v), map_add (mp F v), map_sub (mp F v),
      ← hx i j k S _ u v ⟨⟨hi, hj⟩, hk⟩, ← hx l j k S _ u v ⟨⟨hl, hj⟩, hk⟩,
      ← hx l i k S _ u v ⟨⟨hl, hi⟩, hk⟩, ← hx l i j S _ u v ⟨⟨hl, hi⟩, hj⟩,
      hxs _ _ _ _ _ hi' hj' hk', hxs _ _ _ _ _ hl' hj' hk', hxs _ _ _ _ _ hl' hi' hk',
      hxs _ _ _ _ _ hl' hi' hj']
    ring_nf
    exact map_zero _)
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin n → ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ i j t u,
      IsUnit (mp F u (d i)) → IsUnit (mp F u (d j)) →
      γ j t u - γ i t u = β i j t u - e i j (G.obj t) u := by
    refine ⟨fun i t u ↦ if h : ∃ i, IsUnit (mp F u (d i)) then
      β h.choose i t u - e h.choose i _ u else 0, fun i j t u hi hj ↦ ?_⟩
    have h : ∃ i, IsUnit (mp F u (d i)) := ⟨i, hi⟩
    simp only [dif_pos h]
    linear_combination -he' _ i j _ u h.choose_spec hi hj + hxs _ i j t u h.choose_spec hi hj
  obtain ⟨α, hα⟩ : ∃ α : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ i t t' u a,
      IsUnit (mp F u (d i)) →
      α t t' u a = y i t t' u a - (γ i t' (u ≫ G.map a) - mp F (G.map a) (γ i t u)) := by
    refine ⟨fun t t' u a ↦ if h : ∃ i, IsUnit (mp F u (d i)) then
      y h.choose t t' u a - (γ h.choose t' (u ≫ G.map a) - mp F (G.map a) (γ h.choose t u)) else 0,
      fun i t t' u a hi ↦ ?_⟩
    have h : ∃ i, IsUnit (mp F u (d i)) := ⟨i, hi⟩
    simp only [dif_pos h]
    have k1 := congrArg (mp F (G.map a)) (hγ i _ t u hi h.choose_spec)
    have k2 := hγ i _ t' (u ≫ G.map a) (hu a hi) (hu a h.choose_spec)
    have k3 := he i _ _ _ u (G.map a) ⟨hi, h.choose_spec⟩
    have k4 := hβ i _ t t' u a hi h.choose_spec
    simp only [map_sub] at k1
    linear_combination k1 - k2 + k3 - k4
  refine ⟨α, fun t t' t'' u a b ⟨i, hi⟩ ↦ ?_⟩
  rw [hα i _ _ _ _ hi, hα i _ _ _ _ hi, hα i _ _ _ _ (hu a hi)]
  simp only [map_sub, mp_comp, Category.assoc, G.map_comp]
  linear_combination hy i t t' t'' u a b hi

end GlobalTheory.CatCoh.Desc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCommaCoboundaryOfStandardCoverStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoCocycle_comma_coboundary_of_standardCover_alt : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (n : ℕ) (d : Fin n → F.obj T), Ideal.span (Set.range d) = ⊤ → ∀ (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp F (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → (∀ i : Fin n, ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u (d i)) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), (∃ i, IsUnit (mp F u (d i))) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b := by
  first | exact @GlobalTheory.CatCoh.Desc.twoCocycle_comma_coboundary_of_standardCover | exact GlobalTheory.CatCoh.Desc.twoCocycle_comma_coboundary_of_standardCover | (intros; apply GlobalTheory.CatCoh.Desc.twoCocycle_comma_coboundary_of_standardCover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCoboundaryOfBasisFunctor
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

theorem twoCocycle_coboundary_of_basisFunctor_alt : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → (F).obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp (F) u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (F).obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp (F) u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : C) (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → (F).obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp (F) (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), mp (F) (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T z hz
  classical
  obtain ⟨n, d, hd, hcT⟩ := hcov T
  have hpt : ∀ i : Fin n, ∃ (p : C') (_ : T ⟶ G.obj p), ∀ S (u : T ⟶ S),
      IsUnit (mp F u (d i)) → Nonempty (G.obj p ⟶ S) := by
    intro i
    obtain ⟨T', l, hl, -, -, huniv⟩ := H T (d i)
    obtain ⟨p, v, w, -⟩ := hcT i T' l hl
    exact ⟨p, v, fun S u hu ↦ by obtain ⟨m, -⟩ := huniv S u hu; exact ⟨w ≫ m⟩⟩
  choose p v hp using hpt
  obtain ⟨f, hf⟩ := GlobalTheory.T.twoCocycle_comma_coboundary_of_standardCover_alt F G H hcov hdir T n d hd z hz
    fun i ↦ GlobalTheory.T.twoCocycle_coboundary_on_unitLocus_piece F G H hdir T (d i) (p i) (v i) (hp i) z hz
  have hup : ∀ t (u : T ⟶ G.obj t) t' t'' (a : t ⟶ t') (b : t' ⟶ t''),
      (∃ i, IsUnit (mp F (u ≫ G.map a) (d i))) → ∃ i, IsUnit (mp F (u ≫ G.map (a ≫ b)) (d i)) := by
    rintro t u t' t'' a b ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [G.map_comp, ← Category.assoc, mp_comp]
    exact hi.map _
  obtain ⟨h, hh⟩ := Desc.coboundary_of_restrict (G ⋙ F) (E := fun t ↦ T ⟶ G.obj t)
    (fun u a ↦ u ≫ G.map a) (fun u a b ↦ by simp only [Functor.map_comp, Category.assoc])
    (fun _ _ ↦ True) (fun t u ↦ ∃ i, IsUnit (mp F u (d i))) (fun _ _ _ _ _ ↦ trivial)
    (fun t u _ ↦ GlobalTheory.T.eq_zero_of_upwardFamily_standardCover F G H hdir t _ (hup t u) (GlobalTheory.T.basisObjects_unitLoci_cover_above F G H hcov hdir T n d hd t u))
    (fun t u _ ↦ GlobalTheory.T.exists_glued_section_upwardFamily_standardCover F G H hdir t _ (hup t u) (GlobalTheory.T.basisObjects_unitLoci_cover_above F G H hcov hdir T n d hd t u))
    (fun t u _ ↦ GlobalTheory.T.van1_of_covBy_upward_sieve F G H hdir t _ (hup t u) (GlobalTheory.T.basisObjects_unitLoci_cover_above F G H hcov hdir T n d hd t u))
    z (fun t t' t'' t''' u a b c _ ↦ hz t t' t'' t''' u a b c) f
    (fun t t' t'' u a b hi ↦ hf t t' t'' u a b hi)
  exact ⟨h, fun t t' t'' u a b ↦ hh t t' t'' u a b trivial⟩

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCoboundaryOfBasisFunctorStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → (F).obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp (F) u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (F).obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp (F) u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : C) (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → (F).obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp (F) (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), mp (F) (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) := by
  first | exact @GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.twoCocycle_coboundary_of_basisFunctor_alt | exact GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.twoCocycle_coboundary_of_basisFunctor_alt | (intros; apply GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.twoCocycle_coboundary_of_basisFunctor_alt <;> assumption)
end
