module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LegendreBoundsFactorialMultiIndexCapelli
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTensorEtaleSheafComplexPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanQuasiIsoOfLocalQuasiIsoBoundedBelowDescent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneralLinearGroupDetMapFinOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherianStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CatCoh.Desc.Basis

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C']

theorem span_map_eq_top (F : C ⥤ CommAlgCat.{0} R) {S S' : C} (u : S ⟶ S') {n : ℕ}
    {b : Fin n → F.obj S} (hb : Ideal.span (Set.range b) = ⊤) :
    Ideal.span (Set.range fun i ↦ mp F u (b i)) = ⊤ := by
  have := congrArg (Ideal.map (mp F u)) hb
  rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this

theorem eq_zero_of_local (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : HasLoc F)
    (hdir : (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) →
        ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')))
    {t₁ t₂ : C'} {S : C} (h₁ : Nonempty (G.obj t₁ ⟶ S)) (h₂ : Nonempty (G.obj t₂ ⟶ S)) (z : F.obj S)
    (hz : ∀ t (S' : C) (ψ : S ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) →
      Nonempty (G.obj t ⟶ S') → mp F ψ z = 0) : z = 0 := by
  obtain ⟨w₁⟩ := h₁
  obtain ⟨w₂⟩ := h₂
  obtain ⟨n, b, hb, h⟩ := hdir t₁ t₂ S w₁ w₂
  exact sep_std (H := H) (hb := hb) z fun S' ψ ⟨i, hi⟩ ↦ by
    obtain ⟨t₃, h1, h2, h3⟩ := h i S' ψ hi
    exact hz t₃ S' ψ h1 h2 h3

theorem eq_zero_of_local₃ (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : HasLoc F)
    (hdir : (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) →
        ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')))
    {t₁ t₂ t₃ : C'} {S : C} (h₁ : Nonempty (G.obj t₁ ⟶ S)) (h₂ : Nonempty (G.obj t₂ ⟶ S))
    (h₃ : Nonempty (G.obj t₃ ⟶ S)) (z : F.obj S)
    (hz : ∀ t (S' : C) (ψ : S ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) → Nonempty (t₃ ⟶ t) →
      Nonempty (G.obj t ⟶ S') → mp F ψ z = 0) : z = 0 := by
  refine eq_zero_of_local F G H hdir h₁ h₂ z fun t S' ψ h1 h2 ⟨w⟩ ↦ ?_
  obtain ⟨w₃⟩ := h₃
  obtain ⟨a1⟩ := h1
  obtain ⟨a2⟩ := h2
  refine eq_zero_of_local F G H hdir ⟨w⟩ ⟨w₃ ≫ ψ⟩ _ fun t' S'' χ ⟨a⟩ h3 h4 ↦ ?_
  rw [← mp_comp]
  exact hz t' S'' (ψ ≫ χ) ⟨a1 ≫ a⟩ ⟨a2 ≫ a⟩ h3 h4

theorem exists_glue_points (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) [Quiver.IsThin C] (H : HasLoc F)
    (hdir : (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) →
        ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')))
    (t₁ t₂ : C') (s : ∀ t, F.obj (G.obj t))
    (hs : ∀ t t' (a : t ⟶ t'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) → s t' = mp F (G.map a) (s t)) :
    ∃ x : ∀ S, F.obj S, (∀ S, Nonempty (G.obj t₁ ⟶ S) → Nonempty (G.obj t₂ ⟶ S) →
      ∀ t S' (ψ : S ⟶ S') (w : G.obj t ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) →
        mp F ψ (x S) = mp F w (s t)) ∧
      (∀ S S' (ψ : S ⟶ S'), Nonempty (G.obj t₁ ⟶ S) → Nonempty (G.obj t₂ ⟶ S) →
        x S' = mp F ψ (x S)) := by
  have key : ∀ t t' (S : C) (w : G.obj t ⟶ S) (w' : G.obj t' ⟶ S), Nonempty (t₁ ⟶ t) →
      Nonempty (t₂ ⟶ t) → Nonempty (t₁ ⟶ t') → Nonempty (t₂ ⟶ t') →
      mp F w (s t) = mp F w' (s t') := by
    intro t t' S w w' h1 h2 h1' h2'
    refine sub_eq_zero.1 (eq_zero_of_local F G H hdir ⟨w⟩ ⟨w'⟩ _ fun t'' S' ψ ⟨a⟩ ⟨a'⟩ ⟨w''⟩ ↦ ?_)
    have e1 : w ≫ ψ = G.map a ≫ w'' := Subsingleton.elim _ _
    have e2 : w' ≫ ψ = G.map a' ≫ w'' := Subsingleton.elim _ _
    rw [map_sub, ← mp_comp, ← mp_comp, e1, e2, mp_comp, mp_comp, ← hs t t'' a h1 h2,
      ← hs t' t'' a' h1' h2', sub_self]
  classical
  let σ : ∀ S, F.obj S := fun S ↦
    if h : ∃ t, Nonempty (t₁ ⟶ t) ∧ Nonempty (t₂ ⟶ t) ∧ Nonempty (G.obj t ⟶ S) then
      mp F h.choose_spec.2.2.some (s h.choose) else 0
  have hσ : ∀ t S (w : G.obj t ⟶ S), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) →
      σ S = mp F w (s t) := by
    intro t S w h1 h2
    have h : ∃ t, Nonempty (t₁ ⟶ t) ∧ Nonempty (t₂ ⟶ t) ∧ Nonempty (G.obj t ⟶ S) :=
      ⟨t, h1, h2, ⟨w⟩⟩
    simp only [σ, dif_pos h]
    exact key _ _ _ _ _ h.choose_spec.1 h.choose_spec.2.1 h1 h2
  have h1 : ∀ S, ∃ x : F.obj S, Nonempty (G.obj t₁ ⟶ S) → Nonempty (G.obj t₂ ⟶ S) →
      ∀ t S' (ψ : S ⟶ S') (w : G.obj t ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) →
        mp F ψ x = mp F w (s t) := by
    intro S
    by_cases hS : Nonempty (G.obj t₁ ⟶ S) ∧ Nonempty (G.obj t₂ ⟶ S)
    · obtain ⟨⟨w₁⟩, ⟨w₂⟩⟩ := hS
      obtain ⟨n, b, hb, hcov⟩ := hdir t₁ t₂ S w₁ w₂
      obtain ⟨x, hx⟩ := glue_std (H := H) (hb := hb) (fun S' _ ↦ σ S') fun S' S'' ψ χ ⟨i, hi⟩ ↦ by
        obtain ⟨t, h1, h2, ⟨w⟩⟩ := hcov i S' ψ hi
        show σ S'' = mp F χ (σ S')
        rw [hσ t S'' (w ≫ χ) h1 h2, hσ t S' w h1 h2, mp_comp]
      refine ⟨x, fun _ _ t S' ψ w h1 h2 ↦
        sub_eq_zero.1 <| sep_std (H := H) (hb := span_map_eq_top F ψ hb) _ fun S'' χ ⟨i, hi⟩ ↦ ?_⟩
      have hi' : IsUnit (mp F (ψ ≫ χ) (b i)) := by rw [mp_comp]; exact hi
      rw [map_sub, ← mp_comp, hx S'' (ψ ≫ χ) ⟨i, hi'⟩, ← mp_comp, hσ t S'' (w ≫ χ) h1 h2,
        sub_self]
    · exact ⟨0, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hS⟩
  choose x hx using h1
  refine ⟨x, hx, fun S S' ψ h1 h2 ↦ ?_⟩
  obtain ⟨w₁⟩ := h1
  obtain ⟨w₂⟩ := h2
  refine sub_eq_zero.1 (eq_zero_of_local F G H hdir ⟨w₁ ≫ ψ⟩ ⟨w₂ ≫ ψ⟩ _ fun t S'' χ h1' h2' ⟨w⟩ ↦ ?_)
  rw [map_sub, hx S' ⟨w₁ ≫ ψ⟩ ⟨w₂ ≫ ψ⟩ t S'' χ w h1' h2', ← mp_comp,
    hx S ⟨w₁⟩ ⟨w₂⟩ t S'' (ψ ≫ χ) w h1' h2', sub_self]

theorem oneCocycle_coboundary_comma_localBasis (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) [Quiver.IsThin C] [Quiver.IsThin C']
    (H : HasLoc F) (hcov : (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧
      ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) →
        ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u))
    (hdir : (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) →
        ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')))
    (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'))
    (hy : ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''),
      y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) :
    ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'),
      g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a := by
  classical

  let yb : ∀ t t' : C', F.obj (G.obj t') := fun t t' ↦
    if h : Nonempty (T ⟶ G.obj t) ∧ Nonempty (t ⟶ t') then y t t' h.1.some h.2.some else 0
  have hyb : ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), y t t' u a = yb t t' := by
    intro t t' u a
    have h : Nonempty (T ⟶ G.obj t) ∧ Nonempty (t ⟶ t') := ⟨⟨u⟩, ⟨a⟩⟩
    simp only [yb, dif_pos h]
    exact congrArg₂ (y t t') (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  have hyc : ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''),
      yb t t'' = mp F (G.map b) (yb t t') + yb t' t'' := by
    intro t t' t'' u a b
    rw [← hyb t t'' u (a ≫ b), ← hyb t t' u a, ← hyb t' t'' (u ≫ G.map a) b]
    exact hy t t' t'' u a b

  obtain ⟨n, b, hb, hcT⟩ := hcov T
  have hpt : ∀ i : Fin n, ∃ (p : C') (_ : T ⟶ G.obj p), ∀ S (u : T ⟶ S),
      IsUnit (mp F u (b i)) → Nonempty (G.obj p ⟶ S) := by
    intro i
    obtain ⟨T', l, hl, -, -, huniv⟩ := H T (b i)
    obtain ⟨p, v, w, -⟩ := hcT i T' l hl
    exact ⟨p, v, fun S u hu ↦ by obtain ⟨m, -⟩ := huniv S u hu; exact ⟨w ≫ m⟩⟩
  choose p v hp using hpt

  have hc0 : ∀ i j : Fin n, ∃ x : ∀ S, F.obj S, (∀ S, Nonempty (G.obj (p i) ⟶ S) →
      Nonempty (G.obj (p j) ⟶ S) → ∀ t S' (ψ : S ⟶ S') (w : G.obj t ⟶ S'), Nonempty (p i ⟶ t) →
        Nonempty (p j ⟶ t) → mp F ψ (x S) = mp F w (yb (p j) t - yb (p i) t)) ∧
      (∀ S S' (ψ : S ⟶ S'), Nonempty (G.obj (p i) ⟶ S) → Nonempty (G.obj (p j) ⟶ S) →
        x S' = mp F ψ (x S)) := by
    intro i j
    refine exists_glue_points F G H hdir (p i) (p j) _ fun t t' a ⟨ai⟩ ⟨aj⟩ ↦ ?_
    rw [map_sub, hyc (p j) t t' (v j) aj a, hyc (p i) t t' (v i) ai a]
    ring
  choose c hc hc' using hc0
  have hs : ∀ i j, IsSec F (fun S u ↦ IsUnit (mp F u (b i)) ∧ IsUnit (mp F u (b j)))
      (fun S (_ : T ⟶ S) ↦ c i j S) := fun i j S S' u ψ h ↦
    hc' i j S S' ψ (hp i S u h.1) (hp j S u h.2)
  have hcc : ∀ i j k S (u : T ⟶ S), IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) →
      IsUnit (mp F u (b k)) → c j k S - c i k S + c i j S = 0 := by
    intro i j k S u hi hj hk
    refine eq_zero_of_local₃ F G H hdir (hp i S u hi) (hp j S u hj) (hp k S u hk) _
      fun t S' ψ ai aj ak ⟨w⟩ ↦ ?_
    rw [map_add (f := _), map_sub, hc j k S (hp j S u hj) (hp k S u hk) t S' ψ w aj ak,
      hc i k S (hp i S u hi) (hp k S u hk) t S' ψ w ai ak,
      hc i j S (hp i S u hi) (hp j S u hj) t S' ψ w ai aj]
    simp only [map_sub]
    ring
  obtain ⟨e, he, he'⟩ := cech1 (H := H) (hb := hb) (fun i j S (_ : T ⟶ S) ↦ c i j S) hs hcc
  have he'' : ∀ i j S (u : T ⟶ S), IsUnit (mp F u (b i)) → IsUnit (mp F u (b j)) →
      c i j S = e j S u - e i S u := he'

  have hX0 : ∀ i (t : C') (_ : T ⟶ G.obj t), ∃ x : ∀ S, F.obj S, (∀ S, Nonempty (G.obj t ⟶ S) →
      Nonempty (G.obj (p i) ⟶ S) → ∀ t' S' (ψ : S ⟶ S') (w : G.obj t' ⟶ S'), Nonempty (t ⟶ t') →
        Nonempty (p i ⟶ t') → mp F ψ (x S) = mp F w (yb (p i) t' - yb t t')) ∧
      (∀ S S' (ψ : S ⟶ S'), Nonempty (G.obj t ⟶ S) → Nonempty (G.obj (p i) ⟶ S) →
        x S' = mp F ψ (x S)) := by
    intro i t u
    refine exists_glue_points F G H hdir t (p i) _ fun t' t'' a ⟨a0⟩ ⟨ai⟩ ↦ ?_
    rw [map_sub, hyc (p i) t' t'' (v i) ai a, hyc t t' t'' u a0 a]
    ring
  choose X hX hX' using hX0

  have indep : ∀ t (u : T ⟶ G.obj t) S (ψ : G.obj t ⟶ S) i j, IsUnit (mp F (u ≫ ψ) (b i)) →
      IsUnit (mp F (u ≫ ψ) (b j)) → X i t u S - e i S (u ≫ ψ) = X j t u S - e j S (u ≫ ψ) := by
    intro t u S ψ i j hi hj
    have key : X i t u S - X j t u S + c i j S = 0 :=
      eq_zero_of_local₃ F G H hdir ⟨ψ⟩ (hp i S _ hi) (hp j S _ hj) _ fun t' S' χ a0 ai aj ⟨w⟩ ↦ by
        rw [map_add (f := _), map_sub, hX i t u S ⟨ψ⟩ (hp i S _ hi) t' S' χ w a0 ai,
          hX j t u S ⟨ψ⟩ (hp j S _ hj) t' S' χ w a0 aj,
          hc i j S (hp i S _ hi) (hp j S _ hj) t' S' χ w ai aj]
        simp only [map_sub]
        ring
    linear_combination key - he'' i j S (u ≫ ψ) hi hj

  have hg0 : ∀ t (u : T ⟶ G.obj t), ∃ x : F.obj (G.obj t), ∀ S (ψ : G.obj t ⟶ S) i,
      IsUnit (mp F (u ≫ ψ) (b i)) → mp F ψ x = X i t u S - e i S (u ≫ ψ) := by
    intro t u
    let σ : ∀ S, (G.obj t ⟶ S) → F.obj S := fun S ψ ↦
      if h : ∃ i, IsUnit (mp F (u ≫ ψ) (b i)) then X h.choose t u S - e h.choose S (u ≫ ψ) else 0
    have hσ : ∀ S ψ i, IsUnit (mp F (u ≫ ψ) (b i)) → σ S ψ = X i t u S - e i S (u ≫ ψ) := by
      intro S ψ i hi
      have h : ∃ i, IsUnit (mp F (u ≫ ψ) (b i)) := ⟨i, hi⟩
      simp only [σ, dif_pos h]
      exact indep t u S ψ _ i h.choose_spec hi
    obtain ⟨x, hx⟩ := glue_std (H := H) (hb := span_map_eq_top F u hb) σ fun S S' ψ χ ⟨i, hi⟩ ↦ by
      have hi' : IsUnit (mp F (u ≫ ψ) (b i)) := by rw [mp_comp]; exact hi
      have hi'' : IsUnit (mp F (u ≫ ψ ≫ χ) (b i)) := by
        rw [← Category.assoc, mp_comp]; exact hi'.map _
      rw [hσ S' (ψ ≫ χ) i hi'', hσ S ψ i hi', map_sub, ← hX' i t u S S' χ ⟨ψ⟩ (hp i S _ hi'),
        ← he i S S' (u ≫ ψ) χ hi', Category.assoc]
    exact ⟨x, fun S ψ i hi ↦ by
      rw [hx S ψ ⟨i, by rw [mp_comp] at hi; exact hi⟩, hσ S ψ i hi]⟩
  choose g hg using hg0
  refine ⟨g, fun t t' u a ↦ ?_⟩
  rw [hyb]
  refine sub_eq_zero.1 (sep_std (H := H) (hb := span_map_eq_top F (u ≫ G.map a) hb) _ fun S χ ⟨i, hi⟩ ↦ ?_)
  have hi' : IsUnit (mp F ((u ≫ G.map a) ≫ χ) (b i)) := by rw [mp_comp]; exact hi
  have hi'' : IsUnit (mp F (u ≫ G.map a ≫ χ) (b i)) := by rw [← Category.assoc]; exact hi'
  rw [map_sub, map_sub, hg t' (u ≫ G.map a) S χ i hi', ← mp_comp, hg t u S (G.map a ≫ χ) i hi'',
    Category.assoc]
  have key : X i t' (u ≫ G.map a) S - X i t u S - mp F χ (yb t t') = 0 :=
    eq_zero_of_local F G H hdir ⟨χ⟩ (hp i S _ hi') _ fun t'' S' ψ ⟨a'⟩ ai ⟨w⟩ ↦ by
      rw [map_sub, map_sub, hX i t' (u ≫ G.map a) S ⟨χ⟩ (hp i S _ hi') t'' S' ψ w ⟨a'⟩ ai,
        hX i t u S ⟨G.map a ≫ χ⟩ (hp i S _ hi') t'' S' ψ w ⟨a ≫ a'⟩ ai, ← mp_comp,
        (Subsingleton.elim _ _ : χ ≫ ψ = G.map a' ≫ w), mp_comp, hyc t t' t'' u a a']
      simp only [map_sub, map_add (f := _)]
      ring
  linear_combination key

theorem oneCocycle_vanishing_comma_of_basis : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a) := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T y hy
  exact oneCocycle_coboundary_comma_localBasis F G H hcov hdir T y hy

end GlobalTheory.CatCoh.Desc.Basis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIsIrreducibleComponentOfRationalPointSmoot
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIsIrreducibleComponentOfRationalPointSmoot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isOpen_and_isIrreducible_sectionComponent_of_smooth_field
    (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
    (e : Spec (CommRingCat.of k) ⟶ X) (hf : Smooth f) (he : e ≫ f = 𝟙 _) :
    IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} ∧
      IsIrreducible {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  have hsub : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum k))
  have hZ : {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))}
      = connectedComponent (e p) := by
    ext x
    have h1 : (f ⁻¹' {f x} : Set X) = Set.univ :=
      Set.eq_univ_of_forall fun y => Subsingleton.elim _ _
    have h2 : f x = p := Subsingleton.elim _ _
    rw [Set.mem_setOf_eq, h1, h2, connectedComponentIn_univ]
  rw [hZ]
  have hN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hO : IsOpen (connectedComponent (e p)) := GlobalTheory.T.isOpen_connectedComponent_of_isLocallyNoetherian' X hN (e p)
  refine ⟨hO, ?_⟩
  let U : X.Opens := ⟨connectedComponent (e p), hO⟩
  have hc : ConnectedSpace U.toScheme :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := e p))
  have hi : IrreducibleSpace U.toScheme :=
    GlobalTheory.T.irreducibleSpace_of_smooth_over_field_of_connected k U.toScheme (U.ι ≫ f) inferInstance hc
  exact isIrreducible_iff_irreducibleSpace.mpr hi

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIsIrreducibleComponentOfRationalPointSmootStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_isIrreducible_componentOfRationalPoint_smooth : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (e : Spec (CommRingCat.of k) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} ∧ IsIrreducible {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  first | exact @GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field | exact GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field | (intros; apply GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecPullSurjectiveAndKer
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechDR

namespace GlobalTheory.CechDR

private theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

private theorem spi {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B}
    (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem secPull_surjective_and_ker (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R)
    (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ X : Scheme.{0})
    (s₀ : X₀ ⟶ Sp R₀) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (hpb : IsPullback i s₀ s (spMap π))
    (p : Pair i) (hp : i ⁻¹ᵁ p.1.2.1 = p.1.1.1) :
    Function.Surjective (secPull s s₀ p) ∧
      ∀ b, secPull s s₀ p b = 0 ↔ b ∈ I.map (algebraMap R (Sec s p.1.2.1)) := by
  set J : Ideal (Sec s p.1.2.1) := I.map (algebraMap R (Sec s p.1.2.1)) with hJ
  let q := Ideal.Quotient.mk J
  have hφ : ∀ r, secPull s s₀ p (algebraMap R _ r) = algebraMap R₀ _ (π r) :=
    (semiHom_secPull hpb.w p).map_algebraMap
  have hJker : ∀ a ∈ J, secPull s s₀ p a = 0 := by
    have : J ≤ RingHom.ker (secPull s s₀ p) := by
      rw [hJ, Ideal.map_le_iff_le_comap]
      intro r hr
      rw [← hk, RingHom.mem_ker] at hr
      rw [Ideal.mem_comap, RingHom.mem_ker, hφ, hr, map_zero]
    exact fun a ha ↦ this ha
  let τ : R₀ →+* (Sec s p.1.2.1 ⧸ J) := π.liftOfSurjective hπ
    ⟨q.comp (algebraMap R _), fun r hr ↦ by
      rw [hk] at hr
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hr)⟩
  have hτ : τ.comp π = q.comp (algebraMap R _) := RingHom.liftOfSurjective_comp _ _ _
  have hz : (spMap q ≫ affPt s p.1.2) ≫ s = spMap τ ≫ spMap π := by
    rw [Category.assoc, affPt_w, ← spc, ← spc, hτ]
  let w := hpb.lift _ _ hz
  have hw : w ≫ i = spMap q ≫ affPt s p.1.2 := hpb.lift_fst _ _ _
  haveI : IsOpenImmersion (affPt s₀ p.1.1) := p.1.1.2.isOpenImmersion_fromSpec
  haveI : IsOpenImmersion (affPt s p.1.2) := p.1.2.2.isOpenImmersion_fromSpec
  have hr : Set.range w ⊆ Set.range (affPt s₀ p.1.1) := by
    rintro _ ⟨x, rfl⟩
    have e : Set.range (affPt s₀ p.1.1) = p.1.1.1 := p.1.1.2.range_fromSpec
    have e' : Set.range (affPt s p.1.2) = p.1.2.1 := p.1.2.2.range_fromSpec
    rw [e, ← hp]
    change i (w x) ∈ (p.1.2.1 : Set X)
    rw [← e', ← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let w' := IsOpenImmersion.lift (affPt s₀ p.1.1) w hr
  have hw' : w' ≫ affPt s₀ p.1.1 = w := IsOpenImmersion.lift_fac _ _ _
  let ψ : Sec s₀ p.1.1.1 →+* (Sec s p.1.2.1 ⧸ J) := (Spec.preimage w').hom
  have hψ : spMap ψ = w' := Spec.map_preimage w'
  have h1 : ψ.comp (secPull s s₀ p) = q := by
    apply spi
    rw [← cancel_mono (affPt s p.1.2), spc, Category.assoc, secPull_affPt, hψ, ← Category.assoc,
      hw', hw]
  let ψ' := Ideal.Quotient.lift J (secPull s s₀ p) hJker
  have h2 : ψ'.comp q = secPull s s₀ p := Ideal.Quotient.lift_comp_mk _ _ _
  haveI : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective _ hπ
  haveI : IsClosedImmersion i := MorphismProperty.of_isPullback hpb.flip this
  haveI : Mono (spMap (secPull s s₀ p) ≫ affPt s p.1.2) := by
    rw [secPull_affPt]; infer_instance
  haveI : Mono (spMap (secPull s s₀ p)) := mono_of_mono _ (affPt s p.1.2)
  have h3 : ψ'.comp ψ = RingHom.id _ := by
    apply spi
    rw [← cancel_mono (spMap (secPull s s₀ p)), ← spc, ← spc, RingHom.comp_assoc, h1, h2,
      RingHom.id_comp]
  refine ⟨fun b ↦ ?_, fun b ↦ ⟨fun hb ↦ ?_, hJker b⟩⟩
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ψ b)
    refine ⟨a, ?_⟩
    rw [← h2, RingHom.comp_apply, show q a = ψ b from ha]
    exact congrArg (fun f ↦ f b) h3
  · rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q b = 0
    rw [← h1, RingHom.comp_apply, hb, map_zero]

end GlobalTheory.CechDR
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeFormalGroupDeterminantPowDepthOfRadii
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeFormalGroupDeterminantPowDepthOfRadii
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DepthCount

variable {C : Type} [Field C]

theorem prod_X_col {i : ℕ} (b : Fin i) (d : Fin i →₀ ℕ) :
    (d.prod fun s e => (X (⟨b, s⟩ : Σ _ : Fin i, Fin i) : MvPowerSeries (Σ _ : Fin i, Fin i) C) ^ e)
      = monomial (Finsupp.mapDomain (Sigma.mk b) d) 1 := by
  induction d using Finsupp.induction with
  | zero => simp
  | single_add s n d hs hn ih =>
    rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), ih, Finsupp.mapDomain_add,
      Finsupp.mapDomain_single, Finsupp.prod_single_index (by simp), X_pow_eq,
      monomial_mul_monomial, one_mul]

theorem hasSubst_col {i : ℕ} (b : Fin i) :
    HasSubst (fun a : Fin i => (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) :=
  hasSubst_of_constantCoeff_zero (fun a => constantCoeff_X _)

theorem constantCoeff_col {i : ℕ} (b : Fin i) (g : MvPowerSeries (Fin i) C)
    (hg : constantCoeff g = 0) :
    constantCoeff (subst (fun a : Fin i => (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) g)
      = 0 := by
  have hs := hasSubst_col (C := C) b
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst hs]
  convert finsum_zero with d
  rw [prod_X_col, coeff_monomial, smul_eq_mul]
  split_ifs with h
  · have hd : d = 0 := by
      have h' := h.symm
      rw [← Finsupp.mapDomain_zero (f := Sigma.mk b)] at h'
      exact Finsupp.mapDomain_injective (sigma_mk_injective (i := b)) h'
    subst hd
    simp [hg]
  · simp

theorem wt_col {i : ℕ} (v : AddValuation C (WithTop ℝ)) (ρ : Fin i → ℝ) (b : Fin i)
    (g : MvPowerSeries (Fin i) C) (hg : OrdGe v ρ g 0) (β : (Σ _ : Fin i, Fin i) →₀ ℕ) :
    (((0 - β.sum (fun y e => ρ y.2 * (e : ℝ)) : ℝ)) : WithTop ℝ) ≤
      v (coeff β (subst (fun a : Fin i => (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) g)) := by
  have hs := hasSubst_col (C := C) b
  rw [coeff_subst hs, finsum_eq_sum _ (coeff_subst_finite hs g β)]
  apply v.map_le_sum
  intro d _
  rw [prod_X_col, coeff_monomial, smul_eq_mul]
  split_ifs with h
  · rw [mul_one]
    subst h
    rw [Finsupp.sum_mapDomain_index (by simp) (by intros; push_cast; ring),
      Finsupp.sum_fintype _ _ (by simp)]
    exact hg d
  · simp

theorem depth_count : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (ρ : Fin i → ℝ) (t : Fin d → MvPowerSeries (Fin i) C) (B : ℝ), (∀ a, constantCoeff (t a) = 0) → (∀ a, OrdGe v ρ (t a) 0) → (∀ α ∈ (detPow C i c).support, (((B + c * ∑ a, ρ a : ℝ)) : WithTop ℝ) ≤ v ((detPow C i c).coeff α * mfact α)) → ∀ f : MvPowerSeries (Σ _ : Fin i, Fin d) C, MvIsInt v f → ((B : ℝ) : WithTop ℝ) ≤ v (derivAt0 (detPow C i c) (subst (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) f)) := by
  intro C _ _ v i d c ρ t B ht0 ht hP f hf
  have hw := GlobalTheory.WeightSubst.weight_subst_nonneg C v (Σ _ : Fin i, Fin i) (Σ _ : Fin i, Fin d)
    (fun y => ρ y.2) f
    (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i =>
      (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) hf
    (fun x => constantCoeff_col x.1 _ (ht0 x.2)) (fun x => wt_col v ρ x.1 _ (ht x.2))
  unfold derivAt0
  apply v.map_le_sum
  intro α hα
  have hrow := ((GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape C i c).2.2.2 α hα).1
  rw [v.map_mul]
  have e : B = (B + c * ∑ a, ρ a) + (0 - α.sum (fun y e => ρ y.2 * (e : ℝ))) := by
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hc : ∀ a : Fin i, (∑ b : Fin i, ((α ⟨b, a⟩ : ℕ) : ℝ)) = c := fun a => by
      exact_mod_cast hrow a
    simp_rw [hc]
    rw [← Finset.sum_mul]
    ring
  rw [e, WithTop.coe_add]
  exact add_le_add (hP α hα) (hw α)

end GlobalTheory.DepthCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeFormalGroupDeterminantPowDepthOfRadiiStatement
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_formalGroupDeterminantPowDepth_of_radii : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (ρ : Fin i → ℝ) (t : Fin d → MvPowerSeries (Fin i) C) (B : ℝ), (∀ a, constantCoeff (t a) = 0) → (∀ a, OrdGe v ρ (t a) 0) → (∀ α ∈ (detPow C i c).support, (((B + c * ∑ a, ρ a : ℝ)) : WithTop ℝ) ≤ v ((detPow C i c).coeff α * mfact α)) → ∀ f : MvPowerSeries (Σ _ : Fin i, Fin d) C, MvIsInt v f → ((B : ℝ) : WithTop ℝ) ≤ v (derivAt0 (detPow C i c) (subst (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) f)) := by
  first | exact @GlobalTheory.DepthCount.depth_count | exact GlobalTheory.DepthCount.depth_count | (intros; apply GlobalTheory.DepthCount.depth_count <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftClassFunctionIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftClassFunctionIsometry
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin

theorem shLift_isometry : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (f f' : GL (Fin n) F → ℂ), IsCl f → IsCl f' →
    (Nat.card (GL (Fin n) F) : ℂ) * ∑ᶠ δ, shLift s f δ * star (shLift s f' δ) =
      (Nat.card (GL (Fin n) F') : ℂ) * ∑ᶠ γ, f γ * star (f' γ) := by
  intro F F' _ _ _ _ s hs n f f' hf hf'
  haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective
  letI : Fintype (GL (Fin n) F) := Fintype.ofFinite _
  letI : Fintype (GL (Fin n) F') := Fintype.ofFinite _
  have hex := GlobalTheory.T.every_element_is_norm F F' s hs n
  have hfib := GlobalTheory.T.card_isGaloisTwistedNormGL_mul_card_GL F F' s hs n
  have hlf := (GlobalTheory.T.base_change_lift_class_function F F' s hs n f hf).1
  have hlf' := (GlobalTheory.T.base_change_lift_class_function F F' s hs n f' hf').1
  have hnd := GlobalTheory.T.isConj_of_isConj_glFieldExtensionInclusion F F' n
  obtain ⟨c, hc⟩ : ∃ c : GL (Fin n) F → ℂ, ∀ γ, c γ = (Nat.card {γ' : GL (Fin n) F // IsConj γ γ'} : ℂ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : GL (Fin n) F → ℂ, ∀ γ, v γ = f γ * star (f' γ) := ⟨_, fun _ => rfl⟩
  have hcne : ∀ γ, c γ ≠ 0 := by
    intro γ
    rw [hc, Nat.cast_ne_zero]
    haveI : Nonempty {γ' : GL (Fin n) F // IsConj γ γ'} := ⟨⟨γ, IsConj.refl γ⟩⟩
    exact Nat.card_pos.ne'

  have hclass : ∀ (δ : GL (Fin n) F') (γ : GL (Fin n) F), IsNorm s δ γ → ∀ γ' : GL (Fin n) F, IsNorm s δ γ' ↔ IsConj γ γ' := by
    intro δ γ h γ'
    unfold IsNorm at *
    constructor
    · intro h'
      exact hnd γ γ' (IsConj.trans h (IsConj.symm h'))
    · intro h'
      exact IsConj.trans (IsConj.symm (MonoidHom.map_isConj (incl F F' n) h')) h
  have hcard : ∀ (δ : GL (Fin n) F') (γ : GL (Fin n) F), IsNorm s δ γ → c γ = ((Finset.univ.filter fun γ' => IsNorm s δ γ').card : ℂ) := by
    intro δ γ h
    rw [hc, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 2
    ext γ'
    simp [hclass δ γ h γ']
  have key : ∀ δ : GL (Fin n) F',
      (∑ γ, if IsNorm s δ γ then v γ / c γ else 0) = shLift s f δ * star (shLift s f' δ) := by
    intro δ
    obtain ⟨γ0, h0⟩ := hex δ
    have e : ∀ γ, (if IsNorm s δ γ then v γ / c γ else 0) =
        if IsNorm s δ γ then (shLift s f δ * star (shLift s f' δ)) / c γ0 else 0 := by
      intro γ
      split_ifs with h
      · rw [hv, hcard δ γ h, ← hcard δ γ0 h0, hlf δ γ h, hlf' δ γ h]
      · rfl
    rw [Finset.sum_congr rfl (fun γ _ => e γ), Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, ← hcard δ γ0 h0]
    field_simp [hcne γ0]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have lhs : (∑ δ, shLift s f δ * star (shLift s f' δ)) =
      ∑ γ, ((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ) * (v γ / c γ) := by
    rw [← Finset.sum_congr rfl (fun δ _ => key δ), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [lhs, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  have h := hfib γ
  rw [Nat.card_eq_fintype_card (α := {δ : GL (Fin n) F' // IsNorm s δ γ}), Fintype.card_subtype] at h
  have h' : (Nat.card (GL (Fin n) F) : ℂ) * ((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ) =
      c γ * (Nat.card (GL (Fin n) F') : ℂ) := by
    rw [hc]
    exact_mod_cast (by rw [mul_comm]; exact h)
  rw [show (Nat.card (GL (Fin n) F) : ℂ) * (((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ) * (v γ / c γ)) =
      ((Nat.card (GL (Fin n) F) : ℂ) * ((Finset.univ.filter fun δ => IsNorm s δ γ).card : ℂ)) * v γ / c γ by ring,
    h', hv]
  field_simp [hcne γ]

end GlobalTheory.Shin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniLiftClassFunctionIsometryStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintaniLiftClassFunction_isometry : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (f f' : GL (Fin n) F → ℂ), IsCl f → IsCl f' → (Nat.card (GL (Fin n) F) : ℂ) * ∑ᶠ δ, shLift s f δ * star (shLift s f' δ) = (Nat.card (GL (Fin n) F') : ℂ) * ∑ᶠ γ, f γ * star (f' γ) := by
  first | (exact @GlobalTheory.Shin.shLift_isometry) | (exact GlobalTheory.Shin.shLift_isometry) | (intros; apply GlobalTheory.Shin.shLift_isometry  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitAnalyticFunction
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD

open Polynomial

theorem isIntegral_of_le {k F K : Type} [Field k] [Field F] [Field K] [Algebra k F] [Algebra F K]
    {A A' : Subalgebra k F} (h : A ≤ A') {y : K} (hy : IsIntegral A y) : IsIntegral A' y := by
  obtain ⟨p, hm, he⟩ := hy
  refine ⟨p.map (Subalgebra.inclusion h), hm.map _, ?_⟩
  rw [eval₂_map]
  exact he

theorem rA_mono (k : Type) [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} (x : Fin (d + 1) → F)
    {I J : Finset (Fin (d + 1))} (h : I ⊆ J) : rA k x I ≤ rA k x J := by
  apply Algebra.adjoin_mono
  rintro y ⟨i, hi, j, rfl⟩
  exact ⟨i, h hi, j, rfl⟩

theorem rB_mono_loc : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I →
    (∀ J, I ⊆ J → rB k K x I ≤ rB k K x J) ∧
    ∀ y : K, y ∈ rB k K x I ↔ ∃ N : ℕ, y * algebraMap F K (∏ j ∈ I, x j / x i) ^ N ∈ rB k K x {i} := by
  intro k _ _ F K _ _ _ _ _ _ d x hK I i hi
  have memB : ∀ (J : Finset (Fin (d + 1))) (y : K), y ∈ rB k K x J ↔ IsIntegral (rA k x J) y := fun J y => by
    rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  refine ⟨fun J hJ y hy => (memB J y).2 (isIntegral_of_le (rA_mono k x hJ) ((memB I y).1 hy)), fun y => ?_⟩
  set s : F := ∏ j ∈ I, x j / x i with hs
  have hsi : s ∈ rA k x {i} := Subalgebra.prod_mem _ fun j _ =>
    Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩
  have hsinv : s⁻¹ ∈ rA k x I := by
    rw [hs, ← Finset.prod_inv_distrib]
    refine Subalgebra.prod_mem _ fun j hj => ?_
    rw [inv_div]
    exact Algebra.subset_adjoin ⟨j, hj, i, rfl⟩
  have hsne : s ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (hK.pd.ne j) (hK.pd.ne i)
  have hiI : rA k x {i} ≤ rA k x I := rA_mono k x (Finset.singleton_subset_iff.2 hi)
  simp only [memB]
  constructor
  · rintro ⟨p, hm, he⟩
    have hc : ∀ m, ∃ N : ℕ, (p.coeff m : F) * s ^ N ∈ rA k x {i} := fun m =>
      (GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart k F d x hK.pd I i hi (p.coeff m : F)).1 (p.coeff m).2
    choose Nf hNf using hc
    set N := (Finset.range (p.natDegree + 1)).sup Nf
    have hcN : ∀ m, (p.coeff m : F) * s ^ N ∈ rA k x {i} := by
      intro m
      by_cases hmd : m ≤ p.natDegree
      · have hle : Nf m ≤ N := Finset.le_sup (f := Nf) (Finset.mem_range.2 (Nat.lt_succ_of_le hmd))
        rw [← Nat.add_sub_cancel' hle, pow_add, ← mul_assoc]
        exact Subalgebra.mul_mem _ (hNf m) (Subalgebra.pow_mem _ hsi _)
      · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hmd)]
        simp
    set q : F[X] := (p.map (algebraMap (rA k x I) F)).scaleRoots (s ^ N)
    have hqm : q.Monic := (monic_scaleRoots_iff _).2 (hm.map _)
    have hdeg : (p.map (algebraMap (rA k x I) F)).natDegree = p.natDegree :=
      natDegree_map_eq_of_injective (fun a b h => Subtype.ext h) _
    have hl : q ∈ lifts (algebraMap (rA k x {i}) F) := by
      rw [lifts_iff_coeff_lifts]
      intro m
      rw [coeff_scaleRoots, coeff_map, hdeg]
      have hmem : (algebraMap (rA k x I) F (p.coeff m)) * (s ^ N) ^ (p.natDegree - m) ∈ rA k x {i} := by
        by_cases hmd : m < p.natDegree
        · obtain ⟨e, he'⟩ : ∃ e, p.natDegree - m = e + 1 := ⟨p.natDegree - m - 1, by omega⟩
          rw [he', pow_succ', ← mul_assoc]
          exact Subalgebra.mul_mem _ (hcN m) (Subalgebra.pow_mem _ (Subalgebra.pow_mem _ hsi _) _)
        · rw [Nat.sub_eq_zero_of_le (not_lt.1 hmd), pow_zero, mul_one]
          rcases (not_lt.1 hmd).eq_or_lt with h | h
          · rw [← h, hm.coeff_natDegree, map_one]
            exact Subalgebra.one_mem _
          · rw [coeff_eq_zero_of_natDegree_lt h, map_zero]
            exact Subalgebra.zero_mem _
      exact ⟨⟨_, hmem⟩, rfl⟩
    obtain ⟨q0, hq0, -, hq0m⟩ := lifts_and_natDegree_eq_and_monic hl hqm
    refine ⟨N, q0, hq0m, ?_⟩
    have h1 : eval₂ (algebraMap F K) y (p.map (algebraMap (rA k x I) F)) = 0 := by
      rw [eval₂_map]
      exact he
    have h2 : eval₂ (algebraMap F K) (algebraMap F K (s ^ N) * y) q = 0 :=
      scaleRoots_eval₂_eq_zero (algebraMap F K) (s := s ^ N) h1
    rw [← map_pow, mul_comm]
    rw [← hq0, eval₂_map] at h2
    exact h2
  · rintro ⟨N, hN⟩
    have h1 : IsIntegral (rA k x I) (y * algebraMap F K s ^ N) := isIntegral_of_le hiI hN
    have h2 : IsIntegral (rA k x I) (algebraMap F K s⁻¹ ^ N) := by
      have : IsIntegral (rA k x I) (algebraMap (rA k x I) K ⟨s⁻¹, hsinv⟩) := isIntegral_algebraMap
      exact this.pow N
    have h3 := h1.mul h2
    rwa [mul_assoc, ← mul_pow, ← map_mul, mul_inv_cancel₀ hsne, map_one, one_pow, mul_one] at h3

end GlobalTheory.PD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceDescentLocalEquivalence
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCohomologyEquivalenceIffElementwise
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCohomologyEquivalenceIffElementwise
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCEqv

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R) (E E' : Spc) (f : E ⟶ E'),
    Eqv R f F ↔ SurjH ((HC R F).map f.op) ∧ InjH ((HC R F).map f.op) := by
  intro R _ F E E' f
  obtain ⟨-, cl, hsurj, heq, hzero, hpull⟩ := GlobalTheory.EtC.HCElements.main R F
  constructor
  · intro hf
    refine ⟨fun n z hz => ?_, fun n c hc ⟨y, hy⟩ => ?_⟩
    · obtain ⟨x, hx⟩ := (hf n).2 (cl E n z hz)
      obtain ⟨c, hc, rfl⟩ := hsurj E' n x
      obtain ⟨h, hp⟩ := hpull E E' f n c hc
      rw [hp, heq] at hx
      obtain ⟨y, hy⟩ := hx
      exact ⟨c, y, hc, hy⟩
    · obtain ⟨h, hp⟩ := hpull E E' f n c hc
      have h0 : cl E n (((HC R F).map f.op).f n c) h = 0 := (hzero E n _ h).2 ⟨y, hy⟩
      rw [← hp] at h0
      have : cl E' n c hc = 0 := (hf n).1 (h0.trans (map_zero _).symm)
      obtain ⟨b, hb⟩ := (hzero E' n c hc).1 this
      exact ⟨b, hb.symm⟩
  · rintro ⟨hS, hI⟩ n
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨c, hc, rfl⟩ := hsurj E' n x
      obtain ⟨h, hp⟩ := hpull E E' f n c hc
      rw [hp, hzero] at hx
      obtain ⟨b, hb⟩ := hI n c hc hx
      exact (hzero E' n c hc).2 ⟨b, hb.symm⟩
    · intro x
      obtain ⟨z, hz, rfl⟩ := hsurj E n x
      obtain ⟨c, y, hc, hcy⟩ := hS n z hz
      obtain ⟨h, hp⟩ := hpull E E' f n c hc
      refine ⟨cl E' n c hc, ?_⟩
      rw [hp, heq]
      exact ⟨y, hcy⟩

end GlobalTheory.EtC.HCEqv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCohomologyEquivalenceIffElementwiseStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCohomologyEquivalence_iff_elementwise : ∀ (R : Type) [CommRing R] (F : Shv R) (E E' : Spc) (f : E ⟶ E'), Eqv R f F ↔ SurjH ((HC R F).map f.op) ∧ InjH ((HC R F).map f.op) := by
  first | (exact @GlobalTheory.EtC.HCEqv.main) | (exact GlobalTheory.EtC.HCEqv.main) | (intros; apply GlobalTheory.EtC.HCEqv.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceDescentLocalEquivalence
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.Descent

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) [Cov.IsStableUnderComposition] (Φ Φ' : T ⥤ Spcᵒᵖ) (α : Φ' ⟶ Φ), Refines Cov (fun U X a => Hyp R Φ a ∧ Hyp R Φ' a) → (∀ (U : T) (n : ℤ) (x : H R (Φ.obj U).unop F n), ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : H R (Φ'.obj V).unop F n, pull R (α.app V).unop F n y = pull R (Φ.map g).unop F n x) → (∀ (U : T) (n : ℤ) (y : H R (Φ'.obj U).unop F n), pull R (α.app U).unop F n y = 0 → ∃ (V : T) (g : U ⟶ V), Cov g ∧ pull R (Φ'.map g).unop F n y = 0) → ∀ U, Eqv R (α.app U).unop F := by
  intro R _ F T _ Cov _ Φ Φ' α hRef hS hI U
  obtain ⟨hneg, cl, hcl_surj, hcl_eq, hcl_zero, hpull⟩ := GlobalTheory.T.cohomologyComplexOfSheaf_cocycle_class_properties R F
  have key := GlobalTheory.T.cartan_quasiIso_of_localQuasiIso_boundedBelow_descent T Cov (Φ' ⋙ HC R F) (Φ ⋙ HC R F) (Functor.whiskerRight α (HC R F)) ?_ ?_ ?_ ?_ U
  · exact (GlobalTheory.T.isEtaleCohomologyEquivalence_iff_elementwise R F _ _ (α.app U).unop).2 key
  · exact ⟨0, fun n hn V => ⟨hneg _ n hn, hneg _ n hn⟩⟩
  · intro U' V' g hg
    obtain ⟨X, a, h, hga, h1, h2⟩ := hRef U' V' g hg
    exact ⟨X, a, h, hga, fun n => ⟨GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution R F T Φ' U' X a h2 n, GlobalTheory.T.complexFunctorDegreeTerm_augmented_exact_resolution R F T Φ U' X a h1 n⟩⟩
  · intro n U' z hz
    obtain ⟨V, g, hg, y, hy⟩ := hS U' n (cl (Φ.obj U').unop n z hz)
    obtain ⟨c, hc, rfl⟩ := hcl_surj (Φ'.obj V).unop n y
    obtain ⟨h1, e1⟩ := hpull _ _ (α.app V).unop n c hc
    obtain ⟨h2, e2⟩ := hpull _ _ (Φ.map g).unop n z hz
    rw [e1, e2, hcl_eq] at hy
    obtain ⟨y', hy'⟩ := hy
    exact ⟨V, g, hg, c, y', hc, hy'⟩
  · intro n U' c hc ⟨y, hy⟩
    have h0 : pull R (α.app U').unop F n (cl (Φ'.obj U').unop n c hc) = 0 := by
      obtain ⟨h1, e1⟩ := hpull _ _ (α.app U').unop n c hc
      rw [e1, hcl_zero]
      exact ⟨y, hy⟩
    obtain ⟨V, g, hg, hV⟩ := hI U' n _ h0
    obtain ⟨h2, e2⟩ := hpull _ _ (Φ'.map g).unop n c hc
    rw [e2, hcl_zero] at hV
    obtain ⟨b, hb⟩ := hV
    exact ⟨V, g, hg, b, hb.symm⟩

end GlobalTheory.EtC.Descent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceDescentLocalEquivalenceStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpace_descent_local_equivalence : ∀ (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) [Cov.IsStableUnderComposition] (Φ Φ' : T ⥤ Spcᵒᵖ) (α : Φ' ⟶ Φ), Refines Cov (fun U X a => Hyp R Φ a ∧ Hyp R Φ' a) → (∀ (U : T) (n : ℤ) (x : H R (Φ.obj U).unop F n), ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : H R (Φ'.obj V).unop F n, pull R (α.app V).unop F n y = pull R (Φ.map g).unop F n x) → (∀ (U : T) (n : ℤ) (y : H R (Φ'.obj U).unop F n), pull R (α.app U).unop F n y = 0 → ∃ (V : T) (g : U ⟶ V), Cov g ∧ pull R (Φ'.map g).unop F n y = 0) → ∀ U, Eqv R (α.app U).unop F := by
  first | (exact @GlobalTheory.EtC.Descent.main) | (exact GlobalTheory.EtC.Descent.main) | (intros; apply GlobalTheory.EtC.Descent.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtHeckePointWeilPairingOrthogonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtHeckePointWeilPairingOrthogonal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.HeckeRoot

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {K : Type} [Field K] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}

theorem ev_nsmul (I : TateIsoO D K Q act e) (n j : ℕ) (y : D.La) : I.ev n (j • y) = I.ev n y ^ j := by
  induction j with
  | zero =>
    have h := I.add n 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact mul_left_cancel (a := I.ev n 0) (h.symm.trans (_root_.mul_one _).symm)
  | succ j ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem pair_one (I : TateIsoO D K Q act e) (n : ℕ) (hn : 0 < n) (hnp : n.Coprime p) (w : D.La)
    (hw : ∀ v, (n : ℤ) ∣ 2 * D.EF w v) :
    I.ev n w ^ n = 1 ∧ ∀ z : Q, z ^ n = 1 → e n (I.ev n w) z 1 := by
  refine ⟨(I.onto n hn hnp _).2 ⟨w, rfl⟩, fun z hz => ?_⟩
  obtain ⟨v, rfl⟩ := (I.onto n hn hnp z).1 hz
  have h := I.isom n hn hnp w v
  obtain ⟨t, ht⟩ := hw v
  rw [ht, zpow_mul, zpow_natCast, (I.ζ_prim n hn hnp).pow_eq_one, one_zpow] at h
  exact h

theorem sqrt_hecke_point_weil_orthogonal : ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (K : Type) [Field K] (Q : Type) [Group Q]
    (act : D.O → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (I : GlobalTheory.UPel.HT.TateIsoO D K Q act e)
    (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 0 < N → N.Coprime p →
    (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ x : D.La,
    ∃ (n : ℕ) (h' : Q), 0 < n ∧ n.Coprime p ∧ h' ^ 2 = I.ev (N * k) (N • g x) ∧ (h' ^ (k ^ 2 / c)) ^ n = 1 ∧
      ∀ z : Q, z ^ n = 1 → e n (h' ^ (k ^ 2 / c)) z 1 := by
  intro p _ D K _ Q _ act e I g c k N hc hk hN hNp hEF hsurj hck x
  have hp : p.Prime := Fact.out
  have hc0 : c ≠ 0 := by
    rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hc)
  have hk0 : k ≠ 0 := by
    rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hk)
  have hm : k ^ 2 / c * c = k ^ 2 := Nat.div_mul_cancel hck
  have key : ∀ v, ∃ v', ((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v = k * D.EF x v' := by
    intro v
    obtain ⟨v', hv'⟩ := hsurj v
    refine ⟨v', ?_⟩
    have h1 : D.EF (g x) (g v') = (k : ℤ) * D.EF (g x) v := by rw [hv', map_nsmul, nsmul_eq_mul]
    have h2 := hEF x v'
    have hcZ : (c : ℤ) ≠ 0 := by exact_mod_cast hc0
    have hmZ : ((k ^ 2 / c : ℕ) : ℤ) * c = (k : ℤ) ^ 2 := by exact_mod_cast hm
    apply mul_left_cancel₀ hcZ
    calc (c : ℤ) * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v)
        = (((k ^ 2 / c : ℕ) : ℤ) * c) * D.EF (g x) v := by ring
      _ = k * (k * D.EF (g x) v) := by rw [hmZ]; ring
      _ = k * (c * D.EF x v') := by rw [← h1, h2]
      _ = c * (k * D.EF x v') := by ring
  have core : ∀ n j : ℕ, 0 < n → n.Coprime p → (n : ℤ) ∣ 2 * j * N * k →
      (I.ev n (j • N • g x) ^ (k ^ 2 / c)) ^ n = 1 ∧
        ∀ z : Q, z ^ n = 1 → e n (I.ev n (j • N • g x) ^ (k ^ 2 / c)) z 1 := by
    intro n j hn hnp hd
    rw [← ev_nsmul]
    refine pair_one I n hn hnp _ (fun v => ?_)
    obtain ⟨v', hv'⟩ := key v
    have : 2 * D.EF ((k ^ 2 / c) • j • N • g x) v = 2 * j * N * k * D.EF x v' := by
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      calc _ = 2 * (j : ℤ) * N * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (g x) v) := by ring
        _ = _ := by rw [hv']; ring
    rw [this]
    exact hd.mul_right _
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨r, hr⟩ : Odd k := Nat.odd_iff.2 (by
      rcases Nat.mod_two_eq_zero_or_one k with h | h
      · exfalso
        have h2 : 2 ∣ Nat.gcd k 2 := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h) dvd_rfl
        rw [hk] at h2; omega
      · exact h)
    have hnp : (N * k).Coprime 2 := Nat.Coprime.mul_left hNp hk
    have hn : 0 < N * k := Nat.mul_pos hN (Nat.pos_of_ne_zero hk0)
    refine ⟨N * k, I.ev (N * k) ((r + 1) • N • g x), hn, hnp, ?_, ?_⟩
    · rw [ev_nsmul, ← pow_mul, show (r + 1) * 2 = 1 + k by omega, pow_add, pow_one, ← ev_nsmul,
        smul_smul, mul_comm k N, (I.ker (N * k) hn hnp _).2 ⟨g x, rfl⟩, _root_.mul_one]
    · exact core (N * k) (r + 1) hn hnp ⟨2 * (r + 1), by push_cast; ring⟩
  · have h2p : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).2 (fun h => hp2 h.symm)
    have hnp : (N * k * 2).Coprime p := Nat.Coprime.mul_left (Nat.Coprime.mul_left hNp hk) h2p
    have hnk : 0 < N * k := Nat.mul_pos hN (Nat.pos_of_ne_zero hk0)
    refine ⟨N * k * 2, I.ev (N * k * 2) (N • g x), by omega, hnp, I.tower (N * k) 2 hnk (by norm_num) hnp _, ?_⟩
    have := core (N * k * 2) 1 (by omega) hnp ⟨1, by push_cast; ring⟩
    simpa only [one_smul] using this

end GlobalTheory.UPel.HT.HeckeRoot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtHeckePointWeilPairingOrthogonalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sqrt_heckePoint_weilPairing_orthogonal : ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (K : Type) [Field K] (Q : Type) [Group Q]
    (act : D.O → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (I : GlobalTheory.UPel.HT.TateIsoO D K Q act e)
    (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 0 < N → N.Coprime p →
    (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ x : D.La,
    ∃ (n : ℕ) (h' : Q), 0 < n ∧ n.Coprime p ∧ h' ^ 2 = I.ev (N * k) (N • g x) ∧ (h' ^ (k ^ 2 / c)) ^ n = 1 ∧
      ∀ z : Q, z ^ n = 1 → e n (h' ^ (k ^ 2 / c)) z 1 := by
  first | (exact @GlobalTheory.UPel.HT.HeckeRoot.sqrt_hecke_point_weil_orthogonal) | (exact GlobalTheory.UPel.HT.HeckeRoot.sqrt_hecke_point_weil_orthogonal) | (intros; apply GlobalTheory.UPel.HT.HeckeRoot.sqrt_hecke_point_weil_orthogonal  <;> assumption)
end
end
