module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationCriticalComparisonMap

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingShortExact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingShortExact
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cohomology

theorem subsingleton_H_of_ses {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
    {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃)
    (hi : ∀ T, Function.Injective (α.app T).hom)
    (he : ∀ T, Function.Exact (α.app T).hom (β.app T).hom)
    (hs : ∀ T, Function.Surjective (β.app T).hom)
    (h₂ : ∀ n, Subsingleton (CH.H F₂ n)) (h₃ : ∀ n, Subsingleton (CH.H F₃ n)) :
    ∀ n, Subsingleton (CH.H F₁ n) := by
  obtain ⟨c₁, c₂, c₃⟩ := CrystallineSemistableComparison.P.ses_cochains α β hi he hs
  obtain ⟨δ, -, hinj, -, -, hex⟩ :=
    CrystallineSemistableComparison.P.les (CH.Mor.ofNatTrans α).hom (CH.Mor.ofNatTrans β).hom c₁ c₂ c₃
  intro n
  cases n with
  | zero =>
    haveI : Subsingleton ((CH.cx F₂).H 0) := h₂ 0
    exact ⟨fun x y => hinj (Subsingleton.elim _ _)⟩
  | succ n =>
    haveI : Subsingleton ((CH.cx F₂).H (n + 1)) := h₂ (n + 1)
    haveI : Subsingleton ((CH.cx F₃).H n) := h₃ n
    have key : ∀ x : (CH.cx F₁).H (n + 1), x = 0 := fun x => by
      obtain ⟨y, rfl⟩ := (hex n x).1 (Subsingleton.elim _ _)
      rw [Subsingleton.elim y 0, map_zero]
    exact ⟨fun x y => (key x).trans (key y).symm⟩

end GlobalTheory.CompanionTheory.Cohomology
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingShortExactStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_vanishing_short_exact : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (α : F₁ ⟶ F₂)
    (β : F₂ ⟶ F₃), (∀ T, Function.Injective (α.app T).hom) → (∀ T, Function.Exact (α.app T).hom (β.app T).hom) →
    (∀ T, Function.Surjective (β.app T).hom) → (∀ n, Subsingleton (CH.H F₂ n)) → (∀ n, Subsingleton (CH.H F₃ n)) →
    ∀ n, Subsingleton (CH.H F₁ n) := by
  first | exact @GlobalTheory.CompanionTheory.Cohomology.subsingleton_H_of_ses | exact GlobalTheory.CompanionTheory.Cohomology.subsingleton_H_of_ses | (intros; apply GlobalTheory.CompanionTheory.Cohomology.subsingleton_H_of_ses <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingOfTrivialFrameStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_vanishing_of_trivial_frame : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (E : Frame (Φ := Φ) 0) (F : C ⥤ ModuleCat.{0} R),
    Subsingleton (F.obj E.D) → ∀ n, Subsingleton (CH.H F n) := by
  intro R _ C _ Φ E F hD n
  have hInitial : Limits.IsInitial E.D := by
    refine Limits.IsInitial.ofUniqueHom (fun T => Classical.choice (E.ne T)) ?_
    intro T f
    obtain ⟨g, -, hg⟩ := E.bij f (fun _ => 0) (fun i => i.elim0)
    exact (hg _ (fun i => i.elim0)).trans (hg _ (fun i => i.elim0)).symm
  obtain ⟨-, -, hex0, hex⟩ := CrystallineSemistableComparison.P.initial F E.D hInitial
  have key : ∀ x : CH.H F n, x = 0 := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 x
    refine ((CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).2.1 a ha).2 ?_
    cases n with
    | zero =>
      obtain ⟨m, hm⟩ := hex0 a ha
      rw [one_smul] at hm
      have hm0 : m = 0 := Subsingleton.elim _ _
      rw [hm0, map_zero] at hm
      exact hm.symm
    | succ n =>
      obtain ⟨y, hy⟩ := hex n a ha
      rw [one_smul] at hy
      exact ⟨y, hy⟩
  exact ⟨fun x y => by rw [key x, key y]⟩
end

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace CrystallineSemistableComparison.Pb

theorem sq_sub {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) (T : C)
    (h : a.S T ≤ b.S T) : Subsingleton ((sq a b).obj T) := by
  constructor
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  have h0 : ∀ z ∈ sqM a b T, z = 0 := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hz
    exact Ideal.Quotient.eq_zero_iff_mem.2 (h hw)
  exact Subtype.ext ((h0 x hx).trans (h0 y hy).symm)

theorem Poly.Ladder.mono {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Q : Poly Φ}
    {a b : ℤ → IdF Φ.A} {r r' : ℤ} (h : Q.Ladder a b r) (hr : r' ≤ r) : Q.Ladder a b r' :=
  ⟨h.le, fun r'' h' => h.ca r'' (h'.trans hr), fun r'' h' => h.cb r'' (h'.trans hr)⟩

theorem vanishing_of_ladder (d : ℕ) : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ)
    {a b : ℤ → IdF Φ.A} (E : Frame (Φ := Φ) d) (r : ℤ), Q.Ladder a b r →
    (∀ r', r - d ≤ r' → r' ≤ r → (a r').S E.D ≤ (b r').S E.D) → ∀ j, Subsingleton (CH.H (sq (a r) (b r)) j) := by
  induction d with
  | zero =>
    intro R _ C _ Φ Q a b E r hQ h j
    exact GlobalTheory.T.cohomology_vanishing_of_trivial_frame E (sq (a r) (b r)) (sq_sub _ _ _ (h r (by simp) le_rfl)) j
  | succ d ih =>
    intro R _ C _ Φ Q a b E r hQ h
    let σ : ∀ T : C, E.D ⟶ T := fun T => Classical.choice (E.ne T)
    obtain ⟨β, hi, hx, hs, -⟩ := GlobalTheory.T.filtration_critical_comparison_map Q E a b r (fun r' T => hQ.le r' T) (hQ.ca r le_rfl)
      (hQ.ca (r - 1) (by omega)) (hQ.cb r le_rfl) (hQ.cb (r - 1) (by omega))
    have hcut : ∀ r'' : ℤ, r'' ≤ r → r - (d + 1 : ℕ) ≤ r'' - d → ∀ j,
        Subsingleton (CH.H (Cut.Pσ Q σ ⋙ Cut.U E ⋙ sq (a r'') (b r'')) j) := by
      intro r'' hr hr' j
      have h1 : Subsingleton (CH.H (Cut.U E ⋙ sq (a r'') (b r'')) j) :=
        ih (Cut.Q1 Q) (Cut.E1 E) r'' (Cut.ladder_truncation Q (hQ.mono hr)) (fun r' h1 h2 => h r' (by omega) (by omega)) j
      exact (CrystallineSemistableComparison.P.adj (Cut.U E ⋙ sq (a r'') (b r'')) (Cut.Pσ Q σ) (Cut.U E) (Cut.adjPσ Q σ) j).2.subsingleton
    exact GlobalTheory.T.cohomology_vanishing_short_exact (Functor.whiskerLeft (Pt.Sσ σ) (Functor.whiskerRight (Cut.jNat (E := E) Q) (sq (a r) (b r))))
      (Functor.whiskerLeft (Pt.Sσ σ) β) (fun T => hi _) (fun T => hx _) (fun T => hs _)
      (hcut r le_rfl (by omega)) (hcut (r - 1) (by omega) (by omega))

end CrystallineSemistableComparison.Pb
