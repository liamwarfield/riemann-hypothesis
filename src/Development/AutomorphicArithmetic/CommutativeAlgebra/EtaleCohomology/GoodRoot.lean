module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
noncomputable section
open IsLocalRing

namespace UpperTheory.Et

structure TC (A D : Type) [CommRing A] [CommRing D] [Algebra A D] where
  B : Subalgebra A D
  C : Subalgebra A D
  t : D
  s : D
  ts : t * s = 1
  tB : t ∈ B
  sC : s ∈ C
  locB : ∀ x, ∃ k : ℕ, t ^ k * x ∈ B
  locC : ∀ x, ∃ k : ℕ, s ^ k * x ∈ C

variable {A D : Type} [CommRing A] [CommRing D] [Algebra A D]

def TC.Int (T : TC A D) : Prop :=
  (∀ x ∈ T.B, IsIntegral (Algebra.adjoin A {T.t}) x) ∧ ∀ x ∈ T.C, IsIntegral (Algebra.adjoin A {T.s}) x

def TC.Fin (T : TC A D) : Prop :=
  ∃ X : Finset D, (∀ x ∈ X, x ∈ T.B) ∧ ∀ b ∈ T.B, b ∈ Submodule.span A {y | ∃ x ∈ X, ∃ i : ℕ, y = T.t ^ i * x}

def TC.S (T : TC A D) (j : ℕ) : Submodule A D :=
  Subalgebra.toSubmodule T.B ⊓ (Subalgebra.toSubmodule T.C).comap (LinearMap.mulLeft A (T.s ^ j))

def TC.Coord (T : TC A D) : Prop :=
  ∃ (ι : Type) (β : Module.Basis ι A D) (U : Set ι) (V : ℕ → Set ι), Subalgebra.toSubmodule T.B = Submodule.span A (β '' U) ∧
    ∀ j, (Subalgebra.toSubmodule T.C).comap (LinearMap.mulLeft A (T.s ^ j)) = Submodule.span A (β '' V j) ∧ (U ∩ V j).Finite

def mm [IsLocalRing A] (S : Subalgebra A D) : Submodule A D := maximalIdeal A • Subalgebra.toSubmodule S

def Roots (S : Subalgebra A D) : Prop := ∀ p : Polynomial S, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0

def GoodRoot (q : ℕ) {S : Type} [CommRing S] (ζ : S) : Prop :=
  ζ ^ q = 1 ∧ (∀ a b : ZMod q, a ≠ b → IsUnit (ζ ^ a.val - ζ ^ b.val)) ∧
    ∀ (S' : Type) [CommRing S'] (φ : S →+* S') (x : S'), x ^ q - 1 = ∏ a ∈ Finset.range q, (x - φ ζ ^ a)

end UpperTheory.Et

end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.ZeroPull
noncomputable section

open CategoryTheory

namespace UpperTheory.Ru.crystallineComparison

variable {C : Type 1} [Category.{0} C]

structure Fam (A : C) : Type 1 where
  ι : Type
  [fin : Fintype ι]
  B : ι → C
  f : ∀ i, A ⟶ B i

attribute [instance] Fam.fin


variable (C) in
structure Parts where
  Cov : ∀ {A : C}, Fam A → Prop
  triv : ∀ A : C, Cov (⟨Unit, fun _ => A, fun _ => 𝟙 A⟩ : Fam A)
  pull : ∀ {A A' : C} (φ : A ⟶ A') (S : Fam A), Cov S → ∃ (B' : S.ι → C) (f' : ∀ i, A' ⟶ B' i) (ψ : ∀ i, S.B i ⟶ B' i),
    Cov (⟨S.ι, B', f'⟩ : Fam A') ∧ ∀ i, S.f i ≫ ψ i = φ ≫ f' i
  trans : ∀ {A : C} (S : Fam A) (T : ∀ i, Fam (S.B i)), Cov S → (∀ i, Cov (T i)) →
    Cov (⟨Σ i, (T i).ι, fun x => (T x.1).B x.2, fun x => S.f x.1 ≫ (T x.1).f x.2⟩ : Fam A)
  epi : ∀ {A : C} (S : Fam A), Cov S → ∀ i, Epi (S.f i)
  disj : ∀ {A : C} (S : Fam A), Cov S → ∀ {i j : S.ι}, i ≠ j → ∀ {X : C} (h : S.B i ⟶ X) (h' : S.B j ⟶ X),
    S.f i ≫ h = S.f j ≫ h' → Cov (⟨Empty, fun e => e.elim, fun e => e.elim⟩ : Fam X)

abbrev Coef (C : Type 1) [Category.{0} C] := C ⥤ AddCommGrpCat.{1}

def Parts.Add (Pa : Parts C) (F : Coef C) : Prop :=
  ∀ (A : C) (S : Fam A), Pa.Cov S → Function.Bijective fun (x : F.obj A) (i : S.ι) => (F.map (S.f i)).hom x

def Sec (P : C ⥤ Type) (F : Coef C) : AddSubgroup (∀ A : C, P.obj A → F.obj A) where
  carrier := {c | ∀ {A B : C} (φ : A ⟶ B) (y : P.obj A), (F.map φ).hom (c A y) = c B (P.map φ y)}
  zero_mem' := by intro A B φ y; simp
  add_mem' := by intro a b ha hb A B φ y; simp [ha φ y, hb φ y]
  neg_mem' := by intro a ha A B φ y; simp [ha φ y]


variable (C) in
structure Theory where
  H : (C ⥤ Type) → Coef C → ℕ → Type 1
  [ab : ∀ P F j, AddCommGroup (H P F j)]
  pull : ∀ {Q P : C ⥤ Type} (_ : Q ⟶ P) (F : Coef C) (j : ℕ), H P F j →+ H Q F j
  map : ∀ (P : C ⥤ Type) {F G : Coef C} (_ : F ⟶ G) (j : ℕ), H P F j →+ H P G j
  pull_map : ∀ {Q P : C ⥤ Type} (u : Q ⟶ P) {F G : Coef C} (α : F ⟶ G) (j : ℕ) (x : H P F j),
    pull u G j (map P α j x) = map Q α j (pull u F j x)
  δ : ∀ (P : C ⥤ Type) (S : ShortComplex (Coef C)), S.ShortExact → ∀ j : ℕ, H P S.X₃ j →+ H P S.X₁ (j + 1)
  pull_δ : ∀ {Q P : C ⥤ Type} (u : Q ⟶ P) (S : ShortComplex (Coef C)) (h : S.ShortExact) (j : ℕ) (x : H P S.X₃ j),
    pull u S.X₁ (j + 1) (δ P S h j x) = δ Q S h j (pull u S.X₃ j x)
  ex₃ : ∀ (P : C ⥤ Type) (S : ShortComplex (Coef C)) (h : S.ShortExact) (j : ℕ), Function.Exact (map P S.g j) (δ P S h j)
  ex₁ : ∀ (P : C ⥤ Type) (S : ShortComplex (Coef C)) (h : S.ShortExact) (j : ℕ), Function.Exact (δ P S h j) (map P S.f (j + 1))
  zero : ∀ (P : C ⥤ Type) (F : Coef C), H P F 0 ≃+ Sec P F
  zero_pull : ∀ {Q P : C ⥤ Type} (u : Q ⟶ P) (F : Coef C) (x : H P F 0) (A : C) (y : Q.obj A),
    (zero Q F (pull u F 0 x)).1 A y = (zero P F x).1 A (u.app A y)
  zero_map : ∀ (P : C ⥤ Type) {F G : Coef C} (α : F ⟶ G) (x : H P F 0) (A : C) (y : P.obj A),
    (zero P G (map P α 0 x)).1 A y = (α.app A).hom ((zero P F x).1 A y)
  inj : ∀ (P : C ⥤ Type) (K : Coef C), Injective K → ∀ j : ℕ, Subsingleton (H P K (j + 1))

attribute [instance] Theory.ab

def Parts.LocZero (Pa : Parts C) {Q P : C ⥤ Type} {I : Type} [Fintype I] (a : I → ℤ) (u : I → (Q ⟶ P)) : Prop :=
  ∀ (A : C) (y : Q.obj A), ∃ S : Fam A, Pa.Cov S ∧ ∀ s,
    ∑ i, Finsupp.single ((u i).app _ (Q.map (S.f s) y)) (a i) = 0 ∨ Pa.Cov (⟨Empty, fun e => e.elim, fun e => e.elim⟩ : Fam (S.B s))

def Parts.LocTrans (Pa : Parts C) {Q P : C ⥤ Type} (p : Q ⟶ P) {I : Type} [Fintype I] (g : I → (Q ⟶ Q)) : Prop :=
  (∀ i, g i ≫ p = p) ∧ (∀ A, Function.Surjective (p.app A)) ∧
  ∀ (A : C) (y y' : Q.obj A), p.app A y = p.app A y' → ∃ S : Fam A, Pa.Cov S ∧ ∀ s,
    (Finset.univ.val.map fun i => (g i).app _ (Q.map (S.f s) y)) = Finset.univ.val.map fun i => (g i).app _ (Q.map (S.f s) y')

def Emb : Prop := ∀ (C : Type 1) [Category.{0} C] (Pa : Parts C) (F : Coef C), Pa.Add F →
  ∃ (K : Coef C) (ι : F ⟶ K), Mono ι ∧ Injective K ∧ Pa.Add K

def QuotAdd : Prop := ∀ (C : Type 1) [Category.{0} C] (Pa : Parts C) (S : ShortComplex (Coef C)), S.ShortExact →
  Pa.Add S.X₁ → Pa.Add S.X₂ → Pa.Add S.X₃

def LocSum : Prop := ∀ (C : Type 1) [Category.{0} C] (Pa : Parts C) (T : Theory C) (F : Coef C), Pa.Add F →
  ∀ (Q P : C ⥤ Type) (I : Type) [Fintype I] (a : I → ℤ) (u : I → (Q ⟶ P)), Pa.LocZero a u →
  ∀ (j : ℕ) (x : T.H P F j), ∑ i, a i • T.pull (u i) F j x = 0

def LocAvg : Prop := ∀ (C : Type 1) [Category.{0} C] (Pa : Parts C) (T : Theory C) (F : Coef C), Pa.Add F →
  ∀ (Q P : C ⥤ Type) (p : Q ⟶ P) (I : Type) [Fintype I] (g : I → (Q ⟶ Q)), Pa.LocTrans p g →
  ∀ (j : ℕ) (x : T.H P F j), T.pull p F j x = 0 → Fintype.card I • x = 0

end UpperTheory.Ru.crystallineComparison
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NoethSp
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ZariskiNoetherianInduction
theorem UpperTheory.Reformulated.B.ZariskiNoetherianInduction.noetherian_induction_zariski :
    ∀ (k : Type) [inst : Field k] (n : ℕ) (Q : Set (Fin n → k) → Prop),
    Q ∅ →
      (∀ (s t : Set (Fin n → k)), s ⊆ t → Q t → Q s) →
        (∀ (s t : Set (Fin n → k)), Q s → Q t → Q (s ∪ t)) →
          (∀ (I : Ideal (MvPolynomial (Fin n) k)),
              I.IsPrime →
                ∃ g ∉ I,
                  Q
                    {c : Fin n → k |
                      (∀ p ∈ I, (MvPolynomial.eval c : MvPolynomial (Fin n) k → k) p = (0 : k)) ∧
                        (MvPolynomial.eval c : MvPolynomial (Fin n) k → k) g ≠ (0 : k)}) →
            Q Set.univ := by
  intro k inst n Q h0 hmono hunion hprime
  have key : ∀ I : Ideal (MvPolynomial (Fin n) k),
      Q {c : Fin n → k | ∀ p ∈ I, MvPolynomial.eval c p = 0} := by
    intro I
    induction I using IsNoetherian.induction with
    | _ I ih =>
      have step : ∀ g : MvPolynomial (Fin n) k, g ∉ I →
          Q {c : Fin n → k | (∀ p ∈ I, MvPolynomial.eval c p = 0) ∧
            MvPolynomial.eval c g = 0} := by
        intro g hg
        have hlt : I < I ⊔ Ideal.span {g} := by
          refine lt_of_le_of_ne le_sup_left ?_
          intro h
          apply hg
          rw [h]
          exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self g)
        refine hmono _ _ ?_ (ih _ hlt)
        rintro c ⟨hc, hcg⟩
        have hle : I ⊔ Ideal.span {g} ≤ RingHom.ker (MvPolynomial.eval c) := by
          refine sup_le (fun p hp => (RingHom.mem_ker).2 (hc p hp)) ?_
          rw [Ideal.span_singleton_le_iff_mem]
          exact (RingHom.mem_ker).2 hcg
        exact fun p hp => (RingHom.mem_ker).1 (hle hp)
      by_cases hP : Ideal.IsPrime I
      · obtain ⟨g, hg, hQ⟩ := hprime I hP
        refine hmono _ _ ?_ (hunion _ _ hQ (step g hg))
        intro c hc
        by_cases hcg : MvPolynomial.eval c g = 0
        · exact Or.inr ⟨hc, hcg⟩
        · exact Or.inl ⟨hc, hcg⟩
      · rcases Ideal.not_isPrime_iff.1 hP with htop | ⟨x, hx, y, hy, hxy⟩
        · refine hmono _ _ ?_ h0
          intro c hc
          have h1 := hc 1 (htop ▸ Submodule.mem_top)
          simp at h1
        · refine hmono _ _ ?_ (hunion _ _ (step x hx) (step y hy))
          intro c hc
          have h1 := hc _ hxy
          rw [map_mul] at h1
          rcases mul_eq_zero.1 h1 with h | h
          · exact Or.inl ⟨hc, h⟩
          · exact Or.inr ⟨hc, h⟩
  refine hmono _ _ ?_ (key ⊥)
  intro c _ p hp
  rw [(Ideal.mem_bot).1 hp, map_zero]
end

open TopologicalSpace PrimeSpectrum

theorem UpperTheory.Et.noethSp :
    ∀ (k : Type) [Field k] (n : ℕ) (P : Set (Fin n → k) → Prop), P ∅ → (∀ s t, s ⊆ t → P t → P s) → (∀ s t, P s → P t → P (s ∪ t)) → (∀ I : Ideal (MvPolynomial (Fin n) k), I.IsPrime → ∃ g, g ∉ I ∧ P ({c | ∀ p ∈ I, MvPolynomial.eval c p = 0} ∩ {c | MvPolynomial.eval c g ≠ 0})) → P Set.univ :=
  _root_.UpperTheory.Reformulated.B.ZariskiNoetherianInduction.noetherian_induction_zariski
end
