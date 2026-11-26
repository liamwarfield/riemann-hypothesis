module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceRestrictionExistsPow
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.RootStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.CoeffLgPcurveTop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.GeomSumRoot
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfSubMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial

namespace GlobalTheory.EtC.GmStep

variable (R : Type) [CommRing R]

def rowD (E : Spc) (F : Shv R) (s : ℤ) (p : ℕ) :
    H R (disc.obj (E.obj (op ⦋p⦌))) F s →+ H R (disc.obj (E.obj (op ⦋p + 1⦌))) F s :=
  ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) • pull R (disc.map (E.δ j)) F s

def RowExact (E : Spc) (F : Shv R) (s : ℤ) (p : ℕ) : Prop :=
  ∀ y : H R (disc.obj (E.obj (op ⦋p + 1⦌))) F s, rowD R E F s (p + 1) y = 0 → ∃ z, rowD R E F s p z = y

variable {R}

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
private theorem map_rowDifferential_of_commute_faces_lemma {E E' : _root_.GlobalTheory.EtC.Spc}
    {F F' : _root_.GlobalTheory.EtC.Shv R} {s s' : ℤ}
    (φ : ∀ p : ℕ, _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s →+
      _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E'.obj (op ⦋p⦌))) F' s')
    (hc : ∀ (p : ℕ) (j : Fin (p + 2))
      (y : _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s),
      φ (p + 1) (_root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E.δ j)) F s y) =
        _root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E'.δ j)) F' s' (φ p y))
    (p : ℕ) (y : _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s) :
    φ (p + 1) (_root_.GlobalTheory.EtC.GmStep.rowD R E F s p y) =
      _root_.GlobalTheory.EtC.GmStep.rowD R E' F' s' p (φ p y) := by
  change φ (p + 1) ((AddMonoidHom.eval y) (∑ j : Fin (p + 2),
      ((-1 : ℤ) ^ (j : ℕ)) • pull R (disc.map (E.δ j)) F s)) =
    (AddMonoidHom.eval (φ p y)) (∑ j : Fin (p + 2),
      ((-1 : ℤ) ^ (j : ℕ)) • pull R (disc.map (E'.δ j)) F' s')
  simp only [map_sum, map_zsmul]
  exact Finset.sum_congr rfl fun j _ => congrArg (fun x => ((-1 : ℤ) ^ (j : ℕ)) • x) (hc p j y)


open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.rowExact_transfer {E E' : _root_.GlobalTheory.EtC.Spc}
    {F F' : _root_.GlobalTheory.EtC.Shv R} {s s' : ℤ}
    (φ : ∀ p : ℕ, _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s →+
      _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E'.obj (op ⦋p⦌))) F' s')
    (hφ : ∀ p, Function.Bijective (φ p))
    (hc : ∀ (p : ℕ) (j : Fin (p + 2))
      (y : _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s),
      φ (p + 1) (_root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E.δ j)) F s y) =
        _root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E'.δ j)) F' s' (φ p y))
    (p : ℕ) (h : _root_.GlobalTheory.EtC.GmStep.RowExact R E F s p) : _root_.GlobalTheory.EtC.GmStep.RowExact R E' F' s' p := by
  intro y' hy'
  obtain ⟨y, rfl⟩ := (hφ (p + 1)).2 y'
  have hy : _root_.GlobalTheory.EtC.GmStep.rowD R E F s (p + 1) y = 0 := by
    apply (hφ (p + 1 + 1)).1
    rw [map_rowDifferential_of_commute_faces_lemma φ hc, hy', map_zero]
  obtain ⟨z, rfl⟩ := h y hy
  exact ⟨φ p z, (map_rowDifferential_of_commute_faces_lemma φ hc p z).symm⟩

def laurentMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : LaurentPolynomial A →+* LaurentPolynomial B :=
  LaurentPolynomial.eval₂ ((LaurentPolynomial.C : B →+* LaurentPolynomial B).comp f) (laurentVarUnit B)

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_C {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    _root_.GlobalTheory.EtC.GmStep.laurentMap f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a) := by
  simp [_root_.GlobalTheory.EtC.GmStep.laurentMap, LaurentPolynomial.eval₂_C]

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_T {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (m : ℤ) :
    _root_.GlobalTheory.EtC.GmStep.laurentMap f (LaurentPolynomial.T m) = LaurentPolynomial.T m := by
  have hu : ((_root_.GlobalTheory.EtC.laurentVarUnit B : (LaurentPolynomial B)ˣ) :
      LaurentPolynomial B) = LaurentPolynomial.T 1 := rfl
  have hinv : (((_root_.GlobalTheory.EtC.laurentVarUnit B)⁻¹ : (LaurentPolynomial B)ˣ) :
      LaurentPolynomial B) = LaurentPolynomial.T (-1) := by
    rw [← Units.inv_mul_cancel_left (_root_.GlobalTheory.EtC.laurentVarUnit B)
      (LaurentPolynomial.T (-1)), hu, ← LaurentPolynomial.T_add]
    simp
  rw [_root_.GlobalTheory.EtC.GmStep.laurentMap, LaurentPolynomial.eval₂_T]
  refine Int.induction_on m ?_ (fun k ih => ?_) (fun k ih => ?_)
  · simp
  · rw [zpow_add_one, Units.val_mul, ih, hu, ← LaurentPolynomial.T_add]
  · rw [zpow_sub_one, Units.val_mul, ih, hinv, ← LaurentPolynomial.T_add, sub_eq_add_neg]

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_comp_C {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (_root_.GlobalTheory.EtC.GmStep.laurentMap f).comp LaurentPolynomial.C =
      (LaurentPolynomial.C : B →+* LaurentPolynomial B).comp f :=
  RingHom.ext fun a => _root_.GlobalTheory.EtC.GmStep.laurentMap_C f a

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_coeff {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (p : LaurentPolynomial A) :
    (_root_.GlobalTheory.EtC.GmStep.laurentMap f p).coeff = Finsupp.mapRange f f.map_zero p.coeff := by
  refine LaurentPolynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add (f := _), AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, hp, hq,
      Finsupp.mapRange_add (map_add f)]
  · rw [map_mul, _root_.GlobalTheory.EtC.GmStep.laurentMap_C, _root_.GlobalTheory.EtC.GmStep.laurentMap_T,
      ← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.mapRange_single]


open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_isIntegral {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.IsIntegral) : (_root_.GlobalTheory.EtC.GmStep.laurentMap f).IsIntegral := by
  letI := (_root_.GlobalTheory.EtC.GmStep.laurentMap f).toAlgebra
  intro x
  change IsIntegral (LaurentPolynomial A) x
  refine LaurentPolynomial.induction_on' x (fun p q hp hq => hp.add hq) (fun n b => ?_)
  refine IsIntegral.mul ?_ ?_
  · obtain ⟨P, hm, hP⟩ := hf b
    refine ⟨P.map LaurentPolynomial.C, hm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    change Polynomial.eval₂ ((_root_.GlobalTheory.EtC.GmStep.laurentMap f).comp LaurentPolynomial.C)
      (LaurentPolynomial.C b) P = 0
    rw [_root_.GlobalTheory.EtC.GmStep.laurentMap_comp_C, ← Polynomial.hom_eval₂, hP, map_zero]
  · rw [← _root_.GlobalTheory.EtC.GmStep.laurentMap_T f n]
    exact isIntegral_algebraMap


open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_ker {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (hk : RingHom.ker f ≤ nilradical A) :
    RingHom.ker (_root_.GlobalTheory.EtC.GmStep.laurentMap f) ≤ nilradical (LaurentPolynomial A) := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  have hc : ∀ n, f (x.coeff n) = 0 := by
    intro n
    have h := congrArg (fun g => g n) (_root_.GlobalTheory.EtC.GmStep.laurentMap_coeff f x)
    rw [hx] at h
    simpa using h.symm
  rw [← AddMonoidAlgebra.sum_coeff_single x, Finsupp.sum]
  refine Ideal.sum_mem _ fun n _ => ?_
  rw [LaurentPolynomial.single_eq_C_mul_T]
  refine Ideal.mul_mem_right _ _ ?_
  exact mem_nilradical.mpr ((mem_nilradical.mp (hk (RingHom.mem_ker.mpr (hc n)))).map _)


open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.spec_integral_surj {A B : Type} [CommRing A] [CommRing B]
    (φ : A →+* B) (hi : φ.IsIntegral) (hk : RingHom.ker φ ≤ nilradical A) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) := by
  refine ⟨IsIntegralHom.SpecMap_iff.mpr hi, ⟨?_⟩⟩
  letI := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hi⟩
  intro P
  haveI := P.isPrime
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P.asIdeal (⊥ : Ideal B)
    (fun a ha => nilradical_le_prime P.asIdeal
      (hk (RingHom.mem_ker.mpr (Ideal.mem_bot.mp (Ideal.mem_comap.mp ha)))))
  refine ⟨⟨Q, hQ⟩, ?_⟩
  change PrimeSpectrum.comap φ ⟨Q, hQ⟩ = P
  exact PrimeSpectrum.ext hQP

variable (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']

abbrev baseHom : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A A'))

abbrev laurentHom : Spec (CommRingCat.of (LaurentPolynomial A')) ⟶ Spec (CommRingCat.of (LaurentPolynomial A)) :=
  Spec.map (CommRingCat.ofHom (laurentMap (algebraMap A A')))

def constSq : Arrow.mk (yoneda.map (laurentHom A A')) ⟶ Arrow.mk (yoneda.map (baseHom A A')) :=
  Arrow.homMk (yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : A' →+* LaurentPolynomial A'))))
    (yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : A →+* LaurentPolynomial A)))) (by
      simp only [Arrow.mk_hom, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [laurentMap_comp_C])

def cechC : cech (laurentHom A A') ⟶ cech (baseHom A A') := Arrow.mapCechNerve (constSq A A')

def augK (k : ℕ) : disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌)) ⟶ sch.obj (Spec (CommRingCat.of (LaurentPolynomial A))) :=
  disc.map ((cechAug (laurentHom A A')).app (op ⦋k⦌))

def rowOne (q : ℕ) (i : ℤ) (k : ℕ) :
    Ht q (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) 0 (i - 1) →+ Ht q (disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌))) 1 i where
  toFun a := (cup q (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q (i - 1)) 0 a)
    (pull _ (augK A A' k) (tw q 1) 1 (kum q (laurentVar A)))).cast (by ring) (by ring)
  map_zero' := by simp only [map_zero, AddMonoidHom.zero_apply]; exact GmPhi.cast_zero _ _
  map_add' a b := by simp only [map_add (f := _), AddMonoidHom.add_apply]; exact GmPhi.cast_add _ _ _ _

end GlobalTheory.EtC.GmStep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyLongExactFirstOfInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyLongExactFirstOfInjective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LesFirst

section
variable {R : Type} [CommRing R]

theorem ofHom_comp_comp {K L M I : Cx R} (φ : K ⟶ L) (ψ : L ⟶ M) {n : ℤ} (z : Cochain M I n) :
    (Cochain.ofHom φ).comp ((Cochain.ofHom ψ).comp z (zero_add n)) (zero_add n) =
      (Cochain.ofHom (φ ≫ ψ)).comp z (zero_add n) := by
  ext p q hpq; simp

theorem δ_ofHom_comp' {K L I : Cx R} (φ : K ⟶ L) {n m : ℤ} (z : Cochain L I n) :
    δ n m ((Cochain.ofHom φ).comp z (zero_add n)) = (Cochain.ofHom φ).comp (δ n m z) (zero_add m) := by
  by_cases h : n + 1 = m
  · rw [δ_comp _ _ (zero_add n) 1 m m h (zero_add 1) h]; simp
  · simp [δ_shape _ _ h]

theorem cpull_mk {K L I : Cx R} (φ : K ⟶ L) {n : ℤ} (z : Cocycle L I n) :
    cpull φ I n (CohomologyClass.mk z) = CohomologyClass.mk (zcomp (Cocycle.ofHom φ) z (zero_add n)) := rfl

theorem cpull_comp {K L M I : Cx R} (φ : K ⟶ L) (ψ : L ⟶ M) (n : ℤ) (x : CohomologyClass M I n) :
    cpull φ I n (cpull ψ I n x) = cpull (φ ≫ ψ) I n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  exact congrArg CohomologyClass.mk (Cocycle.ext (ofHom_comp_comp φ ψ x.1))

theorem cpull_zero' {K L I : Cx R} (n : ℤ) (x : CohomologyClass L I n) :
    cpull (0 : K ⟶ L) I n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [cpull_mk, ← CohomologyClass.mk_zero]
  exact congrArg CohomologyClass.mk (Cocycle.ext (by simp [zcomp]))

variable {I : Cx R} (S : ShortComplex (Cx R))

def Snake {n : ℤ} (a : Cochain S.X₁ I n) (c : Cochain S.X₃ I (n + 1)) : Prop :=
  ∃ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = a ∧
    (Cochain.ofHom S.g).comp c (zero_add (n + 1)) = δ n (n + 1) b

theorem fg_zero {n : ℤ} (e : Cochain S.X₃ I n) :
    (Cochain.ofHom S.f).comp ((Cochain.ofHom S.g).comp e (zero_add n)) (zero_add n) = 0 := by
  rw [ofHom_comp_comp, S.zero]; simp

theorem snake_add {n : ℤ} {a a' : Cochain S.X₁ I n} {c c' : Cochain S.X₃ I (n + 1)}
    (h : Snake S a c) (h' : Snake S a' c') : Snake S (a + a') (c + c') := by
  obtain ⟨b, hb, hc⟩ := h; obtain ⟨b', hb', hc'⟩ := h'
  exact ⟨b + b', by rw [Cochain.comp_add, hb, hb'], by rw [Cochain.comp_add, hc, hc', δ_add]⟩

theorem snake_sub {n : ℤ} {a a' : Cochain S.X₁ I n} {c c' : Cochain S.X₃ I (n + 1)}
    (h : Snake S a c) (h' : Snake S a' c') : Snake S (a - a') (c - c') := by
  obtain ⟨b, hb, hc⟩ := h; obtain ⟨b', hb', hc'⟩ := h'
  exact ⟨b - b', by rw [Cochain.comp_sub, hb, hb'], by rw [Cochain.comp_sub, hc, hc', δ_sub]⟩

variable (hI : ∀ n, Injective (I.X n)) (hS : S.ShortExact)
include hI hS

theorem snake_exists {n : ℤ} (a : Cocycle S.X₁ I n) : ∃ c : Cocycle S.X₃ I (n + 1), Snake S a.1 c.1 := by
  have L := cochain_shortExact_of_injective R I hI S hS
  obtain ⟨b, hb⟩ := (L n).1 a.1
  have h1 : (Cochain.ofHom S.f).comp (δ n (n + 1) b) (zero_add (n + 1)) = 0 := by
    rw [← δ_ofHom_comp', hb]; exact a.δ_eq_zero (n + 1)
  obtain ⟨c, hc⟩ := (L (n + 1)).2.1 _ h1
  have h2 : δ (n + 1) (n + 1 + 1) c = 0 := by
    apply (L (n + 1 + 1)).2.2
    rw [← δ_ofHom_comp', hc, δ_δ]
  exact ⟨Cocycle.mk c (n + 1 + 1) rfl h2, b, hb, hc⟩

theorem snake_bdry {n m : ℤ} (hm : m + 1 = n) {a : Cochain S.X₁ I n} {c : Cochain S.X₃ I (n + 1)}
    (h : Snake S a c) (β : Cochain S.X₁ I m) (hβ : δ m n β = a) :
    ∃ e : Cochain S.X₃ I n, δ n (n + 1) e = c := by
  have L := cochain_shortExact_of_injective R I hI S hS
  obtain ⟨b, hb, hc⟩ := h
  obtain ⟨β₂, hβ₂⟩ := (L m).1 β
  have h1 : (Cochain.ofHom S.f).comp (b - δ m n β₂) (zero_add n) = 0 := by
    rw [Cochain.comp_sub, ← δ_ofHom_comp', hβ₂, hβ, hb, sub_self]
  obtain ⟨e, he⟩ := (L n).2.1 _ h1
  refine ⟨e, ?_⟩
  rw [← sub_eq_zero]
  apply (L (n + 1)).2.2
  rw [Cochain.comp_sub, ← δ_ofHom_comp', he, hc, δ_sub, δ_δ, sub_zero, sub_self]

theorem snake_unique {n : ℤ} {a : Cochain S.X₁ I n} {c c' : Cocycle S.X₃ I (n + 1)}
    (h : Snake S a c.1) (h' : Snake S a c'.1) :
    CohomologyClass.mk c = CohomologyClass.mk c' := by
  have h0 := snake_sub S h h'
  rw [sub_self] at h0
  obtain ⟨e, he⟩ := snake_bdry S hI hS (sub_add_cancel n 1) h0 0 (by simp)
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ n rfl]
  exact ⟨e, by rw [he]; rfl⟩

def conn0 (n : ℤ) (a : Cocycle S.X₁ I n) : CohomologyClass S.X₃ I (n + 1) :=
  CohomologyClass.mk (Classical.choose (snake_exists S hI hS a))

theorem etaleSnakeConnectingOnCocycles_eq {n : ℤ} (a : Cocycle S.X₁ I n) (c : Cocycle S.X₃ I (n + 1)) (h : Snake S a.1 c.1) :
    conn0 S hI hS n a = CohomologyClass.mk c :=
  snake_unique S hI hS (Classical.choose_spec (snake_exists S hI hS a)) h

def conn (n : ℤ) : CohomologyClass S.X₁ I n →+ CohomologyClass S.X₃ I (n + 1) :=
  CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (conn0 S hI hS n) (fun a a' => by
      obtain ⟨c, hc⟩ := snake_exists S hI hS a
      obtain ⟨c', hc'⟩ := snake_exists S hI hS a'
      rw [etaleSnakeConnectingOnCocycles_eq S hI hS a c hc, etaleSnakeConnectingOnCocycles_eq S hI hS a' c' hc',
        etaleSnakeConnectingOnCocycles_eq S hI hS (a + a') (c + c') (snake_add S hc hc'), CohomologyClass.mk_add]))
    (by
      intro a ha
      rw [mem_coboundaries_iff a (n - 1) (sub_add_cancel n 1)] at ha
      obtain ⟨β, hβ⟩ := ha
      obtain ⟨c, hc⟩ := snake_exists S hI hS a
      obtain ⟨e, he⟩ := snake_bdry S hI hS (sub_add_cancel n 1) hc β hβ
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, etaleSnakeConnectingOnCocycles_eq S hI hS a c hc,
        CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl]
      exact ⟨e, he⟩)

end

end GlobalTheory.EtC.LesFirst

namespace GlobalTheory.EtC


open LesFirst in
theorem longExact_first_of_injective :
    ∀ (R : Type) [CommRing R] (I : Cx R), (∀ n, Injective (I.X n)) → ∃ d : ∀ (S : ShortComplex (Cx R)), S.ShortExact → ∀ n : ℤ, CohomologyClass S.X₁ I n →+ CohomologyClass S.X₃ I (n + 1), (∀ (S : ShortComplex (Cx R)) (hS : S.ShortExact) n, Function.Exact (cpull S.g I n) (cpull S.f I n) ∧ Function.Exact (cpull S.f I n) (d S hS n) ∧ Function.Exact (d S hS n) (cpull S.g I (n + 1))) ∧ ∀ (S S' : ShortComplex (Cx R)) (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') n x, cpull φ.τ₃ I (n + 1) (d S' hS' n x) = d S hS n (cpull φ.τ₁ I n x) := by
  intro R _ I hI
  refine ⟨fun S hS n => conn S hI hS n, fun S hS n => ⟨?_, ?_, ?_⟩, ?_⟩
  · have L := cochain_shortExact_of_injective R I hI S hS
    intro y
    constructor
    · intro hy
      obtain ⟨y, rfl⟩ := y.mk_surjective
      rw [cpull_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (sub_add_cancel n 1)] at hy
      obtain ⟨β, hβ⟩ := hy
      obtain ⟨β₂, hβ₂⟩ := (L (n - 1)).1 β
      have h1 : (Cochain.ofHom S.f).comp (y.1 - δ (n - 1) n β₂) (zero_add n) = 0 := by
        rw [Cochain.comp_sub, ← δ_ofHom_comp', hβ₂, hβ]; exact sub_self _
      obtain ⟨c, hc⟩ := (L n).2.1 _ h1
      have h2 : δ n (n + 1) c = 0 := by
        apply (L (n + 1)).2.2
        rw [← δ_ofHom_comp', hc, δ_sub, δ_δ, y.δ_eq_zero, sub_zero]
      refine ⟨CohomologyClass.mk (Cocycle.mk c (n + 1) rfl h2), ?_⟩
      rw [cpull_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
        mem_coboundaries_iff _ (n - 1) (sub_add_cancel n 1)]
      refine ⟨-β₂, ?_⟩
      rw [δ_neg]
      change -(δ (n - 1) n β₂) = (Cochain.ofHom S.g).comp c (zero_add n) - y.1
      rw [hc]; abel
    · rintro ⟨x, rfl⟩
      rw [cpull_comp, S.zero, cpull_zero']
  · intro y
    constructor
    · intro hy
      obtain ⟨a, rfl⟩ := y.mk_surjective
      obtain ⟨c, b, hb, hc⟩ := snake_exists S hI hS a
      change conn0 S hI hS n a = 0 at hy
      rw [etaleSnakeConnectingOnCocycles_eq S hI hS a c ⟨b, hb, hc⟩, CohomologyClass.mk_eq_zero_iff,
        mem_coboundaries_iff _ n rfl] at hy
      obtain ⟨e, he⟩ := hy
      have h : δ n (n + 1) (b - (Cochain.ofHom S.g).comp e (zero_add n)) = 0 := by
        rw [δ_sub, δ_ofHom_comp', he, ← hc, sub_self]
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl h), ?_⟩
      rw [cpull_mk]
      refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
      change (Cochain.ofHom S.f).comp (b - (Cochain.ofHom S.g).comp e (zero_add n)) (zero_add n) = a.1
      rw [Cochain.comp_sub, fg_zero, sub_zero, hb]
    · rintro ⟨x, rfl⟩
      obtain ⟨b, rfl⟩ := x.mk_surjective
      change conn0 S hI hS n _ = 0
      rw [etaleSnakeConnectingOnCocycles_eq S hI hS _ 0 ⟨b.1, rfl, by simp⟩, CohomologyClass.mk_zero]
  · intro z
    constructor
    · intro hz
      obtain ⟨c, rfl⟩ := z.mk_surjective
      rw [cpull_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl] at hz
      obtain ⟨β, hβ⟩ := hz
      have h : δ n (n + 1) ((Cochain.ofHom S.f).comp β (zero_add n)) = 0 := by
        rw [δ_ofHom_comp', hβ]; exact fg_zero S c.1
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl h), ?_⟩
      exact etaleSnakeConnectingOnCocycles_eq S hI hS _ c ⟨β, rfl, hβ.symm⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨a, rfl⟩ := x.mk_surjective
      obtain ⟨c, hs⟩ := snake_exists S hI hS a
      change cpull S.g I (n + 1) (conn0 S hI hS n a) = 0
      rw [etaleSnakeConnectingOnCocycles_eq S hI hS a c hs, cpull_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl]
      obtain ⟨b, hb, hc⟩ := hs
      exact ⟨b, hc.symm⟩
  · intro S S' hS hS' φ n x
    obtain ⟨a, rfl⟩ := x.mk_surjective
    obtain ⟨c, b, hb, hc⟩ := snake_exists S' hI hS' a
    change cpull φ.τ₃ I (n + 1) (conn0 S' hI hS' n a) = conn0 S hI hS n _
    rw [etaleSnakeConnectingOnCocycles_eq S' hI hS' a c ⟨b, hb, hc⟩, cpull_mk,
      etaleSnakeConnectingOnCocycles_eq S hI hS _ _ ⟨(Cochain.ofHom φ.τ₂).comp b (zero_add n), ?_, ?_⟩]
    · change _ = (Cochain.ofHom φ.τ₁).comp a.1 (zero_add n)
      rw [ofHom_comp_comp, ← φ.comm₁₂, ← ofHom_comp_comp, hb]
    · change (Cochain.ofHom S.g).comp ((Cochain.ofHom φ.τ₃).comp c.1 (zero_add (n + 1))) (zero_add (n + 1)) = _
      rw [ofHom_comp_comp, ← φ.comm₂₃, ← ofHom_comp_comp, hc, δ_ofHom_comp']

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyLongExactFirstOfInjectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypercohomology_longExact_first_of_injective : ∀ (R : Type) [CommRing R] (I : Cx R), (∀ n, Injective (I.X n)) → ∃ d : ∀ (S : ShortComplex (Cx R)), S.ShortExact → ∀ n : ℤ, CohomologyClass S.X₁ I n →+ CohomologyClass S.X₃ I (n + 1), (∀ (S : ShortComplex (Cx R)) (hS : S.ShortExact) n, Function.Exact (cpull S.g I n) (cpull S.f I n) ∧ Function.Exact (cpull S.f I n) (d S hS n) ∧ Function.Exact (d S hS n) (cpull S.g I (n + 1))) ∧ ∀ (S S' : ShortComplex (Cx R)) (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') n x, cpull φ.τ₃ I (n + 1) (d S' hS' n x) = d S hS n (cpull φ.τ₁ I n x) := by
  first | (exact @GlobalTheory.EtC.longExact_first_of_injective) | (exact GlobalTheory.EtC.longExact_first_of_injective) | (intros; apply GlobalTheory.EtC.longExact_first_of_injective  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStandardOpenCoordinateRingIffLocalizationChar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStandardOpenCoordinateRingIffLocalizationChar
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

namespace GlobalTheory.PD.Loc

variable {k : Type} [Field k] {F : Type} [Field F] [Algebra k F] {d : ℕ} {x : Fin (d + 1) → F}

theorem gen_mem (I : Finset (Fin (d + 1))) {i : Fin (d + 1)} (hi : i ∈ I) (j : Fin (d + 1)) :
    x j / x i ∈ rA k x I :=
  Algebra.subset_adjoin ⟨i, hi, j, rfl⟩

theorem rA_mono {I J : Finset (Fin (d + 1))} (h : I ⊆ J) : rA k x I ≤ rA k x J :=
  Algebra.adjoin_mono fun _ ⟨i, hi, j, e⟩ => ⟨i, h hi, j, e⟩

theorem prod_mem_single (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) :
    ∏ j ∈ I, x j / x i ∈ rA k x {i} :=
  Subalgebra.prod_mem _ fun j _ => gen_mem {i} (Finset.mem_singleton_self i) j

theorem gen_mul_prod_mem (hne : ∀ l, x l ≠ 0) (I : Finset (Fin (d + 1))) (i : Fin (d + 1))
    {i' : Fin (d + 1)} (hi' : i' ∈ I) (j : Fin (d + 1)) :
    x j / x i' * ∏ l ∈ I, x l / x i ∈ rA k x {i} := by
  rw [← Finset.mul_prod_erase I (fun l => x l / x i) hi', ← mul_assoc]
  have e : x j / x i' * (x i' / x i) = x j / x i := by
    field_simp [hne i', hne i]
  rw [e]
  exact Subalgebra.mul_mem _ (gen_mem {i} (Finset.mem_singleton_self i) j)
    (Subalgebra.prod_mem _ fun l _ => gen_mem {i} (Finset.mem_singleton_self i) l)

end GlobalTheory.PD.Loc


open GlobalTheory.PD.Loc in
theorem GlobalTheory.PD.rA_eq_loc : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F),
    IsPd k x → ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → ∀ y : F,
      y ∈ rA k x I ↔ ∃ N : ℕ, y * (∏ j ∈ I, x j / x i) ^ N ∈ rA k x {i} := by
  intro k _ F _ _ d x hx I i hi y
  set P := ∏ j ∈ I, x j / x i with hP
  have hPm : P ∈ rA k x {i} := prod_mem_single I i
  constructor
  · intro hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨i', hi', j, rfl⟩ := hz
      exact ⟨1, by rw [pow_one]; exact gen_mul_prod_mem hx.ne I i hi' j⟩
    | algebraMap r => exact ⟨0, by rw [pow_zero, mul_one]; exact Subalgebra.algebraMap_mem _ r⟩
    | add a b _ _ ha hb =>
      obtain ⟨N₁, h₁⟩ := ha
      obtain ⟨N₂, h₂⟩ := hb
      refine ⟨N₁ + N₂, ?_⟩
      have e : (a + b) * P ^ (N₁ + N₂) = (a * P ^ N₁) * P ^ N₂ + (b * P ^ N₂) * P ^ N₁ := by ring
      rw [e]
      exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ h₁ (Subalgebra.pow_mem _ hPm _))
        (Subalgebra.mul_mem _ h₂ (Subalgebra.pow_mem _ hPm _))
    | mul a b _ _ ha hb =>
      obtain ⟨N₁, h₁⟩ := ha
      obtain ⟨N₂, h₂⟩ := hb
      refine ⟨N₁ + N₂, ?_⟩
      have e : (a * b) * P ^ (N₁ + N₂) = (a * P ^ N₁) * (b * P ^ N₂) := by ring
      rw [e]
      exact Subalgebra.mul_mem _ h₁ h₂
  · rintro ⟨N, hN⟩
    have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (hx.ne j) (hx.ne i)
    have hPinv : P⁻¹ ∈ rA k x I := by
      rw [hP, ← Finset.prod_inv_distrib]
      exact Subalgebra.prod_mem _ fun j hj => by rw [inv_div]; exact gen_mem I hj i
    have e : y = (y * P ^ N) * P⁻¹ ^ N := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hP0, one_pow, mul_one]
    rw [e]
    exact Subalgebra.mul_mem _ (rA_mono (Finset.singleton_subset_iff.2 hi) hN) (Subalgebra.pow_mem _ hPinv _)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStandardOpenCoordinateRingIffLocalizationCharStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_standardOpenCoordinateRing_iff_localization_chart : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → ∀ y : F, y ∈ rA k x I ↔ ∃ N : ℕ, y * (∏ j ∈ I, x j / x i) ^ N ∈ rA k x {i} := by
  first | (exact @GlobalTheory.PD.rA_eq_loc) | (exact GlobalTheory.PD.rA_eq_loc) | (intros; apply GlobalTheory.PD.rA_eq_loc  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixVariablesDeterminantPowMonomialShape
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixVariablesDeterminantPowMonomialShape
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DetPowShape

noncomputable def detZ (i : ℕ) : MvPolynomial (Σ _ : Fin i, Fin i) ℤ :=
  Matrix.det (Matrix.of fun a b : Fin i =>
    (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) ℤ))

theorem detPow_eq_map (C : Type) [Field C] (i c : ℕ) :
    detPow C i c = MvPolynomial.map (Int.castRingHom C) (detZ i ^ c) := by
  rw [map_pow, detZ, RingHom.map_det]
  unfold detPow
  congr 2
  ext a b
  simp [RingHom.mapMatrix_apply]

theorem weight_eq_sum {i : ℕ} (w : (Σ _ : Fin i, Fin i) → ℕ) (α : (Σ _ : Fin i, Fin i) →₀ ℕ) :
    Finsupp.weight w α = ∑ x, α x * w x := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [smul_eq_mul]

theorem det_wh {R : Type} [CommRing R] {i : ℕ} (w : (Σ _ : Fin i, Fin i) → ℕ)
    (hw : ∀ σ : Equiv.Perm (Fin i), ∑ j, w ⟨j, σ j⟩ = 1) :
    MvPolynomial.IsWeightedHomogeneous w (Matrix.det (Matrix.of fun a b : Fin i =>
      (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) R))) 1 := by
  rw [Matrix.det_apply']
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have hp := MvPolynomial.IsWeightedHomogeneous.prod (R := R) (w := w) Finset.univ
    (fun j => (MvPolynomial.X ⟨j, σ j⟩ : MvPolynomial (Σ _ : Fin i, Fin i) R))
    (fun j => w ⟨j, σ j⟩) (fun j _ => MvPolynomial.isWeightedHomogeneous_X R w _)
  rw [hw σ] at hp
  have hc : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Σ _ : Fin i, Fin i) R) =
      MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : R) := by simp
  simp only [Matrix.of_apply]
  rw [hc]
  simpa using hp.C_mul ((Equiv.Perm.sign σ : ℤ) : R)

theorem sum_of_mem_support {C : Type} [Field C] {i c : ℕ} (w : (Σ _ : Fin i, Fin i) → ℕ)
    (hw : ∀ σ : Equiv.Perm (Fin i), ∑ j, w ⟨j, σ j⟩ = 1) (α) (hα : α ∈ (detPow C i c).support) :
    ∑ x, α x * w x = c := by
  have h := (det_wh (R := C) w hw).pow c
  rw [← weight_eq_sum]
  have := h (MvPolynomial.mem_support_iff.1 hα)
  simpa using this

theorem detPow_shape : ∀ (C : Type) [Field C] [CharZero C] (i c : ℕ),
    (detPow C i c).IsHomogeneous (i * c) ∧ (∀ α, ∃ n : ℤ, (detPow C i c).coeff α = n) ∧
    (detPow C i c).coeff (∑ a : Fin i, Finsupp.single ⟨a, a⟩ c) = 1 ∧
    ∀ α ∈ (detPow C i c).support, (∀ a : Fin i, ∑ b : Fin i, α ⟨b, a⟩ = c) ∧
      (∀ b : Fin i, ∑ a : Fin i, α ⟨b, a⟩ = c) := by
  intro C _ _ i c
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (GlobalTheory.LeadingMinors.isHomogeneous_det_X (k := C)
      (fun a b : Fin i => (⟨b, a⟩ : Σ _ : Fin i, Fin i))).pow c
    simpa [Fintype.card_fin, detPow] using this
  · intro α
    exact ⟨(detZ i ^ c).coeff α, by rw [detPow_eq_map, MvPolynomial.coeff_map]; simp⟩
  · let f : Fin i → (Σ _ : Fin i, Fin i) := fun a => ⟨a, a⟩
    have hf : Function.Injective f := fun x y h => congrArg Sigma.fst h
    have h1 : (∑ a : Fin i, Finsupp.single (⟨a, a⟩ : Σ _ : Fin i, Fin i) c) =
        Finsupp.mapDomain f (∑ a : Fin i, Finsupp.single a c) := by
      change _ = Finsupp.mapDomain.addMonoidHom f _
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, f]
    have h2 : MvPolynomial.killCompl hf (detPow C i c) =
        MvPolynomial.monomial (∑ a : Fin i, Finsupp.single a c) 1 := by
      unfold detPow
      rw [map_pow, GlobalTheory.LeadingMinors.killCompl_det_X (k := C) hf
        (fun a b : Fin i => (⟨b, a⟩ : Σ _ : Fin i, Fin i)) id (fun a => rfl),
        MvPolynomial.monomial_pow, one_pow]
      · congr 1
        rw [Finset.smul_sum]
        simp
      · rintro a b hab ⟨x, hx⟩
        obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 hx
        exact hab ((eq_of_heq h2).symm.trans h1)
    rw [h1, ← MvPolynomial.coeff_killCompl hf, h2, MvPolynomial.coeff_monomial, if_pos rfl]
  · intro α hα
    constructor
    · intro a
      have h := sum_of_mem_support (C := C) (c := c)
        (fun x => if x.2 = a then 1 else 0) (fun σ => by
          rw [← Equiv.sum_comp σ.symm]
          simp) α hα
      rw [Fintype.sum_sigma] at h
      simpa using h
    · intro b
      have h := sum_of_mem_support (C := C) (c := c)
        (fun x => if x.1 = b then 1 else 0) (fun σ => by simp) α hα
      rw [Fintype.sum_sigma] at h
      simpa using h

end GlobalTheory.DetPowShape
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixVariablesDeterminantPowMonomialShapeStatement
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixVariablesDeterminantPow_monomial_shape : ∀ (C : Type) [Field C] [CharZero C] (i c : ℕ), (detPow C i c).IsHomogeneous (i * c) ∧ (∀ α, ∃ n : ℤ, (detPow C i c).coeff α = n) ∧ (detPow C i c).coeff (∑ a : Fin i, Finsupp.single ⟨a, a⟩ c) = 1 ∧ ∀ α ∈ (detPow C i c).support, (∀ a : Fin i, ∑ b : Fin i, α ⟨b, a⟩ = c) ∧ (∀ b : Fin i, ∑ a : Fin i, α ⟨b, a⟩ = c) := by
  first | exact @GlobalTheory.DetPowShape.detPow_shape | exact GlobalTheory.DetPowShape.detPow_shape | (intros; apply GlobalTheory.DetPowShape.detPow_shape <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistModuleFreeAndGeneratorSummand
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistModuleFreeAndGeneratorSummand
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.TwFree

variable (q : ℕ) [NeZero q] (A : Type) [CommRing A]

theorem pow_val_mul (ζ : Prim q A) (a b : (ZMod q)ˣ) :
    (ζ.1 ^ (a : ZMod q).val) ^ (b : ZMod q).val = ζ.1 ^ ((a * b : (ZMod q)ˣ) : ZMod q).val := by
  rw [← pow_mul, Units.val_mul, ZMod.val_mul, ← pow_eq_pow_mod _ ((GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q A).1 ζ)]

theorem pow_val_one (ζ : Prim q A) : ζ.1 ^ ((1 : (ZMod q)ˣ) : ZMod q).val = ζ.1 := by
  rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ((GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q A).1 ζ), pow_one]

def orbRel : Setoid (Prim q A) where
  r ζ ξ := ∃ a : (ZMod q)ˣ, ξ.1 = ζ.1 ^ (a : ZMod q).val
  iseqv :=
    { refl := fun ζ => ⟨1, (pow_val_one q A ζ).symm⟩
      symm := fun {ζ ξ} ⟨a, h⟩ => ⟨a⁻¹, by rw [h, pow_val_mul, mul_inv_cancel, pow_val_one]⟩
      trans := fun {ζ ξ η} ⟨a, h⟩ ⟨b, h'⟩ => ⟨a * b, by rw [h', h, pow_val_mul]⟩ }

abbrev Orb := Quotient (orbRel q A)

abbrev orb (ζ : Prim q A) : Orb q A := Quotient.mk (orbRel q A) ζ

def rep (O : Orb q A) : Prim q A := Quotient.out O

theorem exists_coef (ζ : Prim q A) : ∃ a : (ZMod q)ˣ, ζ.1 = (rep q A (orb q A ζ)).1 ^ (a : ZMod q).val :=
  Quotient.exact (Quotient.out_eq (orb q A ζ))

def coef (ζ : Prim q A) : (ZMod q)ˣ := (exists_coef q A ζ).choose

theorem coef_spec (ζ : Prim q A) : ζ.1 = (rep q A (orb q A ζ)).1 ^ (coef q A ζ : ZMod q).val :=
  (exists_coef q A ζ).choose_spec

variable [Nontrivial A]

theorem units_eq_of_pow (r : Prim q A) (a b : (ZMod q)ˣ)
    (h : r.1 ^ (a : ZMod q).val = r.1 ^ (b : ZMod q).val) : a = b := by
  by_contra hne
  have hm : ¬ (a : ZMod q).val ≡ (b : ZMod q).val [MOD q] := by
    intro hm
    apply hne
    apply Units.ext
    apply ZMod.val_injective
    rw [Nat.ModEq, Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at hm
    exact hm
  have hu := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q A).2.2.1 r _ _ hm
  rw [h, sub_self] at hu
  exact not_isUnit_zero hu

theorem orb_coef_of_pow (ζ ξ : Prim q A) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    orb q A ξ = orb q A ζ ∧ coef q A ξ = coef q A ζ * a := by
  have ho : orb q A ξ = orb q A ζ := (Quotient.sound (s := orbRel q A) (a := ζ) (b := ξ) ⟨a, h⟩).symm
  refine ⟨ho, units_eq_of_pow q A (rep q A (orb q A ξ)) _ _ ?_⟩
  rw [← coef_spec, h, coef_spec q A ζ, pow_val_mul, ho]

theorem orb_coef_rep (O : Orb q A) : orb q A (rep q A O) = O ∧ coef q A (rep q A O) = 1 := by
  have ho : orb q A (rep q A O) = O := Quotient.out_eq O
  refine ⟨ho, units_eq_of_pow q A (rep q A O) _ _ ?_⟩
  have h := coef_spec q A (rep q A O)
  rw [ho] at h
  rw [← h, pow_val_one]

variable (i : ℤ)

def coordMap : (Prim q A →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] (Orb q A →₀ ULift.{1} (ZMod q)) :=
  Finsupp.linearCombination _ (fun ζ => Finsupp.single (orb q A ζ) (ULift.up ((coef q A ζ ^ i : (ZMod q)ˣ) : ZMod q)))

theorem twRel_le_ker : twRel q i A ≤ LinearMap.ker (coordMap q A i) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  obtain ⟨ho, hc⟩ := orb_coef_of_pow q A ζ ξ a h
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, coordMap, Finsupp.linearCombination_single,
    Finsupp.smul_single, smul_eq_mul, one_mul, ho, hc, sub_eq_zero]
  congr 1
  apply ULift.ext
  simp [mul_zpow, mul_comm]

def coordQ : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) →ₗ[ULift.{1} (ZMod q)] (Orb q A →₀ ULift.{1} (ZMod q)) :=
  (twRel q i A).liftQ (coordMap q A i) (twRel_le_ker q A i)

def basisMap : (Orb q A →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) :=
  Finsupp.linearCombination _ (fun O => Submodule.Quotient.mk (Finsupp.single (rep q A O) 1))

theorem coordQ_mk_single (ζ : Prim q A) :
    coordQ q A i (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      Finsupp.single (orb q A ζ) (ULift.up ((coef q A ζ ^ i : (ZMod q)ˣ) : ZMod q)) := by
  simp [coordQ, coordMap, Finsupp.linearCombination_single]

def twEquiv : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) ≃ₗ[ULift.{1} (ZMod q)] (Orb q A →₀ ULift.{1} (ZMod q)) :=
  LinearEquiv.ofLinear (coordQ q A i) (basisMap q A i)
    (by
      refine Finsupp.lhom_ext' fun O => LinearMap.ext_ring ?_
      obtain ⟨ho, hc⟩ := orb_coef_rep q A O
      simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, basisMap,
        Finsupp.linearCombination_single, one_smul, coordQ_mk_single, ho, hc, one_zpow, LinearMap.id_coe, id_eq]
      rfl)
    (by
      refine Submodule.linearMap_qext _ (Finsupp.lhom_ext' fun ζ => LinearMap.ext_ring ?_)
      simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, Submodule.mkQ_apply,
        coordQ_mk_single, basisMap, Finsupp.linearCombination_single, LinearMap.id_coe, id_eq]
      rw [← Submodule.Quotient.mk_smul, Finsupp.smul_single, smul_eq_mul, mul_one, eq_comm,
        Submodule.Quotient.eq]
      exact Submodule.subset_span ⟨rep q A (orb q A ζ), ζ, coef q A ζ, coef_spec q A ζ, rfl⟩)

theorem twist_free : ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [Nontrivial A],
    Module.Free (ULift.{1} (ZMod q)) ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) ∧
    ∀ ζ : Prim q A, ∃ f : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q),
      f (Submodule.Quotient.mk (Finsupp.single ζ 1)) = 1 := by
  intro q _ i A _ _
  refine ⟨Module.Free.of_equiv (twEquiv q A i).symm, fun ζ => ?_⟩
  refine ⟨ULift.up (((coef q A ζ ^ i)⁻¹ : (ZMod q)ˣ) : ZMod q) •
    (Finsupp.lapply (orb q A ζ) ∘ₗ coordQ q A i), ?_⟩
  rw [LinearMap.smul_apply, LinearMap.comp_apply, coordQ_mk_single, Finsupp.lapply_apply,
    Finsupp.single_eq_same, smul_eq_mul]
  apply ULift.ext
  simp

end GlobalTheory.TwFree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistModuleFreeAndGeneratorSummandStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistModule_free_and_generator_summand : ∀ (q : ℕ) [NeZero q] (i : ℤ) (A : Type) [CommRing A] [Nontrivial A], Module.Free (ULift.{1} (ZMod q)) ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) ∧ ∀ ζ : Prim q A, ∃ f : ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q), f (Submodule.Quotient.mk (Finsupp.single ζ 1)) = 1 := by
  first | (exact @GlobalTheory.TwFree.twist_free) | (exact GlobalTheory.TwFree.twist_free) | (intros; apply GlobalTheory.TwFree.twist_free  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardOpenCoordinateRingIsFractionRingIsNoethe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardOpenCoordinateRingIsFractionRingIsNoethe
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD


open KaehlerDifferential in
theorem _root_.GlobalTheory.PD.rA_isFractionRing_isNoetherianRing : ∀ (k : Type) [Field k]
    (F : Type) [Field F] [Algebra k F] (d : ℕ)
    (x : Fin (d + 1) → F), _root_.GlobalTheory.PD.IsPd k x → ∀ I : Finset (Fin (d + 1)),
      I.Nonempty →
      IsFractionRing (_root_.GlobalTheory.PD.rA k x I) F ∧
        IsNoetherianRing (_root_.GlobalTheory.PD.rA k x I) := by
  intro k _ F _ _ d x hx I hI
  set S : Set F := {y | ∃ i ∈ I, ∃ j, y = x j / x i} with hS
  have hA : _root_.GlobalTheory.PD.rA k x I = Algebra.adjoin k S := rfl
  refine ⟨?_, ?_⟩
  · refine IsFractionRing.of_field _ F fun z => ?_
    obtain ⟨i, hi⟩ := hI
    have hle : IntermediateField.adjoin k (Set.range fun j : Fin d => x j.succ / x 0) ≤
        IntermediateField.adjoin k S := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, IntermediateField.mem_adjoin_iff_div]
      refine ⟨x j.succ / x i, Algebra.subset_adjoin ⟨i, hi, j.succ, rfl⟩,
        x 0 / x i, Algebra.subset_adjoin ⟨i, hi, 0, rfl⟩, ?_⟩
      have h0 := hx.ne 0
      have hi0 := hx.ne i
      field_simp
    have hz : z ∈ IntermediateField.adjoin k S := by
      apply hle
      rw [hx.gen]
      trivial
    obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
    exact ⟨⟨r, hr⟩, ⟨s, hs⟩, rfl⟩
  · have hfin : S.Finite :=
      (Set.finite_range fun q : Fin (d + 1) × Fin (d + 1) => x q.2 / x q.1).subset
        (by rintro _ ⟨i, -, j, rfl⟩; exact ⟨(i, j), rfl⟩)
    have hfg : (_root_.GlobalTheory.PD.rA k x I).FG := by
      rw [hA, ← hfin.coe_toFinset]
      exact Subalgebra.fg_adjoin_finset _
    haveI := (Subalgebra.fg_iff_finiteType _).mp hfg
    exact Algebra.FiniteType.isNoetherianRing k _

end GlobalTheory.PD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardOpenCoordinateRingIsFractionRingIsNoetheStatement
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardOpenCoordinateRing_isFractionRing_isNoetherianRing : ∀ (k : Type) [Field k] (F : Type) [Field F] [Algebra k F] (d : ℕ) (x : Fin (d + 1) → F), IsPd k x → ∀ I : Finset (Fin (d + 1)), I.Nonempty → IsFractionRing (rA k x I) F ∧ IsNoetherianRing (rA k x I) := by
  first | (exact @GlobalTheory.PD.rA_isFractionRing_isNoetherianRing) | (exact GlobalTheory.PD.rA_isFractionRing_isNoetherianRing) | (intros; apply GlobalTheory.PD.rA_isFractionRing_isNoetherianRing  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIntegralClosureAlgClosu
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIntegralClosureAlgClosu
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem aic_integralClosure_algebraicClosure :
    ∀ (D : Type) [CommRing D] [IsDomain D], AIC (integralClosure D (AlgebraicClosure (FractionRing D))) := by
  intro D _ _ p hp hd
  have hmap : (p.map (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D)))).natDegree = p.natDegree := hp.natDegree_map _
  have hdeg : (p.map (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D)))).degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (hp.map _).ne_zero, hmap]; exact_mod_cast hd.ne'
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root _ hdeg
  have hrDp : IsIntegral (integralClosure D (AlgebraicClosure (FractionRing D))) r := ⟨p, hp, by rwa [Polynomial.eval₂_eq_eval_map]⟩
  have hrD : IsIntegral D r := isIntegral_trans r hrDp
  refine ⟨⟨r, hrD⟩, ?_⟩
  apply Subtype.val_injective
  have key := Polynomial.eval₂_at_apply (p := p) (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D))) ⟨r, hrD⟩
  rw [← Polynomial.eval_map] at key
  have hr' : (p.map (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D))) (AlgebraicClosure (FractionRing D)))).eval r = 0 := hr
  exact key.symm.trans hr'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicPolynomialsHaveRootsIntegralClosureAlgClosuStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monicPolynomialsHaveRoots_integralClosure_algClosure : ∀ (D : Type) [CommRing D] [IsDomain D], AIC (integralClosure D (AlgebraicClosure (FractionRing D))) := by
  first | (exact @GlobalTheory.aic_integralClosure_algebraicClosure) | (exact GlobalTheory.aic_integralClosure_algebraicClosure) | (intros; apply GlobalTheory.aic_integralClosure_algebraicClosure  <;> assumption)
end
end
