module

public import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.EtaleEvenCohomologyGradedCommRingOfCupRingAxioms
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.D2
namespace RingPf

variable {q : ℕ} {E : Spc}

theorem cast_heq {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i) : HEq (x.cast hn hi) x := by
  subst hn hi; rfl

theorem cast_cast {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'') (x : Ht q E n i) :
    (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4; rfl

theorem cast_zero {n i n' i' : ℤ} (hn : n = n') (hi : i = i') : (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn hi; rfl

theorem cast_add {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by
  subst hn hi; rfl

theorem cup_cast_left {n m i j n' i' : ℤ} (h1 : n = n') (h2 : i = i') (a : Ht q E n i) (b : Ht q E m j) :
    cup q (a.cast h1 h2) b = (cup q a b).cast (by rw [h1]) (by rw [h2]) := by
  subst h1 h2; rfl

theorem cup_cast_right {n m i j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (a : Ht q E n i) (b : Ht q E m j) :
    cup q a (b.cast h1 h2) = (cup q a b).cast (by rw [h1]) (by rw [h2]) := by
  subst h1 h2; rfl

theorem pull_cast {E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x) := by
  subst hn hi; rfl

abbrev A (q : ℕ) (E : Spc) (k : ℕ) : Type 1 := Ht q E (2 * (k : ℤ)) (k : ℤ)

def gmul {k l : ℕ} (a : A q E k) (b : A q E l) : A q E (k + l) :=
  (cup q a b).cast (by push_cast; ring) (by push_cast; ring)

def gone (q : ℕ) (E : Spc) : A q E 0 := (one q E).cast (by simp) (by simp)

instance : GradedMonoid.GOne (A q E) := ⟨gone q E⟩

theorem negOnePow_even (i j : ℕ) : (2 * (i : ℤ) * (2 * (j : ℤ))).negOnePow = 1 :=
  Int.negOnePow_even _ ⟨2 * i * j, by ring⟩

section
variable (hr : DivisorRingCompatibility) [NeZero q]
include hr

theorem one_cup (h : Inv q E) {n i : ℤ} (a : Ht q E n i) : cup q (one q E) a = a.cast (by ring) (by ring) :=
  (hr q E).1 h a

theorem cup_one (h : Inv q E) {n i : ℤ} (a : Ht q E n i) : cup q a (one q E) = a.cast (by ring) (by ring) := by
  rw [(hr q E).2.2 a (one q E), (hr q E).1 h, cast_cast]
  simp

theorem gmul_assoc {i j k : ℕ} (a : A q E i) (b : A q E j) (c : A q E k) :
    HEq (gmul (gmul a b) c) (gmul a (gmul b c)) := by
  simp only [gmul, cup_cast_left, cup_cast_right, cast_cast]
  rw [(hr q E).2.1 a b c, cast_cast]
  exact (cast_heq _ _ _).trans (cast_heq _ _ _).symm

theorem gmul_comm {i j : ℕ} (a : A q E i) (b : A q E j) : HEq (gmul a b) (gmul b a) := by
  simp only [gmul]
  rw [(hr q E).2.2 a b, negOnePow_even, one_smul, cast_cast]
  exact (cast_heq _ _ _).trans (cast_heq _ _ _).symm

def gcr (h : Inv q E) : DirectSum.GCommRing (A q E) :=
  letI : GradedMonoid.GMul (A q E) := ⟨gmul⟩
  {
    mul a b := gmul a b
    one := gone q E
    one_mul := by
      rintro ⟨k, a⟩
      refine Sigma.ext (zero_add k) ?_
      show HEq (gmul (gone q E) a) a
      simp only [gmul, gone, cup_cast_left]
      rw [one_cup hr h]
      simp only [cast_cast]
      exact cast_heq _ _ _
    mul_one := by
      rintro ⟨k, a⟩
      refine Sigma.ext (add_zero k) ?_
      show HEq (gmul a (gone q E)) a
      simp only [gmul, gone, cup_cast_right]
      rw [cup_one hr h]
      simp only [cast_cast]
      exact cast_heq _ _ _
    mul_assoc := by
      rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩
      exact Sigma.ext (add_assoc i j k) (gmul_assoc hr a b c)
    mul_comm := by
      rintro ⟨i, a⟩ ⟨j, b⟩
      exact Sigma.ext (add_comm i j) (gmul_comm hr a b)
    mul_zero a := by simp only [gmul, map_zero, cast_zero]
    zero_mul b := by simp only [gmul, map_zero, AddMonoidHom.zero_apply, cast_zero]
    mul_add a b c := by simp only [gmul, map_add (f := _), cast_add]
    add_mul a b c := by simp only [gmul, map_add (f := _), AddMonoidHom.add_apply, cast_add]
    natCast n := n • gone q E
    natCast_zero := zero_smul _ _
    natCast_succ n := succ_nsmul _ _
    intCast n := n • gone q E
    intCast_ofNat n := natCast_zsmul _ _
    intCast_negSucc_ofNat n := by
      show Int.negSucc n • gone q E = -((n + 1 : ℕ) • gone q E)
      rw [negSucc_zsmul]
  }
end

section
variable (hn : DivisorNaturality) (hr : DivisorRingCompatibility) [NeZero q]

abbrev ringOf (hr : DivisorRingCompatibility) (E : Spc) (h : Inv q E) : CommRing (DirectSum ℕ (A q E)) :=
  letI := gcr hr h; DirectSum.commRing (A q E)

def projOf (E : Spc) (k : ℕ) : DirectSum ℕ (A q E) →+ A q E k where
  toFun r := r k
  map_zero' := rfl
  map_add' x y := DirectSum.add_apply x y k


include hn in
def mapOf {E E' : Spc} (f : E ⟶ E') (h : Inv q E) (h' : Inv q E') :
    letI := ringOf hr E h; letI := ringOf hr E' h'; DirectSum ℕ (A q E') →+* DirectSum ℕ (A q E) :=
  letI := gcr hr h; letI := gcr hr h'
  DirectSum.toSemiring (fun k => (DirectSum.of (A q E) k).comp (pull (ZMod q) f (tw q k) (2 * (k : ℤ))))
    (by
      show DirectSum.of (A q E) 0 (pull (ZMod q) f (tw q ((0 : ℕ) : ℤ)) (2 * ((0 : ℕ) : ℤ)) (gone q E')) = 1
      rw [gone, pull_cast, (hn q).2.1 f h']
      rfl)
    (by
      intro i j a b
      simp only [AddMonoidHom.comp_apply]
      rw [DirectSum.of_mul_of]
      congr 1
      show pull (ZMod q) f _ _ (gmul a b) = gmul _ _
      simp only [gmul, pull_cast, (hn q).1 f])

include hn in
theorem mapOf_of {E E' : Spc} (f : E ⟶ E') (h : Inv q E) (h' : Inv q E') (k : ℕ) (a : A q E' k) :
    mapOf hn hr f h h' (DirectSum.of (A q E') k a) = DirectSum.of (A q E) k (pull (ZMod q) f (tw q k) (2 * (k : ℤ)) a) := by
  letI := gcr hr h; letI := gcr hr h'
  exact DirectSum.toSemiring_of _ _ _ k a

end

end RingPf

open RingPf in
theorem etale_even_cohomology_graded_commRing_of_cup_ring_axioms (hn : DivisorNaturality) (hr : DivisorRingCompatibility) : LeafRing := by
  intro q _
  exact ⟨{
    R := fun E _ => DirectSum ℕ (A q E)
    ring := fun E h => ringOf hr E h
    ι := fun {E} _ k => DirectSum.of (A q E) k
    π := fun {E} _ k => projOf E k
    map := fun f h h' => mapOf hn hr f h h'
    π_ι := fun {E} _ k a => by
      show (DirectSum.of (A q E) k a) k = a
      exact DirectSum.of_eq_same (β := A q E) k a
    ι_one := fun {E} _ => rfl
    ι_mul := fun {E} h k l a b => by
      letI := gcr hr h
      exact (DirectSum.of_mul_of (A := A q E) a b).symm
    ι_cpow := fun {E} h k x => by
      letI := gcr hr h
      induction k with
      | zero => rw [pow_zero, cpow_zero]; rfl
      | succ k ih =>
        rw [pow_succ, ← ih, cpow_succ]
        show _ = DirectSum.of (A q E) k _ * DirectSum.of (A q E) 1 _
        rw [DirectSum.of_mul_of]
        congr 1
    map_ι := fun {E E'} f h h' k a => by
      exact mapOf_of hn hr f h h' k a
    π_map := fun {E E'} f h h' k r => by
      letI := gcr hr h; letI := gcr hr h'
      induction r using DirectSum.induction_on with
      | zero => simp only [map_zero]
      | of j a =>
        show projOf E k (mapOf hn hr f h h' (DirectSum.of (A q E') j a)) = _
        rw [mapOf_of]
        show (DirectSum.of (A q E) j (pull (ZMod q) f _ _ a)) k = pull (ZMod q) f _ _ ((DirectSum.of (A q E') j a) k)
        by_cases hjk : j = k
        · subst hjk; rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
        · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hjk), DirectSum.of_eq_of_ne _ _ _ (Ne.symm hjk), map_zero]
      | add x y hx hy => simp only [map_add (f := _), hx, hy] }⟩

theorem LeafRing_of (hn : LeafA6nat) (hr : LeafA6ring) : LeafRing := etale_even_cohomology_graded_commRing_of_cup_ring_axioms hn hr

end LateralTheory.E.D2
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LocIEPf
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.LocIEPf

variable {A : Type} [CommRing A]

def DivS (S : Submonoid A) : Type := S

def val {S : Submonoid A} (s : DivS S) : A := (show S from s).1

lemma val_mem {S : Submonoid A} (s : DivS S) : val s ∈ S := (show S from s).2

instance (S : Submonoid A) : Preorder (DivS S) where
  le s t := val s ∣ val t
  le_refl s := dvd_refl _
  le_trans _ _ _ h1 h2 := dvd_trans h1 h2

def mkD {S : Submonoid A} (a : A) (h : a ∈ S) : DivS S := (⟨a, h⟩ : S)

instance (S : Submonoid A) : IsDirected (DivS S) (· ≤ ·) :=
  ⟨fun s t => ⟨mkD (val s * val t) (S.mul_mem (val_mem s) (val_mem t)),
    Dvd.intro _ rfl, Dvd.intro_left _ rfl⟩⟩

instance (S : Submonoid A) : Nonempty (DivS S) := ⟨mkD 1 S.one_mem⟩

lemma unit_of_dvd {a b : A} (h : a ∣ b) : IsUnit (algebraMap A (Localization.Away b) a) := by
  obtain ⟨c, rfl⟩ := h
  refine isUnit_of_mul_isUnit_left (y := algebraMap A (Localization.Away (a * c)) c) ?_
  rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit _

def mp {a b : A} (h : a ∣ b) : Localization.Away a →+* Localization.Away b :=
  IsLocalization.Away.lift a (unit_of_dvd h)

lemma mp_comp {a b : A} (h : a ∣ b) : (mp h).comp (algebraMap A _) = algebraMap A _ :=
  IsLocalization.lift_comp _

lemma mp_alg {a b : A} (h : a ∣ b) (x : A) : mp h (algebraMap A _ x) = algebraMap A _ x :=
  RingHom.congr_fun (mp_comp h) x

lemma ext_away {a : A} {P : Type} [CommRing P] {j k : Localization.Away a →+* P}
    (h : j.comp (algebraMap A _) = k.comp (algebraMap A _)) : j = k :=
  IsLocalization.ringHom_ext (Submonoid.powers a) h

variable (S : Submonoid A)

def F : DivS S ⥤ CommRingCat.{0} where
  obj s := CommRingCat.of (Localization.Away (val s))
  map f := CommRingCat.ofHom (mp (leOfHom f))
  map_id s := by
    ext1; apply ext_away; ext x; exact mp_alg (leOfHom (𝟙 s)) x
  map_comp f g := by
    ext1; apply ext_away; ext x
    exact (by rw [mp_alg, mp_alg, mp_alg] : mp (leOfHom (f ≫ g)) (algebraMap A _ x) =
      mp (leOfHom g) (mp (leOfHom f) (algebraMap A _ x)))

def tN : (Functor.const (DivS S)).obj (CommRingCat.of A) ⟶ F S where
  app s := CommRingCat.ofHom (algebraMap A (Localization.Away (val s)))
  naturality s t f := by
    ext1; apply RingHom.ext; intro x
    exact (mp_alg (leOfHom f) x).symm

variable (B : Type) [CommRing B] [Algebra A B] [IsLocalization S B]

def lB (s : DivS S) : Localization.Away (val s) →+* B :=
  IsLocalization.Away.lift (val s) (IsLocalization.map_units B ⟨val s, val_mem s⟩)

lemma lB_alg (s : DivS S) (x : A) : lB S B s (algebraMap A _ x) = algebraMap A B x :=
  RingHom.congr_fun (IsLocalization.lift_comp _) x

def sN : F S ⟶ (Functor.const (DivS S)).obj (CommRingCat.of B) where
  app s := CommRingCat.ofHom (lB S B s)
  naturality s t f := by
    ext1; apply ext_away; ext x
    exact (by rw [mp_alg, lB_alg, lB_alg] :
      lB S B t (mp (leOfHom f) (algebraMap A _ x)) = lB S B s (algebraMap A _ x))

lemma isColim : Nonempty (IsColimit (Cocone.mk _ (sN S B))) := by
  have : ReflectsColimitsOfShape (DivS S) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat.{0}) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)⟩
  · intro (x : B)
    obtain ⟨⟨a, m⟩, hx⟩ := IsLocalization.surj S x
    let s : DivS S := mkD (m : A) m.2
    refine ⟨s, IsLocalization.mk' (Localization.Away (val s)) a
      (⟨val s, Submonoid.mem_powers _⟩ : Submonoid.powers (val s)), ?_⟩
    change x = lB S B s _
    have hu := IsLocalization.map_units B m
    refine hu.mul_right_cancel ?_
    rw [hx]
    have h2 : algebraMap A B (m : A) = lB S B s (algebraMap A _ (val s)) := by rw [lB_alg]; rfl
    rw [h2, ← map_mul, IsLocalization.mk'_spec, lB_alg]
  · intro i (y : Localization.Away (val i)) (y' : Localization.Away (val i)) h
    change lB S B i y = lB S B i y' at h
    obtain ⟨⟨c, m⟩, hd⟩ := IsLocalization.surj (Submonoid.powers (val i)) (y - y')
    have hc : algebraMap A B c = algebraMap A B 0 := by
      have := congrArg (lB S B i) hd
      rw [map_mul, map_sub, h, sub_self, zero_mul, lB_alg] at this
      rw [map_zero]; exact this.symm
    obtain ⟨u, hu⟩ := IsLocalization.exists_of_eq (M := S) hc
    let k : DivS S := mkD (val i * (u : A)) (S.mul_mem (val_mem i) u.2)
    have hik : val i ∣ val k := Dvd.intro _ rfl
    refine ⟨k, homOfLE hik, ?_⟩
    change mp hik y = mp hik y'
    rw [← sub_eq_zero, ← map_sub]
    have hm : IsUnit (algebraMap A (Localization.Away (val k)) (m : A)) := by
      obtain ⟨n, hn⟩ := m.2
      rw [← hn, map_pow]; exact (unit_of_dvd hik).pow n
    have hck : algebraMap A (Localization.Away (val k)) c = 0 := by
      have hu' : IsUnit (algebraMap A (Localization.Away (val k)) (u : A)) :=
        unit_of_dvd (Dvd.intro_left _ rfl)
      have := congrArg (algebraMap A (Localization.Away (val k))) hu
      rw [mul_zero, map_mul, map_zero] at this
      exact (hu'.mul_right_eq_zero).1 this
    refine (hm.mul_left_eq_zero).1 ?_
    rw [← mp_alg hik, ← map_mul, hd, mp_alg, hck]

theorem LocIE_of : LateralTheory.E.t_E3Cut.LocIE := by
  intro A B _ _ _ S _
  obtain ⟨hc⟩ := isColim S B
  refine ⟨DivS S, inferInstance, inferInstance, F S, tN S, sN S B, hc, fun j => ⟨?_, ?_⟩⟩
  · change (algebraMap A (Localization.Away (val j))).Etale
    rw [RingHom.etale_algebraMap]
    exact Algebra.Etale.of_isLocalizationAway (val j)
  · ext1; ext x
    exact lB_alg S B j x

end LateralTheory.E.LocIEPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.AdjoinRootExtension
section -- merged from Development.EtaleCohomology.EtaleSheaves.AdjoinRootExtension.AdjoinRootOfInjective
noncomputable section
open Polynomial

namespace LateralTheory.E.AICExtPf

universe u

def MonP (R : Type u) [CommRing R] : Type u := {p : R[X] // p.Monic ∧ 0 < p.natDegree}

variable (R : Type u) [CommRing R]

def stepIdeal : Ideal (MvPolynomial (MonP R) R) :=
  Ideal.span (Set.range fun p : MonP R => p.1.eval₂ MvPolynomial.C (MvPolynomial.X p))

abbrev StepRing : Type u := MvPolynomial (MonP R) R ⧸ stepIdeal R

def stepHom : R →+* StepRing R := algebraMap R (StepRing R)

lemma stepHom_eq : stepHom R = (Ideal.Quotient.mk (stepIdeal R)).comp MvPolynomial.C := rfl

lemma eval_map_hom {A B : Type*} [CommRing A] [CommRing B] (P : A[X]) (g : A →+* B) (a : A) :
    (P.map g).eval (g a) = g (P.eval a) := by
  rw [eval_map, eval₂_at_apply]

lemma step_root (p : MonP R) :
    (p.1.map (stepHom R)).eval (Ideal.Quotient.mk (stepIdeal R) (MvPolynomial.X p)) = 0 := by
  rw [eval_map, stepHom_eq, ← hom_eval₂]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨p, rfl⟩)

lemma adjoinRoot_of_injective {T : Type u} [CommRing T] (q : T[X]) (hq : q.Monic)
    (hd : 0 < q.natDegree) : Function.Injective (AdjoinRoot.of q) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra h
  have h1 : AdjoinRoot.mk q (C r) = 0 := hr
  rw [AdjoinRoot.mk_eq_zero] at h1
  exact hq.not_dvd_of_natDegree_lt (by simpa using h) (by simpa using hd) h1

lemma finite_roots (F : Finset (MonP R)) : ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T),
    Function.Injective φ ∧ ∀ p ∈ F, ∃ a : T, (p.1.map φ).eval a = 0 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨R, inferInstance, RingHom.id R, Function.injective_id, by simp⟩
  | insert q F _ ih =>
    obtain ⟨T, _, φ, hφ, hF⟩ := ih
    by_cases hT : Subsingleton T
    · refine ⟨T, inferInstance, φ, hφ, fun p _ => ⟨0, Subsingleton.elim _ _⟩⟩
    haveI : Nontrivial T := not_subsingleton_iff_nontrivial.1 hT
    set q' := q.1.map φ with hq'
    have hm : q'.Monic := q.2.1.map φ
    have hd : 0 < q'.natDegree := by rw [hq', q.2.1.natDegree_map]; exact q.2.2
    refine ⟨AdjoinRoot q', inferInstance, (AdjoinRoot.of q').comp φ,
      (adjoinRoot_of_injective q' hm hd).comp hφ, ?_⟩
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · refine ⟨AdjoinRoot.root q', ?_⟩
      rw [← Polynomial.map_map, eval_map, AdjoinRoot.eval₂_root]
    · obtain ⟨a, ha⟩ := hF p hp
      refine ⟨AdjoinRoot.of q' a, ?_⟩
      rw [← Polynomial.map_map, eval_map_hom, ha, map_zero]

theorem stepHom_injective : Function.Injective (stepHom R) := by
  classical
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  have hmem : MvPolynomial.C r ∈ stepIdeal R := Ideal.Quotient.eq_zero_iff_mem.1 hr
  obtain ⟨S, hS, hx⟩ := Submodule.mem_span_finite_of_mem_span hmem
  rw [← Set.image_univ] at hS
  obtain ⟨F, -, rfl⟩ := Finset.subset_set_image_iff.1 hS
  obtain ⟨T, _, φ, hφ, hF⟩ := finite_roots R F
  let v : MonP R → T := fun p => if h : p ∈ F then (hF p h).choose else 0
  let ev := MvPolynomial.eval₂Hom φ v
  have hk : Ideal.span (↑(F.image fun p : MonP R => p.1.eval₂ MvPolynomial.C (MvPolynomial.X p)) :
      Set (MvPolynomial (MonP R) R)) ≤ RingHom.ker ev := by
    rw [Ideal.span_le]
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
    rw [SetLike.mem_coe, RingHom.mem_ker, hom_eval₂, MvPolynomial.eval₂Hom_comp_C]
    have : ev (MvPolynomial.X p) = (hF p hp).choose := by
      simp [ev, v, hp]
    rw [this, ← eval_map]
    exact (hF p hp).choose_spec
  have h0 : ev (MvPolynomial.C r) = 0 := RingHom.mem_ker.1 (hk hx)
  have : ev (MvPolynomial.C r) = φ r := by simp [ev]
  exact (injective_iff_map_eq_zero φ).1 hφ r (this ▸ h0)

theorem stepHom_isIntegral : (stepHom R).IsIntegral := by
  intro z
  change IsIntegral R z
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
  induction q using MvPolynomial.induction_on with
  | C a => exact isIntegral_algebraMap
  | add a b ha hb => rw [map_add (f := _)]; exact ha.add hb
  | mul_X a p ha =>
    rw [map_mul]
    refine ha.mul ⟨p.1, p.2.1, ?_⟩
    rw [← eval_map]
    exact step_root R p

theorem step_has_root (p : R[X]) (hp : p.Monic) (hd : 0 < p.natDegree) :
    ∃ a : StepRing R, (p.map (stepHom R)).eval a = 0 :=
  ⟨_, step_root R ⟨p, hp, hd⟩⟩

end LateralTheory.E.AICExtPf
end
end

noncomputable section
open CategoryTheory Polynomial

namespace LateralTheory.E.AICExtPf

def towerObj (C : CommRingCat.{0}) : ℕ → CommRingCat.{0}
  | 0 => C
  | n + 1 => CommRingCat.of (StepRing (towerObj C n))

def towerMap (C : CommRingCat.{0}) (n : ℕ) : towerObj C n ⟶ towerObj C (n + 1) :=
  CommRingCat.ofHom (stepHom (towerObj C n))

abbrev towerF (C : CommRingCat.{0}) : ℕ ⥤ CommRingCat.{0} := Functor.ofSequence (towerMap C)

def fm (C : CommRingCat.{0}) (i j : ℕ) (h : i ≤ j) : towerObj C i →+* towerObj C j :=
  ((towerF C).map (homOfLE h)).hom

instance (C : CommRingCat.{0}) :
    DirectedSystem (fun i => (towerObj C i : Type)) (fun i j h => fm C i j h) where
  map_self i x := by
    have h1 : (towerF C).map (homOfLE (le_refl i)) = 𝟙 _ :=
      (congrArg (towerF C).map (Subsingleton.elim _ _)).trans ((towerF C).map_id i)
    exact congrArg (fun φ : (towerF C).obj i ⟶ (towerF C).obj i => φ.hom x) h1
  map_map k j i hij hjk x := by
    show ((towerF C).map (homOfLE hij) ≫ (towerF C).map (homOfLE hjk)).hom x = _
    rw [← Functor.map_comp, homOfLE_comp]; rfl

lemma fm_succ (C : CommRingCat.{0}) (n : ℕ) (h : n ≤ n + 1) : fm C n (n + 1) h = stepHom (towerObj C n) := by
  have := Functor.ofSequence_map_homOfLE_succ (towerMap C) n
  simp only [fm]
  rw [this]; rfl

lemma fm_comp_succ (C : CommRingCat.{0}) (i j : ℕ) (h : i ≤ j) (h' : i ≤ j + 1) :
    fm C i (j + 1) h' = (stepHom (towerObj C j)).comp (fm C i j h) := by
  rw [← fm_succ C j (Nat.le_succ j)]
  show ((towerF C).map (homOfLE h')).hom =
    ((towerF C).map (homOfLE h) ≫ (towerF C).map (homOfLE (Nat.le_succ j))).hom
  rw [← Functor.map_comp, homOfLE_comp]

lemma fm_injective (C : CommRingCat.{0}) (i j : ℕ) (h : i ≤ j) : Function.Injective (fm C i j h) := by
  induction j, h using Nat.le_induction with
  | base => intro x y hxy; simpa [DirectedSystem.map_self (f := fun i j h => fm C i j h)] using hxy
  | succ j hij ih =>
    rw [fm_comp_succ C i j hij]
    exact (stepHom_injective _).comp ih

lemma fm_isIntegral (C : CommRingCat.{0}) (i j : ℕ) (h : i ≤ j) : (fm C i j h).IsIntegral := by
  induction j, h using Nat.le_induction with
  | base =>
    intro x
    have e : ∀ y, fm C i i le_rfl y = y := fun y => DirectedSystem.map_self (f := fun i j h => fm C i j h) y
    exact ⟨X - Polynomial.C x, monic_X_sub_C x, by simp [eval₂_sub, e]⟩
  | succ j hij ih =>
    rw [fm_comp_succ C i j hij]
    exact RingHom.IsIntegral.trans _ _ ih (stepHom_isIntegral _)

abbrev Lim (C : CommRingCat.{0}) : Type :=
  Ring.DirectLimit (fun i => (towerObj C i : Type)) (fun i j h => fm C i j h)

lemma of_comp (C : CommRingCat.{0}) (i j : ℕ) (h : i ≤ j) :
    (Ring.DirectLimit.of _ (fun i j h => fm C i j h) j).comp (fm C i j h) =
      Ring.DirectLimit.of _ (fun i j h => fm C i j h) i := by
  ext x
  exact Ring.DirectLimit.of_f (G := fun i => (towerObj C i : Type)) (f := fun i j h => fm C i j h) h x

theorem lim_aic (C : CommRingCat.{0}) : GlobalTheory.EtC.AIC (Lim C) := by
  intro p hp hd
  obtain ⟨n, q, hq⟩ := Ring.DirectLimit.Polynomial.exists_of p
  have hinj := Ring.DirectLimit.of_injective (fun i j h => fm C i j h) (fm_injective C) n
  have hqm : q.Monic := by
    apply hinj
    rw [← leadingCoeff_map_of_injective hinj, hq, hp.leadingCoeff, map_one]
  have hqd : 0 < q.natDegree := by
    rw [← natDegree_map_eq_of_injective hinj, hq]; exact hd
  obtain ⟨a, ha'⟩ : ∃ a : towerObj C (n + 1), (q.map (fm C n (n + 1) (Nat.le_succ n))).eval a = 0 := by
    rw [fm_succ]; exact step_has_root (towerObj C n) q hqm hqd
  refine ⟨Ring.DirectLimit.of _ (fun i j h => fm C i j h) (n + 1) a, ?_⟩
  rw [← hq, ← of_comp C n (n + 1) (Nat.le_succ n), ← Polynomial.map_map, Polynomial.eval_map,
    Polynomial.eval₂_at_apply, ha', map_zero]

theorem AICExt_of : LateralTheory.E.t_E3Cut.AICExt := by
  intro C
  refine ⟨CommRingCat.of (Lim C), CommRingCat.ofHom (Ring.DirectLimit.of _ (fun i j h => fm C i j h) 0),
    ?_, ?_, lim_aic C⟩
  · intro x
    obtain ⟨n, y, rfl⟩ := Ring.DirectLimit.exists_of x
    obtain ⟨p, hp, hy⟩ := fm_isIntegral C 0 n (Nat.zero_le n) y
    refine ⟨p, hp, ?_⟩
    change eval₂ (Ring.DirectLimit.of _ (fun i j h => fm C i j h) 0) _ p = 0
    rw [← of_comp C 0 n (Nat.zero_le n), ← hom_eval₂, hy, map_zero]
  · exact Ring.DirectLimit.of_injective (fun i j h => fm C i j h) (fm_injective C) 0

end LateralTheory.E.AICExtPf
end
end
