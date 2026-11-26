module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.LeraHirschUnitOnBlowupChart
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TracePullbackIdentity
public import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOfTwoCoversPullbackSquare

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ChernClassPullbackBlowupFirstLocusEqZero
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

noncomputable section
namespace UpperTheory.Rel1

private abbrev Ac (N : ℕ) : Act := (BC N).sub ((Q1 N).comap (βC N))

private theorem isUnit_cyclotomicPeriod_deRham {N : ℕ} {A : CommRingCat.{0}} (p : Ob (Ac N) A) :
    IsUnit ((show Um N A × Um 2 A from p.pt.1).2.1 1) := by
  have h := p.pt.2
  change IsUnit ((Um.join (show Um N A × Um 2 A from p.pt.1)).1 (Fin.last N)) at h
  simpa [Um.join] using h

private def tU {N : ℕ} {A : CommRingCat.{0}} (p : Ob (Ac N) A) : Aˣ := (isUnit_cyclotomicPeriod_deRham p).unit

private def vert {E : Spc} {N : ℕ} {T : Scheme.{0}} (x : Sx (Sp E (Ac N)) 0 T) : Ob (Ac N) Γ(T, ⊤) :=
  (show ComposableArrows (Ob (Ac N) Γ(T, ⊤)) 0 from x.2).obj 0

private def ww (E : Spc) (N : ℕ) (T : Scheme.{0}) (x : Sx (Sp E (Ac N)) 0 T) : (Γ(T, ⊤))ˣ := tU (vert x)

private theorem triv1 (E : Spc) (N : ℕ) {T' T : Scheme.{0}} (g : T' ⟶ T) (x : Sx (Sp E (Ac N)) 0 T) :
    ww E N T' (x.res g) = Units.map g.appTop.hom.toMonoidHom (ww E N T x) := by
  ext
  rfl

private theorem triv2 (E : Spc) (N : ℕ) (T : Scheme.{0}) (x : Sx (Sp E (Ac N)) 1 T) :
    lineUnit (Sp.map E (incl ((Q1 N).comap (βC N))) ≫ Sp.line E (chiB N)) x * ww E N T (x.face 0) = ww E N T (x.face 1) := by
  let c : ComposableArrows (Ob (Ac N) Γ(T, ⊤)) 1 := x.2
  let f := c.map' 0 1
  have hl : lineUnit (Sp.map E (incl ((Q1 N).comap (βC N))) ≫ Sp.line E (chiB N)) x = (show (Γ(T, ⊤))ˣ × (Γ(T, ⊤))ˣ from f.1).2 := by
    have e : lineUnit (Sp.map E (incl ((Q1 N).comap (βC N))) ≫ Sp.line E (chiB N)) x =
        Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1)
          (show (Γ(T, ⊤))ˣ from (chiB N).app Γ(T, ⊤) f.1)) := rfl
    rw [e]
    ext
    simp [Matrix.GeneralLinearGroup.scalar]
    rfl
  rw [hl]
  change _ * tU (c.obj 1) = tU (c.obj 0)
  ext
  have e := congrArg (fun p => (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from p.1).2.1 1) f.2
  change ((show (Γ(T, ⊤))ˣ × (Γ(T, ⊤))ˣ from f.1).2 : Γ(T, ⊤)) * (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from (c.obj 1).pt.1).2.1 1 =
    (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from (c.obj 0).pt.1).2.1 1
  refine Eq.trans ?_ e.symm
  rfl

end UpperTheory.Rel1
end

theorem UpperTheory.chernClass_pullback_blowupFirstLocus_eq_zero :
    ∀ (q : ℕ) [NeZero q] (N : ℕ) (E : Spc), Inv q E →
        pull _ (Sp.map E (incl ((Q1 N).comap (βC N)))) _ _ (c1 q (Sp.line E (chiB N))) = 0 := by
  intro q _ N E hE
  have hX : Inv q (Sp E (BC N)) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  have hY : Inv q (Sp E (UpperTheory.Rel1.Ac N)) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  rw [(GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 _ _ hX]
  exact UpperTheory.firstChernClass_eq_zero_of_isTrivialized q _ (UpperTheory.Rel1.ww E N) hY ⟨fun g x => UpperTheory.Rel1.triv1 E N g x, UpperTheory.Rel1.triv2 E N⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.LeraHirschChernPowersOnUnitChart
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private noncomputable def sg {N : ℕ} {A : Type} [CommRing A] (i : Fin N) (x : Um N A × Um 2 A) (h : IsUnit (x.1.1 i)) : Um 2 A :=
  Um.scale ![h.unit, 1] x.2

private theorem sg_map {N : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (i : Fin N) (x : Um N A × Um 2 A)
    (h : IsUnit (x.1.1 i)) (h' : IsUnit (((Um.map N f).obj x.1).1 i)) :
    sg i ((Um.map N f).obj x.1, (Um.map 2 f).obj x.2) h' = (Um.map 2 f).obj (sg i x h) := by
  apply Subtype.ext
  funext j
  fin_cases j <;> simp [sg, Um.scale, Um.map]

private theorem sg_act {N : ℕ} {A : Type} [CommRing A] (i : Fin N) (u : Aˣ × Aˣ) (x : Um N A × Um 2 A)
    (h : IsUnit (x.1.1 i)) (h' : IsUnit ((bAct u x).1.1 i)) :
    sg i (bAct u x) h' = Um.scale (fun _ => u.2) (sg i x h) := by
  apply Subtype.ext
  funext j
  fin_cases j
  · simp [sg, Um.scale, bAct]
    linear_combination ((u.2 : A) * (x.1.1 i) * (x.2.1 0)) * (Units.mul_inv u.1)
  · simp [sg, Um.scale, bAct]

private noncomputable def sig {N : ℕ} (i : Fin N) (Q : Pred (XC N)) (hQ : Q.Le (unitAt i)) :
    Act.Hom ((BC N).sub (Q.comap (pC N))) (XC 2) where
  d :=
    { app := fun A => TypeCat.ofHom fun x => sg (A := A) i x.1 (hQ A _ x.2)
      naturality := fun A B f => by
        ext x
        exact sg_map f.hom i x.1 (hQ A _ x.2) _ }
  g := (βC N).g
  eq A u x := sg_act (A := A) i u x.1 (hQ A _ x.2) _

private theorem etC_inv_of_hom {q : ℕ} {X Y : Spc} (f : X ⟶ Y) (h : GlobalTheory.EtC.Inv q Y) : GlobalTheory.EtC.Inv q X :=
  fun U hU => h U (hU.elim fun x => ⟨Sx.map f x⟩)

private theorem um_scale_scale_eq_of_mul_eq_one {A : Type} [CommRing A] (c d : Fin 2 → Aˣ) (h : ∀ j, c j * d j = 1)
    (w : Um 2 A) : Um.scale c (Um.scale d w) = w := by
  rw [← Um.scale_mul]
  simp only [h]
  exact Um.scale_one w

theorem UpperTheory.leraHirsch_chernPowers_on_unitChart :
    ∀ (q : ℕ) [NeZero q] (N : ℕ) (E : Spc) (i : Fin N) (Q : Pred (XC N)), Q.Le (unitAt i) → Inv q E →
        LHQ q E (pC N) (fun j : Fin 2 => 2 * (((j : ℕ) : ℤ))) (fun j : Fin 2 => ((j : ℕ) : ℤ)) (fun j => cpow q (c1 q (Sp.line E (chiB N))) j) Q := by
  intro q _ N E i Q hQ hE
  have hiso : IsIso (Sp.pair E ((pC N).sub Q) (sig i Q hQ)) := by
    apply UpperTheory.isIso_stackProductPair_of_bijective
    · intro A
      constructor
      · rintro ⟨⟨x1, x2⟩, hx⟩ ⟨⟨y1, y2⟩, hy⟩ e
        have e1 : x1 = y1 := congrArg (fun p => p.1.1) e
        have e2 : Um.scale ![(hQ A _ hx).unit, 1] x2 = Um.scale ![(hQ A _ hy).unit, 1] y2 :=
          congrArg Prod.snd e
        subst e1
        have e3 := congrArg (Um.scale ![(hQ A _ hx).unit⁻¹, 1]) e2
        rw [um_scale_scale_eq_of_mul_eq_one _ _ (by intro j; fin_cases j <;> simp <;> exact inv_mul_cancel _),
          um_scale_scale_eq_of_mul_eq_one _ _ (by intro j; fin_cases j <;> simp <;> exact inv_mul_cancel _)] at e3
        subst e3
        rfl
      · rintro ⟨⟨y1, hy1⟩, w⟩
        refine ⟨⟨(y1, Um.scale ![(hQ A _ hy1).unit⁻¹, 1] w), hy1⟩, ?_⟩
        refine Prod.ext rfl ?_
        change Um.scale ![(hQ A _ hy1).unit, 1] (Um.scale ![(hQ A _ hy1).unit⁻¹, 1] w) = w
        exact um_scale_scale_eq_of_mul_eq_one _ _ (by intro j; fin_cases j <;> simp) w
    · intro A
      constructor
      · intro g h e
        exact Prod.ext (congrArg Prod.fst e) (congrArg Prod.snd e)
      · intro p
        exact ⟨(p.1, p.2), rfl⟩
  have hS : GlobalTheory.EtC.Inv q (Sp E ((XC N).sub Q)) := etC_inv_of_hom (Sp.fst E _) hE
  have hP : Pbf q (Sp E ((XC N).sub Q)) 2 :=
    (UpperTheory.projBundleFormula_iff_pglForm q _ 2 hS).mp (UpperTheory.projectiveBundleFormula_rank_two q _ hS)
  have hX : GlobalTheory.EtC.Inv q (Sp (Sp E ((XC N).sub Q)) (XC 2)) := etC_inv_of_hom (Sp.fst _ _) hS
  have hB : GlobalTheory.EtC.Inv q (Sp E (BC N)) := etC_inv_of_hom (Sp.fst E _) hE
  have hcomm : Sp.pair E ((pC N).sub Q) (sig i Q hQ) ≫ Sp.fst (Sp E ((XC N).sub Q)) (XC 2) =
      Sp.map E ((pC N).sub Q) ≫ 𝟙 (Sp E ((XC N).sub Q)) := rfl
  have h1 := UpperTheory.lerayHirsch_of_iso_square q (Sp.fst (Sp E ((XC N).sub Q)) (XC 2)) (Sp.map E ((pC N).sub Q))
    (Sp.pair E ((pC N).sub Q) (sig i Q hQ)) (𝟙 _) hcomm _ _ _ hP
  have hline : Sp.pair E ((pC N).sub Q) (sig i Q hQ) ≫ Sp.line (Sp E ((XC N).sub Q)) (chiX 2) =
      Sp.map E (incl (Q.comap (pC N))) ≫ Sp.line E (chiB N) := rfl
  have key : ∀ j : Fin 2,
      (pull (ZMod q) (Sp.pair E ((pC N).sub Q) (sig i Q hQ)) (tw q ((j : ℕ) : ℤ)) (2 * ((j : ℕ) : ℤ)))
        (cpow q (c1 q (Sp.line (Sp E ((XC N).sub Q)) (chiX 2))) (j : ℕ)) =
      (pull (ZMod q) (Sp.map E (incl (Q.comap (pC N)))) (tw q ((j : ℕ) : ℤ)) (2 * ((j : ℕ) : ℤ)))
        (cpow q (c1 q (Sp.line E (chiB N))) (j : ℕ)) := by
    intro j
    rw [UpperTheory.pull_cupPow_eq_cupPow_pull q _ _ _ hX, UpperTheory.pull_cupPow_eq_cupPow_pull q _ _ _ hB, (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 _ _ hX,
      (GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 _ _ hB, hline]
  show LH q (Sp.map E ((pC N).sub Q)) _ _ _
  convert h1 using 2
  exact (key _).symm
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EqvTwistUnimodularUnitLocus
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

noncomputable section

namespace UpperTheory.W1

variable {q : ℕ}

private theorem cast_cast {X : Spc} {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'')
    (x : Ht q X n i) : (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4
  rfl

private theorem cup_one' [NeZero q] {X : Spc} (hX : Inv q X) {n i : ℤ} (x : Ht q X n i) :
    cup q x (one q X) = x.cast (by ring) (by ring) := by
  rw [GlobalTheory.T.tateTwistCupProduct_graded_comm q X x (one q X), (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 X hX x, cast_cast, mul_zero, Int.negOnePow_zero, one_smul]

private theorem cup_one_cast [NeZero q] {X : Spc} (hX : Inv q X) {n i m j : ℤ} (x : Ht q X n i) (hm : 0 = m) (hj : 0 = j) :
    cup q x ((one q X).cast hm hj) = x.cast (by omega) (by omega) := by
  subst hm hj
  exact cup_one' hX x

private theorem bij_of_cast {X E : Spc} (π : X ⟶ E) {n i n' i' : ℤ} (hn : n' = n) (hi : i' = i)
    (h : Function.Bijective fun x : Ht q E n' i' => (Ht.cast hn hi (pull _ π _ _ x) : Ht q X n i)) :
    Function.Bijective (pull _ π (tw q i) n) := by
  subst hn hi
  exact h

private theorem eqv_comp {R : Type} [CommRing R] {X Y Z : Spc} {f : X ⟶ Y} {g : Y ⟶ Z} {F : Shv R}
    (hf : Eqv R f F) (hg : Eqv R g F) : Eqv R (f ≫ g) F := fun n => by
  have e : (pull R (f ≫ g) F n : H R Z F n → H R X F n) = pull R f F n ∘ pull R g F n :=
    funext (pull_comp R f g F n)
  rw [e]
  exact (hf n).comp (hg n)

private theorem eqv_iso {R : Type} [CommRing R] {X Y : Spc} (f : X ⟶ Y) [IsIso f] (F : Shv R) : Eqv R f F := fun n => by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

private theorem inv_sp {E : Spc} (hE : Inv q E) (a : Act) : Inv q (Sp E a) :=
  fun U ⟨x⟩ => hE U ⟨((Sp.fst E a).app _).app _ x⟩

private theorem equiv_first_twist [NeZero q] (E : Spc) (hE : Inv q E) (i : ℤ) : Eqv _ (Sp.fst E (XC 1)) (tw q i) := by
  have hP : Pbf q E 1 := (UpperTheory.projBundleFormula_iff_pglForm q E 1 hE).1 (UpperTheory.projectiveBundleFormula_rank_one_of_homotopyInvariant q E hE)
  have hX : Inv q (Sp E (XC 1)) := inv_sp hE _
  intro n
  have h := hP n i
  have hn : n - 2 * (((0 : Fin 1) : ℕ) : ℤ) = n := by simp
  have hi : i - (((0 : Fin 1) : ℕ) : ℤ) = i := by simp
  have hform : ∀ a : ∀ j : Fin 1, Ht q E (n - 2 * ((j : ℕ) : ℤ)) (i - ((j : ℕ) : ℤ)),
      ∑ j : Fin 1, ((cup q (pull _ (Sp.fst E (XC 1)) _ _ (a j)) (cpow q (c1 q (Sp.line E (chiX 1))) j)).cast (by ring) (by ring) :
        Ht q (Sp E (XC 1)) n i) =
      Ht.cast hn hi (pull _ (Sp.fst E (XC 1)) _ _ (a 0)) := by
    intro a
    rw [Fin.sum_univ_one]
    have h0 : cpow q (c1 q (Sp.line E (chiX 1))) ((0 : Fin 1) : ℕ) = (one q _).cast (by simp) (by simp) := cpow_zero q _
    rw [h0, cup_one_cast hX, cast_cast]
  simp only [hform] at h
  refine bij_of_cast _ hn hi ?_
  let e := Equiv.piUnique fun j : Fin 1 => Ht q E (n - 2 * ((j : ℕ) : ℤ)) (i - ((j : ℕ) : ℤ))
  have e2 : ∀ x, (e.symm x) 0 = x := fun x => e.apply_symm_apply x
  have h3 := h.comp e.symm.bijective
  have h4 : ((fun a : ∀ j : Fin 1, Ht q E (n - 2 * ((j : ℕ) : ℤ)) (i - ((j : ℕ) : ℤ)) =>
      (Ht.cast hn hi (pull _ (Sp.fst E (XC 1)) _ _ (a 0)) : Ht q (Sp E (XC 1)) n i)) ∘ e.symm) =
      fun x => Ht.cast hn hi (pull _ (Sp.fst E (XC 1)) _ _ x) := by
    funext x
    simp only [Function.comp_apply]
    rw [e2]
  rw [h4] at h3
  exact h3

private def invU {A : Type} [CommRing A] (a : A) (h : IsUnit a) : A := ((h.unit⁻¹ : Aˣ) : A)

private theorem mul_invU {A : Type} [CommRing A] (a : A) (h : IsUnit a) : a * invU a h = 1 :=
  h.mul_val_inv

private theorem invU_eq {A : Type} [CommRing A] {a b : A} (h : IsUnit a) (e : a * b = 1) : invU a h = b :=
  Units.inv_eq_of_mul_eq_one_right e

private theorem um_top {N : ℕ} {A : Type} [CommRing A] (v : Fin N → A) (k : Fin N) (h : IsUnit (v k)) :
    Ideal.span (Set.range v) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨k, rfl⟩) h

private def tl {M : ℕ} {A : Type} [CommRing A] (v : Um (M + 2) A) (h : IsUnit (v.1 (Fin.last (M + 1)))) : Um (M + 1) A :=
  ⟨Fin.tail v.1, um_top _ (Fin.last M) h⟩

private def rho (M : ℕ) : Act.Hom ((XC (M + 2)).sub (Q1 (M + 1))) ((XC (M + 1)).sub (Q1 M)) where
  d :=
    { app := fun A => TypeCat.ofHom fun x => ⟨tl (A := A) x.1 x.2, x.2⟩
      naturality := fun _ _ _ => rfl }
  g := 𝟙 gmF
  eq _ _ _ := rfl

private theorem sig_nat {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a t : A) (h : IsUnit t) (h' : IsUnit (f t)) :
    f (a * invU t h) = f a * invU (f t) h' := by
  rw [map_mul, invU_eq h' (b := f (invU t h)) (by rw [← map_mul, mul_invU, map_one])]

private theorem sig_inv {A : Type} [CommRing A] (u : Aˣ) (a t : A) (h : IsUnit t) (h' : IsUnit ((u : A) * t)) :
    ((u : A) * a) * invU ((u : A) * t) h' = a * invU t h := by
  rw [invU_eq h' (b := ((u⁻¹ : Aˣ) : A) * invU t h) (by
    have e := mul_invU t h
    calc (u : A) * t * (((u⁻¹ : Aˣ) : A) * invU t h) = ((u : A) * ((u⁻¹ : Aˣ) : A)) * (t * invU t h) := by ring
      _ = 1 := by rw [e]; simp)]
  calc (u : A) * a * (((u⁻¹ : Aˣ) : A) * invU t h) = ((u : A) * ((u⁻¹ : Aˣ) : A)) * (a * invU t h) := by ring
    _ = a * invU t h := by simp

private def sig (M : ℕ) : Act.Hom ((XC (M + 2)).sub (Q1 (M + 1))) affC where
  d :=
    { app := fun A => TypeCat.ofHom fun x =>
        (show Um (M + 2) A from x.1).1 0 * invU _ x.2
      naturality := fun A B f => by
        ext x
        exact (sig_nat f.hom _ _ x.2 _).symm }
  g := { app := fun A => GrpCat.ofHom 1, naturality := fun _ _ _ => rfl }
  eq A u x := sig_inv (A := A) u _ _ x.2 _

private theorem bij_plain (M : ℕ) (A : Type) [CommRing A] :
    Function.Bijective (fun x : {v : Um (M + 2) A // IsUnit (v.1 (Fin.last (M + 1)))} =>
      (((⟨tl x.1 x.2, x.2⟩ : {w : Um (M + 1) A // IsUnit (w.1 (Fin.last M))})), x.1.1 0 * invU _ x.2)) := by
  constructor
  · intro x y h
    have h1 : Fin.tail x.1.1 = Fin.tail y.1.1 := congrArg (fun z => z.1.1) (congrArg Prod.fst h)
    have h2 : x.1.1 0 * invU _ x.2 = y.1.1 0 * invU _ y.2 := congrArg Prod.snd h
    have ht : x.1.1 (Fin.last (M + 1)) = y.1.1 (Fin.last (M + 1)) := congrFun h1 (Fin.last M)
    have h0 : x.1.1 0 = y.1.1 0 := by
      have e1 : x.1.1 0 * invU _ x.2 * x.1.1 (Fin.last (M + 1)) = x.1.1 0 := by
        rw [mul_assoc, mul_comm (invU _ _), mul_invU, mul_one]
      have e2 : y.1.1 0 * invU _ y.2 * y.1.1 (Fin.last (M + 1)) = y.1.1 0 := by
        rw [mul_assoc, mul_comm (invU _ _), mul_invU, mul_one]
      rw [← e1, ← e2, h2, ht]
    refine Subtype.ext (Subtype.ext (funext fun k => ?_))
    exact Fin.cases h0 (fun j => congrFun h1 j) k
  · rintro ⟨w, r⟩
    have hw : IsUnit ((Fin.cons (r * w.1.1 (Fin.last M)) w.1.1 : Fin (M + 2) → A) (Fin.last (M + 1))) := by
      rw [← Fin.succ_last, Fin.cons_succ]
      exact w.2
    refine ⟨⟨⟨Fin.cons (r * w.1.1 (Fin.last M)) w.1.1, um_top _ _ hw⟩, hw⟩, Prod.ext ?_ ?_⟩
    · exact Subtype.ext (Subtype.ext (funext fun k => rfl))
    · change (Fin.cons (r * w.1.1 (Fin.last M)) w.1.1 : Fin (M + 2) → A) 0 * invU _ hw = r
      have e : (Fin.cons (r * w.1.1 (Fin.last M)) w.1.1 : Fin (M + 2) → A) (Fin.last (M + 1)) = w.1.1 (Fin.last M) := by
        rw [← Fin.succ_last, Fin.cons_succ]
      rw [Fin.cons_zero, invU_eq hw (b := invU _ w.2) (by rw [e, mul_invU]), mul_assoc, mul_invU, mul_one]

private theorem bij_grp (M : ℕ) (A : CommRingCat.{0}) :
    Function.Bijective (fun g : ((XC (M + 2)).sub (Q1 (M + 1))).G.obj A =>
      (((rho M).g.app A g, (sig M).g.app A g) : ((XC (M + 1)).sub (Q1 M)).G.obj A × affC.G.obj A)) := by
  constructor
  · intro x y h
    exact congrArg Prod.fst h
  · rintro ⟨g, u⟩
    exact ⟨g, rfl⟩

private theorem bij_incl0 (A : CommRingCat.{0}) :
    Function.Bijective (fun x : ((XC 1).sub (Q1 0)).D.obj A => (incl (Q1 0)).d.app A x) := by
  refine ⟨fun x y h => Subtype.ext h, fun v => ⟨⟨v, ?_⟩, rfl⟩⟩
  have h : Ideal.span (Set.range (show Um 1 A from v).1) = ⊤ := (show Um 1 A from v).2
  have hr : Set.range (show Um 1 A from v).1 = {(show Um 1 A from v).1 0} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rw [Subsingleton.elim i 0]
      rfl
    · rintro rfl
      exact ⟨0, rfl⟩
  rw [hr] at h
  exact Ideal.span_singleton_eq_top.1 h

end UpperTheory.W1

end

open UpperTheory.W1 in
theorem UpperTheory.eqv_twist_unimodularUnitLocus :
    ∀ (q : ℕ) [NeZero q] (M : ℕ) (E : Spc) (i : ℤ), Inv q E →
        Eqv _ (Sp.map E (incl (Q1 M)) ≫ Sp.fst E (XC (M + 1))) (tw q i) := by
  intro q _ M E i hE
  induction M with
  | zero =>
    haveI : IsIso (Sp.map E (incl (Q1 0))) :=
      UpperTheory.isIso_stackProductMap_of_bijective E (incl (Q1 0)) bij_incl0 (fun A => Function.bijective_id)
    exact eqv_comp (eqv_iso _ _) (equiv_first_twist E hE i)
  | succ M ih =>
    haveI : IsIso (Sp.pair E (rho M) (sig M)) :=
      UpperTheory.isIso_stackProductPair_of_bijective E (rho M) (sig M) (fun A => bij_plain M A) (bij_grp M)
    have e : Sp.map E (incl (Q1 (M + 1))) ≫ Sp.fst E (XC (M + 1 + 1)) =
        Sp.pair E (rho M) (sig M) ≫ Sp.fst (Sp E ((XC (M + 1)).sub (Q1 M))) affC ≫
          Sp.map E (incl (Q1 M)) ≫ Sp.fst E (XC (M + 1)) := rfl
    rw [e]
    exact eqv_comp (eqv_iso _ _) (eqv_comp (UpperTheory.affineLineAction_fst_twistEquiv q _ i (inv_sp hE _)) ih)
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ChernClassPullbackBlowupSecondLocusEq
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

noncomputable section

namespace UpperTheory.LineUnitTrivialization

private def arr {a : Act} {E : Spc} {U : Scheme.{0}} (x : Sx (Sp E a) 1 U) : a.G.obj Γ(U, ⊤) :=
  (show ComposableArrows (Ob a Γ(U, ⊤)) 1 from x.2).hom.1

private theorem det_scalar {A : Type} [CommRing A] (u : Aˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) u) = u := by
  ext
  simp

private theorem lineUnit_line {a : Act} {E : Spc} (χ : a.G ⟶ gmF) {U : Scheme.{0}} (x : Sx (Sp E a) 1 U) :
    lineUnit (Sp.line E χ) x = (show (Γ(U, ⊤))ˣ from χ.app Γ(U, ⊤) (arr x)) :=
  det_scalar _

private theorem lineUnit_map {a b : Act} {E : Spc} (φ : Act.Hom a b) (χ : b.G ⟶ gmF) {U : Scheme.{0}} (x : Sx (Sp E a) 1 U) :
    lineUnit (Sp.map E φ ≫ Sp.line E χ) x = (show (Γ(U, ⊤))ˣ from χ.app Γ(U, ⊤) (φ.g.app Γ(U, ⊤) (arr x))) :=
  det_scalar _

private def chiM (N : ℕ) (Q : Pred (BC N)) : ((BC N).sub Q).G ⟶ gmF where
  app A := GrpCat.ofHom (MonoidHom.snd Aˣ Aˣ / MonoidHom.fst Aˣ Aˣ)
  naturality A B f := by
    ext x
    exact (map_div (Units.map (f.hom : A →* B)) x.2 x.1).symm

private theorem isUnit_um_join_of_span_castSucc_eq_whole {N : ℕ} {A : Type} [CommRing A] (x : Um N A × Um 2 A)
    (h : Ideal.span ((Um.join x).1 '' Set.range Fin.castSucc) = ⊤) : IsUnit (x.2.1 0) := by
  have h' : Ideal.span ((Um.join x).1 '' Set.range Fin.castSucc) ≤ Ideal.span {x.2.1 0} := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp only [Um.join, Fin.snoc_castSucc]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  rw [h, top_le_iff, Ideal.span_singleton_eq_top] at h'
  exact h'

private def sU {N : ℕ} {A : CommRingCat.{0}} (y : ((BC N).sub ((Q2 N).comap (βC N))).D.obj A) : Aˣ :=
  (isUnit_um_join_of_span_castSucc_eq_whole (A := A) y.1 y.2).unit

private def wS (N : ℕ) (E : Spc) (T : Scheme.{0}) (y : Sx (Sp E ((BC N).sub ((Q2 N).comap (βC N)))) 0 T) : (Γ(T, ⊤))ˣ :=
  sU (show ComposableArrows (Ob ((BC N).sub ((Q2 N).comap (βC N))) Γ(T, ⊤)) 0 from y.2).left.pt

private theorem triv (N : ℕ) (E : Spc) :
    IsTrivBy (Sp.line E (chiM N ((Q2 N).comap (βC N)))) (wS N E) := by
  refine ⟨?_, ?_⟩
  · intro T' T g x
    apply Units.ext
    simp only [wS, sU, IsUnit.unit_spec, Units.coe_map]
    rfl
  · intro T x
    rw [lineUnit_line]
    apply Units.ext
    have key := (show ComposableArrows (Ob ((BC N).sub ((Q2 N).comap (βC N))) Γ(T, ⊤)) 1 from x.2).hom.2
    have k2 := congrArg (fun y => (y.1.2.1 0 : Γ(T, ⊤))) key
    simp only [wS, sU, IsUnit.unit_spec]
    exact k2.symm

end UpperTheory.LineUnitTrivialization

end

open UpperTheory.LineUnitTrivialization in
theorem UpperTheory.chernClass_pullback_blowupSecondLocus_eq :
    ∀ (q : ℕ) [NeZero q] (N : ℕ) (E : Spc), Inv q E →
        pull _ (Sp.map E (incl ((Q2 N).comap (βC N)))) _ _ (c1 q (Sp.line E (chiB N))) =
          pull _ (Sp.map E (incl ((Q2 N).comap (βC N)))) _ _ (c1 q (Sp.line E (chiH N))) := by
  intro q _ N E hE
  have hI : Inv q (Sp E ((BC N).sub ((Q2 N).comap (βC N)))) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  have hI' : Inv q (Sp E (BC N)) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  obtain ⟨-, hpull, hadd⟩ := GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q
  rw [hpull _ _ hI', hpull _ _ hI']
  have h0 : c1 q (Sp.line E (chiM N ((Q2 N).comap (βC N)))) = 0 := UpperTheory.firstChernClass_eq_zero_of_isTrivialized q _ _ hI (triv N E)
  have hsum := hadd (Sp.map E (incl ((Q2 N).comap (βC N))) ≫ Sp.line E (chiH N))
    (Sp.line E (chiM N ((Q2 N).comap (βC N))))
    (Sp.map E (incl ((Q2 N).comap (βC N))) ≫ Sp.line E (chiB N)) hI (by
      intro U x
      rw [lineUnit_map, lineUnit_map, lineUnit_line]
      first
        | exact (mul_div_cancel _ _).symm
        | exact (mul_div_cancel_left _ _).symm
        | exact (mul_div_cancel'_right _ _).symm)
  rw [hsum, h0, add_zero]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TwoOpenCoverOfMapInclComap
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem isUnit_last_join {N : ℕ} {A : Type} [CommRing A] (x : Um N A × Um 2 A) (h : IsUnit (x.2.1 1)) :
    IsUnit ((Um.join x).1 (Fin.last N)) := by
  simpa [Um.join] using h

private theorem closedSubgroup_cutoff_exists {N : ℕ} {A : Type} [CommRing A] (x : Um N A × Um 2 A) (h : IsUnit (x.2.1 0)) :
    Ideal.span ((Um.join x).1 '' Set.range Fin.castSucc) = ⊤ := by
  obtain ⟨u, hu⟩ := h
  have e : (Um.join x).1 '' Set.range Fin.castSucc = (fun i => (u : A) * x.1.1 i) '' Set.univ := by
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, trivial, by simp [Um.join, hu]⟩
    · rintro ⟨i, -, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, by simp [Um.join, hu]⟩
  rw [e, span_scale, Set.image_univ]
  exact x.1.2

theorem UpperTheory.two_open_cover_of_map_incl_comap :
    ∀ (R : Type) [CommRing R] (N : ℕ) (E : Spc),
        Cover2 R (Sp.map E (incl ((Q1 N).comap (βC N)))) (Sp.map E (incl ((Q2 N).comap (βC N)))) := by
  intro R _ N E
  refine UpperTheory.mayerVietoris_stackProduct_of_injective_of_locally_covered R E _ _ (fun A => Subtype.val_injective) (fun A => Subtype.val_injective)
    (fun A => Function.bijective_id) (fun A => Function.bijective_id) ?_
  intro T x
  obtain ⟨S, hS, hP⟩ := UpperTheory.locally_exists_isUnit_of_span_range_eq_top T (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from x).2.1
    (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from x).2.2
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨i, hi⟩ := hP V g hg
  have hx : (show Um N Γ(V, ⊤) × Um 2 Γ(V, ⊤) from (BC N).D.map g.appTop x).2.1 i =
      g.appTop.hom ((show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from x).2.1 i) := rfl
  rw [← hx] at hi
  fin_cases i
  · exact Or.inr ⟨⟨_, closedSubgroup_cutoff_exists _ hi⟩, rfl⟩
  · exact Or.inl ⟨⟨_, isUnit_last_join _ hi⟩, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.TwoOpenCoverOfMapIncl
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem q_of_unit {N : ℕ} {A : Type} [CommRing A] (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤)
    (h : ∃ i, IsUnit (v i)) :
    IsUnit (v (Fin.last N)) ∨ Ideal.span (v '' Set.range Fin.castSucc) = ⊤ := by
  obtain ⟨i, hi⟩ := h
  by_cases hl : i = Fin.last N
  · left
    rw [← hl]
    exact hi
  · right
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hl
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, ⟨j, rfl⟩, rfl⟩) hi

theorem UpperTheory.two_open_cover_of_map_incl :
    ∀ (R : Type) [CommRing R] (N : ℕ) (E : Spc), Cover2 R (Sp.map E (incl (Q1 N))) (Sp.map E (incl (Q2 N))) := by
  intro R _ N E
  refine UpperTheory.mayerVietoris_stackProduct_of_injective_of_locally_covered R E (incl (Q1 N)) (incl (Q2 N)) (fun A x y h => Subtype.ext h) (fun A x y h => Subtype.ext h)
    (fun A => Function.bijective_id) (fun A => Function.bijective_id) ?_
  intro T x
  obtain ⟨S, hS, hP⟩ := UpperTheory.locally_exists_isUnit_of_span_range_eq_top T (show Um (N + 1) Γ(T, ⊤) from x).1 (show Um (N + 1) Γ(T, ⊤) from x).2
  refine ⟨S, hS, fun V g hg => ?_⟩
  let w : (XC (N + 1)).D.obj Γ(V, ⊤) := (XC (N + 1)).D.map g.appTop x
  rcases q_of_unit (fun i => g.appTop.hom ((show Um (N + 1) Γ(T, ⊤) from x).1 i))
      (show Um (N + 1) Γ(V, ⊤) from (XC (N + 1)).D.map g.appTop x).2 (hP V g hg) with h | h
  · have h' : (Q1 N).P Γ(V, ⊤) w := h
    exact Or.inl ⟨⟨w, h'⟩, rfl⟩
  · have h' : (Q2 N).P Γ(V, ⊤) w := h
    exact Or.inr ⟨⟨w, h'⟩, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyLiftOfLiftOnUnitCubeFaces
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.DividedPowerChartLift

private theorem iso_incl (E : Spc) {a : Act} (Q : Pred a) (h : ∀ A x, Q.P A x) : IsIso (Sp.map E (incl Q)) := by
  refine UpperTheory.isIso_stackProductMap_of_bijective E (incl Q) (fun A => ⟨?_, ?_⟩) (fun _ => Function.bijective_id)
  · intro x y hxy
    exact Subtype.ext hxy
  · intro y
    exact ⟨⟨y, h A y⟩, rfl⟩

private theorem le_unit {N : ℕ} (i : Fin N) {Q : Pred (XC N)} (h : Q.Le (spanOn ((({i} : Finset (Fin N))) : Set (Fin N)))) :
    Q.Le (unitAt i) := by
  intro A x hx
  have h1 := h A x hx
  simp only [UpperTheory.Blow.spanOn, Finset.coe_singleton, Set.image_singleton] at h1
  exact Ideal.span_singleton_eq_top.mp h1

private theorem loc_step {N : ℕ} (i : Fin N) (F' : Finset (Fin N)) (hi : i ∉ F') (Q : Pred (XC N))
    (hQ : Q.Le (spanOn ((Finset.cons i F' hi : Finset (Fin N)) : Set (Fin N))))
    (T : Scheme.{0}) (x : (XC N).D.obj Γ(T, ⊤)) (hx : Q.P _ x) :
    Loc T fun V g => (Q.inf (spanOn (F' : Set (Fin N)))).P _ ((XC N).D.map g.appTop x) ∨
      (Q.inf (unitAt i)).P _ ((XC N).D.map g.appTop x) := by
  have hs := hQ _ x hx
  simp only [UpperTheory.Blow.spanOn, Finset.coe_cons, Set.image_insert_eq] at hs
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_insert] at hs
  obtain ⟨a, s, hsF, h1⟩ := hs
  let w : Fin 2 → Γ(T, ⊤) := ![x.1 i, s]
  have hw : Ideal.span (Set.range w) = ⊤ := by
    rw [Ideal.eq_top_iff_one, h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ a (Ideal.subset_span ⟨0, rfl⟩)) (Ideal.subset_span ⟨1, rfl⟩)
  obtain ⟨S, hS, hSP⟩ := UpperTheory.locally_exists_isUnit_of_span_range_eq_top T w hw
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨k, hk⟩ := hSP V g hg
  have hQx : Q.P _ ((XC N).D.map g.appTop x) := Q.map _ _ hx
  fin_cases k
  · right
    exact ⟨hQx, hk⟩
  · left
    refine ⟨hQx, ?_⟩
    apply Ideal.eq_top_of_isUnit_mem _ _ hk
    have hm := Ideal.mem_map_of_mem g.appTop.hom hsF
    rw [Ideal.map_span, ← Set.image_comp] at hm
    exact hm

private theorem all_of_units (q : ℕ) [NeZero q] (N : ℕ) (E : Spc) (hE : Inv q E) {c : Act} (π : Act.Hom c (XC N)) {m : ℕ}
    (d e : Fin m → ℤ) (cl : ∀ j, Ht q (Sp E c) (d j) (e j))
    (H : ∀ (i : Fin N) (Q : Pred (XC N)), Q.Le (unitAt i) → LHQ q E π d e cl Q)
    {F : Finset (Fin N)} (hF : F.Nonempty) :
    ∀ Q : Pred (XC N), Q.Le (spanOn (F : Set (Fin N))) → LHQ q E π d e cl Q := by
  induction hF using Finset.Nonempty.cons_induction with
  | singleton j =>
    intro Q hQ
    exact H j Q (le_unit j hQ)
  | cons j F' hj hF' ih =>
    intro Q hQ
    refine UpperTheory.leraHirsch_of_local_cover_of_inf q E hE π d e cl Q (Q.inf (spanOn (F' : Set (Fin N)))) (Q.inf (unitAt j))
      (fun A x hx => hx.1) (fun A x hx => hx.1) ?_ ?_ ?_ ?_
    · intro T x hx
      exact loc_step j F' hj Q hQ T x hx
    · exact ih _ (fun A x hx => hx.2)
    · exact H j _ (fun A x hx => hx.2)
    · exact H j _ (fun A x hx => hx.2.2)

end UpperTheory.DividedPowerChartLift

theorem UpperTheory.cohomology_lift_of_lift_on_unit_cube_faces :
    ∀ (q : ℕ) [NeZero q] (N : ℕ) (E : Spc), 1 ≤ N → Inv q E → ∀ {c : Act} (π : Act.Hom c (XC N)) {m : ℕ} (d e : Fin m → ℤ)
        (cl : ∀ j, Ht q (Sp E c) (d j) (e j)), (∀ (i : Fin N) (Q : Pred (XC N)), Q.Le (unitAt i) → LHQ q E π d e cl Q) → LH q (Sp.map E π) d e cl := by
  intro q _ N E hN hE c π m d e cl H
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩
  have hT := UpperTheory.DividedPowerChartLift.all_of_units q N E hE π d e cl H hne (Pred.top _) (fun A x _ => by
    show Ideal.span _ = ⊤
    rw [Finset.coe_univ, Set.image_univ]
    exact x.2)
  have hsq : Sp.map E (π.sub (Pred.top _)) ≫ Sp.map E (incl (Pred.top (XC N))) =
      Sp.map E (incl (Pred.comap π (Pred.top _))) ≫ Sp.map E π := rfl
  haveI : IsIso (Sp.map E (incl (Pred.comap π (Pred.top (XC N))))) :=
    UpperTheory.DividedPowerChartLift.iso_incl E _ (fun _ _ => trivial)
  haveI : IsIso (Sp.map E (incl (Pred.top (XC N)))) := UpperTheory.DividedPowerChartLift.iso_incl E _ (fun _ _ => trivial)
  have h2 := UpperTheory.lerayHirsch_of_iso_square q (Sp.map E (π.sub (Pred.top _))) (Sp.map E π)
    (inv (Sp.map E (incl (Pred.comap π (Pred.top (XC N)))))) (inv (Sp.map E (incl (Pred.top (XC N)))))
    (by rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, hsq]) d e _ hT
  convert h2 using 1
  funext j
  rw [← GlobalTheory.EtC.pull_comp, IsIso.inv_hom_id, GlobalTheory.EtC.pull_id]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOfPullbackSquare
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem ht_cast_cast {q : ℕ} {E : Spc} {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'')
    (x : Ht q E n i) : Ht.cast h3 h4 (Ht.cast h1 h2 x) = Ht.cast (h1.trans h3) (h2.trans h4) x := by
  subst h1 h2 h3 h4
  rfl

private theorem ht_cast_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') :
    Ht.cast h1 h2 (0 : Ht q E n i) = 0 := by
  subst h1 h2
  rfl

private theorem ht_cast_sub {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x y : Ht q E n i) :
    Ht.cast h1 h2 (x - y) = Ht.cast h1 h2 x - Ht.cast h1 h2 y := by
  subst h1 h2
  rfl

private theorem ht_cast_sum {q : ℕ} {E : Spc} {n i n' i' : ℤ} {ι : Type} (h1 : n = n') (h2 : i = i') (s : Finset ι)
    (f : ι → Ht q E n i) : Ht.cast h1 h2 (∑ j ∈ s, f j) = ∑ j ∈ s, Ht.cast h1 h2 (f j) := by
  subst h1 h2
  rfl

private theorem eq_zero_of_cast {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i)
    (h : Ht.cast h1 h2 x = 0) : x = 0 := by
  subst h1 h2
  exact h

private theorem cup_cast_left {q : ℕ} {E : Spc} {n m i j n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i)
    (y : Ht q E m j) : cup q (Ht.cast h1 h2 x) y = Ht.cast (by rw [h1]) (by rw [h2]) (cup q x y) := by
  subst h1 h2
  rfl

private theorem cup_cast_right {q : ℕ} {E : Spc} {n m i j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (x : Ht q E n i)
    (y : Ht q E m j) : cup q x (Ht.cast h1 h2 y) = Ht.cast (by rw [h1]) (by rw [h2]) (cup q x y) := by
  subst h1 h2
  rfl

private theorem pull_cast {q : ℕ} {X Y : Spc} (f : X ⟶ Y) {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q Y n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x : Ht q X n i) := by
  subst hn hi
  rfl

private theorem pull_cup {q : ℕ} {X Y : Spc} (f : X ⟶ Y) {n m i j : ℤ} (a : Ht q Y n i) (b : Ht q Y m j) :
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a : Ht q X n i) (pull _ f _ _ b : Ht q X m j) :=
  GlobalTheory.T.cup_hypercohomologyPullback (ZMod q) (twPair q i j) f rfl a b

private theorem cup_one_right {q : ℕ} [NeZero q] {E : Spc} (hE : Inv q E) {n i : ℤ} (a : Ht q E n i) :
    cup q a (one q E) = Ht.cast (by ring) (by ring) a := by
  rw [GlobalTheory.T.tateTwistCupProduct_graded_comm q E a (one q E), (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 E hE a, ht_cast_cast, mul_zero, Int.negOnePow_zero, one_smul]

private theorem cup_assoc' {q : ℕ} [NeZero q] {E : Spc} {n m k i j l : ℤ} (a : Ht q E n i) (b : Ht q E m j) (c : Ht q E k l) :
    cup q a (cup q b c) = Ht.cast (by ring) (by ring) (cup q (cup q a b) c) := by
  rw [GlobalTheory.T.tateTwistCupProduct_assoc q E a b c, ht_cast_cast]
  rfl

private theorem step_term {q : ℕ} [NeZero q] {X B : Spc} (p : B ⟶ X) (ξX : Ht q X 2 1) (ξ : Ht q B 2 1) (hX : Inv q X)
    (hrel : ∀ j : ℕ, cpow q ξ (j + 1) = (cup q (cpow q (pull _ p _ _ ξX) j) ξ).cast (by push_cast; ring) (by push_cast; ring))
    {u v n i : ℤ} (x : Ht q X u v) (j : ℕ) (h1 : u + 2 * ((j + 1 : ℕ) : ℤ) = n) (h2 : v + ((j + 1 : ℕ) : ℤ) = i)
    (h3 : u + 2 * (j : ℤ) + 2 * ((1 : ℕ) : ℤ) = n) (h4 : v + (j : ℤ) + ((1 : ℕ) : ℤ) = i) :
    Ht.cast h1 h2 (cup q (pull _ p _ _ x) (cpow q ξ (j + 1))) =
      Ht.cast h3 h4 (cup q (pull _ p _ _ (cup q x (cpow q ξX j))) (cpow q ξ 1)) := by
  have e0 : cpow q ξ 1 = (cup q (cpow q (pull _ p _ _ ξX) 0) ξ).cast (by simp) (by simp) := hrel 0
  rw [hrel j, e0, cup_cast_right, cup_cast_right, ht_cast_cast, ht_cast_cast, ← UpperTheory.pull_cupPow_eq_cupPow_pull q p ξX j hX,
    ← UpperTheory.pull_cupPow_eq_cupPow_pull q p ξX 0 hX, cup_assoc', cup_assoc', ht_cast_cast, ht_cast_cast, ← pull_cup, ← pull_cup, cpow_zero,
    cup_cast_right, cup_one_right hX, ht_cast_cast, pull_cast, cup_cast_left, ht_cast_cast]

private theorem gysin_injective {q : ℕ} {X B : Spc} (p : B ⟶ X) (ξ : Ht q B 2 1)
    (LHp : LH q p (fun j : Fin 2 => 2 * (((j : ℕ) : ℤ))) (fun j : Fin 2 => ((j : ℕ) : ℤ)) (fun j => cpow q ξ j))
    (n i : ℤ) (y0 : Ht q X n i) (y1 : Ht q X (n - 2) (i - 1))
    (h : Ht.cast (n' := n) (i' := i) (by simp) (by simp) (cup q (pull _ p _ _ y0) (cpow q ξ 0)) +
      Ht.cast (n' := n) (i' := i) (by push_cast; ring) (by push_cast; ring) (cup q (pull _ p _ _ y1) (cpow q ξ 1)) = 0) :
    y0 = 0 ∧ y1 = 0 := by
  let a' : ∀ j : Fin 2, Ht q X (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)) := fun j =>
    Fin.cases (motive := fun j : Fin 2 => Ht q X (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)))
      (Ht.cast (by simp) (by simp) y0)
      (fun k => Ht.cast (by have : (k : ℕ) = 0 := by omega
                            simp [this]) (by have : (k : ℕ) = 0 := by omega
                                             simp [this]) y1) j
  have e0 : a' 0 = Ht.cast (by simp) (by simp) y0 := rfl
  have e1 : a' 1 = Ht.cast (by simp) (by simp) y1 := rfl
  have hz := (LHp n i).1 (a₁ := a') (a₂ := 0) (by
    simp only [Fin.sum_univ_two, Pi.zero_apply, map_zero, AddMonoidHom.zero_apply, ht_cast_zero, add_zero]
    rw [e0, e1, pull_cast, pull_cast, cup_cast_left, cup_cast_left, ht_cast_cast, ht_cast_cast]
    exact h)
  exact ⟨eq_zero_of_cast _ _ _ (e0.symm.trans (congrFun hz 0)), eq_zero_of_cast _ _ _ (e1.symm.trans (congrFun hz 1))⟩

private theorem core {q : ℕ} [NeZero q] (N : ℕ) (hN : 1 ≤ N) {E X Y B : Spc} (πX : X ⟶ E) (πY : Y ⟶ E) (p : B ⟶ X) (β : B ⟶ Y)
    (hc : p ≫ πX = β ≫ πY) (ξX : Ht q X 2 1) (ξY : Ht q Y 2 1) (hX : Inv q X) (hY : Inv q Y)
    (LHX : LH q πX (fun j : Fin N => 2 * (((j : ℕ) : ℤ))) (fun j : Fin N => ((j : ℕ) : ℤ)) (fun j => cpow q ξX j))
    (LHp : LH q p (fun j : Fin 2 => 2 * (((j : ℕ) : ℤ))) (fun j : Fin 2 => ((j : ℕ) : ℤ)) (fun j => cpow q (pull _ β _ _ ξY) j))
    (hrel : ∀ j : ℕ, cpow q (pull _ β _ _ ξY) (j + 1) = (cup q (cpow q (pull _ p _ _ ξX) j) (pull _ β _ _ ξY)).cast (by push_cast; ring) (by push_cast; ring))
    (n i : ℤ) (a : ∀ j : Fin (N + 1), Ht q E (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)))
    (h : ∑ j, ((cup q (pull _ πY _ _ (a j)) (cpow q ξY j)).cast (by ring) (by ring) : Ht q Y n i) = 0) : a = 0 := by
  have pp : ∀ {m k : ℤ} (x : Ht q E m k), (pull _ β _ _ (pull _ πY _ _ x) : Ht q B m k) = pull _ p _ _ (pull _ πX _ _ x) := by
    intro m k x
    rw [← pull_comp, ← pull_comp, hc]
  have h1 : ∑ j : Fin (N + 1), ((cup q (pull _ p _ _ (pull _ πX _ _ (a j))) (cpow q (pull _ β _ _ ξY) j)).cast (by ring) (by ring) : Ht q B n i) = 0 := by
    have h' := congrArg (pull _ β (tw q i) n) h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h'
    rw [← h']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pull_cast, pull_cup, UpperTheory.pull_cupPow_eq_cupPow_pull q β ξY j hY, pp]
  rw [Fin.sum_univ_succ] at h1
  let y0 : Ht q X n i := Ht.cast (by simp) (by simp) (pull _ πX _ _ (a 0))
  let y1 : Ht q X (n - 2) (i - 1) := ∑ k : Fin N, Ht.cast (by simp only [Fin.val_succ]; push_cast; ring) (by simp only [Fin.val_succ]; push_cast; ring)
    (cup q (pull _ πX _ _ (a k.succ)) (cpow q ξX k))
  have hy := gysin_injective p (pull _ β _ _ ξY) LHp n i y0 y1 (by
    rw [← h1]
    congr 1
    · simp only [y0]
      rw [pull_cast, cup_cast_left, ht_cast_cast]
      rfl
    · simp only [y1]
      have sum_apply {A B : Type 1} [AddCommMonoid A] [AddCommMonoid B]
          {ι : Type} (s : Finset ι) (f : ι → A →+ B) (x : A) :
          (s.sum f) x = s.sum (fun j => f j x) := by
        classical
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih => simp [ha, ih]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, sum_apply, ht_cast_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pull_cast, cup_cast_left, ht_cast_cast]
      exact (step_term p ξX (pull _ β _ _ ξY) hX hrel _ k _ _ _ _).symm)
  have hb := (LHX (n - 2) (i - 1)).1
    (a₁ := fun k => Ht.cast (by simp only [Fin.val_succ]; push_cast; ring) (by simp only [Fin.val_succ]; push_cast; ring) (a k.succ)) (a₂ := 0) (by
      simp only [Pi.zero_apply, map_zero, AddMonoidHom.zero_apply, ht_cast_zero, Finset.sum_const_zero]
      rw [← hy.2]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pull_cast, cup_cast_left, ht_cast_cast])
  have ha := fun k : Fin N => eq_zero_of_cast _ _ _ (congrFun hb k)
  let k0 : Fin N := ⟨0, hN⟩
  let f : ∀ j : Fin N, Ht q E (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)) := Pi.single k0 (Ht.cast (by simp [k0]) (by simp [k0]) (a 0))
  have hf := (LHX n i).1 (a₁ := f) (a₂ := 0) (by
    simp only [Pi.zero_apply, map_zero, AddMonoidHom.zero_apply, ht_cast_zero, Finset.sum_const_zero]
    rw [Finset.sum_eq_single k0 (fun j _ hj => by simp only [f, Pi.single_eq_of_ne hj, map_zero, AddMonoidHom.zero_apply, ht_cast_zero])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp only [f, Pi.single_eq_same]
    have e : cpow q ξX (k0 : ℕ) = (one q X).cast (by simp [k0]) (by simp [k0]) := rfl
    have hy0 : (pull _ πX _ _ (a 0) : Ht q X _ _) = 0 := eq_zero_of_cast _ _ _ hy.1
    rw [e, cup_cast_right, cup_one_right hX, pull_cast, hy0]
    simp only [ht_cast_zero])
  have h0 : a 0 = 0 := eq_zero_of_cast _ _ _ ((Pi.single_eq_same (M := fun j : Fin N => Ht q E (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ))) k0 _).symm.trans (congrFun hf k0))
  funext j
  refine Fin.cases h0 ha j

theorem UpperTheory.leray_hirsch_of_pullback_square :
    ∀ (q : ℕ) [NeZero q] (N : ℕ), 1 ≤ N → ∀ {E X Y B : Spc} (πX : X ⟶ E) (πY : Y ⟶ E) (p : B ⟶ X) (β : B ⟶ Y) (_ : p ≫ πX = β ≫ πY)
        (ξX : Ht q X 2 1) (ξY : Ht q Y 2 1), Inv q X → Inv q Y →
        LH q πX (fun j : Fin N => 2 * (((j : ℕ) : ℤ))) (fun j : Fin N => ((j : ℕ) : ℤ)) (fun j => cpow q ξX j) →
        LH q p (fun j : Fin 2 => 2 * (((j : ℕ) : ℤ))) (fun j : Fin 2 => ((j : ℕ) : ℤ)) (fun j => cpow q (pull _ β _ _ ξY) j) →
        (∀ j : ℕ, cpow q (pull _ β _ _ ξY) (j + 1) = (cup q (cpow q (pull _ p _ _ ξX) j) (pull _ β _ _ ξY)).cast (by push_cast; ring) (by push_cast; ring)) →
        ∀ n i : ℤ, Function.Injective fun a : ∀ j : Fin (N + 1), Ht q E (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)) =>
          ∑ j, ((cup q (pull _ πY _ _ (a j)) (cpow q ξY j)).cast (by ring) (by ring) : Ht q Y n i) := by
  intro q _ N hN E X Y B πX πY p β hc ξX ξY hX hY LHX LHp hrel n i a b hab
  have hab' : ∑ j, ((cup q (pull _ πY _ _ (a j)) (cpow q ξY j)).cast (by ring) (by ring) : Ht q Y n i) =
      ∑ j, ((cup q (pull _ πY _ _ (b j)) (cpow q ξY j)).cast (by ring) (by ring) : Ht q Y n i) := hab
  refine sub_eq_zero.1 (core N hN πX πY p β hc ξX ξY hX hY LHX LHp hrel n i (a - b) ?_)
  simp only [Pi.sub_apply, map_sub, AddMonoidHom.sub_apply, ht_cast_sub, Finset.sum_sub_distrib]
  exact sub_eq_zero.2 hab'
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.CpowSuccEqCupOfTwoCover
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem ht_cast_cast' {q : ℕ} {E : Spc} {n i n' i' n'' i'' : ℤ} (x : Ht q E n i) (a : n = n') (b : i = i')
    (c : n' = n'') (d : i' = i'') : (x.cast a b).cast c d = x.cast (a.trans c) (b.trans d) := by
  subst a; subst b; subst c; subst d; rfl

private theorem cup_cast_left' {q : ℕ} {E : Spc} {n m i j n' i' : ℤ} (x : Ht q E n i) (b : Ht q E m j) (hn : n = n')
    (hi : i = i') : cup q (x.cast hn hi) b = (cup q x b).cast (congrArg (· + m) hn) (congrArg (· + j) hi) := by
  subst hn; subst hi; rfl

private theorem cup_self_eq (q : ℕ) [NeZero q] {U V B : Spc} (g₁ : U ⟶ B) (g₂ : V ⟶ B) (ξ h : Ht q B 2 1)
    (hc : Cover2 (ZMod q) g₁ g₂) (h₁ : pull _ g₁ _ _ ξ = 0) (h₂ : pull _ g₂ _ _ ξ = pull _ g₂ _ _ h) :
    cup q ξ ξ = cup q h ξ := by
  have inj := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties (ZMod q) (tw q 1)).1
  have hz : cup q ξ (ξ - h) = 0 :=
    GlobalTheory.T.cupProduct_eq_zero_of_vanishing_on_cover (ZMod q) (twPair q 1 1) inj inj g₁ g₂ hc _ ξ (ξ - h) h₁ (by
      rw [map_sub]
      exact sub_eq_zero.mpr h₂)
  rw [map_sub, sub_eq_zero] at hz
  rw [hz, GlobalTheory.T.tateTwistCupProduct_graded_comm q B ξ h]
  norm_num
  rw [Int.negOnePow_even 4 ⟨2, rfl⟩, one_smul]
  rfl

theorem UpperTheory.cpow_succ_eq_cup_of_two_cover :
    ∀ (q : ℕ) [NeZero q] {U V B : Spc} (g₁ : U ⟶ B) (g₂ : V ⟶ B) (ξ h : Ht q B 2 1), Inv q B → Cover2 (ZMod q) g₁ g₂ →
        pull _ g₁ _ _ ξ = 0 → pull _ g₂ _ _ ξ = pull _ g₂ _ _ h →
        ∀ j : ℕ, cpow q ξ (j + 1) = (cup q (cpow q h j) ξ).cast (by push_cast; ring) (by push_cast; ring) := by
  intro q _ U V B g₁ g₂ ξ h _ hc h₁ h₂ j
  induction j with
  | zero =>
    rw [cpow_succ]
    rfl
  | succ j ih =>
    rw [cpow_succ q ξ (j + 1), ih, cup_cast_left', ht_cast_cast', GlobalTheory.T.tateTwistCupProduct_assoc,
      ht_cast_cast', cup_self_eq q g₁ g₂ ξ h hc h₁ h₂]
    rw [cpow_succ q h j, cup_cast_left', ht_cast_cast', GlobalTheory.T.tateTwistCupProduct_assoc, ht_cast_cast']
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

theorem UpperTheory.projectiveBundleFormula_succ_of_forall :
    ∀ (q : ℕ) [NeZero q] (N : ℕ), 2 ≤ N → (∀ E : Spc, Inv q E → PBF q E N) → ∀ E : Spc, Inv q E → PBF q E (N + 1) := by
  intro q _ N hN H E hE
  have hN1 : 1 ≤ N := by omega
  have invS : ∀ (a : Act), Inv q (Sp E a) := fun a U ⟨x⟩ => hE U ⟨x.1⟩
  refine (UpperTheory.projBundleFormula_iff_pglForm q E (N + 1) hE).2 ?_
  have hX : Pbf q E N := (UpperTheory.projBundleFormula_iff_pglForm q E N hE).1 (H E hE)
  have hc : Sp.map E (βC N) ≫ Sp.line E (chiX (N + 1)) = Sp.line E (chiB N) := rfl
  have hξ : pull _ (Sp.map E (βC N)) _ _ (c1 q (Sp.line E (chiX (N + 1)))) = c1 q (Sp.line E (chiB N)) := by
    rw [(GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 _ _ (invS _), hc]
  have hh : pull _ (Sp.map E (pC N)) _ _ (c1 q (Sp.line E (chiX N))) = c1 q (Sp.line E (chiH N)) := by
    rw [(GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 _ _ (invS _)]
    rfl
  have hlh : LH q (Sp.map E (pC N)) (fun j : Fin 2 => 2 * (((j : ℕ) : ℤ))) (fun j : Fin 2 => ((j : ℕ) : ℤ))
      (fun j => cpow q (pull _ (Sp.map E (βC N)) _ _ (c1 q (Sp.line E (chiX (N + 1))))) j) := by
    rw [hξ]
    exact UpperTheory.cohomology_lift_of_lift_on_unit_cube_faces q N E hN1 hE (pC N) _ _ _ (fun i Q hQ => UpperTheory.leraHirsch_chernPowers_on_unitChart q N E i Q hQ hE)
  have hB1 : ∀ i, Eqv _ (Sp.map E (incl ((Q1 N).comap (βC N))) ≫ Sp.map E (pC N)) (tw q i) := fun i =>
    (UpperTheory.lerayHirsch_one_iff_twist_equiv q (Sp.map E ((incl ((Q1 N).comap (βC N))).comp (pC N))) (invS _)).1
      (UpperTheory.cohomology_lift_of_lift_on_unit_cube_faces q N E hN1 hE _ _ _ _ (fun i Q hQ => UpperTheory.leraHirsch_unit_on_blowupChart q N E i Q hQ hE)) i
  have r1 : pull _ (Sp.map E (incl ((Q1 N).comap (βC N)))) _ _ (pull _ (Sp.map E (βC N)) _ _ (c1 q (Sp.line E (chiX (N + 1))))) = 0 := by
    rw [hξ]
    exact UpperTheory.chernClass_pullback_blowupFirstLocus_eq_zero q N E hE
  have r2 : pull _ (Sp.map E (incl ((Q2 N).comap (βC N)))) _ _ (pull _ (Sp.map E (βC N)) _ _ (c1 q (Sp.line E (chiX (N + 1))))) =
      pull _ (Sp.map E (incl ((Q2 N).comap (βC N)))) _ _ (pull _ (Sp.map E (pC N)) _ _ (c1 q (Sp.line E (chiX N)))) := by
    rw [hξ, hh]
    exact UpperTheory.chernClass_pullback_blowupSecondLocus_eq q N E hE
  have rel := UpperTheory.cpow_succ_eq_cup_of_two_cover q (Sp.map E (incl ((Q1 N).comap (βC N)))) (Sp.map E (incl ((Q2 N).comap (βC N))))
    (pull _ (Sp.map E (βC N)) _ _ (c1 q (Sp.line E (chiX (N + 1))))) (pull _ (Sp.map E (pC N)) _ _ (c1 q (Sp.line E (chiX N))))
    (invS _) (UpperTheory.two_open_cover_of_map_incl_comap _ N E) r1 r2
  intro n i
  refine ⟨UpperTheory.leray_hirsch_of_pullback_square q N hN1 (Sp.fst E (XC N)) (Sp.fst E (XC (N + 1))) (Sp.map E (pC N)) (Sp.map E (βC N)) rfl
      (c1 q (Sp.line E (chiX N))) (c1 q (Sp.line E (chiX (N + 1)))) (invS _) (invS _) hX hlh rel n i,
    UpperTheory.leray_hirsch_of_two_covers_pullback_square q N hN1 (Sp.fst E (XC N)) (Sp.fst E (XC (N + 1))) (Sp.map E (pC N)) (Sp.map E (βC N))
      (Sp.map E (incl (Q1 N))) (Sp.map E (incl (Q2 N))) (Sp.map E (incl ((Q1 N).comap (βC N))))
      (Sp.map E (incl ((Q2 N).comap (βC N)))) (Sp.map E ((βC N).sub (Q1 N))) (Sp.map E ((βC N).sub (Q2 N)))
      rfl rfl rfl (c1 q (Sp.line E (chiX N))) (c1 q (Sp.line E (chiX (N + 1)))) (invS _) (invS _) (invS _)
      (UpperTheory.two_open_cover_of_map_incl _ N E) (UpperTheory.two_open_cover_of_map_incl_comap _ N E) hX hlh (fun i => UpperTheory.eqv_twist_unimodularUnitLocus q N E i hE) hB1
      (fun i => UpperTheory.eqv_twist_blowupRestriction q N E (Q2 N) i (fun _ _ h => h) hE) (fun i => UpperTheory.pullback_cube_faces_equiv_tate_twist q N E i _ _ hE) r1 rel n i⟩
