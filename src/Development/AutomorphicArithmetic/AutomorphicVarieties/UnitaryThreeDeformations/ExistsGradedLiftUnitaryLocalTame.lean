module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Origin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtCorr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtTorus

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtDiag
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R]

private def Up (g : GL (Fin 3) R) : Prop := Matrix.BlockTriangular (g : Matrix (Fin 3) (Fin 3) R) id

private theorem ltd_wt_neg_iff (a b : Fin 3) : wt a b < 0 ↔ b < a := by
  revert a b; decide

private theorem Up.mul {g h : GL (Fin 3) R} (hg : Up g) (hh : Up h) : Up (g * h) :=
  Matrix.BlockTriangular.mul hg hh

private theorem Up.inv {g : GL (Fin 3) R} (hg : Up g) : Up g⁻¹ := by
  letI : Invertible (g : Matrix (Fin 3) (Fin 3) R) := g.invertible
  have := Matrix.blockTriangular_inv_of_blockTriangular hg
  unfold Up
  rwa [Matrix.coe_units_inv]

private theorem Jc (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    (Jmat R 3 * Xᵀ * Jmat R 3) a b = X b.rev a.rev := by
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

private theorem ltd_theta_apply (g : GL (Fin 3) R) (a b : Fin 3) :
    (theta g : Matrix (Fin 3) (Fin 3) R) a b = ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) b.rev a.rev := by
  rw [theta_val, Jc]

private theorem Up.theta {g : GL (Fin 3) R} (hg : Up g) : Up (theta g) := by
  intro a b h
  rw [ltd_theta_apply]
  exact hg.inv (Fin.rev_lt_rev.mpr h)

private theorem Up.sgn {g : GL (Fin 3) R} (hg : Up g) (s : ℤˣ) : Up (sgnAct 3 R s g) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rwa [sgnAct_one]
  · rw [sgnAct_neg_one]; exact hg.theta

private theorem Up.diag_mul {g h : GL (Fin 3) R} (hg : Up g) (hh : Up h) (a : Fin 3) :
    ((g * h : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a a =
      (g : Matrix (Fin 3) (Fin 3) R) a a * (h : Matrix (Fin 3) (Fin 3) R) a a := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single a]
  · intro b _ hb
    rcases lt_or_gt_of_ne hb with h1 | h1
    · rw [hg (show id b < id a from h1), zero_mul]
    · rw [hh (show id a < id b from h1), mul_zero]
  · simp

private def dgl (g : GL (Fin 3) R) (hg : Up g) : GL (Fin 3) R where
  val := Matrix.diagonal fun a => (g : Matrix (Fin 3) (Fin 3) R) a a
  inv := Matrix.diagonal fun a => ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a a
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [← hg.diag_mul hg.inv, mul_inv_cancel]
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    rw [← hg.inv.diag_mul hg, inv_mul_cancel]
    simp

private theorem dgl_val (g : GL (Fin 3) R) (hg : Up g) : (dgl g hg : Matrix (Fin 3) (Fin 3) R) =
    Matrix.diagonal fun a => (g : Matrix (Fin 3) (Fin 3) R) a a := rfl

private theorem dgl_inv_val (g : GL (Fin 3) R) (hg : Up g) :
    (((dgl g hg)⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) =
    Matrix.diagonal fun a => ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a a := rfl

private theorem dgl_mul {g h : GL (Fin 3) R} (hg : Up g) (hh : Up h) :
    dgl (g * h) (hg.mul hh) = dgl g hg * dgl h hh := by
  apply Units.ext
  rw [Units.val_mul (dgl g hg), dgl_val, dgl_val, dgl_val, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact hg.diag_mul hh a

private theorem dgl_sgn {g : GL (Fin 3) R} (hg : Up g) (s : ℤˣ) :
    dgl (sgnAct 3 R s g) (hg.sgn s) = sgnAct 3 R s (dgl g hg) := by
  apply Units.ext
  rw [dgl_val]
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [sgnAct_one, sgnAct_one, dgl_val]
  · rw [sgnAct_neg_one, sgnAct_neg_one]
    ext a b
    rw [ltd_theta_apply, dgl_inv_val]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, ltd_theta_apply]
    · rw [Matrix.diagonal_apply_ne _ hab,
        Matrix.diagonal_apply_ne _ (fun h => hab (Fin.rev_injective h).symm)]

private def Bor (R : Type) [CommRing R] : Subgroup (GG (m := 3) (R := R)) where
  carrier := {x | Up x.left}
  mul_mem' := fun {x y} hx hy => by
    change Up (x * y).left
    rw [SemidirectProduct.mul_left]
    exact Up.mul hx (Up.sgn hy _)
  one_mem' := Matrix.blockTriangular_one
  inv_mem' := fun {x} hx => by
    change Up (x⁻¹).left
    rw [SemidirectProduct.inv_left]
    exact Up.sgn (Up.inv hx) _

private def dgHom (R : Type) [CommRing R] : Bor R →* GG (m := 3) (R := R) :=
  MonoidHom.mk' (fun x => ⟨dgl x.1.left x.2, x.1.right⟩) (fun x y => by
    ext1
    · rw [SemidirectProduct.mul_left]
      change dgl (x.1.left * sgnAct 3 R x.1.right y.1.left) (Up.mul x.2 (Up.sgn y.2 _)) =
        dgl x.1.left x.2 * sgnAct 3 R x.1.right (dgl y.1.left y.2)
      exact (dgl_mul (g := x.1.left) x.2 (Up.sgn (g := y.1.left) y.2 _)).trans
        (congrArg (dgl x.1.left x.2 * ·) (dgl_sgn (g := y.1.left) y.2 _))
    · rfl)

end SlopeTestRemainingChoices

end UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.lt_diag :
    ∀ {R : Type} [CommRing R] [Finite R],
      ∃ (B : Subgroup (GG (m := 3) (R := R))) (dg : B →* GG (m := 3) (R := R)),
        (∀ x : GG (m := 3) (R := R), x ∈ B ↔ ∀ a b, wt a b < 0 → x.mat a b = 0) ∧
        ∀ x : B, (dg x).right = (x : GG (m := 3) (R := R)).right ∧
          (dg x).mat = Matrix.diagonal fun a => (x : GG (m := 3) (R := R)).mat a a := by
  intro R _ _
  refine ⟨Bor R, dgHom R, fun x => ?_, fun x => ⟨rfl, rfl⟩⟩
  exact ⟨fun h a b hab => h ((ltd_wt_neg_iff a b).1 hab), fun h a b hab => h a b ((ltd_wt_neg_iff a b).2 hab)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtGrSub
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem ltgs_inv_mem {M : Type} [Group M] [Finite M] (S : Submonoid M) {x : M} (hx : x ∈ S) : x⁻¹ ∈ S := by
  have hk : 0 < orderOf x := orderOf_pos x
  have e : x⁻¹ = x ^ (orderOf x - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hk, pow_orderOf_eq_one]
  rw [e]
  exact S.pow_mem hx _

theorem UpperTheory.V.UnitaryThreeInertia.lt_grSub :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] [Finite R] (ℬ : ℤ → Submodule O R) [SetLike.GradedMonoid ℬ],
      ∃ S : Subgroup (GG (m := 3) (R := R)), ∀ x, x ∈ S ↔ GrMat ℬ x.mat := by
  intro O R _ _ _ _ ℬ _
  classical
  have hwt : ∀ a c b : Fin 3, wt a c + wt c b = wt a b := by
    intro a c b; simp only [wt]; ring
  have hwrev : ∀ a b : Fin 3, wt b.rev a.rev = wt a b := by
    intro a b; fin_cases a <;> fin_cases b <;> rfl
  have hone : GrMat ℬ (1 : Matrix (Fin 3) (Fin 3) R) := by
    intro a b
    by_cases h : a = b
    · subst h
      rw [Matrix.one_apply_eq]
      have h0 : wt a a = 0 := by simp [wt]
      rw [h0]
      exact SetLike.GradedOne.one_mem
    · rw [Matrix.one_apply_ne h]
      exact Submodule.zero_mem _
  have hmul : ∀ X Y : Matrix (Fin 3) (Fin 3) R, GrMat ℬ X → GrMat ℬ Y → GrMat ℬ (X * Y) := by
    intro X Y hX hY a b
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [← hwt a c b]
    exact SetLike.GradedMul.mul_mem (hX a c) (hY c b)
  let T : Submonoid (GL (Fin 3) R) :=
    { carrier := {g | GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R)}
      mul_mem' := fun {g h} hg hh => by
        show GrMat ℬ ((g * h : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
        rw [Units.val_mul]
        exact hmul _ _ hg hh
      one_mem' := by
        show GrMat ℬ ((1 : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
        rw [Units.val_one]
        exact hone }
  have hinv : ∀ g : GL (Fin 3) R, GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R) →
      GrMat ℬ ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) :=
    fun g hg => ltgs_inv_mem T (x := g) hg
  have hJ : ∀ (M : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3),
      (Jmat R 3 * M * Jmat R 3) a b = M a.rev b.rev := by
    intro M a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat] <;> rfl
  have htheta : ∀ g : GL (Fin 3) R, GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R) →
      GrMat ℬ ((theta g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
    intro g hg a b
    rw [theta_val, hJ, Matrix.transpose_apply, ← hwrev a b]
    exact hinv g hg b.rev a.rev
  have hact : ∀ (s : ℤˣ) (g : GL (Fin 3) R), GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R) →
      GrMat ℬ ((sgnAct 3 R s g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
    intro s g hg
    rcases Int.units_eq_one_or s with rfl | rfl
    · rw [sgnAct_one]; exact hg
    · rw [sgnAct_neg_one]; exact htheta g hg
  haveI : Finite (GG (m := 3) (R := R)) :=
    Finite.of_injective (fun x : GG (m := 3) (R := R) => (x.left, x.right))
    (fun x y h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let S0 : Submonoid (GG (m := 3) (R := R)) :=
    { carrier := {x | GrMat ℬ x.mat}
      mul_mem' := fun {x y} hx hy => by
        show GrMat ℬ ((x * y).left : Matrix (Fin 3) (Fin 3) R)
        rw [SemidirectProduct.mul_left, Units.val_mul]
        exact hmul _ _ hx (hact _ _ hy)
      one_mem' := by
        show GrMat ℬ ((1 : GG (m := 3) (R := R)).left : Matrix (Fin 3) (Fin 3) R)
        rw [SemidirectProduct.one_left, Units.val_one]
        exact hone }
  exact ⟨{ S0 with inv_mem' := fun {x} hx => ltgs_inv_mem S0 hx }, fun x => Iff.rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtUpper
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia

private theorem lu_unit {O : Type} [CommRing O] (t : Oˣ) (ht : IsUnit ((t : O) ^ 2 - 1)) (a b : Fin 3)
    (hab : a ≠ b) : IsUnit (((t ^ wt1 a : Oˣ) : O) - ((t ^ wt1 b : Oˣ) : O)) := by
  have e : (t : O) * ((t⁻¹ : Oˣ) : O) = 1 := Units.mul_inv t
  have h1 : IsUnit ((t : O) - 1) := by
    rw [show (t : O) ^ 2 - 1 = ((t : O) - 1) * (t + 1) by ring] at ht
    exact isUnit_of_mul_isUnit_left ht
  have h2 : IsUnit ((t : O) - ((t⁻¹ : Oˣ) : O)) := by
    have := ht.mul (t⁻¹).isUnit
    convert this using 1
    linear_combination (-(t : O)) * e
  have h3 : IsUnit (1 - ((t⁻¹ : Oˣ) : O)) := by
    have := h1.mul (t⁻¹).isUnit
    convert this using 1
    linear_combination (-1 : O) * e
  have h1' := h1.neg
  have h2' := h2.neg
  have h3' := h3.neg
  rw [neg_sub] at h1' h2' h3'
  have w0 : wt1 0 = 1 := rfl
  have w1 : wt1 1 = 0 := rfl
  have w2 : wt1 2 = -1 := rfl
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg,
      Units.val_one, ne_eq, not_true_eq_false] at hab ⊢ <;> assumption

private theorem lu_up {R : Type} [CommRing R] (U k T : Matrix (Fin 3) (Fin 3) R) (e : U * k = k * T)
    (hU : ∀ a b, wt a b < 0 → U a b = 0) (hT : ∀ a b, wt a b < 0 → T a b = 0)
    (hu : ∀ a b, a ≠ b → IsUnit (U a a - T b b)) :
    ∀ a b, wt a b < 0 → k a b = 0 := by
  have e10 := congrFun (congrFun e 1) 0
  have e20 := congrFun (congrFun e 2) 0
  have e21 := congrFun (congrFun e 2) 1
  have u10 := hU 1 0 (by decide)
  have u20 := hU 2 0 (by decide)
  have u21 := hU 2 1 (by decide)
  have t10 := hT 1 0 (by decide)
  have t20 := hT 2 0 (by decide)
  have t21 := hT 2 1 (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u10, u20, u21, t10, t20, t21] at e10 e20 e21
  have k20 : k 2 0 = 0 := (hu 2 0 (by decide)).mul_right_eq_zero.1 (by linear_combination e20)
  have k10 : k 1 0 = 0 := (hu 1 0 (by decide)).mul_right_eq_zero.1 (by
    rw [k20] at e10; linear_combination e10)
  have k21 : k 2 1 = 0 := (hu 2 1 (by decide)).mul_right_eq_zero.1 (by
    rw [k20] at e21; linear_combination e21)
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)

private theorem lu_J {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    (Jmat R 3 * Xᵀ * Jmat R 3) a b = X b.rev a.rev := by
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

end UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.lt_upper :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [Group D]
      (η : D →* ℤˣ) (Ψ : D →* Oˣ) (r : D →* GG (m := 3) (R := R)) (x : D),
      Red η Ψ r → η x = 1 → IsUnit ((Ψ x : O) ^ 2 - 1) → Upper η r → ∀ g a b, wt a b < 0 → (r g).mat a b = 0 := by
  intro O R D _ _ _ _ _ _ η Ψ r x hr hx hΨ hU g
  rcases Int.units_eq_one_or (η g) with hg | hg
  · exact hU g hg
  have hX : ∀ x a, residue R ((r x).mat a a) = residue R (algebraMap O R ((Ψ x ^ wt1 a : Oˣ) : O)) := by
    intro x a
    have := (residue_eq_zero_iff _).2 (hr.red x a a)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [this]
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.map_apply, Matrix.diagonal_apply_eq]
  obtain ⟨y, hy⟩ : ∃ y, y = g⁻¹ * x⁻¹ * g := ⟨_, rfl⟩
  have hηy : η y = 1 := by simp [hy, hx]
  have hΨy : Ψ y = (Ψ x)⁻¹ := by simp [hy]
  have rx : (r x).right = 1 := (hr.mult x).trans hx
  have ry : (r y).right = 1 := (hr.mult y).trans hηy
  have rg : (r g).right = -1 := (hr.mult g).trans hg
  have e0 : r x * r g = r g * (r y)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hy]; congr 1; group
  have e1 : (r x).left * (r g).left = (r g).left * theta ((r y).left⁻¹) := by
    have := congrArg SemidirectProduct.left e0
    simpa [rx, ry, rg] using this
  have e2 : (r x).mat * (r g).mat = (r g).mat * (Jmat R 3 * (r y).matᵀ * Jmat R 3) := by
    have := congrArg Units.val e1
    rwa [Units.val_mul, Units.val_mul, theta_val, inv_inv] at this
  refine lu_up _ _ _ e2 (hU x hx) (fun a b hab => ?_) (fun a b hab => ?_)
  · rw [lu_J]
    refine hU y hηy _ _ ?_
    have : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl
    rwa [this]
  · have w : wt1 b.rev = -wt1 b := by fin_cases b <;> rfl
    rw [lu_J, ← residue_ne_zero_iff_isUnit, map_sub, hX, hX, ← map_sub,
      ← map_sub, residue_ne_zero_iff_isUnit, hΨy, w, _root_.inv_zpow', neg_neg]
    exact (lu_unit (Ψ x) hΨ a b hab).map _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtRedConj
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem entIn_sub_iff {C : Type} [CommRing C] (I : Ideal C) (X Y : Matrix (Fin 3) (Fin 3) C) :
    EntIn I (X - Y) ↔ X.map (Ideal.Quotient.mk I) = Y.map (Ideal.Quotient.mk I) := by
  constructor
  · intro h
    ext a b
    simp only [Matrix.map_apply]
    exact Ideal.Quotient.eq.mpr (by simpa [Matrix.sub_apply] using h a b)
  · intro h a b
    have hab := congrFun (congrFun h a) b
    simp only [Matrix.map_apply] at hab
    simpa [Matrix.sub_apply] using Ideal.Quotient.eq.mp hab

private theorem congOne_iff {C : Type} [CommRing C] (I : Ideal C) (h : GL (Fin 3) C) :
    CongOne I h ↔ GeneralLinearGroup.map (Ideal.Quotient.mk I) h = 1 := by
  unfold CongOne
  rw [entIn_sub_iff, Matrix.map_one _ (map_zero _) (map_one _)]
  constructor
  · intro e
    exact Units.ext e
  · intro e
    exact congrArg Units.val e

private theorem map_conjBy {C D : Type} [CommRing C] [Group D] (I : Ideal C) (h : GL (Fin 3) C)
    (hh : CongOne I h) (r : D →* GG (m := 3) (R := C)) (g : D) :
    GG.map (Ideal.Quotient.mk I) (conjBy h r g) = GG.map (Ideal.Quotient.mk I) (r g) := by
  have e : GG.map (Ideal.Quotient.mk I) (GG.ofGL h) = 1 := by
    unfold GG.map
    rw [SemidirectProduct.map_inl, (congOne_iff I h).1 hh, map_one]
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, e,
    one_mul, inv_one, mul_one]

private theorem mats_conjBy {C D : Type} [CommRing C] [Group D] (h : GL (Fin 3) C)
    (r : D →* GG (m := 3) (R := C)) (g : D) :
    mats (conjBy h r) g =
      (h : Matrix (Fin 3) (Fin 3) C) * mats r g *
        ((sgnAct 3 C (r g).right h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
  simp [mats, GG.mat, conjBy, GG.ofGL, SemidirectProduct.mul_left, Units.val_mul]

theorem UpperTheory.V.UnitaryThreeInertia.lt_red_conj :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
      [Group D] [TopologicalSpace D] (η : D →* ℤˣ) (Ψ : D →* Oˣ)
      (r : D →* GG (m := 3) (R := R)) (h : GL (Fin 3) R),
      InHat h → Red η Ψ r → InHat h⁻¹ ∧ Red η Ψ (conjBy h r) ∧ (IsLocallyConstant η → IsLocallyConstant (mats r) → IsLocallyConstant (mats (conjBy h r))) := by
  intro O R D _ _ _ _ _ _ _ η Ψ r h hh hr
  have hinv : InHat h⁻¹ := by
    show CongOne (maximalIdeal R) h⁻¹
    rw [congOne_iff, map_inv, (congOne_iff _ h).mp hh, inv_one]
  have hright : ∀ g, (conjBy h r g).right = (r g).right := by
    intro g
    simp [conjBy, GG.ofGL]
  refine ⟨hinv, ⟨fun g => (hright g).trans (hr.mult g), fun g => ?_⟩, fun hη hm => ?_⟩
  · rw [entIn_sub_iff]
    have h0 := (entIn_sub_iff _ _ _).mp (hr.red g)
    rw [← h0, ← GG.map_mat, ← GG.map_mat, map_conjBy _ h hh]
  · have hfun : mats (conjBy h r) = fun g =>
        (h : Matrix (Fin 3) (Fin 3) R) * mats r g *
          ((sgnAct 3 R (η g) h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
      funext g
      rw [mats_conjBy, hr.mult g]
    rw [hfun]
    exact IsLocallyConstant.comp₂ hm hη fun M s =>
      (h : Matrix (Fin 3) (Fin 3) R) * M * ((sgnAct 3 R s h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
end

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia

private theorem lc_hom {R D : Type} [CommRing R] [Group D] [TopologicalSpace D] (η : D →* ℤˣ) (r : D →* GG (m := 3) (R := R))
    (hη : IsLocallyConstant η) (hm : HasMult η r) (hr : IsLocallyConstant (mats r)) : IsLocallyConstant r := by
  rw [IsLocallyConstant.iff_eventually_eq] at *
  intro x
  filter_upwards [hη x, hr x] with y h1 h2
  apply SemidirectProduct.ext
  · apply Units.ext
    exact h2
  · rw [hm y, hm x]
    exact h1

private theorem gg_ext {R : Type} [CommRing R] {x y : GG (m := 3) (R := R)} (h : x.mat = y.mat) (h' : x.right = y.right) : x = y :=
  SemidirectProduct.ext (Units.ext h) h'

private theorem wt_self (a : Fin 3) : wt a a = 0 := sub_self _

private theorem isUnit_of_isUnit_surjective_localRingHom {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (p : R →+* R') (hp : Function.Surjective p) (a : R) (h : IsUnit (p a)) : IsUnit a := by
  by_contra ha
  obtain ⟨u, hu⟩ := h
  obtain ⟨b, hb⟩ := hp (↑u⁻¹ : R')
  have hk : a * b - 1 ∈ RingHom.ker p := by
    rw [RingHom.mem_ker, RingHom.map_sub, map_mul, hb, ← hu, map_one]
    simp
  have hker : RingHom.ker p ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top p)
  have h1 : a * b ∈ maximalIdeal R := Ideal.mul_mem_right b _ ((IsLocalRing.mem_maximalIdeal a).2 ha)
  have h2 := Ideal.sub_mem _ h1 (hker hk)
  rw [sub_sub_cancel] at h2
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h2)

private theorem lift_elt {O R R' : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing R']
    [IsLocalRing R'] [Algebra O R'] (𝒜 : ℤ → Submodule O R) (p : R →ₐ[O] R') (hp : Function.Surjective p)
    (y : GG (m := 3) (R := R')) (t : GG (m := 3) (R := R)) (hy : ∀ a b, wt a b < 0 → y.mat a b = 0) (hX : ∃ X, GrMat 𝒜 X ∧ X.map p = y.mat)
    (ht : ∀ a, t.mat a a ∈ 𝒜 0) (hty : ∀ a, p (t.mat a a) = y.mat a a) :
    ∃ x : GG (m := 3) (R := R), GG.map (p : R →+* R') x = y ∧ GrMat 𝒜 x.mat ∧ (∀ a b, wt a b < 0 → x.mat a b = 0) ∧
      ∀ a, x.mat a a = t.mat a a := by
  classical
  obtain ⟨X, hXg, hXp⟩ := hX
  let M : Matrix (Fin 3) (Fin 3) R := fun a b => if wt a b < 0 then 0 else if a = b then t.mat a a else X a b
  have hMp : M.map (p : R →+* R') = y.mat := by
    ext a b
    show (p : R →+* R') (M a b) = y.mat a b
    simp only [M]
    split_ifs with h1 h2
    · rw [map_zero, hy a b h1]
    · subst h2
      exact hty a
    · rw [← hXp]
      rfl
  have hdet : IsUnit M.det := by
    apply isUnit_of_isUnit_surjective_localRingHom (p : R →+* R') hp
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hMp]
    exact Matrix.isUnits_det_units y.left
  refine ⟨⟨Matrix.nonsingInvUnit M hdet, y.right⟩, ?_, ?_, ?_, ?_⟩
  · apply SemidirectProduct.ext
    · apply Units.ext
      exact hMp
    · rfl
  · intro a b
    show M a b ∈ _
    simp only [M]
    split_ifs with h1 h2
    · exact Submodule.zero_mem _
    · subst h2
      rw [wt_self]
      exact ht a
    · exact hXg a b
  · intro a b h
    show M a b = 0
    simp [M, h]
  · intro a
    show M a a = t.mat a a
    simp [M, wt_self]

private theorem gr_eq_zero {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (𝒜 : ℤ → Submodule O R)
    [GradedAlgebra 𝒜] {i j : ℤ} {x : R} (hi : x ∈ 𝒜 i) (hj : x ∈ 𝒜 j) (h : i ≠ j) : x = 0 := by
  have h1 := DirectSum.decompose_of_mem_same 𝒜 hj
  have h2 := DirectSum.decompose_of_mem_ne 𝒜 hi h
  rw [h2] at h1
  exact h1.symm

private theorem grMat_mul {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (𝒜 : ℤ → Submodule O R)
    [GradedAlgebra 𝒜] {X Y : Matrix (Fin 3) (Fin 3) R} (hX : GrMat 𝒜 X) (hY : GrMat 𝒜 Y) : GrMat 𝒜 (X * Y) := by
  intro a b
  rw [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  have h := SetLike.mul_mem_graded (hX a c) (hY c b)
  have e : wt a c + wt c b = wt a b := by
    simp only [wt]
    ring
  rwa [e] at h

private theorem strict_mul {R : Type} [CommRing R] {b X : Matrix (Fin 3) (Fin 3) R}
    (hb : ∀ a c, wt a c ≤ 0 → b a c = 0) (hX : ∀ a c, wt a c < 0 → X a c = 0) (a c : Fin 3) (h : wt a c ≤ 0) :
    ((1 + b) * X) a c = X a c := by
  rw [add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero, add_zero]
  intro d _
  by_cases hd : wt a d ≤ 0
  · rw [hb a d hd, zero_mul]
  · have e : wt a d + wt d c = wt a c := by
      simp only [wt]
      ring
    have hlt : wt d c < 0 := by omega
    rw [hX d c hlt, mul_zero]

private theorem psi_lc {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Finite R]
    [TopologicalSpace D] (f : D → O)
    (hf : ∀ n : ℕ, IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal O ^ n) (f g)) :
    IsLocallyConstant fun g => algebraMap O R (f g) := by
  have hloc : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have hnil : IsNilpotent (Ideal.jacobson (⊥ : Ideal R)) := IsArtinianRing.isNilpotent_jacobson_bot
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hnil
  obtain ⟨n, hn⟩ := hnil
  have hle : Ideal.map (algebraMap O R) (maximalIdeal O ^ n) ≤ maximalIdeal R ^ n := by
    rw [Ideal.map_pow]
    apply Ideal.pow_right_mono
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact map_nonunit (algebraMap O R) x hx
  have hker : ∀ x ∈ maximalIdeal O ^ n, algebraMap O R x = 0 := by
    intro x hx
    have h := hle (Ideal.mem_map_of_mem _ hx)
    rw [hn] at h
    simpa using h
  have h := (hf n).comp (Ideal.Quotient.lift (maximalIdeal O ^ n) (algebraMap O R) hker)
  exact h

private theorem gg_mul_mat_of_right_eq_one {R : Type} [CommRing R] (z v : GG (m := 3) (R := R)) (h : z.right = 1) :
    (z * v).mat = z.mat * v.mat := by
  show ((z * v).left : Matrix (Fin 3) (Fin 3) R) = _
  rw [SemidirectProduct.mul_left, h, map_one]
  rfl

private theorem eq_of_wt_eq_zero (a b : Fin 3) (h : wt a b = 0) : a = b := by
  fin_cases a <;> fin_cases b <;> simp_all [wt, wt1]

private theorem tri_lift {O R R' D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
    (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (p : R →ₐ[O] R') (j : ℤ) (hp : Function.Surjective p)
    (hs : SmallExt O 𝒜 (RingHom.ker p) j) (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (φ : D)
    (hφ : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1)
    (hη : IsLocallyConstant η) (hηI : ∀ s ∈ I, η s = 1) (hΨ : IsLocallyConstant fun g => algebraMap O R (Ψ g : O))
    (h2 : 0 < j → Subsingleton (H2 (gRep η ((Units.map (residue O).toMonoidHom).comp Ψ) j)))
    (r' : D →* GG (m := 3) (R := R')) (hr : Red η Ψ r') (hlc : IsLocallyConstant (mats r'))
    (hup : ∀ g a b, wt a b < 0 → (r' g).mat a b = 0)
    (hI : ∀ s ∈ I, ∀ a, (r' s).mat a a = algebraMap O R' (psi Ψ a s))
    (hgr : ∀ g, ∃ X, GrMat 𝒜 X ∧ X.map p = (r' g).mat) :
    ∃ r : D →* GG (m := 3) (R := R), push p r = r' ∧ IsLocallyConstant (mats r) ∧ (∀ g, GrMat 𝒜 (r g).mat) ∧
      (∀ g a b, wt a b < 0 → (r g).mat a b = 0) ∧ ∀ s ∈ I, ∀ a, (r s).mat a a = algebraMap O R (psi Ψ a s) := by
  classical
  haveI : Finite R := hs.fin
  haveI : Finite R' := Finite.of_surjective p hp
  obtain ⟨B, dg, hB, hdg⟩ := lt_diag (R := R')
  obtain ⟨B0, dg0, hB0, hdg0⟩ := lt_diag (R := R)
  obtain ⟨S, hS⟩ := lt_grSub (O := O) 𝒜
  let rB : D →* B := r'.codRestrict B (fun g => (hB _).2 (hup g))
  let u' : D →* GG (m := 3) (R := R') := dg.comp rB
  have hu'mat : ∀ g, (u' g).mat = Matrix.diagonal fun a => (r' g).mat a a := fun g => (hdg (rB g)).2
  have hu'right : ∀ g, (u' g).right = η g := fun g => (hdg (rB g)).1.trans (hr.mult g)
  have hu'lc : IsLocallyConstant (mats u') := by
    have e : mats u' = (fun M : Matrix (Fin 3) (Fin 3) R' => Matrix.diagonal fun a => M a a) ∘ mats r' :=
      funext hu'mat
    rw [e]
    exact hlc.comp _
  have hu'diag : ∀ g, (u' g).mat.IsDiag := by
    intro g
    rw [hu'mat]
    exact Matrix.isDiag_diagonal _
  have hu'A : ∀ g a, ∃ y ∈ SetLike.GradeZero.subalgebra 𝒜, p y = (u' g).mat a a := by
    intro g a
    obtain ⟨X, hX, hXp⟩ := hgr g
    refine ⟨X a a, ?_, ?_⟩
    · have h := hX a a
      rw [wt_self] at h
      exact h
    · rw [hu'mat, Matrix.diagonal_apply_eq, ← hXp]
      rfl
  have hu'I : ∀ s ∈ I, ∀ a, (u' s).mat a a = algebraMap O R' (psi Ψ a s) := by
    intro s hsI a
    rw [hu'mat, Matrix.diagonal_apply_eq, hI s hsI a]
  obtain ⟨u, hpu, hulc, hudiag, huA, huI⟩ := lt_torus (SetLike.GradeZero.subalgebra 𝒜) p hp η Ψ I φ hφ hd hη hηI hΨ
    u' hu'right hu'lc hu'diag hu'A hu'I
  have hur : ∀ g, (u g).right = η g := fun g =>
    (congrArg SemidirectProduct.right (DFunLike.congr_fun hpu g)).trans (hu'right g)
  have hupm : ∀ g, (u g).mat.map p = (u' g).mat := fun g =>
    congrArg GG.mat (DFunLike.congr_fun hpu g)
  let P : GG (m := 3) (R := R') → GG (m := 3) (R := R) → GG (m := 3) (R := R) → Prop := fun y t x =>
    GG.map (p : R →+* R') x = y ∧ GrMat 𝒜 x.mat ∧ (∀ a b, wt a b < 0 → x.mat a b = 0) ∧ ∀ a, x.mat a a = t.mat a a
  let L : GG (m := 3) (R := R') → GG (m := 3) (R := R) → GG (m := 3) (R := R) := fun y t => if h : ∃ x, P y t x then h.choose else 1
  let s : D → GG (m := 3) (R := R) := fun g => L (r' g) (u g)
  have hsP : ∀ g, P (r' g) (u g) (s g) := by
    intro g
    have h : ∃ x, P (r' g) (u g) x := by
      apply lift_elt 𝒜 p hp (r' g) (u g) (hup g) (hgr g)
      · intro a
        exact huA g a
      · intro a
        have h1 := congrFun (congrFun (hupm g) a) a
        rw [hu'mat, Matrix.diagonal_apply_eq] at h1
        exact h1
    simp only [s, L, dif_pos h]
    exact h.choose_spec
  have hr'lc : IsLocallyConstant r' := lc_hom η r' hη hr.mult hlc
  have hulc' : IsLocallyConstant u := lc_hom η u hη hur hulc
  have hslc : IsLocallyConstant s := (hr'lc.prodMk hulc').comp (fun q => L q.1 q.2)
  have hsr : ∀ g, (s g).right = η g := fun g =>
    (congrArg SemidirectProduct.right (hsP g).1).trans (hr.mult g)
  have hsred : ∀ g, EntIn (maximalIdeal R) ((s g).mat - ((r0 η Ψ) g).mat.map (algebraMap O R)) := by
    intro g a b
    have h1 := hr.red g a b
    by_contra hn
    have hu : IsUnit (((s g).mat - ((r0 η Ψ) g).mat.map (algebraMap O R)) a b) := by
      by_contra h
      exact hn ((IsLocalRing.mem_maximalIdeal _).2 h)
    apply (IsLocalRing.mem_maximalIdeal _).1 h1
    have e : p (((s g).mat - ((r0 η Ψ) g).mat.map (algebraMap O R)) a b) =
        ((r' g).mat - ((r0 η Ψ) g).mat.map (algebraMap O R')) a b := by
      rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.map_apply, AlgHom.commutes]
      congr 1
      rw [← (hsP g).1]
      rfl
    rw [← e]
    exact hu.map p
  have hsB : ∀ g, s g ∈ B0 := fun g => (hB0 _).2 (hsP g).2.2.1
  have hsS : ∀ g, s g ∈ S := fun g => (hS _).2 (hsP g).2.1
  have hdgs : ∀ g, dg0 ⟨s g, hsB g⟩ = u g := by
    intro g
    apply gg_ext
    · rw [(hdg0 _).2, ← (hudiag g).diagonal_diag]
      congr 1
      funext a
      exact (hsP g).2.2.2 a
    · rw [(hdg0 _).1]
      exact (hsr g).trans (hur g).symm
  have hone : ∀ a b, (1 : Matrix (Fin 3) (Fin 3) R) a b ∈ 𝒜 (wt a b) := by
    intro a b
    rw [Matrix.one_apply]
    split_ifs with hab
    · subst hab
      rw [wt_self]
      exact SetLike.GradedOne.one_mem
    · exact Submodule.zero_mem _
  have hcoc : ∀ g h, ∃ c : Matrix (Fin 3) (Fin 3) R, c ∈ gw R j ∧ EntIn (RingHom.ker p) c ∧
      (∀ a, c a a = 0) ∧ (∀ a b, wt a b < 0 → c a b = 0) ∧
      (s g * s h).mat = (1 + c) * (s (g * h)).mat := by
    intro g h
    set z := s g * s h * (s (g * h))⁻¹ with hz
    have hzr : z.right = 1 := by
      simp only [hz, SemidirectProduct.mul_right, SemidirectProduct.inv_right, hsr, map_mul]
      exact mul_inv_cancel _
    have hzB : z ∈ B0 := B0.mul_mem (B0.mul_mem (hsB g) (hsB h)) (B0.inv_mem (hsB _))
    have hzS : z ∈ S := S.mul_mem (S.mul_mem (hsS g) (hsS h)) (S.inv_mem (hsS _))
    have hzp : GG.map (p : R →+* R') z = 1 := by
      simp only [hz, map_mul, map_inv, (hsP _).1, r'.map_mul, mul_inv_cancel]
    have hzd : ∀ a, z.mat a a = 1 := by
      intro a
      have e : dg0 ⟨z, hzB⟩ = 1 := by
        have e0 : (⟨z, hzB⟩ : B0) = ⟨s g, hsB g⟩ * ⟨s h, hsB h⟩ * (⟨s (g * h), hsB _⟩)⁻¹ := rfl
        rw [e0, map_mul, map_mul, map_inv, hdgs, hdgs, hdgs, ← u.map_mul, mul_inv_cancel]
      have e2 := (hdg0 ⟨z, hzB⟩).2
      rw [e] at e2
      have e3 := congrFun (congrFun e2 a) a
      have e4 : (1 : GG (m := 3) (R := R)).mat = 1 := rfl
      rw [e4, Matrix.one_apply_eq, Matrix.diagonal_apply_eq] at e3
      exact e3.symm
    have hzK : ∀ a b, (z.mat - 1) a b ∈ RingHom.ker p := by
      intro a b
      rw [RingHom.mem_ker, Matrix.sub_apply, map_sub]
      have e1 : p (z.mat a b) = (GG.map (p : R →+* R') z).mat a b := rfl
      rw [e1, hzp]
      change (1 : Matrix (Fin 3) (Fin 3) R') a b - p ((1 : Matrix (Fin 3) (Fin 3) R) a b) = 0
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have hzg : GrMat 𝒜 z.mat := (hS z).1 hzS
    refine ⟨z.mat - 1, ?_, hzK, ?_, ?_, ?_⟩
    · intro a b hne
      exact gr_eq_zero 𝒜 (Submodule.sub_mem _ (hzg a b) (hone a b)) (hs.wt _ (hzK a b)) hne
    · intro a
      rw [Matrix.sub_apply, hzd, Matrix.one_apply_eq, sub_self]
    · intro a b hab
      have hne : a ≠ b := by
        rintro rfl
        rw [wt_self] at hab
        exact lt_irrefl _ hab
      rw [Matrix.sub_apply, (hB0 z).1 hzB a b hab, Matrix.one_apply_ne hne, sub_self]
    · rw [add_sub_cancel, ← gg_mul_mat_of_right_eq_one z (s (g * h)) hzr, hz, inv_mul_cancel_right]
  obtain ⟨r, hrlc, hrg⟩ : ∃ r : D →* GG (m := 3) (R := R), IsLocallyConstant (mats r) ∧ ∀ g, (r g).right = η g ∧
      ∃ b : Matrix (Fin 3) (Fin 3) R, (∀ a c, wt a c ≤ 0 → b a c = 0) ∧ EntIn (RingHom.ker p) b ∧
        GrMat 𝒜 b ∧ (r g).mat = (1 + b) * (s g).mat := by
    by_cases hj : 0 < j
    · obtain ⟨r, hrlc, hrg⟩ := lt_corr η Ψ (RingHom.ker p) j hs.kill hs.le (h2 hj) s hslc hsr hsred
        (fun g h => by
          obtain ⟨c, hc, hcK, -, -, hce⟩ := hcoc g h
          exact ⟨c, hc, hcK, hce⟩)
      refine ⟨r, hrlc, fun g => ⟨(hrg g).1, ?_⟩⟩
      obtain ⟨b, hb, hbK, hbe⟩ := (hrg g).2
      refine ⟨b, ?_, hbK, ?_, hbe⟩
      · intro a c hac
        exact hb a c (by omega)
      · intro a c
        by_cases hw : wt a c = j
        · rw [hw]
          exact hs.wt _ (hbK a c)
        · rw [hb a c hw]
          exact Submodule.zero_mem _
    · have hmul : ∀ g h, s (g * h) = s g * s h := by
        intro g h
        obtain ⟨c, hc, -, hcd, hcl, hce⟩ := hcoc g h
        have hc0 : c = 0 := by
          ext a b
          by_cases hw : wt a b = j
          · by_cases hab : a = b
            · subst hab
              exact hcd a
            · have hlt : wt a b < 0 := by
                have := mt (eq_of_wt_eq_zero a b) hab
                omega
              exact hcl a b hlt
          · exact hc a b hw
        apply gg_ext
        · rw [hce, hc0, add_zero, one_mul]
        · rw [SemidirectProduct.mul_right, hsr, hsr, hsr, map_mul]
      refine ⟨MonoidHom.mk' s hmul, hslc.comp GG.mat, fun g => ⟨hsr g, 0, fun _ _ _ => rfl,
        fun a b => Ideal.zero_mem _, fun a b => Submodule.zero_mem _, ?_⟩⟩
      rw [add_zero, one_mul]
      rfl
  refine ⟨r, ?_, hrlc, ?_, ?_, ?_⟩
  · ext g : 1
    apply gg_ext
    · obtain ⟨b, -, hbK, -, hbe⟩ := (hrg g).2
      change (r g).mat.map (p : R →+* R') = (r' g).mat
      rw [hbe, Matrix.map_mul, ← (hsP g).1]
      have hb0 : (1 + b).map (p : R →+* R') = 1 := by
        ext a c
        change p ((1 + b) a c) = (1 : Matrix (Fin 3) (Fin 3) R') a c
        rw [Matrix.add_apply, map_add (f := _), RingHom.mem_ker.1 (hbK a c), add_zero, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [hb0, one_mul]
      rfl
    · change (r g).right = (r' g).right
      rw [(hrg g).1, hr.mult g]
  · intro g
    obtain ⟨b, -, -, hbg, hbe⟩ := (hrg g).2
    rw [hbe]
    apply grMat_mul 𝒜 _ (hsP g).2.1
    intro a c
    rw [Matrix.add_apply]
    exact Submodule.add_mem _ (hone a c) (hbg a c)
  · intro g a c hac
    obtain ⟨b, hb, -, -, hbe⟩ := (hrg g).2
    rw [hbe, strict_mul hb (hsP g).2.2.1 a c hac.le]
    exact (hsP g).2.2.1 a c hac
  · intro t ht a
    obtain ⟨b, hb, -, -, hbe⟩ := (hrg t).2
    rw [hbe, strict_mul hb (hsP t).2.2.1 a a (by rw [wt_self]), (hsP t).2.2.2 a, huI t ht a]

private theorem lift_gg {O R R' : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing R']
    [IsLocalRing R'] [Algebra O R'] (p : R →ₐ[O] R') (hp : Function.Surjective p)
    (y : GG (m := 3) (R := R')) (M : Matrix (Fin 3) (Fin 3) R) (hM : M.map p = y.mat) :
    ∃ x : GG (m := 3) (R := R), GG.map (p : R →+* R') x = y ∧ x.mat = M := by
  have hdet : IsUnit M.det := by
    apply isUnit_of_isUnit_surjective_localRingHom (p : R →+* R') hp
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    have e : M.map (p : R →+* R') = y.mat := hM
    rw [e]
    exact Matrix.isUnits_det_units y.left
  refine ⟨⟨Matrix.nonsingInvUnit M hdet, y.right⟩, ?_, rfl⟩
  apply SemidirectProduct.ext
  · apply Units.ext
    exact hM
  · rfl

private theorem conjBy_app {C D : Type} [CommRing C] [Group D] (h : GL (Fin 3) C) (r : D →* GG (m := 3) (R := C)) (g : D) :
    conjBy h r g = GG.ofGL h * r g * (GG.ofGL h)⁻¹ := rfl

private theorem map_ofGL {C C' : Type} [CommRing C] [CommRing C'] (f : C →+* C') (h : GL (Fin 3) C) :
    GG.map f (GG.ofGL h) = GG.ofGL (GeneralLinearGroup.map f h) := by
  simp [GG.map, GG.ofGL, SemidirectProduct.map_inl]

end UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.exists_graded_lift_unitary_local_tame :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → ∀ {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (p : R →ₐ[O] R') (j : ℤ), Function.Surjective p → SmallExt O 𝒜 (RingHom.ker p) j →
    ∀ (v : ι), v = F.vl → ∀ (r' : F.D v →* GG (m := 3) (R := R')), Red (F.ηv v) (F.Ψv v) r' → F.LocAt v r' → IsLocallyConstant (mats r') →
      (∀ g, ∃ X, GrMat 𝒜 X ∧ X.map p = (r' g).mat) →
      ∃ r : F.D v →* GG (m := 3) (R := R), push p r = r' ∧ F.LocAt v r ∧ IsLocallyConstant (mats r) ∧ ∀ g, GrMat 𝒜 (r g).mat := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF hV R R' _ _ _ _ _ _ 𝒜 _ p j hp hs v hv r' hr hloc hlc hgr
  subst hv
  classical
  haveI : Finite R := hs.fin
  have hvT : F.vl ∈ F.Tb := Set.mem_insert _ _
  have hlocc : Continuous (F.loc F.vl) := hF.π_cont.comp continuous_subtype_val
  have hηlc : IsLocallyConstant (F.ηv F.vl) := hF.η_cont.comp_continuous hlocc
  obtain ⟨x, hx1, hx2⟩ := hF.x F.vl hvT
  obtain ⟨h, hhin, hhg, hh'in, hhtri⟩ := lt_basis 𝒜 p hp (F.ηv F.vl) (F.Ψv F.vl) (F.Iv F.vl) r' x hr hx1 hx2
    (hloc.1 rfl) (hgr x)
  set h' := GeneralLinearGroup.map (p : R →+* R') h with hh'
  obtain ⟨hinv, -, -⟩ := lt_red_conj (F.ηv F.vl) (F.Ψv F.vl) r' h' hh'in hr
  obtain ⟨-, hr'', hlc''⟩ := lt_red_conj (F.ηv F.vl) (F.Ψv F.vl) r' h'⁻¹ hinv hr
  have hup : ∀ g a b, wt a b < 0 → ((conjBy h'⁻¹ r') g).mat a b = 0 :=
    lt_upper _ _ _ x hr'' hx1 hx2 hhtri.tri
  have hI : ∀ s ∈ F.Iv F.vl, ∀ a, ((conjBy h'⁻¹ r') s).mat a a = algebraMap O R' (psi (F.Ψv F.vl) a s) :=
    fun s hs a => hhtri.ine s hs (hF.η_I F.vl hvT s hs) a
  obtain ⟨S, hS⟩ := lt_grSub (O := O) 𝒜
  have hhS : GG.ofGL h ∈ S := (hS _).2 hhg
  have hmapS : GG.map (p : R →+* R') (GG.ofGL h) = GG.ofGL h' := map_ofGL _ h
  have hgr'' : ∀ g, ∃ X, GrMat 𝒜 X ∧ X.map p = ((conjBy h'⁻¹ r') g).mat := by
    intro g
    obtain ⟨X, hX, hXp⟩ := hgr g
    obtain ⟨y, hy, hyX⟩ := lift_gg p hp (r' g) X hXp
    have hyS : y ∈ S := (hS _).2 (hyX ▸ hX)
    refine ⟨((GG.ofGL h)⁻¹ * y * GG.ofGL h).mat, (hS _).1 (S.mul_mem (S.mul_mem (S.inv_mem hhS) hyS) hhS), ?_⟩
    change (GG.map (p : R →+* R') ((GG.ofGL h)⁻¹ * y * GG.ofGL h)).mat = _
    rw [map_mul, map_mul, map_inv, hmapS, hy, conjBy_app, map_inv, inv_inv]
  have hΨ : IsLocallyConstant fun g => algebraMap O R ((F.Ψv F.vl g : Oˣ) : O) :=
    psi_lc (fun g => ((F.Ψv F.vl g : Oˣ) : O)) (fun n => (hF.Ψ_cont n).comp_continuous hlocc)
  have h2 : 0 < j → Subsingleton (H2 (gRep (F.ηv F.vl)
      ((Units.map (residue O).toMonoidHom).comp (F.Ψv F.vl)) j)) :=
    fun hj => hV.h2 F.vl hvT j (ne_of_gt hj)
  obtain ⟨φ, hφ, hd⟩ := hF.frob F.vl
  obtain ⟨r0', hpush, hlc0, hgr0, hup0, hI0⟩ := tri_lift 𝒜 p j hp hs (F.ηv F.vl) (F.Ψv F.vl) (F.Iv F.vl) φ hφ hd
    hηlc (hF.η_I F.vl hvT) hΨ h2 (conjBy h'⁻¹ r') hr'' (hlc'' hηlc hlc) hup hI hgr''
  have hr0r : ∀ g, (r0' g).right = F.ηv F.vl g := fun g =>
    (congrArg SemidirectProduct.right (DFunLike.congr_fun hpush g)).trans (hr''.mult g)
  have hr0lc : IsLocallyConstant r0' := lc_hom _ r0' hηlc hr0r hlc0
  have hback : conjBy h⁻¹ (conjBy h r0') = r0' := by
    ext g : 1
    rw [conjBy_app, conjBy_app, map_inv]
    group
  refine ⟨conjBy h r0', ?_, ?_, ?_, ?_⟩
  · ext g : 1
    change GG.map (p : R →+* R') ((conjBy h r0') g) = r' g
    rw [conjBy_app, map_mul, map_mul, map_inv, hmapS]
    have e := DFunLike.congr_fun hpush g
    change GG.map (p : R →+* R') (r0' g) = (conjBy h'⁻¹ r') g at e
    rw [e, conjBy_app, map_inv, inv_inv]
    group
  · unfold Frame.LocAt
    refine ⟨fun _ => ⟨h, hhin, ?_, ?_⟩, fun hSb => absurd hSb hF.vl_notMem, fun hT => absurd hvT hT⟩
    · rw [hback]
      intro g _ a b hab
      exact hup0 g a b hab
    · rw [hback]
      intro s hs _ a
      exact hI0 s hs a
  · have e : mats (conjBy h r0') = GG.mat ∘ (fun y => GG.ofGL h * y * (GG.ofGL h)⁻¹) ∘ r0' := by
      funext g
      show ((conjBy h r0') g).mat = (GG.ofGL h * r0' g * (GG.ofGL h)⁻¹).mat
      rw [conjBy_app]
    rw [e]
    exact (hr0lc.comp _).comp _
  · intro g
    rw [conjBy_app]
    exact (hS _).1 (S.mul_mem (S.mul_mem hhS ((hS _).2 (hgr0 g))) (S.inv_mem hhS))
