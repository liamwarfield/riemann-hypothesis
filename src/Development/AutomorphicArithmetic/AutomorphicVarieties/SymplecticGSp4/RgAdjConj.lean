module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MemOfInt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpFlag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CrystallineTransferSurjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LevBasis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TbTriDiag
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OrdLocal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement.OrdinaryLocal

open Polynomial

variable {B : Type} [CommRing B]

private theorem aeval_conj (u : (M4 B)ˣ) (X : M4 B) (p : B[X]) :
    aeval ((u : M4 B) * X * (u⁻¹ : (M4 B)ˣ)) p = (u : M4 B) * aeval X p * (u⁻¹ : (M4 B)ˣ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, mul_add, add_mul]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, Units.conj_pow, ← Algebra.smul_def, ← Algebra.smul_def, mul_smul_comm,
      smul_mul_assoc]

private theorem prj_conj (c : Fin 4 → B) (u : (M4 B)ˣ) (X : M4 B) (i : Fin 4) :
    prj c ((u : M4 B) * X * (u⁻¹ : (M4 B)ˣ)) i = (u : M4 B) * prj c X i * (u⁻¹ : (M4 B)ˣ) :=
  aeval_conj u X _

private theorem eig_left (c : Fin 4 → B) (X : M4 B) (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i : Fin 4) :
    (X - c i • (1 : M4 B)) * prj c X i = 0 := by
  have h1 := Matrix.aeval_self_charpoly X
  rw [h, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), map_mul, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one] at h1
  exact h1

private theorem eig_right (c : Fin 4 → B) (X : M4 B) (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i : Fin 4) :
    prj c X i * (X - c i • (1 : M4 B)) = 0 := by
  have h1 := Matrix.aeval_self_charpoly X
  rw [h, ← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i), map_mul, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one] at h1
  exact h1

private theorem aeval_sub (X : M4 B) (a : B) (p : B[X]) :
    ∃ Y : M4 B, aeval X p - p.eval a • (1 : M4 B) = Y * (X - a • (1 : M4 B)) := by
  obtain ⟨s, hs⟩ : Polynomial.X - C a ∣ p - C (p.eval a) := X_sub_C_dvd_sub_C_eval
  refine ⟨aeval X s, ?_⟩
  have h := congrArg (aeval X) hs
  rw [mul_comm, map_mul, map_sub, map_sub, aeval_X, aeval_C, aeval_C, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one] at h
  exact h

private theorem prj_sub (c : Fin 4 → B) (X : M4 B) (i j : Fin 4) :
    ∃ Y : M4 B, prj c X i - (∏ a ∈ Finset.univ.erase i, (c j - c a)) • (1 : M4 B) = Y * (X - c j • (1 : M4 B)) := by
  obtain ⟨Y, hY⟩ := aeval_sub X (c j) (∏ a ∈ Finset.univ.erase i, (Polynomial.X - C (c a)))
  refine ⟨Y, ?_⟩
  rw [← hY, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rfl

private theorem prj_mul (c : Fin 4 → B) (X : M4 B) (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i j : Fin 4) :
    prj c X i * prj c X j = (∏ a ∈ Finset.univ.erase i, (c j - c a)) • prj c X j := by
  obtain ⟨Y, hY⟩ := prj_sub c X i j
  have h1 := congrArg (· * prj c X j) hY
  simp only [mul_assoc, eig_left c X h j, mul_zero, sub_mul, smul_mul_assoc, one_mul] at h1
  exact sub_eq_zero.mp h1

private theorem unit_d (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (i : Fin 4) :
    IsUnit (∏ a ∈ Finset.univ.erase i, (c i - c a)) :=
  IsUnit.prod_iff.mpr fun a ha => hc i a (Finset.ne_of_mem_erase ha).symm

private theorem zero_d (c : Fin 4 → B) {i j : Fin 4} (hij : j ≠ i) :
    (∏ a ∈ Finset.univ.erase i, (c j - c a)) = 0 :=
  Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩) (sub_self _)

private theorem det_eig (c : Fin 4 → B) (X : M4 B) (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i : Fin 4) :
    (X - c i • (1 : M4 B)).det = 0 := by
  have h1 := Matrix.eval_charpoly X (c i)
  rw [h, eval_prod, Finset.prod_eq_zero (Finset.mem_univ i) (by simp)] at h1
  have h2 : X - c i • (1 : M4 B) = -(Matrix.scalar (Fin 4) (c i) - X) := by
    rw [neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [h2, Matrix.det_neg, ← h1, mul_zero]

private theorem exists_unit [IsLocalRing B] (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (X : M4 B)
    (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) (i : Fin 4) : ∃ ab : Fin 4 × Fin 4, IsUnit (prj c X i ab.1 ab.2) := by
  by_contra hn
  push Not at hn
  obtain ⟨Y, hY⟩ := prj_sub c X i i
  have h1 := congrArg Matrix.det hY
  rw [Matrix.det_mul, det_eig c X h i, mul_zero] at h1
  have h2 := congrArg (residue B) h1
  set d := ∏ a ∈ Finset.univ.erase i, (c i - c a) with hd
  have h3 : (residue B).mapMatrix (prj c X i - d • (1 : M4 B)) = Matrix.diagonal fun _ => -residue B d := by
    ext a b
    have h0 : residue B (prj c X i a b) = 0 := (residue_eq_zero_iff _).mpr (hn (a, b))
    by_cases hab : a = b
    · subst hab; simp [h0]
    · simp [h0, hab]
  rw [RingHom.map_det, h3, Matrix.det_diagonal, map_zero, Finset.prod_eq_zero_iff] at h2
  obtain ⟨_, -, h4⟩ := h2
  exact ((unit_d c hc i).map (residue B)).ne_zero (neg_eq_zero.mp h4)

private theorem diagonalize [IsLocalRing B] (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (X : M4 B)
    (h : X.charpoly = ∏ j, (Polynomial.X - C (c j))) :
    ∃ u : (M4 B)ˣ, (u : M4 B) * X * (u⁻¹ : (M4 B)ˣ) = Matrix.diagonal c := by
  choose ab hab using exists_unit c hc X h
  let P : M4 B := Matrix.of fun x j => prj c X j x (ab j).2
  let Q : M4 B := Matrix.of fun i x => prj c X i (ab i).1 x
  have hQP : Q * P = Matrix.diagonal fun i => (∏ a ∈ Finset.univ.erase i, (c i - c a)) * prj c X i (ab i).1 (ab i).2 := by
    ext i j
    have h1 : (Q * P) i j = (prj c X i * prj c X j) (ab i).1 (ab j).2 := rfl
    rw [h1, prj_mul c X h]
    by_cases hij : i = j
    · subst hij; simp
    · rw [zero_d c (Ne.symm hij), Matrix.diagonal_apply_ne _ hij]; simp
  have hdet : IsUnit (Q * P).det := by
    rw [hQP, Matrix.det_diagonal]
    exact IsUnit.prod_iff.mpr fun a _ => (unit_d c hc a).mul (hab a)
  rw [Matrix.det_mul] at hdet
  obtain ⟨v, hv⟩ := (Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_of_mul_isUnit_right hdet)
  have hXP : X * P = P * Matrix.diagonal c := by
    ext x j
    have h1 : (X * P) x j = (X * prj c X j) x (ab j).2 := rfl
    have h2 := eig_left c X h j
    rw [sub_mul, sub_eq_zero, smul_mul_assoc, one_mul] at h2
    rw [h1, h2, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, mul_comm]
    rfl
  refine ⟨v⁻¹, ?_⟩
  rw [inv_inv, mul_assoc, hv, hXP, ← hv, Units.inv_mul_cancel_left]

private theorem prj_diag (c : Fin 4 → B) (i : Fin 4) :
    prj c (Matrix.diagonal c) i = Matrix.diagonal fun x => ∏ a ∈ Finset.univ.erase i, (c x - c a) := by
  have h1 : Matrix.diagonal c = Matrix.diagonalAlgHom B c := rfl
  unfold prj
  rw [h1, aeval_algHom_apply]
  show Matrix.diagonal _ = _
  congr 1
  funext x
  rw [map_prod, Finset.prod_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp

private theorem sandwich (c : Fin 4 → B) (u : (M4 B)ˣ) (X Y : M4 B) (i j : Fin 4) :
    prj c ((u : M4 B) * X * (u⁻¹ : (M4 B)ˣ)) j * ((u : M4 B) * Y * (u⁻¹ : (M4 B)ˣ)) *
      prj c ((u : M4 B) * X * (u⁻¹ : (M4 B)ˣ)) i = (u : M4 B) * (prj c X j * Y * prj c X i) * (u⁻¹ : (M4 B)ˣ) := by
  rw [prj_conj, prj_conj]
  simp only [mul_assoc, Units.inv_mul_cancel_left]

private theorem entry_zero (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (u : (M4 B)ˣ) (X Y : M4 B)
    (hu : (u : M4 B) * X * (u⁻¹ : (M4 B)ˣ) = Matrix.diagonal c) (i j : Fin 4) (h : prj c X j * Y * prj c X i = 0) :
    ((u : M4 B) * Y * (u⁻¹ : (M4 B)ˣ)) j i = 0 := by
  have h1 := sandwich c u X Y i j
  rw [h, mul_zero, zero_mul, hu, prj_diag, prj_diag] at h1
  have h2 := congrFun (congrFun h1 j) i
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.zero_apply, (unit_d c hc i).mul_left_eq_zero,
    (unit_d c hc j).mul_right_eq_zero] at h2
  exact h2

private theorem row_zero (T P : M4 B) (hT : ∀ i j, j < i → T i j = 0) (hP : T * P = 0) (i : Fin 4)
    (hu : ∀ a, i < a → IsUnit (T a a)) (b a : Fin 4) : i < a → P a b = 0 := by
  induction a using WellFoundedGT.induction with
  | ind a ih =>
    intro ha
    have h1 := congrFun (congrFun hP a) b
    rw [Matrix.mul_apply, Finset.sum_eq_single a, Matrix.zero_apply, (hu a ha).mul_right_eq_zero] at h1
    · exact h1
    · intro x _ hx
      rcases lt_or_gt_of_ne hx with h | h
      · rw [hT a x h, zero_mul]
      · rw [ih x h (ha.trans h), mul_zero]
    · simp

private theorem col_zero (T P : M4 B) (hT : ∀ i j, j < i → T i j = 0) (hP : P * T = 0) (i : Fin 4)
    (hu : ∀ a, a < i → IsUnit (T a a)) (b a : Fin 4) : a < i → P b a = 0 := by
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    intro ha
    have h1 := congrFun (congrFun hP b) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a, Matrix.zero_apply, (hu a ha).mul_left_eq_zero] at h1
    · exact h1
    · intro x _ hx
      rcases lt_or_gt_of_ne hx with h | h
      · rw [ih x h (h.trans ha), zero_mul]
      · rw [hT x a h, mul_zero]
    · simp

private theorem charpoly_tri (c : Fin 4 → B) (T : M4 B) (hT : ∀ i j, j < i → T i j = 0) (hd : ∀ i, T i i = c i) :
    T.charpoly = ∏ j, (Polynomial.X - C (c j)) := by
  rw [Matrix.charpoly_of_upperTriangular T (fun i j h => hT i j h)]
  simp only [hd]

private theorem tri_zero (c : Fin 4 → B) (hc : ∀ i j, i ≠ j → IsUnit (c i - c j)) (T R : M4 B)
    (hT : ∀ i j, j < i → T i j = 0) (hd : ∀ i, T i i = c i) (hR : ∀ i j, j < i → R i j = 0) (i j : Fin 4) (hij : i ≤ j)
    (h0 : R j i = 0) : prj c T j * R * prj c T i = 0 := by
  have hch := charpoly_tri c T hT hd
  have hT' : ∀ k i j, j < i → (T - c k • (1 : M4 B)) i j = 0 := fun k i j h => by
    simp [hT i j h, Matrix.one_apply_ne h.ne']
  have hu : ∀ k a, a ≠ k → IsUnit ((T - c k • (1 : M4 B)) a a) := fun k a h => by
    simpa [hd] using hc a k h
  have hrow := row_zero _ _ (hT' i) (eig_left c T hch i) i fun a h => hu i a h.ne'
  have hcol := col_zero _ _ (hT' j) (eig_right c T hch j) j fun a h => hu j a h.ne
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  rcases lt_or_ge i y with hy | hy
  · rw [hrow b y hy, mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro x _
    rcases lt_or_ge x j with hx | hx
    · rw [hcol a x hx, zero_mul]
    · rcases lt_or_ge y x with hxy | hxy
      · rw [hR x y hxy, mul_zero]
      · have e1 : x = j := le_antisymm (hxy.trans (hy.trans hij)) hx
        have e2 : y = i := le_antisymm hy (hij.trans (hx.trans hxy))
        rw [e1, e2, h0, mul_zero]

private theorem conj_sub (u : (M4 B)ˣ) (Y : M4 B) (a : B) :
    (u : M4 B) * (Y - a • (1 : M4 B)) * (u⁻¹ : (M4 B)ˣ) = (u : M4 B) * Y * (u⁻¹ : (M4 B)ˣ) - a • (1 : M4 B) := by
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, Units.mul_inv]

private theorem conj_zero (u : (M4 B)ˣ) (Y : M4 B) (h : (u : M4 B) * Y * (u⁻¹ : (M4 B)ˣ) = 0) : Y = 0 := by
  rwa [Units.mul_left_eq_zero, Units.mul_right_eq_zero] at h

end UpperTheory.V.GradeZeroInterpolatingElement.OrdinaryLocal

open UpperTheory.V.GradeZeroInterpolatingElement.OrdinaryLocal in
theorem UpperTheory.V.GradeZeroInterpolatingElement.ordLocal :
    ∀ {H : Type} [Group H] (I : Subgroup H) (B : Type) [CommRing B] [IsLocalRing B] (ps : Fin 4 → H → B) (s₀ : H) (r : H →* M4 B), s₀ ∈ I → (∀ i j, i ≠ j → IsUnit (ps i s₀ - ps j s₀)) → (Ord I ps s₀ r ↔ ∃ u : (M4 B)ˣ, (∀ g i j, j < i → ((u : M4 B) * r g * (u⁻¹ : (M4 B)ˣ)) i j = 0) ∧ ∀ s ∈ I, ∀ i, ((u : M4 B) * r s * (u⁻¹ : (M4 B)ˣ)) i i = ps i s) := by
  intro H _ I B _ _ ps s₀ r hs₀ hc
  constructor
  · intro h
    obtain ⟨u, hu⟩ := diagonalize (fun a => ps a s₀) hc (r s₀) h.charpoly
    refine ⟨u, fun g i j hij => entry_zero _ hc u _ _ hu j i (h.stable g j i hij), fun s hs i => ?_⟩
    have h1 := entry_zero _ hc u _ _ hu i i (h.inert s hs i)
    rw [conj_sub, Matrix.sub_apply, sub_eq_zero] at h1
    simpa using h1
  · rintro ⟨u, h1, h2⟩
    refine ⟨?_, fun g i j hij => ?_, fun s hs i => ?_⟩
    · have h3 := charpoly_tri (fun a => ps a s₀) _ (h1 s₀) (h2 s₀ hs₀)
      rw [← h3, Matrix.coe_units_inv]
      exact (Matrix.charpoly_units_conj u (r s₀)).symm
    · apply conj_zero u
      rw [← sandwich]
      exact tri_zero _ hc _ _ (h1 s₀) (h2 s₀ hs₀) (h1 g) i j hij.le (h1 g j i hij)
    · apply conj_zero u
      rw [← sandwich, conj_sub]
      refine tri_zero _ hc _ _ (h1 s₀) (h2 s₀ hs₀) (fun a b hab => ?_) i i le_rfl ?_
      · rw [Matrix.sub_apply, h1 s a b hab]
        simp [Matrix.one_apply_ne hab.ne']
      · rw [Matrix.sub_apply, h2 s hs i]
        simp
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem tb_avg {k G W : Type} [Field k] [CharZero k] [Group G] [AddCommGroup W] [Module k W]
    (a : G → W →ₗ[k] W) (hmul : ∀ g h w, a (g * h) w = a g (a h w)) (f : G → W)
    (hf : ∀ g h, f (g * h) = f g + a g (f h)) (H : Subgroup G) [H.FiniteIndex] (x : W)
    (hx : ∀ h ∈ H, f h = a h x - x) : ∃ y, ∀ g, f g = a g y - y := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set f' : G → W := fun g => f g - (a g x - x) with hf'
  have hc : ∀ g h, f' (g * h) = f' g + a g (f' h) := by
    intro g h
    simp only [hf', hf, hmul, map_sub]
    abel
  have hH : ∀ g h, h ∈ H → f' (g * h) = f' g := by
    intro g h hh
    rw [hc]
    have : f' h = 0 := by simp only [hf', hx h hh, sub_self]
    rw [this, map_zero, add_zero]
  let F : G ⧸ H → W := Quotient.lift f' (by
    intro g g' hgg
    have h1 : g⁻¹ * g' ∈ H := QuotientGroup.leftRel_apply.1 hgg
    have := hH g _ h1
    rw [mul_inv_cancel_left] at this
    exact this.symm)
  have hF : ∀ (g : G) (q : G ⧸ H), F (g • q) = f' g + a g (F q) := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H z => exact hc g z
  set S : W := ∑ q, F q with hS
  have hsum : ∀ g, S = (Fintype.card (G ⧸ H) : k) • f' g + a g S := by
    intro g
    have e1 : ∑ q, F (g • q) = S := Equiv.sum_comp (MulAction.toPerm g) F
    refine e1.symm.trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hF, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← map_sum,
      Nat.cast_smul_eq_nsmul, ← hS]
  have hn : (Fintype.card (G ⧸ H) : k) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨x - (Fintype.card (G ⧸ H) : k)⁻¹ • S, fun g => ?_⟩
  have e : f' g = (Fintype.card (G ⧸ H) : k)⁻¹ • (S - a g S) := by
    rw [eq_inv_smul_iff₀ hn, eq_sub_iff_add_eq]
    exact (hsum g).symm
  have e2 : f g = f' g + (a g x - x) := by simp only [hf', sub_add_cancel]
  rw [e2, e, map_sub, map_smul, smul_sub]
  abel

section Alg

variable {E H : Type} [CommRing E] [Group H]

private def tbSnd (X : M4 (DualNumber E)) : M4 E := Matrix.of fun i j => (X i j).snd

private def tbFst (X : M4 (DualNumber E)) : M4 E := Matrix.of fun i j => (X i j).fst

private theorem tbSnd_mul (X Y : M4 (DualNumber E)) : tbSnd (X * Y) = tbFst X * tbSnd Y + tbSnd X * tbFst Y := by
  ext a b
  simp [tbSnd, tbFst, Matrix.mul_apply, Fin.sum_univ_four, DualNumber.snd_mul]
  ring

private theorem tbFst_mul (X Y : M4 (DualNumber E)) : tbFst (X * Y) = tbFst X * tbFst Y := by
  ext a b
  simp [tbFst, Matrix.mul_apply, Fin.sum_univ_four]

private theorem tbSnd_one : tbSnd (1 : M4 (DualNumber E)) = 0 := by
  ext a b
  by_cases h : a = b <;> simp [tbSnd, Matrix.one_apply, h]

private theorem tb_ad (r : H →* M4 E) (g : H) (X : M4 E) : Loc.adGL r.toHomUnits g X = r g * X * r g⁻¹ := by
  have : ((r.toHomUnits g)⁻¹ : (M4 E)ˣ) = r.toHomUnits g⁻¹ := (map_inv _ _).symm
  show (r.toHomUnits g : M4 E) * X * ((r.toHomUnits g)⁻¹ : (M4 E)ˣ) = _
  rw [this]
  rfl

private theorem tb_coc (r : H →* M4 E) (r' : H →* M4 (DualNumber E)) (h : ∀ g, tbFst (r' g) = r g) (a b : H) :
    tbSnd (r' (a * b)) * r (a * b)⁻¹ =
      tbSnd (r' a) * r a⁻¹ + Loc.adGL r.toHomUnits a (tbSnd (r' b) * r b⁻¹) := by
  rw [tb_ad, map_mul, tbSnd_mul, h, h, mul_inv_rev, map_mul, add_mul, add_comm]
  congr 1
  · rw [mul_assoc, ← mul_assoc (r b), ← map_mul, mul_inv_cancel, map_one, one_mul]
  · simp only [mul_assoc]

private theorem tb_sp (X : M4 (DualNumber E)) (ν : DualNumber E) (hν : ν.snd = 0) (hX : IsGSp ν X) (Y : M4 E)
    (hY : tbFst X * Y = 1) : tbSnd X * Y ∈ sp4 E := by
  have a1 : tbFst (adj X) = adj (tbFst X) := by ext i j; simp [tbFst, adj_apply]
  have a2 : tbSnd (adj X) = adj (tbSnd X) := by ext i j; simp [tbSnd, adj_apply]
  have h1 : adj (tbFst X) * tbFst X = ν.fst • (1 : M4 E) := by
    rw [← a1, ← tbFst_mul, hX]
    ext i j
    by_cases h : i = j <;> simp [tbFst, Matrix.one_apply, h]
  have h2 : adj (tbFst X) * tbSnd X + adj (tbSnd X) * tbFst X = 0 := by
    rw [← a1, ← a2, ← tbSnd_mul, hX]
    ext i j
    by_cases h : i = j <;> simp [tbSnd, Matrix.one_apply, h, hν]
  have h0 : adj (1 : M4 E) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]
  have h3 : adj Y * adj (tbFst X) = 1 := by rw [← Loc.SpFlag.adj_mul, hY, h0]
  have h4 : adj (tbSnd X) = -(adj (tbFst X) * tbSnd X * Y) := by
    have := congrArg (· * Y) h2
    simp only [add_mul, zero_mul, mul_assoc, hY, mul_one] at this
    rw [mul_assoc]
    exact eq_neg_of_add_eq_zero_right this
  show adj _ = -_
  rw [Loc.SpFlag.adj_mul, h4, mul_neg, ← mul_assoc, ← mul_assoc, h3, one_mul]

private theorem tb_tri_diag {A B : M4 E} (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) (i : Fin 4) :
    (A * B) i i = A i i * B i i :=
  Loc.SpFlag.tri_mul_diag (fun i j h => hA i j h) (fun i j h => hB i j h) i

private theorem tb_chars (r : H →* M4 E) (u : (M4 E)ˣ)
    (h : ∀ g i j, j < i → ((u : M4 E) * r g * (u⁻¹ : (M4 E)ˣ)) i j = 0) :
    ∃ κ : Fin 4 → H →* Eˣ, ∀ g i, ((u : M4 E) * r g * (u⁻¹ : (M4 E)ˣ)) i i = κ i g := by
  let k : Fin 4 → H →* E := fun i =>
    { toFun := fun g => ((u : M4 E) * r g * (u⁻¹ : (M4 E)ˣ)) i i
      map_one' := by simp
      map_mul' := fun a b => by
        rw [← tb_tri_diag (h a) (h b), map_mul]
        simp only [mul_assoc, Units.inv_mul_cancel_left] }
  exact ⟨fun i => (k i).toHomUnits, fun g i => rfl⟩

end Alg

private theorem tb_upper {K : Type} [Field K] (T T' P : M4 K) (hT : ∀ i j, j < i → T i j = 0)
    (hT' : ∀ i j, j < i → T' i j = 0) (hd : ∀ i j, i ≠ j → T i i ≠ T' j j) (h : T * P = P * T') :
    ∀ i j, j < i → P i j = 0 := by
  have e := fun i j => congrFun (congrFun h i) j
  simp only [Matrix.mul_apply, Fin.sum_univ_four] at e
  have t := And.intro (And.intro (hT 1 0 (by decide)) (And.intro (hT 2 0 (by decide)) (hT 3 0 (by decide))))
    (And.intro (hT 2 1 (by decide)) (And.intro (hT 3 1 (by decide)) (hT 3 2 (by decide))))
  have t' := And.intro (And.intro (hT' 1 0 (by decide)) (And.intro (hT' 2 0 (by decide)) (hT' 3 0 (by decide))))
    (And.intro (hT' 2 1 (by decide)) (And.intro (hT' 3 1 (by decide)) (hT' 3 2 (by decide))))
  have k : ∀ i j, i ≠ j → T i i * P i j = P i j * T' j j → P i j = 0 := fun i j hij hh => by
    rw [mul_comm (P i j), ← sub_eq_zero, ← sub_mul, mul_eq_zero, sub_eq_zero] at hh
    exact hh.resolve_left (hd i j hij)
  have p30 : P 3 0 = 0 := k _ _ (by decide) (by simpa only [t, t', zero_mul, mul_zero, add_zero, zero_add] using e 3 0)
  have p31 : P 3 1 = 0 := k _ _ (by decide) (by simpa only [t, t', p30, zero_mul, mul_zero, add_zero, zero_add] using e 3 1)
  have p32 : P 3 2 = 0 := k _ _ (by decide) (by simpa only [t, t', p30, p31, zero_mul, mul_zero, add_zero, zero_add] using e 3 2)
  have p20 : P 2 0 = 0 := k _ _ (by decide) (by simpa only [t, t', p30, zero_mul, mul_zero, add_zero, zero_add] using e 2 0)
  have p21 : P 2 1 = 0 := k _ _ (by decide) (by simpa only [t, t', p20, p31, zero_mul, mul_zero, add_zero, zero_add] using e 2 1)
  have p10 : P 1 0 = 0 := k _ _ (by decide) (by simpa only [t, t', p20, p30, zero_mul, mul_zero, add_zero, zero_add] using e 1 0)
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | assumption | exact absurd hij (by decide)

private theorem tb_uniq {K H : Type} [Field K] (r : H → M4 K) (U U' V V' : M4 K) (hU : U' * U = 1) (hU' : U * U' = 1)
    (hV : V' * V = 1) (h1 : ∀ g i j, j < i → (U * r g * U') i j = 0) (h2 : ∀ g i j, j < i → (V * r g * V') i j = 0) (s : H)
    (hd : ∀ i j, i ≠ j → (U * r s * U') i i ≠ (V * r s * V') j j) (g : H) (i : Fin 4) :
    (U * r g * U') i i = (V * r g * V') i i := by
  have e : ∀ g, (U * r g * U') * (U * V') = (U * V') * (V * r g * V') := fun g => by
    simp only [mul_assoc]
    rw [← mul_assoc U' U, hU, one_mul, ← mul_assoc V' V, hV, one_mul]
  have hP := tb_upper _ _ _ (h1 s) (h2 s) hd (e s)
  have hdet : (U * V').det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero (Matrix.isUnit_det_of_right_inverse hU').ne_zero (Matrix.isUnit_det_of_right_inverse hV).ne_zero
  rw [Matrix.det_of_upperTriangular (fun i j h => hP i j h)] at hdet
  have h3 := congrFun (congrFun (e g) i) i
  rw [tb_tri_diag (h1 g) hP, tb_tri_diag hP (h2 g), mul_comm] at h3
  exact mul_left_cancel₀ (Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)) h3

private theorem tb_sub {l : ℕ} [Fact l.Prime] {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [CommGroup A] (φ : Γ →* Formalism.BasicNotions.Loc.GQ l) (hφ : Continuous φ) (σ : Γ) (hσ : Loc.IsFrob (φ σ)) (χ : Γ →* A)
    (hχ : IsOpen (χ.ker : Set Γ)) :
    ∃ U : Subgroup Γ, U.Normal ∧ IsOpen (U : Set Γ) ∧ σ ∈ U ∧ ∀ g ∈ U, φ g ∈ Loc.Iq l → χ g = 1 := by
  haveI := Subgroup.quotient_finite_of_isOpen _ hχ
  haveI : Finite χ.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange χ).toEquiv
  letI : TopologicalSpace χ.range := ⊥
  haveI : DiscreteTopology χ.range := ⟨rfl⟩
  obtain ⟨f, hf, hfI, hfσ⟩ := Loc.frobFree (φ σ) hσ χ.range (χ.rangeRestrict σ)
  refine ⟨(χ.rangeRestrict * (f.comp φ)⁻¹).ker, inferInstance, ?_, ?_, fun g hg hI => ?_⟩
  · refine Subgroup.isOpen_mono (H₁ := χ.ker ⊓ (f.comp φ).ker) (fun g hg => ?_)
      (hχ.inter ((isOpen_discrete {1}).preimage (hf.comp hφ)))
    have h1 : χ.rangeRestrict g = 1 := Subtype.ext hg.1
    have h2 : f.comp φ g = 1 := hg.2
    rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply, h1, h2, inv_one, mul_one]
  · rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, hfσ, mul_inv_cancel]
  · rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, hfI _ hI, inv_one,
      mul_one] at hg
    exact congrArg Subtype.val hg

private theorem tb_loc (hP : Loc.LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] (φ : Γ →* Formalism.BasicNotions.Loc.GQ l) (hφ : Topology.IsOpenEmbedding φ) {E : Type} [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E]
    [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] (r : Γ →* M4 E) (r' : Γ →* M4 (DualNumber E))
    (h : ∀ g, tbFst (r' g) = r g) (hr : Continuous r) (hr' : Continuous fun g => tbSnd (r' g))
    (U : Subgroup Γ) [U.Normal] (hU : IsOpen (U : Set Γ)) (u : (M4 (DualNumber E))ˣ) (κ : Fin 4 → Γ →* (DualNumber E)ˣ)
    (w : Fin 4 → ℤ) (hw : StrictAnti w)
    (h1 : ∀ g i j, j < i → ((u : M4 (DualNumber E)) * r' g * (u⁻¹ : (M4 (DualNumber E))ˣ)) i j = 0)
    (h2 : ∀ g i, ((u : M4 (DualNumber E)) * r' g * (u⁻¹ : (M4 (DualNumber E))ˣ)) i i = κ i g)
    (h3 : ∀ i, ∀ g ∈ U, φ g ∈ Loc.Iq l → κ i g = Loc.cycA l l (DualNumber E) (φ g) ^ w i)
    (h4 : ∀ i j, i < j → ∃ g ∈ U, (κ i g : DualNumber E).fst ≠ (κ j g : DualNumber E).fst * (Loc.cycA l l E (φ g) : E)) :
    (fun g => tbSnd (r' g) * r g⁻¹) ∈ Loc.finiteCocycles φ (Loc.adGL r.toHomUnits) := by
  haveI : IsModuleTopology ℚ_[l] (M4 E) := inferInstanceAs (IsModuleTopology ℚ_[l] (Fin 4 → Fin 4 → E))
  have hri : Continuous fun g => r g⁻¹ := hr.comp continuous_inv
  refine (Loc.pr6 hP φ hφ (Loc.adGL r.toHomUnits) ?_ _ ⟨hr'.matrix_mul hri, tb_coc r r' h⟩ U hU
    (r.toHomUnits.comp U.subtype) (hr.comp continuous_subtype_val) LinearMap.id LinearMap.id (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (r'.toHomUnits.comp U.subtype) (fun g i j => ?_) u
    (fun i => (κ i).comp U.subtype) w (fun g => ⟨h1 g, h2 g⟩) hw (fun i g => h3 i g g.2) fun i j hij => ?_).2.2
  · simp only [ReciprocityTheory.Gal.ContAction, tb_ad]
    exact ((hr.comp continuous_fst).matrix_mul continuous_snd).matrix_mul (hri.comp continuous_fst)
  · refine TrivSqZeroExt.ext (congrFun (congrFun (h g) i) j) ?_
    show tbSnd (r' g) i j = (tbSnd (r' g) * r (g : Γ)⁻¹ * r g) i j
    rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  · obtain ⟨g, hg, hg'⟩ := h4 i j hij
    exact ⟨⟨g, hg⟩, hg'⟩

section Main

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem tb_cont (D : Raw Ω c) (r' : G ℚ Ω →* M4 (DualNumber (PadicAlgCl l))) (h : D.PtIn _ r') :
    Continuous fun g => tbSnd (r' g) := by
  obtain ⟨R, _, _, _, ρ, y, -, rfl⟩ := h
  have hy := ((coPt c R).2 y).2
  refine continuous_matrix fun i j => ?_
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := hy (ε / 2) (half_pos hε)
  filter_upwards [(ρ.cont i j n).eventually_eq g₀] with g hg
  have h1 := hn _ (Ideal.Quotient.eq.1 hg)
  rw [map_sub, TrivSqZeroExt.snd_sub] at h1
  rw [dist_eq_norm]
  exact h1.trans_lt (half_lt_self hε)

private theorem tb_place (D : Raw Ω c) (hD : D.Good) (K : Type) [CommRing K] [Algebra c.O K] (r : G ℚ Ω →* M4 K)
    (h : D.PtIn K r) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal) :
    ∃ (A : ValuationSubring Ω) (N : Subgroup (G ℚ Ω)), IsPlaceOver A w ∧ IsOpen (N : Set (G ℚ Ω)) ∧
      ∀ g ∈ Ine (F := ℚ) A, g ∈ N → r g = 1 := by
  obtain ⟨-, hu, -, -, hp, -⟩ := ptIn D hD K r h
  obtain ⟨f1, -, -, -, -, -, -, -, -, -, -, f2, -⟩ := facts D hD
  by_cases hS : ∃ p ∈ D.Sb, ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
  · obtain ⟨p, hp1, hp2⟩ := hS
    haveI : Fact p.Prime := ⟨(f1 p hp1).1⟩
    obtain ⟨w', hw', hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := p) (F := ℚ) (D.pl p) (hD.pl_over p Fact.out)
    obtain ⟨j, hj⟩ := (Loc.decEmb (F := ℚ) (Ω := Ω) (v := p)).1 _ w' hAw hw'
    refine ⟨D.pl p, D.ψ.ker, ?_, hD.psi_open, fun g hg hg' => (hp p hp1).2 ⟨g, hg.1⟩ ⟨hg, hg'⟩⟩
    rw [← hj]
    exact ((Loc.iotaFacts j).2.2.2.2.2.1 w).2 hp2
  · refine ⟨placeOf Ω w, D.rbar.ker, isPlaceOver_placeOf Ω w, f2, fun g hg hg' => hu _ (fun p hp hv => ?_) g hg hg'⟩
    have h1 : ((p : ℕ) : 𝓞 ℚ) ∈ w.asIdeal := (isPlaceOver_placeOf Ω w _).1 (by simpa using hv)
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact hw h1
    · exact hS ⟨p, hp, h1⟩

private theorem tb_desc (D : Raw Ω c) (r' : G ℚ Ω →* M4 (DualNumber (PadicAlgCl l))) (h : D.PtIn _ r') :
    ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (_ : FiniteDimensional ℚ_[l] K) (_ : Algebra c.O K)
      (r₁ : G ℚ Ω →* M4 (DualNumber K)), (∀ a : c.O, ((algebraMap c.O K a : K) : PadicAlgCl l) = a) ∧ D.PtIn _ r₁ ∧
      ∀ g i j, ((r₁ g i j).fst : PadicAlgCl l) = (r' g i j).fst ∧ ((r₁ g i j).snd : PadicAlgCl l) = (r' g i j).snd := by
  obtain ⟨R, _, _, _, ρ, F, hpt, rfl⟩ := h
  obtain ⟨K, hK, hE⟩ := ((coPt c R).2 F).1
  have hO : ∀ x : c.O, algebraMap c.O (PadicAlgCl l) x ∈ K := fun x => by
    have := (hE (algebraMap c.O R x)).1
    rwa [F.commutes] at this
  letI : Algebra c.O ↥K := ((algebraMap c.O (PadicAlgCl l)).codRestrict K hO).toAlgebra
  let F' : R →ₐ[c.O] DualNumber ↥K :=
    { toFun := fun a => ⟨⟨(F a).fst, (hE a).1⟩, ⟨(F a).snd, (hE a).2⟩⟩
      map_one' := TrivSqZeroExt.ext (Subtype.ext (congrArg TrivSqZeroExt.fst (map_one F)))
        (Subtype.ext (congrArg TrivSqZeroExt.snd (map_one F)))
      map_zero' := TrivSqZeroExt.ext (Subtype.ext (congrArg TrivSqZeroExt.fst (map_zero F)))
        (Subtype.ext (congrArg TrivSqZeroExt.snd (map_zero F)))
      map_add' := fun a b => TrivSqZeroExt.ext (Subtype.ext (congrArg TrivSqZeroExt.fst (map_add F a b)))
        (Subtype.ext (congrArg TrivSqZeroExt.snd (map_add F a b)))
      map_mul' := fun a b => TrivSqZeroExt.ext (Subtype.ext (congrArg TrivSqZeroExt.fst (map_mul F a b)))
        (Subtype.ext (congrArg TrivSqZeroExt.snd (map_mul F a b)))
      commutes' := fun c => TrivSqZeroExt.ext (Subtype.ext (congrArg TrivSqZeroExt.fst (F.commutes c)))
        (Subtype.ext (congrArg TrivSqZeroExt.snd (F.commutes c))) }
  exact ⟨K, hK, inferInstance, mapRep (F' : R →+* DualNumber K) ρ.hom, fun _ => rfl,
    ⟨R, inferInstance, inferInstance, inferInstance, ρ, F', hpt, rfl⟩, fun g i j => ⟨rfl, rfl⟩⟩

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
private theorem tb_atL (D : Raw Ω c) (hD : D.Good) (hP : Loc.LocalPublishedTheorems) (r : G ℚ Ω →* M4 (PadicAlgCl l)) (hr : D.EPt r)
    (r' : G ℚ Ω →* M4 (DualNumber (PadicAlgCl l))) (hr' : D.PtIn _ r') (h : ∀ g, tbFst (r' g) = r g)
    (φ : D.Gp l →* Formalism.BasicNotions.Loc.GQ l) (hφ : Topology.IsOpenEmbedding φ)
    (hI : ∀ g, φ g ∈ Loc.Iq l ↔ (g : G ℚ Ω) ∈ D.Ip l) (hc : ∀ g, Loc.cyc l l (φ g) = cycZ ℚ Ω l (g : G ℚ Ω))
    (hF : ∀ g : D.Gp l, (g : G ℚ Ω) = D.sg l → Loc.IsFrob (φ g)) :
    (fun g : D.Gp l => tbSnd (r' g) * r (g : G ℚ Ω)⁻¹) ∈
      Loc.finiteCocycles φ ((Loc.adGL r.toHomUnits).comp (D.Gp l).subtype) := by
  obtain ⟨-, hT, -, hwt, -, -, hinj, -, -, -, -, -, hom, -⟩ := facts D hD
  have hcr := (eptInt D hD r hr).1
  have hcr' := tb_cont D r' hr'
  obtain ⟨K, _, _, r₁, hO, hr₁, he⟩ := tb_desc D r' hr'
  haveI : IsModuleTopology ℚ_[l] ↥K := isModuleTopologyOfFiniteDimensional
  haveI : CompactSpace (D.Gp l) := isCompact_iff_compactSpace.1 (isClosed_Dec _).isCompact
  have hOi : Function.Injective (algebraMap c.O K) := fun a b e => Subtype.ext (by rw [← hO, ← hO, e])
  obtain ⟨-, -, -, ⟨-, hord⟩, -⟩ := ptIn D hD _ r₁ hr₁
  obtain ⟨u, h1, h2⟩ := (ordLocal _ (DualNumber K) _ D.s0 _ hD.decompSigma_mem.1.1 fun i j hij => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, TrivSqZeroExt.fst_sub, sub_ne_zero]
    exact fun e => hij (hinj (hOi e))).1 hord
  obtain ⟨κ, hκ⟩ := tb_chars _ u h1
  let σ : D.Gp l := ⟨D.sg l, (hT l (Finset.mem_insert_self _ _)).1⟩
  obtain ⟨U, hUn, hU, hσ, hUI⟩ := tb_sub φ hφ.continuous σ (hF σ rfl) ((D.ψ.prod D.om).comp (D.Gp l).subtype) (by
    rw [← MonoidHom.comap_ker, MonoidHom.ker_prod]
    exact (hD.psi_open.inter hom).preimage continuous_subtype_val)
  obtain ⟨v, κ', hv, hκI, -, -, -, hne⟩ := Loc.spPtL D hD (r.comp (D.Gp l).subtype) (by
    obtain ⟨R, i1, i2, i3, ρ, y, hpt, rfl⟩ := hr
    exact ⟨R, i1, i2, i3, D.loc ρ l, y, hpt.atL, rfl⟩)
  let π : DualNumber K →+* PadicAlgCl l := (K.val : K →+* PadicAlgCl l).comp (TrivSqZeroExt.fstHom K K K : DualNumber K →+* K)
  have hπ : ∀ g, π.mapMatrix (r₁ g) = r g := fun g => by
    rw [← h]
    ext i j
    exact (he g i j).1
  have hent : ∀ (g : D.Gp l) i j, (π.mapMatrix u.val * r g * π.mapMatrix (u⁻¹).val : M4 (PadicAlgCl l)) i j =
      π (((u : M4 (DualNumber K)) * r₁ g * (u⁻¹ : (M4 (DualNumber K))ˣ)) i j) := fun g i j => by
    rw [← hπ, ← map_mul, ← map_mul]
    rfl
  have hκκ : ∀ i (g : D.Gp l), π (κ i g) = κ' i g := fun i g => by
    have := tb_uniq (fun g : D.Gp l => r g) (π.mapMatrix u.val) (π.mapMatrix (u⁻¹).val)
      (v⁻¹ : (M4 (PadicAlgCl l))ˣ) v (by rw [← map_mul, Units.inv_mul, map_one])
      (by rw [← map_mul, Units.mul_inv, map_one]) v.mul_inv
      (fun g i j hij => (hent g i j).trans ((congrArg π (h1 g i j hij)).trans (map_zero π))) (fun g => (hv g).1) D.s0
      (fun i j hij e => by
        have e1 := (hent D.s0 i i).trans (congrArg π (h2 D.s0 hD.decompSigma_mem.1.1 i))
        have e2 := ((hv D.s0).2 j).trans (hκI j D.s0 hD.decompSigma_mem.1.1)
        exact hij (hinj (Subtype.ext ((hO _).symm.trans (e1.symm.trans (e.trans e2)))))) g i
    exact ((hent g i i).trans (congrArg π (hκ g i))).symm.trans (this.trans ((hv g).2 i))
  let r₀ : G ℚ Ω →* M4 K := mapRep (TrivSqZeroExt.fstHom K K K : DualNumber K →+* K) r₁
  have hr₀ : ∀ g, (r₀ g).map K.val = r g := hπ
  have hs₀ : ∀ g, (tbSnd (r₁ g)).map K.val = tbSnd (r' g) := fun g => by
    ext i j
    exact (he g i j).2
  have hw : StrictAnti fun i => (D.wts4 i : ℤ) := by
    have := hD.two_le
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [Raw.wts4] at hij ⊢ <;> omega
  have key := tb_loc hP φ hφ (r₀.comp (D.Gp l).subtype) (r₁.comp (D.Gp l).subtype) (fun g => rfl)
    (continuous_matrix fun i j => continuous_induced_rng.2 (by
      refine ((hcr.comp (continuous_subtype_val (p := (· ∈ D.Gp l)))).matrix_elem i j).congr fun g => ?_
      exact (congrFun (congrFun (hr₀ g) i) j).symm))
    (continuous_matrix fun i j => continuous_induced_rng.2 (by
      refine ((hcr'.comp (continuous_subtype_val (p := (· ∈ D.Gp l)))).matrix_elem i j).congr fun g => ?_
      exact (he g i j).2.symm))
    U hU u κ _ hw h1 hκ (fun i g hg hgI => by
      have e := hUI g hg hgI
      have e1 : (g : G ℚ Ω) ∈ D.Ip l ⊓ D.ψ.ker ⊓ D.om.ker :=
        ⟨⟨(hI g).1 hgI, congrArg Prod.fst e⟩, congrArg Prod.snd e⟩
      apply Units.ext
      rw [← hκ, h2 g ((hI g).1 hgI), hwt i g e1, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow]
      congr 1
      refine TrivSqZeroExt.ext (Subtype.ext ((hO _).trans ?_)) rfl
      simp only [Loc.cycA, MonoidHom.comp_apply, hc]
      rfl)
    (fun i j hij => by
      obtain ⟨g, hg, hg'⟩ := hne i j hij.ne U hU ⟨σ, hσ, rfl⟩
      refine ⟨g, hg, fun e => hg' ?_⟩
      rw [← hκκ, ← hκκ]
      refine (congrArg K.val e).trans ?_
      rw [map_mul]
      congr 1
      simp only [Loc.cycA, MonoidHom.comp_apply, hc]
      rfl)
  have key2 := Loc.z1fCoef φ _ ((Loc.adGL r.toHomUnits).comp (D.Gp l).subtype) K.val.toLinearMap.mapMatrix
    (continuous_id.matrix_map continuous_subtype_val) (fun g X => by
      rw [tb_ad, MonoidHom.comp_apply (Loc.adGL r.toHomUnits), tb_ad, ← hr₀, ← hr₀]
      exact (Matrix.map_mul (f := (K.val : K →+* PadicAlgCl l))).trans
        (congrArg (· * _) (Matrix.map_mul (f := (K.val : K →+* PadicAlgCl l))))) _ key
  refine cast (congrArg (· ∈ _) (funext fun g => ?_)) key2
  rw [← hr₀, ← hs₀]
  exact Matrix.map_mul (f := (K.val : K →+* PadicAlgCl l))

end Main

theorem UpperTheory.V.GradeZeroInterpolatingElement.tanBK :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → Loc.LocalPublishedTheorems → ∀ r, D.EPt r → ∀ r' : G ℚ Ω →* M4 (DualNumber (PadicAlgCl l)), D.PtIn _ r' → (∀ g i j, (r' g i j).fst = r g i j) → (fun g => (Matrix.of fun i j => (r' g i j).snd) * r g⁻¹) ∈ Z1 (Loc.adGL r.toHomUnits) ∧ Af.IsBK l (Loc.adGL r.toHomUnits) (fun g => (Matrix.of fun i j => (r' g i j).snd) * r g⁻¹) ∧ ∀ g, (Matrix.of fun i j => (r' g i j).snd) * r g⁻¹ ∈ sp4 (PadicAlgCl l) := by
  intro Ω _ _ _ l _ c D hD hP r hr r' hr' h
  have h' : ∀ g, tbFst (r' g) = r g := fun g => Matrix.ext (h g)
  have hZ : (fun g => tbSnd (r' g) * r g⁻¹) ∈ Z1 (Loc.adGL r.toHomUnits) :=
    ⟨(tb_cont D r' hr').matrix_mul ((eptInt D hD r hr).1.comp continuous_inv), tb_coc r r' h'⟩
  refine ⟨hZ, ⟨fun w hw => ?_, fun τ => ?_⟩, fun g => ?_⟩
  · obtain ⟨A, N, hA, hN, h1⟩ := tb_place D hD _ r' hr' w hw
    haveI := Subgroup.quotient_finite_of_isOpen N hN
    haveI : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    obtain ⟨y, hy⟩ := tb_avg (k := PadicAlgCl l) (G := Ine (F := ℚ) A)
      (fun g => Loc.adGL r.toHomUnits g) (fun g h x => by simp)
      (fun g => tbSnd (r' g) * r (g : G ℚ Ω)⁻¹) (fun g h => hZ.2 g h) (N.subgroupOf _) 0 (fun g hg => by
        rw [h1 g g.2 hg, tbSnd_one, zero_mul, map_zero, sub_zero])
    exact ⟨A, hA, y, fun s hs => hy ⟨s, hs⟩⟩
  · obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := l) (F := ℚ) (D.pl l) (hD.pl_over l Fact.out)
    obtain ⟨j, hj⟩ := (Loc.decEmb (F := ℚ) (Ω := Ω) (v := l)).1 _ w hAw hw
    have h1 := ((Loc.decEmb (F := ℚ) (Ω := Ω) (v := l)).2 j).2
    have h2 := (Loc.iotaFacts j).2.2.2.2.2.2
    rw [hj] at h1 h2
    obtain ⟨φ, hφ, a1, -, a2, a3, -⟩ := h1
    refine ⟨j, Subsingleton.elim _ _, (Loc.bkAbove (F := ℚ) j φ (D.Gp l).subtype hφ a1 _ _ hZ).1
      (tb_atL D hD hP r hr r' hr' h' φ hφ a2 (a3 l) fun g hg => (h2 _).2 ?_)⟩
    have e : Loc.iota j (φ g) = D.sg l := AlgEquiv.ext fun y => j.injective (by rw [Loc.iota_spec, a1, hg])
    rw [e]
    exact hD.sg_frob l (Finset.mem_insert_self _ _)
  · exact tb_sp _ _ rfl ((ptIn D hD _ r' hr').1 g) _ (by rw [h', ← map_mul, mul_inv_cancel, map_one])
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open scoped Matrix TensorProduct

namespace UpperTheory.V.GradeZeroInterpolatingElement

private theorem rg_twist {Γ k V : Type} [Group Γ] [CommRing k] [AddCommGroup V] [Module k V] (A : Representation k Γ V)
    (p : V →ₗ[k] V) (hp : ∀ x, p (p x) = p x) (hA : ∀ g x, p (A g x) = A g (p x)) (η : Γ →* kˣ) :
    ∃ ρ : Representation k Γ V, ∀ g x, ρ g x = A g (p x) + (η g : k) • A g (x - p x) := by
  refine ⟨{ toFun := fun g => A g ∘ₗ p + (η g : k) • (A g ∘ₗ (LinearMap.id - p))
            map_one' := ?_
            map_mul' := fun g h => ?_ }, fun g x => rfl⟩
  · ext x
    simp
  · ext x
    simp only [map_mul, Units.val_mul, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      LinearMap.id_apply, Module.End.mul_apply, map_add, map_smul, map_sub, hA, hp, sub_self, smul_zero, add_zero,
      mul_smul, smul_sub, smul_add, map_zero]
    module

private theorem rg_sign {K Ω : Type} [Field K] [NumberField K] [IsCMField K] (h : Module.finrank ℚ K = 2) [Field Ω]
    [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] (k : Type) [Field k] :
    ∃ η : G ℚ Ω →* kˣ, (∀ s : G K Ω, η (s.restrictScalars ℚ) = 1) ∧
      ∀ c : G ℚ Ω, (∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)) → η c = -1 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : K, IsCMField.complexConj K x ≠ x := by
    by_contra hc
    push Not at hc
    exact IsCMField.complexConj_ne_one K (AlgEquiv.ext hc)
  set δ : K := x - IsCMField.complexConj K x with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 hx.symm
  have hδc : IsCMField.complexConj K δ = -δ := by simp [hδ]
  have hsq : δ * δ ∈ maximalRealSubfield K := (IsCMField.complexConj_eq_self_iff K _).1 (by rw [map_mul, hδc]; ring)
  obtain ⟨q, hq⟩ := Af.surjective_algebraMap_real K h ⟨_, hsq⟩
  have hq' : algebraMap ℚ K q = δ * δ := by
    have := congrArg (fun y : maximalRealSubfield K => (y : K)) hq
    simpa using this
  set d : Ω := algebraMap K Ω δ with hd
  have hd0 : d ≠ 0 := by simpa [hd] using hδ0
  have hdd : d * d = algebraMap ℚ Ω q := by rw [IsScalarTower.algebraMap_apply ℚ K Ω, hq', map_mul]
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hne : -d ≠ d := fun e => hd0 (by linear_combination (-1 / 2 : Ω) * e)
  have hpm : ∀ g : G ℚ Ω, g d = d ∨ g d = -d := fun g => by
    have : g d * g d = d * d := by rw [← map_mul, hdd, AlgEquiv.commutes]
    exact mul_self_eq_mul_self_iff.1 this
  refine ⟨{ toFun := fun g => if g d = d then 1 else -1
            map_one' := by simp
            map_mul' := fun g g' => ?_ }, fun s => ?_, fun c ⟨j, hj⟩ => ?_⟩
  · rcases hpm g with h1 | h1 <;> rcases hpm g' with h2 | h2 <;> simp [AlgEquiv.mul_apply, h1, h2, hne]
  · have : (s.restrictScalars ℚ) d = d := s.commutes δ
    simp [this]
  · have : c d = -d := by
      apply j.injective
      rw [hj, hd, ← map_neg (algebraMap K Ω), ← hδc]
      exact (IsCMField.complexEmbedding_complexConj K (j.comp (algebraMap K Ω)) δ).symm
    simp [this, hne]

section BK

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
  {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] C V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V]

private theorem rg_bk {ρ ρ' : Representation C (G F Ω) V} (f : V →ₗ[C] V) (hf : ∀ g x, f (ρ g x) = ρ' g (f x))
    {z : G F Ω → V} (hz : ∀ g, f (z g) = z g) (h1 : z ∈ Z1 ρ) (h2 : Af.IsBK l ρ z) : z ∈ Z1 ρ' ∧ Af.IsBK l ρ' z := by
  have hc : ∀ g h, z (g * h) = z g + ρ' g (z h) := fun g h => by
    rw [← hz (g * h), h1.2, map_add (f := _), hf, hz, hz]
  refine ⟨⟨h1.1, hc⟩, fun w hw => ?_, fun τ => ?_⟩
  · obtain ⟨A, hA, x, hx⟩ := h2.away w hw
    exact ⟨A, hA, f x, fun s hs => by rw [← hz, hx s hs, map_sub, hf]⟩
  · obtain ⟨j, hj, ⟨hc1, -⟩, x, hx⟩ := h2.above τ
    refine ⟨j, hj, ⟨hc1, fun g h => hc g.1.1 h.1.1⟩,
      LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l]) x, fun g => ?_⟩
    have key : ∀ y : V ⊗[ℚ_[l]] Loc.Bcr l, LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l])
        (Loc.actC ((MonoidHom.snd _ _).comp (Af.decJ F j).subtype) (ρ.comp ((MonoidHom.fst _ _).comp (Af.decJ F j).subtype)) g y) =
        Loc.actC ((MonoidHom.snd _ _).comp (Af.decJ F j).subtype) (ρ'.comp ((MonoidHom.fst _ _).comp (Af.decJ F j).subtype)) g
          (LinearMap.rTensor (Loc.Bcr l) (f.restrictScalars ℚ_[l]) y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Loc.actC, hf]
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
    simp [hz]

end BK

private def rgJ (k : Type) [CommRing k] : GL (Fin 4) k where
  val := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
  inv := !![0, 0, 0, -1; 0, 0, -1, 0; 0, 1, 0, 0; 1, 0, 0, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

private theorem rgJ_adj {k : Type} [CommRing k] (X : M4 k) : Xᵀ * (rgJ k : M4 k) = (rgJ k : M4 k) * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rgJ, Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev]

private noncomputable def rgP (k : Type) [Field k] : M4 k →ₗ[k] M4 k where
  toFun X := (2 : k)⁻¹ • (X - adj X)
  map_add' X Y := by rw [(grp k).2.2.1, ← smul_add]; congr 1; abel
  map_smul' a X := by rw [(grp k).2.2.2.1, ← smul_sub, smul_comm]; rfl

private theorem rgP_apply {k : Type} [Field k] (X : M4 k) : rgP k X = (2 : k)⁻¹ • (X - adj X) := rfl

private theorem rgP_mem {k : Type} [Field k] (X : M4 k) : rgP k X ∈ sp4 k := by
  have h1 : adj (-adj X) = -X := by
    rw [← neg_one_smul k, (grp k).2.2.2.1, (grp k).2.1, neg_one_smul]
  show adj _ = -_
  rw [rgP_apply, (grp k).2.2.2.1, sub_eq_add_neg, (grp k).2.2.1, h1, ← smul_neg]
  congr 1
  abel

private theorem rgP_of_mem {k : Type} [Field k] [CharZero k] {X : M4 k} (h : X ∈ sp4 k) : rgP k X = X := by
  have h' : adj X = -X := h
  rw [rgP_apply, h', sub_neg_eq_add, ← two_smul k, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

private theorem rg_adjConj {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (θ : Γ →* kˣ) (hm : ∀ g, IsGSp (θ g : k) (r g))
    (g : Γ) (X : M4 k) : adj (r g * X * r g⁻¹) = r g * adj X * r g⁻¹ := by
  have h1 : adj (r g) = (θ g : k) • r g⁻¹ := (grp k).2.2.2.2.2.2.1 _ _ _ (hm g) (by rw [← map_mul]; simp)
  have h2 : adj (r g⁻¹) = (θ g⁻¹ : k) • r g := (grp k).2.2.2.2.2.2.1 _ _ _ (hm g⁻¹) (by rw [← map_mul]; simp)
  rw [(grp k).1, (grp k).1, h1, h2]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc, ← Units.val_mul, ← map_mul]
  simp

private theorem rg_ad {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (g : Γ) (X : M4 k) :
    Loc.adGL r.toHomUnits g X = r g * X * r g⁻¹ := rfl

private theorem rg_pair {Γ k : Type} [Group Γ] [Field k] (r : Γ →* M4 k) (θ : Γ →* kˣ) (hm : ∀ g, IsGSp (θ g : k) (r g))
    (c s s' : Γ) (hs : s' = c * s * c⁻¹) :
    (r.toHomUnits s : M4 k)ᵀ * (rgJ k * (r.toHomUnits c)⁻¹ : GL (Fin 4) k) * (r.toHomUnits s' : M4 k) =
      (θ s : k) • ((rgJ k * (r.toHomUnits c)⁻¹ : GL (Fin 4) k) : M4 k) := by
  show (r s)ᵀ * ((rgJ k : M4 k) * r c⁻¹) * r s' = (θ s : k) • ((rgJ k : M4 k) * r c⁻¹)
  have h := hm s
  unfold IsGSp at h
  have e : r c⁻¹ * r s' = r s * r c⁻¹ := by
    rw [← map_mul, ← map_mul, hs]
    congr 1
    group
  rw [mul_assoc, mul_assoc, e, ← mul_assoc, rgJ_adj, mul_assoc, ← mul_assoc (adj _), h, smul_mul_assoc, one_mul, mul_smul_comm]

private theorem rg_alg {Γ k : Type} [Group Γ] [Field k] [CharZero k] (r : Γ →* M4 k) (θ : Γ →* kˣ)
    (hm : ∀ g, IsGSp (θ g : k) (r g)) (η : Γ →* kˣ) :
    ∃ ρ : Representation k Γ (M4 k),
      (∀ g X, η g = 1 → ρ g X = (r.toHomUnits g : M4 k) * X * ((r.toHomUnits g)⁻¹ : GL (Fin 4) k)) ∧
      (∀ g X, η g = -1 → ρ g X = -((((rgJ k * (r.toHomUnits g)⁻¹)⁻¹ : GL (Fin 4) k) : M4 k) * Xᵀ *
        (rgJ k * (r.toHomUnits g)⁻¹ : GL (Fin 4) k))) ∧
      (∀ g X, rgP k (Loc.adGL r.toHomUnits g X) = ρ g (rgP k X)) ∧
      ∀ g X Z, Z * r g⁻¹ ∈ sp4 k → Z * r g⁻¹ = ρ g X - X → Z = -rgP k X * r g - r g * -rgP k X := by
  have hpp : ∀ X, rgP k (rgP k X) = rgP k X := fun X => rgP_of_mem (rgP_mem X)
  have hpA : ∀ g X, rgP k (Loc.adGL r.toHomUnits g X) = Loc.adGL r.toHomUnits g (rgP k X) := fun g X => by
    rw [rgP_apply, rgP_apply, map_smul, map_sub, rg_ad, rg_ad, rg_adjConj r θ hm]
  obtain ⟨ρ, hρ⟩ := rg_twist (Loc.adGL r.toHomUnits) (rgP k) hpp hpA η
  refine ⟨ρ, fun g X h => ?_, fun g X h => ?_, fun g X => ?_, fun g X Z h1 h2 => ?_⟩
  · rw [hρ, h, Units.val_one, one_smul, ← map_add (f := _), add_sub_cancel]
    rfl
  · rw [mul_inv_rev, inv_inv]
    show _ = -((r g * ((rgJ k)⁻¹ : GL _ _)) * Xᵀ * ((rgJ k : M4 k) * r g⁻¹))
    have e : rgP k X - (X - rgP k X) = -adj X := by
      rw [rgP_apply]
      match_scalars <;> field_simp <;> ring
    rw [hρ, h, Units.val_neg, Units.val_one, neg_one_smul, ← sub_eq_add_neg, ← map_sub, e, map_neg, rg_ad,
      mul_assoc _ Xᵀ, ← mul_assoc Xᵀ, rgJ_adj]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  · rw [hρ, hpp, sub_self, map_zero, smul_zero, add_zero, hpA]
  · have e1 : Z * r g⁻¹ = r g * rgP k X * r g⁻¹ - rgP k X := by
      rw [← rgP_of_mem h1, h2, map_sub, hρ, map_add (f := _), map_smul, hpA, hpA, map_sub, hpp, sub_self, map_zero, smul_zero,
        add_zero, rg_ad]
    have := congrArg (· * r g) e1
    simp only [sub_mul, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] at this
    rw [this]
    noncomm_ring

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.rigid :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → Loc.LocalPublishedTheorems → Af.AdVanishQ → ∀ N : ℕ, 1 ≤ N → Af.KillsMu N D.ψ → Af.KillsMu N D.ξ → Af.KillsMu N D.om → ∀ ι r, D.EPt r → Irr r → Aut.IsAut4 ι r → D.RigidAt r := by
  intro Ω _ _ _ l _ c D hD hP hAd N hN h1 h2 h3 ι r hr hirr haut r' hr' hfst
  obtain ⟨hlev, θ, hθ, hdual, hθv⟩ := level D hD N hN h1 h2 h3 r hr
  obtain ⟨K, _, _, _, _, _, _, hK, hirrK⟩ := irrK D hD r hr hirr
  obtain ⟨hz, hbk, hsp⟩ := tanBK D hD hP r hr r' hr' hfst
  have hm : ∀ g, IsGSp (θ g : PadicAlgCl l) (r g) := fun g => by
    rw [hθv]
    exact (ptIn D hD _ r hr).1 g
  obtain ⟨η, hη1, hη2⟩ := rg_sign (Ω := Ω) hK (PadicAlgCl l)
  obtain ⟨ρ, ha, hb, hf, hd⟩ := rg_alg r θ hm η
  have hcc : ∃ j : Ω →+* ℂ, ∀ x, j (D.cc x) = starRingEnd ℂ (j x) := hD.isCC
  have had : Af.IsAdOf (r.toHomUnits.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))
      (θ.comp (AlgEquiv.restrictScalarsHom ℚ)) ρ :=
    ⟨D.cc, rgJ _ * (r.toHomUnits D.cc)⁻¹, hcc, fun s s' hs => rg_pair r θ hm D.cc _ _ hs, fun s X => ha _ X (hη1 s),
      fun X => hb _ X (hη2 _ hcc)⟩
  have hv := hAd K hK 4 (by norm_num) l Ω ι r.toHomUnits _ θ hlev.cont haut hθ hdual hirrK ρ had
  obtain ⟨hz', hbk'⟩ := rg_bk (rgP _) hf (fun g => rgP_of_mem (hsp g)) hz hbk
  obtain ⟨X, hX⟩ := (mem_coboundaries1 _ _).1 (hv _ hz' hbk')
  exact ⟨-rgP (PadicAlgCl l) X, (sp4 (PadicAlgCl l)).neg_mem (rgP_mem (k := PadicAlgCl l) X), fun g i j => congrFun (congrFun (hd g X _ (hsp g) (hX g)) i) j⟩
