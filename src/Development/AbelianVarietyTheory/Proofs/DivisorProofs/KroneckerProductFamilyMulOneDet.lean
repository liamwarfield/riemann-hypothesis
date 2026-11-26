module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
public import Formalism.PolynomialDimension.WeylDim
public import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSecond
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerProductFamilyMulOneDet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerProductFamilyMulOneDet
namespace GlobalTheory.DefPt

open scoped Matrix

section

variable {T : Type} [Fintype T] [DecidableEq T] {J : T → Type} [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)]
  {R : Type} [CommRing R]

theorem kronFamily_mul (M M' : ∀ t, Matrix (J t) (J t) R) :
    kron M * kron M' = kron (fun t => M t * M' t) := by
  ext I I'
  simp only [kron, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun K _ => (Finset.prod_mul_distrib).symm

theorem kronFamily_one : kron (fun t => (1 : Matrix (J t) (J t) R)) = 1 := by
  ext I I'
  simp only [kron, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

theorem kronFamily_det_single (t : T) (A : Matrix (J t) (J t) R) :
    (kron (Function.update (fun s => (1 : Matrix (J s) (J s) R)) t A)).det
      = A.det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) := by
  have h : kron (Function.update (fun s => (1 : Matrix (J s) (J s) R)) t A)
      = (Matrix.blockDiagonal (fun _ : (∀ j : {j // j ≠ t}, J j) => A)).submatrix
          (Equiv.piSplitAt t J) (Equiv.piSplitAt t J) := by
    ext I I'
    simp only [kron, Matrix.of_apply, Matrix.submatrix_apply, Matrix.blockDiagonal_apply,
      Equiv.piSplitAt_apply]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t), Function.update_self]
    have h2 : ∏ s ∈ Finset.univ.erase t,
        Function.update (fun s => (1 : Matrix (J s) (J s) R)) t A s (I s) (I' s)
        = ∏ s ∈ Finset.univ.erase t, (if I s = I' s then (1 : R) else 0) := by
      refine Finset.prod_congr rfl fun s hs => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hs), Matrix.one_apply]
    rw [h2, Finset.prod_ite_zero]
    simp [funext_iff]
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_pi]
  congr 1
  exact (Finset.prod_subtype (Finset.univ.erase t) (p := fun j => j ≠ t) (by simp)
    (fun s => Fintype.card (J s))).symm

theorem kronFamily_det (M : ∀ t, Matrix (J t) (J t) R) :
    (kron M).det = ∏ t, (M t).det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) := by
  have key : ∀ S : Finset T, (kron (fun t => if t ∈ S then M t else 1)).det
      = ∏ t ∈ S, (M t).det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [kronFamily_one]
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, ← ih, ← kronFamily_det_single, ← Matrix.det_mul, kronFamily_mul]
      congr 2
      funext s
      by_cases hs : s = a
      · subst hs
        simp [ha]
      · simp [hs]
  simpa using key Finset.univ

end

theorem kronFamily_mul_one_det :
    ∀ (T : Type) [Fintype T] [DecidableEq T] (J : T → Type) [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)]
      (R : Type) [CommRing R] (M M' : ∀ t, Matrix (J t) (J t) R),
      kron M * kron M' = kron (fun t => M t * M' t) ∧
      kron (fun t => (1 : Matrix (J t) (J t) R)) = 1 ∧
      (kron M).det = ∏ t, (M t).det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) :=
  fun _ _ _ _ _ _ _ _ M M' => ⟨kronFamily_mul M M', kronFamily_one, kronFamily_det M⟩

end GlobalTheory.DefPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerProductFamilyMulOneDetStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kroneckerProductFamily_mul_one_det : ∀ (T : Type) [Fintype T] [DecidableEq T] (J : T → Type) [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)] (R : Type) [CommRing R] (M M' : ∀ t, Matrix (J t) (J t) R), kron M * kron M' = kron (fun t => M t * M' t) ∧ kron (fun t => (1 : Matrix (J t) (J t) R)) = 1 ∧ (kron M).det = ∏ t, (M t).det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) := by
  first | exact @GlobalTheory.DefPt.kronFamily_mul_one_det | exact GlobalTheory.DefPt.kronFamily_mul_one_det | (intros; apply GlobalTheory.DefPt.kronFamily_mul_one_det <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InTypeIsoSortedPos
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

noncomputable section

namespace GlobalTheory.InertTypeIso

open Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : Ideal (𝓞 E))

def consEquiv (a : ℕ) (s : List ℕ) :
    inType P (a :: s) ≃ₗ[𝓞 E] (𝓞 E ⧸ P ^ a) × inType P s where
  toFun x := (x 0, fun i => x i.succ)
  invFun p := Fin.cons (α := fun i : Fin (s.length + 1) => 𝓞 E ⧸ P ^ (a :: s).get i) p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  right_inv p := by
    rcases p with ⟨u, v⟩
    rfl

def zeroEquiv (s : List ℕ) : inType P (0 :: s) ≃ₗ[𝓞 E] inType P s :=
  haveI : Subsingleton (𝓞 E ⧸ P ^ 0) :=
    Ideal.Quotient.subsingleton_iff.mpr ((pow_zero P).trans Ideal.one_eq_top)
  (consEquiv P 0 s).trans
    { toFun := Prod.snd
      invFun := fun x => (0, x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun p => Prod.ext (Subsingleton.elim _ _) rfl
      right_inv := fun _ => rfl }

theorem iso_of_perm {s t : List ℕ} (h : s.Perm t) :
    Nonempty (inType P s ≃ₗ[𝓞 E] inType P t) := by
  induction h with
  | nil => exact ⟨LinearEquiv.refl _ _⟩
  | cons a _ ih =>
    obtain ⟨e⟩ := ih
    exact ⟨(consEquiv P a _).trans (((LinearEquiv.refl _ _).prodCongr e).trans (consEquiv P a _).symm)⟩
  | swap a b l =>
    exact ⟨(consEquiv P b _).trans <|
      ((LinearEquiv.refl _ _).prodCongr (consEquiv P a l)).trans <|
      (LinearEquiv.prodAssoc _ _ _ _).symm.trans <|
      ((LinearEquiv.prodComm _ _ _).prodCongr (LinearEquiv.refl _ _)).trans <|
      (LinearEquiv.prodAssoc _ _ _ _).trans <|
      ((LinearEquiv.refl _ _).prodCongr (consEquiv P b l).symm).trans (consEquiv P a _).symm⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨e1⟩ := ih1
    obtain ⟨e2⟩ := ih2
    exact ⟨e1.trans e2⟩

theorem iso_filter_pos (s : List ℕ) :
    Nonempty (inType P s ≃ₗ[𝓞 E] inType P (s.filter (fun a => 0 < a))) := by
  induction s with
  | nil => exact ⟨LinearEquiv.refl _ _⟩
  | cons a s ih =>
    obtain ⟨e⟩ := ih
    cases a with
    | zero =>
      have hf : (0 :: s).filter (fun a => 0 < a) = s.filter (fun a => 0 < a) := by simp
      rw [hf]
      exact ⟨(zeroEquiv P s).trans e⟩
    | succ m =>
      have hf : ((m + 1) :: s).filter (fun a => 0 < a) = (m + 1) :: s.filter (fun a => 0 < a) := by
        simp
      rw [hf]
      exact ⟨(consEquiv P _ s).trans (((LinearEquiv.refl _ _).prodCongr e).trans (consEquiv P _ _).symm)⟩

theorem inType_iso_sorted_pos : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : Ideal (𝓞 E)) (s : List ℕ),
    ∃ y : List ℕ, y.Pairwise (· ≥ ·) ∧ (∀ a ∈ y, 0 < a) ∧ Nonempty (inType P s ≃ₗ[𝓞 E] inType P y) := by
  intro E _ _ _ P s
  refine ⟨(s.filter (fun a => 0 < a)).insertionSort (· ≥ ·), List.pairwise_insertionSort _ _, ?_, ?_⟩
  · intro a ha
    have := ((List.perm_insertionSort (· ≥ ·) _).mem_iff).mp ha
    simpa using (List.mem_filter.mp this).2
  · obtain ⟨e1⟩ := iso_filter_pos P s
    obtain ⟨e2⟩ := iso_of_perm P (List.perm_insertionSort (· ≥ ·) (s.filter (fun a => 0 < a))).symm
    exact ⟨e1.trans e2⟩

end GlobalTheory.InertTypeIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeOfLocalMatrixFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeOfLocalMatrixFamily
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.LocMatLat

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]


omit [DecidableEq ι] in
theorem exists_denom (B : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) (h : {w | ¬ IntAt w (B w)}.Finite) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ w, IntAt w ((d : K) • B w) := by
  haveI : Finite {w | ¬ IntAt w (B w)} := h
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K))
    (fun p : {w | ¬ IntAt w (B w)} × ι × ι => B p.1.1 p.2.1 p.2.2)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun w i j => ?_⟩
  by_cases hw : IntAt w (B w)
  · rw [Matrix.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_one' (w.valuation_le_one (b : 𝓞 K)) (hw i j)
  · obtain ⟨r, hr⟩ := hb (⟨w, hw⟩, i, j)
    have : ((b : 𝓞 K) : K) • B w i j = algebraMap (𝓞 K) K r := by
      rw [hr]; simp [Algebra.smul_def]
    rw [Matrix.smul_apply, this]
    exact w.valuation_le_one r


omit [DecidableEq ι] in
theorem mulVec_le (w : HeightOneSpectrum (𝓞 K)) {M : Matrix ι ι K} (hM : IntAt w M) {x : ι → K}
    (hx : ∀ j, w.valuation K (x j) ≤ 1) (i : ι) : w.valuation K ((M *ᵥ x) i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_one' (hM i j) (hx j)

theorem isLattice_locLat (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [DecidableEq ι]
    (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K) (hA : IsAdelic A) : Submodule.IsFullLattice K (locLat A) := by
  obtain ⟨hdet, hfin⟩ := hA
  obtain ⟨d, hd0, hd⟩ := exists_denom A (hfin.subset fun w hw h => hw h.1)
  obtain ⟨e, he0, he⟩ := exists_denom (fun w => (A w)⁻¹) (hfin.subset fun w hw h => hw h.2)
  have hdK : (d : K) ≠ 0 := by simpa using hd0
  have heK : (e : K) ≠ 0 := by simpa using he0
  have hLat : Submodule.IsLattice K (locLat A) := by
    constructor
    · let f : (ι → 𝓞 K) →ₗ[𝓞 K] (ι → K) := (e : K)⁻¹ • (Algebra.linearMap (𝓞 K) K).compLeft ι
      have hf : (LinearMap.range f).FG := by
        rw [← Submodule.map_top]
        exact Submodule.FG.map _ Module.Finite.fg_top
      refine hf.of_le fun x hx => ?_
      have hint : ∀ i, (e : K) * x i ∈ (algebraMap (𝓞 K) K).range := fun i =>
        HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K _ fun w => by
          have h1 := mulVec_le w (he w) (hx w) i
          rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec,
            Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hdet w)), Matrix.one_mulVec] at h1
          exact h1
      choose y hy using hint
      refine ⟨y, funext fun i => ?_⟩
      change (e : K)⁻¹ * algebraMap (𝓞 K) K (y i) = x i
      rw [hy, inv_mul_cancel_left₀ heK]
    · intro s hs hli
      exact (LinearIndependent.iff_fractionRing _ _).mp hli
  refine { toIsLattice := hLat, span_eq_top := ?_ }
  rw [eq_top_iff, ← (Pi.basisFun K ι).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  change Pi.basisFun K ι i ∈ Submodule.span K (locLat A : Set (ι → K))
  have hm : (d : K) • Pi.basisFun K ι i ∈ locLat A := by
    intro w j
    have h := mulVec_le w (hd w) (x := Pi.basisFun K ι i) (by
      intro k
      simp only [Pi.basisFun_apply, Pi.single_apply]
      split_ifs <;> simp) j
    simpa only [Matrix.smul_mulVec, Matrix.mulVec_smul] using h
  have hm' := (Submodule.span K (locLat A : Set (ι → K))).smul_mem (d : K)⁻¹
    (Submodule.subset_span hm)
  simpa only [smul_smul, inv_mul_cancel₀ hdK, one_smul] using hm'

end GlobalTheory.LocMatLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeOfLocalMatrixFamilyStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLattice_latticeOfLocalMatrixFamily : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] [DecidableEq ι] (A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K), IsAdelic A → Submodule.IsFullLattice K (locLat A) := by
  first | exact @GlobalTheory.LocMatLat.isLattice_locLat | exact GlobalTheory.LocMatLat.isLattice_locLat | (intros; apply GlobalTheory.LocMatLat.isLattice_locLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLeOfHighestVectorRowOperatorStable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLeOfHighestVectorRowOperatorStable
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare

theorem rowDiv_succ_rec (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) (k : ℕ) :
    ((k : MvPolynomial (Fin r × Fin m) R) + 1) * rowDiv R a b (k + 1) f +
      (if a = b then 1 else 0) * (k : MvPolynomial (Fin r × Fin m) R) * rowDiv R a b k f =
      rowE R r m a b (rowDiv R a b k f) := by
  unfold rowDiv
  induction f using MvPolynomial.induction_on generalizing k with
  | C c =>
    have h : rowGen R a b (C c : MvPolynomial (Fin r × Fin m) R) = Polynomial.C (C c) := by
      simp [rowGen]
    rw [h]
    cases k with
    | zero => simp [rowE_C, Polynomial.coeff_C]
    | succ k => simp
  | add p q hp hq =>
    simp only [map_add (f := _), Polynomial.coeff_add, ← hp, ← hq]
    ring
  | mul_X p v hp =>
    obtain ⟨c, s⟩ := v
    set y : MvPolynomial (Fin r × Fin m) R := if b = c then X (a, s) else 0 with hy
    have hX : rowGen R a b (X (c, s) : MvPolynomial (Fin r × Fin m) R) =
        Polynomial.C (X (c, s)) + Polynomial.C y * Polynomial.X := by
      rw [rowGen, aeval_X, hy]
      by_cases h : b = c
      · rw [if_pos h, if_pos h.symm, mul_comm]
      · rw [if_neg h, if_neg (Ne.symm h), map_zero, zero_mul]
    have hx : rowE R r m a b (X (c, s)) = y := rowE_X R r m a b c s
    have hy' : rowE R r m a b y = (if a = b then 1 else 0) * y := by
      rw [hy]
      split_ifs with h1 h2 h2
      · rw [rowE_X, if_pos h2.symm, one_mul]
      · rw [rowE_X, if_neg (Ne.symm h2), zero_mul]
      · simp
      · simp
    have hs : ∀ j, (rowGen R a b (p * X (c, s))).coeff (j + 1) =
        (rowGen R a b p).coeff (j + 1) * X (c, s) + (rowGen R a b p).coeff j * y := by
      intro j
      rw [map_mul, hX, mul_add, ← mul_assoc, Polynomial.coeff_add, Polynomial.coeff_mul_X, Polynomial.coeff_mul_C,
        Polynomial.coeff_mul_C]
    have h0 : (rowGen R a b (p * X (c, s))).coeff 0 = (rowGen R a b p).coeff 0 * X (c, s) := by
      rw [map_mul, hX, mul_add, ← mul_assoc, Polynomial.coeff_add, Polynomial.coeff_mul_X_zero, Polynomial.coeff_mul_C,
        add_zero]
    cases k with
    | zero =>
      rw [hs, h0, rowE_mul, hx, ← hp]
      push_cast
      ring
    | succ k =>
      rw [hs (k + 1), hs k, map_add (f := rowE R r m a b), rowE_mul, rowE_mul, hx, hy', ← hp, ← hp]
      push_cast
      ring

theorem rowDiv_mem_of_rowE {K : Type} [Field K] [CharZero K] {r m : ℕ} (a b : Fin r)
    (M : Submodule K (MvPolynomial (Fin r × Fin m) K)) (h : ∀ f ∈ M, rowE K r m a b f ∈ M) (k : ℕ)
    {f : MvPolynomial (Fin r × Fin m) K} (hf : f ∈ M) : rowDiv K a b k f ∈ M := by
  induction k with
  | zero => rw [(rowE_eq_rowDiv K r m a b f).2]; exact hf
  | succ k ih =>
    have hrec := rowDiv_succ_rec K a b f k
    have h1 : (if a = b then 1 else 0) * (k : MvPolynomial (Fin r × Fin m) K) * rowDiv K a b k f ∈ M := by
      split_ifs
      · rw [one_mul, ← nsmul_eq_mul]; exact nsmul_mem ih k
      · simp
    have h2 : ((k + 1 : ℕ) : K) • rowDiv K a b (k + 1) f ∈ M := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Nat.cast_succ, eq_sub_of_add_eq hrec]
      exact M.sub_mem (h _ ih) h1
    exact (M.smul_mem_iff (Nat.cast_ne_zero.2 k.succ_ne_zero)).1 h2

theorem dualWeyl_le_of_rowE_stable : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin n → ℕ), Antitone ν →
    ∀ M : Submodule K (MvPolynomial (Fin n × Fin n) K), hw K le_rfl ν ∈ M →
      (∀ a b : Fin n, ∀ f ∈ M, rowE K n n a b f ∈ M) → dualWeyl K n n ν ≤ M := by
  intro K _ _ n ν hν M h0 hE
  rw [Formalism.L2.Col.dualWeyl_eq_weyl K le_rfl ν hν, weyl, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact h0
  | cons x w ih => exact rowDiv_mem_of_rowE x.1 x.2.1 M (hE _ _) x.2.2 ih

end GlobalTheory.BrCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLeOfHighestVectorRowOperatorStableStatement
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_le_of_highest_vector_rowOperator_stable : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ M : Submodule K (MvPolynomial (Fin n × Fin n) K), hw K le_rfl ν ∈ M → (∀ a b : Fin n, ∀ f ∈ M, rowE K n n a b f ∈ M) → dualWeyl K n n ν ≤ M := by
  first | exact @GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable | exact GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable | (intros; apply GlobalTheory.BrCompare.dualWeyl_le_of_rowE_stable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackSectionsProportionalToCombinations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackSectionsProportionalToCombinations
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

open TopologicalSpace

variable {A₀ B₀ X T : Scheme.{0}} {N : LB A₀} {H : LB B₀} {mA mB : ℕ}

theorem mem_nonzeroLocus_iff_comb {a : Fin mA → LB.Sec N} {b : Fin mB → LB.Sec H} {φ : X ⟶ A₀} {p : X ⟶ T}
    {c : Fin mA → Fin mB → Γ(T, ⊤)} {Ψ : X ⟶ B₀} (hcov : ⨆ i, nonzeroLocus (b i) = ⊤)
    (hG : Generates a φ p c) (hP : Proport a b φ p Ψ c) {z : X} {q : N.ι} (hq : φ z ∈ N.U q) {k : H.ι}
    (hk : Ψ z ∈ H.U k) (i : Fin mB) :
    Ψ z ∈ nonzeroLocus (b i) ↔ IsUnit (comb a φ p c z q i) := by
  obtain ⟨j₀, hj₀⟩ := hG z q hq
  obtain ⟨i₀, hi₀⟩ := Opens.mem_iSup.1 (hcov.ge (Set.mem_univ (Ψ z)))
  have u₀ := (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (b i₀) Ψ z hk).1 hi₀
  have e₀ := hP z q k hq hk i₀ j₀
  have ub : IsUnit (gs Ψ z (H.U k) ((b j₀).f k)) := by
    have := u₀.mul hj₀
    rw [e₀] at this
    exact isUnit_of_mul_isUnit_left this
  have e := hP z q k hq hk j₀ i
  rw [GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (b i) Ψ z hk]
  constructor
  · intro h
    have := h.mul hj₀
    rw [← e] at this
    exact isUnit_of_mul_isUnit_right this
  · intro h
    have := ub.mul h
    rw [e] at this
    exact isUnit_of_mul_isUnit_left this

theorem gs_eval_eq {Rg : Type} [CommRing Rg] {fB : B₀ ⟶ Sp Rg} {a : Fin mA → LB.Sec N} {b : Fin mB → LB.Sec H}
    {φ : X ⟶ A₀} {p : X ⟶ T} {c : Fin mA → Fin mB → Γ(T, ⊤)} {Ψ₁ Ψ₂ : X ⟶ B₀}
    (hcov : ⨆ i, nonzeroLocus (b i) = ⊤) (hH : H.IsLB) (hN : N.IsLB) (hG : Generates a φ p c)
    (h₁ : Proport a b φ p Ψ₁ c) (h₂ : Proport a b φ p Ψ₂ c) (e : Ψ₁ ≫ fB = Ψ₂ ≫ fB) {i : Fin mB}
    {r : Fin mB → Γ(B₀, nonzeroLocus (b i))} (hr : ∀ j, GlobalTheory.AmpleSpan.IsRatio (b j) (b i) (r j)) (x : X)
    (m₁ : Ψ₁ x ∈ nonzeroLocus (b i)) (m₂ : Ψ₂ x ∈ nonzeroLocus (b i)) (P : MvPolynomial (Fin mB) Γ(Sp Rg, ⊤)) :
    gs Ψ₁ x _ (MvPolynomial.eval₂Hom (fB.appLE ⊤ (nonzeroLocus (b i)) le_top).hom r P) =
      gs Ψ₂ x _ (MvPolynomial.eval₂Hom (fB.appLE ⊤ (nonzeroLocus (b i)) le_top).hom r P) := by
  obtain ⟨q, hq⟩ := exists_chart hN (φ x)
  have key : ∀ Ψ : X ⟶ B₀, Proport a b φ p Ψ c → Ψ x ∈ nonzeroLocus (b i) → ∀ j,
      gs Ψ x _ (r j) * comb a φ p c x q i = comb a φ p c x q j := fun Ψ hP m j => by
    obtain ⟨k, hk⟩ := exists_chart hH (Ψ x)
    have ub := (GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (b i) Ψ x hk).1 m
    have e₁ := hP x q k hq hk j i
    rw [(hr j).gs Ψ x m hk] at e₁
    refine ub.mul_left_cancel ?_
    rw [← e₁]
    ring
  have uc : IsUnit (comb a φ p c x q i) := by
    obtain ⟨k, hk⟩ := exists_chart hH (Ψ₁ x)
    exact (mem_nonzeroLocus_iff_comb hcov hG h₁ hq hk i).1 m₁
  induction P using MvPolynomial.induction_on with
  | C a₀ =>
    rw [MvPolynomial.eval₂Hom_C, GlobalTheory.AmpleSpan.gs_const fB _ Ψ₁ x m₁, GlobalTheory.AmpleSpan.gs_const fB _ Ψ₂ x m₂, e]
  | add P Q hP hQ => rw [map_add (f := _), gs_add _ x _ m₁, gs_add _ x _ m₂, hP, hQ]
  | mul_X P j hP =>
    rw [map_mul, gs_mul _ x _ m₁, gs_mul _ x _ m₂, hP, MvPolynomial.eval₂Hom_X']
    exact congrArg _ (uc.mul_right_cancel ((key Ψ₁ h₁ m₁ j).trans (key Ψ₂ h₂ m₂ j).symm))

theorem eq_of_proport : ∀ (Rg : Type) [CommRing Rg] (A₀ B₀ X T : Scheme.{0}) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (Ψ₁ Ψ₂ : X ⟶ B₀), GlobalTheory.AmpleSpan.EmbedsBy fB b → H.IsLB → N.IsLB → GlobalTheory.HomFixUniv.Generates a φ p c → GlobalTheory.HomFixUniv.Proport a b φ p Ψ₁ c → GlobalTheory.HomFixUniv.Proport a b φ p Ψ₂ c → Ψ₁ ≫ fB = Ψ₂ ≫ fB → Ψ₁ = Ψ₂ := by
  intro Rg _ A₀ B₀ X T fB N H mA mB a b φ p c Ψ₁ Ψ₂ hE hH hN hG h₁ h₂ e
  obtain ⟨hcov, hloc⟩ := hE
  have hW : ⨆ i, Ψ₁ ⁻¹ᵁ nonzeroLocus (b i) = ⊤ := by
    refine top_le_iff.1 fun x _ => Opens.mem_iSup.2 ?_
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov.ge (Set.mem_univ (Ψ₁ x)))
    exact ⟨i, hi⟩
  let 𝒰 := X.openCoverOfIsOpenCover (fun i => Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)) hW
  refine 𝒰.hom_ext _ _ fun i => ?_
  obtain ⟨ha, r, hr, hs⟩ := hloc i
  have m₂ : ∀ x, Ψ₁ x ∈ nonzeroLocus (b i) → Ψ₂ x ∈ nonzeroLocus (b i) := fun x hx => by
    obtain ⟨q, hq⟩ := exists_chart hN (φ x)
    obtain ⟨k₁, hk₁⟩ := exists_chart hH (Ψ₁ x)
    obtain ⟨k₂, hk₂⟩ := exists_chart hH (Ψ₂ x)
    exact (mem_nonzeroLocus_iff_comb hcov hG h₂ hq hk₂ i).2 ((mem_nonzeroLocus_iff_comb hcov hG h₁ hq hk₁ i).1 hx)
  change (Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)).ι ≫ Ψ₁ = (Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)).ι ≫ Ψ₂
  have w₁ : ∀ w : (Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)).toScheme, Ψ₁ ((Ψ₁ ⁻¹ᵁ nonzeroLocus (b i)).ι w) ∈ nonzeroLocus (b i) :=
    fun w => w.2
  refine GlobalTheory.SecRingIso.hom_ext_affine ha (fun w => w₁ w) (fun w => m₂ _ (w₁ w)) fun f w => ?_
  obtain ⟨P, rfl⟩ := hs f
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_comp _ Ψ₁ w _ (w₁ w), ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_comp _ Ψ₂ w _ (m₂ _ (w₁ w))]
  exact congrArg _ (gs_eval_eq hcov hH hN hG h₁ h₂ e hr _ (w₁ w) (m₂ _ (w₁ w)) P)

end GlobalTheory.HomFixUniv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackSectionsProportionalToCombinationsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_pullbackSectionsProportionalToCombinations : ∀ (Rg : Type) [CommRing Rg] (A₀ B₀ X T : Scheme.{0}) (fB : B₀ ⟶ Sp Rg) (N : LB A₀) (H : LB B₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (Ψ₁ Ψ₂ : X ⟶ B₀), GlobalTheory.AmpleSpan.EmbedsBy fB b → H.IsLB → N.IsLB → GlobalTheory.HomFixUniv.Generates a φ p c → GlobalTheory.HomFixUniv.Proport a b φ p Ψ₁ c → GlobalTheory.HomFixUniv.Proport a b φ p Ψ₂ c → Ψ₁ ≫ fB = Ψ₂ ≫ fB → Ψ₁ = Ψ₂ := by
  first | (exact @GlobalTheory.HomFixUniv.eq_of_proport) | (exact GlobalTheory.HomFixUniv.eq_of_proport) | (intros; apply GlobalTheory.HomFixUniv.eq_of_proport  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPairingLastRowMonomialReadsCoefficient
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPairingLastRowMonomialReadsCoefficient
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

noncomputable section

namespace GlobalTheory.BrCoefFock

variable {K : Type} [Field K] {n : ℕ}

def spl (K : Type) [Field K] (n : ℕ) : BP K n →+* MvPolynomial (Unit × Fin n) (MvPolynomial (Fin n × Fin n) K) :=
  (map (rename (Prod.snd : Unit × Fin n × Fin n → Fin n × Fin n) :
      MvPolynomial (Unit × Fin n × Fin n) K →ₐ[K] MvPolynomial (Fin n × Fin n) K).toRingHom).comp
    ((GlobalTheory.BranchFormula.splitLast K Unit (rfl : n + 1 = n + 1)).toRingHom.comp
      ((rename (fun v : Fin (n + 1) × Fin (n + 1) => (((), v) : Unit × Fin (n + 1) × Fin (n + 1))) :
        _ →ₐ[K] _).toRingHom.comp (incl K n).toRingHom))

theorem coefOne_eq (b : Fin n → ℕ) (x : BP K n) :
    coefOne K n b (incl K n x) = AddMonoidAlgebra.coeff (spl K n x) (GlobalTheory.BranchFormula.expOf fun _ : Unit => b) := by
  unfold coefOne
  rw [GlobalTheory.BranchFormula.coefLast_eq_coeff]
  simp [spl, coeff_map]

theorem spl_C (a : K) : spl K n (C a) = C (C a) := by
  simp [spl, incl, GlobalTheory.BranchFormula.splitLast]

theorem spl_up (a s : Fin n) : spl K n (X (a.castSucc, s)) = C (X (a, s)) := by
  simp [spl, incl, GlobalTheory.BranchFormula.splitLast]

theorem spl_last (s : Fin n) : spl K n (X (Fin.last n, s)) = X ((), s) := by
  simp [spl, incl, GlobalTheory.BranchFormula.splitLast]

def lastV (n : ℕ) (p : Unit × Fin n) : Fin (n + 1) × Fin n := (Fin.last n, p.2)

theorem lastV_inj : Function.Injective (lastV n) := fun _ _ h =>
  Prod.ext rfl (Prod.ext_iff.1 h).2

theorem pderiv_rename_of_ne {σ τ : Type} (e : σ → τ) (v : τ) (h : ∀ u, e u ≠ v) (f : MvPolynomial σ K) :
    pderiv v (rename e f) = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p u hp => simp [hp, pderiv_X_of_ne (h u)]

theorem fockB_C_left {σ : Type} (a : K) (g : MvPolynomial σ K) : fockB (C a) g = a * constantCoeff g :=
  @fockL_C_left K _ starRingOfComm _ a g

theorem emb_inj : Function.Injective (fun v : Fin n × Fin n => ((v.1.castSucc, v.2) : Fin (n + 1) × Fin n)) :=
  (Fin.castSucc_injective n).prodMap Function.injective_id

theorem key (x : BP K n) (β : Unit × Fin n →₀ ℕ) (p : MvPolynomial (Fin n × Fin n) K) :
    fockB x (rename (lastV n) (monomial β (1 : K)) * emb K n p) =
      ((∏ u, (β u).factorial : ℕ) : K) * fockB (AddMonoidAlgebra.coeff (spl K n x) β) p := by
  classical
  induction x using MvPolynomial.induction_on generalizing β p with
  | C a =>
    rw [fockB_C_left, spl_C, coeff_C, map_mul, constantCoeff_rename, constantCoeff_monomial, emb, constantCoeff_rename]
    by_cases h : β = 0
    · subst h; simp [fockB_C_left]
    · rw [if_neg h, if_neg (Ne.symm h), ← fockBL_apply]; simp
  | add f g hf hg =>
    simp only [← fockBL_apply, map_add (f := _), LinearMap.add_apply, MvPolynomial.coeff_add] at *
    rw [hf, hg, mul_add]
  | mul_X f v hf =>
    obtain ⟨a, s⟩ := v
    rw [mul_comm f, fockB_X_mul, map_mul (spl K n), Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    induction a using Fin.lastCases with
    | cast a =>
      rw [pderiv_rename_of_ne (lastV n) (a.castSucc, s) (fun u h => (Fin.castSucc_lt_last a).ne' (Prod.ext_iff.1 h).1),
        mul_zero, add_zero, spl_up, coeff_C_mul, fockB_X_mul, ← hf]
      congr 2
      exact pderiv_rename emb_inj (a, s) p
    | last =>
      have h1 : pderiv (Fin.last n, s) (emb K n p) = 0 :=
        pderiv_rename_of_ne _ _ (fun u h => (Fin.castSucc_lt_last u.1).ne (congrArg Prod.fst h)) p
      have h2 : pderiv (Fin.last n, s) (rename (lastV n) (monomial β (1 : K))) =
          (β ((), s) : K) • rename (lastV n) (monomial (β - Finsupp.single ((), s) 1) (1 : K)) := by
        have := pderiv_rename (R := K) lastV_inj ((), s) (monomial β (1 : K))
        rw [pderiv_monomial] at this
        rw [← map_smul, smul_monomial, smul_eq_mul, mul_comm]
        exact this
      rw [h1, mul_zero, zero_add, h2, mul_comm, smul_mul_assoc, ← fockBL_apply, map_smul, fockBL_apply, hf,
        spl_last, coeff_X_mul', smul_eq_mul]
      split_ifs with h
      · rw [← mul_assoc, ← Nat.cast_mul]
        congr 2
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ((), s)),
          ← Finset.mul_prod_erase _ (fun u => (β u).factorial) (Finset.mem_univ ((), s)), ← mul_assoc]
        congr 1
        · simpa using Nat.mul_factorial_pred (Finsupp.mem_support_iff.1 h)
        · refine Finset.prod_congr rfl fun u hu => ?_
          simp [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hu)]
      · rw [Finsupp.notMem_support_iff.1 h, ← fockBL_apply (0 : MvPolynomial (Fin n × Fin n) K)]
        simp

theorem zmon_eq (b : Fin n → ℕ) :
    zmon K n b = rename (lastV n) (monomial (GlobalTheory.BranchFormula.expOf fun _ : Unit => b) (1 : K)) := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), map_prod, Fintype.prod_prod_type]
  simp [zmon, lastV]

theorem spl_zmon (b : Fin n → ℕ) :
    spl K n (zmon K n b) = monomial (GlobalTheory.BranchFormula.expOf fun _ : Unit => b) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
  simp [zmon, spl_last]

theorem spl_emb (q : MvPolynomial (Fin n × Fin n) K) : spl K n (emb K n q) = C q := by
  induction q using MvPolynomial.induction_on with
  | C a => rw [emb, rename_C, spl_C]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp => rw [map_mul, map_mul, hp, bmF_emb_X, spl_up, map_mul]

theorem fockB_zmon_emb : ∀ (K : Type) [Field K] (n : ℕ) (b : Fin n → ℕ), (∀ (x : BP K n) (p : MvPolynomial (Fin n × Fin n) K), fockB x (zmon K n b * emb K n p) = (bfact b : K) * fockB (coefOne K n b (incl K n x)) p) ∧ ∀ p q : MvPolynomial (Fin n × Fin n) K, fockB (zmon K n b * emb K n q) (zmon K n b * emb K n p) = (bfact b : K) * fockB q p := by
  intro K _ n b
  have h1 : ∀ (x : BP K n) (p : MvPolynomial (Fin n × Fin n) K), fockB x (zmon K n b * emb K n p) =
      (bfact b : K) * fockB (coefOne K n b (incl K n x)) p := by
    intro x p
    rw [zmon_eq, key, coefOne_eq, Fintype.prod_prod_type]
    simp [bfact]
  refine ⟨h1, fun p q => ?_⟩
  rw [h1, coefOne_eq, map_mul, spl_zmon, spl_emb, mul_comm (monomial _ _), coeff_C_mul]
  simp

end GlobalTheory.BrCoefFock
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPairingLastRowMonomialReadsCoefficientStatement
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPairing_lastRow_monomial_reads_coefficient : ∀ (K : Type) [Field K] (n : ℕ) (b : Fin n → ℕ), (∀ (x : BP K n) (p : MvPolynomial (Fin n × Fin n) K), fockB x (zmon K n b * emb K n p) = (bfact b : K) * fockB (coefOne K n b (incl K n x)) p) ∧ ∀ p q : MvPolynomial (Fin n × Fin n) K, fockB (zmon K n b * emb K n q) (zmon K n b * emb K n p) = (bfact b : K) * fockB q p := by
  first | exact @GlobalTheory.BrCoefFock.fockB_zmon_emb | exact GlobalTheory.BrCoefFock.fockB_zmon_emb | (intros; apply GlobalTheory.BrCoefFock.fockB_zmon_emb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreActionPreservesAdelicMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KronIdentity
namespace GlobalTheory.KroneckerIdentity

theorem kron_identity {T : Type} [Fintype T] [DecidableEq T] {J : T → Type}
    [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)] {R : Type} [CommRing R] :
    (GlobalTheory.DefPt.kron fun (t : T) ↦ (1 : Matrix (J t) (J t) R))
      = (1 : Matrix ((t : T) → J t) ((t : T) → J t) R) := by
  ext I I'
  simp only [GlobalTheory.DefPt.kron, Matrix.of_apply, Matrix.one_apply]
  by_cases h : I = I'
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨t, ht⟩ : ∃ t, I t ≠ I' t := not_forall.mp fun hc => h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)

end GlobalTheory.KroneckerIdentity
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreActionPreservesAdelicMatrices
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.FibAdel

open Formalism.HermitianLatticesTheory (localization₂)

section General

variable {K : Type} [Field K] [NumberField K]

theorem valuation_eq_one_of_vAdd (w : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) (h : vAdd w x = 0) :
    w.valuation K x = 1 := by
  unfold vAdd at h
  have h0 : w.valuation K x ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, neg_eq_zero.mp h, WithZero.exp_zero]

theorem kron_mul {T : Type} [Fintype T] [DecidableEq T] {J : T → Type} [∀ t, Fintype (J t)] {R : Type} [CommRing R]
    (M M' : ∀ t, Matrix (J t) (J t) R) : kron M * kron M' = kron fun t => M t * M' t := by
  ext I I''
  simp only [kron, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun I' _ => ?_
  rw [Finset.prod_mul_distrib]

theorem kron_one {T : Type} [Fintype T] [DecidableEq T] {J : T → Type} [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)]
    {R : Type} [CommRing R] : (kron fun t => (1 : Matrix (J t) (J t) R)) = 1 := by
  first
  | exact @_root_.GlobalTheory.KroneckerIdentity.kron_identity
  | exact _root_.GlobalTheory.KroneckerIdentity.kron_identity
  | (apply _root_.GlobalTheory.KroneckerIdentity.kron_identity <;> assumption)
  | (intros; apply _root_.GlobalTheory.KroneckerIdentity.kron_identity <;> assumption)
  | (intros; apply @_root_.GlobalTheory.KroneckerIdentity.kron_identity <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.KroneckerIdentity.kron_identity ..)

theorem rhoMat_mul {n : ℕ} (la : Fin n → ℕ) (g h : Matrix (Fin n) (Fin n) K) :
    rhoMat la g * rhoMat la h = rhoMat la (h * g) := by
  rw [GlobalTheory.DefPt.rhoMat, GlobalTheory.DefPt.rhoMat, GlobalTheory.DefPt.rhoMat, Matrix.transpose_mul, map_mul, LinearMap.toMatrix_mul]

theorem rhoMat_one {n : ℕ} (la : Fin n → ℕ) : rhoMat la (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [GlobalTheory.DefPt.rhoMat, Matrix.transpose_one, map_one, LinearMap.toMatrix_one]

theorem exists_int_scale (w : HeightOneSpectrum (𝓞 K)) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {M : Matrix ι κ K} (hM : IntAt w M) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ A : Matrix ι κ (𝓞 K),
      A.map (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) K t • M := by
  have h1 : ∀ p : ι × κ, ∃ r : 𝓞 K, ∃ d ∈ w.asIdeal.primeCompl,
      M p.1 p.2 * algebraMap (𝓞 K) K d = algebraMap (𝓞 K) K r := fun p => by
    obtain ⟨r, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer (M p.1 p.2) (hM p.1 p.2)
    exact ⟨r, d, d.2, h⟩
  choose r d hd h using h1
  refine ⟨∏ p, d p, Submonoid.prod_mem _ fun p _ => hd p,
    Matrix.of fun i j => (∏ p ∈ Finset.univ.erase (i, j), d p) * r (i, j), ?_⟩
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, map_mul, ← h]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), map_mul]
  ring

theorem valuation_repr_le_one (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} {la : Fin n → ℕ} {f : nabla la K}
    (hf : f ∈ localization₂ w.asIdeal (stdLat la K)) (i : Idx la) : w.valuation K ((basis la K).repr f i) ≤ 1 := by
  obtain ⟨s, hs, hf⟩ := hf
  rw [stdLat_eq_span, Submodule.mem_span_range_iff_exists_fun] at hf
  obtain ⟨c, hc⟩ := hf
  have hc' : ∑ i, (algebraMap (𝓞 K) K (c i)) • basis la K i = (algebraMap (𝓞 K) K s) • f := hc
  have h1 := congrArg (fun x => (basis la K).repr x i) hc'
  simp only [Module.Basis.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
  have h2 : w.valuation K (algebraMap (𝓞 K) K s) = 1 := (w.valuation_eq_one_iff_notMem).2 hs
  have h3 : w.valuation K (algebraMap (𝓞 K) K (c i)) ≤ 1 := w.valuation_le_one (c i)
  rw [h1, map_mul, h2, one_mul] at h3
  exact h3

theorem intAt_rhoMat (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (la : Fin n → ℕ) {g : Matrix (Fin n) (Fin n) K}
    (hg : IntAt w g) : IntAt w (rhoMat la g) := by
  obtain ⟨t, ht, A, hA⟩ := exists_int_scale w (M := gᵀ) (fun i j => hg j i)
  intro i j
  have hj : basis la K j ∈ localization₂ w.asIdeal (stdLat la K) :=
    ⟨1, Submonoid.one_mem _, by rw [one_smul, stdLat_eq_span]; exact Submodule.subset_span ⟨j, rfl⟩⟩
  have h := rho_mem_locP w ht hA hj
  rw [GlobalTheory.DefPt.rhoMat, LinearMap.toMatrix_apply]
  exact valuation_repr_le_one w h i

theorem intAt_smul (w : HeightOneSpectrum (𝓞 K)) {ι κ : Type} [Fintype ι] [DecidableEq ι] {c : K}
    (hc : w.valuation K c ≤ 1) {M : Matrix ι κ K} (hM : IntAt w M) : IntAt w (c • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_one' hc (hM i j)

theorem intAt_kron (w : HeightOneSpectrum (𝓞 K)) {T : Type} [Fintype T] [DecidableEq T] {J : T → Type}
    [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)] {M : ∀ t, Matrix (J t) (J t) K} (hM : ∀ t, IntAt w (M t)) :
    IntAt w (kron M) := fun I I' => by
  rw [kron, Matrix.of_apply, map_prod]
  exact Finset.prod_le_one' fun t _ => hM t (I t) (I' t)

end General

theorem fibA_isAdelic : ∀ (K : Type) [Field K] [NumberField K] (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ)
    (la : ∀ t, Fin (N t) → ℕ) (a : HeightOneSpectrum (𝓞 K) → K)
    (B : HeightOneSpectrum (𝓞 K) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) K), (∀ w, a w ≠ 0) →
    (Function.support fun w => vAdd w (a w)).Finite → (∀ t, IsAdelic fun w => B w t) →
    IsAdelic fun w => fibA la (a w) (B w) := by
  intro K _ _ T _ _ N la a B ha hfin hB
  have hinv : ∀ w, (a w)⁻¹ • kron (fun t => rhoMat (la t) (B w t)⁻¹) * fibA la (a w) (B w) = 1 := by
    intro w
    have e : ∀ t, rhoMat (la t) (B w t)⁻¹ * rhoMat (la t) (B w t) = 1 := fun t => by
      rw [rhoMat_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ((hB t).1 w)), rhoMat_one]
    rw [fibA, Matrix.smul_mul, Matrix.mul_smul, kron_mul, smul_smul, inv_mul_cancel₀ (ha w), one_smul]
    simp only [e]
    exact kron_one
  have hinv' : ∀ w, (fibA la (a w) (B w))⁻¹ = (a w)⁻¹ • kron (fun t => rhoMat (la t) (B w t)⁻¹) :=
    fun w => Matrix.inv_eq_left_inv (hinv w)
  refine ⟨fun w h => ?_, ?_⟩
  · have h1 := congrArg Matrix.det (hinv w)
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at h1
    exact zero_ne_one h1
  · refine (hfin.union (Set.finite_iUnion fun t => (hB t).2)).subset fun w hw => ?_
    by_contra hw'
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, Function.mem_support, not_or, not_exists,
      not_not] at hw'
    obtain ⟨h0, h1⟩ := hw'
    have hv : w.valuation K (a w) = 1 := valuation_eq_one_of_vAdd w (ha w) h0
    refine hw ⟨intAt_smul w hv.le (intAt_kron w fun t => intAt_rhoMat w _ (h1 t).1), ?_⟩
    rw [hinv' w]
    exact intAt_smul w (by rw [map_inv₀, hv, inv_one]) (intAt_kron w fun t => intAt_rhoMat w _ (h1 t).2)

end GlobalTheory.FibAdel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreActionPreservesAdelicMatricesStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_action_preserves_adelic_matrices : ∀ (K : Type) [Field K] [NumberField K] (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ) (a : HeightOneSpectrum (𝓞 K) → K) (B : HeightOneSpectrum (𝓞 K) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) K), (∀ w, a w ≠ 0) → (Function.support fun w => vAdd w (a w)).Finite → (∀ t, IsAdelic fun w => B w t) → IsAdelic fun w => fibA la (a w) (B w) := by
  first | exact @GlobalTheory.FibAdel.fibA_isAdelic | exact GlobalTheory.FibAdel.fibA_isAdelic | (intros; apply GlobalTheory.FibAdel.fibA_isAdelic <;> assumption)
end
end
