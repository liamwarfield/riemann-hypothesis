module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionPrincipalPerfect
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionPrincipalPerfect
namespace GlobalTheory.PerfectCompletion

section General

variable {V : Type} [CommRing V] (x : V)

theorem eval_eq_zero_iff (n : ℕ) (y : AdicCompletion (Ideal.span {x}) V) :
    AdicCompletion.eval (Ideal.span {x}) V n y = 0 ↔
      (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ n ∣ y := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton x),
    Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, -, rfl⟩
    exact ⟨b, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, trivial, by rw [Algebra.smul_def, map_pow]⟩

theorem complete :
    IsAdicComplete (Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x})
      (AdicCompletion (Ideal.span {x}) V) := by
  have h := AdicCompletion.isAdicComplete (M := V) (Submodule.fg_span_singleton x)
  rw [← IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (Ideal.span {x}) V),
    Ideal.map_span, Set.image_singleton] at h
  exact h

theorem dense (y : AdicCompletion (Ideal.span {x}) V) (r : ℕ) :
    ∃ (s : V) (z : AdicCompletion (Ideal.span {x}) V),
      y = algebraMap V _ s + (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ r * z := by
  obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (Ideal.span {x}) V r y)
  have : AdicCompletion.eval (Ideal.span {x}) V r (y - algebraMap V _ s) = 0 := by
    rw [map_sub, ← hs, sub_eq_zero]
    rfl
  obtain ⟨z, hz⟩ := (eval_eq_zero_iff x r _).1 this
  exact ⟨s, z, by rw [← hz]; ring⟩

theorem dvd_iff (s : V) (r : ℕ) :
    (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ^ r ∣ algebraMap V _ s ↔ x ^ r ∣ s := by
  rw [← eval_eq_zero_iff]
  have : AdicCompletion.eval (Ideal.span {x}) V r (algebraMap V _ s) =
      Submodule.Quotient.mk s := rfl
  rw [this, Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

theorem sModEq_iff {C : Type} [CommRing C] (c : C) (n : ℕ) (u v : C) :
    u ≡ v [SMOD (Ideal.span {c} ^ n • ⊤ : Submodule C C)] ↔ c ^ n ∣ u - v := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

end General

section Perfect

variable (l : ℕ) [Fact l.Prime] {V : Type} [CommRing V] [CharP V l] [PerfectRing V l]

theorem pow_root (c : V) : ((frobeniusEquiv V l).symm c) ^ l = c := by
  have := (frobeniusEquiv V l).apply_symm_apply c
  rwa [frobeniusEquiv_apply, frobenius_def] at this

theorem dvd_of_pow_dvd_pow (x s : V) (n : ℕ) (h : x ^ (l * n) ∣ s ^ l) : x ^ n ∣ s := by
  obtain ⟨c, hc⟩ := h
  refine ⟨(frobeniusEquiv V l).symm c, (frobeniusEquiv V l).injective ?_⟩
  rw [frobeniusEquiv_apply, frobeniusEquiv_apply, frobenius_def, frobenius_def, hc, mul_pow,
    pow_root, ← pow_mul, mul_comm n l]

end Perfect

theorem perfect : ∀ (l : ℕ) [Fact l.Prime] (V : Type) [CommRing V] [CharP V l]
    [PerfectRing V l] (x : V), ((l : ℕ) : AdicCompletion (Ideal.span {x}) V) = 0 ∧
      Function.Bijective fun y : AdicCompletion (Ideal.span {x}) V => y ^ l := by
  intro l hl V _ _ _ x
  set C := AdicCompletion (Ideal.span {x}) V
  set X := algebraMap V C x with hX
  have h0 : ((l : ℕ) : C) = 0 := by
    rw [← map_natCast (algebraMap V C), CharP.cast_eq_zero, map_zero]
  refine ⟨h0, ?_⟩
  rcases subsingleton_or_nontrivial C with hC | hC
  · exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨y, Subsingleton.elim _ _⟩⟩
  haveI : CharP C l := (CharP.charP_iff_prime_eq_zero hl.out).mpr h0
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hle : ∀ n : ℕ, n ≤ l * n := fun n => Nat.le_mul_of_pos_left n hl.out.pos
  refine ⟨fun y z hyz => ?_, fun y => ?_⟩
  ·
    have hw : (y - z) ^ l = 0 := by
      simp only at hyz
      rw [sub_pow_char, hyz, sub_self]
    rw [← sub_eq_zero]
    set w := y - z
    refine AdicCompletion.ext fun n => ?_
    rw [← AdicCompletion.eval_apply, ← AdicCompletion.eval_apply, map_zero, eval_eq_zero_iff]
    obtain ⟨s, t, hst⟩ := dense x w (l * n)
    have h1 : X ^ (l * n) ∣ algebraMap V C (s ^ l) := by
      have e : algebraMap V C (s ^ l) = -((X ^ (l * n)) ^ l * t ^ l) := by
        rw [map_pow, eq_neg_iff_add_eq_zero, ← mul_pow, ← add_pow_char, ← hst, hw]
      rw [e, dvd_neg]
      exact dvd_mul_of_dvd_left (dvd_pow_self _ hl0) _
    rw [dvd_iff] at h1
    have h2 := dvd_of_pow_dvd_pow l x s n h1
    rw [hst]
    refine dvd_add ?_ (dvd_mul_of_dvd_left (pow_dvd_pow X (hle n)) _)
    rw [dvd_iff]
    exact h2
  ·
    choose s t hst using fun n => dense x y (l * n)
    set b : ℕ → V := fun n => (frobeniusEquiv V l).symm (s n) with hb
    have hbs : ∀ n, b n ^ l = s n := fun n => pow_root l (s n)
    have hcau : ∀ {m n : ℕ}, m ≤ n →
        algebraMap V C (b m) ≡ algebraMap V C (b n) [SMOD (Ideal.span {X} ^ m • ⊤ : Submodule C C)] := by
      intro m n hmn
      rw [sModEq_iff, ← map_sub, dvd_iff]
      refine dvd_of_pow_dvd_pow l x _ m ?_
      rw [sub_pow_char, hbs, hbs, ← dvd_iff, map_sub]
      have e : algebraMap V C (s m) - algebraMap V C (s n) = X ^ (l * n) * t n - X ^ (l * m) * t m := by
        have := hst m; have := hst n; linear_combination hst n - hst m
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_left (pow_dvd_pow X (Nat.mul_le_mul_left l hmn)) _)
        (dvd_mul_right _ _)
    obtain ⟨L, hL⟩ := (complete x).toIsPrecomplete.prec hcau
    refine ⟨L, ?_⟩
    simp only
    rw [← sub_eq_zero]
    refine (complete x).toIsHausdorff.haus _ fun n => ?_
    rw [sModEq_iff, sub_zero]
    obtain ⟨u, hu⟩ := (sModEq_iff _ _ _ _).1 (hL n)
    have e : L ^ l - y = -((X ^ n) ^ l * u ^ l) - X ^ (l * n) * t n := by
      have hL' : L = algebraMap V C (b n) - X ^ n * u := by rw [← hu]; ring
      rw [hL', sub_pow_char, ← map_pow, hbs, mul_pow]
      linear_combination -(hst n)
    rw [e]
    exact dvd_sub (dvd_neg.2 (dvd_mul_of_dvd_left (dvd_pow_self _ hl0) _))
      (dvd_mul_of_dvd_left (pow_dvd_pow X (hle n)) _)

end GlobalTheory.PerfectCompletion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionPrincipalPerfectStatement
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicCompletion_principal_perfect : ∀ (l : ℕ) [Fact l.Prime] (V : Type) [CommRing V] [CharP V l] [PerfectRing V l] (x : V), ((l : ℕ) : AdicCompletion (Ideal.span {x}) V) = 0 ∧ Function.Bijective fun y : AdicCompletion (Ideal.span {x}) V => y ^ l := by
  first | exact @GlobalTheory.PerfectCompletion.perfect | exact GlobalTheory.PerfectCompletion.perfect | (intros; apply GlobalTheory.PerfectCompletion.perfect <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyLeftMulBasis
open Polynomial

namespace GlobalTheory.TraceDetSplit

theorem det_aeval_prod {K : Type} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K) (s : Multiset K) :
    (aeval N (s.map fun r => X - C r).prod).det
      = (-1) ^ (n * s.card) * (s.map N.charpoly.eval).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    have h1 : (aeval N (X - C r)).det = (-1) ^ n * N.charpoly.eval r := by
      have e : Matrix.scalar (Fin n) r - N = -(N - algebraMap K (Matrix (Fin n) (Fin n) K) r) := by
        rw [neg_sub, Matrix.algebraMap_eq_diagonal]
        rfl
      rw [Matrix.eval_charpoly, e, Matrix.det_neg, Fintype.card_fin, map_sub, aeval_X, aeval_C,
        ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, map_mul, Matrix.det_mul, ih, h1]
    ring

theorem det_aeval {E : Type} [Field E] {n : ℕ} (N : Matrix (Fin n) (Fin n) E) (p : E[X])
    (hp : p.Monic) :
    (aeval N p).det = (-1) ^ (n * p.natDegree) * resultant p N.charpoly := by
  classical
  let φ := algebraMap E (AlgebraicClosure E)
  apply φ.injective
  have hp' : (p.map φ).Monic := hp.map φ
  have hs : (p.map φ).Splits := IsAlgClosed.splits _
  have hd : (p.map φ).natDegree = p.natDegree := natDegree_map φ
  have key : φ.mapMatrix (aeval N p) = aeval (N.map φ) (p.map φ) := by
    rw [aeval_map_algebraMap]
    exact (Polynomial.aeval_algHom_apply
      (AlgHom.mapMatrix (m := Fin n) (Algebra.ofId E (AlgebraicClosure E))) N p).symm
  rw [RingHom.map_det, key, map_mul, map_pow, map_neg, map_one, ← resultant_map_map,
    ← Matrix.charpoly_map]
  conv_lhs => rw [hs.eq_prod_roots_of_monic hp']
  rw [det_aeval_prod, ← hs.natDegree_eq_card_roots, hd, ← hd,
    resultant_eq_prod_eval _ _ _ (by rw [Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim]) hs,
    hp'.leadingCoeff, one_pow, one_mul]

theorem det_trace_monic {E A : Type} [Field E] [CommRing A] [Algebra E A] {n : ℕ} (g : A)
    (e : Fin n → A) (q : Fin n → E[X]) (hd : ∀ k, (q k).natDegree = k) (hm : ∀ k, (q k).Monic) :
    (Matrix.of fun k l : Fin n => Algebra.trace E A (g ^ (k : ℕ) * e l)).det
      = (Matrix.of fun k l : Fin n => Algebra.trace E A (aeval g (q k) * e l)).det := by
  classical
  have hM : (Matrix.of fun k l : Fin n => Algebra.trace E A (aeval g (q k) * e l)) =
      (Matrix.of fun k j : Fin n => (q k).coeff (j : ℕ)) *
        Matrix.of fun k l : Fin n => Algebra.trace E A (g ^ (k : ℕ) * e l) := by
    ext k l
    simp only [Matrix.of_apply, Matrix.mul_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [aeval_eq_sum_range' (n := n) (by rw [hd k]; exact k.isLt), Finset.sum_mul, map_sum,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul]
  have hC : (Matrix.of fun k j : Fin n => (q k).coeff (j : ℕ)).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · refine Finset.prod_eq_one fun k _ => ?_
      simp only [Matrix.of_apply]
      have := (hm k).coeff_natDegree
      rwa [hd k] at this
    · intro i j hij
      simp only [Matrix.of_apply]
      apply coeff_eq_zero_of_natDegree_lt
      rw [hd i]
      exact hij
  rw [hM, Matrix.det_mul, hC, one_mul]

theorem charpoly_leftMul_basis {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] {n : ℕ} (g : A) (w : Module.Basis (Fin n) E A) :
    (Algebra.leftMulMatrix w g).charpoly = (LinearMap.mulLeft E g).charpoly := by
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
  rfl

theorem trace_mul_eq {E A : Type} [Field E] [CommRing A] [Algebra E A] {n : ℕ} (x : Fin n → A)
    (h : A) (w : Module.Basis (Fin n) E A) :
    (Matrix.of fun k l : Fin n => Algebra.trace E A (x k * h * w l))
      = (Matrix.of fun k l : Fin n => Algebra.trace E A (x k * w l)) * Algebra.leftMulMatrix w h := by
  ext k l
  simp only [Matrix.of_apply, Matrix.mul_apply, Algebra.leftMulMatrix_eq_repr_mul]
  conv_lhs => rw [mul_assoc, ← w.sum_repr (h * w l)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.TraceDetSplit


open GlobalTheory.TraceDetSplit in
theorem GlobalTheory.det_trace_pow_prod : ∀ (E A₁ A₂ : Type) [Field E] [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂) (a b : ℕ) (u : Module.Basis (Fin a) E A₁) (w : Module.Basis (Fin b) E A₂), ((LinearMap.mulLeft E g₁).charpoly * (LinearMap.mulLeft E g₂).charpoly).Separable → ∃ ε : E, ε * ε = 1 ∧ (Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂) ((g₁, g₂) ^ (k : ℕ) * Fin.addCases (fun i => (u i, 0)) (fun j => (0, w j)) l)).det = ε * resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly * (Matrix.of fun k l : Fin a => Algebra.trace E A₁ (g₁ ^ (k : ℕ) * u l)).det * (Matrix.of fun k l : Fin b => Algebra.trace E A₂ (g₂ ^ (k : ℕ) * w l)).det := by
  intro E A₁ A₂ _ _ _ _ _ _ _ g₁ g₂ a b u w _
  classical
  have hdeg₁ : (LinearMap.mulLeft E g₁).charpoly.natDegree = a := by
    rw [LinearMap.charpoly_natDegree, Module.finrank_eq_card_basis u, Fintype.card_fin]
  have hCH : aeval g₁ (LinearMap.mulLeft E g₁).charpoly = 0 := by
    have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft E g₁)
    have h2 : aeval (LinearMap.mulLeft E g₁) (LinearMap.mulLeft E g₁).charpoly =
        Algebra.lmul E A₁ (aeval g₁ (LinearMap.mulLeft E g₁).charpoly) :=
      Polynomial.aeval_algHom_apply (Algebra.lmul E A₁) g₁ _
    rw [h2] at h
    simpa using LinearMap.congr_fun h 1
  let q : Fin (a + b) → E[X] := fun k =>
    if (k : ℕ) < a then X ^ (k : ℕ) else X ^ ((k : ℕ) - a) * (LinearMap.mulLeft E g₁).charpoly
  have hd : ∀ k, (q k).natDegree = k := by
    intro k
    by_cases hk : (k : ℕ) < a
    · simp [q, hk]
    · simp only [q, hk, if_false]
      rw [(monic_X_pow _).natDegree_mul (LinearMap.charpoly_monic _), natDegree_X_pow, hdeg₁]
      omega
  have hm : ∀ k, (q k).Monic := by
    intro k
    by_cases hk : (k : ℕ) < a
    · simp only [q, hk, if_true]
      exact monic_X_pow _
    · simp only [q, hk, if_false]
      exact (monic_X_pow _).mul (LinearMap.charpoly_monic _)
  refine ⟨(-1) ^ (a * b), by rw [← mul_pow, neg_one_mul, neg_neg, one_pow], ?_⟩
  rw [det_trace_monic (g₁, g₂) _ q hd hm]
  let M := Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂)
    (aeval (g₁, g₂) (q k) * Fin.addCases (fun i => ((u i, 0) : A₁ × A₂)) (fun j => (0, w j)) l)
  let T₁ := Matrix.of fun k l : Fin a => Algebra.trace E A₁ (g₁ ^ (k : ℕ) * u l)
  let T₂ := Matrix.of fun k l : Fin b => Algebra.trace E A₂ (g₂ ^ (k : ℕ) * w l)
  let S := Matrix.of fun k l : Fin b =>
    Algebra.trace E A₂ (g₂ ^ (k : ℕ) * aeval g₂ (LinearMap.mulLeft E g₁).charpoly * w l)
  have hblock : M.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks T₁ (Matrix.of fun i j => M (Fin.castAdd b i) (Fin.natAdd a j)) 0 S := by
    ext (i | i) (l | l)
    · simp [M, T₁, q, Algebra.trace_prod_apply, aeval_prod_apply]
    · simp [M]
    · simp [M, q, Algebra.trace_prod_apply, aeval_prod_apply, hCH]
    · simp [M, S, q, Algebra.trace_prod_apply, aeval_prod_apply, mul_assoc]
  have hS : S = T₂ * Algebra.leftMulMatrix w (aeval g₂ (LinearMap.mulLeft E g₁).charpoly) :=
    trace_mul_eq (fun k : Fin b => g₂ ^ (k : ℕ)) _ w
  have hres : (Algebra.leftMulMatrix w (aeval g₂ (LinearMap.mulLeft E g₁).charpoly)).det =
      (-1) ^ (b * a) * resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly := by
    rw [← Polynomial.aeval_algHom_apply, det_aeval _ _ (LinearMap.charpoly_monic _),
      charpoly_leftMul_basis, hdeg₁]
  calc M.det = (M.submatrix finSumFinEquiv finSumFinEquiv).det :=
        (Matrix.det_submatrix_equiv_self _ _).symm
    _ = T₁.det * S.det := by rw [hblock, Matrix.det_fromBlocks_zero₂₁]
    _ = _ := by
      rw [hS, Matrix.det_mul, hres]
      ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCosetTranslateMemOfCover
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCosetTranslateMemOfCover
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem det_one_add_uniformizer_smul_ne_zero {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {r : ℕ} {ϖ : O} (hϖ : Irreducible ϖ)
    (a : Matrix (Fin r) (Fin r) O) : (1 + ϖ • a).det ≠ 0 := by
  intro h
  have hres : IsLocalRing.residue O ϖ = 0 :=
    (IsLocalRing.residue_eq_zero_iff ϖ).2 ((IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit)
  have hm : (IsLocalRing.residue O).mapMatrix (1 + ϖ • a) = 1 := by
    ext i j
    simp [Matrix.one_apply, hres, apply_ite (IsLocalRing.residue O)]
  have h1 : IsLocalRing.residue O ((1 + ϖ • a).det) = 1 := by
    rw [RingHom.map_det, hm, Matrix.det_one]
  rw [h, map_zero] at h1
  exact zero_ne_one h1

theorem exists_inv_integral_of_not_mem {O K : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] {ϖ : O}
    (hϖ : Irreducible ϖ) (y : K) (hy : ¬ ∃ c : O, y = algebraMap O K ϖ * algebraMap O K c) :
    ∃ u : O, algebraMap O K u * y = 1 := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy ⟨0, by simp⟩
  rcases ValuationRing.isInteger_or_isInteger O y with ⟨a, ha⟩ | ⟨u, hu⟩
  · have hau : IsUnit a := by
      by_contra hna
      have hmem : a ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal a).2 hna
      rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
      obtain ⟨c, rfl⟩ := hmem
      exact hy ⟨c, by rw [← ha, map_mul]⟩
    obtain ⟨v, rfl⟩ := hau
    refine ⟨(v⁻¹ : Oˣ), ?_⟩
    rw [← ha, ← map_mul]
    simp
  · exact ⟨u, by rw [hu]; exact inv_mul_cancel₀ hy0⟩

theorem coset_translate_mem_of_cover (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O)
    (hϖ : Irreducible ϖ) (N : ℕ) (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g : GL (Fin r) K)
    (z₀ : Matrix (Fin r ⊕ Fin t) (Fin r) O)
    (hx : x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O)
      (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z₀).map (algebraMap O K))
    (hcov : ∀ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, ∃ (g' : GL (Fin r) K)
      (z' : Matrix (Fin r ⊕ Fin t) (Fin r) O), (x + (ϖ ^ N • z).map (algebraMap O K)) *
      (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O)
      (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K))
    (z : Matrix (Fin r ⊕ Fin t) (Fin r) O) : ∃ z' : Matrix (Fin r ⊕ Fin t) (Fin r) O,
      (x + (ϖ ^ N • z).map (algebraMap O K)) * (g : Matrix (Fin r) (Fin r) K) =
      ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map
        (algebraMap O K) := by
  set ι := algebraMap O K with hι
  have hsmul : ∀ (c : O) {m n : Type} (A : Matrix m n O), (c • A).map ι = c • A.map ι := by
    intro c m n A
    exact Matrix.map_smul _ _ (fun a => by simp [hι, Algebra.smul_def]) A
  have hadd : ∀ {m n : Type} (A B : Matrix m n O), (A + B).map ι = A.map ι + B.map ι :=
    fun A B => Matrix.map_add _ (map_add ι) A B
  have hrow : ∀ (A : Matrix (Fin r ⊕ Fin t) (Fin r) K) (G : Matrix (Fin r) (Fin r) K),
      (A * G).toRows₁ = A.toRows₁ * G := fun A G => rfl
  set x₁ := x.toRows₁ with hx₁

  have hinv : ∀ w : Matrix (Fin r) (Fin r) O, (x₁ + (ϖ ^ N • w).map ι).det ≠ 0 := by
    intro w
    obtain ⟨g', z', h⟩ := hcov (Matrix.fromRows w 0)
    have h1 := congrArg Matrix.toRows₁ h
    rw [hrow] at h1
    have e1 : (x + (ϖ ^ N • Matrix.fromRows w (0 : Matrix (Fin t) (Fin r) O)).map ι).toRows₁ =
        x₁ + (ϖ ^ N • w).map ι := by
      ext i j; rfl
    have e2 : Matrix.toRows₁ (((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) +
        ϖ • z').map ι) = (1 + ϖ • Matrix.toRows₁ z').map ι := by
      ext i j; rfl
    rw [e1, e2] at h1
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, show ((1 + ϖ • Matrix.toRows₁ z').map ι).det = ι (1 + ϖ • Matrix.toRows₁ z').det from
      (RingHom.map_det ι _).symm] at h2
    intro h0
    rw [h0, zero_mul] at h2
    exact det_one_add_uniformizer_smul_ne_zero hϖ _
      ((injective_iff_map_eq_zero ι).1 (IsFractionRing.injective O K) _ h2.symm)

  have hdet : IsUnit x₁.det := by
    have := hinv 0
    rw [smul_zero, Matrix.map_zero _ (map_zero ι), add_zero] at this
    exact isUnit_iff_ne_zero.2 this
  set B := x₁⁻¹ with hB
  have hxB : x₁ * B = 1 := Matrix.mul_nonsing_inv _ hdet
  have hC : ∀ i j, ∃ c : O, ι (ϖ ^ N) * B i j = ι ϖ * ι c := by
    intro i j
    by_contra hne
    obtain ⟨u, hu⟩ := exists_inv_integral_of_not_mem hϖ (ι (ϖ ^ N) * B i j) hne
    apply hinv (Matrix.single j i (-u))
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun k => B k j, ?_, ?_⟩
    · intro h0
      have := congrFun h0 i
      simp only [Pi.zero_apply] at this
      rw [this, mul_zero, mul_zero] at hu
      exact zero_ne_one hu
    · funext k
      rw [Matrix.add_mulVec]
      have h1 : Matrix.mulVec x₁ (fun k => B k j) k = (1 : Matrix (Fin r) (Fin r) K) k j := by
        rw [← hxB]; rfl
      have h2 : Matrix.mulVec ((ϖ ^ N • Matrix.single j i (-u)).map ι) (fun k => B k j) k =
          if k = j then -(ι u * (ι (ϖ ^ N) * B i j)) else 0 := by
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply, Matrix.single_apply]
        by_cases hk : k = j
        · subst hk
          rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb])
            (fun h => absurd (Finset.mem_univ i) h)]
          simp [Algebra.smul_def]
          ring
        · simp [hk, Ne.symm hk]
      rw [Pi.add_apply, h1, h2, hu, Matrix.one_apply]
      split_ifs <;> simp

  choose C hC' using hC
  set Cm : Matrix (Fin r) (Fin r) O := Matrix.of C with hCmdef
  have hCm : ι (ϖ ^ N) • B = ι ϖ • Cm.map ι := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, hCmdef, Matrix.of_apply]
    exact hC' i j
  have hx1 : x₁ * (g : Matrix (Fin r) (Fin r) K) = (1 + ϖ • Matrix.toRows₁ z₀).map ι := by
    have h1 := congrArg Matrix.toRows₁ hx
    rw [hrow] at h1
    rw [h1]
    ext i j; rfl
  have hg : (g : Matrix (Fin r) (Fin r) K) = B * (1 + ϖ • Matrix.toRows₁ z₀).map ι := by
    rw [← hx1, ← Matrix.mul_assoc, hB, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have key : ϖ ^ N • (g : Matrix (Fin r) (Fin r) K) =
      ϖ • (Cm * (1 + ϖ • Matrix.toRows₁ z₀)).map ι := by
    rw [hg, Matrix.map_mul, ← Matrix.smul_mul, ← Matrix.smul_mul, ← algebraMap_smul K (ϖ ^ N) B,
      ← algebraMap_smul K ϖ (Cm.map ι), hCm]
  refine ⟨z₀ + z * (Cm * (1 + ϖ • Matrix.toRows₁ z₀)), ?_⟩
  rw [Matrix.add_mul, hx, hsmul, Matrix.smul_mul, ← Matrix.mul_smul, key]
  simp only [hadd, hsmul, Matrix.map_mul, smul_add, add_assoc, Matrix.mul_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCosetTranslateMemOfCoverStatement
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_coset_translate_mem_of_cover : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (N : ℕ) (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g : GL (Fin r) K) (z₀ : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z₀).map (algebraMap O K) → (∀ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, ∃ (g' : GL (Fin r) K) (z' : Matrix (Fin r ⊕ Fin t) (Fin r) O), (x + (ϖ ^ N • z).map (algebraMap O K)) * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K)) → ∀ z : Matrix (Fin r ⊕ Fin t) (Fin r) O, ∃ z' : Matrix (Fin r ⊕ Fin t) (Fin r) O, (x + (ϖ ^ N • z).map (algebraMap O K)) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K) := by
  first | exact @GlobalTheory.coset_translate_mem_of_cover | exact GlobalTheory.coset_translate_mem_of_cover | (intros; apply GlobalTheory.coset_translate_mem_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetOneAddSmulBlkMem
open scoped BigOperators
open Polynomial

namespace GlobalTheory.BlockDet

def blk {B : Type} {g n : ℕ} (M : Fin g → Fin g → Matrix (Fin n) (Fin n) B) :
    Matrix (Fin g × Fin n) (Fin g × Fin n) B :=
  Matrix.of fun pa qb => M pa.1 qb.1 pa.2 qb.2

def splitIdx (g n : ℕ) : Fin n ⊕ (Fin g × Fin n) ≃ Fin (g + 1) × Fin n where
  toFun := Sum.elim (fun a => (0, a)) (fun pa => (pa.1.succ, pa.2))
  invFun := fun pa => Fin.cases (motive := fun _ => Fin n ⊕ (Fin g × Fin n)) (Sum.inl pa.2)
    (fun p => Sum.inr (p, pa.2)) pa.1
  left_inv := by rintro (a | ⟨p, a⟩) <;> simp
  right_inv := by
    rintro ⟨p, a⟩
    refine Fin.cases ?_ (fun p => ?_) p <;> simp

theorem det_one_add_smul_blk_mem {B : Type} [CommRing B] {n : ℕ} (S : Subring B)
    (A : Subring (Matrix (Fin n) (Fin n) B)) (hdet : ∀ a ∈ A, a.det ∈ S) (e : B)
    (he : IsNilpotent e) (heA : ∀ a ∈ A, e • a ∈ A) (g : ℕ) :
    ∀ Θ : Fin g → Fin g → Matrix (Fin n) (Fin n) B, (∀ p q, Θ p q ∈ A) →
      (1 + e • blk Θ).det ∈ S := by
  induction g with
  | zero => intro Θ _; rw [Matrix.det_isEmpty]; exact S.one_mem
  | succ g ih =>
    intro Θ hΘ
    have hnil : IsNilpotent (⟨e • Θ 0 0, heA _ (hΘ 0 0)⟩ : A) := by
      obtain ⟨k, hk⟩ := he
      refine ⟨k, Subtype.ext ?_⟩
      simp [_root_.smul_pow, hk]
    obtain ⟨w, hw⟩ := hnil.isUnit_one_add
    set u : Matrix (Fin n) (Fin n) B := ((w⁻¹ : Aˣ) : A).1 with hu
    have huA : u ∈ A := ((w⁻¹ : Aˣ) : A).2
    have hw' : ((w : A) : Matrix (Fin n) (Fin n) B) = 1 + e • Θ 0 0 := by rw [hw]; rfl
    letI : Invertible (1 + e • Θ 0 0) :=
      ⟨u, by rw [← hw', hu, ← Subring.coe_mul]; simp, by rw [← hw', hu, ← Subring.coe_mul]; simp⟩
    have hinv : ⅟(1 + e • Θ 0 0) = u := rfl
    let Bm : Matrix (Fin n) (Fin g × Fin n) B := Matrix.of fun a qb => Θ 0 qb.1.succ a qb.2
    let Cm : Matrix (Fin g × Fin n) (Fin n) B := Matrix.of fun pa b => Θ pa.1.succ 0 pa.2 b
    have h1 : (1 + e • blk Θ).submatrix (splitIdx g n) (splitIdx g n) =
        Matrix.fromBlocks (1 + e • Θ 0 0) (e • Bm) (e • Cm)
          (1 + e • blk (fun p q => Θ p.succ q.succ)) := by
      ext (a | ⟨p, a⟩) (b | ⟨q, b⟩) <;>
        simp [splitIdx, blk, Bm, Cm, Matrix.one_apply, (Fin.succ_ne_zero _).symm]
    have h2 : (1 + e • blk (fun p q => Θ p.succ q.succ)) - (e • Cm) * u * (e • Bm) =
        1 + e • blk (fun p q => Θ p.succ q.succ - e • (Θ p.succ 0 * u * Θ 0 q.succ)) := by
      rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, add_sub_assoc, ← smul_sub]
      congr 2
    rw [← Matrix.det_submatrix_equiv_self (splitIdx g n), h1, Matrix.det_fromBlocks₁₁, hinv, h2]
    refine S.mul_mem (hdet _ (A.add_mem A.one_mem (heA _ (hΘ 0 0)))) (ih _ fun p q => ?_)
    exact A.sub_mem (hΘ _ _) (heA _ (A.mul_mem (A.mul_mem (hΘ _ _) huA) (hΘ _ _)))

def swapM {O X : Type} {n : ℕ} (a : X → Matrix (Fin n) (Fin n) O) :
    Matrix (Fin n) (Fin n) (X → O) :=
  Matrix.of fun i j x => a x i j

theorem det_sum_smul_mem {O X B : Type} [CommRing O] [CommRing B] (T : Subalgebra O (X → O))
    {n : ℕ} (ι : (X → O) →+* B) (S : Subring B) (hS : ∀ t ∈ T, ι t ∈ S) {m : ℕ}
    (a : Fin m → X → Matrix (Fin n) (Fin n) O)
    (h : ∀ d : Fin m →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det
      (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) ∈ T)
    (c : Fin m → B) (hc : ∀ k, c k ∈ S) :
    (∑ k, c k • (swapM (a k)).map ι).det ∈ S := by
  set D : MvPolynomial (Fin m) (X → O) := Matrix.det
    (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) • (swapM (a k)).map MvPolynomial.C)
    with hD
  have hco : ∀ d, AddMonoidAlgebra.coeff D d ∈ T := by
    intro d
    convert h d using 1
    funext x
    have : AddMonoidAlgebra.coeff D d x =
        AddMonoidAlgebra.coeff (MvPolynomial.map (Pi.evalRingHom (fun _ : X => O) x) D) d := by
      rw [MvPolynomial.coeff_map]; rfl
    rw [this, hD, RingHom.map_det]
    have hm : (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
        (swapM (a k)).map MvPolynomial.C).map (MvPolynomial.map (Pi.evalRingHom (fun _ : X => O) x)) =
        ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map (MvPolynomial.C (σ := Fin m)) := by
      ext i j
      simp [swapM, Matrix.sum_apply]
    exact congrArg (fun M => AddMonoidAlgebra.coeff (Matrix.det M) d) hm
  have hev : (∑ k, c k • (swapM (a k)).map ι).det = MvPolynomial.eval₂Hom ι c D := by
    rw [hD, RingHom.map_det]
    congr 1
    ext i j : 1
    simp [Matrix.sum_apply]
  rw [hev, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  exact S.sum_mem fun d _ => S.mul_mem (hS _ (hco d)) (S.prod_mem fun k _ => S.pow_mem (hc k) _)

theorem main : ∀ {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (n : ℕ) (R : Subalgebra O (X → Matrix (Fin n) (Fin n) O)), (∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, a k ∈ R) → ∀ d : Fin m →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) ∈ T) → ∀ (g : ℕ) (Θ : Fin g → Fin g → X → Matrix (Fin n) (Fin n) O), (∀ p q, Θ p q ∈ R) → (fun x => Matrix.det (Matrix.of fun (pa qb : Fin g × Fin n) => Θ pa.1 qb.1 x pa.2 qb.2)) ∈ T := by
  intro O X _ T n R hR g Θ hΘ
  set N := Fintype.card (Fin g × Fin n) with hN
  let I : Ideal (X → O)[X] := Ideal.span {Polynomial.X ^ (N + 1)}
  let π : (X → O)[X] →+* (X → O)[X] ⧸ I := Ideal.Quotient.mk I
  let ι : (X → O) →+* (X → O)[X] ⧸ I := π.comp Polynomial.C
  let S : Subring ((X → O)[X] ⧸ I) := (π.comp (Polynomial.mapRingHom T.val.toRingHom)).range
  have hS : ∀ t ∈ T, ι t ∈ S := fun t ht => ⟨Polynomial.C ⟨t, ht⟩, by simp [ι]⟩
  have heS : π Polynomial.X ∈ S := ⟨Polynomial.X, by simp⟩
  have he : IsNilpotent (π Polynomial.X) :=
    ⟨N + 1, by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)⟩
  let G : Set (Matrix (Fin n) (Fin n) ((X → O)[X] ⧸ I)) :=
    {M | ∃ a ∈ R, (swapM a).map ι = M}
  have hone : (1 : Matrix (Fin n) (Fin n) ((X → O)[X] ⧸ I)) ∈ G := by
    refine ⟨1, R.one_mem, ?_⟩
    have : swapM (1 : X → Matrix (Fin n) (Fin n) O) = 1 := by
      ext i j x
      simp [swapM, Matrix.one_apply, apply_ite (fun f : X → O => f x)]
    rw [this, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hmul : ∀ M ∈ G, ∀ M' ∈ G, M * M' ∈ G := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    refine ⟨a * b, R.mul_mem ha hb, ?_⟩
    rw [← Matrix.map_mul]
    congr 1
    ext i j x
    simp [swapM, Matrix.mul_apply]
  let A : Subalgebra S (Matrix (Fin n) (Fin n) ((X → O)[X] ⧸ I)) :=
    (Submodule.span S G).toSubalgebra (Submodule.subset_span hone) (by
      intro x y hx hy
      have := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      refine Submodule.span_mono ?_ this
      rintro _ ⟨M, hM, M', hM', rfl⟩
      exact hmul M hM M' hM')
  have hdet : ∀ a ∈ A.toSubring, a.det ∈ S := by
    intro a ha
    obtain ⟨m, c, f, rfl⟩ := Submodule.mem_span_set'.1 (show a ∈ Submodule.span S G from ha)
    choose b hb hbf using fun k => (f k).2
    have := det_sum_smul_mem T ι S hS b (hR m b hb) (fun k => c k) (fun k => (c k).2)
    simp only [hbf] at this
    exact this
  have key := det_one_add_smul_blk_mem S A.toSubring hdet (π Polynomial.X) he
    (fun a ha => A.smul_mem ha (⟨_, heS⟩ : S)) g (fun p q => (swapM (Θ p q)).map ι)
    (fun p q => Submodule.subset_span (R := S) (s := G) ⟨_, hΘ p q, rfl⟩)
  set M : Matrix (Fin g × Fin n) (Fin g × Fin n) (X → O) := blk fun p q => swapM (Θ p q) with hM
  set F : (X → O)[X] := Matrix.det ((Polynomial.X : (X → O)[X]) • M.map Polynomial.C +
    (1 : Matrix (Fin g × Fin n) (Fin g × Fin n) (X → O)).map Polynomial.C) with hF
  have hπ : (1 + π Polynomial.X • blk fun p q => (swapM (Θ p q)).map ι).det = π F := by
    rw [hF, RingHom.map_det, Matrix.map_one _ (map_zero _) (map_one _), map_add (f := _), map_one, add_comm]
    congr 2
  rw [hπ] at key
  obtain ⟨t, ht⟩ := key
  have hdvd : Polynomial.X ^ (N + 1) ∣ t.map T.val.toRingHom - F :=
    Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 ht)
  have hc := Polynomial.X_pow_dvd_iff.1 hdvd N (Nat.lt_succ_self N)
  rw [Polynomial.coeff_sub, Polynomial.coeff_map, hF, hN, Polynomial.coeff_det_X_add_C_card,
    sub_eq_zero] at hc
  have hmem : M.det ∈ T := by rw [← hc]; exact (t.coeff _).2
  convert hmem using 1
  funext x
  exact ((Pi.evalRingHom (fun _ : X => O) x).map_det M).symm

end GlobalTheory.BlockDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorRight
namespace GlobalTheory.Cyc.FontW

def Dv (l r : ℕ) (M : Type*) [AddCommGroup M] : AddSubgroup M :=
  (nsmulAddMonoidHom (l ^ r) : M →+ M).range

theorem mem_Dv {l r : ℕ} {M : Type*} [AddCommGroup M] {x : M} :
    x ∈ Dv l r M ↔ ∃ y, l ^ r • y = x := Iff.rfl

theorem Dv_map {l r : ℕ} {M M' F : Type*} [AddCommGroup M] [AddCommGroup M'] [FunLike F M M']
    [AddMonoidHomClass F M M'] (f : F) {x : M} (hx : x ∈ Dv l r M) : f x ∈ Dv l r M' := by
  obtain ⟨y, rfl⟩ := mem_Dv.1 hx
  exact mem_Dv.2 ⟨f y, (map_nsmul f _ _).symm⟩

theorem Dv_smul {l r : ℕ} {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] (a : A) {x : M}
    (hx : x ∈ Dv l r M) : a • x ∈ Dv l r M := by
  obtain ⟨y, rfl⟩ := mem_Dv.1 hx
  exact mem_Dv.2 ⟨a • y, smul_comm _ _ _⟩

def Cpl (l : ℕ) (M : Type*) [AddCommGroup M] : Prop :=
  (∀ x : M, (∀ r, x ∈ Dv l r M) → x = 0) ∧
    ∀ f : ℕ → M, (∀ r, f (r + 1) - f r ∈ Dv l r M) → ∃ L, ∀ r, L - f r ∈ Dv l r M

theorem Cpl.equiv {l : ℕ} {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] (e : M ≃+ M')
    (h : Cpl l M') : Cpl l M := by
  refine ⟨fun x hx => ?_, fun f hf => ?_⟩
  · exact e.injective (by rw [map_zero]; exact h.1 _ fun r => Dv_map e (hx r))
  · obtain ⟨L, hL⟩ := h.2 (fun r => e (f r)) fun r => by
      rw [← map_sub]; exact Dv_map e (hf r)
    refine ⟨e.symm L, fun r => ?_⟩
    have := Dv_map e.symm (hL r)
    rwa [map_sub, e.symm_apply_apply] at this

theorem Cpl.pi {l : ℕ} {M : Type*} [AddCommGroup M] (ι : Type*) (h : Cpl l M) : Cpl l (ι → M) := by
  refine ⟨fun x hx => funext fun i => ?_, fun f hf => ?_⟩
  · exact h.1 _ fun r => Dv_map (Pi.evalAddMonoidHom (fun _ : ι => M) i) (hx r)
  · choose L hL using fun i => h.2 (fun r => f r i) fun r =>
      Dv_map (Pi.evalAddMonoidHom (fun _ : ι => M) i) (hf r)
    refine ⟨L, fun r => ?_⟩
    choose y hy using fun i => mem_Dv.1 (hL i r)
    exact mem_Dv.2 ⟨y, funext hy⟩

theorem Cpl.tensor_left {l : ℕ} {R P M : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [Module.Free R P] [Module.Finite R P] [AddCommGroup M] [Module R M] (h : Cpl l M) :
    Cpl l (TensorProduct R P M) := by
  classical
  let b := Module.Free.chooseBasis R P
  exact Cpl.equiv ((TensorProduct.equivFinsuppOfBasisLeft b).toAddEquiv.trans
    Finsupp.addEquivFunOnFinite) (h.pi _)

theorem Cpl.tensor_right {l : ℕ} {R P M : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [Module.Free R P] [Module.Finite R P] [AddCommGroup M] [Module R M] (h : Cpl l M) :
    Cpl l (TensorProduct R M P) :=
  Cpl.equiv (TensorProduct.comm R M P).toAddEquiv h.tensor_left

theorem cpl_witt (p : ℕ) [Fact p.Prime] (k : Type*) [CommRing k] [CharP k p] [PerfectRing k p] :
    Cpl p (WittVector p k) := by
  have key : ∀ (r : ℕ) (x : WittVector p k), x ∈ Dv p r (WittVector p k) ↔
      x ∈ ((Ideal.span {(p : WittVector p k)}) ^ r • ⊤ : Submodule (WittVector p k) (WittVector p k)) := by
    intro r x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton', mem_Dv]
    simp [mul_comm]
  refine ⟨fun x hx => ?_, fun f hf => ?_⟩
  · exact IsHausdorff.haus (I := Ideal.span {(p : WittVector p k)}) inferInstance x fun n =>
      SModEq.zero.2 ((key n x).1 (hx n))
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {(p : WittVector p k)}) inferInstance
      (f := f) ((AdicCompletion.isAdicCauchy_iff _ _ f).2 fun n => by
        rw [SModEq.sub_mem, ← key, ← neg_sub]; exact neg_mem (hf n))
    refine ⟨L, fun r => ?_⟩
    have := hL r
    rw [SModEq.sub_mem, ← key] at this
    rw [← neg_sub]; exact neg_mem this

theorem sum_translate {G X : Type*} [Group G] [AddCommMonoid X] (N : Subgroup G) (S : Finset G)
    (hS : ∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N) (f : G → X) (hf : ∀ g, ∀ n ∈ N, f (g * n) = f g) (σ : G) :
    ∑ s ∈ S, f (σ * s) = ∑ s ∈ S, f s := by
  choose π hπ huniq using hS
  refine Finset.sum_nbij' (fun s => π (σ * s)) (fun t => π (σ⁻¹ * t)) (fun s _ => (hπ _).1)
    (fun s _ => (hπ _).1) (fun s hs => ?_) (fun t ht => ?_) (fun s _ => ?_)
  · refine (huniq _ s ⟨hs, ?_⟩).symm
    have := N.inv_mem (hπ (σ * s)).2
    simpa [mul_assoc] using this
  · refine (huniq _ t ⟨ht, ?_⟩).symm
    have := N.inv_mem (hπ (σ⁻¹ * t)).2
    simpa [mul_assoc] using this
  · have := hf (π (σ * s)) _ (hπ (σ * s)).2
    rw [← this]; simp

section Avg

variable {G A M : Type*} [Group G] [CommRing A] [AddCommGroup M] [Module A M] (l : ℕ)
  (𝓕 : Filter G) (a : G → A → A) (ρ : G → M →+ M)

theorem avg_step (amul : ∀ g h β, a (g * h) β = a g (a h β))
    (ρmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (semi : ∀ g β x, ρ g (β • x) = a g β • ρ g x)
    (htr : ∀ W ∈ 𝓕, ∃ N : Subgroup G, N.Normal ∧ (N : Set G) ∈ 𝓕 ∧ (N : Set G) ⊆ W ∧
      ∃ S : Finset G, (∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N) ∧
        ∃ β, (∀ n ∈ N, a n β = β) ∧ ∑ s ∈ S, a s β = 1)
    (c : G → M) (hc : ∀ g h, c (g * h) = c g + ρ g (c h))
    (hcont : ∀ r, {g | c g ∈ Dv l r M} ∈ 𝓕) (k : ℕ) (hk : ∀ g, c g ∈ Dv l k M) :
    ∃ b ∈ Dv l k M, (∀ r, {g | c g - (ρ g b - b) ∈ Dv l r M} ∈ 𝓕) ∧
      ∀ g, c g - (ρ g b - b) ∈ Dv l (k + 1) M := by
  obtain ⟨N, hN, hNF, hNW, S, hS, β, hβ, hsum⟩ := htr _ (hcont (k + 1))
  have hβ' : ∀ g, ∀ n ∈ N, a (g * n) β = a g β := fun g n hn => by rw [amul, hβ n hn]
  have hρ : ∀ σ, ρ σ (∑ s ∈ S, a s β • c s) = ∑ s ∈ S, a (σ * s) β • ρ σ (c s) := by
    intro σ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [semi, amul]
  refine ⟨-∑ s ∈ S, a s β • c s, neg_mem (sum_mem fun s _ => Dv_smul _ (hk s)), fun r => ?_,
    fun σ => ?_⟩
  · obtain ⟨N', hN', hNF', hNW', -⟩ := htr _ (hcont r)
    filter_upwards [hNF, hNF'] with n hn hn'
    refine sub_mem (hNW' hn') ?_
    rw [map_neg, hρ, neg_sub_neg, ← Finset.sum_sub_distrib]
    refine sum_mem fun s _ => ?_
    have h1 : n * s = s * (s⁻¹ * n * s) := by group
    have h2 : a (n * s) β = a s β := by
      rw [h1]; exact hβ' _ _ (by simpa using hN.conj_mem n hn s⁻¹)
    rw [h2, ← smul_sub]
    refine Dv_smul _ ?_
    have h3 : c s - ρ n (c s) = c n - ρ s (c (s⁻¹ * n * s)) := by
      have h4 := hc n s
      rw [h1, hc] at h4
      rw [sub_eq_sub_iff_add_eq_add, h4]
    rw [h3]
    exact sub_mem (hNW' hn') (Dv_map _ (hNW' (by simpa using hN'.conj_mem n hn' s⁻¹)))
  · have h1 : ∑ s ∈ S, a (σ * s) β = 1 := by
      rw [sum_translate N S hS (fun g => a g β) hβ' σ, hsum]
    have h2 : c σ - (ρ σ (-∑ s ∈ S, a s β • c s) - -∑ s ∈ S, a s β • c s) =
        ∑ s ∈ S, a (σ * s) β • c (σ * s) - ∑ s ∈ S, a s β • c s := by
      rw [map_neg, hρ]
      simp only [hc, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, h1, one_smul]
      abel
    rw [h2, ← QuotientAddGroup.eq_iff_sub_mem]
    have h3 := sum_translate N S hS
      (fun g => QuotientAddGroup.mk' (Dv l (k + 1) M) (a g β • c g)) (fun g n hn => by
        rw [hβ' g n hn]
        refine QuotientAddGroup.eq_iff_sub_mem.2 ?_
        rw [hc, smul_add, add_sub_cancel_left]
        exact Dv_smul _ (Dv_map _ (hNW hn))) σ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← map_sum] at h3
    exact h3

theorem avg_cob (hM : Cpl l M) (amul : ∀ g h β, a (g * h) β = a g (a h β))
    (ρmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (semi : ∀ g β x, ρ g (β • x) = a g β • ρ g x)
    (htr : ∀ W ∈ 𝓕, ∃ N : Subgroup G, N.Normal ∧ (N : Set G) ∈ 𝓕 ∧ (N : Set G) ⊆ W ∧
      ∃ S : Finset G, (∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N) ∧
        ∃ β, (∀ n ∈ N, a n β = β) ∧ ∑ s ∈ S, a s β = 1)
    (c : G → M) (hc : ∀ g h, c (g * h) = c g + ρ g (c h))
    (hcont : ∀ r, {g | c g ∈ Dv l r M} ∈ 𝓕) : ∃ b, ∀ g, c g = ρ g b - b := by
  let P : ℕ → M → Prop := fun k b => (∀ r, {g | c g - (ρ g b - b) ∈ Dv l r M} ∈ 𝓕) ∧
      ∀ g, c g - (ρ g b - b) ∈ Dv l k M
  have h0 : P 0 0 := ⟨by simpa using hcont, fun g => mem_Dv.2 ⟨_, by rw [pow_zero, one_smul]⟩⟩
  have hstep : ∀ k b, P k b → ∃ b', P (k + 1) b' ∧ b' - b ∈ Dv l k M := by
    intro k b hb
    obtain ⟨d, hd, h1, h2⟩ := avg_step l 𝓕 a ρ amul ρmul semi htr (fun g => c g - (ρ g b - b))
      (fun g h => by simp only [hc, ρmul, map_sub]; abel) hb.1 k hb.2
    have e : ∀ g, c g - (ρ g (b + d) - (b + d)) = c g - (ρ g b - b) - (ρ g d - d) := fun g => by
      rw [map_add (f := _)]; abel
    refine ⟨b + d, ⟨?_, ?_⟩, by simpa using hd⟩
    · simpa only [e] using h1
    · simpa only [e] using h2
  choose nx hnx using hstep
  let f : (k : ℕ) → {b // P k b} := fun k =>
    Nat.rec ⟨0, h0⟩ (fun k b => ⟨nx k b.1 b.2, (hnx k b.1 b.2).1⟩) k
  obtain ⟨L, hL⟩ := hM.2 (fun k => (f k).1) fun k => (hnx k (f k).1 (f k).2).2
  refine ⟨L, fun g => sub_eq_zero.1 (hM.1 _ fun r => ?_)⟩
  have e : c g - (ρ g L - L) = (c g - (ρ g (f r).1 - (f r).1)) - (ρ g (L - (f r).1) - (L - (f r).1)) := by
    rw [map_sub]; abel
  rw [e]
  exact sub_mem ((f r).2.2 g) (sub_mem (Dv_map _ (hL r)) (hL r))

end Avg

end GlobalTheory.Cyc.FontW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardFilterValLt
namespace GlobalTheory.CardFilterLt

theorem card_filter_val_lt : ∀ {n h : ℕ}, h ≤ n → Finset.card {m : Fin n | (↑m : ℕ) < h} = h := by
  intro n h hh
  have key : (Finset.univ.filter (fun m : Fin n => (m : ℕ) < h)).map Fin.valEmbedding
      = Finset.range h := by
    ext k
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact hm
    · intro hk
      exact ⟨⟨k, lt_of_lt_of_le hk hh⟩, hk, rfl⟩
  have hc := congrArg Finset.card key
  rwa [Finset.card_map, Finset.card_range] at hc

end GlobalTheory.CardFilterLt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulDiagOfTriangular
namespace GlobalTheory.TriangularDiagonal

theorem mul_diag_of_triangular :
    ∀ {p : ℕ} {κ : Fin p → ℤ}, Function.Injective κ → ∀ {M N : Matrix (Fin p) (Fin p) ℂ},
      (∀ (a b : Fin p), κ a < κ b → M a b = (0 : ℂ)) →
      (∀ (a b : Fin p), κ a < κ b → N a b = (0 : ℂ)) →
      ∀ (i : Fin p), (M * N) i i = M i i * N i i := by
  intro p κ hκ M N hM hN i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i ?_ ?_
  · intro k _ hk
    rcases lt_trichotomy (κ i) (κ k) with h | h | h
    · rw [hM i k h, zero_mul]
    · exact absurd (hκ h).symm hk
    · rw [hN k i h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

end GlobalTheory.TriangularDiagonal
end
