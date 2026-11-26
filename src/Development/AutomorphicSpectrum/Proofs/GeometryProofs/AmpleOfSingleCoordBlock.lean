module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsAbPartBaseChange
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFibreNormDehomRoots
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MatchStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordRelationsHomogeneous
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordRelationsHomogeneous
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.FormFamilies
open MvPolynomial

theorem aeval_mul_homog {σ R : Type*} [CommRing R] [Algebra ℤ R] {P : MvPolynomial σ ℤ} {n : ℕ}
    (hP : P.IsHomogeneous n) (a : R) (x : σ → R) :
    aeval (fun j => a * x j) P = a ^ n * aeval x P := by
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : d.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (mem_support_iff.mp hd)
  have : ∏ i ∈ d.support, (a * x i) ^ d i = a ^ n * ∏ i ∈ d.support, x i ^ d i := by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [← hd']
    rfl
  rw [this]
  ring

theorem ringHom_aevalZ {σ A A' : Type*} [CommRing A] [CommRing A'] [Algebra ℤ A] [Algebra ℤ A'] (f : A →+* A')
    (z : σ → A) (g : MvPolynomial σ ℤ) : f (aeval z g) = aeval (fun p => f (z p)) g := by
  induction g using MvPolynomial.induction_on with
  | C a => simp only [aeval_C]; rw [eq_intCast, eq_intCast, map_intCast]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp => simp [hp]

section Val
variable {Ω : Type} [Field Ω]

theorem exists_ratio_mem (W : ValuationSubring Ω) {κ : Type*} [Finite κ] (x : κ → Ω)
    (h : ∃ j, x j ≠ 0) : ∃ c, x c ≠ 0 ∧ ∀ j, x j / x c ∈ W :=
  _root_.UpperTheory.Reformulated.B.ValuationSubringDominantCoordinate.main W x h

theorem charZero_residue (W : ValuationSubring Ω) (hW : ∀ n : ℕ, n ≠ 0 → ((n : Ω))⁻¹ ∈ W)
    [CharZero Ω] : CharZero (IsLocalRing.ResidueField W) := by
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra h0
  have hnΩ : (n : Ω) ≠ 0 := Nat.cast_ne_zero.mpr h0
  have hu : IsUnit (n : W) := by
    refine IsUnit.of_mul_eq_one ⟨(n : Ω)⁻¹, hW n h0⟩ ?_
    apply Subtype.ext
    simp [hnΩ]
  have h1 : IsLocalRing.residue W (n : W) = 0 := by simpa using hn
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal] at h1
  exact h1 hu
end Val

section Pts
variable {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  (y : (Σ k, J k) → Ω)

theorem ne_zero_of_pt {L : Type} [Field L] {z : (Σ k, J k) → L}
    (hz : z ∈ Small.ptsOver L (mCoordIdeal y)) {p : Σ k, J k} (hp : z p ≠ 0) : y p ≠ 0 := by
  intro h0
  apply hp
  have hm : (X p : MRing J) ∈ mCoordIdeal y := by
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]
  simpa using hz.2 _ hm

theorem aeval_ratio_eq_zero (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {f : MRing J}
    (hf : f ∈ mCoordIdeal y) :
    aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) f = 0 := by
  have h0 : mConeMap y f = 0 := hf
  have h1 := congrArg (eval (fun k => (y ⟨k, c k⟩)⁻¹)) h0
  rw [map_zero] at h1
  have h2 := ringHom_aevalZ (eval (fun k => (y ⟨k, c k⟩)⁻¹))
    (fun p : Σ k, J k => (C (y p) * X p.1 : MvPolynomial K Ω)) f
  have h3 : (fun p : Σ k, J k => eval (fun k => (y ⟨k, c k⟩)⁻¹)
      (C (y p) * X p.1 : MvPolynomial K Ω)) = fun p => y p / y ⟨p.1, c p.1⟩ := by
    funext p
    simp [div_eq_mul_inv]
  rw [h3] at h2
  rw [← h2]
  exact h1

theorem ratio_pt_mem (W : ValuationSubring Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hcW : ∀ p : Σ k, J k, y p / y ⟨p.1, c p.1⟩ ∈ W) :
    (fun p => IsLocalRing.residue W ⟨y p / y ⟨p.1, c p.1⟩, hcW p⟩) ∈
      Small.ptsOver (IsLocalRing.ResidueField W) (mCoordIdeal y) := by
  constructor
  · intro k
    refine ⟨c k, ?_⟩
    have h1 : (⟨y ⟨k, c k⟩ / y ⟨k, c k⟩, hcW ⟨k, c k⟩⟩ : W) = 1 :=
      Subtype.ext (by simp [hc k])
    simp only [h1, map_one]
    exact one_ne_zero
  · intro f hf
    have h2 := @ringHom_aevalZ _ _ _ _ _ _ (Ring.toIntAlgebra _) (IsLocalRing.residue W)
      (fun p => (⟨y p / y ⟨p.1, c p.1⟩, hcW p⟩ : W)) f
    rw [← h2]
    have h3 := ringHom_aevalZ W.subtype
      (fun p => (⟨y p / y ⟨p.1, c p.1⟩, hcW p⟩ : W)) f
    have h4 : aeval (fun p => (⟨y p / y ⟨p.1, c p.1⟩, hcW p⟩ : W)) f = 0 := by
      apply Subtype.ext
      exact h3.trans (aeval_ratio_eq_zero y c hc hf)
    rw [h4, map_zero]

theorem rename_mem (k₀ : K) {P : MvPolynomial (J k₀) ℤ} {n : ℕ} (hP : P.IsHomogeneous n)
    (h0 : aeval (fun j => y ⟨k₀, j⟩) P = 0) : rename (Sigma.mk k₀) P ∈ mCoordIdeal y := by
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_rename]
  have e : ((fun p : Σ k, J k => (C (y p) * X p.1 : MvPolynomial K Ω)) ∘ Sigma.mk k₀) =
      fun j => (X k₀ : MvPolynomial K Ω) * C (y ⟨k₀, j⟩) := by
    funext j
    simp [mul_comm]
  rw [e, aeval_mul_homog hP]
  have h1 := ringHom_aevalZ (C : Ω →+* MvPolynomial K Ω) (fun j => y ⟨k₀, j⟩) P
  rw [← h1, h0, map_zero, mul_zero]
end Pts

section Homog
variable {σ : Type*}

def homogAt (i : σ) (G : MvPolynomial σ ℤ) : MvPolynomial σ ℤ :=
  ∑ m ∈ Finset.range (G.totalDegree + 1), X i ^ (G.totalDegree - m) * homogeneousComponent m G

theorem homogAt_isHomogeneous (i : σ) (G : MvPolynomial σ ℤ) :
    (homogAt i G).IsHomogeneous G.totalDegree := by
  refine IsHomogeneous.sum _ _ _ fun m hm => ?_
  have hle : m ≤ G.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have h := (isHomogeneous_X_pow (R := ℤ) i (G.totalDegree - m)).mul
    (homogeneousComponent_isHomogeneous m G)
  rwa [Nat.sub_add_cancel hle] at h

theorem aeval_homogAt {R : Type*} [Field R] (x : σ → R) (i : σ) (hi : x i ≠ 0)
    (G : MvPolynomial σ ℤ) :
    aeval x (homogAt i G) = x i ^ G.totalDegree * aeval (fun j => x j / x i) G := by
  have h0 : aeval (fun j => x j / x i) G = ∑ m ∈ Finset.range (G.totalDegree + 1),
      aeval (fun j => x j / x i) (homogeneousComponent m G) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, sum_homogeneousComponent]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h0, homogAt, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hle : m ≤ G.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have h2 := aeval_mul_homog (homogeneousComponent_isHomogeneous m G) (x i)
    (fun j => x j / x i)
  have hx : (fun j => x i * (x j / x i)) = x := by
    funext j
    field_simp
  rw [hx] at h2
  rw [map_mul, map_pow, aeval_X, h2, ← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem exists_clear {Ω : Type} [Field Ω] [CharZero Ω] (r : σ → Ω) {b : Ω}
    (hb : b ∈ Algebra.adjoin ℚ (Set.range r)) :
    ∃ (N : ℕ) (A : MvPolynomial σ ℤ), N ≠ 0 ∧ (N : Ω) * b = aeval r A := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨1, X j, one_ne_zero, by simp⟩
  | algebraMap q =>
    refine ⟨q.den, C q.num, q.den_ne_zero, ?_⟩
    have hd : (q.den : Ω) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
    rw [eq_ratCast, Rat.cast_def, aeval_C]
    simp only [eq_intCast]
    field_simp
  | add x w _ _ hx hw =>
    obtain ⟨N1, A1, h1, e1⟩ := hx
    obtain ⟨N2, A2, h2, e2⟩ := hw
    refine ⟨N1 * N2, C (N2 : ℤ) * A1 + C (N1 : ℤ) * A2, mul_ne_zero h1 h2, ?_⟩
    simp only [map_add (f := _), map_mul, aeval_C, eq_intCast, Int.cast_natCast, map_natCast, ← e1, ← e2, Nat.cast_mul]
    ring
  | mul x w _ _ hx hw =>
    obtain ⟨N1, A1, h1, e1⟩ := hx
    obtain ⟨N2, A2, h2, e2⟩ := hw
    refine ⟨N1 * N2, A1 * A2, mul_ne_zero h1 h2, ?_⟩
    simp only [map_mul, ← e1, ← e2, Nat.cast_mul]
    ring
end Homog

section Main
variable {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  (y : (Σ k, J k) → Ω)

theorem vanish {L : Type} [Field L] {z : (Σ k, J k) → L}
    (hz : z ∈ Small.ptsOver L (mCoordIdeal y)) {k₀ : K} (i : J k₀) (hy : y ⟨k₀, i⟩ ≠ 0)
    (hzi : z ⟨k₀, i⟩ ≠ 0) (G : MvPolynomial (J k₀) ℤ)
    (hG : aeval (fun j => y ⟨k₀, j⟩ / y ⟨k₀, i⟩) G = 0) :
    aeval (fun j => z ⟨k₀, j⟩ / z ⟨k₀, i⟩) G = 0 := by
  have hy0 : aeval (fun j => y ⟨k₀, j⟩) (homogAt i G) = 0 := by
    rw [aeval_homogAt (fun j => y ⟨k₀, j⟩) i hy, hG, mul_zero]
  have hm := rename_mem y k₀ (homogAt_isHomogeneous i G) hy0
  have h1 := hz.2 _ hm
  rw [aeval_rename] at h1
  have h2 := aeval_homogAt (fun j => z ⟨k₀, j⟩) i hzi G
  have h3 : aeval (fun j => z ⟨k₀, j⟩) (homogAt i G) = 0 := h1
  rw [h3] at h2
  exact (mul_eq_zero.mp h2.symm).resolve_left (pow_ne_zero _ hzi)

def ratio (k₀ : K) (i : J k₀) : J k₀ → Ω := fun j => y ⟨k₀, j⟩ / y ⟨k₀, i⟩

def chartSub [CharZero Ω] (k₀ : K) (i : J k₀) : Subring Ω :=
  (Algebra.adjoin ℚ (Set.range (ratio y k₀ i))).toSubring

def ratioA [CharZero Ω] (k₀ : K) (i : J k₀) : J k₀ → chartSub y k₀ i :=
  fun j => ⟨ratio y k₀ i j, Algebra.subset_adjoin ⟨j, rfl⟩⟩

theorem coe_aeval_ratioA [CharZero Ω] (k₀ : K) (i : J k₀) (f : MvPolynomial (J k₀) ℤ) :
    ((aeval (ratioA y k₀ i) f : chartSub y k₀ i) : Ω) = aeval (ratio y k₀ i) f :=
  ringHom_aevalZ (chartSub y k₀ i).subtype (ratioA y k₀ i) f

theorem span_top [CharZero Ω] (k₀ : K) (hy : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0)
    (S : Set (MvPolynomial (J k₀) ℤ))
    (H : ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ f ∈ S, aeval (fun i => z ⟨k₀, i⟩) f ≠ 0)
    (i : J k₀) (hi : y ⟨k₀, i⟩ ≠ 0) :
    Ideal.span ((fun f => aeval (ratioA y k₀ i) f) '' S) = ⊤ := by
  by_contra hne
  obtain ⟨W, hAW, hsub⟩ := Ideal.image_subset_nonunits_valuationSubring _ hne
  have hinv : ∀ n : ℕ, n ≠ 0 → ((n : Ω))⁻¹ ∈ W := by
    intro n _
    have h1 : ((n : Ω))⁻¹ ∈ chartSub y k₀ i := by
      have h2 := (Algebra.adjoin ℚ (Set.range (ratio y k₀ i))).algebraMap_mem ((n : ℚ)⁻¹)
      have h3 : ((n : Ω))⁻¹ ∈ Algebra.adjoin ℚ (Set.range (ratio y k₀ i)) := by simpa using h2
      exact h3
    exact hAW h1
  have hblock : ∀ k, ∃ c : J k, y ⟨k, c⟩ ≠ 0 ∧ ∀ j, y ⟨k, j⟩ / y ⟨k, c⟩ ∈ W :=
    fun k => exists_ratio_mem W _ (hy k)
  choose c0 hc0 hcW0 using hblock
  classical
  let c : ∀ k, J k := Function.update c0 k₀ i
  have hck : c k₀ = i := Function.update_self _ _ _
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k
    by_cases h : k = k₀
    · subst h
      rw [hck]
      exact hi
    · rw [show c k = c0 k from Function.update_of_ne h _ _]
      exact hc0 k
  have hcW : ∀ p : Σ k, J k, y p / y ⟨p.1, c p.1⟩ ∈ W := by
    rintro ⟨k, j⟩
    by_cases h : k = k₀
    · subst h
      simp only [hck]
      exact hAW (ratioA y k i j).2
    · simp only [show c k = c0 k from Function.update_of_ne h _ _]
      exact hcW0 k j
  haveI := charZero_residue W hinv
  obtain ⟨f, hfS, hf⟩ := H (IsLocalRing.ResidueField W) _ (ratio_pt_mem y W c hc hcW)
  apply hf
  have hnon : (aeval (ratio y k₀ i) f : Ω) ∈ W.nonunits := by
    have h1 := hsub ⟨aeval (ratioA y k₀ i) f, Ideal.subset_span ⟨f, hfS, rfl⟩, rfl⟩
    rwa [Subring.subtype_apply, coe_aeval_ratioA] at h1
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hnon
  let w : J k₀ → W := fun j => ⟨y ⟨k₀, j⟩ / y ⟨k₀, c k₀⟩, hcW ⟨k₀, j⟩⟩
  have e1 : (aeval w f : W) = ⟨aeval (ratio y k₀ i) f, hmem⟩ := by
    apply Subtype.ext
    have h3 := ringHom_aevalZ W.subtype w f
    have h4 : (fun p => W.subtype (w p)) = ratio y k₀ i := by
      funext j
      simp [w, ratio, hck]
    rw [h4] at h3
    exact h3
  have e2 := ringHom_aevalZ (IsLocalRing.residue W) w f
  change aeval (fun i' => IsLocalRing.residue W (w i')) f = 0
  rw [← e2, e1]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr hmax

theorem exists_finset_at [CharZero Ω] (k₀ : K) (hy : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0)
    (S : Set (MvPolynomial (J k₀) ℤ)) (hS : ∀ f ∈ S, ∃ n, f.IsHomogeneous n)
    (H : ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ f ∈ S, aeval (fun i => z ⟨k₀, i⟩) f ≠ 0)
    (i : J k₀) (hi : y ⟨k₀, i⟩ ≠ 0) :
    ∃ T : Finset (MvPolynomial (J k₀) ℤ), (T : Set _) ⊆ S ∧
      ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L),
        z ∈ Small.ptsOver L (mCoordIdeal y) → z ⟨k₀, i⟩ ≠ 0 →
          ∃ f ∈ T, aeval (fun i => z ⟨k₀, i⟩) f ≠ 0 := by
  classical
  have htop := span_top y k₀ hy S H i hi
  obtain ⟨s, hs, hspan⟩ := (Ideal.span_eq_top_iff_finite _).1 htop
  obtain ⟨T, hT, rfl⟩ := Finset.subset_set_image_iff.1 hs
  refine ⟨T, hT, ?_⟩
  intro L _ _ z hz hzi
  by_contra hall
  push_neg at hall
  have key : ∀ b ∈ Ideal.span ((T.image fun f => aeval (ratioA y k₀ i) f :
      Finset (chartSub y k₀ i)) : Set (chartSub y k₀ i)),
      ∃ (N : ℕ) (G : MvPolynomial (J k₀) ℤ), N ≠ 0 ∧ (N : Ω) * (b : Ω) = aeval (ratio y k₀ i) G ∧
        aeval (fun j => z ⟨k₀, j⟩ / z ⟨k₀, i⟩) G = 0 := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem x hx =>
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨f, hf, rfl⟩ := hx
      refine ⟨1, f, one_ne_zero, by rw [Nat.cast_one, _root_.one_mul, coe_aeval_ratioA], ?_⟩
      obtain ⟨n, hn⟩ := hS f (hT hf)
      have h1 := aeval_mul_homog hn (z ⟨k₀, i⟩)⁻¹ (fun j => z ⟨k₀, j⟩)
      rw [hall f hf, mul_zero] at h1
      rw [← h1]
      congr 2
      funext j
      rw [div_eq_inv_mul]
    | zero => exact ⟨1, 0, one_ne_zero, by simp, by simp⟩
    | add x w _ _ hx hw =>
      obtain ⟨N1, A1, h1, e1, v1⟩ := hx
      obtain ⟨N2, A2, h2, e2, v2⟩ := hw
      refine ⟨N1 * N2, C (N2 : ℤ) * A1 + C (N1 : ℤ) * A2, mul_ne_zero h1 h2, ?_, ?_⟩
      · simp only [map_add (f := _), map_mul, aeval_C, eq_intCast, Int.cast_natCast, map_natCast, ← e1, ← e2,
          Nat.cast_mul, AddMemClass.coe_add]
        ring
      · simp only [map_add (f := _), map_mul, v1, v2, mul_zero, add_zero]
    | smul a x _ hx =>
      obtain ⟨N1, A1, h1, e1⟩ := exists_clear (ratio y k₀ i) a.2
      obtain ⟨N2, A2, h2, e2, v2⟩ := hx
      refine ⟨N1 * N2, A1 * A2, mul_ne_zero h1 h2, ?_, ?_⟩
      · simp only [map_mul, ← e1, ← e2, Nat.cast_mul, smul_eq_mul, MulMemClass.coe_mul]
        ring
      · simp only [map_mul, v2, mul_zero]
  obtain ⟨N, G, hN, e1, e2⟩ := key 1 (by rw [hspan]; trivial)
  have hG : aeval (ratio y k₀ i) (G - C (N : ℤ)) = 0 := by
    simp [← e1]
  have h1 := vanish y hz i hi hzi _ hG
  simp only [map_sub, e2, aeval_C, eq_intCast, zero_sub, neg_eq_zero, Int.cast_natCast, map_natCast] at h1
  exact hN (Nat.cast_eq_zero.mp h1)

theorem exists_finset [CharZero Ω] (k₀ : K) (hy : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0)
    (S : Set (MvPolynomial (J k₀) ℤ)) (hS : ∀ f ∈ S, ∃ n, f.IsHomogeneous n)
    (H : ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ f ∈ S, aeval (fun i => z ⟨k₀, i⟩) f ≠ 0) :
    ∃ T : Finset (MvPolynomial (J k₀) ℤ), (T : Set _) ⊆ S ∧
      ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L),
        z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ f ∈ T, aeval (fun i => z ⟨k₀, i⟩) f ≠ 0 := by
  classical
  have hi : ∀ i : J k₀, ∃ T : Finset (MvPolynomial (J k₀) ℤ), (T : Set _) ⊆ S ∧
      ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L),
        z ∈ Small.ptsOver L (mCoordIdeal y) → z ⟨k₀, i⟩ ≠ 0 →
          ∃ f ∈ T, aeval (fun i => z ⟨k₀, i⟩) f ≠ 0 := by
    intro i
    by_cases h : y ⟨k₀, i⟩ = 0
    · exact ⟨∅, by simp, fun L _ _ z hz hzi => absurd h (ne_zero_of_pt y hz hzi)⟩
    · exact exists_finset_at y k₀ hy S hS H i h
  choose T hT hT' using hi
  refine ⟨Finset.univ.biUnion T, ?_, ?_⟩
  · intro f hf
    obtain ⟨i, -, hfi⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hf)
    exact hT i hfi
  · intro L _ _ z hz
    obtain ⟨i, hi'⟩ := hz.1 k₀
    obtain ⟨f, hf, hne⟩ := hT' i L z hz hi'
    exact ⟨f, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hf⟩, hne⟩
end Main

theorem finite_families : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ k : K, ∃ (l : ℕ) (n : Fin l → ℕ) (F : Fin l → J k → MvPolynomial (J k₀) ℤ), (∀ t j, (F t j).IsHomogeneous (n t)) ∧ (∀ t j j', MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F t j) * y ⟨k, j'⟩ = MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F t j') * y ⟨k, j⟩) ∧ ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ t j, MvPolynomial.aeval (fun i' : J k₀ => z ⟨k₀, i'⟩) (F t j) ≠ 0 := by
  intro X Ω _ _ ξ K _ J _ y k₀ hT hE k
  have hy : ∀ k', ∃ j, y ⟨k', j⟩ ≠ 0 := by
    intro k'
    obtain ⟨c, hc, -⟩ := hT.cover ⟨genPt ξ, specializes_rfl⟩
    exact ⟨c k', Finset.prod_ne_zero_iff.mp hc k' (Finset.mem_univ _)⟩
  let Fam : ℕ → (J k → MvPolynomial (J k₀) ℤ) → Prop := fun n F =>
    (∀ j, (F j).IsHomogeneous n) ∧
      ∀ j j', aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F j) * y ⟨k, j'⟩ =
        aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F j') * y ⟨k, j⟩
  let S : Set (MvPolynomial (J k₀) ℤ) := {f | ∃ n F j, Fam n F ∧ f = F j}
  have hS : ∀ f ∈ S, ∃ n, f.IsHomogeneous n := by
    rintro f ⟨n, F, j, hF, rfl⟩
    exact ⟨n, hF.1 j⟩
  have H : ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ f ∈ S, aeval (fun i => z ⟨k₀, i⟩) f ≠ 0 := by
    intro L _ _ z hz
    obtain ⟨i, hi⟩ := hz.1 k₀
    obtain ⟨c, hc⟩ := hz.1 k
    obtain ⟨n, F, hom, rel, hne⟩ := GlobalTheory.T.small_points_coord_ratio_bound X Ω ξ K J y k₀ hT hE L z hz i k c hi hc
    have yc : y ⟨k, c⟩ ≠ 0 := ne_zero_of_pt y hz hc
    refine ⟨F c, ⟨n, F, c, ⟨hom, fun j j' => mul_right_cancel₀ yc ?_⟩, rfl⟩, hne⟩
    linear_combination y ⟨k, j'⟩ * rel j - y ⟨k, j⟩ * rel j'
  obtain ⟨T, hTS, hT'⟩ := exists_finset y k₀ hy S hS H
  have hch : ∀ f : T, ∃ (n : ℕ) (F : J k → MvPolynomial (J k₀) ℤ) (j : J k),
      Fam n F ∧ f.1 = F j := fun f => hTS f.2
  choose n F j hF hj using hch
  refine ⟨T.card, fun t => n (T.equivFin.symm t), fun t => F (T.equivFin.symm t),
    fun t => (hF _).1, fun t => (hF _).2, ?_⟩
  intro L _ _ z hz
  obtain ⟨f, hf, hne⟩ := hT' L z hz
  refine ⟨T.equivFin ⟨f, hf⟩, j ⟨f, hf⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  rw [← hj ⟨f, hf⟩]
  exact hne

end GlobalTheory.CompanionTheory.Ar.FormFamilies
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordRelationsHomogeneousStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coord_relations_homogeneous : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ k : K, ∃ (l : ℕ) (n : Fin l → ℕ) (F : Fin l → J k → MvPolynomial (J k₀) ℤ), (∀ t j, (F t j).IsHomogeneous (n t)) ∧ (∀ t j j', MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F t j) * y ⟨k, j'⟩ = MvPolynomial.aeval (fun i' : J k₀ => y ⟨k₀, i'⟩) (F t j') * y ⟨k, j⟩) ∧ ∀ (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) → ∃ t j, MvPolynomial.aeval (fun i' : J k₀ => z ⟨k₀, i'⟩) (F t j) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FormFamilies.finite_families | exact GlobalTheory.CompanionTheory.Ar.FormFamilies.finite_families | (intros; apply GlobalTheory.CompanionTheory.Ar.FormFamilies.finite_families <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AmpleOfSingleCoordBlock
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.AmpleBlock

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

variable {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

theorem homog_rename (k₀ : K) {F : MvPolynomial (J k₀) ℤ} {n : ℕ} (h : F.IsHomogeneous n) :
    IsMultiHomog (rename (Sigma.mk k₀) F : MRing J) (Pi.single k₀ n) := by
  classical
  intro m hm k
  rw [support_rename_of_injective sigma_mk_injective] at hm
  obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hm
  have hd : ∑ i, m' i = n := by
    have := h (mem_support_iff.1 hm')
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  by_cases hk : k = k₀
  · subst hk
    simp [Finsupp.mapDomain_apply_of_injective sigma_mk_injective, hd]
  · have h0 : ∀ i, Finsupp.mapDomain (Sigma.mk k₀) m' ⟨k, i⟩ = 0 := fun i =>
      Finsupp.mapDomain_notin_range _ _ (by
        rintro ⟨i', hi'⟩
        exact hk (congrArg Sigma.fst hi').symm)
    simp [h0, Pi.single_apply, hk]

theorem rel_at_point {y : (Σ k, J k) → Ω} (k₀ k : K) {A B : MvPolynomial (J k₀) ℤ} {n : ℕ}
    (hA : A.IsHomogeneous n) (hB : B.IsHomogeneous n) (j j' : J k)
    (hr : aeval (fun i => y ⟨k₀, i⟩) A * y ⟨k, j'⟩ = aeval (fun i => y ⟨k₀, i⟩) B * y ⟨k, j⟩)
    {L : Type} [Field L] {z : (Σ k, J k) → L} (hz : z ∈ Small.ptsOver L (mCoordIdeal y)) :
    aeval (fun i => z ⟨k₀, i⟩) A * z ⟨k, j'⟩ = aeval (fun i => z ⟨k₀, i⟩) B * z ⟨k, j⟩ := by
  have hm : (rename (Sigma.mk k₀) A * X ⟨k, j'⟩ - rename (Sigma.mk k₀) B * X ⟨k, j⟩ : MRing J) ∈ mCoordIdeal y := by
    change mConeMap y _ = 0
    rw [map_sub, map_mul, map_mul, ProjLine.mConeMap_eq_of_isMultiHomog y (homog_rename k₀ hA),
      ProjLine.mConeMap_eq_of_isMultiHomog y (homog_rename k₀ hB)]
    simp only [mConeMap, aeval_X, aeval_rename]
    have := congrArg (C : Ω →+* MvPolynomial K Ω) hr
    rw [map_mul, map_mul] at this
    simp only [Function.comp_def]
    linear_combination ((∏ k, (X k : MvPolynomial K Ω) ^ (Pi.single k₀ n : K → ℕ) k) * X k) * this
  have := hz.2 _ hm
  simp only [map_sub, map_mul, aeval_X, aeval_rename, Function.comp_def] at this
  exact sub_eq_zero.mp this

def gForm (k₀ : K) (i : J k₀) (e : ℕ) (G : K → MvPolynomial (J k₀) ℤ) : MRing J :=
  X ⟨k₀, i⟩ ^ e * ∏ k ∈ Finset.univ.erase k₀, rename (Sigma.mk k₀) (G k)

def hForm (k₀ : K) (j : ∀ k, J k) : MRing J :=
  ∏ k ∈ Finset.univ.erase k₀, X ⟨k, j k⟩

theorem gForm_homog (k₀ : K) (i : J k₀) (e : ℕ) {G : K → MvPolynomial (J k₀) ℤ} {d : K → ℕ}
    (hG : ∀ k, (G k).IsHomogeneous (d k)) :
    IsMultiHomog (gForm k₀ i e G) (Pi.single k₀ (e + ∑ k ∈ Finset.univ.erase k₀, d k)) := by
  have h := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul (isMultiHomog_pow (isMultiHomog_X' k₀ i : IsMultiHomog (X ⟨k₀, i⟩ : MRing J) _) e)
    (isMultiHomog_prod (Finset.univ.erase k₀) (fun k => rename (Sigma.mk k₀) (G k))
      (fun k => Pi.single k₀ (d k)) fun k => homog_rename k₀ (hG k))
  rw [gForm]
  convert h using 1
  funext k'
  by_cases hk : k' = k₀
  · subst hk
    simp [Finset.sum_apply]
  · simp [Finset.sum_apply, Pi.single_apply, hk]

def hDeg (k₀ : K) : K → ℕ := fun k => if k = k₀ then 0 else 1

theorem hForm_homog (k₀ : K) (j : ∀ k, J k) : IsMultiHomog (hForm k₀ j) (hDeg k₀) := by
  have h := isMultiHomog_prod (Finset.univ.erase k₀) (fun k => (X ⟨k, j k⟩ : MRing J))
      (fun k => Pi.single k 1) fun k => isMultiHomog_X' k (j k)
  rw [hForm]
  convert h using 1
  funext k'
  by_cases hk : k' = k₀
  · subst hk
    simp [hDeg, Finset.sum_apply, Pi.single_apply]
  · simp [hDeg, Finset.sum_apply, Pi.single_apply, hk]

theorem aeval_gForm {L : Type} [Field L] (z : (Σ k, J k) → L) (k₀ : K) (i : J k₀) (e : ℕ)
    (G : K → MvPolynomial (J k₀) ℤ) :
    aeval z (gForm k₀ i e G) = z ⟨k₀, i⟩ ^ e * ∏ k ∈ Finset.univ.erase k₀, aeval (fun i => z ⟨k₀, i⟩) (G k) := by
  simp [gForm, map_prod, aeval_rename, Function.comp_def]

theorem aeval_hForm {L : Type} [Field L] (z : (Σ k, J k) → L) (k₀ : K) (j : ∀ k, J k) :
    aeval z (hForm k₀ j) = ∏ k ∈ Finset.univ.erase k₀, z ⟨k, j k⟩ := by
  simp [hForm, map_prod]

def sec (y : (Σ k, J k) → Ω) (k₀ : K) (js : ∀ k, J k) (i : J k₀) (e : ℕ) (G : K → MvPolynomial (J k₀) ℤ) : Ω :=
  y ⟨k₀, i⟩ ^ e * ∏ k ∈ Finset.univ.erase k₀, aeval (fun i => y ⟨k₀, i⟩) (G k) / y ⟨k, js k⟩

theorem sec_mul (y : (Σ k, J k) → Ω) (k₀ : K) (js j : ∀ k, J k) (hjs : ∀ k, y ⟨k, js k⟩ ≠ 0) (i : J k₀) (e : ℕ)
    (G G' : K → MvPolynomial (J k₀) ℤ)
    (hr : ∀ k, aeval (fun i => y ⟨k₀, i⟩) (G k) * y ⟨k, j k⟩ = aeval (fun i => y ⟨k₀, i⟩) (G' k) * y ⟨k, js k⟩) :
    aeval y (gForm k₀ i e G') = sec y k₀ js i e G * aeval y (hForm k₀ j) := by
  rw [aeval_gForm, aeval_hForm, sec, _root_.mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  have := hjs k
  field_simp
  exact (hr k).symm

theorem ampleQ_of_forms (y : (Σ k, J k) → Ω) (k₀ : K) (a : K → ℤ) (ha₀ : a k₀ = 1) (ha : ∀ k, k ≠ k₀ → a k = 0)
    (l : K → ℕ) (n : ∀ k, Fin (l k) → ℕ) (F : ∀ k, Fin (l k) → J k → MvPolynomial (J k₀) ℤ)
    (hom : ∀ k t j, (F k t j).IsHomogeneous (n k t))
    (rel : ∀ k t j j', aeval (fun i => y ⟨k₀, i⟩) (F k t j) * y ⟨k, j'⟩ =
      aeval (fun i => y ⟨k₀, i⟩) (F k t j') * y ⟨k, j⟩)
    (pts : ∀ k (L : Type) [Field L] [CharZero L] (z : (Σ k, J k) → L), z ∈ Small.ptsOver L (mCoordIdeal y) →
      ∃ t j, aeval (fun i => z ⟨k₀, i⟩) (F k t j) ≠ 0) :
    Ht.AmpleQ y a := by
  by_cases hy : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0
  swap
  · push_neg at hy
    obtain ⟨k, hk⟩ := hy
    refine ⟨0, 0, Fin.elim0, fun i => i.elim0, fun L _ _ z hz => ?_⟩
    exfalso
    obtain ⟨i, hi⟩ := hz.1 k
    have hm : (X ⟨k, i⟩ : MRing J) ∈ mCoordIdeal y := by
      change mConeMap y _ = 0
      simp [mConeMap, hk i]
    exact hi (by simpa using hz.2 _ hm)
  choose js hjs using hy

  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ T : ∀ k, Fin (l k), ∑ k ∈ Finset.univ.erase k₀, n k (T k) ≤ N := by
    refine ⟨∑ k, ∑ t, n k t, fun T => ?_⟩
    calc ∑ k ∈ Finset.univ.erase k₀, n k (T k) ≤ ∑ k ∈ Finset.univ.erase k₀, ∑ t, n k t :=
          Finset.sum_le_sum fun k _ => Finset.single_le_sum (f := n k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
  let eT : (∀ k, Fin (l k)) → ℕ := fun T => N - ∑ k ∈ Finset.univ.erase k₀, n k (T k)
  have heT : ∀ T, eT T + ∑ k ∈ Finset.univ.erase k₀, n k (T k) = N := fun T => Nat.sub_add_cancel (hN T)
  let I := (∀ k, Fin (l k)) × J k₀
  let S : I → Ω := fun p => sec y k₀ js p.2 (eT p.1) fun k => F k (p.1 k) (js k)
  have hdeg : ∀ k, ((Pi.single k₀ N : K → ℕ) k : ℤ) = hDeg k₀ k + (((N + 1 : ℕ) : ℤ) * a k - 1) := by
    intro k
    by_cases hk : k = k₀
    · subst hk
      simp [hDeg, ha₀]
    · simp [hDeg, Pi.single_apply, hk, ha k hk]

  have hform : ∀ (p : I) (j : ∀ k, J k), IsMultiHomog (gForm k₀ p.2 (eT p.1) fun k => F k (p.1 k) (j k))
      (Pi.single k₀ N) ∧ aeval y (gForm k₀ p.2 (eT p.1) fun k => F k (p.1 k) (j k)) = S p * aeval y (hForm k₀ j) := by
    intro p j
    refine ⟨?_, sec_mul y k₀ js j hjs _ _ _ _ fun k => rel k (p.1 k) (js k) (j k)⟩
    have := gForm_homog k₀ p.2 (eT p.1) (G := fun k => F k (p.1 k) (j k)) (d := fun k => n k (p.1 k))
      fun k => hom k _ _
    rwa [heT] at this
  refine ⟨N + 1, Fintype.card I, fun q => S ((Fintype.equivFin I).symm q), fun q c hc => ?_, fun L _ _ z hz => ?_⟩
  · obtain ⟨h1, h2⟩ := hform ((Fintype.equivFin I).symm q) c
    have h3 := FibreNormDehomRoots.aeval_mem_chartLatNm h1 c hc
    convert h3 using 1
    rw [h2, aeval_hForm, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k₀),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k₀)]
    have e1 : ∏ k ∈ Finset.univ.erase k₀, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * (((N + 1 : ℕ) : ℤ) * a k - 1))) =
        ∏ k ∈ Finset.univ.erase k₀, y ⟨k, c k⟩ := by
      refine Finset.prod_congr rfl fun k hk => ?_
      simp [ha k (Finset.ne_of_mem_erase hk)]
    have e2 : ∏ k ∈ Finset.univ.erase k₀, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * ((1 * (Pi.single k₀ N : K → ℕ) k : ℕ) : ℤ))) = 1 := by
      refine Finset.prod_eq_one fun k hk => ?_
      simp [Pi.single_apply, Finset.ne_of_mem_erase hk]
    rw [e1, e2]
    simp [ha₀]
    ring
  · obtain ⟨i, hi⟩ := hz.1 k₀
    choose T jz hF using fun k => pts k L z hz
    have hzj : ∀ k, z ⟨k, jz k⟩ ≠ 0 := by
      intro k h0
      obtain ⟨j', hj'⟩ := hz.1 k
      have := rel_at_point k₀ k (hom k (T k) (jz k)) (hom k (T k) j') (jz k) j' (rel k _ _ _) hz
      rw [h0, mul_zero] at this
      exact mul_ne_zero (hF k) hj' this
    obtain ⟨h1, h2⟩ := hform (T, i) jz
    have hg : aeval z (gForm k₀ i (eT T) fun k => F k (T k) (jz k)) ≠ 0 := by
      rw [aeval_gForm]
      exact mul_ne_zero (pow_ne_zero _ hi) (Finset.prod_ne_zero_iff.mpr fun k _ => hF k)
    have hh : aeval z (hForm k₀ jz) ≠ 0 := by
      rw [aeval_hForm]
      exact Finset.prod_ne_zero_iff.mpr fun k _ => hzj k
    refine ⟨Fintype.equivFin I (T, i), _ / _, div_ne_zero hg hh, Pi.single k₀ N, hDeg k₀, _, hForm k₀ jz, h1,
      hForm_homog k₀ jz, hdeg, ?_, hh, (div_mul_cancel₀ _ hh).symm⟩
    simpa using h2

theorem ampleQ_of_embeds : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K) (a : K → ℤ), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → a k₀ = 1 → (∀ k, k ≠ k₀ → a k = 0) → Ht.AmpleQ y a := by
  intro X Ω _ _ ξ K _ J _ y k₀ a hT hE ha₀ ha
  classical
  choose l n F hom rel pts using GlobalTheory.T.coord_relations_homogeneous X Ω ξ K J y k₀ hT hE
  exact ampleQ_of_forms y k₀ a ha₀ ha l n F hom rel fun k L _ _ z hz => pts k L z hz

end GlobalTheory.CompanionTheory.Ar.AmpleBlock
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AmpleOfSingleCoordBlockStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_of_single_coord_block : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K) (a : K → ℤ), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → a k₀ = 1 → (∀ k, k ≠ k₀ → a k = 0) → Ht.AmpleQ y a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AmpleBlock.ampleQ_of_embeds | exact GlobalTheory.CompanionTheory.Ar.AmpleBlock.ampleQ_of_embeds | (intros; apply GlobalTheory.CompanionTheory.Ar.AmpleBlock.ampleQ_of_embeds <;> assumption)
end
