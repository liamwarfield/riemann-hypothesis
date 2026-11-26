module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableNormSiegelThetaSeriesTerms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChainRuleAndJacobianCriterion
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinear
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinear
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.HaarAlg

variable {K : Type} [Field K] {κ ι : Type}

theorem intM_add {x y : Matrix κ ι K} (hx : IntM x) (hy : IntM y) : IntM (x + y) :=
  fun k i => (hx k i).add (hy k i)

theorem intM_natCast_smul (n : ℕ) {x : Matrix κ ι K} (hx : IntM x) : IntM ((n : K) • x) := by
  intro k i
  rw [Matrix.smul_apply, smul_eq_mul, ← nsmul_eq_mul]
  exact (hx k i).nsmul n

theorem hasLevel_mul {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (S : ℕ) :
    HasLevel (R * S) φ := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact intM_natCast_smul S (h.1 x hx)
  · rw [Nat.cast_mul, mul_smul]
    exact h.2 x _ (intM_natCast_smul S hy)

theorem exists_common_level {φ ψ : Matrix κ ι K → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ) :
    ∃ R : ℕ, 0 < R ∧ HasLevel R φ ∧ HasLevel R ψ := by
  obtain ⟨R, hR, h1⟩ := hφ
  obtain ⟨S, hS, h2⟩ := hψ
  exact ⟨R * S, Nat.mul_pos hR hS, hasLevel_mul h1 S, mul_comm S R ▸ hasLevel_mul h2 R⟩

theorem hasLevel_map₂ {R : ℕ} {φ ψ : Matrix κ ι K → ℂ} (h1 : HasLevel R φ) (h2 : HasLevel R ψ)
    (f : ℂ → ℂ → ℂ) (hf : f 0 0 = 0) : HasLevel R fun x => f (φ x) (ψ x) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · by_cases a : φ x = 0
    · by_cases b : ψ x = 0
      · exact (hx (by simp only [a, b, hf])).elim
      · exact h2.1 x b
    · exact h1.1 x a
  · simp only [h1.2 x y hy, h2.2 x y hy]

theorem apply_add_of_mem_perSub {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ)
    {p : Matrix κ ι K} (hp : p ∈ perSub K κ ι R) : ∀ x, φ (x + p) = φ x := by
  induction hp using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨y, hy, rfl⟩ := hp
    exact fun x => h.2 x y hy
  | zero => simp
  | add p q _ _ hp hq => intro x; rw [← add_assoc, hq, hp]
  | neg p _ hp => intro x; rw [← hp (x + -p)]; simp

theorem apply_out_mk {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (x : Matrix κ ι K) :
    φ (Quotient.out (QuotientAddGroup.mk x : Matrix κ ι K ⧸ perSub K κ ι R)) = φ x := by
  obtain ⟨p, hp⟩ := QuotientAddGroup.mk_out_eq_mul (perSub K κ ι R) x
  rw [hp]
  exact apply_add_of_mem_perSub h p.2 x

theorem exists_natCast_smul_intM [NumberField K] [Fintype κ] [Fintype ι] (b : Matrix κ ι K) :
    ∃ N : ℕ, 0 < N ∧ IntM ((N : K) • b) := by
  classical
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : κ × ι => b p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, fun k i => ?_⟩
  have h := hy (b k i) (Finset.mem_image.mpr ⟨(k, i), Finset.mem_univ _, rfl⟩)
  rw [Matrix.smul_apply, smul_eq_mul]
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with e | e
  · rw [e, Int.cast_natCast] at h; exact h
  · rw [e, Int.cast_neg, Int.cast_natCast, neg_mul] at h
    simpa using h.neg

theorem hasLevel_translate {R N : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) {b : Matrix κ ι K}
    (hb : IntM ((N : K) • b)) : HasLevel (R * N) fun x => φ (x - b) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · have e : ((R * N : ℕ) : K) • x = (N : K) • ((R : K) • (x - b)) + (R : K) • ((N : K) • b) := by
      rw [Nat.cast_mul]; module
    rw [e]
    exact intM_add (intM_natCast_smul N (h.1 _ hx)) (intM_natCast_smul R hb)
  · show φ _ = φ _
    rw [add_sub_right_comm]
    exact (hasLevel_mul h N).2 _ y hy

theorem finsum_translate {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : HasLevel R φ) (b : Matrix κ ι K) :
    ∑ᶠ q : Matrix κ ι K ⧸ perSub K κ ι R, φ (q.out - b) =
      ∑ᶠ q : Matrix κ ι K ⧸ perSub K κ ι R, φ q.out := by
  rw [← finsum_comp_equiv (Equiv.subRight (QuotientAddGroup.mk b :
    Matrix κ ι K ⧸ perSub K κ ι R)) (f := fun q => φ q.out)]
  refine finsum_congr fun q => ?_
  rw [← apply_out_mk h (q.out - b), QuotientAddGroup.mk_sub, QuotientAddGroup.out_eq']
  rfl

end GlobalTheory.SW.HaarAlg


open GlobalTheory.SW.HaarAlg in
theorem GlobalTheory.SW.isSB_algebra_haar_linear : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (φ ψ : Matrix κ ι K → ℂ), IsSB φ → IsSB ψ → IsSB (φ + ψ) ∧ (∀ c : ℂ, IsSB (c • φ)) ∧ IsSB (φ * ψ) ∧ IsSB (fun x : Matrix κ ι K => conj (φ x)) ∧ haar (φ + ψ) = haar φ + haar ψ ∧ (∀ c : ℂ, haar (c • φ) = c * haar φ) ∧ haar (fun x : Matrix κ ι K => conj (φ x)) = conj (haar φ) ∧ ∀ b : Matrix κ ι K, IsSB (fun x : Matrix κ ι K => φ (x - b)) ∧ haar (fun x : Matrix κ ι K => φ (x - b)) = haar φ := by
  intro K κ ι _ _ _ _ φ ψ hφ hψ
  obtain ⟨R, hR, h1, h2⟩ := exists_common_level hφ hψ
  have hadd : HasLevel R (φ + ψ) := hasLevel_map₂ h1 h2 (fun a b => a + b) (by simp)
  have hsmul : ∀ c : ℂ, HasLevel R (c • φ) := fun c =>
    hasLevel_map₂ h1 h2 (fun a _ => c * a) (by simp)
  have hmul : HasLevel R (φ * ψ) := hasLevel_map₂ h1 h2 (fun a b => a * b) (by simp)
  have hconj : HasLevel R (fun x => conj (φ x)) :=
    hasLevel_map₂ h1 h2 (fun a _ => conj a) (by simp)
  obtain ⟨e1, f1⟩ := GlobalTheory.SW.haar_eq_haarAt K κ ι R φ hR h1
  obtain ⟨e2, f2⟩ := GlobalTheory.SW.haar_eq_haarAt K κ ι R ψ hR h2
  refine ⟨⟨R, hR, hadd⟩, fun c => ⟨R, hR, hsmul c⟩, ⟨R, hR, hmul⟩, ⟨R, hR, hconj⟩, ?_,
    fun c => ?_, ?_, fun b => ?_⟩
  · rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hadd).1, e1, e2]
    unfold haarAt
    rw [← mul_add, ← finsum_add_distrib f1 f2]
    rfl
  · rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR (hsmul c)).1, e1]
    unfold haarAt
    rw [mul_left_comm c]
    congr 1
    exact ((AddMonoidHom.mulLeft c).map_finsum f1).symm
  · rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hconj).1, e1]
    unfold haarAt
    rw [map_mul, map_inv₀, map_pow, map_natCast]
    congr 1
    exact ((starRingEnd ℂ).toAddMonoidHom.map_finsum f1).symm
  · obtain ⟨N, hN, hb⟩ := exists_natCast_smul_intM b
    have hRN := Nat.mul_pos hR hN
    have ht := hasLevel_translate h1 hb
    refine ⟨⟨_, hRN, ht⟩, ?_⟩
    rw [(GlobalTheory.SW.haar_eq_haarAt K κ ι _ _ hRN ht).1, (GlobalTheory.SW.haar_eq_haarAt K κ ι _ _ hRN (hasLevel_mul h1 N)).1]
    unfold haarAt
    rw [finsum_translate (hasLevel_mul h1 N) b]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RationalSchwartzBruhatAlgebraIntegralLinearStatement
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (φ ψ : Matrix κ ι K → ℂ), IsSB φ → IsSB ψ → IsSB (φ + ψ) ∧ (∀ c : ℂ, IsSB (c • φ)) ∧ IsSB (φ * ψ) ∧ IsSB (fun x : Matrix κ ι K => conj (φ x)) ∧ haar (φ + ψ) = haar φ + haar ψ ∧ (∀ c : ℂ, haar (c • φ) = c * haar φ) ∧ haar (fun x : Matrix κ ι K => conj (φ x)) = conj (haar φ) ∧ ∀ b : Matrix κ ι K, IsSB (fun x : Matrix κ ι K => φ (x - b)) ∧ haar (fun x : Matrix κ ι K => φ (x - b)) = haar φ := by
  first | exact @GlobalTheory.SW.isSB_algebra_haar_linear | exact GlobalTheory.SW.isSB_algebra_haar_linear | (intros; apply GlobalTheory.SW.isSB_algebra_haar_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfSiegelThetaSeriesRationalEq
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfSiegelThetaSeriesRationalEq
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW

theorem exists_int_div_of_intM {κ ι : Type} (R S : ℕ) (hR : 0 < R) (hS : 0 < S)
    (x : Matrix κ ι ℚ) (h : IntM ((R : ℚ) • x)) :
    ∃ s : κ × ι → ℤ, (Matrix.of fun k i => (s (k, i) : ℚ) / ((R * S : ℕ) : ℚ)) = x := by
  have h' : ∀ p : κ × ι, ∃ n : ℤ, (n : ℚ) = (R : ℚ) * x p.1 p.2 := by
    intro p
    have := h p.1 p.2
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
    exact ⟨n, by simpa using hn⟩
  choose n hn using h'
  refine ⟨fun p => n p * S, ?_⟩
  ext k i
  have hR' : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  have hS' : (S : ℚ) ≠ 0 := by exact_mod_cast hS.ne'
  simp only [Matrix.of_apply]
  push_cast
  rw [hn (k, i)]
  field_simp

theorem eq_of_thS_eq : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (φ ψ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB ψ → ∀ τ ∈ Siegel ι, (∀ ζ, thS φ τ ζ = thS ψ τ ζ) → φ = ψ := by
  intro κ ι _ _ _ φ ψ hφ hψ τ hτ h
  obtain ⟨R, hR, hRφ, -⟩ := id hφ
  obtain ⟨S, hS, hSψ, -⟩ := id hψ
  have hN : (((R * S : ℕ) : ℚ)) ≠ 0 := by exact_mod_cast (Nat.mul_pos hR hS).ne'
  have hNC : (((R * S : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (Nat.mul_pos hR hS).ne'
  let e : (κ × ι → ℤ) → Matrix κ ι ℚ := fun s =>
    Matrix.of fun k i => (s (k, i) : ℚ) / ((R * S : ℕ) : ℚ)
  have he : Function.Injective e := by
    intro s t hst
    funext p
    have := congrFun (congrFun hst p.1) p.2
    simp only [e, Matrix.of_apply] at this
    have := (div_left_inj' hN).1 this
    exact_mod_cast this
  have hrange : ∀ x, φ x - ψ x ≠ 0 → x ∈ Set.range e := by
    intro x hx
    by_cases h1 : φ x = 0
    · have h2 : ψ x ≠ 0 := by
        intro h2; exact hx (by rw [h1, h2, sub_zero])
      obtain ⟨s, hs⟩ := exists_int_div_of_intM S R hS hR x (hSψ x h2)
      exact ⟨s, by rw [← hs, Nat.mul_comm S R]⟩
    · exact exists_int_div_of_intM R S hR hS x (hRφ x h1)
  let E : (κ → ι → ℂ) → Matrix κ ι ℚ → ℂ := fun ζ x =>
    cexp (π * I * ∑ k, (qv (x k) ⬝ᵥ τ *ᵥ qv (x k) + 2 * (qv (x k) ⬝ᵥ ζ k)))
  have hsφ : ∀ ζ, Summable fun x => φ x * E ζ x := fun ζ =>
    (GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm κ ι φ hφ τ hτ ζ).of_norm
  have hsψ : ∀ ζ, Summable fun x => ψ x * E ζ x := fun ζ =>
    (GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm κ ι ψ hψ τ hτ ζ).of_norm
  have hs : ∀ ζ, Summable fun x => (φ x - ψ x) * E ζ x := fun ζ => by
    simpa only [sub_mul] using (hsφ ζ).sub (hsψ ζ)
  have hz : ∀ ζ, ∑' x, (φ x - ψ x) * E ζ x = 0 := fun ζ => by
    simp only [sub_mul]
    rw [(hsφ ζ).tsum_sub (hsψ ζ)]
    exact sub_eq_zero.2 (h ζ)
  have key := GlobalTheory.coeff_eq_zero_of_fourier_series_eq_zero (κ × ι)
    (fun s => (φ (e s) - ψ (e s)) * E 0 (e s))
    (((hs 0).comp_injective he).norm) (by
      intro y
      have h0 := hz (fun k i => ((R * S : ℕ) : ℂ) * (y (k, i) : ℂ))
      rw [← he.tsum_eq (f := fun x => (φ x - ψ x) * E (fun k i => ((R * S : ℕ) : ℂ) * (y (k, i) : ℂ)) x)
        (by
          intro x hx
          exact hrange x (left_ne_zero_of_mul hx))] at h0
      rw [← h0]
      refine tsum_congr fun s => ?_
      rw [mul_assoc]
      congr 1
      simp only [E]
      rw [← Complex.exp_add]
      congr 1
      have : ∀ k, qv (e s k) ⬝ᵥ (fun i => ((R * S : ℕ) : ℂ) * (y (k, i) : ℂ)) =
          ∑ i, (s (k, i) : ℂ) * (y (k, i) : ℂ) := by
        intro k
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [qv, e, Matrix.of_apply, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
        field_simp
      simp only [this, Pi.zero_apply, dotProduct_zero, mul_zero, add_zero, Finset.sum_add_distrib,
        ← Finset.mul_sum, Fintype.sum_prod_type]
      ring)
  funext x
  by_contra hx
  obtain ⟨s, rfl⟩ := hrange x (sub_ne_zero.2 hx)
  have := key s
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hx (sub_eq_zero.1 h1)
  · exact Complex.exp_ne_zero _ h1

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfSiegelThetaSeriesRationalEqStatement
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_siegelThetaSeriesRational_eq : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (φ ψ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB ψ → ∀ τ ∈ Siegel ι, (∀ ζ, thS φ τ ζ = thS ψ τ ζ) → φ = ψ := by
  first | exact @GlobalTheory.SW.eq_of_thS_eq | exact GlobalTheory.SW.eq_of_thS_eq | (intros; apply GlobalTheory.SW.eq_of_thS_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInnerProductSelfNonnegBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInnerProductSelfNonnegBounds
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.IpPos

open NumberField

variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.exists_of_mem_perSub {R : ℕ} {x : Matrix κ ι K}
    (hx : x ∈ _root_.GlobalTheory.SW.perSub K κ ι R) :
    ∃ y : Matrix κ ι K, _root_.GlobalTheory.SW.IntM y ∧ x = (R : K) • y := by
  obtain ⟨y, rfl⟩ := (_root_.GlobalTheory.SW.HaarLevel.mem_perSub R x).mp hx
  exact ⟨_root_.GlobalTheory.SW.HaarLevel.incl K κ ι y,
    (_root_.GlobalTheory.SW.HaarLevel.intM_iff _).mpr ⟨y, rfl⟩,
    (Nat.cast_smul_eq_nsmul K R _).symm⟩

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.apply_out_mk {R : ℕ} {φ : Matrix κ ι K → ℂ}
    (h : _root_.GlobalTheory.SW.HasLevel R φ) (x : Matrix κ ι K) :
    φ (QuotientAddGroup.mk (s := _root_.GlobalTheory.SW.perSub K κ ι R) x).out = φ x := by
  have hmem := QuotientAddGroup.eq.mp
    (QuotientAddGroup.out_eq' (QuotientAddGroup.mk (s := _root_.GlobalTheory.SW.perSub K κ ι R) x)).symm
  rw [← _root_.GlobalTheory.SW.HaarLevel.periodic h x _ hmem, add_neg_cancel_left]

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.intM_natCast_smul (n : ℕ) {x : Matrix κ ι K}
    (hx : _root_.GlobalTheory.SW.IntM x) : _root_.GlobalTheory.SW.IntM ((n : K) • x) := by
  intro k i
  rw [Matrix.smul_apply, smul_eq_mul]
  exact (isIntegral_natCast n).mul (hx k i)

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
omit [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.hasLevel_mul {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : _root_.GlobalTheory.SW.HasLevel R φ)
    (S : ℕ) : _root_.GlobalTheory.SW.HasLevel (R * S) φ := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact _root_.GlobalTheory.SW.IpPos.intM_natCast_smul S (h.1 x hx)
  · rw [Nat.cast_mul, mul_smul]
    exact h.2 x _ (_root_.GlobalTheory.SW.IpPos.intM_natCast_smul S hy)

def classes (K κ ι : Type) [Field K] (R : ℕ) : Set (Matrix κ ι K ⧸ perSub K κ ι R) :=
  {q | IntM ((R : K) • q.out)}

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.classes_finite_card {R : ℕ} (hR : 0 < R) :
    (_root_.GlobalTheory.SW.IpPos.classes K κ ι R).Finite ∧
      (_root_.GlobalTheory.SW.IpPos.classes K κ ι R).ncard ≤
      (R ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι))) ^ 2 := by
  set L := _root_.GlobalTheory.SW.perSub K κ ι 1
  set H := (_root_.GlobalTheory.SW.perSub K κ ι (1 * (R * R))).addSubgroupOf L
  have hRK : (R : K) ≠ 0 := Nat.cast_ne_zero.mpr hR.ne'
  have hidx : H.index = (R ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι))) ^ 2 := by
    show (_root_.GlobalTheory.SW.perSub K κ ι (1 * (R * R))).relIndex L = _
    rw [_root_.GlobalTheory.SW.HaarLevel.relIndex_perSub 1 (R * R) one_pos, mul_pow, ← sq]
  let g : L →+ Matrix κ ι K ⧸ _root_.GlobalTheory.SW.perSub K κ ι R :=
    (QuotientAddGroup.mk' _).comp
      ((DistribSMul.toAddMonoidHom (Matrix κ ι K) ((R : K)⁻¹)).comp L.subtype)
  have hker : H ≤ g.ker := by
    intro z hz
    rw [AddMonoidHom.mem_ker]
    obtain ⟨y, hy, hzy⟩ :=
      _root_.GlobalTheory.SW.IpPos.exists_of_mem_perSub (AddSubgroup.mem_addSubgroupOf.mp hz)
    simp only [g, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
      DistribSMul.toAddMonoidHom_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, hzy, smul_smul]
    rw [show ((R : K))⁻¹ * ((1 * (R * R) : ℕ) : K) = R by push_cast; field_simp]
    exact AddSubgroup.subset_closure ⟨y, hy, rfl⟩
  let F := QuotientAddGroup.lift H g hker
  have hsub : _root_.GlobalTheory.SW.IpPos.classes K κ ι R ⊆ Set.range F := by
    intro q hq
    have hL : (R : K) • q.out ∈ L :=
      AddSubgroup.subset_closure ⟨_, hq, by rw [Nat.cast_one, one_smul]⟩
    refine ⟨QuotientAddGroup.mk ⟨_, hL⟩, ?_⟩
    simp only [F, QuotientAddGroup.lift_mk, g, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
      DistribSMul.toAddMonoidHom_apply, QuotientAddGroup.mk'_apply, smul_smul,
      inv_mul_cancel₀ hRK, one_smul]
    exact QuotientAddGroup.out_eq' q
  have hfin : Finite (L ⧸ H) := Nat.finite_of_card_ne_zero (by
    rw [← AddSubgroup.index, hidx]; positivity)
  refine ⟨(Set.finite_range F).subset hsub, ?_⟩
  calc (_root_.GlobalTheory.SW.IpPos.classes K κ ι R).ncard ≤ (Set.range F).ncard :=
        Set.ncard_le_ncard hsub (Set.finite_range F)
    _ = Nat.card (Set.range F) := (Nat.card_coe_set_eq _).symm
    _ ≤ Nat.card (L ⧸ H) := Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    _ = _ := hidx

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
theorem _root_.GlobalTheory.SW.IpPos.ip_eq_sum {R : ℕ} (hR : 0 < R) {φ ψ : Matrix κ ι K → ℂ}
    (hφ : _root_.GlobalTheory.SW.HasLevel R φ) (hψ : _root_.GlobalTheory.SW.HasLevel R ψ) :
    _root_.GlobalTheory.SW.ip φ ψ =
      ((R : ℂ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)))⁻¹ *
      ∑ q ∈ (_root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hR).1.toFinset,
        φ q.out * conj (ψ q.out) := by
  have hlev : _root_.GlobalTheory.SW.HasLevel R (fun x => φ x * conj (ψ x)) := by
    refine ⟨fun x hx => hφ.1 x (left_ne_zero_of_mul hx), fun x y hy => ?_⟩
    simp only [hφ.2 x y hy, hψ.2 x y hy]
  unfold _root_.GlobalTheory.SW.ip
  rw [(_root_.GlobalTheory.SW.haar_eq_haarAt K κ ι R _ hR hlev).1]
  unfold _root_.GlobalTheory.SW.haarAt
  congr 1
  refine finsum_eq_sum_of_support_subset _ ?_
  intro q hq
  rw [Set.Finite.coe_toFinset]
  exact hφ.1 _ (left_ne_zero_of_mul hq)

end GlobalTheory.SW.IpPos

open Matrix Complex in
open scoped ComplexConjugate Real in
open NumberField in
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] in
private lemma schwartzBruhatInnerProduct_self_eq_lemma {R : ℕ} (hR : 0 < R) {φ : Matrix κ ι K → ℂ}
    (hφ : _root_.GlobalTheory.SW.HasLevel R φ) :
    _root_.GlobalTheory.SW.ip φ φ =
      (((R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)))⁻¹ *
      ∑ q ∈ (_root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hR).1.toFinset,
        ‖φ q.out‖ ^ 2 : ℝ) := by
  rw [_root_.GlobalTheory.SW.IpPos.ip_eq_sum hR hφ hφ]
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl


open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.SW.ip_self_nonneg_and_bounds : ∀ (K κ ι : Type) [Field K] [NumberField K]
    [Fintype κ] [Fintype ι] (R : ℕ) (φ : Matrix κ ι K → ℂ), 0 < R → _root_.GlobalTheory.SW.HasLevel R φ →
    (_root_.GlobalTheory.SW.ip φ φ).im = 0 ∧ 0 ≤ (_root_.GlobalTheory.SW.ip φ φ).re ∧
    (∀ x, ‖φ x‖ ^ 2 ≤ (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) *
      (_root_.GlobalTheory.SW.ip φ φ).re) ∧
    (∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → (_root_.GlobalTheory.SW.ip φ φ).re ≤
      (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) * B ^ 2) ∧
    (∃ B : ℝ, ∀ x, ‖φ x‖ ≤ B) ∧ ∀ ψ, _root_.GlobalTheory.SW.IsSB ψ →
      ‖_root_.GlobalTheory.SW.ip φ ψ‖ ^ 2 ≤
        (_root_.GlobalTheory.SW.ip φ φ).re * (_root_.GlobalTheory.SW.ip ψ ψ).re := by
  intro K κ ι _ _ _ _ R φ hR hφ
  set N := Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)
  have hfc := _root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hR
  set s := hfc.1.toFinset with hs
  set Sφ := ∑ q ∈ s, ‖φ q.out‖ ^ 2 with hSφ
  have hc : (0 : ℝ) < (R : ℝ) ^ N := by positivity
  have hip : _root_.GlobalTheory.SW.ip φ φ = (((R : ℝ) ^ N)⁻¹ * Sφ : ℝ) :=
    schwartzBruhatInnerProduct_self_eq_lemma hR hφ
  have hre : (_root_.GlobalTheory.SW.ip φ φ).re = ((R : ℝ) ^ N)⁻¹ * Sφ := by
    rw [hip, Complex.ofReal_re]
  have hS0 : 0 ≤ Sφ := Finset.sum_nonneg fun _ _ => by positivity
  have hpt : ∀ x, ‖φ x‖ ^ 2 ≤ (R : ℝ) ^ N * (_root_.GlobalTheory.SW.ip φ φ).re := by
    intro x
    rw [hre, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    by_cases hx : φ x = 0
    · simpa [hx] using hS0
    · have hq : (QuotientAddGroup.mk x : Matrix κ ι K ⧸ _root_.GlobalTheory.SW.perSub K κ ι R) ∈ s := by
        rw [hs, Set.Finite.mem_toFinset]
        show _root_.GlobalTheory.SW.IntM _
        exact hφ.1 _ (by rwa [_root_.GlobalTheory.SW.IpPos.apply_out_mk hφ])
      have h := Finset.single_le_sum (f := fun q => ‖φ q.out‖ ^ 2) (fun _ _ => by positivity) hq
      simpa only [_root_.GlobalTheory.SW.IpPos.apply_out_mk hφ] using h
  refine ⟨by rw [hip, Complex.ofReal_im], by rw [hre]; positivity, hpt, fun B hB => ?_,
    ⟨√((R : ℝ) ^ N * (_root_.GlobalTheory.SW.ip φ φ).re), fun x => by
      simpa using Real.abs_le_sqrt (hpt x)⟩, fun ψ hψ => ?_⟩
  · have h1 : Sφ ≤ s.card • B ^ 2 :=
      Finset.sum_le_card_nsmul _ _ _ (fun q _ => pow_le_pow_left₀ (norm_nonneg _) (hB _) 2)
    have hcard : (s.card : ℝ) ≤ ((R : ℝ) ^ N) ^ 2 := by
      rw [hs, ← Set.ncard_eq_toFinset_card _ hfc.1]
      exact_mod_cast hfc.2
    rw [nsmul_eq_mul] at h1
    rw [hre]
    calc ((R : ℝ) ^ N)⁻¹ * Sφ ≤ ((R : ℝ) ^ N)⁻¹ * (((R : ℝ) ^ N) ^ 2 * B ^ 2) := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_right hcard (sq_nonneg B))
      _ = (R : ℝ) ^ N * B ^ 2 := by field_simp
  · obtain ⟨S, hS, hψS⟩ := hψ
    have hRS : 0 < R * S := Nat.mul_pos hR hS
    have hφ' := _root_.GlobalTheory.SW.IpPos.hasLevel_mul hφ S
    have hψ' : _root_.GlobalTheory.SW.HasLevel (R * S) ψ := by
      rw [mul_comm]; exact _root_.GlobalTheory.SW.IpPos.hasLevel_mul hψS R
    rw [_root_.GlobalTheory.SW.IpPos.ip_eq_sum hRS hφ' hψ',
      schwartzBruhatInnerProduct_self_eq_lemma hRS hφ', schwartzBruhatInnerProduct_self_eq_lemma hRS hψ',
      Complex.ofReal_re, Complex.ofReal_re, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    set t := (_root_.GlobalTheory.SW.IpPos.classes_finite_card (K := K) (κ := κ) (ι := ι) hRS).1.toFinset
    set d : ℝ := ((R * S : ℕ) : ℝ) ^ N
    have hcs : ‖∑ q ∈ t, φ q.out * conj (ψ q.out)‖ ^ 2 ≤
        (∑ q ∈ t, ‖φ q.out‖ ^ 2) * ∑ q ∈ t, ‖ψ q.out‖ ^ 2 := by
      calc _ ≤ (∑ q ∈ t, ‖φ q.out‖ * ‖ψ q.out‖) ^ 2 := by
            gcongr
            refine (norm_sum_le _ _).trans (le_of_eq ?_)
            simp [Complex.norm_conj]
        _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    calc (d⁻¹ * ‖∑ q ∈ t, φ q.out * conj (ψ q.out)‖) ^ 2
        = d⁻¹ * d⁻¹ * ‖∑ q ∈ t, φ q.out * conj (ψ q.out)‖ ^ 2 := by ring
      _ ≤ d⁻¹ * d⁻¹ * ((∑ q ∈ t, ‖φ q.out‖ ^ 2) * ∑ q ∈ t, ‖ψ q.out‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = _ := by ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatInnerProductSelfNonnegBoundsStatement
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhatInnerProduct_self_nonneg_bounds : ∀ (K κ ι : Type) [Field K] [NumberField K] [Fintype κ] [Fintype ι] (R : ℕ) (φ : Matrix κ ι K → ℂ), 0 < R → HasLevel R φ → (ip φ φ).im = 0 ∧ 0 ≤ (ip φ φ).re ∧ (∀ x, ‖φ x‖ ^ 2 ≤ (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) * (ip φ φ).re) ∧ (∀ B : ℝ, (∀ x, ‖φ x‖ ≤ B) → (ip φ φ).re ≤ (R : ℝ) ^ (Module.finrank ℚ K * (Fintype.card κ * Fintype.card ι)) * B ^ 2) ∧ (∃ B : ℝ, ∀ x, ‖φ x‖ ≤ B) ∧ ∀ ψ, IsSB ψ → ‖ip φ ψ‖ ^ 2 ≤ (ip φ φ).re * (ip ψ ψ).re := by
  first | exact @GlobalTheory.SW.ip_self_nonneg_and_bounds | exact GlobalTheory.SW.ip_self_nonneg_and_bounds | (intros; apply GlobalTheory.SW.ip_self_nonneg_and_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CanonicalThetaExponentSymplecticInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CanonicalThetaExponentSymplecticInvariant
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW

theorem isUnit_det_im_of_mem_siegel {ι : Type} [Fintype ι] [DecidableEq ι] {τ : Matrix ι ι ℂ}
    (hτ : τ ∈ Siegel ι) : IsUnit (τ.map fun z => (z.im : ℂ)).det := by
  have h : (τ.map fun z => (z.im : ℂ)) = Complex.ofRealHom.mapMatrix (τ.map Complex.im) := by
    ext i j; simp
  rw [h, ← RingHom.map_det]
  exact (hτ.2.det_pos.ne'.isUnit).map _

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_add' {α β : Type} (M N : Matrix α β ℚ) :
    _root_.GlobalTheory.SW.qm (M + N) = _root_.GlobalTheory.SW.qm M + _root_.GlobalTheory.SW.qm N := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_neg' {α β : Type} (M : Matrix α β ℚ) :
    _root_.GlobalTheory.SW.qm (-M) = -_root_.GlobalTheory.SW.qm M := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_mul_siegel_theta_transformation {α β γ : Type} [Fintype β] (M : Matrix α β ℚ) (N : Matrix β γ ℚ) :
    _root_.GlobalTheory.SW.qm (M * N) = _root_.GlobalTheory.SW.qm M * _root_.GlobalTheory.SW.qm N := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm, Matrix.mul_apply]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_transpose' {α β : Type} (M : Matrix α β ℚ) :
    _root_.GlobalTheory.SW.qm Mᵀ = (_root_.GlobalTheory.SW.qm M)ᵀ := rfl

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_zero' {α β : Type} : _root_.GlobalTheory.SW.qm (0 : Matrix α β ℚ) = 0 := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_one' : _root_.GlobalTheory.SW.qm (1 : Matrix ι ι ℚ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [_root_.GlobalTheory.SW.qm, Matrix.one_apply, h]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma sub_conjTranspose_of_isSymm (τ : Matrix ι ι ℂ) (hτ : τ.IsSymm) :
    τ - τᴴ = (2 * I) • τ.map fun z => (z.im : ℂ) := by
  ext i j
  have h := hτ.apply i j
  simp only [Matrix.sub_apply, conjTranspose_apply, Matrix.smul_apply, map_apply, smul_eq_mul, h]
  rw [show star (τ i j) = conj (τ i j) from rfl, Complex.sub_conj]
  push_cast
  ring

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma qm_conjTranspose_eq_transpose {α β : Type} (M : Matrix α β ℚ) :
    (_root_.GlobalTheory.SW.qm M)ᴴ = (_root_.GlobalTheory.SW.qm M)ᵀ := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm, conjTranspose_apply]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma re_star_dotProduct_ofReal_mulVec (Y : Matrix ι ι ℝ) (v : ι → ℂ) :
    (star v ⬝ᵥ (Y.map (fun t => (t : ℂ)) *ᵥ v)).re =
      (fun i => (v i).re) ⬝ᵥ (Y *ᵥ fun i => (v i).re) + (fun i => (v i).im) ⬝ᵥ (Y *ᵥ fun i => (v i).im) := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Complex.re_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_re, Complex.mul_im]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
private lemma dotProduct_transpose_mulVec_self (N : Matrix ι ι ℂ) (ζ : ι → ℂ) :
    ζ ⬝ᵥ (Nᵀ *ᵥ ζ) = ζ ⬝ᵥ (N *ᵥ ζ) := by
  rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]


open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.SW.canon_exponent_invariant : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∀ τ ∈ _root_.GlobalTheory.SW.Siegel ι, ∀ ζ : ι → ℂ, (ζ ᵥ* (_root_.GlobalTheory.SW.spDen σ τ)⁻¹) ⬝ᵥ ((_root_.GlobalTheory.SW.spAct σ τ).map fun z => (z.im : ℂ))⁻¹ *ᵥ (ζ ᵥ* (_root_.GlobalTheory.SW.spDen σ τ)⁻¹) + 2 * I * (ζ ⬝ᵥ ((_root_.GlobalTheory.SW.spDen σ τ)⁻¹ * _root_.GlobalTheory.SW.qm σ.toBlocks₂₁) *ᵥ ζ) = ζ ⬝ᵥ (τ.map fun z => (z.im : ℂ))⁻¹ *ᵥ ζ := by
  intro ι _ _ σ hσ τ hτ ζ
  obtain ⟨hsym, hpos⟩ := hτ
  have h2 := SymplecticGroup.mem_iff'.mp hσ
  rw [← fromBlocks_toBlocks σ] at h2
  simp [Matrix.J, fromBlocks_transpose, fromBlocks_multiply] at h2
  obtain ⟨r1, r2, r3, r4⟩ := h2
  replace r1 := congrArg _root_.GlobalTheory.SW.qm r1
  replace r2 := congrArg _root_.GlobalTheory.SW.qm r2
  replace r3 := congrArg _root_.GlobalTheory.SW.qm r3
  replace r4 := congrArg _root_.GlobalTheory.SW.qm r4
  simp only [qm_add', qm_neg', qm_mul_siegel_theta_transformation, qm_transpose',
    qm_zero', qm_one'] at r1 r2 r3 r4
  set A := _root_.GlobalTheory.SW.qm σ.toBlocks₁₁ with hA
  set B := _root_.GlobalTheory.SW.qm σ.toBlocks₁₂ with hB
  set C := _root_.GlobalTheory.SW.qm σ.toBlocks₂₁ with hC
  set D := _root_.GlobalTheory.SW.qm σ.toBlocks₂₂ with hD
  set J := _root_.GlobalTheory.SW.spDen σ τ with hJdef
  have hJ : J = C * τ + D := rfl
  set M := A * τ + B with hM
  have hact : _root_.GlobalTheory.SW.spAct σ τ = M * J⁻¹ := rfl
  set Y := τ.map fun z => (z.im : ℂ) with hYdef
  have hY : τ - τᴴ = (2 * I) • Y := sub_conjTranspose_of_isSymm τ hsym
  have hτt : τᵀ = τ := hsym
  have hCh : Cᴴ = Cᵀ := qm_conjTranspose_eq_transpose _
  have hDh : Dᴴ = Dᵀ := qm_conjTranspose_eq_transpose _
  have hAh : Aᴴ = Aᵀ := qm_conjTranspose_eq_transpose _
  have hBh : Bᴴ = Bᵀ := qm_conjTranspose_eq_transpose _
  have hI1 : Jᴴ * M - Mᴴ * J = τ - τᴴ := by
    rw [hJ, hM, conjTranspose_add, conjTranspose_add, conjTranspose_mul, conjTranspose_mul, hCh, hDh, hAh, hBh]
    have hE : (τᴴ * Cᵀ + Dᵀ) * (A * τ + B) - (τᴴ * Aᵀ + Bᵀ) * (C * τ + D) =
        τᴴ * (Cᵀ * A + -(Aᵀ * C)) * τ + τᴴ * (Cᵀ * B + -(Aᵀ * D)) + (Dᵀ * A + -(Bᵀ * C)) * τ +
          (Dᵀ * B + -(Bᵀ * D)) := by noncomm_ring
    rw [hE, r1, r2, r3, r4]
    noncomm_ring
  have hI2 : Mᵀ * J = Jᵀ * M := by
    rw [hJ, hM, transpose_add, transpose_add, transpose_mul, transpose_mul, hτt]
    have hE : (τ * Aᵀ + Bᵀ) * (C * τ + D) - (τ * Cᵀ + Dᵀ) * (A * τ + B) =
        -(τ * (Cᵀ * A + -(Aᵀ * C)) * τ) - τ * (Cᵀ * B + -(Aᵀ * D)) - (Dᵀ * A + -(Bᵀ * C)) * τ -
          (Dᵀ * B + -(Bᵀ * D)) := by noncomm_ring
    rw [r1, r2, r3, r4] at hE
    rw [← sub_eq_zero, hE]
    noncomm_ring
  have hYr : Y = (τ.map Complex.im).map (fun t => (t : ℂ)) := rfl
  have hdetY : Y.det ≠ 0 := by
    have : Y.det = ((τ.map Complex.im).det : ℂ) := by
      rw [hYr]
      exact (RingHom.map_det Complex.ofRealHom _).symm
    rw [this, Complex.ofReal_ne_zero]
    exact hpos.det_pos.ne'
  have h2I : (2 * I : ℂ) ≠ 0 := by simp
  have hdetJ : J.det ≠ 0 := by
    intro hdet
    obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have h0 : star v ⬝ᵥ ((Jᴴ * M - Mᴴ * J) *ᵥ v) = 0 := by
      rw [sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec, hJv, mulVec_zero,
        dotProduct_zero, dotProduct_mulVec, ← star_mulVec, hJv, star_zero, zero_dotProduct, sub_zero]
    rw [hI1, hY, smul_mulVec, dotProduct_smul, smul_eq_mul, mul_eq_zero] at h0
    have h1 := congrArg Complex.re (h0.resolve_left h2I)
    rw [hYr, re_star_dotProduct_ofReal_mulVec, Complex.zero_re] at h1
    have hna := hpos.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).re)
    have hnb := hpos.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).im)
    simp only [star_trivial] at hna hnb
    have ha : (fun i => (v i).re) = 0 := by
      by_contra h
      have := hpos.dotProduct_mulVec_pos h
      simp only [star_trivial] at this
      linarith
    have hb : (fun i => (v i).im) = 0 := by
      by_contra h
      have := hpos.dotProduct_mulVec_pos h
      simp only [star_trivial] at this
      linarith
    apply hv
    funext i
    apply Complex.ext
    · simpa using congrFun ha i
    · simpa using congrFun hb i
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.mpr hdetJ
  have hYu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hdetY
  have hJJ : J * J⁻¹ = 1 := mul_nonsing_inv J hJu
  have hJJ' : J⁻¹ * J = 1 := nonsing_inv_mul J hJu
  have hYY : Y⁻¹ * Y = 1 := nonsing_inv_mul Y hYu
  have hτ'sym : (M * J⁻¹).IsSymm := by
    have hJtu : IsUnit Jᵀ.det := by rwa [det_transpose]
    unfold Matrix.IsSymm
    rw [transpose_mul, transpose_nonsing_inv]
    calc (Jᵀ)⁻¹ * Mᵀ = (Jᵀ)⁻¹ * (Mᵀ * J) * J⁻¹ := by simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = M * J⁻¹ := by rw [hI2, ← Matrix.mul_assoc (Jᵀ)⁻¹, nonsing_inv_mul _ hJtu, Matrix.one_mul]
  set Y' := (_root_.GlobalTheory.SW.spAct σ τ).map fun z => (z.im : ℂ) with hY'def
  have hY' : (2 * I) • Y' = M * J⁻¹ - (M * J⁻¹)ᴴ := by
    rw [hY'def, hact]
    exact (sub_conjTranspose_of_isSymm _ hτ'sym).symm
  have hkey : Jᴴ * Y' * J = Y := by
    apply smul_right_injective _ h2I
    calc (2 * I) • (Jᴴ * Y' * J) = Jᴴ * ((2 * I) • Y') * J := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = Jᴴ * (M * J⁻¹ - (M * J⁻¹)ᴴ) * J := by rw [hY']
      _ = Jᴴ * M - Mᴴ * J := by
        rw [conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul]
        congr 1
        · simp only [Matrix.mul_assoc, hJJ', Matrix.mul_one]
        · rw [← Matrix.mul_assoc Jᴴ, ← conjTranspose_mul, hJJ', conjTranspose_one, Matrix.one_mul]
      _ = (2 * I) • Y := by rw [hI1, hY]
  have hY'inv : Y'⁻¹ = J * Y⁻¹ * Jᴴ := by
    apply Matrix.inv_eq_left_inv
    calc J * Y⁻¹ * Jᴴ * Y' = J * Y⁻¹ * (Jᴴ * Y' * J) * J⁻¹ := by
          simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = 1 := by rw [hkey, Matrix.mul_assoc J, hYY, Matrix.mul_one, hJJ]
  have hJh : Jᴴ = Jᵀ - (2 * I) • (Y * Cᵀ) := by
    have hτh : τᴴ = τ - (2 * I) • Y := by rw [← hY]; abel
    rw [hJ, conjTranspose_add, conjTranspose_mul, transpose_add, transpose_mul, hCh, hDh, hτt, hτh,
      Matrix.sub_mul, Matrix.smul_mul]
    abel
  have hJt : Jᵀ * (J⁻¹)ᵀ = 1 := by rw [← transpose_mul, hJJ', transpose_one]
  have hmat : J⁻¹ * (J * Y⁻¹ * Jᴴ) * (J⁻¹)ᵀ = Y⁻¹ - (2 * I) • (J⁻¹ * C)ᵀ := by
    rw [hJh, transpose_mul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hJJ',
      Matrix.one_mul]
    rw [Matrix.mul_assoc Y⁻¹ Jᵀ, hJt, Matrix.mul_one, hYY, Matrix.one_mul]
  rw [hY'inv, ← dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, mulVec_mulVec, hmat, sub_mulVec,
    dotProduct_sub, smul_mulVec, dotProduct_smul, dotProduct_transpose_mulVec_self, smul_eq_mul]
  ring

end GlobalTheory.SW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CanonicalThetaExponentSymplecticInvariantStatement
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalThetaExponent_symplectic_invariant : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∀ τ ∈ Siegel ι, ∀ ζ : ι → ℂ, (ζ ᵥ* (spDen σ τ)⁻¹) ⬝ᵥ ((spAct σ τ).map fun z => (z.im : ℂ))⁻¹ *ᵥ (ζ ᵥ* (spDen σ τ)⁻¹) + 2 * I * (ζ ⬝ᵥ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁) *ᵥ ζ) = ζ ⬝ᵥ (τ.map fun z => (z.im : ℂ))⁻¹ *ᵥ ζ := by
  first | exact @GlobalTheory.SW.canon_exponent_invariant | exact GlobalTheory.SW.canon_exponent_invariant | (intros; apply GlobalTheory.SW.canon_exponent_invariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ComplexPhaseCalculusRootOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ComplexPhaseCalculusRootOfUnity
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase.Calc

theorem ph_mul {a b : ℂ} (ha : Ph a) (hb : Ph b) : Ph (a * b) := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
  rw [norm_mul, Complex.ofReal_mul, mul_pow, mul_pow, pow_mul a, ha, ← pow_mul, mul_comm m n,
    pow_mul b, hb, ← pow_mul]

theorem ph_inv {a : ℂ} (ha : Ph a) : Ph a⁻¹ := by
  obtain ⟨m, hm, ha⟩ := ha
  refine ⟨m, hm, ?_⟩
  rw [inv_pow, ha, norm_inv, Complex.ofReal_inv, inv_pow]

theorem isMu_of_ph {a : ℂ} (ha : Ph a) (h : ‖a‖ = 1) : IsMu a := by
  obtain ⟨m, hm, ha⟩ := ha
  exact ⟨m, hm, by rw [ha, h]; simp⟩

theorem ph_cancel {a b : ℂ} (hb0 : b ≠ 0) (hb : Ph b) (hab : Ph (a * b)) : Ph a := by
  have h := ph_mul hab (ph_inv hb)
  rwa [mul_assoc, mul_inv_cancel₀ hb0, mul_one] at h


open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.Phase.Calc.calculus : (∀ a b : ℂ, _root_.GlobalTheory.Phase.Ph a → _root_.GlobalTheory.Phase.Ph b → _root_.GlobalTheory.Phase.Ph (a * b)) ∧ (∀ a : ℂ, _root_.GlobalTheory.Phase.Ph a → _root_.GlobalTheory.Phase.Ph (conj a) ∧ _root_.GlobalTheory.Phase.Ph a⁻¹) ∧
    (∀ t : ℝ, _root_.GlobalTheory.Phase.Ph (t : ℂ)) ∧ (∀ a : ℂ, _root_.GlobalTheory.Phase.IsMu a → _root_.GlobalTheory.Phase.Ph a ∧ ‖a‖ = 1) ∧ (∀ a : ℂ, _root_.GlobalTheory.Phase.Ph a → ‖a‖ = 1 → _root_.GlobalTheory.Phase.IsMu a) ∧
    (∀ a b : ℂ, _root_.GlobalTheory.Phase.IsMu a → _root_.GlobalTheory.Phase.IsMu b → _root_.GlobalTheory.Phase.IsMu (a * b) ∧ _root_.GlobalTheory.Phase.IsMu a⁻¹ ∧ _root_.GlobalTheory.Phase.IsMu (conj a)) ∧
    (∀ (a : ℂ) (k : ℕ), 0 < k → (_root_.GlobalTheory.Phase.IsMu (a ^ k) → _root_.GlobalTheory.Phase.IsMu a) ∧ (_root_.GlobalTheory.Phase.Ph (a ^ k) → _root_.GlobalTheory.Phase.Ph a)) ∧
    (∀ q : ℚ, _root_.GlobalTheory.Phase.IsMu (cexp (π * I * (q : ℂ)))) ∧ ∀ a b : ℂ, b ≠ 0 → _root_.GlobalTheory.Phase.Ph b → _root_.GlobalTheory.Phase.Ph (a * b) → _root_.GlobalTheory.Phase.Ph a := by
  refine ⟨fun a b ha hb => ha.mul hb, fun a ha => ⟨?_, ha.inv⟩, fun t => ?_, fun a ha => ?_,
    fun a ha h1 => ?_, fun a b ha hb => ⟨?_, ?_, ?_⟩, fun a k hk => ⟨?_, ?_⟩, fun q => ?_,
    fun a b hb0 hb hab => ?_⟩
  · obtain ⟨m, hm, h⟩ := ha
    refine ⟨m, hm, ?_⟩
    rw [← map_pow, h, Complex.norm_conj, map_pow, Complex.conj_ofReal]
  · refine ⟨2, two_pos, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, ← ofReal_pow, ← ofReal_pow, sq_abs]
  · obtain ⟨m, hm, h⟩ := ha
    have hn : ‖a‖ = 1 := by
      have h' : ‖a‖ ^ m = 1 := by rw [← norm_pow, h, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) hm.ne').1 h'
    exact ⟨⟨m, hm, by rw [h, hn, ofReal_one, one_pow]⟩, hn⟩
  · obtain ⟨m, hm, h⟩ := ha
    exact ⟨m, hm, by rw [h, h1, ofReal_one, one_pow]⟩
  · obtain ⟨m, hm, h⟩ := ha
    obtain ⟨n, hn, h'⟩ := hb
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    rw [mul_pow, pow_mul, h, pow_mul', h', one_pow, one_pow, one_mul]
  · obtain ⟨m, hm, h⟩ := ha
    exact ⟨m, hm, by rw [inv_pow, h, inv_one]⟩
  · obtain ⟨m, hm, h⟩ := ha
    exact ⟨m, hm, by rw [← map_pow, h, map_one]⟩
  · rintro ⟨m, hm, h⟩
    exact ⟨k * m, Nat.mul_pos hk hm, by rw [pow_mul, h]⟩
  · rintro ⟨m, hm, h⟩
    refine ⟨k * m, Nat.mul_pos hk hm, ?_⟩
    rw [pow_mul, h, norm_pow, ofReal_pow, ← pow_mul]
  · refine ⟨2 * q.den, by positivity, ?_⟩
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨q.num, ?_⟩
    have hq : (q : ℂ) = q.num / q.den := by exact_mod_cast (Rat.num_div_den q).symm
    have hd : (q.den : ℂ) ≠ 0 := by exact_mod_cast q.den_nz
    rw [hq]
    field_simp
    push_cast
    ring
  · have := hab.mul hb.inv
    rwa [mul_inv_cancel_right₀ hb0] at this

end GlobalTheory.Phase.Calc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ComplexPhaseCalculusRootOfUnityStatement
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_phase_calculus_rootOfUnity : (∀ a b : ℂ, Ph a → Ph b → Ph (a * b)) ∧ (∀ a : ℂ, Ph a → Ph (conj a) ∧ Ph a⁻¹) ∧ (∀ t : ℝ, Ph (t : ℂ)) ∧ (∀ a : ℂ, IsMu a → Ph a ∧ ‖a‖ = 1) ∧ (∀ a : ℂ, Ph a → ‖a‖ = 1 → IsMu a) ∧ (∀ a b : ℂ, IsMu a → IsMu b → IsMu (a * b) ∧ IsMu a⁻¹ ∧ IsMu (conj a)) ∧ (∀ (a : ℂ) (k : ℕ), 0 < k → (IsMu (a ^ k) → IsMu a) ∧ (Ph (a ^ k) → Ph a)) ∧ (∀ q : ℚ, IsMu (cexp (π * I * (q : ℂ)))) ∧ ∀ a b : ℂ, b ≠ 0 → Ph b → Ph (a * b) → Ph a := by
  first | exact @GlobalTheory.Phase.Calc.calculus | exact GlobalTheory.Phase.Calc.calculus | (intros; apply GlobalTheory.Phase.Calc.calculus <;> assumption)
end
end
