module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAbsoluteValueCompleteSpaceOfDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAbsoluteValueCompleteSpaceOfDvr
open scoped NNReal TensorProduct

namespace GlobalTheory.KLC

open IsDedekindDomain

theorem completeSpace_withAbs_of_unitBall (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field K]
    [Algebra R K] [IsFractionRing R K] (f : AbsoluteValue K ℝ)
    (h : ∀ x : K, f x ≤ 1 ↔ x ∈ Set.range (algebraMap R K)) :
    CompleteSpace (WithAbs f) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hinjK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  let em : R →+* WithAbs f := (WithAbs.equiv f).symm.toRingHom.comp (algebraMap R K)
  have hnorm : ∀ x : R, ‖em x‖ = f (algebraMap R K x) := fun x => rfl
  have hinj : Function.Injective em := (WithAbs.equiv f).symm.injective.comp hinjK
  have hem0 : em π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ.ne_zero
  have hpos : 0 < ‖em π‖ := norm_pos_iff.2 hem0
  have hle : ∀ x, ‖em x‖ ≤ 1 := fun x => (h _).2 ⟨x, rfl⟩
  have key : ∀ (n : ℕ) (x : R), x ∈ IsLocalRing.maximalIdeal R ^ n ↔ ‖em x‖ ≤ ‖em π‖ ^ n := by
    intro n x
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩
      rw [map_mul, map_pow, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (hle y)
    · intro hx
      rw [hnorm, hnorm] at hx
      have hπK : algebraMap R K π ≠ 0 := (map_ne_zero_iff _ hinjK).2 hπ.ne_zero
      obtain ⟨y, hy⟩ := (h (algebraMap R K x / algebraMap R K π ^ n)).1 (by
        rw [map_div₀, map_pow]
        exact div_le_one_of_le₀ hx (by positivity))
      refine ⟨y, hinjK ?_⟩
      rw [map_mul, map_pow, hy, mul_div_cancel₀ _ (pow_ne_zero _ hπK)]
  have hlt : ‖em π‖ < 1 := by
    by_contra hge
    have : (1 : R) ∈ IsLocalRing.maximalIdeal R ^ 1 := (key 1 1).2 (by simpa using hge)
    rw [pow_one] at this
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)
  refine Metric.complete_of_convergent_controlled_sequences (fun n => ‖em π‖ ^ n)
    (fun n => by positivity) ?_
  intro u hu
  have hv : ∀ n, ∃ v : R, em v = u n - u 0 := by
    intro n
    obtain ⟨v, hv⟩ := (h ((u n - u 0).ofAbs)).1 (by
      have := hu 0 n 0 (Nat.zero_le _) le_rfl
      rw [dist_eq_norm, pow_zero, WithAbs.norm_eq_apply_ofAbs] at this
      exact this.le)
    refine ⟨v, ?_⟩
    show WithAbs.toAbs f (algebraMap R K v) = _
    rw [hv, WithAbs.toAbs_ofAbs]
  choose v hv using hv
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := IsLocalRing.maximalIdeal R) (M := R) inferInstance
    (f := v) (by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, key, map_sub, hv, hv,
        sub_sub_sub_cancel_right]
      have := hu m m n le_rfl hmn
      rw [dist_eq_norm] at this
      exact this.le)
  refine ⟨em L + u 0, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hpos.le hlt)
  have := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, key, map_sub, hv] at this
  rw [dist_eq_norm]
  have e : u n - (em L + u 0) = u n - u 0 - em L := by abel
  rw [e]
  exact this

theorem exists_absoluteValue_completeSpace_of_isDiscreteValuationRing :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field K] [Algebra R K]
      [IsFractionRing R K], ∃ f : AbsoluteValue K ℝ, IsNonarchimedean f ∧ f.IsNontrivial ∧
      (∀ x : K, f x ≤ 1 ↔ x ∈ Set.range (algebraMap R K)) ∧ CompleteSpace (WithAbs f) := by
  intro R K _ _ _ _ _ _ _
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let v := IsDiscreteValuationRing.maximalIdeal R
  have hb : (1 : ℝ≥0) < 2 := one_lt_two
  have hball : ∀ x : K, v.adicAbv hb x ≤ 1 ↔ x ∈ Set.range (algebraMap R K) := by
    intro x
    have : v.adicAbv hb x ≤ 1 ↔ v.valuation K x ≤ 1 := by
      rw [← WithZeroMulInt.toNNReal_le_one_iff hb, ← NNReal.coe_le_coe]
      rfl
    rw [this]
    exact ⟨IsDiscreteValuationRing.exists_lift_of_le_one,
      fun ⟨y, hy⟩ => hy ▸ v.valuation_le_one y⟩
  refine ⟨v.adicAbv hb, v.isNonarchimedean_adicAbv hb, ?_, hball,
    completeSpace_withAbs_of_unitBall R K _ hball⟩
  have hπK : algebraMap R K π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 hπ.ne_zero
  have h1 : v.valuation K (algebraMap R K π) < 1 :=
    (v.valuation_lt_one_iff_mem π).2
      (show π ∈ IsLocalRing.maximalIdeal R from (IsLocalRing.mem_maximalIdeal π).2 hπ.not_isUnit)
  have h2 : WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (v.valuation K (algebraMap R K π)) < 1 := by
    have := WithZeroMulInt.toNNReal_strictMono hb h1
    rwa [map_one] at this
  refine ⟨algebraMap R K π, hπK, ?_⟩
  intro heq
  have : ((WithZeroMulInt.toNNReal (ne_zero_of_lt hb) (v.valuation K (algebraMap R K π)) : ℝ≥0) : ℝ)
      = 1 := heq
  exact absurd (NNReal.coe_lt_coe.2 h2) (by rw [this]; simp)

end GlobalTheory.KLC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAbsoluteValueCompleteSpaceOfDvrStatement
open scoped NNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_absoluteValue_completeSpace_of_dvr : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Field K] [Algebra R K] [IsFractionRing R K], ∃ f : AbsoluteValue K ℝ, IsNonarchimedean f ∧ f.IsNontrivial ∧ (∀ x : K, f x ≤ 1 ↔ x ∈ Set.range (algebraMap R K)) ∧ CompleteSpace (WithAbs f) := by
  first | exact @GlobalTheory.KLC.exists_absoluteValue_completeSpace_of_isDiscreteValuationRing | exact GlobalTheory.KLC.exists_absoluteValue_completeSpace_of_isDiscreteValuationRing | (intros; apply GlobalTheory.KLC.exists_absoluteValue_completeSpace_of_isDiscreteValuationRing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NewtonPowerSeriesSurjectiveLinearizationSolution
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NewtonPowerSeriesSurjectiveLinearizationSolution
open Polynomial

namespace GlobalTheory

theorem newton_powerSeries_of_surjective_linearisation (k ι κ : Type) [Field k] [Fintype ι] [Fintype κ]
    (G : (ι → PowerSeries k) → κ → PowerSeries k) (x₀ : ι → k) (L : (ι → k) →ₗ[k] (κ → k))
    (hL : Function.Surjective L)
    (h0 : ∀ e, PowerSeries.constantCoeff (G (fun i => PowerSeries.C (x₀ i)) e) = 0)
    (hG : ∀ (x h : ι → PowerSeries k) (m : ℕ), 1 ≤ m → (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) → ∀ e,
      (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ G (fun i => x i + PowerSeries.X ^ m * h i) e - G x e -
        PowerSeries.X ^ m * PowerSeries.C (L (fun i => PowerSeries.constantCoeff (h i)) e)) :
    ∃ x : ι → PowerSeries k, (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) ∧ ∀ e, G x e = 0 := by
  classical
  let r := Function.surjInv hL
  have hLr : ∀ v, L (r v) = v := Function.surjInv_eq hL
  let step : ℕ → (ι → PowerSeries k) → (ι → PowerSeries k) := fun m x i =>
    x i + PowerSeries.X ^ m * PowerSeries.C (r (fun e => -PowerSeries.coeff m (G x e)) i)
  let sq : ℕ → (ι → PowerSeries k) := fun n =>
    Nat.rec (motive := fun _ => ι → PowerSeries k) (fun i => PowerSeries.C (x₀ i)) (fun n x => step (n + 1) x) n
  have sq_zero : sq 0 = fun i => PowerSeries.C (x₀ i) := rfl
  have sq_succ : ∀ n, sq (n + 1) = step (n + 1) (sq n) := fun n => rfl
  have coeffXC : ∀ (m j : ℕ) (c : k),
      PowerSeries.coeff j ((PowerSeries.X : PowerSeries k) ^ m * PowerSeries.C c) = if j = m then c else 0 := by
    intro m j c
    rw [mul_comm, PowerSeries.coeff_C_mul_X_pow]
  have inv : ∀ n, (∀ i, PowerSeries.constantCoeff (sq n i) = x₀ i) ∧
      ∀ e, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G (sq n) e := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun i => by simp [sq_zero], fun e => ?_⟩
      rw [zero_add, pow_one, PowerSeries.X_dvd_iff, sq_zero]
      exact h0 e
    | succ n ih =>
      have hc : ∀ i, PowerSeries.constantCoeff (sq (n + 1) i) = x₀ i := by
        intro i
        simp [sq_succ, step, ih.1 i]
      refine ⟨hc, fun e => ?_⟩
      set x := sq n with hx
      set v : κ → k := fun e => -PowerSeries.coeff (n + 1) (G x e) with hv
      have key := hG x (fun i => PowerSeries.C (r v i)) (n + 1) (by omega) ih.1 e
      have hcv : (fun i => PowerSeries.constantCoeff (PowerSeries.C (r v i))) = r v := by
        funext i; simp
      rw [hcv, hLr] at key
      have hs : sq (n + 1) = fun i => x i + PowerSeries.X ^ (n + 1) * PowerSeries.C (r v i) := by
        rw [sq_succ]
      have h2 : (PowerSeries.X : PowerSeries k) ^ (n + 1 + 1) ∣
          G x e + PowerSeries.X ^ (n + 1) * PowerSeries.C (v e) := by
        rw [PowerSeries.X_pow_dvd_iff]
        intro j hj
        rw [map_add (f := _), coeffXC]
        rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
        · have := (PowerSeries.X_pow_dvd_iff.mp (ih.2 e)) j hj'
          rw [this, if_neg (by omega), add_zero]
        · have hjn : j = n + 1 := by omega
          subst hjn
          simp [hv]
      have := dvd_add key h2
      rw [hs]
      convert this using 1
      ring
  have stab : ∀ i j n, j ≤ n → PowerSeries.coeff j (sq n i) = PowerSeries.coeff j (sq j i) := by
    intro i j n hjn
    induction n, hjn using Nat.le_induction with
    | base => rfl
    | succ n hjn ihn =>
      rw [← ihn, sq_succ]
      simp only [step, map_add (f := _)]
      rw [coeffXC, if_neg (by omega), add_zero]
  let xl : ι → PowerSeries k := fun i => PowerSeries.mk (fun j => PowerSeries.coeff j (sq j i))
  have hdiff : ∀ n i, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ xl i - sq n i := by
    intro n i
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    simp only [xl, map_sub, PowerSeries.coeff_mk]
    rw [stab i j n (by omega), sub_self]
  have hlim : ∀ n e, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G xl e := by
    intro n e
    choose d hd using hdiff n
    have hx : xl = fun i => sq n i + PowerSeries.X ^ (n + 1) * d i := by
      funext i; rw [← hd i]; ring
    have key := hG (sq n) d (n + 1) (by omega) (inv n).1 e
    rw [← hx] at key
    have k1 : (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G xl e - G (sq n) e := by
      have h3 : (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ (PowerSeries.X : PowerSeries k) ^ (n + 1 + 1) :=
        pow_dvd_pow _ (by omega)
      have := dvd_add (h3.trans key) (dvd_mul_right ((PowerSeries.X : PowerSeries k) ^ (n + 1))
        (PowerSeries.C (L (fun i => PowerSeries.constantCoeff (d i)) e)))
      simpa using this
    have := dvd_add k1 ((inv n).2 e)
    simpa using this
  refine ⟨xl, fun i => ?_, fun e => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [xl, PowerSeries.coeff_mk]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (inv 0).1 i
  · ext j
    rw [map_zero]
    exact PowerSeries.X_pow_dvd_iff.mp (hlim j e) j (by omega)

theorem newton_powerSeries_target : ∀ (k ι κ : Type) [Field k] [Fintype ι] [Fintype κ] (G : (ι → PowerSeries k) → κ → PowerSeries k) (x₀ : ι → k) (L : (ι → k) →ₗ[k] (κ → k)), Function.Surjective L →
 (∀ e, PowerSeries.constantCoeff (G (fun i => PowerSeries.C (x₀ i)) e) = 0) →
 (∀ (x h : ι → PowerSeries k) (m : ℕ), 1 ≤ m → (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) → ∀ e,
   (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ G (fun i => x i + PowerSeries.X ^ m * h i) e - G x e - PowerSeries.X ^ m * PowerSeries.C (L (fun i => PowerSeries.constantCoeff (h i)) e)) →
 ∃ x : ι → PowerSeries k, (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) ∧ ∀ e, G x e = 0 :=
  fun k ι κ _ _ _ G x₀ L hL h0 hG => newton_powerSeries_of_surjective_linearisation k ι κ G x₀ L hL h0 hG

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NewtonPowerSeriesSurjectiveLinearizationSolutionStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newton_powerSeries_surjective_linearization_solution : ∀ (k ι κ : Type) [Field k] [Fintype ι] [Fintype κ] (G : (ι → PowerSeries k) → κ → PowerSeries k) (x₀ : ι → k) (L : (ι → k) →ₗ[k] (κ → k)), Function.Surjective L →
 (∀ e, PowerSeries.constantCoeff (G (fun i => PowerSeries.C (x₀ i)) e) = 0) →
 (∀ (x h : ι → PowerSeries k) (m : ℕ), 1 ≤ m → (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) → ∀ e,
   (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ G (fun i => x i + PowerSeries.X ^ m * h i) e - G x e - PowerSeries.X ^ m * PowerSeries.C (L (fun i => PowerSeries.constantCoeff (h i)) e)) →
 ∃ x : ι → PowerSeries k, (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) ∧ ∀ e, G x e = 0 := by
  first | exact @GlobalTheory.newton_powerSeries_target | exact GlobalTheory.newton_powerSeries_target | (intros; apply GlobalTheory.newton_powerSeries_target <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitAlgebraMapEqOfValuationEqOne
open IsLocalRing

namespace GlobalTheory.PrimeElement

variable {R : Type*} [CommRing R] {π : R}

theorem isPrime_span (hπ : Prime π) : (Ideal.span {π}).IsPrime :=
  (Ideal.span_singleton_prime hπ.ne_zero).2 hπ

theorem mem_primeCompl_span [(Ideal.span {π}).IsPrime] {b : R} :
    b ∈ (Ideal.span {π}).primeCompl ↔ ¬ π ∣ b := by
  rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]

section AtPrime

variable [(Ideal.span {π}).IsPrime] (S : Type*) [CommRing S] [Algebra R S]
  [IsLocalization.AtPrime S (Ideal.span {π})]

theorem maximalIdeal_eq_span [IsLocalRing S] :
    maximalIdeal S = Ideal.span {algebraMap R S π} := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {π}) S, Ideal.map_span,
    Set.image_singleton]

include π in
theorem algebraMap_atPrime_injective [IsDomain R] : Function.Injective (algebraMap R S) :=
  IsLocalization.injective S (Ideal.span {π}).primeCompl_le_nonZeroDivisors

include π in
theorem isDomain_atPrime [IsDomain R] : IsDomain S :=
  IsLocalization.isDomain_of_le_nonZeroDivisors S (Ideal.span {π}).primeCompl_le_nonZeroDivisors

theorem isDiscreteValuationRing [IsDomain R] [IsNoetherianRing R] [IsDomain S] (hπ : π ≠ 0) :
    IsDiscreteValuationRing S := by
  have := IsLocalization.AtPrime.isLocalRing S (Ideal.span {π})
  have : IsNoetherianRing S :=
    IsLocalization.isNoetherianRing (Ideal.span {π}).primeCompl S inferInstance
  have hne : algebraMap R S π ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap_atPrime_injective (π := π) S)).2 hπ
  have hf : ¬ IsField S := by
    rw [isField_iff_maximalIdeal_eq, maximalIdeal_eq_span (π := π) S, Ideal.span_singleton_eq_bot]
    exact hne
  refine ((IsDiscreteValuationRing.TFAE S hf).out 1 5).2 ?_
  exact ⟨⟨_, maximalIdeal_eq_span (π := π) S⟩⟩

theorem irreducible_algebraMap [IsDomain R] [IsNoetherianRing R] (hπ : π ≠ 0) :
    Irreducible (algebraMap R S π) := by
  have := isDomain_atPrime (π := π) S
  have := isDiscreteValuationRing (π := π) S hπ
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 (maximalIdeal_eq_span S)

end AtPrime

theorem exists_eq_of_pow_mul_of_mul {K : Type*} [CommRing K] [IsDomain K] [Algebra R K]
    [FaithfulSMul R K] (hπ : Prime π) {x : K} {n : ℕ} {a b c : R}
    (ha : algebraMap R K (π ^ n) * x = algebraMap R K a) (hb : ¬ π ∣ b)
    (hc : algebraMap R K b * x = algebraMap R K c) : ∃ r : R, algebraMap R K r = x := by
  have hinj := FaithfulSMul.algebraMap_injective R K
  have := hinj.isDomain
  have h : b * a = π ^ n * c := hinj <| by
    rw [map_mul, map_mul, ← ha, ← hc]; ring
  obtain ⟨r, rfl⟩ : π ^ n ∣ a := hπ.pow_dvd_of_dvd_mul_left n hb ⟨c, h⟩
  refine ⟨r, mul_left_cancel₀ ((map_ne_zero_iff _ hinj).2 (pow_ne_zero n hπ.ne_zero)) ?_⟩
  rw [ha, map_mul]

section Inter

variable [(Ideal.span {π}).IsPrime]
  (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.Away π A]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {π})]
  (K : Type*) [CommRing K] [IsDomain K] [Algebra R K] [FaithfulSMul R K]
  [Algebra A K] [IsScalarTower R A K] [Algebra S K] [IsScalarTower R S K]

theorem range_inf_range (hπ : π ≠ 0) :
    (algebraMap A K).range ⊓ (algebraMap S K).range = (algebraMap R K).range := by
  have hp : Prime π := (Ideal.span_singleton_prime hπ).1 inferInstance
  refine le_antisymm ?_ ?_
  · rintro x ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h₁⟩ := IsLocalization.surj (Submonoid.powers π) y
    obtain ⟨⟨c, ⟨b, hb⟩⟩, h₂⟩ := IsLocalization.surj (Ideal.span {π}).primeCompl z
    refine exists_eq_of_pow_mul_of_mul hp (n := n) (a := a) (c := c) ?_
      (mem_primeCompl_span.1 hb) ?_
    · rw [IsScalarTower.algebraMap_apply R A K, IsScalarTower.algebraMap_apply R A K a, ← h₁,
        map_mul, hy, mul_comm]
    · rw [IsScalarTower.algebraMap_apply R S K, IsScalarTower.algebraMap_apply R S K c, ← h₂,
        map_mul, hz, mul_comm]
  · rintro _ ⟨r, rfl⟩
    exact ⟨⟨algebraMap R A r, (IsScalarTower.algebraMap_apply R A K r).symm⟩,
      ⟨algebraMap R S r, (IsScalarTower.algebraMap_apply R S K r).symm⟩⟩

omit [(Ideal.span {π}).IsPrime] in
theorem algebraMap_away_injective (hπ : π ≠ 0) : Function.Injective (algebraMap A K) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  have hinj := FaithfulSMul.algebraMap_injective R K
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers π) y
  have h := congrArg (algebraMap A K) (IsLocalization.mk'_spec A a s)
  rw [map_mul, hy, zero_mul, ← IsScalarTower.algebraMap_apply, eq_comm,
    map_eq_zero_iff _ hinj] at h
  simp [h]


variable {A S} in
theorem exists_algebraMap_eq (hπ : π ≠ 0) {y : A} {z : S}
    (h : algebraMap A K y = algebraMap S K z) :
    ∃ r : R, algebraMap R A r = y := by
  obtain ⟨r, hr⟩ : algebraMap A K y ∈ (algebraMap R K).range := by
    rw [← range_inf_range A S K hπ]
    exact ⟨⟨y, rfl⟩, ⟨z, h.symm⟩⟩
  exact ⟨r, algebraMap_away_injective A K hπ (by rw [← IsScalarTower.algebraMap_apply, hr])⟩


variable {A S} in
theorem exists_unit_algebraMap_eq (hπ : π ≠ 0) {y : A} (hy : IsUnit y) {z : S} (hz : IsUnit z)
    (h : algebraMap A K y = algebraMap S K z) :
    ∃ r : R, IsUnit r ∧ algebraMap R A r = y := by
  obtain ⟨y, rfl⟩ := hy
  obtain ⟨z, rfl⟩ := hz
  have h' : algebraMap A K (y⁻¹ : Aˣ) = algebraMap S K (z⁻¹ : Sˣ) := by
    refine mul_left_cancel₀ (y.isUnit.map (algebraMap A K)).ne_zero ?_
    rw [← map_mul, Units.mul_inv, map_one, h, ← map_mul, Units.mul_inv, map_one]
  obtain ⟨r, hr⟩ := exists_algebraMap_eq (A := A) (S := S) (K := K) hπ h
  obtain ⟨r', hr'⟩ := exists_algebraMap_eq (A := A) (S := S) (K := K) hπ h'
  refine ⟨r, IsUnit.of_mul_eq_one r' (FaithfulSMul.algebraMap_injective R K ?_), hr⟩
  rw [IsScalarTower.algebraMap_apply R A K, map_mul, hr, hr', Units.mul_inv, map_one, map_one]

end Inter

section Valuation

variable [(Ideal.span {π}).IsPrime]
  {A : Type*} [CommRing A] [Algebra R A] [IsLocalization.Away π A]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {π})]
  [IsDomain S] [IsDiscreteValuationRing S]
  (K : Type*) [Field K] [Algebra R K] [FaithfulSMul R K]
  [Algebra A K] [IsScalarTower R A K] [Algebra S K] [IsScalarTower R S K] [IsFractionRing S K]

end Valuation

theorem existsUnique_zpow_mul_eq_unit {S K : Type*} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] [Field K] [Algebra S K] [IsFractionRing S K] {ϖ : S}
    (hϖ : Irreducible ϖ) {x : K} (hx : x ≠ 0) :
    ∃! a : ℤ, ∃ u : S, IsUnit u ∧ algebraMap S K u = algebraMap S K ϖ ^ a * x := by
  have hinj := IsFractionRing.injective S K
  have h0 : algebraMap S K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have key : ∀ (a b : ℤ) (u v : S), IsUnit v → algebraMap S K u = algebraMap S K ϖ ^ a * x →
      algebraMap S K v = algebraMap S K ϖ ^ b * x → b ≤ a := by
    intro a b u v hv h₁ h₂
    by_contra! hlt
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + (n + 1 : ℕ) := ⟨(b - a - 1).toNat, by push_cast; omega⟩
    have : v = ϖ * (ϖ ^ n * u) := hinj <| by
      rw [h₂, hn, zpow_add₀ h0, zpow_natCast, map_mul, map_mul, map_pow, h₁]; ring
    exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (this ▸ hv))
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hp0 : p ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq0 hϖ
  refine existsUnique_of_exists_of_unique ⟨(n : ℤ) - m, (u * v⁻¹ : Sˣ), Units.isUnit _, ?_⟩ ?_
  · have hv : algebraMap S K v ≠ 0 := (v.isUnit.map _).ne_zero
    rw [zpow_sub₀ h0]
    simp only [Units.val_mul, map_mul, map_units_inv, map_pow, zpow_natCast]
    field_simp
  · rintro a b ⟨u, hu, h₁⟩ ⟨v, hv, h₂⟩
    exact le_antisymm (key b a v u hu h₂ h₁) (key a b u v hv h₁ h₂)

end GlobalTheory.PrimeElement
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormDegreeBoundPolynomialCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormForm
open Polynomial

namespace GlobalTheory.NormFormBound

theorem prod_pow_bound {k σ : Type} [Field k] (s : Finset σ) (m : σ → ℕ) (p : σ → k[X]) (d : ℕ)
    (hp : ∀ i, (p i).natDegree ≤ d) :
    (∏ i ∈ s, p i ^ m i).natDegree ≤ (∑ i ∈ s, m i) * d ∧
      (∏ i ∈ s, p i ^ m i).coeff ((∑ i ∈ s, m i) * d) = ∏ i ∈ s, (p i).coeff d ^ m i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, add_mul]
    have hpa : (p a ^ m a).natDegree ≤ m a * d :=
      natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hp a))
    refine ⟨natDegree_mul_le.trans (add_le_add hpa ih1), ?_⟩
    rw [coeff_mul_add_eq_of_natDegree_le hpa ih1, coeff_pow_of_natDegree_le (hp a), ih2, Finset.prod_insert ha]

theorem form_bound {k σ : Type} [Field k] [Infinite k] [Fintype σ] (n : ℕ)
    (F : MvPolynomial σ k[X]) (hF : F.IsHomogeneous n) (h0 : F ≠ 0) :
    ∃ (c : ℕ) (lam : σ → k),
      (∀ (d : ℕ) (p : σ → k[X]), (∀ i, (p i).natDegree ≤ d) →
        (MvPolynomial.eval p F).natDegree ≤ n * d + c) ∧
      ∀ (d : ℕ) (p : σ → k[X]), (∀ i, (p i).natDegree ≤ d) → (∀ i, (p i).coeff d = lam i) →
        (MvPolynomial.eval p F).coeff (n * d + c) ≠ 0 := by
  classical
  set c := F.support.sup (fun m => (F.coeff m).natDegree) with hc
  set G : MvPolynomial σ k := ∑ m ∈ F.support, MvPolynomial.monomial m ((F.coeff m).coeff c) with hG
  have hsumdeg : ∀ m ∈ F.support, ∑ i ∈ m.support, m i = n := by
    intro m hm
    have h := hF (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  have hcle : ∀ m ∈ F.support, (F.coeff m).natDegree ≤ c := fun m hm =>
    Finset.le_sup (f := fun m => (F.coeff m).natDegree) hm
  have hG0 : G ≠ 0 := by
    have hne : F.support.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
    obtain ⟨m0, hm0, hmax⟩ := Finset.exists_max_image F.support (fun m => (F.coeff m).natDegree) hne
    have hcm : c = (F.coeff m0).natDegree :=
      le_antisymm (Finset.sup_le fun m hm => hmax m hm) (hcle m0 hm0)
    intro hG'
    have h1 := congrArg (AddMonoidAlgebra.coeff · m0) hG'
    rw [hG, MvPolynomial.coeff_sum, Finset.sum_eq_single m0] at h1
    · rw [MvPolynomial.coeff_monomial, if_pos rfl, hcm, MvPolynomial.coeff_zero] at h1
      exact (MvPolynomial.mem_support_iff.mp hm0) (Polynomial.leadingCoeff_eq_zero.mp h1)
    · intro m _ hm
      rw [MvPolynomial.coeff_monomial, if_neg hm]
    · intro h
      exact absurd hm0 h
  obtain ⟨lam, hlam⟩ : ∃ lam : σ → k, MvPolynomial.eval lam G ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hG0 (MvPolynomial.funext fun x => by simpa using hall x)
  refine ⟨c, lam, ?_, ?_⟩
  · intro d p hp
    rw [MvPolynomial.eval_eq]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
    have hdeg := (prod_pow_bound m.support m p d hp).1
    rw [hsumdeg m hm] at hdeg
    refine natDegree_mul_le.trans ?_
    have := hcle m hm
    omega
  · intro d p hp hpl
    rw [MvPolynomial.eval_eq, Polynomial.finsetSum_coeff]
    have hterm : ∀ m ∈ F.support, (F.coeff m * ∏ i ∈ m.support, p i ^ m i).coeff (n * d + c) =
        (F.coeff m).coeff c * ∏ i ∈ m.support, lam i ^ m i := by
      intro m hm
      have hb := prod_pow_bound m.support m p d hp
      rw [hsumdeg m hm] at hb
      rw [add_comm (n * d) c, coeff_mul_add_eq_of_natDegree_le (hcle m hm) hb.1, hb.2]
      simp [hpl]
    rw [Finset.sum_congr rfl hterm]
    have hev : MvPolynomial.eval lam G =
        ∑ m ∈ F.support, (F.coeff m).coeff c * ∏ i ∈ m.support, lam i ^ m i := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hG, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [MvPolynomial.eval_monomial, Finsupp.prod]
    rw [← hev]
    exact hlam

theorem exists_norm_form {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)
    (b : Module.Basis (Fin n) R A) :
    ∃ F : MvPolynomial (Fin n) R, F.IsHomogeneous n ∧
      ∀ p : Fin n → R, MvPolynomial.eval p F = Algebra.norm R (∑ i, p i • b i) := by
  classical
  refine ⟨(Matrix.of fun a c => ∑ i, MvPolynomial.C (Algebra.leftMulMatrix b (b i) a c) *
      MvPolynomial.X i).det, ?_, ?_⟩
  · rw [Matrix.det_apply]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    have hC : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin n) R) =
        MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : R) := by simp
    rw [hC]
    have hent : ∀ a ∈ (Finset.univ : Finset (Fin n)), ((Matrix.of fun a c => ∑ i,
        MvPolynomial.C (Algebra.leftMulMatrix b (b i) a c) * MvPolynomial.X i) (σ a) a).IsHomogeneous 1 := by
      intro a _
      rw [Matrix.of_apply]
      refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
      simpa using (MvPolynomial.isHomogeneous_C (Fin n) (Algebra.leftMulMatrix b (b i) (σ a) a)).mul
        (MvPolynomial.isHomogeneous_X R i)
    have hmul := (MvPolynomial.isHomogeneous_C (Fin n) ((Equiv.Perm.sign σ : ℤ) : R)).mul
      (MvPolynomial.IsHomogeneous.prod _ _ (fun _ => 1) hent)
    simpa using hmul
  · intro p
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det]
    congr 1
    ext a c
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Matrix.sum_apply, mul_comm]

theorem norm_degree (k A : Type) [Field k] [Infinite k] [CommRing A] [IsDomain A]
    [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) :
    ∃ (c : ℕ) (lam : Fin n → k),
      (∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).natDegree ≤ d) →
        (Algebra.norm k[X] (∑ i, p i • b i)).natDegree ≤ n * d + c) ∧
      ∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).degree < (d : WithBot ℕ)) →
        ∑ i, (C (lam i) * X ^ d + p i) • b i ≠ 0 ∧
          (Algebra.norm k[X] (∑ i, (C (lam i) * X ^ d + p i) • b i)).natDegree = n * d + c := by
  classical
  haveI : Module.Free k[X] A := Module.Free.of_basis b
  haveI : Module.Finite k[X] A := Module.Finite.of_basis b
  obtain ⟨F, hFh, hFev⟩ := exists_norm_form n b
  have hF0 : F ≠ 0 := by
    intro hF
    have h1 := hFev (fun i => b.repr 1 i)
    rw [hF, map_zero, b.sum_repr 1, map_one] at h1
    exact one_ne_zero h1.symm
  obtain ⟨c, lam, hb1, hb2⟩ := form_bound n F hFh hF0
  refine ⟨c, lam, fun d p hp => ?_, fun d p hp => ?_⟩
  · rw [← hFev]
    exact hb1 d p hp
  · have hq1 : ∀ i, (C (lam i) * X ^ d + p i).natDegree ≤ d := fun i =>
      (natDegree_add_le _ _).trans
        (max_le (natDegree_C_mul_X_pow_le _ _) (natDegree_le_of_degree_le (hp i).le))
    have hq2 : ∀ i, (C (lam i) * X ^ d + p i).coeff d = lam i := fun i => by
      rw [coeff_add, coeff_C_mul_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt (hp i), add_zero]
    have hN : (Algebra.norm k[X] (∑ i, (C (lam i) * X ^ d + p i) • b i)).coeff (n * d + c) ≠ 0 := by
      rw [← hFev]
      exact hb2 d (fun i => C (lam i) * X ^ d + p i) hq1 hq2
    refine ⟨fun h0 => hN (by rw [h0, Algebra.norm_zero, coeff_zero]), ?_⟩
    apply le_antisymm
    · rw [← hFev]
      exact hb1 d (fun i => C (lam i) * X ^ d + p i) hq1
    · exact le_natDegree_of_ne_zero hN

end GlobalTheory.NormFormBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormDegreeBoundPolynomialCombination
open Polynomial

namespace GlobalTheory.NormDegree

noncomputable section

variable {k A : Type} [Field k] [CommRing A] [Algebra k[X] A] {n : ℕ}

theorem natDegree_norm_of_coord_degree : ∀ (k A : Type) [Field k] [Infinite k] [CommRing A] [IsDomain A] [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A), ∃ (c : ℕ) (lam : Fin n → k),
 (∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).natDegree ≤ d) → (Algebra.norm k[X] (∑ i, p i • b i)).natDegree ≤ n * d + c) ∧
 (∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).degree < d) → (∑ i, (C (lam i) * X ^ d + p i) • b i) ≠ 0 ∧ (Algebra.norm k[X] (∑ i, (C (lam i) * X ^ d + p i) • b i)).natDegree = n * d + c) := by
  exact @_root_.GlobalTheory.NormFormBound.norm_degree

end

end GlobalTheory.NormDegree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormDegreeBoundPolynomialCombinationStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_degree_bound_polynomial_combination : ∀ (k A : Type) [Field k] [Infinite k] [CommRing A] [IsDomain A] [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A), ∃ (c : ℕ) (lam : Fin n → k),
 (∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).natDegree ≤ d) → (Algebra.norm k[X] (∑ i, p i • b i)).natDegree ≤ n * d + c) ∧
 (∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).degree < d) → (∑ i, (C (lam i) * X ^ d + p i) • b i) ≠ 0 ∧ (Algebra.norm k[X] (∑ i, (C (lam i) * X ^ d + p i) • b i)).natDegree = n * d + c) := by
  first | exact @GlobalTheory.NormDegree.natDegree_norm_of_coord_degree | exact GlobalTheory.NormDegree.natDegree_norm_of_coord_degree | (intros; apply GlobalTheory.NormDegree.natDegree_norm_of_coord_degree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DedekindFiniteTypeIdealCodimension
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DedekindFiniteTypeIdealCodimension
open Polynomial

namespace GlobalTheory
namespace DedekindCodim

variable {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

theorem algebraMap_quot_bijective (P : Ideal A) [P.IsMaximal] :
    Function.Bijective (algebraMap k (A ⧸ P)) := by
  letI : Field (A ⧸ P) := Ideal.Quotient.field P
  haveI : Algebra.FiniteType k (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P)
      (Ideal.Quotient.mkₐ_surjective k P)
  haveI : Module.Finite k (A ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ P)
  haveI : Algebra.IsIntegral k (A ⧸ P) := Algebra.IsIntegral.of_finite k (A ⧸ P)
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

theorem maximal_part (P : Ideal A) (hP : P.IsMaximal) :
    Module.finrank k (A ⧸ P) = 1 ∧ ∃ φ : A →ₐ[k] k, ∀ u, u ∈ P ↔ φ u = 0 := by
  have hb := algebraMap_quot_bijective (k := k) P
  let e : k ≃ₐ[k] (A ⧸ P) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ P)) hb
  refine ⟨?_, ⟨(e.symm : (A ⧸ P) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k P), fun u => ?_⟩⟩
  · rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
  · change u ∈ P ↔ e.symm (Ideal.Quotient.mkₐ k P u) = 0
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]

theorem exists_sub_mem (P : Ideal A) [P.IsMaximal] (a : A) :
    ∃ c : k, a - algebraMap k A c ∈ P := by
  obtain ⟨c, hc⟩ := (algebraMap_quot_bijective (k := k) P).2 (Ideal.Quotient.mk P a)
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq] at hc
  rw [← P.neg_mem_iff, neg_sub]
  exact hc

theorem span_sup_mul_eq (I P : Ideal A) (hI : I ≠ ⊥) (hP : P.IsMaximal) (x : A) (hx : x ∈ I)
    (hxP : x ∉ I * P) : Ideal.span {x} ⊔ I * P = I := by
  have hKI : Ideal.span {x} ⊔ I * P ≤ I :=
    sup_le ((Ideal.span_singleton_le_iff_mem _).2 hx) Ideal.mul_le_left
  obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.2 hKI
  have hPL : I * P ≤ I * L := hL ▸ le_sup_right
  have hLP : P ≤ L := Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left (show I ≠ 0 from hI)).1
    (Ideal.dvd_iff_le.2 hPL))
  by_cases hLt : L = ⊤
  · rw [hL, hLt, Ideal.mul_top]
  · have := hP.eq_of_le hLt hLP
    subst this
    exact absurd (hL ▸ (le_sup_left : Ideal.span {x} ≤ _) (Ideal.mem_span_singleton_self x)) hxP

theorem rank_quot_mul_maximal (I P : Ideal A) (hI : I ≠ ⊥) (hP : P.IsMaximal) :
    Module.rank k (A ⧸ (I * P)) = Module.rank k (A ⧸ I) + 1 := by
  haveI := hP
  have hne : I * P ≠ I := by
    intro h
    have h2 : I * P = I * ⊤ := by rw [h, Ideal.mul_top]
    exact hP.ne_top (mul_left_cancel₀ (show I ≠ 0 from hI) h2)
  obtain ⟨x, hx, hxP⟩ : ∃ x ∈ I, x ∉ I * P := by
    by_contra h
    push_neg at h
    exact hne (le_antisymm Ideal.mul_le_left h)
  let f : (A ⧸ (I * P)) →ₗ[k] (A ⧸ I) :=
    (Ideal.Quotient.factorₐ k (Ideal.mul_le_left : I * P ≤ I)).toLinearMap
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  set v : A ⧸ (I * P) := Ideal.Quotient.mk _ x with hvdef
  have hv0 : v ≠ 0 := fun h => hxP (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hker : LinearMap.ker f = k ∙ v := by
    apply le_antisymm
    · intro z hz
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hy : y ∈ I := by
        have h0 : f (Ideal.Quotient.mk _ y) = 0 := hz
        exact Ideal.Quotient.eq_zero_iff_mem.1 h0
      have hyK : y ∈ Ideal.span {x} ⊔ I * P := by
        rw [span_sup_mul_eq I P hI hP x hx hxP]; exact hy
      obtain ⟨a', ha', z', hz', hsum⟩ := Submodule.mem_sup.1 hyK
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 ha'
      obtain ⟨c, hc⟩ := exists_sub_mem (k := k) P a
      rw [Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      rw [← hsum, hvdef, Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul,
        Ideal.Quotient.eq]
      have h3 : algebraMap k A c * x - (a * x + z') = -((a - algebraMap k A c) * x) - z' := by
        ring
      rw [h3]
      refine Ideal.sub_mem _ ((I * P).neg_mem ?_) hz'
      rw [mul_comm I P]
      exact Ideal.mul_mem_mul hc hx
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      show f v = 0
      exact Ideal.Quotient.eq_zero_iff_mem.2 hx
  have h1 := LinearMap.rank_range_add_rank_ker f
  rw [LinearMap.range_eq_top.2 hf, rank_top, hker] at h1
  have hv1 : Module.rank k (k ∙ v) = 1 := by
    rw [← Module.finrank_eq_rank, finrank_span_singleton hv0]; simp
  rw [← h1, hv1]

end DedekindCodim
end GlobalTheory

namespace GlobalTheory
namespace DedekindCodim

variable {k A : Type} [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

theorem rank_quot_top : Module.rank k (A ⧸ (⊤ : Ideal A)) = 0 := by
  haveI : Subsingleton (A ⧸ (⊤ : Ideal A)) := Ideal.Quotient.subsingleton_iff.2 rfl
  exact rank_subsingleton' k _

theorem maximal_of_prime {p : Ideal A} (hp : Prime p) : p ≠ ⊥ ∧ p.IsMaximal := by
  have hne : p ≠ ⊥ := hp.ne_zero
  exact ⟨hne, ((Ideal.prime_iff_isPrime hne).1 hp).isMaximal hne⟩

theorem rank_quot_lt (J : Ideal A) (hJ : J ≠ ⊥) : Module.rank k (A ⧸ J) < Cardinal.aleph0 := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.1 hx, rank_quot_top]; exact Cardinal.aleph0_pos
  | h₃ a p ha hp ih =>
    obtain ⟨_, hpm⟩ := maximal_of_prime hp
    rw [mul_comm, rank_quot_mul_maximal a p ha hpm]
    exact Cardinal.add_lt_aleph0 (ih ha) Cardinal.one_lt_aleph0

theorem rank_quot_mul (J : Ideal A) (hJ : J ≠ ⊥) : ∀ I : Ideal A, I ≠ ⊥ →
    Module.rank k (A ⧸ (I * J)) = Module.rank k (A ⧸ I) + Module.rank k (A ⧸ J) := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ
  | h₂ x hx =>
    intro I _
    rw [Ideal.isUnit_iff.1 hx, rank_quot_top, Ideal.mul_top, add_zero]
  | h₃ a p ha hp ih =>
    intro I hI
    obtain ⟨_, hpm⟩ := maximal_of_prime hp
    have hIa : I * a ≠ ⊥ := mul_ne_zero (show I ≠ 0 from hI) ha
    rw [show I * (p * a) = (I * a) * p by ring, rank_quot_mul_maximal _ p hIa hpm, ih ha I hI,
      mul_comm p a, rank_quot_mul_maximal a p ha hpm, add_assoc]

theorem finite_quot (I : Ideal A) (hI : I ≠ ⊥) : Module.Finite k (A ⧸ I) :=
  Module.rank_lt_aleph0_iff.1 (rank_quot_lt I hI)

theorem finrank_quot_mul (I J : Ideal A) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    Module.finrank k (A ⧸ (I * J)) = Module.finrank k (A ⧸ I) + Module.finrank k (A ⧸ J) := by
  haveI := finite_quot (k := k) I hI
  haveI := finite_quot (k := k) J hJ
  haveI := finite_quot (k := k) (I * J) (mul_ne_zero (show I ≠ 0 from hI) (show J ≠ 0 from hJ))
  have h := rank_quot_mul (k := k) J hJ I hI
  rw [← Module.finrank_eq_rank, ← Module.finrank_eq_rank, ← Module.finrank_eq_rank] at h
  exact_mod_cast h

theorem eq_of_le_of_finrank_le (I J : Ideal A) (hI : I ≠ ⊥) (hIJ : I ≤ J)
    (hr : Module.finrank k (A ⧸ I) ≤ Module.finrank k (A ⧸ J)) : I = J := by
  obtain ⟨L, rfl⟩ := Ideal.dvd_iff_le.2 hIJ
  have hJ : J ≠ ⊥ := fun h => hI (by rw [h]; exact (zero_mul L : (0 : Ideal A) * L = 0))
  have hL : L ≠ ⊥ := fun h => hI (by rw [h]; exact (mul_zero J : J * (0 : Ideal A) = 0))
  rw [finrank_quot_mul J L hJ hL] at hr
  have h0 : Module.finrank k (A ⧸ L) = 0 := by omega
  haveI := finite_quot (k := k) L hL
  have hs : Subsingleton (A ⧸ L) := Module.finrank_zero_iff.1 h0
  rw [Ideal.Quotient.subsingleton_iff.1 hs, Ideal.mul_top]

theorem dedekind_finiteType_codim : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A],
    (∀ I : Ideal A, I ≠ ⊥ → Module.Finite k (A ⧸ I)) ∧
    (∀ P : Ideal A, P.IsMaximal → Module.finrank k (A ⧸ P) = 1 ∧
      ∃ φ : A →ₐ[k] k, ∀ u, u ∈ P ↔ φ u = 0) ∧
    (∀ I J : Ideal A, I ≠ ⊥ → J ≠ ⊥ →
      Module.finrank k (A ⧸ (I * J)) = Module.finrank k (A ⧸ I) + Module.finrank k (A ⧸ J)) ∧
    (∀ I J : Ideal A, I ≠ ⊥ → I ≤ J → Module.finrank k (A ⧸ I) ≤ Module.finrank k (A ⧸ J) →
      I = J) := by
  intro k A _ _ _ _ _ _ _
  exact ⟨fun I hI => finite_quot I hI, fun P hP => maximal_part P hP,
    fun I J hI hJ => finrank_quot_mul I J hI hJ,
    fun I J hI hIJ hr => eq_of_le_of_finrank_le I J hI hIJ hr⟩

end DedekindCodim
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DedekindFiniteTypeIdealCodimensionStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dedekind_finiteType_ideal_codimension : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A], (∀ I : Ideal A, I ≠ ⊥ → Module.Finite k (A ⧸ I)) ∧ (∀ P : Ideal A, P.IsMaximal → Module.finrank k (A ⧸ P) = 1 ∧ ∃ φ : A →ₐ[k] k, ∀ u, u ∈ P ↔ φ u = 0) ∧
 (∀ I J : Ideal A, I ≠ ⊥ → J ≠ ⊥ → Module.finrank k (A ⧸ (I * J)) = Module.finrank k (A ⧸ I) + Module.finrank k (A ⧸ J)) ∧
 (∀ I J : Ideal A, I ≠ ⊥ → I ≤ J → Module.finrank k (A ⧸ I) ≤ Module.finrank k (A ⧸ J) → I = J) := by
  first | exact @GlobalTheory.DedekindCodim.dedekind_finiteType_codim | exact GlobalTheory.DedekindCodim.dedekind_finiteType_codim | (intros; apply GlobalTheory.DedekindCodim.dedekind_finiteType_codim <;> assumption)
end
end
