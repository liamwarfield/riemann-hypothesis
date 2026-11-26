module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerTraceAlmostSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorOfSeparableCharpolyField
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
namespace GlobalTheory.Per

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

private theorem isIntegral_iff_spectralNorm_le_one' {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra ℚ_[p] K]
    [Algebra.IsAlgebraic ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] (x : K) :
    IsIntegral ℤ_[p] x ↔ spectralNorm ℚ_[p] K x ≤ 1 := by
  have hx : IsIntegral ℚ_[p] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hlift : minpoly ℚ_[p] x ∈ Polynomial.lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨(minpoly ℚ_[p] x).coeff n, h n⟩, rfl⟩
    obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (minpoly.monic hx)
    refine ⟨g, hgm, ?_⟩
    have h0 := minpoly.aeval ℚ_[p] x
    rw [← hg, Polynomial.aeval_map_algebraMap, Polynomial.aeval_def] at h0
    exact h0

private theorem spectralNorm_mul_zpadic {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra ℚ_[p] K]
    [Algebra.IsAlgebraic ℚ_[p] K] (x y : K) :
    spectralNorm ℚ_[p] K (x * y) = spectralNorm ℚ_[p] K x * spectralNorm ℚ_[p] K y := by
  simpa only [spectralMulAlgNorm_def] using map_mul (spectralMulAlgNorm ℚ_[p] K) x y

private theorem isUnit_iff_spectralNorm_eq_one {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra ℚ_[p] K]
    [Algebra.IsAlgebraic ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
    (b : integralClosure ℤ_[p] K) : IsUnit b ↔ spectralNorm ℚ_[p] K (b : K) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ((u : integralClosure ℤ_[p] K) : K) * ((u⁻¹ : (integralClosure ℤ_[p] K)ˣ) : K) = 1 := by
      have := congrArg (fun z : integralClosure ℤ_[p] K => (z : K)) u.mul_inv
      simpa only [Subalgebra.coe_mul, Subalgebra.coe_one] using this
    have h2 := congrArg (spectralNorm ℚ_[p] K) h1
    rw [spectralNorm_mul_zpadic, spectralNorm_one] at h2
    have ha := (isIntegral_iff_spectralNorm_le_one' _).mp (u : integralClosure ℤ_[p] K).2
    have hb := (isIntegral_iff_spectralNorm_le_one' _).mp ((u⁻¹ : (integralClosure ℤ_[p] K)ˣ) : integralClosure ℤ_[p] K).2
    have ha0 := spectralNorm_nonneg (K := ℚ_[p]) ((u : integralClosure ℤ_[p] K) : K)
    have hb0 := spectralNorm_nonneg (K := ℚ_[p])
      (((u⁻¹ : (integralClosure ℤ_[p] K)ˣ) : integralClosure ℤ_[p] K) : K)
    nlinarith
  · intro h
    have hb0 : (b : K) ≠ 0 := by
      intro h0
      rw [h0, spectralNorm_zero] at h
      exact zero_ne_one h
    have hinv : IsIntegral ℤ_[p] (b : K)⁻¹ := by
      rw [isIntegral_iff_spectralNorm_le_one']
      have h2 := spectralNorm_mul_zpadic (p := p) (b : K) (b : K)⁻¹
      rw [mul_inv_cancel₀ hb0, spectralNorm_one, h, one_mul] at h2
      exact h2.symm.le
    exact isUnit_iff_exists_inv.mpr ⟨⟨(b : K)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hb0)⟩

private theorem isLocalRing_integralClosure_zpadic {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra ℚ_[p] K]
    [Algebra.IsAlgebraic ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] :
    IsLocalRing (integralClosure ℤ_[p] K) := by
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb hab
  have hlt : ∀ c : integralClosure ℤ_[p] K, ¬IsUnit c → spectralNorm ℚ_[p] K (c : K) < 1 :=
    fun c hc => lt_of_le_of_ne ((isIntegral_iff_spectralNorm_le_one' _).mp c.2) (fun h => hc ((isUnit_iff_spectralNorm_eq_one c).mpr h))
  have h1 := hlt a ha
  have h2 := hlt b hb
  have h3 := (isUnit_iff_spectralNorm_eq_one (a + b)).mp hab
  have h4 := isNonarchimedean_spectralNorm (K := ℚ_[p]) (L := K) (a : K) (b : K)
  have h5 : ((a + b : integralClosure ℤ_[p] K) : K) = (a : K) + (b : K) := rfl
  rw [h5] at h3
  rw [h3] at h4
  exact absurd h4 (not_le.mpr (max_lt h1 h2))

private theorem isPrecomplete_maximalIdeal_of_free_finite_zpadic {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]
    [Module ℤ_[p] M] [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M] :
    IsPrecomplete (IsLocalRing.maximalIdeal ℤ_[p]) M := by
  classical
  set b := Module.Free.chooseBasis ℤ_[p] M
  have key : ∀ (n : ℕ) (x : M), x ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n • (⊤ : Submodule ℤ_[p] M) ↔
      ∀ i, b.equivFun x i ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n := by
    intro n x
    constructor
    · intro hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr m _ i
        simp only [map_smul, Pi.smul_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
      · intro x y hx hy i
        simp only [map_add (f := _), Pi.add_apply]
        exact add_mem (hx i) (hy i)
    · intro h
      rw [← b.sum_equivFun x]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top)
  have key1 : ∀ (n : ℕ) (y : ℤ_[p]),
      y ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n • (⊤ : Submodule ℤ_[p] ℤ_[p]) ↔
        y ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n := by
    intro n y
    change y ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ n • (⊤ : Ideal ℤ_[p]) ↔ _
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  rw [isPrecomplete_iff]
  intro f hf
  have hc : ∀ i, ∃ L : ℤ_[p], ∀ n, b.equivFun (f n) i ≡ L
      [SMOD ((IsLocalRing.maximalIdeal ℤ_[p]) ^ n • ⊤ : Submodule ℤ_[p] ℤ_[p])] := by
    intro i
    refine IsPrecomplete.prec inferInstance ?_
    intro m n hmn
    rw [SModEq.sub_mem, key1]
    have := (key m _).mp (SModEq.sub_mem.mp (hf hmn)) i
    simpa only [map_sub, Pi.sub_apply] using this
  choose L hL using hc
  refine ⟨b.equivFun.symm L, fun n => ?_⟩
  rw [SModEq.sub_mem, key]
  intro i
  have := (key1 n _).mp (SModEq.sub_mem.mp (hL i n))
  simpa only [map_sub, Pi.sub_apply, LinearEquiv.apply_symm_apply] using this

private theorem isPrecomplete_of_isPrecomplete_pow {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (he : 0 < e)
    (h : IsPrecomplete (I ^ e) R) : IsPrecomplete I R := by
  rw [isPrecomplete_iff]
  intro f hf
  obtain ⟨L, hL⟩ := h.prec (f := fun k => f (e * k)) (fun {m n} hmn => by
    rw [← pow_mul]
    exact hf (Nat.mul_le_mul_left e hmn))
  refine ⟨L, fun n => ?_⟩
  have hn : n ≤ e * n := by nlinarith
  have h1 : f n ≡ f (e * n) [SMOD (I ^ n • ⊤ : Submodule R R)] := hf hn
  have h2 := hL n
  rw [← pow_mul] at h2
  exact h1.trans (h2.mono (Submodule.smul_mono_left (Ideal.pow_le_pow_right hn)))

private theorem isAdicComplete_maximalIdeal_of_free_finite_zpadic {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra ℤ_[p] B] [Module.Free ℤ_[p] B] [Module.Finite ℤ_[p] B]
    (hp0 : (p : B) ≠ 0) (hpu : ¬IsUnit (p : B)) :
    IsAdicComplete (IsLocalRing.maximalIdeal B) B := by
  have hJ : (IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] B) = Ideal.span {(p : B)} := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  have hprecJ : IsPrecomplete ((IsLocalRing.maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] B)) B :=
    IsPrecomplete.map_algebraMap_iff.mpr isPrecomplete_maximalIdeal_of_free_finite_zpadic
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {(p : B)}) (by rwa [Ne, Ideal.span_singleton_eq_bot]) hϖ
  rw [← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq] at he
  have he0 : 0 < e := Nat.pos_of_ne_zero (fun h => by
    rw [h, pow_zero, Ideal.one_eq_top] at he
    exact hpu (Ideal.span_singleton_eq_top.mp he))
  have hprec : IsPrecomplete (IsLocalRing.maximalIdeal B ^ e) B := by
    rw [← he, ← hJ]
    exact hprecJ
  exact { toIsHausdorff := inferInstance,
          toIsPrecomplete := isPrecomplete_of_isPrecomplete_pow _ e he0 hprec }

theorem integers_completeDVR : ∀ (l : ℕ) [Fact l.Prime], ∀ LL : FinExt l,
    ∃ _ : IsDiscreteValuationRing ↥(OL LL),
      IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) ∧ ((l : ℕ) : ↥(OL LL)) ≠ 0 ∧
      ¬ IsUnit ((l : ℕ) : ↥(OL LL)) ∧ Module.Free ℤ_[l] ↥(OL LL) ∧ Module.Finite ℤ_[l] ↥(OL LL) ∧
      IsFractionRing ↥(OL LL) ↥LL.1 := by
  intro l _ LL
  unfold OL
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : Algebra.IsAlgebraic ℚ_[l] ↥LL.1 := Algebra.IsAlgebraic.of_finite ℚ_[l] ↥LL.1
  have hloc : IsLocalRing (integralClosure ℤ_[l] ↥LL.1) := isLocalRing_integralClosure_zpadic
  have hN : spectralNorm ℚ_[l] ↥LL.1 (((l : ℕ) : integralClosure ℤ_[l] ↥LL.1) : ↥LL.1) =
      (l : ℝ)⁻¹ := by
    have : (((l : ℕ) : integralClosure ℤ_[l] ↥LL.1) : ↥LL.1) = algebraMap ℚ_[l] ↥LL.1 (l : ℚ_[l]) := by
      simp
    rw [this, spectralNorm_extends, Padic.norm_p]
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : (l : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have hpu : ¬IsUnit ((l : ℕ) : integralClosure ℤ_[l] ↥LL.1) := by
    intro h
    have := (isUnit_iff_spectralNorm_eq_one _).mp h
    rw [hN] at this
    exact absurd this hl1.ne
  have hp0 : ((l : ℕ) : integralClosure ℤ_[l] ↥LL.1) ≠ 0 := by
    intro h
    rw [h] at hN
    simp only [ZeroMemClass.coe_zero, spectralNorm_zero] at hN
    exact hl0 hN.symm
  have hnf : ¬IsField (integralClosure ℤ_[l] ↥LL.1) := by
    intro h
    obtain ⟨c, hc⟩ := h.mul_inv_cancel hp0
    exact hpu (isUnit_iff_exists_inv.mpr ⟨c, hc⟩)
  have hded : IsDedekindDomain (integralClosure ℤ_[l] ↥LL.1) := inferInstance
  have hdvr : IsDiscreteValuationRing (integralClosure ℤ_[l] ↥LL.1) :=
    ((IsDiscreteValuationRing.TFAE _ hnf).out 1 3).mpr hded
  have hfin : Module.Finite ℤ_[l] (integralClosure ℤ_[l] ↥LL.1) := inferInstance
  have htf : Module.IsTorsionFree ℤ_[l] (integralClosure ℤ_[l] ↥LL.1) := by
    refine ⟨fun r hr x y hxy => ?_⟩
    have hr0 : r ≠ 0 := hr.ne_zero
    have hne : algebraMap ℤ_[l] ↥LL.1 r ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
      exact (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).mpr hr0)
    have h : ((r • x : integralClosure ℤ_[l] ↥LL.1) : ↥LL.1) =
        ((r • y : integralClosure ℤ_[l] ↥LL.1) : ↥LL.1) := congrArg Subtype.val hxy
    change r • (x : ↥LL.1) = r • (y : ↥LL.1) at h
    rw [Algebra.smul_def, Algebra.smul_def] at h
    exact Subtype.ext (mul_left_cancel₀ hne h)
  have hfree : Module.Free ℤ_[l] (integralClosure ℤ_[l] ↥LL.1) :=
    Module.free_of_finite_type_torsion_free'
  exact ⟨hdvr, isAdicComplete_maximalIdeal_of_free_finite_zpadic hp0 hpu, hp0, hpu, hfree, hfin,
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1⟩

end GlobalTheory.Per
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisGaussNormEventuallyMonomial
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisGaussNormEventuallyMonomial
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

open Filter Topology

namespace GlobalTheory.GaussSlope

theorem eventually_iSup_eq_monomial (c : ℕ → ℝ) (h0 : ∀ n, 0 ≤ c n) (h1 : ∀ n, c n ≤ 1) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hG : (⨆ n, c n * ρ ^ n) ≠ 0) :
    ∃ i, ∀ᶠ r in 𝓝[≥] ρ, (⨆ n, c n * r ^ n) = c i * r ^ i := by
  obtain ⟨j, hj⟩ : ∃ j, 0 < c j := by
    by_contra h
    push Not at h
    apply hG
    have : ∀ n, c n = 0 := fun n => le_antisymm (h n) (h0 n)
    simp [this]
  obtain ⟨σ, hσ, hσ1⟩ := exists_between hρ1
  have hσ0 : 0 < σ := hρ.trans hσ
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (mul_pos hj (pow_pos hρ j)) hσ1
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (insert j (Finset.range M))
    (fun n => toLex (c n * ρ ^ n, n)) ⟨j, Finset.mem_insert_self _ _⟩
  have key : ∀ n ∈ insert j (Finset.range M), ∀ᶠ r in 𝓝[≥] ρ, c n * r ^ n ≤ c i * r ^ i := by
    intro n hn
    rcases Prod.Lex.toLex_le_toLex.1 (hi n hn) with h | ⟨h, h'⟩
    · have : ∀ᶠ r in 𝓝 ρ, c n * r ^ n < c i * r ^ i :=
        ContinuousAt.eventually_lt (f := fun r : ℝ => c n * r ^ n) (g := fun r : ℝ => c i * r ^ i)
          (by fun_prop) (by fun_prop) h
      exact (this.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr : ρ ≤ r := hr
      simp only at h h'
      have e : ∀ m, c m * r ^ m = c m * ρ ^ m * (r / ρ) ^ m := fun m => by
        rw [div_pow]; field_simp
      rw [e n, e i, h]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ((one_le_div hρ).2 hr) h')
        (mul_nonneg (h0 _) (pow_nonneg hρ.le _))
  refine ⟨i, ?_⟩
  have hlt : ∀ᶠ r in 𝓝[≥] ρ, r < σ := (gt_mem_nhds hσ).filter_mono nhdsWithin_le_nhds
  filter_upwards [(eventually_all_finset _).2 key, hlt, self_mem_nhdsWithin] with r hk hrσ hr
  have hr : ρ ≤ r := hr
  have hr0 : 0 ≤ r := hρ.le.trans hr
  have hall : ∀ n, c n * r ^ n ≤ c i * r ^ i := by
    intro n
    by_cases hn : n < M
    · exact hk n (Finset.mem_insert_of_mem (Finset.mem_range.2 hn))
    · refine le_trans ?_ (hk j (Finset.mem_insert_self _ _))
      calc c n * r ^ n ≤ 1 * σ ^ n := by gcongr; exact h1 n
        _ ≤ σ ^ M := by rw [one_mul]; exact pow_le_pow_of_le_one hσ0.le hσ1.le (not_lt.1 hn)
        _ ≤ c j * ρ ^ j := hM.le
        _ ≤ c j * r ^ j := by gcongr
  exact le_antisymm (ciSup_le hall) (le_ciSup (f := fun n => c n * r ^ n) ⟨_, Set.forall_mem_range.2 hall⟩ i)

theorem add_eq_of_lt {R : Type} [CommRing R] (N : R → ℝ) (hadd : ∀ x y, N (x + y) ≤ max (N x) (N y))
    (hneg : ∀ x, N (-x) = N x) {x y : R} (h : N y < N x) : N (x + y) = N x := by
  refine le_antisymm ((hadd x y).trans (max_le le_rfl h.le)) ?_
  have := hadd (x + y) (-y)
  rw [add_neg_cancel_right, hneg] at this
  rcases le_max_iff.1 this with h' | h'
  · exact h'
  · exact absurd h' (not_le.2 h)

theorem map_pow_mul {R : Type} [CommRing R] (N : R → ℝ) (hmul : ∀ x y, N (x * y) = N x * N y)
    (p x : R) (k : ℕ) : N (p ^ k * x) = N p ^ k * N x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, hmul, ih]; ring

theorem slope_abstract {R : Type} [CommRing R] (p : R) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (N : ℝ → R → ℝ)
    (hN : ∀ r, ρ ≤ r → r < 1 → (∀ x, N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧
      (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ N r p = r)
    (b : R) (hb : 0 < N ρ b)
    (hd : ∀ n : ℕ, ∃ (k : ℕ) (a z : R) (c : ℕ → ℝ), p ^ k * b = a + p ^ (k + n) * z ∧ (∀ n, 0 ≤ c n) ∧
      (∀ n, c n ≤ 1) ∧ ∀ r, ρ ≤ r → r < 1 → N r a = ⨆ n, c n * r ^ n) :
    ∃ (r₁ c : ℝ) (k : ℤ), ρ < r₁ ∧ r₁ < 1 ∧ 0 < c ∧ ∀ r, ρ < r → r < r₁ → N r b = c * r ^ k := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hb hρ1
  obtain ⟨k, a, z, c, hab, h0, h1, hc⟩ := hd n
  have hz : ∀ r, ρ ≤ r → r < 1 → N r (p ^ (k + n) * z) ≤ r ^ (k + n) := by
    intro r hr hr1
    obtain ⟨e1, -, -, e4, e5⟩ := hN r hr hr1
    rw [map_pow_mul _ e4, e5]
    exact mul_le_of_le_one_right (pow_nonneg (hρ.le.trans hr) _) (e1 z)
  have hbb : ∀ r, ρ ≤ r → r < 1 → N r (p ^ k * b) = r ^ k * N r b := by
    intro r hr hr1
    obtain ⟨e1, -, -, e4, e5⟩ := hN r hr hr1
    rw [map_pow_mul _ e4, e5]
  have ha : ρ ^ (k + n) < N ρ a := by
    obtain ⟨e1, e2, e3, e4, e5⟩ := hN ρ le_rfl hρ1
    have h2 : ρ ^ (k + n) < N ρ (p ^ k * b) := by
      rw [hbb ρ le_rfl hρ1, pow_add]
      exact mul_lt_mul_of_pos_left hn (pow_pos hρ _)
    have h3 : a = p ^ k * b + -(p ^ (k + n) * z) := by rw [hab]; ring
    rw [h3, add_eq_of_lt _ e2 e3 (by rw [e3]; exact (hz ρ le_rfl hρ1).trans_lt h2)]
    exact h2
  rw [hc ρ le_rfl hρ1] at ha
  obtain ⟨i, hi⟩ := eventually_iSup_eq_monomial c h0 h1 hρ hρ1 ((pow_pos hρ _).trans ha).ne'
  rw [hi.self_of_nhdsWithin Set.self_mem_Ici] at ha
  have hci : 0 < c i := (mul_pos_iff_of_pos_right (pow_pos hρ i)).1 ((pow_pos hρ _).trans ha)
  have h4 : ∀ᶠ r in 𝓝 ρ, r ^ (k + n) < c i * r ^ i :=
    ContinuousAt.eventually_lt (f := fun r : ℝ => r ^ (k + n)) (g := fun r : ℝ => c i * r ^ i)
      (by fun_prop) (by fun_prop) ha
  have h5 : ∀ᶠ r in 𝓝[≥] ρ, r < 1 → N r b = c i * r ^ ((i : ℤ) - k) := by
    filter_upwards [hi, h4.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr1 hr2 hr hr3
    have hr : ρ ≤ r := hr
    have hr0 : 0 < r := hρ.trans_le hr
    obtain ⟨e1, e2, e3, e4, e5⟩ := hN r hr hr3
    have h6 := hbb r hr hr3
    have h7 : N r a = c i * r ^ i := by rw [hc r hr hr3, hr1]
    rw [hab, add_eq_of_lt _ e2 e3 (by rw [h7]; exact (hz r hr hr3).trans_lt hr2), h7] at h6
    rw [zpow_sub₀ hr0.ne', zpow_natCast, zpow_natCast, ← mul_div_assoc, h6]
    field_simp
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 h5
  obtain ⟨σ, hσ, hσ1⟩ := exists_between hρ1
  refine ⟨min u σ, c i, (i : ℤ) - k, lt_min hu hσ, (min_le_right _ _).trans_lt hσ1, hci, fun r hr hr' => ?_⟩
  exact hsub ⟨hr.le, hr'.trans_le (min_le_left _ _)⟩ ((hr'.trans_le (min_le_right _ _)).trans hσ1)

variable (l : ℕ) [Fact l.Prime]

theorem untilt_zero : (0 : Per.Fl l).untilt = 0 :=
  Perfection.teichmuller_zero

theorem exists_pow_mul_eq (s : Per.Acris0 l) : ∃ (k : ℕ) (a : Per.Ainf l),
    (l : Per.Acris l) ^ k * algebraMap (Per.Acris0 l) (Per.Acris l) s = algebraMap (Per.Ainf l) (Per.Acris l) a := by
  obtain ⟨k, a, h⟩ := IsLocalization.Away.surj (l : Per.Ainf l) (s : Per.AinfP l)
  refine ⟨k, a, ?_⟩
  have h1 : (l : Per.Acris0 l) ^ k * s = algebraMap (Per.Ainf l) (Per.Acris0 l) a := by
    apply Subtype.ext
    rw [map_natCast, mul_comm] at h
    simpa using h
  have h2 : algebraMap (Per.Ainf l) (Per.Acris l) a =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) :=
    GlobalTheory.RingIface.tower (l := l) a
  rw [h2, ← h1, map_mul, map_pow, map_natCast]

theorem gauss_l {r : ℝ} (hr : 0 ≤ r) :
    (⨆ n : ℕ, ‖((((l : Per.Ainf l).coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) = r := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have h : ∀ n : ℕ, ‖((((l : Per.Ainf l).coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n
      = if n = 1 then r else 0 := by
    intro n
    rw [WittVector.coeff_p]
    split_ifs with h
    · subst h
      simp
    · rw [untilt_zero]
      have : (1 : ℝ) / (l : ℝ) ^ n ≠ 0 := by positivity
      simp only [ZeroMemClass.coe_zero, norm_zero, Real.zero_rpow this, zero_mul]
  simp only [h]
  have hall : ∀ n : ℕ, (if n = 1 then r else 0) ≤ r := fun n => by split_ifs <;> simp [hr]
  exact le_antisymm (ciSup_le hall)
    (le_ciSup_of_le (f := fun n : ℕ => if n = 1 then r else 0) ⟨_, Set.forall_mem_range.2 hall⟩ 1 (by simp))

end GlobalTheory.GaussSlope

namespace GlobalTheory.MemLoc
open GlobalTheory.GaussSlope

theorem gauss_slope : ∀ (l : ℕ) [Fact l.Prime] (N : ℝ → Per.Acris l → ℝ), (∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ x, 0 ≤ N r x ∧ N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧ (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ ∀ a : Per.Ainf l, N r (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ b : Per.Acris l, N (l : ℝ)⁻¹ b ≠ 0 → ∃ (r₁ c : ℝ) (k : ℤ), (l : ℝ)⁻¹ < r₁ ∧ r₁ < 1 ∧ 0 < c ∧ ∀ r, (l : ℝ)⁻¹ < r → r < r₁ → N r b = c * r ^ k := by
  intro l _ N hN b hb
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hρ : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hρ1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  refine slope_abstract (l : Per.Acris l) hρ hρ1 N (fun r hr hr1 => ?_) b
    (lt_of_le_of_ne ((hN _ le_rfl hρ1).1 b).1 hb.symm) fun n => ?_
  · obtain ⟨e1, e2, e3, e4, e5⟩ := hN r hr hr1
    refine ⟨fun x => (e1 x).2, e2, e3, e4, ?_⟩
    rw [← map_natCast (algebraMap (Per.Ainf l) (Per.Acris l)) l, e5, gauss_l l (hρ.le.trans hr)]
  · obtain ⟨s, z, h⟩ := (acris_basic l).2.2.1 b n
    obtain ⟨k, a, ha⟩ := exists_pow_mul_eq l s
    refine ⟨k, _, z, fun n => ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n), ?_,
      fun n => by positivity, fun n => ?_, fun r hr hr1 => (hN r hr hr1).2.2.2.2 a⟩
    · rw [h, mul_add, ha, pow_add, mul_assoc]
    · exact Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity)

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisGaussNormEventuallyMonomialStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_gauss_norm_eventually_monomial : ∀ (l : ℕ) [Fact l.Prime] (N : ℝ → Per.Acris l → ℝ), (∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ x, 0 ≤ N r x ∧ N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧ (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ ∀ a : Per.Ainf l, N r (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ b : Per.Acris l, N (l : ℝ)⁻¹ b ≠ 0 → ∃ (r₁ c : ℝ) (k : ℤ), (l : ℝ)⁻¹ < r₁ ∧ r₁ < 1 ∧ 0 < c ∧ ∀ r, (l : ℝ)⁻¹ < r → r < r₁ → N r b = c * r ^ k := by
  first | exact @GlobalTheory.MemLoc.gauss_slope | exact GlobalTheory.MemLoc.gauss_slope | (intros; apply GlobalTheory.MemLoc.gauss_slope <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionLines
noncomputable section

namespace GlobalTheory.SenLines

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc TensorProduct PowerSeries

section Series

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M]

def serAct (f : F⟦X⟧) (y : ℤ → M) : ℤ → M := fun m => ∑ᶠ j : ℕ, coeff j f • y (m - j)

def serLine (u : ℤ) (d : M) (c : F⟦X⟧) : ℤ → M :=
  fun m => if 0 ≤ m + u then coeff (m + u).toNat c • d else 0

theorem serAct_one (y : ℤ → M) : serAct (1 : F⟦X⟧) y = y := by
  funext m
  rw [serAct, finsum_eq_single _ 0 (fun j hj => by rw [coeff_one, ite_eq_right hj, zero_smul])]
  simp

def SpanIsLines {N : Type} (L : N → ℤ → M) {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (F : Type) [Field F]
    [Module F M] : Prop :=
  ∀ y : ℤ → M, (∃ (s : ℕ) (x : Fin s → N) (f : Fin s → F⟦X⟧), y = ∑ j, serAct (f j) (L (x j))) ↔
    ∃ c : Fin r → F⟦X⟧, y = ∑ k, serLine (u k) (d k) (c k)

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def LinesAt (i : ZMod n) (ζ : LL) (U : Multiset ℤ) : Prop :=
  ∃ (u : Fin (Module.finrank LL T.V) → ℤ) (d : Fin (Module.finrank LL T.V) → T.V ⊗[Qp] BdR),
    Finset.univ.val.map u = U ∧ LinearIndependent LL d ∧ SpanIsLines (W.levN T i ζ) u d LL

def QFrame (g : W.Gam) (J : O⟦X⟧ →ₐ[O] O⟦X⟧) : Prop :=
  Function.Injective J ∧
  (∀ a, (∃ b, J b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a) ∧
  J X = W.π₀₁ + ((PD.p : ℕ) : O⟦X⟧) ∧
  (∀ c, constantCoeff (J c) = 0 → X - ((PD.p : ℕ) : O⟦X⟧) ∣ c) ∧
  (∃ s : (O⟦X⟧)ˣ, W.γ₀ g (J X) = J X * J s ∧ X - ((PD.p : ℕ) : O⟦X⟧) ∣ (s : O⟦X⟧) - 1) ∧
  Associated (J X) W.q₀ ∧
  IsUnit (algebraMap (LetA O n) W.EE (W.π₀ + ((PD.p : ℕ) : LetA O n)))

end Generic

end GlobalTheory.SenLines
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixedIffMemCompletedIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumMulLeftTransversal
namespace GlobalTheory.LeftTransversalSum

theorem sum_mul_left_transversal {G M : Type} [Group G] [AddCommMonoid M] (H N : Subgroup G)
    (S : Finset G) (hS : ∀ s ∈ S, s ∈ H) (huniq : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ N)
    (f : G → M) (hf : ∀ (g n : G), n ∈ N → f (g * n) = f g) :
    ∀ h ∈ H, ∑ s ∈ S, f (h * s) = ∑ s ∈ S, f s := by
  intro h hh
  have hex : ∀ s : G, ∃ t : G, s ∈ S → t ∈ S ∧ t⁻¹ * (h * s) ∈ N := by
    intro s
    by_cases hs : s ∈ S
    · obtain ⟨t, ht, -⟩ := huniq _ (H.mul_mem hh (hS s hs))
      exact ⟨t, fun _ => ht⟩
    · exact ⟨s, fun h' => absurd h' hs⟩
  choose σ hσ using hex
  have uniq : ∀ x ∈ H, ∀ t ∈ S, ∀ t' ∈ S, t⁻¹ * x ∈ N → t'⁻¹ * x ∈ N → t = t' :=
    fun x hx t ht t' ht' h1 h2 => (huniq x hx).unique ⟨ht, h1⟩ ⟨ht', h2⟩
  refine Finset.sum_nbij σ (fun s hs => (hσ s hs).1) ?_ ?_ ?_
  · intro s hs s' hs' he
    have n1 := (hσ s hs).2
    have n2 := (hσ s' hs').2
    rw [← he] at n2
    have hss : s⁻¹ * s' ∈ N := by
      convert N.mul_mem (N.inv_mem n1) n2 using 1
      group
    exact uniq s' (hS s' hs') s hs s' hs' hss (by simp)
  · intro t ht
    obtain ⟨s, ⟨hs, hsN⟩, -⟩ := huniq (h⁻¹ * t) (H.mul_mem (H.inv_mem hh) (hS t ht))
    refine ⟨s, hs, ?_⟩
    refine uniq (h * s) (H.mul_mem hh (hS s hs)) _ (hσ s hs).1 t ht (hσ s hs).2 ?_
    convert N.inv_mem hsN using 1
    group
  · intro s hs
    have e := hf (σ s) ((σ s)⁻¹ * (h * s)) (hσ s hs).2
    rw [mul_inv_cancel_left] at e
    exact e

end GlobalTheory.LeftTransversalSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixedIffMemCompletedIntegers
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.CycInvariants

theorem exists_reps {G : Type} [Group G] (H N : Subgroup G) [(N.subgroupOf H).FiniteIndex] :
    ∃ S : Finset G, (∀ s ∈ S, s ∈ H) ∧ ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N := by
  classical
  have : Fintype (H ⧸ N.subgroupOf H) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : H ⧸ N.subgroupOf H => ((q.out : H) : G)), ?_, ?_⟩
  · intro s hs
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
    exact q.out.2
  · intro h hh
    refine ⟨((QuotientGroup.mk (⟨h, hh⟩ : H) : H ⧸ N.subgroupOf H).out : H),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · have h1 := QuotientGroup.out_eq' (QuotientGroup.mk (⟨h, hh⟩ : H) : H ⧸ N.subgroupOf H)
      have h2 := QuotientGroup.eq.1 h1
      simpa [Subgroup.mem_subgroupOf] using h2
    · rintro s ⟨hs, hsN⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hs
      have : (QuotientGroup.mk q.out : H ⧸ N.subgroupOf H) = QuotientGroup.mk (⟨h, hh⟩ : H) :=
        QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using hsN)
      rw [QuotientGroup.out_eq'] at this
      rw [this]

theorem sum_reps_invariant {G M : Type} [Group G] [AddCommMonoid M] (H N : Subgroup G)
    (S : Finset G) (hS : ∀ s ∈ S, s ∈ H) (hu : ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N)
    (f : G → M) (hf : ∀ g, ∀ n ∈ N, f (g * n) = f g) (h : G) (hh : h ∈ H) :
    ∑ s ∈ S, f (h * s) = ∑ s ∈ S, f s := by
  first
  | exact @_root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal
  | exact _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal
  | (apply _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal ..)

variable {l : ℕ} [Fact l.Prime]

theorem stabilizer_finiteIndex (x : Om l) : (MulAction.stabilizer (GQ l) x).FiniteIndex := by
  refine ⟨?_⟩
  rw [MulAction.index_stabilizer]
  have hint : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hfin : (MulAction.orbit (GQ l) x).Finite := by
    refine ((minpoly ℚ_[l] x).rootSet_finite (Om l)).subset ?_
    rintro _ ⟨g, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    change Polynomial.aeval (g x) _ = 0
    rw [Polynomial.aeval_algEquiv]
    simp
  exact ((Set.ncard_pos hfin).2 ⟨x, MulAction.mem_orbit_self x⟩).ne'

theorem exists_field (F : IntermediateField ℚ_[l] (Om l)) (x : Om l) :
    ∃ (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l)), x ∈ L ∧ F ≤ L ∧
      (∀ h ∈ F.fixingSubgroup, ∀ x ∈ L, h x ∈ L) ∧ (∀ s ∈ S, s ∈ F.fixingSubgroup) ∧
      (∀ h ∈ F.fixingSubgroup, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) := by
  have := stabilizer_finiteIndex x
  set N := (MulAction.stabilizer (GQ l) x).normalCore with hN
  set L := IntermediateField.fixedField (F.fixingSubgroup ⊓ N) with hL
  have hle : F.fixingSubgroup ⊓ N ≤ L.fixingSubgroup :=
    (IntermediateField.le_iff_le _ _).1 le_rfl
  have hfi : (L.fixingSubgroup.subgroupOf F.fixingSubgroup).FiniteIndex := by
    refine Subgroup.finiteIndex_of_le (H := N.subgroupOf F.fixingSubgroup) ?_
    intro g hg
    exact hle ⟨g.2, hg⟩
  obtain ⟨S, hS, hu⟩ := exists_reps F.fixingSubgroup L.fixingSubgroup
  refine ⟨L, S, ?_, ?_, ?_, hS, hu⟩
  · rw [hL, IntermediateField.mem_fixedField_iff]
    intro g hg
    exact Subgroup.normalCore_le _ hg.2
  · exact (IntermediateField.le_iff_le _ _).2 inf_le_left
  · intro h hh y hy
    rw [hL, IntermediateField.mem_fixedField_iff] at hy ⊢
    intro g hg
    have h1 : h⁻¹ * g * h ∈ F.fixingSubgroup ⊓ N :=
      ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) hg.1) hh,
        by simpa using (Subgroup.normalCore_normal _).conj_mem g hg.2 h⁻¹⟩
    have h2 := congrArg h (hy _ h1)
    simpa using h2

theorem fixed_iff_mem_Ohat : ∀ (l : ℕ) [Fact l.Prime]
    (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act →
    ∀ (K : FinExt l) (y : PadicComplex l), ‖y‖ ≤ 1 →
      ((∀ h ∈ Hinf K, act h y = y) ↔ y ∈ Ohat K) := by
  intro l _ act hact K y hy
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  constructor
  · intro hfix
    rw [Ohat, Metric.mem_closure_iff]
    intro ε hε
    set δ : ℝ := min (ε / 2) 1 with hδ
    have hδ0 : 0 < δ := lt_min (by linarith) one_pos
    obtain ⟨x, hx⟩ := (UniformSpace.Completion.denseRange_coe (α := Om l)).exists_dist_lt y
      (div_pos hδ0 hl0)
    rw [dist_eq_norm] at hx
    obtain ⟨L, S, hxL, hKL, hst, hS, hu⟩ := exists_field (Kinf K) x
    have hnl : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
      rw [← map_natCast (algebraMap ℚ_[l] (Om l))]
      exact (PadicAlgCl.norm_extends l _).trans Padic.norm_p
    have hlne : (l : Om l) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
    obtain ⟨b, hbL, hb1, hb⟩ := GlobalTheory.T.cyclotomicTower_trace_almost_surjective l K L S hKL hst hS hu (l : Om l)
      (natCast_mem _ _) (by rw [hnl]; exact inv_lt_one_of_one_lt₀ hl1)
    set w : Om l := ∑ s ∈ S, s (b * x) with hw
    have hwK : w ∈ Kinf K := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup (Kinf K), IntermediateField.mem_fixedField_iff]
      intro h hh
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hw, map_sum]
      refine sum_reps_invariant _ _ S hS hu (fun g => g (b * x)) ?_ h hh
      intro g n hn
      have := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hn _ (L.mul_mem hbL hxL)
      simp only [AlgEquiv.mul_apply, this]
    set ι := algebraMap (Om l) (PadicComplex l) with hι
    have hιn : ∀ u, ‖ι u‖ = ‖u‖ := fun u => PadicComplex.norm_extends l u
    have hιa : ∀ g u, act g (ι u) = ι (g u) := hact.1
    have hdiff : ι l * y - ι w = ∑ s ∈ S, act s (ι b * (y - ι x)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hb, hw, map_sum, map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [map_mul (act s), map_sub, hfix s (hS s hs), hιa, hιa, map_mul, map_mul, mul_sub]
    have hle : ‖ι l * y - ι w‖ ≤ δ / l := by
      rw [hdiff]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_pos hδ0 hl0).le ?_
      intro s _
      rw [hact.2, norm_mul, hιn]
      calc ‖b‖ * ‖y - ι x‖ ≤ 1 * (δ / l) := mul_le_mul hb1 hx.le (norm_nonneg _) one_pos.le
        _ = δ / l := one_mul _
    have hle' : ‖y - ι (w / l)‖ ≤ δ := by
      have h1 : ι l * y - ι w = ι l * (y - ι (w / l)) := by
        rw [mul_sub, ← map_mul, mul_div_cancel₀ _ hlne]
      rw [h1, norm_mul, hιn, hnl, div_eq_inv_mul δ] at hle
      exact le_of_mul_le_mul_left hle (inv_pos.2 hl0)
    refine ⟨ι (w / l), ⟨⟨w / l, div_mem hwK (natCast_mem _ _), rfl⟩, ?_⟩, ?_⟩
    · have h1 : ι (w / l) = y + -(y - ι (w / l)) := by ring
      rw [h1]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy ?_)
      rw [norm_neg]
      exact hle'.trans (min_le_right _ _)
    · rw [dist_eq_norm]
      exact lt_of_le_of_lt (hle'.trans (min_le_left _ _)) (by linarith)
  · intro hyO h hh
    have hc : Continuous (act h) :=
      (AddMonoidHomClass.isometry_of_norm (act h) (hact.2 h)).continuous
    refine closure_minimal (t := {z | act h z = z}) ?_ (isClosed_eq hc continuous_id) hyO
    rintro _ ⟨⟨u, hu, rfl⟩, -⟩
    change act h (u : PadicComplex l) = (u : PadicComplex l)
    rw [hact.1, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh u hu]

end GlobalTheory.CycInvariants
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixedIffMemCompletedIntegersStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act → ∀ (K : FinExt l) (y : PadicComplex l), ‖y‖ ≤ 1 → ((∀ h ∈ Hinf K, act h y = y) ↔ y ∈ Ohat K) := by
  first | exact @GlobalTheory.CycInvariants.fixed_iff_mem_Ohat | exact GlobalTheory.CycInvariants.fixed_iff_mem_Ohat | (intros; apply GlobalTheory.CycInvariants.fixed_iff_mem_Ohat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulEqZeroSemisimpleRep
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulEqZeroSemisimpleRep
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.TrFormNd

theorem eq_zero_of_trace_mul_eq_zero : ∀ (k Γ : Type) [Field k] [CharZero k] [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) k), IsSSRep r → ∀ M ∈ Submodule.span k (Set.range fun g => ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)), (∀ g, (M * ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).trace = 0) → M = 0 := by
  intro k Γ _ _ _ a r hr M hM hg
  have hnd : PI.SSAscent.UnitaryGroupMassFormula.TrNondeg (PI.SSAscent.UnitaryGroupMassFormula.imAlg r) :=
    PI.SSAscent.UnitaryGroupMassFormula.downStep_of PI.SSAscent.UnitaryGroupMassFormula.trace_nilpotent_ascent k Γ a r hr
  refine hnd M ((GlobalTheory.SSCont.mem_imAlg_iff r M).2 hM) fun y hy => ?_
  have hy' := (GlobalTheory.SSCont.mem_imAlg_iff r y).1 hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    exact hg g
  | zero => simp
  | add y z _ _ hy hz => rw [mul_add, Matrix.trace_add, hy, hz, add_zero]
  | smul c y _ hy => rw [Matrix.mul_smul, Matrix.trace_smul, hy, smul_zero]

end GlobalTheory.TrFormNd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulEqZeroSemisimpleRepStatement
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_semisimple_rep : ∀ (k Γ : Type) [Field k] [CharZero k] [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) k), IsSSRep r → ∀ M ∈ Submodule.span k (Set.range fun g => ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)), (∀ g, (M * ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).trace = 0) → M = 0 := by
  first | exact @GlobalTheory.TrFormNd.eq_zero_of_trace_mul_eq_zero | exact GlobalTheory.TrFormNd.eq_zero_of_trace_mul_eq_zero | (intros; apply GlobalTheory.TrFormNd.eq_zero_of_trace_mul_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommOfBezout
open Matrix

namespace GlobalTheory.UnitDiscAlg

section Basic
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

theorem integ_mul {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖(x * y) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.mul_apply]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    (fun k _ => by rw [norm_mul]; exact mul_le_one₀ (hx i k) (norm_nonneg _) (hy k j))

theorem integ_add {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖(x + y) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i j) (hy i j))

theorem integ_sub {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖(x - y) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.sub_apply, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i j) (by rw [norm_neg]; exact hy i j))

theorem integ_one : ∀ i j, ‖(1 : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem integ_zero : ∀ i j, ‖(0 : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1 := by
  intro i j
  simp

theorem integ_pow {x : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (k : ℕ) :
    ∀ i j, ‖(x ^ k) i j‖ ≤ 1 := by
  induction k with
  | zero => simpa using integ_one
  | succ k ih => rw [pow_succ]; exact integ_mul ih hx

theorem integ_smul {x : Matrix (Fin n) (Fin n) E} {a : E} (ha : ‖a‖ ≤ 1) (hx : ∀ i j, ‖x i j‖ ≤ 1) :
    ∀ i j, ‖(a • x) i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) (hx i j)

end Basic

theorem comm_of_bezout {E : Type} [Field E] {n : ℕ} {N a b : Matrix (Fin n) (Fin n) E}
    (h : ∃ u v : Polynomial E, u * N.charpoly + v * Polynomial.derivative N.charpoly = 1)
    (ha : a * N = N * a) (hb : b * N = N * b) : a * b = b * a := by
  obtain ⟨u, v, huv⟩ := h
  have hs : N.charpoly.Separable := ⟨u, v, huv⟩
  obtain ⟨w, hw⟩ := GlobalTheory.RegSS.cyclicField E (Fin n) N hs
  have hbij := (GlobalTheory.RegSS.CycAlg.cyclicAlgebra E (Fin n) N w hw).2.2
  have ha' := GlobalTheory.RegSS.mem_genAlg_of_commute hbij ha
  have hb' := GlobalTheory.RegSS.mem_genAlg_of_commute hbij hb
  exact congrArg Subtype.val
    (mul_comm (⟨a, ha'⟩ : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg N) ⟨b, hb'⟩)

end GlobalTheory.UnitDiscAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusAndExponentModEq
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

open IsLocalRing

theorem modEq_of_pow_modEq_pow_sub_one (l n a b : ℕ) (hl : 2 ≤ l) (hn : 0 < n)
    (h : l ^ a ≡ l ^ b [MOD l ^ n - 1]) : a ≡ b [MOD n] := by
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · have hpos : 1 ≤ l ^ n := Nat.one_le_pow _ _ (by omega)
    have hone : l ^ n ≡ 1 [MOD l ^ n - 1] :=
      ((Nat.modEq_iff_dvd' hpos).2 dvd_rfl).symm
    have hred : ∀ c : ℕ, l ^ c ≡ l ^ (c % n) [MOD l ^ n - 1] := by
      intro c
      conv_lhs => rw [← Nat.div_add_mod c n, pow_add, pow_mul]
      have := (hone.pow (c / n)).mul_right (l ^ (c % n))
      simpa using this
    have hlt : ∀ c : ℕ, l ^ (c % n) < l ^ n - 1 := by
      intro c
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have h2 : l ^ (c % (k + 1)) ≤ l ^ k :=
        Nat.pow_le_pow_right (by omega) (Nat.lt_succ_iff.1 (Nat.mod_lt _ hn))
      have h3 : l ^ 1 ≤ l ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      have h4 : l ^ k * 2 ≤ l ^ k * l := Nat.mul_le_mul_left _ hl
      rw [pow_one] at h3
      rw [pow_succ]
      omega
    have h5 : l ^ (a % n) ≡ l ^ (b % n) [MOD l ^ n - 1] :=
      ((hred a).symm.trans h).trans (hred b)
    have h6 := Nat.ModEq.eq_of_lt_of_lt h5 (hlt a) (hlt b)
    exact Nat.pow_right_injective hl h6
  · obtain rfl : n = 1 := by omega
    exact Nat.modEq_one

theorem exists_frobenius_and_exponent_modEq (l : ℕ) [Fact l.Prime] :
    (∃ φ : GQ l, ∀ n : ℕ, 0 < n → ∀ x : Om l, x ^ l ^ n = x → φ x = x ^ l) ∧
    ∀ n a b : ℕ, 0 < n → (∀ x : Om l, x ^ l ^ n = x → x ^ l ^ a = x ^ l ^ b) →
      a ≡ b [MOD n] := by
  have hp : l.Prime := Fact.out
  have hgt : ∀ n : ℕ, 0 < n → 1 < l ^ n := fun n hn => Nat.one_lt_pow hn.ne' hp.one_lt
  constructor
  · have e : (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) ≃+* ZMod l := PadicInt.residueField
    have : NeZero l := ⟨hp.ne_zero⟩
    have hcard : Nat.card (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = l := by
      rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
    obtain ⟨φ, hφ⟩ := GlobalTheory.MemLoc.exists_algEquiv_rootOfUnity_eq_pow ℤ_[l] ℚ_[l]
      (Finite.of_equiv _ e.symm.toEquiv) (Om l)
    rw [hcard] at hφ
    refine ⟨φ, fun n hn x hx => ?_⟩
    by_cases h0 : x = 0
    · rw [h0, map_zero, zero_pow hp.ne_zero]
    have h1 := hgt n hn
    refine hφ x (l ^ n - 1) (fun h => ?_) ?_
    · rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at h
      have h2 : l ∣ l ^ n := dvd_pow_self l hn.ne'
      have h3 : l ∣ l ^ n - (l ^ n - 1) := Nat.dvd_sub h2 h
      have h4 : l ^ n - (l ^ n - 1) = 1 := by omega
      rw [h4] at h3
      exact hp.one_lt.ne' (Nat.dvd_one.1 h3)
    · apply mul_right_cancel₀ h0
      rw [← pow_succ, one_mul, Nat.sub_add_cancel h1.le, hx]
  · intro n a b hn h
    have h1 := hgt n hn
    have : NeZero (l ^ n - 1) := ⟨by omega⟩
    have : NeZero ((l ^ n - 1 : ℕ) : Om l) := inferInstance
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ n - 1)
    have h2 : ζ ^ l ^ n = ζ := by
      conv_lhs => rw [← Nat.sub_add_cancel h1.le, pow_succ, hζ.pow_eq_one, one_mul]
    have h3 := h ζ h2
    apply modEq_of_pow_modEq_pow_sub_one l n a b hp.two_le hn
    have hfin : IsOfFinOrder ζ := hζ.isOfFinOrder (by omega)
    rw [hζ.eq_orderOf]
    exact hfin.pow_eq_pow_iff_modEq.1 h3

end GlobalTheory.Cyc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTerFurther
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem φc_tc (l : ℕ) [Fact l.Prime] (y : Formalism.Per.Fl l) : φc l (tc l y) = tc l (y ^ l) := by
  unfold φc tc
  rw [(GlobalTheory.CrisMaps.phiA_extends l).alg]
  congr 1
  rw [GlobalTheory.RingBasics.φA_apply, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]

theorem frob_teich : ∀ (l : ℕ) [Fact l.Prime] (y : Formalism.Per.Fl l), φc l (tc l y) = tc l (y ^ l) :=
  fun l _ y => φc_tc l y

end GlobalTheory.PMon.Gauss
end
