module

public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemIffForallMemLocalizeRingOfIntegers
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem _root_.GlobalTheory.scale_poly_comparison : ∀ eps c κ : ℝ, 0 < eps → 0 < κ → ∃ x0 : ℝ, ∀ s : _root_.Formalism.BasicNotions.Scale, s.eps = eps → x0 ≤ s.x → s.x ^ c ≤ Real.exp (s.x ^ (s.eps / 8)) ∧ s.x ^ c ≤ s.X' ^ κ ∧ s.x ^ c * s.X' ≤ s.b ^ κ ∧ s.b' * s.x ^ c ≤ s.b ∧ s.b ^ (1 - κ) * s.x ^ c ≤ s.b' ∧ (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ s.x ^ (3 : ℝ) → s.b ^ (1 - κ) * s.x ^ c ≤ s.w'' n ∧ s.w'' n ≤ s.b' ∧ s.X'' n = s.x * n * s.X') ∧ Real.exp (c * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) * s.x ^ c ≤ s.X' ^ κ := by
  intro eps c κ heps hκ
  obtain ⟨x1, h1⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 8) c 0 1 0 le_rfl
    (by positivity) one_pos
  obtain ⟨x2, h2⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 3) c 0 κ 0 le_rfl
    (by positivity) hκ
  obtain ⟨x3, h3⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 3) eps (c + 3) 1 κ 0
    (by positivity) (by linarith) hκ
  obtain ⟨x4, h4⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 3) (c + 1) 0 1 0 le_rfl
    (by positivity) one_pos
  obtain ⟨x5, h5⟩ := _root_.GlobalTheory.log_add_rpow_mul_log_pow_le_rpow (eps / 5) (eps / 3) |c| |c| κ 2
    (by positivity) (by linarith) hκ
  refine ⟨max (max (max x1 x2) (max x3 x4)) x5, ?_⟩
  intro s hs hx
  subst hs
  have ht : 1 < s.x := s.one_lt_alt
  have ht0 : 0 < s.x := by linarith
  have hlog : 0 ≤ Real.log s.x := Real.log_nonneg ht.le
  have g1 := h1 s.x (le_trans (by simp) hx)
  have g2 := h2 s.x (le_trans (by simp) hx)
  have g3 := h3 s.x (le_trans (by simp) hx)
  have g4 := h4 s.x (le_trans (by simp) hx)
  have g5 := h5 s.x (le_trans (by simp) hx)
  simp only [Real.rpow_zero, pow_zero, mul_one, zero_mul, add_zero, one_mul] at g1 g2 g3 g4
  have hxc : s.x ^ c = Real.exp (Real.log s.x * c) := Real.rpow_def_of_pos ht0 c
  have hX' : s.X' = Real.exp (s.x ^ (s.eps / 3)) := by unfold _root_.Formalism.BasicNotions.Scale.X'; rfl
  have hb : s.b = Real.exp (s.x ^ s.eps) := by unfold _root_.Formalism.BasicNotions.Scale.b _root_.Formalism.BasicNotions.Scale.L; rfl
  have hb'def : s.b' = s.x * s.b / s.X' := by unfold _root_.Formalism.BasicNotions.Scale.b' _root_.Formalism.BasicNotions.Scale.a; rfl
  have hb' : s.b' = Real.exp (Real.log s.x + s.x ^ s.eps - s.x ^ (s.eps / 3)) := by
    rw [hb'def, hb, hX', Real.exp_sub, Real.exp_add, Real.exp_log ht0]
  have hw : ∀ n : ℕ, s.w'' n = s.b' / (s.x * n) := fun n => by unfold _root_.Formalism.BasicNotions.Scale.w''; rfl
  have hX'' : ∀ n : ℕ, s.X'' n = s.x * s.b / s.w'' n := fun n => by
    unfold _root_.Formalism.BasicNotions.Scale.X'' _root_.Formalism.BasicNotions.Scale.a; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxc]
    exact Real.exp_le_exp.2 (by linarith)
  · rw [hxc, hX', ← Real.exp_mul]
    exact Real.exp_le_exp.2 (by linarith)
  · rw [hxc, hX', hb, ← Real.exp_mul, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  · rw [hb', hxc, hb, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  · rw [hb, ← Real.exp_mul, hxc, ← Real.exp_add, hb']
    exact Real.exp_le_exp.2 (by nlinarith)
  · intro n hn hnx
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    refine ⟨?_, ?_, ?_⟩
    · rw [hw, le_div_iff₀ (by positivity), hb, ← Real.exp_mul, hxc]
      calc Real.exp (s.x ^ s.eps * (1 - κ)) * Real.exp (Real.log s.x * c) * (s.x * n)
          ≤ Real.exp (s.x ^ s.eps * (1 - κ)) * Real.exp (Real.log s.x * c) *
              (s.x * s.x ^ (3 : ℝ)) := by gcongr
        _ = Real.exp (s.x ^ s.eps * (1 - κ) + Real.log s.x * c +
              (Real.log s.x + Real.log s.x * 3)) := by
            rw [Real.rpow_def_of_pos ht0 3, Real.exp_add, Real.exp_add, Real.exp_add,
              Real.exp_log ht0]
        _ ≤ s.b' := by
            rw [hb']
            exact Real.exp_le_exp.2 (by nlinarith)
    · rw [hw]
      have hpos : 0 ≤ s.b' := by rw [hb']; positivity
      exact div_le_self hpos (one_le_mul_of_one_le_of_one_le ht.le hn')
    · have hn0 : (n : ℝ) ≠ 0 := by positivity
      have hbne : s.b ≠ 0 := by rw [hb]; positivity
      have hX'ne : s.X' ≠ 0 := by rw [hX']; positivity
      rw [hX'', hw, hb'def]
      field_simp
  · have hY : 0 ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by positivity
    have hA : c * (s.x ^ (s.eps / 5) * Real.log s.x ^ 2) ≤
        |c| * (s.x ^ (s.eps / 5) * Real.log s.x ^ 2) :=
      mul_le_mul_of_nonneg_right (le_abs_self c) hY
    have hB : c * Real.log s.x ≤ |c| * Real.log s.x :=
      mul_le_mul_of_nonneg_right (le_abs_self c) hlog
    have habs : 0 ≤ |c| := abs_nonneg c
    rw [hxc, hX', ← Real.exp_mul, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparisonStatement
open Formalism.BasicNotions Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scale_polynomial_quantities_comparison : ∀ eps c κ : ℝ, 0 < eps → 0 < κ → ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x → s.x ^ c ≤ Real.exp (s.x ^ (s.eps / 8)) ∧ s.x ^ c ≤ s.X' ^ κ ∧ s.x ^ c * s.X' ≤ s.b ^ κ ∧ s.b' * s.x ^ c ≤ s.b ∧ s.b ^ (1 - κ) * s.x ^ c ≤ s.b' ∧ (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ s.x ^ (3 : ℝ) → s.b ^ (1 - κ) * s.x ^ c ≤ s.w'' n ∧ s.w'' n ≤ s.b' ∧ s.X'' n = s.x * n * s.X') ∧ Real.exp (c * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) * s.x ^ c ≤ s.X' ^ κ := by
  first | exact @GlobalTheory.scale_poly_comparison | exact GlobalTheory.scale_poly_comparison | (intros; apply GlobalTheory.scale_poly_comparison <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTopCountLeConstMulLog
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem goodTopCount_le_const_mul_log (r : ℕ) (de h x : ℝ) (hde : 0 < de) (hde1 : de ≤ 1)
    (hh : 0 ≤ h) (hL : 1 ≤ Real.log x) :
    (G.orbitWindowCount r de h x : ℝ) ≤
      (6 * Real.exp 1 * (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) +
        (h + 3) * 2 + 2) * Real.log x := by
  set L := Real.log x with hLdef
  have hu : (G.goodU de : ℝ) * de ≤ 2 := by
    unfold G.goodU
    have h1 : (⌈1 / de⌉₊ : ℝ) < 1 / de + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (⌈1 / de⌉₊ : ℝ) * de ≤ (1 / de + 1) * de := mul_le_mul_of_nonneg_right h1.le hde.le
    have h3 : (1 / de + 1) * de = 1 + de := by field_simp
    linarith
  have hT : (0 : ℝ) < 10 ^ (6 * r + 1) := by positivity
  have hM : (G.orbitSmallMultiplicity r h x : ℝ) + 5 ≤ ((h + 3) * 10 ^ (6 * r + 1) + 6) * L := by
    unfold G.orbitSmallMultiplicity
    have he : (h + 3) * Real.log x / (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ)) =
        (h + 3) * 10 ^ (6 * r + 1) * L := by
      rw [zpow_neg, zpow_natCast, div_inv_eq_mul]; ring
    rw [he]
    have h1 : (⌈(h + 3) * 10 ^ (6 * r + 1) * L⌉₊ : ℝ) < (h + 3) * 10 ^ (6 * r + 1) * L + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    nlinarith
  have hG : (G.goodG' r de h x : ℝ) * de ≤
      (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) * L := by
    unfold G.goodG' G.goodEll
    have he : (((G.orbitSmallMultiplicity r h x + 5) * ((6 * r + 1) * G.goodU de) : ℕ) : ℝ) * de =
        ((G.orbitSmallMultiplicity r h x : ℝ) + 5) * (((6 * r + 1 : ℕ) : ℝ) * ((G.goodU de : ℝ) * de)) := by
      push_cast; ring
    rw [he]
    calc _ ≤ (((h + 3) * 10 ^ (6 * r + 1) + 6) * L) * (((6 * r + 1 : ℕ) : ℝ) * 2) := by
          apply mul_le_mul hM (mul_le_mul_of_nonneg_left hu (by positivity)) (by positivity)
          positivity
      _ = _ := by ring
  have hb : (h + 3) * Real.logb 2 x ≤ (h + 3) * 2 * L := by
    have h2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have : Real.logb 2 x ≤ 2 * L := by
      unfold Real.logb
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left this (by linarith)
  unfold G.orbitWindowCount
  set A := ((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2) with hA
  have hA0 : 0 ≤ A := by positivity
  have hE : 0 < 6 * Real.exp 1 := by positivity
  have h1 : 6 * Real.exp 1 * (G.goodG' r de h x : ℝ) * de ≤ 6 * Real.exp 1 * A * L := by
    rw [mul_assoc (6 * Real.exp 1), mul_assoc (6 * Real.exp 1)]
    exact mul_le_mul_of_nonneg_left hG hE.le
  have h1' : 0 ≤ 6 * Real.exp 1 * A * L := by positivity
  have h2' : 0 ≤ (h + 3) * 2 * L := by positivity
  have hmax : max (6 * Real.exp 1 * (G.goodG' r de h x : ℝ) * de) ((h + 3) * Real.logb 2 x) ≤
      6 * Real.exp 1 * A * L + (h + 3) * 2 * L := max_le (by linarith) (by linarith)
  have hc := Nat.ceil_lt_add_one (a := max (6 * Real.exp 1 * (G.goodG' r de h x : ℝ) * de)
    ((h + 3) * Real.logb 2 x)) (le_max_of_le_left (by positivity))
  rw [Nat.cast_add, Nat.cast_one]
  nlinarith

theorem topCount_and_lambda_bounds : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ CN x0 : ℝ, ∀ s : Scale,
    s.eps = eps → x0 ≤ s.x → 1 ≤ G.N1 s ∧ (G.N1 s : ℝ) ≤ CN * Real.log s.x ∧
      ∀ K : G.Consts, 1 ≤ K.La → s.x ^ s.eps ≤ G.La K s ∧
        G.La K s ≤ K.La * CN ^ 2 * Real.log s.x ^ 2 * (2 * s.x ^ s.eps) := by
  intro eps he _
  obtain ⟨x1, hx1⟩ := Filter.eventually_atTop.1 ((isLittleO_log_rpow_atTop he).bound one_pos)
  set h : ℝ := 2 + 8 * eps with hh
  set r : ℕ := ⌈8 * (h + 2) / eps⌉₊ + 1 with hr
  refine ⟨6 * Real.exp 1 * (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) +
        (h + 3) * 2 + 2, max x1 (Real.exp 1), ?_⟩
  intro s hs hx
  have hx0 : 0 < s.x := lt_trans one_pos s.one_lt_alt
  have hL : 1 ≤ Real.log s.x := by
    rw [Real.le_log_iff_exp_le hx0]; exact le_trans (le_max_right _ _) hx
  have hP : 0 < s.x ^ s.eps := Real.rpow_pos_of_pos hx0 _
  have hlog : Real.log s.x ≤ s.x ^ s.eps := by
    have := hx1 s.x (le_trans (le_max_left _ _) hx)
    rw [one_mul, ← hs, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hP.le] at this
    exact this
  have hhG : G.hG s = h := by unfold G.hG; rw [hs]
  have hrG : G.rG s = r := by unfold G.rG G.KG; rw [hhG, hs]
  have hN1 : 1 ≤ G.N1 s := by unfold G.N1 G.orbitWindowCount; exact Nat.le_add_left _ _
  have hN := goodTopCount_le_const_mul_log r s.delta1 h s.x (Real.rpow_pos_of_pos hx0 _)
    (Real.rpow_le_one_of_one_le_of_nonpos s.one_lt_alt.le (by have := s.eps_pos; linarith))
    (by positivity) hL
  have hNe : G.N1 s = G.orbitWindowCount r s.delta1 h s.x := by unfold G.N1; rw [hhG, hrG]
  rw [← hNe] at hN
  generalize 6 * Real.exp 1 * (((h + 3) * 10 ^ (6 * r + 1) + 6) * (((6 * r + 1 : ℕ) : ℝ) * 2)) +
        (h + 3) * 2 + 2 = CN at hN ⊢
  refine ⟨hN1, hN, fun K hK => ?_⟩
  have ha : Real.log s.a = Real.log s.x + s.x ^ s.eps := by
    unfold Scale.a Scale.b Scale.L
    rw [Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hN1' : (1 : ℝ) ≤ (G.N1 s : ℝ) := by exact_mod_cast hN1
  have hsq : (1 : ℝ) ≤ (G.N1 s : ℝ) ^ 2 := one_le_pow₀ hN1'
  have hsq' : (G.N1 s : ℝ) ^ 2 ≤ (CN * Real.log s.x) ^ 2 := pow_le_pow_left₀ (by linarith) hN 2
  unfold G.La
  rw [ha]
  constructor
  · have h1 : 1 ≤ K.La * (G.N1 s : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hK hsq
    nlinarith
  · calc K.La * (G.N1 s : ℝ) ^ 2 * (Real.log s.x + s.x ^ s.eps)
        ≤ K.La * (CN * Real.log s.x) ^ 2 * (2 * s.x ^ s.eps) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hsq' (by linarith)) (by linarith) (by linarith)
          have : 0 ≤ K.La := by linarith
          positivity
      _ = _ := by ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsPrincipalIdealRingSemiLoc
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.LocalLattice

noncomputable section

namespace GlobalTheory.SemiLocalFrame

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem algebraMapSubmonoid_le :
    Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl ≤ (𝓞 E)⁰ :=
  algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ v.asIdeal.primeCompl_le_nonZeroDivisors

def semiLoc : Subalgebra (𝓞 E) E :=
  Localization.subalgebra.ofField E (Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl)
    (algebraMapSubmonoid_le E v)

instance isLocalization_semiLoc :
    IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl) (semiLoc E v) :=
  Localization.subalgebra.isLocalization_ofField E _ _

instance isFractionRing_semiLoc : IsFractionRing (semiLoc E v) E :=
  Localization.subalgebra.isFractionRing_ofField E _ _

instance isPrincipalIdealRing_semiLoc : IsPrincipalIdealRing (semiLoc E v) :=
  haveI : IsDedekindDomain (semiLoc E v) :=
    IsLocalization.isDedekindDomain (𝓞 E) (algebraMapSubmonoid_le E v) _
  IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 E) v.asIdeal v.ne_bot

variable {E}

theorem mem_span_semiLoc_iff {V : Type*} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (N : Submodule (𝓞 E) V) (x : V) :
    x ∈ Submodule.span (semiLoc E v) (N : Set V) ↔
      ∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • x ∈ N := by
  rw [mem_span_localization_iff (semiLoc E v)
    (Algebra.algebraMapSubmonoid (𝓞 E) v.asIdeal.primeCompl)]
  exact ⟨fun ⟨_, ⟨s, hs, rfl⟩, h⟩ => ⟨s, hs, h⟩, fun ⟨s, hs, h⟩ => ⟨_, ⟨s, hs, rfl⟩, h⟩⟩

theorem exists_of_mem_semiLoc {z : E} (hz : z ∈ semiLoc E v) :
    ∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • z ∈ (1 : Submodule (𝓞 E) E) := by
  have h := mem_span_semiLoc_iff v (1 : Submodule (𝓞 E) E) z
  rw [Submodule.one_eq_span, Submodule.span_span_of_tower, Submodule.mem_span_singleton,
    ← Submodule.one_eq_span] at h
  exact h.1 ⟨⟨z, hz⟩, mul_one z⟩

theorem exists_common {ι : Type*} [Finite ι] {V : Type*} [AddCommGroup V] [Module (𝓞 E) V]
    (N : Submodule (𝓞 E) V) (x : ι → V)
    (h : ∀ i, ∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • x i ∈ N) :
    ∃ s ∉ v.asIdeal, ∀ i, algebraMap (𝓞 F) (𝓞 E) s • x i ∈ N := by
  classical
  haveI := Fintype.ofFinite ι
  choose s hs h using h
  refine ⟨∏ i, s i, (prod_mem (S := v.asIdeal.primeCompl) fun i _ => hs i), fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul, mul_smul]
  exact N.smul_mem _ (h i)

theorem exists_frame {k : ℕ} (L : Submodule (𝓞 E) (Fin k → E)) (h1 : L.FG)
    (h2 : Submodule.span E (L : Set (Fin k → E)) = ⊤) :
    ∃ g : GL (Fin k) E, ∀ x, (∃ s ∉ v.asIdeal, algebraMap (𝓞 F) (𝓞 E) s • x ∈ L) ↔
      ∀ i, (((g⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i ∈ semiLoc E v := by
  haveI : Submodule.IsLattice E (Submodule.span (semiLoc E v) (L : Set (Fin k → E))) := by
    constructor
    · obtain ⟨s, rfl⟩ := h1
      exact ⟨s, (Submodule.span_span_of_tower (𝓞 E) _ _).symm⟩
    · exact fun _ _ => (LinearIndependent.iff_fractionRing (semiLoc E v) E).mp
  haveI : Submodule.IsFullLattice E (Submodule.span (semiLoc E v) (L : Set (Fin k → E))) := by
    constructor
    rw [Submodule.span_span_of_tower, h2]
  obtain ⟨g, hg⟩ := exists_eq_frameLattice (Submodule.span (semiLoc E v) (L : Set (Fin k → E)))
  refine ⟨g, fun x => ?_⟩
  rw [← mem_span_semiLoc_iff, hg, mem_frameLattice_iff_inv]
  exact forall_congr' fun i =>
    Submodule.mem_one.trans ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

theorem smul_eq (c : 𝓞 F) (z : E) :
    algebraMap (𝓞 F) (𝓞 E) c • z = algebraMap F E (c : F) * z := by
  rw [Algebra.smul_def]; rfl

theorem exists_frame_denominator (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (Fin k → E)) = ⊤) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (B : GL (Fin k) E) (c : 𝓞 F), c ∉ v.asIdeal ∧
      (∀ x ∈ Λ, ∀ i, algebraMap F E (c : F) *
        (((B⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i ∈
          (algebraMap (𝓞 E) E).range) ∧
      ∀ j, (fun i => algebraMap F E (c : F) * (B : Matrix (Fin k) (Fin k) E) i j) ∈ Λ := by
  have hfg : Λ.FG := Module.Finite.iff_fg.1 hfin
  obtain ⟨g, hg⟩ := exists_frame v Λ hfg hspan
  obtain ⟨S, hS⟩ := hfg
  have hone : (1 : 𝓞 F) ∉ v.asIdeal := (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top
  obtain ⟨a, ha, hA⟩ := exists_common v (ι := S × Fin k) (1 : Submodule (𝓞 E) E)
    (fun p => (((g⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ (p.1 : Fin k → E)) p.2)
    (fun p => exists_of_mem_semiLoc v ((hg _).1 ⟨1, hone, by
      rw [map_one, one_smul, ← hS]; exact Submodule.subset_span p.1.2⟩ p.2))
  obtain ⟨b, hb, hB⟩ := exists_common v Λ
    (fun j : Fin k => fun i => (g : Matrix (Fin k) (Fin k) E) i j) (fun j => by
      refine (hg _).2 fun i => ?_
      have : (((g⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ
          (fun k => (g : Matrix _ _ E) k j)) i = (1 : Matrix (Fin k) (Fin k) E) i j := by
        rw [← Units.inv_mul g]; rfl
      rw [this, Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _])
  refine ⟨g, b * a, fun h => (v.isPrime.mem_or_mem h).elim hb ha, fun x hx i => ?_, fun j => ?_⟩
  · have key : algebraMap (𝓞 F) (𝓞 E) a •
        (((g⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i ∈ (1 : Submodule (𝓞 E) E) := by
      rw [← hS] at hx
      induction hx using Submodule.span_induction with
      | mem y hy => exact hA (⟨y, hy⟩, i)
      | zero => simp
      | add y z _ _ hy hz => rw [Matrix.mulVec_add, Pi.add_apply, smul_add]; exact add_mem hy hz
      | smul r y _ hy =>
        rw [Matrix.mulVec_smul, Pi.smul_apply, smul_comm]; exact Submodule.smul_mem _ _ hy
    have := Submodule.smul_mem _ (algebraMap (𝓞 F) (𝓞 E) b) key
    rw [← mul_smul, ← map_mul, smul_eq] at this
    exact Submodule.mem_one.1 this
  · have := Λ.smul_mem (algebraMap (𝓞 F) (𝓞 E) a) (hB j)
    rw [← mul_smul, ← map_mul, mul_comm a b] at this
    convert this using 1
    funext i
    rw [Pi.smul_apply, smul_eq]

end GlobalTheory.SemiLocalFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OneLeLetterBlockLength
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory.HCEntries

variable {D : D7} {L : SizeData₂ D}

theorem one_le_scL (L : SizeData₂ D) : 1 ≤ L.sc.L :=
  Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_b (L : SizeData₂ D) : 1 ≤ L.sc.b :=
  Real.one_le_exp (by linarith [one_le_scL L])

theorem b'_pos (L : SizeData₂ D) : 0 < L.sc.b' := by
  have := L.sc.one_lt_alt
  have := one_le_b L
  unfold Scale.b' Scale.a Scale.X'
  positivity

theorem one_le_n (D : D7) : (1 : ℝ) ≤ D.R.n := by
  have : 1 ≤ D.R.n := by unfold Ranks.n; exact D.R.ord_pos
  exact_mod_cast this

theorem one_le_k (D : D7) : (1 : ℝ) ≤ D.R.k := by
  have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  exact_mod_cast this

theorem one_le_letterBlockLength (D : D7) : (1 : ℝ) ≤ D.R.t := by
  have : 1 ≤ D.R.t := by have := D.R.three_m_lt_t; omega
  exact_mod_cast this

theorem eta_k_le (h : SizeEta L) : L.etaSz ≤ L.sc.b ∧ (D.R.k : ℝ) ≤ L.sc.b := by
  obtain ⟨h1, h2, -⟩ := h
  have hk := one_le_k D
  have ht := one_le_letterBlockLength D
  have hf : (1 : ℝ) ≤ D.R.f := by
    have := one_le_n D
    unfold Ranks.f
    push_cast
    linarith
  have hk3 : (D.R.k : ℝ) ≤ (D.R.k : ℝ) ^ 3 := le_self_pow₀ hk (by norm_num)
  have htf : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f := one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht) hf
  have hP : (D.R.k : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 :=
    hk3.trans (le_mul_of_one_le_left (by positivity) htf)
  rw [le_div_iff₀ (by linarith)] at h2
  constructor <;> nlinarith

theorem b'_Sc_le (h : SizeLstar L) : L.sc.b' + L.Sc ≤ L.sc.b := by
  have hk := one_le_k D
  have ht := one_le_letterBlockLength D
  have hn := one_le_n D
  have hL := one_le_scL L
  have hb := one_le_b L
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hmt : (D.R.m : ℝ) ≤ D.R.t := by
    have : D.R.m ≤ D.R.t := by have := D.R.three_m_lt_t; omega
    exact_mod_cast this
  have h0 : 0 ≤ szlStar L := by unfold szlStar; positivity
  have h1 : szlStar L ≤ L.sc.b := by
    unfold szlStar
    rw [div_le_iff₀ (by positivity), mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have e1 : (1 : ℝ) ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hk (one_le_pow₀ hn)
    have e2 : L.Sc + D.R.t + L.sc.L ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) :=
      le_mul_of_one_le_left (by positivity) e1
    have e3 : 0 ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 := by positivity
    linarith
  have h2 : 0 ≤ L.sc.b / szlStar L := div_nonneg (by linarith) h0
  linarith [h.1]

theorem bT_le (hLa : SizeLa L) (hR : SizeRho L) (hB : SizeBot L) (t : D.host.TT) :
    (L.bT t : ℝ) ≤ 5 / 4 * L.sc.b' := by
  have hx := L.sc.one_lt_alt
  have hk := one_le_k D
  have hb := b'_pos L
  have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_nonneg (by linarith) _) hLa.1
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx.le
  have h1 : 0 ≤ L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k := by positivity
  have h2 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
  unfold SizeRho at hR
  have h3 : szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
    have : 4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
        4 * (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
    linarith
  have h4 := hB t
  have h5 : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
  have h6 := mul_le_mul_of_nonneg_right h3 hb.le
  linarith

theorem aT_le (L : SizeData₂ D) (t : D.host.TT) : (L.aT t : ℝ) ≤ 2 * L.sc.x * L.sc.b := by
  have hx := L.sc.one_lt_alt
  have hb := one_le_b L
  have h1 := (L.aT_win t).2
  have h2 : (1 : ℝ) ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) :=
    one_le_mul_of_one_le_of_one_le (one_le_k D) (Real.one_le_rpow hx.le (by unfold Scale.A; norm_num))
  have h3 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a :=
    div_le_self (by unfold Scale.a; positivity) h2
  have h4 : L.sc.a = L.sc.x * L.sc.b := rfl
  linarith

theorem exists_top {τ : D.what₂.Tau} (h : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces) :
    ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t := by
  unfold Host.topPlaces at h
  obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 h
  exact ⟨⟨t, ht⟩, hte.symm⟩

theorem wj_bounds (h : SizesAt L) (hx : 2 ≤ L.sc.x) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) :
    0 ≤ wj D j τ ∧ wj D j τ ≤ 3 * L.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hR, hB, -, -, hE, -, hS, -⟩ := h
  have hb := one_le_b L
  have hb' := b'_pos L
  have he := (eta_k_le hE).1
  have hbb : L.sc.b' ≤ L.sc.b := by linarith [b'_Sc_le hS, L.Sc_pos]
  by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht⟩ := exists_top ha
    obtain ⟨a1, a2⟩ := L.win_top j h1 h2 τ t ht
    have a3 := L.bT_ge t
    have a4 := bT_le hLa hR hB t
    have a5 : 0 ≤ L.sc.b' / L.sc.x := by positivity
    have a6 : L.sc.b' / L.sc.x ≤ L.sc.b' / 2 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx
    constructor <;> linarith
  · by_cases hc : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · obtain ⟨a1, a2⟩ := L.win_thick j h1 h2 τ hc
      constructor <;> linarith
    · obtain ⟨a1, a2⟩ := L.win_thin j h1 h2 τ ⟨(D.eTau τ).2, ha, hc⟩
      have hn := one_le_n D
      have a5 : 0 ≤ L.sc.w'' D.R.n := by unfold Scale.w''; positivity
      have a6 : L.sc.w'' D.R.n ≤ L.sc.b' :=
        div_le_self hb'.le (one_le_mul_of_one_le_of_one_le (by linarith) hn)
      constructor <;> linarith

theorem b_bounds (h : SizesAt L) (hx : 2 ≤ L.sc.x) (τ : D.what₂.Tau) (j : Fin D.R.m) :
    -L.sc.b ≤ (((D.hc τ).b j : ℚ) : ℝ) ∧ (((D.hc τ).b j : ℚ) : ℝ) ≤ 3 * L.sc.b := by
  obtain ⟨a1, a2⟩ := wj_bounds h hx (j.1 + 1) (by omega) j.2 τ
  have hw : wj D (j.1 + 1) τ = (((D.hc τ).e j : ℚ) : ℝ) := by
    unfold wj
    rw [dite_eq_left (by simp)]
    rfl
  rw [hw] at a1 a2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -⟩ := h
  have he := (eta_k_le hE).1
  have a3 := abs_le.1 (L.be_close τ j j)
  have a4 : (D.hc τ).b j ≤ (D.hc τ).e j := by
    have := (D.hc τ).gap_be j
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  have a5 : (((D.hc τ).b j : ℚ) : ℝ) ≤ (((D.hc τ).e j : ℚ) : ℝ) := by exact_mod_cast a4
  push_cast at a3
  constructor <;> linarith [a3.1]

theorem sigPar_bound (h : SizesAt L) (hx : 2 ≤ L.sc.x) (τ : D.what₂.Tau) (l : ℕ) :
    |((sigPar D τ l : ℚ) : ℝ)| ≤ 4 * L.sc.b := by
  have hb := one_le_b L
  have hS : L.Sc ≤ L.sc.b := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hS, -⟩ := h
    linarith [b'_Sc_le hS, b'_pos L]
  unfold sigPar
  split_ifs with h1 h2
  · obtain ⟨a1, a2⟩ := L.cloud_v τ ⟨l, h1⟩
    rw [abs_le]
    constructor <;> linarith
  · obtain ⟨a1, a2⟩ := b_bounds h hx τ ⟨_, h2⟩
    rw [abs_le]
    push_cast
    constructor <;> linarith
  · simp only [Rat.cast_zero, abs_zero]
    linarith

theorem u_bound (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (l : Fin D.R.k) : |(((D.hcW u τ).u l : ℚ) : ℝ)| ≤ 4 * L.sc.x * L.sc.b := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hm := D.R.two_le_m
  have hb := one_le_b L
  have hxb : 2 * L.sc.b ≤ L.sc.x * L.sc.b := mul_le_mul_of_nonneg_right hx (by linarith)
  have hb1 := b_bounds h hx τ ⟨0, by omega⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -, hS, -⟩ := h
  have hkb := (eta_k_le hE).2
  have hS : L.Sc ≤ L.sc.b := by linarith [b'_Sc_le hS, b'_pos L]
  obtain ⟨r, hr⟩ := l
  rw [abs_le]
  by_cases h0 : r = 0
  · subst h0
    rw [D.hcW_first u τ hr]
    have h2 := L.cloud_v τ ⟨0, by omega⟩
    have h3 : (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨0, hr⟩ : ℚ) : ℝ) := by
      exact_mod_cast (D.hc τ).u_gt_v ⟨0, by omega⟩
    refine ⟨by linarith [h2.1], ?_⟩
    by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht⟩ := exists_top ha
      rw [(L.top_u τ t hr ht).1]
      linarith [aT_le L t]
    · have h1 := P.cloud_place_bound τ (by omega) ha
      push_cast at h1
      linarith [h2.2]
  · by_cases hl : r + 1 < D.R.k
    · have := L.cloud_u u τ ⟨r, hr⟩ (by show 1 ≤ r; omega) hl
      constructor <;> linarith [this.1, this.2]
    · obtain rfl : r = D.R.k - 1 := by omega
      rw [D.hcW_last u τ (by omega)]
      have h2 := L.cloud_v τ ⟨D.R.k - 2, by omega⟩
      have h3 : -(((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨D.R.k - 1, hr⟩ : ℚ) : ℝ) := by
        exact_mod_cast (D.hc τ).u_last_gt (by omega) (by omega)
      have h4 : (((D.hc τ).u ⟨D.R.k - 1, hr⟩ : ℚ) : ℝ) < (((D.hc τ).v ⟨D.R.k - 2, by omega⟩ : ℚ) : ℝ) := by
        have := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
        have e : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, hr⟩ :=
          Fin.ext (by show D.R.k - 2 + 1 = D.R.k - 1; omega)
        simp only at this
        rw [e] at this
        exact_mod_cast this
      constructor <;> linarith [h2.2, hb1.2]

theorem entries : ∀ (eps : ℝ) (Fm : FamP eps), (∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, (∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ τ, 0 ≤ wj (Fm.D x i) j τ ∧ wj (Fm.D x i) j τ ≤ 3 * (Fm.L x i).sc.b ∧ wSz (Fm.D x i) j τ = wj (Fm.D x i) j τ) ∧ (∀ u τ (l : Fin (Fm.D x i).R.k), |((((Fm.D x i).hcW u τ).u l : ℚ) : ℝ)| ≤ 4 * x * (Fm.L x i).sc.b) ∧ (∀ τ l, |((sigPar (Fm.D x i) τ l : ℚ) : ℝ)| ≤ 4 * (Fm.L x i).sc.b)) := by
  intro eps Fm
  refine ⟨2, fun x hx2 hx i => ?_⟩
  have hS := Fm.sizes x hx i
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have h2 : 2 ≤ (Fm.L x i).sc.x := by rw [hsx]; exact hx2
  refine ⟨fun j hj τ => ?_, fun u τ l => ?_, fun τ l => sigPar_bound hS h2 τ l⟩
  · obtain ⟨h1, hm⟩ := Finset.mem_Icc.1 hj
    obtain ⟨a1, a2⟩ := wj_bounds hS h2 j h1 hm τ
    refine ⟨a1, a2, ?_⟩
    unfold wSz wj
    rw [dite_eq_left ⟨h1, hm⟩, dite_eq_left (by omega)]
  · have := u_bound hS (Fm.params x hx i) h2 u τ l
    rwa [hsx] at this

end GlobalTheory.HCEntries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MulVecMemLocLatIffOfFrame
namespace GlobalTheory.OverCompare

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

theorem _root_.GlobalTheory.OverCompare.exists_intV_mul_inclE_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F) (hc : c ∉ v.asIdeal) :
    ∃ u ∈ _root_.Formalism.BasicNotions.intV E v, u * _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F)) = 1 := by
  have hc0 : (c : F) ≠ 0 := by
    intro h
    apply hc
    rw [show c = 0 from RingOfIntegers.coe_eq_zero_iff.mp h]
    exact v.asIdeal.zero_mem
  have hmem : algebraMap F (v.adicCompletion F) (c : F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [_root_.GlobalTheory.LocalLattice.algebraMap_mem_adicCompletionIntegers_iff,
      _root_.GlobalTheory.LocalLattice.mem_localRing_iff]
    refine ⟨c, hc, ?_⟩
    rw [Algebra.smul_def, show algebraMap (𝓞 F) F c = (c : F) from rfl, mul_inv_cancel₀ hc0]
    exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  refine ⟨1 ⊗ₜ[F] algebraMap F (v.adicCompletion F) (c : F)⁻¹, ?_, ?_⟩
  · unfold _root_.Formalism.BasicNotions.intV _root_.Formalism.UG.tensInt _root_.Formalism.UG.intOE
    exact Subring.subset_closure (Or.inr ⟨⟨_, hmem⟩, rfl⟩)
  · unfold _root_.Formalism.UG.inclE
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, ← Algebra.TensorProduct.algebraMap_apply,
      ← Algebra.TensorProduct.algebraMap_apply', ← map_mul, inv_mul_cancel₀ hc0, map_one]

end GlobalTheory.OverCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAddEquivField
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.OverResidue

theorem nonempty_equiv_quot {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (hI : I.IsMaximal) (T : ℕ) (hT : T.Prime) (hc : Nat.card M = T)
    (h0 : ∀ a ∈ I, ∀ m : M, a • m = 0) : Nonempty (M ≃ₗ[R] (R ⧸ I)) := by
  have : Fact T.Prime := ⟨hT⟩
  have : Finite M := Nat.finite_of_card_ne_zero (hc ▸ hT.ne_zero)
  have : Nontrivial M := Finite.one_lt_card_iff_nontrivial.1 (hc ▸ hT.one_lt)
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  let f : R →ₗ[R] M := LinearMap.toSpanSingleton R M m₀
  have hsur : Function.Surjective f := by
    intro m
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 (mem_zmultiples_of_prime_card hc hm₀ (g' := m))
    exact ⟨(n : R), by simp [f, Int.cast_smul_eq_zsmul]⟩
  have hker : I = LinearMap.ker f := by
    refine hI.eq_of_le ?_ fun a ha => h0 a ha m₀
    rw [Ideal.ne_top_iff_one]
    simpa [f] using hm₀
  subst hker
  exact ⟨(f.quotKerEquivOfSurjective hsur).symm⟩

theorem exists_addEquiv_field {R M k : Type} [CommRing R] [AddCommGroup M] [Module R M] [Field k]
    (ρ : R →+* k) (hρ : Function.Surjective ρ) (e : M ≃ₗ[R] (R ⧸ RingHom.ker ρ)) :
    ∃ ε : M ≃+ k, ∀ (a : R) (m : M), ε (a • m) = ρ a * ε m := by
  refine ⟨e.toAddEquiv.trans (RingHom.quotientKerEquivOfSurjective hρ).toAddEquiv, fun a m => ?_⟩
  show RingHom.quotientKerEquivOfSurjective hρ (e (a • m)) =
      ρ a * RingHom.quotientKerEquivOfSurjective hρ (e m)
  rw [map_smul, Algebra.smul_def, map_mul]
  rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)}

theorem exists_red (p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (hp : ∀ x ∈ intV E v, p x ∈ v.adicCompletionIntegers F)
    (hsur : ∀ a ∈ v.adicCompletionIntegers F, ∃ x ∈ intV E v, p x = a) :
    ∃ ρ : intV E v →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F),
      Function.Surjective ρ ∧ primeOf p = RingHom.ker ρ ∧
      (∀ a : intV E v, a ∈ RingHom.ker ρ ↔ Valued.v (p a) < 1) ∧
      ∀ (a : intV E v) (a' : v.adicCompletionIntegers F), (a' : v.adicCompletion F) = p a →
        ρ a = IsLocalRing.residue _ a' := by
  let q : intV E v →+* v.adicCompletionIntegers F :=
    (p.comp (intV E v).subtype).codRestrict (v.adicCompletionIntegers F) fun x => hp x x.2
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨x, hx, hxa⟩ := hsur a a.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxa⟩
  have hk : ∀ a : intV E v, a ∈ RingHom.ker ((IsLocalRing.residue _).comp q) ↔
      Valued.v (p a) < 1 := by
    intro a
    rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    exact Valuation.mem_maximalIdeal_iff (v := Valued.v) (a := q a)
  refine ⟨(IsLocalRing.residue _).comp q, IsLocalRing.residue_surjective.comp hq, ?_, hk, ?_⟩
  · apply le_antisymm
    · rw [primeOf, Ideal.span_le]
      exact fun a ha => (hk a).2 ha
    · exact fun a ha => Ideal.subset_span ((hk a).1 ha)
  · intro a a' h
    have : q a = a' := Subtype.ext h.symm
    rw [RingHom.comp_apply, this]

theorem residue_of_prime_card : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), IsSplitting σ v s → ∀ (M : Type) [AddCommGroup M] [Module (intV E v) M] (T : ℕ), T.Prime → Nat.card M = T → (∀ (a : intV E v) (m : M), Valued.v (prP s a) < 1 → a • m = 0) → (∃ ε : M ≃+ IsLocalRing.ResidueField (v.adicCompletionIntegers F), ∀ (a : intV E v) (a' : v.adicCompletionIntegers F), (a' : v.adicCompletion F) = prP s a → ∀ m, ε (a • m) = a' • ε m) ∧ Nonempty (M ≃ₗ[intV E v] (intV E v ⧸ primeOf (prP s))) ∧ Nat.card (intV E v ⧸ primeOf (prPbar s)) = T := by
  intro F E _ _ _ _ _ σ v s hs M _ _ T hT hc h0
  obtain ⟨ρ, hρ, hρk, hρm, hρa⟩ := exists_red (prP s) (fun x hx => ((hs.2.2 x).1 hx).1)
    (GlobalTheory.OverCompare.sur_prP hs)
  obtain ⟨ρ', hρ', hρk', -, -⟩ := exists_red (prPbar s) (fun x hx => ((hs.2.2 x).1 hx).2)
    (GlobalTheory.OverCompare.sur_prPbar hs)
  rw [hρk, hρk']
  obtain ⟨e⟩ := nonempty_equiv_quot (M := M) (RingHom.ker ρ) (RingHom.ker_isMaximal_of_surjective ρ hρ)
    T hT hc fun a ha m => h0 a m ((hρm a).1 ha)
  obtain ⟨ε, hε⟩ := exists_addEquiv_field ρ hρ e
  refine ⟨⟨ε, fun a a' h m => ?_⟩, ⟨e⟩, ?_⟩
  · rw [hε, hρa a a' h]
    rfl
  · rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective hρ').toEquiv, ← hc]
    exact (Nat.card_congr ε.toEquiv).symm

end GlobalTheory.OverResidue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsGeneratorsMemCompletedLatticeIff
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsGeneratorsMemCompletedLatticeIff
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.OverCompare

def genSums (F : Type) {E : Type} [Field F] [Field E] [Algebra F E] {k m : ℕ}
    (l : Fin m → Fin k → E) (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R) :
    AddSubgroup (Fin k → E ⊗[F] R) where
  carrier := {u | ∃ t : Fin m → R, (∀ j, t j ∈ S₂) ∧ u = fun i => ∑ j, l j i ⊗ₜ[F] t j}
  zero_mem' := ⟨0, fun _ => zero_mem _, by funext i; simp⟩
  add_mem' := by
    rintro _ _ ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩
    refine ⟨t + t', fun j => add_mem (ht j) (ht' j), ?_⟩
    funext i
    simp [TensorProduct.tmul_add, Finset.sum_add_distrib]
  neg_mem' := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨-t, fun j => neg_mem (ht j), ?_⟩
    funext i
    simp [TensorProduct.tmul_neg, Finset.sum_neg_distrib]

theorem tmul_mem_genSums {F E : Type} [Field F] [Field E] [Algebra F E] {k m : ℕ}
    (l : Fin m → Fin k → E) (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R)
    {x : Fin k → E} (hx : x ∈ Submodule.span ℤ (Set.range l)) {s : R} (hs : s ∈ S₂) :
    (fun i => x i ⊗ₜ[F] s) ∈ genSums F l R S₂ := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
  refine ⟨fun j => c j • s, fun j => zsmul_mem hs _, ?_⟩
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [TensorProduct.smul_tmul]

theorem exists_int_generators {E : Type} [Field E] [NumberField E] {k : ℕ}
    (Λ : Submodule (𝓞 E) (Fin k → E)) [Module.Finite (𝓞 E) Λ] :
    ∃ (m : ℕ) (l : Fin m → Fin k → E), (∀ j, l j ∈ Λ) ∧
      ∀ x ∈ Λ, x ∈ Submodule.span ℤ (Set.range l) := by
  have : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Λ)
  refine ⟨m, fun j => (s j : Fin k → E), fun j => (s j).2, fun x hx => ?_⟩
  have h : (⟨x, hx⟩ : Λ) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 h
  refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  simpa using this

theorem exists_generators_mem_latS_iff :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → ∃ (m : ℕ) (l : Fin m → Fin k → E), (∀ j, l j ∈ Λ) ∧ ∀ (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R) (u : Fin k → E ⊗[F] R), u ∈ latS (F := F) R (tensInt (F := F) R (intOE E) S₂) Λ ↔ ∃ t : Fin m → R, (∀ j, t j ∈ S₂) ∧ u = fun i => ∑ j, l j i ⊗ₜ[F] t j := by
  intro F E _ _ _ _ _ k Λ hΛ
  obtain ⟨m, l, hl, hgen⟩ := exists_int_generators Λ
  refine ⟨m, l, hl, fun R _ _ S₂ u => ⟨fun hu => ?_, ?_⟩⟩
  · show u ∈ genSums F l R S₂
    have hst : ∀ s ∈ tensInt (F := F) R (intOE E) S₂, ∀ v ∈ genSums F l R S₂,
        s • v ∈ genSums F l R S₂ := by
      intro s hs
      induction hs using Subring.closure_induction with
      | mem x hx =>
        rintro _ ⟨t, ht, rfl⟩
        rcases hx with ⟨⟨_, a, rfl⟩, rfl⟩ | ⟨y, rfl⟩
        · have e : ((algebraMap (𝓞 E) E a) ⊗ₜ[F] (1 : R)) • (fun i => ∑ j, l j i ⊗ₜ[F] t j) =
              ∑ j, fun i => (a • l j) i ⊗ₜ[F] t j := by
            funext i
            simp [Finset.mul_sum, Algebra.smul_def]
          rw [show ((algebraMap (𝓞 E) E a) ⊗ₜ[F] (1 : R)) • (fun i => ∑ j, l j i ⊗ₜ[F] t j) =
              ∑ j, fun i => (a • l j) i ⊗ₜ[F] t j from e]
          exact sum_mem fun j _ =>
            tmul_mem_genSums l R S₂ (hgen _ (Λ.smul_mem a (hl j))) (ht j)
        · refine ⟨fun j => (y : R) * t j, fun j => mul_mem y.2 (ht j), ?_⟩
          funext i
          simp [Finset.mul_sum]
      | zero => intro v _; rw [zero_smul]; exact zero_mem _
      | one => intro v hv; rwa [one_smul]
      | add x y _ _ hx hy => intro v hv; rw [add_smul]; exact add_mem (hx v hv) (hy v hv)
      | neg x _ hx => intro v hv; rw [neg_smul]; exact neg_mem (hx v hv)
      | mul x y _ _ hx hy => intro v hv; rw [mul_smul]; exact hx _ (hy v hv)
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact tmul_mem_genSums l R S₂ (hgen y hy) (one_mem _)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact hst a a.2 x hx
  · rintro ⟨t, ht, rfl⟩
    have e : (fun i => ∑ j, l j i ⊗ₜ[F] t j) =
        ∑ j, (⟨(1 : E) ⊗ₜ[F] t j, Subring.subset_closure (Or.inr ⟨⟨t j, ht j⟩, rfl⟩)⟩ :
          tensInt (F := F) R (intOE E) S₂) • (fun i => inclE (F := F) R (l j i)) := by
      funext i
      simp [inclE, Subring.smul_def]
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨l j, hl j, rfl⟩)

end GlobalTheory.OverCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsGeneratorsMemCompletedLatticeIffStatement
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generators_mem_completedLattice_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → ∃ (m : ℕ) (l : Fin m → Fin k → E), (∀ j, l j ∈ Λ) ∧ ∀ (R : Type) [CommRing R] [Algebra F R] (S₂ : Subring R) (u : Fin k → E ⊗[F] R), u ∈ latS (F := F) R (tensInt (F := F) R (intOE E) S₂) Λ ↔ ∃ t : Fin m → R, (∀ j, t j ∈ S₂) ∧ u = fun i => ∑ j, l j i ⊗ₜ[F] t j := by
  first | exact @GlobalTheory.OverCompare.exists_generators_mem_latS_iff | exact GlobalTheory.OverCompare.exists_generators_mem_latS_iff | (intros; apply GlobalTheory.OverCompare.exists_generators_mem_latS_iff <;> assumption)
end
end
