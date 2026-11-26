module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticIntegralTraceFormPerfect
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulStarEqOfNormOneUnramifiedQuadratic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorProperties
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.StdChar

def qe (q : ℚ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (q : ℂ))

theorem qe_add (a b : ℚ) : qe (a + b) = qe a * qe b := by
  simp only [qe, Rat.cast_add, mul_add, Complex.exp_add]

theorem qe_int (n : ℤ) : qe n = 1 := by
  simp only [qe, Rat.cast_intCast]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) = n * (2 * Real.pi * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem qe_eq_one {q : ℚ} (h : qe q = 1) : ∃ n : ℤ, q = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨n, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : (q : ℂ) = n := by
    apply mul_left_cancel₀ h2
    rw [hn]; ring
  exact_mod_cast this

def ce (z : AddCircle (1 : ℚ)) : ℂ :=
  Quotient.liftOn' z qe (fun a b h => by
    rw [QuotientAddGroup.leftRel_apply, AddSubgroup.mem_zmultiples_iff] at h
    obtain ⟨n, hn⟩ := h
    have hb : b = a + n := by rw [zsmul_one] at hn; linarith
    rw [hb, qe_add, qe_int, mul_one])

theorem ce_coe (q : ℚ) : ce (q : AddCircle (1 : ℚ)) = qe q := rfl

theorem ce_add (a b : AddCircle (1 : ℚ)) : ce (a + b) = ce a * ce b := by
  induction a using QuotientAddGroup.induction_on with
  | H a =>
  induction b using QuotientAddGroup.induction_on with
  | H b =>
  rw [← QuotientAddGroup.mk_add]
  exact qe_add a b

theorem ce_zero : ce 0 = 1 := by
  rw [show (0 : AddCircle (1 : ℚ)) = ((0 : ℚ) : AddCircle (1 : ℚ)) by simp, ce_coe]
  simpa using qe_int 0

theorem ce_eq_one {z : AddCircle (1 : ℚ)} (h : ce z = 1) : z = 0 := by
  induction z using QuotientAddGroup.induction_on with
  | H q =>
  obtain ⟨n, hn⟩ := qe_eq_one h
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨n, by simp [hn]⟩

section Field
variable {F : Type} [NontriviallyNormedField F]

def intSub (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] : AddSubgroup F where
  carrier := {x | ‖x‖ ≤ 1}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

theorem mem_intSub [IsUltrametricDist F] {x : F} : x ∈ intSub F ↔ ‖x‖ ≤ 1 := Iff.rfl

def charOf (c : F →+ AddCircle (1 : ℚ)) : AddChar F ℂ where
  toFun x := ce (c x)
  map_zero_eq_one' := by simp [ce_zero]
  map_add_eq_mul' a b := by simp [ce_add]

theorem exists_unif [IsUltrametricDist F] [ProperSpace F] :
    ∃ ϖ : F, ϖ ≠ 0 ∧ ‖ϖ‖ < 1 ∧ ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := by
  have hK : IsCompact (Metric.ball (0 : F) 1) :=
    (isCompact_closedBall (0 : F) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball 0 1)
      Metric.ball_subset_closedBall
  obtain ⟨ϖ, hϖ, hmax⟩ := hK.exists_isMaxOn ⟨0, by simp⟩ continuous_norm.continuousOn
  have hϖ1 : ‖ϖ‖ < 1 := by simpa using hϖ
  have hle : ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖ := fun y hy => hmax (by simpa using hy)
  obtain ⟨z, hz0, hz1⟩ := NormedField.exists_norm_lt_one F
  refine ⟨ϖ, ?_, hϖ1, hle⟩
  intro h
  have := hle z hz1
  rw [h, norm_zero] at this
  linarith

theorem exists_nat_norm_lt_one [IsUltrametricDist F] [ProperSpace F] [CharZero F] :
    ∃ N : ℕ, 0 < N ∧ ‖(N : F)‖ < 1 := by
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : F) 1).tendsto_subseq
    (x := fun n : ℕ => (n : F)) (fun n => by simpa using IsUltrametricDist.norm_natCast_le_one F n)
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq 1 one_pos
  have h := hM (M + 1) (by omega)
  have hlt : φ M < φ (M + 1) := hφ (by omega)
  refine ⟨φ (M + 1) - φ M, by omega, ?_⟩
  rw [Nat.cast_sub hlt.le, ← dist_eq_norm]
  simpa using h

variable (F) in
theorem exists_stdChar [IsUltrametricDist F] [ProperSpace F] : ∃ ψ : AddChar F ℂ, IsStdChar ψ := by
  obtain ⟨ϖ, hϖ0, hϖ1, hle⟩ := exists_unif (F := F)
  have hpos : 0 < ‖ϖ‖ := norm_pos_iff.2 hϖ0
  have hx : (QuotientAddGroup.mk ϖ⁻¹ : F ⧸ intSub F) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff, mem_intSub, norm_inv, not_le]
    exact one_lt_inv_iff₀.2 ⟨hpos, hϖ1⟩
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hx
  let c' : F →+ AddCircle (1 : ℚ) := AddMonoidHom.comp c (QuotientAddGroup.mk' (intSub F))
  refine ⟨charOf c', fun x hx1 => ?_, ϖ⁻¹, fun h => hc ?_, fun y hy => ?_⟩
  · show ce (c (QuotientAddGroup.mk x)) = 1
    rw [(QuotientAddGroup.eq_zero_iff x).2 hx1, map_zero, ce_zero]
  · exact ce_eq_one h
  · rw [norm_mul, norm_inv, inv_mul_le_iff₀ hpos, mul_one]
    exact hle y hy

end Field

section Props
variable {F : Type} [NontriviallyNormedField F]

theorem locConst [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) :
    IsLocallyConstant (fun x => ψ x) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨Metric.ball x 1, Metric.isOpen_ball, Metric.mem_ball_self one_pos, fun x' hx' => ?_⟩
  have h : ψ (x' - x) = 1 := hψ.1 _ (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hx').le)
  calc ψ x' = ψ (x + (x' - x)) := by rw [add_sub_cancel]
    _ = ψ x := by rw [AddChar.map_add_eq_mul, h, mul_one]

theorem norm_eq_one [IsUltrametricDist F] [ProperSpace F] [CharZero F] {ψ : AddChar F ℂ}
    (hψ : IsStdChar ψ) (x : F) : ‖ψ x‖ = 1 := by
  obtain ⟨N, hN0, hN1⟩ := exists_nat_norm_lt_one (F := F)
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hxpos) hN1
  have h1 : ψ ((N ^ k : ℕ) • x) = 1 := by
    apply hψ.1
    rw [nsmul_eq_mul, norm_mul, Nat.cast_pow, norm_pow]
    exact (mul_le_mul_of_nonneg_right hk.le (norm_nonneg _)).trans (by rw [inv_mul_cancel₀ hxpos.ne'])
  rw [AddChar.map_nsmul_eq_pow] at h1
  have h2 : ‖ψ x‖ ^ (N ^ k) = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero k hN0.ne')).1 h2

theorem conductor [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) (y : F) :
    (∀ e : F, ‖e‖ ≤ 1 → ψ (e * y) = 1) ↔ ‖y‖ ≤ 1 := by
  constructor
  · intro h
    by_contra hy
    push_neg at hy
    obtain ⟨x, hx, hxy⟩ := hψ.2
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
    have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hxle : ‖x‖ ≤ ‖y‖ := by
      have := hxy y⁻¹ (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hy)
      rwa [norm_mul, norm_inv, mul_inv_le_iff₀ hypos, one_mul] at this
    apply hx
    have := h (x * y⁻¹) (by rw [norm_mul, norm_inv, mul_inv_le_iff₀ hypos, one_mul]; exact hxle)
    rwa [mul_assoc, inv_mul_cancel₀ hy0, mul_one] at this
  · intro hy e he
    exact hψ.1 _ (by rw [norm_mul]; exact mul_le_one₀ he (norm_nonneg _) hy)

end Props

section Ext
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem conductor_trace [hU : Unram F E]
    (htr : ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y)
    (he : ∃ e : E, ‖e‖ ≤ 1 ∧ e + star e = 1)
    {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) (y : E) :
    (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * y)) = 1) ↔ ‖y‖ ≤ 1 := by
  haveI := hU.ultraE
  constructor
  · intro h
    by_contra hy
    push_neg at hy
    obtain ⟨x, hx, hxy⟩ := hψ.2
    obtain ⟨e₀, he₀, hsum⟩ := he
    obtain ⟨a, ha⟩ := hU.unram y
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
    have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have ha1 : 1 < ‖a‖ := ha ▸ hy
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha1; linarith
    have hxle : ‖x‖ ≤ ‖y‖ := by
      have := hxy a⁻¹ (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ ha1)
      rw [norm_mul, norm_inv, mul_inv_le_iff₀ (norm_pos_iff.2 ha0), one_mul] at this
      rwa [ha]
    have htr1 : Algebra.trace F E e₀ = 1 := by
      apply (algebraMap F E).injective
      rw [htr, hsum, map_one]
    apply hx
    have := h (algebraMap F E x * e₀ * y⁻¹) (by
      rw [norm_mul, norm_mul, norm_inv, norm_algebraMap', mul_inv_le_iff₀ hypos]
      calc ‖x‖ * ‖e₀‖ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left he₀ (norm_nonneg _)
        _ ≤ 1 * ‖y‖ := by rw [mul_one, one_mul]; exact hxle)
    rwa [mul_assoc, inv_mul_cancel₀ hy0, mul_one, ← Algebra.smul_def, LinearMap.map_smul, htr1,
      smul_eq_mul, mul_one] at this
  · intro hy e he'
    apply hψ.1
    have hz : ‖e * y‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ he' (norm_nonneg _) hy
    rw [← norm_algebraMap' E, htr]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hz (by rw [hU.norm_star]; exact hz))

end Ext

theorem psi_conductor : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E], (∃ ψ : AddChar F ℂ, IsStdChar ψ) ∧ ∀ ψ : AddChar F ℂ, IsStdChar ψ →
    IsLocallyConstant (fun x => ψ x) ∧ (∀ x, ‖ψ x‖ = 1) ∧
    (∀ y : F, (∀ e : F, ‖e‖ ≤ 1 → ψ (e * y) = 1) ↔ ‖y‖ ≤ 1) ∧
    ∀ y : E, (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * y)) = 1) ↔ ‖y‖ ≤ 1 := by
  intro F E _ _ _ _ hU
  haveI := hU.ultraF
  haveI := hU.charZero
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨htr, he, -⟩ := GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E
  exact ⟨exists_stdChar F, fun ψ hψ => ⟨locConst hψ, norm_eq_one hψ, conductor hψ,
    conductor_trace htr he hψ⟩⟩

end GlobalTheory.StdChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorPropertiesStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedStandardAddChar_conductor_properties : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∃ ψ : AddChar F ℂ, IsStdChar ψ) ∧ ∀ ψ : AddChar F ℂ, IsStdChar ψ → IsLocallyConstant (fun x => ψ x) ∧ (∀ x, ‖ψ x‖ = 1) ∧ (∀ y : F, (∀ e : F, ‖e‖ ≤ 1 → ψ (e * y) = 1) ↔ ‖y‖ ≤ 1) ∧ ∀ y : E, (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * y)) = 1) ↔ ‖y‖ ≤ 1 := by
  first | exact @GlobalTheory.StdChar.psi_conductor | exact GlobalTheory.StdChar.psi_conductor | (intros; apply GlobalTheory.StdChar.psi_conductor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedValuationParitySignCharacterKernelNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedValuationParitySignCharacterKernelNorm
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.EtaChar

theorem exists_unif (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] :
    ∃ π : F, 0 < ‖π‖ ∧ ‖π‖ < 1 ∧ ∀ x : F, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k := by
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  have hc : IsCompact (Metric.ball (0 : F) 1) :=
    (isCompact_closedBall (0 : F) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball _ _)
      Metric.ball_subset_closedBall
  obtain ⟨π, hπm, hmax⟩ := hc.exists_isMaxOn ⟨0, Metric.mem_ball_self one_pos⟩ continuous_norm.continuousOn
  have hπ1 : ‖π‖ < 1 := by simpa using hπm
  have hle : ∀ y : F, ‖y‖ < 1 → ‖y‖ ≤ ‖π‖ := fun y hy => hmax (by simpa using hy)
  obtain ⟨x0, hx0, hx01⟩ := NormedField.exists_norm_lt_one F
  have hπ0 : 0 < ‖π‖ := lt_of_lt_of_le hx0 (hle x0 hx01)
  refine ⟨π, hπ0, hπ1, fun x hx => ?_⟩
  set q := ‖π‖ with hq
  have hxp : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hqi : 1 < q⁻¹ := one_lt_inv₀ hπ0 |>.2 hπ1
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hxp hqi
  have hqn : 0 < q ^ (n + 1) := zpow_pos hπ0 _
  have hz : ‖x * π ^ (n + 1)‖ = ‖x‖ * q ^ (n + 1) := by rw [norm_mul, norm_zpow]
  have hup : ‖x‖ * q ^ (n + 1) ≤ 1 := by
    calc ‖x‖ * q ^ (n + 1) ≤ q⁻¹ ^ (n + 1) * q ^ (n + 1) := mul_le_mul_of_nonneg_right hn2 hqn.le
      _ = 1 := by rw [_root_.inv_zpow, inv_mul_cancel₀ hqn.ne']
  have hlo : q < ‖x‖ * q ^ (n + 1) := by
    calc q = q⁻¹ ^ n * q ^ (n + 1) := by
            rw [_root_.inv_zpow, zpow_add_one₀ hπ0.ne', ← mul_assoc, inv_mul_cancel₀ (zpow_pos hπ0 n).ne', one_mul]
      _ < ‖x‖ * q ^ (n + 1) := mul_lt_mul_of_pos_right hn1 hqn
  have heq : ‖x‖ * q ^ (n + 1) = 1 := by
    by_contra hne
    have := hle (x * π ^ (n + 1)) (by rw [hz]; exact lt_of_le_of_ne hup hne)
    rw [hz] at this
    linarith
  refine ⟨-(n + 1), ?_⟩
  rw [_root_.zpow_neg]; exact eq_inv_of_mul_eq_one_left heq

theorem eta_eq_one_iff {F : Type} [NormedField F] (x : F) : eta x = 1 ↔ ∃ y : F, ‖x‖ = ‖y‖ ^ 2 := by
  unfold eta
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    norm_num

theorem eta_eq_neg_one_iff {F : Type} [NormedField F] (x : F) : eta x = -1 ↔ ¬ ∃ y : F, ‖x‖ = ‖y‖ ^ 2 := by
  unfold eta
  split_ifs with h
  · simp only [h, not_true_eq_false, iff_false]
    norm_num
  · simp [h]

theorem sq_iff_even {F : Type} [NormedField F] {π : F} (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1)
    (hall : ∀ x : F, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k) {x : F} {k : ℤ} (hk : ‖x‖ = ‖π‖ ^ k) :
    (∃ y : F, ‖x‖ = ‖y‖ ^ 2) ↔ Even k := by
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      have : ‖x‖ = 0 := by simpa using hy
      rw [hk] at this
      exact (zpow_pos h0 k).ne' this
    obtain ⟨j, hj⟩ := hall y hy0
    rw [hk, hj, ← zpow_natCast, ← _root_.zpow_mul] at hy
    have := zpow_right_injective₀ h0 h1.ne hy
    exact ⟨j, by rw [this]; push_cast; ring⟩
  · rintro ⟨j, rfl⟩
    refine ⟨π ^ j, ?_⟩
    rw [hk, norm_zpow, ← zpow_natCast, ← _root_.zpow_mul]
    congr 1
    push_cast; ring

theorem eta_of_exp {F : Type} [NormedField F] {π : F} (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1)
    (hall : ∀ x : F, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k) {x : F} {k : ℤ} (hk : ‖x‖ = ‖π‖ ^ k) :
    eta x = if Even k then 1 else -1 := by
  have := sq_iff_even h0 h1 hall hk
  by_cases h : Even k
  · rw [(eta_eq_one_iff x).2 (this.2 h)]; simp [h]
  · rw [(eta_eq_neg_one_iff x).2 (fun h' => h (this.1 h'))]; simp [h]

theorem eta_mul (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F] (x y : F)
    (hx : x ≠ 0) (hy : y ≠ 0) : eta (x * y) = eta x * eta y := by
  obtain ⟨π, h0, h1, hall⟩ := exists_unif F
  obtain ⟨k, hk⟩ := hall x hx
  obtain ⟨l, hl⟩ := hall y hy
  have hkl : ‖x * y‖ = ‖π‖ ^ (k + l) := by rw [norm_mul, hk, hl, zpow_add₀ h0.ne']
  rw [eta_of_exp h0 h1 hall hk, eta_of_exp h0 h1 hall hl, eta_of_exp h0 h1 hall hkl]
  by_cases ek : Even k <;> by_cases el : Even l <;> simp [ek, el, Int.even_add]

theorem eta_of_norm_eq {F : Type} [NormedField F] {x y : F} (h : ‖x‖ = ‖y‖) : eta x = eta y := by
  have e : (∃ z : F, ‖x‖ = ‖z‖ ^ 2) ↔ (∃ z : F, ‖y‖ = ‖z‖ ^ 2) := by rw [h]
  by_cases hh : ∃ z : F, ‖x‖ = ‖z‖ ^ 2
  · rw [(eta_eq_one_iff x).2 hh, (eta_eq_one_iff y).2 (e.1 hh)]
  · rw [(eta_eq_neg_one_iff x).2 hh, (eta_eq_neg_one_iff y).2 (fun h' => hh (e.2 h'))]

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ x y : F, x ≠ 0 → y ≠ 0 → eta (x * y) = eta x * eta y) ∧ (∀ x : F, ‖x‖ = 1 → eta x = 1) ∧ (∀ x : F, x ≠ 0 → (eta x = 1 ↔ ∃ v : E, v * star v = algebraMap F E x)) ∧ IsLocallyConstant (fun x : {x : F // x ≠ 0} => eta x.1) := by
  intro F E _ _ _ _ hU
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  refine ⟨fun x y hx hy => eta_mul F x y hx hy, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · exact (eta_eq_one_iff x).2 ⟨1, by rw [hx, norm_one, one_pow]⟩
  · rw [eta_eq_one_iff]
    constructor
    · rintro ⟨y, hy⟩
      have hy0 : y ≠ 0 := by
        rintro rfl
        exact hx (norm_eq_zero.1 (by simpa using hy))
      obtain ⟨v, hv⟩ := GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic F E (x / y ^ 2) (by rw [norm_div, norm_pow, hy, div_self (by positivity)])
      refine ⟨v * algebraMap F E y, ?_⟩
      rw [star_mul', hU.star_fix y]
      calc v * algebraMap F E y * (star v * algebraMap F E y)
          = (v * star v) * algebraMap F E (y ^ 2) := by rw [map_pow]; ring
        _ = algebraMap F E x := by rw [hv, ← map_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hy0)]
    · rintro ⟨v, hv⟩
      obtain ⟨z, hz⟩ := hU.unram v
      refine ⟨z, ?_⟩
      have := congrArg norm hv
      rw [norm_algebraMap', norm_mul, hU.norm_star, hz] at this
      rw [← this, sq]
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hx : 0 < ‖x.1‖ := norm_pos_iff.2 x.2
    have hmem : {y : {x : F // x ≠ 0} | ‖y.1 - x.1‖ < ‖x.1‖} ∈ 𝓝 x := by
      have : IsOpen {y : {x : F // x ≠ 0} | ‖y.1 - x.1‖ < ‖x.1‖} :=
        isOpen_lt (continuous_norm.comp (continuous_subtype_val.sub continuous_const)) continuous_const
      exact this.mem_nhds (by simpa using hx)
    filter_upwards [hmem] with y hy
    apply eta_of_norm_eq
    have h2 : y.1 = x.1 + (y.1 - x.1) := by ring
    rw [h2, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hy), max_eq_left hy.le]

end GlobalTheory.EtaChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedValuationParitySignCharacterKernelNormStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedValuationParitySign_character_kernel_norms : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ x y : F, x ≠ 0 → y ≠ 0 → eta (x * y) = eta x * eta y) ∧ (∀ x : F, ‖x‖ = 1 → eta x = 1) ∧ (∀ x : F, x ≠ 0 → (eta x = 1 ↔ ∃ v : E, v * star v = algebraMap F E x)) ∧ IsLocallyConstant (fun x : {x : F // x ≠ 0} => eta x.1) := by
  first | exact @GlobalTheory.EtaChar.main | exact GlobalTheory.EtaChar.main | (intros; apply GlobalTheory.EtaChar.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfValNonneg
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma

theorem mem_range_of_val_nonneg (K : UQ) (z : K.E) (h : 0 ≤ val K.O z) :
    ∃ a : K.O, algebraMap K.O K.E a = z := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E z ≠ 0 := by simpa using hz
  have hle : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E z ≤ 1 := by
    unfold val at h
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hle
  exact ⟨a, ha⟩

theorem val_algebraMap_nonneg (K : UQ) (a : K.O) : 0 ≤ val K.O (algebraMap K.O K.E a) := by
  by_cases ha : a = 0
  · simp [ha, val]
  unfold val
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal K.O) (K := K.E) a
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) ≠ 0 := by
    simpa using ha
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem exists_int_image {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (a : K.O) :
    ∃ b : K'.O, algebraMap K'.O K'.E b = φ (algebraMap K.O K.E a) := by
  apply mem_range_of_val_nonneg
  rw [hU.2.2.1]
  exact val_algebraMap_nonneg K a

end GlobalTheory.UnitLemma.Unr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteNormedAlgebraEqModuleTopology
open GlobalTheory.JR MeasureTheory Filter Topology

namespace GlobalTheory

theorem _root_.GlobalTheory.isOpenUnits_and_eventually_sq_normed (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] [CharZero F] (R : Type) [NormedCommRing R] [NormedAlgebra F R]
    [Module.Finite F R] :
    IsOpenUnits R ∧ ∀ᶠ v in 𝓝 (1 : R), ∃ s : R, s ^ 2 = v := by
  haveI : CompleteSpace R := FiniteDimensional.complete F R
  refine ⟨⟨Units.isOpenEmbedding_val⟩, ?_⟩
  have hd := hasStrictFDerivAt_pow (𝕜 := F) 2 (x := (1 : R))
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hsurj : LinearMap.range
      ((((2 : ℕ) • (1 : R) ^ (2 - 1)) • ContinuousLinearMap.id F R : R →L[F] R) : R →ₗ[F] R)
        = ⊤ := by
    refine LinearMap.range_eq_top.2 fun v => ⟨(2 : F)⁻¹ • v, ?_⟩
    have hc : ((2 : ℕ) • (1 : R) ^ (2 - 1)) = algebraMap F R 2 := by
      simp [two_smul, map_ofNat, one_add_one_eq_two]
    simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_id', Pi.smul_apply,
      id_eq, hc, ContinuousLinearMap.coe_coe, smul_eq_mul]
    rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ h2, one_smul]
  have hmap := hd.map_nhds_eq_of_surj hsurj
  rw [one_pow] at hmap
  rw [← hmap, Filter.eventually_map]
  exact Filter.Eventually.of_forall fun s => ⟨s, rfl⟩

theorem _root_.GlobalTheory.finiteNormedAlgebra_eq_moduleTopology (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] (R : Type) [N : NormedCommRing R] [NormedAlgebra F R]
    [Module.Finite F R] :
    N.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      = moduleTopology F R := by
  haveI : IsModuleTopology F R := isModuleTopologyOfFiniteDimensional
  exact eq_moduleTopology F R

theorem _root_.GlobalTheory.isOpenUnits_and_eventually_sq (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] [CharZero F] (R : Type) [CommRing R] [Algebra F R] [Module.Finite F R]
    [τ : TopologicalSpace R] [IsModuleTopology F R] :
    IsOpenUnits R ∧ ∀ᶠ v in 𝓝 (1 : R), ∃ s : R, s ^ 2 = v := by
  classical
  have h := eq_moduleTopology F R
  let b := Module.finBasis F R
  letI : NormedRing (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedRing
  letI : NormedAlgebra F (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedAlgebra
  letI N : NormedCommRing R :=
    NormedCommRing.induced R _ (Algebra.leftMulMatrix b) (Algebra.leftMulMatrix_injective b)
  letI : NormedAlgebra F R := NormedAlgebra.induced F R _ (Algebra.leftMulMatrix b)
  have key := _root_.GlobalTheory.isOpenUnits_and_eventually_sq_normed F R
  have h2 := _root_.GlobalTheory.finiteNormedAlgebra_eq_moduleTopology F R
  have h3 : τ = N.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace :=
    h.trans h2.symm
  rw [h3]
  exact key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

def bas (hG : A.IsGen τ p) : Module.Basis (Fin r) F A.K :=
  basisOfLinearIndependentOfCardEqFinrank' _ hG.1 (by rw [hG.2.1]; simp)

def pt (hG : A.IsGen τ p) (lam : F) (b c : A.K) : Gl r F :=
  (companion p, (bas A hG).equivFun b, fun i => Algebra.trace F A.K (τ ^ (i : ℕ) * c), lam)

def tm (hG : A.IsGen τ p) : A.Kˣ →* GL (Fin r) F :=
  Units.map (Algebra.leftMulMatrix (bas A hG)).toRingHom.toMonoidHom

def unitsMeas (μK : Measure A.K) : Measure A.Kˣ :=
  (μK.withDensity fun t => ENNReal.ofReal (A.absK t)⁻¹).comap Units.val

def desc (M : Meas r F E)
    (hG : A.IsGen τ p) (lam : F) (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ) (x : A.K × A.K) : ℂ :=
  letI := M.mG
  ∫ g, f' (act g (pt A hG lam x.1 x.2)) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) ∂M.μG

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem bas_apply (hG : A.IsGen τ p) (i : Fin r) : LinDesc.bas A hG i = τ ^ (i : ℕ) := by
  simp [LinDesc.bas]

theorem repr_sum (hG : A.IsGen τ p) (c : Fin r → F) :
    (LinDesc.bas A hG).repr (∑ i, c i • τ ^ (i : ℕ)) = Finsupp.equivFunOnFinite.symm c := by
  have : (∑ i, c i • τ ^ (i : ℕ)) = (LinDesc.bas A hG).equivFun.symm c := by
    rw [Module.Basis.equivFun_symm_apply]; simp [bas_apply]
  rw [this]
  ext i
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]; simp

theorem leftMul_tau (hG : A.IsGen τ p) : Algebra.leftMulMatrix (LinDesc.bas A hG) τ = companion p := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, bas_apply, ← pow_succ']
  simp only [companion, Matrix.of_apply]
  by_cases hj : (j : ℕ) + 1 = r
  · rw [if_pos hj, hj]
    have h3 : τ ^ r = ∑ k, (-p k) • τ ^ (k : ℕ) := by
      have := hG.2.2
      simp only [neg_smul, Finset.sum_neg_distrib]
      exact eq_neg_of_add_eq_zero_left this
    rw [h3, repr_sum]; simp
  · rw [if_neg hj]
    have hlt : (j : ℕ) + 1 < r := lt_of_le_of_ne j.2 hj
    have h3 : τ ^ ((j : ℕ) + 1) = LinDesc.bas A hG ⟨(j : ℕ) + 1, hlt⟩ := by rw [bas_apply]
    rw [h3, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hi : (i : ℕ) = (j : ℕ) + 1
    · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
    · rw [if_neg hi, if_neg]
      intro h; exact hi (by rw [← h])

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem tm_coe (hG : A.IsGen τ p) (t : A.Kˣ) :
    ((tm A hG t : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = Algebra.leftMulMatrix (bas A hG) (t : A.K) := rfl

theorem tm_inv_coe (hG : A.IsGen τ p) (t : A.Kˣ) :
    (((tm A hG t)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      Algebra.leftMulMatrix (bas A hG) ((t⁻¹ : A.Kˣ) : A.K) := by
  rw [← map_inv]; rfl

theorem row_mul (hG : A.IsGen τ p) (s c : A.K) :
    (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * c)) ᵥ* Algebra.leftMulMatrix (bas A hG) s =
      fun j : Fin r => Algebra.trace F A.K (τ ^ (j : ℕ) * (s * c)) := by
  funext j
  simp only [Matrix.vecMul, dotProduct, Algebra.leftMulMatrix_eq_repr_mul]
  have hx := (bas A hG).sum_repr (s * bas A hG j)
  calc ∑ i : Fin r, Algebra.trace F A.K (τ ^ (i : ℕ) * c) * (bas A hG).repr (s * bas A hG j) i
      = Algebra.trace F A.K (∑ i : Fin r, ((bas A hG).repr (s * bas A hG j) i • bas A hG i) * c) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_comm, bas_apply A hG i]
    _ = Algebra.trace F A.K (τ ^ (j : ℕ) * (s * c)) := by
        rw [← Finset.sum_mul, hx, bas_apply]; ring_nf

theorem act_tm (hG : A.IsGen τ p) (lam : F) (t : A.Kˣ) (b c : A.K) :
    act (tm A hG t) (pt A hG lam b c) = pt A hG lam ((t : A.K) * b) (((t⁻¹ : A.Kˣ) : A.K) * c) := by
  unfold act pt
  rw [tm_inv_coe, tm_coe]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · simp only
    rw [← leftMul_tau A hG, ← map_mul, ← map_mul]; congr 1
    rw [mul_comm (t : A.K) τ, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  · simp only
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
    exact Algebra.leftMulMatrix_mulVec_repr _ _ _
  · exact row_mul A hG _ c

theorem det_tm (hG : A.IsGen τ p) (t : A.Kˣ) :
    ((tm A hG t : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det = Algebra.norm F (t : A.K) := by
  rw [tm_coe, Algebra.norm_eq_matrix_det (bas A hG)]

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc

theorem act_mul {r : ℕ} {k : Type} [CommRing k] (g h : GL (Fin r) k) (Y : Gl r k) :
    act (g * h) Y = act g (act h Y) := by
  unfold act
  simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem act_one {r : ℕ} {k : Type} [CommRing k] (Y : Gl r k) : act 1 Y = Y := by
  unfold act; simp

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc
theorem pt_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ a : A.K, LinDesc.pt A hG lam 1 a = sec (A.invK τ p lam a) := by
  intro F E _ _ _ _ _ A r τ p hG lam a
  unfold LinDesc.pt sec Et.invK
  congr 1
  refine Prod.ext ?_ rfl
  funext i
  have h1 : (1 : A.K) = LinDesc.bas A hG ⟨0, Fin.pos i⟩ := by
    simp [LinDesc.bas]
  simp only
  rw [h1, Module.Basis.equivFun_self]
  by_cases hi : (i : ℕ) = 0
  · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
  · rw [if_neg hi, if_neg]
    intro h; exact hi (by rw [← h])
end GlobalTheory.JR.LinDesc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfCharpolySeparableInvolution
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfCharpolySeparableInvolution
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem exists_aeval_eq_of_charpoly_separable {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (g : A) (hP : (LinearMap.mulLeft E g).charpoly.Separable) (a : A) :
    ∃ f : E[X], a = aeval g f := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, Subsingleton.elim _ _⟩
  have hint : IsIntegral E g := Algebra.IsIntegral.isIntegral g
  have hm0 : minpoly E g ≠ 0 := minpoly.ne_zero hint
  have hf : aeval (LinearMap.mulLeft E g) (minpoly E g) = 0 := by
    have := aeval_algHom_apply (Algebra.lmul E A) g (minpoly E g)
    rw [minpoly.aeval, map_zero] at this
    exact this
  have hn : 0 < Module.finrank E A := Module.finrank_pos
  have h1 := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank _ _ hf
  have h2 : (LinearMap.mulLeft E g).charpoly ∣ minpoly E g :=
    (hP.squarefree.dvd_pow_iff_dvd hn.ne').1 h1
  have h3 : Module.finrank E A ≤ (minpoly E g).natDegree := by
    have := natDegree_le_of_dvd h2 hm0
    rwa [LinearMap.charpoly_natDegree] at this
  have hli := linearIndependent_pow (K := E) g
  have h4 := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at h4
  haveI : Nonempty (Fin (minpoly E g).natDegree) := ⟨⟨0, by omega⟩⟩
  have htop := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin]; omega)
  have hle : Submodule.span E (Set.range fun i : Fin (minpoly E g).natDegree => g ^ (i : ℕ)) ≤
      Subalgebra.toSubmodule (Algebra.adjoin E {g}) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hg : g ∈ Algebra.adjoin E {g} := Algebra.subset_adjoin (Set.mem_singleton g)
    exact Subalgebra.pow_mem (Algebra.adjoin E {g}) hg (i : ℕ)
  have ha : a ∈ Algebra.adjoin E {g} := by
    have : a ∈ Submodule.span E (Set.range fun i : Fin (minpoly E g).natDegree => g ^ (i : ℕ)) := by
      rw [htop]; trivial
    exact hle this
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨f, hf⟩ := ha
  exact ⟨f, hf.symm⟩

theorem InvAlg.exists_aeval_eq_of_separable :
    ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f :=
  fun _ B hP a => exists_aeval_eq_of_charpoly_separable B.g hP a

end GlobalTheory.UnitLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfCharpolySeparableInvolutionStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable | exact GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable | (intros; apply GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinEqTopAndIsReducedOfCharpolySeparable
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinEqTopAndIsReducedOfCharpolySeparable
open Polynomial

namespace GlobalTheory.SepGen

variable {E : Type} [Field E] {A : Type} [CommRing A] [Algebra E A] [Module.Finite E A]

theorem charpoly_dvd (y : A) (hs : (LinearMap.mulLeft E y).charpoly.Separable) (f : E[X])
    (hf : aeval y f = 0) : (LinearMap.mulLeft E y).charpoly ∣ f := by
  have h0 : aeval (LinearMap.mulLeft E y) f = 0 := by
    have := Polynomial.aeval_algHom_apply (Algebra.lmul E A) y f
    rw [hf, map_zero] at this
    exact this
  by_cases hz : f = 0
  · rw [hz]; exact dvd_zero _
  classical
  have hP := hs.ne_zero
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP hz,
    Multiset.le_iff_subset
      ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP).1 hs.squarefree)]
  intro p hp
  rw [Polynomial.mem_normalizedFactors_iff hP] at hp
  rw [Polynomial.mem_normalizedFactors_iff hz]
  exact ⟨hp.1, hp.2.1,
    GlobalTheory.CuspGL.irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero _ _ _ hp.1 hp.2.2 h0⟩

theorem aeval_charpoly (y : A) : aeval y (LinearMap.mulLeft E y).charpoly = 0 := by
  have h := Polynomial.aeval_algHom_apply (Algebra.lmul E A) y (LinearMap.mulLeft E y).charpoly
  have h2 : aeval (Algebra.lmul E A y) (LinearMap.mulLeft E y).charpoly = 0 :=
    LinearMap.aeval_self_charpoly _
  rw [h2] at h
  simpa using (LinearMap.congr_fun h 1).symm

theorem adjoin_eq_top (y : A) (hs : (LinearMap.mulLeft E y).charpoly.Separable) :
    Algebra.adjoin E ({y} : Set A) = ⊤ := by
  have hi : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  have h1 := natDegree_le_of_dvd (charpoly_dvd y hs _ (minpoly.aeval E y)) (minpoly.ne_zero hi)
  rw [LinearMap.charpoly_natDegree] at h1
  have h2 : Module.finrank E (Algebra.adjoin E ({y} : Set A)) = (minpoly E y).natDegree :=
    (Algebra.adjoin.powerBasis hi).finrank
  have h3 : Subalgebra.toSubmodule (Algebra.adjoin E ({y} : Set A)) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) (h1.trans h2.ge))
  rw [← Algebra.toSubmodule_eq_top]
  exact h3

theorem isReduced (y : A) (hs : (LinearMap.mulLeft E y).charpoly.Separable) : IsReduced A := by
  have h3 := adjoin_eq_top y hs
  refine ⟨fun z ⟨k, hk⟩ => ?_⟩
  have hz : z ∈ Algebra.adjoin E ({y} : Set A) := by rw [h3]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
  obtain ⟨p, rfl⟩ := hz
  have h4 := charpoly_dvd y hs (p ^ k) (by rw [map_pow]; exact hk)
  obtain ⟨r, hr⟩ := hs.squarefree.isRadical k p h4
  change aeval y p = 0
  rw [hr, map_mul, aeval_charpoly, zero_mul]

theorem adjoin_eq_top_and_isReduced : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (y : A), (LinearMap.mulLeft E y).charpoly.Separable →
    Algebra.adjoin E ({y} : Set A) = ⊤ ∧ IsReduced A :=
  fun _ _ _ _ _ _ y hs => ⟨adjoin_eq_top y hs, isReduced y hs⟩

end GlobalTheory.SepGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoin_eq_top_and_isReduced_of_charpoly_separable : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (y : A), (LinearMap.mulLeft E y).charpoly.Separable → Algebra.adjoin E ({y} : Set A) = ⊤ ∧ IsReduced A := by
  first | exact @GlobalTheory.SepGen.adjoin_eq_top_and_isReduced | exact GlobalTheory.SepGen.adjoin_eq_top_and_isReduced | (intros; apply GlobalTheory.SepGen.adjoin_eq_top_and_isReduced <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SgnLatSpanBasis
open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.UnitLemma.SgnBasis

theorem eta_mul_isUnit (K : UQ) (a : K.E) (u : K.O) (hu : IsUnit u) :
    K.eta (a * algebraMap K.O K.E u) = K.eta a := by
  have hv : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E u) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    intro h
    exact (IsDiscreteValuationRing.maximalIdeal K.O).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ h hu)
  simp only [UQ.eta, val, map_mul, hv, mul_one]

private theorem eta_det_trace_matrix_eq_of_span_eq (K : UQ) (B : InvAlg K)
    (e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A)
    (m : Fin (Module.finrank K.E B.A) → B.A)
    (hm : Submodule.span K.O (Set.range m) = Submodule.span K.O (Set.range e)) :
    K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * m l)).det =
      K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)).det := by
  classical
  have hP0 : ∀ l, ∃ c : Fin (Module.finrank K.E B.A) → K.O, ∑ j, c j • e j = m l := by
    intro l
    refine (Submodule.mem_span_range_iff_exists_fun K.O).mp ?_
    rw [← hm]
    exact Submodule.subset_span ⟨l, rfl⟩
  have hQ0 : ∀ l, ∃ c : Fin (Module.finrank K.E B.A) → K.O, ∑ j, c j • m j = e l := by
    intro l
    refine (Submodule.mem_span_range_iff_exists_fun K.O).mp ?_
    rw [hm]
    exact Submodule.subset_span ⟨l, rfl⟩
  choose P hP using hP0
  choose Q hQ using hQ0

  have hli : LinearIndependent K.O e :=
    e.linearIndependent.restrict_scalars fun a b h =>
      IsFractionRing.injective K.O K.E (by simpa [Algebra.smul_def] using h)

  have hsum : ∀ l, ∑ i, (∑ j, Q l j * P j i) • e i = e l := by
    intro l
    calc ∑ i, (∑ j, Q l j * P j i) • e i = ∑ j, Q l j • ∑ i, P j i • e i := by
          simp only [Finset.sum_smul, Finset.smul_sum, mul_smul]
          exact Finset.sum_comm
      _ = e l := by simp only [hP, hQ]
  have hQP : Matrix.of Q * Matrix.of P = 1 := by
    ext l i
    have key : ∑ i, ((Matrix.of Q * Matrix.of P) l i - (1 : Matrix _ _ K.O) l i) • e i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, Matrix.mul_apply, Matrix.of_apply,
        Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true, hsum, sub_self]
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ key i)
  have hunit : IsUnit (Matrix.of P).det := Matrix.isUnit_det_of_left_inverse hQP

  have hmat : (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * m l)) =
      (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)) *
        (Matrix.of P).transpose.map (algebraMap K.O K.E) := by
    ext k l
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
    rw [← hP l]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.mul_sum, mul_smul_comm, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul K.E (P l j), map_smul, smul_eq_mul, mul_comm]
  have hdet : ((Matrix.of P).transpose.map (algebraMap K.O K.E)).det =
      algebraMap K.O K.E (Matrix.of P).det := by
    rw [RingHom.map_det, ← Matrix.det_transpose]
    rfl
  rw [hmat, Matrix.det_mul, hdet]
  exact eta_mul_isUnit K _ _ hunit

theorem sgnLat_span_basis (K : UQ) (B : InvAlg K) (e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A) :
    B.sgnLat (Submodule.span K.O (Set.range e)) =
      K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)).det := by
  dsimp only [InvAlg.sgnLat]
  exact eta_det_trace_matrix_eq_of_span_eq K B e _
    (Classical.epsilon_spec (p := fun m : Fin (Module.finrank K.E B.A) → B.A =>
      Submodule.span K.O (Set.range m) = Submodule.span K.O (Set.range e)) ⟨e, rfl⟩)

end GlobalTheory.UnitLemma.SgnBasis
end
