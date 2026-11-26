module

public import Mathlib

@[expose] public section

section -- merged from GroundTheory.PAdicHodge.PerfectoidField
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open NNReal

section Integers

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

abbrev normInteger : Subring K := (NormedField.valuation (K := K)).integer

variable {K}

theorem mem_normInteger {x : K} : x ∈ normInteger K ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
  simp

theorem normInteger_integers : (NormedField.valuation (K := K)).Integers (normInteger K) :=
  Valuation.integer.integers _


theorem mem_span_singleton_pow_iff {a x : normInteger K} (n : ℕ) :
    x ∈ Ideal.span {a} ^ n ↔ ‖(x : K)‖ ≤ ‖(a : K)‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, rfl⟩
    rw [Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]
    calc ‖(y : K)‖ * ‖(a : K)‖ ^ n ≤ 1 * ‖(a : K)‖ ^ n := by
          gcongr; exact mem_normInteger.1 y.2
      _ = _ := one_mul _
  · intro hx
    by_cases ha : (a : K) ^ n = 0
    · refine ⟨0, ?_⟩
      have : ‖(x : K)‖ = 0 := le_antisymm (by simpa [← norm_pow, ha] using hx) (norm_nonneg _)
      ext; simp [norm_eq_zero.1 this]
    · refine ⟨⟨(x : K) / (a : K) ^ n, mem_normInteger.2 ?_⟩, ?_⟩
      · rw [norm_div, norm_pow]
        exact div_le_one_of_le₀ hx (by positivity)
      · ext; simp [div_mul_cancel₀ _ ha]

theorem isAdicComplete_span_singleton [CompleteSpace K] {a : normInteger K}
    (ha : ‖(a : K)‖ < 1) : IsAdicComplete (Ideal.span {a}) (normInteger K) := by
  have hmem : ∀ (n : ℕ) (x y : normInteger K),
      x ≡ y [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule (normInteger K) (normInteger K))] ↔
        ‖(x : K) - y‖ ≤ ‖(a : K)‖ ^ n := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_singleton_pow_iff]
    simp
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    simp only [hmem, ZeroMemClass.coe_zero, sub_zero] at hx
    have ht : Filter.Tendsto (fun n : ℕ => ‖(a : K)‖ ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ha
    have : ‖(x : K)‖ ≤ 0 := ge_of_tendsto' ht hx
    ext; simpa using this
  · intro f hf
    simp only [hmem] at hf
    have ht : Filter.Tendsto (fun n : ℕ => ‖(a : K)‖ ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ha
    have hc : CauchySeq (fun n => (f n : K)) := by
      refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
      obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
      refine ⟨N, fun n hn => ?_⟩
      rw [dist_eq_norm, norm_sub_rev]
      exact (hf hn).trans_lt (hN N le_rfl)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hL1 : ‖L‖ ≤ 1 :=
      le_of_tendsto' hL.norm fun n => mem_normInteger.1 (f n).2
    refine ⟨⟨L, mem_normInteger.2 hL1⟩, fun n => (hmem n _ _).2 ?_⟩
    have h2 : Filter.Tendsto (fun m => (f n : K) - f m) Filter.atTop (nhds ((f n : K) - L)) :=
      tendsto_const_nhds.sub hL
    exact le_of_tendsto h2.norm (Filter.eventually_atTop.2 ⟨n, fun m hm => hf hm⟩)

theorem surjective_pow_modP_of_exists_pow_eq {p : ℕ} (hp : p ≠ 0)
    (h : ∀ x : K, ‖x‖ ≤ 1 → ∃ y : K, y ^ p = x) :
    Function.Surjective (fun x : ModP (normInteger K) p => x ^ p) := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨y, hy⟩ := h x (mem_normInteger.1 x.2)
  have hy1 : ‖y‖ ≤ 1 := by
    have : ‖y‖ ^ p ≤ 1 := by rw [← norm_pow, hy]; exact mem_normInteger.1 x.2
    exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hp).1 this
  refine ⟨Ideal.Quotient.mk _ ⟨y, mem_normInteger.2 hy1⟩, ?_⟩
  simp only [← map_pow]
  congr 1
  ext; simp [hy]

end Integers

class IsPerfectoidField (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    (p : ℕ) [Fact p.Prime] : Prop where

  complete : CompleteSpace K

  norm_natCast_lt_one : ‖(p : K)‖ < 1

  exists_norm_mem_Ioo : ∀ r : ℝ, r < 1 → ∃ x : K, r < ‖x‖ ∧ ‖x‖ < 1

  surjective_pow : Function.Surjective (fun x : ModP (normInteger K) p => x ^ p)

namespace IsPerfectoidField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]

theorem completeSpace (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p] : CompleteSpace K :=
  IsPerfectoidField.complete p

theorem norm_natCast_integer_lt_one : ‖((p : normInteger K) : K)‖ < 1 := by
  simpa using IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)

instance fact_not_isUnit : Fact (¬ IsUnit (p : normInteger K)) := by
  refine ⟨fun hu => ?_⟩
  obtain ⟨u, hu⟩ := hu
  have h1 : ‖((u : normInteger K) : K)‖ * ‖(((u⁻¹ : (normInteger K)ˣ) : normInteger K) : K)‖ = 1 := by
    rw [← norm_mul, ← Subring.coe_mul, Units.mul_inv]; simp
  have ha : ‖((u : normInteger K) : K)‖ < 1 := hu ▸ norm_natCast_integer_lt_one p
  have hb := mem_normInteger.1 ((u⁻¹ : (normInteger K)ˣ) : normInteger K).2
  nlinarith [norm_nonneg ((u : normInteger K) : K)]

instance fact_valuation_ne_one : Fact (NormedField.valuation (p : K) ≠ 1) := by
  refine ⟨fun h => ?_⟩
  have h' : ‖(p : K)‖ = 1 := by
    rw [NormedField.valuation_apply] at h
    exact congrArg NNReal.toReal h
  exact (IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)).ne h'

instance isAdicComplete : IsAdicComplete (Ideal.span {(p : normInteger K)}) (normInteger K) :=
  haveI := completeSpace (K := K) p
  isAdicComplete_span_singleton (norm_natCast_integer_lt_one p)

theorem surjective_frobenius : Function.Surjective (frobenius (ModP (normInteger K) p) p) :=
  IsPerfectoidField.surjective_pow

theorem surjective_fontaineTheta : Function.Surjective (WittVector.fontaineTheta (normInteger K) p) :=
  _root_.surjective_fontaineTheta (surjective_frobenius p)

theorem isDomain_preTilt : IsDomain (PreTilt (normInteger K) p) :=
  PreTilt.isDomain K NormedField.valuation (normInteger K) normInteger_integers p

end IsPerfectoidField

namespace IsPerfectoidField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]


omit [IsUltrametricDist K] in
theorem exists_norm_mem_Ioo_of_exists_pow_eq
    (h : ∀ (x : K) (n : ℕ), 0 < n → ∃ y : K, y ^ n = x) :
    ∀ r : ℝ, r < 1 → ∃ x : K, r < ‖x‖ ∧ ‖x‖ < 1 := by
  intro r hr
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
  set r' := max r 0 with hr'
  have hr'0 : 0 ≤ r' := le_max_right _ _
  have hr'1 : r' < 1 := max_lt hr zero_lt_one
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hc0 hr'1
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hN
    exact absurd (hN.trans hc1) (lt_irrefl _)
  obtain ⟨y, hy⟩ := h c N (Nat.pos_of_ne_zero hN0)
  have hyN : ‖y‖ ^ N = ‖c‖ := by rw [← norm_pow, hy]
  refine ⟨y, lt_of_le_of_lt (le_max_left r 0) ?_, ?_⟩
  · rw [← pow_lt_pow_iff_left₀ hr'0 (norm_nonneg y) hN0, hyN]
    exact hN
  · rw [← pow_lt_one_iff_of_nonneg (norm_nonneg y) hN0, hyN]
    exact hc1

theorem of_isAlgClosed (p : ℕ) [Fact p.Prime] [CompleteSpace K] [IsAlgClosed K]
    (hp : ‖(p : K)‖ < 1) : IsPerfectoidField K p := by
  refine ⟨inferInstance, hp, ?_, ?_⟩
  · exact exists_norm_mem_Ioo_of_exists_pow_eq fun x _ hn => IsAlgClosed.exists_pow_nat_eq x hn
  · exact surjective_pow_modP_of_exists_pow_eq (Fact.out : p.Prime).ne_zero
      fun x _ => IsAlgClosed.exists_pow_nat_eq x (Fact.out : p.Prime).pos

instance padicComplex (p : ℕ) [Fact p.Prime] : IsPerfectoidField ℂ_[p] p :=
  of_isAlgClosed p (by
    have h := PadicComplex.norm_extends' p (p : ℚ_[p])
    have hc : (((p : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) = (p : ℂ_[p]) := by
      rw [map_natCast, PadicComplex.coe_natCast]
    rw [← hc, h]
    exact Padic.norm_p_lt_one)

end IsPerfectoidField

end GroundTheory.PAdicHodge

end
end

section -- merged from GroundTheory.PAdicHodge.GaloisOnCp
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open UniformSpace Topology Filter

noncomputable section

theorem continuousSMul_of_isometry_of_dense {G X : Type*} [Monoid G] [TopologicalSpace G]
    [PseudoMetricSpace X] [MulAction G X] (D : Set X) (hD : Dense D)
    (hiso : ∀ g : G, Isometry fun x : X => g • x)
    (horb : ∀ d ∈ D, Continuous fun g : G => g • d) : ContinuousSMul G X := by
  refine ⟨continuous_iff_continuousAt.2 fun ⟨g₀, x₀⟩ => ?_⟩
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨d, hd, hxd⟩ := Metric.mem_closure_iff.1 (hD x₀) (ε / 4) (by positivity)
  have h1 : ∀ᶠ g in 𝓝 g₀, dist (g • d) (g₀ • d) < ε / 4 :=
    Metric.tendsto_nhds.1 ((horb d hd).tendsto g₀) _ (by positivity)
  have h2 : ∀ᶠ x in 𝓝 x₀, dist x x₀ < ε / 4 := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [h1.prod_nhds h2] with q hq
  obtain ⟨hg, hx⟩ := hq
  have e1 : dist (q.1 • q.2) (q.1 • d) = dist q.2 d := (hiso q.1).dist_eq q.2 d
  have e2 : dist (g₀ • d) (g₀ • x₀) = dist d x₀ := (hiso g₀).dist_eq d x₀
  have e3 : dist q.2 d ≤ dist q.2 x₀ + dist x₀ d := dist_triangle _ _ _
  have e4 : dist d x₀ = dist x₀ d := dist_comm _ _
  calc dist (q.1 • q.2) (g₀ • x₀)
      ≤ dist (q.1 • q.2) (q.1 • d) + dist (q.1 • d) (g₀ • d) + dist (g₀ • d) (g₀ • x₀) :=
        dist_triangle4 _ _ _ _
    _ < ε := by rw [e1, e2, e4]; linarith

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem spectralNorm_gal_apply (σ : Gal(PadicAlgCl p/K)) (x : PadicAlgCl p) :
    spectralNorm ℚ_[p] (PadicAlgCl p) (σ x) = spectralNorm ℚ_[p] (PadicAlgCl p) x :=
  (spectralNorm_eq_of_equiv (σ.restrictScalars ℚ_[p]) x).symm

theorem norm_gal_apply (σ : Gal(PadicAlgCl p/K)) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ :=
  spectralNorm_gal_apply σ x

theorem isometry_gal (σ : Gal(PadicAlgCl p/K)) : Isometry σ :=
  AddMonoidHomClass.isometry_of_norm σ (norm_gal_apply σ)

instance : UniformContinuousConstSMul Gal(PadicAlgCl p/K) (PadicAlgCl p) :=
  ⟨fun σ => (isometry_gal σ).uniformContinuous⟩

instance : Algebra.IsIntegral K (PadicAlgCl p) := Algebra.IsIntegral.tower_top ℚ_[p]

theorem continuous_gal_apply (y : PadicAlgCl p) :
    Continuous fun σ : Gal(PadicAlgCl p/K) => σ • y := by
  refine continuous_iff_continuousAt.2 fun σ₀ => tendsto_nhds_of_eventually_eq ?_
  let S := MulAction.stabilizer Gal(PadicAlgCl p/K) y
  have hS : (S : Set Gal(PadicAlgCl p/K)) ∈ 𝓝 (σ₀⁻¹ * σ₀) := by
    rw [inv_mul_cancel]
    exact (stabilizer_isOpen_of_isIntegral y).mem_nhds S.one_mem
  filter_upwards [(continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds hS]
    with σ hσ
  have h : (σ₀⁻¹ * σ) • y = y := hσ
  rw [mul_smul, inv_smul_eq_iff] at h
  exact h

theorem gal_smul_coe (σ : Gal(PadicAlgCl p/K)) (y : PadicAlgCl p) :
    σ • (y : ℂ_[p]) = ((σ y : PadicAlgCl p) : ℂ_[p]) :=
  (Completion.coe_smul σ y).symm

instance instMulSemiringActionCp : MulSemiringAction Gal(PadicAlgCl p/K) ℂ_[p] :=
  { (inferInstance : DistribMulAction Gal(PadicAlgCl p/K) ℂ_[p]) with
    smul_one := fun σ => by
      rw [← Completion.coe_one, gal_smul_coe, map_one]
    smul_mul := fun σ x y => by
      refine Completion.induction_on₂ x y (isClosed_eq ?_ ?_) fun a b => ?_
      · exact (continuous_const_smul σ).comp (continuous_fst.mul continuous_snd)
      · exact ((continuous_const_smul σ).comp continuous_fst).mul
          ((continuous_const_smul σ).comp continuous_snd)
      · rw [← Completion.coe_mul, gal_smul_coe, gal_smul_coe, gal_smul_coe, map_mul,
          Completion.coe_mul] }

theorem norm_smul_gal (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) : ‖σ • x‖ = ‖x‖ := by
  refine Completion.induction_on x
    (isClosed_eq (continuous_norm.comp (continuous_const_smul σ)) continuous_norm) fun a => ?_
  rw [gal_smul_coe, PadicComplex.norm_extends, PadicComplex.norm_extends, norm_gal_apply]

theorem isometry_smul_gal (σ : Gal(PadicAlgCl p/K)) : Isometry fun x : ℂ_[p] => σ • x :=
  Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul_gal]

instance : ContinuousSMul Gal(PadicAlgCl p/K) ℂ_[p] :=
  continuousSMul_of_isometry_of_dense (Set.range ((↑) : PadicAlgCl p → ℂ_[p]))
    Completion.denseRange_coe isometry_smul_gal (by
      rintro _ ⟨y, rfl⟩
      simp_rw [gal_smul_coe]
      exact (Completion.continuous_coe _).comp (continuous_gal_apply y))

theorem gal_smul_coe_of_mem (σ : Gal(PadicAlgCl p/K)) (k : K) :
    σ • ((k : PadicAlgCl p) : ℂ_[p]) = ((k : PadicAlgCl p) : ℂ_[p]) := by
  rw [gal_smul_coe]
  exact congrArg _ (σ.commutes k)

theorem gal_smul_algebraMap (σ : Gal(PadicAlgCl p/K)) (q : ℚ_[p]) :
    σ • algebraMap ℚ_[p] ℂ_[p] q = algebraMap ℚ_[p] ℂ_[p] q := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p]]
  change σ • ((algebraMap ℚ_[p] (PadicAlgCl p) q : PadicAlgCl p) : ℂ_[p]) = _
  rw [gal_smul_coe]
  exact congrArg _ ((σ.restrictScalars ℚ_[p]).commutes q)

def galCp (σ : Gal(PadicAlgCl p/K)) : ℂ_[p] ≃+* ℂ_[p] :=
  MulSemiringAction.toRingEquiv _ ℂ_[p] σ

theorem galCp_apply (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) : galCp σ x = σ • x := rfl

theorem galCp_coe (σ : Gal(PadicAlgCl p/K)) (y : PadicAlgCl p) :
    galCp σ (y : ℂ_[p]) = ((σ y : PadicAlgCl p) : ℂ_[p]) :=
  gal_smul_coe σ y

theorem norm_galCp (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) : ‖galCp σ x‖ = ‖x‖ :=
  norm_smul_gal σ x

theorem isometry_galCp (σ : Gal(PadicAlgCl p/K)) : Isometry (galCp σ) :=
  isometry_smul_gal σ

theorem continuous_galCp (σ : Gal(PadicAlgCl p/K)) : Continuous (galCp σ) :=
  (isometry_galCp σ).continuous

theorem eq_galCp_of_continuous (σ : Gal(PadicAlgCl p/K)) (f : ℂ_[p] → ℂ_[p])
    (hf : Continuous f) (h : ∀ y : PadicAlgCl p, f y = ((σ y : PadicAlgCl p) : ℂ_[p])) :
    f = galCp σ :=
  Completion.ext hf (continuous_galCp σ) fun y => by rw [h, galCp_coe]

def galCpHom : Gal(PadicAlgCl p/K) →* RingAut ℂ_[p] :=
  MulSemiringAction.toRingAut _ ℂ_[p]

theorem galCp_mul (σ τ : Gal(PadicAlgCl p/K)) : galCp (σ * τ) = (galCp τ).trans (galCp σ) :=
  map_mul galCpHom σ τ

theorem galCp_one : galCp (1 : Gal(PadicAlgCl p/K)) = RingEquiv.refl ℂ_[p] :=
  map_one galCpHom

theorem mem_padicComplexInt_iff (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplex.norm_eq_norm, Valuation.norm_def, ← NNReal.coe_one, NNReal.coe_le_coe,
    ← map_one (Valuation.RankOne.hom (PadicComplex.valued p).v),
    (Valuation.RankOne.strictMono _).le_iff_le, Valuation.restrict_le_one_iff]
  rfl

end

end GroundTheory.PAdicHodge
end

section -- merged from GroundTheory.PAdicHodge.RobbaSeries
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology

namespace Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

def ConvergesAt (a : ℤ → K) (ρ : ℝ) : Prop :=
  Tendsto (fun n : ℤ => ‖a n‖ * ρ ^ n) cofinite (𝓝 0)

def gaussNorm (a : ℤ → K) (ρ : ℝ) : ℝ := ⨆ n, ‖a n‖ * ρ ^ n

def domSet (a : ℤ → K) (ρ : ℝ) : Set ℤ := {n | ‖a n‖ * ρ ^ n = gaussNorm a ρ}

def lowIndex (a : ℤ → K) (ρ : ℝ) : ℤ := sInf (domSet a ρ)

def highIndex (a : ℤ → K) (ρ : ℝ) : ℤ := sSup (domSet a ρ)

variable {a b c : ℤ → K} {ρ : ℝ}

section Basic

theorem ConvergesAt.bddAbove (h : ConvergesAt a ρ) :
    BddAbove (Set.range fun n : ℤ => ‖a n‖ * ρ ^ n) :=
  h.bddAbove_range_of_cofinite

theorem ConvergesAt.le_gaussNorm (h : ConvergesAt a ρ) (n : ℤ) :
    ‖a n‖ * ρ ^ n ≤ gaussNorm a ρ :=
  le_ciSup h.bddAbove n

theorem gaussNorm_le {C : ℝ} (h : ∀ n, ‖a n‖ * ρ ^ n ≤ C) : gaussNorm a ρ ≤ C :=
  ciSup_le h

theorem gaussNorm_nonneg (hρ : 0 < ρ) : 0 ≤ gaussNorm a ρ :=
  Real.iSup_nonneg fun n => by positivity

theorem ConvergesAt.finite_le (h : ConvergesAt a ρ) {ε : ℝ} (hε : 0 < ε) :
    {n | ε ≤ ‖a n‖ * ρ ^ n}.Finite := by
  have := Filter.eventually_cofinite.1 (h.eventually (gt_mem_nhds hε))
  simpa only [not_lt] using this

end Basic

section Product

variable [CompleteSpace K]

end Product

section Dominant

section Attained

variable (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0)
include hρ h ha

theorem ConvergesAt.exists_eq_gaussNorm : ∃ n, ‖a n‖ * ρ ^ n = gaussNorm a ρ := by
  obtain ⟨n0, hn0⟩ := Function.ne_iff.1 ha
  have hε : 0 < ‖a n0‖ * ρ ^ n0 := by have := norm_pos_iff.2 hn0; positivity
  set S := (h.finite_le hε).toFinset
  have hn0S : n0 ∈ S := by simp [S]
  obtain ⟨m, hmS, hm⟩ := S.exists_max_image (fun n => ‖a n‖ * ρ ^ n) ⟨n0, hn0S⟩
  refine ⟨m, le_antisymm (h.le_gaussNorm m) (gaussNorm_le fun n => ?_)⟩
  by_cases hn : n ∈ S
  · exact hm n hn
  · simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hn
    exact hn.le.trans (hm n0 hn0S)

theorem gaussNorm_pos : 0 < gaussNorm a ρ := by
  obtain ⟨n0, hn0⟩ := Function.ne_iff.1 ha
  have := norm_pos_iff.2 hn0
  exact lt_of_lt_of_le (by positivity) (h.le_gaussNorm n0)

theorem domSet_finite : (domSet a ρ).Finite :=
  (h.finite_le (gaussNorm_pos hρ h ha)).subset fun n hn => le_of_eq (Eq.symm hn)

theorem domSet_nonempty : (domSet a ρ).Nonempty :=
  h.exists_eq_gaussNorm hρ ha

theorem lowIndex_mem : lowIndex a ρ ∈ domSet a ρ :=
  Int.csInf_mem (domSet_nonempty hρ h ha) (domSet_finite hρ h ha).bddBelow

theorem highIndex_mem : highIndex a ρ ∈ domSet a ρ :=
  Int.csSup_mem (domSet_nonempty hρ h ha) (domSet_finite hρ h ha).bddAbove

theorem lowIndex_le {n : ℤ} (hn : n ∈ domSet a ρ) : lowIndex a ρ ≤ n :=
  csInf_le (domSet_finite hρ h ha).bddBelow hn

theorem le_highIndex {n : ℤ} (hn : n ∈ domSet a ρ) : n ≤ highIndex a ρ :=
  le_csSup (domSet_finite hρ h ha).bddAbove hn

theorem weight_lt_of_lt_lowIndex {n : ℤ} (hn : n < lowIndex a ρ) :
    ‖a n‖ * ρ ^ n < gaussNorm a ρ :=
  lt_of_le_of_ne (h.le_gaussNorm n) fun heq => absurd (lowIndex_le hρ h ha heq) (not_le.2 hn)

theorem weight_lt_of_highIndex_lt {n : ℤ} (hn : highIndex a ρ < n) :
    ‖a n‖ * ρ ^ n < gaussNorm a ρ :=
  lt_of_le_of_ne (h.le_gaussNorm n) fun heq => absurd (le_highIndex hρ h ha heq) (not_le.2 hn)

theorem ne_zero_of_mem_domSet {n : ℤ} (hn : n ∈ domSet a ρ) : a n ≠ 0 := by
  intro h0
  have := gaussNorm_pos hρ h ha
  simp only [domSet, Set.mem_setOf_eq, h0, norm_zero, zero_mul] at hn
  linarith

end Attained

section Multiplicative

variable [CompleteSpace K]

variable (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
include hρ ha hb ha0 hb0

end Multiplicative

end Dominant

end Laurent

end GroundTheory.PAdicHodge
end
end

section -- merged from GroundTheory.PAdicHodge.SlopeCauchyBinet
section -- merged from GroundTheory.PowerSubgroups.CountableNeighbourhoods.ExistsMaxMinorNeZeroOfLinearIndependentAlt
namespace GroundTheory.Variant₂.N1

def KSubset (n k : ℕ) : Type := { s : Finset (Fin n) // s.card = k }

def KSubset.emb {n k : ℕ} (s : KSubset n k) : Fin k ↪o Fin n :=
  (s.1).orderEmbOfFin s.2

def maxMinor {R : Type*} [CommRing R] {n k : ℕ} (B : Matrix (Fin n) (Fin k) R)
    (s : KSubset n k) : R :=
  (B.submatrix (⇑s.emb) id).det

theorem exists_maxMinor_ne_zero_of_linearIndependent_alt {R : Type*} [CommRing R] {n k : ℕ}
    [IsDomain R] (B : Matrix (Fin n) (Fin k) R) (hB : LinearIndependent R B.col) :
    ∃ s : KSubset n k, maxMinor B s ≠ 0 := by
  classical
  set K := FractionRing R
  set B' : Matrix (Fin n) (Fin k) K := B.map (algebraMap R K) with hB'
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have h1 : LinearIndependent R B'.col := by
    have hker : LinearMap.ker ((Algebra.linearMap R K).compLeft (Fin n)) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      funext i
      exact hinj (congr_fun hxy i)
    have := hB.map' ((Algebra.linearMap R K).compLeft (Fin n)) hker
    have heq : B'.col = ((Algebra.linearMap R K).compLeft (Fin n)) ∘ B.col := by
      funext j i
      rfl
    rw [heq]
    exact this
  have h2 : LinearIndependent K B'.col := (LinearIndependent.iff_fractionRing R K).mp h1
  have hrank : B'.rank = k := by
    rw [Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card h2, Fintype.card_fin]
  rw [Matrix.rank_eq_finrank_span_row] at hrank
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K B'.row
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = k := by
    rw [← hrank, ← hspan, finrank_span_eq_card hli]
  let t : Finset (Fin n) := Finset.univ.map ⟨a, ha⟩
  have ht : t.card = k := by simp [t, hcard]
  let s : KSubset n k := ⟨t, ht⟩
  refine ⟨s, ?_⟩
  have hmem : ∀ i : Fin k, ∃ c : κ, a c = s.emb i := by
    intro i
    have h : s.emb i ∈ t := Finset.orderEmbOfFin_mem t ht i
    simp only [t, Finset.mem_map, Finset.mem_univ, true_and] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, hc⟩
  choose e he using hmem
  have he_inj : Function.Injective e := by
    intro i j hij
    apply s.emb.injective
    rw [← he i, ← he j, hij]
  have hrows : LinearIndependent K (B'.submatrix s.emb id).row := by
    have hfam : (B'.submatrix s.emb id).row = (B'.row ∘ a) ∘ e := by
      funext i j
      show B' (s.emb i) j = B' (a (e i)) j
      rw [he i]
    rw [hfam]
    exact hli.comp e he_inj
  have hdet : (B'.submatrix s.emb id).det ≠ 0 := by
    have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  intro h
  apply hdet
  have hmap : B'.submatrix s.emb id = (B.submatrix s.emb id).map (algebraMap R K) := rfl
  rw [hmap]
  show ((algebraMap R K).mapMatrix (B.submatrix s.emb id)).det = 0
  rw [← RingHom.map_det]
  unfold maxMinor at h
  rw [h, map_zero]

end GroundTheory.Variant₂.N1
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open Matrix Finset Equiv

abbrev KSubset (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

def KSubset.emb {n k : ℕ} (s : KSubset n k) : Fin k ↪o Fin n := s.1.orderEmbOfFin s.2

theorem KSubset.range_emb {n k : ℕ} (s : KSubset n k) : Set.range s.emb = (s.1 : Set (Fin n)) :=
  Finset.range_orderEmbOfFin _ _

variable {R : Type*} [CommRing R]

section CauchyBinet

variable {k n : ℕ}

private theorem det_mul_eq_sum_fun (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ p : Fin k → Fin n, (A.submatrix id p).det * ∏ i, B (p i) i := by
  simp only [det_apply', Matrix.mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ,
    submatrix_apply, id, sum_mul, prod_mul_distrib, mul_assoc]
  rw [Finset.sum_comm]

theorem det_mul_eq_sum_minors (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det =
      ∑ s : KSubset n k, (A.submatrix id s.emb).det * (B.submatrix s.emb id).det := by
  classical
  set F : (Fin k → Fin n) → R := fun p => (A.submatrix id p).det * ∏ i, B (p i) i with hF
  have hzero : ∀ p, ¬ Function.Injective p → F p = 0 := by
    intro p hp
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
      simp only [Function.Injective, not_forall] at hp
      obtain ⟨i, j, h, hne⟩ := hp
      exact ⟨i, j, h, hne⟩
    simp only [hF]
    rw [det_zero_of_column_eq hne (fun r => by simp [hij]), zero_mul]
  have hterm : ∀ (s : KSubset n k) (σ : Perm (Fin k)),
      F (s.emb ∘ σ) = (A.submatrix id s.emb).det * (Perm.sign σ * ∏ i, B (s.emb (σ i)) i) := by
    intro s σ
    simp only [hF]
    have : A.submatrix id (s.emb ∘ σ) = (A.submatrix id s.emb).submatrix id σ := rfl
    rw [this, det_permute']
    simp only [Function.comp_apply]
    ring
  have hs : ∀ s : KSubset n k, (A.submatrix id s.emb).det * (B.submatrix s.emb id).det =
      ∑ σ : Perm (Fin k), F (s.emb ∘ σ) := by
    intro s
    simp only [hterm, ← mul_sum]
    congr 1
    rw [det_apply']
    rfl
  have hprod := Fintype.sum_prod_type (fun x : KSubset n k × Perm (Fin k) => F (x.1.emb ∘ x.2))
  simp only at hprod
  rw [det_mul_eq_sum_fun, Finset.sum_congr rfl (fun s _ => hs s)]
  change ∑ p, F p = _
  rw [← hprod, ← Finset.sum_filter_of_ne (p := Function.Injective) (fun p _ h => by
      by_contra hp; exact h (hzero p hp))]
  symm
  refine Finset.sum_bij (fun x _ => x.1.emb ∘ x.2) ?_ ?_ ?_ ?_
  · intro x _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact x.1.emb.injective.comp x.2.injective
  · rintro ⟨s, σ⟩ _ ⟨t, τ⟩ _ h
    simp only at h
    have hst : s = t := by
      apply Subtype.ext
      have h1 : Set.range (s.emb ∘ σ) = Set.range (t.emb ∘ τ) := by rw [h]
      rw [Set.range_comp, Set.range_comp, σ.range_eq_univ, τ.range_eq_univ, Set.image_univ,
        Set.image_univ, KSubset.range_emb, KSubset.range_emb] at h1
      exact_mod_cast h1
    subst hst
    have : σ = τ := by
      ext i
      have := congrFun h i
      simp only [Function.comp_apply] at this
      exact congrArg Fin.val (s.emb.injective this)
    rw [this]
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hcard : (Finset.univ.image p).card = k := by
      rw [Finset.card_image_of_injective _ hp, Finset.card_univ, Fintype.card_fin]
    let s : KSubset n k := ⟨Finset.univ.image p, hcard⟩
    have hex : ∀ i, ∃ j, s.emb j = p i := by
      intro i
      have : p i ∈ (s.1 : Set (Fin n)) := by simp [s]
      rw [← KSubset.range_emb] at this
      exact this
    choose f hf using hex
    have hfinj : Function.Injective f := by
      intro i j hij
      apply hp
      rw [← hf i, ← hf j, hij]
    let σ : Perm (Fin k) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
    refine ⟨(s, σ), Finset.mem_univ _, ?_⟩
    funext i
    exact hf i
  · intro x _
    rfl

end CauchyBinet

section Minors

variable {m n k : ℕ}

def maxMinor (B : Matrix (Fin n) (Fin k) R) (s : KSubset n k) : R :=
  (B.submatrix s.emb id).det

end Minors

section Independence

variable {n k : ℕ}

theorem linearIndependent_col_iff_mulVec_eq_zero (B : Matrix (Fin n) (Fin k) R) :
    LinearIndependent R B.col ↔ ∀ v, B *ᵥ v = 0 → v = 0 := by
  rw [Fintype.linearIndependent_iff]
  have key : ∀ v : Fin k → R, ∑ j, v j • B.col j = B *ᵥ v := by
    intro v; ext i; simp [mulVec, dotProduct, Finset.sum_apply, col, mul_comm]
  constructor
  · intro h v hv
    funext j
    exact h v (by rw [key, hv]) j
  · intro h g hg j
    have := h g (by rw [← key, hg])
    exact congrFun this j

theorem exists_maxMinor_ne_zero_of_linearIndependent [IsDomain R]
    (B : Matrix (Fin n) (Fin k) R) (hB : LinearIndependent R B.col) :
    ∃ s : KSubset n k, maxMinor B s ≠ 0 :=
  _root_.GroundTheory.Variant₂.N1.exists_maxMinor_ne_zero_of_linearIndependent_alt B hB

end Independence

end GroundTheory.PAdicHodge
end

section -- merged from GroundTheory.PAdicHodge.SemilinearResidue
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open Polynomial Module Finset

namespace SemilinearResidue

section Poly

variable {k : Type*} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]


omit [CharP k p] in
include hp in
theorem two_le_pow {e : ℕ} (he : 0 < e) : 2 ≤ p ^ e :=
  calc 2 ≤ p := hp.out.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ e := Nat.pow_le_pow_right hp.out.pos he

variable {e : ℕ}

end Poly

section Vec

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem linearIndependent_of_notMem_span (v : ℕ → V) : ∀ m : ℕ,
    (∀ j < m, v j ∉ Submodule.span k (Set.range (fun i : Fin j => v i))) →
      LinearIndependent k (fun i : Fin m => v i) := by
  intro m
  induction m with
  | zero => exact fun _ => linearIndependent_empty_type
  | succ m ih =>
    intro h
    exact linearIndependent_finSucc'.mpr
      ⟨ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h m (Nat.lt_succ_self m)⟩


variable (k) in
theorem exists_rel [FiniteDimensional k V] (v : ℕ → V) :
    ∃ m, (∃ c : ℕ → k, v m = ∑ i ∈ range m, c i • v i) ∧
      LinearIndependent k (fun i : Fin m => v i) := by
  classical
  let P : ℕ → Prop := fun j => v j ∈ Submodule.span k (Set.range (fun i : Fin j => v i))
  have hex : ∃ j, P j := by
    by_contra hcon
    push Not at hcon
    have li := linearIndependent_of_notMem_span v (finrank k V + 1) (fun j _ => hcon j)
    have := li.fintype_card_le_finrank
    simp at this
  refine ⟨Nat.find hex, ?_, linearIndependent_of_notMem_span v _ (fun j hj => Nat.find_min hex hj)⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp (Nat.find_spec hex)
  refine ⟨fun i => if h : i < Nat.find hex then c ⟨i, h⟩ else 0, ?_⟩
  rw [← hc, Finset.sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [i.2]

variable {p : ℕ} [hp : Fact p.Prime] [CharP k p] {e : ℕ} {φ : V →+ V}


end Vec

end SemilinearResidue

end GroundTheory.PAdicHodge
end
