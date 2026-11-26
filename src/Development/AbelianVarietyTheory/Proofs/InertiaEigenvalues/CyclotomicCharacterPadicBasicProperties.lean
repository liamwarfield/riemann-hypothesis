module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexMatrixGaussSumNormIntegralGalois

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime]

theorem exists_primRoot_pow (m : ℕ) : ∃ ζ : Om l, IsPrimitiveRoot ζ (l ^ m) := by
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : NeZero ((l ^ m : ℕ) : Om l) := ⟨by exact_mod_cast pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ m)

theorem padic_norm_sub_le_trans {x y z : ℚ_[l]} {r : ℝ} (h1 : ‖x - y‖ ≤ r) (h2 : ‖y - z‖ ≤ r) :
    ‖x - z‖ ≤ r := by
  have : x - z = (x - y) + (y - z) := by ring
  rw [this]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

theorem norm_nat_sub_one_le_iff (a m : ℕ) :
    ‖(a : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) ↔ ((l : ℤ) ^ m) ∣ (a : ℤ) - 1 := by
  rw [← Padic.norm_int_le_pow_iff_dvd]
  push_cast
  rfl

theorem IsCyc.norm_sub_one_le_of_prim {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) (g : GQ l) (m : ℕ)
    {ζ : Om l} (hζ : IsPrimitiveRoot ζ (l ^ m)) (hg : g ζ = ζ) :
    ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
  obtain ⟨a, ha, hga⟩ := h g m ζ hζ.pow_eq_one
  refine padic_norm_sub_le_trans ha ?_
  rw [norm_nat_sub_one_le_iff]
  have h0 : ζ ≠ 0 := hζ.ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  have h1 : ζ ^ ((a : ℤ) - 1) = 1 := by
    rw [zpow_sub₀ h0, zpow_natCast, ← hga, hg, zpow_one, div_self h0]
  have := (hζ.zpow_eq_one_iff_dvd _).1 h1
  exact_mod_cast this

theorem IsCyc.fix_iff {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) (g : GQ l) (m : ℕ) :
    (∀ ζ : Om l, ζ ^ (l ^ m) = 1 → g ζ = ζ) ↔ ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
  constructor
  · intro hg
    obtain ⟨ζ, hζ⟩ := exists_primRoot_pow (l := l) m
    exact h.norm_sub_one_le_of_prim g m hζ (hg ζ hζ.pow_eq_one)
  · intro hg ζ hζ
    obtain ⟨a, ha, hga⟩ := h g m ζ hζ
    rw [norm_sub_rev] at ha
    obtain ⟨c, hc⟩ := (norm_nat_sub_one_le_iff a m).1 (padic_norm_sub_le_trans ha hg)
    have h0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hζ
      exact zero_ne_one hζ
    have ha' : (a : ℤ) = ((l ^ m : ℕ) : ℤ) * c + 1 := by push_cast; linarith
    rw [hga, ← zpow_natCast, ha', zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, one_mul,
      zpow_one]

theorem IsCyc.norm_le_one {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) (g : GQ l) :
    ‖(χ g : ℚ_[l])‖ ≤ 1 := by
  obtain ⟨a, ha, -⟩ := h g 0 1 (one_pow _)
  have h2 : ‖(a : ℚ_[l]) - 0‖ ≤ 1 := by
    rw [sub_zero]; exact IsUltrametricDist.norm_natCast_le_one _ _
  simp only [Nat.cast_zero, neg_zero, zpow_zero] at ha
  simpa using padic_norm_sub_le_trans ha h2

theorem IsCyc.norm_eq_one {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) (g : GQ l) :
    ‖(χ g : ℚ_[l])‖ = 1 := by
  have h1 := h.norm_le_one g
  have h2 := h.norm_le_one g⁻¹
  have h3 : ‖(χ g : ℚ_[l])‖ * ‖(χ g⁻¹ : ℚ_[l])‖ = 1 := by
    rw [← norm_mul, ← Units.val_mul, ← map_mul]; simp
  have h4 := norm_nonneg (χ g : ℚ_[l])
  nlinarith

theorem exists_zpow_neg_lt {ε : ℝ} (hε : 0 < ε) : ∃ m : ℕ, (l : ℝ) ^ (-(m : ℤ)) < ε :=
  PadicInt.exists_pow_neg_lt l hε

theorem IsCyc.continuous {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) :
    Continuous (fun g => (χ g : ℚ_[l])) := by
  change Continuous ((Units.coeHom ℚ_[l]).comp χ)
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_zpow_neg_lt (l := l) hε
  obtain ⟨ζ, hζ⟩ := exists_primRoot_pow (l := l) m
  rw [Filter.Eventually, krullTopology_mem_nhds_one_iff]
  refine ⟨IntermediateField.adjoin ℚ_[l] {ζ},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ), ?_⟩
  intro g hg
  have hg' : g ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ
    (IntermediateField.mem_adjoin_simple_self _ _)
  have := h.norm_sub_one_le_of_prim g m hζ hg'
  simp only [Set.mem_setOf_eq, map_one, dist_eq_norm]
  exact this.trans_lt hm

theorem mem_fixingSubgroup_adjoin_iff (S : Set (Om l)) (g : GQ l) :
    g ∈ (IntermediateField.adjoin ℚ_[l] S).fixingSubgroup ↔ ∀ x ∈ S, g x = x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hg x hx
    exact hg x (IntermediateField.subset_adjoin _ _ hx)
  · intro hg x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => exact hg x hx
    | algebraMap x => exact g.commutes x
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]

theorem cyc_basic : ∀ (l : ℕ) [Fact l.Prime] (χ : GQ l →* ℚ_[l]ˣ), IsCyc χ → (∀ g, ‖(χ g : ℚ_[l])‖ = 1) ∧ Continuous (fun g => (χ g : ℚ_[l])) ∧ ∀ (K : FinExt l) (g : GQ l), g ∈ (K0 K).fixingSubgroup → ((∀ j : ℕ, g ∈ Gj K j ↔ ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ))) ∧ (g ∈ Hinf K ↔ χ g = 1)) := by
  intro l _ χ h
  refine ⟨h.norm_eq_one, h.continuous, fun K g hg => ⟨fun j => ?_, ?_⟩⟩
  · rw [Gj, Ks, IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf,
      mem_fixingSubgroup_adjoin_iff, ← h.fix_iff]
    exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
  · rw [Hinf, Kinf, IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf,
      mem_fixingSubgroup_adjoin_iff]
    constructor
    · rintro ⟨-, h2⟩
      by_contra hne
      have hpos : 0 < ‖(χ g : ℚ_[l]) - 1‖ := by
        rw [norm_pos_iff, sub_ne_zero]
        exact fun e => hne (Units.ext e)
      obtain ⟨m, hm⟩ := exists_zpow_neg_lt (l := l) hpos
      exact absurd ((h.fix_iff g m).1 fun ζ hζ => h2 ζ ⟨m, hζ⟩) (not_le.2 hm)
    · intro h1
      refine ⟨hg, ?_⟩
      rintro x ⟨m, hx⟩
      refine (h.fix_iff g m).2 ?_ x hx
      rw [h1, Units.val_one, sub_self, norm_zero]
      positivity

end GlobalTheory.Cyc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicPropertiesStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicCharacterPadic_basic_properties : ∀ (l : ℕ) [Fact l.Prime] (χ : GQ l →* ℚ_[l]ˣ), IsCyc χ → (∀ g, ‖(χ g : ℚ_[l])‖ = 1) ∧ Continuous (fun g => (χ g : ℚ_[l])) ∧ ∀ (K : FinExt l) (g : GQ l), g ∈ (K0 K).fixingSubgroup → ((∀ j : ℕ, g ∈ Gj K j ↔ ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ))) ∧ (g ∈ Hinf K ↔ χ g = 1)) := by
  first | exact @GlobalTheory.Cyc.cyc_basic | exact GlobalTheory.Cyc.cyc_basic | (intros; apply GlobalTheory.Cyc.cyc_basic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplex
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem _root_.GlobalTheory.Cyc.norm_natCast_prime_padicComplex (l : ℕ) [Fact l.Prime] :
    ‖(l : PadicComplex l)‖ = (l : ℝ)⁻¹ := by
  have h1 := PadicComplex.norm_extends l (algebraMap ℚ_[l] (PadicAlgCl l) l)
  rw [PadicAlgCl.norm_extends, Padic.norm_p, map_natCast] at h1
  rw [← h1]
  norm_cast

theorem _root_.GlobalTheory.Cyc.norm_sub_one_le_of_isPrimitiveRoot {K : Type*} [NormedField K]
    [IsUltrametricDist K]
    {n : ℕ} (hn : n ≠ 0) {ζ μ : K} (hζ : IsPrimitiveRoot ζ n) (hμ : μ ^ n = 1) :
    ‖μ - 1‖ ≤ ‖ζ - 1‖ := by
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨k, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  have hnorm : ‖ζ‖ = 1 := by
    have h := congrArg norm hζ.pow_eq_one
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hn).mp h
  clear hμ
  induction k with
  | zero => simp
  | succ k ih =>
    have : ζ ^ (k + 1) - 1 = ζ ^ k * (ζ - 1) + (ζ ^ k - 1) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
    rw [norm_mul, norm_pow, hnorm, one_pow, one_mul]

theorem _root_.GlobalTheory.Cyc.norm_primitiveRoot_sub_one (l : ℕ) [hl : Fact l.Prime] (j : ℕ)
    (hj : 1 ≤ j) (ζ : PadicComplex l) (hζ : IsPrimitiveRoot ζ (l ^ j)) :
    ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by
  have hpos : 0 < l ^ j := pow_pos hl.out.pos j
  have hall : ∀ μ ∈ primitiveRoots (l ^ j) (PadicComplex l), ‖1 - μ‖ = ‖ζ - 1‖ := by
    intro μ hμ
    rw [mem_primitiveRoots hpos] at hμ
    rw [norm_sub_rev]
    exact le_antisymm
      (_root_.GlobalTheory.Cyc.norm_sub_one_le_of_isPrimitiveRoot hpos.ne' hζ hμ.pow_eq_one)
      (_root_.GlobalTheory.Cyc.norm_sub_one_le_of_isPrimitiveRoot hpos.ne' hμ hζ.pow_eq_one)
  have heval :=
    congrArg (Polynomial.eval 1) (Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ)
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [Polynomial.eval_one_cyclotomic_prime_pow, Polynomial.eval_prod] at heval
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at heval
  have hprod := congrArg norm heval
  rw [_root_.GlobalTheory.Cyc.norm_natCast_prime_padicComplex, norm_prod, Finset.prod_congr rfl hall, Finset.prod_const,
    hζ.card_primitiveRoots, Nat.totient_prime_pow hl.out (Nat.succ_pos k)] at hprod
  simp only [Nat.succ_sub_one, Nat.add_sub_cancel] at hprod ⊢
  have hN : l ^ k * (l - 1) ≠ 0 :=
    Nat.mul_ne_zero (pow_ne_zero _ hl.out.ne_zero) (Nat.sub_ne_zero_of_lt hl.out.one_lt)
  have hcast : ((l ^ k * (l - 1) : ℕ) : ℝ) = (l : ℝ) ^ k * ((l : ℝ) - 1) := by
    push_cast [Nat.cast_sub hl.out.one_le]
    ring
  rw [← Real.pow_rpow_inv_natCast (norm_nonneg (ζ - 1)) hN, ← hprod, hcast,
    Real.inv_rpow (Nat.cast_nonneg l), ← Real.rpow_neg (Nat.cast_nonneg l), neg_div, one_div]

end GlobalTheory.Cyc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPrimitiveRootPrimePowSubOnePadicComplexStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex : ∀ (l : ℕ) [Fact l.Prime] (j : ℕ), 1 ≤ j → ∀ ζ : PadicComplex l, IsPrimitiveRoot ζ (l ^ j) → ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by
  first | exact @GlobalTheory.Cyc.norm_primitiveRoot_sub_one | exact GlobalTheory.Cyc.norm_primitiveRoot_sub_one | (intros; apply GlobalTheory.Cyc.norm_primitiveRoot_sub_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplex
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem eventually_apply_eq {l : ℕ} [Fact l.Prime] (x : Om l) (g₀ : GQ l) :
    ∀ᶠ g : GQ l in nhds g₀, g x = g₀ x := by
  have hS := stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) x
  have hc : Continuous fun g : GQ l => g₀⁻¹ * g := continuous_const.mul continuous_id
  have hmem : (fun g : GQ l => g₀⁻¹ * g) g₀ ∈ (MulAction.stabilizer (GQ l) x : Set (GQ l)) := by
    simp
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hS.mem_nhds hmem)] with g hg
  have hg' : (g₀⁻¹ * g) x = x := hg
  have := congrArg g₀ hg'
  simpa [AlgEquiv.mul_apply] using this

theorem IsActC.continuous_orbit (l : ℕ) [Fact l.Prime]
    (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (h : IsActC act) (y : PadicComplex l) :
    Continuous (fun g => act g y) := by
  obtain ⟨hext, hiso⟩ := h
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨x, hx⟩ : ∃ x : Om l, dist y (x : PadicComplex l) < ε / 2 :=
    UniformSpace.Completion.denseRange_coe.exists_dist_lt y (half_pos hε)
  filter_upwards [eventually_apply_eq x g₀] with g hg
  have h1 : act g y - act g₀ y = act g (y - x) - act g₀ (y - x) := by
    rw [map_sub, map_sub, hext g x, hext g₀ x, hg]
    ring
  rw [dist_eq_norm, h1]
  calc ‖act g (y - x) - act g₀ (y - x)‖ ≤ ‖act g (y - x)‖ + ‖act g₀ (y - x)‖ := norm_sub_le _ _
    _ = 2 * ‖y - x‖ := by rw [hiso, hiso]; ring
    _ < ε := by rw [← dist_eq_norm]; linarith

end GlobalTheory.Cyc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplexStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_orbit_padicComplex : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act → ∀ y : PadicComplex l, Continuous (fun g => act g y) := by
  first | exact @GlobalTheory.Cyc.IsActC.continuous_orbit | exact GlobalTheory.Cyc.IsActC.continuous_orbit | (intros; apply GlobalTheory.Cyc.IsActC.continuous_orbit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicNormZpowSubOnePadicValInt
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicNormZpowSubOnePadicValInt
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc.LiftExp

variable {l : ℕ} [hl : Fact l.Prime]

theorem one_add_pow_expand (x : ℚ_[l]) (hx : ‖x‖ ≤ 1) (n : ℕ) :
    ∃ r : ℚ_[l], ‖r‖ ≤ 1 ∧
      (1 + x) ^ n - 1 = n * x + ((n.choose 2 : ℕ) * x ^ 2 + x ^ 3 * r) := by
  induction n with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr, h⟩ := ih
    refine ⟨(n.choose 2 : ℕ) + (r + x * r), ?_, ?_⟩
    · refine (Padic.nonarchimedean _ _).trans (max_le ?_ ((Padic.nonarchimedean _ _).trans
        (max_le hr ?_)))
      · exact IsUltrametricDist.norm_natCast_le_one _ _
      · rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hr
    · have h2 : (1 + x) ^ n = 1 + (n * x + ((n.choose 2 : ℕ) * x ^ 2 + x ^ 3 * r)) := by
        rw [← h]; ring
      rw [pow_succ, h2, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
      push_cast
      ring

theorem norm_add_of_lt {a b : ℚ_[l]} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [Padic.add_eq_max_of_ne h.ne', max_eq_left h.le]

theorem one_lt_l : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt

theorem zpow_lt {a b : ℤ} (h : a < b) : (l : ℝ) ^ a < (l : ℝ) ^ b :=
  zpow_lt_zpow_right₀ one_lt_l h

theorem norm_pow_sub_one_of (j : ℕ) (hj : 1 ≤ j) (u : ℚ_[l]) (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)))
    (n : ℕ) (e c : ℤ) (hn : ‖(n : ℚ_[l])‖ = (l : ℝ) ^ (-e))
    (hc : ‖((n.choose 2 : ℕ) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-c)) (h1 : e < c + j) (h2 : e < 2 * j) :
    ‖u ^ n - 1‖ = (l : ℝ) ^ (-((j : ℤ) + e)) := by
  have hl0 : (l : ℝ) ≠ 0 := (zero_lt_one.trans one_lt_l).ne'
  have hx : ‖u - 1‖ ≤ 1 := by
    rw [hu]; exact zpow_le_one_of_nonpos₀ one_lt_l.le (by omega)
  obtain ⟨r, hr, h⟩ := one_add_pow_expand (u - 1) hx n
  rw [add_sub_cancel] at h
  have hm : ‖(n : ℚ_[l]) * (u - 1)‖ = (l : ℝ) ^ (-((j : ℤ) + e)) := by
    rw [norm_mul, hn, hu, ← zpow_add₀ hl0]; congr 1; ring
  rw [h, norm_add_of_lt, hm]
  rw [hm]
  refine (Padic.nonarchimedean _ _).trans_lt (max_lt ?_ ?_)
  · rw [norm_mul, norm_pow, hu]
    calc _ ≤ (l : ℝ) ^ (-c) * ((l : ℝ) ^ (-(j : ℤ))) ^ 2 := by gcongr
      _ = (l : ℝ) ^ (-c + (-(j : ℤ)) * 2) := by
        rw [zpow_add₀ hl0, zpow_mul]; norm_cast
      _ < _ := zpow_lt (by omega)
  · rw [norm_mul, norm_pow, hu]
    calc _ ≤ ((l : ℝ) ^ (-(j : ℤ))) ^ 3 * 1 := by gcongr
      _ = (l : ℝ) ^ ((-(j : ℤ)) * 3) := by
        rw [mul_one, zpow_mul]; norm_cast
      _ < _ := zpow_lt (by omega)

theorem norm_pow_coprime (j : ℕ) (hj : 1 ≤ j) (u : ℚ_[l]) (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)))
    (n : ℕ) (hn : ¬ l ∣ n) : ‖u ^ n - 1‖ = (l : ℝ) ^ (-(j : ℤ)) := by
  have := norm_pow_sub_one_of j hj u hu n 0 0
    (by
      rw [neg_zero, zpow_zero, Padic.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hn)
    (by rw [neg_zero, zpow_zero]; exact IsUltrametricDist.norm_natCast_le_one _ _)
    (by omega) (by omega)
  simpa using this

theorem norm_pow_prime (j : ℕ) (hj : Lev l j) (u : ℚ_[l]) (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) :
    ‖u ^ l - 1‖ = (l : ℝ) ^ (-((j + 1 : ℕ) : ℤ)) := by
  have hn : ‖(l : ℚ_[l])‖ = (l : ℝ) ^ (-(1 : ℤ)) := by simp
  have hj1 := hj.1
  push_cast
  by_cases h2 : l = 2
  · have := hj.2 h2
    exact norm_pow_sub_one_of j hj.1 u hu l 1 0 hn
      (by rw [neg_zero, zpow_zero]; exact IsUltrametricDist.norm_natCast_le_one _ _)
      (by omega) (by omega)
  · have h3 : 2 < l := lt_of_le_of_ne hl.out.two_le (Ne.symm h2)
    obtain ⟨m, hm⟩ := hl.out.dvd_choose_self (k := 2) two_ne_zero h3
    refine norm_pow_sub_one_of j hj.1 u hu l 1 1 hn ?_ (by omega) (by omega)
    rw [hm, Nat.cast_mul, norm_mul, hn]
    exact mul_le_of_le_one_right (by positivity) (IsUltrametricDist.norm_natCast_le_one _ _)

theorem norm_pow_prime_pow (a : ℕ) (j : ℕ) (hj : Lev l j) (u : ℚ_[l])
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) :
    ‖u ^ (l ^ a) - 1‖ = (l : ℝ) ^ (-((j + a : ℕ) : ℤ)) := by
  induction a with
  | zero => simpa using hu
  | succ a ih =>
    have h : Lev l (j + a) := ⟨by have := hj.1; omega, fun h => by have := hj.2 h; omega⟩
    rw [pow_succ, pow_mul]
    exact norm_pow_prime (j + a) h _ ih

theorem norm_pow_nat (j : ℕ) (hj : Lev l j) (u : ℚ_[l])
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) (n : ℕ) (hn : n ≠ 0) :
    ‖u ^ n - 1‖ = (l : ℝ) ^ (-((j : ℤ) + (padicValNat l n : ℤ))) := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hl.out.ne_one
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  rw [Nat.padicValNat_def, Nat.multiplicity_mul (pow_ne_zero _ hl.out.ne_zero) hm0,
    Nat.multiplicity_prime_pow,
    padicValNat.eq_zero_of_not_dvd hm, pow_mul,
    norm_pow_coprime (j + a) (by have := hj.1; omega) _ (norm_pow_prime_pow a j hj u hu) m hm]
  push_cast
  simp

theorem norm_zpow_sub_one : ∀ (l : ℕ) [Fact l.Prime] (j : ℕ), Lev l j → ∀ u : ℚ_[l],
    ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)) → ∀ k : ℤ, k ≠ 0 →
      ‖u ^ k - 1‖ = (l : ℝ) ^ (-((j : ℤ) + (padicValInt l k : ℤ))) := by
  intro l _ j hj u hu k hk
  have hu1 : ‖u‖ = 1 := by
    have h : ‖u - 1‖ < ‖(1 : ℚ_[l])‖ := by
      rw [hu, norm_one]
      exact zpow_lt_one_of_neg₀ one_lt_l (by have := hj.1; omega)
    have := norm_add_of_lt h
    simpa using this
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  have key := norm_pow_nat j hj u hu k.natAbs (Int.natAbs_ne_zero.2 hk)
  unfold padicValInt
  rw [← Nat.padicValNat_def, ← key]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simp
  · rw [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast]
    have : (u ^ n)⁻¹ - 1 = -((u ^ n - 1) * (u ^ n)⁻¹) := by field_simp; ring
    rw [this, norm_neg, norm_mul, norm_inv, norm_pow, hu1]; simp

end GlobalTheory.Cyc.LiftExp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicNormZpowSubOnePadicValIntStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt : ∀ (l : ℕ) [Fact l.Prime] (j : ℕ), Lev l j → ∀ u : ℚ_[l], ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)) → ∀ k : ℤ, k ≠ 0 → ‖u ^ k - 1‖ = (l : ℝ) ^ (-((j : ℤ) + (padicValInt l k : ℤ))) := by
  first | exact @GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one | exact GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one | (intros; apply GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherel
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.SelfDualLat

theorem isLC_indicator_one {X : Type} [TopologicalSpace X] (s : Set X) (h : IsClopen s) :
    IsLocallyConstant (s.indicator (fun _ => (1 : ℂ))) := by
  classical
  intro B
  rw [Set.indicator_preimage, Set.ite]
  refine (IsOpen.inter ?_ h.isOpen).union ?_
  · rw [Set.preimage_const]; split_ifs <;> simp
  · rw [Set.diff_eq]
    refine IsOpen.inter ?_ h.isClosed.isOpen_compl
    change IsOpen ((fun _ : X => (0:ℂ)) ⁻¹' B)
    rw [Set.preimage_const]; split_ifs <;> simp

theorem topo : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V], LocallyCompactSpace V ∧ SecondCountableTopology V ∧ T2Space V ∧ IsTopologicalAddGroup V := by
  intro F E _ _ _ _ _ V _ _ _ _ _
  haveI := (inferInstance : Unram F E).lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V
  haveI : ContinuousNeg V := ⟨by
    have := IsModuleTopology.continuous_of_linearMap (R := F) (A := V) (B := V) (-LinearMap.id)
    exact this⟩
  let e : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := (Module.finBasis F V).equivFun
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc' : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : V ≃ₜ (Fin (Module.finrank F V) → F) := ⟨e.toEquiv, hc, hc'⟩
  exact ⟨h.isOpenEmbedding.locallyCompactSpace, h.isEmbedding.secondCountableTopology, h.isEmbedding.t2Space,
    IsTopologicalAddGroup.mk⟩
theorem orth : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] [IsTopologicalAddGroup V] (β : LinearMap.BilinForm F V) (μ : Measure V), μ.IsAddHaarMeasure → ∀ M : AddSubgroup V, IsOpen (M : Set V) → IsCompact (M : Set V) → ∀ y, ∫ x in (M : Set V), ψ (β x y) ∂μ = Set.indicator {y | ∀ x ∈ M, ψ (β x y) = 1} (fun _ => ((μ M).toReal : ℂ)) y := by
  intro F E _ _ _ _ _ ψ hψ V _ _ _ _ _ _ _ _ β μ hμ M hMo hMc y
  classical
  by_cases hy : y ∈ {y | ∀ x ∈ M, ψ (β x y) = 1}
  · rw [Set.indicator_of_mem hy, setIntegral_congr_fun hMo.measurableSet (fun x hx => hy x hx)]
    simp [Measure.real]
  · rw [Set.indicator_of_notMem hy]
    simp only [Set.mem_setOf_eq, not_forall] at hy
    obtain ⟨x0, hx0, hne⟩ := hy
    have ht := integral_add_left_eq_self (μ := μ) (fun x => (M : Set V).indicator (fun x => ψ (β x y)) x) x0
    have hpt : ∀ x, (M : Set V).indicator (fun x => ψ (β x y)) (x0 + x) =
        ψ (β x0 y) * (M : Set V).indicator (fun x => ψ (β x y)) x := by
      intro x
      by_cases hx : x ∈ M
      · have : x0 + x ∈ M := M.add_mem hx0 hx
        simp [Set.indicator_of_mem (show x0 + x ∈ (M : Set V) from this),
          Set.indicator_of_mem (show x ∈ (M : Set V) from hx), map_add, AddChar.map_add_eq_mul]
      · have : x0 + x ∉ M := fun h => hx (by simpa using M.sub_mem h hx0)
        simp [Set.indicator_of_notMem (show x0 + x ∉ (M : Set V) from this),
          Set.indicator_of_notMem (show x ∉ (M : Set V) from hx)]
    simp_rw [hpt] at ht
    rw [integral_const_mul, integral_indicator hMo.measurableSet] at ht
    have h0 : (ψ (β x0 y) - 1) * ∫ x in (M : Set V), ψ (β x y) ∂μ = 0 := by rw [sub_mul, one_mul, ht, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
theorem planch : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [IsTopologicalAddGroup V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → ∀ μ : Measure V, SelfDual μ (fun x y => ψ (β x y)) → ∀ f, IsTest f → ∫ y, ‖fourB μ (fun x y => ψ (β x y)) f y‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ ψ hψ V _ _ _ _ _ _ _ _ _ _ _ β hβs hβn μ hsd f hf
  haveI := hsd.1
  have hψ' := (GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ
  have hI := GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ V β hβs hβn
  set B : V → V → ℂ := fun x y => ψ (β x y) with hB
  set g := fourB μ B f with hgdef
  have hg : IsTest g := hI.2 μ hsd.1 f hf
  have hψc : Continuous (fun t : F => ψ t) := hψ'.1.continuous
  have hβc : Continuous (fun p : V × V => β p.1 p.2) := IsModuleTopology.continuous_bilinear_of_finite_left β
  have hfc : Continuous f := hf.1.continuous
  have hgc : Continuous g := hg.1.continuous
  have hfi : Integrable f μ := hfc.integrable_of_hasCompactSupport hf.2
  have hgi : Integrable g μ := hgc.integrable_of_hasCompactSupport hg.2
  have key : ∀ h : V → ℂ, ((∫ y, ‖h y‖ ^ 2 ∂μ : ℝ) : ℂ) = ∫ y, h y * (starRingEnd ℂ) (h y) ∂μ := by
    intro h
    rw [← integral_complex_ofReal]
    congr 1; ext y
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hconj : ∀ t : F, (starRingEnd ℂ) (ψ t) = ψ (-t) := by
    intro t
    rw [AddChar.map_neg_eq_inv]
    have h1 : ‖ψ t‖ = 1 := hψ'.2.1 t
    have h0 : ψ t ≠ 0 := by intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1]; simp
  have hinner : ∀ x, ∫ y, ψ (β x y) * (starRingEnd ℂ) (g y) ∂μ = (starRingEnd ℂ) (f x) := by
    intro x
    have := hsd.2 f hf (-x)
    rw [neg_neg] at this
    rw [← this]
    show _ = (starRingEnd ℂ) (∫ y, g y * B y (-x) ∂μ)
    rw [← integral_conj]
    congr 1; ext y
    rw [map_mul, hconj]
    simp only [map_neg, neg_neg, hβs.eq x y]
    ring
  have hint : Integrable (Function.uncurry fun y x => f x * ψ (β x y) * (starRingEnd ℂ) (g y)) (μ.prod μ) := by
    refine Integrable.mono' ((hgi.norm).mul_prod hfi.norm) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      exact ((hfc.comp continuous_snd).mul (hψc.comp (hβc.comp continuous_swap))).mul
        (Complex.continuous_conj.comp (hgc.comp continuous_fst))
    · refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [Function.uncurry, norm_mul, hψ'.2.1, mul_one, Complex.norm_conj]
      rw [mul_comm]
  apply Complex.ofReal_injective
  rw [key, key]
  calc ∫ y, g y * (starRingEnd ℂ) (g y) ∂μ
      = ∫ y, ∫ x, f x * ψ (β x y) * (starRingEnd ℂ) (g y) ∂μ ∂μ := by
        congr 1; ext y
        rw [hgdef]; unfold fourB
        rw [← integral_mul_const]
    _ = ∫ x, ∫ y, f x * ψ (β x y) * (starRingEnd ℂ) (g y) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ x, f x * (starRingEnd ℂ) (f x) ∂μ := by
        congr 1; ext x
        simp_rw [mul_assoc]
        rw [integral_const_mul, hinner]

end GlobalTheory.JR.SelfDualLat

open GlobalTheory.JR.SelfDualLat in
theorem GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → ∀ μ : Measure V, μ.IsAddHaarMeasure → (∀ M : AddSubgroup V, IsOpen (M : Set V) → IsCompact (M : Set V) → (SelfDual μ (fun x y => ψ (β x y)) ↔ μ M * μ {y | ∀ x ∈ M, ψ (β x y) = 1} = 1) ∧ ∀ y, ∫ x in (M : Set V), ψ (β x y) ∂μ = Set.indicator {y | ∀ x ∈ M, ψ (β x y) = 1} (fun _ => ((μ M).toReal : ℂ)) y) ∧ (SelfDual μ (fun x y => ψ (β x y)) → ∀ f, IsTest f → ∫ y, ‖fourB μ (fun x y => ψ (β x y)) f y‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) := by
  intro F E _ _ _ _ _ ψ hψ V _ _ _ _ _ _ _ β hβs hβn μ hμ
  obtain ⟨hLC, hSC, hT2, hTG⟩ := topo F E V
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hTG
  have hI := GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ V β hβs hβn
  have fwd : ∀ ν : Measure V, SelfDual ν (fun x y => ψ (β x y)) → ∀ M : AddSubgroup V, IsOpen (M : Set V) →
      IsCompact (M : Set V) → ν M * ν {y | ∀ x ∈ M, ψ (β x y) = 1} = 1 := by
    intro ν hν M hMo hMc
    haveI := hν.1
    set P : Set V := {y | ∀ x ∈ M, ψ (β x y) = 1} with hP
    set g : V → ℂ := (M : Set V).indicator (fun _ => 1) with hg
    have hMcl : IsClosed (M : Set V) := AddSubgroup.isClosed_of_isOpen M hMo
    have hgt : IsTest g := ⟨isLC_indicator_one _ ⟨hMcl, hMo⟩,
      HasCompactSupport.intro hMc (fun x hx => Set.indicator_of_notMem hx _)⟩
    have h1 : ∀ x, fourB ν (fun x y => ψ (β x y)) g x = P.indicator (fun _ => ((ν M).toReal : ℂ)) x := by
      intro x
      rw [← orth F E ψ hψ V β ν hν.1 M hMo hMc x]
      unfold fourB
      rw [← integral_indicator hMo.measurableSet]
      congr 1; ext t
      by_cases ht : t ∈ (M : Set V) <;> simp [hg, ht]
    have hc : ((ν M).toReal : ℂ) ≠ 0 := by
      have h0 : ν M ≠ 0 := (hMo.measure_pos ν ⟨0, M.zero_mem⟩).ne'
      have ht : ν M ≠ ⊤ := hMc.measure_lt_top.ne
      exact_mod_cast (ENNReal.toReal_pos h0 ht).ne'
    have hft := hI.2 ν hν.1 g hgt
    have hPm : MeasurableSet P := by
      have : P = (fourB ν (fun x y => ψ (β x y)) g) ⁻¹' {((ν M).toReal : ℂ)} := by
        ext y
        show y ∈ P ↔ fourB ν (fun x y => ψ (β x y)) g y = ((ν M).toReal : ℂ)
        rw [h1]
        by_cases hy : y ∈ P
        · simp [Set.indicator_of_mem hy, hy]
        · rw [Set.indicator_of_notMem hy]; exact ⟨fun h => absurd h hy, fun h => absurd h.symm hc⟩
      rw [this]; exact (hft.1.isOpen_fiber _).measurableSet
    have h2 := hν.2 g hgt 0
    rw [neg_zero, show g 0 = 1 by simp [hg, M.zero_mem]] at h2
    have h3 : fourB ν (fun x y => ψ (β x y)) (fourB ν (fun x y => ψ (β x y)) g) 0 =
        (ν P).toReal * (ν M).toReal := by
      show ∫ x, fourB ν (fun x y => ψ (β x y)) g x * ψ (β x 0) ∂ν = _
      simp_rw [h1, map_zero, AddChar.map_zero_eq_one, mul_one]
      rw [integral_indicator_const _ hPm]
      simp [Measure.real]
    rw [h3] at h2
    rw [← ENNReal.toReal_eq_one_iff, ENNReal.toReal_mul]
    have h4 : (((ν M).toReal * (ν P).toReal : ℝ) : ℂ) = 1 := by push_cast; linear_combination h2
    exact_mod_cast h4
  refine ⟨fun M hMo hMc => ⟨⟨fun hsd => fwd μ hsd M hMo hMc, fun h => ?_⟩, orth F E ψ hψ V β μ hμ M hMo hMc⟩,
    fun hsd f hf => planch F E ψ hψ V β hβs hβn μ hsd f hf⟩
  obtain ⟨⟨μ0, hμ0, -⟩, -⟩ := hI
  haveI := hμ0.1
  have hsc : μ = Measure.addHaarScalarFactor μ μ0 • μ0 := Measure.isAddLeftInvariant_eq_smul μ μ0
  set c := Measure.addHaarScalarFactor μ μ0 with hcdef
  have h0 := fwd μ0 hμ0 M hMo hMc
  rw [hsc] at h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
  have hcc : ((c * c : NNReal) : ENNReal) = 1 := by
    calc ((c * c : NNReal) : ENNReal) = (c : ENNReal) * c * (μ0 M * μ0 {y | ∀ x ∈ M, ψ (β x y) = 1}) := by
          rw [h0, mul_one, ENNReal.coe_mul]
      _ = (c : ENNReal) * μ0 M * ((c : ENNReal) * μ0 {y | ∀ x ∈ M, ψ (β x y) = 1}) := by ring
      _ = 1 := h
  have hcc' : (c : ℝ) * c = 1 := by exact_mod_cast (ENNReal.coe_eq_one.1 hcc)
  have hc1 : c = 1 := by
    have : (c : ℝ) = 1 := by nlinarith [c.2]
    exact_mod_cast this
  have : μ = μ0 := by rw [hsc, hc1, one_smul]
  rw [this]; exact hμ0
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualIffLatticeVolumeAndPlancherelStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → ∀ μ : Measure V, μ.IsAddHaarMeasure → (∀ M : AddSubgroup V, IsOpen (M : Set V) → IsCompact (M : Set V) → (SelfDual μ (fun x y => ψ (β x y)) ↔ μ M * μ {y | ∀ x ∈ M, ψ (β x y) = 1} = 1) ∧ ∀ y, ∫ x in (M : Set V), ψ (β x y) ∂μ = Set.indicator {y | ∀ x ∈ M, ψ (β x y) = 1} (fun _ => ((μ M).toReal : ℂ)) y) ∧ (SelfDual μ (fun x y => ψ (β x y)) → ∀ f, IsTest f → ∫ y, ‖fourB μ (fun x y => ψ (β x y)) f y‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) := by
  first | exact @GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel | exact GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel | (intros; apply GlobalTheory.JR.selfDual_iff_lattice_volume_and_plancherel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SesqAsym
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.SesqAsym

theorem trace_σ {K : UQ} (B : InvAlg K) (a : B.A) :
    Algebra.trace K.E B.A (B.σ a) = K.c (Algebra.trace K.E B.A a) := by
  have h := Algebra.trace_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) a
  rw [h, RingEquiv.apply_symm_apply]

theorem sesq_asym : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → (∃ β : B.Aˣ, B.σ (β : B.A) = β * (ε * B.g)) ∧ ∀ (s : B.A → B.A → K.E), (∀ x y z, s (x + y) z = s x z + s y z) → (∀ (c : K.E) x z, s (c • x) z = c * s x z) → (∀ y, (∀ z, s y z = 0) → y = 0) → (∀ y z, K.c (s z y) = s (ε * B.g * y) z) → ∃ β : B.Aˣ, B.σ (β : B.A) = β * (ε * B.g) ∧ ∀ y z, s y z = B.herm β y z := by
  intro K B hg hP ε hε
  have hσε : B.σ ε = ε := by rcases hε with rfl | rfl <;> simp
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  set u := ε * B.g with hu_def
  have hu : u * B.σ u = 1 := by
    rw [hu_def, map_mul, hσε]
    calc ε * B.g * (ε * B.σ B.g) = (ε * ε) * (B.g * B.σ B.g) := by ring
      _ = 1 := by rw [hεε, hg, one_mul]
  refine ⟨GlobalTheory.T.exists_unit_sigma_eq_mul_invAlg K B u hu, ?_⟩
  intro s hadd hlin hnd hsym
  have hvu : B.σ u * u = 1 := by rw [mul_comm]; exact hu

  have hsym' : ∀ y z, s y z = K.c (s z (B.σ u * y)) := by
    intro y z
    rw [hsym, ← mul_assoc, hu, one_mul]
  have hadd2 : ∀ y z z', s y (z + z') = s y z + s y z' := by
    intro y z z'
    rw [hsym', hadd, map_add (f := _), ← hsym', ← hsym']
  have hlin2 : ∀ (e : K.E) y z, s y (e • z) = K.c e * s y z := by
    intro e y z
    rw [hsym', hlin, map_mul, ← hsym']
  have hsu : ∀ y z, s (u * y) (u * z) = s y z := by
    intro y z
    rw [← hsym, ← hsym, K.c_c]
  have hneg1 : ∀ y z, s (-y) z = - s y z := by
    intro y z
    have := hlin (-1) y z
    simpa using this
  have hneg2 : ∀ y z, s y (-z) = - s y z := by
    intro y z
    have := hlin2 (-1) y z
    simpa using this
  have hsg : ∀ y z, s (B.g * y) (B.g * z) = s y z := by
    intro y z
    rcases hε with rfl | rfl
    · simpa [hu_def] using hsu y z
    · have := hsu y z
      simp only [hu_def, neg_mul, one_mul] at this
      rw [hneg1, hneg2, neg_neg] at this
      exact this
  have hadj_g : ∀ y z, s (B.g * y) z = s y (B.σ B.g * z) := by
    intro y z
    conv_lhs => rw [show z = B.g * (B.σ B.g * z) by rw [← mul_assoc, hg, one_mul]]
    exact hsg _ _
  have hadj : ∀ a y z, s (a * y) z = s y (B.σ a * z) := by
    intro a
    obtain ⟨f, rfl⟩ := GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution K B hP a
    induction f using Polynomial.induction_on with
    | C e =>
      intro y z
      rw [aeval_C, ← Algebra.smul_def, B.σ_alg, ← Algebra.smul_def, hlin, hlin2, K.c_c]
    | add p q hp hq =>
      intro y z
      rw [map_add (f := _), add_mul, hadd, hp, hq, map_add (f := _), add_mul, hadd2]
    | monomial n e ih =>
      intro y z
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X, mul_assoc, ih, hadj_g]
      congr 1
      rw [map_mul B.σ _ B.g]
      ring

  let ℓ : Module.Dual K.E B.A :=
    { toFun := fun y => s y 1
      map_add' := fun x y => hadd x y 1
      map_smul' := fun c x => hlin c x 1 }
  let φ : B.A →ₗ[K.E] Module.Dual K.E B.A := Algebra.traceForm K.E B.A
  have hφi : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine GlobalTheory.T.eq_zero_of_trace_mul_of_separable_generated K B hP (GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution K B hP) w fun y => ?_
    have := LinearMap.congr_fun hw y
    simpa [φ, Algebra.traceForm_apply] using this
  have hφs : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).mp hφi
  obtain ⟨β, hβ⟩ := hφs ℓ
  have hβs : ∀ y, s y 1 = Algebra.trace K.E B.A (β * y) := by
    intro y
    have := LinearMap.congr_fun hβ y
    simpa [φ, ℓ, Algebra.traceForm_apply] using this.symm
  have hform : ∀ y z, s y z = B.herm β y z := by
    intro y z
    have h1 := hadj (B.σ z) y 1
    rw [B.σ_σ, mul_one] at h1
    rw [← h1, hβs]
    unfold InvAlg.herm
    congr 1; ring

  have hβinj : Function.Injective (LinearMap.mulLeft K.E β) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hy' : β * y = 0 := hy
    refine hnd y fun z => ?_
    rw [hform]
    unfold InvAlg.herm
    rw [hy', zero_mul, map_zero]
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.mp hβinj) 1
  have hxβ : β * x = 1 := hx
  refine ⟨⟨β, x, hxβ, by rw [mul_comm]; exact hxβ⟩, ?_, hform⟩
  show B.σ β = β * u
  rw [← sub_eq_zero]
  refine GlobalTheory.T.eq_zero_of_trace_mul_of_separable_generated K B hP (GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution K B hP) _ fun y => ?_
  have h3 : Algebra.trace K.E B.A (B.σ β * y) = Algebra.trace K.E B.A (β * u * y) := by
    have h2 := hsym y 1
    rw [hform, hform] at h2
    unfold InvAlg.herm at h2
    rw [← trace_σ] at h2
    simp only [map_mul B.σ, map_one, B.σ_σ, mul_one] at h2
    rw [h2]; congr 1; ring
  rw [sub_mul, map_sub, h3, sub_self]

end GlobalTheory.SesqAsym
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisAddPiSmul
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.WachTie

theorem _root_.GlobalTheory.WachTie.exists_invariant_basis : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {r : ℕ}, IsUnit (W.DelF.card : O) → Nonempty (Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T)) → ∃ b : Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T), ∀ k, (b k : W.DD T) ∈ W.NΔ T := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W T r hu ⟨b⟩
  classical
  have hmul : ∀ g ∈ W.DelF, ∀ δ ∈ W.DelF, g * δ ∈ W.DelF := by
    intro g hg δ hδ
    obtain ⟨a, ha, hga⟩ := (W.DelF_def g).1 hg
    obtain ⟨c, hc, hδc⟩ := (W.DelF_def δ).1 hδ
    refine (W.DelF_def _).2 ⟨a * c, Nat.mul_pos ha hc, ?_⟩
    rw [mul_pow, pow_mul, hga, one_pow, one_mul, mul_comm, pow_mul, hδc, one_pow]
  have himage : ∀ g ∈ W.DelF, W.DelF.image (g * ·) = W.DelF := by
    intro g hg
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hx
      exact hmul g hg δ hδ
    · rw [Finset.card_image_of_injective _ (mul_right_injective g)]
  let avg : W.DD T →ₗ[O] W.DD T := ((↑hu.unit⁻¹ : O)) • ∑ δ ∈ W.DelF, W.γD T δ
  have havg : ∀ x, avg x = (↑hu.unit⁻¹ : O) • ∑ δ ∈ W.DelF, W.γD T δ x := by
    intro x
    simp [avg, LinearMap.sum_apply]
  have hinv : ∀ g ∈ W.DelF, ∀ x, W.γD T g (avg x) = avg x := by
    intro g hg x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [havg, map_smul, map_sum]
    congr 1
    simp_rw [← W.γD_mul T]
    conv_rhs => rw [← himage g hg]
    rw [Finset.sum_image (fun a _ c _ h => mul_left_cancel h)]
  have hN : ∀ x ∈ W.N T, avg x ∈ W.N T := by
    intro x hx
    rw [havg]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.sum_mem _ fun δ _ => W.N_Γ T δ x hx)
  open Pointwise in
  have hQ : ∀ x ∈ W.N T, avg x - x ∈ (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • W.N T := by
    intro x hx
    have hsplit : avg x - x = (↑hu.unit⁻¹ : O) • ∑ δ ∈ W.DelF, (W.γD T δ x - x) := by
      rw [havg, Finset.sum_sub_distrib, Finset.sum_const, smul_sub, ← Nat.cast_smul_eq_nsmul O,
        smul_smul, IsUnit.val_inv_mul, one_smul]
    rw [hsplit]
    refine Submodule.smul_of_tower_mem _ _ (Submodule.sum_mem _ fun δ _ => ?_)
    obtain ⟨y, hy, hxy⟩ := W.N_π T δ x hx
    rw [hxy]
    exact Submodule.smul_mem_pointwise_smul _ _ _ hy
  have hb : ∀ k, ∃ y : W.N T, (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • y =
      (⟨avg (b k), hN _ (b k).2⟩ : W.N T) - b k := by
    intro k
    open Pointwise in
    obtain ⟨y, hy, hxy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (hQ _ (b k).2)
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hxy)⟩
  choose y hy using hb
  let g : W.N T →ₗ[_root_.Formalism.BasicNotions.LetA O n] W.N T := b.constr (_root_.Formalism.BasicNotions.LetA O n) y
  let f : W.N T →ₗ[_root_.Formalism.BasicNotions.LetA O n] W.N T := LinearMap.id + (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • g
  have hf : ∀ k, f (b k) = ⟨avg (b k), hN _ (b k).2⟩ := by
    intro k
    simp only [f, g, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply,
      Module.Basis.constr_basis, hy]
    abel
  have hunit : IsUnit f := by
    haveI := Module.Free.of_basis b
    haveI := Module.Finite.of_basis b
    rw [LinearMap.isUnit_iff_isUnit_det, ← LinearMap.det_toMatrix b]
    have hM : LinearMap.toMatrix b b f = 1 + (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • LinearMap.toMatrix b b g := by
      simp [f, map_add (f := _), LinearMap.toMatrix_id]
    rw [hM, Pi.isUnit_iff]
    intro i
    rw [PowerSeries.isUnit_iff_constantCoeff]
    let ψ : _root_.Formalism.BasicNotions.LetA O n →+* O :=
      (PowerSeries.constantCoeff (R := O)).comp (Pi.evalRingHom (fun _ : ZMod n => O⟦X⟧) i)
    change IsUnit (ψ (Matrix.det (1 + (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • LinearMap.toMatrix b b g)))
    rw [RingHom.map_det]
    have h2 : ψ.mapMatrix (1 + (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • LinearMap.toMatrix b b g) = 1 := by
      ext p q
      simp [ψ, _root_.Formalism.BasicNotions.letπ, Matrix.one_apply]
      split_ifs <;> simp
    rw [h2, Matrix.det_one]
    exact isUnit_one
  have hbij := (Module.End.isUnit_iff f).1 hunit
  refine ⟨b.map (LinearEquiv.ofBijective f hbij), fun k => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.ofBijective_apply, hf]
  exact ⟨hN _ (b k).2, fun δ hδ => hinv δ hδ _⟩

end GlobalTheory.WachTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCycCycChar
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

noncomputable def cycChar (l : ℕ) [Fact l.Prime] : GQ l →* ℚ_[l]ˣ :=
  (Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp
    ((cyclotomicCharacter (Om l) l).comp (MulSemiringAction.toRingAut (GQ l) (Om l)))

theorem _root_.GlobalTheory.Cyc.isCyc_cycChar (l : ℕ) [Fact l.Prime] :
    _root_.GlobalTheory.Cyc.IsCyc (_root_.GlobalTheory.Cyc.cycChar l) := by
  intro g m ζ h
  set x : ℤ_[l] := (cyclotomicCharacter (_root_.Formalism.BasicNotions.Loc.Om l) l (MulSemiringAction.toRingAut _ _ g) : ℤ_[l])
    with hx
  refine ⟨(PadicInt.toZModPow m x).val, ?_, ?_⟩
  · have hmem : x - ((PadicInt.toZModPow m x).val : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ m} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val,
        sub_self]
    have h2 : ‖((x - ((PadicInt.toZModPow m x).val : ℤ_[l]) : ℤ_[l]) : ℚ_[l])‖ ≤
        (l : ℝ) ^ (-(m : ℤ)) :=
      (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 hmem
    have h3 : ((_root_.GlobalTheory.Cyc.cycChar l g : ℚ_[l]ˣ) : ℚ_[l]) = (x : ℚ_[l]) := rfl
    rw [h3]
    rw [PadicInt.coe_sub, PadicInt.coe_natCast] at h2
    exact h2
  · exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut _ _ g) ζ h

theorem _root_.GlobalTheory.Cyc.exists_isCyc :
    ∀ (l : ℕ) [Fact l.Prime], ∃ χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℚ_[l]ˣ, _root_.GlobalTheory.Cyc.IsCyc χ :=
  fun l _ => ⟨_root_.GlobalTheory.Cyc.cycChar l, _root_.GlobalTheory.Cyc.isCyc_cycChar l⟩

end GlobalTheory.Cyc
end
