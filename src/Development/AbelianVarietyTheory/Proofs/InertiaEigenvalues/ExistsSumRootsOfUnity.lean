module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestric
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AssociatedPowOfUnits
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumRootsOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumRootsOfUnity
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.UnramSpan

open GlobalTheory.UnramValue

variable {l : ℕ} [Fact l.Prime]

theorem fg_rootRing {m : ℕ} (hm : 0 < m) : (rootRing l m).toSubmodule.FG := by
  classical
  have hfin : {x : Om l | x ^ m = 1}.Finite := by
    refine (Polynomial.nthRoots m (1 : Om l)).toFinset.finite_toSet.subset ?_
    intro x hx
    simpa [Polynomial.mem_nthRoots hm] using hx
  refine fg_adjoin_of_finite hfin ?_
  intro x hx
  refine IsIntegral.of_pow hm ?_
  rw [show x ^ m = 1 from hx]; exact isIntegral_one

theorem exists_mem_rootRing {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) (h1 : ‖x‖ ≤ 1) :
    ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ x ∈ rootRing l m := by
  have hp : l.Prime := Fact.out
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  obtain ⟨m, hm, hl, c, hc, h⟩ := exists_mul_mem hx
  refine ⟨m, hm, hl, ?_⟩
  have key : ∀ k : ℕ, (l : Om l) ^ k * x ∈ rootRing l m → x ∈ rootRing l m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      obtain ⟨z, hz, ez⟩ := exists_eq_mul hm hl hk (by
        rw [norm_mul, norm_pow, norm_l]
        have : ((l : ℝ)⁻¹) ^ (k + 1) < 1 :=
          pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl1) (Nat.succ_ne_zero k)
        calc _ ≤ ((l : ℝ)⁻¹) ^ (k + 1) * 1 := by gcongr
          _ < 1 := by simpa using this)
      apply ih
      have : (l : Om l) ^ k * x = z := by
        apply mul_left_cancel₀ hl0
        rw [← ez]; ring
      rwa [this]
  apply key c.valuation
  have e := PadicInt.unitCoeff_spec hc
  set u := PadicInt.unitCoeff hc
  have e2 : (l : Om l) ^ c.valuation * x =
      algebraMap ℤ_[l] (Om l) (↑u⁻¹ : ℤ_[l]) * (algebraMap ℤ_[l] (Om l) c * x) := by
    rw [← mul_assoc, ← map_mul]
    congr 1
    conv_rhs => rw [e, Units.inv_mul_cancel_left]
    simp
  rw [e2]
  exact mul_mem (Subalgebra.algebraMap_mem _ _) h

theorem norm_pow_sub_pow_le {m : ℕ} (hm : 0 < m) {k : ℕ} (hk : k ≠ 0) {a b : Om l}
    (ha : a ∈ rootRing l m) (hb : b ∈ rootRing l m) (h : ‖a - b‖ ≤ (l : ℝ)⁻¹) :
    ‖a ^ (l ^ k) - b ^ (l ^ k)‖ ≤ (l : ℝ)⁻¹ * ‖a - b‖ := by
  have hp : l.Prime := Fact.out
  have hd := sub_mem ha hb
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (⟨b, hb⟩ : rootRing l m) ⟨a - b, hd⟩ k
  have hr' := congrArg Subtype.val hr
  simp only [MulMemClass.coe_mul, AddMemClass.coe_add, SubmonoidClass.coe_pow,
    SubringClass.coe_natCast, add_sub_cancel] at hr'
  have e : a ^ (l ^ k) - b ^ (l ^ k) = (a - b) ^ (l ^ k) + l * (a - b) * (b * r) := by
    rw [hr']; ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · obtain ⟨j, hj⟩ : ∃ j, l ^ k = j + 2 :=
      ⟨l ^ k - 2, by have := Nat.one_lt_pow hk hp.one_lt; omega⟩
    have h1 := norm_le_one hm hd
    have h2 : ‖a - b‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) h1
    rw [hj, norm_pow, pow_add, sq]
    calc _ ≤ 1 * ((l : ℝ)⁻¹ * ‖a - b‖) := by gcongr
      _ = _ := one_mul _
  · rw [norm_mul, norm_mul, norm_l]
    have h1 := norm_le_one hm (mul_mem hb r.2)
    calc _ ≤ (l : ℝ)⁻¹ * ‖a - b‖ * 1 := by gcongr
      _ = _ := mul_one _

def part (F : IntermediateField ℚ_[l] (Om l)) (m : ℕ) : Submodule ℤ_[l] (Om l) :=
  (rootRing l m).toSubmodule ⊓ F.toSubalgebra.toSubmodule.restrictScalars ℤ_[l]

theorem mem_part {F : IntermediateField ℚ_[l] (Om l)} {m : ℕ} {x : Om l} :
    x ∈ part F m ↔ x ∈ rootRing l m ∧ x ∈ F := Iff.rfl

theorem fg_part (F : IntermediateField ℚ_[l] (Om l)) {m : ℕ} (hm : 0 < m) : (part F m).FG :=
  (fg_rootRing hm).of_le inf_le_left

theorem exists_teich (F : IntermediateField ℚ_[l] (Om l)) {m : ℕ} (hm : 0 < m) (hl : ¬ l ∣ m)
    {x : Om l} (hx : x ∈ part F m) :
    ∃ w ∈ part F m, w ^ (l ^ m.totient) = w ∧ ‖x - w‖ < 1 := by
  have hp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hli : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have : ContinuousSMul ℤ_[l] (Om l) := by
    refine continuousSMul_of_algebraMap ℤ_[l] (Om l) ?_
    exact (AddMonoidHomClass.isometry_of_norm _ norm_algebraMap_int).continuous
  have hc : IsCompact ((part F m : Set (Om l)) ∩ Metric.closedBall x (l : ℝ)⁻¹) :=
    (Submodule.isCompact_of_fg (fg_part F hm)).inter_right Metric.isClosed_closedBall
  have hstep : ∀ y ∈ rootRing l m, ‖y ^ (l ^ m.totient) - y‖ ≤ (l : ℝ)⁻¹ := by
    intro y hy
    obtain ⟨z, hz, ez⟩ := pow_sub_mem hl hy
    rw [ez, add_sub_cancel_left, norm_mul, norm_l]
    have h1 := norm_le_one hm hz
    calc _ ≤ (l : ℝ)⁻¹ * 1 := by gcongr
      _ = _ := mul_one _
  obtain ⟨w, ⟨hw, hwx⟩, hmin⟩ := hc.exists_isMinOn
    (f := fun y : Om l => ‖y ^ (l ^ m.totient) - y‖)
    ⟨x, hx, Metric.mem_closedBall_self (by positivity)⟩ (by fun_prop)
  rw [Metric.mem_closedBall, dist_eq_norm] at hwx
  have hw' := mem_part.mp hw
  refine ⟨w, hw, ?_, by rw [norm_sub_rev]; exact hwx.trans_lt hli⟩
  have hmem : w ^ (l ^ m.totient) ∈ (part F m : Set (Om l)) ∩ Metric.closedBall x (l : ℝ)⁻¹ := by
    refine ⟨mem_part.mpr ⟨pow_mem hw'.1 _, pow_mem hw'.2 _⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm,
      show w ^ (l ^ m.totient) - x = (w ^ (l ^ m.totient) - w) + (w - x) by ring]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hstep w hw'.1) hwx)
  have h1 : ‖w ^ (l ^ m.totient) - w‖ ≤ ‖(w ^ (l ^ m.totient)) ^ (l ^ m.totient) - w ^ (l ^ m.totient)‖ :=
    hmin hmem
  have h2 := norm_pow_sub_pow_le hm (Nat.totient_pos.mpr hm).ne' (pow_mem hw'.1 (l ^ m.totient))
    hw'.1 (hstep w hw'.1)
  have h3 := norm_nonneg (w ^ (l ^ m.totient) - w)
  have h4 : ‖w ^ (l ^ m.totient) - w‖ = 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h4)

theorem part_le_span (F : IntermediateField ℚ_[l] (Om l)) {m : ℕ} (hm : 0 < m) (hl : ¬ l ∣ m) :
    part F m ≤ Submodule.span ℤ_[l]
      {w : Om l | w ∈ F ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ w ^ m = 1} := by
  have hp : l.Prime := Fact.out
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal ℤ_[l])
    (fg_part F hm) (IsLocalRing.maximalIdeal_le_jacobson _) ?_
  intro x hx
  obtain ⟨w, hw, ew, hxw⟩ := exists_teich F hm hl hx
  have hd := mem_part.mp (sub_mem hx hw)
  obtain ⟨z, hz, ez⟩ := exists_eq_mul hm hl hd.1 hxw
  have hzF : z ∈ F := by
    have : z = (x - w) / l := by rw [ez]; field_simp
    rw [this]
    exact div_mem hd.2 (natCast_mem F l)
  have e : x = w + (l : ℤ_[l]) • z := by
    rw [Algebra.smul_def, map_natCast, ← ez]; ring
  rw [e]
  refine Submodule.add_mem_sup ?_ (Submodule.smul_mem_smul ?_ (mem_part.mpr ⟨hz, hzF⟩))
  · by_cases h0 : w = 0
    · rw [h0]; exact zero_mem _
    · have hq : 1 < l ^ m.totient := Nat.one_lt_pow (Nat.totient_pos.mpr hm).ne' hp.one_lt
      refine Submodule.subset_span ⟨(mem_part.mp hw).2, l ^ m.totient - 1, by omega, ?_, ?_⟩
      · intro hd
        have h1 : l ∣ l ^ m.totient := dvd_pow_self l (Nat.totient_pos.mpr hm).ne'
        have h2 := Nat.dvd_sub h1 hd
        rw [show l ^ m.totient - (l ^ m.totient - 1) = 1 by omega] at h2
        exact hp.not_dvd_one h2
      · apply mul_right_cancel₀ h0
        rw [← pow_succ, Nat.sub_add_cancel hq.le, ew, one_mul]
  · rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _

theorem exists_sum_rootsOfUnity : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (c : Om l), c ∈ K0 K → ‖c‖ ≤ 1 → ∃ (n : ℕ) (z : Fin n → ℤ_[l]) (ω : Fin n → Om l), (∀ i, ω i ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ ω i ^ m = 1) ∧ c = ∑ i, algebraMap ℚ_[l] (Om l) (z i : ℚ_[l]) * ω i := by
  intro l _ K c hc h1
  obtain ⟨m, hm, hl, h⟩ := exists_mem_rootRing (x := c) (show c ∈ K.1 ⊓ MaximalUnramifiedExtension l from hc).2 h1
  obtain ⟨n, z, g, e⟩ := Submodule.mem_span_set'.mp (part_le_span (K0 K) hm hl (mem_part.mpr ⟨h, hc⟩))
  refine ⟨n, z, fun i => g i, fun i => (g i).2, ?_⟩
  rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l)]
  rfl

end GlobalTheory.UnramSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumRootsOfUnityStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_sum_padicInt_mul_rootsOfUnity : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (c : Om l), c ∈ K0 K → ‖c‖ ≤ 1 → ∃ (n : ℕ) (z : Fin n → ℤ_[l]) (ω : Fin n → Om l), (∀ i, ω i ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ ω i ^ m = 1) ∧ c = ∑ i, algebraMap ℚ_[l] (Om l) (z i : ℚ_[l]) * ω i := by
  first | exact @GlobalTheory.UnramSpan.exists_sum_rootsOfUnity | exact GlobalTheory.UnramSpan.exists_sum_rootsOfUnity | (intros; apply GlobalTheory.UnramSpan.exists_sum_rootsOfUnity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCommensurableOfIsLatIn
namespace GlobalTheory

open Formalism.MainNotions.IntegralHeckeForms

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module O W]

theorem _root_.GlobalTheory.relLength_ne_top_of_isLatIn {V A B : Submodule O W} (hA : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn A V)
    (hB : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn B V) : _root_.GlobalTheory.relLength A B ≠ ⊤ := by
  rw [_root_.GlobalTheory.relLength_ne_top_iff]
  obtain ⟨hAfg, hAV, -⟩ := hA
  obtain ⟨-, -, hBV⟩ := hB
  have : Module.Finite O A := Module.Finite.iff_fg.mpr hAfg
  apply _root_.GlobalTheory.isFiniteLength_of_isTorsion
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H a =>
    obtain ⟨c, hc, hcB⟩ := hBV a (hAV a.2)
    refine ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hcB

theorem _root_.GlobalTheory.lengthCommensurable_of_isLatIn {V A B : Submodule O W} (hA : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn A V)
    (hB : _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn B V) : _root_.GlobalTheory.LengthCommensurable A B :=
  ⟨_root_.GlobalTheory.relLength_ne_top_of_isLatIn hA hB,
    _root_.GlobalTheory.relLength_ne_top_of_isLatIn hB hA⟩

theorem _root_.GlobalTheory.sIdx_eq_signedLength_div (l : ℕ) (A B : Submodule O W) :
    _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l A B = (_root_.GlobalTheory.signedLength A B : ℝ) /
      ((IsDiscreteValuationRing.addVal O (l : O)).toNat : ℝ) := by
  unfold _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx _root_.Formalism.MainNotions.IntegralHeckeForms.lenR _root_.GlobalTheory.signedLength
  rw [← _root_.GlobalTheory.relLength_eq_length_quotient_comap,
    ← _root_.GlobalTheory.relLength_eq_length_quotient_comap]
  push_cast
  rw [sub_div]

theorem _root_.GlobalTheory.sIdx_add_and_mono :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (W : Type)
      [AddCommGroup W] [Module O W] (l : ℕ) (V L₁ L₂ L₃ : Submodule O W),
      _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₁ V → _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₂ V → _root_.Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₃ V →
      _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₃ = _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ + _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₂ L₃ ∧
        (L₃ ≤ L₂ → _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ ≤ _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₃) := by
  intro O _ _ _ W _ _ l V L₁ L₂ L₃ h₁ h₂ h₃
  have hadd : _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₃ = _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ + _root_.Formalism.MainNotions.IntegralHeckeForms.sIdx l L₂ L₃ := by
    simp only [_root_.GlobalTheory.sIdx_eq_signedLength_div]
    rw [(_root_.GlobalTheory.lengthCommensurable_of_isLatIn h₁ h₂).signedLength_eq_add
      (_root_.GlobalTheory.lengthCommensurable_of_isLatIn h₂ h₃)]
    push_cast
    rw [add_div]
  refine ⟨hadd, fun hle => ?_⟩
  rw [hadd, le_add_iff_nonneg_right, _root_.GlobalTheory.sIdx_eq_signedLength_div]
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact_mod_cast (_root_.GlobalTheory.lengthCommensurable_of_isLatIn h₂ h₃).signedLength_nonneg hle

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltSeparatedCompleteEpsilonRootSubOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltSeparatedCompleteEpsilonRootSubOne
namespace GlobalTheory.TiltComplete

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

section General

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]

theorem coeff_sum_stable (t : Perfection R p) (a : ℕ → Perfection R p) (n M N : ℕ)
    (hM : Perfection.coeff R p n t ^ M = 0) (h : M ≤ N) :
    Perfection.coeff R p n (∑ i ∈ Finset.range N, t ^ i * a i) =
      Perfection.coeff R p n (∑ i ∈ Finset.range M, t ^ i * a i) := by
  induction N, h using Nat.le_induction with
  | base => rfl
  | succ N h ih =>
    rw [Finset.sum_range_succ, map_add (f := _), ih, map_mul, map_pow, pow_eq_zero_of_le h hM, zero_mul,
      add_zero]

theorem exists_limit (t : Perfection R p) (M : ℕ → ℕ)
    (hM : ∀ n, Perfection.coeff R p n t ^ M n = 0) (a : ℕ → Perfection R p) :
    ∃ x : Perfection R p, ∀ n N, M n ≤ N →
      Perfection.coeff R p n x = Perfection.coeff R p n (∑ i ∈ Finset.range N, t ^ i * a i) := by
  refine ⟨⟨fun n => Perfection.coeff R p n (∑ i ∈ Finset.range (M n), t ^ i * a i), fun n => ?_⟩,
    fun n N h => ?_⟩
  · beta_reduce
    rw [← coeff_sum_stable t a (n + 1) _ _ (hM _) (le_max_left (M (n + 1)) (M n)),
      ← coeff_sum_stable t a n _ _ (hM _) (le_max_right (M (n + 1)) (M n)),
      Perfection.coeff_pow_p']
  · rw [Perfection.coeff_mk, coeff_sum_stable t a n _ _ (hM _) h]

theorem separated_complete (t : Perfection R p) (M : ℕ → ℕ)
    (hM : ∀ n, Perfection.coeff R p n t ^ M n = 0) :
    (∀ x : Perfection R p, (∀ m : ℕ, t ^ m ∣ x) → x = 0) ∧
      ∀ a : ℕ → Perfection R p, ∃ x : Perfection R p, ∀ m : ℕ,
        t ^ m ∣ x - ∑ i ∈ Finset.range m, t ^ i * a i := by
  refine ⟨fun x hx => Perfection.ext fun n => ?_, fun a => ?_⟩
  · obtain ⟨c, rfl⟩ := hx (M n)
    rw [map_mul, map_pow, hM, zero_mul, map_zero]
  · obtain ⟨x, hx⟩ := exists_limit t M hM a
    refine ⟨x, fun m => ?_⟩
    obtain ⟨y, hy⟩ := exists_limit t M hM fun i => a (m + i)
    refine ⟨y, Perfection.ext fun n => ?_⟩
    rw [map_sub, map_mul, hx n (m + M n) (Nat.le_add_left _ _), hy n (M n) le_rfl, ← map_mul,
      ← map_sub, Finset.sum_range_add, add_sub_cancel_left, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [pow_add, mul_assoc]

end General

theorem tilt_separated_complete : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (s : ℕ), (∀ x : OCb l, (∀ m : ℕ, (AI.εroot s - 1) ^ m ∣ x) → x = 0) ∧ ∀ a : ℕ → OCb l, ∃ x : OCb l, ∀ m : ℕ, (AI.εroot s - 1) ^ m ∣ x - ∑ i ∈ Finset.range m, (AI.εroot s - 1) ^ i * a i := by
  intro l _ P AI s
  refine separated_complete (R := ModP (OC l) l) (p := l) (AI.εroot s - 1 : OCb l)
    (fun n => l ^ (s + n)) fun n => ?_
  change PreTilt.coeff n (AI.εroot s - 1) ^ l ^ (s + n) = 0
  have h := ζ_add_pow AI 0 (s + n)
  rw [zero_add, AI.ζ_zero] at h
  rw [map_sub, map_one, sub_pow_char_pow, coeff_εroot, ← map_pow, h, map_one, one_pow, sub_self]

end GlobalTheory.TiltComplete
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltSeparatedCompleteEpsilonRootSubOneStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_separated_complete_epsilonRoot_sub_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (s : ℕ), (∀ x : OCb l, (∀ m : ℕ, (AI.εroot s - 1) ^ m ∣ x) → x = 0) ∧ ∀ a : ℕ → OCb l, ∃ x : OCb l, ∀ m : ℕ, (AI.εroot s - 1) ^ m ∣ x - ∑ i ∈ Finset.range m, (AI.εroot s - 1) ^ i * a i := by
  first | exact @GlobalTheory.TiltComplete.tilt_separated_complete | exact GlobalTheory.TiltComplete.tilt_separated_complete | (intros; apply GlobalTheory.TiltComplete.tilt_separated_complete <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenRBaseChangeSubquotient
open scoped TensorProduct

namespace GlobalTheory

section

variable {O : Type} [CommRing O] (O' : Type) [CommRing O'] [Algebra O O']
  {W : Type} [AddCommGroup W] [Module O W]

theorem isLatIn_baseChange [IsDomain O'] (hinj : Function.Injective (algebraMap O O'))
    {V L : Submodule O W} (h : Formalism.MainNotions.IntegralHeckeForms.IsLatIn L V) :
    Formalism.MainNotions.IntegralHeckeForms.IsLatIn (L.baseChange O') (V.baseChange O') := by
  obtain ⟨hfg, hle, hsat⟩ := h
  refine ⟨?_, Submodule.baseChange_mono O' hle, ?_⟩
  · obtain ⟨s, rfl⟩ := hfg
    rw [Submodule.baseChange_span]
    exact Submodule.fg_span (s.finite_toSet.image _)
  · intro x hx
    rw [Submodule.baseChange_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, hv, rfl⟩ := hy
      obtain ⟨c, hc, hcv⟩ := hsat v hv
      refine ⟨algebraMap O O' c, fun h0 => hc (hinj (by rw [h0, map_zero])), ?_⟩
      rw [algebraMap_smul, ← map_smul]
      exact Submodule.tmul_mem_baseChange_of_mem 1 hcv
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha, hay⟩ := hy
      obtain ⟨b, hb, hbz⟩ := hz
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      rw [smul_add]
      refine Submodule.add_mem _ ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hay
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hbz
    | smul a y _ hy =>
      obtain ⟨b, hb, hby⟩ := hy
      refine ⟨b, hb, ?_⟩
      rw [smul_comm]
      exact Submodule.smul_mem _ _ hby

variable [IsDomain O] [IsDiscreteValuationRing O] [IsDomain O'] [IsDiscreteValuationRing O']
  [IsLocalHom (algebraMap O O')]

theorem lenR_baseChange_subquotient (hinj : Function.Injective (algebraMap O O')) (l : ℕ)
    (A B : Submodule O W) :
    Formalism.MainNotions.IntegralHeckeForms.lenR O' l
              (A.baseChange O' ⧸ (B.baseChange O').comap (A.baseChange O').subtype) =
      Formalism.MainNotions.IntegralHeckeForms.lenR O l (A ⧸ B.comap A.subtype) := by
  haveI : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').mpr hinj
  have h1 : Module.length O'
      (A.baseChange O' ⧸ (B.baseChange O').comap (A.baseChange O').subtype) =
      Module.length O (A ⧸ B.comap A.subtype) *
        (((IsLocalRing.maximalIdeal O').ramificationIdx O : ℕ) : ℕ∞) :=
    length_baseChange_subquotient_dvr O O' (X := W) A B
  have h2 := addVal_algebraMap (R := O) O' (l : O)
  rw [map_natCast] at h2
  have he : (((IsLocalRing.maximalIdeal O').ramificationIdx O : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ramificationIdx_maximalIdeal_pos O O').ne'
  unfold Formalism.MainNotions.IntegralHeckeForms.lenR
  rw [h1, h2, ENat.toNat_mul, ENat.toNat_mul, ENat.toNat_coe, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_right _ _ he]

end

theorem sIdx_baseChange :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ (W : Type) [AddCommGroup W] [Module O W] (l : ℕ) (V L₁ L₂ : Submodule O W), Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₁ V → Formalism.MainNotions.IntegralHeckeForms.IsLatIn L₂ V → Formalism.MainNotions.IntegralHeckeForms.IsLatIn (L₁.baseChange O') (V.baseChange O') ∧ Formalism.MainNotions.IntegralHeckeForms.sIdx l (L₁.baseChange O') (L₂.baseChange O') = Formalism.MainNotions.IntegralHeckeForms.sIdx l L₁ L₂ := by
  intro O _ _ _ O' _ _ _ _ _ hinj W _ _ l V L₁ L₂ h₁ _
  refine ⟨isLatIn_baseChange O' hinj h₁, ?_⟩
  unfold Formalism.MainNotions.IntegralHeckeForms.sIdx
  rw [lenR_baseChange_subquotient O' hinj, lenR_baseChange_subquotient O' hinj]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalCharExistsOfGreen
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GreenExists

open Polynomial Formalism.D.Classical Formalism.CyclotomicNorms Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq

variable {g : ℕ} [hg : Fact g.Prime]

theorem mem_grUnipBlock_iff {d a : ℕ} (ha : a < d) (u : Gn g d) :
    u ∈ (grUnipBlock d a : Set (GL (Fin d) (ZMod g))) ↔
      InPar a (u : Mt g d) ∧ tl a (u : Mt g d) = ((1 : Gn g a) : Mt g a) ∧
        br a (d - a) (u : Mt g d) = ((1 : Gn g (d - a)) : Mt g (d - a)) := by
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_, ?_⟩
    · rcases h i j with h1 | h1
      · rw [h1, if_neg]; rintro rfl; omega
      · omega
    · ext i j
      have hi := i.2
      have hj := j.2
      have hij : (i : ℕ) < d ∧ (j : ℕ) < d := by omega
      rcases h ⟨i, hij.1⟩ ⟨j, hij.2⟩ with h1 | h1
      · simp only [tl, entN, dif_pos hij, h1, Units.val_one, Matrix.one_apply, Fin.ext_iff]
      · simp only at h1; omega
    · ext i j
      have hi := i.2
      have hj := j.2
      have hij : a + (i : ℕ) < d ∧ a + (j : ℕ) < d := by omega
      rcases h ⟨a + i, hij.1⟩ ⟨a + j, hij.2⟩ with h1 | h1
      · simp only [br, entN, dif_pos hij, h1, Units.val_one, Matrix.one_apply, Fin.ext_iff, add_right_inj]
      · simp only at h1; omega
  · rintro ⟨h1, h2, h3⟩ i j
    have hi := i.2
    have hj := j.2
    by_cases hia : (i : ℕ) < a
    · by_cases hja : (j : ℕ) < a
      · left
        have := congrFun (congrFun h2 ⟨i, hia⟩) ⟨j, hja⟩
        simpa only [tl, entN, dif_pos (And.intro hi hj), Units.val_one, Matrix.one_apply, Fin.ext_iff] using this
      · right; omega
    · left
      by_cases hja : (j : ℕ) < a
      · rw [h1 i j hja (by omega), if_neg]; rintro rfl; omega
      · have := congrFun (congrFun h3 ⟨i - a, by omega⟩) ⟨j - a, by omega⟩
        have e1 : a + (i - a) = (i : ℕ) := by omega
        have e2 : a + (j - a) = (j : ℕ) := by omega
        have e3 : ((i : ℕ) - a = j - a) ↔ (i : ℕ) = j := by omega
        simpa only [br, entN, e1, e2, e3, dif_pos (And.intro hi hj), Units.val_one, Matrix.one_apply,
          Fin.ext_iff] using this

theorem pow_eq_self_iff {f : (ZMod g)[X]} (hf : Irreducible f) {z : Fbar g} (hz : aeval z f = 0) (n : ℕ) :
    z ^ g ^ n = z ↔ f.natDegree ∣ n := by
  have hx : IsIntegral (ZMod g) z := Algebra.IsIntegral.isIntegral z
  have has : Associated (minpoly (ZMod g) z) f :=
    (minpoly.irreducible hx).associated_of_dvd hf (minpoly.dvd _ _ hz)
  rw [hf.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X, ← has.dvd_iff_dvd_left, minpoly.dvd_iff]
  simp [sub_eq_zero]

theorem rootsBar_eq {f : (ZMod g)[X]} (hf : Irreducible f) {z : Fbar g} (hz : aeval z f = 0) :
    rootsBar f = (Finset.range f.natDegree).val.map fun i => z ^ g ^ i := by
  have hroot : ∀ i, aeval (z ^ g ^ i) f = 0 := fun i => by
    have := aeval_algHom_apply ((FiniteField.frobeniusAlgHom (ZMod g) (Fbar g)) ^ i) z f
    rw [hz, map_zero] at this
    rw [← this]
    congr 1
    rw [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
  have hinj : ∀ i j, i < j → j < f.natDegree → z ^ g ^ i ≠ z ^ g ^ j := fun i j hij hj h => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have h2 : (z ^ g ^ i) ^ g ^ (m + 1) = z ^ g ^ i := by
      rw [← pow_mul, ← pow_add, ← add_assoc, ← h]
    have := Nat.le_of_dvd (Nat.succ_pos m) ((pow_eq_self_iff hf (hroot i) _).1 h2)
    omega
  have hnd : ((Finset.range f.natDegree).val.map fun i => z ^ g ^ i).Nodup := by
    refine Multiset.Nodup.map_on (fun i hi j hj h => ?_) (Finset.range _).nodup
    rw [← Finset.mem_def, Finset.mem_range] at hi hj
    rcases lt_trichotomy i j with h1 | h1 | h1
    · exact absurd h (hinj i j h1 hj)
    · exact h1
    · exact absurd h.symm (hinj j i h1 hi)
  symm
  refine Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hnd).2 fun w hw => ?_) ?_
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hw
    simpa [rootsBar, hf.ne_zero, aeval_def, eval_map] using hroot i
  · have := card_roots' (f.map (algebraMap (ZMod g) (Fbar g)))
    simpa [rootsBar] using this

end GlobalTheory.GreenExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlSpanImageContinuousRepFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlSpanImageContinuousRepFinite
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory

theorem zl_span_image_finite : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous r → ∃ t : Finset Γ, ∀ f : Γ →₀ ℤ_[l], ∃ f' : Γ →₀ ℤ_[l], f'.support ⊆ t ∧ (f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) = (f'.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) := by
  intro l _ Γ _ _ _ _ a r hr
  classical
  obtain ⟨L, hLfin, hL⟩ := GlobalTheory.T.exists_finiteExtension_entries_of_compact_rep l Γ a r hr
  let ρ : Γ → Matrix (Fin a) (Fin a) (PadicAlgCl l) := fun g => ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))
  have hρ : Continuous ρ := Units.continuous_val.comp hr
  let e : Matrix (Fin a) (Fin a) L →ₗ[ℚ_[l]] Matrix (Fin a) (Fin a) (PadicAlgCl l) :=
    LinearMap.mapMatrix L.val.toLinearMap
  let V := LinearMap.range e
  haveI : FiniteDimensional ℚ_[l] V := LinearMap.finiteDimensional_range e
  have hρV : ∀ g, ρ g ∈ V := fun g => ⟨fun i j => ⟨ρ g i j, hL g i j⟩, by ext i j; rfl⟩
  let ρV : Γ → V := fun g => ⟨ρ g, hρV g⟩
  have hρVc : Continuous ρV := hρ.subtype_mk _
  let b := Module.finBasis ℚ_[l] V
  let φ : V →ₗ[ℚ_[l]] (Fin (Module.finrank ℚ_[l] V) → ℚ_[l]) := b.equivFun.toLinearMap
  have hφinj : Function.Injective φ := b.equivFun.injective
  have hφ : Continuous φ := LinearMap.continuous_of_finiteDimensional φ
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hφ.comp hρVc).continuousOn
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm ℚ_[l] C
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1 (Set.mem_univ _))
  have hcpos : 0 < ‖c‖ := lt_of_le_of_lt hC0 hc
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
  have hbd : ∀ g i, ‖c⁻¹ * φ (ρV g) i‖ ≤ 1 := by
    intro g i
    rw [norm_mul, norm_inv]
    have h1 := (norm_le_pi_norm (φ (ρV g)) i).trans (hC g (Set.mem_univ _))
    rw [inv_mul_le_iff₀ hcpos]
    linarith
  let ψ : Γ → (Fin (Module.finrank ℚ_[l] V) → ℤ_[l]) := fun g i => ⟨c⁻¹ * φ (ρV g) i, hbd g i⟩
  obtain ⟨G, hG⟩ : (Submodule.span ℤ_[l] (Set.range ψ)).FG := IsNoetherian.noetherian _
  have hGT : ∀ x ∈ G, ∃ T : Finset (Fin (Module.finrank ℚ_[l] V) → ℤ_[l]),
      ↑T ⊆ Set.range ψ ∧ x ∈ Submodule.span ℤ_[l] (T : Set _) := fun x hx =>
    Submodule.mem_span_finite_of_mem_span (hG ▸ Submodule.subset_span hx)
  choose T hT1 hT2 using hGT
  let U := G.attach.biUnion (fun x => T x.1 x.2)
  have hU : ∀ y ∈ U, ∃ g, ψ g = y := by
    intro y hy
    obtain ⟨x, -, hx⟩ := Finset.mem_biUnion.mp hy
    exact hT1 x.1 x.2 hx
  let t : Finset Γ := U.image (fun y => if h : ∃ g, ψ g = y then h.choose else 1)
  refine ⟨t, ?_⟩
  have hspan : Submodule.span ℤ_[l] (Set.range ψ) ≤ Submodule.span ℤ_[l] (ψ '' (t : Set Γ)) := by
    rw [← hG, Submodule.span_le]
    intro x hx
    refine Submodule.span_mono ?_ (hT2 x hx)
    intro y hy
    have hyU : y ∈ U := Finset.mem_biUnion.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, hy⟩
    have hex : ∃ g, ψ g = y := hU y hyU
    refine ⟨hex.choose, ?_, hex.choose_spec⟩
    simp only [t, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨y, hyU, by rw [dite_eq_left hex]⟩

  let A : (Γ →₀ ℤ_[l]) → V := fun f => f.sum fun h c' => ((c' : ℚ_[l])) • ρV h
  have hSM : ∀ f : Γ →₀ ℤ_[l], (f.sum fun h c' => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c' : ℚ_[l])) • ρ h) = ((A f : V) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) := by
    intro f
    simp only [A, Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul, algebraMap_smul]
    rfl
  have hLC : ∀ f : Γ →₀ ℤ_[l], ∀ i, ((Finsupp.linearCombination ℤ_[l] ψ f i : ℤ_[l]) : ℚ_[l]) = c⁻¹ * φ (A f) i := by
    intro f i
    have hcs : ∀ F : Γ → ℤ_[l], ((∑ x ∈ f.support, F x : ℤ_[l]) : ℚ_[l]) = ∑ x ∈ f.support, (F x : ℚ_[l]) :=
      fun F => map_sum PadicInt.Coe.ringHom F f.support
    rw [Finsupp.linearCombination_apply]
    unfold Finsupp.sum
    simp only [A]
    unfold Finsupp.sum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_apply, hcs, map_sum, Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, PadicInt.coe_mul]
    simp only [ψ]
    ring
  intro f
  have hx : Finsupp.linearCombination ℤ_[l] ψ f ∈ Submodule.span ℤ_[l] (ψ '' (t : Set Γ)) :=
    hspan (Finsupp.mem_span_range_iff_exists_finsupp.mpr ⟨f, rfl⟩)
  obtain ⟨f', hf'sup, hf'⟩ := (Finsupp.mem_span_image_iff_linearCombination ℤ_[l]).mp hx
  refine ⟨f', ?_, ?_⟩
  · rw [Finsupp.mem_supported] at hf'sup
    exact_mod_cast hf'sup
  · show (f.sum fun h c' => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c' : ℚ_[l])) • ρ h) = (f'.sum fun h c' => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c' : ℚ_[l])) • ρ h)
    rw [hSM, hSM]
    congr 1
    apply hφinj
    funext i
    have h1 := hLC f i
    have h2 := hLC f' i
    rw [hf'] at h2
    have : c⁻¹ * φ (A f) i = c⁻¹ * φ (A f') i := h1.symm.trans h2
    exact mul_left_cancel₀ (inv_ne_zero hc0) this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlSpanImageContinuousRepFiniteStatement
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zlSpan_image_continuous_rep_finite : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous r → ∃ t : Finset Γ, ∀ f : Γ →₀ ℤ_[l], ∃ f' : Γ →₀ ℤ_[l], f'.support ⊆ t ∧ (f.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) = (f'.sum fun h c => ((algebraMap ℚ_[l] (PadicAlgCl l)) (c : ℚ_[l])) • ((r h : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) := by
  first | exact @GlobalTheory.zl_span_image_finite | exact GlobalTheory.zl_span_image_finite | (intros; apply GlobalTheory.zl_span_image_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisOneSubFrobeniusSurjective
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.OneSubPhi

theorem one_sub_mul_onto (p : ℕ) {A : Type} [CommRing A] (φ : A →+* A)
    (hA : IsAdicComplete (Ideal.span {(p : A)}) A) (x : A) : ∃ y : A, y - (p : A) * φ y = x := by
  have hc : IsAdicComplete (Ideal.span {(p : ℤ)}) A := by
    rw [← IsAdicComplete.map_algebraMap_iff (S := A), Ideal.map_span, Set.image_singleton, map_natCast]
    exact hA
  let f : A →ₗ[ℤ] A :=
    LinearMap.id - ((AddMonoidHom.mulLeft (p : A)).comp φ.toAddMonoidHom).toIntLinearMap
  have hf : ∀ y, f y = y - (p : A) * φ y := fun _ => rfl
  have hs : Function.Surjective f := by
    refine surjective_of_mkQ_comp_surjective (I := Ideal.span {(p : ℤ)}) fun G => ?_
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ G
    refine ⟨g, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hf]
    have : g - (p : A) * φ g - g = (p : ℤ) • (-φ g) := by simp
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  obtain ⟨y, hy⟩ := hs x
  exact ⟨y, (hf y).symm.trans hy⟩

theorem onto_of_denom (p : ℕ) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (φ : A →+* A)
    (ψ : B →+* B) (hψ : ∀ x, ψ (f x) = f (φ x)) (t : A) (ht : φ t = (p : A) * t)
    (hT : IsUnit (f t)) (hp : IsUnit (p : B))
    (h0 : ∀ x : A, ∃ y : A, y - (p : A) * φ y = x)
    (h1 : ∀ (r : ℕ) (x : A), ∃ β z : A, (p : A) * φ x = (p : A) * (φ β - (p : A) ^ r * β) + t * z)
    (r : ℕ) : ∀ (x : A) (b : B), b * f t ^ r = f x * f t → ∃ y : B, y - ψ y = b := by
  have hψT : ψ (f t) = (p : B) * f t := by rw [hψ, ht, map_mul, map_natCast]
  induction r with
  | zero =>
    intro x b hb
    obtain ⟨y, hy⟩ := h0 x
    refine ⟨f y * f t, ?_⟩
    have e := congrArg f hy
    rw [map_sub, map_mul, map_natCast] at e
    rw [map_mul, hψT, hψ]
    linear_combination f t * e - hb
  | succ r ih =>
    intro x b hb
    have hb' : b * f t ^ r = f x := hT.mul_right_cancel (by rw [← hb]; ring)
    obtain ⟨β, z, hz⟩ := h1 r x
    obtain ⟨s, hs⟩ := (hT.pow r).exists_left_inv
    obtain ⟨q, hq⟩ := (hp.pow (r + 1)).exists_left_inv
    have hψq : ψ q * (p : B) ^ (r + 1) = 1 := by
      have := congrArg ψ hq
      rwa [map_mul, map_pow, map_natCast, map_one] at this
    have eq : ψ q = q := by linear_combination q * hψq - ψ q * hq
    have hψs : ψ s * ((p : B) ^ r * f t ^ r) = 1 := by
      have := congrArg ψ hs
      rwa [map_mul, map_pow, hψT, map_one, mul_pow] at this
    obtain ⟨y, hy⟩ := ih z (f z * f t * s) (by rw [mul_assoc, hs, mul_one])
    have e1 := congrArg ψ hb'
    rw [map_mul, map_pow, hψT, hψ, mul_pow] at e1
    have e2 := congrArg f hz
    simp only [map_mul, map_add (f := _), map_sub, map_pow, map_natCast] at e2
    refine ⟨b - f β * s + q * y, ?_⟩
    rw [map_add (f := _), map_sub, map_mul, map_mul, eq, hψ]
    apply ((hp.pow (r + 1)).mul (hT.pow r)).mul_left_cancel
    linear_combination -(p : B) * e1 - e2 - (p : B) ^ (r + 1) * f β * hs + (p : B) * f (φ β) * hψs
      + f t ^ r * (y - ψ y) * hq + f t ^ r * hy + f z * f t * hs

variable {l : ℕ} [Fact l.Prime]

theorem ainf_onto (r : ℕ) (a : Per.Ainf l) : ∃ β : Per.Ainf l, Per.φA l β - (l : Per.Ainf l) ^ r * β = a := by
  obtain ⟨β, hβ⟩ := (ArtinSchreierWitt.main l).2.2 ((l : Per.Ainf l) ^ r) a
  exact ⟨β, by rw [GlobalTheory.RingBasics.φA_apply]; exact hβ⟩

theorem phiA_alg (a : Per.Ainf l) : phiA l (algebraMap (Per.Ainf l) (Per.Acris l) a) =
    algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l a) := (GlobalTheory.CrisMaps.phiA_extends l).alg a

theorem exists_w (e : Per.Fl l) (he : e.untilt = 1) : ∃ w : Per.Acris l,
    (l : Per.Acris l) * w = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ^ (l - 1) := by
  obtain ⟨w, hw, -⟩ := exists_mu_pow_div l e he
  have hw0 : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) ^ (l - 1) :=
    Subtype.ext (by simpa using hw)
  have hw1 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) hw0
  rw [map_mul, map_natCast, map_pow, ← TFil.alg_factor] at hw1
  exact ⟨_, hw1⟩

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem mul_phi_mem (C : Core l) (x : Per.Acris l) : ∃ (a : Per.Ainf l) (z : Per.Acris l),
    (l : Per.Acris l) * phiA l x = (l : Per.Acris l) * algebraMap (Per.Ainf l) (Per.Acris l) a + C.t * z := by
  have he := core_isEps l C
  obtain ⟨t, u, ht, hu, htu⟩ := exists_isLogA l C.ε he.1
  have e1 : t = C.t := (LogFun.log_fun l C.ε C.t he.1 C.t_log).1 t ht
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨w, hw⟩ := exists_w C.ε he.1
  obtain ⟨a, z, hz⟩ := phiA_mem_ainf_add l C.ε he w hw x
  have h2 : l - 1 = l - 2 + 1 := by
    have := (Fact.out : l.Prime).two_le
    omega
  rw [h2, pow_succ] at hw
  generalize algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) = m at hw htu
  refine ⟨a, v * m ^ (l - 2) * z, ?_⟩
  rw [hz, ← e1, htu]
  linear_combination z * hw - m * m ^ (l - 2) * z * hv

end GlobalTheory.MemLoc.OneSubPhi

namespace GlobalTheory.MemLoc

theorem one_sub_phi_onto (l : ℕ) [Fact l.Prime] (C : Core l) : C.OneSubPhiOnto := by
  intro b
  obtain ⟨r, x, hx⟩ := GlobalTheory.T.bcris_eq_acris_localization_periodT l C b
  obtain ⟨hT, -, -, hl⟩ := core_t_unit_fil l C
  refine OneSubPhi.onto_of_denom l (algebraMap (Per.Acris l) (Per.Bcris l)) (phiA l) (Per.φB l)
    (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.2 C.t (TPhi.t_phi l C) hT hl
    (OneSubPhi.one_sub_mul_onto l (phiA l) (acris_basic l).1) (fun s y => ?_) (r + 1) x b
    (by rw [pow_succ, ← mul_assoc, hx])
  obtain ⟨a, z, hz⟩ := OneSubPhi.mul_phi_mem C y
  obtain ⟨β, hβ⟩ := OneSubPhi.ainf_onto s a
  refine ⟨algebraMap (Per.Ainf l) (Per.Acris l) β, z, ?_⟩
  rw [hz, ← hβ, OneSubPhi.phiA_alg, map_sub, map_mul, map_pow, map_natCast]

end GlobalTheory.MemLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepTwist
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.HalfTwist

theorem eta_char (D : D7) (w : PlE D.host) :
    D.naut.lpChar (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaTinv w) = D.naut.lpUnr w {1} := by
  have hu := D.naut.etaT_unr w
  have hinv := D.naut.etaTinv_def w
  have hd1 : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ _
  have hcard : Multiset.card (D.naut.frobEig (D.naut.locG D.naut.etaT w)) = 1 := by
    rw [D.naut.frobEig_card _ hu, D.naut.locG_dim]
  obtain ⟨b, hb⟩ := Multiset.card_eq_one.1 hcard
  have hb0 : b ≠ 0 := by
    have h0 := D.naut.frobEig_ne_zero _ hu
    rw [hb] at h0
    intro hb'
    exact h0 (by simp [hb'])
  have hinvb : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {b⁻¹} := by
    rw [hinv.2, hb, Multiset.map_singleton]
  have hunr := D.naut.unr_char _ _ hd1 hu hinv.1
  have hf := D.naut.frobEig_char _ _ b⁻¹ hu hinv.1 hd1 hinvb
  rw [D.naut.unr_eq_lpUnr _ hunr, hf, hb, Multiset.map_singleton, mul_inv_cancel₀ hb0]

theorem eta_inf (D : D7) (hA : SumRepresentations.At.TieAut D.nd D.naut) (τ : D.host.E →+* ℂ) :
    ∃ h : ℂ, D.naut.infG D.naut.etaT τ = {h} ∧ D.naut.infG D.naut.etaTinv τ = {-h} ∧
      (h = 1 / 2 ∨ h = -(1 / 2)) := by
  obtain ⟨h1, h2⟩ := hA.2.1 τ
  rcases h1 with h1 | h1
  · exact ⟨1 / 2, h1, by rw [h2, h1, Multiset.map_singleton], Or.inl rfl⟩
  · exact ⟨-(1 / 2), h1, by rw [h2, h1, Multiset.map_singleton], Or.inr rfl⟩

end GlobalTheory.HalfTwist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOfQBMemLat
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOfQBMemLat
noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped Formalism.Per

theorem norm_le_of_qB_mem_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (M n : ℕ) (hM : 1 ≤ M) (z : ℚ_[l]) (hz : qB P z ∈ Lat AI M n) :
    ‖z‖ ≤ (l : ℝ) ^ (-(n : ℤ)) := by
  let J : ThetaL P AI := GlobalTheory.ThetaTie.thetaL T
  obtain ⟨a, ha⟩ := hz
  have hq : ∀ c : ℚ_[l], ‖J.θ (qB P c)‖ = ‖c‖ := by
    intro c
    have e : qB P c = algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) c) :=
      IsScalarTower.algebraMap_apply _ _ _ c
    rw [e, J.θ_Om]
    exact (PadicComplex.norm_extends _ _).trans (PadicAlgCl.norm_extends _ _)
  have h1 := FilB_anti (P := P) (a := 1) (b := (M : ℤ)) (by exact_mod_cast hM) ha
  have h0 := FilB_anti (P := P) (a := 0) (b := 1) (by norm_num) h1
  have hk := (J.θ_ker _ h0).2 h1
  have hadd := J.θ_add _ h0 _ (io_mem AI (((l : ℕ) : Ainf l) ^ n * a))
  rw [sub_add_cancel, hk, zero_add] at hadd
  have e2 : io AI (((l : ℕ) : Ainf l) ^ n * a) = qB P ((l : ℚ_[l]) ^ n) * io AI a := by
    simp only [map_mul, map_pow, map_natCast]
  rw [e2, J.θ_mul _ (qB_mem _) _ (io_mem AI a)] at hadd
  rw [← hq z, hadd, norm_mul, hq, Padic.norm_p_pow]
  exact mul_le_of_le_one_right (by positivity) (J.θ_int a)

end GlobalTheory.ExpImage
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOfQBMemLatStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_le_of_qB_mem_Lat_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (M n : ℕ), 1 ≤ M → ∀ z : ℚ_[l], qB P z ∈ Lat AI M n → ‖z‖ ≤ (l : ℝ) ^ (-(n : ℤ)) := by
  first | exact @GlobalTheory.ExpImage.norm_le_of_qB_mem_Lat | exact GlobalTheory.ExpImage.norm_le_of_qB_mem_Lat | (intros; apply GlobalTheory.ExpImage.norm_le_of_qB_mem_Lat <;> assumption)
end
end
