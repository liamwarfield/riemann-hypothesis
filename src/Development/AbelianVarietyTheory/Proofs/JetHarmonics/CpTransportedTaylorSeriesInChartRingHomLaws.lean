module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesInChartRingHomLaws
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TaylorRead

theorem tay_add {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) :
    tay (fun z => F z + G z) = tay F + tay G := by
  ext n
  have := iteratedDeriv_add (n := n) (x := (0 : ℂ)) hF.contDiffAt hG.contDiffAt
  simp only [tay, coeff_mk, map_add (f := _)]
  rw [← add_div, ← this]
  rfl

theorem tay_mul {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) :
    tay (fun z => F z * G z) = tay F * tay G := by
  ext n
  have := iteratedDeriv_mul (n := n) (x := (0 : ℂ)) hF.contDiffAt hG.contDiffAt
  simp only [tay, coeff_mk, coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => iteratedDeriv i F 0 / (i.factorial : ℂ) * (iteratedDeriv j G 0 / (j.factorial : ℂ)))]
  change iteratedDeriv n (F * G) 0 / _ = _
  rw [this, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h := Nat.choose_mul_factorial_mul_factorial hi'
  have h1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : ((n - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
  have h3 : (n.choose i : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi').ne'
  rw [← h]
  push_cast
  field_simp

theorem tay_congr {F G : ℂ → ℂ} (h : F =ᶠ[𝓝 0] G) : tay F = tay G := by
  ext n
  simp only [tay, coeff_mk]
  rw [h.iteratedDeriv_eq n]

theorem eventuallyEq_of_tay_eq {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (h : tay F = tay G) : F =ᶠ[𝓝 0] G := by
  have hd : ∀ n, iteratedDeriv n F 0 = iteratedDeriv n G 0 := by
    intro n
    have h1 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have := congrArg (coeff n) h
    simp only [tay, coeff_mk] at this
    exact (div_left_inj₀ h1).mp this
  have hs : AnalyticAt ℂ (F - G) 0 := hF.sub hG
  have htop : analyticOrderAt (F - G) 0 = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hs]
    intro i _
    rw [iteratedDeriv_sub hF.contDiffAt hG.contDiffAt, hd, sub_self]
  filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
  exact sub_eq_zero.mp hz

theorem tay_const (c : ℂ) : tay (fun _ => c) = C c := by
  ext n
  simp only [tay, coeff_mk, iteratedDeriv_const, coeff_C]
  split_ifs with h
  · simp [h]
  · simp

theorem derivative_tay (F : ℂ → ℂ) : PowerSeries.derivative (tay F) = tay (deriv F) := by
  ext n
  have h1 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h2 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  simp only [coeff_derivative, tay, coeff_mk, iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  field_simp

theorem tay_id : tay (fun z => z) = X := by
  ext n
  rcases n with _ | n
  · simp [tay]
  · have : deriv (fun z : ℂ => z) = fun _ => 1 := by ext; simp
    simp only [tay, coeff_mk, iteratedDeriv_succ', this, iteratedDeriv_const, coeff_X]
    rcases n with _ | n <;> simp

theorem iteratedDeriv_comp_mul (F : ℂ → ℂ) (α : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z => F (α * z)) = fun x => α ^ n * iteratedDeriv n F (α * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    ext x
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field, deriv_comp_mul_left, iteratedDeriv_succ,
      smul_eq_mul]
    ring

theorem tay_comp_mul (F : ℂ → ℂ) (α : ℂ) : tay (fun z => F (α * z)) = rescale α (tay F) := by
  ext n
  simp only [tay, coeff_mk, coeff_rescale, iteratedDeriv_comp_mul, mul_zero]
  ring

theorem constantCoeff_subst_of {R : Type*} [CommRing R] {ℓ : R⟦X⟧} (hℓ : constantCoeff ℓ = 0)
    (f : R⟦X⟧) : constantCoeff (f.subst ℓ : R⟦X⟧) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' (HasSubst.of_constantCoeff_zero' hℓ),
    finsum_eq_single _ 0]
  · simp
  · intro d hd
    simp [hℓ, hd]

theorem subst_injective_of {R : Type*} [Field R] {ℓ : R⟦X⟧} (hℓ : constantCoeff ℓ = 0)
    (h1 : coeff 1 ℓ ≠ 0) {f g : R⟦X⟧} (h : (f.subst ℓ : R⟦X⟧) = g.subst ℓ) : f = g := by
  have hu : IsUnit (coeff 1 ℓ) := h1.isUnit
  have key : ∀ f : R⟦X⟧, PowerSeries.subst (R := R) (S := R) (substInvOfIsUnit ℓ hu) (PowerSeries.subst (R := R) (S := R) ℓ f) = f := by
    intro f
    rw [subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hℓ) (HasSubst.substInvOfIsUnit ℓ hu),
      subst_substInvOfIsUnit_right ℓ hℓ hu, X_subst]
  rw [← key f, h, key g]

theorem hat_laws : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧), constantCoeff ℓ = 0 → (∀ F G : ℂ → ℂ, AnalyticAt ℂ F 0 → AnalyticAt ℂ G 0 → hat ι ℓ (fun z => F z + G z) = hat ι ℓ F + hat ι ℓ G ∧ hat ι ℓ (fun z => F z * G z) = hat ι ℓ F * hat ι ℓ G ∧ ((∀ᶠ z in 𝓝[≠] (0 : ℂ), F z = G z) → hat ι ℓ F = hat ι ℓ G) ∧ (coeff 1 ℓ ≠ 0 → hat ι ℓ F = hat ι ℓ G → F =ᶠ[𝓝 0] G)) ∧ (∀ c : ℂ, hat ι ℓ (fun _ => c) = C (ι c)) ∧ hat ι ℓ (fun z => z) = ℓ ∧ (∀ F : ℂ → ℂ, constantCoeff (hat ι ℓ F) = ι (F 0)) ∧ (∀ F : ℂ → ℂ, AnalyticAt ℂ F 0 → PowerSeries.derivative (hat ι ℓ F) = PowerSeries.derivative ℓ * hat ι ℓ (deriv F)) ∧ (∀ (F : ℂ → ℂ) (α : ℂ), AnalyticAt ℂ F 0 → hat ι ℓ (fun z => F (α * z)) = hat ι (C (ι α) * ℓ) F) ∧ ∀ (F : ℂ → ℂ) (h : ℂ_[q]⟦X⟧), constantCoeff h = 0 → (hat ι ℓ F).subst h = hat ι (ℓ.subst h) F := by
  intro q _ ι ℓ hℓ
  have hs : HasSubst ℓ := HasSubst.of_constantCoeff_zero' hℓ
  refine ⟨fun F G hF hG => ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hat]
    rw [tay_add hF hG, map_add (f := _), subst_add hs]
  · simp only [hat]
    rw [tay_mul hF hG, map_mul, subst_mul hs]
  · intro h
    have : F =ᶠ[𝓝 0] G := (hF.frequently_eq_iff_eventually_eq hG).mp h.frequently
    simp only [hat]
    rw [tay_congr this]
  · intro h1 h
    apply eventuallyEq_of_tay_eq hF hG
    exact PowerSeries.map_injective (ι : ℂ →+* ℂ_[q]) ι.injective (subst_injective_of hℓ h1 h)
  · intro c
    simp only [hat]
    rw [tay_const, map_C, subst_C]
    rfl
  · simp only [hat]
    rw [tay_id, map_X, subst_X hs]
  · intro F
    simp only [hat]
    rw [constantCoeff_subst_of hℓ, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
    simp [tay]
  · intro F _
    simp only [hat]
    rw [derivative_subst hs, mul_comm, ← derivative_tay]
    congr 2
    ext n
    simp [coeff_derivative]
  · intro F α _
    simp only [hat]
    have e : PowerSeries.map (ι : ℂ →+* ℂ_[q]) (rescale α (tay F))
        = rescale (ι α) (PowerSeries.map (ι : ℂ →+* ℂ_[q]) (tay F)) := by
      ext n
      simp [coeff_rescale]
    rw [tay_comp_mul, e, rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X' _) hs,
      subst_smul hs, subst_X hs, smul_eq_C_mul]
  · intro F h hh
    simp only [hat]
    rw [subst_comp_subst_apply hs (HasSubst.of_constantCoeff_zero' hh)]

end GlobalTheory.MomOne.TaylorRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffShiftS
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

noncomputable section
namespace GlobalTheory.MomOne.Shift
variable {q : ℕ} [Fact q.Prime]

def sS (ζ : ℂ_[q]) : ℂ_[q]⟦X⟧ := C ζ * (1 + X) - 1

lemma coeff_sS_pow (ζ : ℂ_[q]) (m n : ℕ) :
    coeff n (sS ζ ^ m) = (m.choose n : ℂ_[q]) * ζ ^ n * (ζ - 1) ^ (m - n) := by
  have hs : sS ζ = C ζ * X + C (ζ - 1) := by
    simp only [sS, map_sub, map_one]
    ring
  have hterm : ∀ k ∈ Finset.range (m + 1),
      (C ζ * X) ^ k * C (ζ - 1) ^ (m - k) * (m.choose k : ℂ_[q]⟦X⟧) =
        C (ζ ^ k * (ζ - 1) ^ (m - k) * (m.choose k : ℂ_[q])) * X ^ k := by
    intro k _
    simp only [mul_pow, map_mul, map_pow, map_natCast]
    ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs, add_pow, Finset.sum_congr rfl hterm, map_sum]
  simp only [PowerSeries.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hn
  · ring
  · rw [Finset.mem_range] at hn
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma coeff_shiftS (ζ : ℂ_[q]) (f : ℂ_[q]⟦X⟧) (n : ℕ) :
    coeff n (shiftS ζ f) = ∑' m, coeff m f * coeff n (sS ζ ^ m) := by
  simp only [shiftS, PowerSeries.coeff_mk, coeff_sS_pow]

lemma norm_le_one_of {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) : ‖ζ‖ ≤ 1 := by
  calc ‖ζ‖ = ‖(ζ - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ max ‖ζ - 1‖ ‖(1 : ℂ_[q])‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le h.le (by rw [norm_one])

lemma norm_coeff_sS_pow {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) (m n : ℕ) :
    ‖coeff n (sS ζ ^ m)‖ ≤ ‖ζ - 1‖ ^ (m - n) := by
  rw [coeff_sS_pow, norm_mul, norm_mul, norm_pow, norm_pow]
  have h1 := IsUltrametricDist.norm_natCast_le_one ℂ_[q] (m.choose n)
  have h2 : ‖ζ‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) (norm_le_one_of h)
  calc ‖(m.choose n : ℂ_[q])‖ * ‖ζ‖ ^ n * ‖ζ - 1‖ ^ (m - n) ≤ 1 * 1 * ‖ζ - 1‖ ^ (m - n) := by gcongr
    _ = ‖ζ - 1‖ ^ (m - n) := by ring

lemma summable_norm_term {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) {a : ℕ → ℂ_[q]} {B : ℝ} (ha : ∀ m, ‖a m‖ ≤ B)
    (n : ℕ) : Summable fun m => ‖a m * coeff n (sS ζ ^ m)‖ := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (ha 0)
  have hg : Summable fun m : ℕ => B * ‖ζ - 1‖ ^ (m - n) := by
    refine Summable.mul_left B ((summable_nat_add_iff n).mp ?_)
    simpa using summable_geometric_of_lt_one (norm_nonneg (ζ - 1)) h
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hg
  rw [norm_mul]
  exact mul_le_mul (ha m) (norm_coeff_sS_pow h m n) (norm_nonneg _) hB0

lemma summable_term {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) {a : ℕ → ℂ_[q]} {B : ℝ} (ha : ∀ m, ‖a m‖ ≤ B)
    (n : ℕ) : Summable fun m => a m * coeff n (sS ζ ^ m) := (summable_norm_term h ha n).of_norm

lemma bd_shiftS {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) {f : ℂ_[q]⟦X⟧} {B : ℝ} (hf : Bd B f) :
    Bd B (shiftS ζ f) := by
  intro n
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hf 0)
  rw [coeff_shiftS]
  have hs := summable_term (a := fun m => coeff m f) h hf n
  have hterm : ∀ m, ‖coeff m f * coeff n (sS ζ ^ m)‖ ≤ B := fun m => by
    rw [norm_mul]
    calc ‖coeff m f‖ * ‖coeff n (sS ζ ^ m)‖ ≤ B * 1 :=
          mul_le_mul (hf m) ((norm_coeff_sS_pow h m n).trans (pow_le_one₀ (norm_nonneg _) h.le))
            (norm_nonneg _) hB0
      _ = B := mul_one B
  have hcl : IsClosed {x : ℂ_[q] | ‖x‖ ≤ B} := isClosed_le continuous_norm continuous_const
  refine hcl.mem_of_tendsto hs.hasSum.tendsto_sum_nat (Filter.Eventually.of_forall fun N => ?_)
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 fun m _ => hterm m

lemma shiftS_add {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) :
    shiftS ζ (f + g) = shiftS ζ f + shiftS ζ g := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨B', hB'⟩ := hg
  ext n
  rw [map_add (f := _), coeff_shiftS, coeff_shiftS, coeff_shiftS]
  simp only [map_add (f := _), add_mul]
  exact (summable_term (a := fun m => coeff m f) h hB n).tsum_add
    (summable_term (a := fun m => coeff m g) h hB' n)

lemma shiftS_mul {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) :
    shiftS ζ (f * g) = shiftS ζ f * shiftS ζ g := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨B', hB'⟩ := hg
  ext n
  simp only [coeff_shiftS, PowerSeries.coeff_mul]
  have hprod : ∀ p : ℕ × ℕ, (∑' m, coeff m f * coeff p.1 (sS ζ ^ m)) * (∑' m, coeff m g * coeff p.2 (sS ζ ^ m)) =
      ∑' m, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
        (coeff x.1 f * coeff p.1 (sS ζ ^ x.1)) * (coeff x.2 g * coeff p.2 (sS ζ ^ x.2)) := fun p =>
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (summable_norm_term (a := fun m => coeff m f) h hB p.1)
      (summable_norm_term (a := fun m => coeff m g) h hB' p.2)
  have hsum : ∀ p : ℕ × ℕ, Summable fun m => ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
      (coeff x.1 f * coeff p.1 (sS ζ ^ x.1)) * (coeff x.2 g * coeff p.2 (sS ζ ^ x.2)) := fun p =>
    (summable_norm_sum_mul_antidiagonal_of_summable_norm
      (summable_norm_term (a := fun m => coeff m f) h hB p.1)
      (summable_norm_term (a := fun m => coeff m g) h hB' p.2)).of_norm
  rw [Finset.sum_congr rfl (fun p _ => hprod p), ← Summable.tsum_finsetSum (fun p _ => hsum p)]
  refine tsum_congr fun m => ?_
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rw [← hx', pow_add, PowerSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

lemma shiftS_C (ζ c : ℂ_[q]) : shiftS ζ (C c) = C c := by
  ext n
  rw [coeff_shiftS, tsum_eq_single 0 (fun m hm => by simp [PowerSeries.coeff_C, hm])]
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, PowerSeries.coeff_one, hn]

lemma shiftS_X (ζ : ℂ_[q]) : shiftS ζ X = C ζ * (1 + X) - 1 := by
  ext n
  rw [coeff_shiftS, tsum_eq_single 1 (fun m hm => by simp [PowerSeries.coeff_X, hm])]
  simp [sS]

lemma constantCoeff_shiftS (ζ : ℂ_[q]) (f : ℂ_[q]⟦X⟧) :
    constantCoeff (shiftS ζ f) = ev f (ζ - 1) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_shiftS]
  simp [coeff_sS_pow, ev]

lemma shiftS_one (f : ℂ_[q]⟦X⟧) : shiftS 1 f = f := by
  ext n
  rw [coeff_shiftS, tsum_eq_single n (fun m hm => ?_)]
  · simp [coeff_sS_pow]
  · rw [coeff_sS_pow]
    rcases lt_or_gt_of_ne hm with hlt | hlt
    · simp [Nat.choose_eq_zero_of_lt hlt]
    · simp [Nat.sub_ne_zero_of_lt hlt]

lemma coeff_DT (f : ℂ_[q]⟦X⟧) (n : ℕ) :
    coeff n (DT f) = coeff (n + 1) f * ((n : ℂ_[q]) + 1) + coeff n f * n := by
  rcases n with _ | n
  · rw [DT, add_mul, one_mul, map_add (f := _), PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_derivative]
    simp
  · simp [DT, add_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_succ_X_mul]

lemma DT_sS_pow (ζ : ℂ_[q]) (m : ℕ) :
    DT (sS ζ ^ m) = C (m : ℂ_[q]) * (sS ζ ^ (m - 1) + sS ζ ^ m) := by
  unfold DT
  rw [Derivation.leibniz_pow]
  have hd : PowerSeries.derivative (sS ζ) = C ζ := by simp [sS]
  have h1 : (1 + X) * C ζ = sS ζ + 1 := by
    unfold sS
    ring
  rw [hd]
  rcases m with _ | m
  · simp
  · simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, map_natCast]
    rw [show (1 + X) * ((((m + 1 : ℕ) : ℂ_[q]⟦X⟧)) * (sS ζ ^ m * C ζ)) =
        ((m + 1 : ℕ) : ℂ_[q]⟦X⟧) * sS ζ ^ m * ((1 + X) * C ζ) by ring, h1, pow_succ]
    ring

lemma DT_shiftS {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) {f : ℂ_[q]⟦X⟧} (hf : Bdd f) :
    DT (shiftS ζ f) = shiftS ζ (DT f) := by
  obtain ⟨B, hB⟩ := hf
  have hn1 : ∀ m : ℕ, ‖(m : ℂ_[q])‖ ≤ 1 := fun m => IsUltrametricDist.norm_natCast_le_one ℂ_[q] m
  have hB1 : ∀ m : ℕ, ‖coeff m f * (m : ℂ_[q])‖ ≤ B := fun m => by
    rw [norm_mul]
    nlinarith [hB m, hn1 m, norm_nonneg (coeff m f), norm_nonneg (m : ℂ_[q])]
  have hB2 : ∀ m : ℕ, ‖coeff (m + 1) f * ((m : ℂ_[q]) + 1)‖ ≤ B := fun m => by
    have h0 := hB1 (m + 1)
    push_cast at h0
    exact h0
  ext n
  have hk : ∀ m : ℕ, coeff (n + 1) (sS ζ ^ m) * ((n : ℂ_[q]) + 1) + coeff n (sS ζ ^ m) * n =
      (m : ℂ_[q]) * coeff n (sS ζ ^ (m - 1)) + (m : ℂ_[q]) * coeff n (sS ζ ^ m) := by
    intro m
    rw [← coeff_DT, DT_sS_pow, PowerSeries.coeff_C_mul, map_add (f := _), mul_add]
  have s0 := summable_term (a := fun m => coeff m f) h hB n
  have s1 := summable_term (a := fun m => coeff m f) h hB (n + 1)
  have s2 := summable_term (a := fun m => coeff m f * (m : ℂ_[q])) h hB1 n
  have s3 := summable_term (a := fun m => coeff (m + 1) f * ((m : ℂ_[q]) + 1)) h hB2 n
  have s4 : Summable fun m : ℕ => coeff m f * (m : ℂ_[q]) * coeff n (sS ζ ^ (m - 1)) := by
    refine (summable_nat_add_iff 1).mp ?_
    simpa using s3
  rw [coeff_DT, coeff_shiftS, coeff_shiftS, coeff_shiftS]
  simp only [coeff_DT, add_mul]
  calc (∑' m, coeff m f * coeff (n + 1) (sS ζ ^ m)) * ((n : ℂ_[q]) + 1) +
        (∑' m, coeff m f * coeff n (sS ζ ^ m)) * n
      = ∑' m, (coeff m f * coeff (n + 1) (sS ζ ^ m) * ((n : ℂ_[q]) + 1) +
          coeff m f * coeff n (sS ζ ^ m) * n) := by
        rw [← tsum_mul_right, ← tsum_mul_right, ← Summable.tsum_add (s1.mul_right _) (s0.mul_right _)]
    _ = ∑' m, (coeff m f * (m : ℂ_[q]) * coeff n (sS ζ ^ (m - 1)) +
          coeff m f * (m : ℂ_[q]) * coeff n (sS ζ ^ m)) :=
        tsum_congr fun m => by linear_combination (coeff m f) * hk m
    _ = ∑' m, coeff m f * (m : ℂ_[q]) * coeff n (sS ζ ^ (m - 1)) +
          ∑' m, coeff m f * (m : ℂ_[q]) * coeff n (sS ζ ^ m) := s4.tsum_add s2
    _ = ∑' m, coeff (m + 1) f * ((m : ℂ_[q]) + 1) * coeff n (sS ζ ^ m) +
          ∑' m, coeff m f * (m : ℂ_[q]) * coeff n (sS ζ ^ m) := by
        rw [s4.tsum_eq_zero_add]
        simp
    _ = _ := (s3.tsum_add s2).symm

theorem shift_laws : ∀ (q : ℕ) [Fact q.Prime] (ζ : ℂ_[q]), ‖ζ - 1‖ < 1 → (∀ (f : ℂ_[q]⟦X⟧) (B : ℝ), Bd B f → Bd B (shiftS ζ f)) ∧ (∀ f g : ℂ_[q]⟦X⟧, Bdd f → Bdd g → shiftS ζ (f + g) = shiftS ζ f + shiftS ζ g ∧ shiftS ζ (f * g) = shiftS ζ f * shiftS ζ g) ∧ (∀ c : ℂ_[q], shiftS ζ (C c) = C c) ∧ shiftS ζ X = C ζ * (1 + X) - 1 ∧ (∀ f : ℂ_[q]⟦X⟧, constantCoeff (shiftS ζ f) = ev f (ζ - 1)) ∧ (∀ f : ℂ_[q]⟦X⟧, Bdd f → DT (shiftS ζ f) = shiftS ζ (DT f)) ∧ (∀ f : ℂ_[q]⟦X⟧, shiftS 1 f = f) := by
  intro q _ ζ h
  exact ⟨fun f B hf => bd_shiftS h hf, fun f g hf hg => ⟨shiftS_add h hf hg, shiftS_mul h hf hg⟩,
    shiftS_C ζ, shiftS_X ζ, constantCoeff_shiftS ζ, fun f hf => DT_shiftS h hf, shiftS_one⟩

end GlobalTheory.MomOne.Shift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MkLeContinuumOfDenseRange
set_option autoImplicit false

open Cardinal

namespace GlobalTheory.PadicComplexIso

theorem exists_ringEquiv_over (R K L : Type) [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] [Algebra R K] [Algebra R L] (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ e : K ≃+* L, ∀ x : R, e (algebraMap R K x) = algebraMap R L x := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L
  have hL : ℵ₀ < #L := hKL ▸ hK
  have hsK : #K = #s := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hK
  have htL : #L = #t := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR hL
  obtain ⟨e⟩ : Nonempty (s ≃ t) := Cardinal.eq.1 (hsK.symm.trans (hKL.trans htL))
  let _ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  let _ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let e0 : Algebra.adjoin R (Set.range ((↑) : s → K)) ≃ₐ[R] Algebra.adjoin R (Set.range ((↑) : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L e0.toRingEquiv, fun x => ?_⟩
  rw [IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : s → K))) K,
    IsAlgClosure.equivOfEquiv_algebraMap, AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

theorem mk_le_continuum_of_denseRange {X Y : Type} [MetricSpace Y] (f : X → Y)
    (hf : DenseRange f) (hX : #X ≤ 𝔠) : #Y ≤ 𝔠 := by
  have hex : ∀ (y : Y) (n : ℕ), ∃ x, dist (f x) y < 1 / ((n : ℝ) + 1) := by
    intro y n
    obtain ⟨x, hx⟩ := Metric.denseRange_iff.1 hf y (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
    exact ⟨x, by rw [dist_comm]; exact hx⟩
  choose g hg using hex
  have hlim : ∀ y, Filter.Tendsto (fun n => f (g y n)) Filter.atTop (nhds y) := by
    intro y
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hg y n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hinj : Function.Injective g := by
    intro y y' h
    have h2 := hlim y'
    rw [← h] at h2
    exact tendsto_nhds_unique (hlim y) h2
  calc #Y ≤ #(ℕ → X) := Cardinal.mk_le_of_injective hinj
    _ = #X ^ ℵ₀ := by rw [← Cardinal.mk_nat, Cardinal.power_def]
    _ ≤ 𝔠 ^ ℵ₀ := Cardinal.power_le_power_right hX
    _ = 𝔠 := Cardinal.continuum_power_aleph0

theorem mk_padicComplex (q : ℕ) [Fact q.Prime] : #ℂ_[q] = 𝔠 := by
  apply le_antisymm
  · have hQp : #ℚ_[q] ≤ 𝔠 :=
      mk_le_continuum_of_denseRange _ (Padic.denseRange_ratCast q)
        (by rw [Cardinal.mkRat]; exact Cardinal.aleph0_le_continuum)
    have hAl : #(PadicAlgCl q) ≤ 𝔠 :=
      (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[q] (PadicAlgCl q)).trans
        (max_le hQp Cardinal.aleph0_le_continuum)
    exact mk_le_continuum_of_denseRange _ (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl q)) hAl
  · obtain ⟨g, -, -, hg⟩ :=
      (PerfectSpace.univ_perfect (α := ℂ_[q])).exists_nat_bool_injection Set.univ_nonempty
    calc 𝔠 = #(ℕ → Bool) := by
          rw [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.two_power_aleph0]
      _ ≤ #ℂ_[q] := Cardinal.mk_le_of_injective hg

theorem exists_ringEquiv_extending : ∀ (q : ℕ) [Fact q.Prime]
    (lam : algebraicClosure ℚ ℂ →+* ℂ_[q]),
    ∃ ι : ℂ ≃+* ℂ_[q], ∀ x : algebraicClosure ℚ ℂ, ι (x : ℂ) = lam x := by
  intro q _ lam
  let _ : Algebra (algebraicClosure ℚ ℂ) ℂ_[q] := lam.toAlgebra
  have _ : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hR : #(algebraicClosure ℚ ℂ) ≤ ℵ₀ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ (algebraicClosure ℚ ℂ)).trans
      (by rw [Cardinal.mkRat, max_self])
  have hK : ℵ₀ < #ℂ := by
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  obtain ⟨e, he⟩ := exists_ringEquiv_over (algebraicClosure ℚ ℂ) ℂ ℂ_[q] hR hK
    (by rw [Cardinal.mk_complex, mk_padicComplex])
  exact ⟨e, fun x => he x⟩

end GlobalTheory.PadicComplexIso
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpBinomialPowerSubOneSeriesIntegralityCompositio
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpBinomialPowerSubOneSeriesIntegralityCompositio
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.MulSeries

variable {q : ℕ} [Fact q.Prime]

def zcHom : ℤ_[q] →+* ℂ_[q] := (algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom

theorem zc_eq (a : ℤ_[q]) : zc a = zcHom a := rfl

theorem norm_zc (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  rw [norm_algebraMap', PadicInt.norm_def]

theorem coeff_DT (f : ℂ_[q]⟦X⟧) (n : ℕ) :
    coeff n (DT f) = coeff (n + 1) f * (n + 1) + coeff n f * n := by
  rw [DT, add_mul, one_mul, map_add (f := _), coeff_derivative]
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul, coeff_derivative]; simp

theorem coeff_one_add_mulS (a : ℤ_[q]) (n : ℕ) :
    coeff n (1 + mulS a : ℂ_[q]⟦X⟧) = zcHom (Ring.choose a n) := by
  cases n with
  | zero => simp [mulS]
  | succ n => simp [mulS, coeff_one, zc_eq]

theorem constantCoeff_mulS (a : ℤ_[q]) : constantCoeff (mulS a : ℂ_[q]⟦X⟧) = 0 := by
  simp [mulS]

theorem hasSubst_mulS (a : ℤ_[q]) : HasSubst (mulS a : ℂ_[q]⟦X⟧) :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_mulS a)

theorem choose_step (c : ℤ_[q]) (n : ℕ) :
    Ring.choose c (n + 1) * (n + 1) + Ring.choose c n * n = c * Ring.choose c n := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose c (n + 1)
  rw [descPochhammer_succ_right, Polynomial.smeval_mul, Ring.descPochhammer_eq_factorial_smul_choose] at h1
  simp only [Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast, pow_one, pow_zero,
    nsmul_eq_mul, mul_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h1
  have h0 : (n.factorial : ℤ_[q]) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  apply mul_left_cancel₀ h0
  linear_combination -h1

theorem DT_one_add_mulS (a : ℤ_[q]) :
    DT (1 + mulS a : ℂ_[q]⟦X⟧) = C (zc a) * (1 + mulS a) := by
  ext n
  rw [coeff_DT, coeff_C_mul, coeff_one_add_mulS, coeff_one_add_mulS, zc_eq]
  have := congrArg zcHom (choose_step a n)
  simpa using this

theorem DT_mulS (a : ℤ_[q]) : DT (mulS a : ℂ_[q]⟦X⟧) = C (zc a) * (1 + mulS a) := by
  rw [← DT_one_add_mulS]; simp [DT]

theorem ode_unique (c : ℂ_[q]) (h : ℂ_[q]⟦X⟧) {f g : ℂ_[q]⟦X⟧} (hf : DT f = C c * f + h)
    (hg : DT g = C c * g + h) (h0 : constantCoeff f = constantCoeff g) : f = g := by
  ext n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have h1 := congrArg (coeff n) hf
    have h2 := congrArg (coeff n) hg
    rw [coeff_DT, map_add (f := _), coeff_C_mul] at h1 h2
    have h3 : ((n : ℂ_[q]) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    apply mul_right_cancel₀ h3
    rw [ih] at h1
    linear_combination h1 - h2

theorem DT_logS : DT (logS : ℂ_[q]⟦X⟧) = 1 := by
  ext n
  rw [coeff_DT]
  cases n with
  | zero => simp [logS]
  | succ n =>
    have h3 : ((n : ℂ_[q]) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have h4 : ((n : ℂ_[q]) + 1 + 1) ≠ 0 := by exact_mod_cast (n + 1).succ_ne_zero
    simp only [logS, coeff_mk, coeff_one, Nat.succ_ne_zero, if_false]
    push_cast
    field_simp
    ring

theorem DT_subst_mulS (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧) :
    DT (f.subst (mulS a : ℂ_[q]⟦X⟧)) = C (zc a) * (DT f).subst (mulS a : ℂ_[q]⟦X⟧) := by
  have hs := hasSubst_mulS a
  have h2 := DT_mulS a
  have h1 : (DT f).subst (mulS a : ℂ_[q]⟦X⟧) =
      (1 + mulS a) * (derivative f).subst (mulS a : ℂ_[q]⟦X⟧) := by
    rw [DT, ← coe_substAlgHom hs, map_mul, map_add (f := _), map_one, substAlgHom_X]
  rw [h1]
  unfold DT at h2 ⊢
  rw [derivative_subst hs]
  linear_combination ((derivative f).subst (mulS a : ℂ_[q]⟦X⟧)) * h2

theorem constantCoeff_subst_mulS (a : ℤ_[q]) {f : ℂ_[q]⟦X⟧} (hf : constantCoeff f = 0) :
    constantCoeff (f.subst (mulS a : ℂ_[q]⟦X⟧)) = 0 := by
  have hs := hasSubst_mulS a
  obtain ⟨b, rfl⟩ : (X : ℂ_[q]⟦X⟧) ∣ f := X_dvd_iff.2 hf
  rw [← coe_substAlgHom hs, map_mul, substAlgHom_X, map_mul, constantCoeff_mulS, zero_mul]

theorem logS_subst (a : ℤ_[q]) :
    (logS : ℂ_[q]⟦X⟧).subst (mulS a : ℂ_[q]⟦X⟧) = C (zc a) * logS := by
  have hs := hasSubst_mulS a
  have h0 : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by simp [logS]
  refine ode_unique 0 (C (zc a)) ?_ ?_ ?_
  · rw [DT_subst_mulS, DT_logS, ← coe_substAlgHom hs]; simp
  · have := DT_logS (q := q)
    unfold DT at this ⊢
    rw [Derivation.leibniz, derivative_C]
    simp only [smul_eq_mul, mul_zero, add_zero, map_zero, zero_mul, zero_add]
    linear_combination (C (zc a)) * this
  · rw [constantCoeff_subst_mulS a h0, map_mul, h0, mul_zero]

theorem mulS_subst (a b : ℤ_[q]) :
    (mulS a : ℂ_[q]⟦X⟧).subst (mulS b : ℂ_[q]⟦X⟧) = mulS (a * b) := by
  have hs := hasSubst_mulS b
  have hz : zc (a * b) = zc a * zc b := by simp [zc_eq]
  refine ode_unique (zc (a * b)) (C (zc (a * b))) ?_ ?_ ?_
  · rw [DT_subst_mulS, DT_mulS, ← coe_substAlgHom hs, map_mul, map_add (f := _), map_one, hz, map_mul]
    have : (substAlgHom hs : ℂ_[q]⟦X⟧ →ₐ[ℂ_[q]] ℂ_[q]⟦X⟧) (C (zc a)) = C (zc a) :=
      (substAlgHom hs : ℂ_[q]⟦X⟧ →ₐ[ℂ_[q]] ℂ_[q]⟦X⟧).commutes (zc a)
    rw [this]
    ring
  · rw [DT_mulS]; ring
  · rw [constantCoeff_subst_mulS b (constantCoeff_mulS a), constantCoeff_mulS]

theorem mulS_one : (mulS (1 : ℤ_[q]) : ℂ_[q]⟦X⟧) = X := by
  refine ode_unique 1 1 ?_ ?_ ?_
  · rw [DT_mulS]; simp [zc_eq, add_comm]
  · simp [DT, add_comm]
  · simp [constantCoeff_mulS]

theorem bd_mulS (a : ℤ_[q]) : Bd 1 (mulS a : ℂ_[q]⟦X⟧) := by
  intro n
  rw [mulS, coeff_mk]
  split_ifs
  · simp
  · rw [norm_zc]; exact PadicInt.norm_le_one _

theorem bd_one_pow {h : ℂ_[q]⟦X⟧} (hh : Bd 1 h) (d : ℕ) : Bd 1 (h ^ d) := by
  induction d with
  | zero => intro n; rw [pow_zero, coeff_one]; split_ifs <;> simp
  | succ d ih =>
    intro n
    rw [pow_succ, coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (ih _) (norm_nonneg _) (hh _)

theorem bd_subst {f h : ℂ_[q]⟦X⟧} {A : ℝ} (hf : Bd A f) (hh : Bd 1 h) (h0 : constantCoeff h = 0) :
    Bd A (f.subst h) := by
  classical
  intro n
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' h0
  have hA : 0 ≤ A := (norm_nonneg _).trans (hf 0)
  rw [coeff_subst' hs, finsum_def]
  split_ifs
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hA fun d _ => ?_
    rw [smul_eq_mul, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (bd_one_pow hh d n)).trans (hf d)
  · simpa using hA

theorem bd_subst_mulS_iff (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧) (B : ℝ) (ha : ‖a‖ = 1) :
    Bd B (f.subst (mulS a : ℂ_[q]⟦X⟧)) ↔ Bd B f := by
  refine ⟨fun h => ?_, fun h => bd_subst h (bd_mulS a) (constantCoeff_mulS a)⟩
  obtain ⟨b, hb⟩ := (PadicInt.isUnit_iff.2 ha).exists_right_inv
  have h1 := bd_subst h (bd_mulS b) (constantCoeff_mulS b)
  rwa [subst_comp_subst_apply (hasSubst_mulS a) (hasSubst_mulS b), mulS_subst, hb, mulS_one,
    X_subst] at h1

theorem mulS_laws : ∀ (q : ℕ) [Fact q.Prime], (∀ a : ℤ_[q], Bd 1 (mulS a : ℂ_[q]⟦X⟧) ∧ constantCoeff (mulS a : ℂ_[q]⟦X⟧) = 0 ∧ coeff 1 (mulS a : ℂ_[q]⟦X⟧) = zc a ∧ (logS : ℂ_[q]⟦X⟧).subst (mulS a : ℂ_[q]⟦X⟧) = C (zc a) * logS) ∧ (∀ a b : ℤ_[q], (mulS a : ℂ_[q]⟦X⟧).subst (mulS b : ℂ_[q]⟦X⟧) = mulS (a * b)) ∧ (mulS (1 : ℤ_[q]) : ℂ_[q]⟦X⟧) = X ∧ (∀ (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧) (B : ℝ), ‖a‖ = 1 → (Bd B (f.subst (mulS a : ℂ_[q]⟦X⟧)) ↔ Bd B f)) ∧ DT (logS : ℂ_[q]⟦X⟧) = 1 ∧ (∀ a : ℤ_[q], ‖zc a‖ = ‖a‖) :=
  fun _ _ => ⟨fun a => ⟨bd_mulS a, constantCoeff_mulS a, by simp [mulS], logS_subst a⟩, mulS_subst,
    mulS_one, bd_subst_mulS_iff, DT_logS, norm_zc⟩

end GlobalTheory.MomOne.MulSeries
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpBinomialPowerSubOneSeriesIntegralityCompositioStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cpBinomialPowerSubOneSeries_integrality_composition_log : ∀ (q : ℕ) [Fact q.Prime], (∀ a : ℤ_[q], Bd 1 (mulS a : ℂ_[q]⟦X⟧) ∧ constantCoeff (mulS a : ℂ_[q]⟦X⟧) = 0 ∧ coeff 1 (mulS a : ℂ_[q]⟦X⟧) = zc a ∧ (logS : ℂ_[q]⟦X⟧).subst (mulS a : ℂ_[q]⟦X⟧) = C (zc a) * logS) ∧ (∀ a b : ℤ_[q], (mulS a : ℂ_[q]⟦X⟧).subst (mulS b : ℂ_[q]⟦X⟧) = mulS (a * b)) ∧ (mulS (1 : ℤ_[q]) : ℂ_[q]⟦X⟧) = X ∧ (∀ (a : ℤ_[q]) (f : ℂ_[q]⟦X⟧) (B : ℝ), ‖a‖ = 1 → (Bd B (f.subst (mulS a : ℂ_[q]⟦X⟧)) ↔ Bd B f)) ∧ DT (logS : ℂ_[q]⟦X⟧) = 1 ∧ (∀ a : ℤ_[q], ‖zc a‖ = ‖a‖) := by
  first | exact @GlobalTheory.MomOne.MulSeries.mulS_laws | exact GlobalTheory.MomOne.MulSeries.mulS_laws | (intros; apply GlobalTheory.MomOne.MulSeries.mulS_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeHeisenbergRelationsOneVariable
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeHeisenbergRelationsOneVariable
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem cmLatticeHermitianForm_add_left (d : ℕ) (x y z : ℂ) : h1 d (x + y) z = h1 d x z + h1 d y z := by
  simp only [h1]; ring

theorem cmLatticeHermitianForm_add_right (d : ℕ) (x y z : ℂ) : h1 d x (y + z) = h1 d x y + h1 d x z := by
  simp only [h1, map_add (f := _)]; ring

theorem cmLatticeHermitianForm_swap (d : ℕ) (x y : ℂ) :
    h1 d y x = h1 d x y - 2 * Complex.I * (((h1 d x y).im : ℝ) : ℂ) := by
  have h : h1 d y x = conj (h1 d x y) := by
    simp only [h1, map_mul, Complex.conj_ofReal, Complex.conj_conj]; ring
  rw [h]
  apply Complex.ext
  · simp
  · simp; ring

theorem cmLatticeTranslationOperator_comp (d : ℕ) (x y : ℂ) (F : ℂ → ℂ) :
    U1 d x (U1 d y F) = fun z => Complex.exp (-(Real.pi : ℂ) * Complex.I * (((h1 d x y).im : ℝ) : ℂ)) *
      U1 d (x + y) F z := by
  funext z
  simp only [U1]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc z x y]
  congr 2
  simp only [cmLatticeHermitianForm_add_left, cmLatticeHermitianForm_add_right]
  rw [cmLatticeHermitianForm_swap d x y]
  ring

theorem differentiable_cmLatticeTranslationOperator (d : ℕ) (x : ℂ) (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    Differentiable ℂ (U1 d x F) := by
  unfold U1 h1
  fun_prop

theorem cmLatticeWeylOperator_comp (d : ℕ) (hd : 0 < d) (x y : ℂ) (F : ℂ → ℂ) (h : InOK d (x * conj y)) :
    W1 d x (W1 d y F) = W1 d (x + y) F := by
  obtain ⟨u, v, h⟩ := h
  have hs : Real.sqrt d ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    exact (Real.sqrt_pos.2 this).ne'
  have him : (h1 d x y).im = v := by
    rw [h1, h, wK, Complex.im_ofReal_mul]
    simp
    field_simp
  have hre : Complex.normSq (x + y) = Complex.normSq x + Complex.normSq y + (2 * u + v) := by
    rw [Complex.normSq_add, h, wK]
    simp
    ring
  funext z
  have h2 : U1 d x (W1 d y F) z = Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq y : ℝ) : ℂ)) *
      U1 d x (U1 d y F) z := by
    simp only [U1, W1]; ring
  have h3 : W1 d x (W1 d y F) z = Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) *
      U1 d x (W1 d y F) z := rfl
  rw [h3, h2, cmLatticeTranslationOperator_comp]
  simp only [W1]
  rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add, him, hre]
  congr 1
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(u + v), ?_⟩
  push_cast
  ring

theorem cmLatticeTranslationOperator_theta_quasiPeriodicity (d : ℕ) (θ : ℂ → ℂ) (t l z : ℂ) (h : W1 d l θ = θ) :
    U1 d t θ (z + l) * θ z = kap1 d l t * (U1 d t θ z * θ (z + l)) := by
  have a := congrFun h z
  have b := congrFun h (z + t)
  simp only [W1, U1] at a b
  simp only [U1, kap1]
  have e : z + l + t = z + t + l := by ring
  rw [e]
  set A := θ (z + t + l)
  set B := θ (z + l)
  rw [← a, ← b]
  have key : Complex.exp (-(Real.pi : ℂ) * h1 d (z + l) t - (Real.pi : ℂ) / 2 * h1 d t t) *
      Complex.exp (-(Real.pi : ℂ) * h1 d z l - (Real.pi : ℂ) / 2 * h1 d l l) =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * (((h1 d l t).im : ℝ) : ℂ)) *
      (Complex.exp (-(Real.pi : ℂ) * h1 d (z + t) l - (Real.pi : ℂ) / 2 * h1 d l l) *
      Complex.exp (-(Real.pi : ℂ) * h1 d z t - (Real.pi : ℂ) / 2 * h1 d t t)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [cmLatticeHermitianForm_add_left]
    rw [cmLatticeHermitianForm_swap d l t]
    ring
  linear_combination (A * B * Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq l : ℝ) : ℂ))) * key

theorem heisenbergOne : ∀ d : ℕ, 0 < d → (∀ (x y : ℂ) (F : ℂ → ℂ), U1 d x (U1 d y F) = fun z => Complex.exp (-(Real.pi : ℂ) * Complex.I * (((h1 d x y).im : ℝ) : ℂ)) * U1 d (x + y) F z) ∧ (∀ F, U1 d 0 F = F) ∧ (∀ (x : ℂ) (F : ℂ → ℂ), Differentiable ℂ F → Differentiable ℂ (U1 d x F) ∧ Differentiable ℂ (W1 d x F)) ∧ (∀ (x : ℂ) (F : ℂ → ℂ) (z : ℂ), U1 d x (fun z => F (-z)) z = U1 d (-x) F (-z)) ∧ (∀ (x y : ℂ) (F : ℂ → ℂ), d % 4 = 3 → InOK d (x * conj y) → W1 d x (W1 d y F) = W1 d (x + y) F) ∧ (∀ (θ : ℂ → ℂ) (t l z : ℂ), W1 d l θ = θ → U1 d t θ (z + l) * θ z = kap1 d l t * (U1 d t θ z * θ (z + l))) ∧ (∀ (x : ℂ) (f F : ℂ → ℂ) (z : ℂ), W1 d x (fun z => f z * F z) z = f (z + x) * W1 d x F z ∧ U1 d x (fun z => f z * F z) z = f (z + x) * U1 d x F z) ∧ ∀ (x y z : ℂ), kap1 d x (y + z) = kap1 d x y * kap1 d x z ∧ kap1 d (x + y) z = kap1 d x z * kap1 d y z := by
  intro d hd
  refine ⟨cmLatticeTranslationOperator_comp d, ?_, ?_, ?_, fun x y F _ h => cmLatticeWeylOperator_comp d hd x y F h,
    fun θ t l z h => cmLatticeTranslationOperator_theta_quasiPeriodicity d θ t l z h, ?_, ?_⟩
  · intro F
    funext z
    simp [U1, h1]
  · intro x F hF
    refine ⟨differentiable_cmLatticeTranslationOperator d x F hF, ?_⟩
    exact (differentiable_cmLatticeTranslationOperator d x F hF).const_mul _
  · intro x F z
    simp only [U1, h1, map_neg]
    congr 1
    · congr 1; ring
    · congr 1; ring
  · intro x f F z
    simp only [W1, U1]
    constructor <;> ring
  · intro x y z
    simp only [kap1, cmLatticeHermitianForm_add_left, cmLatticeHermitianForm_add_right, Complex.add_im, ← Complex.exp_add]
    constructor <;> (congr 1; push_cast; ring)

end GlobalTheory.MomOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeHeisenbergRelationsOneVariableStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLattice_heisenberg_relations_one_variable : ∀ d : ℕ, 0 < d → (∀ (x y : ℂ) (F : ℂ → ℂ), U1 d x (U1 d y F) = fun z => Complex.exp (-(Real.pi : ℂ) * Complex.I * (((h1 d x y).im : ℝ) : ℂ)) * U1 d (x + y) F z) ∧ (∀ F, U1 d 0 F = F) ∧ (∀ (x : ℂ) (F : ℂ → ℂ), Differentiable ℂ F → Differentiable ℂ (U1 d x F) ∧ Differentiable ℂ (W1 d x F)) ∧ (∀ (x : ℂ) (F : ℂ → ℂ) (z : ℂ), U1 d x (fun z => F (-z)) z = U1 d (-x) F (-z)) ∧ (∀ (x y : ℂ) (F : ℂ → ℂ), d % 4 = 3 → InOK d (x * conj y) → W1 d x (W1 d y F) = W1 d (x + y) F) ∧ (∀ (θ : ℂ → ℂ) (t l z : ℂ), W1 d l θ = θ → U1 d t θ (z + l) * θ z = kap1 d l t * (U1 d t θ z * θ (z + l))) ∧ (∀ (x : ℂ) (f F : ℂ → ℂ) (z : ℂ), W1 d x (fun z => f z * F z) z = f (z + x) * W1 d x F z ∧ U1 d x (fun z => f z * F z) z = f (z + x) * U1 d x F z) ∧ ∀ (x y z : ℂ), kap1 d x (y + z) = kap1 d x y * kap1 d x z ∧ kap1 d (x + y) z = kap1 d x z * kap1 d y z := by
  first | exact @GlobalTheory.MomOne.heisenbergOne | exact GlobalTheory.MomOne.heisenbergOne | (intros; apply GlobalTheory.MomOne.heisenbergOne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MeanFundamentalDomainEqOfPeriodic
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory

theorem setIntegral_translate_of_periodic {n : Type} [Fintype n] (L : AddSubgroup (n → ℝ))
    [Countable L] (D : Set (n → ℝ)) (g : (n → ℝ) → ℂ)
    (hD : IsAddFundamentalDomain L D volume) (hp : ∀ p ∈ L, ∀ s, g (s + p) = g s)
    (s : n → ℝ) : ∫ t in D, g (s + t) = ∫ t in D, g t := by
  have hsD : IsAddFundamentalDomain L (s +ᵥ D) volume := hD.vadd_of_comm s
  have himg : (fun t => s + t) '' D = s +ᵥ D := by
    change (fun t => s +ᵥ t) '' D = s +ᵥ D
    exact Set.image_vadd
  rw [← (measurePreserving_add_left volume s).setIntegral_image_emb
    (MeasurableEquiv.addLeft s).measurableEmbedding g D, himg]
  refine hsD.setIntegral_eq hD (fun p x => ?_)
  rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
  exact hp p p.2 x

theorem mean_fundamentalDomain_eq_of_periodic :
    ∀ (n : Type) [Fintype n] (L L' : AddSubgroup (n → ℝ)) [Countable L] [Countable L'] (D D' : Set (n → ℝ)) (g : (n → ℝ) → ℂ), MeasureTheory.IsAddFundamentalDomain L D MeasureTheory.volume → MeasureTheory.IsAddFundamentalDomain L' D' MeasureTheory.volume → MeasureTheory.volume D < ⊤ → MeasureTheory.volume D' < ⊤ → Continuous g → (∃ C : ℝ, ∀ s, ‖g s‖ ≤ C) → (∀ p ∈ L, ∀ s, g (s + p) = g s) → (∀ p ∈ L', ∀ s, g (s + p) = g s) → ((MeasureTheory.volume D).toReal : ℂ) * ∫ s in D', g s = ((MeasureTheory.volume D').toReal : ℂ) * ∫ s in D, g s := by
  intro n _ L L' _ _ D D' g hD hD' hDfin hD'fin hg ⟨C, hC⟩ hp hp'
  have : IsFiniteMeasure (volume.restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hDfin⟩
  have : IsFiniteMeasure (volume.restrict D') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hD'fin⟩
  have hint : Integrable (Function.uncurry fun s t => g (s + t))
      ((volume.restrict D).prod (volume.restrict D')) := by
    refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun z => hC _)
    exact (hg.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
  have h1 : ∫ s in D, ∫ t in D', g (s + t) = ((volume D).toReal : ℂ) * ∫ t in D', g t := by
    simp_rw [setIntegral_translate_of_periodic L' D' g hD' hp']
    rw [setIntegral_const]
    simp [Complex.real_smul, Measure.real]
  have h2 : ∫ t in D', ∫ s in D, g (s + t) = ((volume D').toReal : ℂ) * ∫ s in D, g s := by
    have : ∀ t, ∫ s in D, g (s + t) = ∫ s in D, g s := fun t => by
      simp_rw [add_comm _ t]
      exact setIntegral_translate_of_periodic L D g hD hp t
    simp_rw [this]
    rw [setIntegral_const]
    simp [Complex.real_smul, Measure.real]
  rw [← h1, ← h2]
  exact integral_integral_swap hint

end GlobalTheory
end
