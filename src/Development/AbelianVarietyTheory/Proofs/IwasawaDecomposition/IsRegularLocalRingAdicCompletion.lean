module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
open IsLocalRing

namespace GlobalTheory.RegularCompletion

theorem isRegularLocalRing_adicCompletion :
    ∀ (T : Type) [CommRing T] [IsRegularLocalRing T],
      IsRegularLocalRing (AdicCompletion (maximalIdeal T) T) := by
  intro T _ _
  haveI : IsNoetherianRing (AdicCompletion (maximalIdeal T) T) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion T (maximalIdeal T)
  set S := AdicCompletion (maximalIdeal T) T

  obtain ⟨s, hcard, hs⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (maximalIdeal T).fg_of_isNoetherianRing
  set xs := s.toList
  have hofl : Ideal.ofList xs = maximalIdeal T := by
    rw [← hs]; unfold Ideal.ofList; congr 1; ext x; simp [xs]
  have hlen : xs.length = (maximalIdeal T).spanFinrank := by simp [xs, hcard]
  have hreg : RingTheory.Sequence.IsRegular T xs := GlobalTheory.isRegular_of_length_eq_spanFinrank hofl hlen
  have hmem : ∀ r ∈ xs.map (algebraMap T S), r ∈ maximalIdeal S := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem _ (hofl ▸ Ideal.subset_span hx)
  have hregS : RingTheory.Sequence.IsRegular S (xs.map (algebraMap T S)) :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr
      (hreg.toIsWeaklyRegular.of_flat)
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hregS
  have hnt : Nontrivial (S ⧸ Ideal.ofList (xs.map (algebraMap T S))) := by
    rw [Ideal.Quotient.nontrivial_iff]
    intro htop
    apply hregS.2
    simp [htop]
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  rw [AdicCompletion.spanFinrank_maximalIdeal_eq, ← hdim]
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ Ideal.ofList (xs.map (algebraMap T S))) :=
    ringKrullDim_nonneg_of_nontrivial
  rw [List.length_map, hlen]
  calc ((Submodule.spanFinrank (maximalIdeal T) : ℕ) : WithBot ℕ∞)
      = 0 + ((Submodule.spanFinrank (maximalIdeal T) : ℕ) : WithBot ℕ∞) := (zero_add _).symm
    _ ≤ _ := add_le_add_left h0 _

end GlobalTheory.RegularCompletion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open Filter Topology Asymptotics Set

namespace GlobalTheory.Mem.RayPrimes

theorem log_bounded (g : ℝ → ℂ) (L : ℂ → ℂ) (hL : Continuous L) (h1 : L 1 ≠ 0)
    (hg : ContinuousOn g (Ioi 1)) (he : ∀ s : ℝ, 1 < s → cexp (g s) = L s) :
    g =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  have hc : Continuous (fun s : ℝ => L s / L 1 - 1) := by fun_prop (disch := exact h1)
  have ht : ∀ᶠ s : ℝ in 𝓝 1, ‖L s / L 1 - 1‖ < 1 / 2 := by
    have := (hc.norm.tendsto 1)
    simp only [ofReal_one, div_self h1, sub_self, norm_zero] at this
    exact this.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1 ht
  have hb' : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), ‖L s / L 1 - 1‖ < 1 / 2 := fun s hs => hb (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2])
  have hslit : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), 1 + (L s / L 1 - 1) ∈ slitPlane := fun s hs =>
    mem_slitPlane_of_norm_lt_one (by linarith [hb' s hs])
  set k : ℝ → ℂ := fun s => g s - log (1 + (L s / L 1 - 1)) with hk
  have hkc : ContinuousOn k (Ioo 1 (1 + δ)) :=
    (hg.mono Ioo_subset_Ioi_self).sub
      (ContinuousOn.clog (continuous_const.add hc).continuousOn hslit)
  have hke : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), cexp (k s) = L 1 := fun s hs => by
    have hne : L s ≠ 0 := by rw [← he s hs.1]; exact exp_ne_zero _
    simp only [hk]
    rw [exp_sub, exp_log (slitPlane_ne_zero (hslit s hs)), he s hs.1, add_sub_cancel]
    field_simp
  have hconst : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), k s = k (1 + δ / 2) := fun s hs =>
    Complex.isCoveringMap_exp.constOn_of_comp isPreconnected_Ioo hkc
      (fun a ha b hb => Subtype.ext (by simp only; rw [hke a ha, hke b hb])) hs
      ⟨by linarith, by linarith⟩
  refine IsBigO.of_bound (‖k (1 + δ / 2)‖ + 1) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 1 + δ by linarith)] with s hs
  have h2 : g s = k (1 + δ / 2) + log (1 + (L s / L 1 - 1)) := by
    rw [← hconst s hs]; simp [hk]
  have h3 := norm_log_one_add_half_le_self (hb' s hs).le
  rw [h2, norm_one, mul_one]
  refine (norm_add_le _ _).trans ?_
  linarith [hb' s hs]

section series

variable {ι : Type} (n : ι → ℕ) (hn : ∀ v, 2 ≤ n v) (a : ι → ℂ) (ha : ∀ v, ‖a v‖ ≤ 1)
include hn ha

theorem norm_term_le (v : ι) {s t : ℝ} (hst : t ≤ s) :
    ‖a v * (n v : ℂ) ^ (-(s : ℂ))‖ ≤ (n v : ℝ) ^ (-t) := by
  have h2 : (2 : ℝ) ≤ n v := by exact_mod_cast hn v
  rw [norm_mul, norm_natCast_cpow_of_pos (by linarith [hn v])]
  simp only [neg_re, ofReal_re]
  calc ‖a v‖ * (n v : ℝ) ^ (-s) ≤ 1 * (n v : ℝ) ^ (-t) := by
        gcongr
        · exact ha v
        · linarith
    _ = _ := one_mul _

theorem norm_term_le_inv (v : ι) {s : ℝ} (hs : 1 ≤ s) :
    ‖a v * (n v : ℂ) ^ (-(s : ℂ))‖ ≤ (n v : ℝ)⁻¹ := by
  have := norm_term_le n hn a ha v hs
  rwa [Real.rpow_neg_one] at this

theorem norm_term_le_half (v : ι) {s : ℝ} (hs : 1 ≤ s) :
    ‖a v * (n v : ℂ) ^ (-(s : ℂ))‖ ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ n v := by exact_mod_cast hn v
  refine (norm_term_le_inv n hn a ha v hs).trans ?_
  rw [one_div]; gcongr

theorem continuousOn_logSum (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s)) :
    ContinuousOn (fun s : ℝ => ∑' v, -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ)))) (Ioi 1) := by
  intro s hs1
  obtain ⟨t, ht1, hts⟩ := exists_between (show (1 : ℝ) < s from hs1)
  have : ContinuousOn (fun s : ℝ => ∑' v, -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ)))) (Ioi t) := by
    refine continuousOn_tsum (u := fun v => 3 / 2 * (n v : ℝ) ^ (-t)) ?_ ((hs t ht1).mul_left _) ?_
    · intro v
      refine ContinuousOn.neg (ContinuousOn.clog ?_ ?_)
      · have h0 : (n v : ℂ) ≠ 0 := by
          have := hn v
          exact_mod_cast (by omega : n v ≠ 0)
        refine (continuous_const.sub (continuous_const.mul ?_)).continuousOn
        exact Continuous.const_cpow (by fun_prop) (Or.inl h0)
      · intro x hx
        rw [sub_eq_add_neg]
        refine mem_slitPlane_of_norm_lt_one ?_
        rw [norm_neg]
        linarith [norm_term_le_half n hn a ha v (ht1.le.trans (le_of_lt hx))]
    · intro v x hx
      rw [norm_neg, sub_eq_add_neg]
      have h := norm_log_one_add_half_le_self (z := -(a v * (n v : ℂ) ^ (-(x : ℂ))))
        (by rw [norm_neg]; exact norm_term_le_half n hn a ha v (ht1.le.trans (le_of_lt hx)))
      rw [norm_neg] at h
      linarith [norm_term_le n hn a ha v (le_of_lt hx)]
  exact (this.continuousAt (Ioi_mem_nhds hts)).continuousWithinAt

theorem summable_term (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s)) {s : ℝ} (h : 1 < s) :
    Summable fun v => a v * (n v : ℂ) ^ (-(s : ℂ)) :=
  Summable.of_norm_bounded (hs s h) fun v => norm_term_le n hn a ha v le_rfl

theorem logSum_sub_bounded (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s)) :
    (fun s : ℝ => (∑' v, -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ)))) - ∑' v, a v * (n v : ℂ) ^ (-(s : ℂ)))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  refine IsBigO.of_bound (∑' v, (n v : ℝ) ^ (-(2 : ℝ))) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs1
  have hs1 : 1 < s := hs1
  have hb : ∀ v, ‖-log (1 - a v * (n v : ℂ) ^ (-(s : ℂ))) - a v * (n v : ℂ) ^ (-(s : ℂ))‖
      ≤ (n v : ℝ) ^ (-(2 : ℝ)) := by
    intro v
    set z := a v * (n v : ℂ) ^ (-(s : ℂ)) with hz
    have h1 : ‖z‖ ≤ 1 / 2 := norm_term_le_half n hn a ha v hs1.le
    have h2 : ‖z‖ ≤ (n v : ℝ)⁻¹ := norm_term_le_inv n hn a ha v hs1.le
    have h3 := norm_log_one_add_sub_self_le (z := -z) (by rw [norm_neg]; linarith)
    have h4 : -log (1 - z) - z = -(log (1 + -z) - -z) := by rw [← sub_eq_add_neg 1 z]; ring
    rw [h4, norm_neg]
    refine h3.trans ?_
    rw [norm_neg, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two, ← inv_pow]
    have h5 : (1 - ‖z‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have h6 : ‖z‖ ^ 2 ≤ ((n v : ℝ)⁻¹) ^ 2 := by gcongr
    have h7 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ ≤ ‖z‖ ^ 2 * 2 := by gcongr
    linarith
  have hsum := summable_term n hn a ha hs hs1
  have hd := Summable.of_norm_bounded (hs 2 (by norm_num)) hb
  have hl : Summable fun v => -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ))) := by
    simpa using hd.add hsum
  rw [← hl.tsum_sub hsum, norm_one, mul_one]
  exact tsum_of_norm_bounded (hs 2 (by norm_num)).hasSum hb

end series

section orth

variable {G : Type} [CommGroup G] [Fintype G]

theorem norm_char (χ : G →* ℂˣ) (x : G) : ‖(χ x : ℂ)‖ = 1 := by
  refine Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card G) ?_ Fintype.card_ne_zero
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]

theorem sum_char_eq_zero [Fintype (G →* ℂˣ)] {x : G} (hx : x ≠ 1) :
    ∑ χ : G →* ℂˣ, (χ x : ℂ) = 0 := by
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hx
  let f : (G →* ℂˣ) →* ℂ :=
    { toFun := fun χ => (χ x : ℂ), map_one' := by simp, map_mul' := by simp }
  refine sum_hom_units_eq_zero f ?_
  intro h
  apply hφ
  have := DFunLike.congr_fun h φ
  simpa [f] using this

theorem not_summable_class {ι : Type} (n : ι → ℕ) (hn : ∀ v, 2 ≤ n v) (cl : ι → G)
    (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s))
    (hχ : ∀ χ : G →* ℂˣ, χ ≠ 1 → ∃ L : ℂ → ℂ, Continuous L ∧ L 1 ≠ 0 ∧ ∀ s : ℝ, 1 < s →
      cexp (∑' v, -log (1 - (χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ)))) = L s)
    (Z : ℂ → ℂ) (hZ : Continuous Z) (hZ1 : Z 1 ≠ 0)
    (h1 : ∀ s : ℝ, 1 < s → Z s = (s - 1) *
      cexp (∑' v, -log (1 - ((1 : G →* ℂˣ) (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ)))))
    (c : G) : ¬ Summable fun v : {v // cl v = c} => (n v : ℝ)⁻¹ := by
  classical
  intro hc
  have : Fintype (G →* ℂˣ) := Fintype.ofFinite _
  let g : (G →* ℂˣ) → ℝ → ℂ := fun χ s => ∑' v, -log (1 - (χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ)))
  let P : (G →* ℂˣ) → ℝ → ℂ := fun χ s => ∑' v, (χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ))
  have hgP : ∀ χ, (fun s => g χ s - P χ s) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := fun χ =>
    logSum_sub_bounded n hn _ (fun v => (norm_char χ _).le) hs
  have hP : ∀ χ, χ ≠ 1 → P χ =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    intro χ h
    obtain ⟨L, hL, hL1, hL2⟩ := hχ χ h
    have := log_bounded (g χ) L hL hL1
      (continuousOn_logSum n hn _ (fun v => (norm_char χ _).le) hs) hL2
    simpa using this.sub (hgP χ)
  have hS : (fun s => ∑ χ, (χ c⁻¹ : ℂ) * P χ s) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    have hc' := (summable_subtype_iff_indicator (f := fun v => (n v : ℝ)⁻¹)
      (s := {v | cl v = c})).1 hc
    have hc'' := hc'.mul_left (Fintype.card (G →* ℂˣ) : ℝ)
    refine IsBigO.of_bound (∑' v, (Fintype.card (G →* ℂˣ) : ℝ) *
      ({v | cl v = c}).indicator (fun v => (n v : ℝ)⁻¹) v) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs1
    have hs1 : 1 < s := hs1
    have hsum : ∀ χ : G →* ℂˣ, Summable fun v =>
        (χ c⁻¹ : ℂ) * ((χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ))) := fun χ =>
      (summable_term n hn _ (fun v => (norm_char χ _).le) hs hs1).mul_left _
    simp only [P, ← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun χ _ => hsum χ), norm_one, mul_one]
    refine tsum_of_norm_bounded hc''.hasSum fun v => ?_
    by_cases hv : cl v = c
    · rw [indicator_of_mem (by exact hv)]
      refine (norm_sum_le _ _).trans ?_
      rw [← nsmul_eq_mul, ← Finset.card_univ]
      refine Finset.sum_le_card_nsmul _ _ _ fun χ _ => ?_
      rw [norm_mul, norm_char, one_mul]
      exact norm_term_le_inv n hn (fun v => (χ (cl v) : ℂ)) (fun v => (norm_char χ _).le) v hs1.le
    · rw [indicator_of_notMem (by exact hv)]
      have : c⁻¹ * cl v ≠ 1 := fun h => hv (inv_mul_eq_one.1 h).symm
      have h0 := sum_char_eq_zero this
      simp only [map_mul, Units.val_mul] at h0
      simp only [← mul_assoc, ← Finset.sum_mul, h0]
      simp
  have hP1 : P 1 =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    have h2 : (fun s => ∑ χ ∈ Finset.univ.erase 1, (χ c⁻¹ : ℂ) * P χ s) =O[𝓝[>] 1]
        (fun _ => (1 : ℝ)) :=
      (IsBigO.sum fun χ hχ => (hP χ (Finset.ne_of_mem_erase hχ)).const_mul_left
        (χ c⁻¹ : ℂ)).congr_left fun s => Finset.sum_apply _ _ _
    refine (hS.sub h2).congr_left fun s => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G →* ℂˣ))]
    simp
  have hg1 : g 1 =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    simpa using (hgP 1).add hP1
  obtain ⟨B, hB⟩ := hg1.bound
  have hlim : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 (Z 1)) := by
    have : Continuous fun s : ℝ => Z s := by fun_prop
    simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
  have hlim0 : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun s : ℝ => ‖(s : ℂ) - 1‖ * Real.exp B) ?_ ?_
    · filter_upwards [hB, self_mem_nhdsWithin] with s h hs1
      rw [h1 s hs1, norm_mul, norm_exp]
      gcongr
      rw [norm_one, mul_one] at h
      exact (re_le_norm _).trans h
    · have : Continuous fun s : ℝ => ‖(s : ℂ) - 1‖ * Real.exp B := by fun_prop
      simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
  exact hZ1 (tendsto_nhds_unique hlim hlim0)

end orth

section field

variable {K : Type} [Field K] [NumberField K]

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

end field

end GlobalTheory.Mem.RayPrimes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotInjectiveTwoPrimesEqualNormCofinite
open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.Mem.ZetaPole

theorem dedekindZeta_eq_tsum_ideal (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = ∑' I : Ideal (𝓞 K), ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have h := (GlobalTheory.Mem.summable_norm_absNorm_cpow K hs).of_norm.hasSum
  rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I)).hasSum_iff] at h
  refine HasSum.tsum_eq (h.sigma fun n => ?_)
  have : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      ((fun I : Ideal (𝓞 K) => ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)) ∘
        (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I))) ⟨n, I⟩ =
          (n : ℂ) ^ (-s) := by
    rintro ⟨I, rfl⟩; rfl
  simp only [this]
  have := Fintype.ofFinite {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  have e : LSeries.term (fun n => (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s n =
      ∑ _I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}, (n : ℂ) ^ (-s) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hs0]
    · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
      simp
  rw [e]
  exact hasSum_fintype _

noncomputable def logFactor (n : ℕ) (s : ℝ) : ℝ := -Real.log (1 - (n : ℝ) ^ (-s))

theorem rpow_lt_one {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 0 < s) : (n : ℝ) ^ (-s) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn) (by linarith)

theorem logFactor_nonneg {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 0 < s) : 0 ≤ logFactor n s := by
  have h1 := rpow_lt_one hn hs
  have h2 : 0 ≤ (n : ℝ) ^ (-s) := by positivity
  unfold logFactor
  have := Real.log_nonpos (x := 1 - (n : ℝ) ^ (-s)) (by linarith) (by linarith)
  linarith

theorem logFactor_le {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 1 ≤ s) : logFactor n s ≤ logFactor n 1 := by
  have h1 := rpow_lt_one hn one_pos
  have h2 : (n : ℝ) ^ (-s) ≤ (n : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.le) (by linarith)
  unfold logFactor
  have := Real.log_le_log (x := 1 - (n : ℝ) ^ (-1 : ℝ)) (y := 1 - (n : ℝ) ^ (-s))
    (by linarith) (by linarith)
  linarith

theorem ofReal_logFactor {n : ℕ} (hn : 1 < n) {s : ℝ} (hs : 0 < s) :
    ((logFactor n s : ℝ) : ℂ) = -Complex.log (1 - (n : ℂ) ^ (-(s : ℂ))) := by
  have h1 := rpow_lt_one hn hs
  unfold logFactor
  rw [Complex.ofReal_neg, Complex.ofReal_log (by linarith), Complex.ofReal_sub,
    Complex.ofReal_cpow (Nat.cast_nonneg _)]
  simp

theorem summable_logFactor (K : Type) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    Summable fun v : HeightOneSpectrum (𝓞 K) => logFactor (Ideal.absNorm v.asIdeal) s := by
  have hS := (GlobalTheory.Mem.summable_norm_absNorm_cpow K (s := (s : ℂ)) (by simpa using hs)).of_norm
  have pinj : Function.Injective fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal := fun v w h =>
    HeightOneSpectrum.ext h
  have h := (Summable.clog_one_sub (hS.comp_injective pinj)).neg
  rw [← Complex.summable_ofReal]
  refine h.congr fun v => ?_
  rw [ofReal_logFactor (NumberField.HeightOneSpectrum.one_lt_absNorm v) (by linarith)]
  rfl

theorem norm_dedekindZeta_eq_exp (K : Type) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    ‖dedekindZeta K s‖ =
      Real.exp (∑' v : HeightOneSpectrum (𝓞 K), logFactor (Ideal.absNorm v.asIdeal) s) := by
  classical
  have hs' : 1 < (s : ℂ).re := by simpa using hs
  have hs0 : (s : ℂ) ≠ 0 := by rintro h; rw [h] at hs'; norm_num at hs'
  have h := GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K (fun I => if I = ⊥ then 0 else 1)
    (by simp) (by simp) (fun I J => by
      by_cases hI : I = ⊥ <;> by_cases hJ : J = ⊥ <;> simp [hI, hJ, Ideal.mul_eq_bot])
    (fun I => by split_ifs <;> simp) s hs'
  have e1 : ∀ I : Ideal (𝓞 K), (if I = ⊥ then (0 : ℂ) else 1) * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-(s : ℂ))
      = ((Ideal.absNorm I : ℕ) : ℂ) ^ (-(s : ℂ)) := fun I => by
    by_cases hI : I = ⊥
    · simp [hI, hs0]
    · simp [hI]
  simp only [e1] at h
  simp only [← ofReal_logFactor (NumberField.HeightOneSpectrum.one_lt_absNorm _)
    (lt_trans one_pos hs)] at h
  rw [dedekindZeta_eq_tsum_ideal K hs', h, ← Complex.ofReal_tsum, Complex.norm_exp,
    Complex.ofReal_re]

theorem not_injective_double_primes :
    ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ∀ f : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} × Bool → HeightOneSpectrum (𝓞 F), Function.Injective f → (∀ x, Ideal.absNorm (f x).asIdeal = Ideal.absNorm x.1.1.asIdeal) → False := by
  intro K F _ _ _ _ S hS f hf hN
  set c : ℝ := ∑ v ∈ hS.toFinset, logFactor (Ideal.absNorm v.asIdeal) 1 with hc
  have key : ∀ s : ℝ, 1 < s →
      Real.exp (-2 * c) * ‖dedekindZeta K s‖ ^ 2 ≤ ‖dedekindZeta F s‖ := by
    intro s hs
    rw [norm_dedekindZeta_eq_exp K hs, norm_dedekindZeta_eq_exp F hs, sq, ← Real.exp_add,
      ← Real.exp_add, Real.exp_le_exp]
    have hK := summable_logFactor K hs
    have hF := summable_logFactor F hs
    have h1 := tsum_comp_le_tsum_of_inj hF (fun v => logFactor_nonneg
      (NumberField.HeightOneSpectrum.one_lt_absNorm v) (by linarith)) hf
    have h2 := hF.comp_injective hf
    have e : ((fun v : HeightOneSpectrum (𝓞 F) => logFactor (Ideal.absNorm v.asIdeal) s) ∘ f) =
        fun x => logFactor (Ideal.absNorm x.1.1.asIdeal) s := by
      funext x
      simp only [Function.comp_apply, hN]
    rw [e] at h1 h2
    rw [h2.tsum_prod] at h1
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul,
      tsum_mul_left, Nat.cast_ofNat] at h1
    have h3 := hK.sum_add_tsum_compl (s := hS.toFinset)
    rw [hS.coe_toFinset] at h3
    have h4 : ∑ v ∈ hS.toFinset, logFactor (Ideal.absNorm v.asIdeal) s ≤ c :=
      Finset.sum_le_sum fun v _ =>
        logFactor_le (NumberField.HeightOneSpectrum.one_lt_absNorm v) hs.le
    have h5 : ∑' x : ↑(Sᶜ), logFactor (Ideal.absNorm x.1.asIdeal) s =
      ∑' x : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, logFactor (Ideal.absNorm x.1.asIdeal) s := rfl
    linarith
  have tK := (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).norm
  have tF := (tendsto_sub_one_mul_dedekindZeta_nhdsGT F).norm
  have t0 : Tendsto (fun s : ℝ => ‖(s : ℂ) - 1‖) (𝓝[>] 1) (𝓝 0) := by
    have : Continuous fun s : ℝ => ‖(s : ℂ) - 1‖ := by fun_prop
    simpa using (this.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 1))
  have hle := le_of_tendsto_of_tendsto ((tK.pow 2).const_mul (Real.exp (-2 * c))) (t0.mul tF) (by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have := mul_le_mul_of_nonneg_left (key s hs) (sq_nonneg ‖(s : ℂ) - 1‖)
    simp only [norm_mul]
    nlinarith)
  have hpos : 0 < ‖(dedekindZeta_residue K : ℂ)‖ :=
    norm_pos_iff.2 (by exact_mod_cast dedekindZeta_residue_ne_zero K)
  have : 0 < Real.exp (-2 * c) * ‖(dedekindZeta_residue K : ℂ)‖ ^ 2 := by positivity
  linarith

end GlobalTheory.Mem.ZetaPole
end
