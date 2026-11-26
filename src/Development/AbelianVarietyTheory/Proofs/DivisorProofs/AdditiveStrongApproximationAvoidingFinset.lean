module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveStrongApproximationAvoidingFinset
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveStrongApproximationAvoidingFinset
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
open Filter

namespace GlobalTheory.AddApproxPlaces


open NumberField.mixedEmbedding MeasureTheory in
theorem exists_small_of_infinitePlace (F : Type) [Field F] [NumberField F] (w₀ : InfinitePlace F)
    (f : InfinitePlace F → NNReal) (hf : ∀ w, f w ≠ 0) :
    ∃ g : F, g ≠ 0 ∧ (∀ w : InfinitePlace F, w ≠ w₀ → w g < f w) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F g ≤ 1 := by
  classical
  obtain ⟨g, hg, hB⟩ := adjust_f F (f := f) (w₁ := w₀) ((minkowskiBound F 1).toNNReal + 1) (fun w _ => hf w)
  have h : minkowskiBound F 1 < volume (convexBodyLT F g) := by
    rw [convexBodyLT_volume, hB, ← ENNReal.coe_toNNReal (minkowskiBound_lt_top F 1).ne, ← ENNReal.coe_mul,
      ENNReal.coe_lt_coe, ENNReal.toNNReal_coe]
    exact (lt_add_one _).trans_le (le_mul_of_one_le_left zero_le (one_le_convexBodyLTFactor F))
  obtain ⟨a, ha, hlt⟩ := exists_ne_zero_mem_ringOfIntegers_lt F h
  refine ⟨a, RingOfIntegers.coe_ne_zero_iff.2 ha, fun w hw => ?_, fun v => v.valuation_le_one a⟩
  rw [← hg w hw]; exact hlt w


open NumberField.mixedEmbedding MeasureTheory nonZeroDivisors in
theorem exists_small_of_finitePlace (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (f : InfinitePlace F → NNReal) (hf : ∀ w, f w ≠ 0) :
    ∃ g : F, g ≠ 0 ∧ (∀ w : InfinitePlace F, w g < f w) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ p → v.valuation F g ≤ 1 := by
  classical
  set P : NNReal := convexBodyLTFactor F * ∏ w, (f w) ^ (w.mult) with hP
  have hP0 : 0 < P := pos_iff_ne_zero.2 (mul_ne_zero (convexBodyLTFactor_ne_zero F)
    (Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (hf w)))
  set B : NNReal := (minkowskiBound F 1).toNNReal with hB
  have hN : (1 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((B : ℝ) / P) hN
  have hJ : ((p.asIdeal ^ k : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (pow_ne_zero _ p.ne_bot)
  let I : (FractionalIdeal (𝓞 F)⁰ F)ˣ := (Units.mk0 _ hJ)⁻¹
  have hI : minkowskiBound F I = ENNReal.ofReal (((Ideal.absNorm p.asIdeal : ℝ) ^ k)⁻¹) * minkowskiBound F 1 := by
    unfold minkowskiBound
    rw [volume_fundamentalDomain_fractionalIdealLatticeBasis F 1]
    simp only [volume_fundamentalDomain_fractionalIdealLatticeBasis, I, Units.val_inv_eq_inv_val,
      Units.val_mk0, map_inv₀, FractionalIdeal.coeIdeal_absNorm, Units.val_one, map_one, map_pow]
    simp [mul_assoc]
  have h : minkowskiBound F I < volume (convexBodyLT F f) := by
    have hpos : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) ^ k := by positivity
    rw [hI, convexBodyLT_volume, ← ENNReal.coe_toNNReal (minkowskiBound_lt_top F 1).ne, ← hB, ← ENNReal.coe_mul, ← hP,
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hP0), inv_mul_lt_iff₀ hpos]
    exact (div_lt_iff₀ (by exact_mod_cast hP0)).1 hk
  obtain ⟨a, ha, ha0, hlt⟩ := exists_ne_zero_mem_ideal_lt F I h
  refine ⟨a, ha0, hlt, fun v hv => ?_⟩
  have hnle : ¬ p.asIdeal ^ k ≤ v.asIdeal := fun hle =>
    hv (HeightOneSpectrum.ext (p.isMaximal.eq_of_le v.isPrime.ne_top (v.isPrime.le_of_pow_le hle)).symm)
  obtain ⟨b, hb, hbv⟩ := SetLike.not_le_iff_exists.1 hnle
  have ha' : a ∈ ((p.asIdeal ^ k : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    simpa [I] using ha
  have hab := (FractionalIdeal.mem_inv_iff hJ).1 ha' (algebraMap (𝓞 F) F b)
    (FractionalIdeal.mem_coeIdeal_of_mem _ hb)
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hab
  have h1 : v.valuation F (algebraMap (𝓞 F) F b) = 1 :=
    le_antisymm (v.valuation_le_one b) (not_lt.1 fun h => hbv ((v.valuation_lt_one_iff_mem b).1 h))
  have h2 : v.valuation F (algebraMap (𝓞 F) F c) ≤ 1 := v.valuation_le_one c
  rwa [hc, map_mul, h1, mul_one] at h2

theorem exists_int_nhds_finite (F : Type) [Field F] [NumberField F] (N : Set (Af F)) (hN : N ∈ 𝓝 (0 : Af F)) :
    ∃ m : 𝓞 F, m ≠ 0 ∧ ∀ y : Af F,
      (∀ v, Valued.v (evalV F v y) ≤ v.valuation F (algebraMap (𝓞 F) F m)) → y ∈ N := by
  have hM : ∀ᶠ a in 𝓝 (0 : Af F), ∀ c ∈ {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F}, a * c ∈ N := by
    refine (GlobalTheory.AdeleCocompact.isCompact_integral F).eventually_forall_of_forall_eventually fun c _ => ?_
    have hcont : Continuous (fun p : Af F × Af F => p.1 * p.2) := by fun_prop
    exact hcont.continuousAt.eventually_mem (by simpa using hN)
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele F).eventually hM).exists
  have h0 : ((n.factorial : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
  refine ⟨(n.factorial : ℕ), Nat.cast_ne_zero.2 n.factorial_ne_zero, fun y hy => ?_⟩
  have e : y = ((n.factorial : ℕ) : Af F) * (algebraMap F (Af F) ((n.factorial : ℕ) : F)⁻¹ * y) := by
    rw [← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul, mul_inv_cancel₀ h0, map_one, one_mul]
  rw [e]
  refine hn _ fun v => ?_
  have e' : (algebraMap F (Af F) ((n.factorial : ℕ) : F)⁻¹ * y) v =
      (((((n.factorial : ℕ) : F)⁻¹ : F)) : v.adicCompletion F) * evalV F v y := rfl
  rw [e', HeightOneSpectrum.mem_adicCompletionIntegers, map_mul,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
  have h1 := hy v
  rw [map_natCast] at h1
  have h2 : v.valuation F ((n.factorial : ℕ) : F) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  exact (inv_mul_le_one₀ (pos_iff_ne_zero.2 h2)).2 h1

theorem exists_delta_nhds_infinite (F : Type) [Field F] [NumberField F] (N : Set (Ainf F))
    (hN : N ∈ 𝓝 (0 : Ainf F)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : Ainf F, (∀ w, ‖y w‖ < δ) → y ∈ N := by
  have hN' : N ∈ 𝓝 (0 : (w : InfinitePlace F) → w.Completion) := hN
  obtain ⟨δ, hδ, h⟩ := Metric.mem_nhds_iff.1 hN'
  exact ⟨δ, hδ, fun y hy => h (mem_ball_zero_iff.2 ((pi_norm_lt_iff hδ).2 hy))⟩

theorem exists_small (F : Type) [Field F] [NumberField F] (S₁ : Finset (InfinitePlace F))
    (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (hS : S₁.Nonempty ∨ S₂.Nonempty)
    (m : 𝓞 F) (hm : m ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ g : F, g ≠ 0 ∧ (∀ w, w ∉ S₁ → w g < δ) ∧
      ∀ v, v ∉ S₂ → v.valuation F g ≤ v.valuation F (algebraMap (𝓞 F) F m) := by
  have hm' : algebraMap (𝓞 F) F m ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 hm
  have hw : ∀ w : InfinitePlace F, 0 < w (algebraMap (𝓞 F) F m) := fun w => InfinitePlace.pos_iff.2 hm'
  let f : InfinitePlace F → NNReal := fun w => ⟨δ / w (algebraMap (𝓞 F) F m), (div_pos hδ (hw w)).le⟩
  have hf : ∀ w, f w ≠ 0 := fun w => NNReal.coe_ne_zero.1 (div_pos hδ (hw w)).ne'
  obtain ⟨g, hg, h1, h2⟩ : ∃ g : F, g ≠ 0 ∧ (∀ w, w ∉ S₁ → w g < f w) ∧ ∀ v, v ∉ S₂ → v.valuation F g ≤ 1 := by
    rcases hS with ⟨w₀, hw₀⟩ | ⟨p, hp⟩
    · obtain ⟨g, hg, h1, h2⟩ := exists_small_of_infinitePlace F w₀ f hf
      exact ⟨g, hg, fun w hw => h1 w (fun h => hw (h ▸ hw₀)), fun v _ => h2 v⟩
    · obtain ⟨g, hg, h1, h2⟩ := exists_small_of_finitePlace F p f hf
      exact ⟨g, hg, fun w _ => h1 w, fun v hv => h2 v (fun h => hv (h ▸ hp))⟩
  refine ⟨g * algebraMap (𝓞 F) F m, mul_ne_zero hg hm', fun w hw' => ?_, fun v hv => ?_⟩
  · rw [map_mul]
    exact (lt_div_iff₀ (hw w)).1 (h1 w hw')
  · rw [map_mul]
    exact mul_le_of_le_one_left' (h2 v hv)

theorem exists_small_adele (F : Type) [Field F] [NumberField F] (S₁ : Finset (InfinitePlace F))
    (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F) (hε : IsPlacesIdem S₁ S₂ ε)
    (hS : S₁.Nonempty ∨ S₂.Nonempty) (N : Set (AF F)) (hN : N ∈ 𝓝 (0 : AF F)) :
    ∃ f : F, f ≠ 0 ∧ (1 - ε) * algebraMap F (AF F) f ∈ N := by
  have hN' : N ∈ 𝓝 ((0 : Ainf F), (0 : Af F)) := hN
  obtain ⟨N₁, hN₁, N₂, hN₂, hsub⟩ := mem_nhds_prod_iff.1 hN'
  obtain ⟨δ, hδ, hδN⟩ := exists_delta_nhds_infinite F N₁ hN₁
  obtain ⟨m, hm, hmN⟩ := exists_int_nhds_finite F N₂ hN₂
  obtain ⟨g, hg, h1, h2⟩ := exists_small F S₁ S₂ hS m hm δ hδ
  refine ⟨g, hg, hsub ⟨?_, ?_⟩⟩
  · apply hδN
    intro w
    have e : ((1 - ε) * algebraMap F (AF F) g).1 w = (1 - fstA F ε w) * (algebraMap F (Ainf F) g) w := by
      change (fstA F ((1 - ε) * algebraMap F (AF F) g)) w = _
      rw [map_mul, map_sub, map_one, AlgHom.commutes]
      rfl
    rw [e]
    by_cases hw : w ∈ S₁
    · rw [hε.1 w hw, sub_self, zero_mul, norm_zero]; exact hδ
    · rw [hε.2.1 w hw, sub_zero, one_mul]
      have := GroundTheory.Global.norm_algebraMap_apply (K := F) g w
      exact this.trans_lt (h1 w hw)
  · apply hmN
    intro v
    have e : evalV F v ((1 - ε) * algebraMap F (AF F) g).2 =
        (1 - evalV F v (sndA F ε)) * (g : v.adicCompletion F) := by
      change evalV F v (sndA F ((1 - ε) * algebraMap F (AF F) g)) = _
      rw [map_mul, map_mul, map_sub, map_sub, map_one, map_one, AlgHom.commutes, AlgHom.commutes]
      rfl
    rw [e]
    by_cases hv : v ∈ S₂
    · rw [hε.2.2.1 v hv, sub_self, zero_mul, map_zero]; exact zero_le'
    · rw [hε.2.2.2 v hv, sub_zero, one_mul, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact h2 v hv

theorem exists_approx_notMem : ∀ (F : Type) [Field F] [NumberField F], ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ (x : AF F) (U : Set (AF F)), U ∈ 𝓝 x → ∀ Z : Finset F, ∃ t : F, t ∉ Z ∧ ∃ s : AF F, algebraMap F (AF F) t + ε * s ∈ U := by
  intro F _ _ S₁ S₂ ε hε hS x U hU Z
  have hc : Tendsto (fun p : AF F × AF F => x + (p.1 + p.2)) (𝓝 ((0 : AF F), (0 : AF F))) (𝓝 x) := by
    have : Continuous (fun p : AF F × AF F => x + (p.1 + p.2)) := by fun_prop
    simpa using this.tendsto ((0 : AF F), (0 : AF F))
  obtain ⟨V₁, hV₁, V₂, hV₂, hV⟩ := mem_nhds_prod_iff.1 (hc hU)
  obtain ⟨C, hC, hCF⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  have hM : ∀ᶠ a in 𝓝 (0 : AF F), ∀ c ∈ C, -(a * c) ∈ V₁ := by
    refine hC.eventually_forall_of_forall_eventually fun c _ => ?_
    have hcont : Continuous (fun p : AF F × AF F => -(p.1 * p.2)) := by fun_prop
    exact hcont.continuousAt.eventually_mem (by simpa using hV₁)
  obtain ⟨f, hf, hfM⟩ := exists_small_adele F S₁ S₂ ε hε hS _ hM
  obtain ⟨t₀, ht₀⟩ := hCF (algebraMap F (AF F) f⁻¹ * x)
  set c := algebraMap F (AF F) f⁻¹ * x - algebraMap F (AF F) t₀ with hc_def
  have hd₁ : -((1 - ε) * algebraMap F (AF F) f * c) ∈ V₁ := hfM c ht₀
  have hff : algebraMap F (AF F) f * algebraMap F (AF F) f⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hf, map_one]
  have e₁ : algebraMap F (AF F) (f * t₀) + ε * (algebraMap F (AF F) f * c) =
      x + -((1 - ε) * algebraMap F (AF F) f * c) := by
    rw [hc_def, map_mul]
    linear_combination x * hff

  set n := Z.card with hn
  have hM₂ : ∀ᶠ a in 𝓝 (0 : AF F), ∀ q ∈ Finset.range (n + 1), ((q : ℕ) : AF F) * a ∈ V₂ := by
    refine (Filter.eventually_all_finset _).2 fun q _ => ?_
    have hcont : Continuous (fun a : AF F => ((q : ℕ) : AF F) * a) := by fun_prop
    exact hcont.continuousAt.eventually_mem (by simpa using hV₂)
  obtain ⟨f₂, hf₂, hf₂M⟩ := exists_small_adele F S₁ S₂ ε hε hS _ hM₂
  obtain ⟨q, hq, hqZ⟩ : ∃ q ∈ Finset.range (n + 1), f * t₀ + (q : F) * f₂ ∉ Z := by
    by_contra hcon
    push_neg at hcon
    have hinj : Set.InjOn (fun q : ℕ => f * t₀ + (q : F) * f₂) (Finset.range (n + 1) : Set ℕ) := by
      intro a _ b _ hab
      have : (a : F) * f₂ = (b : F) * f₂ := add_left_cancel hab
      exact_mod_cast mul_right_cancel₀ hf₂ this
    have := Finset.card_le_card_of_injOn _ (fun a ha => hcon a ha) hinj
    simp [hn] at this
  refine ⟨f * t₀ + (q : F) * f₂, hqZ, algebraMap F (AF F) f * c - algebraMap F (AF F) ((q : F) * f₂), ?_⟩
  have e₂ : algebraMap F (AF F) (f * t₀ + (q : F) * f₂) +
      ε * (algebraMap F (AF F) f * c - algebraMap F (AF F) ((q : F) * f₂)) =
      x + (-((1 - ε) * algebraMap F (AF F) f * c) + ((q : ℕ) : AF F) * ((1 - ε) * algebraMap F (AF F) f₂)) := by
    rw [map_add (f := _), map_mul (algebraMap F (AF F)) (q : F) f₂, map_natCast]
    linear_combination e₁
  rw [e₂]
  exact hV (Set.mk_mem_prod hd₁ (hf₂M q hq))

end GlobalTheory.AddApproxPlaces

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveStrongApproximationAvoidingFinsetStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_strongApproximation_avoiding_finset : ∀ (F : Type) [Field F] [NumberField F], ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ (x : AF F) (U : Set (AF F)), U ∈ 𝓝 x → ∀ Z : Finset F, ∃ t : F, t ∉ Z ∧ ∃ s : AF F, algebraMap F (AF F) t + ε * s ∈ U := by
  first | exact @GlobalTheory.AddApproxPlaces.exists_approx_notMem | exact GlobalTheory.AddApproxPlaces.exists_approx_notMem | (intros; apply GlobalTheory.AddApproxPlaces.exists_approx_notMem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfSymmetric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassEqZeroOfSquareZeroRetraction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassEqZeroOfSquareZeroRetraction
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.CechPic

theorem squareZero_localUnit_difference_ring_identity {R : Type*} [CommRing R] {Tj Tk Nj Nk H G G' Sj Sk Pj Pk Pj' Pk' M : R}
    (hT : Tj = G' * Tk) (hS : Sj = G * G * Sk) (hP : Pj = G' * G' * Pk) (hj' : Pj * Pj' = 1)
    (hk' : Pk * Pk' = 1) (hNj : Nj = Sj * Pj' - 1) (hNk : Nk = Sk * Pk' - 1) (hNj2 : Nj * Nj = 0)
    (hNk2 : Nk * Nk = 0) (hH : 2 * H = 1)
    (hM : M = Tj * (1 + Nj * H) - G * (Tk * (1 + Nk * H))) (hM2 : M * M = 0) :
    M * (G * (Tk * (1 + Nk * H))) = 0 := by
  have e1 : (Tj * (1 + Nj * H)) ^ 2 = Tj ^ 2 * Sj * Pj' := by
    linear_combination Tj ^ 2 * Nj * hH + Tj ^ 2 * H ^ 2 * hNj2 + Tj ^ 2 * hNj
  have e2 : (G * (Tk * (1 + Nk * H))) ^ 2 = G ^ 2 * Tk ^ 2 * Sk * Pk' := by
    linear_combination G ^ 2 * Tk ^ 2 * Nk * hH + G ^ 2 * Tk ^ 2 * H ^ 2 * hNk2 + G ^ 2 * Tk ^ 2 * hNk
  have e4 : Pj' * (G' * G') = Pk' := by
    linear_combination (-(Pj' * (G' * G'))) * hk' + Pk' * hj' - Pk' * Pj' * hP
  have e5 : (Tj * (1 + Nj * H)) ^ 2 = (G * (Tk * (1 + Nk * H))) ^ 2 := by
    rw [e1, e2, hT, hS]
    linear_combination G ^ 2 * Tk ^ 2 * Sk * e4
  linear_combination H * e5 - H * hM2 +
    H * (Tj * (1 + Nj * H) + G * (Tk * (1 + Nk * H)) + M) * hM - M * (G * (Tk * (1 + Nk * H))) * hH

end GlobalTheory.CechPic


open GlobalTheory.SmallExtLift in
theorem GlobalTheory.CechPic.eq_zero_of_sqZero_retract : ∀ {X X' : Scheme.{0}} (i : X ⟶ X') (q : X' ⟶ X), i ≫ q = 𝟙 X → (∀ x, i (q x) = x) → IsUnit (2 : Γ(X', ⊤)) → (∀ (W : X'.Opens) (f g : Γ(X', W)), (i.app W).hom f = 0 → (i.app W).hom g = 0 → f * g = 0) → ∀ (c : GlobalTheory.CechPic.Pic X'), GlobalTheory.CechPic.pull i c = 0 → 2 • c = 0 → c = 0 := by
  intro X X' i q e hiq h2 hsq c hc hc2
  obtain ⟨Q, hQ, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  rw [two_nsmul, ← GlobalTheory.CechPic.cls_tens hQ hQ (GlobalTheory.CechPic.isLB_tens hQ hQ),
    GlobalTheory.CechPic.cls_eq_zero_iff] at hc2
  obtain ⟨s, hs⟩ := hc2
  rw [← GlobalTheory.CechPic.cls_pull hQ i (pull_isLB hQ i), GlobalTheory.CechPic.cls_eq_zero_iff] at hc
  obtain ⟨t₀, ht₀⟩ := hc
  refine (GlobalTheory.CechPic.cls_eq_zero_iff hQ).2 ?_

  have genLaw : ∀ {M : LB X'} (t : LB.Gen M), t.IsGen → ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z)
      (a b : M.ι) (ha : f z ∈ M.U a) (hb : f z ∈ M.U b),
      gr f z _ ha (t.s a).val = gr f z (M.U a ⊓ M.U b) ⟨ha, hb⟩ (M.g a b).val * gr f z _ hb (t.s b).val := by
    intro M t ht Z f z a b ha hb
    have hm : f z ∈ M.U a ⊓ M.U b := ⟨ha, hb⟩
    have := congrArg (fun u => gr f z _ hm u.val) (ht a b)
    simp only [Units.val_mul, map_mul] at this
    exact (gr_res f z _ hm _).symm.trans (this.trans (congrArg₂ (· * ·) rfl (gr_res f z _ hm _)))
  let W : Q.ι → X.Opens := fun j => (Q.pull i).U (fun _ => j)
  have hσ : ∀ j, Q.U j ≤ (q ≫ i) ⁻¹ᵁ Q.U j := fun j x hx => by
    simp only [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply, hiq]; exact hx
  have hW : ∀ j, Q.U j ≤ q ⁻¹ᵁ W j := fun j x hx => pull_le Q i j le_rfl (hσ j hx)
  have hσf : ∀ j {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z), f z ∈ Q.U j → ((f ≫ q) ≫ i) z ∈ Q.U j := by
    intro j Z f z hz
    simp only [Scheme.Hom.comp_apply, hiq]; exact hz
  have hWf : ∀ j {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z), f z ∈ Q.U j → (f ≫ q) z ∈ W j :=
    fun j Z f z hz => hW j hz
  let sj : ∀ j, Γ(X', Q.U j)ˣ := fun j => res (le_inf le_rfl le_rfl) (s.s (j, j))
  let u : ∀ j, Γ(X', Q.U j) := fun j => (q.appLE (W j) (Q.U j) (hW j)).hom (t₀.s fun _ => j).val
  let σi : ∀ j, Γ(X', Q.U j) := fun j => ((q ≫ i).appLE (Q.U j) (Q.U j) (hσ j)).hom (sj j)⁻¹.val
  let n : ∀ j, Γ(X', Q.U j) := fun j => (sj j).val * σi j - 1
  let hh : ∀ j, Γ(X', Q.U j) := fun j => (X'.presheaf.map (homOfLE le_top).op).hom h2.unit⁻¹.val
  let t : ∀ j, Γ(X', Q.U j) := fun j => u j * (1 + n j * hh j)
  have gn : ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z) j (hz : f z ∈ Q.U j),
      gr f z _ hz (n j) = gr f z _ hz (sj j).val * gr ((f ≫ q) ≫ i) z (Q.U j) (hσf j f z hz) (sj j)⁻¹.val - 1 := by
    intro Z f z j hz
    simp only [n, σi, map_sub, map_mul, map_one]
    rw [gr_appLE]
    exact congrArg (fun w => _ * w - 1) (gr_congr (Category.assoc f q i).symm z _ _ _)
  have gt : ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z) j (hz : f z ∈ Q.U j),
      gr f z _ hz (t j) = gr (f ≫ q) z (W j) (hWf j f z hz) (t₀.s fun _ => j).val *
        (1 + gr f z _ hz (n j) * gr f z ⊤ trivial h2.unit⁻¹.val) := by
    intro Z f z j hz
    simp only [t, u, hh, map_mul, map_add (f := _), map_one]
    rw [gr_appLE, gr_res]
  have E1 : (𝟙 X ≫ i) ≫ q = 𝟙 X := by rw [Category.assoc, e, Category.id_comp]
  have E2 : ((𝟙 X ≫ i) ≫ q) ≫ i = 𝟙 X ≫ i := by rw [E1]
  have hn0 : ∀ j, (i.app (Q.U j)).hom (n j) = 0 := fun j => gr_ext fun y hy => by
    rw [gr_app, map_zero, gn (𝟙 X ≫ i) y j hy, gr_congr E2 y _ (hσf j _ y hy), ← map_mul, Units.mul_inv,
      map_one, sub_self]
  have hn2 : ∀ j, n j * n j = 0 := fun j => hsq _ _ _ (hn0 j) (hn0 j)
  have gti : ∀ j y (hy : (𝟙 X ≫ i) y ∈ Q.U j),
      gr (𝟙 X ≫ i) y _ hy (t j) = gr ((𝟙 X ≫ i) ≫ q) y (W j) (hWf j _ y hy) (t₀.s fun _ => j).val := by
    intro j y hy
    rw [gt (𝟙 X ≫ i) y j hy, gn (𝟙 X ≫ i) y j hy, gr_congr E2 y _ (hσf j _ y hy), ← map_mul, Units.mul_inv, map_one, sub_self, zero_mul,
      add_zero, mul_one]
  let m : ∀ j k, Γ(X', Q.U j ⊓ Q.U k) := fun j k =>
    (X'.presheaf.map (homOfLE inf_le_left).op).hom (t j) -
      (Q.g j k).val * (X'.presheaf.map (homOfLE inf_le_right).op).hom (t k)
  have gm' : ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z) j k (hz : f z ∈ Q.U j ⊓ Q.U k),
      gr f z _ hz (m j k) = gr f z _ hz.1 (t j) - gr f z _ hz (Q.g j k).val * gr f z _ hz.2 (t k) := by
    intro Z f z j k hz
    simp only [m, map_sub, map_mul]
    rw [gr_res, gr_res]
  have hm0 : ∀ j k, (i.app _).hom (m j k) = 0 := fun j k => gr_ext fun y hy => by
    rw [gr_app, map_zero, gm' (𝟙 X ≫ i) y j k hy, gti j y hy.1, gti k y hy.2, sub_eq_zero]
    have := gr_gen ht₀ ((𝟙 X ≫ i) ≫ q) y (hσf j _ y hy.1) (hσf k _ y hy.2)
    exact this.trans (congrArg (· * _) (gr_congr E2 y _ _ _))
  have gS : ∀ {Z : Scheme.{0}} (f : Z ⟶ X') (z : Z) a b (ha : f z ∈ Q.U a) (hb : f z ∈ Q.U b),
      gr f z _ ha (sj a).val = gr f z (Q.U a ⊓ Q.U b) ⟨ha, hb⟩ (Q.g a b).val *
        gr f z (Q.U a ⊓ Q.U b) ⟨ha, hb⟩ (Q.g a b).val * gr f z _ hb (sj b).val := by
    intro Z f z a b ha hb
    have hS := genLaw s hs f z (a, a) (b, b) ⟨ha, ha⟩ ⟨hb, hb⟩
    have hm : f z ∈ (Q.U a ⊓ Q.U a) ⊓ (Q.U b ⊓ Q.U b) := ⟨⟨ha, ha⟩, ⟨hb, hb⟩⟩
    have hg : gr f z _ hm ((GlobalTheory.CechPic.tens Q Q).g (a, a) (b, b)).val =
        gr f z (Q.U a ⊓ Q.U b) ⟨ha, hb⟩ (Q.g a b).val * gr f z (Q.U a ⊓ Q.U b) ⟨ha, hb⟩ (Q.g a b).val := by
      show gr f z _ hm (res _ (Q.g a b) * res _ (Q.g a b)).val = _
      rw [Units.val_mul, map_mul]
      exact congrArg₂ (· * ·) (gr_res f z _ hm _) (gr_res f z _ hm _)
    refine (gr_res f z (le_inf le_rfl le_rfl : Q.U a ≤ Q.U a ⊓ Q.U a) ha (s.s (a, a)).val).trans (hS.trans ?_)
    exact congrArg₂ (· * ·) hg (gr_res f z (le_inf le_rfl le_rfl : Q.U b ≤ Q.U b ⊓ Q.U b) hb (s.s (b, b)).val).symm
  refine gen_of_refine hQ Q.U hQ.cover id (fun _ => le_rfl) t
    (fun j => ((Units.isUnit _).map _).mul (isUnit_one_add (hn2 j) _)) fun a b x ha hb => ?_
  have hab : (𝟙 X') x ∈ Q.U a ⊓ Q.U b := ⟨ha, hb⟩
  have hmx := gm' (𝟙 X') x a b hab
  have hm := hmx
  rw [gt (𝟙 X') x a ha, gt (𝟙 X') x b hb] at hm
  have hmm := congrArg (gr (𝟙 X') x _ hab) (hsq _ _ _ (hm0 a b) (hm0 a b))
  rw [map_mul, map_zero] at hmm
  have hT := gr_gen ht₀ (𝟙 X' ≫ q) x (hσf a _ x ha) (hσf b _ x hb)
  have hSx := gS (𝟙 X') x a b ha hb
  have hPx := gS ((𝟙 X' ≫ q) ≫ i) x a b (hσf a _ x ha) (hσf b _ x hb)
  have hj' : gr ((𝟙 X' ≫ q) ≫ i) x _ (hσf a _ x ha) (sj a).val * gr ((𝟙 X' ≫ q) ≫ i) x _ (hσf a _ x ha) (sj a)⁻¹.val = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hk' : gr ((𝟙 X' ≫ q) ≫ i) x _ (hσf b _ x hb) (sj b).val * gr ((𝟙 X' ≫ q) ≫ i) x _ (hσf b _ x hb) (sj b)⁻¹.val = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hNa := gn (𝟙 X') x a ha
  have hNb := gn (𝟙 X') x b hb
  have hNa2 := congrArg (gr (𝟙 X') x _ ha) (hn2 a)
  have hNb2 := congrArg (gr (𝟙 X') x _ hb) (hn2 b)
  rw [map_mul, map_zero] at hNa2 hNb2
  have hH : 2 * gr (𝟙 X') x ⊤ trivial h2.unit⁻¹.val = 1 := by
    have := congrArg (gr (𝟙 X') x ⊤ trivial) h2.val_inv_mul
    rw [map_mul, map_one, map_ofNat] at this
    linear_combination this
  have key := GlobalTheory.CechPic.squareZero_localUnit_difference_ring_identity hT hSx hPx hj' hk' hNa hNb hNa2 hNb2 hH hm hmm
  have hB := ((Units.isUnit (Q.g a b)).map (gr (𝟙 X') x (Q.U a ⊓ Q.U b) hab)).mul
    (((Units.isUnit (t₀.s fun _ => b)).map (gr (𝟙 X' ≫ q) x (W b) (hWf b _ x hb))).mul (isUnit_one_add hNb2 (gr (𝟙 X') x ⊤ trivial h2.unit⁻¹.val)))
  have h0 := hB.mul_left_eq_zero.1 key
  rw [hmx] at h0
  exact sub_eq_zero.1 h0
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassEqZeroOfSquareZeroRetractionStatement
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicardClass_eq_zero_of_squareZero_retraction : ∀ {X X' : Scheme.{0}} (i : X ⟶ X') (q : X' ⟶ X), i ≫ q = 𝟙 X → (∀ x, i (q x) = x) → IsUnit (2 : Γ(X', ⊤)) → (∀ (W : X'.Opens) (f g : Γ(X', W)), (i.app W).hom f = 0 → (i.app W).hom g = 0 → f * g = 0) → ∀ (c : GlobalTheory.CechPic.Pic X'), GlobalTheory.CechPic.pull i c = 0 → 2 • c = 0 → c = 0 := by
  first | exact @GlobalTheory.CechPic.eq_zero_of_sqZero_retract | exact GlobalTheory.CechPic.eq_zero_of_sqZero_retract | (intros; apply GlobalTheory.CechPic.eq_zero_of_sqZero_retract <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymFirstOrder
open GlobalTheory.CechPic

theorem lbIso_of_symmetric : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A']
    (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left),
    IsAbelianScheme A →
    IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i →
    IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → i ≫ q = 𝟙 _ →
    ∀ (L M : LB A'.left), L.IsLB → M.IsLB →
      LBIso (L.pull (GrpObj.inv : A' ⟶ A').left) L → LBIso (M.pull (GrpObj.inv : A' ⟶ A').left) M →
      LBIso (L.pull i) (M.pull i) → LBIso L M := by
  intro K _ _ A _ A' _ i q hA hi hq e L M hL hM hLs hMs hLM
  have hA' : IsAbelianScheme A' := by
    have := hA.comm
    have hcomm : IsCommMonObj A' := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hq.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hq.2 T x y (pushPt hq.1.w x) (pushPt hq.1.w y) rfl rfl,
        ← hq.2 T y x (pushPt hq.1.w y) (pushPt hq.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hcomm, MorphismProperty.of_isPullback (P := @Smooth) hq.1 hA.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hq.1 hA.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hq.1 hA.geomConnected⟩
  set c := cls L hL - cls M hM with hc
  have h0 : pull i c = 0 := by
    rw [hc, map_sub, ← cls_pull hL i (pull_isLB hL i), ← cls_pull hM i (pull_isLB hM i),
      (cls_eq_iff (pull_isLB hL i) (pull_isLB hM i)).2 hLM, sub_self]
  have hinv : pull (GrpObj.inv : A' ⟶ A').left c = c := by
    rw [hc, map_sub, ← cls_pull hL _ (pull_isLB hL _), ← cls_pull hM _ (pull_isLB hM _),
      (cls_eq_iff _ hL).2 hLs, (cls_eq_iff _ hM).2 hMs]
  have hlam := ConstTheta.lam_eq_zero GlobalTheory.laws_without_cohomology.1 hA' hi.1 c h0 (𝟙 A') (𝟙 A')⁻¹
  have einv : (𝟙 A')⁻¹ = (GrpObj.inv : A' ⟶ A') := by simp [Hom.inv_def]
  have hone : pull (1 : A' ⟶ A').left c = 0 := by
    rw [Hom.one_def, Over.comp_left, pull_comp]
    obtain ⟨Q, hQ, hQc⟩ := cls_surj (pull (η[A'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ A').left c)
    rw [← hQc, (cls_eq_zero_iff hQ).2 (LB.exists_isGen_of_isLocalRing hQ), map_zero]
  have htwo : 2 • c = 0 := by
    unfold lam at hlam
    rw [mul_inv_cancel, einv, hinv, hone, Over.id_left, pull_id] at hlam
    rw [two_nsmul, ← neg_eq_zero, neg_add]
    simpa [sub_eq_add_neg, add_assoc] using hlam

  have hsurj : Surjective i := by
    have : Surjective (GlobalTheory.DeRham.epsRed K) := ⟨fun x => by
      haveI := ConstTheta.subsingleton_sp (K := K)
      obtain ⟨t⟩ : Nonempty (Sp K) := inferInstance
      exact ⟨t, Subsingleton.elim _ _⟩⟩
    exact MorphismProperty.of_isPullback (P := @Surjective) hi.1.flip this
  have hiq : ∀ x, i (q x) = x := fun x => by
    obtain ⟨y, rfl⟩ := hsurj.surj x
    rw [← Scheme.Hom.comp_apply i q, e]; rfl
  have h2 : IsUnit (2 : Γ(A'.left, ⊤)) := by
    have u : IsUnit (2 : DualNumber K) := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [show TrivSqZeroExt.fst (2 : DualNumber K) = 2 from rfl]; exact isUnit_iff_ne_zero.2 two_ne_zero)
    have u' := (u.map (Scheme.ΓSpecIso (CommRingCat.of (DualNumber K))).inv.hom).map A'.hom.appTop.hom
    rwa [map_ofNat, map_ofNat] at u'
  have hsq : ∀ (W : A'.left.Opens) (f g : Γ(A'.left, W)), (i.app W).hom f = 0 → (i.app W).hom g = 0 → f * g = 0 := by
    refine SquareZero.mul_eq_zero_of_app_eq_zero (DualNumber K) K (TrivSqZeroExt.fstHom K K K).toRingHom
      TrivSqZeroExt.fst_surjective ?_ A'.left A.left A'.hom A.hom i hi.1
    rw [pow_two, eq_bot_iff, Ideal.mul_le]
    intro r hr s hs
    have hr' : r.fst = 0 := hr
    have hs' : s.fst = 0 := hs
    rw [Ideal.mem_bot]
    ext <;> simp [hr', hs']
  have hc0 := GlobalTheory.T.cechPicardClass_eq_zero_of_squareZero_retraction i q e hiq h2 hsq c h0 htwo
  exact (cls_eq_iff hL hM).1 (sub_eq_zero.1 hc0)

end GlobalTheory.SymFirstOrder
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H
open scoped BigOperators
open Classical

namespace GlobalTheory.BaseVacuum

def four : Fin 4 ≃ Fin 2 × Fin 2 := (finCongr (by norm_num)).trans finProdFinEquiv.symm

def posE (n n' : ℕ) : (Fin n' × Fin n) × Fin 4 ≃ Fin (n' * 2) × Fin (n * 2) :=
  ((Equiv.refl _).prodCongr four).trans
    ((Equiv.prodProdProdComm _ _ _ _).trans (finProdFinEquiv.prodCongr finProdFinEquiv))

abbrev Ix (D : D7) (n n' : ℕ) : Type := (Fin n' × Fin n) × (Fin 4 × D.what₂.Tau)

def blk (D : D7) {n n' : ℕ} (k : Fin n' × Fin n) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)) : Fin 4 × D.what₂.Tau → ℂ :=
  fun w => z w.2 (posE n n' (k, w.1)).1 (posE n n' (k, w.1)).2

def reix (D : D7) (n n' : ℕ) : TaylorLogMetric.VC D (n * 2) (n' * 2) ≃ₗ[ℂ] (Ix D n n' → ℂ) where
  toFun z p := blk D p.1 z p.2
  invFun y τ i j := y (((posE n n').symm (i, j)).1, (((posE n n').symm (i, j)).2, τ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv z := by
    funext τ i j
    simp [blk]
  right_inv y := by
    funext p
    simp [blk]

def gBig {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ) :
    (Ix D n n' → ℂ) ≃ₗ[ℂ] (Ix D n n' → ℂ) where
  toFun y p := B.gC (fun w => y (p.1, w)) p.2
  invFun y p := B.gC.symm (fun w => y (p.1, w)) p.2
  map_add' x y := by
    funext p
    show B.gC ((fun w => x (p.1, w)) + (fun w => y (p.1, w))) p.2 = _
    rw [map_add (f := _)]; rfl
  map_smul' c x := by
    funext p
    show B.gC (c • (fun w => x (p.1, w))) p.2 = _
    rw [map_smul]; rfl
  left_inv y := by
    funext p
    simp
  right_inv y := by
    funext p
    simp

def phi {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ) :
    TaylorLogMetric.VC D (n * 2) (n' * 2) ≃ₗ[ℂ] (Ix D n n' → ℂ) :=
  (reix D n n').trans (gBig B n n')

theorem phi_apply {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ)
    (z : TaylorLogMetric.VC D (n * 2) (n' * 2)) (p : Ix D n n') : phi B n n' z p = B.gC (blk D p.1 z) p.2 := rfl

def ixE (D : D7) (n n' : ℕ) : Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2)) ≃ Ix D n n' :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin]
    simp only [Fintype.card_prod, Fintype.card_fin, D.what₂.card_Tau, TaylorLogMetric.fF]
    ring)

def xv {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (w : Fin 4 × D.what₂.Tau) : Fin 4 → D.host.E :=
  B.γ₀.g.symm (Pi.single w 1)

def putB (D : D7) {n n' : ℕ} (k : Fin n' × Fin n) (x : Fin 4 → D.host.E) :
    Matrix (Fin (n' * 2)) (Fin (n * 2)) D.host.E :=
  fun i j => if ((posE n n').symm (i, j)).1 = k then x ((posE n n').symm (i, j)).2 else 0

def bas {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (n n' : ℕ) :
    Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2)) → Matrix (Fin (n' * 2)) (Fin (n * 2)) D.host.E :=
  fun j => putB D (ixE D n n' j).1 (xv B (ixE D n n' j).2)

def blkLat {ι m : Type} (Λ : AddSubgroup (m → ℂ)) : AddSubgroup (ι × m → ℂ) where
  carrier := {y | ∀ k, (fun w => y (k, w)) ∈ Λ}
  zero_mem' := fun _ => Λ.zero_mem
  add_mem' := fun hx hy k => Λ.add_mem (hx k) (hy k)
  neg_mem' := fun hx k => Λ.neg_mem (hx k)

end GlobalTheory.BaseVacuum
end
end
