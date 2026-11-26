module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.MeromorphicAtProd
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.SummablePrimesRpow
open NumberField IsDedekindDomain

namespace PositivityTheory.Lord

theorem dedekindZeta_eq_exp (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = Complex.exp (∑' P : HeightOneSpectrum (𝓞 K),
      -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  classical
  set X : Ideal (𝓞 K) → ℂ := fun I => if I = ⊥ then 0 else 1 with hX
  have h0 : X ⊥ = 0 := by simp [hX]
  have h1 : ∀ I, I ≠ ⊥ → X I = 1 := fun I hI => by simp only [hX, if_neg hI]
  have hmul : ∀ I J, X (I * J) = X I * X J := by
    intro I J
    by_cases hI : I = ⊥
    · subst hI
      rw [Ideal.bot_mul, h0, zero_mul]
    by_cases hJ : J = ⊥
    · subst hJ
      rw [Ideal.mul_bot, h0, mul_zero]
    rw [h1 I hI, h1 J hJ, h1 _ (fun h => (Ideal.mul_eq_bot.1 h).elim hI hJ), one_mul]
  have hle : ∀ I, ‖X I‖ ≤ 1 := by
    intro I
    by_cases hI : I = ⊥
    · subst hI
      rw [h0]; simp
    · rw [h1 I hI]; simp
  have h := GlobalTheory.tsum_ideal_mul_absNorm_cpow_eq_exp_tsum K X h0 (h1 _ top_ne_bot) hmul hle s hs
  have hs0 : -s ≠ 0 := by
    rintro h0
    rw [neg_eq_zero] at h0
    subst h0
    norm_num at hs
  have e1 : ∀ I : Ideal (𝓞 K), X I * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) =
      ((Ideal.absNorm I : ℕ) : ℂ) ^ (-s) := by
    intro I
    by_cases hI : I = ⊥
    · subst hI
      rw [h0, zero_mul, Ideal.absNorm_bot, Nat.cast_zero, Complex.zero_cpow hs0]
    · rw [h1 I hI, one_mul]
  have e2 : ∀ P : HeightOneSpectrum (𝓞 K), X P.asIdeal = 1 := fun P => h1 _ P.ne_bot
  simp only [e1, e2] at h
  rw [GlobalTheory.Mem.ZetaPole.dedekindZeta_eq_tsum_ideal K hs, h]

theorem two_le_absNorm' (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    2 ≤ Ideal.absNorm P.asIdeal := by
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := fun h =>
    P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

theorem summable_primes_rpow (K : Type) [Field K] [NumberField K] (σ : ℝ) (hσ : 1 < σ) :
    Summable fun P : HeightOneSpectrum (𝓞 K) => ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-σ) := by
  have h := GlobalTheory.Mem.summable_norm_absNorm_cpow K (s := (σ : ℂ)) (by simpa using hσ)
  have hinj : Function.Injective fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal :=
    fun P Q hPQ => HeightOneSpectrum.ext hPQ
  refine (h.comp_injective hinj).congr fun P => ?_
  have hpos : 0 < Ideal.absNorm P.asIdeal := by have := two_le_absNorm' K P; omega
  simp only [Function.comp_apply]
  rw [Complex.norm_natCast_cpow_of_pos hpos]
  simp

theorem zeta_euler (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun P : HeightOneSpectrum (𝓞 K) => 1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))
        (GroundTheory.Global.continuedDedekindZeta K s)⁻¹ ∧
      GroundTheory.Global.continuedDedekindZeta K s ≠ 0 := by
  have hE := ((GlobalTheory.eulerProduct_eq_exp_and_pos (HeightOneSpectrum (𝓞 K))
    (fun P => Ideal.absNorm P.asIdeal) (fun _ => 1) (two_le_absNorm' K) (fun _ => by simp)
    (summable_primes_rpow K)).1 s hs).2
  rw [← dedekindZeta_eq_exp K hs, ← GroundTheory.Global.continuedDedekindZeta_eq K hs] at hE
  have hne : GroundTheory.Global.continuedDedekindZeta K s ≠ 0 := by
    rw [GroundTheory.Global.continuedDedekindZeta_eq K hs, dedekindZeta_eq_exp K hs]
    exact Complex.exp_ne_zero _
  refine ⟨?_, hne⟩
  have := hE.inv₀ hne
  simpa using this

end PositivityTheory.Lord
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.ZetaEGrouped
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.NatCastPowCpow
open NumberField IsDedekindDomain

namespace PositivityTheory.Lord

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def badSet : Set (HeightOneSpectrum (𝓞 F)) :=
  {v | ¬ ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal}

theorem badSet_finite : (badSet F E).Finite := by
  classical
  let _ : Algebra (FractionRing (𝓞 F)) (FractionRing (𝓞 E)) := FractionRing.liftAlgebra _ _
  have hD : differentIdeal (𝓞 F) (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hW := Ideal.finite_factors (R := 𝓞 E) hD
  refine (hW.image (HeightOneSpectrum.under (𝓞 F))).subset ?_
  intro v hv
  simp only [badSet, Set.mem_ofPred_eq, not_forall] at hv
  obtain ⟨w, hwv, hw⟩ := hv
  refine ⟨w, ?_, ?_⟩
  · have := w.isPrime
    exact (dvd_differentIdeal_iff (P := w.asIdeal)).2 hw
  · ext1
    simp [hwv.over]

theorem fib_finite (v : HeightOneSpectrum (𝓞 F)) :
    {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.LiesOver v.asIdeal}.Finite := by
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).preimage
    (Set.injOn_of_injective (fun a b h => HeightOneSpectrum.ext h))).subset ?_
  intro P hP
  exact ⟨P.isPrime, hP⟩

noncomputable def fib (v : HeightOneSpectrum (𝓞 F)) : Finset (HeightOneSpectrum (𝓞 E)) :=
  (fib_finite F E v).toFinset

theorem mem_fib {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)} :
    P ∈ fib F E v ↔ P.asIdeal.LiesOver v.asIdeal := by
  simp [fib]

theorem natCast_pow_cpow (q f : ℕ) (s : ℂ) : ((q ^ f : ℕ) : ℂ) ^ s = ((q : ℂ) ^ s) ^ f := by
  induction f with
  | zero => simp
  | succ n ih =>
    have h := Complex.mul_cpow_ofReal_nonneg (a := ((q ^ n : ℕ) : ℝ)) (b := (q : ℝ)) (by positivity) (by positivity) s
    have e1 : ((q ^ (n + 1) : ℕ) : ℂ) = (((q ^ n : ℕ) : ℝ) : ℂ) * ((q : ℝ) : ℂ) := by
      push_cast; ring
    rw [e1, h, pow_succ, ← ih]
    simp only [Complex.ofReal_natCast]

private theorem inertiaDeg_eq_ramIdx_mul_of_ramIdx_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (p : Ideal (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (he : p.ramificationIdx' P.asIdeal = 1) :
    p.inertiaDeg' P.asIdeal = p.ramificationIdx' P.asIdeal * p.inertiaDeg' P.asIdeal := by
  rw [he, one_mul]

theorem local_factor (h2 : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ badSet F E) (s : ℂ) :
    ∏ P ∈ fib F E v, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) =
      (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) *
        (1 - PositivityTheory.SiegelWeilFormula.Gen.eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) := by
  classical
  set p := v.asIdeal with hpdef
  have hp0 : p ≠ ⊥ := v.ne_bot
  haveI hpm : p.IsMaximal := v.isMaximal
  have hmap0 : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hp0
  have hunr : ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver p →
      Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal := by
    simpa [badSet] using hv
  have hlies : ∀ P ∈ fib F E v, P.asIdeal.LiesOver p := fun P hP => (mem_fib F E).mp hP
  have hmapfib : (fib F E v).map ⟨HeightOneSpectrum.asIdeal, fun a b h => HeightOneSpectrum.ext h⟩ =
      IsDedekindDomain.primesOverFinset p (𝓞 E) := by
    ext Q
    rw [Finset.mem_map, IsDedekindDomain.mem_primesOverFinset_iff hp0]
    constructor
    · rintro ⟨P, hP, rfl⟩
      exact ⟨P.isPrime, (mem_fib F E).mp hP⟩
    · intro hQ
      have hQ0 : Q ≠ ⊥ := by
        intro h
        apply hp0
        rw [hQ.2.over, h]
        exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
      exact ⟨⟨Q, hQ.1, hQ0⟩, (mem_fib F E).mpr hQ.2, rfl⟩
  have hcard_eq : (IsDedekindDomain.primesOverFinset p (𝓞 E)).card = (fib F E v).card := by
    rw [← hmapfib, Finset.card_map]
  have he : ∀ P ∈ fib F E v, p.ramificationIdx' P.asIdeal = 1 := by
    intro P hP
    haveI := hlies P hP
    haveI := hunr P (hlies P hP)
    rw [Ideal.ramificationIdx'_eq_ramificationIdx' p P.asIdeal hmap0]
    exact Ideal.ramificationIdx_eq_one _ _
  have hsum : ∑ P ∈ fib F E v, p.inertiaDeg' P.asIdeal = 2 := by
    have h := Ideal.sum_ramification_inertia (𝓞 E) F E hp0
    rw [← hmapfib, Finset.sum_map] at h
    rw [← h2, ← h]
    refine Finset.sum_congr rfl fun P hP => ?_
    exact inertiaDeg_eq_ramIdx_mul_of_ramIdx_eq_one p P (he P hP)
  have hnorm : ∀ P ∈ fib F E v,
      Ideal.absNorm P.asIdeal = Ideal.absNorm p ^ p.inertiaDeg' P.asIdeal := by
    intro P hP
    haveI := hlies P hP
    exact Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal p hpm.isPrime hp0
  have hfpos : ∀ P ∈ fib F E v, 0 < p.inertiaDeg' P.asIdeal := by
    intro P hP
    haveI := hlies P hP
    exact Ideal.inertiaDeg'_pos p P.asIdeal
  have hcard_le : (fib F E v).card ≤ 2 := by
    rw [← hsum, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun P hP => hfpos P hP
  have hcard_pos : 0 < (fib F E v).card := by
    rw [Finset.card_pos]
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h] at hsum
    simp at hsum
  rcases (show (fib F E v).card = 1 ∨ (fib F E v).card = 2 by omega) with hc | hc
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have hamem : a ∈ fib F E v := by
      rw [ha]
      exact Finset.mem_singleton_self a
    have haf : p.inertiaDeg' a.asIdeal = 2 := by
      rw [ha, Finset.sum_singleton] at hsum
      exact hsum
    have hmapa : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p = a.asIdeal := by
      haveI := hlies a hamem
      have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) p ≤ a.asIdeal :=
        Ideal.map_le_of_le_comap (le_of_eq (Ideal.LiesOver.over))
      obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
      have hn := congrArg Ideal.absNorm hJ
      rw [Ideal.absNorm_algebraMap, map_mul, hnorm a hamem, haf,
        ← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E, h2] at hn
      have hNp : 0 < Ideal.absNorm p :=
        Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
      have hJ1 : Ideal.absNorm J = 1 := by
        have h' : Ideal.absNorm p ^ 2 * 1 = Ideal.absNorm p ^ 2 * Ideal.absNorm J := by
          rw [mul_one]
          exact hn
        exact (Nat.eq_of_mul_eq_mul_left (by positivity) h').symm
      rw [Ideal.absNorm_eq_one_iff.mp hJ1, Ideal.mul_top] at hJ
      exact hJ
    have hfield : IsField (TensorProduct F (HeightOneSpectrum.adicCompletion F v) E) :=
      GlobalTheory.InertField.isField_of_inert F E h2 v (by rw [hmapa]; exact a.isPrime)
    have heSp : PositivityTheory.SiegelWeilFormula.Gen.eSp E v = -1 := by
      unfold PositivityTheory.SiegelWeilFormula.Gen.eSp
      exact if_pos hfield
    rw [ha, Finset.prod_singleton, hnorm a hamem, haf, heSp, natCast_pow_cpow]
    ring
  · obtain ⟨a, b, hab, hfab⟩ := Finset.card_eq_two.mp hc
    have hamem : a ∈ fib F E v := by
      rw [hfab]
      simp
    have hbmem : b ∈ fib F E v := by
      rw [hfab]
      simp
    have hpa := hfpos a hamem
    have hpb := hfpos b hbmem
    rw [hfab, Finset.sum_pair hab] at hsum
    have ha1 : p.inertiaDeg' a.asIdeal = 1 := by omega
    have hb1 : p.inertiaDeg' b.asIdeal = 1 := by omega
    have hsplit : (p.primesOver (𝓞 E)).ncard = 2 := by
      rw [← IsDedekindDomain.coe_primesOverFinset hp0, Set.ncard_coe_finset, hcard_eq, hc]
    have hnf := GlobalTheory.SplitPlace.not_isField_of_split F E h2 v hsplit
    have heSp : PositivityTheory.SiegelWeilFormula.Gen.eSp E v = 1 := by
      unfold PositivityTheory.SiegelWeilFormula.Gen.eSp
      exact if_neg hnf
    rw [hfab, Finset.prod_pair hab, hnorm a hamem, hnorm b hbmem, ha1, hb1, heSp, pow_one]
    ring

end PositivityTheory.Lord
end

open NumberField IsDedekindDomain

namespace PositivityTheory.Lord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem zetaE_grouped {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => ∏ P ∈ fib F E v, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)))
      (GroundTheory.Global.continuedDedekindZeta E s)⁻¹ := by
  classical
  have hex : ∀ P : HeightOneSpectrum (𝓞 E), ∃ v : HeightOneSpectrum (𝓞 F), P ∈ fib F E v := by
    intro P
    refine ⟨⟨P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)), inferInstance, ?_⟩, ?_⟩
    · intro h
      exact P.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)
    · rw [mem_fib]
      exact ⟨rfl⟩
  have huniq : ∀ (P : HeightOneSpectrum (𝓞 E)) (v w : HeightOneSpectrum (𝓞 F)),
      P ∈ fib F E v → P ∈ fib F E w → v = w := by
    intro P v w hv hw
    rw [mem_fib] at hv hw
    apply HeightOneSpectrum.ext
    rw [hv.over, hw.over]
  choose π hπ using hex
  let e : (Σ v : HeightOneSpectrum (𝓞 F), {P // P ∈ fib F E v}) ≃ HeightOneSpectrum (𝓞 E) :=
    { toFun := fun x => x.2.1
      invFun := fun P => ⟨π P, ⟨P, hπ P⟩⟩
      left_inv := by
        rintro ⟨v, P, hP⟩
        exact Sigma.subtype_ext (huniq P _ _ (hπ P) hP) rfl
      right_inv := fun P => rfl }
  obtain ⟨h, -⟩ := zeta_euler E hs
  have h' := (e.hasProd_iff).2 h
  exact h'.sigma (fun v => Finset.hasProd (fib F E v) _)

end PositivityTheory.Lord
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.NormESpZpow
open NumberField InfinitePlace IsDedekindDomain HeckeCharacterZeroLocus.SiegelWeilU

namespace PositivityTheory.Lord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cm_places {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    nrRealPlaces F = Module.finrank ℚ F ∧ nrComplexPlaces F = 0 ∧ nrRealPlaces E = 0 ∧
      nrComplexPlaces E = Module.finrank ℚ F := by
  obtain ⟨hF, hE, h2, -⟩ := h
  have hcF : nrComplexPlaces F = 0 := IsTotallyReal.nrComplexPlaces_eq_zero F
  have hrE : nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  have kF := card_add_two_mul_card_eq_rank F
  have kE := card_add_two_mul_card_eq_rank E
  have ht := Module.finrank_mul_finrank ℚ F E
  rw [h2] at ht
  refine ⟨by omega, hcF, hrE, by omega⟩

theorem eSp_zpow (v : HeightOneSpectrum (𝓞 F)) (j : ℤ) :
    PositivityTheory.SiegelWeilFormula.Gen.eSp E v ^ j = if Even j then 1 else PositivityTheory.SiegelWeilFormula.Gen.eSp E v := by
  unfold PositivityTheory.SiegelWeilFormula.Gen.eSp
  split_ifs with h1 h2 h2
  · exact h2.neg_one_zpow
  · exact (Int.not_even_iff_odd.1 h2).neg_one_zpow
  · exact one_zpow j
  · exact one_zpow j

end PositivityTheory.Lord
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.ZetaOrd
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.InvGammaRZo
open Filter Topology Complex
open scoped Real

namespace PositivityTheory.Lord

theorem invGamma_zo (n : ℕ) : ZO (fun z => (Complex.Gamma z)⁻¹) (-(n : ℂ)) 1 := by
  induction n with
  | zero =>
    refine ⟨fun z => (Complex.Gamma (z + 1))⁻¹, ?_, ?_, ?_⟩
    · have hd : Differentiable ℂ fun z : ℂ => (Complex.Gamma (z + 1))⁻¹ := by
        intro z
        have h := (Complex.differentiable_one_div_Gamma (z + 1)).comp z (differentiableAt_id.add_const (1 : ℂ))
        exact h.congr_of_eventuallyEq (Eventually.of_forall fun w => by simp)
      exact hd.analyticAt _
    · simp
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hz0 : z ≠ 0 := by simpa using hz
      rw [Complex.Gamma_add_one z hz0, mul_inv, ← mul_assoc]
      simp [hz0]
  | succ n ih =>
    obtain ⟨u, hu, hu0, he⟩ := ih
    have hx : (-((n + 1 : ℕ) : ℂ)) + 1 = -(n : ℂ) := by push_cast; ring
    refine ⟨fun z => z * u (z + 1), ?_, ?_, ?_⟩
    · have h1 : AnalyticAt ℂ (fun z : ℂ => z + 1) (-((n + 1 : ℕ) : ℂ)) :=
        analyticAt_id.add analyticAt_const
      exact analyticAt_id.mul (hu.comp_of_eq h1 hx)
    · simp only [hx]
      refine mul_ne_zero ?_ hu0
      rw [neg_ne_zero]
      exact_mod_cast Nat.succ_ne_zero n
    · have ht : Tendsto (fun z : ℂ => z + 1) (𝓝[≠] (-((n + 1 : ℕ) : ℂ))) (𝓝[≠] (-(n : ℂ))) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have hc : Continuous fun z : ℂ => z + 1 := continuous_id.add continuous_const
          have := (hc.tendsto (-((n + 1 : ℕ) : ℂ))).mono_left (nhdsWithin_le_nhds (s := {(-((n + 1 : ℕ) : ℂ))}ᶜ))
          simpa only [hx] using this
        · filter_upwards [self_mem_nhdsWithin] with z hz
          intro h
          apply hz
          have : z = -(n : ℂ) - 1 := by rw [← h]; ring
          rw [Set.mem_singleton_iff, this]; push_cast; ring
      have h0 : ∀ᶠ z in 𝓝[≠] (-((n + 1 : ℕ) : ℂ)), z ≠ 0 := by
        refine eventually_nhdsWithin_of_eventually_nhds (isOpen_compl_singleton.mem_nhds ?_)
        rw [Set.mem_compl_singleton_iff, neg_ne_zero]
        exact_mod_cast Nat.succ_ne_zero n
      filter_upwards [ht.eventually he, h0] with z h1 h2
      have hg : (Complex.Gamma z)⁻¹ = z * (Complex.Gamma (z + 1))⁻¹ := by
        rw [Complex.Gamma_add_one z h2, mul_inv, ← mul_assoc, mul_inv_cancel₀ h2, one_mul]
      rw [hg, h1]
      push_cast
      ring

theorem invGammaR_zo (j : ℤ) (hj : j ≤ 0) :
    ZO (fun s => (Gammaℝ s)⁻¹) (j : ℂ) (if Even j then 1 else 0) := by
  split_ifs with he
  · obtain ⟨m, hm⟩ := he
    obtain ⟨n, hn⟩ : ∃ n : ℕ, m = -(n : ℤ) := ⟨m.natAbs, by omega⟩
    obtain ⟨u, hu, hu0, hue⟩ := invGamma_zo n
    have hjn : (j : ℂ) = -(2 * (n : ℂ)) := by rw [hm, hn]; push_cast; ring
    have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    refine ⟨fun s => ((π : ℂ) ^ (-s / 2))⁻¹ * u (s / 2) / 2, ?_, ?_, ?_⟩
    · have h1 : AnalyticAt ℂ (fun s : ℂ => ((π : ℂ) ^ (-s / 2))⁻¹) (j : ℂ) := by
        have hd : Differentiable ℂ fun s : ℂ => (π : ℂ) ^ (-s / 2) :=
          fun s => ((differentiableAt_id.neg).div_const 2).const_cpow (Or.inl hpi)
        exact (hd.analyticAt _).inv (by rw [Ne, cpow_eq_zero_iff]; tauto)
      have h2 : AnalyticAt ℂ (fun s : ℂ => u (s / 2)) (j : ℂ) := by
        have hc : AnalyticAt ℂ (fun s : ℂ => s / 2) (j : ℂ) := analyticAt_id.div_const
        exact hu.comp_of_eq hc (by rw [hjn]; ring)
      exact (h1.mul h2).div_const
    · simp only
      have : (j : ℂ) / 2 = -(n : ℂ) := by rw [hjn]; ring
      rw [this]
      refine div_ne_zero (mul_ne_zero (inv_ne_zero ?_) hu0) two_ne_zero
      rw [Ne, cpow_eq_zero_iff]; tauto
    · have ht : Tendsto (fun s : ℂ => s / 2) (𝓝[≠] (j : ℂ)) (𝓝[≠] (-(n : ℂ))) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have hc : Continuous fun s : ℂ => s / 2 := continuous_id.div_const 2
          have := (hc.tendsto (j : ℂ)).mono_left (nhdsWithin_le_nhds (s := {(j : ℂ)}ᶜ))
          have e : (j : ℂ) / 2 = -(n : ℂ) := by rw [hjn]; ring
          simpa only [e] using this
        · filter_upwards [self_mem_nhdsWithin] with s hs
          intro h
          apply hs
          have : s = 2 * (-(n : ℂ)) := by rw [← h]; ring
          rw [Set.mem_singleton_iff, this, hjn]; ring
      filter_upwards [ht.eventually hue] with s h1
      rw [Gammaℝ_def, mul_inv, h1, hjn]
      ring
  · have hd : Differentiable ℂ fun s => (Gammaℝ s)⁻¹ := differentiable_Gammaℝ_inv
    refine ⟨fun s => (Gammaℝ s)⁻¹, hd.analyticAt _, inv_ne_zero fun h => he ?_,
      Eventually.of_forall fun s => by simp⟩
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.1 h
    refine ⟨-(n : ℤ), ?_⟩
    have : ((j : ℤ) : ℂ) = ((-(n : ℤ) + -(n : ℤ) : ℤ) : ℂ) := by rw [hn]; push_cast; ring
    exact_mod_cast this

theorem invGammaC_zo (j : ℤ) (hj : j ≤ 0) : ZO (fun s => (Gammaℂ s)⁻¹) (j : ℂ) 1 := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨j.natAbs, by omega⟩
  obtain ⟨u, hu, hu0, hue⟩ := invGamma_zo n
  have hjn : (j : ℂ) = -(n : ℂ) := by rw [hn]; push_cast; ring
  have h2pi : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)
  refine ⟨fun s => (2 * (2 * (π : ℂ)) ^ (-s))⁻¹ * u s, ?_, ?_, ?_⟩
  · have hd : Differentiable ℂ fun s : ℂ => 2 * (2 * (π : ℂ)) ^ (-s) :=
      fun s => (differentiableAt_id.neg.const_cpow (Or.inl h2pi)).const_mul 2
    refine ((hd.analyticAt _).inv ?_).mul (by rw [hjn]; exact hu)
    exact mul_ne_zero two_ne_zero (by rw [Ne, cpow_eq_zero_iff]; tauto)
  · simp only
    rw [hjn]
    refine mul_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero ?_)) hu0
    rw [Ne, cpow_eq_zero_iff]; tauto
  · rw [hjn]
    filter_upwards [hue] with s h1
    rw [Gammaℂ_def, mul_inv, h1]
    ring

end PositivityTheory.Lord
end

open Filter Topology Complex NumberField InfinitePlace
open scoped Real

namespace PositivityTheory.Lord

open GroundTheory.Global

theorem zeta_analyticAt (K : Type) [Field K] [NumberField K] {x : ℂ} (hx : x ≠ 1) :
    AnalyticAt ℂ (continuedDedekindZeta K) x :=
  (differentiableOn_continuedDedekindZeta K).analyticAt (isOpen_compl_singleton.mem_nhds hx)

theorem zeta_pole (K : Type) [Field K] [NumberField K] :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A 1 ∧ A 1 ≠ 0 ∧
      ∀ᶠ s in 𝓝[≠] (1 : ℂ), (s - 1) * continuedDedekindZeta K s = A s := by
  refine ⟨Function.update (fun s => (s - 1) * continuedDedekindZeta K s) 1 (dedekindZeta_residue K : ℂ),
    (differentiable_sub_one_mul_continuedDedekindZeta K).analyticAt 1, ?_, ?_⟩
  · rw [Function.update_apply, if_pos rfl]
    exact Complex.ofReal_ne_zero.mpr (dedekindZeta_residue_ne_zero K)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Function.update_apply, if_neg (show s ≠ 1 from hs)]

theorem completed_zeta_continued_eq (K : Type) [Field K] [NumberField K] {s : ℂ} (hs0 : s ≠ 0) :
    continuedDedekindZeta K s = ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2)) *
      ((Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K) * completedDedekindZeta K s := by
  rw [continuedDedekindZeta_of_ne_zero K hs0, normalizedDedekindZeta, mul_inv, inv_pow, inv_pow]

theorem discr_cpow_analytic (K : Type) [Field K] [NumberField K] (x : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2))) x ∧
      ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(x / 2)) ≠ 0 := by
  have hpos : (0 : ℝ) < |(discr K : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  refine ⟨AnalyticAt.cpow analyticAt_const (by fun_prop) (Complex.ofReal_mem_slitPlane.mpr hpos), ?_⟩
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => (Complex.ofReal_ne_zero.mpr hpos.ne') h.1

theorem gammaInv_zo (K : Type) [Field K] [NumberField K] (j : ℤ) (hj : j ≤ 0) :
    ZO (fun s => (Gammaℝ s)⁻¹ ^ nrRealPlaces K * (Gammaℂ s)⁻¹ ^ nrComplexPlaces K) (j : ℂ)
      ((if Even j then 1 else 0) * nrRealPlaces K + 1 * nrComplexPlaces K) :=
  ((invGammaR_zo j hj).pow _).mul ((invGammaC_zo j hj).pow _)

theorem one_le_places (K : Type) [Field K] [NumberField K] : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
  have h := card_add_two_mul_card_eq_rank K
  have h1 : 0 < Module.finrank ℚ K := Module.finrank_pos
  omega

theorem zeta_zo_nonpos (K : Type) [Field K] [NumberField K] (j : ℤ) (hj : j ≤ 0) :
    ZO (continuedDedekindZeta K) (j : ℂ)
      (nrRealPlaces K * (if Even j then 1 else 0) + nrComplexPlaces K - (if j = 0 then 1 else 0)) := by
  have hG := gammaInv_zo K j hj
  rcases hj.lt_or_eq with hlt | rfl
  · have hb := discr_cpow_analytic K (j : ℂ)
    have hne : j ≠ 0 := hlt.ne
    have hj0 : (j : ℂ) ≠ 0 := by exact_mod_cast hne
    have hj1 : (j : ℂ) ≠ 1 := by
      intro h
      have : j = 1 := by exact_mod_cast h
      omega
    have hΛa : AnalyticAt ℂ (completedDedekindZeta K) (j : ℂ) := by
      refine DifferentiableOn.analyticAt (s := {0}ᶜ ∩ {1}ᶜ) (fun z hz => ?_)
        ((isOpen_compl_singleton.inter isOpen_compl_singleton).mem_nhds ⟨hj0, hj1⟩)
      exact (differentiableAt_completedDedekindZeta K hz.1 hz.2).differentiableWithinAt
    have hΛ0 : completedDedekindZeta K (j : ℂ) ≠ 0 := by
      intro h0
      have hre : 1 < (1 - (j : ℂ)).re := by
        have : (j : ℝ) < 0 := by exact_mod_cast hlt
        simp only [Complex.sub_re, Complex.one_re, Complex.intCast_re]
        linarith
      have hs1 : (1 - (j : ℂ)) ≠ 0 := by
        intro h
        rw [h, Complex.zero_re] at hre
        exact absurd hre (by norm_num)
      have e1 := completedDedekindZeta_one_sub K hj0 hj1
      have e2 := completed_zeta_continued_eq K hs1
      rw [e1, h0, mul_zero] at e2
      exact (zeta_euler K hre).2 e2
    have Z := ((ZO.of_analytic hb.1 hb.2).mul hG).mul (ZO.of_analytic hΛa hΛ0)
    have hord : nrRealPlaces K * (if Even j then 1 else 0) + nrComplexPlaces K - (if j = 0 then 1 else 0)
        = 0 + ((if Even j then 1 else 0) * nrRealPlaces K + 1 * nrComplexPlaces K) + 0 := by
      rw [if_neg hne, Nat.sub_zero]
      ring
    rw [hord]
    refine Z.congr ?_
    filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hj0)] with s hs
    exact (completed_zeta_continued_eq K hs).symm
  · have he : Even (0 : ℤ) := ⟨0, rfl⟩
    simp only [Int.cast_zero, he, ↓reduceIte, one_mul, mul_one] at hG ⊢
    have hm : 1 ≤ nrRealPlaces K + nrComplexPlaces K := one_le_places K
    obtain ⟨k, hk⟩ : ∃ k, nrRealPlaces K + nrComplexPlaces K = k + 1 :=
      ⟨_, (Nat.sub_add_cancel hm).symm⟩
    rw [hk] at hG
    rw [hk, Nat.add_sub_cancel]
    have hb0 := discr_cpow_analytic K 0
    obtain ⟨L, hT, hL0⟩ : ∃ L : ℂ, Tendsto (fun s => s * completedDedekindZeta K s) (𝓝[≠] 0) (𝓝 L) ∧ L ≠ 0 := by
      refine ⟨_, tendsto_mul_completedDedekindZeta_zero K, ?_⟩
      have h1 : (0 : ℝ) < √|(discr K : ℝ)| * dedekindZeta_residue K :=
        mul_pos (Real.sqrt_pos.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))))
          (dedekindZeta_residue_pos K)
      exact neg_ne_zero.mpr (mul_ne_zero (Complex.ofReal_ne_zero.mpr h1.ne')
        (inv_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))))
    set F : ℂ → ℂ := Function.update (fun s => s * completedDedekindZeta K s) 0 L with hFdef
    have hFa : AnalyticAt ℂ F 0 := by
      apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      · filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds (zero_ne_one : (0 : ℂ) ≠ 1))] with z hz0 hz1
        have hd : DifferentiableAt ℂ (fun s => s * completedDedekindZeta K s) z :=
          differentiableAt_id.mul (differentiableAt_completedDedekindZeta K hz0 hz1)
        refine hd.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_compl_singleton.mem_nhds hz0] with w hw
        rw [hFdef, Function.update_apply, if_neg (show w ≠ 0 from hw)]
      · rw [hFdef]
        exact continuousAt_update_same.mpr hT
    unfold ZO at hG ⊢
    obtain ⟨u, hu, hu0, hGu⟩ := hG
    refine ⟨fun s => ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (-(s / 2)) * u s * F s, (hb0.1.mul hu).mul hFa, ?_, ?_⟩
    · refine mul_ne_zero (mul_ne_zero hb0.2 hu0) ?_
      rw [hFdef, Function.update_apply, if_pos rfl]
      exact hL0
    · filter_upwards [self_mem_nhdsWithin, hGu] with s hs hGs
      beta_reduce at hGs
      rw [completed_zeta_continued_eq K hs, hGs]
      have hFs : F s = s * completedDedekindZeta K s := by
        rw [hFdef, Function.update_apply, if_neg (show s ≠ 0 from hs)]
      rw [hFs, pow_succ]
      ring

end PositivityTheory.Lord
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.FactorDifferentiable
open Filter Topology Complex NumberField IsDedekindDomain

namespace PositivityTheory.Lord

theorem factor_differentiable (N : ℕ) (hN : N ≠ 0) (c : ℂ) :
    Differentiable ℂ (fun s : ℂ => 1 - c * (N : ℂ) ^ (-s)) := by
  intro s
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  exact (differentiableAt_const _).sub
    ((differentiableAt_const _).mul (differentiableAt_id.neg.const_cpow (Or.inl hN')))

theorem factor_analytic (N : ℕ) (hN : N ≠ 0) (c x : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => 1 - c * (N : ℂ) ^ (-s)) x :=
  (PositivityTheory.Lord.factor_differentiable N hN c).analyticAt x

theorem factor_ne_zero (N : ℕ) (hN : 2 ≤ N) (c s : ℂ) (hc : ‖c‖ ≤ 1) (hs : 0 < s.re) :
    1 - c * (N : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have hpos : 0 < N := by omega
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlt : ‖(N : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hN1 (neg_neg_of_pos hs)
  have h1 : c * (N : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖c * (N : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖c‖ * ‖(N : ℂ) ^ (-s)‖ ≤ 1 * ‖(N : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ < 1 := by rwa [one_mul]
  rw [h1, norm_one] at hn
  exact lt_irrefl _ hn

theorem factor_ne_zero_int (N : ℕ) (hN : 2 ≤ N) (c : ℂ) (hc : ‖c‖ = 1) (j : ℤ) (hj : j ≠ 0) :
    1 - c * (N : ℂ) ^ (-(j : ℂ)) ≠ 0 := by
  intro h
  have hpos : 0 < N := by omega
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have h1 : c * (N : ℂ) ^ (-(j : ℂ)) = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖c * (N : ℂ) ^ (-(j : ℂ))‖ = ‖(1 : ℂ)‖ := by rw [h1]
  rw [norm_mul, hc, one_mul, norm_one, Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re,
    Complex.intCast_re] at hn
  rcases lt_or_gt_of_ne hj with hj' | hj'
  · have hjr : (j : ℝ) < 0 := by exact_mod_cast hj'
    have : (1 : ℝ) < (N : ℝ) ^ (-(j : ℝ)) := Real.one_lt_rpow hN1 (by linarith)
    linarith
  · have hjr : (0 : ℝ) < j := by exact_mod_cast hj'
    have : (N : ℝ) ^ (-(j : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hN1 (by linarith)
    linarith

theorem factor_zo (N : ℕ) (hN : 2 ≤ N) (c : ℂ) (hc : ‖c‖ = 1) (j : ℤ) (hj : j ≠ 0) :
    ZO (fun s : ℂ => 1 - c * (N : ℂ) ^ (-s)) (j : ℂ) 0 :=
  PositivityTheory.Lord.ZO.of_analytic (PositivityTheory.Lord.factor_analytic N (by omega) c _)
    (PositivityTheory.Lord.factor_ne_zero_int N hN c hc j hj)

theorem factor_zo_zero (N : ℕ) (hN : 2 ≤ N) : ZO (fun s : ℂ => 1 - (N : ℂ) ^ (-s)) 0 1 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have han : AnalyticAt ℂ (fun s : ℂ => 1 - (N : ℂ) ^ (-s)) 0 := by
    simpa only [one_mul] using PositivityTheory.Lord.factor_analytic N (by omega) 1 0
  have hd : HasDerivAt (fun s : ℂ => 1 - (N : ℂ) ^ (-s))
      (-((N : ℂ) ^ (-(0 : ℂ)) * Complex.log N * (-1))) 0 :=
    (((hasDerivAt_id (0 : ℂ)).neg).const_cpow (Or.inl hN')).const_sub 1
  refine PositivityTheory.Lord.ZO.one_of_deriv han ?_ ?_
  · show 1 - (N : ℂ) ^ (-(0 : ℂ)) = 0
    rw [neg_zero, Complex.cpow_zero, sub_self]
  · rw [hd.deriv, neg_zero, Complex.cpow_zero, one_mul, mul_neg_one, neg_neg]
    intro hlog
    have h1 : (N : ℂ) = 1 := by rw [← Complex.exp_log hN', hlog, Complex.exp_zero]
    have : N = 1 := by exact_mod_cast h1
    omega

theorem two_le_absNorm (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K)) :
    2 ≤ Ideal.absNorm P.asIdeal := by
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.ne_bot
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact P.isPrime.ne_top
  omega

end PositivityTheory.Lord
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.FinMod
namespace PositivityTheory.Lord

theorem hasProd_compl_finset {ι : Type*} [DecidableEq ι] (f g : ι → ℂ) (a : ℂ) (T S : Finset ι) (hST : S ⊆ T)
    (hg : HasProd g a) (hg0 : ∀ v ∈ T, g v ≠ 0) (hfg : ∀ v, v ∉ T → f v = g v) :
    HasProd (fun v : {v // v ∉ S} => f v) (a * (∏ v ∈ T, (g v)⁻¹) * ∏ v ∈ T \ S, f v) := by
  let F : ι → ℂ := Set.mulIndicator {v | v ∉ S} f
  let k : ι → ℂ := fun v => if v ∈ T then (g v)⁻¹ * F v else 1
  have hkT : HasProd k (∏ v ∈ T, k v) :=
    hasProd_prod_of_ne_finset_one (fun v hv => if_neg hv)
  have hgk : ∀ v, g v * k v = F v := by
    intro v
    by_cases hv : v ∈ T
    · show g v * (if v ∈ T then (g v)⁻¹ * F v else 1) = F v
      rw [if_pos hv, ← mul_assoc, mul_inv_cancel₀ (hg0 v hv), one_mul]
    · have hvS : v ∉ S := fun h => hv (hST h)
      show g v * (if v ∈ T then (g v)⁻¹ * F v else 1) = Set.mulIndicator {v | v ∉ S} f v
      rw [if_neg hv, mul_one, Set.mulIndicator_of_mem (show v ∈ {v | v ∉ S} from hvS), hfg v hv]
  have hFT : ∏ v ∈ T, F v = ∏ v ∈ T \ S, f v := by
    rw [Finset.sdiff_eq_filter, Finset.prod_filter]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    by_cases hvS : v ∈ S
    · rw [if_neg (not_not.2 hvS)]
      exact Set.mulIndicator_of_notMem (show v ∉ {v | v ∉ S} from not_not.2 hvS) f
    · rw [if_pos hvS]
      exact Set.mulIndicator_of_mem (show v ∈ {v | v ∉ S} from hvS) f
  have hkprod : ∏ v ∈ T, k v = (∏ v ∈ T, (g v)⁻¹) * ∏ v ∈ T \ S, f v := by
    rw [← hFT, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun v hv => if_pos hv)
  have hF : HasProd F (a * (∏ v ∈ T, (g v)⁻¹) * ∏ v ∈ T \ S, f v) := by
    have h := hg.mul hkT
    rw [hkprod, ← mul_assoc] at h
    convert h using 1
    funext v
    exact (hgk v).symm
  exact (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ S})).2 hF

end PositivityTheory.Lord
end

open NumberField InfinitePlace IsDedekindDomain Filter Topology HeckeCharacterZeroLocus.SiegelWeilU
open GroundTheory.Global (continuedDedekindZeta meromorphicOn_continuedDedekindZeta)
open PositivityTheory.SiegelWeilFormula.Gen (eSp LOrd)

namespace PositivityTheory.Lord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem zeta_inv_po_of_one_lt (K : Type) [Field K] [NumberField K] {x : ℂ} (hx : 1 < x.re) :
    PO (fun s => (continuedDedekindZeta K s)⁻¹) x 0 := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  exact PO.of_analytic ((zeta_analyticAt K hx1).inv (zeta_euler K hx).2)

theorem factorF_zo (v : HeightOneSpectrum (𝓞 F)) (j : ℤ) :
    ZO (fun s : ℂ => 1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) (j : ℂ) (if j = 0 then 1 else 0) := by
  have hN := two_le_absNorm F v
  by_cases hj : j = 0
  · subst hj
    simpa using factor_zo_zero _ hN
  · rw [if_neg hj]
    simpa using factor_zo _ hN 1 (by simp) j hj

theorem lOrd_even (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (S : Finset (HeightOneSpectrum (𝓞 F))) (j : ℤ)
    (hj : Even j) :
    ∃ Z : ℂ → ℂ, MeromorphicOn Z Set.univ ∧
      (∀ s : ℂ, 1 < s.re → HasProd (fun v : {v // v ∉ S} =>
        1 - eSp E v.1 ^ j * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)) (Z s)) ∧
      PO Z (j : ℂ) (if 1 ≤ j then 0 else if j = 0 then S.card + Module.finrank ℚ F - 1
        else Module.finrank ℚ F) := by
  classical
  obtain ⟨hFr, hFc, -, -⟩ := cm_places h
  have hfac : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : ℂ),
      AnalyticAt ℂ (fun s : ℂ => 1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) x := fun v x => by
    simpa using factor_analytic _ (by have := two_le_absNorm F v; omega) 1 x
  refine ⟨fun s => (continuedDedekindZeta F s)⁻¹ *
    ∏ v ∈ S, (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹, ?_, ?_, ?_⟩
  · intro x _
    exact ((meromorphicOn_continuedDedekindZeta F x trivial).inv).mul
      (meromorphicAt_prod S _ fun v _ => (hfac v x).meromorphicAt.inv)
  · intro s hs
    have hs0 : 0 < s.re := by linarith
    have key := hasProd_compl_finset (fun v => 1 - eSp E v ^ j * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))
      (fun v => 1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) _ S S (Finset.Subset.refl S) (zeta_euler F hs).1
      (fun v _ => by simpa using factor_ne_zero _ (two_le_absNorm F v) 1 s (by simp) hs0)
      (fun v _ => by simp [eSp_zpow, hj])
    rw [Finset.sdiff_self, Finset.prod_empty, mul_one] at key
    exact key
  · by_cases hj1 : 1 ≤ j
    · have hj0 : j ≠ 0 := by omega
      have hre : 1 < (j : ℂ).re := by
        obtain ⟨k, hk⟩ := hj
        simp only [Complex.intCast_re]
        exact_mod_cast (by omega : (1 : ℤ) < j)
      have hP := (zeta_inv_po_of_one_lt F hre).mul
        (PO.prod S (fun v s => (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) (fun _ => if j = 0 then 1 else 0)
          fun v _ => (factorF_zo v j).inv)
      rw [if_pos hj1]
      exact hP.mono (by simp [hj0])
    · rw [if_neg hj1]
      have hle : j ≤ 0 := by omega
      have hP := (zeta_zo_nonpos F j hle).inv.mul
        (PO.prod S (fun v s => (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) (fun _ => if j = 0 then 1 else 0)
          fun v _ => (factorF_zo v j).inv)
      have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
      refine hP.mono ?_
      by_cases hj0 : j = 0
      · simp [hj0, hFr, hFc] <;> omega
      · simp [hj0, hFr, hFc, hj]

private theorem hasProd_inv' {ι : Type} {f : ι → ℂ} {a : ℂ} (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => (f i)⁻¹) a⁻¹ := by
  unfold HasProd at h ⊢
  convert h.inv₀ ha using 1
  funext t
  exact Finset.prod_inv_distrib _

theorem lOrd_odd (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (S : Finset (HeightOneSpectrum (𝓞 F))) (j : ℤ)
    (hj : ¬ Even j) :
    ∃ Z : ℂ → ℂ, MeromorphicOn Z Set.univ ∧
      (∀ s : ℂ, 1 < s.re → HasProd (fun v : {v // v ∉ S} =>
        1 - eSp E v.1 ^ j * (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s)) (Z s)) ∧
      PO Z (j : ℂ) (if 1 ≤ j then 0 else if j = 0 then S.card + Module.finrank ℚ F - 1
        else Module.finrank ℚ F) := by
  classical
  obtain ⟨-, -, hEr, hEc⟩ := cm_places h
  have h2 : Module.finrank F E = 2 := h.2.2.1
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hj ⟨0, rfl⟩
  have hfacF : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : ℂ),
      AnalyticAt ℂ (fun s : ℂ => 1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) x := fun v x => by
    simpa using factor_analytic _ (by have := two_le_absNorm F v; omega) 1 x
  have hfacE : ∀ (P : HeightOneSpectrum (𝓞 E)) (x : ℂ),
      AnalyticAt ℂ (fun s : ℂ => 1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) x := fun P x => by
    simpa using factor_analytic _ (by have := two_le_absNorm E P; omega) 1 x
  have hfac : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : ℂ),
      AnalyticAt ℂ (fun s : ℂ => 1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) x := fun v x =>
    factor_analytic _ (by have := two_le_absNorm F v; omega) _ x
  have hneF : ∀ (v : HeightOneSpectrum (𝓞 F)) (s : ℂ), 0 < s.re →
      (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ≠ 0 := fun v s hs => by
    simpa using factor_ne_zero _ (two_le_absNorm F v) 1 s (by simp) hs
  have hneE : ∀ (P : HeightOneSpectrum (𝓞 E)) (s : ℂ), 0 < s.re →
      (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ≠ 0 := fun P s hs => by
    simpa using factor_ne_zero _ (two_le_absNorm E P) 1 s (by simp) hs
  have hneFj : ∀ v : HeightOneSpectrum (𝓞 F), (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-(j : ℂ))) ≠ 0 :=
    fun v => by simpa using factor_ne_zero_int _ (two_le_absNorm F v) 1 (by simp) j hj0
  have hesp : ∀ v : HeightOneSpectrum (𝓞 F), eSp E v ^ j = eSp E v := fun v => by
    rw [eSp_zpow, if_neg hj]
  set T : Finset (HeightOneSpectrum (𝓞 F)) := S ∪ (badSet_finite F E).toFinset with hT
  refine ⟨fun s => ((continuedDedekindZeta E s)⁻¹ * continuedDedekindZeta F s *
      ∏ v ∈ T, ((∏ P ∈ fib F E v, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))) *
        (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)⁻¹) *
      ∏ v ∈ T \ S, (1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)), ?_, ?_, ?_⟩
  · intro x _
    refine ((((meromorphicOn_continuedDedekindZeta E x trivial).inv).mul
      (meromorphicOn_continuedDedekindZeta F x trivial)).mul ?_).mul ?_
    · exact meromorphicAt_prod T _ fun v _ =>
        ((meromorphicAt_prod (fib F E v) _ fun P _ => (hfacE P x).meromorphicAt).mul
          (hfacF v x).meromorphicAt.inv).inv
    · exact meromorphicAt_prod (T \ S) _ fun v _ => (hfac v x).meromorphicAt
  · intro s hs
    have hs0 : 0 < s.re := by linarith
    have hFinv : HasProd (fun v : HeightOneSpectrum (𝓞 F) => (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)
        (continuedDedekindZeta F s) := by
      have := hasProd_inv' (zeta_euler F hs).1 (inv_ne_zero (zeta_euler F hs).2)
      rwa [inv_inv] at this
    have hg := (zetaE_grouped (F := F) (E := E) hs).mul hFinv
    have key := hasProd_compl_finset (fun v => 1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))
      (fun v => (∏ P ∈ fib F E v, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))) *
        (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) _ T S Finset.subset_union_left hg
      (fun v _ => mul_ne_zero (Finset.prod_ne_zero_iff.2 fun P _ => hneE P s hs0) (inv_ne_zero (hneF v s hs0)))
      (fun v hv => by
        have hvb : v ∉ badSet F E := fun hb =>
          hv (Finset.mem_union_right _ ((badSet_finite F E).mem_toFinset.2 hb))
        rw [local_factor F E h2 v hvb s, mul_comm (1 - _) (1 - _), mul_assoc, mul_inv_cancel₀ (hneF v s hs0),
          mul_one])
    simp only [hesp]
    exact key
  · have hZg : ∀ v : HeightOneSpectrum (𝓞 F), ZO (fun s => (∏ P ∈ fib F E v,
        (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))) * (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) (j : ℂ) 0 := by
      intro v
      have h1 := ZO.prod (fib F E v) (fun P s => 1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) (fun _ => 0)
        (fun P _ => by
          have := factorF_zo P j
          rwa [if_neg hj0] at this)
      have h3 : ZO (fun s => (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹) (j : ℂ) 0 :=
        ZO.of_analytic ((hfacF v j).inv (hneFj v)) (inv_ne_zero (hneFj v))
      have := h1.mul h3
      simp only [Finset.sum_const_zero, add_zero] at this
      exact this
    have hPg : PO (fun s => ∏ v ∈ T, ((∏ P ∈ fib F E v, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))) *
        (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)⁻¹) (j : ℂ) 0 := by
      have := PO.prod T (fun v s => ((∏ P ∈ fib F E v, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))) *
        (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)⁻¹) (fun _ => 0) (fun v _ => (hZg v).inv)
      simp only [Finset.sum_const_zero] at this
      exact this
    have hPf : PO (fun s => ∏ v ∈ T \ S, (1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) (j : ℂ) 0 := by
      have := PO.prod (T \ S) (fun v s => 1 - eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) (fun _ => 0)
        (fun v _ => PO.of_analytic (hfac v j))
      simp only [Finset.sum_const_zero] at this
      exact this
    by_cases hj1 : 1 ≤ j
    · rw [if_pos hj1]
      by_cases hj1' : j = 1
      · subst hj1'
        obtain ⟨AE, hAE, hAE1, hevE⟩ := zeta_pole E
        obtain ⟨AF, hAF, -, hevF⟩ := zeta_pole F
        have hc : ((1 : ℤ) : ℂ) = 1 := by simp
        have hZ : PO (fun s => (continuedDedekindZeta E s)⁻¹ * continuedDedekindZeta F s) ((1 : ℤ) : ℂ) 0 := by
          rw [hc]
          refine ⟨fun s => AF s / AE s, hAF.div hAE hAE1, ?_⟩
          filter_upwards [hevE, hevF, self_mem_nhdsWithin] with s hE hF hs
          have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
          rw [← hE, ← hF, pow_zero, one_mul, mul_div_mul_left _ _ hs1, div_eq_inv_mul]
        exact ((hZ.mul hPg).mul hPf).mono (by norm_num)
      · have hre : 1 < (j : ℂ).re := by
          simp only [Complex.intCast_re]
          exact_mod_cast (by omega : (1 : ℤ) < j)
        have hj1c : (j : ℂ) ≠ 1 := by exact_mod_cast hj1'
        have hZ := (zeta_inv_po_of_one_lt E hre).mul (PO.of_analytic (zeta_analyticAt F hj1c))
        exact ((hZ.mul hPg).mul hPf).mono (by norm_num)
    · rw [if_neg hj1, if_neg hj0]
      have hle : j ≤ 0 := by omega
      have hj1c : (j : ℂ) ≠ 1 := by exact_mod_cast (by omega : j ≠ 1)
      have hZ := ((zeta_zo_nonpos E j hle).inv).mul (PO.of_analytic (zeta_analyticAt F hj1c))
      refine ((hZ.mul hPg).mul hPf).mono ?_
      simp [hEr, hEc, hj, hj0]

theorem _root_.PositivityTheory.SiegelWeilFormula.Gen.lOrd : LOrd := by
  intro F E _ _ _ _ _ σ h S j
  by_cases hj : Even j
  · exact lOrd_even σ h S j hj
  · exact lOrd_odd σ h S j hj

end PositivityTheory.Lord
