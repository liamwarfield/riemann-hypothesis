module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IdeleNormLocalCompatibility

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicCharEqLocPowOfLocalArtinUnit
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.cyclotomicChar_eq_locPow_of_localArtin_unit :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (σ : Weil h),
    valuation (w.adicCompletion F) (a σ : w.adicCompletion F) = 1 →
    ((cycBar F Ω p σ : (Qbar p)ˣ) : Qbar p) = GlobalTheory.HeckeGal.locPow ι (fun _ => 1) w (a σ : w.adicCompletion F) := by
  intro hG F Ω _ _ _ _ _ w A h a ha p _ ι σ hv
  obtain ⟨art, hart⟩ := hG F Ω
  obtain ⟨μ, hμ, hL⟩ := hart.exists_isLAdicOf ι (GlobalTheory.Published.CharAboveModel.absPow_isAlgPos F 1)
  have e := GlobalTheory.Published.CharAboveModel.eq_cyc_pow hart hμ hL
  have h1 := hL.loc (a σ) σ (ha.glob art hart σ)
  have : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion F))
    (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))
  have hu : Valued.v (a σ : w.adicCompletion F) = 1 := he.eq_one_iff_eq_one.1 hv
  have h2 : (GlobalTheory.HeckeGal.Model.absPow F ((1 : ℕ) : ℝ)).loc w (a σ) = 1 :=
    (GlobalTheory.HeckeGal.Model.absPow_isAbsPow F ((1 : ℕ) : ℝ)).1 w _ hu
  rw [h2, e, pow_one, cyc_eq_map_cycZ] at h1
  simp only [Units.val_one, map_one, one_mul, Nat.cast_one] at h1
  exact h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FixesRootsOfUnityOfCyclotomicCharNearOne
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.fixes_roots_of_unity_of_cyclotomicChar_near_one :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (p : ℕ) [Fact p.Prime] (b : ℕ) (s : G F Ω),
    ‖((cycBar F Ω p s : (Qbar p)ˣ) : Qbar p) - 1‖ ≤ ‖((p ^ b : ℕ) : Qbar p)‖ → ∀ ζ : Ω, ζ ^ p ^ b = 1 → s ζ = ζ := by
  intro F Ω _ _ _ _ _ p _ b s h ζ hζ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (p ^ i) := fun i => inferInstance
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [pow_zero, pow_one] at hζ
    rw [hζ, map_one]
  set j : ℤ_[p] := ((cycZ F Ω p s : ℤ_[p]ˣ) : ℤ_[p]) with hj
  have hn : ∀ x : ℚ_[p], ‖algebraMap ℚ_[p] (PadicAlgCl p) x‖ = ‖x‖ := fun x => PadicAlgCl.norm_extends p x
  have e1 : ((cycBar F Ω p s : (Qbar p)ˣ) : Qbar p) - 1 = algebraMap ℚ_[p] (PadicAlgCl p) (((j - 1 : ℤ_[p])) : ℚ_[p]) := by
    rw [show ((cycBar F Ω p s : (Qbar p)ˣ) : Qbar p) = algebraMap ℚ_[p] (PadicAlgCl p) (j : ℚ_[p]) from rfl]
    simp
  have e2 : ((p ^ b : ℕ) : Qbar p) = algebraMap ℚ_[p] (PadicAlgCl p) ((((p : ℤ_[p]) ^ b : ℤ_[p])) : ℚ_[p]) := by
    simp
  rw [e1, e2, hn, hn] at h
  have h' : ‖j - 1‖ ≤ (p : ℝ) ^ (-(b : ℤ)) := by
    rw [← PadicInt.norm_p_pow]
    exact h
  have hmem := (PadicInt.norm_le_pow_iff_mem_span_pow (j - 1) b).mp h'
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
  have hspec := cyclotomicCharacter.spec (L := Ω) p (MulSemiringAction.toRingAut (G F Ω) Ω s) ζ hζ
  have hone : (p ^ b : ℕ) ≠ 1 := by
    have := Nat.one_lt_pow hb.ne' (Fact.out : p.Prime).one_lt
    omega
  have hval : ((cyclotomicCharacter Ω p (MulSemiringAction.toRingAut (G F Ω) Ω s)).val.toZModPow b).val = 1 := by
    have hj' : (cyclotomicCharacter Ω p (MulSemiringAction.toRingAut (G F Ω) Ω s)).val = j := rfl
    rw [hj', hmem]
    exact ZMod.val_one'' hone
  rw [hval, pow_one] at hspec
  exact hspec
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.NormLocPowSubOneLeOfValuationSubOneLe
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem norm_lt_one_of_valuation_lt {F : Type} [Field F] [NumberField F] {w : HeightOneSpectrum (𝓞 F)} {p : ℕ} [Fact p.Prime]
    (j : w.adicCompletion F →+* Qbar p) (hj : Continuous j) (y : w.adicCompletion F) (hy : Valued.v y < 1) :
    ‖j y‖ < 1 := by
  have h2 := Valued.tendsto_zero_pow_of_v_lt_one hy
  have h3 := (hj.tendsto 0).comp h2
  rw [map_zero] at h3
  rw [← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  refine h3.congr (fun n => ?_)
  simp

private theorem norm_le_one_of_valuation_le {F : Type} [Field F] [NumberField F] {w : HeightOneSpectrum (𝓞 F)} {p : ℕ} [Fact p.Prime]
    (j : w.adicCompletion F →+* Qbar p) (hj : Continuous j) (y : w.adicCompletion F) (hy : Valued.v y ≤ 1) :
    ‖j y‖ ≤ 1 := by
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  set t := algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F a) with ht
  have h1 : Valued.v t < 1 := by
    have : Valued.v t = w.valuation F (algebraMap (𝓞 F) F a) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [this]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem w a).2 ha
  have ht0 : t ≠ 0 := by
    rw [ht, map_ne_zero]
    exact fun h => ha0 (by simpa using h)
  have hpos : 0 < ‖j t‖ := norm_pos_iff.mpr ((map_ne_zero j).mpr ht0)
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖j t‖⁻¹) hlt
  have h4 : Valued.v (t * y ^ n) < 1 := by
    rw [map_mul, map_pow]
    calc Valued.v t * Valued.v y ^ n ≤ Valued.v t * 1 := by
          gcongr
          exact pow_le_one' hy n
      _ < 1 := by rwa [mul_one]
  have h5 := norm_lt_one_of_valuation_lt j hj _ h4
  rw [map_mul, map_pow, norm_mul, norm_pow] at h5
  rw [inv_lt_iff_one_lt_mul₀' hpos] at hn
  exact absurd (hn.trans h5) (lt_irrefl _)

theorem UpperTheory.norm_locPow_sub_one_le_of_valuation_sub_one_le :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (M : ℕ)
    (u : w.adicCompletion F), valuation (w.adicCompletion F) (u - 1) ≤ valuation (w.adicCompletion F) (M : w.adicCompletion F) →
    ‖GlobalTheory.HeckeGal.locPow ι (fun _ => 1) w u - 1‖ ≤ ‖(M : Qbar p)‖ := by
  intro F _ _ w p _ ι M u h
  have hv : Valued.v (u - 1) ≤ Valued.v (M : w.adicCompletion F) :=
    ((Valuation.Compatible.vle_iff_le (v := valuation (w.adicCompletion F)) _ _).mpr h :)
  have hM1 : ‖(M : Qbar p)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ M
  have key : ∀ j : w.adicCompletion F →+* Qbar p, Continuous j → ‖j u - 1‖ ≤ ‖(M : Qbar p)‖ := by
    intro j hj
    by_cases hM : (M : w.adicCompletion F) = 0
    · rw [hM, map_zero, le_zero_iff, map_eq_zero, sub_eq_zero] at hv
      simp [hv]
    · have hx : Valued.v ((u - 1) / (M : w.adicCompletion F)) ≤ 1 := by
        rw [map_div₀]
        exact div_le_one_of_le₀ hv zero_le
      have h1 := norm_le_one_of_valuation_le j hj _ hx
      have hM' : (M : Qbar p) ≠ 0 := by
        rw [← map_natCast j]
        exact (map_ne_zero j).mpr hM
      rw [map_div₀, map_sub, map_one, map_natCast, norm_div, div_le_one (norm_pos_iff.mpr hM')] at h1
      exact h1
  unfold GlobalTheory.HeckeGal.locPow
  refine finprod_induction (fun z : Qbar p => ‖z - 1‖ ≤ ‖(M : Qbar p)‖) (by simp) ?_ ?_
  · intro x y hx hy
    have hx1 : ‖x‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max (x - 1) 1
      rw [sub_add_cancel, norm_one] at this
      exact this.trans (max_le (hx.trans hM1) le_rfl)
    have e : x * y - 1 = x * (y - 1) + (x - 1) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hx)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hx1).trans hy
  · intro j
    rw [zpow_one]
    exact key j.1 j.2
end

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N ValuativeRel
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.card_padicAlgCl_eq_continuum (p : ℕ) [Fact p.Prime] :
    Cardinal.mk (PadicAlgCl p) = Cardinal.continuum := by
  have hle : Cardinal.mk ℚ_[p] ≤ Cardinal.continuum := by
    have h1 : Cardinal.mk ℚ_[p] ≤ Cardinal.mk (CauSeq ℚ (padicNorm p)) := Cardinal.mk_quotient_le
    have h2 : Cardinal.mk (CauSeq ℚ (padicNorm p)) ≤ Cardinal.mk (ℕ → ℚ) := Cardinal.mk_subtype_le _
    refine h1.trans (h2.trans ?_)
    rw [Cardinal.mk_arrow, Cardinal.mk_eq_aleph0 ℚ, Cardinal.mk_nat]
    simp
  have hge : Cardinal.continuum ≤ Cardinal.mk ℚ_[p] := by
    obtain ⟨f, -, -, hf⟩ :=
      Perfect.exists_nat_bool_injection (PerfectSpace.univ_perfect (α := ℚ_[p])) Set.univ_nonempty
    have := Cardinal.mk_le_of_injective hf
    simpa using this
  apply le_antisymm
  · have := Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)
    refine this.trans ?_
    exact max_le hle Cardinal.aleph0_le_continuum
  · exact hge.trans (Cardinal.mk_le_of_injective (algebraMap ℚ_[p] (PadicAlgCl p)).injective)

private theorem UpperTheory.nonempty_qbar_ringEquiv_complex (p : ℕ) [Fact p.Prime] : Nonempty (Qbar p ≃+* ℂ) := by
  have hc := UpperTheory.card_padicAlgCl_eq_continuum p
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ (PadicAlgCl p)
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ ℂ
  have hQ : Cardinal.mk ℚ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs hQ
    (by rw [hc]; exact Cardinal.aleph0_lt_continuum)
  have h2 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht hQ
    (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum)
  simp only [Cardinal.lift_id] at h1 h2
  have hst : Cardinal.mk s = Cardinal.mk t := by rw [← h1, ← h2, hc, Cardinal.mk_complex]
  obtain ⟨e⟩ := Cardinal.eq.mp hst
  exact ⟨IsAlgClosed.equivOfTranscendenceBasis _ _ e hs ht⟩

private theorem UpperTheory.algEquiv_fixes_root_of_fixes_prime_power_roots {F K : Type} [Field F] [Field K] [Algebra F K] (g : K ≃ₐ[F] K) :
    ∀ d : ℕ, d ≠ 0 → (∀ p b : ℕ, p.Prime → p ^ b ∣ d → ∀ ζ : K, ζ ^ (p ^ b) = 1 → g ζ = ζ) →
    ∀ ζ : K, ζ ^ d = 1 → g ζ = ζ := by
  intro d
  induction d using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro _ H ζ hζ
    exact H p n hp dvd_rfl ζ hζ
  | zero =>
    intro h
    exact absurd rfl h
  | one =>
    intro _ _ ζ hζ
    rw [pow_one] at hζ
    rw [hζ, map_one]
  | coprime a b ha hb hab iha ihb =>
    intro hd H ζ hζ
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hA : g (ζ ^ b) = ζ ^ b :=
      iha ha0 (fun p c hp hpc => H p c hp (hpc.trans (Dvd.intro _ rfl))) _
        (by rw [← pow_mul, mul_comm, hζ])
    have hB : g (ζ ^ a) = ζ ^ a :=
      ihb hb0 (fun p c hp hpc => H p c hp (hpc.trans (Dvd.intro_left _ rfl))) _
        (by rw [← pow_mul, hζ])
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow (mul_ne_zero ha0 hb0)] at hζ
      exact zero_ne_one hζ
    have hbez : (1 : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b := by
      have := Nat.gcd_eq_gcd_ab a b
      rw [Nat.Coprime.gcd_eq_one hab] at this
      exact_mod_cast this
    have e : ζ = (ζ ^ a) ^ Nat.gcdA a b * (ζ ^ b) ^ Nat.gcdB a b := by
      rw [← zpow_natCast ζ a, ← zpow_natCast ζ b, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0, ← hbez,
        zpow_one]
    rw [e, map_mul, map_zpow₀, map_zpow₀, hA, hB]

theorem UpperTheory.inertia_fixes_roots_of_unity_of_artin_congruence :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ M : ℕ, 1 ≤ M → ∀ σ : Weil h,
    valuation (w.adicCompletion F) (a σ : w.adicCompletion F) = 1 →
    valuation (w.adicCompletion F) ((a σ : w.adicCompletion F) - 1) ≤ valuation (w.adicCompletion F) (M : w.adicCompletion F) →
    (σ : G F Ω) ∈ Ine (F := F) A ∧ ∀ ζ : Ω, ζ ^ M = 1 → (σ : G F Ω) ζ = ζ := by
  intro hGAR F Ω _ _ _ _ _ w A h a ha M hM σ hv hvM
  have hord : GlobalTheory.SmGL.ord (w.adicCompletion F) (a σ) = 0 := GlobalTheory.SmGL.ord_eq_zero_iff.mpr hv
  have hdeg : deg σ = 0 := by
    have := ha.ord_eq σ
    rw [hord] at this
    omega
  refine ⟨deg_eq_zero_iff.mp hdeg, ?_⟩
  have hnat : ∀ n : ℕ, valuation (w.adicCompletion F) (n : w.adicCompletion F) ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ]
      exact (Valuation.map_add _ _ _).trans (max_le ih (by rw [map_one]))
  apply UpperTheory.algEquiv_fixes_root_of_fixes_prime_power_roots (σ : G F Ω) M (by omega)
  intro p b hp hpb ζ hζ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ι⟩ := UpperTheory.nonempty_qbar_ringEquiv_complex p
  have hle : valuation (w.adicCompletion F) ((a σ : w.adicCompletion F) - 1) ≤
      valuation (w.adicCompletion F) ((p ^ b : ℕ) : w.adicCompletion F) := by
    obtain ⟨c, hc⟩ := hpb
    refine hvM.trans ?_
    rw [hc, Nat.cast_mul, map_mul]
    exact mul_le_of_le_one_right' (hnat c)
  have h82 := UpperTheory.norm_locPow_sub_one_le_of_valuation_sub_one_le F w p ι (p ^ b) (a σ) hle
  have h78 := UpperTheory.cyclotomicChar_eq_locPow_of_localArtin_unit hGAR F Ω w A h a ha p ι σ hv
  rw [← h78] at h82
  exact UpperTheory.fixes_roots_of_unity_of_cyclotomicChar_near_one F Ω p b (σ : G F Ω) h82 ζ hζ
