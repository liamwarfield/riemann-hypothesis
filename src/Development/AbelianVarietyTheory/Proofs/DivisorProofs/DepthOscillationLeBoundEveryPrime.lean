module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLargeInertPrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorDepthBoundedOddInertPrimeCmType

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeAtSmallOddInertPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeAtSmallOddInertPrime
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig IsSmall IsSpread sumSmallSpread not_isBig_iff)

namespace GlobalTheory.RefSum.OscInert

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}


open Classical in
theorem two_mul_card_psi_le :
    2 * (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card ≤ Module.finrank ℚ E := by
  have hne : starRingEnd ℂ H.rt0 ≠ H.rt0 := by
    intro h
    have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 h
    have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
    simp [pow_two, Complex.mul_re, him] at h2
    have hd : (2:ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
    nlinarith [sq_nonneg H.rt0.re]
  have hinj : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card ≤
      (Finset.univ.filter (fun τ : E →+* ℂ => ¬ InPsi H τ)).card := by
    refine Finset.card_le_card_of_injOn (fun τ => (starRingEnd ℂ).comp τ) ?_ ?_
    · intro τ hτ
      simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_coe, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ ⊢
      unfold InPsi at hτ ⊢
      simp only [RingHom.coe_comp, Function.comp_apply, hτ]
      exact hne
    · intro τ _ σ _ h
      ext x
      have := congrArg (fun g : E →+* ℂ => starRingEnd ℂ (g x)) h
      simpa using this
  have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (E →+* ℂ)))
    (fun τ => InPsi H τ)
  rw [Finset.card_univ, NumberField.Embeddings.card] at htot
  omega


open Classical in
theorem card_big_fiber_le {Dw : Datum H} {F k m : ℕ} (hS : Shape Dw F k m) (τ : E →+* ℂ) :
    (Finset.univ.filter (fun f : Lt1 Dw => GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f ∧ f.1 = τ)).card ≤ m + 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  calc _ ≤ (Finset.Ico (k - 2) Dw.p).card := by
        refine Finset.card_le_card_of_injOn (fun f => f.2.val) ?_ ?_
        · intro f hf
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_coe, Finset.mem_univ, true_and,
            Set.mem_setOf_eq, Finset.mem_Ico] at hf ⊢
          obtain ⟨⟨hpsi, hk⟩, -⟩ := hf
          have hlt := f.2.isLt
          have hm : Dw.mult f.1 = Dw.p := if_pos hpsi
          have hk' : k ≤ f.2.val + 1 + 1 := hk
          omega
        · intro f hf g hg hfg
          simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_coe, Finset.mem_univ, true_and,
            Set.mem_setOf_eq] at hf hg
          obtain ⟨τ1, j1⟩ := f
          obtain ⟨τ2, j2⟩ := g
          obtain ⟨-, h1'⟩ := hf
          obtain ⟨-, h2'⟩ := hg
          simp only at h1' h2' hfg
          subst h1' h2'
          exact Sigma.ext rfl (heq_of_eq (Fin.ext hfg))
    _ ≤ m + 1 := by rw [Nat.card_Ico]; omega

theorem boundFine_le {p N q i c m M : ℕ} (hp : 2 ≤ p) (hq : q ≤ m) (hi : N ≤ m + i) (hiN : i ≤ N) (hc : 1 ≤ c)
    (hcM : c ≤ M) :
    boundFine p N q i c ≤ (c : ℝ) * (m * (4 + Real.logb p M / 2) / ((p : ℝ) - 1)) + (N : ℝ) ^ 2 * (Real.logb p M + 1) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hq' : (q : ℝ) ≤ m := by exact_mod_cast hq
  have hi' : (N : ℝ) ≤ m + i := by exact_mod_cast hi
  have hiN' : (i : ℝ) ≤ N := by exact_mod_cast hiN
  have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hcM' : (c : ℝ) ≤ M := by exact_mod_cast hcM
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hl0 : 0 ≤ Real.logb p c := Real.logb_nonneg (by linarith) hc'
  have hl : Real.logb p c ≤ Real.logb p M := Real.logb_le_logb_of_le (by linarith) (by linarith) hcM'
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp2 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hcm : (0 : ℝ) ≤ c * m := by positivity
  have t1 : (c : ℝ) * ((N : ℝ) - 2 * q - i) * p / ((p : ℝ) ^ 2 - 1) ≤ c * m / ((p : ℝ) - 1) := by
    calc _ ≤ (c : ℝ) * m * p / ((p : ℝ) ^ 2 - 1) := by
          gcongr
          linarith
      _ ≤ _ := by
          rw [div_le_div_iff₀ hp2 hp1]
          nlinarith [mul_nonneg hcm hp1.le]
  have t2 : (c : ℝ) * q * (3 + 1 / 2 * Real.logb p c) / ((p : ℝ) - 1) ≤
      c * m * (3 + 1 / 2 * Real.logb p M) / ((p : ℝ) - 1) := by
    gcongr
  have t3 : (i : ℝ) ^ 2 * (Real.logb p c + 1) ≤ (N : ℝ) ^ 2 * (Real.logb p M + 1) := by
    gcongr
  have e : (c : ℝ) * (m * (4 + Real.logb p M / 2) / ((p : ℝ) - 1)) =
      c * m / ((p : ℝ) - 1) + c * m * (3 + 1 / 2 * Real.logb p M) / ((p : ℝ) - 1) := by ring
  unfold boundFine
  linarith


open Classical in
theorem sum_bound_le {Dw : Datum H} {F k m M : ℕ} {Mb Sm : ℝ} {cx : Lt1 Dw → ℕ} {p : ℕ}
    (hS : Shape Dw F k m) (hB : ExpBd Dw k cx Mb Sm M) (hp : 2 ≤ p) (hM : 1 ≤ M) :
    ∑ f, (if GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f ∧ 1 ≤ cx f then boundFine p (Dw.p + Dw.q) Dw.q (rk f) (cx f) else boundAll p (rk f) (cx f))
      ≤ eSmall F (Dw.p + Dw.q) m Mb Sm M p := by
  have hfib := card_big_fiber_le hS
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  obtain ⟨hMb, hτ, hSm, hcM⟩ := hB
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hL : 0 ≤ Real.logb p M := Real.logb_nonneg (by linarith) (by exact_mod_cast hM)
  have hF : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card ≤ F := by
    have := two_mul_card_psi_le (H := H)
    omega
  have hF' : ((Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card : ℝ) ≤ F := by exact_mod_cast hF
  set X : ℝ := m * (4 + Real.logb p M / 2) / ((p : ℝ) - 1) with hX
  set Y : ℝ := ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 * (Real.logb p M + 1) with hY
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hmaps : ∀ f ∈ Finset.univ.filter (fun f : Lt1 Dw => GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f),
      f.1 ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ) := fun f hf =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hf).2.1⟩
  have hbig : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f), ((cx f : ℝ) * X + Y) ≤
      F * (Mb * X + (m + 1) * Y) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc _ ≤ ∑ _τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ), (Mb * X + (m + 1) * Y) := by
          refine Finset.sum_le_sum fun τ _ => ?_
          rw [Finset.filter_filter, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul]
          have a1 := hτ τ
          have a2 : ((Finset.univ.filter (fun f : Lt1 Dw => GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f ∧ f.1 = τ)).card : ℝ) ≤ m + 1 := by
            exact_mod_cast hfib τ
          rw [Nat.cast_sum] at a1
          refine add_le_add (mul_le_mul_of_nonneg_right ?_ hX0) (mul_le_mul_of_nonneg_right ?_ hY0)
          · convert a1
          · convert a2
      _ ≤ _ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right hF' (by positivity)
  have hsm : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => ¬ GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f), boundAll p (rk f) (cx f) ≤
      Sm / ((p : ℝ) - 1) := by
    refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right hSm hp1.le)
    unfold sumSmallSpread boundAll
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr ?_ fun f _ => by rw [Nat.cast_mul]
    ext f
    simp only [Finset.mem_filter, not_isBig_iff]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun f : Lt1 Dw => GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f)]
  have e : eSmall F (Dw.p + Dw.q) m Mb Sm M p = F * (Mb * X + (m + 1) * Y) + Sm / ((p : ℝ) - 1) := by
    rw [hX, hY]
    unfold eSmall
    ring
  rw [e]
  refine add_le_add (le_trans (Finset.sum_le_sum fun f hf => ?_) hbig) (le_trans (le_of_eq ?_) hsm)
  · have hb : GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f := (Finset.mem_filter.1 hf).2
    have hm : Dw.mult f.1 = Dw.p := if_pos hb.1
    have hr := rk_le f
    have hk := hb.2
    split_ifs with h
    · exact boundFine_le hp h2 (by omega) (by omega) h.2 (hcM f)
    · have h0 : cx f = 0 := by
        by_contra hne
        exact h ⟨hb, by omega⟩
      simp [boundAll, h0, hY0]
  · exact Finset.sum_congr rfl fun f hf => if_neg fun h => (Finset.mem_filter.1 hf).2 h.1

end GlobalTheory.RefSum.OscInert

namespace GlobalTheory.RefSum

theorem oscLe_eSmall_of_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ (p : ℤ) ∣ discr E → InertInK H p → 1 ≤ M → OscLe Xo c p cx (eSmall F (Dw.p + Dw.q) m Mb Sm M p + 1) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hB p hp hp2 hpd hin hM la
  classical
  have key : ∀ f : Lt1 Dw, ∃ A B : ℝ, FacBetween Xo la f (cx f) A B ∧ B - A ≤
      (if GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f ∧ 1 ≤ cx f then boundFine p (Dw.p + Dw.q) Dw.q (rk f) (cx f) else boundAll p (rk f) (cx f)) := by
    intro f
    split_ifs with h
    · exact GlobalTheory.T.factor_depth_bounded_odd_inert_prime_cmType E H Dw l Xo c p la hp2 hpd hin f (cx f) h.1.1 h.2
    · exact ⟨0, _, (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1, (sub_zero _).le⟩
  choose A B hAB hle using key
  obtain ⟨-, n, hn⟩ := (GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 A B hAB
  have h1 := OscInert.sum_bound_le hS hB hp.out.two_le hM
  have h2 := (Finset.sum_le_sum fun f (_ : f ∈ Finset.univ) => hle f).trans (by convert h1)
  exact ⟨n, fun T io e ho y => ⟨(hn T io e ho y).1, fun ha => ((hn T io e ho y).2 ha).trans
    (EReal.coe_le_coe_iff.2 (by linarith))⟩⟩

end GlobalTheory.RefSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeAtSmallOddInertPrimeStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthOscillation_le_at_small_odd_inertPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ (p : ℤ) ∣ discr E → InertInK H p → 1 ≤ M → OscLe Xo c p cx (eSmall F (Dw.p + Dw.q) m Mb Sm M p + 1) := by
  first | exact @GlobalTheory.RefSum.oscLe_eSmall_of_inert | exact GlobalTheory.RefSum.oscLe_eSmall_of_inert | (intros; apply GlobalTheory.RefSum.oscLe_eSmall_of_inert <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeAtTwoCmField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanUpperBoundBigFactorsPlaceAboveTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanUpperBoundBigFactorsPlaceAboveTwo
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem mean_bound_big_factors_at_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (F : ℕ) (vd : ℝ), UpperTheory.Depth.SplitPlaces p H F vd → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ¬ IsUnit ((p : ℕ) : T.V) → y.IsAlg → ∃ len : (E →+* ℂ) → ℝ, (∀ τ, 0 ≤ len τ) ∧ (∀ τ, ¬ InPsi H τ → len τ = 0) ∧ ∑ τ, len τ ≤ F * Dw.q * (1 + vd / 2) ∧ ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → nuFac p y f k ≤ ((k * len f.1 : ℝ) : EReal) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p hp F vd hTP T io y h2 hy
  classical
  obtain ⟨Ch, -⟩ := (@GlobalTheory.IntChartExists.intChart_exists E _ _ _ H Dw l Xo c H.starRing).2.2 (fun _ => rfl) T io y
  obtain ⟨X⟩ := GlobalTheory.CharDepth.nonempty_valExt T p h2
  obtain ⟨xs, hAF, hprod⟩ := GlobalTheory.CharDepth.colength_bound_at_two p (GlobalTheory.ChF.colength_bound_split_place_chart p)
    E H Dw l Xo c T io y Ch X hy F vd hTP
  set v2 : ℝ := (X.v ((p : ℕ) : X.C) : ℝ) with hv2
  set B : ℝ := (F : ℝ) * Dw.q * (1 + vd / 2) with hB

  have hv2pos : 0 < v2 := by
    rw [hv2, NNReal.coe_pos, pos_iff_ne_zero, Ne, map_eq_zero]
    exact Nat.cast_ne_zero.2 hp.out.ne_zero
  have hv2lt : v2 < 1 := by
    have h2C : algebraMap X.O X.C ((p : ℕ) : X.O) = ((p : ℕ) : X.C) := map_natCast _ _
    have hle := X.ints.map_le_one ((p : ℕ) : X.O)
    have hne : X.v (algebraMap X.O X.C ((p : ℕ) : X.O)) ≠ 1 := fun h =>
      X.nonunit.out ((X.ints.isUnit_iff_valuation_eq_one).2 h)
    rw [h2C] at hle hne
    rw [hv2]
    exact_mod_cast lt_of_le_of_ne hle hne
  have hlogv : Real.log v2 < 0 := Real.log_neg hv2pos hv2lt

  have hpos : ∀ τ, InPsi H τ → 0 < (xs τ : ℝ) := by
    intro τ hτ
    have hP : 0 < ∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ) :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos hv2pos _) hprod
    rcases (NNReal.coe_nonneg (xs τ)).lt_or_eq with h | h
    · exact h
    · exfalso
      have : ∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ) = 0 :=
        Finset.prod_eq_zero (Finset.mem_filter.2 ⟨Finset.mem_univ _, hτ⟩) h.symm
      linarith
  have hle1 : ∀ τ, InPsi H τ → (xs τ : ℝ) ≤ 1 := by
    intro τ hτ
    have hne : xs τ ≠ 0 := fun h => by have := hpos τ hτ; rw [h] at this; simp at this
    exact_mod_cast (GlobalTheory.CharDepth.exists_flag_characters X.C X.v X.O X.ints _ _ _ _ _ (hAF τ hτ) hne).1
  let len : (E →+* ℂ) → ℝ := fun τ => if InPsi H τ then Real.log (xs τ) / Real.log v2 else 0
  have hlen_pow : ∀ τ, InPsi H τ → v2 ^ len τ = (xs τ : ℝ) := by
    intro τ hτ
    simp only [len, if_pos hτ]
    rw [Real.rpow_def_of_pos hv2pos, mul_div_cancel₀ _ hlogv.ne, Real.exp_log (hpos τ hτ)]
  refine ⟨len, ?_, ?_, ?_, ?_⟩
  · intro τ
    by_cases hτ : InPsi H τ
    · simp only [len, if_pos hτ]
      exact div_nonneg_of_nonpos (Real.log_nonpos (NNReal.coe_nonneg _) (hle1 τ hτ)) hlogv.le
    · simp [len, if_neg hτ]
  · intro τ hτ
    simp [len, if_neg hτ]
  · have hsum : ∑ τ, len τ = (∑ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), Real.log (xs τ)) / Real.log v2 := by
      rw [Finset.sum_div, Finset.sum_filter]
    have hlogP : Real.log (∏ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), (xs τ : ℝ)) =
        ∑ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), Real.log (xs τ) :=
      Real.log_prod fun τ hτ => (hpos τ (Finset.mem_filter.1 hτ).2).ne'
    have hlb : B * Real.log v2 ≤ ∑ τ ∈ Finset.univ.filter (fun τ => InPsi H τ), Real.log (xs τ) := by
      rw [← hlogP, ← Real.log_rpow hv2pos]
      exact Real.log_le_log (Real.rpow_pos_of_pos hv2pos _) hprod
    rw [hsum, div_le_iff_of_neg hlogv]
    exact hlb
  · intro f k hf
    have hr : (X.v ((p : ℕ) : X.C) : ℝ) ^ len f.1 ≤ xs f.1 := (hlen_pow f.1 hf).le
    exact (GlobalTheory.T.flagStep_characters_of_colength E H Dw l Xo c p T io y Ch X f (xs f.1) (len f.1) (hAF f.1 hf) hr).2 k

end GlobalTheory.RefSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanUpperBoundBigFactorsPlaceAboveTwoStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanUpperBound_bigFactors_placeAboveTwo : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (F : ℕ) (vd : ℝ), UpperTheory.Depth.SplitPlaces p H F vd → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ¬ IsUnit ((p : ℕ) : T.V) → y.IsAlg → ∃ len : (E →+* ℂ) → ℝ, (∀ τ, 0 ≤ len τ) ∧ (∀ τ, ¬ InPsi H τ → len τ = 0) ∧ ∑ τ, len τ ≤ F * Dw.q * (1 + vd / 2) ∧ ∀ (f : Lt1 Dw) (k : ℕ), InPsi H f.1 → nuFac p y f k ≤ ((k * len f.1 : ℝ) : EReal) := by
  first | exact @GlobalTheory.RefSum.mean_bound_big_factors_at_two | exact GlobalTheory.RefSum.mean_bound_big_factors_at_two | (intros; apply GlobalTheory.RefSum.mean_bound_big_factors_at_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeAtTwoCmField
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig sumSmallSpread not_isBig_iff)

namespace GlobalTheory.RefSum

theorem extendedReal_coe_finset_sum_of_real {α : Type} (s : Finset α) (g : α → ℝ) :
    ((∑ a ∈ s, g a : ℝ) : EReal) = ∑ a ∈ s, (g a : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

theorem oscLe_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime] (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitPlaces p H F vd → OscLe Xo c p cx (F * m * (1 + vd / 2) * Mb + Sm) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE p hp vd hvd hT
  classical
  intro la
  refine ⟨0, fun T io e ho y => ?_⟩
  have hfall : ∀ f : Lt1 Dw, letI := H.starRing
      (((0 : ℝ) : EReal) ≤ nuFac p y f (cx f) ∧ (y.IsAlg → nuFac p y f (cx f) ≤ ((boundAll p (rk f) (cx f) : ℝ) : EReal))) :=
    fun f => ((GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1 T io e ho y)
  have hnu : letI := H.starRing; nuP p y cx = ∑ f, nuFac p y f (cx f) := rfl
  refine ⟨?_, fun hy => ?_⟩
  · simp only [Nat.cast_zero, EReal.coe_zero] at hfall ⊢
    rw [hnu]
    exact Finset.sum_nonneg fun f _ => (hfall f).1
  · obtain ⟨len, hlen0, -, hlenS, hlen⟩ :=
      GlobalTheory.T.meanUpperBound_bigFactors_placeAboveTwo E H Dw l Xo c p F vd hT T io y (not_isUnit_of_overLa la ho) hy
    set b : Lt1 Dw → ℝ := fun f => if GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f then (cx f : ℝ) * len f.1 else (rk f : ℝ) * cx f with hb
    have hfb : ∀ f, letI := H.starRing; nuFac p y f (cx f) ≤ ((b f : ℝ) : EReal) := by
      intro f
      by_cases hbig : GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f
      · simp only [hb, if_pos hbig]
        simpa [mul_comm] using hlen f (cx f) hbig.1
      · simp only [hb, if_neg hbig]
        have := (hfall f).2 hy
        have hB : boundAll p (rk f) (cx f) ≤ (rk f : ℝ) * cx f := by
          have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
          unfold boundAll
          exact div_le_self (by positivity) (by linarith)
        exact this.trans (EReal.coe_le_coe_iff.2 hB)
    have hsum : letI := H.starRing; nuP p y cx ≤ ((∑ f, b f : ℝ) : EReal) := by
      rw [hnu, extendedReal_coe_finset_sum_of_real]
      exact Finset.sum_le_sum fun f _ => hfb f
    refine hsum.trans (EReal.coe_le_coe_iff.2 ?_)
    have hsplit : ∑ f, b f = (∑ f ∈ Finset.univ.filter (GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k), (cx f : ℝ) * len f.1) +
        ∑ f ∈ Finset.univ.filter (fun f => ¬ GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f), (rk f : ℝ) * cx f := by
      simp only [hb]; rw [Finset.sum_ite]
    have hsmall : (∑ f ∈ Finset.univ.filter (fun f => ¬ GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f), (rk f : ℝ) * cx f) ≤ Sm := by
      refine le_trans (le_of_eq ?_) hE.2.2.1
      unfold sumSmallSpread
      push_cast
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext f; simp [not_isBig_iff]
    have hbig : (∑ f ∈ Finset.univ.filter (GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k), (cx f : ℝ) * len f.1) ≤ F * m * (1 + vd / 2) * Mb := by
      have hfib := Finset.sum_fiberwise (Finset.univ.filter (GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k)) (fun f : Lt1 Dw => f.1)
        (fun f => (cx f : ℝ) * len f.1)
      rw [← hfib]
      have h1 : ∀ τ : E →+* ℂ, (∑ f ∈ (Finset.univ.filter (GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k)).filter (fun f : Lt1 Dw => f.1 = τ), (cx f : ℝ) * len f.1)
          ≤ len τ * Mb := by
        intro τ
        have hτ := hE.2.1 τ
        have : (∑ f ∈ (Finset.univ.filter (GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k)).filter (fun f : Lt1 Dw => f.1 = τ), (cx f : ℝ) * len f.1)
            = len τ * ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f ∧ f.1 = τ), (cx f : ℝ) := by
          rw [Finset.filter_filter, Finset.mul_sum]
          refine Finset.sum_congr (by ext f; simp) fun f hf => ?_
          rw [(Finset.mem_filter.1 hf).2.2, mul_comm]
        rw [this]
        refine mul_le_mul_of_nonneg_left ?_ (hlen0 τ)
        rw [Nat.cast_sum] at hτ
        refine le_trans (le_of_eq ?_) hτ
        exact Finset.sum_congr (by ext f; simp) fun _ _ => rfl
      have hq : (Dw.q : ℝ) ≤ m := by exact_mod_cast hS.2.1
      calc _ ≤ ∑ τ : E →+* ℂ, len τ * Mb := Finset.sum_le_sum fun τ _ => h1 τ
        _ = (∑ τ, len τ) * Mb := by rw [Finset.sum_mul]
        _ ≤ (F * Dw.q * (1 + vd / 2)) * Mb := mul_le_mul_of_nonneg_right hlenS hE.1
        _ ≤ F * m * (1 + vd / 2) * Mb := by
          apply mul_le_mul_of_nonneg_right _ hE.1
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
    simp only [Nat.cast_zero, zero_add]
    rw [hsplit]
    linarith

end GlobalTheory.RefSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeAtTwoCmFieldStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_oscillation_le_at_two_cmField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime] (vd : ℝ), 0 ≤ vd → UpperTheory.Depth.SplitPlaces p H F vd → OscLe Xo c p cx (F * m * (1 + vd / 2) * Mb + Sm) := by
  first | exact @GlobalTheory.RefSum.oscLe_two | exact GlobalTheory.RefSum.oscLe_two | (intros; apply GlobalTheory.RefSum.oscLe_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeOddSplitUnramifiedPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeOddSplitUnramifiedPrime
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OscSplit

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig IsSmall IsSpread sumBig sumSmallSpread not_isBig_iff)

theorem ereal_coe_sum {α : Type} (s : Finset α) (g : α → ℝ) :
    ((∑ a ∈ s, g a : ℝ) : EReal) = ∑ a ∈ s, (g a : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open Classical in
theorem card_filter_inPsi (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = Module.finrank ℚ E / 2 := by
  rw [← GlobalTheory.LamF.card_psiSet H, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun τ => by
    rw [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩)


open Classical in
theorem sumBig_le {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {F k : ℕ} {Mb : ℝ} {cx : Lt1 Dw → ℕ}
    (hF : Module.finrank ℚ E = 2 * F)
    (h : ∀ τ : E →+* ℂ, ((∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f ∧ f.1 = τ), cx f : ℕ) : ℝ) ≤ Mb) :
    (sumBig k cx : ℝ) ≤ F * Mb := by
  have hc : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = F := by
    rw [card_filter_inPsi, hF]; omega
  have e : sumBig k cx = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ),
      ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f ∧ f.1 = τ), cx f := by
    unfold sumBig
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k))
      (t := Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)) (g := fun f : Lt1 Dw => f.1)
      (fun f hf => Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hf).2.1⟩)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.filter_filter]
  rw [e, Nat.cast_sum]
  refine (Finset.sum_le_sum fun τ _ => h τ).trans ?_
  rw [Finset.sum_const, hc, nsmul_eq_mul]

theorem oscLe_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ (p : ℤ) ∣ discr E → SplitInK H p → OscLe Xo c p cx ((F * m * Mb + Sm) / ((p : ℝ) - 1)) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hB p hp h2 hd hs la
  classical
  obtain ⟨-, hqm, -, -, -, hF⟩ := hS
  obtain ⟨hMb, hbig, hsm, -⟩ := hB
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    linarith
  let B : Lt1 Dw → ℝ := fun f =>
    if GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f then (cx f : ℝ) * (Dw.q / ((p : ℝ) - 1)) else boundAll p (rk f) (cx f)
  have hsum : ∑ f, B f ≤ (F * m * Mb + Sm) / ((p : ℝ) - 1) := by
    have e1 : ∑ f ∈ Finset.univ.filter (GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k), (cx f : ℝ) * (Dw.q / ((p : ℝ) - 1)) =
        (sumBig k cx : ℝ) * Dw.q / ((p : ℝ) - 1) := by
      rw [← Finset.sum_mul, mul_div_assoc, sumBig, Nat.cast_sum]
    have e2 : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => ¬ GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f), boundAll p (rk f) (cx f) =
        (sumSmallSpread k cx : ℝ) / ((p : ℝ) - 1) := by
      rw [sumSmallSpread, Nat.cast_sum, Finset.sum_div]
      refine Finset.sum_congr (Finset.filter_congr fun f _ => not_isBig_iff k f) fun f _ => ?_
      rw [boundAll, Nat.cast_mul]
    have h1 := sumBig_le (k := k) (cx := cx) hF hbig
    have h3 : (Dw.q : ℝ) ≤ m := by exact_mod_cast hqm
    have h4 : (sumBig k cx : ℝ) * Dw.q ≤ F * Mb * m :=
      mul_le_mul h1 h3 (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hMb)
    rw [Finset.sum_ite, e1, e2, ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hp1.le
  refine ⟨0, fun T io e ho y => ?_⟩
  have hall := fun f => (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1 T io e ho y
  constructor
  · rw [Nat.cast_zero, EReal.coe_zero]
    exact Finset.sum_nonneg fun f _ => (hall f).1
  · intro ha
    rw [Nat.cast_zero, zero_add]
    refine le_trans ?_ (EReal.coe_le_coe_iff.2 hsum)
    rw [ereal_coe_sum]
    refine Finset.sum_le_sum fun f _ => ?_
    by_cases hf : GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f
    · simp only [B, if_pos hf]
      exact (GlobalTheory.T.factorDepth_upperBound_oddUnramifiedPrime E H Dw l Xo c p T io y (not_isUnit_of_overLa la ho) ha h2 hd f (cx f) hf.1).1 hs
    · simp only [B, if_neg hf]
      exact (hall f).2 ha

end GlobalTheory.OscSplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeOddSplitUnramifiedPrimeStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depth_oscillation_le_odd_split_unramified_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ (p : ℤ) ∣ discr E → SplitInK H p → OscLe Xo c p cx ((F * m * Mb + Sm) / ((p : ℝ) - 1)) := by
  first | exact @GlobalTheory.OscSplit.oscLe_split | exact GlobalTheory.OscSplit.oscLe_split | (intros; apply GlobalTheory.OscSplit.oscLe_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationZeroAboveAndDegreeBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationZeroAboveAndDegreeBound
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig sumSmallSpread not_isBig_iff)


open Classical in
theorem card_filter_inPsi_of_finrank {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {F : ℕ} (hF : Module.finrank ℚ E = 2 * F) :
    (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = F := by
  have h := GlobalTheory.LamF.card_psiSet H
  rw [hF] at h
  have h2 : Nat.card (GlobalTheory.LamF.psiSet H) = (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun τ => by
      rw [Finset.mem_filter]; exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩)
  omega


open Classical in
theorem degree_le_of_exponentBound {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {F k m M : ℕ} {Mb Sm : ℝ} {cx : Lt1 Dw → ℕ} (hS : Shape Dw F k m) (hE : ExpBd Dw k cx Mb Sm M) :
    (∑ f : Lt1 Dw, (rk f : ℝ) * (cx f : ℝ)) ≤ F * (Dw.p + Dw.q : ℕ) * Mb + Sm := by
  obtain ⟨hMb, hbig, hsm, -⟩ := hE
  have hF : Module.finrank ℚ E = 2 * F := hS.2.2.2.2.2
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k)]
  refine add_le_add ?_ ?_
  · have hB : ∑ f ∈ Finset.univ.filter (GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k), (cx f : ℝ) ≤ F * Mb := by
      rw [← Finset.sum_fiberwise (Finset.univ.filter (GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k)) (fun f : Lt1 Dw => f.1)]
      calc ∑ τ : E →+* ℂ, ∑ f ∈ (Finset.univ.filter (GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k)).filter (fun f : Lt1 Dw => f.1 = τ), (cx f : ℝ)
          ≤ ∑ τ : E →+* ℂ, if InPsi H τ then Mb else 0 := by
            refine Finset.sum_le_sum fun τ _ => ?_
            split_ifs with hτ
            · have := hbig τ
              rw [Finset.filter_filter]
              push_cast at this
              convert this using 3
            · apply le_of_eq
              apply Finset.sum_eq_zero
              intro f hf
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
              exact absurd (hf.2 ▸ hf.1.1) hτ
        _ = F * Mb := by
            rw [← Finset.sum_filter, Finset.sum_const, card_filter_inPsi_of_finrank H hF, nsmul_eq_mul]
    have hN : ∀ f : Lt1 Dw, (rk f : ℝ) ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := by
      intro f
      have h1 := rk_le f
      have h2 : Dw.mult f.1 ≤ Dw.p + Dw.q := by
        unfold Datum.mult; split_ifs <;> omega
      exact_mod_cast h1.trans h2
    calc ∑ f ∈ Finset.univ.filter (GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k), (rk f : ℝ) * (cx f : ℝ)
        ≤ ∑ f ∈ Finset.univ.filter (GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k), ((Dw.p + Dw.q : ℕ) : ℝ) * (cx f : ℝ) :=
          Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_right (hN f) (Nat.cast_nonneg _)
      _ = ((Dw.p + Dw.q : ℕ) : ℝ) * ∑ f ∈ Finset.univ.filter (GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k), (cx f : ℝ) := by rw [Finset.mul_sum]
      _ ≤ ((Dw.p + Dw.q : ℕ) : ℝ) * (F * Mb) := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg _)
      _ = F * (Dw.p + Dw.q : ℕ) * Mb := by ring
  · have he : ∑ f ∈ Finset.univ.filter (fun f => ¬ GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification.IsBig k f), (rk f : ℝ) * (cx f : ℝ) = (sumSmallSpread k cx : ℝ) := by
      unfold sumSmallSpread
      push_cast
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext f
      simp [not_isBig_iff]
    rw [he]; exact hsm

theorem oscLe_zero_above_and_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], (M < p → OscLe Xo c p cx 0) ∧ OscLe Xo c p cx ((F * (Dw.p + Dw.q : ℕ) * Mb + Sm) / ((p : ℝ) - 1)) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE p _
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  constructor
  · intro hMp la
    refine ⟨0, ?_⟩
    have h := ((GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 (fun _ => 0) (fun _ => 0)
      (fun f => (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).2 (lt_of_le_of_lt (hE.2.2.2 f) hMp))).1
    simpa using h
  · intro la
    refine ⟨0, ?_⟩
    have h := ((GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 (fun _ => 0) (fun f => boundAll p (rk f) (cx f))
      (fun f => (GlobalTheory.T.factorDepth_between_zero_and_bound E H Dw l Xo c p la f (cx f)).1)).1
    have hsum : ∑ f, boundAll p (rk f) (cx f) ≤ (F * (Dw.p + Dw.q : ℕ) * Mb + Sm) / ((p : ℝ) - 1) := by
      unfold boundAll
      rw [← Finset.sum_div]
      exact div_le_div_of_nonneg_right (degree_le_of_exponentBound hS hE) (by linarith)
    intro T io e ho y
    obtain ⟨h1, h2⟩ := h T io e ho y
    refine ⟨by simpa using h1, fun ha => (h2 ha).trans ?_⟩
    simp only [Finset.sum_const_zero, Nat.cast_zero, zero_add]
    exact EReal.coe_le_coe_iff.2 hsum

end GlobalTheory.RefSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationZeroAboveAndDegreeBoundStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthOscillation_zero_above_and_degreeBound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], (M < p → OscLe Xo c p cx 0) ∧ OscLe Xo c p cx ((F * (Dw.p + Dw.q : ℕ) * Mb + Sm) / ((p : ℝ) - 1)) := by
  first | exact @GlobalTheory.RefSum.oscLe_zero_above_and_degree | exact GlobalTheory.RefSum.oscLe_zero_above_and_degree | (intros; apply GlobalTheory.RefSum.oscLe_zero_above_and_degree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeBoundEveryPrime
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.RefSum

theorem oscLe_eOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (vd : ℕ → ℝ) (S R : Finset ℕ), (∀ q, 0 ≤ vd q) → (∀ (q : ℕ) [Fact q.Prime], q ∈ S → UpperTheory.Depth.SplitPlaces q H F (vd q)) → 2 ∈ S → H.d ∈ R → (∀ q : ℕ, q.Prime → q ∉ S → q ∉ R → ¬ (q : ℤ) ∣ discr E) → ∀ (p : ℕ) [Fact p.Prime], OscLe Xo c p cx (eOf F (Dw.p + Dw.q) k m Mb Sm vd M S R p) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE vd S R hvd h2 h2S hdR hR p _
  have hram := GlobalTheory.T.depthOscillation_zero_above_and_degreeBound E H Dw l Xo c F k m M Mb Sm cx hS hE p
  have hMb : 0 ≤ Mb := hE.1
  have hp : p.Prime := Fact.out
  have hp2le : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hF : (0 : ℝ) ≤ F := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hFmMb : (0 : ℝ) ≤ F * m * Mb := by positivity
  unfold eOf
  split_ifs with h1 hS' h3 h4
  · exact hram.1 h1
  · exact GlobalTheory.T.depth_oscillation_le_at_two_cmField E H Dw l Xo c F k m M Mb Sm cx hS hE p (vd p) (hvd p) (h2 p hS')
  · exact hram.2
  all_goals
    have hpM : p ≤ M := Nat.le_of_not_lt h1
    have h2' : p ≠ 2 := fun h => hS' (h ▸ h2S)
    have hpd : ¬ (p : ℤ) ∣ discr E := hR p hp hS' h3
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by
      have : 1 ≤ M := le_trans hp.one_lt.le hpM
      exact_mod_cast this
    have hlog : 0 ≤ Real.logb p M := Real.logb_nonneg (by exact_mod_cast hp.one_lt) hM1
    by_cases hsq : IsSquare (-(H.d : ZMod p))
    · have hd0 : (H.d : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hdv
        have : p = H.d := (Nat.prime_dvd_prime_iff_eq hp H.d_prime).1 hdv
        exact h3 (this ▸ hdR)
      have hs := GlobalTheory.T.depth_oscillation_le_odd_split_unramified_prime E H Dw l Xo c F k m M Mb Sm cx hS hE p h2' hpd ⟨hd0, hsq⟩
      refine OscLe.mono Xo hs ?_
      first
      | (unfold eSmall
         have hA : (F * m * Mb + Sm) / ((p : ℝ) - 1) ≤ (F * m * Mb * (4 + Real.logb p M / 2) + Sm) / ((p : ℝ) - 1) := by
           apply div_le_div_of_nonneg_right _ hp1.le
           nlinarith
         have hB : (0 : ℝ) ≤ F * (m + 1) * ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 * (Real.logb p M + 1) := by positivity
         linarith)
      | (have hA : (F * m * Mb + Sm) / ((p : ℝ) - 1) ≤ (6 * F * m * Mb + Sm) / ((p : ℝ) - 1) := by
           apply div_le_div_of_nonneg_right _ hp1.le
           nlinarith
         linarith)
    · first
      | exact GlobalTheory.T.depthOscillation_le_at_small_odd_inertPrime E H Dw l Xo c F k m M Mb Sm cx hS hE p h2' hpd hsq (by exact_mod_cast hM1)
      | exact GlobalTheory.T.depthOscillation_large_inertPrime E H Dw l Xo c F k m M Mb Sm cx hS hE p hpd hsq (by omega)

end GlobalTheory.RefSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLeBoundEveryPrimeStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthOscillation_le_bound_every_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (vd : ℕ → ℝ) (S R : Finset ℕ), (∀ q, 0 ≤ vd q) → (∀ (q : ℕ) [Fact q.Prime], q ∈ S → UpperTheory.Depth.SplitPlaces q H F (vd q)) → 2 ∈ S → H.d ∈ R → (∀ q : ℕ, q.Prime → q ∉ S → q ∉ R → ¬ (q : ℤ) ∣ discr E) → ∀ (p : ℕ) [Fact p.Prime], OscLe Xo c p cx (eOf F (Dw.p + Dw.q) k m Mb Sm vd M S R p) := by
  first | exact @GlobalTheory.RefSum.oscLe_eOf | exact GlobalTheory.RefSum.oscLe_eOf | (intros; apply GlobalTheory.RefSum.oscLe_eOf <;> assumption)
end
