module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AllGoodPrimeDepthDataExistProof
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GoodPlaceDepthBoundProof
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GoodPrimeWeightHypothesesOfDepthParameters
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameFreeFiniteOrderRuleConstPeriodSpace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthLeafGoodPrimesOfPointData
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlacesMatchCmTypeFrobeniusOfParameters
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComapLiesOver
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobPlace

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem comap_liesOver {E K : Type} [Field E] [Field K] [NumberField K] (f : 𝓞 E →+* 𝓞 K)
    (la : HeightOneSpectrum (𝓞 K)) :
    (la.asIdeal.comap f).LiesOver (Ideal.span {((resCharOf la : ℕ) : ℤ)}) := by
  have hl := Crude.resCharOf_prime la
  have hP := la.isPrime
  have hmax : (Ideal.span {((resCharOf la : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hle : Ideal.span {((resCharOf la : ℕ) : ℤ)} ≤ (la.asIdeal.comap f).under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show f (algebraMap ℤ (𝓞 E) ((resCharOf la : ℕ) : ℤ)) ∈ la.asIdeal
    rw [map_natCast, map_natCast]
    exact Crude.crv_char_mem la
  have hne : (la.asIdeal.comap f).under ℤ ≠ ⊤ := by
    intro h
    apply la.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : ℤ) ∈ (la.asIdeal.comap f).under ℤ := by rw [h]; trivial
    change f (algebraMap ℤ (𝓞 E) 1) ∈ la.asIdeal at h1
    rwa [map_one, map_one] at h1
  exact ⟨hmax.eq_of_le hne hle⟩

theorem card_under {S : Type} [CommRing S] (p : ℕ) (Q : Ideal S) [h : Q.LiesOver (Ideal.span {(p : ℤ)})] :
    Nat.card (ℤ ⧸ Q.under ℤ) = p := by
  rw [← h.over, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

theorem eTau_plOf (D : D7) (z : RPl D.R) :
    ((D.eTau (plOf D z) : D.R.Psi) : D.R.GG) =
      ((if z.1 then -1 else 1, 1), D.R.iota z.2) := by
  unfold plOf
  rw [Equiv.apply_symm_apply]
  cases z.1 <;> rfl

theorem inert_ne {N : NumDatum} {l : ℕ} (h : Inert N l) : l ∉ N.H.small ∧ l ≠ N.q ∧ l ≠ N.d := by
  unfold Inert NumDatum.cls primeClass at h
  refine ⟨fun h2 => ?_, fun hq => ?_, fun hd => ?_⟩
  · rw [if_pos h2] at h
    rcases h with h | h <;> cases h
  · rw [if_pos hq] at h
    split_ifs at h <;> rcases h with h | h <;> cases h
  · rw [if_pos hd] at h
    split_ifs at h <;> rcases h with h | h <;> cases h

theorem gal_step (D : D7) (L : SizeData₂ D) (p : ℕ) [Fact p.Prime] (hI : Inert (numOf D L) p)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) (z : RPl D.R) :
    ((D.eTau (plOf D ((numOf D L).pos p z 1)) : D.R.Psi) : D.R.GG) * D.R.cc =
      ((D.eTau (plOf D z) : D.R.Psi) : D.R.GG) *
        D.host.galE σ := by
  obtain ⟨h2, hq, hd⟩ := inert_ne hI
  have hN : ¬ p ∣ D.host.condN := fun h => by
    rcases (D.host.toHostRaw.dvd_condN_iff_small Fact.out).1 h with h | h | h
    exacts [h2 h, hq h, hd h]
  have hc : p.Coprime D.host.condN := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hN
  have hC := factClassFrob D.R D.host p hN P σ hσ
  have hH : (D.host.galE σ).2 = D.R.iota ((numOf D L).hP p) := by
    have e1 := (D.host.toHostAx.frob_iff p hc P σ).1 hσ
    have e2 : (numOf D L).hP p = D.R.iotaInv (D.host.art (ZMod.unitOfCoprime p hc)).2 := dif_pos hc
    rw [e2, Formalism.HC.Frame.iota_iotaInv]
    exact congrArg Prod.snd e1
  have hcls : (numOf D L).cls p = D.host.cls p := rfl
  have hpos := eTau_plOf D
    (xor z.1 (decide (D.host.cls p = PrimeClass.signal ∧ Odd 1)), z.2 + 1 • (numOf D L).hP p)
  refine (congrArg (· * D.R.cc) hpos).trans ?_
  rw [eTau_plOf]
  refine Prod.ext ?_ ?_
  · rcases hI with h | h
    · rw [hcls] at h
      have h1 := hC.2.2.1 h
      simp only [Prod.fst_mul, h1, h, Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]
      cases z.1 <;> simp
    · rw [hcls] at h
      have h1 := hC.2.1.1 h
      simp only [Prod.fst_mul, h1, h, Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]
      cases z.1 <;> simp
  · simp only [Prod.snd_mul, Formalism.HC.Frame.cc, mul_one, hH]
    rw [Formalism.HC.Frame.iota_add]
    exact congrArg (fun t => D.R.iota z.2 * D.R.iota t) (one_nsmul _)

theorem conj_emb {R : Ranks} (H : Formalism.BasicNotions.Host R) (g g' : R.GG) (σ : H.E ≃ₐ[ℚ] H.E)
    (h : g' * R.cc = g * H.galE σ) (x : H.E) :
    ComplexEmbedding.conjugate (H.emb g') x = H.emb g (σ x) := by
  have hg : ∀ g : R.GG, H.galE (H.sigmaOf g) = g := fun g => MulEquiv.apply_symm_apply _ _
  have he : H.sigmaOf g' * H.conj = H.sigmaOf g * σ := by
    apply H.galE_injective
    rw [H.galE_mul, H.galE_mul, hg, hg, H.galE_conjE, h]
  rw [ComplexEmbedding.conjugate_coe_eq, ← H.conjE_apply (H.emb g') x]
  change H.φ₀ ((H.sigmaOf g' * H.conj) x) = H.φ₀ ((H.sigmaOf g * σ) x)
  rw [he]

theorem frob_place : ∀ (D : D7) (L : SizeData₂ D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (lv : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff lv) (la : HeightOneSpectrum (𝓞 c.F)), Inert (numOf D L) (resCharOf la) → ∀ (z : RPl D.R) (x : 𝓞 D.host.E),
  ∃ y ∈ la.asIdeal, ((y : 𝓞 c.F) : c.F) = embK c (ComplexEmbedding.conjugate (DV.tauEmb D (plOf D ((numOf D L).pos (resCharOf la) z 1)))) x - embK c (DV.tauEmb D (plOf D z)) x ^ resCharOf la := by
  intro D L H lv c la hI z x
  haveI : Fact (resCharOf la).Prime := ⟨Crude.resCharOf_prime la⟩
  obtain ⟨h2, hq, hd⟩ := inert_ne hI
  let f : 𝓞 D.host.E →+* 𝓞 c.F := RingOfIntegers.mapRingHom (embF c (DV.tauEmb D (plOf D z)))
  haveI := la.isPrime
  haveI := comap_liesOver f la
  have hN : ¬ resCharOf la ∣ D.host.condN := fun h => by
    rcases (D.host.toHostRaw.dvd_condN_iff_small Fact.out).1 h with h | h | h
    exacts [h2 h, hq h, hd h]
  obtain ⟨σ, hσ⟩ := (D.host.der.frob (resCharOf la) hN (la.asIdeal.comap f)).1
  have hg := gal_step D L (resCharOf la) hI (la.asIdeal.comap f) σ hσ z
  have h1 := hσ x
  rw [card_under (resCharOf la)] at h1
  refine ⟨_, h1, ?_⟩
  rw [map_sub, map_pow]
  push_cast
  congr 1
  apply Subtype.ext
  rw [embK_coe]
  exact (conj_emb D.host _ _ σ hg (x : D.host.E)).symm

end GlobalTheory.FrobPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlacesMatchCmTypeFrobeniusOfParameters
set_option autoImplicit false

namespace GlobalTheory.GoodDepth

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem placeTie_of_pins : ∀ (D : D7) (L : SizeData₂ D) (T : Core D), T.Q.Pins →
    PlaceTie (numOf D L) T.Q.c (fun z => DV.tauEmb D (plOf D z)) := by
  intro D L T hp
  have hh := hp.1
  refine ⟨?_, ?_, hh.1, D.host.hostE_isGalois, ?_, ?_, ?_⟩
  · intro z z' h
    exact (plOf_bijective_card D).1.1 (D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h)))
  · intro τ
    constructor
    · intro hτ
      have hex : ∃ t : D.what₂.Tau, τ = DV.tauEmb D t := by
        obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 τ
        by_cases hgP : g ∈ D.R.Psi
        · obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 hgP
          exact ⟨t, hg.symm.trans ht⟩
        · exfalso
          have h2 : g * D.R.cc ∈ D.R.Psi := by
            by_contra h
            exact hgP ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g).2 h)
          obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2 h2
          have h3 : DV.tauEmb D t (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hh.2.2.2 t
          rw [← ht, Formalism.L2.Geo.emb_mul_cc_comp, hg, RingHom.comp_apply] at h3
          have h4 : τ (D.host.conj (T.Q.H.rt : D.host.E)) = star (τ (T.Q.H.rt : D.host.E)) := Formalism.MainNotions.WeightFamilies.emb_conj D τ _
          have hτ' : τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hτ
          have hc : (starRingEnd ℂ) T.Q.H.rt0 ≠ T.Q.H.rt0 := by
            intro he
            obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 he
            have hs := T.Q.H.sqrt_neg_disc_sq
            rw [hx] at hs
            have hs' : x ^ 2 = -(T.Q.H.d : ℝ) := by exact_mod_cast hs
            have hd : (0 : ℝ) < T.Q.H.d := by exact_mod_cast T.Q.H.d_prime.pos
            nlinarith [sq_nonneg x]
          apply hc
          calc star T.Q.H.rt0 = star (τ (T.Q.H.rt : D.host.E)) := by rw [hτ']
            _ = τ (D.host.conj (T.Q.H.rt : D.host.E)) := h4.symm
            _ = T.Q.H.rt0 := h3
      obtain ⟨t, ht⟩ := hex
      obtain ⟨z, hz⟩ := (plOf_bijective_card D).1.2 t
      exact ⟨z, by rw [ht, ← hz]⟩
    · rintro ⟨z, rfl⟩
      exact hh.2.2.2 _
  · intro σ τ
    exact D.host.galE_injective (by
      rw [D.host.galE_mul, D.host.galE_mul, mul_comm])
  · intro p hp h2 hq hd
    exact GlobalTheory.GoodDepth.not_dvd_discr_host D.R D.host p hp h2 hq hd
  · intro la hla z x
    exact GlobalTheory.FrobPlace.frob_place D L T.Q.H _ T.Q.c la hla z x

end GlobalTheory.GoodDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlacesMatchCmTypeFrobeniusOfParametersStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaces_match_cmTypeFrobenius : ∀ (D : D7) (L : SizeData₂ D) (T : Core D), T.Q.Pins → PlaceTie (numOf D L) T.Q.c (fun z => DV.tauEmb D (plOf D z)) := by
  first | exact @GlobalTheory.GoodDepth.placeTie_of_pins | exact GlobalTheory.GoodDepth.placeTie_of_pins | (intros; apply GlobalTheory.GoodDepth.placeTie_of_pins <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthTableGoodPrimeLeaf
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalizedLatticeExponentEqRoundedDepthGoodPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalizedLatticeExponentEqRoundedDepthGoodPlace
set_option autoImplicit false

namespace GlobalTheory.GoodDepth

open Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Units

variable {K : Type} [Field K] [NumberField K] [StarRing K] (v : HeightOneSpectrum (𝓞 K))

theorem vwUnit_mul {x y : K} (hx : x ≠ 0 ∧ Formalism.DivisionValues.vw v x = 0) (hy : y ≠ 0 ∧ Formalism.DivisionValues.vw v y = 0) :
    x * y ≠ 0 ∧ Formalism.DivisionValues.vw v (x * y) = 0 :=
  ⟨mul_ne_zero hx.1 hy.1, by rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul v _ _ hx.1 hy.1, hx.2, hy.2, add_zero]⟩

theorem vwUnit_nat {N : ℕ} (hN : ¬ plc v ∣ N) : (N : K) ≠ 0 ∧ Formalism.DivisionValues.vw v (N : K) = 0 := by
  have h0 : N ≠ 0 := by rintro rfl; exact hN (dvd_zero _)
  refine ⟨by exact_mod_cast h0, ?_⟩
  rw [DepthTie.vw_N v N h0, Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd hN]
  simp

theorem vwUnit_pow {x : K} (hx : x ≠ 0 ∧ Formalism.DivisionValues.vw v x = 0) (n : ℕ) :
    x ^ n ≠ 0 ∧ Formalism.DivisionValues.vw v (x ^ n) = 0 := by
  induction n with
  | zero =>
    have := vwUnit_nat v (N := 1) (by simpa using (plc_prime v).ne_one)
    simpa using this
  | succ n ih => rw [pow_succ]; exact vwUnit_mul v ih hx

theorem vwUnit_prime {p : ℕ} (hp : p.Prime) (h : plc v ≠ p) : (p : K) ≠ 0 ∧ Formalism.DivisionValues.vw v (p : K) = 0 :=
  vwUnit_nat v fun hd => h ((Nat.prime_dvd_prime_iff_eq (plc_prime v) hp).1 hd)

theorem vwUnit_factor {x y : K} (hx : IsIntegral ℤ x) (hy : IsIntegral ℤ y)
    (h : x * y ≠ 0 ∧ Formalism.DivisionValues.vw v (x * y) = 0) :
    (x ≠ 0 ∧ Formalism.DivisionValues.vw v x = 0) ∧ (y ≠ 0 ∧ Formalism.DivisionValues.vw v y = 0) := by
  have x0 := left_ne_zero_of_mul h.1
  have y0 := right_ne_zero_of_mul h.1
  have h2 := h.2
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul v _ _ x0 y0] at h2
  have a := DepthTie.vw_nonneg_of_isIntegral v x hx
  have b := DepthTie.vw_nonneg_of_isIntegral v y hy
  exact ⟨⟨x0, by omega⟩, ⟨y0, by omega⟩⟩

end Units

theorem vw_sigAt_good {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dd : DepData E) {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 E) K]
    (hsp : PiSplit (H := H) Dd) (hprime : Dd.Q.g1.Prime ∧ Dd.Q.g2.Prime ∧ Dd.Q.q1.Prime ∧ Dd.Q.dd.Prime)
    (v : HeightOneSpectrum (𝓞 K)) (h2 : plc v ∉ Dd.Q.sm) (hq : plc v ≠ Dd.Q.q1) (hd : plc v ≠ Dd.Q.dd)
    (hg1 : plc v ≠ Dd.Q.g1) (hg2 : plc v ≠ Dd.Q.g2) (Dw' : Datum H) (j : ℕ) :
    Formalism.DivisionValues.vw v (sigAt (Dw := Dw') (H := H) (LL := K) Dd j) = 0 := by
  obtain ⟨e0, e1, -⟩ := DepthTie.alg_pi_ne_zero (K := K) Dd hsp ⟨hprime.1, hprime.2.1⟩
  have u1 := vwUnit_prime v hprime.1 hg1
  have u2 := vwUnit_prime v hprime.2.1 hg2
  have uq := vwUnit_prime v hprime.2.2.1 hq
  have ud := vwUnit_prime v hprime.2.2.2 hd
  have ut : ∀ a : ℕ → ℕ, ((∏ p ∈ Dd.Q.sm.filter Nat.Prime, p ^ a p : ℕ) : K) ≠ 0 ∧
      Formalism.DivisionValues.vw v ((∏ p ∈ Dd.Q.sm.filter Nat.Prime, p ^ a p : ℕ) : K) = 0 := fun a => vwUnit_nat v fun hdv => by
    obtain ⟨p, hp, h⟩ := (Prime.dvd_finsetProd_iff (plc_prime v).prime _).1 hdv
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
    exact h2 ((Nat.prime_dvd_prime_iff_eq (plc_prime v) hp2).1 ((plc_prime v).dvd_of_dvd_pow h) ▸ hp1)
  obtain ⟨a0, b0⟩ := vwUnit_factor v (DepthTie.isIntegral_alg _) (DepthTie.isIntegral_alg _) (e0 ▸ u1)
  obtain ⟨a1, b1⟩ := vwUnit_factor v (DepthTie.isIntegral_alg _) (DepthTie.isIntegral_alg _) (e1 ▸ u2)
  rw [DepthTie.sigAt_eq]
  refine (vwUnit_mul v ?_ ?_).2
  · unfold nnKAt nnOf
    rw [Fin.prod_univ_two]
    exact vwUnit_mul v (vwUnit_mul v (vwUnit_pow v b0 _) (vwUnit_pow v a0 _))
      (vwUnit_mul v (vwUnit_pow v b1 _) (vwUnit_pow v a1 _))
  · unfold DepthTie.Nsig DepPage.Z1 DepPage.q
    simp only [Nat.cast_mul, Nat.cast_pow]
    exact vwUnit_mul v (vwUnit_pow v (vwUnit_mul v u1 u2) _)
      (vwUnit_mul v (vwUnit_mul v (ut _) (vwUnit_pow v uq _)) (vwUnit_pow v ud _))

theorem normalizedLattice_exponent_eq_roundedDepth_goodPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (Dw : ℕ → Datum H) (Xo : ∀ j, Moduli (Dw j) lv) (c : Coeff lv) [StarRing (𝓞 E)] (Dd : DepData E)
  (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ),
  (∀ v j, O.E v j = EAt (Xo := Xo (ι j)) (c := c) (LL := K) Dd v (ι j)) → (∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) →
  (O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) → PiSplit (H := H) Dd → LeafPage O →
  ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J), ¬ (plc v ∈ O.sm ∨ plc v = O.q1 ∨ plc v = O.dd ∨ plc v = O.g1 ∨ plc v = O.g2) →
    O.e0 v j ≤ (Dd.Q.T : ℝ) * ((nuWAt (Xo := Xo (ι j)) Dd (placeBelow (K := c.F) v) (ι j)).toReal / (ramOverZ (placeBelow (K := c.F) v) : ℝ)) + 1 ∧
    (nuWAt (Xo := Xo (ι j)) Dd (placeBelow (K := c.F) v) (ι j) = 0 → O.e0 v j = 0) := by
  intro E _ _ _ H lv Dw Xo c _ Dd K _ _ _ _ _ _ Bs Df S P _ _ oc O ι hE hσ hpr hsp hPg v j hv
  obtain ⟨hprime, -, -⟩ := DepthTie.page_facts Dd O hPg hpr
  obtain ⟨p1, p2, p3, p4, p5⟩ := hpr
  rw [p1, p2, p3, p4, p5] at hv
  simp only [not_or] at hv
  obtain ⟨h2, hq, hd, hg1, hg2⟩ := hv
  have hs := vw_sigAt_good Dd hsp hprime v h2 hq hd hg1 hg2 (Dw (ι j)) (ι j)
  obtain ⟨o1, o2⟩ := DepthTie.one_le_ramOver_below (F := c.F) v
  have hW : 0 ≤ (nuWAt (Xo := Xo (ι j)) (c := c) Dd (placeBelow (K := c.F) v) (ι j)).toReal :=
    EReal.toReal_nonneg (le_max_left _ _)
  have hram : ¬ Dd.Q.IsRam (plc v) := by
    unfold DepPage.IsRam; tauto
  have hbad : ¬ Dd.Q.IsBad (plc v) := by
    unfold DepPage.IsBad; tauto
  have r1 : (1 : ℝ) ≤ (ramOver (K := c.F) v : ℝ) := by exact_mod_cast o1
  have r2 : (1 : ℝ) ≤ (ramOverZ (placeBelow (K := c.F) v) : ℝ) := by exact_mod_cast o2
  have key : O.e0 v j = (⌈(ramOverZ (placeBelow (K := c.F) v) : ℝ) * (Dd.Q.T : ℝ) *
      ((nuWAt (Xo := Xo (ι j)) (c := c) Dd (placeBelow (K := c.F) v) (ι j)).toReal /
        (ramOverZ (placeBelow (K := c.F) v) : ℝ))⌉ : ℝ) / (ramOverZ (placeBelow (K := c.F) v) : ℝ) := by
    unfold OnObj.e0
    rw [hE v j, hσ v j, hs, DepthTie.ramw_eq_below (F := c.F) v]
    unfold EAt expE DepPage.eLam nuStarAt DepPage.nuN DepPage.cP
    simp only []
    rw [DepthTie.resChar_below (F := c.F) v, if_neg hg1, if_neg hg2, if_neg hram, if_neg hbad]
    simp only [Nat.cast_zero, add_zero, Int.cast_zero, sub_zero, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
    rw [mul_div_mul_left _ _ (by linarith)]
    congr 1
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.ceil_nonneg (by positivity))]
  refine ⟨?_, fun h0 => ?_⟩
  · rw [key, div_le_iff₀ (by linarith)]
    refine (Int.ceil_lt_add_one _).le.trans ?_
    nlinarith
  · rw [key, h0]
    simp

end GlobalTheory.GoodDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalizedLatticeExponentEqRoundedDepthGoodPlaceStatement
open Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.onObj_exponent_eq_rounded_depth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (Dw : ℕ → Datum H) (Xo : ∀ j, Moduli (Dw j) lv) (c : Coeff lv) [StarRing (𝓞 E)] (Dd : DepData E)
  (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ),
  (∀ v j, O.E v j = EAt (Xo := Xo (ι j)) (c := c) (LL := K) Dd v (ι j)) → (∀ v j, O.σ v j = sigAt (Dw := Dw (ι j)) (H := H) (LL := K) Dd (ι j)) →
  (O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm) → PiSplit (H := H) Dd → LeafPage O →
  ∀ (v : HeightOneSpectrum (𝓞 K)) (j : Bs.J), ¬ (plc v ∈ O.sm ∨ plc v = O.q1 ∨ plc v = O.dd ∨ plc v = O.g1 ∨ plc v = O.g2) →
    O.e0 v j ≤ (Dd.Q.T : ℝ) * ((nuWAt (Xo := Xo (ι j)) Dd (placeBelow (K := c.F) v) (ι j)).toReal / (ramOverZ (placeBelow (K := c.F) v) : ℝ)) + 1 ∧
    (nuWAt (Xo := Xo (ι j)) Dd (placeBelow (K := c.F) v) (ι j) = 0 → O.e0 v j = 0) := by
  first | exact @GlobalTheory.GoodDepth.normalizedLattice_exponent_eq_roundedDepth_goodPlace | exact GlobalTheory.GoodDepth.normalizedLattice_exponent_eq_roundedDepth_goodPlace | (intros; apply GlobalTheory.GoodDepth.normalizedLattice_exponent_eq_roundedDepth_goodPlace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumLevelTailMulLogPrimesLe
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumLevelTailMulLogPrimesLe
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral

namespace GlobalTheory.TailPrimeSum

theorem thBounds : ThBounds := by
  intro k l hk hl
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨-, h3, hlt, he⟩ := GlobalTheory.LevelsOrbits.thlEq k l hk hl
  refine ⟨?_, ?_, fun h => ?_⟩
  · rw [he]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) h3)
  · rw [he]
    exact inv_strictAnti₀ (by positivity) hlt
  · have h1 : (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ 3 := by
      calc (k : ℝ) ^ ((3 : ℝ) / 2) < ((l : ℝ) ^ 2) ^ ((3 : ℝ) / 2) :=
            Real.rpow_lt_rpow (by positivity) h (by norm_num)
        _ = (l : ℝ) ^ 3 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
            norm_num
    have h2 : i0 k l ≤ 3 := Nat.sInf_le ⟨⟨1, by norm_num⟩, le_rfl, h1⟩
    rw [he, le_antisymm h2 h3]

lemma sum_log_le (Q : Finset ℕ) (x : ℝ) (hx : 0 ≤ x) (hQ : ∀ p ∈ Q, p.Prime)
    (hle : ∀ p ∈ Q, (p : ℝ) ≤ x) : ∑ p ∈ Q, Real.log p ≤ 3 / 2 * x := by
  have h1 : ∑ p ∈ Q, Real.log p ≤ Chebyshev.theta x := by
    unfold Chebyshev.theta
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_)
      (fun p _ _ => Real.log_natCast_nonneg p)
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨(hQ p hp).pos, Nat.le_floor (hle p hp)⟩, hQ p hp⟩
  have h2 := Chebyshev.theta_le_log4_mul_x hx
  have h3 : Real.log 4 ≤ 3 / 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  have := mul_le_mul_of_nonneg_right h3 hx
  linarith

lemma tail_le (N : ℕ) : ∀ (Q : Finset ℕ) (Y : ℝ), 0 < Y → (∀ p ∈ Q, p.Prime) →
    (∀ p ∈ Q, Y < p ∧ (p : ℝ) ≤ 2 ^ N * Y) →
    ∑ p ∈ Q, ((p : ℝ) ^ 3)⁻¹ * Real.log p ≤ 4 / Y ^ 2 := by
  induction N with
  | zero =>
    intro Q Y hY _ h
    have : Q = ∅ := Finset.eq_empty_of_forall_notMem fun p hp => by
      have := h p hp
      simp only [pow_zero, one_mul] at this
      linarith [this.1, this.2]
    rw [this, Finset.sum_empty]
    positivity
  | succ N ih =>
    intro Q Y hY hQ h
    rw [← Finset.sum_filter_add_sum_filter_not Q (fun p : ℕ => (p : ℝ) ≤ 2 * Y)]
    have h1 : ∑ p ∈ Q.filter (fun p : ℕ => (p : ℝ) ≤ 2 * Y), ((p : ℝ) ^ 3)⁻¹ * Real.log p
        ≤ (Y ^ 3)⁻¹ * (3 / 2 * (2 * Y)) := by
      calc _ ≤ ∑ p ∈ Q.filter (fun p : ℕ => (p : ℝ) ≤ 2 * Y), (Y ^ 3)⁻¹ * Real.log p := by
            refine Finset.sum_le_sum fun p hp => ?_
            have := (h p (Finset.mem_filter.1 hp).1).1
            refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
            exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hY.le this.le 3)
        _ ≤ _ := by
            rw [← Finset.mul_sum]
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact sum_log_le _ _ (by positivity) (fun p hp => hQ p (Finset.mem_filter.1 hp).1)
              (fun p hp => (Finset.mem_filter.1 hp).2)
    have h2 := ih (Q.filter (fun p : ℕ => ¬ (p : ℝ) ≤ 2 * Y)) (2 * Y) (by positivity)
      (fun p hp => hQ p (Finset.mem_filter.1 hp).1) (fun p hp => by
        obtain ⟨a, b⟩ := Finset.mem_filter.1 hp
        refine ⟨not_le.1 b, ?_⟩
        have := (h p a).2
        rw [pow_succ, mul_assoc] at this
        exact this)
    have h3 : (Y ^ 3)⁻¹ * (3 / 2 * (2 * Y)) + 4 / (2 * Y) ^ 2 = 4 / Y ^ 2 := by
      field_simp
      ring
    linarith

theorem main : Formalism.UnitaryBoundIntegral.ThBounds ∧ ∀ (k : ℕ) (Q : Finset ℕ), 1 ≤ k → (∀ p ∈ Q, p.Prime) →
    ∑ p ∈ Q, thl k p * Real.log p ≤ 20 / k := by
  refine ⟨thBounds, fun k Q hk hQ => ?_⟩
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set Y : ℝ := Real.sqrt k with hYdef
  have hY1 : 1 ≤ Y := Real.one_le_sqrt.2 hk'
  have hY : 0 < Y := by linarith
  have hY2 : Y ^ 2 = k := Real.sq_sqrt (by positivity)
  have hY3 : (k : ℝ) ^ ((3 : ℝ) / 2) = Y ^ 3 := by
    rw [← hY2, ← Real.rpow_natCast, ← Real.rpow_mul hY.le, ← Real.rpow_natCast]
    norm_num
  rw [← Finset.sum_filter_add_sum_filter_not Q (fun p : ℕ => (p : ℝ) ≤ Y)]
  have h1 : ∑ p ∈ Q.filter (fun p : ℕ => (p : ℝ) ≤ Y), thl k p * Real.log p
      ≤ (Y ^ 3)⁻¹ * (3 / 2 * Y) := by
    calc _ ≤ ∑ p ∈ Q.filter (fun p : ℕ => (p : ℝ) ≤ Y), (Y ^ 3)⁻¹ * Real.log p := by
          refine Finset.sum_le_sum fun p hp => ?_
          refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
          rw [← hY3]
          exact (thBounds k p hk (hQ p (Finset.mem_filter.1 hp).1).two_le).2.1.le
      _ ≤ _ := by
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact sum_log_le _ _ hY.le (fun p hp => hQ p (Finset.mem_filter.1 hp).1)
            (fun p hp => (Finset.mem_filter.1 hp).2)
  have h2 : ∑ p ∈ Q.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Y), thl k p * Real.log p ≤ 4 / Y ^ 2 := by
    calc _ ≤ ∑ p ∈ Q.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Y), ((p : ℝ) ^ 3)⁻¹ * Real.log p := by
          refine Finset.sum_le_sum fun p hp => ?_
          refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg p)
          exact (thBounds k p hk (hQ p (Finset.mem_filter.1 hp).1).two_le).1
      _ ≤ _ := by
          refine tail_le (Q.sup id) _ Y hY (fun p hp => hQ p (Finset.mem_filter.1 hp).1)
            (fun p hp => ?_)
          obtain ⟨a, b⟩ := Finset.mem_filter.1 hp
          refine ⟨not_le.1 b, ?_⟩
          have h3 : p ≤ Q.sup id := Finset.le_sup (f := id) a
          have h4 : p ≤ 2 ^ (Q.sup id) := h3.trans Nat.lt_two_pow_self.le
          have h5 : (p : ℝ) ≤ 2 ^ (Q.sup id) := by exact_mod_cast h4
          exact h5.trans (le_mul_of_one_le_right (by positivity) hY1)
  have h3 : (Y ^ 3)⁻¹ * (3 / 2 * Y) + 4 / Y ^ 2 = (11 / 2) / Y ^ 2 := by
    field_simp
    ring
  have h4 : (11 / 2 : ℝ) / Y ^ 2 ≤ 20 / k := by
    rw [hY2]
    gcongr
    norm_num
  linarith

end GlobalTheory.TailPrimeSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumLevelTailMulLogPrimesLeStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_level_tail_mul_log_primes_le : Formalism.UnitaryBoundIntegral.ThBounds ∧ ∀ (k : ℕ) (Q : Finset ℕ), 1 ≤ k → (∀ p ∈ Q, p.Prime) → ∑ p ∈ Q, thl k p * Real.log p ≤ 20 / k := by
  first | exact @GlobalTheory.TailPrimeSum.main | exact GlobalTheory.TailPrimeSum.main | (intros; apply GlobalTheory.TailPrimeSum.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthTableGoodPrimeLeaf
set_option autoImplicit false

namespace GlobalTheory.GoodDepth

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond

theorem thl_nonneg_leaf (k l : ℕ) : 0 ≤ thl k l := by
  unfold thl
  apply Real.sSup_nonneg
  rintro t ⟨i, -, -, -, rfl⟩
  positivity

theorem err_mono_leaf (Cc C k m f w Se Se' th l T X : ℝ) (hCc : 0 < Cc) (hC : Cc ≤ C) (hk : 1 ≤ k) (hm : 1 ≤ m) (hf : 8 ≤ f)
    (hw : 0 ≤ w) (hS : Se' ≤ Se) (hS0 : 0 ≤ Se) (hth : 0 ≤ th) (hl : 0 ≤ l) :
    Cc * (Real.log k * m * w / l + f * k * Se' / l + k * th * w + if X < l then k * w / l ^ 2 else 0) ≤
      C * (Real.log k * m * w + f * k * Se) / l + C * k * w * th + T * 0 + if X < l then C * k * w / l ^ 2 else 0 := by
  have hlog : 0 ≤ Real.log k := Real.log_nonneg hk
  have hk0 : 0 ≤ k := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hf0 : 0 ≤ f := by linarith
  have h1 : f * k * Se' / l ≤ f * k * Se / l :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS (by positivity)) hl
  have hI : 0 ≤ (if X < l then k * w / l ^ 2 else 0) := by split_ifs <;> positivity
  have hR : C * (Real.log k * m * w + f * k * Se) / l + C * k * w * th + T * 0 + (if X < l then C * k * w / l ^ 2 else 0) =
      C * (Real.log k * m * w / l + f * k * Se / l + k * th * w + if X < l then k * w / l ^ 2 else 0) := by
    split_ifs <;> ring
  rw [hR]
  have h0 : 0 ≤ Real.log k * m * w / l + f * k * Se / l + k * th * w + if X < l then k * w / l ^ 2 else 0 := by
    positivity
  calc _ ≤ Cc * (Real.log k * m * w / l + f * k * Se / l + k * th * w + if X < l then k * w / l ^ 2 else 0) :=
        mul_le_mul_of_nonneg_left (by linarith) hCc.le
    _ ≤ _ := mul_le_mul_of_nonneg_right hC h0

theorem leafGood : LeafGoodSt := by
  intro C1 hC1
  obtain ⟨Cc, hCc, hnu⟩ := GlobalTheory.T.goodPlaceDepthBound_proof C1 hC1
  refine ⟨max Cc 20, ?_⟩
  intro E _ _ _ H lv Dw Xo c _ Dd K _ _ _ _ _ _ Bs Df S P _ _ oc O ι Nm N pl hC0 hE hσ hT hpr hsp hlev hstar hEx hPk hPl hj
    hN hPg tF tP
  have hCcC : Cc ≤ O.C := le_trans (le_max_left _ _) hC0
  have h20 : (20 : ℝ) ≤ O.C := le_trans (le_max_right _ _) hC0
  have hPg' := hPg
  obtain ⟨hC, hk, hm, hf, -, hSc, heta, -, -, -, pg1, pg2, -⟩ := hPg'
  have hb : 0 < O.b := Real.exp_pos _
  have hkN : 1 ≤ N.R.k := by
    have := hN.k_eq ▸ hk
    exact_mod_cast this
  refine ⟨fun l => ⟨?_, ?_⟩, fun Q hQ => ?_, fun Q _ => ?_, fun w _ hw j => ?_⟩
  · rw [hN.th_eq]; exact thl_nonneg_leaf _ _
  · rw [hN.ad_eq]
  · simp only [hN.th_eq]
    refine (GlobalTheory.T.sum_level_tail_mul_log_primes_le.2 N.R.k Q hkN hQ).trans ?_
    rw [hN.k_eq]
    exact div_le_div_of_nonneg_right h20 (Nat.cast_nonneg _)
  · simp only [hN.ad_eq, zero_mul, Finset.sum_const_zero, mul_zero]
    have : 0 ≤ O.m := by linarith
    have : 0 ≤ O.C := by linarith
    positivity
  · obtain ⟨j1, j2, jp, jq, jD, jG⟩ := hj j
    obtain ⟨t1, t2, t3, t4, t5⟩ := tP
    have hp : (Formalism.EigenvalueLevelCeiling.plc w).Prime := Formalism.EigenvalueLevelCeiling.plc_prime w
    have hw' := hw
    simp only [not_or] at hw'
    obtain ⟨n2, nq, nd, ng1, ng2⟩ := hw'
    have hF : Nm.F0 w j = N.FjP (ι j) (Formalism.EigenvalueLevelCeiling.plc w) := tF w j
    have key : ∀ v : HeightOneSpectrum (𝓞 K), Formalism.EigenvalueLevelCeiling.plc v = Formalism.EigenvalueLevelCeiling.plc w →
        O.e0 v j ≤ Nm.F0 w j + O.aE j (Formalism.EigenvalueLevelCeiling.plc w) + 1 ∧ (O.Y < (Formalism.EigenvalueLevelCeiling.plc w : ℝ) → O.e0 v j = 0) := by
      intro v hv
      have hr : resCharOf (placeBelow (K := c.F) v) = Formalism.EigenvalueLevelCeiling.plc w := (DepthTie.resChar_below (F := c.F) v).trans hv
      obtain ⟨e1, e2⟩ := GlobalTheory.T.onObj_exponent_eq_rounded_depth E H lv Dw Xo c Dd K Bs Df S P oc O ι hE hσ hpr hsp hPg v j (by rw [hv]; exact hw)
      have hM : ¬ Formalism.EigenvalueLevelCeiling.plc w ∣ lv.M := by
        intro hd
        have hl : (lv.M : ℕ) = Dd.Q.g1 * Dd.Q.g2 := hlev
        rw [hl, ← hpr.1, ← hpr.2.1] at hd
        rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
        · exact ng1 ((Nat.prime_dvd_prime_iff_eq hp pg1).1 h)
        · exact ng2 ((Nat.prime_dvd_prime_iff_eq hp pg2).1 h)
      obtain ⟨-, b1, b2⟩ := hnu E H (Dw (ι j)) lv (Xo (ι j)) c hstar (hEx j) (hPk j) N (ι j) pl (Dd.aL (ι j)) (Dd.nW (ι j))
        Dd.Q.T O.b O.L (O.wt j) j1 j2 hPl jp jq jD jG (hN.wt_sum j) (hN.wt_b j) (placeBelow (K := c.F) v)
        (by rw [hr, ← t5]; exact n2) (by rw [hr, ← t3]; exact nq) (by rw [hr, ← t4]; exact nd) (by rw [hr, ← t1]; exact ng1)
        (by rw [hr, ← t2]; exact ng2) (by rw [hr]; exact hM)
      rw [hr] at b1 b2
      constructor
      · have hm' := err_mono_leaf Cc O.C O.k O.m O.f (O.wt j) O.Se (N.Sc + N.eta) (O.th (Formalism.EigenvalueLevelCeiling.plc w))
          (Formalism.EigenvalueLevelCeiling.plc w) O.T O.X2 hCc hCcC hk hm hf (hb.le.trans (hN.wt_b j)) hN.Se_ge (add_nonneg hSc heta)
          (by rw [hN.th_eq]; exact thl_nonneg_leaf _ _) (Nat.cast_nonneg _)
        rw [← hN.th_eq, ← hN.k_eq, ← hN.m_eq, ← hN.f_eq, ← hN.depthNumbers_threshold_eq] at b1
        unfold nuWAt at e1
        unfold OnObj.aE OnObj.A1 OnObj.Akw
        rw [hF, hN.ad_eq]
        linarith
      · intro hY
        apply e2
        apply b2
        have h1 := hN.DF_ge j
        have h0 : (0 : ℝ) ≤ O.DF := le_trans (Nat.cast_nonneg _) h1
        have h2 : O.DF ≤ O.Y := by
          unfold OnObj.Y
          nlinarith
        have : ((DF (Dw (ι j)) (Dd.aL (ι j)) : ℕ) : ℝ) < (Formalism.EigenvalueLevelCeiling.plc w : ℝ) := lt_of_le_of_lt (h1.trans h2) hY
        exact_mod_cast this
    have k1 := key w rfl
    have k2 := key (Formalism.DivisionValues.conjPl w) (Formalism.EigenvalueLevelCeiling.plc_conjPl w)
    refine ⟨fun _ => ⟨k1.1, k2.1⟩, fun hY => ⟨k1.2 hY, k2.2 hY, ?_⟩⟩
    rw [hF]
    obtain ⟨θ0, hdeg⟩ := jG.deg
    exact (GlobalTheory.T.forcedContent_bounds_programmeValue_goodPrime N (ι j) _ hp (t5 ▸ n2) (t3 ▸ nq) (t4 ▸ nd) (t1 ▸ ng1) (t2 ▸ ng2) (fun z => (hdeg.w_pos z).le) jG.ratio).1

end GlobalTheory.GoodDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthTableGoodPrimeLeafStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthTable_goodPrimeLeaf : LeafGoodSt := by
  first | exact @GlobalTheory.GoodDepth.leafGood | exact GlobalTheory.GoodDepth.leafGood | (intros; apply GlobalTheory.GoodDepth.leafGood <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthLeafGoodPrimesOfPointData
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

namespace GlobalTheory.GoodDepth

theorem numOf_sizes_le (D : D7) (L : SizeData₂ D) (hk : (1 : ℝ) ≤ D.R.k) (hm : (1 : ℝ) ≤ D.R.m) :
    (numOf D L).Sc + (numOf D L).eta ≤ L.Sc + L.etaSz := by
  have hS := L.Sc_pos
  have hE := L.Sc_eq
  have he := L.etaSz_pos
  have hDel : (0 : ℝ) ≤ (D.s.Del : ℝ) := by
    by_contra hneg
    push Not at hneg
    have : (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  have h1 : (numOf D L).Sc ≤ L.Sc := by
    show (D.R.k : ℝ) * (4 * ((⌊(D.s.Del : ℝ)⌋₊ : ℕ) : ℝ)) ≤ L.Sc
    rw [hE]
    have := Nat.floor_le hDel
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (numOf D L).eta ≤ L.etaSz := by
    show (D.R.m : ℝ) * ((⌊LevelStarExponents.h0 L⌋₊ : ℕ) : ℝ) ≤ L.etaSz
    have hm0 : (0 : ℝ) < D.R.m := by linarith
    have e : L.etaSz = D.R.m * LevelStarExponents.h0 L := by unfold LevelStarExponents.h0; field_simp
    have h0 : 0 ≤ LevelStarExponents.h0 L := by unfold LevelStarExponents.h0; positivity
    rw [e]
    exact mul_le_mul_of_nonneg_left (Nat.floor_le h0) hm0.le
  linarith

theorem card_RPl (R : Ranks) : Fintype.card (RPl R) = R.f := by
  simp [RPl, Ranks.f, Ranks.n, R.card_A]


set_option maxHeartbeats 1000000 in
theorem leafGood_run : ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), LawsM T → ∀ (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (Nm : IndefNum Bs),
  RunTie T EX Tp hK O ι → (∀ j, PkgSt (T.Q.Xo (ι j)) T.Q.c) → C0 ≤ oc.C → LeafPage O → LeafSizes O → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  DepthCond.ContentEqualsDatumContent Nm (numOf D L) ι → LeafDepthGood Nm O := by
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.depthTable_goodPrimeLeaf 100 (by norm_num)
  refine ⟨C0, ?_⟩
  intro D L Pm Tp hK T hT EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι Nm R hPk hC hPg hSz hCn hx5 hx hkb tF
  have hb : O.b = L.sc.b := by
    unfold OnObj.b OnObj.xe Scale.b Scale.L
    rw [R.x_eq, R.eps_eq]
  have hL : O.L = L.sc.L := by
    unfold OnObj.L
    rw [hb, Scale.b, Real.log_exp]
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hk1 : (1 : ℝ) ≤ D.R.k := R.k_eq ▸ hPg.2.1
  have hm1 : (1 : ℝ) ≤ D.R.m := R.m_eq ▸ hPg.2.2.1
  have hf8 : (8 : ℝ) ≤ D.R.f := R.f_eq ▸ hPg.2.2.2.1
  have hlog : Real.log D.R.k ≤ L.sc.L := by
    have := hSz.2.2.2.2.2.2.1
    rwa [R.k_eq, hL] at this
  refine hC0 D.host.E T.Q.H T.Q.l T.Q.Dw T.Q.Xo T.Q.c (depOf T EX Tp hK) K Bs Df S P oc O ι Nm (numOf D L)
    (fun z => DV.tauEmb D (plOf D z)) hC R.E_eq R.σ_eq R.T_eq ⟨R.jets_eq_fact, R.g2_eq, R.cmQuadraticForm_eq_alternatingForm, R.dd_eq, R.sm_eq⟩
    (piSplit_depDataOf ..) (levelQ_depDataOf _ _ _ _ _ _ _ _ _ hT) R.star_eq
    (fun j => (GlobalTheory.T.exists_integral_chart_integral_framed_point _ _ _ _ _ _).2.1 R.star_eq) hPk (GlobalTheory.T.realPlaces_match_cmTypeFrobenius D L T hT.pins) (fun j => ?_) ?_ hPg tF
    ⟨R.jets_eq_fact, R.g2_eq, R.cmQuadraticForm_eq_alternatingForm, R.dd_eq, R.sm_eq⟩
  · have hj := R.inR j
    have hd := hT.pins.2.2.2 _ hj
    refine ⟨hj.1, hj.2, hd.1, hd.2.1, fun τ i i' h => (dom_wtA (lR Tp hK (ι j))).1 τ h, ?_⟩
    rw [hb, hL]
    exact GlobalTheory.T.goodPrimeWeightHypotheses_of_depthParameters D L Pm Tp hK T hT.pins hCn hx5 hx hkb hlog _ hj
  · refine ⟨R.k_eq, R.m_eq, R.f_eq, ?_, R.depthNumbers_threshold_eq, R.th_eq, R.ad_eq, fun j => ?_, fun j => ?_, fun j => ?_⟩
    · unfold OnObj.Se
      rw [R.Sc_eq, R.eta_eq]
      exact numOf_sizes_le D L hk1 hm1
    · rw [R.wt_eq]
      have h := (GlobalTheory.T.firstRows_bound_and_sizes_bounds D L Pm Tp hK (ι j) (R.inR j) hx hkb).2
      calc (∑ z, (numOf D L).w (ι j) z) ≤ ∑ _z : RPl D.R, 2 * L.sc.b := Finset.sum_le_sum fun z _ => (h z).2
        _ = 2 * (D.R.f : ℝ) * L.sc.b := by
          rw [Finset.sum_const, Finset.card_univ, card_RPl, nsmul_eq_mul]; ring
    · rw [R.wt_eq, hb]; nlinarith
    · have h := (GlobalTheory.T.weightExponents_embeddings_degree D T.Q hT.pins (ι j) (R.inR j) (lR Tp hK (ι j))).1
      have h2 := R.DF_ge j
      rw [← h] at h2
      exact h2

end GlobalTheory.GoodDepth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthLeafGoodPrimesOfPointDataStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLeaf_goodPrimes_of_point_data : ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), LawsM T → ∀ (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (Nm : IndefNum Bs),
  RunTie T EX Tp hK O ι → (∀ j, PkgSt (T.Q.Xo (ι j)) T.Q.c) → C0 ≤ oc.C → LeafPage O → LeafSizes O → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  DepthCond.ContentEqualsDatumContent Nm (numOf D L) ι → LeafDepthGood Nm O := by
  first | exact @GlobalTheory.GoodDepth.leafGood_run | exact GlobalTheory.GoodDepth.leafGood_run | (intros; apply GlobalTheory.GoodDepth.leafGood_run <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthTableGoodPrimesOfChartForm
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

namespace GlobalTheory

theorem leafDepthGood_of_chartForm : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), LawsM T → ∀ (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (Nm : IndefNum Bs),
  RunTie T EX Tp hK O ι → C0 ≤ oc.C → LeafPage O → LeafSizes O → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  DepthCond.ContentEqualsDatumContent Nm (numOf D L) ι → LeafDepthGood Nm O := by
  intro hUp
  obtain ⟨C0, h⟩ := GlobalTheory.T.depthLeaf_goodPrimes_of_point_data
  refine ⟨C0, ?_⟩
  intro D L Pm Tp hK T hT EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι Nm hR
  exact h D L Pm Tp hK T hT EX K Bs Df S P oc O ι Nm hR
    (fun j => GlobalTheory.T.allGoodPrimeDepthDataExist_proof hUp _ _ _ _ (T.Q.Xo (ι j)) T.Q.c)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthTableGoodPrimesOfChartFormStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthTable_goodPrimes_of_chartForm : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), LawsM T → ∀ (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (Nm : IndefNum Bs),
  RunTie T EX Tp hK O ι → C0 ≤ oc.C → LeafPage O → LeafSizes O → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  DepthCond.ContentEqualsDatumContent Nm (numOf D L) ι → LeafDepthGood Nm O := by
  first | exact @GlobalTheory.leafDepthGood_of_chartForm | exact GlobalTheory.leafDepthGood_of_chartForm | (intros; apply GlobalTheory.leafDepthGood_of_chartForm <;> assumption)
end
