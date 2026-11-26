module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfOpenCompact
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohTopEuler
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIdeleCircle

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsPrimeMemAsIdeal
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaD
namespace Bl.FirstLemmaD

theorem goal1 :
  ∀ {F : Type} [inst : Field.{0} F] [NumberField.{0} F]
  (v : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} F)),
  Exists.{1} fun (p : Nat) ↦
    And (Nat.Prime p) (Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} v) (Nat.cast.{0} p)) := by
  intro F _ _ v
  have := v.isPrime
  have hne : v.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) ≠ ⊥ :=
    fun h => v.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)
  have hpr : (v.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers F))).IsPrime :=
    Ideal.comap_isPrime _ _
  obtain ⟨x, hx, hxp⟩ := hpr.exists_mem_prime_of_ne_bot hne
  refine ⟨x.natAbs, Int.prime_iff_natAbs_prime.mp hxp, ?_⟩
  obtain ⟨c, hc⟩ : x ∣ (x.natAbs : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
  have hmem : ((x.natAbs : ℤ)) ∈ v.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) := by
    rw [hc]
    exact Ideal.mul_mem_right c _ hx
  rw [Ideal.mem_comap, map_natCast] at hmem
  exact hmem

end Bl.FirstLemmaD
end

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel Formalism.GaloisCohomology NumberField IsDedekindDomain Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem exists_prime_mem_asIdeal {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal :=
  _root_.Bl.FirstLemmaD.goal1 v

theorem finCd2_GK (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hK : FiniteDimensional ℚ_[p] K) (R : Type) [CommRing R] (M : Type) [AddCommGroup M]
    [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation R (GK p K) M) (hrho : ContAction rho) :
    Finite (H0 rho) ∧ Finite (H1 rho) ∧ Finite (H2 rho) ∧
      ∀ n, 3 ≤ n → Subsingleton (Hn rho n) := by
  obtain ⟨hsep, _, _, hloc, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcField p K hK
  have : CharZero K := algebraRat.charZero K
  obtain ⟨A, _, e, he⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcRep (GK p K) R M rho hrho
  have : Finite A := Finite.of_equiv _ e.toEquiv
  have hn : ((Nat.card A : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  obtain ⟨e0, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc0 (GK p K) R M rho A e he
  obtain ⟨e1, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 (GK p K) R M rho A e he
  obtain ⟨e2, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 (GK p K) R M rho A e he
  have := finite_cohomology_localField A hn 0
  have := finite_cohomology_localField A hn 1
  have := finite_cohomology_localField A hn 2
  refine ⟨Finite.of_equiv _ e0.symm.toEquiv, Finite.of_equiv _ e1.symm.toEquiv,
    Finite.of_equiv _ e2.symm.toEquiv, fun n h => ?_⟩
  obtain ⟨en⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcn (GK p K) R M rho A e he n
  have := subsingleton_cohomology_localField A hn n h
  exact en.toEquiv.subsingleton

theorem localFiniteness : ReciprocityTheory.Gal.LocalFiniteness := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A rho v _ hA hc
  obtain ⟨p, hp, hpv⟩ := exists_prime_mem_asIdeal v
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hK, e, he, he', -⟩ := GlobalTheory.DecLocal.exists_mulEquiv_cyc F Ω p v A hpv hA
  let E : GK p K ≃ₜ* Dec (F := F) A :=
    { e.symm with continuous_toFun := he', continuous_invFun := he }
  have h : ReciprocityTheory.Neutral.Bridge.FinCd2 (rho.comp (E : GK p K →* Dec (F := F) A)) :=
    finCd2_GK p K hK _ M _ (ReciprocityTheory.Neutral.Bridge.contAction_comp E hc)
  exact ReciprocityTheory.Neutral.Bridge.FinCd2.of_comp E h

end GlobalTheory.CompanionTheory.Hypotheses₂
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CardH1EqCardH0MulCardH2
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel Formalism.ConjugateSelfDual

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler


open PositivityTheory.LocalTateOrthogonality.Gcoh in
theorem card_H1_eq_card_H0_mul_card_H2 (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hK : FiniteDimensional ℚ_[p] K) (l : ℕ) [hl : Fact l.Prime] (hlp : l ≠ p) (r : ℕ) (M : Type)
    [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK p K) M) (hrho : ContAction rho) :
    Nat.card (H1 rho) = Nat.card (H0 rho) * Nat.card (H2 rho) := by
  obtain ⟨hsep, v, t, hloc, hcard⟩ := gcField p K hK
  obtain ⟨A, hA, e, he⟩ := gcRep _ _ M rho hrho
  obtain ⟨e0, -⟩ := gc0 _ _ M rho A e he
  obtain ⟨e1, -⟩ := gc1 _ _ M rho A e he
  obtain ⟨e2, -⟩ := gc2 _ _ M rho A e he
  obtain ⟨k, hk⟩ := exists_card_eq_pow l r M
  have hfA : Finite A := Finite.of_equiv M e.toEquiv
  have hA' : Nat.card A = l ^ k := (Nat.card_congr e.toEquiv).symm.trans hk
  have : CharZero K := algebraRat.charZero K
  have hne : ((Nat.card A : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hE := @card_cohomology_mul_div_eq K (PadicAlgCl p) _ v t hloc _ _ hsep A hA hfA hne
  have hfin := @finite_cohomology_localField K (PadicAlgCl p) _ v t hloc _ _ hsep A hA hfA hne 1
  have hcop : Nat.Coprime (Nat.card A) p := by
    rw [hA']
    exact Nat.Coprime.pow_left k ((Nat.coprime_primes hl.out Fact.out).2 hlp)
  have hu : IsUnit ((Nat.card A : ℕ) : 𝒪[K]) := by
    obtain ⟨a, b, hab⟩ := hcop.cast (R := 𝒪[K])
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
    · exact isUnit_of_mul_isUnit_right h
    · exfalso
      have h3 := hcard 1
      rw [pow_one, card_quotient_span_eq_one_of_isUnit (isUnit_of_mul_isUnit_right h)] at h3
      have h4 : 1 < p ^ Module.finrank ℚ_[p] K :=
        Nat.one_lt_pow Module.finrank_pos.ne' (Fact.out : p.Prime).one_lt
      omega
  rw [card_quotient_span_eq_one_of_isUnit hu, Nat.cast_one, inv_one] at hE
  rw [Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv]
  have hp1 : (Nat.card (cohomology A 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_mul]
  exact ((div_eq_one_iff_eq hp1).1 hE).symm

theorem exists_prime_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hmax := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 F ⧸ v.asIdeal)
  refine ⟨p, CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) p, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem localEulerChar_holds : ReciprocityTheory.Gal.LocalEulerChar := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A rho v hr hA hc
  have hval : ∀ (p : ℕ), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → A.valuation (p : Ω) < 1 := fun p hp => by
    simpa using (hA (p : 𝓞 F)).2 hp
  refine ⟨fun hl => ?_, fun hl => ?_⟩
  · obtain ⟨K, hK, i0, -, -, hdeg⟩ := GlobalTheory.DecLocal.decEquiv (p := l) (F := F) A (hval l hl)
    let i : ↥(Dec (F := F) A) ≃ₜ* Formalism.GaloisCohomology.GK l K := i0
    let rhoK : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K) M := rho.comp i.symm.toMulEquiv.toMonoidHom
    have hcomp : ∀ h m, rhoK (i h) m = rho h m := fun h m =>
      congrArg (fun g => rho g m) (i.symm_apply_apply h)
    have hcK : ContAction rhoK := hc.comp' i.symm.continuous
    have h := PositivityTheory.LocalTateOrthogonality.Gcoh.top_euler l K hK r M rhoK hr hcK
    rw [hdeg v hA] at h
    rw [← Nat.card_congr (ReciprocityTheory.Neutral.Bridge.equivH0OfIso i rhoK rho hcomp).toEquiv,
      ← Nat.card_congr (ReciprocityTheory.Neutral.Bridge.equivH1OfIso i rhoK rho hcomp).toEquiv,
      ← Nat.card_congr (ReciprocityTheory.Neutral.Bridge.equivH2OfIso i rhoK rho hcomp).toEquiv]
    exact h
  · obtain ⟨p, hp, hpv⟩ := exists_prime_mem v
    haveI : Fact p.Prime := ⟨hp⟩
    have hlp : l ≠ p := fun h => hl (h ▸ hpv)
    obtain ⟨K, hK, i0, -, -, -⟩ := GlobalTheory.DecLocal.decEquiv (p := p) (F := F) A (hval p hpv)
    let i : ↥(Dec (F := F) A) ≃ₜ* Formalism.GaloisCohomology.GK p K := i0
    let rhoK : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK p K) M := rho.comp i.symm.toMulEquiv.toMonoidHom
    have hcomp : ∀ h m, rhoK (i h) m = rho h m := fun h m =>
      congrArg (fun g => rho g m) (i.symm_apply_apply h)
    have hcK : ContAction rhoK := hc.comp' i.symm.continuous
    have h := card_H1_eq_card_H0_mul_card_H2 p K hK l hlp r M rhoK hcK
    rw [← Nat.card_congr (ReciprocityTheory.Neutral.Bridge.equivH0OfIso i rhoK rho hcomp).toEquiv,
      ← Nat.card_congr (ReciprocityTheory.Neutral.Bridge.equivH1OfIso i rhoK rho hcomp).toEquiv,
      ← Nat.card_congr (ReciprocityTheory.Neutral.Bridge.equivH2OfIso i rhoK rho hcomp).toEquiv]
    exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalAnnihilatorSelfDualVolume
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalAnnihilatorSelfDualVolume
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

theorem psiF_eq_one_of_int_of_vanish : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ),
    IsCharAF F ψ → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ c : Af F,
      (∀ v, c v ∈ v.adicCompletionIntegers F) → (∀ v ∈ T, c v = 0) → psiF ψ c = 1 := by
  intro F _ _ ψ hψ
  classical
  have hcont : Continuous (psiF ψ) := by
    have h : Continuous (fun y : Af F => ψ ((0 : InfiniteAdeleRing F), y)) :=
      hψ.1.comp (continuous_const.prodMk continuous_id)
    exact h
  have hW : psiF ψ ⁻¹' Metric.ball (1 : ℂ) (1 / 2) ∈ nhds (0 : Af F) := by
    refine hcont.continuousAt.preimage_mem_nhds ?_
    rw [psiF_zero]
    exact Metric.ball_mem_nhds _ (by norm_num)
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hc : Continuous (RestrictedProduct.structureMap R A Filter.cofinite) :=
    RestrictedProduct.isEmbedding_structureMap.continuous
  have hp : (RestrictedProduct.structureMap R A Filter.cofinite) ⁻¹' (psiF ψ ⁻¹' Metric.ball (1 : ℂ) (1 / 2)) ∈
      nhds (fun v => (0 : A v)) :=
    hc.continuousAt.preimage_mem_nhds hW
  rw [nhds_pi, Filter.mem_pi] at hp
  obtain ⟨I, hI, t, ht, hsub⟩ := hp
  refine ⟨hI.toFinset, fun c hint hT => ?_⟩
  let H : AddSubgroup (Af F) :=
    { carrier := {y | (∀ v, y v ∈ v.adicCompletionIntegers F) ∧ ∀ v ∈ hI.toFinset, y v = 0}
      add_mem' := by
        intro a b ha hb
        refine ⟨fun v => ?_, fun v hv => ?_⟩
        · change a v + b v ∈ v.adicCompletionIntegers F
          exact add_mem (ha.1 v) (hb.1 v)
        · change a v + b v = 0
          rw [ha.2 v hv, hb.2 v hv, add_zero]
      zero_mem' := ⟨fun v => zero_mem _, fun v _ => rfl⟩
      neg_mem' := by
        intro a ha
        refine ⟨fun v => ?_, fun v hv => ?_⟩
        · change -(a v) ∈ v.adicCompletionIntegers F
          exact neg_mem (ha.1 v)
        · change -(a v) = 0
          rw [ha.2 v hv, neg_zero] }
  have hs : ∀ y ∈ H, ‖psiF ψ y - 1‖ < 1 / 2 := by
    intro y hy
    have hmem : (fun v => (⟨y v, hy.1 v⟩ : A v)) ∈
        (RestrictedProduct.structureMap R A Filter.cofinite) ⁻¹' (psiF ψ ⁻¹' Metric.ball (1 : ℂ) (1 / 2)) := by
      refine hsub fun v hv => ?_
      have h0 : (⟨y v, hy.1 v⟩ : A v) = (0 : A v) :=
        Subtype.ext (hy.2 v (by simpa using hv))
      rw [h0]
      exact mem_of_mem_nhds (ht v)
    have he : RestrictedProduct.structureMap R A Filter.cofinite (fun v => (⟨y v, hy.1 v⟩ : A v)) = y :=
      by ext v; rfl
    have h2 : psiF ψ y ∈ Metric.ball (1 : ℂ) (1 / 2) := by
      rw [← he]
      exact hmem
    rw [Metric.mem_ball, dist_eq_norm] at h2
    exact h2
  exact char_eq_one_of_near H (psiF ψ) (psiF_zero ψ) (psiF_add ψ) hs (x := c) ⟨hint, hT⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalAnnihilatorSelfDualVolumeStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_character_trivial_almost_everywhere : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ c : Af F, (∀ v, c v ∈ v.adicCompletionIntegers F) → (∀ v ∈ T, c v = 0) → psiF ψ c = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.psiF_eq_one_of_int_of_vanish | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.psiF_eq_one_of_int_of_vanish | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.psiF_eq_one_of_int_of_vanish <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideDescendsFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideDescendsFinite
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfEx

theorem exists_bumps_inf : (∀ (P : Type) [Fintype P] (a : P → ℝ), (∀ w, a w ≠ 0) → ∃ g : ℕ → (P → ℝ) → ℝ, (∀ k, Continuous (g k) ∧ HasCompactSupport (g k) ∧ (∀ x, 0 ≤ g k x) ∧ 0 < ∫ x, g k x) ∧ (∀ k, tsupport (g k) ⊆ Metric.closedBall 0 (1 / ((k : ℝ) + 1))) ∧ ∀ k, Integrable (fun t : P → ℝ => ∫ x, (g k x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * t w) : ℝ) : ℂ)))) → ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ laminf : Measure (Ainf F), laminf.IsAddHaarMeasure → ∃ ρ : ℕ → Ainf F → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂laminf) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : Ainf F)).smallSets ∧ ∀ k, Integrable (fouInf ψ laminf (ρ k)) laminf := by
  intro hreal F _ _ hF ψ hψ laminf hH
  haveI := hF
  classical
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have he : Continuous (GlobalTheory.CompanionTheory.SW.RealCoord.coord F) := (GlobalTheory.CompanionTheory.SW.RealCoord.isHomeomorph_coord F).continuous
  have he' : Continuous (GlobalTheory.CompanionTheory.SW.RealCoord.coord F).symm := (GlobalTheory.CompanionTheory.SW.RealCoord.coordHomeo F).symm.continuous
  have hpc : Continuous (psiInf F ψ) := hψ.1.comp (continuous_id.prodMk continuous_const)
  obtain ⟨a, ha, hχ⟩ := GlobalTheory.CompanionTheory.SW.SdPi.exists_form (GlobalTheory.CompanionTheory.SW.RealCoord.coord F) he' (psiInf F ψ) hpc (fun _ => hψ.2.1 _)
    (fun u v => by
      simp only [psiInf, map_add (f := _), ← AddChar.map_add_eq_mul]
      congr 1
      exact Prod.ext rfl (add_zero _).symm)
    (GlobalTheory.T.localComponents_nontrivial_adelic_character F ψ hψ).2.2
  obtain ⟨g, hg1, hg2, hg3⟩ := hreal (InfinitePlace F) a ha
  set e := GlobalTheory.CompanionTheory.SW.RealCoord.coord F with hedef
  set E := GlobalTheory.CompanionTheory.SW.RealCoord.coordHomeo F with hEdef
  have hEe : ∀ y, E y = e y := fun _ => rfl
  haveI : (laminf.map e).IsAddHaarMeasure :=
    AddEquiv.isAddHaarMeasure_map laminf e.toAddEquiv he he'
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, laminf.map e = c • (volume : Measure (InfinitePlace F → ℝ)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : laminf.map e = 0 := by simpa using hc
    exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := laminf.map e)).open_pos Set.univ isOpen_univ
      Set.univ_nonempty (by simp [h0])
  have hme : MeasurableEmbedding e := E.measurableEmbedding
  have hint : ∀ f : (InfinitePlace F → ℝ) → ℂ, ∫ y, f (e y) ∂laminf = (c : ℝ) • ∫ u, f u := by
    intro f
    rw [← hme.integral_map (μ := laminf) f, hc, integral_smul_nnreal_measure]
    rfl
  have hintR : ∀ f : (InfinitePlace F → ℝ) → ℝ, ∫ y, f (e y) ∂laminf = (c : ℝ) * ∫ u, f u := by
    intro f
    rw [← hme.integral_map (μ := laminf) f, hc, integral_smul_nnreal_measure]
    rfl
  refine ⟨fun k y => g k (e y), fun k => ⟨(hg1 k).1.comp he, (hg1 k).2.1.comp_homeomorph E, fun y => (hg1 k).2.2.1 _, ?_⟩, ?_, fun k => ?_⟩
  · rw [hintR]
    have : (0 : ℝ) < c := by exact_mod_cast pos_iff_ne_zero.2 hc0
    exact mul_pos this (hg1 k).2.2.2
  · rw [Filter.tendsto_smallSets_iff]
    intro U hU
    have hV : E.symm ⁻¹' U ∈ nhds (0 : InfinitePlace F → ℝ) := by
      apply E.symm.continuous.continuousAt.preimage_mem_nhds
      have : E.symm 0 = 0 := e.symm.map_zero
      rwa [this]
    obtain ⟨ε, hε, hεV⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hV
    have hlim : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hlim.eventually (ge_mem_nhds hε)] with k hk y hy
    have h1 : e y ∈ tsupport (g k) := tsupport_comp_subset_preimage (g k) he hy
    have h3 : e y ∈ E.symm ⁻¹' U := hεV (Metric.closedBall_subset_closedBall hk (hg2 k h1))
    have h5 : E.symm (e y) = y := E.symm_apply_apply y
    rw [Set.mem_preimage, h5] at h3
    exact h3
  · have hfou : ∀ t, fouInf ψ laminf (fun y => g k (e y)) t = (c : ℝ) • ∫ x, (g k x : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * e t w) : ℝ) : ℂ)) := by
      intro t
      have h6 := hint (fun u => (g k u : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (u w * e t w) : ℝ) : ℂ)))
      rw [← h6, fouInf]
      simp only [hχ, map_mul, Pi.mul_apply]
    have hG : Integrable (fun t => ∫ x, (g k x : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * e t w) : ℝ) : ℂ))) laminf := by
      have h7 : Integrable (fun t : InfinitePlace F → ℝ => ∫ x, (g k x : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * t w) : ℝ) : ℂ))) (laminf.map e) := by
        rw [hc]
        exact (hg3 k).smul_measure_nnreal
      exact hme.integrable_map_iff.1 h7
    rw [funext hfou]
    exact hG.smul (c : ℝ)

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfEx
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideDescendsFiniteStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.number_field_approximate_identity : (∀ (P : Type) [Fintype P] (a : P → ℝ), (∀ w, a w ≠ 0) → ∃ g : ℕ → (P → ℝ) → ℝ, (∀ k, Continuous (g k) ∧ HasCompactSupport (g k) ∧ (∀ x, 0 ≤ g k x) ∧ 0 < ∫ x, g k x) ∧ (∀ k, tsupport (g k) ⊆ Metric.closedBall 0 (1 / ((k : ℝ) + 1))) ∧ ∀ k, Integrable (fun t : P → ℝ => ∫ x, (g k x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (x w * t w) : ℝ) : ℂ)))) → ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ laminf : Measure (Ainf F), laminf.IsAddHaarMeasure → ∃ ρ : ℕ → Ainf F → ℝ, (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂laminf) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : Ainf F)).smallSets ∧ ∀ k, Integrable (fouInf ψ laminf (ρ k)) laminf := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfEx.exists_bumps_inf | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfEx.exists_bumps_inf | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.InfEx.exists_bumps_inf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CmHeckeCharacterInfinityType
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CmHeckeCharacterInfinityType
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeArch

open InfinitePlace.Completion

variable {E : Type} [Field E] [NumberField E]

theorem infiniteEmbedding_eq (w : InfinitePlace E) (a : (w.Completion)ˣ) :
    (infiniteEmbedding w a : IdeleGroup E) = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w a := by
  classical
  refine Units.ext (Prod.ext ?_ rfl)
  show Pi.mulSingle w (a : w.Completion) = Pi.mulSingle w (a : w.Completion)
  congr!

theorem component_on_field (χ : HChar E) (hu : IsUnitary χ) {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (n : I → ℤ)
    (hn : Formalism.L2.Host.HChar.HasInf χ φ n) (i : I) (k : Eˣ) :
    (((toHecke χ hu).infiniteComponent (InfinitePlace.mk (φ i)) (Formalism.L2.Host.atInf _ k) : Circle) : ℂ) =
      (φ i (k : E) / ((‖φ i (k : E)‖ : ℝ) : ℂ)) ^ n i := by
  have h := (GlobalTheory.InfTypeLocal.infType_iff_local E I φ hφ χ.1 χ.2.1 n).1 hn i k
  rw [HeckeCharacter.infiniteComponent_apply, coe_toIdele, infiniteEmbedding_eq]
  exact h

theorem denseRange_atInf_place (w : InfinitePlace E) : DenseRange (Formalism.L2.Host.atInf w) :=
  ((Function.surjective_eval w).denseRange.comp (GlobalTheory.InfTypeLocal.denseRange_atInf E)
    (continuous_apply w) : DenseRange _)

theorem component_eq (χ : HChar E) (hu : IsUnitary χ) {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (n : I → ℤ)
    (hn : Formalism.L2.Host.HChar.HasInf χ φ n) (i : I)
    (e : (InfinitePlace.mk (φ i)).Completion →+* ℂ) (hec : Continuous e)
    (he : ∀ k : E, e (algebraMap E _ k) = φ i k) (a : ((InfinitePlace.mk (φ i)).Completion)ˣ) :
    (((toHecke χ hu).infiniteComponent (InfinitePlace.mk (φ i)) a : Circle) : ℂ) =
      (e a / ((‖e a‖ : ℝ) : ℂ)) ^ n i := by
  have h1 : Continuous fun u : ((InfinitePlace.mk (φ i)).Completion)ˣ => e u :=
    hec.comp Units.continuous_val
  have h2 : ∀ u : ((InfinitePlace.mk (φ i)).Completion)ˣ, e u ≠ 0 := fun u =>
    (map_ne_zero _).2 u.ne_zero
  have h3 : ∀ u : ((InfinitePlace.mk (φ i)).Completion)ˣ, ((‖e u‖ : ℝ) : ℂ) ≠ 0 := fun u => by
    exact_mod_cast norm_ne_zero_iff.2 (h2 u)
  have key : (fun u : ((InfinitePlace.mk (φ i)).Completion)ˣ =>
      (((toHecke χ hu).infiniteComponent (InfinitePlace.mk (φ i)) u : Circle) : ℂ)) =
      fun u : ((InfinitePlace.mk (φ i)).Completion)ˣ => (e u / ((‖e u‖ : ℝ) : ℂ)) ^ n i := by
    refine (denseRange_atInf_place _).equalizer ?_ ?_ ?_
    · exact continuous_subtype_val.comp (map_continuous _)
    · exact (h1.div (Complex.continuous_ofReal.comp h1.norm) h3).zpow₀ _
        fun u => Or.inl (div_ne_zero (h2 u) (h3 u))
    · funext k
      show _ = (e (algebraMap E _ (k : E)) / ((‖e (algebraMap E _ (k : E))‖ : ℝ) : ℂ)) ^ n i
      rw [he]
      exact component_on_field χ hu hφ n hn i k
  exact congrFun key a

theorem conj_div_norm {z : ℂ} (hz : z ≠ 0) :
    (starRingEnd ℂ) z / ((‖z‖ : ℝ) : ℂ) = (z / ((‖z‖ : ℝ) : ℂ))⁻¹ := by
  have h0 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  rw [inv_div, div_eq_div_iff h0 hz, Complex.conj_mul']
  ring

theorem params (χ : HChar E) (hu : IsUnitary χ) {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (n : I → ℤ)
    (hn : Formalism.L2.Host.HChar.HasInf χ φ n) (i : I) (hc : (InfinitePlace.mk (φ i)).IsComplex) :
    (toHecke χ hu).infiniteTau (InfinitePlace.mk (φ i)) = 0 ∧
      ((toHecke χ hu).infiniteWeight (InfinitePlace.mk (φ i))).natAbs = (n i).natAbs := by
  set w := InfinitePlace.mk (φ i) with hw
  set T := toHecke χ hu with hT
  have hnr : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.2 hc
  set e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hc with he
  have hec : Continuous e.symm := (isometryEquivComplexOfIsComplex hc).symm.continuous
  set ψ : ℂˣ →ₜ* Circle := (T.infiniteComponent w).comp (unitsContinuousHom e.symm hec) with hψ
  obtain ⟨p, -, huniq⟩ := existsUnique_complexUnits_circle ψ
  have hι : ∀ z : ℂˣ, extensionEmbedding w ((unitsContinuousHom e.symm hec z : (w.Completion)ˣ) : w.Completion) = z :=
    fun z => e.apply_symm_apply (z : ℂ)
  have hnorm : ∀ z : ℂˣ, ‖((unitsContinuousHom e.symm hec z : (w.Completion)ˣ) : w.Completion)‖ = ‖(z : ℂ)‖ := fun z => by
    rw [← hι z]
    exact ((isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _).symm
  have h1 : ∀ z : ℂˣ, (ψ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ (T.infiniteWeight w, 2 * T.infiniteTau w).1 *
      ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((((T.infiniteWeight w, 2 * T.infiniteTau w).2 : ℝ) : ℂ) * Complex.I) := fun z => by
    have hpos : 0 < ‖(z : ℂ)‖ := norm_pos_iff.2 z.ne_zero
    show ((T.infiniteComponent w (unitsContinuousHom e.symm hec z) : Circle) : ℂ) = _
    rw [HeckeCharacter.infiniteComponent_eq, hι, hnorm, InfinitePlace.mult, if_neg hnr,
      ofReal_pow_cpow hpos]
    congr 2
    push_cast
    ring
  have h2 : ∃ s : ℤ, s.natAbs = (n i).natAbs ∧ ∀ z : ℂˣ, (ψ z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ (s, (0 : ℝ)).1 *
      ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((((s, (0 : ℝ)).2 : ℝ) : ℂ) * Complex.I) := by
    have h0 : ∀ k : E, extensionEmbedding w (algebraMap E _ k) = w.embedding k := fun k => by
      rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
        Algebra.algebraMap_self_apply, extensionEmbedding_coe]
      rfl
    have hcont := (isometry_extensionEmbedding w).continuous
    rcases InfinitePlace.embedding_mk_eq (φ i) with h | h
    · refine ⟨n i, rfl, fun z => ?_⟩
      have := component_eq χ hu hφ n hn i (extensionEmbedding w) hcont
        (fun k => by rw [h0, hw, h]) (unitsContinuousHom e.symm hec z)
      show ((T.infiniteComponent w (unitsContinuousHom e.symm hec z) : Circle) : ℂ) = _
      rw [this, hι]
      simp
    · refine ⟨-n i, by simp, fun z => ?_⟩
      have := component_eq χ hu hφ n hn i ((starRingEnd ℂ).comp (extensionEmbedding w))
        (Complex.continuous_conj.comp hcont)
        (fun k => by
          rw [RingHom.comp_apply, h0, hw, h]
          simp) (unitsContinuousHom e.symm hec z)
      show ((T.infiniteComponent w (unitsContinuousHom e.symm hec z) : Circle) : ℂ) = _
      rw [this, RingHom.comp_apply, hι, Complex.norm_conj, conj_div_norm z.ne_zero, inv_zpow, ← zpow_neg]
      simp
  obtain ⟨s, hs, h2⟩ := h2
  have e1 := huniq _ h1
  have e2 := huniq _ h2
  have e3 := e1.trans e2.symm
  have e4 : T.infiniteWeight w = s := congrArg Prod.fst e3
  have e5 : 2 * T.infiniteTau w = 0 := congrArg Prod.snd e3
  exact ⟨by linarith, by rw [e4, hs]⟩

theorem infiniteParams_of_hasInf : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (χ : HChar E) (hu : IsUnitary χ) (n : I → ℤ), Formalism.L2.Host.HChar.HasInf χ φ n → ∀ i : I, (toHecke χ hu).infiniteTau (InfinitePlace.mk (φ i)) = 0 ∧ ((toHecke χ hu).infiniteWeight (InfinitePlace.mk (φ i))).natAbs = (n i).natAbs := by
  intro E _ _ _ I _ φ hφ χ hu n hn i
  exact params χ hu (GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hφ) n hn i
    (IsTotallyComplex.isComplex _)

end GlobalTheory.CompanionTheory.HeckeArch
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CmHeckeCharacterInfinityTypeStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_hecke_character_infinity_type : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (χ : HChar E) (hu : IsUnitary χ) (n : I → ℤ), Formalism.L2.Host.HChar.HasInf χ φ n → ∀ i : I, (toHecke χ hu).infiniteTau (InfinitePlace.mk (φ i)) = 0 ∧ ((toHecke χ hu).infiniteWeight (InfinitePlace.mk (φ i))).natAbs = (n i).natAbs := by
  first | exact @GlobalTheory.CompanionTheory.HeckeArch.infiniteParams_of_hasInf | exact GlobalTheory.CompanionTheory.HeckeArch.infiniteParams_of_hasInf | (intros; apply GlobalTheory.CompanionTheory.HeckeArch.infiniteParams_of_hasInf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HaarIntegralIntegersFiniteSum
section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HaarIntegralIntegersFiniteSum
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

open MeasureTheory

namespace GlobalTheory.CompanionTheory.PeriodicInt

variable {E : Type} [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)}

theorem valued_algebraMap (x : E) :
    Valued.v (algebraMap E (v.adicCompletion E) x) = v.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem valued_int_le_one (a : 𝓞 E) :
    Valued.v (algebraMap E (v.adicCompletion E) (a : E)) ≤ 1 := by
  rw [valued_algebraMap]
  exact v.valuation_le_one a

theorem valued_le_one_of_mem_valBall {m : ℕ} {x : v.adicCompletion E}
    (h : x ∈ valBall (v.adicCompletion E) (m : ℤ)) : Valued.v x ≤ 1 := by
  refine (mem_valBall_iff_valued.1 h).trans ?_
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem exists_int_close (m : ℕ) {y : v.adicCompletion E} (hy : Valued.v y ≤ 1) :
    ∃ a : 𝓞 E, y - algebraMap E (v.adicCompletion E) (a : E) ∈
      valBall (v.adicCompletion E) (m : ℤ) := by
  have hopen : IsOpen {z : v.adicCompletion E | y - z ∈ valBall (v.adicCompletion E) (m : ℤ)} :=
    (isOpen_valBall (m : ℤ)).preimage (continuous_const.sub continuous_id)
  obtain ⟨x, hx⟩ := (v.denseRange_algebraMap E).exists_mem_open hopen
    ⟨y, by simp [zero_mem]⟩
  have hx' : y - algebraMap E (v.adicCompletion E) x ∈ valBall (v.adicCompletion E) (m : ℤ) := hx
  have h1 : Valued.v (algebraMap E (v.adicCompletion E) x) ≤ 1 := by
    have e : algebraMap E (v.adicCompletion E) x =
        y - (y - algebraMap E (v.adicCompletion E) x) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le hy (valued_le_one_of_mem_valBall hx'))
  rw [valued_algebraMap] at h1
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer h1
    (Units.mk0 _ (WithZero.exp_ne_zero (a := -(m : ℤ))))
  rw [Units.val_mk0] at ha
  refine ⟨a, ?_⟩
  have e : y - algebraMap E (v.adicCompletion E) (a : E) =
      (y - algebraMap E (v.adicCompletion E) x) +
        algebraMap E (v.adicCompletion E) (x - (a : E)) := by
    rw [map_sub]; ring
  rw [e]
  refine add_mem hx' (mem_valBall_iff_valued.2 ?_)
  rw [valued_algebraMap, Valuation.map_sub_swap]
  exact ha.le

theorem sub_mem_pow_of_close {m : ℕ} {a b : 𝓞 E}
    (h : algebraMap E (v.adicCompletion E) (a : E) - algebraMap E (v.adicCompletion E) (b : E) ∈
      valBall (v.adicCompletion E) (m : ℤ)) : a - b ∈ v.asIdeal ^ m := by
  have h1 := mem_valBall_iff_valued.1 h
  rw [← map_sub, valued_algebraMap] at h1
  rw [← v.intValuation_le_pow_iff_mem, ← v.valuation_of_algebraMap (K := E)]
  simpa using h1

theorem close_of_sub_mem_pow {m : ℕ} {a b : 𝓞 E} (h : a - b ∈ v.asIdeal ^ m) :
    algebraMap E (v.adicCompletion E) (a : E) - algebraMap E (v.adicCompletion E) (b : E) ∈
      valBall (v.adicCompletion E) (m : ℤ) := by
  rw [mem_valBall_iff_valued, ← map_sub, valued_algebraMap]
  exact valuation_sub_le h

theorem integral_eq_finsum : ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (m : ℕ) (g : v.adicCompletion E → ℂ), (∀ y, 1 < Valued.v y → g y = 0) → (∀ y h : v.adicCompletion E, Valued.v h ≤ WithZero.exp (-(m : ℤ)) → g (y + h) = g y) → ∫ y, g y ∂haarIntegers (v.adicCompletion E) = (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℂ))⁻¹ * ∑ᶠ r : 𝓞 E ⧸ v.asIdeal ^ m, g (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) := by
  intro E _ _ v m g h0 hp
  classical
  have : Finite (𝓞 E ⧸ v.asIdeal ^ m) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ v.ne_bot)
  have := Fintype.ofFinite (𝓞 E ⧸ v.asIdeal ^ m)
  let a : (𝓞 E ⧸ v.asIdeal ^ m) → v.adicCompletion E := fun r =>
    algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)
  let S : (𝓞 E ⧸ v.asIdeal ^ m) → Set (v.adicCompletion E) := fun r =>
    (fun y => y + (-a r)) ⁻¹' (valBall (v.adicCompletion E) (m : ℤ) : Set (v.adicCompletion E))
  have memS : ∀ r y, y ∈ S r ↔ y - a r ∈ valBall (v.adicCompletion E) (m : ℤ) := fun r y => by
    simp only [S, Set.mem_preimage, SetLike.mem_coe, sub_eq_add_neg]
  have hSm : ∀ r, MeasurableSet (S r) := fun r =>
    ((isOpen_valBall (m : ℤ)).preimage (continuous_id.add continuous_const)).measurableSet
  have hB : (haarIntegers (v.adicCompletion E)).real
      (valBall (v.adicCompletion E) (m : ℤ) : Set (v.adicCompletion E)) =
      (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℝ))⁻¹ := by
    rw [measureReal_def, haarIntegers_valBall, residueCard_adicCompletion, ENNReal.coe_toReal,
      NNReal.coe_zpow, NNReal.coe_natCast, zpow_neg, zpow_natCast]
    push_cast
    rfl
  have hSμ : ∀ r, (haarIntegers (v.adicCompletion E)).real (S r) =
      (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℝ))⁻¹ := fun r => by
    rw [← hB, measureReal_def, measureReal_def]
    exact congrArg ENNReal.toReal (measure_preimage_add_right _ _ _)
  have hfin : ∀ r, haarIntegers (v.adicCompletion E) (S r) ≠ ⊤ := fun r => by
    have : haarIntegers (v.adicCompletion E) (S r) =
        haarIntegers (v.adicCompletion E)
          (valBall (v.adicCompletion E) (m : ℤ) : Set (v.adicCompletion E)) :=
      measure_preimage_add_right _ _ _
    rw [this, haarIntegers_valBall]
    exact ENNReal.coe_ne_top
  have hdecomp : ∀ y, g y = ∑ r, (S r).indicator (fun _ => g (a r)) y := by
    intro y
    by_cases hy : Valued.v y ≤ 1
    · obtain ⟨b, hb⟩ := exists_int_close (v := v) m hy
      set r : 𝓞 E ⧸ v.asIdeal ^ m := Ideal.Quotient.mk _ b with hr
      have hclose : a r - algebraMap E (v.adicCompletion E) (b : E) ∈
          valBall (v.adicCompletion E) (m : ℤ) :=
        close_of_sub_mem_pow (Ideal.Quotient.eq.1 (by rw [Ideal.Quotient.mk_out]))
      have hyr : y ∈ S r := by
        rw [memS]
        have e : y - a r = (y - algebraMap E (v.adicCompletion E) (b : E)) -
            (a r - algebraMap E (v.adicCompletion E) (b : E)) := by ring
        rw [e]
        exact sub_mem hb hclose
      rw [Finset.sum_eq_single r, Set.indicator_of_mem hyr]
      · have := hp (a r) (y - a r) (mem_valBall_iff_valued.1 ((memS r y).1 hyr))
        rwa [add_sub_cancel] at this
      · intro r' _ hne
        refine Set.indicator_of_notMem (fun hyr' => hne ?_) _
        have h1 := sub_mem ((memS r y).1 hyr) ((memS r' y).1 hyr')
        have e : y - a r - (y - a r') = a r' - a r := by ring
        rw [e] at h1
        have h2 := sub_mem_pow_of_close h1
        have h3 := Ideal.Quotient.eq.2 h2
        simpa [Ideal.Quotient.mk_out] using h3
      · simp
    · rw [h0 y (not_le.1 hy)]
      refine (Finset.sum_eq_zero fun r _ => Set.indicator_of_notMem (fun hyr => hy ?_) _).symm
      have e : y = (y - a r) + a r := by ring
      rw [e]
      exact (Valuation.map_add _ _ _).trans
        (max_le (valued_le_one_of_mem_valBall ((memS r y).1 hyr)) (valued_int_le_one _))
  have hint : ∀ r, Integrable ((S r).indicator (fun _ => g (a r)))
      (haarIntegers (v.adicCompletion E)) := fun r =>
    (integrable_indicator_iff (hSm r)).2 (integrableOn_const (hfin r))
  calc ∫ y, g y ∂haarIntegers (v.adicCompletion E)
      = ∫ y, ∑ r, (S r).indicator (fun _ => g (a r)) y ∂haarIntegers (v.adicCompletion E) :=
        integral_congr_ae (Filter.Eventually.of_forall hdecomp)
    _ = ∑ r, ∫ y, (S r).indicator (fun _ => g (a r)) y ∂haarIntegers (v.adicCompletion E) :=
        integral_finsetSum _ fun r _ => hint r
    _ = _ := by
        rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [integral_indicator_const _ (hSm r), hSμ r, Complex.real_smul]
        push_cast
        rfl

end GlobalTheory.CompanionTheory.PeriodicInt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HaarIntegralIntegersFiniteSumStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_integral_integers_finite_sum : ∀ (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (m : ℕ) (g : v.adicCompletion E → ℂ), (∀ y, 1 < Valued.v y → g y = 0) → (∀ y h : v.adicCompletion E, Valued.v h ≤ WithZero.exp (-(m : ℤ)) → g (y + h) = g y) → ∫ y, g y ∂haarIntegers (v.adicCompletion E) = (((Ideal.absNorm v.asIdeal ^ m : ℕ) : ℂ))⁻¹ * ∑ᶠ r : 𝓞 E ⧸ v.asIdeal ^ m, g (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) := by
  first | exact @GlobalTheory.CompanionTheory.PeriodicInt.integral_eq_finsum | exact GlobalTheory.CompanionTheory.PeriodicInt.integral_eq_finsum | (intros; apply GlobalTheory.CompanionTheory.PeriodicInt.integral_eq_finsum <;> assumption)
end
end
