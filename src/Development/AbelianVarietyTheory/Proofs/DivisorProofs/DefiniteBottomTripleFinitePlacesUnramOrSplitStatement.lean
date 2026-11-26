module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleFinitePlacesUnramOrSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LargePlaceRatioRamified
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LargePlaceRatioRamified
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RamifiedOnLargePlaces

theorem chrEq_mul' {D : D7} {c c' : (AE D)ˣ →* Circle} {χ χ' : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ)
    (h' : ChrEq c' χ') : ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]
  · rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx]
    rfl

theorem not_unramAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ →
    ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∈ S1 D →
    ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  intro D T Lc sc G μ₀ hIs t v e he hv i j hU
  have hi1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have hi2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  set k := D.R.m - (i : ℕ) with hk
  have hμ : ChrEq (Lc.mu t ((j : ℕ) + 1)) (Lc.C.mu0 j * Lc.xiH t) := chrEq_mul' (hIs.mu0 j) (hIs.xi t)
  have hν : ChrEq (Lc.mu t ((j : ℕ) + 1) / G.ch.chi k) (Lc.C.mu0 j * Lc.xiH t * (G.ch.chiH k)⁻¹) := by
    rw [div_eq_mul_inv]; exact GlobalTheory.ChartQuot.chrEq_div hμ (G.ch.chi_eq k hi1 hi2)
  set P := G.pl.w v
  have hP : P.under (𝓞 D.host.F) = v := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inr hv))
  have hUnr := (GlobalTheory.LFun.unrAt_iff_of_chrEq hν P).1
    (GlobalTheory.UnrOverPlace.unrAt_of_unramAt D _ v e he hU P hP)
  apply (G.ch.lev1 k hi1 hi2 P (by rw [hP]; exact hv)).2
  intro x hx hxv
  have h1 := hUnr x hx
  have h2 := (Lc.C.isMu0 j).tame P x hx hxv
  have h3 := hIs.xi_tame t P x hx hxv
  have e1 : (Lc.C.mu0 j * Lc.xiH t * (G.ch.chiH k)⁻¹).loc P x =
      (Lc.C.mu0 j).loc P x * (Lc.xiH t).loc P x * ((G.ch.chiH k).loc P x)⁻¹ := rfl
  rw [e1, h2, h3, one_mul, one_mul, inv_eq_one] at h1
  exact h1

end GlobalTheory.RamifiedOnLargePlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LargePlaceRatioRamifiedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.large_place_ratio_ramified : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∈ S1 D → ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  first | exact @GlobalTheory.RamifiedOnLargePlaces.not_unramAt | exact GlobalTheory.RamifiedOnLargePlaces.not_unramAt | (intros; apply GlobalTheory.RamifiedOnLargePlaces.not_unramAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterQuotientNotUnramifiedAtBasePlaceId
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterQuotientNotUnramifiedAtBasePlaceId
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RamifiedIdeleBasePlace

theorem ideleCharacterQuotient_not_unramified_at_basePlaceIdempotent : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ →
    ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v = G.pl.v0 →
      ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  intro D T Lc sc G μ₀ hL t v e he hv i j hU
  subst hv
  have hw : (G.pl.w G.pl.v0).under (𝓞 D.host.F) = G.pl.v0 := G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  have h1 := GlobalTheory.UnrOverPlace.unrAt_of_unramAt D _ G.pl.v0 e he hU _ hw
  exact GlobalTheory.RowTest.squareNuHeckeCharacter_not_unramified_at_chosenPlace hL G t i j
    ((GlobalTheory.LFun.unrAt_iff_of_chrEq (GlobalTheory.FunObj.SqNum.chrEq_nu G t i j hL) _).1 h1)

end GlobalTheory.RamifiedIdeleBasePlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterQuotientNotUnramifiedAtBasePlaceIdStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_unramAt_mu_div_chi_at_base_place : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v = G.pl.v0 → ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  first | exact @GlobalTheory.RamifiedIdeleBasePlace.ideleCharacterQuotient_not_unramified_at_basePlaceIdempotent | exact GlobalTheory.RamifiedIdeleBasePlace.ideleCharacterQuotient_not_unramified_at_basePlaceIdempotent | (intros; apply GlobalTheory.RamifiedIdeleBasePlace.ideleCharacterQuotient_not_unramified_at_basePlaceIdempotent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareMuDivChiRamifiedAtTwistPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareMuDivChiRamifiedAtTwistPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RamTwist

theorem unramAt_of_div {D : D7} {ε : AF D.host.F} {a b c : (AE D)ˣ →* Circle}
    (h : GlobalTheory.WeilParts.UnramAt ε (a * b / c)) (ha : GlobalTheory.WeilParts.UnramAt ε a) (hc : GlobalTheory.WeilParts.UnramAt ε c) :
    GlobalTheory.WeilParts.UnramAt ε b := by
  intro x h1 h2 h3
  have e := h x h1 h2 h3
  rw [MonoidHom.div_apply, MonoidHom.mul_apply, ha x h1 h2 h3, hc x h1 h2 h3, one_mul, div_one] at e
  exact e

theorem not_overP_g {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc)
    {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∉ G.pl.S0) (PP : HeightOneSpectrum (𝓞 D.host.E))
    (hPP : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v) (k : Fin 2) : ¬ Formalism.L2.Host.OverP D.host (D.host.g k) PP := by
  intro h
  have hk : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    subst hPP
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal
    rw [map_natCast]
    exact h
  refine hv (G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_)))
  fin_cases k
  · exact Or.inl hk
  · exact Or.inr (Or.inl hk)

end GlobalTheory.RamTwist


open GlobalTheory.RamTwist in
theorem GlobalTheory.SqTop.not_unramAt_twist : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → ∀ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v → ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  intro D T Lc sc G μ₀ hμ t v e he hv PP hPP hPv i j hU
  have hmi1 : 1 ≤ D.R.m - (i : ℕ) := by have := i.2; omega
  have hmi2 : D.R.m - (i : ℕ) ≤ D.R.m := Nat.sub_le _ _
  have hchi : GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i)) :=
    GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (G.ch.chi_eq _ hmi1 hmi2) v e he fun P hP =>
      G.ch.unr _ hmi1 hmi2 P (hP ▸ hv)
  have hmu : GlobalTheory.WeilParts.UnramAt e (Lc.mu0 ((j : ℕ) + 1)) :=
    GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hμ.mu0 j) v e he fun P hP =>
      (Lc.C.isMu0 j).unr P (not_overP_g G hv P hP)
  have hxi : GlobalTheory.WeilParts.UnramAt e (Lc.xi t) := by
    refine unramAt_of_div (a := Lc.mu0 ((j : ℕ) + 1)) (c := G.ch.chi (D.R.m - i)) ?_ hmu hchi
    exact hU
  have h1 := GlobalTheory.UnrOverPlace.unrAt_of_unramAt D (Lc.xi t) v e he hxi PP hPv
  exact (hμ.Q_ram t PP).2 (Or.inl hPP) ((GlobalTheory.LFun.unrAt_iff_of_chrEq (hμ.xi t) PP).1 h1)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareMuDivChiRamifiedAtTwistPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_mu_div_chi_ramified_at_twist_place : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∉ G.pl.S0 → ∀ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v → ∀ i j : Fin D.R.m, ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) / G.ch.chi (D.R.m - i)) := by
  first | exact @GlobalTheory.SqTop.not_unramAt_twist | exact GlobalTheory.SqTop.not_unramAt_twist | (intros; apply GlobalTheory.SqTop.not_unramAt_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceNotNonsplit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceNotNonsplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitAtSmallPlaces

theorem not_nonSplitAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ →
    ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∈ G.pl.S0 →
      ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
  intro D T Lc sc G μ₀ _ _ v ε hε hv hns
  obtain ⟨e, he⟩ := G.pl.w_split v hv
  have hb := Formalism.IndefR.Fin.below_of_idemAt he
  have hbv : Formalism.IndefR.Fin.belowPl (G.pl.w v) = v := by
    refine HeightOneSpectrum.ext ?_
    have a := congrArg HeightOneSpectrum.asIdeal (G.pl.under_w hv)
    rw [← a]
    rfl
  rw [hbv] at hb
  refine hns.2 ⟨e, he.1, ?_⟩
  rw [hb, Formalism.IndefR.Fin.placeIdem_eq hε]
  rfl

end GlobalTheory.SplitAtSmallPlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlaceNotNonsplitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_place_not_nonsplit : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → v ∈ G.pl.S0 → ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
  first | exact @GlobalTheory.SplitAtSmallPlaces.not_nonSplitAt | exact GlobalTheory.SplitAtSmallPlaces.not_nonSplitAt | (intros; apply GlobalTheory.SplitAtSmallPlaces.not_nonSplitAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceUnderNotDvdDifferentIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceUnderNotDvdDifferentIdeal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistPlDiff

theorem natAbs_discr_dvd_pow (D : D7) : ∃ M : ℕ,
    (discr D.host.E).natAbs ∣ (D.host.QS * D.host.q * D.host.d) ^ M := by
  have hD : (discr D.host.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero _)
  have hN : D.host.QS * D.host.q * D.host.d ≠ 0 := D.host.condN_ne_zero
  refine ⟨(discr D.host.E).natAbs, (Nat.dvd_pow_self_iff hD hN).2 fun p hp => ?_⟩
  have h := Nat.mem_primeFactors.1 hp
  exact Nat.mem_primeFactors.2
    ⟨h.1, D.host.der.discr_primes.1 p h.1 (Int.natCast_dvd.2 h.2.1), hN⟩

theorem under_not_dvd_differentIdeal : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T), ∀ PP ∈ Lc.Q t, ¬ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  intro D T Lc μ₀ hL t PP hPP hdvd
  obtain ⟨h2qdT, -⟩ := hL.Q_off t PP hPP
  set P := (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) with hPdef

  have h1 : Ideal.absNorm P.asIdeal ∣ (discr D.host.E).natAbs := by
    have ha : Ideal.absNorm P.asIdeal ∣ (discr D.host.F).natAbs := by
      rw [← NumberField.absNorm_differentIdeal D.host.F (𝓞 D.host.F)]
      exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)
    exact ha.trans (Int.natAbs_dvd_natAbs.2 (NumberField.discr_dvd_discr _ _))
  obtain ⟨M, hM⟩ := natAbs_discr_dvd_pow D

  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have := Ideal.absNorm_mem P.asIdeal
    have h' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (Ideal.absNorm P.asIdeal : 𝓞 D.host.F) ∈ PP.asIdeal := this
    simpa using h'
  have hpow : (((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E)) ^ M ∈ PP.asIdeal := by
    obtain ⟨c, hc⟩ := h1.trans hM
    rw [← Nat.cast_pow, hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem
  have hx := PP.isPrime.mem_of_pow_mem M hpow
  apply h2qdT
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hx

end GlobalTheory.TwistPlDiff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceUnderNotDvdDifferentIdealStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_place_under_not_dvd_differentIdeal : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T), ∀ PP ∈ Lc.Q t, ¬ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  first | exact @GlobalTheory.TwistPlDiff.under_not_dvd_differentIdeal | exact GlobalTheory.TwistPlDiff.under_not_dvd_differentIdeal | (intros; apply GlobalTheory.TwistPlDiff.under_not_dvd_differentIdeal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceUnderNotNonSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceUnderNotNonSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitTwistPlaces

theorem not_nonSplitAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → ∀ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v → ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
  intro D T Lc sc G μ₀ hμ t v e he PP hPP hv hns
  obtain ⟨f, hf⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt ((hμ.Q_pl t PP hPP).2 PP hPP)
  exact GlobalTheory.AdTh.RecPair.under_ne hf hns hv

end GlobalTheory.SplitTwistPlaces
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceUnderNotNonSplitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_place_under_not_nonSplit : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → ∀ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v → ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
  first | exact @GlobalTheory.SplitTwistPlaces.not_nonSplitAt | exact GlobalTheory.SplitTwistPlaces.not_nonSplitAt | (intros; apply GlobalTheory.SplitTwistPlaces.not_nonSplitAt <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotRam

open GlobalTheory.WeilParts

variable {D : D7}

theorem unramAt_mul {e : AF D.host.F} {a b : (AE D)ˣ →* Circle} (ha : UnramAt e a) (hb : UnramAt e b) : UnramAt e (a * b) := by
  intro x h1 h2 h3
  rw [MonoidHom.mul_apply, ha x h1 h2 h3, hb x h1 h2 h3, one_mul]

theorem unramAt_pow {e : AF D.host.F} {a : (AE D)ˣ →* Circle} (ha : UnramAt e a) (n : ℕ) : UnramAt e (a ^ n) := by
  intro x h1 h2 h3
  rw [MonoidHom.pow_apply, ha x h1 h2 h3, one_pow]

theorem bottom_ram : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → (GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) ∧ GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∨ (¬ GlobalTheory.WeilParts.NonSplitAt D v e ∧ ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∧ ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hr T Lc μ₀ hμ G => ?_⟩⟩
  intro W i j A A' WW X _ t v e he
  by_cases hS : v ∈ G.pl.S0 ∨ ∃ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v
  · right
    rw [mul_div_mul_right_eq_div]
    rcases hS with hS | ⟨PP, hPP, hPv⟩
    · refine ⟨GlobalTheory.T.small_place_not_nonsplit G μ₀ hμ t v e he hS, ?_, ?_⟩
      · rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1
        · exact GlobalTheory.T.not_unramAt_mu_div_chi_at_base_place G μ₀ hμ t v e he h0 i j
        · exact GlobalTheory.T.large_place_ratio_ramified G μ₀ hμ t v e he h1 i j
      · rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1
        · subst h0; exact GlobalTheory.T.auxiliary_place_not_dvd_different_base_field G
        · exact GlobalTheory.T.large_place_not_dvd_different large₂ hr v h1
    · refine ⟨GlobalTheory.T.twist_place_under_not_nonSplit G μ₀ hμ t v e he PP hPP hPv, ?_, hPv ▸ GlobalTheory.T.twist_place_under_not_dvd_differentIdeal Lc μ₀ hμ t PP hPP⟩
      by_cases h0 : v ∈ G.pl.S0
      · rcases G.pl.mem_S0_of_sum_eq.1 h0 with h0 | h1
        · exact GlobalTheory.T.not_unramAt_mu_div_chi_at_base_place G μ₀ hμ t v e he h0 i j
        · exact GlobalTheory.T.large_place_ratio_ramified G μ₀ hμ t v e he h1 i j
      · exact GlobalTheory.T.square_mu_div_chi_ramified_at_twist_place G μ₀ hμ t v e he h0 PP hPP hPv i j
  · left
    push_neg at hS
    obtain ⟨h1, h2⟩ := GlobalTheory.T.grid_characters_unramified G μ₀ hμ t v e he hS.1 i
    exact ⟨unramAt_mul (GlobalTheory.T.level_character_unramified_mu G μ₀ hμ t v e he hS.1 hS.2 j) (unramAt_pow h2 _), unramAt_mul h1 (unramAt_pow h2 _)⟩

end GlobalTheory.BotRam

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottomTriple_finitePlaces_unram_or_split : GBig fun {D} {T} {Lc} {sc} G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → (GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2)) ∧ GlobalTheory.WeilParts.UnramAt e (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∨ (¬ GlobalTheory.WeilParts.NonSplitAt D v e ∧ ¬ GlobalTheory.WeilParts.UnramAt e (Lc.mu t (j + 1) * Lc.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * Lc.eta ^ (rankV D i j % 2))) ∧ ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F)) := by
  first | exact @GlobalTheory.BotRam.bottom_ram | exact GlobalTheory.BotRam.bottom_ram | (intros; apply GlobalTheory.BotRam.bottom_ram <;> assumption)
