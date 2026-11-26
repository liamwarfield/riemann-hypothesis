module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.TypePlain
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.AbConv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WindowMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinSph
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SphUnl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SumCardLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Ad0IrrMulVec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.QuadraticCharpolyCoeffDifference
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetRepresentatives
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainIntegralCentralInvariance
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftConductor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLocalType
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftHeckeEigenvalues
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftWhittakerExpansion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftRapidDecay
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftFourierCoefficients
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeProjectionEigenform
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NotDih
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.EndOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.DualOfWeights
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.GalAut

@[expose] public section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom
attribute [local instance 10000] DivisionSemiring.to_moduleIsTorsionFree

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.PlainTorOfMono0
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace UpperTheory.Gal.projectedFormsSystemPart.Pm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem linked_single {ρ ρ' : IrrGL (k := k)} (hρ : ρ.IsCusp) (hρ' : ρ'.IsCusp) (hne : ρ ≠ ρ.nu 1) (e : ρ' = ρ.nu 1) :
    (Segment.single ρ hρ).Linked (Segment.single ρ' hρ') := by
  subst e
  refine ⟨⟨Segment.ofFirst ρ hρ 2 two_pos, ?_⟩, ?_, ?_⟩
  · rw [Segment.carrier_single, Segment.carrier_single]
    ext z
    rw [Segment.mem_carrier]
    simp only [Segment.first_ofFirst, Segment.len_ofFirst, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      interval_cases i
      · left; simp
      · right; simp
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, by simp⟩
      · exact ⟨1, by norm_num, by simp⟩
  · rw [Segment.carrier_single, Segment.carrier_single, Set.singleton_subset_iff, Set.mem_singleton_iff]
    exact hne
  · rw [Segment.carrier_single, Segment.carrier_single, Set.singleton_subset_iff, Set.mem_singleton_iff]
    exact fun e => hne e.symm

theorem eq_single_of_len {Δ : Segment k} (h : Δ.len = 1) : Δ = Segment.single Δ.first Δ.isCusp_first :=
  Segment.ext_first (by simp [Segment.single]) (by simp [Segment.single, h])

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem ne_nu_one {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {rc : IrrGL (k := w.adicCompletion E) → WD h} (L : UpperTheory.Zero.LLC.LawsT a ha rc) {ρ : IrrGL (k := w.adicCompletion E)}
    (hρ : ρ.IsCusp) : ρ ≠ ρ.nu 1 := by
  intro e0
  refine WD.lpTw_one_ne (rc ρ) (by rw [L.dim]; exact hρ.1) ?_
  calc (rc ρ).lpTw 1 = rc (ρ.nu ((1 : ℝ) : ℂ)) := (L.nu ρ 1).symm
    _ = rc ρ := by rw [Complex.ofReal_one, ← e0]

end UpperTheory.Gal.projectedFormsSystemPart.Pm

open UpperTheory.Gal.projectedFormsSystemPart.Pm in
theorem UpperTheory.Gal.projectedFormsSystemPart.plainTor_of_mono0 : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n, ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ σ : SmIrr (GL (Fin n) (w.adicCompletion E)), π.IsLocComp w σ → UpperTheory.Zero.LLC.Toral (IrrGL.of σ.ρ σ.smooth σ.irred) → ∀ rc : IrrGL (k := w.adicCompletion E) → WD h, UpperTheory.Zero.LLC.IsRecT h rc → (rc (algNorm σ)).mono0 → PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) := by
  intro Ω _ E _ _ _ _ _ n _ π w A h σ hσ hT rc hrc hm
  obtain ⟨a, ha, L⟩ := hrc
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hg : IsGeneric σ.ρ := GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E n π w σ hσ
  have hnu : ∀ (z : IrrGL (k := w.adicCompletion E)) (s : ℂ), IsGeneric z.rep → IsGeneric (z.nu s).rep :=
    fun z s hz => (isGeneric_congr (IrrGL.twEquiv z _ _)).1 ((isGeneric_twist_iff _).2 hz)
  have hgτ : IsGeneric (algNorm σ).rep :=
    hnu _ _ ((isGeneric_congr (IrrGL.equivOf σ.ρ σ.smooth σ.irred)).1 hg)
  obtain ⟨c, Δ, y, hd, hun, hL, ⟨e⟩⟩ := GlobalTheory.genericUnlinkedGL_outright (w.adicCompletion E) (algNorm σ).1 _
    (algNorm σ).rep (algNorm σ).2.rep.smooth (algNorm σ).2.rep.irr hgτ
  have hIsL : IsL ((List.ofFn Δ : List (Segment (w.adicCompletion E))) : Multiset (Segment (w.adicCompletion E)))
      (algNorm σ).rep :=
    ⟨c, y, hd, ⟨Δ, ⟨Fin.univ_val_map Δ, fun i j hij hp => hun i j hij.ne hp.1⟩, hL⟩,
      (isCosocle_self (algNorm σ).2.rep.irr).of_equiv (.refl _) e⟩
  have hm' := hm
  rw [L.langlands (List.ofFn Δ) (algNorm σ) hIsL, segSum] at hm'
  have hlen : ∀ i, (Δ i).len = 1 := by
    intro i
    have hmi := GlobalTheory.UnlinkedMono.noMonodromy_of_mem_weilDeligneListSum _ hm' _
      (List.mem_map.2 ⟨Δ i, List.mem_ofFn.2 ⟨i, rfl⟩, rfl⟩)
    by_contra hne
    have hirr : IsIrrWD ((rc (Δ i).first).lpTw ((((Δ i).len : ℝ) - 1) / 2)) := by
      rw [← L.nu]; exact L.cusp _ ((Δ i).isCusp_first.nu _)
    exact GlobalTheory.SegLen.not_mono0_lpChar_lpSp hirr (by have := (Δ i).len_pos; omega) hmi
  obtain ⟨s, hs, hch⟩ := hT
  have hs' := GlobalTheory.LocGL.SupportRing.hasSupport_nu hs (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)
  have hms := GlobalTheory.LocGL.ZelevinskyExpansion.msupp_eq_of_isL (algNorm σ).2.rep.irr hIsL hs'
  have mem : ∀ u ∈ s, ∃ i, (Δ i).first = u.nu (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) := by
    intro u hu
    have hu' : u.nu (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) ∈ msupp ((List.ofFn Δ : List (Segment (w.adicCompletion E))) :
        Multiset (Segment (w.adicCompletion E))) := by
      rw [hms]; exact Multiset.mem_map_of_mem _ hu
    rw [msupp, Multiset.mem_bind] at hu'
    obtain ⟨D, hD, hu''⟩ := hu'
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 (Multiset.mem_coe.1 hD)
    rw [Segment.mem_ms, Segment.mem_carrier] at hu''
    obtain ⟨m, hm1, e'⟩ := hu''
    have : m = 0 := by have := hlen i; omega
    subst this
    exact ⟨i, by simpa using e'⟩
  refine ⟨s, hs, hch, ?_⟩
  intro y1 hy1 z1 hz1 hyz
  obtain ⟨i, hi⟩ := mem y1 hy1
  obtain ⟨j, hj⟩ := mem z1 hz1
  have key : (Δ i).first = (Δ j).first.nu 1 := by
    rw [hi, hj, hyz, IrrGL.nu_nu, IrrGL.nu_nu, add_comm]
  have hne := Pm.ne_nu_one L (Δ j).isCusp_first
  by_cases hij : i = j
  · subst hij; exact hne key
  · refine hun j i (Ne.symm hij) ?_
    rw [Pm.eq_single_of_len (hlen j), Pm.eq_single_of_len (hlen i)]
    exact Pm.linked_single _ _ hne key

theorem UpperTheory.Gal.projectedFormsSystemPart.typePlain : UpperTheory.Gal.projectedFormsSystemPart.TypePlain := by
  intro E Ω _ _ _ _ _ _ n hn π w A h σ hσ rc hrc χ ⟨b, hb, hN, hχ⟩
  have hm : (rc (algNorm σ)).mono0 := hb ▸ (WD.monodromyZero_ofWeilDeligneRepClass_iff b).2 hN
  refine UpperTheory.Gal.projectedFormsSystemPart.plainTor_of_mono0 Ω E n hn π w A h σ hσ ?_ rc hrc hm
  have hT : UpperTheory.Zero.LLC.Toral (algNorm σ) := by
    refine UpperTheory.Zero.LLC.abConv E Ω A w h rc hrc (algNorm σ) (fun j : Fin n => (χ j).comp (Weil h).subtype) fun t => ?_
    rw [← hb, WD.charPol_mk, hχ t, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]
    rfl
  obtain ⟨s, hs, hch⟩ := hT
  have hs' := GlobalTheory.LocGL.SupportRing.hasSupport_nu hs (-(((1 - (n : ℝ)) / 2 : ℝ) : ℂ))
  have e : (algNorm σ).nu (-(((1 - (n : ℝ)) / 2 : ℝ) : ℂ)) = IrrGL.of σ.ρ σ.smooth σ.irred := by
    unfold algNorm
    rw [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero]
  rw [← e]
  refine ⟨_, hs', fun y hy => ?_⟩
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hy
  exact hch z hz
end
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V

theorem UpperTheory.Gal.projectedFormsSystemPart.autAway (PH : Af.HypothesesH) (hL : PartLink) (hC : ConjTor) {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L]
    [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) {n : ℕ} (hn : 1 ≤ n) (V : s.Lev)
    (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (hτ : TypeFor r ι τ₀) (hS : V.S' = s.S) :
    (hset Q τ₀).Aut ι fun _ ρ => Af.IsIrr (ρ.comp V.pr) → AwayOk s ι (ρ.comp V.pr) := by
  intro lam _ d ξ hξ F hF hK hI
  obtain ⟨e, he⟩ := hξ
  have hTeich : ∃ t, r.IsTeich t := by
    have := c.dvr
    have := c.fin
    obtain ⟨hc, hfin, hlm, -⟩ := abelian₂.dvr_finite l c.O
    have := hc
    have := hfin
    have : CharP (ResidueField c.O) l := by
      refine (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 ?_
      rwa [← map_natCast (residue c.O), residue_eq_zero_iff]
    have : CharP (c.O ⧸ maximalIdeal c.O) l := inferInstanceAs (CharP (ResidueField c.O) l)
    let j := Perfection.lift l (ResidueField c.O) (c.O ⧸ maximalIdeal c.O) (RingHom.id (ResidueField c.O))
    have hj (z : ResidueField c.O) : Perfection.coeff (c.O ⧸ maximalIdeal c.O) l 0 (j z) = z :=
      RingHom.congr_fun ((Perfection.lift l (ResidueField c.O) (c.O ⧸ maximalIdeal c.O)).symm_apply_apply
        (RingHom.id (ResidueField c.O))) z
    let τ : ResidueField c.O →* c.O := (Perfection.teichmuller l (maximalIdeal c.O)).comp j
    refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨(Perfection.mk_teichmuller (j _)).trans (hj _), ?_⟩⟩
    rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
  obtain ⟨t, ht⟩ := hTeich
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) := by
    let f := ι.toRingHom.comp (algebraMap c.O (Qbar l))
    have hinj : Function.Injective (Matrix.GeneralLinearGroup.map f : GL (Fin m) c.O →* GL (Fin m) ℂ) :=
      Units.map_injective (Matrix.map_injective (ι.injective.comp Subtype.val_injective))
    exact MonoidHom.ker_comp_of_injective τ₀ _ hinj ▸ (hτ t ht).1
  have h1 := decompU l L Ω s n hn V Q c m τ₀ ι hop lam d e ξ he F hF hK hI
  refine IsConcreteLE.le_iff.1 (iSup_le fun σ => ?_) h1
  by_cases h0 : YOf Q ι τ₀ e ξ σ.1 = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨Y, hY, hP⟩ := hL l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ.1 σ.2 h0
  rw [← hY]
  refine le_iSup (fun Y : {Y : (hset Q τ₀).Part ι lam ξ // Af.IsIrr (Y.r.comp V.pr) → AwayOk s ι (Y.r.comp V.pr)} => Y.1.Y)
    ⟨Y, fun hi => ?_⟩
  obtain ⟨π, p1, p2, p3, p4, p5⟩ := hP hi
  refine ⟨π, p1, p2, p3, fun w hw hw0 => ?_⟩
  by_cases hwS : w.under (𝓞 (Lp L)) ∈ V.S'
  swap
  · obtain ⟨B, hB⟩ := p4 w (partUR2Unr l L Ω s n hn V Q c ι m τ₀ lam d e ξ he σ.1 σ.2 h0 w hwS)
    exact ImaginaryQuadraticEtaCharacter.sphUnl L n hn π w B hB
  obtain ⟨hwv, hsp⟩ := UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s
  rw [hS] at hwS
  have hu : w.under (𝓞 (Lp L)) ∈ s.St := by
    rcases hwS with h | h | h
    · refine absurd ?_ hw
      rw [← map_natCast (algebraMap (𝓞 (Lp L)) (𝓞 L))]
      exact h
    · exact h
    · exact absurd h hw0
  refine hC L n hn π p2 (s.w (w.under (𝓞 (Lp L)))) w (hwv _).symm ?_
  refine (ImaginaryQuadraticEtaCharacter.plainIff L n hn π _).1 fun τ hτ' => ?_
  classical
  have hs : ∀ u : s.St, IsSplitAt (s.w u) := fun u => hsp _ (by
    rw [hwv]
    exact s.split _ (Or.inr (Or.inl u.2)))
  choose loc hloc using fun u : s.St => (Af.locCompC PH.toClassicalTheorems L n π (s.w u)).1
  obtain ⟨rc, hrc⟩ := PH.toClassicalTheorems.exists_rec (s.hw (w.under (𝓞 (Lp L))))
  have k := partUR2Type l L Ω s n hn V Q c ι m τ₀ lam d e ξ he σ.1 σ.2 h0 _ (hτ t ht)
    (Function.update loc ⟨_, hu⟩ τ) (fun u' => p5 _ (hs u') _ (by
      by_cases e : u' = ⟨_, hu⟩
      · subst e
        rwa [Function.update_self]
      · rw [Function.update_of_ne e]
        exact hloc _)) ⟨_, hu⟩ rc hrc
  rw [Function.update_self] at k
  exact typePlain L Ω n hn π _ _ (s.hw _) τ hτ' rc (Z.Desc.W.toT PH.toClassicalTheorems hrc)
    (fun i => W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l))) ((t i).comp V.pr)) k

theorem UpperTheory.Gal.projectedFormsSystemPart.tu_same {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {n : ℕ} (hn : 1 ≤ n) {ι : Qbar l ≃+* ℂ} {ρ : G F Ω →* GL (Fin n) (Qbar l)} {π π' : CuspSub F n}
    (h : Af.AttC ι ρ π) (h' : Af.AttC ι ρ π') {w : Plc F} (k : TU π w) : TU π' w := by
  obtain ⟨t, ht⟩ := ImaginaryQuadraticEtaCharacter.winOf F n hn π
  have ev : ∀ᶠ v : Plc F in Filter.cofinite, ∃ B, (CG.mk π).HasSat v B ∧ (CG.mk π').HasSat v B := by
    filter_upwards [h.2, h'.2] with v ⟨B, hB, hE⟩ ⟨B', hB', hE'⟩
    exact ⟨B, hB, (UpperTheory.hecke_eigenvalue_basic_properties F Ω l ι v).2.2 n ρ B B' hE hE' ▸ hB'⟩
  have k' : ImaginaryQuadraticEtaCharacter.WinAt π' t w := by
    rcases hn.eq_or_lt with rfl | h2
    · exact ImaginaryQuadraticEtaCharacter.suppSmo1 F π π' ev t w (ht w k.1 k.2)
    · exact ImaginaryQuadraticEtaCharacter.suppSmo F n h2 π π' ev t w (ht w k.1 k.2)
  exact ⟨k'.1, ImaginaryQuadraticEtaCharacter.winUnl F n π' t w k'⟩
