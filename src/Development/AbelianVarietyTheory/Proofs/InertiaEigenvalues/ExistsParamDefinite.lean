module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParametersBoundedEigenfunction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterTwistProps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAway
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDualC
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevOpenNormalIffDegreeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LengthEqLengthInvariantsOfTorsionLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Hk3

namespace GlobalTheory.DownLift.Params

variable {D : D7}

theorem mem_bddAut_of_posDef {V : HSp D} (hs : V.SigOK) (hp : V.IsPosDef) {f : GA D V → ℂ} (hc : Continuous f)
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) : f ∈ GlobalTheory.FinZeta.bddAut V := by
  have hpos : ∀ τ, (gramAt D V τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.DefiniteQuotient.exists_compact V hpos
  obtain ⟨b, hb⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨hc, hl, b, fun g => ?_⟩
  obtain ⟨γ, hγ, c, hcC, rfl⟩ := hcov g
  rw [hl γ hγ]
  exact hb c hcC

theorem level_abs {Γ Gf W : Type} [Group Γ] [Group Gf] [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* Gf}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup Gf} {χ : J →* ℂˣ} {f : Gf → W} (hf : f ∈ Bridge.AdForms ι ρ J χ)
    {k : Gf} (hk : k ∈ J) (h : Gf) : f (h * k) = ((χ ⟨k, hk⟩ : ℂˣ) : ℂ) • f h := by
  have h3 := hf 1 h ⟨k, hk⟩
  rw [map_one, map_one, one_mul] at h3
  exact h3

theorem ext_level {V : HSp D} (c : CoefA V) (hc : c.Is) {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}
    {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) (levEnv V β L).J (levEnv V β L).χ)
    {k : GA D V} (hk : k ∈ levG V β (flag1L L)) (h : GA D V) :
    c.ext f (h * k) = levChi V β (flag1L L) k • c.ext f h := by
  have hJ : (finHom V).rangeRestrict k ∈ (levEnv V β L).J := hk.2
  exact (GlobalTheory.DefLiftHecke.ext_mul c hc f hk.1 h).trans ((congrArg (c.ρ h⁻¹) (level_abs hf hJ _)).trans (map_smul _ _ _))

theorem exists_coord_ne {V : HSp D} (c : CoefA V) {f : Bridge.Gf V → c.W} (h0 : f ≠ 0) :
    ∃ ℓ : c.W →ₗ[ℂ] ℂ, (fun h => ℓ (c.ext f h)) ≠ 0 := by
  obtain ⟨u, hu⟩ := Function.ne_iff.1 h0
  obtain ⟨g, rfl⟩ := (finHom V).rangeRestrict_surjective u
  have h1 : c.ext f g ≠ 0 := fun e => hu (by
    have e' : c.ρ g⁻¹ (f ((finHom V).rangeRestrict g)) = 0 := e
    have := congrArg (c.ρ g) e'
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_zero] at this)
  refine ⟨innerₛₗ ℂ (c.ext f g), Function.ne_iff.2 ⟨g, fun e => h1 ?_⟩⟩
  exact inner_self_eq_zero.1 e


set_option maxHeartbeats 1000000 in
theorem exists_param_definite {V : HSp D} (hs : V.SigOK) (hp : V.IsPosDef) (c : CoefA V) (hc : c.Is)
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1)
    {L : LevDat D.host.E ℂ V.rank} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hS : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S) {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) (h0 : f ≠ 0) (s : Sys D)
    (he : ∀ P d, P.under (𝓞 D.host.F) ∉ S → IsLab V P d → hkF V P (Finsupp.single d 1) f = s P d • f) :
    ∃ B, GlobalTheory.LFun.IsSysParamD D S V.rank s B := by
  obtain ⟨n, hB⟩ := hβ
  rw [one_pow] at hB
  obtain ⟨ℓ, hℓ⟩ := exists_coord_ne c h0
  have hsph := (GlobalTheory.FinZeta.LevelOff.level_offS D V β Λ (flag1L L) S hB hS).1
  have hbd : (fun h => ℓ (c.ext f h)) ∈ GlobalTheory.FinZeta.bddAut V :=
    mem_bddAut_of_posDef hs hp (ℓ.continuous_of_finiteDimensional.comp (GlobalTheory.ThetaIntegrand.ext_continuous c hc β L hf))
      fun γ hγ g => congrArg ℓ (GlobalTheory.ThetaIntegrand.ext_invariant c hf γ hγ g)
  have hlev : ∀ k ∈ (levG V β (flag1L L) : Set (GA D V)), ∀ g,
      (fun h => ℓ (c.ext f h)) (g * k) = levChi V β (flag1L L) k * (fun h => ℓ (c.ext f h)) g := fun k hk g =>
    (congrArg ℓ (ext_level c hc hf hk g)).trans (map_smul _ _ _)
  have heig : ∀ w d R, Hecke₂ V (levG V β (flag1L L) : Set (GA D V)) (levChi V β (flag1L L)) S w d R →
      heckeLin V R (fun h => ℓ (c.ext f h)) = s w d • fun h => ℓ (c.ext f h) := fun w d R hR => by
    have hw : w.under (𝓞 D.host.F) ∉ S := by
      obtain ⟨_, _, _, _, h, -⟩ := hR
      exact (GlobalTheory.GoodPrimes.offS_iff S w).1 h
    have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := GlobalTheory.DefLiftHecke.one_pow_notMem w 0
    obtain ⟨hk, hop, -⟩ := GlobalTheory.LevOp.level_operators V β Λ 1 (flag1L L) hB w h1 fun PP hPP =>
      ⟨fun e => hw (e ▸ hS PP hPP), fun e => hw (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e ▸ hS PP hPP)⟩
    have hR' : SphOp V w d R := ((hop S d R).1 hR).2
    have h2 := ((GlobalTheory.SphLabelOps.label_operators V w).1 d R hR').2 _ (GlobalTheory.PRep.rightReg ℂ (GA D V) ℂ)
      (fun h => ℓ (c.ext f h)) fun k hkk => funext fun g => by
        have := hlev k (hk k hkk).1 g
        rwa [(hk k hkk).2, one_mul] at this
    funext g
    have h3 := congrFun h2 g
    have h4 := GlobalTheory.DefLiftHecke.ext_hkF c hc w (Finsupp.single d 1) f g
    rw [he w d hw ⟨R, hR'⟩, map_smul, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same, one_smul] at h4
    rw [opOf, Finsupp.sum_single_index (by exact zero_smul _ _), one_smul, Finset.sum_apply, LinearMap.sum_apply,
      Finset.sum_apply] at h3
    have h5 := congrArg ℓ h4
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Pi.smul_apply, map_smul] at h5
    exact h3.trans h5.symm
  obtain ⟨B, hB', -⟩ := GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D V _ _ S hsph _ hbd hℓ hlev s heig
  exact ⟨B, (GlobalTheory.LFun.isParamFunV_iff_isSysParamD_of_level hsph hℓ hlev heig B).1 hB'⟩

theorem exists_param_part (hP : GlobalTheory.Published.CuspRapidDecay) {V : HSp D} {Sp : D.what₂.Tau → SPar} {θ : InfFam D}
    (hθ : IsInfFam θ) {M : DSModel V Sp}
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1)
    {L : LevDat D.host.E ℂ V.rank} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hS : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S) {s : Sys D}
    (h : partFull θ M (levS V β L) (levChi V β L) S s ≠ ⊥) :
    ∃ B, GlobalTheory.LFun.IsSysParamD D S V.rank s B ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ S →
      ∀ a ∈ B w, ‖(a : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((V.rank : ℝ) - 1) / 2) := by
  obtain ⟨n, hB⟩ := hβ
  rw [one_pow] at hB
  have hsph := (GlobalTheory.FinZeta.LevelOff.level_offS D V β Λ L S hB hS).1
  obtain ⟨U, hU, hU0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨v, hv⟩ : ∃ v, U v ≠ 0 := by
    by_contra h
    push Not at h
    exact hU0 (MultilinearMap.ext h)
  obtain ⟨h1, h2⟩ := (mem_partFull θ M _ _ S s U).1 hU
  have h3 := (GlobalTheory.MultMem.mem_mult_iff ..).1 h1
  obtain ⟨B, hB', hb⟩ := GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D V _ _ S hsph (U v)
    ⟨(h3.aut v).cont, (h3.aut v).left, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ (h3.aut v) (h3.cusp v)⟩ hv (h3.lev v) s
    fun P d R hR => h2 P d R hR v
  exact ⟨B, (GlobalTheory.LFun.isParamFunV_iff_of_mem_partFull hsph hU hv B).1 hB', fun w hw => (hb w hw).2⟩

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem under_mem_badPl (t : T) {PP : Pl D.host.E} (h : PP ∈ R.Pg ∨ PP ∈ R.Q t) :
    (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
  classical
  exact Finset.mem_image.2 ⟨PP, Finset.mem_union.2 h, rfl⟩

theorem good_iff (t : T) (P : Pl D.host.E) : Good R t P ↔ P.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t := by
  classical
  constructor
  · intro h hm
    obtain ⟨PP, hPP, e⟩ := Finset.mem_image.1 hm
    obtain ⟨h1, h2⟩ := h PP (Finset.mem_union.1 hPP)
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with h3 | h3
    · exact h1 h3.symm
    · exact h2 (GlobalTheory.GoodPrimes.isConjPl_iff.2 h3)
  · intro hw PP hPP
    exact ⟨fun e => hw (e ▸ under_mem_badPl R t hPP),
      fun e => hw (GlobalTheory.LevelPlaces.under_eq_of_isConjPl e ▸ under_mem_badPl R t hPP)⟩

theorem paramsV {F : Face D A} (hC : Core R F) (i : Fin D.R.m) (t : T) (h) (hh : IsOpsV R i t h) (s y)
    (hy : IsEigV R i t h s y) (h0 : y ≠ 0) :
    ∃ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) (Vc D i).rank s B :=
  exists_param_definite (D.sp.V_sig _) (hC.models.vpos i) (R.cV i) (hC.models.cV i) (hC.lev.βV i) (L := R.datVt i t)
    (fun _ hPP => under_mem_badPl R t hPP) ((hC.models.HV i t).2.1.le (LinearMap.mem_range_self _ y))
    (fun e => h0 ((hC.models.HV i t).1 (e.trans (map_zero _).symm))) s fun P d hP hd =>
      (hh P ((good_iff R t P).2 hP) _ y).symm.trans
        ((congrArg (R.HV i t).e (hy P d ((good_iff R t P).2 hP) hd)).trans (map_smul _ _ _))

theorem paramsW (hP : GlobalTheory.Published.CuspRapidDecay) {F : Face D A} (hC : Core R F) (i : Fin D.R.m) (t : T) (c : Sys D)
    (hc : partW R i t c ≠ ⊥) : ∃ B', GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B' ∧
    ∀ w, Good R t w → ∀ a ∈ B' w, ‖(a : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2) := by
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  obtain ⟨B, h1, h2⟩ := exists_param_part hP hC.models.inf (hC.lev.βW i) (L := R.datWp i R.triv)
    (fun PP hPP => under_mem_badPl R t (hPP.imp_right fun h => absurd h (Finset.notMem_empty _))) hc
  rw [rW] at h1 h2
  exact ⟨B, h1, fun w hw => h2 w ((good_iff R t w).1 hw)⟩

theorem paramsEx : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, ParamsEx R i t :=
  fun hP _ _ _ _ _ _ _ _ _ _ _ R _ hG _ i t => ⟨paramsV R hG.core i t, paramsW R hP hG.core i t⟩

end GlobalTheory.DownLift.Params

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalCompatibilityAtTypes
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.WildSetSQ

theorem char_eq_one_of_wild {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (had : IsAdic (IsLocalRing.maximalIdeal O)) (χ : G E Ω →* Oˣ)
    (hχ : Continuous fun g => ((χ g : Oˣ) : O)) (σ : G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (m : ℕ) (hm : ¬ A.valuation (m : Ω) < 1)
    (h : χ σ ^ m = 1) : χ σ = 1 := by
  have key : ∀ M : ℕ, ((χ σ : Oˣ) : O) - 1 ∈ IsLocalRing.maximalIdeal O ^ M := by
    intro M
    let H : Subgroup (G E Ω) :=
      ((Units.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ M)).toMonoidHom).comp χ).ker
    have hH : ∀ g, g ∈ H ↔ ((χ g : Oˣ) : O) - 1 ∈ IsLocalRing.maximalIdeal O ^ M := by
      intro g
      rw [← Ideal.Quotient.eq, map_one, MonoidHom.mem_ker, Units.ext_iff]
      rfl
    have ho : IsOpen (H : Set (G E Ω)) := by
      have e : (H : Set (G E Ω)) = (fun g => ((χ g : Oˣ) : O) - 1) ⁻¹'
          ((IsLocalRing.maximalIdeal O ^ M : Ideal O) : Set O) := by
        ext g
        exact hH g
      rw [e]
      exact ((isAdic_iff.1 had).1 M).preimage (hχ.sub continuous_const)
    refine (hH σ).1 (GlobalTheory.WildKill.mem_of_wild A H ho σ m hm hσ ?_)
    rw [hH, map_pow, h, Units.val_one, sub_self]
    exact zero_mem _
  rw [Units.ext_iff, Units.val_one, ← sub_eq_zero]
  have h2 := Ideal.mem_iInf.2 key
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top] at h2
  simpa using h2

theorem coprime_pred (g : ℕ) (hg : 1 ≤ g) : (g - 1).Coprime g := by
  obtain ⟨n, rfl⟩ : ∃ n, g = n + 1 := ⟨g - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  simp

end GlobalTheory.WildSetSQ

namespace GlobalTheory.WildSetSQ

end GlobalTheory.WildSetSQ

namespace GlobalTheory.WildSetSQ

end GlobalTheory.WildSetSQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientTypeConjugatePlaceAtSplitPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbTypeUeIffLocalEmbeddingInCMHalfType
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbTypeUeIffLocalEmbeddingInCMHalfType
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.TypeUeHalf

theorem main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (ep : Bool) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw), EmbeddingTypes.EmbTypeUe (i := i) (w := w) (hw := hw) ep τ ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.EmbIn (N := D.nd) D.nbr i ep w hw τ :=
  fun _ _ _ _ ep τ => GlobalTheory.SplitDecl.embTypeUe_iff ep τ

end GlobalTheory.TypeUeHalf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbTypeUeIffLocalEmbeddingInCMHalfTypeStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embTypeUe_iff_localEmbeddingInCMHalfType : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (ep : Bool) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw), EmbeddingTypes.EmbTypeUe (i := i) (w := w) (hw := hw) ep τ ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.EmbIn (N := D.nd) D.nbr i ep w hw τ := by
  first | exact @GlobalTheory.TypeUeHalf.main | exact GlobalTheory.TypeUeHalf.main | (intros; apply GlobalTheory.TypeUeHalf.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientTypeConjugatePlaceAtSplitPrime
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.TypeConjSplit

theorem ambTypeD_of_splitRow : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) → EmbeddingTypes.ambTypeD (D := D) i ep := by
  intro D i ep hi u hu hU w hw hc τ₀ hτ
  obtain ⟨-, h2, h3, -⟩ := (GlobalTheory.SplitRowAll.splitRow_at D).2 i hi
  have hUin : ∀ τ, EmbIn (N := D.nd) D.nbr i ep u hu τ :=
    fun τ => (GlobalTheory.T.embTypeUe_iff_localEmbeddingInCMHalfType D i u hu ep τ).1 (hU τ)
  have hwin : EmbIn (N := D.nd) D.nbr i ep w hw τ₀ := (GlobalTheory.T.embTypeUe_iff_localEmbeddingInCMHalfType D i w hw ep τ₀).1 hτ
  rcases h3 u w hu hw hc with ⟨hpu, hpw⟩ | ⟨hpu, hpw⟩ <;> cases ep
  · obtain ⟨τ⟩ := hpu.1
    exact h2 u hu τ ⟨hpu.2 τ, hUin τ⟩
  · exact h2 w hw τ₀ ⟨hwin, hpw.2 τ₀⟩
  · exact h2 w hw τ₀ ⟨hpw.2 τ₀, hwin⟩
  · obtain ⟨τ⟩ := hpu.1
    exact h2 u hu τ ⟨hUin τ, hpu.2 τ⟩

end GlobalTheory.TypeConjSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientTypeConjugatePlaceAtSplitPrimeStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ambientType_conjugatePlace_at_splitPrime : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool), GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) → EmbeddingTypes.ambTypeD (D := D) i ep := by
  first | exact @GlobalTheory.TypeConjSplit.ambTypeD_of_splitRow | exact GlobalTheory.TypeConjSplit.ambTypeD_of_splitRow | (intros; apply GlobalTheory.TypeConjSplit.ambTypeD_of_splitRow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitRowPrimeOf
section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TorsionExponentCondition
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
open Classical

namespace GlobalTheory.HubX.Check

variable {D : D7}

variable {L : SizeData₂ D} {HW : HWOf D.loc} {R : KillingConditions.RowK} {X : KillingConditions.HubData D}

theorem not_inert {l : ℕ} (h1 : TwistedPlaces.SplitK D l) : ¬ TwistedPlaces.InertK D l := by
  intro h2
  unfold TwistedPlaces.SplitK at h1
  unfold TwistedPlaces.InertK at h2
  rw [h1] at h2
  rcases h2 with h2 | h2 <;> cases h2

theorem decl (h : Canon L HW R X) (hJ : AdmissibleParameterJ.ConclusionJa D) (i : D.nd.Loc) (hg : D.nd.l i ∉ TwistedPlaces.gset D)
    (hr : KillingConditions.RangeAD L X.exc (D.nd.l i)) (hs : TwistedPlaces.SplitK D (D.nd.l i))
    (hex : ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc hJ.choose) : EmbeddingTypes.hypDecl i (X.dc i) hJ.choose := by
  have hp := (D.nd.lPrime i).out
  have h5 : 5 ≤ D.nd.l i := by
    have h2 := hp.two_le
    have h3 : D.nd.l i ≠ 3 := fun e => hr.1 (Or.inr e)
    have h2' : D.nd.l i ≠ 2 := fun e => hr.1 (Or.inl (e ▸ D.host.toHostRaw.two_mem_small))
    have h4 : D.nd.l i ≠ 4 := fun e => by rw [e] at hp; norm_num at hp
    omega
  have hsp : GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) := by
    refine ⟨hp, h5, fun e => hr.2.1 (Or.inl e), fun e => hr.2.1 (Or.inr e), fun k e => hg ?_, hs⟩
    rw [e]
    fin_cases k <;> simp [TwistedPlaces.gset]
  have he : epJ D = hJ.choose := epJ_eq hJ
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) ∧ ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc (epJ D) :=
    ⟨hsp, by rw [he]; exact hex⟩
  rw [h.dc i (not_inert hs), dcOf, dite_eq_left hc, ← he]
  exact hc.2.choose_spec

end GlobalTheory.HubX.Check

end
end

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX.SplitDecl

theorem splitRowPrime_of {D : D7} {L : SizeData₂ D} {X : KillingConditions.HubData D} (i : D.nd.Loc)
    (hg : D.nd.l i ∉ TwistedPlaces.gset D) (hr : KillingConditions.RangeAD L X.exc (D.nd.l i)) (hs : TwistedPlaces.SplitK D (D.nd.l i)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) := by
  have hp := (D.nd.lPrime i).out
  have h5 : 5 ≤ D.nd.l i := by
    have h2 := hp.two_le
    have h3 : D.nd.l i ≠ 3 := fun e => hr.1 (Or.inr e)
    have h2' : D.nd.l i ≠ 2 := fun e => hr.1 (Or.inl (e ▸ D.host.toHostRaw.two_mem_small))
    have h4 : D.nd.l i ≠ 4 := fun e => by rw [e] at hp; norm_num at hp
    omega
  refine ⟨hp, h5, fun e => hr.2.1 (Or.inl e), fun e => hr.2.1 (Or.inr e), fun k e => hg ?_, hs⟩
  rw [e]
  fin_cases k <;> simp [TwistedPlaces.gset]

theorem main : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D),
    GlobalTheory.HubX.Canon L HW R X → ∀ (hJ : AdmissibleParameterJ.ConclusionJa D) (i : D.nd.Loc), TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D →
    KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) →
    EmbeddingTypes.hypDecl i (X.dc i) (Exists.choose hJ) ∧
      ∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1 := by
  intro D L HW R X h hJ i _ hg hr hs
  have hsp := splitRowPrime_of (L := L) (X := X) i hg hr hs
  refine ⟨GlobalTheory.HubX.Check.decl h hJ i hg hr hs ((GlobalTheory.T.exists_splitPlacesDeclaration_splitRowPrime D i hJ.choose hsp).1), ?_⟩
  intro v hv
  exact (GlobalTheory.SplitPlaces.placesSplit D.host (D.nd.l i) hsp v hv).1

end GlobalTheory.HubX.SplitDecl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
noncomputable section

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.Pst GlobalTheory.GalOfCusp

variable (D : D7) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
  (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {w : PlE D.host}
  (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O)

structure IsDeRhamOf : Prop where
  deRham : IsdRAt (D.loc l) Bw (resDec D.nd.plOm.1 r w)
  jumps : ∀ (τ : D.host.E →+* Qbar l) (L : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1), IsInduced Bw τ τ' →
    ∃ J : Multiset ℤ, J.map (fun n : ℤ => (n : ℂ)) =
      (D.naut.infG π (ι.toRingHom.comp τ)).map (fun z => -(z + (s : ℂ)) + ((a : ℂ) - 1) / 2) ∧
      IsJumpsAt (D.loc l) Bw (resDec D.nd.plOm.1 r w) τ J

def FrobMatch {K : Type} [CommRing K] (φ : K →+* ℂ) (M : G D.host.E D.nd.Om →* GL (Fin a) K) (u : ℝ) : Prop :=
  ∀ᶠ w : PlE D.host in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    (M σ : Matrix (Fin a) (Fin a) K).charpoly.map φ =
      ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) u)).map fun α => X - C α).prod

variable {D ι π s r}

end GlobalTheory.TripleLocal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundAtPointAllLocalisationsOfObjectConditionsAl
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundAtPointAllLocalisationsOfObjectConditionsAl
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.LocalisationBoundAtPoint

theorem boundAtPoint_all_localisations_of_objectConditions : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.AllDesignConditions D → TruncatedSeriesCountingIdentities.IntegralityFromMetric D := by
  intro hGAR hBK hLTD hLEC D h51 i r ρ π dc lenRow e' cB hR hA hl0 hl1
  have a51 := h51 i hl0 hl1 r ρ π dc lenRow e' cB hR hA
  obtain ⟨G1, G2, G3, G4, G5, G5x, G6, BK, TB, ROW, LIFT, Cont, SS, Decomp, Eps, Comparison₂, Shape, Font, H2, CFT⟩ := hA
  have TB78 : EmbeddingTypes.admTB i r π dc cB := fun w hw _ C hC => TB w hw C hC
  exact GlobalTheory.T.globalLatticeIndexTheorem_of_lengthBoundAtPlaces hGAR hLTD hLEC D i r ρ π dc lenRow e' cB G1 G2 G3 G4 G5 G5x G6 BK
    (GlobalTheory.T.blochKatoAnnihilator_all_of_tateDuality_eulerChar hBK hLTD hLEC D i) Cont Decomp Font (GlobalTheory.T.tateFinitenessAll_of_localTateDuality hLTD D i) Comparison₂ a51
    (GlobalTheory.T.unramifiedTrivialH1f_of_decl D i dc) ROW LIFT TB78 hl0 hl1

end GlobalTheory.LocalisationBoundAtPoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundAtPointAllLocalisationsOfObjectConditionsAlStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralityFromMetric_of_designConditionAll : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.AllDesignConditions D → TruncatedSeriesCountingIdentities.IntegralityFromMetric D := by
  first | exact @GlobalTheory.LocalisationBoundAtPoint.boundAtPoint_all_localisations_of_objectConditions | exact GlobalTheory.LocalisationBoundAtPoint.boundAtPoint_all_localisations_of_objectConditions | (intros; apply GlobalTheory.LocalisationBoundAtPoint.boundAtPoint_all_localisations_of_objectConditions <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCaseBoundAtPointOfAdmittedItems
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCaseBoundAtPointOfAdmittedItems
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory

theorem splitCase_bound_at_point_of_admitted_items : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (ep : Bool) (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ),
    EmbeddingTypes.admitted i r ρ π dc ep e' c0 cB →
    (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π) →
    EmbeddingTypes.aux₃ i r ρ π dc ep e' c0 cB := by
  intro hAR hTD hEC D i r ρ π dc ep e' c0 cB hA hG2 hL hD hπ
  obtain ⟨hJ, hRow⟩ := EmbeddingTypes.jump_and_length_of_admitted i r ρ π dc e' c0 cB hA hL hD hπ
  obtain ⟨g1, -, g3, g4, g578, g5x, g6, -, a51, -, -, hBK, hLc, -, -, hTB, unr, ct, -, dcm, -, tie, -,
    font, -, fin, -⟩ := hA
  have g5 : TruncatedSeriesCountingIdentities.admG5 i r := Formalism.MainNotions.N.K.SplitLatticeDiagonal.admG5_of_adm51_admG5 i r ρ π hπ a51 g578
  have g2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π := hG2 hL.2.2.2.1 hL.2.2.2.2 hπ
  refine ⟨hJ, hRow, fun hs hsha _ => ?_⟩
  have hthm := GlobalTheory.T.globalLatticeIndexTheorem_of_lengthBoundAtPlaces hAR hTD hEC D i r ρ π dc (EmbeddingTypes.lenRowSplit i dc e' c0) (fun _ => e') cB
    g1 g2 g3 g4 g5 g5x g6 hBK.1 hBK.2 ct dcm font fin tie a51 unr
    (EmbeddingTypes.admissible_length_of_local i r ρ π dc hD.2 e' c0 hRow) hLc hTB
  exact EmbeddingTypes.length_bound_of_theorem i ρ π dc hD.2 e' c0 cB hJ hthm hL.2.2.2.1 hL.2.2.2.2 hπ hs hsha

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCaseBoundAtPointOfAdmittedItemsStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitCase_bound_at_point_of_admitted_items_alt : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ep : Bool) (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), EmbeddingTypes.admitted i r ρ π dc ep e' c0 cB → (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π) → EmbeddingTypes.aux₃ i r ρ π dc ep e' c0 cB := by
  first | exact @GlobalTheory.splitCase_bound_at_point_of_admitted_items | exact GlobalTheory.splitCase_bound_at_point_of_admitted_items | (intros; apply GlobalTheory.splitCase_bound_at_point_of_admitted_items <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemContraIff
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.LFun

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem invT_val_eq (g : GA E a) : (invT a (Ad E) g).val = (g.valᵀ)⁻¹ := by
  change (g⁻¹).valᵀ = _
  rw [Matrix.coe_units_inv, Matrix.transpose_nonsing_inv]

theorem invT_scalar {R : Type} [CommRing R] (z : Rˣ) :
    invT a R (GeneralLinearGroup.scalar (Fin a) z) = GeneralLinearGroup.scalar (Fin a) z⁻¹ := by
  apply Units.ext
  change ((GeneralLinearGroup.scalar (Fin a) z)⁻¹).valᵀ = _
  rw [← map_inv]
  ext i j
  by_cases h : i = j
  · subst h; simp [GeneralLinearGroup.scalar]
  · simp [GeneralLinearGroup.scalar, h, Ne.symm h]

namespace CuspSub

variable (π : CuspSub E a)

def contra : CuspSub E a := UpperTheory.V.TC.dual π

variable {π} {π' : CuspSub E a}

theorem HasCentral.contra {ω : HChar E} (h : π.HasCentral ω) : π.contra.HasCentral ω⁻¹ := by
  rintro z _ ⟨ψ, hψ, rfl⟩
  change rt E a _ (UpperTheory.V.TC.dualFn E a ψ) = _ • UpperTheory.V.TC.dualFn E a ψ
  rw [UpperTheory.V.TC.rt_dualFn, invT_scalar, h z⁻¹ ψ hψ, map_smul]
  congr 1
  simp

theorem IsUnitary.contra (h : π.IsUnitary) : π.contra.IsUnitary := by
  obtain ⟨ω, h1, h2⟩ := h
  exact ⟨ω⁻¹, h1.inv, h2.contra⟩

end CuspSub

namespace CG

end CG

end GlobalTheory.CuspRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DblApply
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SWPairProof

variable {D : D7}

def dbl (V W : HSp D) (f₁ f₂ : WO V W → ℂ) : WO (GlobalTheory.Doubling.dblSp W) V → ℂ :=
  GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta W V (GlobalTheory.PairLift.dag V W f₂) (GlobalTheory.PairLift.dag V W f₁)

theorem dbl_apply (V W : HSp D) (f₁ f₂ : WO V W → ℂ) (x : WO (GlobalTheory.Doubling.dblSp W) V) :
    dbl V W f₁ f₂ x = starRingEnd ℂ (f₂ (GlobalTheory.PairLift.adjO V W (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL W V x))) *
      f₁ (GlobalTheory.PairLift.adjO V W (-GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR W V x)) := by
  simp only [dbl, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, GlobalTheory.PairLift.dag, Complex.conj_conj]

end GlobalTheory.SWPairProof

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistFrontInputs
open ReciprocityTheory.Gal Formalism.GaloisCohomology GlobalTheory.Published

namespace GlobalTheory

theorem twist_front_inputs : PoitouTateDuality → LocalFiniteness → LocalTateDuality → LocalFinitenessK → LocalTateDualityK → LocalEulerCharK → GlobalArtinReciprocity → GlobalTheory.TwSys.Cheb ∧ ChebotarevDegreeOne ∧ ChebotarevOpenNormal ∧ PoitouTateTotallyComplex ∧ CohDimTwo ∧ TameLocal ∧ Formalism.MainNotions.BlochKatoReduction.Gen.ArchimedeanSignatureMatching ∧ RayCharacterArtin :=
  fun hP hF hT a b c hA => ⟨cheb_holds, chebotarevDegreeOne', cheb_holds, hP.totallyComplex, ⟨hP.cohDimTwoGlobal, cohDimTwoLocal_of_localFiniteness hF⟩, TameLocal_of_duality hT, (GlobalTheory.TateLimit.twist_cohomology_inputs hP a b c).1, hA.rayCharacterArtin⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferEqOfIsOpenKer
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ArtinTransfer

open scoped Pointwise
open UpperTheory.V.Base (galOf galEmb galEmbTop range_galEmb galEmb_mem)
open Formalism.L2.Host (IsUnitAt IsUnifAt aboveF)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap finiteCompletionMap infiniteAdeleMap)

section Group

variable {Γ B : Type} [Group Γ] [CommGroup B] {H : Subgroup Γ} [H.FiniteIndex] (φ : H →* B)

end Group

section Places

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [Algebra L Ω]


variable [Algebra K L] [IsScalarTower K L Ω]

end Places

section Ideles

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable {K} in
theorem loc_same (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 v = x := by
  classical
  exact Pi.mulSingle_eq_same v _

variable {K} in
theorem loc_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v) (x : (v.adicCompletion K)ˣ) :
    (localIdele K v x).val.2 w = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne h _

theorem ideleMap_apply (a : Ideles K) (w : HeightOneSpectrum (𝓞 L)) :
    (ideleMap K L a).val.2 w = finiteCompletionMap K L w (a.val.2 (w.under (𝓞 K))) := rfl

end Ideles

section Artin

variable {K L Ω B : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [Algebra L Ω]
  [CommGroup B]

variable [Algebra K L]


variable [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]

end Artin

end GlobalTheory.ArtinTransfer

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDoubleCosetsConjMaxCompact
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDoubleCosetsConjMaxCompact
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.ClassFinConj

theorem exists_finset_double_cosets_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (h : GAf L n),
    ∃ T : Finset (GAf L n), ∀ g : GAf L n, ∃ γ ∈ GQ L n, ∃ t ∈ T,
      ∃ κ ∈ (Umax L n ⊓ (Umax L n).map (MulAut.conj h).toMonoidHom), g = γ * t * κ := by
  intro L _ _ _ n h
  classical
  obtain ⟨T, hT⟩ := GlobalTheory.DefiniteClassFinite.exists_finset_double_cosets_Umax L n
  obtain ⟨N', hN', hc⟩ := GlobalTheory.CongConjugate.congConj L n h 1 one_pos
  obtain ⟨J, hJ⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hN'
  refine ⟨(T ×ˢ J).image (fun p => p.1 * p.2), fun g => ?_⟩
  obtain ⟨γ, t, u, ht, hu, e⟩ := hT g
  obtain ⟨j, hj, κ, hκ, eu⟩ := hJ u hu
  refine ⟨(γ : GAf L n), γ.2, t * j, Finset.mem_image.2 ⟨(t, j), Finset.mem_product.2 ⟨ht, hj⟩, rfl⟩, κ,
    Subgroup.mem_inf.2 ⟨hκ.1, Subgroup.mem_map.2 ⟨h⁻¹ * κ * h, (hc κ hκ).1, ?_⟩⟩, ?_⟩
  · simp [MulAut.conj_apply, mul_assoc]
  · rw [e, eu]; simp only [mul_assoc]

end GlobalTheory.ClassFinConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDoubleCosetsConjMaxCompactStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_doubleCosets_conj_maxCompact : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (h : GAf L n), ∃ T : Finset (GAf L n), ∀ g : GAf L n, ∃ γ ∈ GQ L n, ∃ t ∈ T, ∃ κ ∈ (Umax L n ⊓ (Umax L n).map (MulAut.conj h).toMonoidHom), g = γ * t * κ := by
  first | exact @GlobalTheory.ClassFinConj.exists_finset_double_cosets_conj | exact GlobalTheory.ClassFinConj.exists_finset_double_cosets_conj | (intros; apply GlobalTheory.ClassFinConj.exists_finset_double_cosets_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothWhittakerBumpAdelicGL
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothWhittakerBumpAdelicGL
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology


open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump in
theorem GlobalTheory.WhitBump.exists_bump_glob : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ b : GA E (a + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (a + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (a + 1)), IsCompact C ∧ ∀ p, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (a + 1)), u⁻¹ * p ∈ C) ∧ (∃ U : Subgroup (GL (Fin (a + 1)) (Af E)), IsOpen (U : Set (GL (Fin (a + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (a + 1) u) = b g) ∧ ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (a + 1)) := by
  intro E _ _ _ m
  obtain ⟨f, hf, hfc, hfs, hf1⟩ := exists_bumpInf_ne (E := E) (n := m + 1)
  obtain ⟨h1, hN, hK, hsupp⟩ := bumpFin_spec (E := E) (n := m + 1) fun u hu hk => psiFin_integral u hu hk
  set c := bumpInf f (oneL E (m + 1)) with hc
  let pI : GA E (m + 1) → GL (Fin (m + 1)) (Cinf E) := fun g => GeneralLinearGroup.map (pInf E) g
  let pF : GA E (m + 1) → GL (Fin (m + 1)) (Af E) := fun g => GeneralLinearGroup.map (pFin E) g
  refine ⟨fun g => bumpInf f (toL (pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) / c * bumpFin (pF g),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [pI, pF, map_one, Units.val_one, h1, mul_one]
    exact div_self hf1
  · intro u hu g
    simp only [pI, pF, map_mul, Units.val_mul]
    have e := bumpInf_mul f _ (pInf_mem_unipB hu) (toL ((GeneralLinearGroup.map (pInf E) g : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))
    erw [e]
    rw [hN _ (pFin_mem_unipB hu), psiN_eq]
    ring
  · let T := tsupport f
    let C : Set (GA E (m + 1)) := (fun q : GL (Fin (m + 1)) (Cinf E) × GL (Fin (m + 1)) (Af E) =>
      infGL E (m + 1) q.1 * finGL E (m + 1) q.2) ''
        ({y : GL (Fin (m + 1)) (Cinf E) | toL (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) ∈ T} ×ˢ
          (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1) : Set (GL (Fin (m + 1)) (Af E))))
    refine ⟨C, ?_, ?_⟩
    · refine ((isCompact_setOf_toL T hfc hfs).prod
        (GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E (m + 1))).image ?_
      exact ((GlobalTheory.ConstTermSmooth.continuous_infGL).comp continuous_fst).mul
        (continuous_finGL_bump.comp continuous_snd)
    · intro p hp
      have hI : bumpInf f (toL (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) ≠ 0 := by
        intro h; apply hp; simp only [h, zero_div, zero_mul]
      have hF : bumpFin (pF p) ≠ 0 := by
        intro h; apply hp; simp only [h, mul_zero]
      obtain ⟨t, ht⟩ : ∃ t, f (toL (nu t * Matrix.of (toL (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))))) ≠ 0 := by
        by_contra hall
        push_neg at hall
        have hall' : ∀ t, f (toL (nu t * (pI p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))) = 0 := hall
        apply hI
        unfold bumpInf
        simp [hall']
      obtain ⟨uf, huf, hk⟩ := hsupp _ hF
      refine ⟨infGL E (m + 1) (nuGL t)⁻¹ * finGL E (m + 1) uf,
        mem_NA_of (inv_mem (nuGL_mem t)) huf, ⟨(nuGL t * pI p, uf⁻¹ * pF p), ⟨?_, hk⟩, ?_⟩⟩
      · exact subset_tsupport f ht
      · refine ga_ext ?_ ?_ <;> simp [pI, pF]
  · refine ⟨GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1),
      GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E (m + 1), fun k hk g => ?_⟩
    simp only [pI, pF, map_mul, pInf_finGL, pFin_finGL, mul_one]
    rw [hK k hk]
  · intro g
    have hsm := contDiffOn_bumpInf f hf hfc hfs
    set L := lmul (toL (pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) with hL
    have hmaps : Set.MapsTo L (invSet E (m + 1)) (invSet E (m + 1)) := fun x hx => by
      have hx' : IsUnit (Matrix.of x) := hx
      change IsUnit ((pI g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) * Matrix.of x)
      exact (pI g).isUnit.mul hx'
    have h2 : ContDiffOn ℝ ∞ (fun x : Lie E (m + 1) => bumpInf f (L x)) (invSet E (m + 1)) :=
      hsm.comp (L.contDiff.contDiffOn) hmaps
    have hl : ContDiffOn ℝ ∞ (fun x : Lie E (m + 1) => bumpInf f (L x) / c * bumpFin (pF g))
        (invSet E (m + 1)) := (h2.div_const c).mul contDiffOn_const
    refine hl.congr fun x hx => ?_
    have hx' : IsUnit (Matrix.of x) := hx
    rw [chart, dite_eq_left hx']
    simp only [pI, pF, map_mul, pInf_infGL, pFin_infGL, mul_one, Units.val_mul, IsUnit.unit_spec]
    rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothWhittakerBumpAdelicGLStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_whittakerBump_adelicGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ b : GA E (a + 1) → ℂ, b 1 = 1 ∧ (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (a + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) ∧ (∃ C : Set (GA E (a + 1)), IsCompact C ∧ ∀ p, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (a + 1)), u⁻¹ * p ∈ C) ∧ (∃ U : Subgroup (GL (Fin (a + 1)) (Af E)), IsOpen (U : Set (GL (Fin (a + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (a + 1) u) = b g) ∧ ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (a + 1)) := by
  first | (exact @GlobalTheory.WhitBump.exists_bump_glob) | (exact GlobalTheory.WhitBump.exists_bump_glob) | (intros; apply GlobalTheory.WhitBump.exists_bump_glob  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameRelationCocycleSquareZeroInertia
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameRelationCocycleSquareZeroInertia
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.TameRelation

open GlobalTheory.TameQuot

theorem eq_one_of_index_coprime {J N : Type} [Group J] [AddCommGroup N] {l k : ℕ}
    (hN : ∀ m : N, (l ^ k) • m = 0) (θ : J →* Multiplicative N) (h : θ.ker.index.Coprime l)
    (σ : J) : θ σ = 1 := by
  have h1 : θ σ ^ θ.ker.index = 1 := by
    rw [← map_pow]; exact θ.ker.pow_index_mem σ
  have h2 : θ σ ^ l ^ k = 1 := hN (θ σ).toAdd
  exact (pow_eq_one_iff_of_coprime (h.pow_right k)).1 ⟨h1, h2⟩

theorem pow_formula {Γ R W : Type} [Group Γ] [CommRing R] [AddCommGroup W] [Module R W]
    (ρ : Representation R Γ W) {b : R} (hb : b * b = 0) {γ : Γ} (hγ : ∀ m, ρ γ m = m + b • m)
    (z : Γ → W) (hz : ∀ g h, z (g * h) = z g + ρ g (z h)) (k : ℕ) :
    (∀ m, ρ (γ ^ k) m = m + k • b • m) ∧ z (γ ^ k) = k • z γ + k.choose 2 • b • z γ := by
  have hbb : ∀ m : W, b • b • m = 0 := fun m => by rw [← mul_smul, hb, zero_smul]
  induction k with
  | zero => simpa using hz 1 1
  | succ k ih =>
    refine ⟨fun m => ?_, ?_⟩
    · rw [pow_succ', map_mul, Module.End.mul_apply, ih.1, hγ, smul_add, smul_comm b k, hbb,
        smul_zero, add_zero, succ_nsmul]
      abel
    · rw [pow_succ', hz, ih.2, hγ, smul_add, smul_comm b k, smul_comm b (k.choose 2), hbb,
        smul_zero, add_zero, succ_nsmul, Nat.choose_succ_succ' k 1, Nat.choose_one_right, add_smul]
      abel

theorem tame_relation : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∀ (k : ℕ), normV v % (2 * l ^ k) = 1 → ∀ (M : ℕ) (d : G F Ω →* Multiplicative (ZMod (l ^ M))) (γ σ : G F Ω), 1 ≤ M → IsOpen (d.ker : Set (G F Ω)) → γ ∈ Ine (F := F) A → d γ = Multiplicative.ofAdd 1 → IsFrob A (normV v) σ → ∀ (R : Type) [CommRing R] (W : Type) [AddCommGroup W] [Module R W] [TopologicalSpace W] [DiscreteTopology W] (ρ : Representation R (G F Ω) W) (a b : R), (∀ m : W, (l ^ k) • m = 0) → b * b = 0 → (∀ τ ∈ Ine (F := F) A, ∀ m, ρ τ m = m + (((Multiplicative.toAdd (d τ)).val : R) * b) • m) → (∀ m, ρ σ m = m + a • m) → ∀ z : Z1 ρ, a • z.1 γ = b • z.1 σ ∧ (b = 0 → z.1 γ = 0 → ∀ τ ∈ Ine (F := F) A, z.1 τ = 0) := by
  intro hT F Ω _ _ _ _ _ l hlp A v hA hl k hq M d γ σ hM hd hγ hdγ hσ R _ W _ _ _ _ ρ a b h4 hb hI hρ z
  obtain ⟨-, -, hco, ⟨t, tc, ts, hk⟩, -, -⟩ := hT F Ω l A v hA hl
  haveI : Fact (1 < l ^ M) := ⟨one_lt_pow₀ hlp.out.one_lt (by omega)⟩
  have hdJ : ∀ τ ∈ ineKer F A l, d τ = 1 := fun τ hτ =>
    eq_one_of_index_coprime (l := l) (k := M) (fun m => by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])
      (d.comp (ineKer F A l).subtype) (hco _ inferInstance (hd.preimage continuous_subtype_val)) ⟨τ, hτ⟩
  have hρJ : ∀ τ ∈ ineKer F A l, ∀ m, ρ τ m = m := fun τ hτ m => by
    rw [hI τ (ineKer_le_Ine A l hτ), hdJ τ hτ]; simp
  have hzJ : ∀ τ ∈ ineKer F A l, z.1 τ = 0 := fun τ hτ => by
    let θ : ineKer F A l →* Multiplicative W :=
      MonoidHom.mk' (fun g => Multiplicative.ofAdd (z.1 g)) fun g h => by
        have := z.2.2 (g : G F Ω) h
        rw [hρJ _ g.2] at this
        exact congrArg Multiplicative.ofAdd this
    have ho : IsOpen (θ.ker : Set (ineKer F A l)) :=
      (isOpen_discrete {0}).preimage (z.2.1.comp continuous_subtype_val)
    exact eq_one_of_index_coprime (l := l) (k := k) h4 θ
      (hco _ inferInstance ho) ⟨τ, hτ⟩
  refine ⟨?_, fun hb0 h0 τ hτ => ?_⟩
  · have hj := tame_rel hA hl hσ hγ
    have hγ' : ∀ m, ρ γ m = m + b • m := fun m => by
      rw [hI γ hγ, hdγ, toAdd_ofAdd, ZMod.val_one, Nat.cast_one, one_mul]
    obtain ⟨p1, p2⟩ := pow_formula ρ hb hγ' z.1 z.2.2 (normV v)
    have hqs : ∀ m : W, normV v • m = m := KStar.Tree.nsmul_eq_self_of_mod hq h4
    obtain ⟨c, hc⟩ := KStar.Tree.dvd_choose_two hq
    rw [hc, mul_comm (l ^ k), mul_smul, h4, smul_zero, add_zero, hqs] at p2
    have e : σ * γ = γ ^ normV v * (((γ ^ normV v)⁻¹ * (σ * γ * σ⁻¹)) * σ) := by group
    have h1 := z.2.2 σ γ
    rw [e, z.2.2, z.2.2 _ σ, hzJ _ hj, hρJ _ hj, zero_add, p1, p2, hqs, hρ, ← add_assoc,
      ← add_assoc, add_comm (z.1 γ)] at h1
    exact (add_left_cancel h1).symm
  · have hg : IsProGen F A l γ := by
      refine (isProGen_iff_isUnit F Ω l A t tc ts hk ⟨γ, hγ⟩).2 ?_
      by_contra hu
      obtain ⟨y, hy⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 (PadicInt.mem_nonunits.1 hu)
      obtain ⟨g, hg⟩ := ts (Multiplicative.ofAdd y)
      have h1 : t ((g ^ l)⁻¹ * ⟨γ, hγ⟩) = 1 := by
        rw [map_mul, map_inv, map_pow, inv_mul_eq_one, hg]
        refine Multiplicative.toAdd.injective ?_
        rw [hy, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul]
      have h2 : d (((g : G F Ω) ^ l)⁻¹ * γ) = 1 := hdJ _ ((hk _).1 h1)
      rw [map_mul, map_inv, map_pow, inv_mul_eq_one, hdγ] at h2
      have h3 := congrArg (fun x => ZMod.castHom (dvd_pow_self l (by omega : M ≠ 0)) (ZMod l)
        (Multiplicative.toAdd x)) h2
      simp only [toAdd_pow, toAdd_ofAdd, map_one, nsmul_eq_mul, map_mul, map_natCast,
        ZMod.natCast_self, zero_mul] at h3
      exact zero_ne_one h3
    let θ : Ine (F := F) A →* Multiplicative W :=
      MonoidHom.mk' (fun g => Multiplicative.ofAdd (z.1 g)) fun g h => by
        have := z.2.2 (g : G F Ω) h
        rw [hI _ g.2, hb0, mul_zero, zero_smul, add_zero] at this
        exact congrArg Multiplicative.ofAdd this
    have ho : IsOpen (θ.ker : Set (Ine (F := F) A)) :=
      (isOpen_discrete {0}).preimage (z.2.1.comp continuous_subtype_val)
    have hc : IsClosed ((θ.ker.map (Ine (F := F) A).subtype : Subgroup (G F Ω)) : Set (G F Ω)) :=
      (isClosed_Ine A).isClosedEmbedding_subtypeVal.isClosedMap _ (θ.ker.isClosed_of_isOpen ho)
    have h1 : Subgroup.zpowers γ ⊔ ineKer F A l ≤ θ.ker.map (Ine (F := F) A).subtype :=
      sup_le (Subgroup.zpowers_le.2 ⟨⟨γ, hγ⟩, h0, rfl⟩) fun τ hτ =>
        ⟨⟨τ, ineKer_le_Ine A l hτ⟩, hzJ τ hτ, rfl⟩
    obtain ⟨τ', hτ', rfl⟩ := Subgroup.topologicalClosure_minimal _ h1 hc (hg.2 hτ)
    exact hτ'

end GlobalTheory.TameRelation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameRelationCocycleSquareZeroInertiaStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_relation_cocycle_squareZero_inertia : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∀ (k : ℕ), normV v % (2 * l ^ k) = 1 → ∀ (M : ℕ) (d : G F Ω →* Multiplicative (ZMod (l ^ M))) (γ σ : G F Ω), 1 ≤ M → IsOpen (d.ker : Set (G F Ω)) → γ ∈ Ine (F := F) A → d γ = Multiplicative.ofAdd 1 → IsFrob A (normV v) σ → ∀ (R : Type) [CommRing R] (W : Type) [AddCommGroup W] [Module R W] [TopologicalSpace W] [DiscreteTopology W] (ρ : Representation R (G F Ω) W) (a b : R), (∀ m : W, (l ^ k) • m = 0) → b * b = 0 → (∀ τ ∈ Ine (F := F) A, ∀ m, ρ τ m = m + (((Multiplicative.toAdd (d τ)).val : R) * b) • m) → (∀ m, ρ σ m = m + a • m) → ∀ z : Z1 ρ, a • z.1 γ = b • z.1 σ ∧ (b = 0 → z.1 γ = 0 → ∀ τ ∈ Ine (F := F) A, z.1 τ = 0) := by
  first | exact @GlobalTheory.TameRelation.tame_relation | exact GlobalTheory.TameRelation.tame_relation | (intros; apply GlobalTheory.TameRelation.tame_relation <;> assumption)
end
end
