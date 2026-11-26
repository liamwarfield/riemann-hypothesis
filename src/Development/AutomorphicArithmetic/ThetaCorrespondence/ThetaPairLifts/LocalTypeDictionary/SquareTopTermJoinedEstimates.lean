module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaConjugateMeanLogAbsBoundOfTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomConstantOfTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairsExistBaseTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLValueUpperBoundPermutedWeightsOfFE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareRatioValuationWithoutNormFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LValueRatioLowerBoundGauge
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricValueHeightBoundOfDenominatorsMeans
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomTripleIntegralEqConstMulLocal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomFormulaLargeRank
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomFormulaSmallRank
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomMinorMatching
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TowerOfThetaMatching

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftPeterssonNormEqRallisIntegral
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisInnerProductBottomNormEq
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
noncomputable section
namespace GlobalTheory.BottomRallis
variable {D : D7}
end GlobalTheory.BottomRallis
namespace GlobalTheory.BottomRallis
variable {D : D7}
end GlobalTheory.BottomRallis
namespace GlobalTheory.BottomRallis
variable {D : D7}
theorem rallis_inner_product_bottom_norm_eq (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A B : HSp D}
    {χA χB : (AE D)ˣ →* Circle} {sA : RealMat A} {sB : RealMat B} {t : ℕ} {cA : CptF A} {a : GL (Fin A.rank) (AE D)}
    {om : WRep A B} {ν : Measure (WO A B)} {𝓕 : Set (WO A B)} (hPair : Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕)
    (hA : wittIndex A = 0) (hB : wittIndex B = 0) {LA : Lat A} {LB : Lat B} {Sf : Finset (FinPl D)}
    {Φ : WO A B → ℂ} (hF : IsFockVec ψ θ A B sA sB Φ) (hU : Unram ψ A B χB LA LB Sf Φ Φ)
    (m : Measure (GA D A)) (mH : Measure (GA D B)) [m.IsHaarMeasure] [mH.IsHaarMeasure]
    (hint : ∃ s₁ : ℝ, s₁ < (t : ℝ) / 2 ∧
      IntegrableOn (integrand om m ν 𝓕 LA a Φ Φ (fun _ => 1) (fun _ => 1) s₁) (openOff A LA Sf) m)
    (l : ℕ → ℂ) (hl : ∀ i < A.rank,
      HolValueAt (LFun.charL χB⁻¹ (Sf : Set (FinPl D))) ((t : ℂ) / 2 + (A.rank : ℂ) / 2 - i) (l i)) :
    petersson B mH (up om m Φ (fun _ => 1)) (up om m Φ (fun _ => 1)) =
      volQ B mH * volQ A m * ((∏ i ∈ Finset.range A.rank, l i) /
        LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank ((t : ℂ) / 2)) *
        ∫ g in openOff A LA Sf, wcoef om ν 𝓕 Φ Φ g ∂m := by
  have hU19 := GlobalTheory.T.unramifiedDoublingIntegral_inert_place
  have hPB := paramBoundOn_all_of_split_inert D (GlobalTheory.T.sphericalParameterBound_split_place D) (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU19 D)
  have hLZ := localZetaOn_all_of_split_inert D (GlobalTheory.T.unramifiedDoublingIntegral_splitPlace_adelic hP.unramifiedDoublingGL D)
    (GlobalTheory.T.unramified_doubling_integral_inert_adelic hU19 D (GlobalTheory.T.sphericalParameterBound_nonsplit_places hU19 D))
  have hE : EulerRight D :=
    GlobalTheory.T.doubling_eulerProduct_farRight hP.cuspRapidDecay D (GlobalTheory.T.doublingSphericalFactorization_of_weilDualPair hP.weilRepresentationUnitaryPair D) hLZ hPB
  have hG : GlobalFormAniso D := _root_.GlobalTheory.T.theta_tower_compatibility hP.weilRepresentationUnitaryPair hP.cuspRapidDecay hP.doublingMethod D
    (_root_.UpperTheory.Lit.Sw47.siegelWeil_fock_anisotropic_unconditional D)
  have hH := heckeFormAniso_of_global_euler D hG hE
  have h1 : (fun _ : GA D A => (1 : ℂ)) ∈ A0 θ A cA := GlobalTheory.T.one_mem_A0_of_wittIndex_eq_zero hPair.setting hA
  have hpar := GlobalTheory.T.constantFunction_has_trivialRep_satakeParameters A LA Sf hU.sdA hU.two
  have hsph : SphFun A LA Sf (fun _ : GA D A => (1 : ℂ)) := fun _ _ _ _ _ => rfl
  obtain ⟨-, -, -, hfin⟩ := hH ψ θ A B χA χB sA sB t cA a om ν 𝓕 hPair hB LA LB Sf Φ Φ hF hF hU m mH
    inferInstance inferInstance _ h1 _ h1 (trivPar A.rank) hpar hsph hint
  have hL : HolValueAt (fun s => LFun.LSD D Sf (trivPar A.rank) χB (s + 1 / 2)) ((t : ℂ) / 2)
      (∏ i ∈ Finset.range A.rank, l i) := by
    refine HolValueAt.congr (holValueAt_prod (Finset.range A.rank) fun i hi => ?_) (GlobalTheory.T.partial_L_trivial_rep_twist_eq_prod_hecke_L χB Sf A.rank hU.unr)
    have h2 := hl i (Finset.mem_range.1 hi)
    rw [show (t : ℂ) / 2 + (A.rank : ℂ) / 2 - i = (t : ℂ) / 2 + ((A.rank : ℂ) / 2 - i) by ring] at h2
    have h3 := h2.comp_add
    simpa only [add_sub_assoc] using h3
  rw [hfin _ hL]
  simp only [rcoef_one]
  rw [integral_mul_const]
  ring
end GlobalTheory.BottomRallis
namespace GlobalTheory.BottomRallis
end GlobalTheory.BottomRallis
end
end
end

section
noncomputable section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
namespace GlobalTheory.NormRatio
section General
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
end General
section Translates
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : GlobalTheory.Core.Rk.IP.WRep S T}
  {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} {G : Type} [Group G] (ι : G →* GA D S)
end Translates
section Exact
variable {D : D7} {δ t0 : ℂ} {Q : ℕ} {P : Pair D ⊤ δ t0 Q} {X : Data P} {r : D.host.E}
end Exact
section Fock
variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q} {X : Data P}
end Fock
section Norm
variable {D : D7} {δ t0 : ℂ} {Q : ℕ} {P : Pair D ⊤ δ t0 Q} {X : Data P} {r : D.host.E}
theorem theta_lift_petersson_norm_eq_rallis_integral (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : GlobalTheory.NormSum.Inp D) (h : IsExact P X r) (hX : IsDict P X)
    {K₀ : Subgroup (GL (Fin X.B.rank) (Lev.EAf D))} {μ₀ : Measure (GA D X.B)} (hK : IsMaxLevel X.toFrame K₀ μ₀)
    {𝔪 : Ideal (𝓞 D.host.E)} {Sf : Finset (FinPl D)} {o : ℕ} (hm : GoodMod D 𝔪 Sf) (hstd : IsStdDatum P 𝔪 o)
    (ho : o + P.a ≤ P.d) (ha : 1 ≤ P.a) (had : P.a < P.d) (hu : GlobalTheory.LFun.UnrOff X.χB (Sf : Set (FinPl D))) (Λ : ℂ → ℂ)
    (hΛ : ∀ s, GlobalTheory.Cont.HolValueAt (GlobalTheory.LFun.charL X.χB⁻¹ (Sf : Set (FinPl D))) s (Λ s)) (T : Tup D P.a P.d P.n) :
    GlobalTheory.Cusp.petersson X.B μ₀ (X.lift T) (X.lift T) =
      mass D P.d * mass D P.a * ((∏ i ∈ Finset.range P.a, Λ (((P.d - P.a : ℕ) : ℂ) / 2 + (P.a : ℂ) / 2 - i)) /
        GlobalTheory.LFun.dSfun D.host.E (Sf : Set (FinPl D)) P.a P.d (((P.d - P.a : ℕ) : ℂ) / 2)) *
        (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp (minorPol D T) (minorPol D T) *
          ((locNorm D 𝔪 P.a (P.d - P.a) : ℂ) * (vacNorm D ⊤ δ t0 P.a P.d : ℂ))) := by
  refine (GlobalTheory.T.exists_thetaDoublingPairData_identity_cartan P X hX ha had).elim fun cA h1 => h1.elim fun a h2 => h2.elim fun ν h3 => h3.elim fun 𝓕 hPair => ?_
  have hfd := finite_data hI h hm hstd ho
  refine hfd.1.elim fun LB hLB => ?_
  have hn := (hfd.2 ν 𝓕 hPair.covol).1
  have hs := (hfd.2 ν 𝓕 hPair.covol).2
  have hlev := fun x => GlobalTheory.T.standardLattice_selfDual_and_integral_iff_stabilizes X.A P.a (X.ιA x) x h.std.frame.gramA X.rkA (h.std.ptA x)
  have hsph : IsSphOff X.ψ X.A X.B (stdLat X.A) LB Sf (X.fock T) := isSphOff_pure hX.2.inf hLB.2 _ _ _ _ _
  have hU : GlobalTheory.Core.Rk.IP.Unram X.ψ X.A X.B X.χB (stdLat X.A) LB Sf (X.fock T) (X.fock T) :=
    ⟨(hlev 1).1, hLB.1, fun v _ h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2, hu, hsph, hsph⟩
  have hint := GlobalTheory.T.doublingIntegrand_integrable_of_coefficient_const_compact P X hX (hlev 1).1 (fun x => (hlev x).2) a ν 𝓕 hPair.maj Sf (X.fock T)
    (ip X.A X.B ν 𝓕 (X.fock T) (X.fock T))
    (fun x hx k hk => (wcoef_fock hX ν 𝓕 T _ hk).trans (by rw [hX.2.fixA x hx T]))
    (fun x hx hx' k hk => (wcoef_fock hX ν 𝓕 T _ hk).trans (ip_fock_zero hX hPair.covol T (h.std.ptA x).1 (hs x hx hx')))
  refine hK.meas.elim fun 𝓕₀ h𝓕₀ => hX.1.measA.elim fun 𝓕A h𝓕A => ?_
  haveI := hX.1.haarA
  haveI : μ₀.IsHaarMeasure := h𝓕₀.1.1
  have hA : GlobalTheory.Cusp.wittIndex X.A = 0 := GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Mem.ColAd.isAniso_of_gram hX.1.gramA)
  have hB : GlobalTheory.Cusp.wittIndex X.B = 0 := GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Mem.ColAd.isAniso_of_gram hX.1.gramB)
  have key := _root_.GlobalTheory.BottomRallis.rallis_inner_product_bottom_norm_eq hP hPair hA hB (isFockVec_fock hX T) hU X.m μ₀
    ⟨((P.d - P.a : ℕ) : ℝ) / 2 - 1, by linarith, hint.1 _⟩
    (fun i => Λ (((P.d - P.a : ℕ) : ℂ) / 2 + (X.A.rank : ℂ) / 2 - i)) fun i _ => hΛ _
  have vA := volQ_eq_mass X.A P.a X.ιA X.KA X.m 𝓕A hX.1.defA hX.1.injA hX.1.rangeA hX.1.ratA hX.1.levA hX.1.levA_iff h𝓕A
  have vB := volQ_eq_mass X.B P.d X.ιB K₀ μ₀ 𝓕₀ hX.1.defB hX.1.injB hX.1.rangeB hX.1.ratB hK.lev hK.mem_iff h𝓕₀
  have e1 := hint.2.trans ((ip_fock hX hPair.covol T).trans (congrArg _ hn))
  refine key.trans ?_
  rw [vA, vB, e1, X.rkA, X.rkB]
theorem petersson_norm_bottom_theta_lift_eq (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : GlobalTheory.NormSum.Inp D) {large₂ : SizeData₂ D} (hR : GlobalTheory.SqTop.Rec large₂) {T : Type}
    {L : LevCh D T} {sc : Consts} {μ : T} (hL : L.Is μ) (G : GridData L sc) {t : T} {i j : Fin D.R.m}
    {P' : Pair D ⊤ δ t0 Q} (hb : IsBottom G t i j (modT G t) P P') {Λ : ℂ → ℂ} (hΛ : GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ) :
    (P.norm : ℂ) = normFactor D δ t0 P.a P.d P.n *
      ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ s := by
  have hm := goodMod_modT hL (GlobalTheory.SqTop.BotT.pde_ne_q hR).1 (GlobalTheory.SqTop.BotT.pde_ne_q hR).2 G t
  have hrk := GlobalTheory.FunObj.SqNum.Model.bot_ranks (D := D) i j
  have hPa := hb.rank.1
  have hPd := hb.rank.2.2.1
  have hdict := exact_dictionary P hI (isCongLevel_of_isBlockLevel hm.1 hb.lev.1)
  refine hdict.2.1.elim fun X h1 => h1.elim fun r h2 => h2.elim fun K₀ h3 => h3.elim fun μ₀ h4 => ?_
  have h5 := hdict.2.2 X r K₀ μ₀ h4.1 h4.2
  have hX := h5.1.1
  have hχ := GlobalTheory.T.heckeCharEq_of_finitePart_power_inverse X.χB P.W.chV' P.W.ep' (nuH G t i j) hX.2.weil.hecT h4.1.chB hb.chars.2
  have hl := GlobalTheory.T.squareNu_unramified_off_pair_partial_L_primitive hL hR.hF G t i j X.χB hχ
  have hT := _root_.GlobalTheory.NormRatio.theta_lift_petersson_norm_eq_rallis_integral hP hI h4.1 hX h4.2 hm hb.std (by rw [zero_add]; exact P.a_le) (by omega) (by omega) hl.1 Λ
    (hl.2 Λ hΛ)
  have hidx : ((P.J.relIndex (intG D P.d) : ℕ) : ℝ) = locIdx D (modT G t) P.a (P.d - P.a) :=
    GlobalTheory.StdLoc.relIndex_blockLevel P (modT G t) P.a hm.1 hm.2.1 P.a_le (hPa.symm ▸ hb.lev.1)
  have hidx' : ((P.J.relIndex (intG D P.d) : ℕ) : ℂ) = (locIdx D (modT G t) P.a (P.d - P.a) : ℂ) := by
    rw [← hidx]; rfl
  have hd := GlobalTheory.T.localIndex_localNorm_normalizingFactor_eq_partial D (modT G t) (sfB G t) hm P.a (P.d - P.a) (by omega)
  rw [Nat.add_sub_cancel' P.a_le] at hd
  have hre : 0 < (((P.d - P.a : ℕ) : ℂ) / 2).re := by
    have : (0 : ℝ) < ((P.d - P.a : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < P.d - P.a)
    rw [show (((P.d - P.a : ℕ) : ℂ) / 2) = ((((P.d - P.a : ℕ) : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    positivity
  have hprod : ∏ k ∈ Finset.range P.a, Λ (((P.d - P.a : ℕ) : ℂ) / 2 + (P.a : ℂ) / 2 - k) =
      ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ s := by
    obtain ⟨u, hu⟩ := hrk.2.2.1
    have e1 : P.d = 2 * GlobalTheory.SqTop.h0 D i j := by unfold GlobalTheory.SqTop.h0; omega
    rw [← GlobalTheory.BottomRallis.prod_range_sub_eq_prod_Icc (fun s => Λ s) P.a (GlobalTheory.SqTop.h0 D i j) (GlobalTheory.SqTop.e0 D i j)
      (by unfold GlobalTheory.SqTop.h0 GlobalTheory.SqTop.e0; omega)]
    refine Finset.prod_congr rfl fun k _ => congrArg Λ ?_
    rw [Nat.cast_sub P.a_le, e1]
    push_cast
    ring
  refine h5.2.2.2.2.trans ?_
  rw [Finset.sum_congr rfl fun T _ => hT T, ← Finset.mul_sum, ← Finset.sum_mul, hidx', hprod]
  exact collect hd (GlobalTheory.LFun.dSfun_ne_zero_of_re_pos _ _ _ hre) (GlobalTheory.LFun.dSfun_ne_zero_of_re_pos _ _ _ hre)
end Norm
theorem big_theta_petersson_norm_ratio_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ =>
  ∀ (δ t0 : ℂ) (i j : Fin D.R.m) (t t' : T) (Q Q' : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (P₁ P₁' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q')
    (Λ Λ' : ℂ → ℂ), GlobalTheory.FunObj.SqNum.IsBottom G t i j (GlobalTheory.SqTop.modT G t) P P' →
    GlobalTheory.FunObj.SqNum.IsBottom G t' i j (GlobalTheory.SqTop.modT G t') P₁ P₁' →
    GlobalTheory.CMVal.IsHeckeL (GlobalTheory.FunObj.SqNum.nuH G t i j) Λ → GlobalTheory.CMVal.IsHeckeL (GlobalTheory.FunObj.SqNum.nuH G t' i j) Λ' →
    (P.norm : ℂ) * ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ' s =
      (P₁.norm : ℂ) * ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ s := by
  intro hP hI _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro δ t0 i j t t' Q Q' P P' P₁ P₁' Λ Λ' hb hb' hΛ hΛ'
  have h1 := _root_.GlobalTheory.NormRatio.petersson_norm_bottom_theta_lift_eq hP (hI D) hR hL G hb hΛ
  have h2 := _root_.GlobalTheory.NormRatio.petersson_norm_bottom_theta_lift_eq hP (hI D) hR hL G hb' hΛ'
  have h3 := (GlobalTheory.BottomReal.bottom_real_eq G hL hb hb').1
  have h4 : normFactor D δ t0 P.a P.d P.n = normFactor D δ t0 P₁.a P₁.d P₁.n :=
    congr (congr (congrArg (normFactor D δ t0) h3.1) h3.2.1) h3.2.2.1
  rw [h1, h2, h4]
  ring
end GlobalTheory.NormRatio
end
end

section
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_petersson_norm_ratio_formula : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ =>
  ∀ (δ t0 : ℂ) (i j : Fin D.R.m) (t t' : T) (Q Q' : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (P₁ P₁' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q')
    (Λ Λ' : ℂ → ℂ), GlobalTheory.FunObj.SqNum.IsBottom G t i j (GlobalTheory.SqTop.modT G t) P P' →
    GlobalTheory.FunObj.SqNum.IsBottom G t' i j (GlobalTheory.SqTop.modT G t') P₁ P₁' →
    GlobalTheory.CMVal.IsHeckeL (GlobalTheory.FunObj.SqNum.nuH G t i j) Λ → GlobalTheory.CMVal.IsHeckeL (GlobalTheory.FunObj.SqNum.nuH G t' i j) Λ' →
    (P.norm : ℂ) * ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ' s =
      (P₁.norm : ℂ) * ∏ s ∈ Finset.Icc (1 - (GlobalTheory.SqTop.e0 D i j : ℤ)) (GlobalTheory.SqTop.h0 D i j : ℤ), Λ s := by
  first | exact @_root_.GlobalTheory.NormRatio.big_theta_petersson_norm_ratio_eq | exact _root_.GlobalTheory.NormRatio.big_theta_petersson_norm_ratio_eq | (intros; apply _root_.GlobalTheory.NormRatio.big_theta_petersson_norm_ratio_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsBottomBasisChange
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.BottomFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BottomRebase
theorem bottom_basis_change : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      ∃ (X' : Tri T A A' WW) (ζ : T → ℂ), IsBottomTri W i j X' ∧ X'.rW.β = 1 ∧ (∀ t, ∃ n : ℕ, 0 < n ∧ ζ t ^ n = 1) ∧
        X'.IsConst W.ψ W.θ fun t => ζ t * c0 t := by
  intro _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc _ _ G => ?_⟩⟩
  intro W _ i j A A' WW X c0 hX hc
  obtain ⟨Z, v, hZ, e1, e2, e3, hv, H⟩ := frame_change W.ψ W.θ W.θ_is _ _ _ _ X hX.is 1 (isFrame_one hX.stdW.2.1)
  refine ⟨Z, v, ⟨hX.rank, hX.rank', e1 ▸ hX.std, e2 ▸ hX.std', ?_, hZ⟩, by rw [e3], hv, H c0 hc⟩
  rw [e3]
  exact hX.stdW
end GlobalTheory.BottomRebase
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bottom_basis_change : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      ∃ (X' : Tri T A A' WW) (ζ : T → ℂ), IsBottomTri W i j X' ∧ X'.rW.β = 1 ∧ (∀ t, ∃ n : ℕ, 0 < n ∧ ζ t ^ n = 1) ∧
        X'.IsConst W.ψ W.θ fun t => ζ t * c0 t := by
  first | exact @_root_.GlobalTheory.BottomRebase.bottom_basis_change | exact _root_.GlobalTheory.BottomRebase.bottom_basis_change | (intros; apply _root_.GlobalTheory.BottomRebase.bottom_basis_change <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomConstantOfTheta
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomConstantRatioEqLocalFactorRatio
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomConstantTransferAlongTower
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BotTransfer
theorem bottom_constant_transfer_along_tower : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
      NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D)
      (Y : Tri T B B' WW₁) (c : T → ℂ), IsBottomTri W i j X → IsBottomTri W i j Y → Y.IsConst W.ψ W.θ c →
      ∃ u : T → D.what₂.LLˣ, X.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  intro _ _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro W S hψ hN i j A A' WW X B B' WW₁ Y c hX hY hc
  obtain ⟨X₁, hX₁, hX₁c⟩ := GlobalTheory.T.definiteBottomTriple_transport_same_ranks_constants W i j A A' WW X B B' WW₁ Y hX hY
  obtain ⟨Y₁, hY₁, e1, e2, e3, hY₁c⟩ := GlobalTheory.T.exists_definiteBottomTriple_transferred_frames W S hψ μ₀ hL hN i j B B' WW₁ X₁ Y hX₁ hY
  obtain ⟨u, hu⟩ := hY₁c c hc
  exact ⟨u, hX₁c _ (GlobalTheory.T.definiteBottomTriple_constants_eq_of_same_lattices W i j B B' WW₁ X₁ Y₁ hX₁ hY₁ e1.symm e2.symm e3.symm _ hu)⟩
end GlobalTheory.BotTransfer
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_tower_bottom_constant_transfer : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
      NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D)
      (Y : Tri T B B' WW₁) (c : T → ℂ), IsBottomTri W i j X → IsBottomTri W i j Y → Y.IsConst W.ψ W.θ c →
      ∃ u : T → D.what₂.LLˣ, X.IsConst W.ψ W.θ fun t => D.what₂.embLL (u t) * c t := by
  first | exact @_root_.GlobalTheory.BotTransfer.bottom_constant_transfer_along_tower | exact _root_.GlobalTheory.BotTransfer.bottom_constant_transfer_along_tower | (intros; apply _root_.GlobalTheory.BotTransfer.bottom_constant_transfer_along_tower <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BotRatio
theorem bottom_theta_constant_ratio_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall → GlobalTheory.SqTop.LNe →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ),
      IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      c0 t ≠ 0 ∧ c0 μ₀ ≠ 0 ∧ ∃ γ : D.what₂.LL, D.what₂.embLL γ * c0 μ₀ = c0 t := by
  intro hPr hK hM _ _ hL
  refine GlobalTheory.BotRatio.gBig_of_two (_root_.GlobalTheory.T.bottom_triple_integral_eq_const_mul_local hPr hK hM hL) (_root_.GlobalTheory.T.witt_tower_bottom_constant_transfer hPr hK hM) fun {D T Lc sc} G μ₀ C x b ha hb => ?_
  intro W S hψ hN i j t A A' WW X c0 hX hc
  obtain ⟨B, B', WW₁, Y, hY, hS⟩ := hN.bottom i j ⟨A, A', WW, X, hX⟩
  have hr := hS.rationalSums (fun t => (hY.integrable t).1) fun t => (hY.integrable t).2
  obtain ⟨u, hu⟩ := hb W S hψ hN i j B B' WW₁ Y A A' WW X c0 hY hX hc
  obtain ⟨lam, hl⟩ := ha W hψ i j B B' WW₁ Y hY
  have hR := GlobalTheory.ConstRatio.ratIn_of_definite hY.is (GlobalTheory.ConstRatio.posDef_of_std hY.std)
    (GlobalTheory.ConstRatio.posDef_of_std hY.std') (GlobalTheory.ConstRatio.posDef_of_std hY.stdW) hl hr μ₀
  obtain ⟨κ, hκ, e⟩ := hl.eq_mul hu
  have h1 : GlobalTheory.ConstRatio.RatIn D.what₂.embLL μ₀ fun t => D.what₂.embLL (u t) * c0 t := by
    rw [show (fun t => D.what₂.embLL (u t) * c0 t) = fun t => κ * lam t from funext e]
    exact (GlobalTheory.ConstRatio.ratIn_const hκ).mul hR
  have h2 : GlobalTheory.ConstRatio.RatIn D.what₂.embLL μ₀ c0 :=
    GlobalTheory.ConstRatio.RatIn.of_mul h1 (GlobalTheory.ConstRatio.ratIn_of_unit fun t => ⟨u t, rfl⟩) fun t => mul_comm _ _
  obtain ⟨h3, y, hy⟩ := h2 t
  refine ⟨h3, (h2 μ₀).1, y, ?_⟩
  rw [hy, div_mul_cancel₀ _ (h2 μ₀).1]
end GlobalTheory.BotRatio
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_constant_ratio_eq_local_factor_ratio : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall → GlobalTheory.SqTop.LNe →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ),
      IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      c0 t ≠ 0 ∧ c0 μ₀ ≠ 0 ∧ ∃ γ : D.what₂.LL, D.what₂.embLL γ * c0 μ₀ = c0 t := by
  first | exact @_root_.GlobalTheory.BotRatio.bottom_theta_constant_ratio_eq | exact _root_.GlobalTheory.BotRatio.bottom_theta_constant_ratio_eq | (intros; apply _root_.GlobalTheory.BotRatio.bottom_theta_constant_ratio_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisInnerProductFormulaFirstOccurrence
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.BotFormula.bottom_theta_petersson_norm_formula : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ),
      IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ) (δ t0 : ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ (u : ℂ) (M : Tup D P.a P.d P.n → Tup D P'.a P'.d P'.n → ℤ) (M' : Tup D P'.a P'.d P'.n → Tup D P.a P.d P.n → ℤ),
          u ≠ 0 ∧ u ∈ Qbar ∧
          (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (hd : P'.d = P.d) (h : GA D P.d),
            (∀ T, starRingEnd ℂ (P.coord h T) = κ * u * c0 s * ∑ T', (M T T' : ℂ) * P'.coord (hd ▸ h) T') ∧
            ∀ T', P'.coord (hd ▸ h) T' * (κ * u * c0 s) = ∑ T, (M' T' T : ℂ) * starRingEnd ℂ (P.coord h T) := by
  intro hPr hK hM hI hB
  obtain ⟨cA, hA⟩ := _root_.GlobalTheory.T.theta_bottom_formula_large hPr hK hM hI hB
  obtain ⟨cB, hB'⟩ := _root_.GlobalTheory.T.theta_bottom_formula_small hPr hK hM hI hB
  obtain ⟨cC, hC⟩ := _root_.GlobalTheory.T.rallis_bottom_minor_matching hPr hK hM hI hB
  obtain ⟨cD, hD⟩ := _root_.GlobalTheory.T.exists_bottom_basis_change hPr
  refine ⟨max (max (max cA cB) cC) cD, fun ε CF hCF => ?_⟩
  simp only [max_le_iff] at hCF
  obtain ⟨CA, xA, hA⟩ := hA ε CF hCF.1.1.1
  obtain ⟨CB, xB, hB'⟩ := hB' ε CF hCF.1.1.2
  obtain ⟨CC, xC, hC⟩ := hC ε CF hCF.1.2
  obtain ⟨CD, xD, hD⟩ := hD ε CF hCF.2
  refine ⟨max (max (max CA CB) CC) CD, max (max (max xA xB) xC) xD, fun C hC0 D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  simp only [max_le_iff] at hC0 hx
  have hA := hA C hC0.1.1.1 D large₂ he hx.1.1.1 hR T Lc μ₀ hL G
  have hB' := hB' C hC0.1.1.2 D large₂ he hx.1.1.2 hR T Lc μ₀ hL G
  have hC := hC C hC0.1.2 D large₂ he hx.1.2 hR T Lc μ₀ hL G
  have hD := hD C hC0.2 D large₂ he hx.2 hR T Lc μ₀ hL G
  intro W S hψ _ i j A A' WW X₀ c0 δ t0 hX₀ hc₀
  obtain ⟨X, ζ, hX, hβ, hζ, hc⟩ := hD W hψ i j A A' WW X₀ c0 hX₀ hc₀
  obtain ⟨Ω, hΩ, HA⟩ := hA W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨Ω', hΩ', HB⟩ := hB' W hψ i j A A' WW X δ t0 hX hβ
  obtain ⟨κ₀, hκ₀, HC⟩ := hC W hψ i j A A' WW X _ hX hc
  refine ⟨Ω * κ₀ * Ω', mul_ne_zero (mul_ne_zero hΩ hκ₀) hΩ', fun s Q P P' hP => ?_⟩
  obtain ⟨uA, huA, huAQ, huAu, HA⟩ := HA s Q P P' hP
  obtain ⟨uB, huB, huBQ, huBu, HB⟩ := HB s Q P P' hP
  obtain ⟨n, hn, hζn⟩ := hζ s
  obtain ⟨hz0, hzQ, hzu⟩ := GlobalTheory.BotFormula.root_unit hn hζn
  have ea : P.a = A.rank := hP.rank.1.trans hX.rank.symm
  have ea' : P'.a = A'.rank := hP.rank.2.1.trans hX.rank'.symm
  have ed : P.d = WW.rank := by rw [hP.rank.2.2.1, ← hX.is.rank, hX.rank, hX.rank']
  have ed' : P'.d = WW.rank := hP.rank.2.2.2.trans ed
  obtain ⟨M, M', hMM, HC⟩ := HC s Q δ t0 P P' hP ea ea' ed ed'
  refine ⟨uA * uB * ζ s, M, M', mul_ne_zero (mul_ne_zero huA huB) hz0, Qbar.mul_mem (Qbar.mul_mem huAQ huBQ) hzQ, fun p _ hp lam => ?_, fun hd h => ?_⟩
  · rw [GlobalTheory.BotFormula.lamC_mul lam (Qbar.mul_mem huAQ huBQ) hzQ, GlobalTheory.BotFormula.lamC_mul lam huAQ huBQ, norm_mul, norm_mul,
      huAu p hp lam, huBu p hp lam, hzu p lam, one_mul, one_mul]
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_finiteAdelicPoint_unitaryGroup_gramOne WW hX.stdW.1 h ed.symm
  have hg' := hg.cast hd
  have key : ∀ T, starRingEnd ℂ (P.coord h T) =
      Ω * κ₀ * Ω' * (uA * uB * ζ s) * c0 s * ∑ T', (M T T' : ℂ) * P'.coord (hd ▸ h) T' := by
    intro T
    rw [HA ea ed h g hg T, HC g T]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T' _ => ?_
    rw [HB ea' ed' (hd ▸ h) g hg' T']
    ring
  refine ⟨key, fun T' => ?_⟩
  simp_rw [key, Finset.mul_sum]
  rw [Finset.sum_comm]
  have e1 : ∀ T'' T, (M' T' T : ℂ) * (Ω * κ₀ * Ω' * (uA * uB * ζ s) * c0 s * ((M T T'' : ℂ) * P'.coord (hd ▸ h) T'')) =
      ((M' T' T * M T T'' : ℤ) : ℂ) * (Ω * κ₀ * Ω' * (uA * uB * ζ s) * c0 s * P'.coord (hd ▸ h) T'') := by
    intro T'' T; push_cast; ring
  simp_rw [e1, ← Finset.sum_mul, ← Int.cast_sum, hMM]
  simp only [apply_ite (Int.cast (R := ℂ)), Int.cast_one, Int.cast_zero, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rallis_inner_product_formula_first_occurrence : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ),
      IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ) (δ t0 : ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ (u : ℂ) (M : Tup D P.a P.d P.n → Tup D P'.a P'.d P'.n → ℤ) (M' : Tup D P'.a P'.d P'.n → Tup D P.a P.d P.n → ℤ),
          u ≠ 0 ∧ u ∈ Qbar ∧
          (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (hd : P'.d = P.d) (h : GA D P.d),
            (∀ T, starRingEnd ℂ (P.coord h T) = κ * u * c0 s * ∑ T', (M T T' : ℂ) * P'.coord (hd ▸ h) T') ∧
            ∀ T', P'.coord (hd ▸ h) T' * (κ * u * c0 s) = ∑ T, (M' T' T : ℂ) * starRingEnd ℂ (P.coord h T) := by
  first | exact @_root_.GlobalTheory.BotFormula.bottom_theta_petersson_norm_formula | exact _root_.GlobalTheory.BotFormula.bottom_theta_petersson_norm_formula | (intros; apply _root_.GlobalTheory.BotFormula.bottom_theta_petersson_norm_formula <;> assumption)
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SqTop.BotConstPf
end GlobalTheory.SqTop.BotConstPf
namespace GlobalTheory.SqTop
open BotConstPf
theorem botConst_of_inputs_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → BotSmall → LNe → BotConst := by
  intro hPr hK hM hInp hS hL
  refine gBig_imp (Model.gBig_and (Model.gBig_and (_root_.GlobalTheory.T.bottom_constant_ratio_eq_local_factor_ratio hPr hK hM hInp hS hL) (_root_.GlobalTheory.T.rallis_inner_product_formula_first_occurrence hPr hK hM hInp hS)) hS) ?_
  intro D T Lc sc G μ₀ C x b hμ H
  obtain ⟨⟨H1, H2⟩, hGood, htw, hSm⟩ := H
  intro W S hψ hN i j t A A' WW X c0 δ t0 P₀ P₀' P P' z z' C' dl hX hc hB₀ hB hz hz' hz0 hz'0 hI
  obtain ⟨hct, hc0, γ, hγ⟩ := H1 W S hψ hN i j t A A' WW X c0 hX hc
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hγ
    exact hct hγ.symm
  refine ⟨γ, hγ0, hc0, hγ, fun w hw => ?_⟩
  obtain ⟨κ, hκ, H⟩ := H2 W S hψ hN i j A A' WW X c0 δ t0 hX hc
  obtain ⟨-, hQn1, hmod⟩ := Model.base_tuple G hμ
  obtain ⟨u₁, M, M', hu₁, hu₁q, hu₁n, hr₁⟩ := H t _ P P' hB
  obtain ⟨u₂, N₁, N₂, hu₂, hu₂q, hu₂n, hr₂⟩ := H μ₀ _ P₀ P₀' (hmod ▸ hB₀)
  obtain ⟨S', del, hE, hCo, -, rfl⟩ := hI
  obtain ⟨p, hp, hpw⟩ := exists_prime_under w
  haveI : Fact p.Prime := ⟨hp⟩
  have hpQ : ¬ p ∣ Qn G t := fun hd => hw (by
    obtain ⟨k, hk⟩ := hd
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hpw)
  have hp1 : ¬ p ∣ Qn G μ₀ := by rw [hQn1]; exact hp.not_dvd_one
  obtain ⟨hv, hvn⟩ := lamC_div_norm hu₁q hu₂q (hu₁n p hpQ) (hu₂n p hp1)
  have hlev : padicValNat p (levQ G.pl * Qn G t) ≤ padicValNat p (levQ G.pl) := by
    have h0 : levQ G.pl ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ =>
      pow_ne_zero _ (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
    have hzQ : padicValNat p (Qn G t) = 0 := by
      simpa only [← Nat.padicValNat_def] using (multiplicity_eq_zero_of_not_dvd hpQ)
    rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) h0 (Model.Qn_ne_zero G t), hzQ, add_zero]
  have e1 := hB.rank
  have e2 := hB₀.rank
  have s1 := hSm δ t0 _ P P' t i j _ hB
  have s2 := hSm δ t0 _ P₀ P₀' μ₀ i j _ hB₀
  refine GlobalTheory.T.valuation_proportionalityRatio_le_bottomPairs D (bigN D) (maxWt D sc.cGap) (levQ G.pl) S' del _ (hInp D) hE hCo D.what₂.LL D.what₂.embLL w p hpw δ t0
    (levQ G.pl * Qn G t) (levQ G.pl) hlev le_rfl P P' P₀ P₀' s1.1 s1.2 s2.1 s2.2 e1.2.2.2 e2.2.2.2
    (κ * u₁ * c0 t) (κ * u₂ * c0 μ₀) (u₁ / u₂) M N₂ (fun h T => (hr₁ e1.2.2.2 h).1 T)
    (fun h T' => (hr₂ e2.2.2.2 h).2 T') (mul_ne_zero (mul_ne_zero hκ hu₂) hc0) hv hvn γ z z' ?_ hz hz' hz0 hz'0
  rw [← hγ]
  field_simp
end GlobalTheory.SqTop
end
end

section
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.botConst_of_theta_matching : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → (∀ D, GlobalTheory.NormSum.Inp D) → BotSmall → LNe → BotConst := by
  first | exact @_root_.GlobalTheory.SqTop.botConst_of_inputs_alt | exact _root_.GlobalTheory.SqTop.botConst_of_inputs_alt | (intros; apply _root_.GlobalTheory.SqTop.botConst_of_inputs_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomThetaNeZeroOfInnerProductFormula
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SqTop.BotNeFormula
set_option maxHeartbeats 4000000 in
theorem bottomTheta_ne_zero_of_innerProduct_formula : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → LNe → BotSmall → NormBig → TriEx → BotNe := by
  intro hPr hK hM hI hL hB hN hT
  have hA := _root_.GlobalTheory.T.theta_bottom_formula_large hPr hK hM hI hB
  have hB' := _root_.GlobalTheory.T.theta_bottom_formula_small hPr hK hM hI hB
  have hC := _root_.GlobalTheory.T.rallis_bottom_minor_matching hPr hK hM hI hB
  have hR := _root_.GlobalTheory.T.exists_bottom_basis_change hPr
  refine GlobalTheory.SqTop.BotConstPf.gBig_imp (GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and hL hB)
    (GlobalTheory.SqTop.Model.gBig_and hN hT)) (GlobalTheory.SqTop.Model.gBig_and hA (GlobalTheory.SqTop.Model.gBig_and hB' (GlobalTheory.SqTop.Model.gBig_and hC hR)))) ?_
  intro D T Lc sc G μ₀ C x b hLc ⟨⟨⟨l1, l2⟩, l3, l5⟩, a1, a2, a3, a4⟩
  intro δ t0 Q P P' i j hbot
  have hmod : modT G μ₀ = SqNum.condE G.pl := by simp [modT, l2.2.1]
  rw [← hmod] at hbot
  obtain ⟨Λ, hΛ, hnz⟩ := (l1 i j).1 μ₀
  have hh : (h0 D i j : ℤ) ≤ halfRank D i j := by exact_mod_cast squareBottomHalfRankSum_le_halfRank D i j
  obtain ⟨Aa, hAa, hAn⟩ := l3 δ t0 i j
  have hP : P.norm ≠ 0 := by
    intro h0'
    have e := hAn μ₀ Q P P' Λ hbot hΛ
    rw [h0', Complex.ofReal_zero] at e
    refine mul_ne_zero hAa (Finset.prod_ne_zero_iff.2 fun s hs => ?_) e.symm
    rw [Finset.mem_Icc] at hs
    exact hnz s hs.1 (hs.2.trans hh)
  obtain ⟨h, Tt, hne⟩ := exists_coord_ne_of_norm_ne P hP
  refine ⟨⟨h, Tt, hne⟩, ?_⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.Ker.Model.exists_stdChar D
  obtain ⟨W, hWψ⟩ := GlobalTheory.GridWeil.exists_weil hPr.weilRepresentationUnitaryPair D T Lc μ₀ hLc sc G ψ hψ
  have hψW : IsStdChar D W.ψ (-1) := hWψ ▸ hψ
  obtain ⟨A, A', WW, X₀, c₀, hX₀, hc₀⟩ := l5 W hψW i j
  obtain ⟨X, ζ, hX, hβ, -, hc⟩ := a4 W hψW i j A A' WW X₀ c₀ hX₀ hc₀
  obtain ⟨Ω, -, HA⟩ := a1 W hψW i j A A' WW X δ t0 hX hβ
  obtain ⟨Ω', -, HB⟩ := a2 W hψW i j A A' WW X δ t0 hX hβ
  obtain ⟨κ₀, -, HC⟩ := a3 W hψW i j A A' WW X _ hX hc
  obtain ⟨uA, -, -, -, HA⟩ := HA μ₀ Q P P' hbot
  obtain ⟨uB, -, -, -, HB⟩ := HB μ₀ Q P P' hbot
  have ea : P.a = A.rank := hbot.rank.1.trans hX.rank.symm
  have ea' : P'.a = A'.rank := hbot.rank.2.1.trans hX.rank'.symm
  have ed : P.d = WW.rank := by rw [hbot.rank.2.2.1, ← hX.is.rank, hX.rank, hX.rank']
  have hd : P'.d = P.d := hbot.rank.2.2.2
  have ed' : P'.d = WW.rank := hd.trans ed
  obtain ⟨M, -, -, HC⟩ := HC μ₀ Q δ t0 P P' hbot ea ea' ed ed'
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_finiteAdelicPoint_unitaryGroup_gramOne WW hX.stdW.1 h ed.symm
  have hg' := hg.cast hd
  by_contra hz
  push Not at hz
  apply hne
  have e := HA ea ed h g hg Tt
  rw [HC g Tt] at e
  have hs : ∑ T', (M Tt T' : ℂ) * X.I' W.ψ W.θ μ₀ (GlobalTheory.BotFormula.minorF ea' ed' T') g = 0 := by
    refine Finset.sum_eq_zero fun T' _ => ?_
    rw [HB ea' ed' (hd ▸ h) g hg' T', hz, mul_zero, mul_zero]
  rw [hs, mul_zero, mul_zero] at e
  simpa using e
end GlobalTheory.SqTop.BotNeFormula
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomTheta_nonvanishing : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → (∀ D, GlobalTheory.NormSum.Inp D) → LNe → BotSmall → NormBig → TriEx → BotNe := by
  first | exact @_root_.GlobalTheory.SqTop.BotNeFormula.bottomTheta_ne_zero_of_innerProduct_formula | exact _root_.GlobalTheory.SqTop.BotNeFormula.bottomTheta_ne_zero_of_innerProduct_formula | (intros; apply _root_.GlobalTheory.SqTop.BotNeFormula.bottomTheta_ne_zero_of_innerProduct_formula <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.NormBigOfNonvanishing
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BigThetaLiftNeZeroOfPeterssonNorm
section
noncomputable section
open NumberField
open GlobalTheory.SqTop
namespace GlobalTheory.NormBigNe
theorem big_theta_petersson_norm_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.GBig fun {D} _ _ _ G _ _ _ _ =>
  ∀ (δ t0 : ℂ) (i j : Fin D.R.m) t (Q : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q),
    GlobalTheory.FunObj.SqNum.IsBottom G t i j (GlobalTheory.SqTop.modT G t) P P' → P.norm ≠ 0 := by
  rintro hP hI ⟨a, k⟩
  refine ⟨a, fun ε CF hCF => ?_⟩
  obtain ⟨c, x, l⟩ := k ε CF hCF
  refine ⟨c, x, fun C hC D large₂ he hx hR T Lc μ₀ hμ G δ t0 i j t Q P P' hb => ?_⟩
  obtain ⟨Λ, hΛ, hne⟩ := (l C hC D large₂ he hx hR T Lc μ₀ hμ G i j).1 t
  have e := _root_.GlobalTheory.NormRatio.petersson_norm_bottom_theta_lift_eq hP (hI D) hR hμ G hb hΛ
  have hrk := GlobalTheory.FunObj.SqNum.Model.bot_ranks (D := D) i j
  have hPa := hb.rank.1
  have hPd := hb.rank.2.2.1
  have hre : 0 < (((P.d - P.a : ℕ) : ℂ) / 2).re := by
    have : (0 : ℝ) < ((P.d - P.a : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < P.d - P.a)
    rw [show (((P.d - P.a : ℕ) : ℂ) / 2) = ((((P.d - P.a : ℕ) : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    positivity
  intro h0
  rw [h0, Complex.ofReal_zero] at e
  refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.2 fun s hs => ?_) e.symm
  · unfold GlobalTheory.NormRatio.normFactor
    refine div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (GlobalTheory.NormRatio.std_mass_ne_zero D _))
      (GlobalTheory.NormRatio.std_mass_ne_zero D _))
      (GlobalTheory.NormRatio.fockSum_ne_zero D _ _ _ P.a_le)) ?_) (GlobalTheory.LFun.dSfun_ne_zero_of_re_pos _ _ _ hre)
    · exact_mod_cast (GlobalTheory.NormExact.normConst_pos P.crv _ _).ne'
    · exact_mod_cast GlobalTheory.VacuumNorm.vacNorm_ne_zero D ⊤ δ t0 P.crv P.pt0 _ _
  · obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.1 hs
    exact hne s hs1 (hs2.trans (by exact_mod_cast GlobalTheory.SqTop.squareBottomHalfRankSum_le_halfRank D i j))
end GlobalTheory.NormBigNe
end
end

section
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.big_theta_lift_ne_zero_of_petersson_norm : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.GBig fun {D} _ _ _ G _ _ _ _ =>
  ∀ (δ t0 : ℂ) (i j : Fin D.R.m) t (Q : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q),
    GlobalTheory.FunObj.SqNum.IsBottom G t i j (GlobalTheory.SqTop.modT G t) P P' → P.norm ≠ 0 := by
  first | exact @_root_.GlobalTheory.NormBigNe.big_theta_petersson_norm_ne_zero | exact _root_.GlobalTheory.NormBigNe.big_theta_petersson_norm_ne_zero | (intros; apply _root_.GlobalTheory.NormBigNe.big_theta_petersson_norm_ne_zero <;> assumption)
end
end

section
open Finset
open GlobalTheory.SqTop GlobalTheory.FunObj.SqNum
open GlobalTheory.NormSum (Pair)
open GlobalTheory.CMVal (IsHeckeL)
namespace GlobalTheory.NormBigProof
theorem normBig_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → LNe → NormBig := by
  intro hP hI hL
  obtain ⟨a1, k1⟩ := hL
  obtain ⟨a2, k2⟩ := _root_.GlobalTheory.T.theta_lift_petersson_norm_ratio_formula hP hI ⟨a1, k1⟩
  obtain ⟨a3, k3⟩ := _root_.GlobalTheory.T.big_theta_lift_ne_zero_of_petersson_norm hP hI ⟨a1, k1⟩
  refine ⟨max a1 (max a2 a3), fun ε CF hCF => ?_⟩
  obtain ⟨c1, x1, l1⟩ := k1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨c2, x2, l2⟩ := k2 ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨c3, x3, l3⟩ := k3 ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max c1 (max c2 c3), max x1 (max x2 x3), fun C hC D large₂ he hx hRec T Lc μ₀ hμ G => ?_⟩
  have hl := l1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hRec T Lc μ₀ hμ G
  have hr := l2 C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hRec T Lc μ₀ hμ G
  have hz := l3 C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hRec T Lc μ₀ hμ G
  intro δ t0 i j
  by_cases hex : ∃ (t : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G t i j (modT G t) P P'
  · obtain ⟨t₀, Q₀, P₀, P₀', hb₀⟩ := hex
    obtain ⟨Λ₀, hΛ₀, hne⟩ := (hl i j).1 t₀
    have hprod : ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ₀ s ≠ 0 :=
      prod_ne_zero_iff.2 fun s hs => hne s (mem_Icc.1 hs).1
        (le_trans (mem_Icc.1 hs).2 (by exact_mod_cast squareBottomHalfRankSum_le_halfRank D i j))
    have hn₀ : (P₀.norm : ℂ) ≠ 0 := by exact_mod_cast hz δ t0 i j t₀ Q₀ P₀ P₀' hb₀
    refine ⟨(P₀.norm : ℂ) / ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ₀ s, div_ne_zero hn₀ hprod,
      fun t Q P P' Λ hb hΛ => ?_⟩
    have e := hr δ t0 i j t t₀ Q Q₀ P P' P₀ P₀' Λ Λ₀ hb hb₀ hΛ hΛ₀
    rw [div_mul_eq_mul_div, eq_div_iff hprod, e]
  · exact ⟨1, one_ne_zero, fun t Q P P' Λ hb _ => absurd ⟨t, Q, P, P', hb⟩ hex⟩
end GlobalTheory.NormBigProof
end

section
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normBig_of_lNe : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → LNe → NormBig := by
  first | exact @_root_.GlobalTheory.NormBigProof.normBig_alt | exact _root_.GlobalTheory.NormBigProof.normBig_alt | (intros; apply _root_.GlobalTheory.NormBigProof.normBig_alt <;> assumption)
end
end

section
namespace GlobalTheory.SqTop
theorem square_top_term_joined_estimates : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators → GlobalTheory.SqTop.Refl → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SqTop.DenSum ∧ GlobalTheory.SqTop.ThbSt ∧ GlobalTheory.SqTop.OneSqSt ∧ GlobalTheory.SqTop.BotSmall ∧ GlobalTheory.SqTop.BotNe ∧ GlobalTheory.SqTop.FieldDat ∧ GlobalTheory.SqTop.TorEx ∧ GlobalTheory.SqTop.DenEx ∧ GlobalTheory.SqTop.BotEx ∧ GlobalTheory.SqTop.LNe ∧ GlobalTheory.SqTop.TriEx ∧ GlobalTheory.SqTop.Tower := by
  intro hHD hPr hFE hTD hTr hZD hRefl hTI hLM
  have hS := GlobalTheory.T.completedHeckeL_bounded_in_vertical_strips
  have hInp := GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied
  have hF : FieldDat := GlobalTheory.SqTop.fieldDat
  have hL : LNe := GlobalTheory.SqTop.lNe_of_functionalEquation hFE hS hF
  have hLB : LBound := GlobalTheory.T.heckeLValue_upperBound_permutedWeights_of_FE hFE hS hF
  have hTor : TorEx := GlobalTheory.ToricExist.torEx hTr hF hL
  have hBA : BetaArch := GlobalTheory.T.betaConjugate_mean_logAbs_bound_of_transport hTr hF hLB hTor
  have hDE : DenEx := GlobalTheory.DenExist.denEx hZD hF
  have hDS : DenSum := GlobalTheory.DenSumPf.denSum hZD hF
  have hThb : ThbSt := GlobalTheory.T.toricValueHeightBound_of_denominatorsMeans hTD hF hTor hDE hDS hBA
  have hBS : BotSmall := GlobalTheory.SqTop.BotSmallProof.botSmall_holds
  have hBC : BotConst := _root_.GlobalTheory.T.botConst_of_theta_matching hPr hTI hLM hInp hBS hL
  have hBE : BotEx := GlobalTheory.T.bottomPairs_exist_baseTuple hInp
  have hBET : BotExT := GlobalTheory.T.bottomPairsExistEveryTuple_of_cmThetaHypotheses hInp
  have hNB : NormBig := _root_.GlobalTheory.T.normBig_of_lNe hPr hInp hL
  have hRL : RhoLow := GlobalTheory.T.lValueRatio_lower_bound_gauge hTD hF hTor
  have hTri : TriEx := _root_.GlobalTheory.T.triEx_of_howe_duality_real hHD hPr hTI hLM hL
  have hBN : BotNe := _root_.GlobalTheory.T.bottomTheta_nonvanishing hPr hTI hLM hInp hL hBS hNB hTri
  have hTw : Tower := _root_.GlobalTheory.T.tower_of_theta_matching_lNe hPr hTI hLM hL
  have hOne : OneSqSt := GlobalTheory.T.square_ratio_valuation_without_norm_formula hInp hL hTor hBS hBET hNB hBN hTri hTw hBC hRefl hRL
  exact ⟨hDS, hThb, hOne, hBS, hBN, hF, hTor, hDE, hBE, hL, hTri, hTw⟩
end GlobalTheory.SqTop
end

section
theorem _root_.GlobalTheory.T.square_leading_term_bound : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators → GlobalTheory.SqTop.Refl → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SqTop.DenSum ∧ GlobalTheory.SqTop.ThbSt ∧ GlobalTheory.SqTop.OneSqSt ∧ GlobalTheory.SqTop.BotSmall ∧ GlobalTheory.SqTop.BotNe ∧ GlobalTheory.SqTop.FieldDat ∧ GlobalTheory.SqTop.TorEx ∧ GlobalTheory.SqTop.DenEx ∧ GlobalTheory.SqTop.BotEx ∧ GlobalTheory.SqTop.LNe ∧ GlobalTheory.SqTop.TriEx ∧ GlobalTheory.SqTop.Tower := by
  first | exact @_root_.GlobalTheory.SqTop.square_top_term_joined_estimates | exact _root_.GlobalTheory.SqTop.square_top_term_joined_estimates | (intros; apply _root_.GlobalTheory.SqTop.square_top_term_joined_estimates <;> assumption)
end
