module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPointwiseArchimedeanDecayBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOnWeilDatumTransportAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFourth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoefficientMapExtremalEqPhaseSmulLetters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaChrTied
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryStandardCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingConjugateOscillatorEighth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuumEntireFactorIsThetaMovedLattices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationBijectiveSchwartz

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModerateGrowthHeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModerateGrowthHeight
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace GlobalTheory.ThetaModGrowthPair

theorem theta_modGrowth : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  have hlat := GlobalTheory.T.adelicThetaSum_norm_le_polynomial_scale
  have hfin := GlobalTheory.T.weilRep_rational_support_common_denominator
  have harch := GlobalTheory.T.weilRepresentation_pointwise_archimedeanDecay_bound
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨N₀, k₂, C₂, hL⟩ := hlat F (Fin n × Fin d)
  obtain ⟨C₁, k₁, hA⟩ := harch F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ N₀
  obtain ⟨C₃, k₃, hF⟩ := hfin F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  refine ⟨|C₂| * |C₁| * |C₃| ^ k₂, k₁ + k₃ * k₂, fun g h => ?_⟩
  obtain ⟨m, hm1, hmC, hsupp⟩ := hF g h
  set H : ℝ := (ht g : ℝ) * ht h with hH
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  have hb := hL (C₁ * H ^ k₁) m (om (g, h) Φ) hm1 (fun ξ => hA g h _) hsupp
  have hA0 : 0 ≤ C₁ * H ^ k₁ :=
    le_trans (by positivity) (hA g h (fun i => algebraMap F (AF F) ((0 : Fin n × Fin d → F) i)))
  have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ k₂ := by positivity
  have hmk : (m : ℝ) ^ k₂ ≤ (|C₃| * H ^ k₃) ^ k₂ :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (hmC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _))) _
  have hC1 : C₁ * H ^ k₁ ≤ |C₁| * H ^ k₁ := mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _)
  show ‖thetaSum F (om (g, h) Φ)‖ ≤ _
  calc ‖thetaSum F (om (g, h) Φ)‖ ≤ C₂ * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ := hb
    _ ≤ |C₂| * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hA0) hm0
    _ ≤ |C₂| * (|C₁| * H ^ k₁) * (|C₃| * H ^ k₃) ^ k₂ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hC1 (abs_nonneg _)) hmk hm0 (mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (pow_nonneg hH0 _)))
    _ = |C₂| * |C₁| * |C₃| ^ k₂ * H ^ (k₁ + k₃ * k₂) := by rw [pow_add, pow_mul]; ring

end GlobalTheory.ThetaModGrowthPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModerateGrowthHeightStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_moderate_growth_height : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  first | exact @GlobalTheory.ThetaModGrowthPair.theta_modGrowth | exact GlobalTheory.ThetaModGrowthPair.theta_modGrowth | (intros; apply GlobalTheory.ThetaModGrowthPair.theta_modGrowth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlacesUnderSplitCoprimeConductor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlacesUnderSplitCoprimeConductor
open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory.KummerTwistLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem twist_places_under_split_coprime_conductor : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T), GlobalTheory.CMVal.IsFinSetSplitPlacesCoprimeConductor (GlobalTheory.FunObj.SqNum.condF G.pl) ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) := by
  intro D T L sc G μ₀ hL t q hq
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
  have hP' : P ∈ L.Q t ∧ P ∉ G.pl.W0 := by
    simp only [GlobalTheory.SqTop.twPl, Finset.mem_filter] at hP
    rcases Finset.mem_union.1 hP.1 with h | h
    · exact absurd h hP.2
    · exact ⟨h, hP.2⟩
  refine ⟨⟨P, Formalism.DivisionValues.conjPl P, fun e => ?_, rfl, ?_⟩, ?_⟩
  · apply (hL.Q_pl t P hP'.1).2 P hP'.1
    intro c hc
    refine ⟨Formalism.DivisionValues.cO _ c, ?_, rfl⟩
    have h : Formalism.DivisionValues.cO _ c ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hc
    rwa [← e] at h
  · exact congrArg HeightOneSpectrum.asIdeal (GlobalTheory.TwistTypePlaces.under_conjPl P)
  · have hS : P.under (𝓞 D.host.F) ∉ G.pl.S0 := by
      intro h
      rcases G.pl.mem_S0_of_sum_eq.1 h with h0 | h1
      · exact G.pl.levelPlace_ne_basePlace t P hP'.1 h0
      · apply hP'.2
        rw [G.pl.w_Q t P hP'.1 h1]
        exact Finset.mem_image_of_mem _ h
    have h0 := GlobalTheory.FunObj.SqNum.Model.expIn_condF G.pl (P.under (𝓞 D.host.F))
    rw [if_neg hS] at h0
    have hne : GlobalTheory.FunObj.SqNum.condF G.pl ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun u _ => pow_ne_zero _ u.ne_bot
    exact (multiplicity_eq_zero (FiniteMultiplicity.of_prime_left (P.under (𝓞 D.host.F)).prime hne)).1 h0

end GlobalTheory.KummerTwistLemmas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlacesUnderSplitCoprimeConductorStatement
open NumberField IsDedekindDomain
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinSetSplitPlacesCoprimeConductor_twPl_under : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T), GlobalTheory.CMVal.IsFinSetSplitPlacesCoprimeConductor (GlobalTheory.FunObj.SqNum.condF G.pl) ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) := by
  first | exact @GlobalTheory.KummerTwistLemmas.twist_places_under_split_coprime_conductor | exact GlobalTheory.KummerTwistLemmas.twist_places_under_split_coprime_conductor | (intros; apply GlobalTheory.KummerTwistLemmas.twist_places_under_split_coprime_conductor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTransportCmExtensionIsUnitaryOn
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTransportCmExtensionIsUnitaryOn
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.WeilAdmCMUnit

theorem isUnitaryOn_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om :=
  GlobalTheory.T.isUnitaryOn_weilDatum_transport_adelicSchwartz

end GlobalTheory.WeilAdmCMUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTransportCmExtensionIsUnitaryOnStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatumTransport_cmExtension_isUnitaryOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → IsUnitaryOn (adeleClass F) om := by
  first | exact @GlobalTheory.WeilAdmCMUnit.isUnitaryOn_transport | exact GlobalTheory.WeilAdmCMUnit.isUnitaryOn_transport | (intros; apply GlobalTheory.WeilAdmCMUnit.isUnitaryOn_transport <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateWeilRepresentationThird
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne


set_option maxHeartbeats 1000000 in
theorem integral_theta_chi {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank)
    (hL : ∀ k, k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β L ↔ k ∈ Formalism.L2.DIV.lev D.sp.cm S.gram β (Lev.flag1L L))
    (χ' : (levEnv S β L).J →* ℂˣ)
    {f : Bridge.Gf S → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J χ')
    (Λ : c.W →ₗ[ℂ] (WO S T → ℂ)) (hΛ : ∀ w, IsThetaFunO ψ S T (Λ w))
    (hΛa : ∀ a ∈ GinfC S, ∀ w, om (a, 1) (Λ w) = Λ (c.ρ a w))
    (hΛk : ∀ k ∈ GfC S, ∀ hk : fin S k ∈ (levEnv S β L).J, ∀ w,
      om (k, 1) (Λ w) = ((χ' ⟨fin S k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ w)
    {ν : Measure (GA D S)} {𝓕 : Set (GA D S)} (hν : IsMeasDef S (Formalism.L2.DIV.lev D.sp.cm S.gram β L) ν 𝓕)
    (J' : Subgroup (Bridge.Gf S)) (Cl : Type) [Fintype Cl] (h : Cl → GA D S) (hle : J' ≤ (levEnv S β L).J)
    (hN : J'.relIndex (levEnv S β L).J ≠ 0) (hy : Bridge.IsReps (Bridge.ratF S) J' (fun k => fin S (h k)))
    (hh : ∀ k, h k ∈ GfC S) (g : GA D T) :
    ∫ x in 𝓕, thetaKO om x g (Λ (c.ext f x)) ∂ν = ∑ k, ((J'.relIndex (levEnv S β L).J : ℕ) : ℂ)⁻¹ *
      ((Nat.card (Bridge.stab (Bridge.ratF S) J' (fin S (h k))) : ℕ) : ℂ)⁻¹ * thetaKO om (h k) g (Λ (f (fin S (h k)))) := by
  rw [GlobalTheory.ClsInt.integral_eq_classSum_of_le D S β L ν 𝓕 hp hs hν hL J' Cl h hle hN hy hh
    (fun x => thetaKO om x g (Λ (c.ext f x))) ?_ ?_]
  · exact Finset.sum_congr rfl fun k _ => by rw [ext_fin c hc f (hh k)]
  · intro γ hγ x
    have e : (γ * x, g) = ((γ, 1) : GA D S × GA D T) * (x, g) := by rw [Prod.mk_mul_mk, one_mul]
    simp only [thetaKO]
    rw [GlobalTheory.ThetaIntegrand.ext_invariant c hf γ hγ, e, map_mul]
    exact hom.om_aut γ hγ 1 (one_mem _) _ (hom.om_pres _ _ (hΛ _))
  · intro u hu x
    refine (GlobalTheory.LiftUnfold.exists_fin_mul_real S u).elim fun k hk0 => hk0.2.elim fun a ha0 => ?_
    have hk := hk0.1
    have ha := ha0.1
    have e := ha0.2.2
    have hk' : fin S k ∈ (levEnv S β L).J := by rw [e]; exact hu
    have h1 : c.ρ k⁻¹ = 1 := hc.1 _ (inv_mem hk)
    have h2 : (finHom S).rangeRestrict a = 1 := Subtype.ext (MonoidHom.mem_ker.1 ha)
    have h3 := GlobalTheory.LiftUnfold.form_right (Bridge.ratF S) c.coef.ρ hf ⟨fin S k, hk'⟩
    have h4 := GlobalTheory.LiftUnfold.integrand_right om c.ρ (finHom S).rangeRestrict Λ f u k a ha0.2.1 (χ' ⟨fin S k, hk'⟩)
      h1 h2 h3 (hΛk k hk hk') (hΛa a ha) x g
    exact congrFun h4 0

end GlobalTheory.GalOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAndNuRamifiedPlaceDegreeOneExponentTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAndNuRamifiedPlaceDegreeOneExponentTwo
open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.BadPlaceExp

theorem under_eq_of_isConjPl {D : D7} {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl w w') :
    w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) := by
  have le : (w.under (𝓞 D.host.F)).asIdeal ≤ (w'.under (𝓞 D.host.F)).asIdeal := by
    intro c hc
    obtain ⟨c', h1, h2⟩ := h _ hc
    have hs : star ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) =
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) := by
      letI := D.host.isCMField_hostE
      exact IsCMField.complexConj_apply_eq_self D.host.E (c : D.host.F)
    have : c' = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c := RingOfIntegers.ext (h2.trans hs)
    show algebraMap _ _ c ∈ w'.asIdeal
    rwa [← this]
  exact HeightOneSpectrum.ext ((w.under (𝓞 D.host.F)).isMaximal.eq_of_le (w'.under (𝓞 D.host.F)).isPrime.ne_top le)

theorem main : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ → IsBaseCond (condF G.pl) → ∀ (i j : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)), ¬ (Lc.xiH t).UnrAt w → ¬ (nuH G μ₀ i j).UnrAt w → ∃ q : ℕ, q.Prime ∧ Nat.card (𝓞 D.host.E ⧸ w.asIdeal) = q ∧ (q : 𝓞 D.host.E) ∉ w.asIdeal ^ 2 ∧ ExpAt (nuH G μ₀ i j) w 2 := by
  intro D T Lc sc G μ₀ hL hB i j t w hx hn
  have hm := Lc.C.isMu0 j
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have e : nuH G μ₀ i j = Lc.C.mu0 j / G.ch.chiH (D.R.m - i) := by
    rw [nuH, hL.xi_base, mul_one]
  have hE : ExpAt (nuH G μ₀ i j) w (expIn (condF G.pl) (w.under (𝓞 D.host.F))) := by
    rw [e]
    refine Model.expAt_div G a1 a2 hm.tame (fun Q hQ => hm.unr Q fun k hk => hQ ((S1_mem_OmF D).2 ?_)) w
    have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ Q.asIdeal
      rw [map_natCast]; exact hk
    fin_cases k
    · exact Or.inl this
    · exact Or.inr (Or.inl this)
  have hS0 : w.under (𝓞 D.host.F) ∈ G.pl.S0 := by
    by_contra h
    rw [Model.expIn_condF, if_neg h] at hE
    exact hn ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 ((hE 0).2 le_rfl))
  have hv0 : w.under (𝓞 D.host.F) ≠ G.pl.v0 := by
    rcases (hL.Q_ram t w).1 hx with h | ⟨PP', hP', hc⟩
    · exact G.pl.levelPlace_ne_basePlace t w h
    · rw [← under_eq_of_isConjPl hc]; exact G.pl.levelPlace_ne_basePlace t PP' hP'
  have hc2 : condExp G.pl (w.under (𝓞 D.host.F)) = 2 := by rw [condExp, if_neg hv0]
  have h2 : expIn (condF G.pl) (w.under (𝓞 D.host.F)) = 2 := by
    rw [Model.expIn_condF, if_pos hS0, hc2]
  rw [h2] at hE
  have hdvd : (w.under (𝓞 D.host.F)).asIdeal ∣ condF G.pl :=
    (dvd_pow_self _ (by rw [hc2]; norm_num)).trans (Finset.dvd_prod_of_mem _ hS0)
  obtain ⟨-, -, hb⟩ := hB
  obtain ⟨-, -, l, hl, -, hlv, hdisc, hnorm⟩ := hb _ hdvd
  have hlw : (l : 𝓞 D.host.E) ∈ w.asIdeal := by
    have : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (l : 𝓞 D.host.F) ∈ w.asIdeal := hlv
    rwa [map_natCast] at this
  refine ⟨l, hl, ?_, ?_, hE⟩
  · rw [← hnorm w hlw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · exact GlobalTheory.Mem.RaySplit.not_mem_sq hl hlw
      ((GlobalTheory.Mem.RaySplit.not_dvd_discr_iff_ramificationIdx D.host.E hl).1 hdisc _ w.isPrime hlw)

end GlobalTheory.BadPlaceExp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAndNuRamifiedPlaceDegreeOneExponentTwoStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_and_nu_ramified_place_degree_one_exponent_two : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ → IsBaseCond (condF G.pl) → ∀ (i j : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)), ¬ (Lc.xiH t).UnrAt w → ¬ (nuH G μ₀ i j).UnrAt w → ∃ q : ℕ, q.Prime ∧ Nat.card (𝓞 D.host.E ⧸ w.asIdeal) = q ∧ (q : 𝓞 D.host.E) ∉ w.asIdeal ^ 2 ∧ ExpAt (nuH G μ₀ i j) w 2 := by
  first | exact @GlobalTheory.BadPlaceExp.main | exact GlobalTheory.BadPlaceExp.main | (intros; apply GlobalTheory.BadPlaceExp.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanTranslatesEqTop
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open Classical

noncomputable section
namespace GlobalTheory.LowSpan

theorem span_translates_eq_top : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : Formalism.IndefR.Mult.DSModel V S) (v : M.Vec), IsExtVec M v → ∀ τ : D.what₂.Tau, Formalism.MainNotions.S.IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ)) → Submodule.span ℂ {u : lowT M τ | ∃ k ∈ Formalism.REAL.Kset (M.ε τ), ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ)} = ⊤ := by
  intro D V S M v hv τ hK
  obtain ⟨_hfd, hst, hirr, -, -⟩ := hK
  obtain ⟨-, -, hU, -⟩ := M.ds τ
  obtain ⟨S₀, hS₀, hS₀sm⟩ := GlobalTheory.SmoothLowType.exists_lowK_le_sm D V S M τ
  have hle : S₀ ≤ Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ) :=
    le_sSup (s := {T | Formalism.MainNotions.S.IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) T}) hS₀
  have hS₀ne : S₀ ≠ ⊥ := by
    obtain ⟨w, hw, hw0, -⟩ := hS₀.2.2.2.1
    intro h; rw [h] at hw; exact hw0 ((Submodule.mem_bot ℂ).1 hw)
  have hLsm : Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ≤ M.sm τ := by
    rcases hirr S₀ hle hS₀.2.1 with h | h
    · exact absurd h hS₀ne
    · rw [← h]; exact hS₀sm

  set L := Formalism.MainNotions.S.lowKSub (M.ε τ) (M.lam τ) (M.σ τ) with hLdef
  set v0 : M.H τ := ((v τ : M.sm τ) : M.H τ) with hv0def
  have hv0L : v0 ∈ L := (hv τ).2.1
  have hv00 : v0 ≠ 0 := by
    intro h; have h1 := (hv τ).1; rw [← hv0def, h, norm_zero] at h1; exact zero_ne_one h1
  set T : Set (M.H τ) := {x | ∃ k ∈ Formalism.REAL.Kset (M.ε τ), x = M.σ τ k v0} with hTdef
  have hWL : Submodule.span ℂ T ≤ L := by
    rw [Submodule.span_le]; rintro _ ⟨k, hk, rfl⟩; exact hst k hk _ hv0L
  have hWst : Formalism.MainNotions.S.IsKStableOn (M.ε τ) (M.σ τ) (Submodule.span ℂ T) := by
    intro g hg x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, hk, rfl⟩ := hy
      apply Submodule.subset_span
      refine ⟨g * k, Formalism.REAL.Kset_mul _ hg hk, ?_⟩
      rw [hU.1.2 g (kset_uj hg) k (kset_uj hk)]; rfl
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have h1K : (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.REAL.Kset (M.ε τ) := by
    have := diag_mem (ε := M.ε τ) (fun _ => (0 : ℝ))
    simpa using this
  have hW0 : Submodule.span ℂ T ≠ ⊥ := by
    intro h
    have : v0 ∈ Submodule.span ℂ T := Submodule.subset_span ⟨1, h1K, by rw [hU.1.1]; rfl⟩
    rw [h] at this; exact hv00 ((Submodule.mem_bot ℂ).1 this)
  have hWeq : Submodule.span ℂ T = L := (hirr _ hWL hWst).resolve_left hW0
  let f : lowT M τ →ₗ[ℂ] M.H τ := (M.sm τ).subtype ∘ₗ (lowT M τ).subtype
  have hf : Function.Injective f := (M.sm τ).injective_subtype.comp (lowT M τ).injective_subtype
  apply Submodule.map_injective_of_injective hf
  rw [Submodule.map_span, Submodule.map_top]
  have himg : f '' {u : lowT M τ | ∃ k ∈ Formalism.REAL.Kset (M.ε τ), ((u : M.sm τ) : M.H τ) = M.σ τ k v0} = T := by
    ext x; constructor
    · rintro ⟨u, ⟨k, hk, hu⟩, rfl⟩; exact ⟨k, hk, hu⟩
    · rintro ⟨k, hk, rfl⟩
      have hxL : M.σ τ k v0 ∈ L := hst k hk _ hv0L
      exact ⟨⟨⟨_, hLsm hxL⟩, hxL⟩, ⟨k, hk, rfl⟩, rfl⟩
  rw [himg, hWeq]
  ext y; constructor
  · intro hy; exact ⟨⟨⟨y, hLsm hy⟩, hy⟩, rfl⟩
  · rintro ⟨x, rfl⟩; exact x.2

end GlobalTheory.LowSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingConjugateOscillatorNinth
noncomputable section

namespace GlobalTheory.GalOne.IoCmp

section Letters

open NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem letter_relab {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} {σ : c.F →+* ℂ}
    {X : Data E r} {g q0 n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} (Dc : Dic Dw c σ X g q0 n a)
    (hm : ∀ τ, Formalism.L2.PjFree.relab c σ τ ∉ X.Ψ → Dw.mult τ ≤ X.p0) (ℓ : Formalism.L2.Pj.LtN Dw n) :
    (Dc.eL ℓ).2.2 = ℓ.2.2 ∧
      ((∃ k, (Dc.eL ℓ).2.1 = Sum.inl k ∧ Formalism.L2.PjFree.relab c σ ℓ.1 = (Dc.eL ℓ).1.1 ∧ (k : ℕ) = ℓ.2.1) ∨
       (∃ k, (Dc.eL ℓ).2.1 = Sum.inr k ∧ Formalism.L2.PjFree.relab c σ ℓ.1 = conjEmb (Dc.eL ℓ).1.1 ∧ (k : ℕ) = ℓ.2.1)) := by
  have hd := Dc.dir_eq ℓ
  generalize Dc.eL ℓ = L at hd ⊢
  obtain ⟨t, ρ, b⟩ := L
  obtain ⟨τ, i, b'⟩ := ℓ
  simp only [letterDir] at hd ⊢
  have hb : b = b' := by
    by_contra hne
    have := congrFun (congrFun hd b) (Dc.idx.symm (rowOf X Dc.hr (t, ρ)))
    simp [Pi.single_eq_of_ne hne] at this
  subst hb
  have hj : Dc.idx.symm (rowOf X Dc.hr (t, ρ)) = Dc.e.symm ⟨τ, i⟩ := by
    by_contra hne
    have := congrFun (congrFun hd b) (Dc.idx.symm (rowOf X Dc.hr (t, ρ)))
    rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
    exact one_ne_zero this
  have hi : Dc.idx (Dc.e.symm ⟨τ, i⟩) = (t, rowIdx Dc.hr ρ) := by rw [← hj, Equiv.apply_symm_apply]; rfl
  have hty := Dc.ty_eq (Dc.e.symm ⟨τ, i⟩)
  have hper : ∀ x v, per X x v (t, rowIdx Dc.hr ρ) = Formalism.L2.Pj.perFr X x v (Formalism.L2.PjFree.relab c σ τ) i := fun x v => by
    have := Dc.per_eq x v (Dc.e.symm ⟨τ, i⟩)
    rwa [pv, Function.comp_apply, hi, Equiv.apply_symm_apply] at this
  rw [hi, Equiv.apply_symm_apply] at hty
  refine ⟨rfl, ?_⟩
  rcases ρ with k | k
  · have h1 : Formalism.L2.PjFree.relab c σ τ = t.1 := hty.symm.trans (rowType_rowOf_inl X Dc.hr t k)
    rw [h1] at hper
    have h2 := coord_eq_of_per_mem X t _ (by simp) i hper
    rw [rowIdx_inl] at h2
    exact Or.inl ⟨k, rfl, h1, by omega⟩
  · have h1 : Formalism.L2.PjFree.relab c σ τ = conjEmb t.1 := hty.symm.trans (rowType_rowOf_inr X Dc.hr t k)
    rw [h1] at hper
    have hk := k.2
    have h2 := coord_eq_of_per_conj X t _ (by rw [rowIdx_inr]; omega) i hper
    rw [rowIdx_inr] at h2
    have h3 := hm τ (by rw [h1]; exact (X.cmType t.1).1 t.2)
    have h4 : (i : ℕ) < X.p0 := lt_of_lt_of_le i.2 h3
    exact Or.inr ⟨k, rfl, h1, by omega⟩

end Letters

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne
open GlobalTheory.OneMapRef.IoCmp

end GlobalTheory.GalOne.IoCmp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaOfUnitVacuum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

noncomputable section
namespace GlobalTheory.VacRead
open GlobalTheory.ThetaLawMoved GlobalTheory.ThetaLawOF

theorem theta_of_unit_vacuum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, δ ≠ 0 → ∀ (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Formalism.MainNotions.StandardLatticesGL3.SD D Ls → Formalism.MainNotions.StandardLatticesGL3.SD D Lt → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → (fun Y => Φ (δ⁻¹ • Y)) ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) Ls Lt := by
  intro D ψ θ S T frS frT hS hT δ hδ Ls Lt hLs hLt f hf Φ hΦd hΦ
  obtain ⟨ΛS, hΛS, hSd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV S frS hS Ls hLs
  obtain ⟨ΛT, hΛT, hTd⟩ := GlobalTheory.MovedDict.isSelfDualC_inV T frT hT Lt hLt
  rw [← hΛS, ← hΛT] at hf
  have hψ := hf.1
  have hθ := hf.2.inf
  obtain ⟨σ, hch⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, -, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hSd hTd
  refine ⟨hΦd.comp ((differentiable_id).const_smul δ⁻¹), ?_⟩
  intro x hx Y
  obtain ⟨v, hv, rfl⟩ := mem_La_frame_sd S T frS frT hS hT Ls Lt hLs δ x hx
  rw [← hΛS, ← hΛT] at hv
  have hv' : GlobalTheory.VacUnique.finRat S T (-v) ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) := by
    rw [AddMonoidHom.map_neg]; exact neg_mem hv
  obtain ⟨ε, -, hε⟩ := h3 f hf.2.lat _ hv'
  have hsign := sign_eq_alpha_sd ψ S T frS frT hS hT hψ ΛS ΛT hSd hTd δ hδ v hv ε (fun g hg => hε g hg)
  have hlaw := GlobalTheory.VacUnique.apply_add_infRat hch hψ hf.2.theta v (hε f hf.2.lat)
  set X : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b with hX
  set Z : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank := δ⁻¹ • Y with hZ
  have hZY : Y = δ • Z := by rw [hZ, smul_smul, mul_inv_cancel₀ hδ, one_smul]
  set z : GlobalTheory.FockCompare.RW T S := fun τ => GlobalTheory.FockPos.frAt frT τ * Matrix.of (Z τ) * (GlobalTheory.FockPos.frAt frS τ)⁻¹ with hz
  have hzτ : ∀ τ, (GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (z τ) * GlobalTheory.FockPos.frAt frS τ = Matrix.of (Z τ) :=
    fun τ => coord_back frS frT Z τ
  have hz1 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S z) = Z := by
    rw [zCo_iota hch]; funext τ; exact coord_back frS frT Z τ
  have hz2 : GlobalTheory.FockPos.zCo θ frS frT (GlobalTheory.FockCompare.iotaW σ T S (z + GlobalTheory.VacUnique.infRat S T v)) = Z + X := by
    rw [zCo_iota hch]; funext τ
    show (GlobalTheory.FockPos.frAt frT τ)⁻¹ * (Matrix.of (z τ) + Matrix.of (GlobalTheory.VacUnique.infRat S T v τ)) * GlobalTheory.FockPos.frAt frS τ = Z τ + X τ
    rw [Matrix.mul_add, Matrix.add_mul, hzτ τ]
    rfl
  have hom : GlobalTheory.VacUnique.omO S T (GlobalTheory.VacUnique.infRat S T v) z = ∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re := by
    rw [omO_frame frS frT hS hT]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hzτ τ]
    rfl
  have hl := hlaw z
  rw [hΦ _ (hch.real_iota T S _), hΦ _ (hch.real_iota T S _), GlobalTheory.FockPos.gaussO, GlobalTheory.FockPos.gaussO, hz1, hz2, hom, hsign] at hl

  simp only [Formalism.MainNotions.TaylorLogMetric.U]
  have e1 : δ⁻¹ • (Y + δ • X) = Z + X := by rw [smul_add, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  rw [e1, hZY, torusHermitianForm_scaled_coordinate_eq hδ, torusHermitianForm_scaled_coordinate_eq hδ]
  have hZZ : δ⁻¹ • δ • Z = Z := by rw [smul_smul, inv_mul_cancel₀ hδ, one_smul]
  rw [hZZ]
  set a := Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X) with ha
  have kE : Complex.exp (-(Real.pi * Complex.I) * ((-∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re : ℝ) : ℂ)) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) =
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := entry (Z τ i j) (X τ i j) (Formalism.L2.Pj.xiR D)
    push_cast at h ⊢
    linear_combination h
  apply mul_left_cancel₀ (Complex.exp_ne_zero (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)))
  rw [← kE]
  calc _ = a * Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) *
        (Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖(Z + X) τ a b‖ ^ 2 : ℝ) : ℂ)) * Φ (Z + X)) := by
        rw [kE]; ring
    _ = _ := by
        rw [hl]
        have := al_mul_self (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • X)
        rw [← ha] at this
        linear_combination (Complex.exp (-(Real.pi * Complex.I) * ((-∑ τ, ∑ a, ∑ b, 2 * (Complex.I * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) *
      (starRingEnd ℂ (Z τ a b) * X τ a b)).re : ℝ) : ℂ)) *
      Complex.exp (-((Real.pi * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, ((‖Z τ a b‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, Z τ a b * starRingEnd ℂ (X τ a b)) -
        (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2) * Φ Z) * this

end GlobalTheory.VacRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsActFockVectorsAnyDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsActFockVectorsAnyDatum
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.FockAnyDatum

theorem om_ioP_of_datum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (φ : WO (Vc D i) (Wc D i) → ℂ), IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) R.Pg Q ξR (R.vacP i) φ → ∀ u ∈ GinfC (Vc D i), ∀ x w, R.ωP i A.μ0 (u, 1) (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ (R.ioP i x w)) = pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ (R.ioP i x ((R.cV i).ρ u w)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξR Q φ hφ u hu x w
  have hθ : IsInfFam R.θ := hR.models.inf
  have hω := hR.thP.ωP
  have hthφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ := by
    obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := hφ
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ h h0.theta
  have hthv : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i A.μ0) := by
    obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := hR.thP.vP i A.μ0
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ h h0.theta
  have hvφ := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hφ hthφ
  have hvv := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hR.thP.vP i A.μ0) hthv
  have hBS : ∀ τ, (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = 1 := fun τ =>
    GlobalTheory.JointHarm.onb_eq_one (hR.models.BV i τ)
  have hBu : ∀ τ, IsUnit (R.BV i τ) := fun τ => IsUnit.of_mul_eq_one_right _ (hBS τ)
  obtain ⟨x₁, x₂, x₃, hx⟩ := GlobalTheory.T.lowestKType_coefficientWeight_eq_minorWeights D i (sg0 D A) (sgAt_mk _ R.hv0) (R.MW i (sg0 D A)) (hR.models.order i)
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 = (Wc D i).rank := fun τ =>
    (GlobalTheory.T.thetaWeightArithmeticAtPlace_proof D i τ).rank.1.trans hrk.symm
  have hfr : ∀ τ, (R.MW i (sg0 D A)).fr τ * ((R.MW i (sg0 D A)).fr τ)⁻¹ = 1 := fun τ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit τ))
  have e : (fun τ => (R.MW i (sg0 D A)).fr τ * compAt R.θ τ (Formalism.L2.Theta.mt (Wc D i) 1) *
      ((R.MW i (sg0 D A)).fr τ)⁻¹) = 1 := by
    funext τ; rw [GlobalTheory.JointHarm.compAt_mt_one', Matrix.mul_one, hfr]; rfl
  have act := fun (f : WO (Vc D i) (Wc D i) → ℂ) (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f) hv =>
    GlobalTheory.T.weil_maximalCompact_fock_substitution_character D R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i A.μ0) _ (R.MW i (sg0 D A)) (R.BV i) (hω i A.μ0) hθ
      (D.sp.V_sig _) (D.sp.W_sig _) hBS _ _ hpq (hR.models.order i) _ _
      (fun τ => (GlobalTheory.T.thetaLiftInfinityTypes_atRealPlace D T0 R.toLevCh A.μ0 hR.lev i A.μ0 τ).chiV)
      (fun τ => (GlobalTheory.T.thetaLiftInfinityTypes_atRealPlace D T0 R.toLevCh A.μ0 hR.lev i A.μ0 τ).chiW) x₁ x₂ x₃ (fun τ => (hx τ).1) (fun τ => (hx τ).2.1)
      (fun τ => (hx τ).2.2.1) f hf hv u hu 1 (one_mem _)
      (fun τ => by rw [congrFun e τ]; exact GlobalTheory.JointHarm.one_mem_K)
  have aφ := (act φ hthφ hvφ).2
  have av := (act _ hthv hvv).2
  rw [e] at aφ av
  have hcV : ∀ τ, IsCartanInv (gramAt D (Vc D i) τ) ((fun _ => (1 : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ)) τ) :=
    fun τ => by
      have hu' := (Matrix.isUnit_iff_isUnit_det _).1 (hBu τ)
      have h1 := Matrix.mul_nonsing_inv _ hu'
      have hG : gramAt D (Vc D i) τ = ((R.BV i τ)⁻¹)ᴴ * (R.BV i τ)⁻¹ := by
        calc gramAt D (Vc D i) τ
            = ((R.BV i τ)⁻¹)ᴴ * ((R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ) * (R.BV i τ)⁻¹ := by
              rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one,
                Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
          _ = _ := by rw [hBS τ, Matrix.mul_one]
      refine ⟨Matrix.one_mul _, by simp, ?_⟩
      rw [Matrix.mul_one, hG]
      exact Matrix.PosDef.conjTranspose_mul_self _
        (Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_nonsing_inv_iff.2 (hBu τ)))
  have hne : R.vP i A.μ0 ≠ 0 :=
    GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hR.lev.βV i))
      (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hR.lev.βW i))
      (hrk.trans_le (r_le_V i)) (hR.thP.vP i A.μ0)
  have hinj := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) (hω i A.μ0).std hθ
    (fun _ => 1) (R.BV i) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) _ hcV
    (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart _ τ) (hR.models.BV i)
    (fun τ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hR.models.order i τ))
    (D.sp.V_sig _) (D.sp.W_sig _) (R.vP i A.μ0) hthv hvv hne
  have key := (hR.thP.ioP i A.μ0).1 u hu x w
  unfold RealDat.ptP at key
  rw [av] at key
  rw [aφ, hinj key]

end GlobalTheory.FockAnyDatum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsActFockVectorsAnyDatumStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoints_act_fock_vectors_any_datum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (φ : WO (Vc D i) (Wc D i) → ℂ), IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) R.Pg Q ξR (R.vacP i) φ → ∀ u ∈ GinfC (Vc D i), ∀ x w, R.ωP i A.μ0 (u, 1) (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ (R.ioP i x w)) = pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ (R.ioP i x ((R.cV i).ρ u w)) := by
  first | exact @GlobalTheory.FockAnyDatum.om_ioP_of_datum | exact GlobalTheory.FockAnyDatum.om_ioP_of_datum | (intros; apply GlobalTheory.FockAnyDatum.om_ioP_of_datum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOfOrderDvd
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section

namespace GlobalTheory.XiSplit

open Formalism.L2.Host

theorem isUnitary_of_orderDvd {L : Type} [Field L] [NumberField L] {χ : HChar L} {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) : χ.IsUnitary := by
  intro x
  have h1 : (χ.1 x) ^ n = 1 := by
    have : (χ ^ n).1 x = 1 := by rw [h]; rfl
    rw [← this]; rfl
  have h2 : ‖((χ.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

theorem inf_eq_one {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] {χ : HChar L} {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hx : ∀ x, (χ.1 x) ^ n = 1 := fun x => congrArg (fun ξ : HChar L => ξ.1 x) h
  have hw : ∀ (w : InfinitePlace L) (y : (w.Completion)ˣ), χ.locInf w y = 1 := by
    intro w y
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (y : w.Completion)) hn
    have hz' : (e.symm z) ^ n = y := by rw [← map_pow, hz]; simp
    have hz0 : e.symm z ≠ 0 := by
      intro h0; rw [h0, zero_pow hn.ne'] at hz'; exact y.ne_zero hz'.symm
    have : y = (Units.mk0 _ hz0) ^ n := Units.ext (by simp [hz'])
    rw [this, map_pow]
    exact hx _
  show χ.1 (Formalism.L2.Host.infDiag k) = 1
  unfold Formalism.L2.Host.infDiag
  rw [MonoidHom.finsetProd_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => hw w _

theorem smul_eq_of_isConjPl {D : D7} {w w' : HeightOneSpectrum (𝓞 D.host.E)} (hc : Formalism.IndefR.Lev.IsConjPl w w') :
    D.host.conj • w.asIdeal = w'.asIdeal := by
  have hle : D.host.conj • w.asIdeal ≤ w'.asIdeal := by
    intro y hy
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
    obtain ⟨z, hzv, hz⟩ := hc _ hy
    have e : z = y := RingOfIntegers.ext
      ((hz.trans (GlobalTheory.TypePlaces.star_eq_conj D _)).trans (D.host.conj.apply_symm_apply (y : D.host.E)))
    exact e ▸ hzv
  have hmax : (D.host.conj • w.asIdeal).IsMaximal := by
    have := w.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => w.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  exact hmax.eq_of_le w'.isPrime.ne_top hle

theorem isConjPl_of_smul_eq {D : D7} {w w' : HeightOneSpectrum (𝓞 D.host.E)}
    (h : D.host.conj • w.asIdeal = w'.asIdeal) : Formalism.IndefR.Lev.IsConjPl w w' := fun c hc =>
  ⟨D.host.conj • c, h ▸ Ideal.smul_mem_pointwise_smul _ _ _ hc, (GlobalTheory.TypePlaces.star_eq_conj D _).symm⟩

theorem unrAt_of_inert {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ∃ q : ℕ, q.Prime ∧ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    (L.xiH t).UnrAt P := by
  obtain ⟨q, -, hI, hqP⟩ := hP
  have hfix : D.host.conj • P.asIdeal = P.asIdeal := hI P.asIdeal P.isPrime P.ne_bot hqP
  by_contra h
  rcases (hL.Q_ram t P).1 h with hPQ | ⟨P', hP', hc⟩
  · exact ((hL.Q_pl t) P hPQ).2 P hPQ (isConjPl_of_smul_eq hfix)
  · have e1 := (smul_eq_of_isConjPl hc).trans hfix.symm
    have e2 : P'.asIdeal = P.asIdeal := by
      simpa using congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) e1
    have e3 : P' = P := HeightOneSpectrum.ext e2
    subst e3
    exact ((hL.Q_pl t) P' hP').2 P' hP' hc

theorem exists_heckeU_xi : ∀ {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T}, L.Is μ₀ → ∀ t : T,
    ∃ χ : HeckeU D 0, (∀ x, χ.f x = (L.xiH t).1 (finIdl D x)) ∧ ∀ τ, χ.n τ = 0 := by
  intro D T L μ₀ hL t
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have hu : (L.xiH t).IsUnitary := isUnitary_of_orderDvd hn ho
  have hi : (L.xiH t).HasInf (Formalism.L2.Host.embTau D) 0 := fun k => by
    rw [inf_eq_one hn ho k]
    simp
  have hp : ∀ τ, Even ((0 : D.what₂.Tau → ℤ) τ - ((0 : ℕ) : ℤ)) := fun τ => by simp
  have hc : ∃ m : ℕ, 0 < m ∧ ∀ u, IntU D u → (∃ s ∈ OhE D, (u : AE D) - 1 = (m : AE D) * s) →
      (L.xiH t).1 (finIdl D u) = 1 := by
    obtain ⟨M, hM, h⟩ := GlobalTheory.Mem.HeckeLevel.exists_level_nat D.host.E (L.xiH t)
    refine ⟨M, hM, fun u hu ⟨s, hs, e⟩ => h _ (GlobalTheory.Mem.Col2.SplitChar.finIdl_unit hu)
      (fun w => by rw [GlobalTheory.Mem.Col2.SplitChar.finIdl_fst]; rfl) fun P => ?_⟩
    rw [GlobalTheory.Mem.Col2.SplitChar.vl_sub_one, e, map_mul, GlobalTheory.Mem.Col2.SplitChar.vl_nat,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact mul_le_of_le_one_right' (GlobalTheory.Mem.Col2.SplitChar.vl_le hs P)
  have hnorm := GlobalTheory.NuCharNorm.chi_norm_one D (L.xiH t) (hL.xi_triv t)
    (GlobalTheory.Mem.HeckeLevel.exists_level_nat D.host.E (L.xiH t))
  have hr := GlobalTheory.UnrKill.unr_kill D (L.xiH t) (unrAt_of_inert hL t)
  exact ⟨GlobalTheory.SplitCharGen.ofHChar 0 (L.xiH t) 0 hu hi hp hc hnorm hr, fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.XiSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuTwistedTupleIsCMValueHeckeCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuTwistedTupleIsCMValueHeckeCharacter
open NumberField IsDedekindDomain
open Classical

noncomputable section

namespace GlobalTheory.SqTop.TwVal

open Formalism.BasicNotions Formalism.IndefR.Links
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

variable {D : D7}

theorem under_eq_of_conj {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
  refine HeightOneSpectrum.ext ((P.under (𝓞 D.host.F)).isMaximal.eq_of_le (P'.under (𝓞 D.host.F)).isPrime.ne_top
    fun a ha => ?_)
  obtain ⟨c', h1, h2⟩ := h (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ha
  have hfix : star (algebraMap D.host.F D.host.E (a : D.host.F)) = algebraMap D.host.F D.host.E (a : D.host.F) :=
    (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = c' := RingOfIntegers.ext (h2.trans hfix).symm
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P'.asIdeal
  rwa [e]

theorem expAt_mul_unr {χ ξ : HChar D.host.E} {P : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (h : GlobalTheory.CMVal.ExpAt χ P n) (hξ : ξ.UnrAt P) : GlobalTheory.CMVal.ExpAt (χ * ξ) P n := by
  intro m
  have hm : ξ.LevelLe P m := hξ.levelLe m
  refine ⟨fun hx => (h m).1 ?_, fun hn => ((h m).2 hn).mul hm⟩
  have := hx.mul hm.inv
  rwa [mul_inv_cancel_right] at this

theorem expAt_mul_low {χ ξ : HChar D.host.E} {P : HeightOneSpectrum (𝓞 D.host.E)} {n k : ℕ}
    (h : GlobalTheory.CMVal.ExpAt χ P n) (hξ : ξ.LevelLe P k) (hk : k < n) : GlobalTheory.CMVal.ExpAt (χ * ξ) P n := by
  intro m
  refine ⟨fun hx => ?_, fun hn => ((h m).2 hn).mul (Model.levelLe_mono hξ (by omega))⟩
  by_contra c
  have a := Model.levelLe_mono hx (le_max_left m k)
  have b := Model.levelLe_mono hξ (le_max_right m k)
  have := a.mul b.inv
  rw [mul_inv_cancel_right] at this
  have := (h _).1 this
  omega

theorem isValChar_nu_twist {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T)
    (i j : Fin D.R.m) {s : ℕ} (hs : s ≤ halfRank D i j) :
    GlobalTheory.CMVal.IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl)
      ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) (nuH G t i j) := by
  have e : nuH G t i j = nuH G μ₀ i j * L.xiH t := by
    simp only [nuH, hL.xi_base, mul_one]
    rw [div_mul_eq_mul_div]
  obtain ⟨n, hn, hf⟩ := hL.xi_fin t
  obtain ⟨hu0, htr0, hinf0, hloc0⟩ := (Model.isValChar_nu hL G i j hs).1
  have unipotent_character_trivial_off_S0 : ∀ PP ∈ GlobalTheory.SqTop.twPl G t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ G.pl.S0 := fun PP hPP hS => by
    simp only [GlobalTheory.SqTop.twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hPP
    have hQ : PP ∈ L.Q t := hPP.1.resolve_left hPP.2
    rcases G.pl.mem_S0_of_sum_eq.1 hS with h | h
    · exact G.pl.levelPlace_ne_basePlace t PP hQ h
    · exact hPP.2 (by rw [G.pl.w_Q t PP hQ h]; exact Finset.mem_image_of_mem _ hS)
  have ram : ∀ PP : HeightOneSpectrum (𝓞 D.host.E), ¬ (L.xiH t).UnrAt PP →
      (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S1 D ∨
        (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ (GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F) := by
    intro PP hPP
    obtain ⟨P', hP', hu⟩ : ∃ P' ∈ L.Q t, P'.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := by
      rcases (hL.Q_ram t PP).1 hPP with h | ⟨P', h, hc⟩
      · exact ⟨PP, h, rfl⟩
      · exact ⟨P', h, under_eq_of_conj hc⟩
    by_cases hW : P' ∈ G.pl.W0
    · left
      obtain ⟨u, hu', rfl⟩ := Finset.mem_image.1 hW
      rw [← hu, G.pl.under_w hu']
      exact (G.pl.mem_S0_of_sum_eq.1 hu').resolve_left fun h => G.pl.levelPlace_ne_basePlace t _ hP' ((G.pl.under_w hu').trans h)
    · right
      exact Finset.mem_image.2 ⟨P', by
        simp only [GlobalTheory.SqTop.twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union]; exact ⟨Or.inr hP', hW⟩, hu⟩
  rw [e]
  refine ⟨hu0.mul (HChar.isUnitary_of_order hn hf), htr0.mul (hL.xi_triv t), fun k => ?_,
    fun v P hP => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · rw [HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one (L.xiH t) hn hf k, mul_one]
    exact hinf0 k
  · obtain rfl : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hP
    obtain ⟨PP, hPP, hu⟩ := Finset.mem_image.1 hv
    have h0 := (hloc0 _ P hP).2 (Finset.notMem_empty _)
    rw [Model.expIn_condF, if_neg (hu ▸ unipotent_character_trivial_off_S0 PP hPP)] at h0
    exact (Model.levelLe_mono ((h0 0).2 le_rfl) (Nat.zero_le 1)).mul (hL.xi_tame t P)
  · obtain rfl : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hP
    have h0 := (hloc0 _ P hP).2 (Finset.notMem_empty _)
    by_cases hr : (L.xiH t).UnrAt P
    · exact expAt_mul_unr h0 hr
    · have hS1 := (ram P hr).resolve_right hv
      refine expAt_mul_low h0 (hL.xi_tame t P) ?_
      rw [Model.expIn_condF, if_pos (G.pl.mem_S0_of_sum_eq.2 (Or.inr hS1)), condExp,
        if_neg fun (e : P.under (𝓞 D.host.F) = G.pl.v0) => G.ch.basePlace_not_mem_chiGridBadPlaces (e ▸ hS1)]
      norm_num

end GlobalTheory.SqTop.TwVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuTwistedTupleIsCMValueHeckeCharacterStatement
open NumberField IsDedekindDomain
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_nu_twisted_tuple_isCMValueHeckeCharacter : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (i j : Fin D.R.m) {s : ℕ}, s ≤ GlobalTheory.FunObj.SqNum.halfRank D i j → GlobalTheory.CMVal.IsValChar (GlobalTheory.FunObj.SqNum.cmPhi D) s (GlobalTheory.FunObj.SqNum.kap D sc.cGap i j s) (GlobalTheory.FunObj.SqNum.condF G.pl) ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)) (GlobalTheory.FunObj.SqNum.nuH G t i j) := by
  first | exact @GlobalTheory.SqTop.TwVal.isValChar_nu_twist | exact GlobalTheory.SqTop.TwVal.isValChar_nu_twist | (intros; apply GlobalTheory.SqTop.TwVal.isValChar_nu_twist <;> assumption)
end
end
