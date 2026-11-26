module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableOfRapidDecay
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapValuesCompactSobolevBound
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrXLeKOOfPrCat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HandBFSmul
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMeasureUniformInTupleOfThetaLiftScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMeasureUniformInTupleOfThetaLiftScalar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.RealMeasOne

variable {D : D7}

theorem ginfC_facts (V : HSp D) : IsTopologicalGroup (GA D V) ∧ LocallyCompactSpace (GA D V) ∧
    SecondCountableTopology (GA D V) ∧ T2Space (GA D V) ∧ BorelSpace (GA D V) ∧ LocallyCompactSpace (GinfC V) ∧
    SecondCountableTopology (GinfC V) ∧ BorelSpace (GinfC V) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  exact ⟨i1, i2, i3, i4, i5, i6.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    Topology.IsInducing.subtypeVal.secondCountableTopology, Subtype.borelSpace _⟩

theorem eq_map_of_lev {V : HSp D} (K : Subgroup (GA D V)) (hK : K ≤ GfC V) (A : Set (GA D V)) (ν : Measure (GA D V))
    (mR : Measure (GinfC V)) (hH : mR.IsHaarMeasure)
    (h : ∀ (f : GinfC V → ℂ) (F : GA D V → ℂ), Integrable f mR → (∀ b : GinfC V, ∀ κ ∈ K, F ((b : GA D V) * κ) = f b) →
      IntegrableOn F A ν ∧ ∫ g in A, F g ∂ν = ∫ b, f b ∂mR) :
    mR = Measure.map (GlobalTheory.AutMult.toInf V) (ν.restrict A) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ginfC_facts V
  haveI := hH
  have hmeas : Measurable (GlobalTheory.AutMult.toInf V) := (GlobalTheory.AutMult.continuous_toInf V).measurable

  have hfin : ∀ G : Set (GinfC V), MeasurableSet G → mR G < ⊤ →
      mR G = Measure.map (GlobalTheory.AutMult.toInf V) (ν.restrict A) G := by
    intro G hG hGf
    have hS : MeasurableSet (GlobalTheory.AutMult.toInf V ⁻¹' G) := hmeas hG
    have hf : Integrable (G.indicator fun _ => (1 : ℂ)) mR :=
      (integrable_indicator_iff hG).2 ((integrableOn_const_iff (by simp)).2 (Or.inr hGf))
    obtain ⟨hi, he⟩ := h (G.indicator fun _ => (1 : ℂ)) ((GlobalTheory.AutMult.toInf V ⁻¹' G).indicator fun _ => (1 : ℂ)) hf
      (fun b κ hκ => by
        have h1 : GlobalTheory.AutMult.toInf V ((b : GA D V) * κ) = b := by
          rw [map_mul, GlobalTheory.AutMult.toInf_coe, (GlobalTheory.ChainOnto.HaarInf.toInf_eq_one_iff V κ).2 (hK hκ), mul_one]
        classical
        rw [Set.indicator_apply, Set.indicator_apply, Set.mem_preimage, h1])
    have hi' : ν.restrict A (GlobalTheory.AutMult.toInf V ⁻¹' G) < ⊤ := by
      have := ((integrable_indicator_iff hS).1 hi)
      rcases (integrableOn_const_iff (by simp)).1 this with h0 | h0
      · simp at h0
      · exact h0
    rw [integral_indicator_const _ hS, integral_indicator_const _ hG] at he
    have he' : (ν.restrict A).real (GlobalTheory.AutMult.toInf V ⁻¹' G) = mR.real G := by
      simpa using he
    rw [Measure.map_apply hmeas hG]
    exact ((ENNReal.toReal_eq_toReal_iff' hGf.ne hi'.ne).1 he'.symm)
  refine Measure.ext fun G hG => ?_
  have hU : ⋃ n, G ∩ spanningSets mR n = G := by rw [← Set.inter_iUnion, iUnion_spanningSets, Set.inter_univ]
  have hmono : Monotone fun n => G ∩ spanningSets mR n := fun a b hab =>
    Set.inter_subset_inter_right _ (monotone_spanningSets mR hab)
  rw [← hU, hmono.measure_iUnion, hmono.measure_iUnion]
  refine iSup_congr fun n => hfin _ (hG.inter (measurableSet_spanningSets mR n)) ?_
  exact (measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top mR n)

end GlobalTheory.RealMeasOne

namespace GlobalTheory.RealMeasOne

variable {D : D7}

theorem infMat_toInf (V : HSp D) (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    infMat D.sp.cm.sig V.gram φ (GlobalTheory.AutMult.toInf V g : GA D V) = infMat D.sp.cm.sig V.gram φ g := by
  conv_rhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
  rw [GlobalTheory.PointAtPlaceHom.infMat_mul, GlobalTheory.TensRep.infMat_of_mem_fin V φ (GlobalTheory.AutMult.toFin V g).2, Matrix.mul_one]

theorem eq_of_measLevW {V : HSp D}
    {good : ∀ ρ : D.what₂.Tau, Measure (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) → Prop}
    (hgood : ∀ ρ m, good ρ m → m.IsHaarMeasure)
    {K₁ K₂ : Subgroup (GL (Fin V.rank) (Lev.EAf D))} {ν₁ ν₂ : Measure (GA D V)}
    (h₁ : Lev.IsMeasLevW V K₁ good ν₁) (h₂ : Lev.IsMeasLevW V K₂ good ν₂)
    (m₁ m₂ : Measure (GinfC V)) (hH₁ : m₁.IsHaarMeasure) (hH₂ : m₂.IsHaarMeasure)
    (e₁ : m₁ = Measure.map (GlobalTheory.AutMult.toInf V) (ν₁.restrict {g | Lev.finE V g ∈ K₁}))
    (e₂ : m₂ = Measure.map (GlobalTheory.AutMult.toInf V) (ν₂.restrict {g | Lev.finE V g ∈ K₂})) : m₁ = m₂ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ginfC_facts V
  haveI := hH₁
  haveI := hH₂
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.1
  have := fun P Q => (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
  obtain ⟨-, ⟨θ, hθ⟩, h1⟩ := h₁
  obtain ⟨⟨A, hA⟩, h1⟩ := h1 θ hθ
  obtain ⟨⟨m, hm⟩, h1⟩ := h1 A hA
  obtain ⟨-, -, h2⟩ := h₂
  obtain ⟨-, h2⟩ := h2 θ hθ
  obtain ⟨-, h2⟩ := h2 A hA
  have h2 := h2 m hm
  let B : ∀ ρ : D.what₂.Tau, TopologicalSpace.PositiveCompacts (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2) :=
    fun ρ => Classical.arbitrary _
  have hB : ∀ ρ, MeasurableSet (B ρ : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2)) := fun ρ =>
    (B ρ).isCompact.measurableSet
  let S : Set (GA D V) := {h | ∀ ρ, ∃ b ∈ (B ρ : Set _), UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h}
  have hSc : IsClosed S := by
    have e : S = ⋂ ρ, (fun h => A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h) ⁻¹'
        ((fun b => UpqT.mat b * A ρ) '' (B ρ : Set (UpqT (V.sig (tauE D ρ)).1 (V.sig (tauE D ρ)).2))) := by
      ext h
      simp only [Set.mem_iInter]
      exact Iff.rfl
    rw [e]
    refine isClosed_iInter fun ρ => IsClosed.preimage ?_ ?_
    · exact continuous_const.matrix_mul (GlobalTheory.Mem.VolExists.continuous_infMat (σ := D.sp.cm.sig) V.gram (hθ ρ))
    · exact ((B ρ).isCompact.image ((GlobalTheory.UpqTopology.continuous_mat).matrix_mul continuous_const)).isClosed
  have hS : MeasurableSet S := hSc.measurableSet
  let E : Set (GinfC V) := Subtype.val ⁻¹' S
  have hE : MeasurableSet E := measurable_subtype_coe hS
  have hpre : GlobalTheory.AutMult.toInf V ⁻¹' E = S := by
    ext h
    simp only [E, S, Set.mem_preimage, Set.mem_setOf_eq, infMat_toInf]
  have hval : ∀ (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (ν : Measure (GA D V)),
      Measure.map (GlobalTheory.AutMult.toInf V) (ν.restrict {g | Lev.finE V g ∈ K}) E =
        ν {h | Lev.finE V h ∈ K ∧ ∀ ρ, ∃ b ∈ (B ρ : Set _), UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig V.gram (θ ρ) h} := by
    intro K ν
    rw [Measure.map_apply (GlobalTheory.AutMult.continuous_toInf V).measurable hE, hpre, Measure.restrict_apply hS]
    congr 1
    ext h
    exact and_comm
  have v1 : m₁ E = ∏ ρ, m ρ (B ρ) := by rw [e₁, hval]; exact h1 m hm (fun ρ => B ρ) hB
  have v2 : m₂ E = ∏ ρ, m ρ (B ρ) := by rw [e₂, hval]; exact h2 (fun ρ => B ρ) hB
  have h0 : ∏ ρ, m ρ (B ρ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun ρ _ => by
    have := hgood ρ (m ρ) (hm ρ)
    exact (Measure.measure_pos_of_nonempty_interior (m ρ) (B ρ).interior_nonempty).ne'
  have ht : ∏ ρ, m ρ (B ρ) ≠ ⊤ := ENNReal.prod_ne_top fun ρ _ => by
    have := hgood ρ (m ρ) (hm ρ)
    exact (B ρ).isCompact.measure_lt_top.ne
  have e : m₂ = ((Measure.haarScalarFactor m₂ m₁ : NNReal) : ENNReal) • m₁ := Measure.isMulLeftInvariant_eq_smul m₂ m₁
  have e' := v2
  rw [e, Measure.smul_apply, v1, smul_eq_mul] at e'
  have hc : ((Measure.haarScalarFactor m₂ m₁ : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj h0 ht).1 (e'.trans (one_mul _).symm)
  rw [e, hc, one_smul]

end GlobalTheory.RealMeasOne

namespace GlobalTheory.RealMeasOne

theorem models_good {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hM : R.IsModels) (j : ℕ)
    (hj : j < D.R.m) :
    ∃ good : ∀ ρ : D.what₂.Tau, Measure (UpqT ((Yc D j).sig (tauE D ρ)).1 ((Yc D j).sig (tauE D ρ)).2) → Prop,
      (∀ ρ m, good ρ m → m.IsHaarMeasure) ∧
      ∀ t, Lev.IsMeasLevW (Yc D j) (lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)) good (R.νY t j) := by
  rcases Nat.lt_or_ge (j + 1) D.R.m with h | h
  · exact ⟨fun _ m => Lev.IsMinf m, fun _ _ hm => hm.1, fun t => (hM.νY t j h).1⟩
  · obtain rfl : j = D.R.m - 1 := by omega
    exact ⟨fun _ m => m.IsHaarMeasure ∧ IsProbabilityMeasure m, fun _ _ hm => hm.1, fun t => (hM.νY' t).1⟩

theorem one_real_measure : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F →
    (∀ h : RangeX R, RChain R h) → RangeX R → RMeas R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hC hR j hj
  by_cases hT : Nonempty T
  swap
  · exact ⟨0, fun t => (hT ⟨t⟩).elim⟩
  obtain ⟨t₀⟩ := hT
  have hlev : ∀ t, ∃ mR, IsLevMeas (stY R t j) mR := fun t =>
    (GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D (comR R t) (twR R t) (hC hR t).1 j hj.le (stY R t j) ((hC hR t).2.1 j hj)).2.2.2.2.2
  choose mR hmR using hlev
  obtain ⟨good, hgood, hW⟩ := models_good R hG.core.models j hj
  have hmap : ∀ t, mR t = Measure.map (GlobalTheory.AutMult.toInf (Yc D j))
      ((R.νY t j).restrict {g | Lev.finE (Yc D j) g ∈ lev D.sp.cm (Yc D j).gram (R.βY j) (R.datYt t j R.triv)}) := fun t => by
    exact eq_map_of_lev (Lev.levG (Yc D j) (R.βY j) (R.datYt t j R.triv)) inf_le_left _ _ (mR t) (hmR t).1 (hmR t).2
  refine ⟨mR t₀, fun t => ?_⟩
  have e : mR t = mR t₀ := by
    exact eq_of_measLevW hgood (hW t) (hW t₀) (mR t) (mR t₀) (hmR t).1 (hmR t₀).1 (hmap t) (hmap t₀)
  rw [← e]
  exact hmR t

end GlobalTheory.RealMeasOne

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMeasureUniformInTupleOfThetaLiftScalarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realMeasureUniformInTuple_of_thetaLiftScalar : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → (∀ h : RangeX R, RChain R h) → RangeX R → RMeas R := by
  first | exact @GlobalTheory.RealMeasOne.one_real_measure | exact GlobalTheory.RealMeasOne.one_real_measure | (intros; apply GlobalTheory.RealMeasOne.one_real_measure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Core.Mi.SepPer

variable {D : D7}

def contLeft (V : HSp D) : Submodule ℂ (GA D V → ℂ) where
  carrier := {F | Continuous F ∧ ∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g}
  add_mem' := by
    rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    exact ⟨hF.add hG, fun γ hγ g => by simp [hF' γ hγ g, hG' γ hγ g]⟩
  zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
  smul_mem' := by
    rintro c F ⟨hF, hF'⟩
    exact ⟨continuous_const.mul hF, fun γ hγ g => by simp [hF' γ hγ g]⟩

theorem rTrans_mem {V : HSp D} (t : GA D V) {F : GA D V → ℂ} (hF : F ∈ contLeft V) : rTrans t F ∈ contLeft V :=
  ⟨hF.1.comp (continuous_id.mul continuous_const), fun γ hγ g => by
    simp only [rTrans, mul_assoc]; exact hF.2 γ hγ (g * t)⟩

theorem norm_psiBes {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (θ : D.host.E) (z : Fin S₀.rank → D.host.E) (n : GA D S) : ‖psiBes ψ d θ z n‖ = 1 := by
  exact hψ.1.2.1 _

theorem per_add_bound {ρ : ℕ} (B : BesLev D ρ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {φ : GA D B.A → ℂ} (hφ : IsContAut B.A φ) (Ω : Set (GA D B.V)) (hΩc : IsCompact Ω)
    (hΩ : ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω) :
    ∃ C : ℝ, (∀ f g, f ∈ contLeft B.V → g ∈ contLeft B.V → B.per ψ φ (f + g) = B.per ψ φ f + B.per ψ φ g) ∧
      ∀ f, f ∈ contLeft B.V → ∀ K : ℝ, (∀ x ∈ Ω, ‖f x‖ ≤ K) → ‖B.per ψ φ f‖ ≤ C * K := by
  obtain ⟨Cφ, hCφ⟩ := GlobalTheory.Unf.EvalCont.bounded_of_contAut B.cpt hφ
  have hμ : B.vA.μ B.vA.𝓕 < ⊤ := GlobalTheory.Unf.vol_fund_lt_top B.cpt B.vA
  have hν1 : B.vN.ν B.vN.𝓝 = 1 := B.vN.unit.2.2
  have hν : B.vN.ν B.vN.𝓝 < ⊤ := by rw [hν1]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 hν.ne
  have hψc : Continuous ψ := hψ.1.1
  have hemb := GlobalTheory.Unf.BesSemi.continuous_embA B.d B.o
  have hpsi := GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψc 1 (vecB B.o B.ζ)

  have hsup : ∀ f, f ∈ contLeft B.V → ∀ K : ℝ, (∀ x ∈ Ω, ‖f x‖ ≤ K) →
      ∀ (h : GA D B.A) (n : flagN B.d), ‖f (n.1 * embA B.d B.o h)‖ ≤ K := by
    intro f hf K hK h n
    have hs : n.1 * embA B.d B.o h ∈ besGrp B.d B.o :=
      mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)
    obtain ⟨γ, hγ, hγs⟩ := hΩ _ hs
    rw [← hf.2 γ (Subgroup.mem_inf.1 hγ).1]
    exact hK _ hγs
  have hbd : ∀ f, f ∈ contLeft B.V → ∀ K : ℝ, (∀ x ∈ Ω, ‖f x‖ ≤ K) →
      ∀ h n, ‖GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n‖ ≤ Cφ * K := by
    intro f hf K hK h n
    simp only [GlobalTheory.MixPer.besFun, norm_mul, norm_star, norm_psiBes hψ, mul_one]
    exact mul_le_mul (hCφ h) (hsup f hf K hK h n) (norm_nonneg _) ((norm_nonneg _).trans (hCφ h))
  have hcont : ∀ f, f ∈ contLeft B.V → ∀ h, Continuous (GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h) := by
    intro f hf h
    change Continuous fun n : flagN B.d => φ h * f (n.1 * embA B.d B.o h) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n.1)
    exact (continuous_const.mul (hf.1.comp (continuous_subtype_val.mul continuous_const))).mul
      (continuous_star.comp (hpsi.comp continuous_subtype_val))
  have hcontH : ∀ f, f ∈ contLeft B.V → ∀ n : flagN B.d,
      Continuous fun h => GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n := by
    intro f hf n
    simp only [GlobalTheory.MixPer.besFun]
    exact (hφ.2.mul (hf.1.comp (continuous_const.mul hemb))).mul continuous_const
  have hK : ∀ f, f ∈ contLeft B.V → ∃ K : ℝ, ∀ x ∈ Ω, ‖f x‖ ≤ K := by
    intro f hf
    obtain ⟨K, hK⟩ := hΩc.exists_bound_of_continuousOn hf.1.continuousOn
    exact ⟨K, hK⟩
  have hin : ∀ f, f ∈ contLeft B.V → ∀ h,
      IntegrableOn (GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h) B.vN.𝓝 B.vN.ν := by
    intro f hf h
    obtain ⟨K, hK⟩ := hK f hf
    exact Measure.integrableOn_of_bounded hν.ne (hcont f hf h).aestronglyMeasurable
      (Filter.Eventually.of_forall fun n => hbd f hf K hK h n)
  have houtC : ∀ f, f ∈ contLeft B.V →
      Continuous fun h => ∫ n in B.vN.𝓝, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν := by
    intro f hf
    obtain ⟨K, hK⟩ := hK f hf
    haveI := GlobalTheory.Unf.EvalCont.firstCountable_GA B.A
    exact continuous_of_dominated (bound := fun _ => Cφ * K)
      (fun h => (hcont f hf h).aestronglyMeasurable)
      (fun h => Filter.Eventually.of_forall fun n => hbd f hf K hK h n) (integrable_const _)
      (Filter.Eventually.of_forall fun n => hcontH f hf n)
  have hout : ∀ f, f ∈ contLeft B.V →
      IntegrableOn (fun h => ∫ n in B.vN.𝓝, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν) B.vA.𝓕 B.vA.μ := by
    intro f hf
    obtain ⟨K, hK⟩ := hK f hf
    refine Measure.integrableOn_of_bounded (M := Cφ * K * B.vN.ν.real B.vN.𝓝) hμ.ne (houtC f hf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun h => ?_)
    exact norm_setIntegral_le_of_norm_le_const hν fun n _ => hbd f hf K hK h n
  refine ⟨Cφ * B.vA.μ.real B.vA.𝓕, fun f g hf hg => ?_, fun f hf K hK' => ?_⟩
  · have e : ∀ h n, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ (f + g) h n =
        GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n + GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ g h n := by
      intro h n; simp only [GlobalTheory.MixPer.besFun, Pi.add_apply]; ring
    simp only [GlobalTheory.Unf.BesLev.per, GlobalTheory.MixPer.besPer]
    simp_rw [e]
    rw [← integral_add (hout f hf) (hout g hg)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun h => integral_add (hin f hf h) (hin g hg h))
  · have hνr : B.vN.ν.real B.vN.𝓝 = 1 := by simp [Measure.real, hν1]
    have h1 : ∀ h ∈ B.vA.𝓕, ‖∫ n in B.vN.𝓝, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν‖ ≤ Cφ * K := by
      intro h _
      have := norm_setIntegral_le_of_norm_le_const hν fun n _ => hbd f hf K hK' h n
      rwa [hνr, mul_one] at this
    have h2 := norm_setIntegral_le_of_norm_le_const hμ h1
    simp only [GlobalTheory.Unf.BesLev.per, GlobalTheory.MixPer.besPer]
    calc _ ≤ Cφ * K * B.vA.μ.real B.vA.𝓕 := h2
      _ = _ := by ring

end GlobalTheory.Core.Mi.SepPer

namespace GlobalTheory.Core.Mi.SepPer

variable {D : D7}

theorem mult_mem_contLeft (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) {T : MMap M} (hT : T ∈ Mult θ M J χ) (u : M.Vec) : T u ∈ contLeft V := by
  let Q : Submodule ℂ (MMap M) :=
    { carrier := {T | ∀ u, T u ∈ contLeft V}
      add_mem' := fun ha hb u => by simpa using (contLeft V).add_mem (ha u) (hb u)
      zero_mem' := fun u => by simpa using (contLeft V).zero_mem
      smul_mem' := fun c T hT u => by simpa using (contLeft V).smul_mem c (hT u) }
  have : Mult θ M J χ ≤ Q := Submodule.span_le.2 fun T hT u => ⟨(hT.aut u).cont, (hT.aut u).left⟩
  exact this hT u

theorem mult_bound (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) {T : MMap M} (hT : T ∈ Mult θ M J χ) (Ω : Set (GA D V)) (hΩ : IsCompact Ω)
    (τ : D.what₂.Tau) (v : M.Vec) :
    ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ Y ∈ l, Y ∈ lieAt V τ) ∧
      ∀ w : M.sm τ, ∀ g ∈ Ω, ‖T (Function.update v τ w) g‖ ≤
        C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum := by
  induction hT using Submodule.span_induction with
  | mem T hT => exact GlobalTheory.T.cuspFormMap_values_compact_sobolev_bound D θ V S M J χ hθ T hT Ω hΩ τ v
  | zero => exact ⟨[], 0, by simp, fun w g _ => by simp⟩
  | add T₁ T₂ _ _ h₁ h₂ =>
    obtain ⟨L₁, C₁, hL₁, hb₁⟩ := h₁
    obtain ⟨L₂, C₂, hL₂, hb₂⟩ := h₂
    refine ⟨L₁ ++ L₂, max C₁ 0 + max C₂ 0, fun l hl => ?_, fun w g hg => ?_⟩
    · rcases List.mem_append.1 hl with h | h
      exacts [hL₁ l h, hL₂ l h]
    · set s₁ := (L₁.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum
      set s₂ := (L₂.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum
      have hs₁ : 0 ≤ s₁ := List.sum_nonneg fun x hx => by
        obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      have hs₂ : 0 ≤ s₂ := List.sum_nonneg fun x hx => by
        obtain ⟨l, _, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      rw [List.map_append, List.sum_append, MultilinearMap.add_apply, Pi.add_apply]
      calc _ ≤ ‖T₁ (Function.update v τ w) g‖ + ‖T₂ (Function.update v τ w) g‖ := norm_add_le _ _
        _ ≤ C₁ * s₁ + C₂ * s₂ := add_le_add (hb₁ w g hg) (hb₂ w g hg)
        _ ≤ max C₁ 0 * s₁ + max C₂ 0 * s₂ :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hs₁)
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hs₂)
        _ ≤ (max C₁ 0 + max C₂ 0) * (s₁ + s₂) := by
          have := le_max_right C₁ 0; have := le_max_right C₂ 0; nlinarith
  | smul c T _ h =>
    obtain ⟨L, C, hL, hb⟩ := h
    refine ⟨L, ‖c‖ * C, hL, fun w g hg => ?_⟩
    rw [MultilinearMap.smul_apply, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb w g hg) (norm_nonneg _)

end GlobalTheory.Core.Mi.SepPer

namespace GlobalTheory.Core.Mi


open SepPer in
theorem sepCont_per_rTrans : ∀ (D : D7) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : D.what₂.Tau → SPar) (M : DSModel B.V S) (J : Set (GA D B.V)) (χ : GA D B.V → ℂ) (t : GA D B.V) (φ : GA D B.A → ℂ), IsInfFam θ → IsStdChar D ψ (-1) → IsContAut B.A φ → ∀ T ∈ MultT θ M J χ, ∃ Λ : SmT M →ₗ[ℂ] ℂ, SepCont M Λ ∧ ∀ x, Λ x = B.per ψ φ (rTrans t (T x)) := by
  intro D θ ψ ρ B S M J χ t φ hθ hψ hφ T hT
  obtain ⟨-, -, ⟨Ω, hΩc, hΩ⟩, -⟩ := GlobalTheory.T.besselGroup_quotient_fundamentalDomain_cocompact D ρ B
  obtain ⟨Cp, hadd, hbd⟩ := per_add_bound B hψ hφ Ω hΩc hΩ
  set T' : MMap M := PiTensorProduct.lift.symm T with hT'
  have hT'm : T' ∈ Mult θ M J χ := (mem_multT θ M J χ T).1 hT
  have hTt : ∀ u : M.Vec, T (PiTensorProduct.tprod ℂ u) = T' u := by
    intro u
    have : T = PiTensorProduct.lift T' := by rw [hT']; exact (PiTensorProduct.lift.apply_symm_apply T).symm
    rw [this, PiTensorProduct.lift.tprod]
  have hmem : ∀ x : SmT M, T x ∈ contLeft B.V := by
    intro x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r u =>
      rw [map_smul, hTt]
      exact (contLeft B.V).smul_mem r (mult_mem_contLeft θ M J χ hT'm u)
    | add x y hx hy =>
      rw [map_add (f := _)]
      exact (contLeft B.V).add_mem hx hy
  let Λ : SmT M →ₗ[ℂ] ℂ :=
    { toFun := fun x => B.per ψ φ (rTrans t (T x))
      map_add' := fun x y => by
        have e : rTrans t (T (x + y)) = rTrans t (T x) + rTrans t (T y) := by
          funext g; simp [rTrans]
        rw [e]
        exact hadd _ _ (rTrans_mem t (hmem x)) (rTrans_mem t (hmem y))
      map_smul' := fun c x => by
        have e : rTrans t (T (c • x)) = c • rTrans t (T x) := by
          funext g; simp [rTrans]
        have := GlobalTheory.HandHom.per_smul B ψ 1 c φ (rTrans t (T x))
        rw [one_smul, one_mul] at this
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [e, this] }
  refine ⟨Λ, fun τ v => ?_, fun x => rfl⟩
  have hΩt : IsCompact ((fun g => g * t) '' Ω) := hΩc.image (continuous_id.mul continuous_const)
  obtain ⟨L, Cu, hL, hb⟩ := mult_bound θ hθ M J χ hT'm _ hΩt τ v
  let ℓ₀ : M.sm τ →ₗ[ℂ] ℂ := (Λ.compMultilinearMap (PiTensorProduct.tprod ℂ)).toLinearMap v τ
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
  have hℓw : ∀ w : M.sm τ, ℓ w = Λ (PiTensorProduct.tprod ℂ (Function.update v τ w)) := by
    intro w
    have := congrArg (fun m => m w) hℓ
    simpa [ℓ₀, MultilinearMap.toLinearMap_apply] using this
  refine ⟨ℓ, ⟨L, Cp * Cu, hL, fun w hw => ?_⟩, hℓw⟩
  have hw' : w ∈ M.sm τ := Submodule.subset_span hw
  have e := hℓw ⟨w, hw'⟩
  simp only at e
  rw [e]
  change ‖B.per ψ φ (rTrans t (T (PiTensorProduct.tprod ℂ (Function.update v τ ⟨w, hw'⟩))))‖ ≤ _
  have hK : ∀ x ∈ Ω, ‖rTrans t (T (PiTensorProduct.tprod ℂ (Function.update v τ ⟨w, hw'⟩))) x‖ ≤
      Cu * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum := by
    intro x hx
    rw [rTrans, hTt]
    exact hb ⟨w, hw'⟩ (x * t) ⟨x, hx, rfl⟩
  calc _ ≤ Cp * (Cu * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) w‖).sum) := hbd _ (rTrans_mem t (hmem _)) _ hK
    _ = _ := by ring

end GlobalTheory.Core.Mi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuousStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriod_rightTranslate_sobolevSepContinuous : ∀ (D : D7) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : D.what₂.Tau → SPar) (M : DSModel B.V S) (J : Set (GA D B.V)) (χ : GA D B.V → ℂ) (t : GA D B.V) (φ : GA D B.A → ℂ), IsInfFam θ → IsStdChar D ψ (-1) → IsContAut B.A φ → ∀ T ∈ MultT θ M J χ, ∃ Λ : SmT M →ₗ[ℂ] ℂ, SepCont M Λ ∧ ∀ x, Λ x = B.per ψ φ (rTrans t (T x)) := by
  first | exact @GlobalTheory.Core.Mi.sepCont_per_rTrans | exact GlobalTheory.Core.Mi.sepCont_per_rTrans | (intros; apply GlobalTheory.Core.Mi.sepCont_per_rTrans <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockMatrixTwoByTwoFinStandardSkewMap
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.Frame

section Generic
variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

theorem submatrix_fromBlocks_mul (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrixTwoByTwoFin_smul (r : R) (a b c d : Matrix (Fin n) (Fin n) R) :
    r • blk4 a b c d = blk4 (r • a) (r • b) (r • c) (r • d) := by
  unfold blk4
  rw [← Matrix.fromBlocks_smul]; rfl

theorem block_matrix_map (f : R → S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4
  rw [← Matrix.fromBlocks_map]; rfl

theorem blockMatrixTwoByTwoFin_transpose (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d)ᵀ = blk4 aᵀ cᵀ bᵀ dᵀ := by
  unfold blk4
  rw [← Matrix.fromBlocks_transpose]; rfl

theorem blockMatrixTwoByTwoFin_forall_entries (p : R → Prop) {a b c d : Matrix (Fin n) (Fin n) R} (ha : ∀ i j, p (a i j)) (hb : ∀ i j, p (b i j))
    (hc : ∀ i j, p (c i j)) (hd : ∀ i j, p (d i j)) (i j : Fin (n + n)) : p (blk4 a b c d i j) := by
  unfold blk4
  rw [Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j
  exacts [ha i j, hb i j, hc i j, hd i j]

theorem map_smul_hom (f : R →+* S) {m : Type} (r : R) (a : Matrix m m R) : (r • a).map f = f r • a.map f := by
  ext i j; simp

def frm (K : Matrix (Fin n) (Fin n) R) (e t t' : R) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  blk4 1 ((e * t) • K) 1 ((-(e * t')) • K)

def frmInv (H : Matrix (Fin n) (Fin n) R) (e' t t' : R) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  blk4 (t' • 1) (t • 1) (e' • H) ((-e') • H)

variable {H K : Matrix (Fin n) (Fin n) R} {e e' t t' : R}

theorem frm_mul_inv (hKH : K * H = 1) (he : e * e' = 1) (ht : t + t' = 1) :
    frm K e t t' * frmInv H e' t t' = 1 := by
  unfold frm frmInv
  rw [submatrix_fromBlocks_mul, ← block_matrix_one]
  simp only [Matrix.smul_mul, Matrix.mul_smul, hKH, Matrix.one_mul, smul_smul, ← add_smul]
  congr 1
  · rw [show t' + e' * (e * t) = 1 by linear_combination ht + t * he, one_smul]
  · rw [show t + -e' * (e * t) = 0 by linear_combination (-t) * he, zero_smul]
  · rw [show t' + e' * (-(e * t')) = 0 by linear_combination (-t') * he, zero_smul]
  · rw [show t + -e' * (-(e * t')) = 1 by linear_combination ht + t' * he, one_smul]

theorem adj_frm (c : R →+* R) (hK : (K.map c)ᵀ = K) (hct : c t = t') (hct' : c t' = t) :
    ((frm K e t t').map c)ᵀ = blk4 1 1 ((c e * t') • K) ((-(c e * t)) • K) := by
  unfold frm
  rw [block_matrix_map, blockMatrixTwoByTwoFin_transpose, map_smul_hom, map_smul_hom, Matrix.transpose_smul, Matrix.transpose_smul, hK,
    Matrix.map_one _ c.map_zero c.map_one, Matrix.transpose_one, map_neg, map_mul, map_mul, hct, hct']

theorem gram_frm (ce : R) (hKH : K * H = 1) (hHK : H * K = 1) (ht : t + t' = 1) :
    blk4 1 1 ((ce * t') • K) ((-(ce * t)) • K) * blk4 H 0 0 (-H) * frm K e t t' = blk4 0 (e • 1) (ce • 1) 0 := by
  unfold frm
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, hKH, hHK, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, smul_neg, ← neg_smul, smul_smul, ← add_smul]
  congr 1
  · simp
  · congr 1; linear_combination e * ht
  · congr 1; linear_combination ce * ht
  · convert zero_smul R K using 2; ring

theorem norm_frm (ce : R) (f : R →+* S) (hK : (K * K).map f = 1) (ht : t + t' = 1) (h2 : f (2 * t) = 1)
    (h4 : f (e * ce) = 4) :
    (blk4 1 1 ((ce * t') • K) ((-(ce * t)) • K) * frm K e t t').map f = (2 : S) • 1 := by
  unfold frm
  have ht' : f t + f t' = 1 := by rw [← map_add (f := _), ht, map_one]
  have h2' : 2 * f t = 1 := by rw [← h2, map_mul, map_ofNat]
  rw [map_mul] at h4
  rw [submatrix_fromBlocks_mul, ← block_matrix_one, blockMatrixTwoByTwoFin_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, ← add_smul]
  rw [block_matrix_map, map_smul_hom, map_smul_hom, map_smul_hom, hK, smul_zero]
  congr 1
  · rw [← two_smul R, map_smul_hom, Matrix.map_one _ f.map_zero f.map_one, map_ofNat]
  · convert zero_smul S _ using 2
    simp only [map_add (f := _), map_neg, map_mul]
    linear_combination f e * h2' - f e * ht'
  · convert zero_smul S _ using 2
    simp only [map_add (f := _), map_neg, map_mul]
    linear_combination f ce * ht' - f ce * h2'
  · congr 1
    simp only [map_add (f := _), map_neg, map_mul]
    linear_combination (2 * f t * f t') * h4 + (8 * f t) * ht' + (2 - 4 * f t) * h2'

theorem exists_frame_ring (c : R →+* R) (hc : ∀ x, c (c x) = x) (p : R → Prop) (p0 : p 0) (p1 : p 1)
    (pmul : ∀ {x y}, p x → p y → p (x * y)) (pneg : ∀ {x}, p x → p (-x)) (pc : ∀ {x}, p x → p (c x))
    (Hm : GL (Fin n) R) (hH' : (Hm.1.map c)ᵀ = Hm.1) (hI1 : ∀ i j, p (Hm.1 i j)) (hI2 : ∀ i j, p ((Hm⁻¹).1 i j))
    (m : R) (hm : c m = -m) (u ε : Rˣ) (t : R) (hs1 : (ε : R) * u * c u = m) (hs2 : p ε) (hs3 : p (ε⁻¹ : Rˣ))
    (ht1 : t + c t = 1) (ht2 : p t) :
    ∃ M M' : GL (Fin (n + n)) R, (M.1.map c)ᵀ * blk4 Hm.1 0 0 (-Hm.1) * M.1 = m • blk4 0 1 (-1) 0 ∧
      (∀ i j : Fin n, M.1 (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n)) =
        M.1 (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n))) ∧
      ((∀ i j, p (M'.1 i j)) ∧ ∀ i j, p ((M'⁻¹).1 i j)) ∧ M.1 = (u : R) • M'.1 ∧
      ∀ (S : Type) [CommRing S] (f : R →+* S), (Hm.1 * Hm.1).map f = 1 → f (ε * c ε) = 4 → f (2 * t) = 1 →
        ((M.1.map c)ᵀ * M.1).map f = f (2 * u * c u) • 1 := by
  have hKH : (Hm⁻¹).1 * Hm.1 = 1 := Units.inv_mul Hm
  have hHK : Hm.1 * (Hm⁻¹).1 = 1 := Units.mul_inv Hm
  generalize (Hm⁻¹).1 = K at hKH hHK hI2
  have pone : ∀ i j : Fin n, p ((1 : Matrix (Fin n) (Fin n) R) i j) := fun i j => by
    rw [Matrix.one_apply]
    split_ifs
    exacts [p1, p0]
  have hK : (K.map c)ᵀ = K := by
    have h1 : Hm.1 * (K.map c)ᵀ = 1 := by
      conv_lhs => rw [← hH']
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hKH, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.transpose_one]
    calc (K.map c)ᵀ = K * (Hm.1 * (K.map c)ᵀ) := by rw [← Matrix.mul_assoc, hKH, Matrix.one_mul]
      _ = K := by rw [h1, Matrix.mul_one]
  have hinv := frm_mul_inv (e := (ε : R)) (e' := ((ε⁻¹ : Rˣ) : R)) hKH (Units.mul_inv ε) ht1
  have hadj := adj_frm (e := (ε : R)) c hK rfl (hc t)
  let M' : GL (Fin (n + n)) R := ⟨_, _, hinv, mul_eq_one_comm.1 hinv⟩
  let M : GL (Fin (n + n)) R := ⟨(u : R) • M'.1, ((u⁻¹ : Rˣ) : R) • (M'⁻¹).1,
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.mul_inv, Units.mul_inv, one_smul],
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.inv_mul, Units.inv_mul, one_smul]⟩
  have hM : M.1 = (u : R) • frm K (ε : R) t (c t) := rfl
  have hadjM : (M.1.map c)ᵀ = c u • blk4 1 1 ((c ε * c t) • K) ((-(c ε * t)) • K) := by
    rw [← hadj, hM, ← Matrix.transpose_smul, ← map_smul_hom]
  have hcε : c ε * u * c u = -m := by
    have h := congrArg c hs1
    rw [map_mul, map_mul, hc, hm] at h
    linear_combination h
  refine ⟨M, M', ?_, ?_, ⟨?_, ?_⟩, rfl, fun S _ f hR h4 h2 => ?_⟩
  · rw [hadjM, hM, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, gram_frm _ hKH hHK ht1, smul_smul,
      blockMatrixTwoByTwoFin_smul, blockMatrixTwoByTwoFin_smul, smul_zero, smul_zero, smul_smul, smul_smul, smul_neg, ← neg_smul, ← hcε, ← hs1]
    congr 2 <;> ring
  · intro i j
    rw [hM]
    simp only [frm, blk4, Matrix.smul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁]
  · exact blockMatrixTwoByTwoFin_forall_entries p pone (fun i j => pmul (pmul hs2 ht2) (hI2 i j)) pone
      (fun i j => pmul (pneg (pmul hs2 (pc ht2))) (hI2 i j))
  · exact blockMatrixTwoByTwoFin_forall_entries p (fun i j => pmul (pc ht2) (pone i j))
      (fun i j => pmul ht2 (pone i j)) (fun i j => pmul hs3 (hI1 i j))
      (fun i j => pmul (pneg hs3) (hI1 i j))
  · have hKK : (K * K).map f = 1 := by
      have h1 : K * K * (Hm.1 * Hm.1) = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc K Hm.1, hKH, Matrix.one_mul, hKH]
      have h3 : (K * K * (Hm.1 * Hm.1)).map f = (1 : Matrix (Fin n) (Fin n) R).map f := by rw [h1]
      rwa [Matrix.map_mul, hR, Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at h3
    rw [hadjM, hM, Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_smul_hom,
      norm_frm _ _ hKK ht1 h2 h4, smul_smul]
    congr 1
    simp only [map_mul, map_ofNat]
    ring

theorem blockMatrixTwoByTwoFin_standardSkew_map (f : R →+* S) :
    (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0).map f = blk4 0 1 (-1) 0 := by
  rw [block_matrix_map, Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _),
    Matrix.map_one _ (map_zero _) (map_one _)]

end Generic

variable {D : D7}

theorem compFin_cA (v : HeightOneSpectrum (𝓞 D.host.F)) (z : AE D) :
    compFin D.host.F D.host.E v (cA D z) = sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem intA_cA {z : AE D} (h : IntA z) : IntA (cA D z) := by
  intro v
  change compFin D.host.F D.host.E v (cA D z) ∈ intLoc D.host.F D.host.E v
  rw [compFin_cA]; exact sigR_mem_intLoc _ (h v)

theorem intA_mul {x y : AE D} (hx : IntA x) (hy : IntA y) : IntA (x * y) := by
  intro v
  change compFin D.host.F D.host.E v (x * y) ∈ intLoc D.host.F D.host.E v
  rw [map_mul]; exact Subring.mul_mem _ (hx v) (hy v)

theorem intA_neg {x : AE D} (hx : IntA x) : IntA (-x) := by
  intro v
  change compFin D.host.F D.host.E v (-x) ∈ intLoc D.host.F D.host.E v
  rw [map_neg]; exact Subring.neg_mem _ (hx v)

theorem intA_zero : IntA (0 : AE D) := by
  intro v
  change compFin D.host.F D.host.E v 0 ∈ intLoc D.host.F D.host.E v
  rw [map_zero]; exact Subring.zero_mem _

theorem intA_one : IntA (1 : AE D) := by
  intro v
  change compFin D.host.F D.host.E v 1 ∈ intLoc D.host.F D.host.E v
  rw [map_one]; exact Subring.one_mem _

theorem cA_incA_skew {μ : D.host.E} (h : IsSkew μ) : cA D (incA D μ) = -incA D μ := by
  change μ ≠ 0 ∧ star μ = -μ at h
  rw [show cA D (incA D μ) = incA D (star μ) from rfl, h.2, map_neg]

theorem rat_Jst (n : ℕ) : (rat (Jst D n) : Mx D (n + n) (n + n)) = blk4 0 1 (-1) 0 := blockMatrixTwoByTwoFin_standardSkew_map (incA D)

theorem exists_frame : ∀ (D : D7) (n : ℕ) (Hm : GL (Fin n) (AE D)), adj Hm.1 = Hm.1 → IntGL Hm → (∀ w, (Hm.1 * Hm.1).map (compInf D.host.F D.host.E w) = 1) → ∀ (μ : D.host.E) (u ε : (AE D)ˣ) (t : AE D), IsSkew μ → ScalData μ u ε → HalfData t → ∃ M M' : GL (Fin (n + n)) (AE D), adj M.1 * dblGram finSumFinEquiv Hm.1 * M.1 = incA D μ • rat (Jst D n) ∧ (∀ i j : Fin n, M.1 (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n)) = M.1 (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n))) ∧ IntGL M' ∧ M.1 = (u : AE D) • M'.1 ∧ ∀ w, (adj M.1 * M.1).map (compInf D.host.F D.host.E w) = compInf D.host.F D.host.E w (2 * u * cA D u) • 1 := by
  intro D n Hm hH hI hR μ u ε t hμ hs ht
  obtain ⟨M, M', h1, h2, h3, h4, h5⟩ := exists_frame_ring (cA D) Formalism.L2.Theta.cA_cA (fun z : AE D => IntA z) intA_zero intA_one
    intA_mul intA_neg intA_cA Hm hH hI.1 hI.2 (incA D μ) (cA_incA_skew hμ) u ε t hs.1 hs.2.1 hs.2.2.1 ht.1 ht.2.1
  refine ⟨M, M', ?_, h2, h3, h4, fun w => h5 _ _ (hR w) (hs.2.2.2 w) (ht.2.2 w)⟩
  rw [rat_Jst]
  exact h1

end GlobalTheory.StdUnn.Frame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanInvolutionEqOfCommute
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanInvolutionEqOfCommute
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder

namespace GlobalTheory.StdUnn

theorem isCartanInv_eq_of_commute : ∀ (k : ℕ) (G s s' : Matrix (Fin k) (Fin k) ℂ), IsCartanInv G s → IsCartanInv G s' → s * s' = s' * s → s = s' := by
  intro k G s s' h h' hc
  have key : ∀ w : Fin k → ℂ, s' *ᵥ w = -(s *ᵥ w) → w = 0 := by
    intro w hw
    by_contra hne
    have h1 := h.2.2.dotProduct_mulVec_pos hne
    have h2 := h'.2.2.dotProduct_mulVec_pos hne
    rw [← Matrix.mulVec_mulVec, hw, Matrix.mulVec_neg, dotProduct_neg, Matrix.mulVec_mulVec] at h2
    exact lt_asymm h1 (neg_pos.1 h2)
  have e : s' * (1 - s * s') = -(s * (1 - s * s')) := by
    rw [Matrix.mul_sub, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hc, h.1,
      Matrix.mul_assoc, h'.1]
    simp
  have hr : (1 - s * s') = 0 := by
    ext i j
    have := key ((1 - s * s') *ᵥ Pi.single j 1) (by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e, Matrix.neg_mulVec])
    simpa using congrFun this i
  have h1 : s * s' = 1 := (sub_eq_zero.1 hr).symm
  calc s = s * (s * s') := by rw [h1, Matrix.mul_one]
    _ = s' := by rw [← Matrix.mul_assoc, h.1, Matrix.one_mul]

end GlobalTheory.StdUnn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanInvolutionEqOfCommuteStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartanInvolution_eq_of_commute : ∀ (k : ℕ) (G s s' : Matrix (Fin k) (Fin k) ℂ), IsCartanInv G s → IsCartanInv G s' → s * s' = s' * s → s = s' := by
  first | exact @GlobalTheory.StdUnn.isCartanInv_eq_of_commute | exact GlobalTheory.StdUnn.isCartanInv_eq_of_commute | (intros; apply GlobalTheory.StdUnn.isCartanInv_eq_of_commute <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CastGAMemGFset
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Core.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem castGA_mem_GFset {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA) :
    Formalism.L2.SG.RowsJoinPinned.castGA e x ∈ I'.GFset ↔ x ∈ I.GFset := by
  subst e; rfl

theorem besGrp_iff_sA (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (g : GA D (D.sp.Y 0)) :
    g ∈ besGrp B.d B.o ↔ (iotaX X h g).1 ∈ X.SinfU u ∧ (iotaX X h g).2 ∈ SfinU X u := by
  have hS : besGrp B.d B.o = (Formalism.L2.SG.Pf.SAsub X u).comap (iotaX X h).toMonoidHom := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro n hn
        obtain ⟨h1, h2⟩ := (B.tieN n).1 hn
        exact ⟨fun v => (h1 v).1, Formalism.L2.SG.Pf.nfin_sfin X u h2⟩
      · intro g hg
        obtain ⟨h1, h2⟩ := (B.tieH g).1 hg
        exact ⟨hinf_le_sinf X u _ h1, Formalism.L2.SG.Pf.hfin_sfin X u ⟨_, h2⟩⟩
    · intro g hg
      have hg' : (iotaX X h g).1 ∈ X.SinfU u ∧ (iotaX X h g).2 ∈ SfinU X u := hg
      obtain ⟨hg1, hg2⟩ := hg'
      obtain ⟨hi, hhi, ni, hni, ei⟩ := Formalism.L2.SG.Pf.Sinf.levi X u hg1
      obtain ⟨hf, nf, hnf, ef⟩ := Formalism.L2.SG.Closed.FinLeviC_holds D X u _ hg2
      have hgeq : g = (iotaX X h).symm (hi, (hf : X.B.I.Gf)) * (iotaX X h).symm (ni, nf) := by
        rw [← map_mul, (iotaX X h).eq_symm_apply]
        exact Prod.ext ei ef
      rw [hgeq]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left ?_)
      · refine (B.tieH _).2 ?_
        rw [ContinuousMulEquiv.apply_symm_apply]
        exact ⟨hhi, hf.2⟩
      · refine (B.tieN _).2 ?_
        rw [ContinuousMulEquiv.apply_symm_apply]
        exact ⟨hni, hnf⟩
  rw [hS]; rfl

theorem besGrp_eq_sGroup : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A),
    (∀ g, g ∈ besGrp B.d B.o ↔ (iotaX X h g).1 ∈ X.SinfU u ∧ (iotaX X h g).2 ∈ SfinU X u) ∧
      ∀ g, g ∈ GQ (D.sp.Y 0) ⊓ besGrp B.d B.o ↔ iotaX X h g ∈ Srat X u := by
  intro D X h u ψ A B
  refine ⟨besGrp_iff_sA D X h u ψ A B, fun g => ?_⟩
  rw [Subgroup.mem_inf, besGrp_iff_sA D X h u ψ A B, Formalism.L2.SG.Pf.srat_eq, Subgroup.mem_inf,
    Formalism.MainNotions.LeviCoordinates.rr_mem_GF, Formalism.IndefR.RationalEmbedding.iota_rat]
  have e : iotaX X h g = Formalism.L2.SG.RowsJoinPinned.castGA h.symm (Formalism.IndefR.RationalEmbedding.iota D g) := rfl
  rw [e, castGA_mem_GFset]
  rfl

end GlobalTheory.Core.Mi

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealPlacesIdempotentExtensionAdeles
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealPlacesIdempotentExtensionAdeles
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

section
variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]

private theorem realIdem_map {R S : Type} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] (f : R →ₐ[F] S)
    (σ : E →ₐ[F] E) (x : R) :
    (Algebra.TensorProduct.map f σ).toRingHom (x ⊗ₜ[F] (1 : E)) = f x ⊗ₜ[F] (1 : E) := by
  change Algebra.TensorProduct.map f σ (x ⊗ₜ[F] (1 : E)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]

private theorem realIdem_gen (σ : E →ₐ[F] E) : ∃ e : AF F ⊗[F] E, e * e = e ∧ sigR (AF F) σ e = e ∧
    (∀ v, compFin F E v e = 0) ∧ (∀ w, compInf F E w e = 1) ∧
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom e = 0 ∧
    (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom e = 1 := by
  have hp : pairA F 1 0 * pairA F 1 0 = pairA F 1 0 :=
    Prod.ext (mul_one (1 : Ainf F)) (mul_zero (0 : Af F))
  have h0 : sndA F (pairA F 1 0) = 0 := rfl
  have h1 : fstA F (pairA F 1 0) = 1 := rfl
  refine ⟨pairA F 1 0 ⊗ₜ[F] (1 : E), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hp]
  · exact realIdem_map F E (AlgHom.id F (AF F)) σ _
  · intro v
    refine (realIdem_map F E (evFin F v) (AlgHom.id F E) _).trans ?_
    rw [evFin, AlgHom.comp_apply, h0, map_zero, TensorProduct.zero_tmul]
  · intro w
    refine (realIdem_map F E (evInf F w) (AlgHom.id F E) _).trans ?_
    rw [evInf, AlgHom.comp_apply, h1, map_one, Algebra.TensorProduct.one_def]
  · rw [realIdem_map, h0, TensorProduct.zero_tmul]
  · rw [realIdem_map, h1, Algebra.TensorProduct.one_def]

end

theorem realIdem_exists : ∀ D : D7, ∃ e : AE D, e * e = e ∧ cA D e = e ∧ (∀ v, compFin D.host.F D.host.E v e = 0) ∧ (∀ w, compInf D.host.F D.host.E w e = 1) ∧ finPart D e = 0 ∧ infPart D e = 1 :=
  fun D => realIdem_gen D.host.F D.host.E _

end GlobalTheory.StdUnn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealPlacesIdempotentExtensionAdelesStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realPlacesIdempotent_extensionAdeles : ∀ D : D7, ∃ e : AE D, e * e = e ∧ cA D e = e ∧ (∀ v, compFin D.host.F D.host.E v e = 0) ∧ (∀ w, compInf D.host.F D.host.E w e = 1) ∧ finPart D e = 0 ∧ infPart D e = 1 := by
  first | exact @GlobalTheory.StdUnn.realIdem_exists | exact GlobalTheory.StdUnn.realIdem_exists | (intros; apply GlobalTheory.StdUnn.realIdem_exists <;> assumption)
end
end
