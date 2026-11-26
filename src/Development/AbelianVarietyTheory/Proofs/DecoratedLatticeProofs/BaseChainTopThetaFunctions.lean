module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopStepVectorTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaLiftInnerProductFormulaOfPublishedStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedPlacesSpherical
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulSumEqZeroOfPureTensorFunctionZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteZetaIntegralThetaLiftEqPartialLValue
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeCoefficientsSqIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivEqZeroOfEven
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKTranslate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasDerivAtLogCosh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MatrixEntryNormSumUpperRightBlockElementPLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.T2SpaceIsNonarchimedeanLocalFieldSingleBlock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLastStepTwistBasePoint
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenStringOfAgreement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainTopThetaFunctions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BaseChainTop

variable {D : D7}

theorem comb_pureTensorO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS sT BS BT) {e : WO S T →₀ ℂ} (he : IsFinComb e) {f₀ : WO S T → ℂ}
    (hf₀ : IsThetaFunO ψ S T f₀) (P) :
    comb ψ S T e (pureTensorO ψ θ S T sS sT BS BT f₀ P) = pureTensorO ψ θ S T sS sT BS BT (comb ψ S T e f₀) P := by
  let q := e.support.equivFin
  have key := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hψ hθ sS sT BS BT f₀ hf₀ e.support.card
    (fun i => e (q.symm i).1) (fun i => (q.symm i).1) (fun i => he _ (q.symm i).2) P).1
  have h1 : ∀ g : WO S T → (WO S T → ℂ), ∑ u ∈ e.support, e u • g u = ∑ i, e (q.symm i).1 • g (q.symm i).1 := by
    intro g
    rw [← Finset.sum_coe_sort e.support]
    exact (Equiv.sum_comp q.symm (fun u : e.support => e u.1 • g u.1)).symm
  simp only [comb]
  rw [h1, h1]
  exact key

theorem isItW_of_comb {V W : HSp D} {S S' : D.what₂.Tau → SPar} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {M : DSModel V S} {M' : DSModel W S'} {χS χT : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hω : IsWeilDatumO ψ V W χS χT ω) (hθ : IsInfFam θ)
    {f g : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) {b : WO V W →₀ ℂ} (hb : IsFinComb b) (hg : comb ψ V W b f = g)
    {It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M}
    (hI : IsItW θ M M' ω (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') g) It) :
    IsItW θ M M' ω (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f) It := by
  have hψ : IsStdChar D ψ (-1) := hω.std
  have hpt : ∀ φ, IsThetaFunO ψ V W (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ _ _ _ _ hf φ
  have hrel : ∀ φ, comb ψ V W b (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f φ) =
      pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') g φ := fun φ => by
    rw [← hg]
    exact comb_pureTensorO hψ hθ _ _ _ _ hb hf φ
  have hcomm : ∀ a ∈ GinfC V, ∀ a' ∈ GinfC W, ∀ φ,
      ω (a, a') (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') g φ) =
        comb ψ V W b (ω (a, a') (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f φ)) := fun a ha a' ha' φ => by
    rw [← hrel, GlobalTheory.FrComb.om_comb hω ha ha' hb (hpt φ)]
  refine ⟨hI.ne, hI.bdd, fun τ x hx φ φ' h v => ?_, fun τ X hX φ φ' hd v => ?_, fun τ y hy φ φ' v v' h hv => ?_,
    fun τ X hX φ φ' v v' hd hD => ?_⟩
  · refine hI.eqK τ x hx φ φ' ?_ v
    rw [hcomm _ (Formalism.IndefR.Eqv.Act.atTau_mem θ τ x) 1 (one_mem _) φ, ← h, hrel]
  · refine hI.eqg τ X hX φ φ' (fun z => ?_) v
    have e1 : (fun t : ℝ => ω (oneP θ V τ X t, 1) (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') g φ) z) =
        fun t => ∑ x ∈ b.support, b x * (ψ (symplOH V W z x) *
          ω (oneP θ V τ X t, 1) (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f φ) (z + x)) := funext fun t => by
      rw [hcomm _ (Formalism.IndefR.Eqv.Act.oneP_mem θ τ X t) 1 (one_mem _) φ, GlobalTheory.FrComb.comb_apply]
    rw [e1, ← hrel φ', GlobalTheory.FrComb.comb_apply]
    exact HasDerivAt.fun_sum fun x _ => ((hd (z + x)).const_mul _).const_mul _
  · refine hI.invK τ y hy φ φ' v v' ?_ hv
    rw [hcomm 1 (one_mem _) _ (Formalism.IndefR.Eqv.Act.atTau_mem θ τ y) φ, ← h, hrel]
  · refine hI.invg τ X hX φ φ' v v' (fun z => ?_) hD
    have e1 : (fun t : ℝ => ω (1, oneP θ W τ X t) (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') g φ) z) =
        fun t => ∑ x ∈ b.support, b x * (ψ (symplOH V W z x) *
          ω (1, oneP θ W τ X t) (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f φ) (z + x)) := funext fun t => by
      rw [hcomm 1 (one_mem _) _ (Formalism.IndefR.Eqv.Act.oneP_mem θ τ X t) φ, GlobalTheory.FrComb.comb_apply]
    rw [e1, ← hrel φ', GlobalTheory.FrComb.comb_apply]
    exact HasDerivAt.fun_sum fun x _ => ((hd (z + x)).const_mul _).const_mul _

end GlobalTheory.BaseChainTop

namespace GlobalTheory.BaseChainTop

end GlobalTheory.BaseChainTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerProductEqConstMulLValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerProductEqConstMulLValue
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AFormL

theorem aFormL : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → D.host.ccK = ⊤ → ∀ SF, GlobalTheory.Hk3.IsSF R SF → AForm R SF := by
  intro hDS hHC hCusp hWS hSE hUD hBZ D G _ _ Pl0 T A Ks _ _ _ R F hG hc SF hSF
  have hHM := GlobalTheory.HarmModule.harmonicModule_of GlobalTheory.FockDecay.harmonicDecay GlobalTheory.CartanInt.coshIntegral
  have hPM := GlobalTheory.PlaceTensor.placeModels D
  exact GlobalTheory.LiftScalarL.aForm R F
    (GlobalTheory.T.finiteDatum_sourceLevelCharacter_law GlobalTheory.SingleBlock.localIntegralSingleBlock R F hPM)
    (GlobalTheory.T.twistedThetaLift_innerProductFormula_of_hypotheses hCusp hWS hSE R F hG.params)
    (GlobalTheory.T.fockVector_matrixCoefficient_formula hHM R F hPM)
    (GlobalTheory.T.finiteZetaIntegral_thetaLift_eq_partialLValue hCusp hBZ hUD R F)
    (GlobalTheory.T.thetaLevelIndex_mul_schwartzNorm_formula GlobalTheory.SingleBlock.localIntegralSingleBlock R F hPM)
    (GlobalTheory.RealCoefSq.lowestKType_coefficients_sq_integrable R F hG.core)
    hG hc SF hSF

end GlobalTheory.AFormL

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerProductEqConstMulLValueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaInnerProduct_eq_const_mul_LValue : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → D.host.ccK = ⊤ → ∀ SF, GlobalTheory.Hk3.IsSF R SF → AForm R SF := by
  first | exact @GlobalTheory.AFormL.aFormL | exact GlobalTheory.AFormL.aFormL | (intros; apply GlobalTheory.AFormL.aFormL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DataNonvanishingAllMembers
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.MemberData


open Formalism.MainNotions.S in
theorem dataNW_of_val {C : Formalism.MainNotions.Inhab.FC} {cD ch : ℝ} (hC : Std C) {D : D7} (L : SizeData₂ D)
    (hV : Val C cD ch L) (hS : SizesAt L) (hR : ∀ u, GlobalTheory.Core.Rk.RankMu D u) : GlobalTheory.Core.Deg.DataNW D := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hk0 : 0 < D.R.k := by omega
  have hSc := Sc_eq' L
  have e1 : ∀ u τ, uOne D u τ 1 = (((D.hc τ).u ⟨0, hk0⟩ : ℚ) : ℝ) := fun u τ => by
    rw [show (1 : ℕ) = 0 + 1 from rfl, uOne_succ u τ 0 hk0, D.hcW_first u τ hk0]
  have e2 : ∀ τ, vOne D τ 1 = (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) := fun τ => vOne_succ τ 0 (by omega)
  have hCc : L.Cc = 2 := hV.Cc_eq.trans hC.2.1
  have hdu : ∀ u, 0 < D.duS u := fun u => by
    have h := hR u
    unfold GlobalTheory.Core.Rk.RankMu at h
    rw [GlobalTheory.Core.Rk.d0_eq] at h
    have hd : (0 : ℝ) < (D.mem u).A.duStar := by exact_mod_cast (D.mem u).A.duStar_pos
    have hT : (1 : ℝ) < (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.one_lt
    have hTk : 0 < ((D.mem u).A.T : ℝ) ^ D.R.k - 1 := sub_pos.2 (one_lt_pow₀ hT (by omega))
    have h0 : (0 : ℝ) < D.duS u := by rw [h]; positivity
    exact_mod_cast h0
  refine ⟨data1 L, data2, ?_, ?_, ?_, ?_, data7, data8,
    fun u => ⟨GlobalTheory.CollCompare.splits_level D u, T_mod D u⟩, hdu,
    Formalism.L2.SG.ResidEvFree.splitsE_g D 0, Formalism.L2.SG.ResidEvFree.splitsE_g D 1,
    discriminant_eq_base_sq D (Formalism.MainNotions.UnusedSlot33.ramification_two_and_conjugation_at_q_and_d D),
    fun u => ne_of_mod (D.host.g_prime 0).two_le (D.host.g_prime 1).two_le (T_mod D u)⟩
  · intro u τ
    rw [e1, e2, ← hSc]
    by_cases ht : Formalism.MainNotions.S.IsTop D τ
    · obtain ⟨t, ht⟩ := ht
      have h1 := (L.top_u τ t hk0 ht).1
      have h2 := (L.cloud_v τ ⟨0, by omega⟩).2
      have h3 := (L.aT_win t).1
      have h4 := Formalism.MainNotions.FormalGroupSystem.Pf.nd_Sc_le hS
      have h5 := L.Sc_pos
      have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
      rw [h1]
      linarith
    · have := (L.cloud_gap τ (by omega) (fun h => ht ((isTop_iff τ).2 h))).1
      push_cast at this
      exact this
  · intro u τ ht
    have := (L.cloud_gap τ (by omega) (fun h => ht ((isTop_iff τ).2 h))).2
    push_cast at this
    rw [hCc] at this
    rw [e1, e2]
    linarith
  · intro u τ ht
    have hv := hV.hc.1 τ ⟨D.R.k - 2, by omega⟩
    have hu := (hV.hc.2.1 τ hk0 (fun h => ht ((isTop_iff τ).2 h))).2
    have e : D.R.k - 1 = D.R.k - 2 + 1 := by omega
    have hv' := vOne_succ τ (D.R.k - 2) (by omega)
    rw [← e] at hv'
    rw [uOne_last u τ, hv', hv, hu]
    norm_num
  · intro τ ht
    obtain ⟨t, ht⟩ := ht
    have hm0 : 0 < D.R.m := by omega
    have eb : bOne D τ 1 = (((D.hc τ).b ⟨0, hm0⟩ : ℚ) : ℝ) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, bOne_succ τ 0 hm0]
    have et : bTop D τ = (L.bT t : ℝ) + ((D.R.k : ℝ) - 1) / 2 := by
      unfold bTop
      rw [uOne_last D.u₀ τ, (L.top_u τ t hk0 ht).2]
      ring
    have h1 := L.top_b τ t hm0 ht
    obtain ⟨b1, hb, htop, -, -⟩ := hV.hc.2.2.1
    have hb0 := (hb τ ⟨0, hm0⟩).1
    have hbt := htop τ t ht
    have hbR : (((D.hc τ).b ⟨0, hm0⟩ : ℚ) : ℝ) = (L.bT t : ℝ) + ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) := by
      rw [hb0, hbt]
      push_cast
      ring
    have hfl : ((⌊L.sc.b' / L.sc.x⌋ : ℤ) : ℝ) ≤ L.sc.b' / L.sc.x := Int.floor_le _
    have hb'0 := Formalism.MainNotions.FormalGroupSystem.Pf.nd_b'_nonneg (L := L)
    have hx1 := Formalism.MainNotions.FormalGroupSystem.Pf.nd_x_ge (L := L)
    have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb'0 hx1
    have hbT := L.bT_ge t
    have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
    rw [eb, et]
    constructor <;> linarith

theorem val_congr {C C' : Formalism.MainNotions.Inhab.FC} {cD cD' ch ch' : ℝ} {D : D7} {L : SizeData₂ D} (h1 : C = C') (h2 : cD = cD')
    (h3 : ch = ch') (h : Val C cD ch L) : Val C' cD' ch' L := by
  subst h1 h2 h3
  exact h

end GlobalTheory.Fam.MemberData

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicUnitaryLiftOfChartBasePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicUnitaryLiftOfChartBasePoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.BasePointLift

theorem exists_lift_of_ptOf : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : ℕ) (hi : i ≤ B.R.m) (k : TC.GA B (B.R.N i)), (∃ p : Formalism.L2.Col.DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, TC.PtOf k p ∧ p.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) → ∃ kA : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i), kA ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) kA = k.1 := by
  intro B X I hI hP l Z i hi k hk
  obtain ⟨p, hp, -⟩ := hk
  have hu := hp.uni
  obtain ⟨-, -, -, hg⟩ := GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z
  have hg1 := (hg i hi).1
  unfold Formalism.L2.Forms.gramN at hg1
  have hy : k ∈ Formalism.UG.UPts (Formalism.L2.Forms.sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))
      (((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).sp.X i).gram.reindex (finCongr (rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi)) (finCongr (rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi)))
      (FiniteAdeleRing (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) := by
    rw [hg1]
    change k ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i)
    exact hu
  obtain ⟨a, ha, e⟩ := GlobalTheory.Core.Mi.PinModel.exists_finM _ (rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) i hi) ⟨k, hy⟩
  exact ⟨a, ha, e⟩

end GlobalTheory.BasePointLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicUnitaryLiftOfChartBasePointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicUnitaryLift_of_chartBasePoint : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : ℕ) (hi : i ≤ B.R.m) (k : TC.GA B (B.R.N i)), (∃ p : Formalism.L2.Col.DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, TC.PtOf k p ∧ p.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) → ∃ kA : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i), kA ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) kA = k.1 := by
  first | exact @GlobalTheory.BasePointLift.exists_lift_of_ptOf | exact GlobalTheory.BasePointLift.exists_lift_of_ptOf | (intros; apply GlobalTheory.BasePointLift.exists_lift_of_ptOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelCharacterRepsOnAdelicUnitaryPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelCharacterRepsOnAdelicUnitaryPoints
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.ChartLevRead

theorem exists_finM_GfC {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (V.gram.reindex (finCongr hn) (finCongr hn))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ a ∈ GfC V, GlobalTheory.AdForm.finM V hn a = y.1.1 := by
  subst hn
  obtain ⟨a, ha, e⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V ⟨y.1, y.2⟩
  refine ⟨a, ha, ?_⟩
  have e2 : (Lev.finE V a : GL _ _) = y.1 := congrArg Subtype.val e
  rw [← e2]
  rfl

theorem levData : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : ℕ) (hi : i ≤ B.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} (K : LevelChart (I.rec7 l Z) T bad i hi stab lat), ∃ (U : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))) (chi : U →* ℂˣ) (h : cl → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)), (∀ g, g ∈ U ↔ g ∈ GfC _ ∧ ∃ κ : K.lev.U, κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g) ∧ (∀ (g : U) (κ : K.lev.U), κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 → chi g = K.lev.chi κ) ∧ (∀ c, h c ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (h c) = (K.y c).1.1) := by
  intro B X I l Z i hi T bad cl stab _ lat K
  refine ⟨GfC _ ⊓ GlobalTheory.ClassSumLevel.levG _ (rankN (I.rec7 l Z) i hi) K.lev, ?_⟩
  have huniq : ∀ κ κ' : K.lev.U, κ.1.1 = κ'.1.1 → κ = κ' := fun κ κ' h => Subtype.ext (Units.ext h)
  let φ : (GfC _ ⊓ GlobalTheory.ClassSumLevel.levG _ (rankN (I.rec7 l Z) i hi) K.lev : Subgroup _) → K.lev.U :=
    fun g => (Subgroup.mem_inf.1 g.2).2.choose
  have hφ : ∀ g, (φ g).1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 := fun g => (Subgroup.mem_inf.1 g.2).2.choose_spec
  let Φ : (GfC _ ⊓ GlobalTheory.ClassSumLevel.levG _ (rankN (I.rec7 l Z) i hi) K.lev : Subgroup _) →* K.lev.U :=
    MonoidHom.mk' φ (fun a b => huniq _ _ (by
      show (φ (a * b)).1.1 = (φ a).1.1 * (φ b).1.1
      rw [hφ, hφ, hφ]
      exact StabMove.finM_mul _ _ a.1 b.1))
  choose h hG hh using fun c => exists_finM_GfC _ (rankN (I.rec7 l Z) i hi) (K.y c)
  refine ⟨K.lev.chi.comp Φ, h, fun g => ?_, fun g κ hκ => ?_, fun c => ⟨hG c, hh c⟩⟩
  · rw [Subgroup.mem_inf]; rfl
  · show K.lev.chi (φ g) = K.lev.chi κ
    exact congrArg K.lev.chi (huniq (φ g) κ ((hφ g).trans hκ.symm))

end GlobalTheory.ChartLevRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelCharacterRepsOnAdelicUnitaryPointsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevelCharacterReps_on_adelicUnitaryPoints : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (i : ℕ) (hi : i ≤ B.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} (K : LevelChart (I.rec7 l Z) T bad i hi stab lat), ∃ (U : Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))) (chi : U →* ℂˣ) (h : cl → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)), (∀ g, g ∈ U ↔ g ∈ GfC _ ∧ ∃ κ : K.lev.U, κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g) ∧ (∀ (g : U) (κ : K.lev.U), κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 → chi g = K.lev.chi κ) ∧ (∀ c, h c ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (h c) = (K.y c).1.1) := by
  first | exact @GlobalTheory.ChartLevRead.levData | exact GlobalTheory.ChartLevRead.levData | (intros; apply GlobalTheory.ChartLevRead.levData <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdditiveCharacterCongruenceInvariance
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

noncomputable section

namespace GlobalTheory.FamTraceChiColSide

theorem psi_unif_mul_congr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ}
    (S : GlobalTheory.SymChain.SymData k s κ) (d e : k) (hv : valuation k (d - e) < 1) :
    (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * e) : ℂ) = (S.ψ (((S.ϖ⁻¹ : kˣ) : k) * d) : ℂ) := by
  have hsplit : ((S.ϖ⁻¹ : kˣ) : k) * d = ((S.ϖ⁻¹ : kˣ) : k) * e + ((S.ϖ⁻¹ : kˣ) : k) * (d - e) := by ring
  have h1 : S.ψ (((S.ϖ⁻¹ : kˣ) : k) * (d - e)) = 1 := by
    refine (S.cond 1).2 le_rfl _ ?_
    have hle := (S.unif _).1 hv
    have hϖ : valuation k ((S.ϖ : kˣ) : k) ≠ 0 := by simp
    rw [map_one, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    calc (valuation k ((S.ϖ : kˣ) : k))⁻¹ * valuation k (d - e)
        ≤ (valuation k ((S.ϖ : kˣ) : k))⁻¹ * valuation k ((S.ϖ : kˣ) : k) := by gcongr
      _ = 1 := inv_mul_cancel₀ hϖ
  rw [hsplit, AddChar.map_add_eq_mul, h1, mul_one]

end GlobalTheory.FamTraceChiColSide

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStepPointOfChartBasePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStepPointOfChartBasePoint
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.KxPoint

theorem pointOf_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i ≤ B.R.m → ∀ {C : Type} (chOf : (I.stp u a i).Cl → C) (Lb : C → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U : C → Subgroup (TC.GA B (B.R.N i))) (chi : ∀ β, U β →* ℂˣ) (y : (I.stp u a i).Cl → TC.GA B (B.R.N i)) (st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k : C → TC.GA B (B.R.N i)), I.Reads u a i chOf Lb U chi y st k → ∀ β, (∃ q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, TC.PtOf (k β) q) → (∀ P ∈ I.SQ, P ∉ I.Q a → (k β).1.map (adAt B.host.F P) = 1) → ∃ (b0 : Idx I.sel (I.tup a) (I.idx a) i) (p0 : PtAt B.R I.sel (I.tup a) (I.cst a) u i), TC.PtOf (k β) (extTo I.SQ p0.1.1) ∧ p0.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) ∧ ∀ c, chOf c = β → c.1 = b0 ∧ cosetIn ((I.stp u a i).rep c) = cosetIn p0 := by
  intro B X I hI hP u a i hi C chOf Lb U chi y st k hR β hq hk
  have hPr : (B.primes X).Ok := (base_fields_primes_ok B X).2.1
  have hd := ChEx.q_disj I hI a
  obtain ⟨c₀, hc₀⟩ := hR.onto β
  obtain ⟨q, hqk⟩ := hq
  obtain ⟨p, hpk, hpN⟩ := hR.k_std β
  have hqN : q.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) := by
    rw [← hpN]
    exact GlobalTheory.BaseCosetPt.lat_eq_of_carries
      (Formalism.L2.Ker.full_of_sd ⟨q.deco.2.lat, q.deco.2.uni⟩)
      (Formalism.L2.Ker.full_of_sd ⟨p.deco.2.lat, p.deco.2.uni⟩) hqk.lat hpk.lat
  obtain ⟨r', hr'1, hr'2, hr'3⟩ := ChExM.exists_pt_inv hd ((I.stp u a i).rep c₀) q
  have hcos : cosetIn r' = cosetIn ((I.stp u a i).rep c₀) :=
    (ChExM.cosetIn_iff hd (MemChart.hqG hPr) _ _).2 ⟨hr'2, hr'3⟩
  refine ⟨c₀.1, r', ?_, ?_, ?_⟩
  · rw [hr'1]
    refine ⟨hqk.uni, hqk.lat, hqk.f, hqk.be, fun P i' j => ?_⟩
    rw [extTo_fr]
    by_cases hPQ : P.1 ∈ I.Q a
    · rw [ptFr_of_mem q (hd P.1 hPQ) hPQ]
      exact hqk.fr ⟨P.1, hPQ⟩ i' j
    · have hPG : P.1 ∉ (B.primes X).vGs := by
        obtain ⟨b, -, hb⟩ := Finset.mem_biUnion.1 P.2
        exact ChEx.q_disj I hI b P.1 hb
      have hfr : ptFr q P.1 = 1 := by
        unfold ptFr
        rw [dite_eq_right hPG, dite_eq_right hPQ, hqN]
        unfold GlobalTheory.Mem.Col2.latFr
        exact if_pos rfl
      have hkP := congrFun (congrFun (hk P.1 P.2 hPQ) i') j
      rw [hfr]
      simp only [Matrix.map_apply] at hkP
      rw [hkP]
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  · rw [hr'1]; exact hqN
  · intro c hc
    obtain ⟨h1, h2⟩ := (hR.key c c₀).1 (hc.trans hc₀.symm)
    exact ⟨h1, h2.trans hcos.symm⟩

end GlobalTheory.KxPoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStepPointOfChartBasePointStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stepPoint_of_chartBasePoint : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i ≤ B.R.m → ∀ {C : Type} (chOf : (I.stp u a i).Cl → C) (Lb : C → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U : C → Subgroup (TC.GA B (B.R.N i))) (chi : ∀ β, U β →* ℂˣ) (y : (I.stp u a i).Cl → TC.GA B (B.R.N i)) (st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k : C → TC.GA B (B.R.N i)), I.Reads u a i chOf Lb U chi y st k → ∀ β, (∃ q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, TC.PtOf (k β) q) → (∀ P ∈ I.SQ, P ∉ I.Q a → (k β).1.map (adAt B.host.F P) = 1) → ∃ (b0 : Idx I.sel (I.tup a) (I.idx a) i) (p0 : PtAt B.R I.sel (I.tup a) (I.cst a) u i), TC.PtOf (k β) (extTo I.SQ p0.1.1) ∧ p0.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) ∧ ∀ c, chOf c = β → c.1 = b0 ∧ cosetIn ((I.stp u a i).rep c) = cosetIn p0 := by
  first | exact @GlobalTheory.KxPoint.pointOf_base | exact GlobalTheory.KxPoint.pointOf_base | (intros; apply GlobalTheory.KxPoint.pointOf_base <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevOnto

theorem list_prod_map_mulSingle {n : ℕ} {G : Fin n → Type*} [∀ i, Monoid (G i)] (x : ∀ i, G i) (k : Fin n) :
    ∀ l : List (Fin n), l.Nodup → ((l.map fun i => Pi.mulSingle i (x i) k).prod = if k ∈ l then x k else 1)
  | [], _ => by simp
  | b :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, list_prod_map_mulSingle x k l hl.2]
    by_cases hb : b = k
    · subst hb
      simp [hl.1]
    · rw [Pi.mulSingle_eq_of_ne (Ne.symm hb), one_mul]
      simp [List.mem_cons, Ne.symm hb]

theorem list_prod_mulSingle {n : ℕ} {G : Fin n → Type*} [∀ i, Monoid (G i)] (x : ∀ i, G i) :
    ((List.finRange n).map fun i => Pi.mulSingle i (x i)).prod = x := by
  funext k
  rw [Pi.list_prod_apply, List.map_map]
  have := list_prod_map_mulSingle x k (List.finRange n) (List.nodup_finRange n)
  simpa [Function.comp_def] using this

theorem map_pr_eq_one {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (V : HSp D) (g : GA D V)
    (hg : SuppAt q.e V g) (hv : q.v ≠ q'.v) : (mt V g).map q'.pr = 1 := by
  obtain ⟨ε, hε, hE⟩ := q.above
  obtain ⟨ε', hε', hE'⟩ := q'.above
  rw [GlobalTheory.SplitCut.eFin_of_placeIdem hε] at hE
  rw [GlobalTheory.SplitCut.eFin_of_placeIdem hε'] at hE'
  have hsp := q'.split
  have h0 : q'.e * (q.e + cA D q.e) = 0 := by
    have h1 : q'.e = q'.e * (q'.e + cA D q'.e) := by rw [mul_add, hsp.1, hsp.2.1, add_zero]
    rw [h1, mul_assoc, hE', hE, ← map_mul, GlobalTheory.LocWeil.PlaceIdem.eFin_mul_eFin _ (Ne.symm hv), map_zero, mul_zero]
  have hpr : q'.pr (q.e + cA D q.e) = 0 := by
    rw [← q'.pr_sec (q'.pr _), q'.sec_pr, h0, map_zero]
  ext a b
  rw [Matrix.map_apply]
  have h2 : mt V g a b = (mt V g - 1) a b + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) a b := by
    rw [Matrix.sub_apply, sub_add_cancel]
  rw [h2, map_add (f := _), ← hg a b, map_mul, hpr, zero_mul, zero_add]
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

theorem locHom_eq_one {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {Y : Type} [Fintype Y] [DecidableEq Y]
    (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (V : HSp D) (F : Frame k' V.rank Y) (g : GA D V)
    (hg : SuppAt q.e V g) (hv : q.v ≠ q'.v) : GlobalTheory.LevIdx.locHom q' V F g = 1 := by
  refine ((GlobalTheory.LevIdx.eq_locHom_iff q' V F g 1).1 ?_).symm
  rw [map_pr_eq_one q q' V g hg hv, Units.val_one, Matrix.mul_one, F.βγ]

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} {a : GeoAll W u}

end GlobalTheory.LevOnto
end

namespace GlobalTheory.LevOnto
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} {a : GeoAll W u}

end GlobalTheory.LevOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowStepRelation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenBridge.SuppLev


set_option maxHeartbeats 1000000 in
theorem bc_prV_eq_one_of_not (D : D7) (S : HSp D) (n : ℕ) (hn : S.rank = n) (κ : GA D S)
    (g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hg : GlobalTheory.AdForm.finM S hn κ = g.1) (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (w : HeightOneSpectrum (𝓞 D.host.F))
    (hw : ¬ P w) (hκ : κ ∈ GlobalTheory.FinPl.grpAt S P) : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) g = 1 := by
  subst hn
  have h1 : GlobalTheory.AdelicU.proj (Formalism.L2.Forms.sigD D) S.gram w κ = 1 :=
    ((GlobalTheory.FinPl.KOpen.mem_grpAt_iff S _ κ).1 hκ).2 w hw
  have hp := GlobalTheory.AdelicU.matHom_proj (Formalism.L2.Forms.sigD D) S.gram w κ
  have hE : Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) w) g =
      GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram w (GlobalTheory.AdelicU.proj _ S.gram w κ) := by
    ext i j
    have hij := congrFun (congrFun hg i) j
    have e1 : (GlobalTheory.StabConjIndex.toGL (Formalism.L2.Forms.sigD D) S.gram w (GlobalTheory.AdelicU.proj _ S.gram w κ)).val i j =
        GlobalTheory.StabConjIndex.swap w ((GlobalTheory.AdelicU.matHom (Fv D.host.F w) (Formalism.L2.Forms.sigD D) S.gram
          (GlobalTheory.AdelicU.proj (Formalism.L2.Forms.sigD D) S.gram w κ)).val i j) := rfl
    rw [e1, hp]
    show Formalism.UG.prV w (g.1 i j) = GlobalTheory.StabConjIndex.swap w (GlobalTheory.AdelicU.compFin _ _ w _)
    rw [← hij]
    exact GlobalTheory.FamTrace.prV_toEAf_eq_swap D w _
  rw [hE, h1, map_one]


set_option maxHeartbeats 1000000 in
theorem exists_mem_level_set (D : D7) (S : HSp D) (n : ℕ) (hn : S.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (K : StepLevel D.host.F D.host.E (sigD D) (S.gram.reindex (finCongr hn) (finCongr hn)) T f bad)
    (t : 𝓞 D.host.E) (ht : t ∣ (T : 𝓞 D.host.E))
    (hLb : ∀ x, x ∈ K.Lb ↔ ∀ j : Fin n, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E) ∧ (j.1 + 1 = n → t ∣ r))
    (L : GlobalTheory.FinPl.Lat S) (hfg : L.FG) (hL : ∀ x, x ∈ L ↔ ∀ j, ∃ r : 𝓞 D.host.E, x j = (r : D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (κ : GA D S) (hκ : κ ∈ GlobalTheory.FinPl.grpAt S P)
    (hP : ∀ v, P v → v ∉ bad ∧ (T : 𝓞 D.host.F) ∉ v.asIdeal ∧ GlobalTheory.FinPl.Moves S κ L L (· = v)) :
    ∃ x : K.U, x.1.1 = GlobalTheory.AdForm.finM S hn κ := by
  obtain ⟨g, hgU, hg⟩ : ∃ g ∈ Formalism.UG.UPts (sigD D) (S.gram.reindex (finCongr hn) (finCongr hn))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F), GlobalTheory.AdForm.finM S hn κ = g.1 := by
    obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D S n hn
    have hf := GlobalTheory.FinPl.SetCut.grpAt_le_GfC S _ hκ
    exact ⟨(e ⟨κ, hf⟩).1, (e ⟨κ, hf⟩).2, (he ⟨κ, hf⟩).symm⟩
  refine ⟨⟨g, (K.U_eq _).2 ⟨hgU, fun w => ?_⟩⟩, hg.symm⟩
  by_cases hw : P w
  · obtain ⟨hb, hT, hm⟩ := hP w hw
    subst hn
    have key : ∀ j i : Fin S.rank, ∃ r : 𝓞 D.host.E,
        (Pi.single j (T : D.host.E) : Fin S.rank → D.host.E) i = (r : D.host.E) ∧ t ∣ r := fun j i => by
      rw [Pi.single_apply]
      split_ifs
      · exact ⟨T, (map_natCast (algebraMap (𝓞 D.host.E) D.host.E) T).symm, ht⟩
      · exact ⟨0, rfl, dvd_zero _⟩
    have e := GlobalTheory.FamTrace.levelVL_eq_of_std (sigD D) (S.gram.reindex (finCongr rfl) (finCongr rfl)) (Lb := K.Lb) (Λ := L) hT
      (fun x hx j => let ⟨r, hr, _⟩ := (hLb x).1 hx j; ⟨r, hr⟩)
      (fun j => (hLb _).2 fun i => let ⟨r, hr, hd⟩ := key j i; ⟨r, hr, fun _ => hd⟩)
      (fun x hx => (hL x).1 hx) (fun j => (hL _).2 fun i => let ⟨r, hr, _⟩ := key j i; ⟨r, hr⟩)
    rw [K.Uloc_hyp w hb hT, e]
    exact GlobalTheory.FamTrace.bc_prV_mem_levelVL_of_moves D S _ rfl L L hfg (fun _ => Iff.rfl) κ g hg w hm
  · rw [bc_prV_eq_one_of_not D S n hn κ g hg P w hw hκ]
    exact one_mem _

end GlobalTheory.PenBridge.SuppLev


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopValueVanishingUniform
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopVal.Inj

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem exists_fin {D : D7} (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V) :
    ∃ g' : GA D V, g' ∈ GfC V ∧ finHom V g' = finHom V g ∧
      ∃ y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
        y ∈ Formalism.UG.UPts D.sp.cm.sig (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∧
        ∀ i j, (Formalism.UG.bc (swapAE D) (finHom V g')).1 i j = y.1 (finCongr hn i) (finCongr hn j) := by
  subst hn
  let z := (GlobalTheory.FinPartIso.finEquiv D.sp.cm.sig V.gram).symm (GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram g)
  have hz : GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram z.1 = GlobalTheory.AdelicU.projFin D.sp.cm.sig V.gram g :=
    (GlobalTheory.FinPartIso.finEquiv D.sp.cm.sig V.gram).apply_symm_apply _
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D V _ rfl
  refine ⟨z.1, z.2, congrArg Subtype.val hz, (e ⟨z.1, z.2⟩).1, (e ⟨z.1, z.2⟩).2, fun i j => ?_⟩
  rw [he]
  rfl

theorem eq_zero_of_models {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (h : R.models_jX) (t : T) (x : A.fam.amb.FR t)
    (hx : ∀ g, (R.HX t).e (R.jX t x) ((finHom D.sp.X').rangeRestrict g) = 0) : x = 0 := by
  have h1 : R.B.jR t x = 0 := by
    funext k
    obtain ⟨g, hg⟩ := (finHom D.sp.X').rangeRestrict_surjective k
    exact (congrFun (h t x) k).symm.trans ((congrArg ((R.HX t).e (R.jX t x)) hg.symm).trans (hx g))
  have h2 : Function.Injective (R.B.jR t) := GlobalTheory.PresBasic.extL_injective (R.B.R t).pres
  exact (injective_iff_map_eq_zero (R.B.jR t)).1 h2 x h1

theorem eq_zero_of_isRes {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : Col2.TC B X) (a : I.ι) (φ : Frm I a) τ (e : I.tup a = τ)
    (ok : (Formalism.L2.Col.mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel τ).Ok)
    (h : IsRes φ (0 : ((Formalism.L2.Col.mtildeKGSD (Pr := B.primes X) B.wts I.Ch I.sel τ).toCSD ok).Forms)) : φ = 0 := by
  subst e
  obtain ⟨ok', h⟩ := h
  exact (LinearEquiv.map_eq_zero_iff _).1 (eq_of_heq h)


set_option maxHeartbeats 2000000 in
theorem eq_zero_twArgs (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : G.Inst (w.st Z).toD7 L)
    (Gl : G.LatInst (w.st Z).toD7) (Kc : G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC)
    (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : Bl.RowsT K w Z Wt ex.p0) (a : R3.TwArgs ex t) :
    ∀ (s : a.x.T) (φ : Frm w.I (a.x.Y.tup s)), IsRes φ (0 : a.x.A3.A.fam.amb.FR s) → φ = 0 := by
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  have hT' : Y.tup = t.r.Y.tup := eq_of_heq htup
  intro s φ h
  have e : w.I.tup (Y.tup s) = s.1 :=
    (congrArg w.I.tup ((congrFun hT' s).trans (t.r.tup_ix s))).trans (R3.tup_ixOf w.I s)
  exact eq_zero_of_isRes w.I _ φ s.1 e _ h

theorem exists_hasMat {D : D7} (gP : Formalism.L2.Forms.gramP D = 1) (g : GA D D.sp.X') :
    ∃ g' y, GlobalTheory.Core.Rk.Top.HasMat g' y ∧ y ∈ Formalism.L2.Herm.UstdAf D.sp.cm (D.R.N D.R.m - 1) ∧
      (finHom D.sp.X').rangeRestrict g = (finHom D.sp.X').rangeRestrict g' := by
  obtain ⟨g', h1, h2, y, h3, h4⟩ := exists_fin _ _ (Formalism.L2.Forms.rankP D) g
  have h6 : y ∈ Formalism.UG.UPts _ (Formalism.L2.Forms.gramP D) _ := h3
  rw [gP] at h6
  exact ⟨g', y, ⟨h1, h4⟩, h6, Subtype.ext h2.symm⟩

theorem eq_zero_of_hasMat {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (h : R.models_jX) (gP : Formalism.L2.Forms.gramP D = 1)
    (t : T) (x : A.fam.amb.FR t)
    (hx : ∀ g y, GlobalTheory.Core.Rk.Top.HasMat g y → y ∈ Formalism.L2.Herm.UstdAf D.sp.cm (D.R.N D.R.m - 1) →
      (R.HX t).e (R.jX t x) ((finHom D.sp.X').rangeRestrict g) = 0) : x = 0 := by
  refine eq_zero_of_models R h t x fun g => ?_
  exact (exists_hasMat gP g).elim fun g' h1 => h1.elim fun y h2 =>
    (congrArg ((R.HX t).e (R.jX t x)) h2.2.2).trans (hx g' y h2.1 h2.2.1)


end GlobalTheory.TopVal.Inj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopValueWitness
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Col GlobalTheory.Mem.Col2 GlobalTheory.Core.Rk.Top GlobalTheory.TopVal

namespace GlobalTheory.TopVal

def DatVal {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {G : Type} [Group G] [Fintype G]
    {Pl0 T : Type} {A : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [aK : Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) A Ks) (tup : T → I.ι) : Prop :=
  ∃ c : Val B →ₛₗ[B.embLL] R.cX.W,
    (∀ (γ : GQ (I.rec7 l Z).sp.X') γE (g : GL (Fin (B.R.N B.R.m - 1)) B.fields.E), Bridge.IsRatMat (I.rec7 l Z).sp.X' γ γE →
      GlobalTheory.Mem.R3.MatEq (A := B.fields.E) γE g → ∀ v, c (rhoV B.fields.emb B.wts.sgTrue g v) = R.cX.ρ γ.1 (c v)) ∧
    ∀ (t : T) (φ : Frm I (tup t)) (x : A.fam.amb.FR t), IsRes φ x →
      ∀ (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') y, HasMat h y → IsUni B y →
        (R.HX t).e (R.jX t x) ((finHom (I.rec7 l Z).sp.X').rangeRestrict h) = c (val φ (latOf I (tup t) y))

theorem matEq_of_hasMat {D : D7} {h : GA D D.sp.X'} {y} (hm : HasMat h y) :
    GlobalTheory.Mem.R3.MatEq (R3.matIn D.sp.X' 1 ((finHom D.sp.X').rangeRestrict h)) y := by
  refine ⟨Formalism.L2.Forms.rankP D, fun i j i' j' hi hj => ?_⟩
  have e1 : finCongr (Formalism.L2.Forms.rankP D) i = i' := Fin.ext hi
  have e2 : finCongr (Formalism.L2.Forms.rankP D) j = j' := Fin.ext hj
  rw [← e1, ← e2, ← hm.2 i j]
  unfold R3.matIn
  rw [mul_one]
  rfl


set_option maxHeartbeats 1000000 in
theorem datVal_rows (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : Bl.RowsT K w Z Wt p0) (hs : t.r.z.Std) :
    DatVal w.I w.l Z (aK := t.r.z.alg) t.r.z.R.toRealDat t.r.Y.tup := by
  obtain ⟨c, h1, h2, -, -⟩ := hs.1
  have h3 := t.r.z.pins.char.base.models.jX
  have h4 := t.r.z.lev.beta.2
  refine ⟨c, fun γ γE g hr hm v => h1 γ γE g hr hm v, fun s => ?_⟩
  have h5 : w.I.tup (t.r.Y.tup s) = s.1 := (congrArg w.I.tup (t.r.tup_ix s)).trans (R3.tup_ixOf w.I s)
  have key : ∀ (a : w.I.ι), w.I.tup a = s.1 → ∀ (φ : Frm w.I a) (x : (R3.famT t).A.fam.amb.FR s), IsRes φ x →
      ∀ (h : GA (w.D Z) (w.D Z).sp.X') y, HasMat h y → IsUni B y →
        t.r.z.R.B.jR s x ((finHom (w.D Z).sp.X').rangeRestrict h) = c (val φ (latOf w.I a y)) := by
    intro a ha
    obtain ⟨s, hs'⟩ := s
    change w.I.tup a = s at ha
    subst ha
    rintro φ x ⟨ok, hx⟩ h y hm hu
    have hx' : ((by with_unfolding_all exact ((mtildeKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (w.I.tup a)).res ok φ :)) : (R3.famT t).A.fam.amb.FR ⟨w.I.tup a, hs'⟩) = x := by
      apply eq_of_heq
      exact (by with_unfolding_all exact (hx :))
    have hM := matEq_of_hasMat hm
    have e := h2 B.sp.cm ⟨w.I.tup a, hs'⟩ ⟨⟨ok⟩, φ⟩ ((finHom (w.D Z).sp.X').rangeRestrict h) ⟨y, hu⟩ (by rw [h4]; exact hM)
    have e2 := decoPt_mk B.sp.cm (B.R.N B.R.m - 1) ∅ (rowSG (B.primes w.px) w.I.sel (w.I.tup a)) ⟨y, hu⟩
    rw [← hx']
    refine Eq.trans ((by with_unfolding_all exact (e :))) (congrArg (fun d => c (val φ d)) e2)
  intro φ x hx h y hm hu
  exact (congrFun (h3 s x) _).trans (key _ h5 φ x hx h y hm hu)


set_option maxHeartbeats 1000000 in
theorem datVal_twArgs (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : G.Inst (w.st Z).toD7 L)
    (Gl : G.LatInst (w.st Z).toD7) (Kc : G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC)
    (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : Bl.RowsT K w Z Wt ex.p0) (a : R3.TwArgs ex t) (hs : t.r.z.Std) :
    DatVal w.I w.l Z (aK := a.x.alg) a.x.R.toRealDat a.x.Y.tup := by
  have h := datVal_rows K B f T w Z Wt ex.p0 t hs
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  have hT' : Y.tup = t.r.Y.tup := eq_of_heq htup
  rw [← hT'] at h
  obtain ⟨c, h1, h2⟩ := h
  refine ⟨(by with_unfolding_all exact (c :)), ?_, ?_⟩
  · exact (by with_unfolding_all exact (h1 :))
  · exact (by with_unfolding_all exact (h2 :))


end GlobalTheory.TopVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneFormExistsHeq
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Matrix

noncomputable section

namespace GlobalTheory.TopVal.OneForm

section Generic

variable {D : D7} {O : Obj D} {c : ℝ}


end Generic

section Rows

open GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.Bl


set_option maxHeartbeats 800000 in
theorem row_of_pack {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (x : R3.TwIn ex)
    {G : Type} [g : Group G] [fi : Fintype G] {Pl0 I0 T0 : Type} (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m)
    {C : Formalism.L2.Pj.CoreJ D} {al : Algebra C.Q.c.F D.what₂.LL} {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3}
    {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
    (pack : (⟨x.G, x.grp, x.fin, x.Pl0, x.I0, x.T, x.A3, x.core, x.alg, x.R, x.F, x.cG⟩ :
      Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : Formalism.L2.Pj.CoreJ D)
        (_ : Algebra C.Q.c.F D.what₂.LL) (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3),
        G0 R.Pg D.R.r ≃* G0g D.nd) = ⟨G, g, fi, Pl0, I0, T0, A3, C, al, R, F, cG⟩)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (hP : F.P1 = P) (hψ : HEq F.ψ1 ψ)
    (τ : T0 → D.what₂.Tup) (j : ∀ s, (Fin (rDim D A3.A P ψ s) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb (τ s))
    (hτ : HEq x.Y.tup τ) (hj : HEq x.Y.jA j) (s : x.T) (v : Fin (rDim D x.A3.A x.F.P1 x.F.ψ1 s) → D.what₂.LL) :
    ∃ (s' : T0) (v' : Fin (rDim D A3.A P ψ s') → D.what₂.LL), x.Y.tup s = τ s' ∧
      HEq (R3.rowForm x.A3.A x.F.P1 x.F.ψ1 s v) (R3.rowForm A3.A P ψ s' v') ∧ HEq (x.Y.jA s v) (j s' v') := by
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  subst hP
  cases hψ
  cases hτ
  cases hj
  exact ⟨s, v, rfl, HEq.rfl, HEq.rfl⟩


set_option maxHeartbeats 800000 in
theorem row_of_args {K : Ctx} {B : GlobalTheory.Mem.Base} {f : GlobalTheory.Mem.Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
    {t : RowsT K w Z Wt ex.p0} (a : R3.TwArgs ex t) (s : a.x.T)
    (v : Fin (rDim (w.st Z).toD7 a.x.A3.A a.x.F.P1 a.x.F.ψ1 s) → (w.st Z).toD7.what₂.LL) :
    ∃ (s' : R3.TupU w.I (R3.usedOf w.I T Wt))
      (v' : Fin (rDim (w.st Z).toD7 (R3.famT t).A (R3.lev1 w.I) (R3.chr1 w.I) s') → (w.st Z).toD7.what₂.LL),
      a.x.Y.tup s = t.r.Y.tup s' ∧
      HEq (R3.rowForm a.x.A3.A a.x.F.P1 a.x.F.ψ1 s v) (R3.rowForm (D := (w.st Z).toD7) (R3.famT t).A (R3.lev1 w.I) (R3.chr1 w.I) s' v') ∧
      HEq (a.x.Y.jA s v) (t.r.Y.jA s' v') :=
  row_of_pack a.x (R3.famT t) a.pack (R3.lev1 w.I) (R3.chr1 w.I) rfl HEq.rfl t.r.Y.tup t.r.Y.jA a.tup a.jA s v


set_option maxHeartbeats 800000 in
theorem rowForm_all (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (R3.Gc X.B px → X.B.LL)) (tr : R3.TrI X.B px) (s : R3.TupU I U) (a : I.ι) (h : s.1 = I.tup a)
    (v : Fin (rDim X.toD7 (R3.famR X I hX U Xg tr).A (R3.lev1 I) (R3.chr1 I) s) → X.toD7.what₂.LL) :
    ∃ v' : Fin (rDim X.toD7 (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a)) → X.toD7.what₂.LL,
      (∀ i i', Fin.val i = Fin.val i' → v' i = v i') ∧
      HEq (R3.rowForm (D := X.toD7) (R3.famR X I hX Set.univ Xg tr).A (R3.lev1 I) (R3.chr1 I) (tAll I a) v')
        (R3.rowForm (D := X.toD7) (R3.famR X I hX U Xg tr).A (R3.lev1 I) (R3.chr1 I) s v) := by
  obtain ⟨τ, hτ⟩ := s
  dsimp only at h
  subst h
  exact ⟨v, fun i i' e => congrArg v (Fin.ext e), HEq.rfl⟩


set_option maxHeartbeats 800000 in
theorem one_form_rows {K : Ctx} {B : GlobalTheory.Mem.Base} {f : GlobalTheory.Mem.Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
    {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} (rx : RXs t) (s : R3.TupU w.I (R3.usedOf w.I T Wt))
    (v : Fin (rDim (w.st Z).toD7 (R3.famT t).A (R3.lev1 w.I) (R3.chr1 w.I) s) → (w.st Z).toD7.what₂.LL) :
    ∃ φ : Frm w.I (t.r.Y.tup s),
      IsRes φ (R3.rowForm (D := (w.st Z).toD7) (R3.famT t).A (R3.lev1 w.I) (R3.chr1 w.I) s v) ∧
      ∀ u, RecVal (I := w.I) (l := w.l) (Z := Z) u (t.r.Y.tup s) φ (t.r.Y.jA s v) := by
  have hs : s.1 = w.I.tup (t.r.Y.tup s) :=
    (R3.tup_ixOf w.I s).symm.trans (congrArg w.I.tup (t.r.tup_ix s)).symm
  obtain ⟨v', hv, hf⟩ := rowForm_all (w.st Z) w.I t.hX _ t.r.z.Xg t.r.z.tr s (t.r.Y.tup s) hs v
  have hj : rx.all.jA (t.r.Y.tup s) v' = t.r.Y.jA s v := (rx.jA_use s).2 v' v hv
  obtain ⟨x, ⟨φ, hφ, hres, hx⟩, he⟩ := rx.crd (t.r.Y.tup s) v'
  subst hx
  refine ⟨φ, ⟨_, hres.trans hf⟩, fun u => ?_⟩
  rw [← hj, he]
  have key : ∀ (a : w.C.Tup) (φ : Frm w.I a) hφ,
      RecVal (I := w.I) (l := w.l) (Z := Z) u a φ (rx.e a (Df.toCx w.I t.hX a ⟨φ.1, hφ⟩)) := by
    intro a φ hφ
    refine ⟨fun h => ?_, fun p => rx.eMtTw u a _ p⟩
    subst h
    exact fun p => rx.eMt0 u _ p
  exact key _ φ hφ

end Rows

theorem one_form_congr {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : Col2.TC B X} {l : I.Laws} {Z : Col2.TC.Later B (I.cols l)}
    {a a' : (I.rec7 l Z).what₂.Tup} {V V' : Type} {x : V} {x' : V'} {G : (I.rec7 l Z).what₂.Amb a} {G' : (I.rec7 l Z).what₂.Amb a'}
    (ha : a = a') (hx : HEq x x') (hG : HEq G G') (h : ∃ φ : Frm I a', IsRes φ x' ∧ ∀ u, RecVal u a' φ G') :
    ∃ φ : Frm I a, IsRes φ x ∧ ∀ u, RecVal u a φ G := by
  subst ha
  cases hx
  cases hG
  exact h



end GlobalTheory.TopVal.OneForm

end
end
