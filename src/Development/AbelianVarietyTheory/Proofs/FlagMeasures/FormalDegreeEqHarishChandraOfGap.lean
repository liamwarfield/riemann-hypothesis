module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FinalClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSupportCompatible
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalNongenericBoundRecordFamily
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalLatticeClassesFiniteLocalOrbitsStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeEqHarishChandraOfGap
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeEqHarishChandraOfGap
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem dsig_eq_fdegHC_of_gap : ∀ (D : D7), Ties D → ∀ (τ : D.what₂.Tau) (h : ℝ),
    Formalism.QuantumDeterminants.IsHCParam (lamSH D.R (D.hc τ)) → Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamSH D.R (D.hc τ)) h →
    Formalism.MainNotions.GapDS.thrE (epsSH D.R) + 1 < h → D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) := by
  intro D hT τ h hlam hg hth
  have hth' : Formalism.MainNotions.GapDS.thrE (epsSH D.R) < h :=
    lt_trans (lt_add_of_pos_right _ zero_lt_one) hth
  obtain ⟨H, i1, i2, σ, hσ, -⟩ := ReciprocityTheory.ChartRestriction.DS.dsExistsG_closed _ (epsSH D.R) _ hlam h hg hth'
  have hpq := Formalism.MainNotions.S.Pv.DegI.minpq_pos D
  have hp : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf (epsSH D.R) := le_trans hpq (min_le_left _ _)
  have hq : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf (epsSH D.R) := le_trans hpq (min_le_right _ _)
  have htrue : ∃ a, epsSH D.R a = true := by
    unfold ReciprocityTheory.ChartRestriction.DS.pOf at hp
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hp)
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  have hfalse : ∃ a, epsSH D.R a = false := by
    unfold ReciprocityTheory.ChartRestriction.DS.qOf at hq
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  have hd := GlobalTheory.T.harishChandra_formalDegree_compactDual_large_gaps D.cd D.s.cdScale hT.cdScale_tie _ (epsSH D.R) _ h hlam htrue hfalse hg hth H σ hσ
  exact (hT.dsig_tie τ H σ _ hσ hd).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeEqHarishChandraOfGapStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegree_eq_harishChandra_of_gap : ∀ (D : D7), Ties D → ∀ (τ : D.what₂.Tau) (h : ℝ), Formalism.QuantumDeterminants.IsHCParam (lamSH D.R (D.hc τ)) → Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamSH D.R (D.hc τ)) h → Formalism.MainNotions.GapDS.thrE (epsSH D.R) + 1 < h → D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) :=
  GlobalTheory.dsig_eq_fdegHC_of_gap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabUMapEqOfRoots
noncomputable section

open Matrix Formalism.MainNotions.S
open scoped Classical

namespace GlobalTheory.LoopAct

variable {n m : ℕ}

def IsMatOn (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin m → Fin n → ℂ) (M : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ b, g *ᵥ f b = ∑ c, M c b • f c

theorem isMatOn_mul {g h : Matrix (Fin n) (Fin n) ℂ} {f : Fin m → Fin n → ℂ} {M₁ M₂ : Matrix (Fin m) (Fin m) ℂ}
    (hg : IsMatOn g f M₁) (hh : IsMatOn h f M₂) : IsMatOn (g * h) f (M₁ * M₂) := by
  intro b
  rw [← Matrix.mulVec_mulVec, hh b, Matrix.mulVec_sum]
  have e : ∀ c, g *ᵥ (M₂ c b • f c) = ∑ d, (M₂ c b * M₁ d c) • f d := by
    intro c
    rw [Matrix.mulVec_smul, hg c, Finset.smul_sum]
    exact Finset.sum_congr rfl fun d _ => smul_smul _ _ _
  rw [Finset.sum_congr rfl fun c _ => e c, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_smul, Matrix.mul_apply]
  congr 1
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem isMatOn_unique {g : Matrix (Fin n) (Fin n) ℂ} {f : Fin m → Fin n → ℂ} {M₁ M₂ : Matrix (Fin m) (Fin m) ℂ}
    (hf : LinearIndependent ℂ f) (hM : IsMatOn g f M₁) (hN : IsMatOn g f M₂) : M₁ = M₂ := by
  ext c b
  have h : ∑ d, (M₁ d b - M₂ d b) • f d = 0 := by
    simp_rw [sub_smul, Finset.sum_sub_distrib, ← hM b, ← hN b, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hf _ h c)

theorem isMatOn_conj {g P Pi : Matrix (Fin n) (Fin n) ℂ} {f : Fin m → Fin n → ℂ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hg : IsMatOn g (fun j => P *ᵥ f j) A) (hP : Pi * P = 1) : IsMatOn (Pi * g * P) f A := by
  intro b
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg b, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]

variable {N : ℕ}

theorem stabU_mul {Z a b : Matrix (Fin N) (Fin N) ℂ} (hZ : IsUnit Z.det) (ha : a ∈ GlobalTheory.LoopV.stabU Z)
    (hb : b ∈ GlobalTheory.LoopV.stabU Z) : a * b ∈ GlobalTheory.LoopV.stabU Z := by
  refine ⟨Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_mul ha.1 hb.1, ?_⟩
  have e : Z * (a * b) * Z⁻¹ = (Z * a * Z⁻¹) * (Z * b * Z⁻¹) := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hZ]
  rw [e]
  exact Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_mul ha.2 hb.2

theorem stabU_inv {Z a : Matrix (Fin N) (Fin N) ℂ} (hZ : IsUnit Z.det) (ha : a ∈ GlobalTheory.LoopV.stabU Z) :
    a⁻¹ ∈ GlobalTheory.LoopV.stabU Z := by
  refine ⟨(Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv ha.1).1, ?_⟩
  have hai := Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv ha.1
  have e : Z * a⁻¹ * Z⁻¹ = (Z * a * Z⁻¹)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hZ, Matrix.mul_assoc]
  rw [e]
  exact (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv ha.2).1

theorem stabU_map_eq_ofRoots {K : Type} [Field K] (ψ : K →+* ℂ) (p : Point K N) (x : Matrix (Fin N) (Fin N) ℂ)
    (hx : x ∈ GlobalTheory.LoopV.stabU ((ptMat p).map ψ)) :
    x = GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat p)) (fun q => x q.1.1 q.1.2) := by
  obtain ⟨σ, d, hd, hw⟩ := GlobalTheory.LoopV.Cell.ptMat_monomial p
  have hd' : ∀ i, ψ (d i) ≠ 0 := fun i => (map_ne_zero ψ).2 (hd i)
  have hw' : ∀ i j, (ptMat p).map ψ i j = if j = σ i then ψ (d i) else 0 := by
    intro i j; rw [Matrix.map_apply, hw]; split_ifs <;> simp
  ext a b
  unfold GlobalTheory.LoopV.ofRoots
  by_cases hr : (a, b) ∈ GlobalTheory.LoopV.roots (ptMat p)
  · rw [dite_eq_left hr]
  · rw [dite_eq_right hr]
    rcases lt_trichotomy a b with hab | rfl | hab
    · rw [if_neg hab.ne]
      have hσ : σ.symm a < σ.symm b := by
        rw [GlobalTheory.LoopV.Cell.mono_roots hd hw] at hr
        push_neg at hr
        rcases (hr hab).lt_or_eq with h | h
        · exact h
        · exact absurd (σ.symm.injective h) hab.ne
      have h0 := (hx.2 (σ.symm a) (σ.symm b)).1 hσ
      rw [GlobalTheory.LoopV.Cell.mono_conj hd' hw'] at h0
      simp only [Equiv.apply_symm_apply, mul_eq_zero, inv_eq_zero, hd', false_or, or_false] at h0
      exact h0
    · rw [if_pos rfl]; exact (hx.1 a a).2 rfl
    · rw [if_neg hab.ne']; exact (hx.1 a b).1 hab

end GlobalTheory.LoopAct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ValuationLtOneIffNormLtOnePadicCmCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ValuationLtOneIffNormLtOnePadicCmCompletion
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Filter Topology

namespace GlobalTheory.SlocVal

theorem tendsto_pow_map {A B : Type} [Ring A] [TopologicalSpace A] [Ring B] [TopologicalSpace B]
    (f : A →+* B) (hf : Continuous f) {x : A} (hx : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => f x ^ n) atTop (𝓝 0) := by
  have h := (hf.tendsto 0).comp hx
  rw [map_zero] at h
  simpa [Function.comp_def, map_pow] using h

theorem continuous_symm {A B : Type} [Field A] [TopologicalSpace A] [IsTopologicalRing A]
    [SigmaCompactSpace A] [Field B] [TopologicalSpace B] [IsTopologicalRing B] [BaireSpace B]
    [T2Space B] (e : A ≃+* B) (he : Continuous e) : Continuous e.symm := by
  have ho : IsOpenMap e :=
    AddMonoidHom.isOpenMap_of_sigmaCompact e.toAddEquiv.toAddMonoidHom e.surjective he
  exact e.toEquiv.continuous_symm_iff.2 ho

end GlobalTheory.SlocVal


open GlobalTheory.SlocVal in
theorem GlobalTheory.valuation_lt_one_iff_norm_lt_one_of_continuous : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (g : ℕ) [Fact g.Prime] (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (j : ℚ_[g] ≃+* s.w.adicCompletion L), Continuous i → Continuous j → ∀ z : s.v.adicCompletion (maximalRealSubfield L), Valued.v z < 1 ↔ ‖j.symm (i z)‖ < 1 := by
  intro L _ _ _ s g _ i j hi hj z
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion (maximalRealSubfield L) s.v
  have hj' : Continuous j.symm := continuous_symm j hj
  have hi' : Continuous i.symm := continuous_symm i hi
  have hφ : Continuous (i.trans j.symm) := hj'.comp hi
  have hψ : Continuous (i.trans j.symm).symm := hi'.comp hj
  have hz : Valued.v z < 1 ↔ ‖z‖ < 1 := (Valued.toNormedField.norm_lt_one_iff).symm
  rw [hz, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  constructor
  · intro h
    exact tendsto_pow_map (i.trans j.symm).toRingHom hφ h
  · intro h
    have := tendsto_pow_map (i.trans j.symm).symm.toRingHom hψ h
    simpa using this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ValuationLtOneIffNormLtOnePadicCmCompletionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_lt_one_iff_norm_lt_one_padic_cmCompletion : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (g : ℕ) [Fact g.Prime] (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (j : ℚ_[g] ≃+* s.w.adicCompletion L), Continuous i → Continuous j → ∀ z : s.v.adicCompletion (maximalRealSubfield L), Valued.v z < 1 ↔ ‖j.symm (i z)‖ < 1 := by
  first | exact @GlobalTheory.valuation_lt_one_iff_norm_lt_one_of_continuous | exact GlobalTheory.valuation_lt_one_iff_norm_lt_one_of_continuous | (intros; apply GlobalTheory.valuation_lt_one_iff_norm_lt_one_of_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordsNonGenericEstimatesChain
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordsNonGenericEstimatesChain
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna

namespace GlobalTheory

theorem closed_steps_gram_vectors : NondegenerateGramTuple := by
  intro D X
  have hn : 2 * D.R.rS + 2 ≤ X.B.I.n := by
    rw [X.n_eq]
    have h1 := D.R.rS_two
    have h2 := D.R.r_eq
    have h3 := D.R.k_ge
    omega
  have hH : ∀ i j, star (X.B.I.J j i) = X.B.I.J i j := fun i j => by
    have := congrFun (congrFun X.B.I.J_herm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  obtain ⟨X0, hX⟩ := exists_nondegenerate X.B.I.E X.B.I.n (2 * D.R.rS + 2) hn X.B.I.J hH X.B.I.J_det
  refine ⟨X0, ?_⟩
  have e : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE X.B.I.cm.sig X.B.I.J X0 =
      PI.NormGramAtOrigin.gram (starRingEnd _) X.B.I.J X0 := by
    ext a b; rfl
  rw [e]; exact hX

theorem closed_steps_equal_words :
    PN.NGChain ∧ StepClassG ∧ StepPointsG ∧ StepNormOneG ∧ TieOfCtx ∧ StepPinExists ∧
      StepTermVanishG ∧ Formalism.L2.SG.NGVanish.FormNGC ∧
      (Formalism.L2.SG.Pf.MainEqFam.StepFamG → StepLocGenPinnedG) := by
  have hPts : StepPointsG :=
    Formalism.L2.SG.Pf.MainEqPoints.stepPointsG_of_leaves Formalism.L2.SG.Closed.AvgCore_holds
      Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Closed.ChiTrivialC_holds
      Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds
      (fun D X Y u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')
  have hNorm : StepNormOneG :=
    Formalism.L2.SG.NGCut.LeadingMinorIntegrality.Gen.stepNormOneG_of_leaves Formalism.L2.SG.Closed.AvgCore_holds
      Formalism.L2.SG.Pf.ginfUnimod_holds Formalism.L2.SG.Pf.nLamNinf_holds Formalism.L2.SG.Closed.ChiTrivialC_holds
      Formalism.L2.SG.Pf.psiInfChar_holds Formalism.L2.SG.Pf.rClosedC_holds Formalism.L2.SG.Pf.roDiscreteC_holds
      Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds Formalism.L2.SG.NonRelPf.nonRelCharC_holds
      (fun D X Y u u' => Formalism.L2.SG.LeadingMinorsNonvanishing.atSomeAll_holds D X Y u u')
  have hLoc : ∀ D, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39 := fun D =>
    ((GlobalTheory.local_nongeneric_bound_record_family 39 le_rfl).2.1 D).1
  exact ⟨Formalism.FourierDecayAlt.P.norm_chain, Formalism.L2.SG.Pf.stepClassG_holds, hPts, hNorm,
    tieOfCtx_of closed_steps_gram_vectors, Formalism.L2.SG.NGPin.stepPinExists,
    Formalism.L2.SG.Pf.MainEqVanish.stepTermVanishG_of_form Formalism.L2.SG.Pf.formGC_holds,
    Formalism.L2.SG.Pf.formNGC_holds,
    fun hFam => Formalism.L2.SG.Pf.stepLocGenPinnedG_of_loc (Formalism.L2.SG.Pf.stepLocPinnedG_of_fam hLoc hFam)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordsNonGenericEstimatesChainStatement
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equalWords_nonGeneric_estimates_chain : PN.NGChain ∧ StepClassG ∧ StepPointsG ∧ StepNormOneG ∧ TieOfCtx ∧ StepPinExists ∧ StepTermVanishG ∧ Formalism.L2.SG.NGVanish.FormNGC ∧ (Formalism.L2.SG.Pf.MainEqFam.StepFamG → StepLocGenPinnedG) := by
  first | exact @GlobalTheory.closed_steps_equal_words | exact GlobalTheory.closed_steps_equal_words | (intros; apply GlobalTheory.closed_steps_equal_words <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InputsOfSubsetWidths
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem inputs_of_subset_widths : ∀ S S' : Set ℝ, S ⊆ S' → (AmpOn S' → AmpOn S) ∧ (SmallOn S' → SmallOn S) ∧ (CntOn S' → CntOn S) ∧ (CountBoundOn S' → CountBoundOn S) ∧ (TieOn S' → TieOn S) := by
  intro S S' hSS
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h Cg cb Cu cT CT hb hT
    obtain ⟨C, C2, Ch, h1, h2, h3⟩ := h Cg cb Cu cT CT hb hT
    refine ⟨C, C2, Ch, h1, h2, fun Cpr δ hδ => ?_⟩
    obtain ⟨thr, ht⟩ := h3 Cpr δ hδ
    exact ⟨thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT δ hb hT hδ
    obtain ⟨thr, ht⟩ := h Cg cb Cu cT CT δ hb hT hδ
    exact ⟨thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT
    obtain ⟨c3, cH, cS, c4, thr, ht⟩ := h Cg cb Cu cT CT
    exact ⟨c3, cH, cS, c4, thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT
    obtain ⟨c3, cH, thr, ht⟩ := h Cg cb Cu cT CT
    exact ⟨c3, cH, thr, fun C0 hC0 => ht C0 (hSS hC0)⟩
  · intro h Cg cb Cu cT CT
    obtain ⟨cV, thr, ht⟩ := h Cg cb Cu cT CT
    exact ⟨cV, thr, fun C0 hC0 => ht C0 (hSS hC0)⟩

end GlobalTheory.Core.Deg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteRationalIsometriesFixingFramesConjStabiliz
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteRationalIsometriesFixingFramesConjStabiliz
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.FixFin

section Img

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem img_mul (g g' : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) :
    LocNG.img (g * g') Λ = LocNG.img g (LocNG.img g' Λ) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨g' x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩

theorem img_one (Λ : Submodule M.L.O V) : LocNG.img (1 : V ≃ₗ[E] V) Λ = Λ := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro hv; exact ⟨v, hv, rfl⟩

theorem img_inv {g : V ≃ₗ[E] V} {Λ Λ' : Submodule M.L.O V} (h : LocNG.img g Λ = Λ') :
    LocNG.img g⁻¹ Λ' = Λ := by
  rw [← h, ← img_mul, inv_mul_cancel, img_one]

theorem mem_Aut {g : V ≃ₗ[E] V} {Λ : Submodule M.L.O V} : g ∈ LocNG.Aut Λ ↔ LocNG.img g Λ = Λ := by
  constructor
  · intro hg
    unfold LocNG.Aut at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact img_one Λ
    | mul x y _ _ hx hy => rw [img_mul, hy, hx]
    | inv x _ hx => exact img_inv hx
  · intro h; exact Subgroup.subset_closure h

theorem img_fg_span (g : V ≃ₗ[E] V) (L : Submodule M.L.O V)
    (h : L.FG ∧ Submodule.span E (L : Set V) = ⊤) :
    (LocNG.img g L).FG ∧ Submodule.span E (LocNG.img g L : Set V) = ⊤ := by
  refine ⟨h.1.map _, ?_⟩
  have e : (LocNG.img g L : Set V) = (g : V →ₗ[E] V) '' (L : Set V) := rfl
  rw [e, Submodule.span_image, h.2, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

end Img

variable {D : D7}

theorem localLattice_fg_span (Z : LocDat D) (Λ : LV D) (h : Submodule.IsFullLattice D.host.E Λ) (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG ∧ Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
  have hc : Submodule.IsFullLattice D.host.E (LatLoc.cL Λ) := by
    refine { toIsLattice := LatLoc.isLattice_map _ _ h.toIsLattice, span_eq_top := ?_ }
    change Submodule.span D.host.E ((LatLoc.cE D).toLinearMap '' (Λ : Set (VS D).V)) = ⊤
    rw [Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact (LatLoc.cE D).surjective
  have := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Λ) hc).2.1 p
  rw [LatLoc.localLattice_eq]
  exact this

private theorem isFullLattice_of_local_span {D : D7} (Z : LocDat D) (p : PlF D) (Λ : LV D)
    (hΛ : Submodule.IsLattice D.host.E Λ)
    (hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤) :
    Submodule.IsFullLattice D.host.E Λ := by
  let U := Submodule.span D.host.E (Λ : Set (VS D).V)
  let b := Module.finBasis D.host.E U
  let W := Submodule.span (D.s.atP p).Ep
    (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
  have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
    have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
    change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
    rw [map_sum, map_sum] at hx
    rw [← hx]
    exact W.sum_mem fun i _ => by
      rw [map_smul, baseChange_smul₂]
      exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
  have htop : W = ⊤ := by
    apply top_le_iff.mp
    rw [← hspan, lattice₂, Submodule.span_span_of_tower]
    refine Submodule.span_le.2 ?_
    rintro y ⟨x, hx, heq⟩
    rw [← heq]
    exact hW ⟨x, Submodule.subset_span hx⟩
  refine { toIsLattice := hΛ, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
  rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
  simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
    finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)


end GlobalTheory.Unfold.FixFin


set_option maxHeartbeats 1000000 in
open GlobalTheory.Unfold.FixFin in
theorem GlobalTheory.Unfold.FixFin.conj_aut_finite : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∀ a : ∀ p, ↥(FP p).UW0, {p | ((a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite → {h : ↥(FlagPairStabilizer F F') | ∀ p, (((a p)⁻¹ * φ h p * a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∈ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite := by
  intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀ a ha
  have hLG := LatLoc.lattices_local_global D Z
  obtain ⟨Λa, hΛa, hΛap⟩ := hLG.2 Λ₀ hΛ₀
    (fun p => LocNG.img ((a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (lattice₂ D Z.M p Λ₀))
    (fun p => img_fg_span _ _ (localLattice_fg_span Z Λ₀ hΛ₀ p))
    (ha.subset fun p hp hA => hp (mem_Aut.1 hA))
  obtain ⟨p⟩ := GlobalTheory.PhiEmbed.exists_place D
  have hΛaFull : Submodule.IsFullLattice D.host.E Λa := by
    apply isFullLattice_of_local_span Z p Λa hΛa
    rw [hΛap p]
    exact (img_fg_span _ _ (localLattice_fg_span Z Λ₀ hΛ₀ p)).2
  have H128 := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hR
  have H133 := (GlobalTheory.T.rationalLatticeClasses_finite_localOrbits D X Y u u' F F' w hw hG Z FP hB hR Λa hΛaFull).1
  refine (H133.preimage Subtype.val_injective.injOn).subset ?_
  intro h hh
  refine ⟨h.2, ?_⟩
  have hgl : Submodule.IsFullLattice D.host.E (Formalism.HermitianLatticesTheory.gmap (h : GV D) Λa) := by
    refine { toIsLattice := LatLoc.isLattice_map (h : GV D) Λa hΛa, span_eq_top := ?_ }
    change Submodule.span D.host.E (((h : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) '' (Λa : Set (VS D).V)) = ⊤
    rw [Submodule.span_image, hΛaFull.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact (h : GV D).surjective
  apply (hLG.1 _ _ hgl hΛaFull).2
  intro p
  rw [H128.2.2.1 (h : GV D) p _ Λa (hφ h p), hΛap p]
  have e := mem_Aut.1 (hh p)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, img_mul, img_mul] at e
  have e2 := congrArg (LocNG.img ((a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) e
  rwa [← img_mul, mul_inv_cancel, img_one] at e2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteRationalIsometriesFixingFramesConjStabilizStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_rationalIsometries_fixing_frames_conjStabilizer : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∀ a : ∀ p, ↥(FP p).UW0, {p | ((a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite → {h : ↥(FlagPairStabilizer F F') | ∀ p, (((a p)⁻¹ * φ h p * a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∈ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite := by
  first | exact @GlobalTheory.Unfold.FixFin.conj_aut_finite | exact GlobalTheory.Unfold.FixFin.conj_aut_finite | (intros; apply GlobalTheory.Unfold.FixFin.conj_aut_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteDoubleCosetsRationalLocalLatticeStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteDoubleCosetsRationalLocalLatticeStabilizer
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblCos

variable {D : D7}

theorem img_mul (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (a b : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (M p).L.O (Vp D p)) :
    LocNG.img (a * b) Λ = LocNG.img a (LocNG.img b Λ) := by
  ext x
  simp only [LocNG.img, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    LinearEquiv.mul_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem img_one (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (Λ : Submodule (M p).L.O (Vp D p)) : LocNG.img (1 : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) Λ = Λ := by
  ext x
  simp [LocNG.img]

theorem mem_Aut_iff (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (M p).L.O (Vp D p)) :
    g ∈ LocNG.Aut Λ ↔ LocNG.img g Λ = Λ := by
  constructor
  · intro hg

    let K : Subgroup (Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) :=
      { carrier := {a | LocNG.img a Λ = Λ}
        mul_mem' := fun {a b} ha hb => by
          have ha' : LocNG.img a Λ = Λ := ha
          have hb' : LocNG.img b Λ = Λ := hb
          show LocNG.img (a * b) Λ = Λ
          rw [img_mul p M, hb', ha']
        one_mem' := img_one p M Λ
        inv_mem' := fun {a} ha => by
          have ha' : LocNG.img a Λ = Λ := ha
          show LocNG.img a⁻¹ Λ = Λ
          calc LocNG.img a⁻¹ Λ = LocNG.img a⁻¹ (LocNG.img a Λ) := by rw [ha']
            _ = Λ := by rw [← img_mul p M, inv_mul_cancel, img_one p M] }
    exact (Subgroup.closure_le K).2 (fun a ha => ha) hg
  · intro h
    exact Subgroup.subset_closure h

theorem span_img (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (M p).L.O (Vp D p))
    (h : Submodule.span (D.s.atP p).Ep (Λ : Set (Vp D p)) = ⊤) :
    Submodule.span (D.s.atP p).Ep (LocNG.img g Λ : Set (Vp D p)) = ⊤ := by
  have himg : (LocNG.img g Λ : Set (Vp D p)) = (g : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p) '' (Λ : Set (Vp D p)) := by
    ext x
    simp [LocNG.img]
  rw [himg, Submodule.span_image, h, Submodule.map_top]
  exact LinearEquiv.range g

theorem img_key (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (c g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (A B C : Submodule (M p).L.O (Vp D p))
    (h1 : C = LocNG.img c B) (h2 : C = LocNG.img g A) : LocNG.img (c⁻¹ * g) A = B := by
  rw [img_mul p M, ← h2, h1, ← img_mul p M, inv_mul_cancel, img_one p M]

theorem img_key' (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (c s g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (A B C : Submodule (M p).L.O (Vp D p))
    (h1 : C = LocNG.img c B) (h2 : C = LocNG.img g A) (h3 : LocNG.img s A = B) :
    LocNG.img ((c * s)⁻¹ * g) A = A := by
  rw [mul_inv_rev, mul_assoc, img_mul p M, img_key p M c g A B C h1 h2, ← h3, ← img_mul p M,
    inv_mul_cancel, img_one p M]

private theorem latP_fg_and_span_eq_top (Z : LocDat D) (Λ : LV D) (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG ∧ Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
  haveI : Submodule.IsLattice D.host.E (GlobalTheory.Unfold.LatLoc.cL Λ) :=
    GlobalTheory.Unfold.LatLoc.isLattice_map (GlobalTheory.Unfold.LatLoc.cE D) Λ hΛ.toIsLattice
  have hc : Submodule.IsFullLattice D.host.E (GlobalTheory.Unfold.LatLoc.cL Λ) := by
    refine { span_eq_top := ?_ }
    change Submodule.span D.host.E ((GlobalTheory.Unfold.LatLoc.cE D).toLinearMap '' (Λ : Set (VS D).V)) = ⊤
    rw [← Submodule.map_span, hΛ.span_eq_top, Submodule.map_top, LinearEquiv.range]
  have h := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (GlobalTheory.Unfold.LatLoc.cL Λ) hc).2.1 p
  rw [GlobalTheory.Unfold.LatLoc.localLattice_eq]
  exact h

private theorem isFullLattice_of_local_span {D : D7} (Z : LocDat D) (p : PlF D) (Λ : LV D)
    (hΛ : Submodule.IsLattice D.host.E Λ)
    (hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤) :
    Submodule.IsFullLattice D.host.E Λ := by
  let U := Submodule.span D.host.E (Λ : Set (VS D).V)
  let b := Module.finBasis D.host.E U
  let W := Submodule.span (D.s.atP p).Ep
    (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
  have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
    have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
    change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
    rw [map_sum, map_sum] at hx
    rw [← hx]
    exact W.sum_mem fun i _ => by
      rw [map_smul, baseChange_smul₂]
      exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
  have htop : W = ⊤ := by
    apply top_le_iff.mp
    rw [← hspan, lattice₂, Submodule.span_span_of_tower]
    refine Submodule.span_le.2 ?_
    rintro y ⟨x, hx, heq⟩
    rw [← heq]
    exact hW ⟨x, Submodule.subset_span hx⟩
  refine { toIsLattice := hΛ, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
  rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
  simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
    finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)


private theorem gmap_inv_gmap_flag_measures (γ : GV D) (L : LV D) :
    Formalism.HermitianLatticesTheory.gmap γ⁻¹ (Formalism.HermitianLatticesTheory.gmap γ L) = L := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have hz' : (γ⁻¹ : GV D) (γ z) = z := γ.symm_apply_apply z
    rw [hz']
    exact hz
  · intro hx
    refine ⟨γ x, ⟨x, hx, rfl⟩, ?_⟩
    exact γ.symm_apply_apply x

end GlobalTheory.DblCos


open GlobalTheory.DblCos in
set_option maxHeartbeats 5000000 in
theorem GlobalTheory.DblCos.finite_double_cosets : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∃ S : Finset (∀ p, ↥(FP p).UW0), (∀ s ∈ S, {p | ((s p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite) ∧ ∀ g : ∀ p, ↥(FP p).UW0, {p | ((g p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite → ∃ s ∈ S, ∃ h : ↥(FlagPairStabilizer F F'), ∃ k : ∀ p, ↥(FP p).UW0, (∀ p, ((k p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∈ LocNG.Aut (lattice₂ D Z.M p Λ₀)) ∧ g = φ h * s * k := by
  intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀
  obtain ⟨-, -, hLat, -⟩ := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hR
  obtain ⟨-, Slat, hSlat⟩ := GlobalTheory.T.rationalLatticeClasses_finite_localOrbits D X Y u u' F F' w hw hG Z FP hB hR Λ₀ hΛ₀
  obtain ⟨hcmp, hglue⟩ := GlobalTheory.T.hermitianLattice_local_global_principle D Z

  let fam : LV D → ∀ p, ↥(FP p).UW0 := fun Λs p =>
    if hc : (∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λs) ∧
        lattice₂ D Z.M p Λs ≠ lattice₂ D Z.M p Λ₀ then ⟨hc.1.choose, hc.1.choose_spec.1⟩ else 1
  have fam_one : ∀ Λs p, lattice₂ D Z.M p Λs = lattice₂ D Z.M p Λ₀ → fam Λs p = 1 := by
    intro Λs p he
    simp only [fam]
    rw [dite_eq_right]
    exact fun hc => hc.2 he
  have fam_spec : ∀ Λs p, (∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λs) →
      LocNG.img ((fam Λs p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (lattice₂ D Z.M p Λ₀) =
        lattice₂ D Z.M p Λs := by
    intro Λs p hex
    by_cases he : lattice₂ D Z.M p Λs = lattice₂ D Z.M p Λ₀
    · rw [fam_one Λs p he, he]
      exact img_one p Z.M _
    · have hc : (∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λs) ∧
          lattice₂ D Z.M p Λs ≠ lattice₂ D Z.M p Λ₀ := ⟨hex, he⟩
      simp only [fam, dif_pos hc]
      exact hc.1.choose_spec.2
  refine ⟨(Slat.filter (fun Λs => Submodule.IsFullLattice D.host.E Λs)).image fam, ?_, ?_⟩
  ·
    intro s hs
    obtain ⟨Λs, hmem, rfl⟩ := Finset.mem_image.1 hs
    have hL : Submodule.IsFullLattice D.host.E Λs := (Finset.mem_filter.1 hmem).2
    apply (hcmp Λs Λ₀ hL hΛ₀).1.subset
    intro p hp
    by_contra he
    apply hp
    rw [fam_one Λs p (not_not.1 he)]
    exact (mem_Aut_iff p Z.M _ _).2 (img_one p Z.M _)
  · intro g hg

    obtain ⟨Λ, hΛ, hΛp⟩ := hglue Λ₀ hΛ₀
      (fun p => LocNG.img ((g p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (lattice₂ D Z.M p Λ₀))
      (fun p => by
        obtain ⟨hfg, hspan⟩ := latP_fg_and_span_eq_top Z Λ₀ hΛ₀ p
        exact ⟨hfg.map _, span_img p Z.M _ _ hspan⟩)
      (by
        apply hg.subset
        intro p hp hmem
        exact hp ((mem_Aut_iff p Z.M _ _).1 hmem))
    obtain ⟨Λs, hΛsS, γ, hγ, hγΛ⟩ := hSlat Λ hΛ (fun p => ⟨_, (g p).2, (hΛp p).symm⟩)
    have hΛfull : Submodule.IsFullLattice D.host.E Λ := by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      let p : PlF D := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.F)⟩
      apply isFullLattice_of_local_span Z p Λ hΛ
      rw [hΛp p]
      exact span_img p Z.M _ _ (latP_fg_and_span_eq_top Z Λ₀ hΛ₀ p).2
    have hΛsL : Submodule.IsFullLattice D.host.E Λs := by
      have hfull : Submodule.IsFullLattice D.host.E (Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ) := by
        refine { toIsLattice := GlobalTheory.RatLocMove.isLattice_gmap' γ⁻¹ Λ hΛ, span_eq_top := ?_ }
        change Submodule.span D.host.E (((γ⁻¹ : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) '' (Λ : Set (VS D).V)) = ⊤
        rw [Submodule.span_image, hΛfull.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
        exact (γ⁻¹ : GV D).surjective
      rwa [← hγΛ, gmap_inv_gmap_flag_measures] at hfull
    let hh : ↥(FlagPairStabilizer F F') := ⟨γ, (mem_H0sub F F' γ).2 hγ⟩
    let s := fam Λs
    refine ⟨s, Finset.mem_image.2 ⟨Λs, Finset.mem_filter.2 ⟨hΛsS, hΛsL⟩, rfl⟩, hh,
      s⁻¹ * (φ hh)⁻¹ * g, ?_, by group⟩
    intro p

    have hC1 : lattice₂ D Z.M p Λ = LocNG.img ((φ hh p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)
        (lattice₂ D Z.M p Λs) := by
      rw [← hγΛ]
      exact hLat γ p _ Λs (hφ hh p)
    have hC2 := hΛp p
    have hex : ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λs :=
      ⟨(((φ hh p)⁻¹ * g p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p), ((φ hh p)⁻¹ * g p).2, by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, img_mul p Z.M, ← hC2, hC1, ← img_mul p Z.M,
          inv_mul_cancel, img_one p Z.M]⟩
    have hs := fam_spec Λs p hex
    rw [mem_Aut_iff p Z.M]
    have key := img_key' p Z.M _ _ _ _ _ _ hC1 hC2 hs
    simpa [Pi.mul_apply, Pi.inv_apply, mul_inv_rev, mul_assoc] using key
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteDoubleCosetsRationalLocalLatticeStabilizerStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_doubleCosets_rational_localLatticeStabilizers : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∃ S : Finset (∀ p, ↥(FP p).UW0), (∀ s ∈ S, {p | ((s p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite) ∧ ∀ g : ∀ p, ↥(FP p).UW0, {p | ((g p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite → ∃ s ∈ S, ∃ h : ↥(FlagPairStabilizer F F'), ∃ k : ∀ p, ↥(FP p).UW0, (∀ p, ((k p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∈ LocNG.Aut (lattice₂ D Z.M p Λ₀)) ∧ g = φ h * s * k := by
  first
  | exact GlobalTheory.DblCos.finite_double_cosets
  | intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀
    exact GlobalTheory.DblCos.finite_double_cosets D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀.toIsLattice
end
end
