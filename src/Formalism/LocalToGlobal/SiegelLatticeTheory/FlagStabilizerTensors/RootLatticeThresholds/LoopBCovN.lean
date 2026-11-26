module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RMeasP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TheoremSRecursion
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootCoordinatesIndex
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsFin

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf.LoopBCovN

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def eN (D : D7) : ℝ := (D.R.rS : ℝ) ^ 2 + (D.R.rS : ℝ) / 2

def CovNFormula : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), 0 < θ →
    LoopTerm.covN (Y := Y) C u = (θ * (2 * D.host.v) ^ eN D) ^ Fintype.card D.what₂.Tau

theorem rdE_ge_one (D : D7) : 1 ≤ 2 * D.host.v := by
  unfold Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
  have hd : (1 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| := by
    have h0 : NumberField.discr D.host.E ≠ 0 := NumberField.discr_ne_zero D.host.E
    have h1 : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs h0
    exact_mod_cast h1
  have h2 : (1 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| ^ (1 / (Module.finrank ℚ D.host.E : ℝ)) :=
    Real.one_le_rpow hd (by positivity)
  linarith

theorem covWinN_of (hF : CovNFormula) {D : D7} {X : HidaSetting D} {Y : Full X} (C : Choice X 1) (large₂ : SizeData₂ D) {C1 : ℝ}
    (hC1 : 0 ≤ C1) (hup : eN D * Real.log (2 * D.host.v) ≤ C1 * (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b)
    (u u' : D.what₂.Word) : LoopTerm.CovWinN (Y := Y) C large₂ C1 u u' := by
  have hbpos : 0 < large₂.sc.b := by
    unfold Scale.b
    exact Real.exp_pos _
  have hv := rdE_ge_one D
  have hv0 : 0 < 2 * D.host.v := by linarith
  have heN : 0 ≤ eN D := by
    unfold eN
    positivity
  have hy1 : 1 ≤ (2 * D.host.v) ^ eN D := Real.one_le_rpow hv heN
  have hlog0 : 0 ≤ eN D * Real.log (2 * D.host.v) := mul_nonneg heN (Real.log_nonneg hv)
  have hyexp : (2 * D.host.v) ^ eN D = Real.exp (Real.log (2 * D.host.v) * eN D) :=
    Real.rpow_def_of_pos hv0 _
  have hcov : ∀ w, LoopTerm.covN (Y := Y) C w = ((2 * D.host.v) ^ eN D) ^ Fintype.card D.what₂.Tau := by
    intro w
    rw [hF D X Y 1 C w one_pos, one_mul]
  have hx : (LoopTerm.covN (Y := Y) C u * LoopTerm.covN (Y := Y) C u') ^ (1 / (2 * (Fintype.card D.what₂.Tau : ℝ))) = 1 ∨
      (LoopTerm.covN (Y := Y) C u * LoopTerm.covN (Y := Y) C u') ^ (1 / (2 * (Fintype.card D.what₂.Tau : ℝ))) =
        (2 * D.host.v) ^ eN D := by
    rw [hcov u, hcov u', ← pow_add, ← two_mul]
    rcases Nat.eq_zero_or_pos (Fintype.card D.what₂.Tau) with h0 | hpos
    · left
      simp [h0]
    · right
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      have hN : (0 : ℝ) < Fintype.card D.what₂.Tau := by exact_mod_cast hpos
      have h2 : ((2 * Fintype.card D.what₂.Tau : ℕ) : ℝ) * (1 / (2 * (Fintype.card D.what₂.Tau : ℝ))) = 1 := by
        push_cast
        field_simp
      rw [h2, Real.rpow_one]
  have hxb : ∀ z : ℝ, (z = 1 ∨ z = (2 * D.host.v) ^ eN D) → 1 ≤ z ∧ z ≤ (2 * D.host.v) ^ eN D := by
    rintro z (rfl | rfl) <;> exact ⟨by linarith, by linarith⟩
  obtain ⟨hx1, hx2⟩ := hxb _ hx
  have hup' : Real.log (2 * D.host.v) * eN D ≤ Real.log large₂.sc.b * (C1 * (D.R.m : ℝ) ^ 2) := by linarith
  unfold LoopTerm.CovWinN normWin
  refine ⟨le_trans ?_ hx1, le_trans hx2 ?_⟩
  · rw [Real.rpow_def_of_pos hbpos]
    have hneg : Real.log large₂.sc.b * -(C1 * (D.R.m : ℝ) ^ 2) ≤ 0 := by nlinarith
    exact Real.exp_le_one_iff.mpr hneg
  · rw [hyexp, Real.rpow_def_of_pos hbpos]
    exact Real.exp_le_exp.mpr hup'

theorem log_rd_le {D : D7} (large₂ : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt large₂) :
    Real.log (2 * D.host.v) ≤ Real.log large₂.sc.b / 72 := by
  obtain ⟨-, -, -, -, hT, hC, hQ, -⟩ := hS
  obtain ⟨-, -, -, -, -, -, hr1, hr2⟩ := hQ
  have h2v : 2 * D.host.v = D.host.rdE := by unfold Formalism.BasicNotions.Host.v; ring
  rw [h2v]
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have hd : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have ht : (1 : ℝ) ≤ D.R.t := hT.1
  have hqd : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
    have h1 : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hcond : D.host.rdE ≤ Formalism.MainNotions.szCond large₂ := by
    unfold Formalism.MainNotions.szCond
    calc D.host.rdE ≤ (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) := hr2
      _ ≤ (D.host.QS : ℝ) / 2 * ((D.host.q : ℝ) * D.host.d) := by gcongr
      _ ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by
        have h0 : (0 : ℝ) ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := by positivity
        nlinarith
  have hc1 : (1 : ℝ) ≤ Formalism.MainNotions.szCond large₂ := le_trans hr1 hcond
  have hb0 : 0 < large₂.sc.b := lt_of_lt_of_le (by norm_num) (Formalism.MainNotions.S.two_le_scb large₂)
  have h36 : Formalism.MainNotions.szCond large₂ ^ 36 ≤ Real.sqrt large₂.sc.b := by
    have : Formalism.MainNotions.szCond large₂ ^ 36 ≤ Formalism.MainNotions.szCond large₂ ^ 36 * (D.R.t : ℝ) ^ 150 := by
      have : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ ht
      nlinarith [pow_pos (lt_of_lt_of_le one_pos hc1) 36]
    exact this.trans hC
  have hl := Real.log_le_log (pow_pos (lt_of_lt_of_le one_pos hc1) 36) h36
  rw [Real.log_pow, Real.log_sqrt hb0.le] at hl
  have hl2 := Real.log_le_log (lt_of_lt_of_le one_pos hr1) hcond
  push_cast at hl
  linarith

theorem eN_le (D : D7) : eN D ≤ (D.R.m : ℝ) ^ 2 / 2 := by
  unfold eN
  have h : (D.R.rS : ℝ) ≤ (D.R.m : ℝ) / 2 := by
    have : 2 * D.R.rS ≤ D.R.m := by unfold Formalism.BasicNotions.Ranks.rS; omega
    have : (2 * D.R.rS : ℝ) ≤ D.R.m := by exact_mod_cast this
    linarith
  have h0 : (0 : ℝ) ≤ D.R.rS := by positivity
  have hm : (1 : ℝ) ≤ D.R.m := by have := D.R.two_le_m; exact_mod_cast (by omega : 1 ≤ D.R.m)
  nlinarith

theorem covWinN_sizes (hF : CovNFormula) {D : D7} {X : HidaSetting D} {Y : Full X} (C : Choice X 1) (large₂ : SizeData₂ D)
    (hS : Formalism.MainNotions.SizesAt large₂) {C1 : ℝ} (hC1 : 1 / 144 ≤ C1) (u u' : D.what₂.Word) :
    LoopTerm.CovWinN (Y := Y) C large₂ C1 u u' := by
  have hv := rdE_ge_one D
  have hl0 : 0 ≤ Real.log (2 * D.host.v) := Real.log_nonneg hv
  have hl := log_rd_le large₂ hS
  have he := eN_le D
  have hb : 0 ≤ Real.log large₂.sc.b := by linarith
  have hm : 0 ≤ (D.R.m : ℝ) ^ 2 := by positivity
  refine covWinN_of hF C large₂ (by linarith) ?_ u u'
  calc eN D * Real.log (2 * D.host.v) ≤ ((D.R.m : ℝ) ^ 2 / 2) * (Real.log large₂.sc.b / 72) :=
        mul_le_mul he hl hl0 (by positivity)
    _ = 1 / 144 * (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b := by ring
    _ ≤ C1 * (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b := by
        apply mul_le_mul_of_nonneg_right _ hb
        exact mul_le_mul_of_nonneg_right hC1 hm

theorem covN_pos (hF : CovNFormula) {D : D7} {X : HidaSetting D} {Y : Full X} {θ : ℝ} (hθ : 0 < θ) (C : Choice X θ)
    (u u' : D.what₂.Word) : 0 < LoopTerm.covN (Y := Y) C u * LoopTerm.covN (Y := Y) C u' := by
  rw [hF D X Y θ C u hθ, hF D X Y θ C u' hθ]
  have h1 := rdE_ge_one D
  have h2 : 0 < θ * (2 * D.host.v) ^ eN D := mul_pos hθ (Real.rpow_pos_of_pos (by linarith) _)
  exact mul_pos (pow_pos h2 _) (pow_pos h2 _)

end Formalism.L2.SG.Pf.LoopBCovN
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBTheta
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.LoopBTheta

theorem normWin_one {D : D7} (large₂ : SizeData₂ D) {C1 : ℝ} (hC1 : 0 ≤ C1) : normWin D large₂ C1 1 := by
  have hL : 0 ≤ large₂.sc.L := by
    show 0 ≤ large₂.sc.x ^ large₂.sc.eps
    exact le_of_lt (Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _)
  have hb : (1 : ℝ) ≤ large₂.sc.b := by
    show (1 : ℝ) ≤ Real.exp large₂.sc.L
    exact Real.one_le_exp hL
  have hc : 0 ≤ C1 * (D.R.m : ℝ) ^ 2 := mul_nonneg hC1 (sq_nonneg _)
  refine ⟨?_, ?_⟩
  · exact Real.rpow_le_one_of_one_le_of_nonpos hb (neg_nonpos.mpr hc)
  · exact Real.one_le_rpow hb hc

end Formalism.L2.SG.Pf.LoopBTheta
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ThmBChain
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Pf.BDat Formalism.L2.SG.Pf.BDatR Formalism.L2.SG.ThmBUseR
open scoped ENNReal

namespace Formalism.L2.SG.Pf.ThmBChain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem theoremB_uniform_rotated (h : Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform) : JointNormBoundRotatedUniform := by
  exact h

end Formalism.L2.SG.Pf.ThmBChain
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXHolds
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.FinXP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_Gflag {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} (n m : ℕ)
    (F : FlagG S r (n : E)) (F' : FlagG S r (m : E)) : star (Gflag F F') = Gflag F F' := by
  unfold Gflag
  simp only [star_sub, star_mul', star_star, star_natCast]
  ring

theorem greal_holds {D : D7} {X : HidaSetting D} (Y : Full X) : ∀ u u' (t : RT Y u u'), t.G ∈ D.host.F := by
  intro u u' t
  rw [← Formalism.BasicNotions.Examples₂.conj_eq_self_iff D.host, ← Formalism.BasicNotions.Examples₂.star_eq_conj D.host]
  exact star_Gflag _ _ _ _


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in
theorem phLoc_int_of_gap {D : D7} (X : HidaSetting D) (hg : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (v : InfinitePlace X.B.I.F) (d : ℝ) :
    Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) d) (Formalism.REAL.muG (X.B.I.ε v)) := by
  have h := Formalism.L2.SG.WuDecayPf.coef_integrable_of_weighted X
    (Formalism.L2.SG.Pf.WuDec.coefWeighted_of_gap X Formalism.L2.SG.Closed.CoefWeightedLoc_holds hg) v
  have hs : Integrable (fun g => star (Formalism.L2.SG.WuDecayPf.coefV X v g)) (Formalism.REAL.muG (X.B.I.ε v)) :=
    h.mono (continuous_star.comp_aestronglyMeasurable h.1) (ae_of_all _ fun g => le_of_eq (norm_star _))
  exact hs.const_mul (d : ℂ)


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in
theorem finX_holds (hWu : Formalism.L2.SG.Pf.WuDecayOfGap) (hRF : Formalism.L2.SG.RowsDef.RowsFinDim) (hFL : Formalism.L2.SG.Pf.FinLeviC)
    (hK : IotaKer) :
    Formalism.L2.SG.PoincareAmplitudeLowerBounds.FinXC := by
  intro D T hg
  obtain ⟨hWD, hph⟩ := hWu D hg T.X
  have hK2 := Formalism.L2.SG.Closed.level_subgroup_properties T.X
  have hfold : ∀ u, Formalism.L2.SG.WuDecay.FoldOK T.X u T.Y.hK := fun u =>
    Formalism.L2.SG.Closed.FoldOKC_holds hFL D T.X T.Y u hK2 hWD
  exact finX_of_neat T.Y (fun u => Formalism.L2.SG.Pf.neatKu_full D T.X T.Y u)
    (fun u => Formalism.L2.SG.Closed.InHHC_holds D T.X T.Y u hph (hfold u))
    (Formalism.L2.SG.Pf.RowDictPf.finiteDimensional_HHX_of_hypotheses T.X hRF Formalism.L2.SG.Pf.RowDictPf.schur_orthogonality_discrete_series
      (fun v => phLoc_int_of_gap T.X hg v _))
    (fun u u' t => fibFin_holds D T.X T.Y u u' t)
    (fun u u' s₁ s₂ s₁' s₂' h1 h2 h3 h4 => pairIndep_of hK D T.X T.Y u u' s₁ s₂ s₁' s₂' h1 h2 h3 h4)
    (greal_holds T.Y) Formalism.L2.SG.Closed.VolPosC_holds

end Formalism.L2.SG.Pf.FinXP

end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.QuotientSpan
noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.QuotientSpan

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (v : InfinitePlace X.B.I.F) {lam : ℂ} (hl : lam ≠ 0)
  {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ} {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ}
  (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi)

abbrev eV (a : Fin D.R.rS) : Fin X.B.I.n → ℂ := rv X.B.I v (X.eR a)

include hT in
theorem Q_e (a : Fin D.R.rS) :
    Q *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 = lam ^ (D.R.rS - a.val) • eV v a :=
  (hT.2.2.2 a a rfl).1

include hT hl in
theorem Qi_e (a : Fin D.R.rS) :
    Qi *ᵥ eV v a = (lam ^ (D.R.rS - a.val))⁻¹ • Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 := by
  have h := congrArg (fun x => Qi *ᵥ x) (Q_e v hT a)
  simp only [Matrix.mulVec_mulVec, hT.1, Matrix.one_mulVec, Matrix.mulVec_smul] at h
  rw [h, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl), one_smul]

include hT hl in
theorem Qi_spanLt (a : ℕ) (x : Fin X.B.I.n → ℂ) (hx : x ∈ spanLt (eV (X := X) v) a) (i : Fin (2 * D.R.rS + D.R.k + 1))
    (hi : a ≤ i.val) : (Qi *ᵥ x) i = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨b, hb, rfl⟩ := hx'
    rw [Qi_e v hl hT, Pi.smul_apply, Pi.single_apply, if_neg, smul_zero]
    intro h
    have := congrArg Fin.val h
    simp only [Formalism.QuantumDeterminants.eI] at this
    simp only [Set.mem_setOf_eq] at hb
    omega
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, Pi.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [Matrix.mulVec_smul, Pi.smul_apply, hx, smul_zero]

include hT in
theorem Q_spanLt (a : ℕ) (ha : a ≤ D.R.rS) (w : Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (hw : ∀ i : Fin (2 * D.R.rS + D.R.k + 1), a ≤ i.val → w i = 0) : Q *ᵥ w ∈ spanLt (eV (X := X) v) a := by
  have hw' : w = ∑ i, w i • Pi.single i (1 : ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hw', Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : a ≤ i.val
  · rw [hw i hi, zero_smul, Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  · have hir : i.val < D.R.rS := by omega
    have e : i = Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨i.val, hir⟩ := Fin.ext rfl
    rw [Matrix.mulVec_smul, e, Q_e v hT]
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i.val, hir⟩, ?_, rfl⟩))
    simp only [Set.mem_setOf_eq]
    omega

include hT hl in
theorem hJ_e (a : Fin D.R.rS) (y : Fin X.B.I.n → ℂ) :
    hJ (X.B.I.ε v) (eV v a) y = star ((lam ^ (D.R.rS - a.val))⁻¹) * (Qi *ᵥ y) (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) := by
  obtain ⟨_, hQQi, hH, _⟩ := hT
  have he : eV v a = (lam ^ (D.R.rS - a.val))⁻¹ • (Q *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1) := by
    rw [Q_e v ⟨‹_›, hQQi, hH, ‹_›⟩, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl), one_smul]
  have hy : y = Q *ᵥ (Qi *ᵥ y) := by rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
  conv_lhs => rw [he, hy]
  unfold hJ
  rw [star_smul, smul_dotProduct, ← Formalism.L2.SG.Pf.LTL.star_dot_conjT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH,
    Pi.star_single, star_one, single_dotProduct, one_mul, Formalism.L2.SG.RootCoordinatesIndex.hpk_eI, smul_eq_mul]


include hT hl in
theorem inN_iff (z : Fin X.B.I.n → ℂ) (hz : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS (Qi *ᵥ z))
    (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) (hg : gᴴ * Formalism.REAL.Jm (X.B.I.ε v) * g = Formalism.REAL.Jm (X.B.I.ε v)) :
    InN (X.B.I.ε v) (eV v) z g ↔ Qi * g * Q ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS := by
  have hQiQ := hT.1
  have hQQi := hT.2.1
  have hH := hT.2.2.1
  have hstar_ne : ∀ a : Fin D.R.rS, star ((lam ^ (D.R.rS - a.val))⁻¹) ≠ 0 := fun a =>
    star_ne_zero.2 (inv_ne_zero (pow_ne_zero _ (hl)))
  have hcol : ∀ (M : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) i j,
      M i j = (M *ᵥ Pi.single j 1) i := fun M i j => by rw [Matrix.mulVec_single_one]; rfl
  constructor
  · rintro ⟨⟨hIe, hIz⟩, hperp⟩
    refine ⟨?_, fun a i hai => ?_, fun i j hj1 hj2 hi => ?_⟩
    ·
      show (Qi * g * Q)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (Qi * g * Q) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
      have hQiQ' : (Qi)ᴴ * (Q)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQQi, Matrix.conjTranspose_one]
      rw [← hH]
      calc (Qi * g * Q)ᴴ * ((Q)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q) * (Qi * g * Q)
          = (Q)ᴴ * (gᴴ * ((Qi)ᴴ * (Q)ᴴ) * Formalism.REAL.Jm (X.B.I.ε v) * ((Q * Qi) * g)) *
              Q := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hQiQ', hQQi, Matrix.mul_one, Matrix.one_mul, hg]
    ·
      rw [hcol (Qi * g * Q) i (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a)]
      have h1 : (Qi * g * Q) *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 =
          Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 +
            lam ^ (D.R.rS - a.val) • (Qi *ᵥ ((g - 1) *ᵥ eV v a)) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Q_e v hT, Matrix.mulVec_smul, Matrix.mulVec_smul,
          Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Qi_e v hl hT, smul_sub, smul_smul,
          mul_inv_cancel₀ (pow_ne_zero _ (hl)), one_smul]
        abel
      rw [h1, Pi.add_apply, Pi.smul_apply, Qi_spanLt v hl hT a.val _ (hIe a) i hai, smul_zero, add_zero, Pi.single_apply]
    ·
      rw [hcol (Qi * g * Q) i j]
      have horth : ∀ b : Fin D.R.rS, hJ (X.B.I.ε v) (eV v b) (Q *ᵥ Pi.single j 1) = 0 := by
        intro b
        rw [hJ_e v hl hT, Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec, Pi.single_apply, if_neg, mul_zero]
        intro h
        have := congrArg Fin.val h
        simp only [Formalism.QuantumDeterminants.esI] at this
        have := b.isLt
        omega
      have h1 : (Qi * g * Q) *ᵥ Pi.single j 1 =
          Pi.single j 1 + Qi *ᵥ ((g - 1) *ᵥ (Q *ᵥ Pi.single j 1)) := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
        simp only [Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec, Matrix.mul_assoc]
        abel
      rw [h1, Pi.add_apply, Qi_spanLt v hl hT D.R.rS _ (hperp _ horth) i hi, add_zero, Pi.single_apply]
  · rintro ⟨_, hce, hcw⟩
    have hg' : g = Q * (Qi * g * Q) * Qi := by
      simp only [← Matrix.mul_assoc]
      rw [hQQi, Matrix.one_mul, Matrix.mul_assoc, hQQi, Matrix.mul_one]
    set m := Qi * g * Q with hm
    have key : ∀ x, (g - 1) *ᵥ x = Q *ᵥ ((m - 1) *ᵥ (Qi *ᵥ x)) := by
      intro x
      conv_lhs => rw [hg']
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]

    have hmW : ∀ x : Fin (2 * D.R.rS + D.R.k + 1) → ℂ, (∀ a, x (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) = 0) →
        ∀ i : Fin (2 * D.R.rS + D.R.k + 1), D.R.rS ≤ i.val → ((m - 1) *ᵥ x) i = 0 := by
      intro x hx i hi
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj1 : j.val < D.R.rS
      · have e : j = Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨j.val, hj1⟩ := Fin.ext rfl
        have := hce ⟨j.val, hj1⟩ i (by simp only; omega)
        rw [Matrix.sub_apply, e, this, Matrix.one_apply, sub_self, zero_mul]
      · by_cases hj2 : j.val ≤ D.R.rS + D.R.k
        · rw [Matrix.sub_apply, hcw i j (by omega) hj2 hi, Matrix.one_apply, sub_self, zero_mul]
        · have hjr : 2 * D.R.rS + D.R.k - j.val < D.R.rS := by have := j.isLt; omega
          have e : j = Formalism.QuantumDeterminants.esI D.R.k D.R.rS ⟨2 * D.R.rS + D.R.k - j.val, hjr⟩ := by
            ext; simp only [Formalism.QuantumDeterminants.esI]; have := j.isLt; omega
          rw [e, hx, mul_zero]
    refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
    · rw [key, Qi_e v hl hT, Matrix.mulVec_smul, Matrix.mulVec_smul]
      refine Submodule.smul_mem _ _ (Q_spanLt v hT a.val a.isLt.le _ fun i hi => ?_)
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, ← hcol m i (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a), hce a i hi,
        Pi.single_apply, sub_self]
    · rw [key]
      refine Q_spanLt v hT D.R.rS le_rfl _ (hmW _ (fun a => hz _ (Or.inr ?_)))
      simp only [Formalism.QuantumDeterminants.esI]
      have := a.isLt
      omega
    · rw [key]
      refine Q_spanLt v hT D.R.rS le_rfl _ (hmW _ fun a => ?_)
      have h1 := hy a
      rw [hJ_e v hl hT] at h1
      exact (mul_eq_zero.1 h1).resolve_left (hstar_ne a)

theorem inN_conj {n r' : ℕ} {ε : Fin n → Bool} {e : Fin r' → Fin n → ℂ} {z : Fin n → ℂ}
    {g hh : Matrix (Fin n) (Fin n) ℂ} (hhU : hhᴴ * Formalism.REAL.Jm ε * hh = Formalism.REAL.Jm ε) (hu : IsUnit hh.det)
    (he : ∀ a, hh *ᵥ e a = e a) (hz : hh *ᵥ z = z) (hg : InN ε e z g) : InN ε e z (hh⁻¹ * g * hh) := by
  have hie : ∀ a, hh⁻¹ *ᵥ e a = e a := fun a => by
    conv_lhs => rw [← he a]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have hiz : hh⁻¹ *ᵥ z = z := by
    conv_lhs => rw [← hz]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have hspan : ∀ k (x : Fin n → ℂ), x ∈ spanLt e k → hh⁻¹ *ᵥ x ∈ spanLt e k := by
    intro k x hx
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨b, hb, rfl⟩ := hx'
      rw [hie]
      exact Submodule.subset_span ⟨b, hb, rfl⟩
    | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx
  have key : ∀ x, (hh⁻¹ * g * hh - 1) *ᵥ x = hh⁻¹ *ᵥ ((g - 1) *ᵥ (hh *ᵥ x)) := by
    intro x
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have horth : ∀ y, (∀ a, hJ ε (e a) y = 0) → ∀ a, hJ ε (e a) (hh *ᵥ y) = 0 := by
    intro y hy a
    have e1 : hJ ε (e a) (hh *ᵥ y) = hJ ε (hh *ᵥ e a) (hh *ᵥ y) := by rw [he]
    rw [e1]
    unfold hJ
    rw [← Formalism.L2.SG.HermitianMatrixIdentities.star_dot_conjT' hh, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hhU]
    exact hy a
  obtain ⟨⟨hIe, hIz⟩, hperp⟩ := hg
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key, he]; exact hspan _ _ (hIe a)
  · rw [key, hz]; exact hspan _ _ hIz
  · rw [key]; exact hspan _ _ (hperp _ (horth y hy))

end Formalism.L2.SG.QuotientSpan

end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsEtAlg
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsES
noncomputable section

open MonoidAlgebra

namespace Formalism.L2.SG.Pf.AllRowsES

open Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsGA Formalism.L2.SG.Pf.AllRowsFin
  Formalism.L2.SG.Pf.AllRowsRhoX

variable {D : D7}

abbrev CV (D : D7) : Type := ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)

def Ea (a : CV D) : MonoidAlgebra ℂ (G0g D.nd) :=
  haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun γ : G0g D.nd =>
    ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv)

theorem Ea_coeff (a : CV D) (γ : G0g D.nd) :
    (Ea a).coeff γ = haveI : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) := by
  simp [Ea, MonoidAlgebra.coeff_ofCoeff]

open Classical in
theorem ES_eq (S : Set (Tup2 D)) : ES S = ∑ a ∈ Finset.univ.filter (fun a : CV D => tupOf a ∈ S), Ea a := by
  apply MonoidAlgebra.ext
  ext γ
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.sum_filter]
  unfold ES
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  rw [finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · rw [Ea_coeff]
  · rfl

theorem monicOf_inj {g : ℕ} [Fact g.Prime] {N : ℕ} {a b : Fin N → ZMod g}
    (h : Formalism.CyclotomicNorms.monicOf a = Formalism.CyclotomicNorms.monicOf b) : a = b := by
  funext i
  rw [← Formalism.L2.SG.Pf.RowDictPf.coeff_monicOf a i, ← Formalism.L2.SG.Pf.RowDictPf.coeff_monicOf b i, h]

open Classical in
theorem Ea_mul (a b : CV D) : Ea a * Ea b = if a = b then Ea a else 0 := by
  have : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  apply MonoidAlgebra.ext
  ext γ
  rw [coeff_mul_fin]
  simp only [Ea_coeff]
  have key : ∑ δ : G0g D.nd, (∏ kv : (Σ k : Fin 2, D.nd.PlG k),
        (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (δ kv)) *
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (b kv))).coeff ((δ⁻¹ * γ) kv) =
      ∏ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))) *
        (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (b kv)))).coeff (γ kv) := by
    simp only [coeff_mul_fin]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [← Finset.prod_mul_distrib]
    rfl
  rw [key]
  split_ifs with hab
  · subst hab
    rw [Ea_coeff]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [D.ntypes.eSer_idem]
  · obtain ⟨kv, hkv⟩ : ∃ kv, a kv ≠ b kv := by
      by_contra h
      push Not at h
      exact hab (funext h)
    have h0 : (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))) * (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (b kv))) = 0 :=
      D.ntypes.eSer_orth kv.1 _ _ fun h => hkv (monicOf_inj h)
    rw [Finset.prod_eq_zero (Finset.mem_univ kv) (by rw [h0]; simp)]
    simp


open Classical in
theorem ES_idem (S : Set (Tup2 D)) : ES S * ES S = ES S := by
  rw [ES_eq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  simp only [Ea_mul]
  rw [Finset.sum_eq_single a (fun b _ hb => if_neg (Ne.symm hb)) (fun h => absurd ha h), if_pos rfl]

theorem ES_central (S : Set (Tup2 D)) (y : MonoidAlgebra ℂ (G0g D.nd)) : ES S * y = y * ES S :=
  central_of_class _ (ES_conj S) y

theorem ES_selfadj (S : Set (Tup2 D)) : conjA (ES S) = ES S :=
  selfadj_of_central_idem _ (ES_idem S) (ES_central S)

end Formalism.L2.SG.Pf.AllRowsES
end
end

noncomputable section

open MonoidAlgebra MeasureTheory

namespace Formalism.L2.SG.Pf.AllRowsEtAlg

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsGA
  Formalism.L2.SG.Pf.AllRowsFin Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.Pf.AllRowsES Formalism.L2.SG.Pf.unitaryCongruence

variable {D : D7} {X : HidaSetting D} (hS : Function.Surjective (rhoX X))
include hS

def Ehat : MonoidAlgebra ℂ (G0g D.nd) := MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm (hat hS X.B.e))

theorem Ehat_coeff (γ : G0g D.nd) : (Ehat hS).coeff γ = hat hS X.B.e γ := by
  simp [Ehat, MonoidAlgebra.coeff_ofCoeff]

theorem Ehat_idem : Ehat hS * Ehat hS = Ehat hS := by
  apply MonoidAlgebra.ext
  ext γ
  rw [coeff_mul_fin]
  simp only [Ehat_coeff hS]
  exact hat_e_idem hS γ

theorem hat_inv {f : X.B.I.Gf → ℂ} (hf : BiInv X f) (hsa : ∀ x, f x⁻¹ = star (f x)) (γ : G0g D.nd) :
    hat hS f γ⁻¹ = star (hat hS f γ) := by
  have h1 : f ((sec hS γ⁻¹ : KSub X.B.I) : X.B.I.Gf) = f (((sec hS γ)⁻¹ : KSub X.B.I) : X.B.I.Gf) := by
    rw [val_hat hS hf, val_hat hS hf, rho_sec, map_inv, rho_sec]
  have hcoe : (((sec hS γ)⁻¹ : KSub X.B.I) : X.B.I.Gf) = ((sec hS γ : KSub X.B.I) : X.B.I.Gf)⁻¹ := rfl
  unfold hat
  rw [h1, hcoe, hsa, star_mul', Complex.star_def, Complex.conj_ofReal]

theorem Ehat_selfadj : conjA (Ehat hS) = Ehat hS := by
  apply MonoidAlgebra.ext
  ext γ
  rw [conjA_coeff, Ehat_coeff hS, Ehat_coeff hS, hat_inv hS (biInv_e X) X.B.e_adm.2.2.1 γ, star_star]

theorem hat_eT' (S : Set (Tup2 D)) (γ : G0g D.nd) : hat hS (eT X S) γ = (Ehat hS * ES S).coeff γ := by
  rw [hat_eT hS S γ, coeff_mul_fin]
  simp only [Ehat_coeff hS]

theorem prod_idem (S : Set (Tup2 D)) : (Ehat hS * ES S) * (Ehat hS * ES S) = Ehat hS * ES S := by
  rw [mul_assoc, ES_central S (Ehat hS * ES S), mul_assoc, ← mul_assoc (Ehat hS) (Ehat hS), Ehat_idem hS,
    ES_idem]

theorem prod_selfadj (S : Set (Tup2 D)) : conjA (Ehat hS * ES S) = Ehat hS * ES S := by
  rw [conjA_mul, ES_selfadj, Ehat_selfadj hS, ES_central]

theorem eT_idem (S : Set (Tup2 D)) : X.B.I.convF X.B.μf (eT X S) (eT X S) = eT X S := by
  apply hat_inj hS (biInv_conv hS (biInv_eT X S) (biInv_eT X S)) (biInv_eT X S)
  intro γ
  rw [conv_hat hS (biInv_eT X S) (biInv_eT X S) γ]
  simp only [hat_eT' hS S]
  rw [← coeff_mul_fin, prod_idem hS S]

theorem eT_inv (S : Set (Tup2 D)) (x : X.B.I.Gf) : eT X S x⁻¹ = star (eT X S x) := by
  by_cases hx : x ∈ X.B.I.Kset
  · have key : eT X S x = hat hS (eT X S) (rhoX X ⟨x, hx⟩) / (V X : ℂ) := val_hat hS (biInv_eT X S) ⟨x, hx⟩
    have k1 : eT X S x⁻¹ = hat hS (eT X S) (rhoX X ⟨x, hx⟩)⁻¹ / (V X : ℂ) := by
      have := val_hat hS (biInv_eT X S) (⟨x, hx⟩ : KSub X.B.I)⁻¹
      rwa [map_inv] at this
    have hc : ∀ γ, (Ehat hS * ES S).coeff γ⁻¹ = star ((Ehat hS * ES S).coeff γ) := by
      intro γ
      conv_lhs => rw [← prod_selfadj hS S]
      rw [conjA_coeff, inv_inv]
    rw [k1, key, hat_eT' hS S, hat_eT' hS S, hc, star_div₀, Complex.star_def, Complex.conj_ofReal]
  · have hx' : x⁻¹ ∉ X.B.I.Kset := fun h => hx (by simpa using K_inv X.B.I h)
    rw [eT_of_not_mem X S hx, eT_of_not_mem X S hx', star_zero]

section Pos

open scoped ComplexOrder


omit hS in
theorem posType_of (I : AutInst) (μ : Measure I.Gf) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    {f : I.Gf → ℂ} (hc : Continuous f) {C : Set I.Gf} (hC : IsCompact C) (hCo : IsOpen C)
    (hsupp : ∀ x, f x ≠ 0 → x ∈ C) (hconv : I.convF μ f f = f) (hsa : ∀ x, f x⁻¹ = star (f x)) :
    I.IsPosType f := by
  intro m x c
  have hsub : ∀ i j, f ((x i)⁻¹ * x j) = ∫ z, star (f (z⁻¹ * x i)) * f (z⁻¹ * x j) ∂μ := by
    intro i j
    conv_lhs => rw [← hconv]
    have := integral_mul_left_eq_self (μ := μ) (fun y => f y * f (y⁻¹ * ((x i)⁻¹ * x j))) (x i)⁻¹
    show ∫ y, f y * f (y⁻¹ * ((x i)⁻¹ * x j)) ∂μ = _
    rw [← this]
    congr 1
    funext z
    rw [← hsa (z⁻¹ * x i)]
    congr 1 <;> congr 1 <;> group
  have hint : ∀ i j, Integrable (fun z => star (f (z⁻¹ * x i)) * f (z⁻¹ * x j)) μ := by
    intro i j
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hc.comp (continuous_inv.mul continuous_const)).star).mul
        (hc.comp (continuous_inv.mul continuous_const))
    · refine HasCompactSupport.intro
        (IsCompact.image (f := fun y : I.Gf => x j * y⁻¹) hC (continuous_const.mul continuous_inv)) ?_
      intro z hz
      have h0 : f (z⁻¹ * x j) = 0 := by
        by_contra h
        apply hz
        exact ⟨z⁻¹ * x j, hsupp _ h, by group⟩
      rw [h0, mul_zero]
  have hF : ∀ z, ((Complex.normSq (∑ j, c j * f (z⁻¹ * x j)) : ℝ) : ℂ) =
      ∑ i, ∑ j, star (c i) * c j * (star (f (z⁻¹ * x i)) * f (z⁻¹ * x j)) := by
    intro z
    rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def, star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul']
    ring
  have key : ∫ z, ((Complex.normSq (∑ j, c j * f (z⁻¹ * x j)) : ℝ) : ℂ) ∂μ =
      ∑ i, ∑ j, star (c i) * c j * f ((x i)⁻¹ * x j) := by
    simp_rw [hF]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hint i j).const_mul _))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, hsub]
  rw [← key, integral_complex_ofReal]
  exact Complex.zero_le_real.2 (integral_nonneg fun z => Complex.normSq_nonneg _)

end Pos

theorem eT_pos (S : Set (Tup2 D)) : X.B.I.IsPosType (eT X S) := by
  exact posType_of X.B.I X.B.μf (isLocallyConstant_eT X S).continuous (PI.WAU.Cpt.isCompact_Kset X.B.I)
    (PI.WAU.kset_open X.B.I) (fun x hx => by_contra fun h => hx (eT_of_not_mem X S h)) (eT_idem hS S)
    (eT_inv hS S)

theorem etAlg_of (S : Set (Tup2 D)) : EtAlg X S :=
  ⟨eT_idem hS S, eT_inv hS S, eT_pos hS S⟩

end Formalism.L2.SG.Pf.AllRowsEtAlg
end
end
