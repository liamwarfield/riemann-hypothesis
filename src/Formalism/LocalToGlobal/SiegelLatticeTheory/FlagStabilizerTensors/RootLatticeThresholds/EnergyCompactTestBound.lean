module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierXJointAt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvHoldsGen
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MSTypP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GridsRichITc

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPinNormSt
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPinNorm
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.Pf.Carrier.JointPinNorm

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointPf
  Formalism.L2.SG.Pf.Carrier.JointQuot Formalism.L2.SG.Pf.Carrier.EnergyFinal Formalism.L2.SG.Pf.Carrier.EnergyPlace
  Formalism.L2.SG.Pf.Carrier.JointPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Bessel

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def qDiag (q : (Fin r → ℂ) × ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.diagonal (Fin.snoc (α := fun _ => ℂ) q.1 q.2)

def OrbDirac : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r),
    γ ∈ Formalism.FourierDecayAlt.B.GV k r → ∀ F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp),
      Formalism.FourierDecayAlt.D.orbJ D γ (Measure.dirac (Matrix.of.symm (1 : Formalism.FourierDecayAlt.B.Mat k r))) F = Formalism.FourierDecayAlt.B.JF D F γ

def HSsgs : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (p : Formalism.FourierDecayAlt.B.SS k r), D.inSS p → ∀ g : Formalism.FourierDecayAlt.B.Mat k r,
      ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF D F (Formalism.FourierDecayAlt.B.sgs p g))‖ = ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF D F g)‖

def CosetOf : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r),
    γ ∈ Formalism.FourierDecayAlt.B.GV k r → ∀ q ∈ Formalism.FourierDecayAlt.JF.QDom k r D.z D.z', Formalism.QuantumDeterminants.Zhat k r D.z D.z' γ = qDiag q →
      ∃ p, D.inSS p ∧ γ = Formalism.FourierDecayAlt.B.sgs p (Formalism.FourierDecayAlt.B.gq D q)

def RelDiag : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r) (d : Fin (r + 1) → ℂ),
    γ ∈ Formalism.FourierDecayAlt.B.GV k r → (∀ a, d a ≠ 0) → Formalism.QuantumDeterminants.Zhat k r D.z D.z' γ = Matrix.diagonal d →
      Formalism.FourierDecayAlt.C6.IsRelevant D γ

end Bessel

section BesselPf

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem star_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mat k r) :
    star (psi k r z c g) = (psi k r z c g)⁻¹ := by
  unfold psi
  rw [← Complex.exp_neg, Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

theorem norm_xiTau (D : RealPlaceData k r Wp Wq) (p : SS k r) : ‖xiTau D (1, 1) p‖ = 1 := by
  unfold xiTau
  rw [Complex.norm_exp]
  simp

theorem orbIntegrand_eq [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq) (γ : Mat k r) (F : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) :
    Formalism.FourierDecayAlt.D.orbIntegrand D γ F p =
      (psi k r D.z cStd (Matrix.of p.1.2) * star (psi k r D.z' cStd (Matrix.of p.2.2))) •
        ((D.π (Matrix.of p.1.1)).comp
          ((F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1)).comp
            (D.π' (Matrix.of p.2.1)⁻¹))) := by
  unfold Formalism.FourierDecayAlt.D.orbIntegrand
  rw [Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.xiTau_eq, star_psi]
  rfl

theorem hs_left [FiniteDimensional ℂ Wq] (A : Wp →L[ℂ] Wp) (hA : ∀ v, ‖A v‖ = ‖v‖) (X : Wq →L[ℂ] Wp) :
    ‖hsVec (A.comp X)‖ = ‖hsVec X‖ := by
  simp only [hsVec, PiLp.norm_eq_of_L2, ContinuousLinearMap.comp_apply, hA]

theorem hs_right [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (U : Wq →L[ℂ] Wq) (hU : ∀ v, ‖U v‖ = ‖v‖)
    (X : Wq →L[ℂ] Wp) : ‖hsVec (X.comp U)‖ = ‖hsVec X‖ := by
  let li : Wq →ₗᵢ[ℂ] Wq := ⟨U.toLinearMap, hU⟩
  let e : Wq ≃ₗᵢ[ℂ] Wq := li.toLinearIsometryEquiv rfl
  have h := Formalism.L2.SG.RealObj.InfCut.hsb_indep ((stdOrthonormalBasis ℂ Wq).map e) (stdOrthonormalBasis ℂ Wq) X
  simp only [OrthonormalBasis.map_apply] at h
  simp only [hsVec, PiLp.norm_eq_of_L2, ContinuousLinearMap.comp_apply]
  congr 1

theorem hs_smul [FiniteDimensional ℂ Wq] (c : ℂ) (hc : ‖c‖ = 1) (X : Wq →L[ℂ] Wp) :
    ‖hsVec (c • X)‖ = ‖hsVec X‖ := by
  simp only [hsVec, PiLp.norm_eq_of_L2, ContinuousLinearMap.smul_apply, norm_smul, hc, one_mul]

theorem hSsgs_holds : HSsgs := by
  intro k r Wp Wq _ _ _ _ _ _ D F p hp g
  have hj := Formalism.FourierDecayAlt.P.OrbitalIntegralIdentities.jf_equiv D F p hp g
  unfold Formalism.FourierDecayAlt.B.rho at hj
  have hh : Matrix.of p.1.1 ∈ UWset k r D.z := hp.1
  have hh' : (Matrix.of p.2.1)⁻¹ ∈ UWset k r D.z' := Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hp.2.2.1
  calc ‖hsVec (JF D F (sgs p g))‖
        = ‖hsVec ((D.π (Matrix.of p.1.1)).comp ((JF D F (sgs p g)).comp (D.π' (Matrix.of p.2.1)⁻¹)))‖ := by
          rw [hs_left _ (D.π_unitary _ hh), hs_right _ (D.π'_unitary _ hh')]
    _ = ‖hsVec ((xiTau D (1, 1) p)⁻¹ • JF D F g)‖ := by rw [hj]
    _ = ‖hsVec (JF D F g)‖ := hs_smul _ (by rw [norm_inv, norm_xiTau, inv_one]) _

theorem orbDirac_holds : OrbDirac := by
  intro k r Wp Wq _ _ _ _ _ D γ hγ F
  have hu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hγ
  have hinv : γ⁻¹ * γ = 1 := by
    first
    | exact Matrix.nonsing_inv_mul γ ((Matrix.isUnit_iff_isUnit_det _).1 hu)
    | exact Matrix.nonsing_inv_mul γ hu
  have hact : ∀ p, Formalism.FourierDecayAlt.C6.actR γ (Matrix.of (Matrix.of.symm (1 : Mat k r))) p = p := by
    intro p
    simp only [Formalism.FourierDecayAlt.C6.actR, Equiv.apply_symm_apply, Matrix.mul_one, Matrix.one_mul, hinv]
    rfl
  have hnc1 : Formalism.FourierDecayAlt.D.IsNormCut D γ (Measure.dirac (Matrix.of.symm (1 : Mat k r))) (fun _ => (1 : ℝ)) :=
    ⟨measurable_const, fun _ => zero_le_one, fun p _ => by simp⟩
  have hJF : JF D F γ = ∫ p, Formalism.FourierDecayAlt.D.orbIntegrand D γ F p ∂D.μSS := by
    have h := orbIntegrand_eq D γ F
    simp only [h]
    rfl
  unfold Formalism.FourierDecayAlt.D.orbJ
  split_ifs with h
  · obtain ⟨hnc, -⟩ := h.choose_spec
    rw [hJF]
    apply integral_congr_ae
    filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS D] with p hp
    have h1 := hnc.2.2 p hp
    rw [integral_dirac, hact] at h1
    rw [h1]
    exact one_smul ℝ _
  · rw [hJF]
    symm
    apply integral_undef
    intro hi
    exact h ⟨fun _ => 1, hnc1, by simpa using hi⟩

theorem dmin_diag (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (x : Fin (r + 1) → ℂ)
    (hZ : Formalism.QuantumDeterminants.Zhat k r z z' γ = Matrix.diagonal x) (l : Fin (r + 2)) :
    Dmin k r z z' γ l = ∏ i : Fin l, x (Fin.castLE (Nat.le_of_lt_succ l.isLt) i) := by
  unfold Dmin
  rw [hZ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
  rfl

theorem prod_castLE_succ (x : Fin (r + 1) → ℂ) (m : ℕ) (hm : m + 1 ≤ r + 1) :
    ∏ i : Fin (m + 1), x (Fin.castLE hm i) =
      (∏ i : Fin m, x (Fin.castLE (by omega) i)) * x ⟨m, by omega⟩ := by
  rw [Fin.prod_univ_castSucc]
  rfl

theorem prod_castLE_ne (x : Fin (r + 1) → ℂ) (hx : ∀ a, x a ≠ 0) (m : ℕ) (hm : m ≤ r + 1) :
    ∏ i : Fin m, x (Fin.castLE hm i) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => hx _

theorem cosetOf_holds : CosetOf := by
  intro k r Wp Wq _ _ _ _ D γ hγ q hq hZ
  set x : Fin (r + 1) → ℂ := Fin.snoc (α := fun _ => ℂ) q.1 q.2 with hxdef
  have hT := mul_pos D.T_pos D.T'_pos
  have hq2 : q.2 ≠ 0 := by
    intro h; have := hq.2; rw [h, map_zero] at this; exact absurd this (not_lt.2 hT.le)
  have hx : ∀ a, x a ≠ 0 := fun a => by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp only [hxdef, Fin.snoc_last]; exact hq2
    · simp only [hxdef, Fin.snoc_castSucc]; exact hq.1 i
  have hZ' : Formalism.QuantumDeterminants.Zhat k r D.z D.z' γ = Matrix.diagonal x := hZ
  have hD := dmin_diag D.z D.z' γ x hZ'

  have hDr1 : Dmin k r D.z D.z' γ (Fin.last (r + 1)) = Dmin k r D.z D.z' γ ⟨r, by omega⟩ * q.2 := by
    rw [hD, hD]
    have := prod_castLE_succ x r (le_refl _)
    simp only [Fin.val_last] at *
    rw [this]
    congr 1
    show x (Fin.last r) = q.2
    simp [hxdef]
  have hOm : γ ∈ Formalism.FourierDecayAlt.JF.Om k r D.z D.z' := by
    refine ⟨hγ, fun l _ => by rw [hD]; exact prod_castLE_ne x hx _ _, ?_⟩
    unfold Gf
    rw [hDr1, map_mul]
    have h0 : 0 < Complex.normSq (Dmin k r D.z D.z' γ ⟨r, by omega⟩) := by
      rw [hD]; exact Complex.normSq_pos.2 (prod_castLE_ne x hx _ _)
    nlinarith [hq.2]
  obtain ⟨p, hp, q', hq', he⟩ := Formalism.FourierDecayAlt.Final.jf_psiOnto k r Wp Wq D γ hOm
  refine ⟨p, hp, ?_⟩
  have hcm : ∀ a : Fin r, cmin k r D.z D.z' γ a = q.1 a := by
    intro a
    unfold cmin
    rw [hD, hD]
    have := prod_castLE_succ x a.val (by omega)
    simp only at this ⊢
    rw [this, mul_div_cancel_left₀ _ (prod_castLE_ne x hx _ _)]
    show x (Fin.castSucc a) = q.1 a
    simp [hxdef]
  have hzt : zeta k r D.z D.z' γ = q.2 := by
    unfold zeta
    rw [hDr1, mul_div_cancel_left₀ _ (by rw [hD]; exact prod_castLE_ne x hx _ _)]
  have hqq : q' = q := by
    have h1 : ∀ a, cmin k r D.z D.z' γ a = q'.1 a := by
      intro a; rw [he]; unfold cmin; simp only [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs D hp]
      exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.cmin_gq D hq' a
    have h2 : zeta k r D.z D.z' γ = q'.2 := by
      rw [he]; unfold zeta; simp only [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs D hp]
      exact Formalism.FourierDecayAlt.P.BigCellZetaMinors.zeta_gq D hq'
    ext a
    · rw [← h1, hcm]
    · rw [← h2, hzt]
  rw [he, hqq]

theorem ptEntry_ones (l : List ℂ) : ∀ a b : ℕ,
    Formalism.FourierDecayAlt.D.ptEntry (l.map fun t => (1, t)) a b = if a = b then l.getD a 0 else 0 := by
  induction l with
  | nil => intro a b; simp [Formalism.FourierDecayAlt.D.ptEntry]
  | cons t l ih =>
    intro a b
    cases a <;> cases b <;> simp [Formalism.FourierDecayAlt.D.ptEntry, ih]

theorem relDiag_holds : RelDiag := by
  intro k r Wp Wq _ _ _ _ D γ d hγ hd hZ
  refine Formalism.FourierDecayAlt.Final.d_ptRelevant k r Wp Wq D ((List.ofFn d).map fun t => (1, t)) γ ⟨?_, ?_⟩ hγ ?_
  · intro b hb
    simp only [List.mem_map, List.mem_ofFn] at hb
    obtain ⟨t, ⟨a, rfl⟩, rfl⟩ := hb
    exact ⟨le_refl _, hd a⟩
  · simp only [Formalism.FourierDecayAlt.D.ptSize, List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  · rw [hZ]
    ext i j
    show Matrix.diagonal d i j = Formalism.FourierDecayAlt.D.ptEntry _ i.val j.val
    rw [ptEntry_ones, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      simp only [if_true]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
    · simp [h, Fin.val_inj]

end BesselPf

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def StOne (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  ∀ (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) (cv : Fin (D.R.rS + 1) → ℂ), cv ∈ GoodV u u' →
    Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat g) = Matrix.diagonal cv →
    StSet (NV X u v) (NV X u' v) g = {1}

def ZhatTr (P : Parts X u u') (hr : P.S.G.r = D.R.rS) : Prop :=
  P.FromX → 0 < P.S.g →
  ∀ (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) (cv : Fin (D.R.rS + 1) → ℂ), cv ∈ GoodV u u' →
    Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat g) = Matrix.diagonal cv →
    trG (P.Q v) (P.Qi v) g ∈ Formalism.FourierDecayAlt.B.GV P.S.G.k P.S.G.r ∧
    Formalism.QuantumDeterminants.Zhat P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z (P.T (P.τ.symm v)).base.z' (trG (P.Q v) (P.Qi v) g) =
      qDiag (phiQ P hr cv) ∧
    phiQ P hr cv ∈ Formalism.FourierDecayAlt.JF.QDom P.S.G.k P.S.G.r (P.T (P.τ.symm v)).base.z (P.T (P.τ.symm v)).base.z'

theorem trMeas_dirac (P : Parts X u u') (v : InfinitePlace X.B.I.F) (hQ : P.Qi v * P.Q v = 1) :
    trMeas P v (Measure.dirac 1) = Measure.dirac (Matrix.of.symm (1 : Formalism.FourierDecayAlt.B.Mat P.S.G.k P.S.G.r)) := by
  unfold trMeas
  have h1 : Continuous (fun s : Formalism.REAL.UJ (X.B.I.ε v) => ((s : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)) := Units.continuous_val.comp continuous_subtype_val
  have hm : Measurable (fun s : Formalism.REAL.UJ (X.B.I.ε v) => Matrix.of.symm (trG (P.Q v) (P.Qi v) s)) := by
    refine Continuous.measurable ?_
    exact (continuous_const.matrix_mul h1).matrix_mul continuous_const
  rw [Measure.map_dirac' hm]
  congr 1
  simp [trG, uMat, hQ]

theorem normBridge_of (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hOD : OrbDirac) (hHS : HSsgs) (hCo : CosetOf)
    (hRel : RelDiag) (hSt : StOne X u u') (hZ : ZhatTr P hr) : NormBridge P hr := by
  intro hFX hBuilt hg v g cv hcv hZg
  obtain ⟨hGV, hZB, hq⟩ := hZ hFX hg v g cv hcv hZg
  have hQ : P.Qi v * P.Q v = 1 := (hFX v).1.1
  have hS := hSt v g cv hcv hZg
  refine ⟨Measure.dirac 1, Formalism.REAL.muG _, ⟨?_, ?_, ?_, ?_, ?_⟩, rfl, ?_⟩
  · rw [hZg]; exact hcv.2
  · rw [hZg]
    exact ⟨1, cv, hcv.1, by ext i a; simp only [Formalism.FourierDecayAlt.C2.monoP, Matrix.diagonal_apply, Matrix.of_apply, Equiv.Perm.coe_one, id]; split_ifs with h <;> simp_all⟩
  · exact hRel _ _ _ _ _ _ (Fin.snoc (α := fun _ => ℂ) (phiQ P hr cv).1 (phiQ P hr cv).2) hGV
      (fun a => by
        refine Fin.lastCases ?_ (fun i => ?_) a
        · simp only [Fin.snoc_last]; intro h; have := hq.2; rw [h, map_zero] at this
          exact absurd this (not_lt.2 (mul_pos (P.T (P.τ.symm v)).base.T_pos (P.T (P.τ.symm v)).base.T'_pos).le)
        · simp only [Fin.snoc_castSucc]; exact hq.1 i) hZB
  · rw [hS]
    refine ⟨inferInstance, Measure.dirac_ne_zero, ?_, ?_⟩
    · simp
    · intro s hs; rw [Set.mem_singleton_iff.1 hs]; simp
  · intro f hf
    simp [lintegral_dirac]
  · rw [trMeas_dirac P v hQ, hOD _ _ _ _ _ _ hGV]
    obtain ⟨p, hp, hγ⟩ := hCo _ _ _ _ _ _ hGV _ hq hZB
    rw [hγ]
    exact hHS _ _ _ _ _ _ _ hp _

theorem normBridge_of_two (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hSt : StOne X u u') (hZ : ZhatTr P hr) :
    NormBridge P hr :=
  normBridge_of P hr orbDirac_holds hSsgs_holds cosetOf_holds relDiag_holds hSt hZ

end Formalism.L2.SG.Pf.Carrier.JointPinNorm
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointPinNormSt

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointQuot
  Formalism.L2.SG.Pf.Carrier.JointPin Formalism.L2.SG.Pf.Carrier.JointPinNorm Formalism.L2.SG.HidaSetting

section Lin

variable {n r : ℕ} (ε : Fin n → Bool)

theorem hJ_add_r (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  simp [hJ, Matrix.mulVec_add, dotProduct_add]

theorem hJ_sub_r (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  simp [hJ, Matrix.mulVec_sub, dotProduct_sub]

theorem hJ_smul_r (x : Fin n → ℂ) (c : ℂ) (y : Fin n → ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  simp [hJ, Matrix.mulVec_smul, dotProduct_smul]

theorem hJ_zero_r (x : Fin n → ℂ) : hJ ε x 0 = 0 := by
  simp [hJ]

theorem hJ_sum_r {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (f : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, f i) = ∑ i ∈ s, hJ ε x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hJ_zero_r]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hJ_add_r, ih]

theorem hJ_unit (M : Matrix (Fin n) (Fin n) ℂ) (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) (x y : Fin n → ℂ) :
    hJ ε (M *ᵥ x) (M *ᵥ y) = hJ ε x y := by
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]

theorem hJ_conj_swap (x y : Fin n → ℂ) : hJ ε x y = conj (hJ ε y x) :=
  Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_conj ε x y

theorem recon (e u : Fin r → Fin n → ℂ) (κ : Fin r → ℂ) (hκ : ∀ d, κ d ≠ 0)
    (hue : ∀ d c, hJ ε (u d) (e c) = if d = c then κ d else 0) (s : Finset (Fin r)) (w : Fin n → ℂ)
    (hw : w ∈ Submodule.span ℂ (e '' ↑s)) : w = ∑ c ∈ s, (hJ ε (u c) w / κ c) • e c := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    rw [Finset.sum_eq_single b]
    · rw [hue, if_pos rfl, div_self (hκ b), one_smul]
    · intro c _ hcb; rw [hue, if_neg hcb, zero_div, zero_smul]
    · intro h; exact absurd hb h
  | zero => simp [hJ_zero_r]
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [hJ_add_r, add_div, add_smul, Finset.sum_add_distrib]
  | smul t x _ hx =>
    conv_lhs => rw [hx]
    simp only [hJ_smul_r, Finset.smul_sum, smul_smul, mul_div_assoc]

theorem zero_of_pair (e u : Fin r → Fin n → ℂ) (κ : Fin r → ℂ) (hκ : ∀ d, κ d ≠ 0)
    (hue : ∀ d c, hJ ε (u d) (e c) = if d = c then κ d else 0) (s : Finset (Fin r)) (w : Fin n → ℂ)
    (hw : w ∈ Submodule.span ℂ (e '' ↑s)) (h0 : ∀ c ∈ s, hJ ε (u c) w = 0) : w = 0 := by
  rw [recon ε e u κ hκ hue s w hw]
  exact Finset.sum_eq_zero fun c hc => by rw [h0 c hc, zero_div, zero_smul]

theorem orth_span (e : Fin r → Fin n → ℂ) (x : Fin n → ℂ) (s : Set (Fin r)) (hx : ∀ c ∈ s, hJ ε x (e c) = 0)
    (w : Fin n → ℂ) (hw : w ∈ Submodule.span ℂ (e '' s)) : hJ ε x w = 0 := by
  induction hw using Submodule.span_induction with
  | mem y hy => obtain ⟨b, hb, rfl⟩ := hy; exact hx b hb
  | zero => exact hJ_zero_r ε x
  | add y y' _ _ hy hy' => rw [hJ_add_r, hy, hy', add_zero]
  | smul t y _ hy => rw [hJ_smul_r, hy, mul_zero]

theorem spanLt_eq (e : Fin r → Fin n → ℂ) (a : ℕ) :
    spanLt e a = Submodule.span ℂ (e '' ↑(Finset.univ.filter fun b : Fin r => b.1 < a)) := by
  unfold spanLt
  congr 2
  ext b
  simp

theorem st_one_lin (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (G Gi M : Matrix (Fin n) (Fin n) ℂ)
    (hGi : G * Gi = 1) (hG : Gᴴ * Formalism.REAL.Jm ε * G = Formalism.REAL.Jm ε)
    (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) (hee : ∀ a b, hJ ε (e a) (e b) = 0) (cv : Fin r → ℂ)
    (hcv : ∀ a, cv a ≠ 0) (hZ : ∀ a b, hJ ε (e a) (G *ᵥ e b) = if a = b then cv a else 0)
    (hN : InN ε e z M) (hN' : InN ε e z' (Gi * M * G)) : M = 1 := by
  classical
  have hGGi : ∀ x, G *ᵥ (Gi *ᵥ x) = x := fun x => by rw [Matrix.mulVec_mulVec, hGi, Matrix.one_mulVec]
  have hMG : ∀ x, G *ᵥ ((Gi * M * G) *ᵥ x) = M *ᵥ (G *ᵥ x) := fun x => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGi, Matrix.one_mul]

  have hu1 : ∀ d c, hJ ε (G *ᵥ e d) (e c) = if d = c then conj (cv d) else 0 := by
    intro d c
    rw [hJ_conj_swap, hZ]
    by_cases h : c = d
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), map_zero]
  have hu2 : ∀ d c, hJ ε (Gi *ᵥ e d) (e c) = if d = c then cv d else 0 := by
    intro d c
    rw [← hJ_unit ε G hG, hGGi, hZ]
  have hk1 : ∀ d, conj (cv d) ≠ 0 := fun d => by simpa using hcv d
  have hfx : ∀ x y, M *ᵥ x = x → hJ ε x (M *ᵥ y) = hJ ε x y := fun x y hx => by
    conv_lhs => rw [← hx]
    exact hJ_unit ε M hM x y

  have key : ∀ m : ℕ, ∀ c : Fin r, c.1 = m → M *ᵥ e c = e c ∧ M *ᵥ (G *ᵥ e c) = G *ᵥ e c := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro c hc
      have ih' : ∀ d : Fin r, d.1 < c.1 → M *ᵥ e d = e d ∧ M *ᵥ (G *ᵥ e d) = G *ᵥ e d :=
        fun d hd => ih d.1 (hc ▸ hd) d rfl
      have h1 : M *ᵥ e c = e c := by
        have hw := hN.1.1 c
        rw [spanLt_eq] at hw
        have h0 := zero_of_pair ε e (fun d => G *ᵥ e d) (fun d => conj (cv d)) hk1 hu1 _ _ hw (by
          intro d hd
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, hJ_sub_r, hfx _ _ (ih' d hd).2, sub_self])
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
        exact h0
      refine ⟨h1, ?_⟩
      have hw := hN'.1.1 c
      rw [spanLt_eq] at hw
      have h0 := zero_of_pair ε e (fun d => Gi *ᵥ e d) cv hcv hu2 _ _ hw (by
        intro d hd
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
        rw [← hJ_unit ε G hG, hGGi, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, hMG, hJ_sub_r,
          hfx _ _ (ih' d hd).1, sub_self])
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
      rw [← hMG, h0]
  have hfix1 : ∀ c, M *ᵥ e c = e c := fun c => (key c.1 c rfl).1
  have hfix2 : ∀ c, M *ᵥ (G *ᵥ e c) = G *ᵥ e c := fun c => (key c.1 c rfl).2

  have hall : ∀ v, M *ᵥ v = v := by
    intro v
    set S1 : Fin n → ℂ := ∑ c, (hJ ε (G *ᵥ e c) v / conj (cv c)) • e c with hS1
    set S2 : Fin n → ℂ := ∑ c, (hJ ε (e c) v / cv c) • (G *ᵥ e c) with hS2
    set v1 := v - S1 - S2 with hv1
    have hGe : ∀ d c, hJ ε (G *ᵥ e d) (G *ᵥ e c) = 0 := fun d c => by rw [hJ_unit ε G hG, hee]
    have ho1 : ∀ d, hJ ε (e d) v1 = 0 := by
      intro d
      rw [hv1, hJ_sub_r, hJ_sub_r, hS1, hS2, hJ_sum_r, hJ_sum_r]
      simp only [hJ_smul_r, hee, mul_zero, Finset.sum_const_zero, sub_zero, hZ]
      rw [Finset.sum_eq_single d (fun c _ hc => by rw [if_neg (Ne.symm hc), mul_zero]) (by simp), if_pos rfl,
        div_mul_cancel₀ _ (hcv d), sub_self]
    have ho2 : ∀ d, hJ ε (G *ᵥ e d) v1 = 0 := by
      intro d
      rw [hv1, hJ_sub_r, hJ_sub_r, hS1, hS2, hJ_sum_r, hJ_sum_r]
      simp only [hJ_smul_r, hGe, mul_zero, Finset.sum_const_zero, sub_zero, hu1]
      rw [Finset.sum_eq_single d (fun c _ hc => by rw [if_neg (Ne.symm hc), mul_zero]) (by simp), if_pos rfl,
        div_mul_cancel₀ _ (hk1 d), sub_self]
    have hv : v = v1 + S1 + S2 := by rw [hv1]; abel
    clear_value v1 S1 S2

    have hX : (M - 1) *ᵥ v1 ∈ spanLt e r := hN.2 v1 ho1
    have hGX : (Gi * M * G - 1) *ᵥ (Gi *ᵥ v1) ∈ spanLt e r :=
      hN'.2 _ (fun a => by rw [← hJ_unit ε G hG, hGGi]; exact ho2 a)
    have hw : (M - 1) *ᵥ v1 = G *ᵥ ((Gi * M * G - 1) *ᵥ (Gi *ᵥ v1)) := by
      rw [Matrix.sub_mulVec (Gi * M * G), Matrix.mulVec_sub, hMG, hGGi, Matrix.one_mulVec, hGGi,
        Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [spanLt_eq] at hX
    have h0 := zero_of_pair ε e (fun d => G *ᵥ e d) (fun d => conj (cv d)) hk1 hu1 _ _ hX (by
      intro d _
      rw [hw, hJ_unit ε G hG]
      exact orth_span ε e (e d) _ (fun c _ => hee d c) _ hGX)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    rw [hv, Matrix.mulVec_add, Matrix.mulVec_add, h0, hS1, hS2, Matrix.mulVec_sum, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hfix1, hfix2]
  exact Matrix.ext_of_mulVec_single fun i => by rw [hall, Matrix.one_mulVec]

end Lin

variable {D : D7}

theorem stOne_holds (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : StOne X u u' := by
  intro v g cv hcv hZ
  have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b => by
    rw [show X.eR a = X.crd (X.eX a) from rfl, show X.eR b = X.crd (X.eX b) from rfl,
      Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, X.ee, map_zero]
  have hfrm : ∀ (w : D.what₂.Word) (c : Fin D.R.rS), frm X w 1 v (Fin.castSucc c) = rv X.B.I v (X.eR c) := by
    intro w c
    simp [frm, famSc, fam, Fin.snoc_castSucc]
  have hZ' : ∀ a b : Fin D.R.rS, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (uMat g *ᵥ rv X.B.I v (X.eR b)) =
      if a = b then cv (Fin.castSucc a) else 0 := by
    intro a b
    have := congrFun (congrFun hZ (Fin.castSucc a)) (Fin.castSucc b)
    unfold Formalism.L2.SG.RealObj.Zhat at this
    simp only [hfrm, Matrix.diagonal_apply, Fin.castSucc_inj] at this
    exact this
  have hmemUJ : ∀ y : Formalism.REAL.UJ (X.B.I.ε v), (uMat y)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat y = Formalism.REAL.Jm (X.B.I.ε v) :=
    fun y => y.2
  have hone : (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ StSet (NV X u v) (NV X u' v) g := by
    have h1 : ∀ w : D.what₂.Word, (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ NV X w v := by
      intro w
      show InN _ _ _ (uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)))
      have : uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) = 1 := rfl
      rw [this]
      refine ⟨⟨fun a => ?_, ?_⟩, fun y _ => ?_⟩ <;> simp [Submodule.zero_mem]
    refine ⟨h1 u, ?_⟩
    rw [mul_one, inv_mul_cancel]
    exact h1 u'
  ext y
  refine ⟨fun hy => ?_, fun hy => by rw [Set.mem_singleton_iff.1 hy]; exact hone⟩
  obtain ⟨hy1, hy2⟩ := hy
  have hcoe : uMat (g⁻¹ * y * g) = uMat g⁻¹ * uMat y * uMat g := by
    simp [uMat]
  have hGi : uMat g * uMat g⁻¹ = 1 := by
    simp [uMat]
  have hN' : InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat g⁻¹ * uMat y * uMat g) := by
    rw [← hcoe]; exact hy2
  have hM := st_one_lin (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u'))
    (uMat g) (uMat g⁻¹) (uMat y) hGi (hmemUJ g) (hmemUJ y) hee (fun a => cv (Fin.castSucc a))
    (fun a => hcv.1 _) hZ' hy1 hN'
  rw [Set.mem_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  exact hM

theorem normBridge_of_zhat {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word} (P : Parts X u u')
    (hr : P.S.G.r = D.R.rS) (hZ : ZhatTr P hr) : NormBridge P hr :=
  normBridge_of_two P hr (stOne_holds X u u') hZ

end Formalism.L2.SG.Pf.Carrier.JointPinNormSt
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierXAll

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.CarrierT

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

theorem energy_compact_test_bound {D : D7} (T : Formalism.L2.SG.SpectralTiesReal.STies D) {θ : ℝ} (C : Choice T.X θ) (u u' : D.what₂.Word)
    (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie T.X e) (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2)
    (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (a b : ∀ j : Fin (nfE D), T.X.B.H (tauE T.X e j)) (ξ : ∀ j : Fin (nfE D), T.X.Vloc u (tauE T.X e j))
    (ξ' : ∀ j : Fin (nfE D), T.X.Vloc u' (tauE T.X e j)) (cc : Fin (nfE D) → ℂ)
    (i0' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (T.X.Vloc u (tauE T.X e j)) (T.X.Vloc u' (tauE T.X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf T.X C u u' e j).base.π
      (towersOf T.X C u u' e j).base.z (m0E T.X C u u' e j *ᵥ nuE T.X C u' e i0' j)) (A₀ : ℝ)
    (X0 : Fin (2 * D.R.rS + 2) → Fin T.X.B.I.n → T.X.B.I.E) (sd Cb Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Formalism.MainNotions.S.Lat.Tu D u : ℕ) : D.host.E)} {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (i0b i0b' : ∀ _ : InfinitePlace T.X.B.I.F, Fin D.R.k) (νq : T.X.B.I.Ginf → Measure T.X.B.I.Ginf)
    (hpin : JointPin.PinCov (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))))
    (hBuilt : Formalism.FourierDecayAlt.D.IsBuilt (Formalism.L2.SG.Pf.Carrier.sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)) (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).χ (nuE T.X C u' e i0') (m0E T.X C u u' e) (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).top A₀) :
    (∏ v, (Formalism.FourierDecayAlt.B.normSq ((ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).T v).base ((ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀).fc v)).toReal /
        Formalism.FourierDecayAlt.D.GamLev (Formalism.L2.SG.Pf.Carrier.sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).G.k (Formalism.L2.SG.Pf.Carrier.sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).G.r (Formalism.FourierDecayAlt.D.kapG (Formalism.L2.SG.Pf.Carrier.sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).g (Formalism.FourierDecayAlt.S6.rd D.host.E))
          (Formalism.FourierDecayAlt.D.deG (Formalism.L2.SG.Pf.Carrier.sOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀)).g (Formalism.FourierDecayAlt.S6.rd D.host.E)) 0) =
      (Formalism.L2.SG.SpectralTiesReal.massDataY T.X T.hb T.Y u u' X0 T.ψ sd Cb Th vR Q i0b i0b' νq).IntN := by
  have hFX : (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))).FromX :=
    BaseOf.fromX T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd.χ (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1))
      (nuE T.X C u' e i0') (m0E T.X C u u' e) (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf T.X C u u' e j) (nuE T.X C u' e i0' j)
        (m0E T.X C u u' e j) (Θ j) (TP j)) A₀ (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))
  have hg0 : 0 < (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))).S.g := by
    show 0 < D.host.g 0 * D.host.g 1
    exact Nat.mul_pos (Formalism.L2.SG.Pf.CarrierSz.g_pos D).1 (Formalism.L2.SG.Pf.CarrierSz.g_pos D).2
  have hZ := zhatTr_carrierOf T.X u u' e he hv C CA de de' l (gridT e l) (grid1T e l) (towersOf T.X C u u' e)
    (Tz_towersOf_base_eq_T T.X C u u' e) (fcT T.X C e u u' a b ξ ξ' cc) cutStd.χ (sgOf (Formalism.L2.SG.SpectralTiesReal.gOf D e) (plE D) ((D.mem u).A.T : ℝ) ((D.mem u').A.T : ℝ) de de' (l + 1)) (nuE T.X C u' e i0') (m0E T.X C u u' e)
    (fun j => Formalism.FourierDecayAlt.Top.topOf (parE e u u' de de' j) (l + 1) (towersOf T.X C u u' e j) (nuE T.X C u' e i0' j)
        (m0E T.X C u u' e j) (Θ j) (TP j)) A₀ (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))
  have hPN := JointPin.placeNormG_of_pin (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))) rfl hpin
    (JointPinNormSt.normBridge_of_zhat _ rfl hZ) hFX hBuilt hg0
  have hrd : Formalism.FourierDecayAlt.S6.rd D.host.E = D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE Formalism.FourierDecayAlt.S6.rd
    rw [Int.cast_abs, one_div]
  have hk1 : 1 ≤ (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))).S.G.k := by
    show 1 ≤ D.R.k
    have := Formalism.MainNotions.BridgeLemma.five_le_k D
    omega
  exact EnergyNF.energy_norm_bound_third_form T.hb T.Y X0 T.ψ sd Cb Th vR Q i0b i0b' νq (CarrierOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀) (modelsOf (ITc T.X C u u' e he hv CA de de' l (gridT e l) (grid1T e l) (fcT T.X C e u u' a b ξ ξ' cc) cutStd i0' Θ TP A₀))) rfl rfl
    (fun v => Tz_towersOf_base_eq_T T.X C u u' e _) rfl hrd hg0 hk1 (Formalism.L2.SG.WConst.card_places T.X) T.ψ_char T.ψ_std
    (Formalism.L2.SG.Pf.ProdConvCut2.prodConv_holds T u u') (Formalism.L2.S.Pv.MSTypP.lemmaMSStd_holds T.X u u' T.ψ) hPN

end Formalism.L2.SG.Pf.CarrierXAll
