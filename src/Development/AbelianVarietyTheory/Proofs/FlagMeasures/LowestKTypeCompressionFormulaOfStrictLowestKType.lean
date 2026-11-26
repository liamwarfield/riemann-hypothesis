module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyUJ
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneLargeGaps
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesBesselGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermLatticeOverInnerDatumFgSpan

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeCompressionFormulaOfStrictLowestKType
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeCompressionFormulaOfStrictLowestKType
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.FormGapFree

open GlobalTheory.Jet.FormGap GlobalTheory.Dec.FormF GlobalTheory.Dec.PsiEig Filter Topology

theorem formulaGap : FormulaGap := by
  intro n ε lam H _ _ σ hlam hσ h hgap hh w hw X hX u hu v hv
  haveI := hσ.1
  have hU := hσ.2.2.1
  obtain ⟨g₀, hg1, hg2⟩ := exists_gap hlam hgap hh
  have hS := GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub n ε lam H σ hlam hσ fun a b hab => by
    rcases lt_trichotomy a b with hlt | heq | hlt
    · exact (hg2.trans_le (hg1 a b hlt hab)).trans_le (le_abs_self _)
    · exact absurd (congrArg ε heq) hab
    · rw [abs_sub_comm]
      exact (hg2.trans_le (hg1 b a hlt hab.symm)).trans_le (le_abs_self _)
  obtain ⟨V, E, hD, hSV⟩ := GlobalTheory.DerEx.exists_isDer_lowKSub n ε lam H σ hU hS
  have han := GlobalTheory.Jet.Anal.lowK_analytic n ε H σ V E lam hU hD hS hSV u hu X hX.1
  obtain ⟨hw1, hwS, hwt⟩ := hw
  generalize lowKSub ε lam σ = S at *
  haveI := hS.1
  haveI := FiniteDimensional.complete ℂ S
  obtain ⟨τ, hτ, hτσ⟩ := TauExt.tauExists n ε _ H σ S ⟨w, hwS⟩ (URep_K hU) hS hw1 hwt
  have hw0 : (⟨w, hSV hwS⟩ : V) ≠ 0 := fun h0 => by
    have : w = 0 := congrArg Subtype.val h0
    simp [this] at hw1
  obtain ⟨hK, hsp, hfd⟩ := (KType.kType_iff n ε H σ V E hU hD).2 _ S ⟨w, hSV hwS⟩ hS hSV hwS hw0 hwt
  have hA : ∀ x y : S, LocAn ε (fun z => ⟪y, Psi ε lam τ ⟨w, hwS⟩ (z.map star) x⟫_ℂ) := fun x y =>
    locAn_conj (f := fun z => ⟪y, Psi ε lam τ ⟨w, hwS⟩ z x⟫_ℂ) fun g hg => psiAnalytic n ε lam S τ _ hlam hτ y x g hg
  have hsm : ∀ (x : V) (y : H), SmoothOnG ε (fun z => ⟪y, diffOp ε lam σ τ ⟨w, hwS⟩ z x⟫_ℂ) := fun x y => by
    rw [inner_diffOp]
    exact Line.smooth_comb _ (hD.2.2.2 x _) (hA _ _).smooth
  have hjet := GlobalTheory.Jet.Germ.germ_jet_zero n ε H σ V E lam g₀ ⟨w, hSV hwS⟩ hU hD hK hfd hg1 hg2
    (fun z => (diffOp ε lam σ τ ⟨w, hwS⟩ z : H →ₗ[ℂ] H)) ?_ ?_ ?_ ?_
  · rw [hsp] at hjet
    have h0 := Line.vanish_of_zero_jet n ε _ X (hsm ⟨u, hSV hu⟩ v) hX.1 (fun l => hjet l u hu v) (by
      intro t ht
      have e := inner_diffOp (ε := ε) (σ := σ) lam τ ⟨w, hwS⟩ u v
      simp only [congrFun e]
      exact (((innerSL ℂ (S.starProjection v)).restrictScalars ℝ).analyticAt _ |>.comp (han t ht)).add
        (analyticAt_const.mul (locAn_line (hA _ _) hX.1 t ht)))
    have hp := exp_posDef (P_star hX)
    have h1 := (psiPolar n ε lam S τ _ hlam hτ).1 1 (one_K ε) _ (P_star hX)
    rw [one_mul, hτ.2.1.1, ← exp_star] at h1
    rw [← exp_star] at hp
    have h2 := ps_entry (lam := lam) hτ hτσ (z := NormedSpace.exp X) (fun k hk => (phiPos n lam _ (by
      rw [K_inv hk]
      exact hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC hk).1))).1) u v
    rw [congrFun (inner_diffOp lam τ ⟨w, hwS⟩ u v), h1, Submodule.starProjection_eq_self_iff.2 hv, neg_one_mul,
      add_neg_eq_zero] at h0
    refine h0.trans (h2.trans ?_)
    congr 2
    funext k
    have hk : toMK k ∈ Kset ε := k.2
    have hpos : ((toMK k)⁻¹ * NormedSpace.exp X * toMK k).PosDef := by
      rw [K_inv hk]
      exact (exp_posDef hX).conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC hk).1)
    rw [Phi_star, (phiPos n lam _ hpos).2.1.le.isSelfAdjoint.star_eq]
  · rw [hsp]
    exact fun g hg x _ => ⟨S.sub_mem (S.starProjection_apply_mem _) (Subtype.prop _),
      fun k₁ h₁ k₂ h₂ => diffOp_equiv hlam hU hS.2.1 hτ hτσ hg h₁ h₂ x⟩
  · rw [hsp]
    exact fun x hx y => hsm ⟨x, hSV hx⟩ y
  · intro G hG y
    filter_upwards [psi_near_one hlam hτ hτσ, GlobalTheory.Jet.SchmidIntegral.eab_integral_eq_zero n ε H σ V E lam _ hU hD hK hfd G hG y] with g h1 h2
    have h3 : ∀ a b, Eab ε a b (fun z => ⟪y, diffOp ε lam σ τ ⟨w, hwS⟩ z (at1 G a b : V)⟫_ℂ) (umat g) =
        ⟪S.starProjection y, σ (umat g) (E a b (at1 G a b) : V)⟫_ℂ + (-1) * ((Module.finrank ℂ S : ℂ) *
          Eab ε a b (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) *
            (⟪y, σ (toMK k) w⟫_ℂ * ⟪σ (toMK k) w, (at1 G a b : V)⟫_ℂ) ∂(muK ε)) (umat g)) := fun a b => by
      rw [inner_diffOp, ← h1 a b (at1 G a b : V) y]
      refine (Line.word_comb (-1) (hD.2.2.2 _ _) (hA _ _).smooth [(a, b)] _ g.2).trans ?_
      rw [(Coef.coef_flow n ε H σ V E hU hD).1 _ _ _ _ g.2]
      rfl
    have h4 := congrArg (fun x : V => ⟪S.starProjection y, σ (umat g) x⟫_ℂ)
      (GlobalTheory.Jet.Schmid.mul_vminus_eq_zero n ε H σ V E lam _ hlam hσ hD hK hfd G hG)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Submodule.coe_sum, map_sum, inner_sum, Submodule.coe_zero, map_zero, inner_zero_right] at h4
    simp only [ContinuousLinearMap.coe_coe, h3, Finset.sum_add_distrib, ← Finset.mul_sum, h2, h4]
    simp
  · rw [hsp]
    intro x hx
    change diffOp ε lam σ τ ⟨w, hwS⟩ 1 x = 0
    rw [diffOp_apply, map_star_one, (psiPolar n ε lam S τ _ hlam hτ).2.1, hU.1.1]
    exact sub_self _

end GlobalTheory.Jet.FormGapFree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeCompressionFormulaOfStrictLowestKTypeStatement
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKType_compressionFormula_of_strictLowestKType : FormulaGap := by
  first | exact @GlobalTheory.Jet.FormGapFree.formulaGap | exact GlobalTheory.Jet.FormGapFree.formulaGap | (intros; apply GlobalTheory.Jet.FormGapFree.formulaGap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefWeightedLocUncond
namespace GlobalTheory.Sloc.CoefWeighted

theorem coefWeightedLoc_uncond : Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc :=
  ReciprocityTheory.ChartRestriction.DS.coefWeightedLoc

end GlobalTheory.Sloc.CoefWeighted
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelesCmFieldEqZeroOfComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelesCmFieldEqZeroOfComponents
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

namespace GlobalTheory


open Classical in
theorem equivFinsuppOfBasisLeft_lTensor {K M N N' ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N'] [DecidableEq ι]
    (b : Module.Basis ι K M) (f : N →ₗ[K] N') (x : M ⊗[K] N) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b (LinearMap.lTensor M f x) i =
      f (TensorProduct.equivFinsuppOfBasisLeft b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem AL_eq_zero_of_compAt (L : Type) [Field L] [NumberField L] (a : ReciprocityTheory.Aut.AL L)
    (h : ∀ v, ReciprocityTheory.Aut.compAt L v a = 0) : a = 0 := by
  classical
  set K := maximalRealSubfield L
  let b := Module.finBasis K L
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := AFplus L) b
  have hc : ∀ i, e a i = 0 := by
    intro i
    refine RestrictedProduct.ext _ _ (fun v => ?_)
    have h1 : ∀ x, ReciprocityTheory.Aut.compAt L v x =
        LinearMap.lTensor L (ReciprocityTheory.Aut.evalAt L v).toLinearMap x := by
      intro x
      simp only [ReciprocityTheory.Aut.compAt]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul m n => simp [Algebra.TensorProduct.map_tmul]
      | add x y hx hy => simp only [map_add (f := _)] at *; rw [hx, hy]
    have h2 := equivFinsuppOfBasisLeft_lTensor b (ReciprocityTheory.Aut.evalAt L v).toLinearMap a i
    rw [← h1 a, h v, map_zero, Finsupp.zero_apply] at h2
    exact h2.symm
  have : e a = 0 := Finsupp.ext hc
  simpa using congrArg e.symm this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelesCmFieldEqZeroOfComponentsStatement
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelesCmField_eq_zero_of_components : ∀ (L : Type) [Field L] [NumberField L] (a : ReciprocityTheory.Aut.AL L), (∀ v, ReciprocityTheory.Aut.compAt L v a = 0) → a = 0 := by
  first | exact @GlobalTheory.AL_eq_zero_of_compAt | exact GlobalTheory.AL_eq_zero_of_compAt | (intros; apply GlobalTheory.AL_eq_zero_of_compAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPeriodPositivity
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPeriodPositivity
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AmpNormal

theorem det_hpk (k r : ℕ) : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

noncomputable def lmulEquiv {k r : ℕ} (t : MatKR k r) (ht : IsUnit t.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := fun i j => (t⁻¹ * Matrix.of x) i j
  invFun x := fun i j => (t * Matrix.of x) i j
  left_inv x := by
    show t * (t⁻¹ * Matrix.of x) = Matrix.of x
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ht, Matrix.one_mul]
  right_inv x := by
    show t⁻¹ * (t * Matrix.of x) = Matrix.of x
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ht, Matrix.one_mul]
  measurable_toFun := by
    have : Continuous fun x : MatKR k r => t⁻¹ * x := continuous_const.matrix_mul continuous_id
    exact Continuous.measurable (f := fun x : Mt k r => (fun i j => (t⁻¹ * Matrix.of x) i j : Mt k r)) this
  measurable_invFun := by
    have : Continuous fun x : MatKR k r => t * x := continuous_const.matrix_mul continuous_id
    exact Continuous.measurable (f := fun x : Mt k r => (fun i j => (t * Matrix.of x) i j : Mt k r)) this

theorem one_side (hH : Hyps) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ} {c : ℂ}
    {μW μN μG νq : Measure (Mt k r)} {B l : R.H → Wp} {w : R.H} {dd m : ℝ}
    (hds : R.IsDS ε mu) (hgap : GapAtLeast ε mu h) (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h)
    (hS : SideG k r z π u μW μN μG νq) (hc : c ≠ 0)
    (hB : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π B)
    (hl : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π l)
    (hbe : ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l v)).smulRight (l x))
    (hw : R.KFin w) (hm : 0 < m)
    (hmass : PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) = ENNReal.ofReal m)
    (hd0 : 0 < dd) (hdd : ∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ w = dd) :
    (∃ v, R.KFin v ∧ l v ≠ 0) ∧ ∃ β : ℂ, (∀ v ∈ R.sm, B v = β • l v) ∧ m * dd = ‖β‖ ^ 2 * ‖w‖ ^ 2 := by
  have hKF : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨hmul, hone, hinn, hsm, hTKsm, hTK, hKT, -, hcont⟩ := GlobalTheory.rep_basic_of_isDS hKF k r ε mu R hds
  obtain ⟨hG1, hGm, hGi⟩ := uHGroup _ _ (det_hpk k r)
  obtain ⟨t, ht, hN, hz, -⟩ := GlobalTheory.TorusScale.exists_torus_scale k r c hc
  obtain ⟨-, hcomm, hpsi⟩ := hz z hS.1
  have htd : IsUnit t.det := (hGi t ht).1
  have hti : t⁻¹ ∈ GG k r := (hGi t ht).2
  have hU : Formalism.MainNotions.S.IsURepOn (GG k r) R.σ := by
    refine ⟨⟨ContinuousLinearMap.ext hone, fun a ha b hb => ContinuousLinearMap.ext (hmul a ha b hb)⟩, fun g hg v => ?_,
      hcont⟩
    rw [@norm_eq_sqrt_re_inner ℂ, hinn g hg, ← @norm_eq_sqrt_re_inner ℂ]
  have e1 : ∀ v, R.σ t⁻¹ (R.σ t v) = v := fun v => by
    rw [← hmul _ hti _ ht, Matrix.nonsing_inv_mul _ htd, hone]
  have e2 : ∀ v, R.σ t (R.σ t⁻¹ v) = v := fun v => by
    rw [← hmul _ ht _ hti, Matrix.mul_nonsing_inv _ htd, hone]
  obtain ⟨hS', hR⟩ := GlobalTheory.BesselMove.bessel_move hH k r Wp z π u c μW μN μG νq t ht hN hcomm hpsi hS
  obtain ⟨hbes, hmove⟩ := hR R hU
  obtain ⟨l₁, hl₁⟩ := GlobalTheory.exists_normalised_bessel_map hH k r ε mu h R Wp z π u μW _ μG _ hds hgap hok hS'
  have hl₂ : IsBeL R z π μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) (fun v => l (R.σ t v)) := by
    refine ⟨(hbes l).1 hl, fun x hx v hv => ⟨(hl₁.2 x hx v hv).1, ?_⟩⟩
    rw [(hl₁.2 x hx v hv).2, ← hbe _ (hsm t ht x hx) _ (hTK t ht v hv),
      hmove l₁ hl₁ _ (hsm t ht x hx) _ (hTK t ht v hv), e1, e1]
  have hae : ∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r :=
    (GlobalTheory.quotMeas_ae_mem_and_measurable hKF k r ε mu R Wp z π u μW μN μG νq hds hS).1
  have htr : ∀ F : R.H → Wp,
      PI.BesselPeriodGGP.l2SG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) (fun g => F (R.σ t (R.σ g w))) =
        PI.BesselPeriodGGP.l2SG νq (fun g => F (R.σ g w)) := by
    intro F
    unfold PI.BesselPeriodGGP.l2SG
    refine (lintegral_map_equiv _ (lmulEquiv t htd)).trans (lintegral_congr_ae ?_)
    filter_upwards [hae] with x hx
    have : R.σ t (R.σ (Matrix.of (lmulEquiv t htd x)) w) = R.σ (Matrix.of x) w := by
      show R.σ t (R.σ (t⁻¹ * Matrix.of x) w) = _
      rw [hmul _ hti _ hx, e2]
    simp only [this]
  have hB₁ : IsBes R z π (fun v => B (R.σ t v)) := (hbes B).1 hB
  obtain ⟨v, hv, hv0⟩ := GlobalTheory.T.discrete_series_bessel_gap hH k r ε mu h R Wp z π u μW _ μG _ (fun v => B (R.σ t v))
    (fun v => l (R.σ t v)) w hds hgap hok hS' hB₁ hw
    (by rw [htr B, hmass]; exact (ENNReal.ofReal_pos.2 hm).ne') (by rw [htr B, hmass]; exact ENNReal.ofReal_ne_top) hl₂
  have hvs : v ∈ R.sm := hTKsm v (hKT v hv)
  have hnz : NzOn R (fun v => l (R.σ t v)) := ⟨v, hvs, hv0⟩
  refine ⟨GlobalTheory.exists_kFin_ne_zero_of_cwCont hKF k r ε mu R hds Wp l hl.1 hl.2.1 hl.2.2.2 ⟨_, hsm t ht v hvs, hv0⟩, ?_⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.BesselLine.bessel_line hH k r ε mu R Wp z π u μW _ μG _ _ _ hds hS' hl₂.1 hnz hB₁
  have hβ' : ∀ v ∈ R.sm, B v = β • l v := fun v hv => by
    have := hβ _ (hsm _ hti v hv)
    simpa only [e2] using this
  refine ⟨β, hβ', ?_⟩
  have hws : w ∈ R.sm := hTKsm w (hKT w hw)
  have hiso := (GlobalTheory.scaled_bessel_isometric hH k r ε mu h R Wp z π u μW _ μG _ _ dd hds hgap hok hS' hl₂ hdd hnz).2 w hws
  have h2 := (htr fun v => ((Real.sqrt dd : ℝ) : ℂ) • l v).symm.trans hiso
  have h3 : ENNReal.ofReal dd * PI.BesselPeriodGGP.l2SG νq (fun g => B (R.σ g w)) =
      ENNReal.ofReal (‖β‖ ^ 2) * PI.BesselPeriodGGP.l2SG νq (fun g => ((Real.sqrt dd : ℝ) : ℂ) • l (R.σ g w)) := by
    unfold PI.BesselPeriodGGP.l2SG
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    have en : ∀ y : Wp, ((‖y‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := fun y => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]; rfl
    rw [en, en, hβ' _ (hsm _ hx w hws), ← ENNReal.ofReal_mul hd0.le, ← ENNReal.ofReal_mul (by positivity),
      norm_smul, norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow,
      Real.sq_sqrt hd0.le]
    congr 1
    ring
  rw [hmass, h2, ← ENNReal.ofReal_mul hd0.le, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at h3
  linarith

theorem scale_pos {k r : ℕ} {μG μW ν : Measure (Mt k r)} {κ : ℝ≥0∞} (hG : μG ≠ 0)
    (hq : IsQuotMeas μG (muS μW (haarLie (Nset k r) κ)) ν) : 0 < κ := by
  rw [pos_iff_ne_zero]
  rintro rfl
  apply hG
  have := hq (fun _ => 1) measurable_const
  simpa [muS, haarLie] using this

theorem sideG_of {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : MatKR k r → (Wp →L[ℂ] Wp)} {u : Fin k → ℝ}
    {μW μG νq : Measure (Mt k r)} {κ : ℝ≥0∞} (hκ : κ < ⊤) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : IsHCTypeW k r z u π) (hW : IsHaarOn (UWset k r z) μW) (hG : IsHaarOn (UH (Hpk k r)) μG)
    (hq : IsQuotMeas μG (muS μW (haarLie (Nset k r) κ)) νq) :
    ∃ U, SideG k r z π U μW (haarLie (Nset k r) κ) μG νq := by
  refine ⟨fun n => if h : n - 1 < k then u ⟨n - 1, h⟩ else 0, hz, hT, ⟨u, hπ⟩,
    GlobalTheory.ThA.capParam_of_isHCTypeW k r z u _ Wp π hz hT hπ (fun i => by simp), hW,
    GlobalTheory.T.haarLie_isHaarOn_unipotentRadical k r κ (scale_pos hG.2.1 hq) hκ, hG, hq⟩

theorem dsigW_eq {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : MatKR k r → (H →L[ℂ] H)) (w : List (MatKR k r)) (v : H) :
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v = PI.UpqRep.dsigW (k := k) (r := r) σ w v := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show Formalism.MainNotions.S.dsig σ X (Formalism.MainNotions.S.dsigW σ w v) = PI.UpqRep.dsig σ X (PI.UpqRep.dsigW σ w v)
    rw [ih]; rfl

theorem isBesselMapSm_of {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {ψ : MatKR k r → ℂ}
    {σ : MatKR k r → (H →L[ℂ] H)} {π : MatKR k r → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (h : Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) z ψ σ π B) :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B := by
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  refine ⟨h1, h2, h3, C, Ws, h4, fun v hv => ?_⟩
  simpa only [dsigW_eq] using h5 v hv

theorem amp_eq_smul_normalised : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (h : ℝ) (l : A.H → W.Wp) (l' : A.H → W.Wq), haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; 0 < θ → 0 < D.host.ka / gg D → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → GapAtLeast (epsSH D.R) lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) A.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') A.σ W.π' l' → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π A.σ W.μW W.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z' ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π' A.σ W.μW' W.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l v ≠ 0) ∧ (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l' v ≠ 0) ∧ ∃ (w0 : A.H) (η : ℂ), PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ w0 ∧ ‖η‖ = PI.BesselPeriodGGP.fdegH W.μG A.σ w0 * Real.sqrt ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ)) ∧ ∀ (ν : Measure (Mt D.R.k D.R.rS)) (γ : MatKR D.R.k D.R.rS), γ ∈ UH (Hpk D.R.k D.R.rS) → ν {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 → A.J ν γ = η • amp (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) l l' w0 ν γ := by
  intro hH D τ w w' θ W lam A h l l' hθ hka hT hT' hW hA hgap hok hl hl' hbe hbe'
  haveI := FiniteDimensional.complete ℂ W.Wp
  haveI := FiniteDimensional.complete ℂ W.Wq
  obtain ⟨c1, c2, z1, z2, t1, t2, hG, w1, -, w2, -, hN, q1, q2⟩ := hW
  obtain ⟨hlam, hds, b1, b2, hsm0, hv0, ⟨P, hP, hlowK⟩, hc, l1, l2, -⟩ := hA
  set R : Rep D.R.k D.R.rS := ⟨A.H, A.σ⟩ with hR
  have hDS : R.IsDS (epsSH D.R) lam := ⟨hlam, hds⟩
  have hKF : PI.KFinSmooth := hH.1.2.2.1
  obtain ⟨-, -, -, hsm, hTKsm, -, hKT, -, -⟩ := GlobalTheory.rep_basic_of_isDS hKF _ _ _ _ R hDS
  obtain ⟨-, hGm, -⟩ := uHGroup _ _ (det_hpk D.R.k D.R.rS)
  rw [hN] at q1 q2 hbe hbe'
  obtain ⟨U, hS⟩ := sideG_of ENNReal.ofReal_lt_top z1 (t1 ▸ hT) c1 w1 hG q1
  obtain ⟨U', hS'⟩ := sideG_of ENNReal.ofReal_lt_top z2 (t2 ▸ hT') c2 w2 hG q2
  have hcs : ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) ≠ 0 := by
    have : 2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) = 2 * (D.host.ka / gg D) := by
      rw [mul_div_assoc]; rfl
    rw [this]
    exact_mod_cast (by positivity : (0 : ℝ) < 2 * (D.host.ka / gg D)).ne'
  have hn : 0 < ‖A.v0‖ := norm_pos_iff.2 hv0
  set w0 : A.H := ((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0 with hw0
  have hw1 : ‖w0‖ = 1 := by rw [hw0, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hlow : PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ w0 :=
    ⟨P, hP, hw1, Submodule.smul_mem _ _ hlowK⟩
  have hv : A.v0 = ((‖A.v0‖ : ℝ) : ℂ) • w0 := by
    rw [hw0, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  have hwK : R.KFin w0 := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow
  have hvK : R.KFin A.v0 := by
    obtain ⟨S, h1, h2, h3⟩ := hwK
    exact ⟨S, h1, hv ▸ S.smul_mem _ h2, h3⟩
  have hws : w0 ∈ R.sm := hTKsm _ (hKT _ hwK)
  obtain ⟨c₀, hc₀, hdeg⟩ := GlobalTheory.BesselDegree.schur_fdeg hH _ _ (epsSH D.R) W.μG hG
  have hdd := (hdeg lam R hDS).1
  have hd0 : 0 < c₀ * Formalism.QuantumDeterminants.fdegHC lam := mul_pos hc₀ (GlobalTheory.BesselNorm.fdegHC_pos lam hlam.1.injective)
  set dd := c₀ * Formalism.QuantumDeterminants.fdegHC lam
  have hp : (0 : ℝ) < Module.finrank ℂ W.Wp := by
    obtain ⟨g, -, hnt, -⟩ := c1
    exact_mod_cast Module.finrank_pos
  have hq : (0 : ℝ) < Module.finrank ℂ W.Wq := by
    obtain ⟨g, -, hnt, -⟩ := c2
    exact_mod_cast Module.finrank_pos
  obtain ⟨nz1, β, hβ, e1⟩ := one_side hH R (B := A.B) (l := l) hDS hgap hok hS hcs (isBesselMapSm_of b1) hl hbe hvK (mul_pos hc hp) l1 hd0 hdd
  obtain ⟨nz2, β', hβ', e2⟩ := one_side hH R (B := A.B') (l := l') hDS hgap hok hS' hcs (isBesselMapSm_of b2) hl' hbe' hvK (mul_pos hc hq) l2 hd0 hdd
  refine ⟨nz1, nz2, w0, (A.cN : ℂ)⁻¹ * ((β * (‖A.v0‖ : ℝ)) * star (β' * (‖A.v0‖ : ℝ))), hlow, ?_, ?_⟩
  · have hw00 : w0 ≠ 0 := by rw [← norm_pos_iff, hw1]; exact one_pos
    rw [show PI.BesselPeriodGGP.fdegH W.μG A.σ w0 = dd from hdd w0 hw00]
    rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
    simp only [norm_mul, norm_star, norm_inv, Complex.norm_real, norm_norm, Real.norm_of_nonneg hc.le]
    have e1' : ‖β‖ ^ 2 * ‖A.v0‖ ^ 2 = A.cN * Module.finrank ℂ W.Wp * dd := e1.symm
    have e2' : ‖β'‖ ^ 2 * ‖A.v0‖ ^ 2 = A.cN * Module.finrank ℂ W.Wq * dd := e2.symm
    rw [mul_pow, mul_pow, mul_pow, mul_pow, e1', e2']
    field_simp
  · intro ν γ hγ hν
    have hae : ∀ᵐ x ∂ν, Matrix.of x ∈ UH (Hpk D.R.k D.R.rS) := hν
    unfold LocS.J amp ampJ
    rw [Complex.ofReal_one, inv_one, one_smul, mul_smul]
    congr 1
    rw [← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    have a1 : A.Φ (γ * Matrix.of x) = (β * (‖A.v0‖ : ℝ)) • l (A.σ (γ * Matrix.of x) w0) := by
      have hs := hsm _ (hGm _ hγ _ hx) w0 hws
      have hs' := hsm _ (hGm _ hγ _ hx) A.v0 hsm0
      unfold LocS.Φ
      rw [hβ _ hs', mul_smul, ← hl.2.1 _ _ hs, ← map_smul, ← hv]
    have a2 : A.Φ' (Matrix.of x) = (β' * (‖A.v0‖ : ℝ)) • l' (A.σ (Matrix.of x) w0) := by
      have hs := hsm _ hx w0 hws
      have hs' := hsm _ hx A.v0 hsm0
      unfold LocS.Φ'
      rw [hβ' _ hs', mul_smul, ← hl'.2.1 _ _ hs, ← map_smul, ← hv]
    rw [a1, a2]
    ext y
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left, ContinuousLinearMap.smul_apply,
      smul_smul]
    congr 1
    simp only [RCLike.star_def]
    ring

end GlobalTheory.AmpNormal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPeriodPositivityStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_period_positivity : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (h : ℝ) (l : A.H → W.Wp) (l' : A.H → W.Wq), haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; 0 < θ → 0 < D.host.ka / gg D → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → GapAtLeast (epsSH D.R) lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) A.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') A.σ W.π' l' → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π A.σ W.μW W.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z' ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π' A.σ W.μW' W.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l v ≠ 0) ∧ (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l' v ≠ 0) ∧ ∃ (w0 : A.H) (η : ℂ), PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ w0 ∧ ‖η‖ = PI.BesselPeriodGGP.fdegH W.μG A.σ w0 * Real.sqrt ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ)) ∧ ∀ (ν : Measure (Mt D.R.k D.R.rS)) (γ : MatKR D.R.k D.R.rS), γ ∈ UH (Hpk D.R.k D.R.rS) → ν {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 → A.J ν γ = η • amp (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) l l' w0 ν γ := by
  first | exact @GlobalTheory.AmpNormal.amp_eq_smul_normalised | exact GlobalTheory.AmpNormal.amp_eq_smul_normalised | (intros; apply GlobalTheory.AmpNormal.amp_eq_smul_normalised <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceProjectionEqZeroOfPlaceComponentEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceProjectionEqZeroOfPlaceComponentEqZero
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

namespace GlobalTheory.SplitProj

theorem proj_eq_lift_compAt (L : Type) [Field L] [NumberField L] (s : SplitPlace L) (x : AL L) :
    s.proj x = (Algebra.TensorProduct.lift s.i (AlgHom.id _ _) (fun _ _ => Commute.all _ _)) (compAt L s.v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]

theorem proj_eq_zero_of_compAt_eq_zero : ∀ (L : Type) [Field L] [NumberField L] (s : ReciprocityTheory.Aut.SplitPlace L)
    (a : ReciprocityTheory.Aut.AL L), ReciprocityTheory.Aut.compAt L s.v a = 0 → s.proj a = 0 := by
  intro L _ _ s a h
  rw [proj_eq_lift_compAt, h, map_zero]

end GlobalTheory.SplitProj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceProjectionEqZeroOfPlaceComponentEqZeroStatement
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceProjection_eq_zero_of_placeComponent_eq_zero : ∀ (L : Type) [Field L] [NumberField L] (s : ReciprocityTheory.Aut.SplitPlace L) (a : ReciprocityTheory.Aut.AL L), ReciprocityTheory.Aut.compAt L s.v a = 0 → s.proj a = 0 := by
  first | exact @GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero | exact GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero | (intros; apply GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneCountingHypotheses
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneCountingHypotheses
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem one_le_rkR_of_ne {n : ℕ} (ε : Fin n → Bool) {a c : Fin n} (h : ε a ≠ ε c) : 1 ≤ rkR ε := by
  unfold rkR
  rw [le_min_iff]
  constructor
  · refine Finset.card_pos.2 ?_
    cases ha : ε a
    · exact ⟨c, by simpa [ha] using h⟩
    · exact ⟨a, by simp [ha]⟩
  · refine Finset.card_pos.2 ?_
    cases ha : ε a
    · exact ⟨a, by simp [ha]⟩
    · exact ⟨c, by simpa [ha] using h⟩

theorem countHyp_isKTypeOf_lowKSub : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) := by
  intro B Cg n₀ d p q b hn₀ hC v
  obtain ⟨-, -, -, -, -, -, hrk, -, -, -, -, -, h, -, hgap, -, -, h8, -, -⟩ :=
    countHyp_numerics B Cg n₀ d p q b hn₀ hC
  refine GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub _ _ _ _ _ (hC.1 v).1 (hC.1 v).2.1 fun a c hac => ?_
  have hq : (1 : ℝ) ≤ q := by
    have := one_le_rkR_of_ne _ hac
    rw [hrk v] at this
    exact_mod_cast this
  have hg : h ≤ |B.lam v a - B.lam v c| := hgap v a c hac
  have hn : (0 : ℝ) ≤ B.I.n := Nat.cast_nonneg _
  nlinarith

end GlobalTheory.Dec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneCountingHypothesesStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKTypeOf_lowK_of_countHyp : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) := by
  first | exact @GlobalTheory.Dec.countHyp_isKTypeOf_lowKSub | exact GlobalTheory.Dec.countHyp_isKTypeOf_lowKSub | (intros; apply GlobalTheory.Dec.countHyp_isKTypeOf_lowKSub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralIdempotentSplitPlaceCmFiniteAdeles
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralIdempotentSplitPlaceCmFiniteAdeles
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SplitIdem

section Single

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L

open Classical in
def singleAt (v : HeightOneSpectrum (𝓞 L⁺)) (t : v.adicCompletion L⁺) : AFplus L :=
  RestrictedProduct.mk (Pi.single v t) (by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw
    rw [Pi.single_eq_of_ne hw]
    exact zero_mem _)

theorem singleAt_self (v : HeightOneSpectrum (𝓞 L⁺)) (t : v.adicCompletion L⁺) :
    singleAt (L := L) v t v = t := by
  classical
  show Pi.single v t v = t
  exact Pi.single_eq_same v t

theorem singleAt_ne {v w : HeightOneSpectrum (𝓞 L⁺)} (t : v.adicCompletion L⁺) (h : w ≠ v) :
    singleAt (L := L) v t w = 0 := by
  classical
  show Pi.single v t w = 0
  exact Pi.single_eq_of_ne h t

theorem singleAt_int (v : HeightOneSpectrum (𝓞 L⁺)) (t : v.adicCompletion L⁺) (ht : Valued.v t ≤ 1) :
    ∀ w, singleAt (L := L) v t w ∈ w.adicCompletionIntegers L⁺ := by
  intro w
  by_cases h : w = v
  · subst h
    rw [singleAt_self]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ht
  · rw [singleAt_ne t h]
    exact zero_mem _

theorem one_tmul_algebraMap (c : L⁺) :
    ((1 : L) ⊗ₜ[L⁺] algebraMap L⁺ (AFplus L) c : AL L) = (algebraMap L⁺ L c) ⊗ₜ[L⁺] (1 : AFplus L) := by
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]

end Single

theorem exists_idem : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L),
    ∃ ε : ReciprocityTheory.Aut.AL L, ε * ε = ε ∧ ε * ReciprocityTheory.Aut.conjAL L ε = 0 ∧ ε ∈ ReciprocityTheory.Aut.ALint L ∧
      s.proj ε = 1 ∧ ReciprocityTheory.Aut.compAt L s.v (ε + ReciprocityTheory.Aut.conjAL L ε) = 1 ∧
      ∀ v, v ≠ s.v → ReciprocityTheory.Aut.compAt L v ε = 0 ∧ ReciprocityTheory.Aut.compAt L v (ReciprocityTheory.Aut.conjAL L ε) = 0 := by
  intro L _ _ _ s
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep (L := L) s
  set cc := IsCMField.complexConj L with hcc
  set α := s.i (e : L) with hα
  set β := s.i (cc (e : L)) with hβ
  have hαβ : Valued.v (α - β) = 1 := by
    rw [Valuation.map_sub_eq_of_lt_left _ (he'.trans_eq he.symm)]; exact he
  have hne : α - β ≠ 0 := by
    intro h; rw [h, map_zero] at hαβ; exact zero_ne_one hαβ
  set a := (α - β)⁻¹ with ha
  set b := -β * a with hb
  have hva : Valued.v a = 1 := by rw [ha, map_inv₀, hαβ, inv_one]
  have hvb : Valued.v b ≤ 1 := by
    rw [hb, map_mul, Valuation.map_neg, hva, mul_one]; exact he'.le
  have hT : cc ((e : L) + cc (e : L)) = (e : L) + cc (e : L) := by
    rw [map_add (f := _), IsCMField.complexConj_apply_apply, add_comm]
  have hN : cc ((e : L) * cc (e : L)) = (e : L) * cc (e : L) := by
    rw [map_mul, IsCMField.complexConj_apply_apply, mul_comm]
  let T : maximalRealSubfield L := ⟨(e : L) + cc (e : L), (IsCMField.complexConj_eq_self_iff L _).1 hT⟩
  let N : maximalRealSubfield L := ⟨(e : L) * cc (e : L), (IsCMField.complexConj_eq_self_iff L _).1 hN⟩
  have hTL : algebraMap (maximalRealSubfield L) L T = (e : L) + cc (e : L) := rfl
  have hNL : algebraMap (maximalRealSubfield L) L N = (e : L) * cc (e : L) := rfl
  have hTv : algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) T = α + β := by
    rw [hα, hβ, ← map_add (f := _), ← hTL, AlgHom.commutes]
  have hNv : algebraMap (maximalRealSubfield L) (s.v.adicCompletion (maximalRealSubfield L)) N = α * β := by
    rw [hα, hβ, ← map_mul, ← hNL, AlgHom.commutes]
  set A : AFplus L := singleAt s.v a with hA
  set B : AFplus L := singleAt s.v b with hB
  let ι := (Algebra.TensorProduct.includeRight : AFplus L →ₐ[maximalRealSubfield L] AL L)
  have hι : ∀ x : AFplus L, ι x = (1 : L) ⊗ₜ x := fun x => rfl
  set E : AL L := (e : L) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L) with hEdef
  have hinv : (α - β) * a = 1 := mul_inv_cancel₀ hne
  have hE : E * E = ι (algebraMap _ _ T) * E - ι (algebraMap _ _ N) := by
    rw [hι, hι, one_tmul_algebraMap, one_tmul_algebraMap, hEdef, hTL, hNL,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← TensorProduct.sub_tmul]
    congr 1; ring
  have hcE : conjAL L E = ι (algebraMap _ _ T) - E := by
    rw [hι, one_tmul_algebraMap, hTL, hEdef, ← TensorProduct.sub_tmul, add_sub_cancel_left]
    simp [conjAL, Algebra.TensorProduct.map_tmul, hcc]
  have hcι : ∀ x : AFplus L, conjAL L (ι x) = ι x := by
    intro x; rw [hι]; simp [conjAL, Algebra.TensorProduct.map_tmul]

  have ext' : ∀ x y : AFplus L, (∀ w, x w = y w) → x = y := fun x y h => RestrictedProduct.ext _ _ h
  have comp : ∀ w, (A w = 0 ∧ B w = 0) ∨ (w = s.v) := by
    intro w; by_cases h : w = s.v
    · exact Or.inr h
    · exact Or.inl ⟨singleAt_ne a h, singleAt_ne b h⟩
  have hAv : A s.v = a := singleAt_self _ _
  have hBv : B s.v = b := singleAt_self _ _
  have hTw : (algebraMap (maximalRealSubfield L) (AFplus L) T) s.v = α + β := hTv
  have hNw : (algebraMap (maximalRealSubfield L) (AFplus L) N) s.v = α * β := hNv
  have hP : algebraMap _ _ T * A * A + (A * B + A * B) = A := by
    apply ext'; intro w
    rcases comp w with ⟨h1, h2⟩ | rfl
    · show _ * A w * A w + (A w * B w + A w * B w) = A w
      rw [h1, h2]; ring
    · show _ * A s.v * A s.v + (A s.v * B s.v + A s.v * B s.v) = A s.v
      rw [hAv, hBv, hb]; erw [hTw]
      linear_combination a * hinv
  have hQ : B * B - algebraMap _ _ N * A * A = B := by
    apply ext'; intro w
    rcases comp w with ⟨h1, h2⟩ | rfl
    · show B w * B w - _ * A w * A w = B w
      rw [h1, h2]; ring
    · show B s.v * B s.v - _ * A s.v * A s.v = B s.v
      rw [hAv, hBv, hb]; erw [hNw]
      linear_combination (-β * a) * hinv
  have hR : algebraMap _ _ N * A * A + algebraMap _ _ T * A * B + B * B = 0 := by
    apply ext'; intro w
    rcases comp w with ⟨h1, h2⟩ | rfl
    · show _ * A w * A w + _ * A w * B w + B w * B w = 0
      rw [h1, h2]; ring
    · show _ * A s.v * A s.v + _ * A s.v * B s.v + B s.v * B s.v = 0
      rw [hAv, hBv, hb]; erw [hNw, hTw]
      ring
  have hS : (algebraMap _ _ T * A + (B + B) : AFplus L) s.v = 1 := by
    show _ * A s.v + (B s.v + B s.v) = 1
    rw [hAv, hBv, hb]; erw [hTw]
    linear_combination hinv
  have hP' := congrArg ι hP
  have hQ' := congrArg ι hQ
  have hR' := congrArg ι hR
  simp only [map_add (f := _), map_mul, map_sub, map_zero] at hP' hQ' hR'
  have hpE : s.proj E = α := by
    rw [hEdef]; unfold SplitPlace.proj
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, mul_one]
  have hpι : ∀ x : AFplus L, s.proj (ι x) = x s.v := by
    intro x; rw [hι]; unfold SplitPlace.proj
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]; rfl
  have hcomp : ∀ w (x : AFplus L), compAt L w (ι x) = (1 : L) ⊗ₜ (x w) := by
    intro w x; rw [hι]; unfold compAt
    erw [Algebra.TensorProduct.map_tmul]
    rfl
  have hconjε : conjAL L (E * ι A + ι B) = (ι (algebraMap _ _ T) - E) * ι A + ι B := by
    rw [map_add (f := _), map_mul, hcE, hcι, hcι]
  refine ⟨E * ι A + ι B, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (ι A) ^ 2 * hE + E * hP' + hQ'
  · rw [hconjε]
    linear_combination (-(ι A) ^ 2) * hE + hR'
  · refine Subring.add_mem _ (Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨e, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨A, singleAt_int _ _ hva.le, rfl⟩)))
      (Subring.subset_closure (Or.inr ⟨B, singleAt_int _ _ hvb, rfl⟩))
  · rw [map_add (f := _), map_mul, hpE, hpι, hpι, hAv, hBv, hb]
    linear_combination hinv
  · have h : E * ι A + ι B + conjAL L (E * ι A + ι B) = ι (algebraMap _ _ T * A + (B + B)) := by
      rw [hconjε]; simp only [map_add (f := _), map_mul]; ring
    rw [h, hcomp, hS]; rfl
  · intro w hw
    rcases comp w with ⟨h1, h2⟩ | h
    · refine ⟨?_, ?_⟩
      · rw [map_add (f := _), map_mul, hcomp, hcomp, h1, h2]; simp
      · rw [hconjε, map_add (f := _), map_mul, hcomp, hcomp, h1, h2]; simp
    · exact absurd h hw

end GlobalTheory.SplitIdem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralIdempotentSplitPlaceCmFiniteAdelesStatement
open NumberField IsDedekindDomain ReciprocityTheory.Aut
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralIdempotent_splitPlace_cmFiniteAdeles : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L), ∃ ε : ReciprocityTheory.Aut.AL L, ε * ε = ε ∧ ε * ReciprocityTheory.Aut.conjAL L ε = 0 ∧ ε ∈ ReciprocityTheory.Aut.ALint L ∧ s.proj ε = 1 ∧ ReciprocityTheory.Aut.compAt L s.v (ε + ReciprocityTheory.Aut.conjAL L ε) = 1 ∧ ∀ v, v ≠ s.v → ReciprocityTheory.Aut.compAt L v ε = 0 ∧ ReciprocityTheory.Aut.compAt L v (ReciprocityTheory.Aut.conjAL L ε) = 0 := by
  first | exact @GlobalTheory.SplitIdem.exists_idem | exact GlobalTheory.SplitIdem.exists_idem | (intros; apply GlobalTheory.SplitIdem.exists_idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalLatticeOverLocalInnerData
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalLatticeOverLocalInnerData
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.GlueOver

theorem exists_locOver : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (d0 : Dat Z FP), (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ {p | ¬ ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ ∧ τ.abelian₂ = lattice₂ D Z.M p Λ₀}.Finite) → ∃ Λ : LV D, LocOver Λ d0 := by
  intro D Z FP d0 hT hΛ
  obtain ⟨Λ₀, hΛ₀, hfin⟩ := hΛ
  have hc : ∀ p, ∃ τ : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (d0 p) τ ∧
      ((∃ τ' : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (d0 p) τ' ∧ τ'.abelian₂ = lattice₂ D Z.M p Λ₀) →
        τ.abelian₂ = lattice₂ D Z.M p Λ₀) := by
    intro p
    by_cases h : ∃ τ' : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (d0 p) τ' ∧ τ'.abelian₂ = lattice₂ D Z.M p Λ₀
    · obtain ⟨τ', h1, h2⟩ := h
      exact ⟨τ', h1, fun _ => h2⟩
    · obtain ⟨τ', h1⟩ := hT p
      exact ⟨τ', h1, fun h' => absurd h' h⟩
  choose τ hτ hτ' using hc
  haveI : Infinite (PlF D) := GlobalTheory.LvT.Inh.ResFin.infinite_places D.host.F
  obtain ⟨p, hp⟩ := Infinite.exists_notMem_finset hfin.toFinset
  have hp' : ∃ t, LocNG.IsTermOver (FP p) (d0 p) t ∧ t.abelian₂ = lattice₂ D Z.M p Λ₀ := by
    by_contra h
    exact hp (hfin.mem_toFinset.mpr h)
  obtain ⟨t, ht, heq⟩ := hp'
  have hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ₀ : Set (Vp D p)) = ⊤ := by
    rw [← heq]
    exact (GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (d0 p) t ht).2
  have hfull : Submodule.IsFullLattice D.host.E Λ₀ := by
    let U := Submodule.span D.host.E (Λ₀ : Set (VS D).V)
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
    refine { toIsLattice := hΛ₀, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
    rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
    simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
      finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)
  obtain ⟨Λ, hΛ, heq⟩ := (GlobalTheory.Unfold.LatLoc.lattices_local_global D Z).2 Λ₀ hfull (fun p => (τ p).abelian₂)
    (fun p => GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (d0 p) (τ p) (hτ p))
    (hfin.subset (fun p hp h => hp (hτ' p h)))
  exact ⟨Λ, hΛ, fun p => ⟨τ p, hτ p, (heq p).symm⟩⟩

end GlobalTheory.Unfold.GlueOver
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalLatticeOverLocalInnerDataStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalLattice_over_localInnerData : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (d0 : Dat Z FP), (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ {p | ¬ ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ ∧ τ.abelian₂ = lattice₂ D Z.M p Λ₀}.Finite) → ∃ Λ : LV D, LocOver Λ d0 := by
  first | exact @GlobalTheory.Unfold.GlueOver.exists_locOver | exact GlobalTheory.Unfold.GlueOver.exists_locOver | (intros; apply GlobalTheory.Unfold.GlueOver.exists_locOver <;> assumption)
end
end
