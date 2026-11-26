module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowUnfoldingBasicHypotheses
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedProductDependsOnDataProduct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorLatticeFixedLargeDepth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandBesselPeriodInvariantProof
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefinitePeriodDependsOnProductFunction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnermostIntegrandLeftPeriodInvariantLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatBFSource
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.Unf.FB GlobalTheory.FinPl.HandInvPf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesMove

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem qS_xZero {S S₀ T T₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (d' : HypDec T T₀ ρ) (c : skewA D ρ) (w : Mx D ρ ρ) :
    d.qS T c (xZero d' ⬝ w) = 0 := by
  have h : adj (xZero d' ⬝ w) ⬝ (gA T ⬝ (xZero d' ⬝ w)) = 0 := by
    rw [xZero, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA T), ← Matrix.mul_assoc (adj d'.jX), d'.gram_XX,
      Matrix.zero_mul, Matrix.mul_zero]
  rw [← cenS_nC, ← neg_inj, LinkPoint.neg_cenS_eq, h, Matrix.zero_mul, trace_zero, map_zero, neg_zero]


set_option maxHeartbeats 1000000 in
theorem flatBF_source {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {Ψ : WO B.V J.W → ℂ}
    (hΨ : IsThetaFunO ψ B.V J.W Ψ) {n : GA D B.V} (hn : n ∈ flagN B.d) :
    flatBF s (s.om (n, 1) Ψ) = psiBes ψ B.d 1 (vecB B.o B.ζ) n • flatBF s Ψ := by
  have hψ := s.weil.std
  obtain ⟨u, hu, b, c, rfl⟩ := GlobalTheory.MixPer.Decomp.flag_decomp B.d hn
  obtain ⟨om', hom'⟩ := (GlobalTheory.Desc.weil_data_descend D ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  have FS := fun f hf => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have MV := fun x => (GlobalTheory.T.mixedCoordinates_of_thetaFunction_are_thetaFunctions D ψ hψ).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  have hfl : psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.levi u * (B.d.nB b * B.d.nC c)) =
      psiUni ψ u * psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b) := by
    rw [psiBes_mul B.d ψ 1 _ (B.d.levi_mem_NFlag hu) (mul_mem (B.d.nB_mem_NFlag b) (B.d.nC_mem_NFlag c)),
      psiBes_mul B.d ψ 1 _ (B.d.nB_mem_NFlag b) (B.d.nC_mem_NFlag c), psiBes_nC, mul_one, psiBes_levi]
  have hdet : Matrix.GeneralLinearGroup.det u = 1 := by
    have bt : Matrix.BlockTriangular u.1 id := fun a b h => (hu a b).1 h
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular bt, Units.val_one]
    exact Finset.prod_eq_one fun i _ => (hu i i).2
  have hmod : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod J.W.rank u = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, hdet, map_one, NNReal.coe_one, Real.one_rpow]
  have h1 := s.weil.om_pres (B.d.nC c, 1) Ψ hΨ
  have h2 := s.weil.om_pres (B.d.nB b, 1) _ h1
  have e : s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ =
      s.om (B.d.levi u, 1) (s.om (B.d.nB b, 1) (s.om (B.d.nC c, 1) Ψ)) := by
    rw [← om_mul, ← om_mul, mul_assoc, mul_one, mul_one]
  let u' : UX D ρ := ⟨u, hu⟩
  have key : ∀ v : UX D ρ,
      evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ) (xZero J.d ⬝ v.1.1)
          (yZero B.V₀ ρ (vecB B.o B.ζ)) =
        psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b) •
          evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := by
    intro v
    have ex : xZero J.d ⬝ v.1.1 ⬝ u.1 = xZero J.d ⬝ (v * u').1.1 := by
      rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
    have t1 := (FS _ h2).levi u (xZero J.d ⬝ v.1.1)
    rw [hdet, hmod, map_one, inv_one, Circle.coe_one, Complex.ofReal_one, mul_one, one_smul, ex] at t1
    have t2 := (FS _ h1).unip b (xZero J.d ⬝ (v * u').1.1)
    rw [Matrix.mul_assoc (xZero J.d)] at t2
    have t3 : B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 (s.om (B.d.nC c, 1) Ψ) (xZero J.d ⬝ (v * u').1.1) =
        ψ (B.d.qS J.W c (xZero J.d ⬝ (v * u').1.1)) • B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) :=
      (FS _ hΨ).centre c _
    rw [qS_xZero, AddChar.map_zero_eq_one, one_smul] at t3
    have t4 := (GlobalTheory.T.heisenbergThetaMixedModelTarget_of_mixedModel D ψ hψ B.V₀ J.W J.W₀ ρ J.d s.vT.μ s.vT.𝓕 s.vT.covol _ (MV (xZero J.d ⬝ (v * u').1.1))).1
      ((v * u').1.1 ⬝ b) (yZero B.V₀ ρ (vecB B.o B.ζ))
    have t5 : ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ ((v * u').1.1 ⬝ b))) =
        psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b) := by
      refine (psi_yZero ψ B.d J.d _ _).trans ?_
      rw [psiBes_nB, psiBes_nB, ← Matrix.mulVec_mulVec, dotProduct_mulVec (ell D ρ) (v * u').1.1, ell_vecMul (v * u').2]
    rw [t5] at t4
    unfold evalAt
    rw [e]
    change I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target J.d B.V₀ ψ s.vT.μ s.vT.𝓕
      (I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source B.d J.W ψ s.vS.μ s.vS.𝓕 _ _) _ = _
    rw [t1, t2]
    change I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source B.d J.W ψ s.vS.μ s.vS.𝓕
      (s.om (B.d.nC c, 1) Ψ) (xZero J.d ⬝ (v * u').1.1) =
      I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source B.d J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) at t3
    rw [t3]
    exact t4
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.UnitU.topology D ρ
  have := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).2.2 _ s.vU.unit
  have hmul : ∀ v : UX D ρ, psiUni ψ (v * u').1 = psiUni ψ v.1 * psiUni ψ u := fun v => by
    rw [← ThLaws.psiFlag_levi ψ J.d, ← ThLaws.psiFlag_levi ψ J.d, ← ThLaws.psiFlag_levi ψ J.d, Subgroup.coe_mul, map_mul,
      psiFlag_mul J.d ψ (J.d.levi_mem_NFlag v.2) (J.d.levi_mem_NFlag hu)]
  have hu1 : psiUni ψ u * star (psiUni ψ u) = 1 := mul_star_psi hψ _
  funext w
  rw [hfl]
  simp only [Pi.smul_apply, smul_eq_mul]
  change ∫ v, star (psiUni ψ v.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕
      (s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ) (xZero J.d ⬝ v.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν = _ *
    ∫ v, star (psiUni ψ v.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ v.1.1)
      (yZero B.V₀ ρ (vecB B.o B.ζ)) w ∂s.vU.ν
  conv_rhs => rw [← integral_mul_right_eq_self _ u', ← integral_const_mul]
  congr 1
  funext v
  rw [key, hmul, star_mul']
  simp only [Pi.smul_apply, smul_eq_mul]
  generalize evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) _ _ = z
  linear_combination (-(star (psiUni ψ v.1) * psiBes ψ B.d 1 (vecB B.o B.ζ) (B.d.nB b) * z)) * hu1

theorem flatBF_bes {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {Φ : WO B.V J.W → ℂ}
    (hΦ : IsThetaFunO ψ B.V J.W Φ) {n : GA D B.V} (hn : n ∈ flagN B.d) (a : GA D B.A) (g : GA D B.V) (h : GA D J.W) :
    flatBF s (s.om (n * embA B.d B.o a * g, h) Φ) =
      psiBes ψ B.d 1 (vecB B.o B.ζ) n • s.om₀ (B.o.emb (a, 1), 1) (flatBF s (s.om (g, h) Φ)) := by
  obtain ⟨om', hom'⟩ := (GlobalTheory.Desc.weil_data_descend D ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  have hΨ := s.weil.om_pres (g, h) Φ hΦ
  have c := GlobalTheory.T.besselToJacobiFlatSchwartz_equivariant D ψ _ B J s om' hom' _ hΨ a 1 (one_mem _) 1
  have p1 : psiFlag ψ J.d 1 = 1 := by
    have := psiFlag_levi_mul ψ J.d 1 (one_mem (stabX J.d))
    rw [map_one, mul_one] at this
    rw [this, psiUni, Units.val_one, upSum_one, psiE_zero]
  rw [map_one, mul_one, p1, star_one, one_smul, opA, jacT_one, id, show s.om₀ (1, 1) = 1 from map_one _,
    Module.End.one_apply] at c
  rw [← c, ← flatBF_source s (s.weil.om_pres _ _ hΨ) hn, ← om_mul, ← om_mul, one_mul, one_mul]

theorem om_rat_line {V₀ A L S : HSp D} (o : OrthDec V₀ A L) {χ χ' : (AE D)ˣ →* Circle} {om : Om V₀ S}
    (hom : IsWeilDatumO ψ V₀ S χ χ' om) {γ : GA D A} (hγ : γ ∈ GQ A) {f : WO V₀ S → ℂ} (hf : IsThetaFunO ψ V₀ S f) (y : WO L S) :
    om (o.emb (γ, 1), 1) f ((o.resS S).symm (0, y)) = f ((o.resS S).symm (0, y)) := by
  have hact : actO V₀ S (o.emb (γ, 1)) 1 ((o.resS S).symm (0, y)) = (o.resS S).symm (0, y) := by
    apply (o.resS S).injective
    rw [o.resS_actO, AddEquiv.apply_symm_apply]
    simp only [actO_eq, inv_one, mt_one, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul]
  have h0 : ∀ F : WO V₀ S → ℂ, ∀ p, heisO ψ V₀ S p F 0 = F p := fun F p => by
    rw [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]
  have h1 := congrFun (hom.om_heis (o.emb (γ, 1)) 1 ((o.resS S).symm (0, y)) f hf) 0
  rw [hact, h0] at h1
  rw [← h1, hom.om_aut _ (o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hom.std hf _), h0]

theorem handBF_move {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {L' : HSp D} {ζ' : Fin L'.rank → D.host.E}
    (l : Link B L' ζ') {φ : GA D B.A → ℂ} (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g) {Ξ : WO B.V₀ J.W₀ → ℂ}
    (hΞ : IsThetaFunO ψ B.V₀ J.W₀ Ξ) (c : ℂ) (hc : c * star c = 1) (a : GA D B.A) :
    handBF s l (star c • rTrans a φ) (c • s.om₀ (B.o.emb (a, 1), 1) Ξ) = handBF s l φ Ξ := by
  funext h w
  unfold handBF
  congr 1
  rw [← GlobalTheory.ChainOnto.setIntegral_fd_mul_right D B.A B.vA.μ B.vA.𝓕 B.vA.haar B.vA.fund
    (fun h₀ => φ h₀ * s.om₀ (B.o.emb (h₀, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))) ?_ a]
  · congr 1
    funext x
    rw [map_smul, ← om_mul, ← map_mul, Prod.mk_mul_mk, mul_one, mul_one]
    simp only [Pi.smul_apply, smul_eq_mul, rTrans]
    linear_combination (φ (x * a) * s.om₀ (B.o.emb (x * a, 1), h) Ξ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w))) * hc
  · intro γ hγ x
    have e : s.om₀ (B.o.emb (γ * x, 1), h) Ξ = s.om₀ (B.o.emb (γ, 1), 1) (s.om₀ (B.o.emb (x, 1), h) Ξ) := by
      rw [← om_mul, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    simp only [hφ γ hγ]
    rw [e, om_rat_line B.o s.weil₀ hγ (s.weil₀.om_pres _ _ hΞ)]

theorem hand_right {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} (s₁ : StepBF ψ B J)
    (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (Φ₁ : WO B.V J.W → ℂ) {Φ₂ : WO J.W B'.V → ℂ}
    (hΦ₂ : IsThetaFunO ψ J.W B'.V Φ₂) (φ : GA D B.A → ℂ) (g : GA D B.V) (h₁ : GA D J.W) (h₂ : GA D B'.V)
    {n : GA D B'.V} (hn : n ∈ flagN B'.d) (a : GA D B'.A) :
    Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ (n * embA B'.d B'.o a * h₂) =
      star (psiBes ψ B'.d 1 (vecB B'.o B'.ζ) n) • rTrans a (Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂) := by
  have hD : Descent D := GlobalTheory.Desc.weil_data_descend D
  have hΨ₂ := s₂.weil.om_pres (h₁, h₂) Φ₂ hΦ₂
  have e : flatFB s₂ (s₂.om (h₁, n * embA B'.d B'.o a * h₂) Φ₂) = star (psiBes ψ B'.d 1 (vecB B'.o B'.ζ) n) •
      s₂.om₀ (1, B'.o.emb (a, 1)) (flatFB s₂ (s₂.om (h₁, h₂) Φ₂)) := by
    have c := GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction D hD ψ σ J B' s₂ _ hΨ₂ 1 a
    rw [map_one] at c
    rw [← c, ← GlobalTheory.T.flatSchwartz_targetUnipotent_conj_besselCharacter D hD ψ σ J B' s₂ _ (s₂.weil.om_pres _ _ hΨ₂) n hn, ← om_mul, ← om_mul, one_mul, one_mul]
  unfold Chain.hand
  rw [e, handFB_smul_om]

theorem hand_left {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} (s₁ : StepBF ψ B J)
    (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) {Φ₁ : WO B.V J.W → ℂ} (Φ₂ : WO J.W B'.V → ℂ)
    (hΦ₁ : IsThetaFunO ψ B.V J.W Φ₁) {φ : GA D B.A → ℂ} (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g)
    (g : GA D B.V) (h₁ : GA D J.W) (h₂ : GA D B'.V) {n : GA D B.V} (hn : n ∈ flagN B.d) (a : GA D B.A) :
    Chain.hand s₁ s₂ l vL Φ₁ Φ₂ (star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) • rTrans a φ) (n * embA B.d B.o a * g) h₁ h₂ =
      Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ h₂ := by
  have hΞ := (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) ψ).1 _ B J s₁ _ (s₁.weil.om_pres (g, h₁) Φ₁ hΦ₁)
  unfold Chain.hand
  rw [flatBF_bes s₁ hΦ₁ hn, handBF_move s₁ l hφ hΞ (psiBes ψ B.d 1 (vecB B.o B.ζ) n) (mul_star_psi s₁.weil.std _)]

theorem biLift_last {V₀ A L S X T L'' : HSp D} (o : OrthDec V₀ A L) (o'' : OrthDec X T L'')
    (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) {χA χz χS : (AE D)ˣ →* Circle} {om₁ : Om V₀ S} {oma : Om A S} {omz : Om L S}
    (h₁ : IsWeilDatumO ψ V₀ S (χA * χz) χS om₁) (ha : IsWeilDatumO ψ A S χA χS oma) (hz : IsWeilDatumO ψ L S χz χS omz)
    (omb : Om S X) (vA : Vol A) (vS : Vol S) {φ : GA D A → ℂ} (hφ : ∀ γ ∈ GQ A, ∀ g, φ (γ * g) = φ g) {Ξ : WO V₀ S → ℂ}
    (hΞ : IsThetaFunO ψ V₀ S Ξ) (Φ₂ : WO S T → ℂ) (c : ℂ) (hc : c * star c = 1) (a : GA D A) :
    GlobalTheory.SeeSaw.biLift oma omb vA vS (star c • rTrans a φ) (GlobalTheory.FinPl.lastBi o o'' τ (c • om₁ (o.emb (a, 1), 1) Ξ) Φ₂) =
      GlobalTheory.SeeSaw.biLift oma omb vA vS φ (GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂) := by
  have hsrc := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ h₁.std V₀ A L o S
  have e0 : ∀ v, (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) =
      Φ₂ (o''.resT S v).1 • fun u => Ξ ((o.resS S).symm (u, GlobalTheory.FinPl.kap τ S (o''.resT S v).2)) := fun v => rfl
  have e1 : ∀ v, (fun u => GlobalTheory.FinPl.lastBi o o'' τ (c • om₁ (o.emb (a, 1), 1) Ξ) Φ₂ u v) =
      c • oma (a, 1) fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v := fun v => by
    funext u
    have k := (hsrc.om_slice χA χz χS om₁ oma omz h₁ ha hz a 1 1 Ξ hΞ (GlobalTheory.FinPl.kap τ S (o''.resT S v).2)).2 u
    rw [show omz (1, 1) = 1 from map_one _] at k
    simp only [Module.End.one_apply] at k
    rw [e0, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.FinPl.lastBi, OrthDec.boxT, k]
    ring
  funext h₂
  unfold GlobalTheory.SeeSaw.biLift
  congr 1
  funext h
  rw [← GlobalTheory.ChainOnto.setIntegral_fd_mul_right D A vA.μ vA.𝓕 vA.haar vA.fund
    (fun h₀ => φ h₀ * omb (h, h₂) (fun v => oma (h₀, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0) 0) ?_ a]
  · congr 1
    funext x
    have e2 : (fun v => oma (x, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ (c • om₁ (o.emb (a, 1), 1) Ξ) Φ₂ u v) 0) =
        c • fun v => oma (x * a, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0 := by
      funext v
      rw [e1, map_smul, ← om_mul, mul_one]
      rfl
    rw [e2, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, rTrans]
    linear_combination (φ (x * a) * omb (h, h₂) (fun v => oma (x * a, h)
      (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0) 0) * hc
  · intro γ hγ x
    have e : ∀ v, oma (γ * x, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0 =
        oma (x, h) (fun u => GlobalTheory.FinPl.lastBi o o'' τ Ξ Φ₂ u v) 0 := fun v => by
      have k := ha.om_aut γ hγ 1 (one_mem _) _
        (ha.om_pres (x, h) _ ((hsrc.slice_theta Ξ hΞ).1 (GlobalTheory.FinPl.kap τ S (o''.resT S v).2)))
      rw [← om_mul, one_mul] at k
      rw [e0, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, k]
    simp only [hφ γ hγ, e]

end GlobalTheory.BesMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnermostIntegrandLeftPeriodInvariantLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLeftInv

section Steps

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem rowGrp_odd (j σ : ℕ) (hj : j + 2 * σ + 1 = D.R.m) :
    rowGrp G j = jacGrp (rowJac G j (by omega) σ (by omega)) := by
  obtain rfl : σ = (D.R.m - 1 - j) / 2 := by omega
  exact dif_pos hj

theorem rowGrp_even (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) :
    rowGrp G j = besGrp (besDecAt G j σ hj) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  obtain rfl : σ = (D.R.m - 2 - j) / 2 := by omega
  unfold rowGrp
  rw [dif_neg (by omega), dif_pos hj]

variable (W : G.Weil) {t : T} {M : GlobalTheory.FunObj.Vol G} (hM : M.Is t)

abbrev handAt (j σ : ℕ) (hj : j + 2 * (σ + 1) + 2 = D.R.m) (Φ : SchDown G t) (φ : GA D (G.V (.top j)) → ℂ)
    (g : GA D (G.V (.grid D.R.m j))) (h₁ : GA D (G.V (.grid D.R.m (j + 1)))) (h₂ : GA D (G.V (.grid D.R.m (j + 1 + 1)))) :
    GA D (G.V (.top (j + 1 + 1))) → ℂ :=
  GlobalTheory.Unf.Chain.hand (stepAt G W t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
    (stepAt G W t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega)))
    (linkAt hM j σ hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
    ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
    (B := besAt G hM j (σ + 1) hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (J := jacAt G hM (j + 1) (σ + 1) (by omega))
    (B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
    (Φ ⟨j, by omega⟩) (Φ ⟨j + 1, by omega⟩) φ g h₁ h₂

theorem biL_conAt (j σ : ℕ) (hj : j + 2 * (σ + 1) + 2 = D.R.m) (Φ : SchDown G t) (hΦ : ∀ j, IsThetaFunO W.ψ _ _ (Φ j))
    (φ : GA D (G.V (.top j)) → ℂ) (hφ : GlobalTheory.Unf.IsContAut _ φ) (h : Pts G) :
    biL W M t j φ (conAt W hM Φ h j) = handAt W hM j σ hj Φ φ (h j) (h (j + 1)) (h (j + 1 + 1)) := by
  obtain rfl : σ = (D.R.m - 4 - j) / 2 := by omega
  refine Eq.trans ?_ (dbl_hand_eq_biLift G W t hM _ j hj _ _ _ φ (hΦ ⟨j, by omega⟩) (hΦ ⟨j + 1, by omega⟩) hφ _ _ _).symm
  have e : conAt W hM Φ h j = _ := (dif_neg (by omega)).trans (dif_pos hj)
  rw [e]
  rfl

theorem handAt_contAut (j σ : ℕ) (hj : j + 2 * (σ + 1) + 2 = D.R.m) (Φ : SchDown G t) (hΦ : ∀ j, IsThetaFunO W.ψ _ _ (Φ j))
    (φ : GA D (G.V (.top j)) → ℂ) (hφ : GlobalTheory.Unf.IsContAut _ φ) (g h₁ h₂) :
    GlobalTheory.Unf.IsContAut _ (handAt W hM j σ hj Φ φ g h₁ h₂) := by
  let B := besAt G hM j (σ + 1) hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some
  let J := jacAt G hM (j + 1) (σ + 1) (by omega)
  let B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN (besDecAt G (j + 1 + 1) σ (by omega))).some
  let s₁ : GlobalTheory.Unf.StepBF W.ψ B J :=
    stepAt G W t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
  let s₂ : GlobalTheory.Unf.StepFB W.ψ J B' :=
    stepAt G W t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega))
  have t₁ : IsThetaFunO W.ψ B.V₀ J.W₀ (GlobalTheory.Unf.flatBF s₁ (s₁.om (g, h₁) (Φ ⟨j, by omega⟩))) :=
    (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) W.ψ).1 _ B J s₁ _ (s₁.weil.om_pres (g, h₁) _ (hΦ ⟨j, by omega⟩))
  have t₂ : IsThetaFunO W.ψ J.W₀ B'.V₀ (GlobalTheory.Unf.flatFB s₂ (s₂.om (h₁, h₂) (Φ ⟨j + 1, by omega⟩))) :=
    (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) W.ψ).2 _ J B' s₂ _
      (s₂.weil.om_pres (h₁, h₂) _ (hΦ ⟨j + 1, by omega⟩))
  exact GlobalTheory.FinPl.ValDbl.contAut_hand0 s₁ s₂ (linkAt hM j σ hj _ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
    ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some) hφ t₁ t₂

theorem biL_contAut (Φ : SchDown G t) (hΦ : ∀ j, IsThetaFunO W.ψ _ _ (Φ j)) (h : Pts G) (i : ℕ) (hi : Even i) (hm : i + 2 < D.R.m)
    (ψ : GA D (G.V (.top i)) → ℂ) (hψ : GlobalTheory.Unf.IsContAut _ ψ) : GlobalTheory.Unf.IsContAut _ (biL W M t i ψ (conAt W hM Φ h i)) := by
  obtain ⟨a, ha⟩ := D.R.m_even
  obtain ⟨b, hb⟩ := hi
  rw [biL_conAt W hM i (a - b - 2) (by omega) Φ hΦ ψ hψ]
  exact handAt_contAut W hM _ _ _ Φ hΦ ψ hψ _ _ _

theorem odd_step (Φ : SchDown G t) (hΦ : ∀ j, IsThetaFunO W.ψ _ _ (Φ j)) (h : Pts G) (i σ : ℕ)
    (hi : i + 2 * (σ + 1) + 2 = D.R.m) (r) (hr : r ∈ rowGrp G (i + 1)) (ψ : GA D (G.V (.top i)) → ℂ)
    (hψ : GlobalTheory.Unf.IsContAut _ ψ) :
    biL W M t i ψ (conAt W hM Φ (Function.update h (i + 1) (r * h (i + 1))) i) = biL W M t i ψ (conAt W hM Φ h i) := by
  rw [biL_conAt W hM i σ hi Φ hΦ ψ hψ, biL_conAt W hM i σ hi Φ hΦ ψ hψ, Function.update_self,
    Function.update_of_ne (show i ≠ i + 1 by omega), Function.update_of_ne (show i + 1 + 1 ≠ i + 1 by omega)]
  rw [rowGrp_odd (i + 1) (σ + 1) (by omega)] at hr
  exact (GlobalTheory.FinPl.HandInvPf.handInv D W.ψ σ (besAt G hM i (σ + 1) hi (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
    (jacAt G hM (i + 1) (σ + 1) (by omega)) (besAt G hM (i + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
    _ _ _ _ _ _ (hΦ ⟨i, by omega⟩) (hΦ ⟨i + 1, by omega⟩) ψ hψ _ _ _).1 r hr

theorem even_first (Φ : SchDown G t) (hΦ : ∀ j, IsThetaFunO W.ψ _ _ (Φ j)) (h : Pts G) (i σ : ℕ)
    (hi : i + 2 * (σ + 1) + 2 = D.R.m) (hi' : i + 1 + 1 + 2 * σ + 2 = D.R.m) (n) (hn : n ∈ flagN (besDecAt G (i + 1 + 1) σ hi')) (a)
    (ψ : GA D (G.V (.top i)) → ℂ) (hψ : GlobalTheory.Unf.IsContAut _ ψ) :
    biL W M t i ψ (conAt W hM Φ (Function.update h (i + 1 + 1)
        (n * embA (besDecAt G (i + 1 + 1) σ hi') (GlobalTheory.OrthSumExists.orthDecHsum D _ _) a * h (i + 1 + 1))) i) =
      star (psiBes W.ψ (besDecAt G (i + 1 + 1) σ hi') 1
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D _ _) fun _ => D.host.xi0 ^ σ) n) • rTrans a (biL W M t i ψ (conAt W hM Φ h i)) := by
  rw [biL_conAt W hM i σ hi Φ hΦ ψ hψ, biL_conAt W hM i σ hi Φ hΦ ψ hψ, Function.update_self,
    Function.update_of_ne (show i ≠ i + 1 + 1 by omega), Function.update_of_ne (show i + 1 ≠ i + 1 + 1 by omega)]
  exact GlobalTheory.BesMove.hand_right (B := besAt G hM i (σ + 1) hi (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
    (J := jacAt G hM (i + 1) (σ + 1) (by omega)) (B' := besAt G hM (i + 1 + 1) σ hi' (GlobalTheory.Unf.Inhab.nonempty_volN _).some) _ _ _ _ _
    (hΦ ⟨i + 1, by omega⟩) ψ _ _ _ hn a

theorem even_second (Φ : SchDown G t) (hΦ : ∀ j, IsThetaFunO W.ψ _ _ (Φ j)) (h : Pts G) (j σ : ℕ)
    (hj : j + 2 * σ + 2 = D.R.m) (n) (hn : n ∈ flagN (besDecAt G j σ hj)) (a)
    (φ : GA D (G.V (.top j)) → ℂ) (hφ : GlobalTheory.Unf.IsContAut _ φ) :
    biL W M t j (star (psiBes W.ψ (besDecAt G j σ hj) 1
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D _ _) fun _ => D.host.xi0 ^ σ) n) • rTrans a φ)
      (conAt W hM Φ (Function.update h j (n * embA (besDecAt G j σ hj) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) a * h j)) j) =
      biL W M t j φ (conAt W hM Φ h j) := by
  rcases σ with _ | σ
  · have e : ∀ h' : Pts G, conAt W hM Φ h' j = lastDat W hM j hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some (h' j) (Φ ⟨j, by omega⟩)
        (castSch G (show j + 1 + 1 = D.R.m by omega) (Φ ⟨j + 1, by omega⟩)) := fun h' => dif_pos hj
    rw [e, e, Function.update_self]
    obtain ⟨χz, hzH, hzE, -, -, hodd⟩ := GlobalTheory.T.thetaGrid_lastRow_column_characters_differ G W t
    obtain ⟨hS0, hT0⟩ := hodd j (by omega) (by omega)
    let B := besAt G hM j 0 hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    let s := (lastAt G W t hM j hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some).s
    have homa : IsWeilDatumO W.ψ (G.V (.top j)) (G.V (.top (j + 1))) (G.chrS (.top t j)) (G.chrT (.top t j))
        (W.om (.top t j)) := W.om_is (.top t j) (by show j + 1 ≤ D.R.m; omega)
    have hom₁ : IsWeilDatumO W.ψ B.V₀ (G.V (.top (j + 1))) (G.chrS (.top t j) * χz) (G.chrT (.top t j)) s.om₀ := by
      rw [← hS0, ← hT0]; exact s.weil₀
    obtain ⟨omz, homz⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (GlobalTheory.SeeSaw.Model.nLine D) (G.V (.top (j + 1))) W.ψ χz
      (G.chrT (.top t j)) W.ψ_std hzH homa.hecT hzE homa.resT
    have hΞ := (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) W.ψ).1 _ B _ s _
      (s.weil.om_pres (h j, 1) _ (hΦ ⟨j, by omega⟩))
    have k := GlobalTheory.BesMove.flatBF_bes (B := B) s (hΦ ⟨j, by omega⟩) hn a (h j) 1
    have k' := GlobalTheory.BesMove.biLift_last B.o (topOrthAt G (show D.R.m = j + 1 + 1 by omega)) lastTau hom₁ homa homz
      (W.om (.top t (j + 1))) (volAt hM (.top j) (by show j ≤ D.R.m; omega))
      (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) hφ.1 hΞ
      (fun w => castSch G (show j + 1 + 1 = D.R.m by omega) (Φ ⟨j + 1, by omega⟩)
        ((rowJac G (j + 1) (by omega) 0 (by omega)).ext0 _ w))
      (psiBes W.ψ B.d 1 (vecB B.o B.ζ) n) (GlobalTheory.FinPl.HandInvPf.mul_star_psi W.ψ_std _) a
    erw [← k] at k'
    exact k'
  · obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top j))
    have hφ' : GlobalTheory.Unf.IsContAut _ (star (psiBes W.ψ (besDecAt G j (σ + 1) hj) 1
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D _ _) fun _ => D.host.xi0 ^ (σ + 1)) n) • rTrans a φ) :=
      ⟨fun γ hγ x => by simp only [Pi.smul_apply, rTrans, mul_assoc, hφ.1 γ hγ],
        (hφ.2.comp (continuous_mul_const a)).const_smul _⟩
    rw [biL_conAt W hM j σ hj Φ hΦ _ hφ', biL_conAt W hM j σ hj Φ hΦ φ hφ, Function.update_self,
      Function.update_of_ne (show j + 1 ≠ j by omega), Function.update_of_ne (show j + 1 + 1 ≠ j by omega)]
    exact GlobalTheory.BesMove.hand_left (B := besAt G hM j (σ + 1) hj (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (J := jacAt G hM (j + 1) (σ + 1) (by omega))
      (B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) _ _ _ _ _
      (hΦ ⟨j, by omega⟩) hφ.1 _ _ _ hn a

theorem even_step (Φ : SchDown G t) (hΦ : ∀ j, IsThetaFunO W.ψ _ _ (Φ j)) (h : Pts G) (i σ : ℕ)
    (hi : i + 2 * (σ + 1) + 2 = D.R.m) (r) (hr : r ∈ rowGrp G (i + 1 + 1)) (ψ : GA D (G.V (.top i)) → ℂ)
    (hψ : GlobalTheory.Unf.IsContAut _ ψ) :
    biL W M t (i + 1 + 1) (biL W M t i ψ (conAt W hM Φ (Function.update h (i + 1 + 1) (r * h (i + 1 + 1))) i))
        (conAt W hM Φ (Function.update h (i + 1 + 1) (r * h (i + 1 + 1))) (i + 1 + 1)) =
      biL W M t (i + 1 + 1) (biL W M t i ψ (conAt W hM Φ h i)) (conAt W hM Φ h (i + 1 + 1)) := by
  have hi' : i + 1 + 1 + 2 * σ + 2 = D.R.m := by omega
  rw [rowGrp_even (i + 1 + 1) σ hi'] at hr
  obtain ⟨n, hn, a, rfl⟩ := (GlobalTheory.CharLaws.mem_besGrp _ _ r).1 hr
  rw [even_first W hM Φ hΦ h i σ hi hi' n hn a ψ hψ]
  refine even_second W hM Φ hΦ h (i + 1 + 1) σ hi' n hn a _ ?_
  rw [biL_conAt W hM i σ hi Φ hΦ ψ hψ]
  exact handAt_contAut W hM _ _ _ Φ hΦ ψ hψ _ _ _

omit hM in
theorem jPer_congr_above (M : GlobalTheory.FunObj.Vol G) (t : T) (C C' : BiFam G) (F : Fn G (.grid D.R.m D.R.m)) :
    ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (φ : Fn G (.top j)), Even j → (∀ i, Even i → j ≤ i → C i = C' i) →
      jPer W M t C F σ j hj φ = jPer W M t C' F σ j hj φ
  | 0, j, hj, φ, he, hC => by
    simp only [jPer]
    rw [hC j he le_rfl]
  | σ + 1, j, hj, φ, he, hC => by
    simp only [jPer]
    rw [hC j he le_rfl]
    exact jPer_congr_above M t C C' F σ (j + 1 + 1) _ _ (by obtain ⟨a, ha⟩ := he; exact ⟨a + 1, by omega⟩)
      fun i hi hji => hC i hi (by omega)


omit hM in
theorem jPer_congr_window (M : GlobalTheory.FunObj.Vol G) (t : T) (C C' : BiFam G) (F : Fn G (.grid D.R.m D.R.m)) (k : ℕ)
    (hk4 : k + 1 + 1 + 2 ≤ D.R.m) (hC : ∀ i, Even i → i ≠ k → i ≠ k + 1 + 1 → C i = C' i)
    (hpres : ∀ i, Even i → i < k → ∀ ψ : GA D (G.V (.top i)) → ℂ, GlobalTheory.Unf.IsContAut _ ψ →
      GlobalTheory.Unf.IsContAut _ (biL W M t i ψ (C i)))
    (hwin : ∀ ψ : GA D (G.V (.top k)) → ℂ, GlobalTheory.Unf.IsContAut _ ψ →
      biL W M t (k + 1 + 1) (biL W M t k ψ (C k)) (C (k + 1 + 1)) =
        biL W M t (k + 1 + 1) (biL W M t k ψ (C' k)) (C' (k + 1 + 1))) :
    ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (φ : Fn G (.top j)), Even j → Even k → j ≤ k → GlobalTheory.Unf.IsContAut _ φ →
      jPer W M t C F σ j hj φ = jPer W M t C' F σ j hj φ
  | 0, j, hj, φ, he, hk, hjk, hφ => by
    have h1 : j + 2 = D.R.m := by simpa using hj
    have h2 : j ≤ k := hjk
    omega
  | σ + 1, j, hj, φ, he, hk, hjk, hφ => by
    rcases Nat.lt_or_ge j k with hlt | hge
    · have hCj : C j = C' j := hC j he (by omega) (by omega)
      simp only [jPer]
      rw [← hCj]
      have hle : j + 1 + 1 ≤ k := by
        rw [Nat.even_iff] at he hk
        omega
      exact jPer_congr_window M t C C' F k hk4 hC hpres hwin σ (j + 1 + 1) _ _
        he.add_one.add_one hk hle (hpres j he hlt φ hφ)
    · have hkj : k = j := Nat.le_antisymm hge hjk
      subst k
      cases σ with
      | zero =>
        simp only [jPer]
        rw [hwin φ hφ]
      | succ σ' =>
        simp only [jPer]
        rw [hwin φ hφ]
        exact jPer_congr_above W M t C C' F σ' (j + 1 + 1 + 1 + 1) _ _
          (by obtain ⟨a, ha⟩ := he; exact ⟨a + 2, by omega⟩) fun i hi hji => hC i hi (by omega) (by omega)

theorem conAt_update (Φ : SchDown G t) (h : Pts G) (j : ℕ) (x : GA D (G.V (.grid D.R.m j))) (i : ℕ) (h0 : i ≠ j)
    (h1 : i + 1 ≠ j) (h2 : i + 1 + 1 ≠ j) : conAt W hM Φ (Function.update h j x) i = conAt W hM Φ h i := by
  unfold conAt
  simp only [Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h2]

end Steps

theorem rinv_all {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) : RInv ch := by
  intro t M hM Φ f hΦ hf P φ F hφ hF j hj r hr h
  obtain ⟨c, hc⟩ := D.R.m_even
  have hm2 := D.R.two_le_m
  have hj' : 1 ≤ j ∧ j + 2 ≤ D.R.m := by
    simp only [idx, List.mem_range'_1] at hj
    omega
  unfold per
  rcases Nat.even_or_odd j with he | ho
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 + 1 := ⟨j - 2, by obtain ⟨a, ha⟩ := he; omega⟩
    obtain ⟨b, hb⟩ : Even i := by
      obtain ⟨a, ha⟩ := he
      exact ⟨a - 1, by omega⟩
    refine jPer_congr_window ch.W M t _ _ _ i (by omega) ?_ ?_ ?_ _ 0 top_idx _ ⟨0, rfl⟩ ⟨b, hb⟩ (Nat.zero_le _) hφ
    · intro i' hi' h1 h2
      refine conAt_update ch.W hM Φ h _ _ i' h2 ?_ ?_
      · intro e; obtain ⟨a, ha⟩ := hi'; omega
      · intro e; exact h1 (by omega)
    · intro i' hi' hlt ψ hψ
      exact biL_contAut ch.W hM Φ hΦ _ i' hi' (by omega) ψ hψ
    · intro ψ hψ
      exact even_step ch.W hM Φ hΦ h i (c - b - 2) (by omega) r hr ψ hψ
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    obtain ⟨b, hb⟩ : Even i := by
      obtain ⟨a, ha⟩ := ho
      exact ⟨a, by omega⟩
    refine jPer_congr_window ch.W M t _ _ _ i (by omega) ?_ ?_ ?_ _ 0 top_idx _ ⟨0, rfl⟩ ⟨b, hb⟩ (Nat.zero_le _) hφ
    · intro i' hi' h1 h2
      refine conAt_update ch.W hM Φ h _ _ i' ?_ ?_ ?_
      · intro e; obtain ⟨a, ha⟩ := hi'; omega
      · intro e; exact h1 (by omega)
      · intro e; obtain ⟨a, ha⟩ := hi'; omega
    · intro i' hi' hlt ψ hψ
      exact biL_contAut ch.W hM Φ hΦ _ i' hi' (by omega) ψ hψ
    · intro ψ hψ
      rw [odd_step ch.W hM Φ hΦ h i (c - b - 2) (by omega) r hr ψ hψ,
        conAt_update ch.W hM Φ h (i + 1) _ (i + 1 + 1) (by omega) (by omega) (by omega)]

theorem rinv : Big fun ch => RInv ch :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => rinv_all ch⟩⟩

end GlobalTheory.RowLeftInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnermostIntegrandLeftPeriodInvariantLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.innermostIntegrand_leftPeriodInvariant_largeDepth : Big fun ch => RInv ch := by
  first | exact @GlobalTheory.RowLeftInv.rinv | exact GlobalTheory.RowLeftInv.rinv | (intros; apply GlobalTheory.RowLeftInv.rinv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedIntegrandBiInvariantLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowInv

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

def mvD (t : T) (j : ℕ) (k : GA D (ch.G.V (.grid D.R.m j))) (Φ : SchDown ch.G t) : SchDown ch.G t := fun i =>
  ch.W.om (.mu t D.R.m i) ((Pi.mulSingle j k : Pts ch.G) i, (Pi.mulSingle j k : Pts ch.G) (i + 1)) (Φ i)

theorem mulSingle_fin {j : ℕ} {k : GA D (ch.G.V (.grid D.R.m j))} (hk : k ∈ GfC _) (i : ℕ) :
    (Pi.mulSingle j k : Pts ch.G) i ∈ GfC _ := by
  rcases eq_or_ne i j with rfl | hi
  · rwa [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne hi]
    exact one_mem _

theorem om_move (t : T) {j : ℕ} {k : GA D (ch.G.V (.grid D.R.m j))} (hk : k ∈ GfC _) {Φ : SchDown ch.G t}
    (hΦ : ∀ i, IsThetaFunO ch.W.ψ _ _ (Φ i)) (P : PolDown ch.G) (i : ℕ) (hi : i < D.R.m)
    (g : GA D (ch.G.V (.grid D.R.m i))) (g' : GA D (ch.G.V (.grid D.R.m (i + 1)))) :
    ch.W.om (.mu t D.R.m i) (g * (Pi.mulSingle j k : Pts ch.G) i, g' * (Pi.mulSingle j k : Pts ch.G) (i + 1))
        (fockD ch.W t Φ P ⟨i, hi⟩) =
      ch.W.om (.mu t D.R.m i) (g, g') (fockD ch.W t (mvD ch t j k Φ) P ⟨i, hi⟩) := by
  have hom := ch.W.om_is (.mu t D.R.m i) ⟨le_rfl, hi⟩
  have hb := mulSingle_fin ch hk i
  have hb' := mulSingle_fin ch hk (i + 1)
  have key := GlobalTheory.OrientedHeis.om_pureTensorO D ch.W.ψ ch.W.θ (ch.G.pS (.mu t D.R.m i)) (ch.G.pT (.mu t D.R.m i))
    (ch.G.chrS (.mu t D.R.m i)) (ch.G.chrT (.mu t D.R.m i)) (ch.W.om (.mu t D.R.m i)) hom ch.W.θ_is
    (ch.G.cartS ch.W.cart (.mu t D.R.m i)) (ch.G.cartS ch.W.cart (.mu t D.R.m i))
    (ch.G.onS ch.W.onb (.mu t D.R.m i)) (ch.G.onS ch.W.onb (.mu t D.R.m i))
    (ch.G.onT ch.W.cart (.mu t D.R.m i)) (ch.G.onT ch.W.cart (.mu t D.R.m i))
    (ch.G.onT ch.W.onb (.mu t D.R.m i)) (ch.G.onT ch.W.onb (.mu t D.R.m i)) _ _
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ hb', Matrix.one_mul]) (Φ ⟨i, hi⟩) (hΦ ⟨i, hi⟩) (P ⟨i, hi⟩)
  have e1 : ((g * (Pi.mulSingle j k : Pts ch.G) i, g' * (Pi.mulSingle j k : Pts ch.G) (i + 1)) :
      GA D (ch.G.V (.grid D.R.m i)) × GA D (ch.G.V (.grid D.R.m (i + 1)))) =
      (g, g') * ((Pi.mulSingle j k : Pts ch.G) i, (Pi.mulSingle j k : Pts ch.G) (i + 1)) := rfl
  rw [e1, map_mul, Module.End.mul_apply]
  exact congrArg (ch.W.om (.mu t D.R.m i) (g, g')) key.2

theorem lastDat_congr {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (Wl : G.Weil) {t : T} {M : Vol G}
    (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j 0 hj)) (g g' : GA D (G.V (.grid D.R.m j)))
    (Φ₁ Φ₁' : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ)
    (e : Wl.om (.mu t D.R.m j) (g, 1) Φ₁ = Wl.om (.mu t D.R.m j) (g', 1) Φ₁') :
    lastDat Wl hM j hj vN g Φ₁ Φ₂ = lastDat Wl hM j hj vN g' Φ₁' Φ₂ := by
  have e' : (lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁ = (lastAt G Wl t hM j hj vN).s.om (g', 1) Φ₁' := e
  unfold lastDat
  rw [e']

theorem down_theta {t : T} {Φ : ch.G.Datum} {τ : SchRow ch.G × SchDown ch.G t →₀ ℂ} (hτ : IsFlipFin t ch.S.B ch.rm Φ τ)
    {d : SchRow ch.G × SchDown ch.G t} (hd : d ∈ τ.support) (j : Fin D.R.m) : IsThetaFunO ch.W.ψ _ _ (d.2 j) := by
  obtain ⟨e, _he, φ, hφ, _⟩ := hτ
  have hv := ch.rm.vT_is t D.R.m j le_rfl j.2
  exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt ch.W.ψ_std ch.W.θ_is ((hφ d hd).2 j).2 hv.2.theta

theorem fockD_theta (t : T) {Φ : SchDown ch.G t} (hΦ : ∀ j, IsThetaFunO ch.W.ψ _ _ (Φ j)) (P : PolDown ch.G) (j : Fin D.R.m) :
    IsThetaFunO ch.W.ψ _ _ (fockD ch.W t Φ P j) := by
  have hom := ch.W.om_is (.mu t D.R.m j) ⟨le_rfl, j.2⟩
  have key := GlobalTheory.OrientedHeis.om_pureTensorO D ch.W.ψ ch.W.θ (ch.G.pS (.mu t D.R.m j)) (ch.G.pT (.mu t D.R.m j))
    (ch.G.chrS (.mu t D.R.m j)) (ch.G.chrT (.mu t D.R.m j)) (ch.W.om (.mu t D.R.m j)) hom ch.W.θ_is
    (ch.G.cartS ch.W.cart (.mu t D.R.m j)) (ch.G.cartS ch.W.cart (.mu t D.R.m j))
    (ch.G.onS ch.W.onb (.mu t D.R.m j)) (ch.G.onS ch.W.onb (.mu t D.R.m j))
    (ch.G.onT ch.W.cart (.mu t D.R.m j)) (ch.G.onT ch.W.cart (.mu t D.R.m j))
    (ch.G.onT ch.W.onb (.mu t D.R.m j)) (ch.G.onT ch.W.onb (.mu t D.R.m j)) 1 1
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _), Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite _ τ (one_mem _), Matrix.one_mul]) (Φ j) (hΦ j) (P j)
  exact key.1

theorem mvD_theta (t : T) {j : ℕ} {k : GA D (ch.G.V (.grid D.R.m j))} {Φ : SchDown ch.G t}
    (hΦ : ∀ i, IsThetaFunO ch.W.ψ _ _ (Φ i)) (i : Fin D.R.m) : IsThetaFunO ch.W.ψ _ _ (mvD ch t j k Φ i) :=
  (ch.W.om_is (.mu t D.R.m i) ⟨le_rfl, i.2⟩).om_pres _ _ (hΦ i)

theorem update_eq_mul (h : Pts ch.G) (j : ℕ) (k : GA D (ch.G.V (.grid D.R.m j))) :
    Function.update h j (h j * k) = h * Pi.mulSingle j k := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp
  · simp [hi]

theorem conAt_move (t : T) {M : Vol ch.G} (hM : M.Is t) {j : ℕ} (hj : j ∈ idx D) {k : GA D (ch.G.V (.grid D.R.m j))}
    (hk : k ∈ GfC _) {Φ : SchDown ch.G t} (hΦ : ∀ i, IsThetaFunO ch.W.ψ _ _ (Φ i)) (P : PolDown ch.G) (h : Pts ch.G) :
    conAt ch.W hM (fockD ch.W t Φ P) (h * Pi.mulSingle j k) = conAt ch.W hM (fockD ch.W t (mvD ch t j k Φ) P) h := by
  have hjm : j ≤ D.R.m - 2 := by
    simp only [idx, List.mem_range'_1] at hj
    omega
  funext j'
  unfold conAt
  by_cases h0 : j' + 2 * 0 + 2 = D.R.m
  · rw [dite_eq_left h0, dite_eq_left h0]
    have hne1 : j' + 1 ≠ j := by omega
    have hne2 : j' + 1 + 1 ≠ j := by omega
    have hmv : mvD ch t j k Φ ⟨j' + 1, by omega⟩ = Φ ⟨j' + 1, by omega⟩ := by
      simp only [mvD, Fin.val_mk, Pi.mulSingle_eq_of_ne hne1, Pi.mulSingle_eq_of_ne hne2, Prod.mk_one_one, map_one,
        Module.End.one_apply]
    have hf : fockD ch.W t (mvD ch t j k Φ) P ⟨j' + 1, by omega⟩ = fockD ch.W t Φ P ⟨j' + 1, by omega⟩ := by
      unfold fockD
      rw [hmv]
    rw [hf]
    refine lastDat_congr ch.W hM j' h0 _ _ _ _ _ _ ?_
    have e := om_move ch t hk hΦ P j' (by omega) (h j') 1
    rw [Pi.mulSingle_eq_of_ne hne1, one_mul] at e
    exact e
  rw [dite_eq_right h0, dite_eq_right h0]
  by_cases h1 : j' + 2 * ((D.R.m - 4 - j') / 2 + 1) + 2 = D.R.m
  · refine dite_congr rfl (fun h1' => ?_) (fun _ => rfl)
    have e1 := om_move ch t hk hΦ P j' (by omega) (h j') (h (j' + 1))
    have e2 := om_move ch t hk hΦ P (j' + 1) (by omega) (h (j' + 1)) (h (j' + 1 + 1))
    simp only [Pi.mul_apply]
    rw [e1, e2]
  · refine dite_congr rfl (fun h1' => absurd h1' h1) (fun _ => rfl)

theorem inv_of (hB : BasicAt ch) (hC : ConLin ch) (hK : KFix ch) (hR : RInv ch) (hT : TensAt ch) : InvAt ch := by
  intro t a τ hτ M hM P y j hj h
  refine ⟨fun r hr => ?_, fun k hk => ?_⟩
  · unfold tot
    refine Finsupp.sum_congr fun d hd => ?_
    rw [hR t M hM _ d.1 (fockD_theta ch t (down_theta ch hτ hd) P.2)
      (fun i => (hB.2.2.2.2.1 t _ τ hτ M hM d hd P.2 h).2 i) P.1 _ _ (hB.1 a) (hB.2.1 t y) j hj r hr h]
  · have hk' : k ∈ GfC _ := (Subgroup.mem_inf.1 hk).1
    have hmv : ∀ d ∈ τ.support, conAt ch.W hM (fockD ch.W t d.2 P.2) (h * Pi.mulSingle j k) =
        conAt ch.W hM (fockD ch.W t (mvD ch t j k d.2) P.2) h := fun d hd =>
      conAt_move ch t hM hj hk' (down_theta ch hτ hd) P.2 h
    rw [update_eq_mul]
    unfold tot
    simp only [Finsupp.sum]
    refine Eq.trans (Finset.sum_congr rfl fun d hd =>
      congrArg (fun C => τ d * per ch.W M t C d.1 P.1 (colFn ch a) (formTop ch t y)) (hmv d hd)) ?_
    let Φs : (SchRow ch.G × SchDown ch.G t) ⊕ (SchRow ch.G × SchDown ch.G t) → SchDown ch.G t :=
      Sum.elim (fun d => mvD ch t j k d.2) (fun d => d.2)
    let fs : (SchRow ch.G × SchDown ch.G t) ⊕ (SchRow ch.G × SchDown ch.G t) → SchRow ch.G := Sum.elim (·.1) (·.1)
    let xs : (SchRow ch.G × SchDown ch.G t) ⊕ (SchRow ch.G × SchDown ch.G t) → ℂ := Sum.elim (fun d => τ d) (fun d => -τ d)
    have hth : ∀ i ∈ τ.support.disjSum τ.support, ∀ n, IsThetaFunO ch.W.ψ _ _ (Φs i n) := by
      rintro (d | d) hd n
      · exact mvD_theta ch t (down_theta ch hτ (Finset.inl_mem_disjSum.1 hd)) n
      · exact down_theta ch hτ (Finset.inr_mem_disjSum.1 hd) n
    have hvan : ∀ (yr : RowPt ch.G) (v : ∀ j : Fin D.R.m, WO (ch.G.V (.grid D.R.m j)) (ch.G.V (.grid D.R.m (j + 1)))),
        ∑ i ∈ τ.support.disjSum τ.support, xs i * ((∏ n, fs i n (yr n)) * ∏ n, Φs i n (v n)) = 0 := by
      intro yr v
      have hk2 := hK t _ τ hτ j hj k hk yr v
      simp only [Finsupp.sum] at hk2
      rw [Finset.sum_disjSum]
      simp only [xs, fs, Φs, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib]
      rw [← sub_eq_add_neg, sub_eq_zero]
      exact hk2
    have hgood : ∀ i ∈ τ.support.disjSum τ.support, Good ch.W (conAt ch.W hM (fockD ch.W t (Φs i) P.2) h) (fs i) := by
      rintro (d | d) hd
      · have hd' := Finset.inl_mem_disjSum.1 hd
        show Good ch.W (conAt ch.W hM (fockD ch.W t (mvD ch t j k d.2) P.2) h) d.1
        rw [← hmv d hd']
        exact hB.2.2.2.2.1 t _ τ hτ M hM d hd' P.2 _
      · exact hB.2.2.2.2.1 t _ τ hτ M hM d (Finset.inr_mem_disjSum.1 hd) P.2 h
    have key := hT t M (hB.2.2.1 t M hM) _ _ (hB.1 a) (hB.2.1 t y) _ (τ.support.disjSum τ.support) xs
      (fun i => conAt ch.W hM (fockD ch.W t (Φs i) P.2) h) fs hgood (hC t M hM P.2 h _ _ xs fs Φs hth hvan) P.1
    rw [Finset.sum_disjSum] at key
    simp only [xs, fs, Φs, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at key
    rw [← sub_eq_zero, sub_eq_add_neg]
    exact key

theorem main : Big fun ch => InvAt ch :=
  big_mono (fun ch h => inv_of ch h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2)
    (Big.and GlobalTheory.T.lastRow_unfolding_basicHypotheses (Big.and GlobalTheory.T.unfoldedProduct_depends_on_dataProduct (Big.and GlobalTheory.T.flippedFiniteTensorLatticeFixed_largeDepth (Big.and GlobalTheory.T.innermostIntegrand_leftPeriodInvariant_largeDepth GlobalTheory.T.definitePeriod_depends_on_productFunction))))

end GlobalTheory.RowInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedIntegrandBiInvariantLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolded_integrand_biInvariant_large_depth : Big fun ch => InvAt ch := by
  first | exact @GlobalTheory.RowInv.main | exact GlobalTheory.RowInv.main | (intros; apply GlobalTheory.RowInv.main <;> assumption)
end
