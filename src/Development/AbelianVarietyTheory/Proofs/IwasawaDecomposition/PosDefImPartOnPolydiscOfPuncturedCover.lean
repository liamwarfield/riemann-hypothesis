module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProduct
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardGLResidueTypePrimeDvdCardTypeGroup
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotPeriodMatrixIntVecContinuousBoundary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameTwistOfOneField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefImPartOnPolydiscOfPuncturedCover
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefImPartOnPolydiscOfPuncturedCover
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem posDef_im_on_ball_of_logExp : ∀ (n a : ℕ) (J : Type) [Fintype J] [DecidableEq J] (Δ : (Fin n → ℂ) → Matrix J J ℂ), (∀ i j, DifferentiableOn ℂ (fun z => Δ z i j) (Metric.ball 0 1)) → (∀ s ∈ logDom n a, ((Δ (logExp a s)).map Complex.im).PosDef) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ((Δ z).map Complex.im).PosDef := by
  intro n a J _ _ Δ hΔ hpos z hz
  set U := Metric.ball (0 : Fin n → ℂ) 1 with hU
  have hcont : ∀ i j, ContinuousOn (fun w => Δ w i j) U := fun i j => (hΔ i j).continuousOn
  have hM : ContinuousOn (fun w => (Δ w).map Complex.im) U := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    exact Complex.continuous_im.comp_continuousOn (hcont i j)
  have hMT : ContinuousOn (fun w => ((Δ w).map Complex.im)ᵀ) U := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    exact Complex.continuous_im.comp_continuousOn (hcont j i)
  have hsymm : ((Δ z).map Complex.im)ᵀ = (Δ z).map Complex.im := by
    refine eq_on_ball_of_eq_on_logExp_image n a 1 (Matrix J J ℝ)
      (fun w => ((Δ w).map Complex.im)ᵀ) (fun w => (Δ w).map Complex.im) le_rfl hMT hM ?_ z hz
    intro s hs _
    have h1 := (hpos s hs).1
    unfold Matrix.IsHermitian at h1
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hsymm
  intro x hx
  set q : (Fin n → ℂ) → ℂ := fun w => ∑ i, ∑ j, (x i : ℂ) * Δ w i j * (x j : ℂ) with hq
  have hqim : ∀ w, (q w).im = star x ⬝ᵥ ((Δ w).map Complex.im *ᵥ x) := by
    intro w
    simp [q, dotProduct, mulVec, Complex.im_sum, Complex.mul_im, Finset.mul_sum, mul_comm,
      mul_left_comm, mul_assoc]
  have hqd : DifferentiableOn ℂ q U := by
    rw [hq]
    apply DifferentiableOn.fun_sum
    intro i _
    apply DifferentiableOn.fun_sum
    intro j _
    exact ((hΔ i j).const_mul (x i : ℂ)).mul_const (x j : ℂ)
  have hqpos : ∀ s ∈ logDom n a, 0 < (q (logExp a s)).im := by
    intro s hs
    rw [hqim]
    exact (hpos s hs).dotProduct_mulVec_pos hx
  have hqc : ContinuousOn (fun w => (q w).im) U :=
    Complex.continuous_im.comp_continuousOn hqd.continuousOn
  have hnn : ∀ w ∈ U, 0 ≤ (q w).im := by
    intro w hw
    have := eq_on_ball_of_eq_on_logExp_image n a 1 ℝ (fun w => min (q w).im 0) (fun _ => 0)
      le_rfl ((continuous_id.min continuous_const).comp_continuousOn hqc) continuousOn_const
      (fun s hs _ => min_eq_right (hqpos s hs).le) w hw
    exact (min_eq_right_iff.1 this)
  rw [← hqim]
  rcases (hnn z hz).lt_or_eq with h | h0
  · exact h
  exfalso
  set F : (Fin n → ℂ) → ℂ := fun w => Complex.exp (Complex.I * q w) with hF
  have hFn : ∀ w, ‖F w‖ = Real.exp (-(q w).im) := by
    intro w
    simp [F, Complex.norm_exp, Complex.I_mul_re]
  have hFd : DifferentiableOn ℂ F U := (hqd.const_mul Complex.I).cexp
  have hmax : IsMaxOn (norm ∘ F) U z := by
    intro w hw
    simp only [Set.mem_setOf_eq, Function.comp, hFn, ← h0, neg_zero]
    exact Real.exp_le_exp.2 (by linarith [hnn w hw])
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball (0 : Fin n → ℂ) 1).isPreconnected
    Metric.isOpen_ball hFd hz hmax
  obtain ⟨s, hs⟩ := (GlobalTheory.ShFam.Hor.Mark.nonempty_logDom : (logDom n a).Nonempty)
  have hmem : logExp a s ∈ U := GlobalTheory.ShFam.Hor.Mark.logExp_mem hs
  have h2 := congrArg norm (heq hmem)
  simp only [Function.const_apply, hFn, ← h0, neg_zero] at h2
  have h3 : (q (logExp a s)).im = 0 := by
    have := Real.exp_injective h2
    linarith
  exact (hqpos s hs).ne' h3

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefImPartOnPolydiscOfPuncturedCoverStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posDef_imPart_on_polydisc_of_punctured_cover : ∀ (n a : ℕ) (J : Type) [Fintype J] [DecidableEq J] (Δ : (Fin n → ℂ) → Matrix J J ℂ), (∀ i j, DifferentiableOn ℂ (fun z => Δ z i j) (Metric.ball 0 1)) → (∀ s ∈ logDom n a, ((Δ (logExp a s)).map Complex.im).PosDef) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ((Δ z).map Complex.im).PosDef := by
  first | exact @GlobalTheory.posDef_im_on_ball_of_logExp | exact GlobalTheory.posDef_im_on_ball_of_logExp | (intros; apply GlobalTheory.posDef_im_on_ball_of_logExp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitReductionStandardFrameConj
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameRedSplit

theorem conj_red_core {R K k ι : Type} [CommRing R] [Field K] [CommRing k] {m : ℕ} (S : Subring R) (O : ValuationSubring K)
    (pr : R →+* K) (φ : O →+* k) (res : S →+* k) (hres : ∀ z : S, ∃ h : pr z ∈ O, res z = φ ⟨_, h⟩)
    (β : GL (Fin m) R) (B B' : Matrix (Fin m) (Fin m) R) (hBB : B * B' = 1)
    (U : Set ι) (Km : ι → Matrix (Fin m) (Fin m) R) (Z : ∀ κ ∈ U, GL (Fin m) S)
    (hZ : ∀ κ (hκ : κ ∈ U), β.1 * (Z κ hκ).1.map S.subtype * (β⁻¹).1 = B * Km κ * B')
    (hsurj : ∀ u : GL (Fin m) O, ∃ κ, ∃ hκ : κ ∈ U, (Km κ).map pr = u.1.map O.subtype) :
    ∃ b : GL (Fin m) k, ∀ κ (hκ : κ ∈ U) (y : GL (Fin m) O), (Km κ).map pr = y.1.map O.subtype →
      (Z κ hκ).1.map res = (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).1 := by
  classical
  obtain ⟨γ, hγ⟩ : ∃ γ : Matrix (Fin m) (Fin m) R, γ = (β⁻¹).1 * B := ⟨_, rfl⟩
  obtain ⟨γ', hγ'⟩ : ∃ γ' : Matrix (Fin m) (Fin m) R, γ' = B' * β.1 := ⟨_, rfl⟩
  have g1 : γ * γ' = 1 := by
    rw [hγ, hγ', Matrix.mul_assoc, ← Matrix.mul_assoc B, hBB, Matrix.one_mul, Units.inv_mul]
  have g2 : γ' * γ = 1 := mul_eq_one_comm.mp g1
  have hZ' : ∀ κ (hκ : κ ∈ U), (Z κ hκ).1.map S.subtype = γ * Km κ * γ' := by
    intro κ hκ
    have e : γ * Km κ * γ' = (β⁻¹).1 * (B * Km κ * B') * β.1 := by
      rw [hγ, hγ']; simp only [Matrix.mul_assoc]
    rw [e, ← hZ κ hκ]
    simp only [Matrix.mul_assoc]
    rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  let c : GL (Fin m) K := ⟨γ.map pr, γ'.map pr, by rw [← Matrix.map_mul, g1, Matrix.map_one _ (map_zero _) (map_one _)],
    by rw [← Matrix.map_mul, g2, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have hc : ∀ κ (hκ : κ ∈ U), (c.1 * (Km κ).map pr * (c⁻¹).1) = ((Z κ hκ).1.map S.subtype).map pr := by
    intro κ hκ
    rw [hZ' κ hκ, Matrix.map_mul, Matrix.map_mul]
    rfl
  have hent : ∀ u : GL (Fin m) O, ∀ a b, (c * Matrix.GeneralLinearGroup.map O.subtype u * c⁻¹).1 a b ∈ O := by
    intro u a b
    obtain ⟨κ, hκ, hK⟩ := hsurj u
    have e : (c * Matrix.GeneralLinearGroup.map O.subtype u * c⁻¹).1 = c.1 * (Km κ).map pr * (c⁻¹).1 := by
      rw [hK]; rfl
    rw [e, hc κ hκ, Matrix.map_apply, Matrix.map_apply]
    exact (hres _).1
  have hnorm : ∀ u ∈ Formalism.UG.GLint (Fin m) O.toSubring, c * u * c⁻¹ ∈ Formalism.UG.GLint (Fin m) O.toSubring := by
    rintro _ ⟨u, rfl⟩
    refine GlobalTheory.HeckeStdFacts.mem_GLint_iff.2 ⟨fun a b => hent u a b, fun a b => ?_⟩
    have e : (c * Formalism.UG.bc O.toSubring.subtype u * c⁻¹)⁻¹ = c * Matrix.GeneralLinearGroup.map O.subtype u⁻¹ * c⁻¹ := by
      rw [map_inv]
      group
      rfl
    rw [e]
    exact hent u⁻¹ a b
  obtain ⟨h, ⟨h₀, rfl⟩, hconj⟩ := GlobalTheory.HeckeStdFacts.exists_int_of_normalizes O.valuation O.toSubring
    (fun x => (O.valuation_le_one_iff x).symm) c hnorm
  suffices H : ∀ h₁ : GL (Fin m) O, (∀ x, c * x * c⁻¹ = Matrix.GeneralLinearGroup.map O.subtype h₁ * x *
      (Matrix.GeneralLinearGroup.map O.subtype h₁)⁻¹) → ∃ b : GL (Fin m) k, ∀ κ (hκ : κ ∈ U) (y : GL (Fin m) O),
      (Km κ).map pr = y.1.map O.subtype → (Z κ hκ).1.map res = (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).1 from H h₀ hconj
  intro h₁ hconj'
  refine ⟨Matrix.GeneralLinearGroup.map φ h₁, fun κ hκ y hy => ?_⟩
  ext a b
  obtain ⟨hm, hr⟩ := hres ((Z κ hκ).1 a b)
  have e1 : pr ((Z κ hκ).1 a b : R) = (c * Matrix.GeneralLinearGroup.map O.subtype y * c⁻¹).1 a b := by
    have := congrFun (congrFun (hc κ hκ) a) b
    rw [hy] at this
    exact this.symm
  have e2 : (c * Matrix.GeneralLinearGroup.map O.subtype y * c⁻¹) =
      Matrix.GeneralLinearGroup.map O.subtype (h₁ * y * h₁⁻¹) := by
    rw [hconj']
    simp only [map_mul, map_inv]
  have e3 : (⟨_, hm⟩ : O) = (h₁ * y * h₁⁻¹).1 a b := by
    apply Subtype.ext
    show pr _ = _
    rw [e1, e2]
    rfl
  have e4 : Matrix.GeneralLinearGroup.map φ h₁ * Matrix.GeneralLinearGroup.map φ y * (Matrix.GeneralLinearGroup.map φ h₁)⁻¹ =
      Matrix.GeneralLinearGroup.map φ (h₁ * y * h₁⁻¹) := by
    simp only [map_mul, map_inv]
  rw [Matrix.map_apply, hr, e3, e4]
  rfl

theorem resS_eq_phiR (D : D7) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (y : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∃ h : s.proj (y : EAf D) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      resS D.host.F s.w y = GlobalTheory.MtRed.phiR s ⟨_, h⟩ := by
  have hmem : s.proj (y : EAf D) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (GlobalTheory.RowGood.proj_le_one s y.2)
  refine ⟨hmem, ?_⟩
  obtain ⟨a, ha, hφ⟩ := GlobalTheory.MtRed.exists_approx s ⟨_, hmem⟩
  rw [hφ]
  exact GlobalTheory.RowGood.res_eq (rfl : maximalRealSubfield D.host.E = _) s (y : EAf D) y (GlobalTheory.RowGood.tr_rfl _).symm a ha


set_option maxHeartbeats 1600000 in
theorem frameRed_exists : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), R3.StdFrame hF P → IsBaseFrame V β Λ 1 → ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, ∃ (φ : Os s →+* kP s.w) (b : GL (Fin n) (kP s.w)), IsResidue s φ ∧ FrameRed hn P β s φ b := by
  intro D V n hn hF P β Λ hP hβ s
  subst hn
  obtain ⟨⟨β₀, β₀', h01, h10, hmat⟩, hK⟩ := hP
  have hSt : ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank, finE V (P.ψ κ) ∈ St β := fun κ hκ =>
    (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hβ (P.into κ)).2 ((hK κ).1 hκ)
  have hfin : ∀ κ : Formalism.AUTREP.GAf D.host.E V.rank, (finE V (P.ψ κ)).1 =
      β₀.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) * (κ.1.1.map (GlobalTheory.RowGood.tr hF)) *
        β₀'.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) := by
    intro κ
    have e := congrArg (fun M => Matrix.map M (GlobalTheory.LevSplit.swp D.host.F D.host.E)) (hmat κ)
    refine e.trans ?_
    simp only [Matrix.map_mul]
    rfl
  have hBB : β₀.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) * β₀'.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) = 1 := by
    rw [← Matrix.map_mul, h01, Matrix.map_one _ (map_zero _) (map_one _)]
  have hZ : ∀ (κ : Formalism.AUTREP.GAf D.host.E V.rank) (hκ : κ ∈ {κ | κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank}),
      β.1 * (pullFr β ⟨_, hSt κ hκ⟩).1.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * (β⁻¹).1 =
        β₀.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) * (κ.1.1.map (GlobalTheory.RowGood.tr hF)) *
          β₀'.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) := by
    intro κ hκ
    exact (congrArg (fun g : GL (Fin V.rank) (EAf D) => g.1) (frGL_pullFr β ⟨_, hSt κ hκ⟩)).trans (hfin κ)
  have hpr : ∀ κ : Formalism.AUTREP.GAf D.host.E V.rank, (κ.1.1.map (GlobalTheory.RowGood.tr hF)).map s.proj = (s.loc V.rank κ).1 := by
    intro κ
    ext i j
    simp only [Matrix.map_apply]
    rw [GlobalTheory.RowGood.tr_rfl]
    rfl
  have hsurj : ∀ u : GL (Fin V.rank) (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)),
      ∃ κ : Formalism.AUTREP.GAf D.host.E V.rank, ∃ _ : κ ∈ {κ | κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank},
        (κ.1.1.map (GlobalTheory.RowGood.tr hF)).map s.proj =
          u.1.map (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype := by
    intro u
    obtain ⟨x, hx, hloc⟩ := GlobalTheory.SplitSec.exists_trivOutside_loc D.host.E V.rank s
      (Matrix.GeneralLinearGroup.map (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype u)
    refine ⟨x, (GlobalTheory.HeckeStdFacts.loc_mem_GLint_iff s hx).1 ⟨u, ?_⟩, ?_⟩
    · exact hloc.symm
    · rw [hpr, hloc]; rfl
  obtain ⟨b, hb⟩ := conj_red_core (R := EAf D) (K := s.v.adicCompletion (maximalRealSubfield D.host.E)) (k := kP s.w)
    (ι := Formalism.AUTREP.GAf D.host.E V.rank) (m := V.rank) (S := Formalism.L2.Herm.intAf D.host.F D.host.E)
    (O := s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (pr := s.proj) (φ := GlobalTheory.MtRed.phiR s)
    (res := resS D.host.F s.w) (hres := resS_eq_phiR D s) (β := β) (hBB := hBB)
    (U := {κ | κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank})
    (Km := fun κ => κ.1.1.map (GlobalTheory.RowGood.tr hF))
    (Z := fun κ hκ => pullFr β ⟨_, hSt κ hκ⟩) (hZ := hZ) (hsurj := hsurj)
  refine ⟨GlobalTheory.MtRed.phiR s, b, ⟨GlobalTheory.MtRed.phiR_surj s, GlobalTheory.MtRed.phiR_eq_zero s⟩, fun κ hκ y hy a c => ?_⟩
  have hy' : (κ.1.1.map (GlobalTheory.RowGood.tr hF)).map s.proj =
      y.1.map (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype := by
    rw [hpr]
    exact Matrix.ext fun i j => (hy i j).symm
  have e := congrFun (congrFun (hb κ hκ y hy') a) c
  have hr : redFn β s.w (finE V (P.ψ κ)) = Formalism.UG.bc (resS D.host.F s.w) (pullFr β ⟨_, hSt κ hκ⟩) := by
    have h1 := redFn_frGL β s.w (pullFr β ⟨_, hSt κ hκ⟩)
    rwa [frGL_pullFr] at h1
  rw [← e, hr]
  rfl

end GlobalTheory.FrameRedSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemStOneOfInt
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.R3.LiftBrg.StdFrame

section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
end

theorem castGL_rfl {R : Type} [CommRing R] {m : ℕ} (x : GL (Fin m) R) : castGL (rfl : m = m) x = x := by
  ext i j
  simp [castGL]

section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end

end GlobalTheory.Mem.R3.LiftBrg.StdFrame

namespace GlobalTheory.Mem.R3.LiftBrg

end GlobalTheory.Mem.R3.LiftBrg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormCoordinateLtOneInPrimitiveCell
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormCoordinateLtOneInPrimitiveCell
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory

theorem orbMark_coord_lt_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell H.bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, h₀.mem i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i ∧ t i < 1) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
    LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β = 1 →
    ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1 := by
  intro E _ _ _ H φ hφ X₀ _ _ _ m₀ δ₀ h₀ hli₀ hprim₀ v t hv ht hvsum X _ _ _ m δ h hli hprim
    β _ _ hβ1 c hc hβsum j
  obtain ⟨p, -, hpos, hcells⟩ :=
    GlobalTheory.T.exists_markedForm_pieces_rays_of_simplicialCells E H φ hφ δ₀ h₀ hli₀ hprim₀ v t hv (fun i => (ht i).1) hvsum β hβ1
  rcases (hc j).lt_or_eq with hcj | hcj
  · obtain ⟨i, hti, d, hd, hpd, hcd⟩ := (hcells m δ h hli c hc hβsum).2 j hcj
    have hpi := (hpos i hti).2.2.1
    have hδj := GlobalTheory.T.isPrimitiveBalancedForm_primitive_among_intForms H.bar (δ j) (h.mem j) (hprim j)
    have hd1 := (GlobalTheory.T.primitive_intBilinForm_eq_of_positive_real_ray (p i) (δ j) d hd hpi hδj hpd).2
    rw [hcd, hd1, mul_one]
    exact (ht i).2
  · rw [← hcj]; exact zero_lt_one

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MarkedFormCoordinateLtOneInPrimitiveCellStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.markedForm_coordinate_lt_one_in_primitiveCell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)), IsTwInv H φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell H.bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, h₀.mem i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i ∧ t i < 1) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
    LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β = 1 →
    ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1 := by
  first | exact @GlobalTheory.orbMark_coord_lt_one | exact GlobalTheory.orbMark_coord_lt_one | (intros; apply GlobalTheory.orbMark_coord_lt_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralRationalAtMember
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.CenRatAt

theorem transfer {K G Pl0 V : Type} [Field K] [NumberField K] [StarRing K] [Group G] [Fintype G]
    (B B' : Formalism.L2.DIV.BlockDat K G Pl0) (hB : B = B') (ℓ : Formalism.L2.DIV.Lvl K G) (Q : V → V → Prop)
    (e : (Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) → V) (e' : (Fin (B'.S.lvlDim B'.r ℓ.P ℓ.ψ) → K) → V)
    (h : GlobalTheory.Mem.Top.Bl.SameOn e e') (a : MonoidAlgebra K G)
    (H : ∀ x, Q (e x) (e ((B.S.lvlOp B.r ℓ.P ℓ.ψ a).mulVec x))) (x' : Fin (B'.S.lvlDim B'.r ℓ.P ℓ.ψ) → K) :
    Q (e' x') (e' ((B'.S.lvlOp B'.r ℓ.P ℓ.ψ a).mulVec x')) := by
  subst hB
  have he : e = e' := funext fun x => h.2 x x fun i i' hi => congrArg x (Fin.ext hi)
  subst he
  exact H x'

theorem famR_L_eq (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U U' : Set I.ι)
    (Xg : Finset (R3.Gc X.B px → X.B.LL)) (tr tr' : R3.TrI X.B px) (k : Fin X.toD7.R.m) (s : R3.TupU I U) (s' : R3.TupU I U')
    (h : s.1 = s'.1) : (R3.famR X I hX U Xg tr).A.fam.L k s = (R3.famR X I hX U' Xg tr').A.fam.L k s' := by
  obtain ⟨τ, hτ⟩ := s
  obtain ⟨τ', hτ'⟩ := s'
  cases h
  rfl

section Main

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}


set_option maxHeartbeats 1000000 in
theorem cenRat_of (t : RowsT K w Z Wt p0) (r : RXs t) : GlobalTheory.CenLocAt.CenRat t.r.Y t.r.z.cG := by
  intro s k z a ha x
  have h5 : (tAll w.I (t.r.Y.tup s)).1 = s.1 := (congrArg w.I.tup (t.r.tup_ix s)).trans (R3.tup_ixOf w.I s)
  have h3 := (r.all.cen (t.r.Y.tup s) z a ha).2.2 k
  exact transfer _ _ (famR_L_eq (w.st Z) w.I t.hX _ _ _ _ _ k _ _ h5) _
    (fun u v => (w.st Z).toD7.ntypes.cenMt (t.r.Y.tup s) ((k : ℕ) + 1) z ((w.st Z).toD7.what₂.jMt (t.r.Y.tup s) ((k : ℕ) + 1) u) =
      (w.st Z).toD7.what₂.jMt (t.r.Y.tup s) ((k : ℕ) + 1) v)
    (r.all.eMt k (t.r.Y.tup s)) (t.r.Y.eMt k s) (r.eMt_use k s) a h3 x

end Main

end GlobalTheory.CenRatAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFrameUnitaryDivisorSplit
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameOff

noncomputable def evAt (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    Af D.host.F ⊗[D.host.F] D.host.E →+* Fv D.host.F v ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem map_conj_eq_one {R S : Type} [CommRing R] [CommRing S] {m k : ℕ} (f : R →+* S) (b : Matrix (Fin m) (Fin k) R)
    (b' : Matrix (Fin k) (Fin m) R) (K : Matrix (Fin k) (Fin k) R) (hb : b * b' = 1) (hK : K.map f = 1) :
    (b * K * b').map f = 1 := by
  rw [Matrix.map_mul, Matrix.map_mul, hK, Matrix.mul_one, ← Matrix.map_mul, hb, Matrix.map_one _ (map_zero f) (map_one f)]


set_option maxHeartbeats 1000000 in
theorem evAt_swapCast_symm (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (x : ReciprocityTheory.Aut.AL D.host.E) :
    evAt D v ((swapCast hF).symm x) =
      (Algebra.TensorProduct.comm (maximalRealSubfield D.host.E) D.host.E (v.adicCompletion (maximalRealSubfield D.host.E)))
        (ReciprocityTheory.Aut.compAt D.host.E v x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingEquiv.map_zero, RingHom.map_zero, RingHom.map_zero, _root_.map_zero]
  | tmul e a => rfl
  | add x y hx hy => rw [RingEquiv.map_add (e := _), RingHom.map_add (f := _), RingHom.map_add (f := _), _root_.map_add (f := _), hx, hy]

theorem map_evAt_eq_one (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) {n : ℕ}
    (A : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (κ : Formalism.AUTREP.GAf D.host.E n) (hA : ReciprocityTheory.Aut.TrivOutside A κ) (hv : v ∉ A) :
    ((κ.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (swapCast hF).symm).map (evAt D v) = 1 := by
  have h1 := hA v hv
  ext i j
  have h2 := congrFun (congrFun h1 i) j
  rw [Matrix.map_apply] at h2
  rw [Matrix.map_apply, Matrix.map_apply, evAt_swapCast_symm, h2]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h]

theorem stdFrame_stab_red : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), R3.StdFrame hF P → IsBaseFrame V β Λ 1 → ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, finE V (P.ψ κ) ∈ Formalism.L2.DIV.St β ∧ ∀ (A : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (PP : Formalism.L2.DIV.Pl D.host.E), ReciprocityTheory.Aut.TrivOutside A κ → NG.OverPl PP v → v ∉ A → redFn β PP (finE V (P.ψ κ)) = 1 := by
  intro D V n hF P β Λ hP hB κ hκ
  have hSt : finE V (P.ψ κ) ∈ Formalism.L2.DIV.St β :=
    (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hB (P.into κ)).2 ((hP.2 κ).1 hκ)
  refine ⟨hSt, fun A v PP hA hPP hv => ?_⟩
  have hu : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v := HeightOneSpectrum.ext hPP
  refine GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP hSt ?_
  rw [GlobalTheory.FinPl.KOpen.proj_eq_one_iff, hu]
  obtain ⟨⟨b, b', hbb, -, hmat⟩, -⟩ := hP
  have hF1 : (finMat D.sp.cm.sig V.gram (P.ψ κ)).map (evAt D v) = 1 := by
    rw [hmat κ]
    exact map_conj_eq_one _ _ _ _ hbb (map_evAt_eq_one D hF A v κ hA hv)
  intro i j
  have h3 := congrFun (congrFun hF1 i) j
  change evAt D v (finPart D ((Formalism.L2.Theta.mt V (P.ψ κ) - 1) i j)) = 0
  rw [Matrix.sub_apply, RingHom.map_sub, RingHom.map_sub]
  change evAt D v (finMat D.sp.cm.sig V.gram (P.ψ κ) i j) - _ = 0
  rw [Matrix.map_apply] at h3
  rw [h3, sub_eq_zero]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h]

end GlobalTheory.FrameOff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfMarkedFormsInSameCellSimplicialFan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfMarkedFormsInSameCellSimplicialFan
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem eq_of_orbMark_of_inRCone_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)), IsTwInv H φ → IsTwInv H lab →
  SimpLab H.bar q φ lab →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell H.bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, h₀.mem i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ γ →
      ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms H.bar X, (∀ y, 0 ≤ β' y y) →
        (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β = 1 → (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β' = 1 →
        InRCone γ β → InRCone γ β' → β = β' := by
  intro E _ _ _ H q φ lab hφ hlab hS X₀ _ _ _ m₀ δ₀ h₀ hli₀ hprim₀ v t hv ht hvt X _ _ _ _ hX m γ hγ β hβ hβn β' hβ' hβ'n
    hm hm' hin hin'
  obtain ⟨m', δ, hδ, hδli, hδinj, hγδ⟩ := hS.2 X hX m γ hγ
  have hcδ : ∀ j, InRCone δ (γ j) := hγδ
  obtain ⟨c, hc, hβc⟩ := inRCone_trans hcδ hin
  obtain ⟨c', hc', hβc'⟩ := inRCone_trans hcδ hin'
  obtain ⟨p, hp, hpi, hpc⟩ := GlobalTheory.T.exists_markedForm_pieces_rays_of_simplicialCells E H φ hφ δ₀ h₀ hli₀ hprim₀ v t hv ht hvt β hm
  obtain ⟨p', hp', hpi', hpc'⟩ := GlobalTheory.T.exists_markedForm_pieces_rays_of_simplicialCells E H φ hφ δ₀ h₀ hli₀ hprim₀ v t hv ht hvt β' hm'
  have hlabray : ∀ (x : LinearMap.BilinForm ℤ X) (j : Fin m') (d : ℝ), 0 < d → x ∈ balForms H.bar X →
      (∀ y, 0 ≤ x y y) → toReal x = d • toReal (δ j) → lab.evalZ x = lab.evalZ (δ j) := by
    intro x j d hd hxb hxn hx
    obtain ⟨a, b, ha, hb, hab⟩ := GlobalTheory.T.exists_pos_rat_multiple_of_pos_real_multiple_intForm x (δ j) d hd (hδli.ne_zero j) hx
    have h1 := hS.1 X hX x hxb hxn a ha
    have h2 := hS.1 X hX (δ j) (hδ.mem j) (hδ.nonneg j) b hb
    rw [← h1, ← h2, hab]
  have hpeq : ∀ i, 0 < t i → p i = p' i := by
    intro i hti
    obtain ⟨hpb, hpn, hpp, hpl⟩ := hpi i hti
    obtain ⟨hpb', hpn', hpp', hpl'⟩ := hpi' i hti
    obtain ⟨j, -, d, hd, hpd⟩ := (hpc m' δ hδ hδli c hc hβc).1 i hti
    obtain ⟨j', -, d', hd', hpd'⟩ := (hpc' m' δ hδ hδli c' hc' hβc').1 i hti
    have hjj : j = j' := hδinj (by
      show lab.evalZ (δ j) = lab.evalZ (δ j')
      rw [← hlabray _ j d hd hpb hpn hpd, ← hlabray _ j' d' hd' hpb' hpn' hpd', hpl lab hlab, hpl' lab hlab])
    subst hjj
    have : toReal (p i) = (d / d') • toReal (p' i) := by
      rw [hpd, hpd', smul_smul, div_mul_cancel₀ _ hd'.ne']
    exact (GlobalTheory.T.primitive_intBilinForm_eq_of_positive_real_ray (p i) (p' i) (d / d') (div_pos hd hd') hpp hpp' this).1
  apply toReal_injective
  rw [hp, hp']
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases (ht i).lt_or_eq with h | h
  · rw [hpeq i h]
  · rw [← h, zero_smul, zero_smul]

end GlobalTheory.PolFan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfMarkedFormsInSameCellSimplicialFanStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_markedForms_in_same_cell_simplicialFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)), IsTwInv H φ → IsTwInv H lab →
  SimpLab H.bar q φ lab →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module (𝓞 E) X₀] [Module.Finite (𝓞 E) X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell H.bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim H.bar (⟨δ₀ i, h₀.mem i⟩ : balForms H.bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar φ γ →
      ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms H.bar X, (∀ y, 0 ≤ β' y y) →
        (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β = 1 → (OrbMark.orbFun (𝓞 E) H.w0 v).evalZ β' = 1 →
        InRCone γ β → InRCone γ β' → β = β' := by
  first | exact @GlobalTheory.PolFan.eq_of_orbMark_of_inRCone_cell | exact GlobalTheory.PolFan.eq_of_orbMark_of_inRCone_cell | (intros; apply GlobalTheory.PolFan.eq_of_orbMark_of_inRCone_cell <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActionReadAtMember
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.CenLocAt

section Gen

open _root_.Formalism.L2.DIV _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.IndefR.Lev

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0)

theorem liftForm_lvlAct (hok : A3.fam3.Ok3 1) (k : Fin D.R.m) (s : T) (a : MonoidAlgebra D.what₂.LL G) (ha : ∀ b, b * a = a * b)
    (x : Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 k s) → D.what₂.LL) :
    (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s (lvlAct F k s a x) : A3.A.fam.amb.FL k s) =
      ∑ g : G, a.coeff g • A3.A.fam.amb.opL k s (Sum.inr g) (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s x) :=
  GlobalTheory.ClassSumIdentity.lvlE_lvlOp hok.ok2.conj _ ((hok.ok2.lifts k s).hpos _) _ (hok.ok2.lifts k s).act _ _ a ha x


variable (R) in
theorem jV_sum (k : Fin D.R.m) (s : T) (c : G → D.what₂.LL) (v : G → A3.A.fam.amb.FL k s) :
    R.jV k s (∑ g, c g • v g) = ∑ g, D.what₂.embLL (c g) • R.jV k s (v g) :=
  (map_sum (R.jV k s) (fun g => c g • v g) Finset.univ).trans
    (Finset.sum_congr rfl fun g _ => (R.jV k s).map_smulₛₗ (c g) (v g))


variable (R) in
theorem extV_sum (k : Fin D.R.m) (s : T) (c : G → ℂ) (w : G → (R.HV k s).H) (y : GA D (Vc D k)) :
    R.extV k s (∑ g, c g • w g) y = ∑ g, c g • R.extV k s (w g) y := by
  have e := map_sum (R.extV k s) (fun g => c g • w g) Finset.univ
  refine (congrFun e y).trans ((Finset.sum_apply y Finset.univ _).trans (Finset.sum_congr rfl fun g _ => ?_))
  exact congrFun ((R.extV k s).map_smul (c g) (w g)) y

theorem extV_act {A : FamIn D.what₂.LL G Pl0 T D.R.m} (R : RealDat D A Ks) (hM : R.IsModels) (hred : R.grp_red_L)
    (k : Fin D.R.m) (s : T) (g : G) {κ : GA D (Vc D k)} (hκ : IsLevelLift (Vc D k) (R.βV k) (R.datVt k s) (R.eG g) κ)
    (v : A.fam.amb.FL k s) (y : GA D (Vc D k)) :
    R.extV k s (R.jV k s (A.fam.amb.opL k s (Sum.inr g) v)) y =
      (levChi (Vc D k) (R.βV k) (flagL (R.datVt k s)) κ)⁻¹ • R.extV k s (R.jV k s v) (y * κ) := by
  have e1 := Formalism.IndefR.Eqv.Act.jV_act R hM k s g v _ (Formalism.IndefR.Eqv.Act.red_of_liftV R hred k s g hκ)
  have e2 := Formalism.IndefR.Eqv.Act.ext_g0Act (R.cV k) (hM.cV k) (levEnv (Vc D k) (R.βV k) (R.datVt k s)).ch
    ⟨_, Formalism.IndefR.Eqv.Act.mem_Q_of_liftV R k s g hκ⟩ κ hκ.1 rfl ((R.HV k s).e (R.jV k s v)) y
  have e3 := congrArg (fun f => (R.cV k).ext f y) e1
  have hch : ((((levEnv (Vc D k) (R.βV k) (R.datVt k s)).ch ⟨_, Formalism.IndefR.Eqv.Act.mem_Q_of_liftV R k s g hκ⟩)⁻¹ : ℂˣ) : ℂ) =
      (levChi (Vc D k) (R.βV k) (flagL (R.datVt k s)) κ)⁻¹ := Units.val_inv_eq_inv_val _
  refine (Formalism.IndefR.Eqv.Act.extV_apply R k s _ y).trans (e3.trans (e2.trans ?_))
  exact congrArg₂ (fun (c : ℂ) (w : (R.cV k).W) => c • w) hch (Formalism.IndefR.Eqv.Act.extV_apply R k s _ (y * κ)).symm

theorem actRead_of (hM : R.toRealDat.IsModels) (hred : R.toRealDat.grp_red_L) (hok : A3.fam3.Ok3 1) : ActRead Y := by
  intro s h k a ha κ hκ x y
  have hr : ∀ x', adForm Y (Y.tup s) h k (ratForm Y k s x') =
      R.extV k s (R.jV k s (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s x')) := fun x' => Y.mtRead k s h x'
  have e1 : R.jV k s (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s (lvlAct F k s a x)) =
      ∑ g : G, D.what₂.embLL (a.coeff g) •
        R.jV k s (A3.A.fam.amb.opL k s (Sum.inr g) (liftForm A3.A F.lv2.P0 F.lv2.ψ0 k s x)) :=
    (congrArg (R.jV k s) (liftForm_lvlAct hok k s a ha x)).trans (jV_sum R k s _ _)
  refine (congrFun (hr _) y).trans ((congrFun (congrArg (R.extV k s) e1) y).trans
    ((extV_sum R k s _ _ y).trans (Finset.sum_congr rfl fun g _ => ?_)))
  refine (congrArg (fun w => D.what₂.embLL (a.coeff g) • w) (extV_act R.toRealDat hM hred k s g (hκ g) _ y)).trans ?_
  exact (smul_smul _ _ _).trans (congrArg _ (congrFun (hr x) (y * κ g)).symm)

end Gen

end GlobalTheory.CenLocAt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChainChartLocalUnitCharacterCompatibleLeve
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChainChartLocalUnitCharacterCompatibleLeve
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG
open Formalism.L2.G.Cmp

noncomputable section

namespace GlobalTheory.Mem.Top.KerTwPsi

open Formalism.MainNotions.G _root_.Formalism.L2.G Formalism.MainNotions.G.CmpJ _root_.Formalism.L2.Forms Formalism.UG
open scoped TensorProduct

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {i : ℕ} (hi : i + 1 ≤ D.R.m) {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) (gramN D (i + 1) hi) T D.R.f bad)
  {Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))}


set_option maxHeartbeats 4000000 in
def kapU (hU : SameUlocJ hi S Uloc) (p : ℕ) : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc p →* S.U :=
  ((glue (epsP D.host.F p D.host.E) (isIdempotentElem_placeIdempotent D.host.F p D.host.E)).comp
    (((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) _).toMonoidHom.comp
      (awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc p).subtype).prod 1)).codRestrict S.U (by
    intro a
    have ha := (mem_awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc p a.1).1 a.2
    refine (S.U_eq _).2 ⟨glue_mem_UJ (epsP D.host.F p D.host.E) (isIdempotentElem_placeIdempotent D.host.F p D.host.E) _
      (epsP_sig D.host.F p D.host.E (sigD D)) _
      (reGL_mem_UPts (rankN D (i + 1) hi) (sigD D) (D.sp.X (i + 1)).gram (gramN D (i + 1) hi) (gramN_apply D (i + 1) hi) _ a.1 ha.1)
      (Subgroup.one_mem _), fun v => ?_⟩
    by_cases hv : ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal
    · show bc (prV (E := D.host.E) v) (glue _ _ (_, _)) ∈ _
      rw [bc_glue_one _ _ _ (epsP_over D.host.F p D.host.E v hv)]
      show bc (prV (E := D.host.E) v) 1 ∈ _
      rw [map_one]
      exact Subgroup.one_mem _
    · show bc (prV (E := D.host.E) v) (glue _ _ (_, _)) ∈ _
      rw [bc_glue_zero _ _ _ (epsP_off D.host.F p D.host.E v hv)]
      show bc (prV (E := D.host.E) v) (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) _ a.1) ∈ _
      rw [bc_reGL, hU v]
      exact Subgroup.mem_map.2 ⟨_, ha.2 v hv, rfl⟩)

theorem kapU_over (hU : SameUlocJ hi S Uloc) (p : ℕ) (a : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc p)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) :
    bc (prV (E := D.host.E) v) (kapU hi S hU p a).1 = 1 := by
  show bc (prV (E := D.host.E) v) (glue _ _ (_, _)) = 1
  rw [bc_glue_one _ _ _ (epsP_over D.host.F p D.host.E v hv)]
  exact map_one _

theorem kapU_off (hU : SameUlocJ hi S Uloc) (p : ℕ) (a : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc p)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : ((p : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) :
    bc (prV (E := D.host.E) v) (kapU hi S hU p a).1 =
      bc (prV (E := D.host.E) v) (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) _ a.1) := by
  show bc (prV (E := D.host.E) v) (glue _ _ (_, _)) = _
  rw [bc_glue_zero _ _ _ (epsP_off D.host.F p D.host.E v hv)]
  rfl


set_option maxHeartbeats 4000000 in
theorem exists_psiTiedJ (hU : SameUlocJ hi S Uloc) (e : D.what₂.LL →+* (D.gat u w hg).Kf)
    [IsFractionRing (D.gat u w hg).O (D.gat u w hg).Kf]
    (hrat : ChiRatAll S D.what₂.embLL) (hfin : ∃ n : ℕ, 0 < n ∧ ∀ κ, S.chi κ ^ n = 1) :
    ∃ ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ,
      UnitCharacterChartCompatibility hi S e ψ := by
  obtain ⟨n, hn, hc⟩ := hfin
  obtain ⟨ψ, hψ⟩ := GlobalTheory.Port.exists_char (O := (D.gat u w hg).O) D.what₂.embLL e
    (S.chi.comp (kapU hi S hU (D.what₂.places.resChar w))) (fun a => hrat _) ⟨n, hn, fun a => hc _⟩
  refine ⟨ψ, fun a κ hκp hκo => ?_⟩
  obtain ⟨r, hr⟩ := hrat κ
  have hχ : S.chi κ = S.chi (kapU hi S hU (D.what₂.places.resChar w) a) := by
    have h1 : S.chi (κ * (kapU hi S hU (D.what₂.places.resChar w) a)⁻¹) = 1 := by
      refine S.chi_triv _ fun v _ => ?_
      rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      by_cases hv : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal
      · rw [hκp v hv, kapU_over hi S hU _ a v hv, inv_one, one_mul]
      · rw [hκo v hv, kapU_off hi S hU _ a v hv, mul_inv_cancel]
    rwa [map_mul, map_inv, mul_inv_eq_one] at h1
  exact ⟨r, hr, hψ a r (hr.trans (congrArg (fun z : ℂˣ => (z : ℂ)) hχ))⟩

end GlobalTheory.Mem.Top.KerTwPsi


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.Top.KerTwPsi.psi_tied : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m) (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)),
        ∃ ψ : Formalism.L2.G.awayG (w.D Z).sp.cm.sig ((w.D Z).sp.X (j + 1)).gram
            (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Uloc ((w.D Z).what₂.places.resChar v) →* ((w.D Z).gat u v hg).Oˣ,
          Formalism.MainNotions.G.CmpJ.UnitCharacterChartCompatibility hj (tt.forms.ch u ((w.D Z).what₂.muAt v) hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).lev (t.cmp.embW u v hg) ψ := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQp O hO' hunf E hE Fl hfl hw u v hg hμ tt hstd j hj β
  haveI : IsFractionRing ((w.D Z).gat u v hg).O ((w.D Z).gat u v hg).Kf :=
    (((w.D Z).gat u v hg).P.setting (plc t.Gt u v hg)).frac_O
  exact GlobalTheory.Mem.Top.KerTwPsi.exists_psiTiedJ hj _ (tt.forms.car u _ hμ (j + 1) _ hj β).Uloc_eq (t.cmp.embW u v hg)
    (GlobalTheory.T.twisted_chain_chart_level_characters_rational w ‹_› ‹_› ‹_› Z t Wt nch n hmu tt hstd u _ hμ j hj β) (tt.forms.chi_fin u _ hμ (j + 1) _ hj β)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChainChartLocalUnitCharacterCompatibleLeveStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chainChart_localUnitCharacter_compatible_level : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m) (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)),
        ∃ ψ : Formalism.L2.G.awayG (w.D Z).sp.cm.sig ((w.D Z).sp.X (j + 1)).gram
            (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Uloc ((w.D Z).what₂.places.resChar v) →* ((w.D Z).gat u v hg).Oˣ,
          Formalism.MainNotions.G.CmpJ.UnitCharacterChartCompatibility hj (tt.forms.ch u ((w.D Z).what₂.muAt v) hμ (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).lev (t.cmp.embW u v hg) ψ := by
  first | exact @GlobalTheory.Mem.Top.KerTwPsi.psi_tied | exact GlobalTheory.Mem.Top.KerTwPsi.psi_tied | (intros; apply GlobalTheory.Mem.Top.KerTwPsi.psi_tied <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistRingMapLargeCoefficientRings
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistRingMapLargeCoefficientRings
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem GlobalTheory.HeckeLocN.exists_twRing_of_large : ∀ (D : D7) (C : NChoice D) (F : TwFrameC D) (low : Finset ℕ) (E0 : PlEmb D.what₂), TwistFrameLowIndexCompatibility D F low → ChoiceC D C → ∀ w : D.what₂.places.Pl, ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ (X : CoefIn D.what₂) (j : ℕ), X.E = E0 → F0.1 ≤ (X.Kx j w).1 → ∃ f : D.ntw.O0 (C.twI w) →+* OcC X j w, TwAlgAt C X j w f ∧ TwRdAt C X j w f ∧ (TwistedAt D w → ∀ (x : D.LL0) (y : D.ntw.O0 (C.twI w)), algebraMap (D.ntw.O0 (C.twI w)) (FractionRing (D.ntw.O0 (C.twI w))) y = (if C.sd w then D.ntw.emb0 (C.twI w) else D.ntw.emb0b (C.twI w)) x → ecC X j w (x : D.what₂.LL) = algebraMap (OcC X j w) (FractionRing (OcC X j w)) (f y)) := by
  intro D C F low E0 hT hC w
  obtain ⟨φ, hR, hn, ⟨K, hKf, hK⟩, halg⟩ :=
    GlobalTheory.HeightCounting.SameTw.exists_reads D C F hT w (D.what₂.places.resChar w) (C.twI_l w) (E0.emb w) (E0.emb_w w)
  refine ⟨⟨K, hKf⟩, ?_⟩
  intro X j hXE hle
  let g : D.ntw.O0 (C.twI w) →+* ↥(X.Kx j w).1 := φ.codRestrict (X.Kx j w).1 (fun y => hle (hK y))
  let f : D.ntw.O0 (C.twI w) →+* OcC X j w :=
    g.codRestrict (Loc.OL (X.Kx j w)) (fun y => (Formalism.BasicNotions.Examples₂.LB.mem_OL (X.Kx j w) (g y)).2 (hn y))
  have hf : ∀ y, iqC X j w (algebraMap (OcC X j w) (FractionRing (OcC X j w)) (f y)) = φ y := fun y => by
    rw [iqC_alg]; rfl
  have e1 : (iqC X j w).comp (ecC X j w) = E0.emb w := by
    ext x; rw [RingHom.comp_apply, iqC_ec, hXE]
  have e2 : (iqC X j w).comp ((algebraMap (OcC X j w) (FractionRing (OcC X j w))).comp f) = φ := by
    ext y; exact hf y
  have hRd : GlobalTheory.HeightCounting.SameTw.Reads D C w (ecC X j w) ((algebraMap (OcC X j w) (FractionRing (OcC X j w))).comp f) :=
    GlobalTheory.HeightCounting.SameTw.Reads.of_comp (iqC X j w) (by rw [e1, e2]; exact hR)
  refine ⟨f, ?_, hRd, fun hw x y hy => GlobalTheory.HeightCounting.SameTw.Reads.emb hC hw hRd x y hy⟩
  intro z z' hz
  apply Subtype.val_injective
  apply Subtype.val_injective
  change φ _ = _
  rw [halg z z' hz]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistRingMapLargeCoefficientRingsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twist_ring_map_large_coefficient_rings : ∀ (D : D7) (C : NChoice D) (F : TwFrameC D) (low : Finset ℕ) (E0 : PlEmb D.what₂), TwistFrameLowIndexCompatibility D F low → ChoiceC D C → ∀ w : D.what₂.places.Pl, ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ (X : CoefIn D.what₂) (j : ℕ), X.E = E0 → F0.1 ≤ (X.Kx j w).1 → ∃ f : D.ntw.O0 (C.twI w) →+* OcC X j w, TwAlgAt C X j w f ∧ TwRdAt C X j w f ∧ (TwistedAt D w → ∀ (x : D.LL0) (y : D.ntw.O0 (C.twI w)), algebraMap (D.ntw.O0 (C.twI w)) (FractionRing (D.ntw.O0 (C.twI w))) y = (if C.sd w then D.ntw.emb0 (C.twI w) else D.ntw.emb0b (C.twI w)) x → ecC X j w (x : D.what₂.LL) = algebraMap (OcC X j w) (FractionRing (OcC X j w)) (f y)) := by
  first | exact @GlobalTheory.HeckeLocN.exists_twRing_of_large | exact GlobalTheory.HeckeLocN.exists_twRing_of_large | (intros; apply GlobalTheory.HeckeLocN.exists_twRing_of_large <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupLeBaseLatticeLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupLeBaseLatticeLevel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem reL_symm_reL_self {E : Type} [Field E] [NumberField E] {a b : ℕ} (h : a = b) (L : Submodule (𝓞 E) (Fin a → E)) :
    reL h.symm (reL h L) = L := by
  subst h
  rw [Formalism.L2.Forms.reL_rfl, Formalism.L2.Forms.reL_rfl]


set_option maxHeartbeats 4000000 in
theorem chart_Uloc_le_levelVL_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom ≤ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0 := by
  intro B X I hI hP l Z Ch0 chOf0 F u a Q h1 Ch _ chOf K g _ hStd _ hRd _ _ Lb0 hLb β v _
  obtain ⟨k, H, -⟩ := hRd
  obtain ⟨c0⟩ := GlobalTheory.Mem.Col2.TC.stepBefore_cl_nonempty I hI u
  obtain ⟨k', H'⟩ := (hStd u).mid (B.R.m - 1) h1 (succ_pred_m _)
  have hKb : (K β).lev.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 := by
    rw [← hLb]
    ext x
    rw [← (F u).levJ_Lb h1 (chOf0 u (B.R.m - 1) c0)]
    exact (H.lb β x).trans (H'.lb _ x).symm
  have hle := (GlobalTheory.Port.formsLev_re (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (I.rec7 l Z).sp.cm.sig
    ((I.rec7 l Z).sp.X (B.R.m - 1)).gram (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _))
    (fun _ _ => rfl) (K β).lev v).1
  rw [hKb, reL_symm_reL_self] at hle
  exact hle

end GlobalTheory.Mem.Col2.TC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLocalGroupLeBaseLatticeLevelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_localGroup_le_baseLattice_level : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom ≤ levelVL (I.rec7 l Z).sp.cm.sig ((I.rec7 l Z).sp.X (B.R.m - 1)).gram v Lb0 := by
  first | exact @GlobalTheory.Mem.Col2.TC.chart_Uloc_le_levelVL_base | exact GlobalTheory.Mem.Col2.TC.chart_Uloc_le_levelVL_base | (intros; apply GlobalTheory.Mem.Col2.TC.chart_Uloc_le_levelVL_base <;> assumption)
end
end
