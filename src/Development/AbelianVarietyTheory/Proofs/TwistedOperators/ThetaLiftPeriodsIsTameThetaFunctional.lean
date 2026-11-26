module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightComparableWittDecomposition
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergOpArchimedeanSumRealPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDarbouxOrientedPairTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalVCutIdemOfNotMem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftPeriodsIsTameThetaFunctional
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftPeriodsIsTameThetaFunctional
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.LiftTame

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem tame_congr (hψ : IsStdChar D ψ (-1)) {ℓ ℓ' : (WO S T → ℂ) → ℂ} (h : Tame ψ S T ℓ)
    (e : ∀ f, IsThetaFunO ψ S T f → ℓ' f = ℓ f) : Tame ψ S T ℓ' := by
  have hh : ∀ f, IsThetaFunO ψ S T f → ∀ w, ℓ' (heisO ψ S T w f) = ℓ (heisO ψ S T w f) := fun f hf w =>
    e _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w)
  refine ⟨fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun f hf m _ α hα hI => ?_⟩
  · rw [e _ (GlobalTheory.WeilVacMove.isTheta_add hf hf'), e _ hf, e _ hf', h.add f f' hf hf']
  · rw [e _ (GlobalTheory.WeilVacMove.isTheta_smul c hf), e _ hf, h.smul c f hf]
  · simpa only [hh f hf] using h.cont f hf
  · simpa only [hh f hf] using h.bdd f hf
  · rw [e _ hI, h.sup f hf m α hα hI]
    simp only [hh f hf]

theorem finite_vol {V : HSp D} (v : GlobalTheory.Unf.Vol V) : IsFiniteMeasure (v.μ.restrict v.𝓕) := by
  have h : IntegrableOn (fun _ => (1 : ℝ)) v.𝓕 v.μ := by
    simpa using GlobalTheory.Size.integrableOn_inv_quotHeight_pow (V := V) 0 v.haar v.fund
  rcases (integrableOn_const_iff (by simp)).1 h with h | h
  · simp at h
  · exact isFiniteMeasure_restrict.2 h.ne

theorem tame_double {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T χS χT om) (vT : GlobalTheory.Unf.Vol T)
    {G : GA D T → ℂ} (hG : RapidDec T G) {A : HSp D} (vA : GlobalTheory.Unf.Vol A) {φ : GA D A → ℂ} (hφ : RapidDec A φ)
    {N : Type} [TopologicalSpace N] [SecondCountableTopology N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N)
    [IsFiniteMeasure ν] (K : GA D A → N → ℂ) (g : GA D A → N → GA D S)
    (hK : Continuous fun p : GA D A × N => K p.1 p.2) (hg : Continuous fun p : GA D A × N => g p.1 p.2)
    {C C' : ℝ} {a a' : ℕ} (hKb : ∀ h n, ‖K h n‖ ≤ C * (‖φ h‖ * quotHeight A h ^ a))
    (hgb : ∀ h n, quotHeight S (g h n) ≤ C' * quotHeight A h ^ a') :
    Tame ψ S T fun Φ => ∫ h in vA.𝓕, ∫ n, K h n * liftS om vT.μ vT.𝓕 G Φ (g h n) ∂ν ∂vA.μ := by
  obtain ⟨-, h2A, -, hbA, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨-, h2T, -, hbT, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  haveI := finite_vol vA
  haveI := finite_vol vT
  have hc : Continuous fun y : (GA D A × N) × GA D T => K y.1.1 y.1.2 * G y.2 :=
    (hK.comp continuous_fst).mul (hG.continuous.comp continuous_snd)
  have hg' : Continuous fun y : (GA D A × N) × GA D T => g y.1.1 y.1.2 := hg.comp continuous_fst
  obtain ⟨hI, hT⟩ := GlobalTheory.T.weilKernelFunctional_superposition_isTame D ψ S T χS χT om hom ((GA D A × N) × GA D T)
    (((vA.μ.restrict vA.𝓕).prod ν).prod (vT.μ.restrict vT.𝓕)) (fun y => K y.1.1 y.1.2 * G y.2) (fun y => g y.1.1 y.1.2)
    (fun y => y.2) (fun _ => 0) hc.measurable hg' continuous_snd continuous_const (fun k => by
      obtain ⟨M, hM⟩ := hφ.decay (a + a' * k)
      obtain ⟨M', hM'⟩ := hG.decay k
      refine Integrable.of_bound (hc.norm.mul ((((continuous_quotHeight S).comp hg').mul
        ((continuous_quotHeight T).comp continuous_snd)).pow k)).aestronglyMeasurable (|C| * |C'| ^ k * M * M')
        (Filter.Eventually.of_forall fun y => ?_)
      obtain ⟨⟨h, n⟩, t⟩ := y
      have p1 := (quotHeight_pos A h).le
      have p2 := (quotHeight_pos T t).le
      have p3 := (quotHeight_pos S (g h n)).le
      have b1 : ‖K h n‖ ≤ |C| * (‖φ h‖ * quotHeight A h ^ a) :=
        (hKb h n).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
      have b2 : quotHeight S (g h n) ≤ |C'| * quotHeight A h ^ a' :=
        (hgb h n).trans (mul_le_mul_of_nonneg_right (le_abs_self C') (by positivity))
      have hM0 : 0 ≤ M := le_trans (by positivity) (hM h)
      show ‖‖K h n * G t‖ * (quotHeight S (g h n) * quotHeight T t) ^ k‖ ≤ _
      rw [Real.norm_of_nonneg (by positivity), norm_mul]
      calc ‖K h n‖ * ‖G t‖ * (quotHeight S (g h n) * quotHeight T t) ^ k
          ≤ |C| * (‖φ h‖ * quotHeight A h ^ a) * ‖G t‖ * (|C'| * quotHeight A h ^ a' * quotHeight T t) ^ k := by gcongr
        _ = |C| * |C'| ^ k * (‖φ h‖ * quotHeight A h ^ (a + a' * k)) * (‖G t‖ * quotHeight T t ^ k) := by ring
        _ ≤ _ := by gcongr; exacts [hM h, hM' t])
  refine tame_congr hom.std hT fun f hf => ?_
  have h1 := hI f hf
  rw [integral_prod _ h1, integral_prod _ h1.integral_prod_left]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  simp only [liftS_apply]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  ring

theorem lift_periods_tame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) (vW : GlobalTheory.Unf.Vol W) (G : GA D W → ℂ), RapidDec W G → (∀ (ρ : ℕ) (B : BesL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om : Om B.V W), IsWeilDatumO ψ B.V W χ χ' om → ∀ φ, RapidDec B.A φ → Tame ψ B.V W fun Φ => B.per ψ φ (liftS om vW.μ vW.𝓕 G Φ)) ∧ ∀ (ρ : ℕ) (J : JacL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om : Om J.W W), IsWeilDatumO ψ J.W W χ χ' om → ∀ (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (χ₁ χ₂ : (AE D)ˣ →* Circle) (omz : Om J.W₀ L'), IsWeilDatumO ψ J.W₀ L' χ₁ χ₂ omz → ∀ φ Φ₀, RapidDec J.W₀ φ → IsThetaFunO ψ J.W₀ L' Φ₀ → Tame ψ J.W W fun Φ => J.per ψ ζ' omz φ (liftS om vW.μ vW.𝓕 G Φ) Φ₀ := by
  intro D ψ W vW G hG
  refine ⟨fun ρ B χ χ' om hom φ hφ => ?_, fun ρ J χ χ' om hom L' ζ' χ₁ χ₂ omz homz φ Φ₀ hφ hΦ₀ => ?_⟩
  · obtain ⟨-, h2, -, hb, ht, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.V
    haveI : SecondCountableTopology (flagN B.d) := TopologicalSpace.Subtype.secondCountableTopology (flagN B.d : Set (GA D B.V))
    haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) :=
      isFiniteMeasure_restrict.2 (by rw [B.vN.unit.2.2]; exact ENNReal.one_ne_top)
    obtain ⟨C₁, a₁, h₁⟩ := GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition D B.V B.V₀ ρ B.d
    obtain ⟨C₂, a₂, h₂⟩ := GlobalTheory.T.unitaryQuotientHeight_orthogonalSum_comparable D B.V₀ B.A B.L B.o
    have hn : Continuous fun p : GA D B.A × flagN B.d => p.2.1 := continuous_subtype_val.comp continuous_snd
    have := tame_double hom vW hG B.vA hφ (B.vN.ν.restrict B.vN.𝓝)
      (fun h (n : flagN B.d) => φ h * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n.1)) (fun h n => n.1 * embA B.d B.o h)
      ((hφ.continuous.comp continuous_fst).mul
        ((GlobalTheory.CharLaws.continuous_psiBes ψ B.d hom.std.1.1 1 (vecB B.o B.ζ)).comp hn).star)
      (hn.mul ((B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))).comp
        continuous_fst))
      (C := 1) (a := 0) (C' := |C₁| * |C₂| ^ a₁) (a' := a₂ * a₁) (fun h n => by
        have e : ‖psiBes ψ B.d 1 (vecB B.o B.ζ) n.1‖ = 1 := hom.std.1.2.1 _
        simp [e]) (fun h n => by
        have p1 := (quotHeight_pos B.A h).le
        have p2 := (quotHeight_pos B.V₀ (B.o.emb (h, 1))).le
        have b : quotHeight B.V₀ (B.o.emb (h, 1)) ≤ |C₂| * quotHeight B.A h ^ a₂ :=
          (h₂ h).2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
        calc _ ≤ C₁ * quotHeight B.V₀ (B.o.emb (h, 1)) ^ a₁ := (h₁ n.1 n.2 _).2
          _ ≤ |C₁| * (|C₂| * quotHeight B.A h ^ a₂) ^ a₁ := by gcongr; exact le_abs_self _
          _ = _ := by ring)
    convert this using 2 with Φ
    unfold BesL.per besPer besFun
    congr 1; funext h; congr 1; funext n; ring
  · obtain ⟨-, h2, -, hb, ht, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D J.W
    haveI : SecondCountableTopology (flagN J.d) := TopologicalSpace.Subtype.secondCountableTopology (flagN J.d : Set (GA D J.W))
    haveI : IsFiniteMeasure (J.vN.ν.restrict J.vN.𝓝) :=
      isFiniteMeasure_restrict.2 (by rw [J.vN.unit.2.2]; exact ENNReal.one_ne_top)
    obtain ⟨C₁, a₁, h₁⟩ := GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition D J.W J.W₀ ρ J.d
    obtain ⟨C₂, a₂, h₂⟩ := GlobalTheory.SupThetaGrowth.om_sup_quotHeight D ψ J.W₀ L' χ₁ χ₂ omz homz Φ₀ hΦ₀
    have hn : Continuous fun p : GA D J.W₀ × flagN J.d => p.2.1 := continuous_subtype_val.comp continuous_snd
    have hth : ∀ n h, thetaJS ψ J.d ζ' omz Φ₀ n h =
        ψ (cenS J.d L' (zEll L' ρ ζ') n) * omz (h, 1) Φ₀ (ptS J.d L' (zEll L' ρ ζ') n) := fun n h => by
      rw [thetaJS, GlobalTheory.Unf.FB.ThLaws.jacS_zero_apply]
    have hJ : Continuous fun p : (GA D J.W₀ × GA D L') × WO J.W₀ L' => omz p.1 Φ₀ p.2 :=
      (@GlobalTheory.Unf.jointCont_all D) ψ J.W₀ L' χ₁ χ₂ omz homz Φ₀ hΦ₀
    have hthc : Continuous fun p : GA D J.W₀ × flagN J.d => thetaJS ψ J.d ζ' omz Φ₀ p.2.1 p.1 := by
      simp only [hth]
      exact (hom.std.1.1.comp ((GlobalTheory.Unf.FB.ThLaws.continuous_cenS _ _ _).comp hn)).mul
        (hJ.comp ((continuous_fst.prodMk continuous_const).prodMk ((GlobalTheory.Unf.FB.ThLaws.continuous_ptS _ _ _).comp hn)))
    have := tame_double hom vW hG J.v0 hφ (J.vN.ν.restrict J.vN.𝓝)
      (fun h (n : flagN J.d) => φ h * star (thetaJS ψ J.d ζ' omz Φ₀ n.1 h) * star (psiFlag ψ J.d n.1))
      (fun h n => n.1 * J.d.emb0 h)
      (((hφ.continuous.comp continuous_fst).mul hthc.star).mul
        ((GlobalTheory.Unf.FB.ThLaws.continuous_psiFlag hom.std.1.1 _).comp hn).star)
      (hn.mul (J.d.continuous_embed.comp continuous_fst))
      (C := C₂ * quotHeight L' 1 ^ a₂) (a := a₂) (C' := C₁) (a' := a₁) (fun h n => by
        have e : ‖psiFlag ψ J.d n.1‖ = 1 := hom.std.1.2.1 _
        rw [norm_mul, norm_mul, norm_star, norm_star, e, hth, norm_mul, hom.std.1.2.1, one_mul, mul_one]
        refine (mul_le_mul_of_nonneg_left (h₂ h 1 _) (norm_nonneg _)).trans (le_of_eq ?_)
        ring) (fun h n => (h₁ n.1 n.2 _).2)
    convert this using 2 with Φ
    unfold JacL.per fjSrc fjSrcFun
    congr 1; funext h; congr 1; funext n; ring

end GlobalTheory.LiftTame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftPeriodsIsTameThetaFunctionalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_periods_isTameThetaFunctional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) (vW : GlobalTheory.Unf.Vol W) (G : GA D W → ℂ), RapidDec W G → (∀ (ρ : ℕ) (B : BesL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om : Om B.V W), IsWeilDatumO ψ B.V W χ χ' om → ∀ φ, RapidDec B.A φ → Tame ψ B.V W fun Φ => B.per ψ φ (liftS om vW.μ vW.𝓕 G Φ)) ∧ ∀ (ρ : ℕ) (J : JacL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om : Om J.W W), IsWeilDatumO ψ J.W W χ χ' om → ∀ (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (χ₁ χ₂ : (AE D)ˣ →* Circle) (omz : Om J.W₀ L'), IsWeilDatumO ψ J.W₀ L' χ₁ χ₂ omz → ∀ φ Φ₀, RapidDec J.W₀ φ → IsThetaFunO ψ J.W₀ L' Φ₀ → Tame ψ J.W W fun Φ => J.per ψ ζ' omz φ (liftS om vW.μ vW.𝓕 G Φ) Φ₀ := by
  first | exact @GlobalTheory.LiftTame.lift_periods_tame | exact GlobalTheory.LiftTame.lift_periods_tame | (intros; apply GlobalTheory.LiftTame.lift_periods_tame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceComponentArchLineComplexStructure
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceComponentArchLineComplexStructure
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer
noncomputable section

namespace GlobalTheory.CartanLinTransfer

variable {D : D7}

theorem phi_smul_realAd {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (a : AE D) :
    θ τ (infPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 1 • a)) = θ τ (infPart D a) := by
  rw [GlobalTheory.ArchLineSum.infPart_smul, map_mul, GlobalTheory.ArchLineSum.theta_realAd hθ, Complex.ofReal_one, one_mul]

theorem phi_incM {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : Type} (J : Matrix m n D.host.E) :
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J).map ((θ τ).comp (infPart D)) = J.map (tauE D τ) := by
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, ← (hθ τ).1]
  rfl

theorem cartH_gram {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) :
    (A.cart τ)ᴴ * gramAt D V τ = gramAt D V τ * A.cart τ := by
  have hu : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  have hJ : (Formalism.REAL.Jm (A.ε τ))ᴴ = Formalism.REAL.Jm (A.ε τ) := by
    ext a b; by_cases h : a = b
    · subst h; simp [Formalism.REAL.Jm, Matrix.conjTranspose_apply]; split_ifs <;> simp
    · simp [Formalism.REAL.Jm, Matrix.conjTranspose_apply, h, Ne.symm h]
  have hJJ : Formalism.REAL.Jm (A.ε τ) * Formalism.REAL.Jm (A.ε τ) = 1 := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext a; split_ifs <;> simp
  rw [← A.fr_gram τ, Fr.cart, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ, Matrix.conjTranspose_nonsing_inv]
  have h1 : ((A.fr τ)ᴴ)⁻¹ * (A.fr τ)ᴴ = 1 := Matrix.nonsing_inv_mul _ (by rw [Matrix.det_conjTranspose]; exact hu.star)
  have h2 : A.fr τ * (A.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  calc _ = (A.fr τ)ᴴ * (Formalism.REAL.Jm (A.ε τ) * (((A.fr τ)ᴴ)⁻¹ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
        simp only [Matrix.mul_assoc]
    _ = (A.fr τ)ᴴ * (Formalism.REAL.Jm (A.ε τ) * ((A.fr τ * (A.fr τ)⁻¹) * Formalism.REAL.Jm (A.ε τ))) * A.fr τ := by
        rw [h1, h2, Matrix.mul_one, Matrix.one_mul]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem cart_frSgn' (ε : Bool) {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) :
    (frSgn ε A).cart τ = (if ε then -1 else 1 : ℂ) • A.cart τ := by
  cases ε
  · simp [Fr.cart, frSgn]
  · have h : Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) = -Formalism.REAL.Jm (A.ε τ) := by
      ext a b
      by_cases hab : a = b
      · subst hab; cases h : A.ε τ a <;> simp [Formalism.REAL.Jm, h]
      · simp [Formalism.REAL.Jm, hab]
    show (A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) * A.fr τ = _
    rw [h, Matrix.mul_neg, Matrix.neg_mul]; simp [Fr.cart]

end GlobalTheory.CartanLinTransfer

namespace GlobalTheory.CartanLinTransfer

theorem map_conj_conj {m n : Type} (M : Matrix m n ℂ) : (M.map (starRingEnd ℂ)).map (starRingEnd ℂ) = M := by
  ext i j; simp

theorem map_conj_smul {m n : Type} (c : ℂ) (M : Matrix m n ℂ) :
    (c • M).map (starRingEnd ℂ) = (starRingEnd ℂ c) • M.map (starRingEnd ℂ) := by
  ext i j; simp

theorem map_conj_transpose {m n : Type} (M : Matrix m n ℂ) : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := by
  ext i j; simp [Matrix.conjTranspose_apply]

theorem alg_step {m n k : ℕ} (e : Fin m ≃ Fin k) (Ac G : Matrix (Fin n) (Fin n) ℂ) (Bc : Matrix (Fin m) (Fin m) ℂ)
    (P P' : Matrix (Fin n) (Fin k) ℂ) (s : ℂ) (hs : starRingEnd ℂ s = s) (hAG : Acᴴ * G = G * Ac)
    (h : P'.map (starRingEnd ℂ) =
      Complex.I • ((-s) • Ac * P.map (starRingEnd ℂ) * ((Matrix.reindex e e Bc).map (starRingEnd ℂ))ᵀ)) :
    P'ᵀ.submatrix e id * (s • G) = Complex.I • (Bc * (Pᵀ.submatrix e id * (s • G)) * (s • Ac)) := by
  have h2 := congrArg (fun M => M.map (starRingEnd ℂ)) h
  simp only [map_conj_conj, map_conj_smul, Matrix.map_mul, Matrix.transpose_map, Complex.conj_I, map_neg, hs] at h2
  rw [h2]
  have hsub : (Matrix.reindex e e Bc).submatrix e e = Bc := by
    ext i j; simp [Matrix.reindex_apply]
  have hprod : ∀ K : Matrix (Fin n) (Fin n) ℂ,
      (Matrix.reindex e e Bc * (Pᵀ * K)).submatrix e id = Bc * (Pᵀ.submatrix e id * K) := by
    intro K
    rw [← Matrix.submatrix_mul_equiv (Matrix.reindex e e Bc) (Pᵀ * K) e e id, hsub]
    congr 1
  rw [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_smul, map_conj_transpose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.submatrix_smul, Pi.smul_apply, smul_smul]
  rw [hprod]
  simp only [Matrix.mul_assoc, hAG]
  congr 1
  ring

end GlobalTheory.CartanLinTransfer


open GlobalTheory.CartanLinTransfer in
theorem GlobalTheory.CartanLinTransfer.compAt_archLine_cplxO : ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d),
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
    ∀ u u' : Matrix (Fin S.rank) (Fin d) (AE D),
      (∀ w, u'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
        Complex.I • (Vs.θ w * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Ws.θ w)ᵀ)) →
    ∀ τ, compAt θ τ (GlobalTheory.VacTransfer.archLine cS u' 1) =
      cplxO ((frSgn ε A).cart τ) (B.cart τ) (compAt θ τ (GlobalTheory.VacTransfer.archLine cS u 1)) := by
  intro D θ hθ ε S X A B d e Bs Vs Ws hBs cS hcS u u' hu τ
  obtain ⟨τw, hemb, hV, hW⟩ := hBs (InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)))
  set w : InfinitePlace D.host.F := InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)) with hw
  have hembR : (Bs.emb w).1 = (starRingEnd ℂ).comp (tauE D τw) := RingHom.ext hemb
  have hτ : τw = τ := by
    apply (GlobalTheory.CMTypePlaces.places_bijective D).1
    have h2 := (Bs.emb w).2
    rw [hembR] at h2
    have h3 := congrArg InfinitePlace.mk h2
    have hc : (starRingEnd ℂ).comp ((tauE D τw).comp (algebraMap D.host.F D.host.E)) =
        ComplexEmbedding.conjugate ((tauE D τw).comp (algebraMap D.host.F D.host.E)) :=
      RingHom.ext fun x => by simp [ComplexEmbedding.conjugate_coe_eq]
    rw [InfinitePlace.mk_embedding, RingHom.comp_assoc, hc, InfinitePlace.mk_conjugate_eq] at h3
    exact h3
  rw [hτ] at hembR hV hW
  have hcomp : ((starRingEnd ℂ).comp (tauE D τ)).comp (algebraMap D.host.F D.host.E) = w.embedding := by
    rw [← hembR]; exact (Bs.emb w).2
  have hE : Bs.emb w = ⟨(starRingEnd ℂ).comp (tauE D τ), hcomp⟩ := Subtype.ext hembR
  have hpi : ∀ y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w) y = starRingEnd ℂ (((θ τ).comp (infPart D)) y) := by
    intro y; rw [hE]; exact GlobalTheory.ConjInfExp.piInf_eq θ hθ τ w hcomp y
  have hmap : ∀ v : Matrix (Fin S.rank) (Fin d) (AE D),
      v.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) = (v.map ((θ τ).comp (infPart D))).map (starRingEnd ℂ) := by
    intro v; ext i j; simp only [Matrix.map_apply, hpi]
  have hu1 := hu w
  rw [hmap, hmap, hV, hW] at hu1
  have hz : ∀ v : Matrix (Fin S.rank) (Fin d) (AE D), compAt θ τ (GlobalTheory.VacTransfer.archLine cS v 1) =
      (v.map ((θ τ).comp (infPart D)))ᵀ.submatrix e id * ((if ε then -1 else 1 : ℂ) • gramAt D S τ) := by
    intro v
    show (cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 1 • v)).map ((θ τ).comp (infPart D)) = _
    rw [hcS, Matrix.map_mul, phi_incM hθ]
    congr 1
    · ext i j
      simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.smul_apply, id,
        RingHom.comp_apply, phi_smul_realAd hθ]
    · ext i j
      cases ε <;> simp [gramAt, Matrix.smul_apply]
  have hsgn : (if ε then 1 else -1 : ℂ) = -(if ε then -1 else 1 : ℂ) := by cases ε <;> simp
  have hs : starRingEnd ℂ (if ε then -1 else 1 : ℂ) = (if ε then -1 else 1 : ℂ) := by cases ε <;> simp
  rw [hsgn] at hu1
  rw [hz, hz, cart_frSgn', cplxO]
  exact alg_step e (A.cart τ) (gramAt D S τ) (B.cart τ) _ _ _ hs (cartH_gram A τ) hu1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceComponentArchLineComplexStructureStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceComponent_archLine_complexStructure : ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d),
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
    ∀ u u' : Matrix (Fin S.rank) (Fin d) (AE D),
      (∀ w, u'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
        Complex.I • (Vs.θ w * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Ws.θ w)ᵀ)) →
    ∀ τ, compAt θ τ (GlobalTheory.VacTransfer.archLine cS u' 1) =
      cplxO ((frSgn ε A).cart τ) (B.cart τ) (compAt θ τ (GlobalTheory.VacTransfer.archLine cS u 1)) := by
  first | exact @GlobalTheory.CartanLinTransfer.compAt_archLine_cplxO | exact GlobalTheory.CartanLinTransfer.compAt_archLine_cplxO | (intros; apply GlobalTheory.CartanLinTransfer.compAt_archLine_cplxO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepSchrodingerModelHalfSubstitution
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepSchrodingerModelHalfSubstitution
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchrodSubst

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

variable {D : D7} {S T : HSp D}

private lemma isSBHalf_psi_mul_halfInd {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)}
    (hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1)
    {y : WO S T} (hy : y ∈ half S T (cA D e)) {m : ℕ} (hm : 0 < m) (hmy : m • y ∈ Λ) :
    IsSBHalf e Λ (fun t => ψ (symplO S T t y) * halfInd e Λ t) := by
  have h0 : IsSBHalf e Λ (halfInd e Λ) := GlobalTheory.isSBHalf_halfInd e Λ
  unfold IsSBHalf at h0 ⊢
  obtain ⟨hsupp, k, hk, hinv, hlat⟩ := h0
  have hχ : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y
      rw [GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y
      rw [GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul]
    · intro y
      rw [GlobalTheory.PlaceModel.symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y
      rw [GlobalTheory.PlaceModel.symplO_zero_right, AddChar.map_zero_eq_one]
  refine ⟨fun t ht => hsupp t (right_ne_zero_of_mul ht), m * k, Nat.mul_pos hm hk, ?_, ?_⟩
  · intro u hu hue t
    have huh : u ∈ half S T e := (GlobalTheory.PlaceModel.isHalf_iff S T).1 hue
    have hmu : IsHalf e (m • u) := (GlobalTheory.PlaceModel.isHalf_iff S T).2 ((half S T e).nsmul_mem huh m)
    have hI : halfInd e Λ (t + (m * k) • u) = halfInd e Λ t := by
      rw [mul_comm, ← smul_smul]
      exact hinv (m • u) (Λ.nsmul_mem hu m) hmu t
    have hone : ψ (symplO S T ((m * k) • u) y) = 1 := by
      have hs := hχ.nsmul m (k • u) y
      rw [← smul_smul, hs]
      exact hLL' (k • u) ⟨Λ.nsmul_mem hu k, (half S T e).nsmul_mem huh k⟩ (m • y)
        ⟨hmy, (half S T (cA D e)).nsmul_mem hy m⟩
    have hsplit := hχ.left t ((m * k) • u) y
    beta_reduce
    rw [hI, hsplit, hone, mul_one]
  · intro t ht
    rw [← smul_smul]
    exact Λ.nsmul_mem (hlat t (right_ne_zero_of_mul ht)) m

theorem placeModel_wave {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)}
    (hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1)
    (hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ)
    {f₀ : WO S T → ℂ} {T₁ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ T₁) {x y : WO S T} (hx : IsHalf e x)
    (hy' : IsHalf (cA D e) y) :
    T₁ (wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y) =
      heisO ψ S T x (heisO ψ S T y f₀) := by
  obtain ⟨m, hm, hmy⟩ := hden y ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy')
  have hΦ0 : IsSBHalf e Λ (halfInd e Λ) := GlobalTheory.isSBHalf_halfInd e Λ
  have hΨ := isSBHalf_psi_mul_halfInd hLL' ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy') hm hmy
  have hwave : wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y =
      fun t => ψ (symplO S T (t + x) y) * halfInd e Λ (t + x) := by
    funext t
    simp only [GlobalTheory.PlaceModel.wave, GlobalTheory.PlaceModel.halfInd_eq_ind]
  have hvac : T₁ (halfInd e Λ) = f₀ := by simpa using h₁.vac
  rw [hwave, h₁.trans _ hΨ x hx, h₁.modul _ hΦ0 y hy', hvac]

theorem wave_actO (ψ : AddChar (AF D.host.F) ℂ) (e : AE D) {Λ : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T}
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) (x y : WO S T) :
    (fun t => wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y (actO S T g⁻¹ h⁻¹ t)) =
      wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) (actO S T g h x) (actO S T g h y) := by
  funext t
  have ht : actO S T g h (actO S T g⁻¹ h⁻¹ t) = t := by
    simpa using GlobalTheory.SplitHecke.actO_inv_actO g⁻¹ h⁻¹ t
  have hadd : t + actO S T g h x = actO S T g h (actO S T g⁻¹ h⁻¹ t + x) := by
    have := map_add (GlobalTheory.SplitHecke.actAdd S T g h) (actO S T g⁻¹ h⁻¹ t) x
    change actO S T g h (actO S T g⁻¹ h⁻¹ t + x) = actO S T g h (actO S T g⁻¹ h⁻¹ t) + actO S T g h x at this
    rw [this, ht]
  have hhalf : ∀ w : WO S T, actO S T g h w ∈ half S T e ↔ w ∈ half S T e := by
    intro w
    simp only [← GlobalTheory.PlaceModel.isHalf_iff]
    constructor
    · intro hw
      simpa [GlobalTheory.SplitHecke.actO_inv_actO] using GlobalTheory.SplitHecke.isHalf_actO g⁻¹ h⁻¹ hw
    · exact GlobalTheory.SplitHecke.isHalf_actO g h
  have hmem : ∀ w : WO S T, actO S T g h w ∈ Λ ⊓ half S T e ↔ w ∈ Λ ⊓ half S T e := by
    intro w
    simp only [AddSubgroup.mem_inf, hhalf, ← hΛ w]
  simp only [GlobalTheory.PlaceModel.wave]
  rw [hadd, GlobalTheory.SplitHecke.symplO_actO]
  simp only [GlobalTheory.PlaceModel.ind]
  by_cases hw : actO S T g⁻¹ h⁻¹ t + x ∈ Λ ⊓ half S T e
  · rw [if_pos hw, if_pos ((hmem _).2 hw)]
  · rw [if_neg hw, if_neg (fun hw' => hw ((hmem _).1 hw'))]

theorem om_placeModel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (a : AE D) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → a * a = a → infPart D a = 0 → IsThetaFunO ψ S T f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → ∀ (g : GA D S) (h : GA D T) (c : ℂ), (∀ u, u ∈ (latO S T ΛS ΛT fun _ => True) ↔ actO S T g h u ∈ (latO S T ΛS ΛT fun _ => True)) → om (g, h) f₀ = c • f₀ → ∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → om (g, h) (Tm Φ) = c • Tm fun x => Φ (actO S T g⁻¹ h⁻¹ x) := by
  intro D ψ S T χS χT om ΛS ΛT a f₀ Tm hW hS hT ha hinf hth hTm g h c hΛ hc Φ hΦ
  have hstd : IsStdChar D ψ (-1) := hW.std
  have hψ : IsCharAF D.host.F ψ := by
    unfold IsStdChar at hstd
    exact hstd.1
  have hdual := (GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hstd hS hT).1
  have hsm : ∀ w : AE D, w * w = w → ∀ u ∈ (latO S T ΛS ΛT fun _ => True),
      w • u ∈ (latO S T ΛS ΛT fun _ => True) := by
    intro w hw u hu
    refine GlobalTheory.LatticeStable.smul_mem_latO D S T ΛS ΛT (fun _ => True) w ?_ u hu
    exact GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hw])
  have hfm := GlobalTheory.LatFinMod.latO_finite_mod D S T ΛS ΛT hS.1.fg hT.1.fg (fun _ => True)
  have hnm : ∀ t : WO S T, t.map (infPart D) = 0 → ∃ k : ℕ, 0 < k ∧ k • t ∈ (latO S T ΛS ΛT fun _ => True) :=
    fun t ht => GlobalTheory.PlaceDatum.exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT hT) t ht
  generalize (latO S T ΛS ΛT fun _ => True) = Λ at hdual hsm hfm hnm hTm hΛ hΦ ⊢
  have hcA : cA D a * cA D a = cA D a := by rw [← map_mul, ha]
  have hinf' : infPart D (cA D a) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinf
  have hLL : ∀ u ∈ Λ ⊓ half S T a, ∀ y ∈ Λ ⊓ half S T (cA D a), ψ (symplO S T u y) = 1 := by
    intro u hu y hy
    rw [AddSubgroup.mem_inf] at hu hy
    exact (hdual u (GlobalTheory.PlaceDatum.infPart_of_half hinf ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hden : ∀ y ∈ half S T (cA D a), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ := fun y hy =>
    hnm y (GlobalTheory.PlaceDatum.infPart_of_half hinf' ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hy))
  have hXd : ∀ x ∈ half S T a, (∀ y ∈ Λ ⊓ half S T (cA D a), ψ (symplO S T x y) = 1) →
      x ∈ Λ ⊓ half S T a := by
    intro x hx hxy
    refine AddSubgroup.mem_inf.2 ⟨?_, hx⟩
    refine (hdual x (GlobalTheory.PlaceDatum.infPart_of_half hinf ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hx))).2 ?_
    intro u' hu'
    have hmem : cA D a • u' ∈ Λ ⊓ half S T (cA D a) := by
      refine AddSubgroup.mem_inf.2 ⟨hsm _ hcA u' hu', ?_⟩
      rw [GlobalTheory.PlaceModel.mem_half, smul_smul, hcA]
    have heq : symplO S T x u' = symplO S T x (cA D a • u') := by
      rw [← GlobalTheory.PlaceModel.symplO_smul, (GlobalTheory.PlaceModel.mem_half S T).1 hx]
    rw [heq]
    exact hxy _ hmem
  have hfin : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ Λ ⊓ half S T a, ∃ r ∈ R, ∃ u ∈ Λ ⊓ half S T a, t = r + k • u := by
    intro k hk
    obtain ⟨R, hR, hRt⟩ := hfm k hk
    refine ⟨(fun r => a • r) '' R, hR.image _, ?_⟩
    intro t ht
    rw [AddSubgroup.mem_inf] at ht
    obtain ⟨r, hr, u, hu, rfl⟩ := hRt t ht.1
    refine ⟨a • r, Set.mem_image_of_mem _ hr, a • u, AddSubgroup.mem_inf.2 ⟨hsm a ha u hu, ?_⟩, ?_⟩
    · rw [GlobalTheory.PlaceModel.mem_half, smul_smul, ha]
    · have h2 := (GlobalTheory.PlaceModel.mem_half S T).1 ht.2
      rw [smul_add, smul_comm a k u] at h2
      exact h2.symm
  have htf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk =>
    Function.LeftInverse.injective (g := fun t : WO S T => incA D (k : D.host.E)⁻¹ • t)
      (fun t => GlobalTheory.PlaceModel.inv_smul_nsmul S T hk t)
  have hspan : Φ ∈ GlobalTheory.PlaceModel.waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T a)
      (half S T (cA D a)) (Λ ⊓ half S T a) := by
    unfold IsSBHalf at hΦ
    obtain ⟨hsupp, k, hk, hinv, hlat⟩ := hΦ
    have hχ : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x x' y
        rw [GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul]
      · intro x y y'
        rw [GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul]
      · intro y
        rw [GlobalTheory.PlaceModel.symplO_zero_left, AddChar.map_zero_eq_one]
      · intro y
        rw [GlobalTheory.PlaceModel.symplO_zero_right, AddChar.map_zero_eq_one]
    refine GlobalTheory.PlaceDatum.mem_waveSpan (L' := Λ ⊓ half S T (cA D a)) hχ
      inf_le_right inf_le_right hLL hXd (fun k hk x hx => GlobalTheory.PlaceModel.half_div S T a k hk x hx)
      (fun k hk y hy => GlobalTheory.PlaceModel.half_div S T (cA D a) k hk y hy) htf hfin Φ
      (fun t ht => (GlobalTheory.PlaceModel.isHalf_iff S T).1 (hsupp t ht)) k hk ?_ ?_
    · intro u hu t
      rw [AddSubgroup.mem_inf] at hu
      exact hinv u hu.1 ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hu.2) t
    · intro t ht
      exact AddSubgroup.mem_inf.2 ⟨hlat t ht,
        (half S T a).nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (hsupp t ht)) k⟩
  clear hΦ
  unfold GlobalTheory.PlaceModel.waveSpan at hspan
  induction hspan using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hΨ
    have hxH : IsHalf a x := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hx
    have hyH : IsHalf (cA D a) y := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hy
    have hthy : IsThetaFunO ψ S T (heisO ψ S T y f₀) :=
      by
        simpa using GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ f₀ hth
          Unit {()} (fun _ => y) (fun _ => 1)
          (fun _ _ => GlobalTheory.PlaceDatum.infPart_of_half hinf' hyH)
    rw [placeModel_wave hLL hden hTm hxH hyH, hW.om_heis g h x _ hthy, hW.om_heis g h y f₀ hth, hc,
      GlobalTheory.SplitScalar.heisO_smul, GlobalTheory.SplitScalar.heisO_smul, wave_actO ψ a hΛ x y,
      placeModel_wave hLL hden hTm (GlobalTheory.SplitHecke.isHalf_actO g h hxH) (GlobalTheory.SplitHecke.isHalf_actO g h hyH)]
  | zero =>
    rw [show (fun x => (0 : WO S T → ℂ) (actO S T g⁻¹ h⁻¹ x)) = 0 from rfl]
    simp only [map_zero, smul_zero]
  | add Ψ₁ Ψ₂ _ _ ih₁ ih₂ =>
    rw [show (fun x => (Ψ₁ + Ψ₂) (actO S T g⁻¹ h⁻¹ x)) =
      (fun x => Ψ₁ (actO S T g⁻¹ h⁻¹ x)) + (fun x => Ψ₂ (actO S T g⁻¹ h⁻¹ x)) from rfl]
    simp only [map_add (f := _), ih₁, ih₂, smul_add]
  | smul r Ψ _ ih =>
    rw [show (fun x => (r • Ψ) (actO S T g⁻¹ h⁻¹ x)) = r • (fun x => Ψ (actO S T g⁻¹ h⁻¹ x)) from rfl]
    simp only [map_smul, ih]
    exact smul_comm r c _

end GlobalTheory.SchrodSubst

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepSchrodingerModelHalfSubstitutionStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_schrodingerModel_half_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (a : AE D) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → a * a = a → infPart D a = 0 → IsThetaFunO ψ S T f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → ∀ (g : GA D S) (h : GA D T) (c : ℂ), (∀ u, u ∈ (latO S T ΛS ΛT fun _ => True) ↔ actO S T g h u ∈ (latO S T ΛS ΛT fun _ => True)) → om (g, h) f₀ = c • f₀ → ∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → om (g, h) (Tm Φ) = c • Tm fun x => Φ (actO S T g⁻¹ h⁻¹ x) := by
  first | exact @GlobalTheory.SchrodSubst.om_placeModel | exact GlobalTheory.SchrodSubst.om_placeModel | (intros; apply GlobalTheory.SchrodSubst.om_placeModel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EigenOfLocalComponentsFiniteAdelicPair
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoPlaceComponentsFiniteAdelicUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoPlaceComponentsFiniteAdelicUnitary
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Filter Topology

namespace GlobalTheory.PlaceLimit

theorem sum_placeIdem {D : D7} {ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F}
    (hε : ∀ v, IsPlaceIdem D v (ε v)) (A : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    ∑ v ∈ A, ε v = pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A) := by
  choose α h0 h1 h2 using hε
  refine Prod.ext ?_ ?_
  · change fstA D.host.F (∑ v ∈ A, ε v) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun v _ => by rw [h0]; rfl
  · change sndA D.host.F (∑ v ∈ A, ε v) = GlobalTheory.LevelClosure.cutIdem A
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine RestrictedProduct.ext _ _ fun w => ?_
    change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w (∑ v ∈ A, sndA D.host.F (ε v)) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w (GlobalTheory.LevelClosure.cutIdem A)
    have e : ∀ v, sndA D.host.F (ε v) = α v := fun v => by rw [h0]; rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [e]
    by_cases hw : w ∈ A
    · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_mem hw,
        Finset.sum_eq_single w (fun v _ hv => h2 v w (Ne.symm hv)) (fun h => absurd hw h), h1]
    · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_notMem hw]
      exact Finset.sum_eq_zero fun v hv => h2 v w fun h => hw (h ▸ hv)

theorem pair_cutIdem_mul_self {F : Type} [Field F] [NumberField F] (A : Finset (HeightOneSpectrum (𝓞 F))) :
    pairA F 0 (GlobalTheory.LevelClosure.cutIdem A) * pairA F 0 (GlobalTheory.LevelClosure.cutIdem A) =
      pairA F 0 (GlobalTheory.LevelClosure.cutIdem A) := by
  refine Prod.ext (mul_zero _) ?_
  change GlobalTheory.LevelClosure.cutIdem A * GlobalTheory.LevelClosure.cutIdem A = GlobalTheory.LevelClosure.cutIdem A
  refine RestrictedProduct.ext _ _ fun w => ?_
  change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (GlobalTheory.LevelClosure.cutIdem A * GlobalTheory.LevelClosure.cutIdem A) =
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (GlobalTheory.LevelClosure.cutIdem A)
  rw [map_mul]
  by_cases hw : w ∈ A
  · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_mem hw, one_mul]
  · rw [GlobalTheory.LevelClosure.evalV_cutIdem_of_notMem hw, zero_mul]

theorem tendsto_cut_mul {D : D7} {z : AE D} (hz : infPart D z = 0) :
    Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) * z) atTop (𝓝 z) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have h : Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) atTop (𝓝 (pairA D.host.F 0 1)) := by
    have := GlobalTheory.LevelClosure.tendsto_cutIdem_mul (1 : Af D.host.F)
    simp only [mul_one] at this
    exact (tendsto_const_nhds (x := (0 : Ainf D.host.F))).prodMk_nhds this
  have h2 := h.smul_const z
  have e : pairA D.host.F 0 1 • z = z := by
    rw [Algebra.smul_def, mul_comm]
    exact GlobalTheory.PlaceDatum.mul_pair_one hz
  rw [e] at h2
  simpa only [Algebra.smul_def] using h2

theorem tendsto_mix {D : D7} (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) :
    Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) • Formalism.L2.Theta.mt V g +
        (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A))) •
          (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) atTop (𝓝 (Formalism.L2.Theta.mt V g)) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) _
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have h1 : infPart D (Formalism.L2.Theta.mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
    congrArg (fun u : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => u.1 i j) (show infHom V g = 1 from hg)
  have h2 : infPart D (Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) = 0 := by
    rw [RingHom.map_sub, h1, sub_eq_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact (RingHom.map_one _).symm
    · exact (RingHom.map_zero _).symm
  have h3 := (tendsto_cut_mul h2).add_const ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)
  rw [sub_add_cancel] at h3
  refine h3.congr fun A => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem eq_mix_of_mul {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {f : R} (hf : f * f = f)
    {a a' b b' : Matrix n n R} (ha : a * a' = 1) (hb : b' * b = 1)
    (h : b = f • a + (1 - f) • (1 : Matrix n n R)) : b' = f • a' + (1 - f) • (1 : Matrix n n R) := by
  have : b * (f • a' + (1 - f) • (1 : Matrix n n R)) = 1 := by
    rw [h, GlobalTheory.IdemSupport.mix_mul hf, ha, one_mul, GlobalTheory.IdemSupport.mix_self]
  calc b' = b' * (b * (f • a' + (1 - f) • (1 : Matrix n n R))) := by rw [this, mul_one]
    _ = _ := by rw [← mul_assoc, hb, one_mul]

theorem tendsto_components : ∀ (D : D7) (V : HSp D) (g : GA D V), g ∈ GfC V → ∀ (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F), (∀ v, IsPlaceIdem D v (ε v)) → ∀ gs : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V, (∀ A, Formalism.L2.Theta.mt V (gs A) = algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) • Formalism.L2.Theta.mt V g + (1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) → Filter.Tendsto gs Filter.atTop (nhds g) := by
  intro D V g hg ε hε gs hgs
  simp only [sum_placeIdem hε] at hgs
  have hinv : ∀ A, Formalism.L2.Theta.mt V (gs A)⁻¹ =
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A)) • Formalism.L2.Theta.mt V g⁻¹ +
        (1 - algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.LevelClosure.cutIdem A))) •
          (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := fun A =>
    eq_mix_of_mul (by rw [← RingHom.map_mul, pair_cutIdem_mul_self])
      (by rw [← GlobalTheory.IdemSupport.mt_mul, mul_inv_cancel, GlobalTheory.IdemSupport.mt_one])
      (by rw [← GlobalTheory.IdemSupport.mt_mul, inv_mul_cancel, GlobalTheory.IdemSupport.mt_one]) (hgs A)
  have h1 := (tendsto_mix V hg).congr fun A => (hgs A).symm
  have h2 := (tendsto_mix V (inv_mem hg)).congr fun A => (hinv A).symm
  refine tendsto_subtype_rng.2 (Units.isEmbedding_embedProduct.tendsto_nhds_iff.2 ?_)
  exact h1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h2)

end GlobalTheory.PlaceLimit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoPlaceComponentsFiniteAdelicUnitaryStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_placeComponents_finiteAdelicUnitary : ∀ (D : D7) (V : HSp D) (g : GA D V), g ∈ GfC V → ∀ (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F), (∀ v, IsPlaceIdem D v (ε v)) → ∀ gs : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V, (∀ A, Formalism.L2.Theta.mt V (gs A) = algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) • Formalism.L2.Theta.mt V g + (1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) → Filter.Tendsto gs Filter.atTop (nhds g) := by
  first | exact @GlobalTheory.PlaceLimit.tendsto_components | exact GlobalTheory.PlaceLimit.tendsto_components | (intros; apply GlobalTheory.PlaceLimit.tendsto_components <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EigenOfLocalComponentsFiniteAdelicPair
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceProduct

theorem mix_orth {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {e f : A} (h : e * f = 0)
    (a : Matrix n n A) :
    (e • a + (1 - e) • (1 : Matrix n n A)) * (f • a + (1 - f) • (1 : Matrix n n A)) =
      (e + f) • a + (1 - (e + f)) • (1 : Matrix n n A) := by
  have h1 : e * (1 - f) = e := by linear_combination -h
  have h2 : (1 - e) * f = f := by linear_combination -h
  have h3 : (1 - e) * (1 - f) = 1 - (e + f) := by linear_combination h
  simp only [add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul]
  rw [h, h1, h2, h3, zero_smul, zero_add, add_smul]
  abel

theorem sum_idem {A ι : Type} [CommRing A] (e : ι → A) (h1 : ∀ i, e i * e i = e i)
    (h2 : ∀ i j, i ≠ j → e i * e j = 0) (B : Finset ι) : (∑ i ∈ B, e i) * (∑ i ∈ B, e i) = ∑ i ∈ B, e i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => h2 i j (Ne.symm hj)) (fun hn => absurd hi hn), h1]

theorem exists_components (D : D7) (V : HSp D) (g : GA D V)
    (ε : HeightOneSpectrum (𝓞 D.host.F) → AF D.host.F) (hε : ∀ v, IsPlaceIdem D v (ε v)) :
    ∃ gs : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V,
      (∀ A, Formalism.L2.Theta.mt V (gs A) = algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) • Formalism.L2.Theta.mt V g +
        (1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v)) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) ∧
      gs ∅ = 1 ∧ ∀ v B (h : v ∉ B), gs (Finset.cons v B h) = gs {v} * gs B := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hsum : ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) = ∑ v ∈ A, algebraMap (AF D.host.F) (AE D) (ε v) :=
    fun A => map_sum _ _ _
  have hid : ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) * algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) =
        algebraMap (AF D.host.F) (AE D) (∑ v ∈ A, ε v) := by
    intro A
    rw [hsum]
    exact sum_idem (fun v => algebraMap (AF D.host.F) (AE D) (ε v))
      (fun v => GlobalTheory.IdemSupport.place_idem hΦ (hε v))
      (fun v w hvw => GlobalTheory.IdemSupport.place_orth hΦ (hε v) (hε w) hvw) A
  have hc := fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
    GlobalTheory.IdemSupport.cA_algebraMap (D := D) (∑ v ∈ A, ε v)
  choose gs hgs using fun A => GlobalTheory.IdemSupport.exists_piece V (hid A) (hc A) g
  refine ⟨gs, hgs, ?_, ?_⟩
  · apply GlobalTheory.IdemSupport.mt_inj V
    rw [hgs, GlobalTheory.IdemSupport.mt_one, Finset.sum_empty, map_zero, zero_smul, sub_zero, one_smul, zero_add]
  · intro v B hvB
    apply GlobalTheory.IdemSupport.mt_inj V
    rw [GlobalTheory.IdemSupport.mt_mul, hgs, hgs, hgs, Finset.sum_cons, Finset.sum_singleton, map_add (f := _)]
    refine (mix_orth ?_ _).symm
    rw [hsum, Finset.mul_sum]
    exact Finset.sum_eq_zero fun w hw =>
      GlobalTheory.IdemSupport.place_orth hΦ (hε v) (hε w) (fun hvw => hvB (by rw [hvw]; exact hw))

theorem eigen_of_local_components : ∀ (D : D7) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ), (∀ w, Continuous fun p : GA D S × GA D T => om p f w) → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (A : Finset (HeightOneSpectrum (𝓞 D.host.F))) (s : HeightOneSpectrum (𝓞 D.host.F) → ℂ), (∀ v, v ∉ A → s v = 1) → (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ∀ (g' : GA D S) (h' : GA D T), Formalism.L2.Theta.mt S g' = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt S g + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → Formalism.L2.Theta.mt T h' = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt T h + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) → om (g', h') f = s v • f) → om (g, h) f = (∏ v ∈ A, s v) • f := by
  intro D S T om f hcont g hg h hh A s hs hloc
  choose ε hε using fun v : HeightOneSpectrum (𝓞 D.host.F) => GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
  obtain ⟨gs, hgs, hgs0, hgsm⟩ := exists_components D S g ε hε
  obtain ⟨hs', hhs, hhs0, hhsm⟩ := exists_components D T h ε hε
  have key : ∀ B : Finset (HeightOneSpectrum (𝓞 D.host.F)), om (gs B, hs' B) f = (∏ v ∈ B, s v) • f := by
    intro B
    induction B using Finset.cons_induction with
    | empty =>
      rw [hgs0, hhs0, Finset.prod_empty, one_smul]
      show om 1 f = f
      rw [map_one]
      rfl
    | cons v B hvB ih =>
      have hv := hloc v (ε v) (hε v) (gs {v}) (hs' {v}) (by rw [hgs, Finset.sum_singleton])
        (by rw [hhs, Finset.sum_singleton])
      rw [hgsm v B hvB, hhsm v B hvB, ← Prod.mk_mul_mk, map_mul, Module.End.mul_apply, ih, map_smul, hv,
        smul_smul, Finset.prod_cons, mul_comm]
  have hpair : Filter.Tendsto (fun B => (gs B, hs' B)) Filter.atTop (nhds (g, h)) :=
    (GlobalTheory.T.tendsto_placeComponents_finiteAdelicUnitary D S g hg ε hε gs hgs).prodMk_nhds (GlobalTheory.T.tendsto_placeComponents_finiteAdelicUnitary D T h hh ε hε hs' hhs)
  funext w
  rw [Pi.smul_apply, smul_eq_mul]
  have ht := ((hcont w).tendsto (g, h)).comp hpair
  refine tendsto_nhds_unique ht (tendsto_const_nhds.congr' ?_)
  filter_upwards [Filter.eventually_ge_atTop A] with B hB
  show _ = om (gs B, hs' B) f w
  rw [key, Pi.smul_apply, smul_eq_mul, Finset.prod_subset hB fun v _ hv => hs v hv]

end GlobalTheory.PlaceProduct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EigenOfLocalComponentsFiniteAdelicPairStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_of_local_components_finiteAdelic_pair : ∀ (D : D7) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ), (∀ w, Continuous fun p : GA D S × GA D T => om p f w) → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (A : Finset (HeightOneSpectrum (𝓞 D.host.F))) (s : HeightOneSpectrum (𝓞 D.host.F) → ℂ), (∀ v, v ∉ A → s v = 1) → (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ∀ (g' : GA D S) (h' : GA D T), Formalism.L2.Theta.mt S g' = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt S g + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → Formalism.L2.Theta.mt T h' = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.mt T h + (1 - algebraMap (AF D.host.F) (AE D) ε) • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) → om (g', h') f = s v • f) → om (g, h) f = (∏ v ∈ A, s v) • f := by
  first | exact @GlobalTheory.PlaceProduct.eigen_of_local_components | exact GlobalTheory.PlaceProduct.eigen_of_local_components | (intros; apply GlobalTheory.PlaceProduct.eigen_of_local_components <;> assumption)
end
end
