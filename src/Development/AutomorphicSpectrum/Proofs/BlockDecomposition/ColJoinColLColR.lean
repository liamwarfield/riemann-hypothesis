module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Unfold2
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixMul

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColJoinColLColR
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold

section Join

variable {R : Type*} {m r s : ℕ}

def colJoin (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) : Matrix (Fin m) (Fin (r + s)) R :=
  Matrix.of fun i k => Sum.elim (y₁ i) (y₂ i) (finSumFinEquiv.symm k)

def colL (y : Matrix (Fin m) (Fin (r + s)) R) : Matrix (Fin m) (Fin r) R := Matrix.of fun i j => y i (Fin.castAdd s j)

def colR (y : Matrix (Fin m) (Fin (r + s)) R) : Matrix (Fin m) (Fin s) R := Matrix.of fun i j => y i (Fin.natAdd r j)

@[simp] theorem colJoin_castAdd (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) (i : Fin m) (j : Fin r) :
    colJoin y₁ y₂ i (Fin.castAdd s j) = y₁ i j := by
  simp [colJoin]

@[simp] theorem colJoin_natAdd (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) (i : Fin m) (j : Fin s) :
    colJoin y₁ y₂ i (Fin.natAdd r j) = y₂ i j := by
  simp [colJoin]

@[simp] theorem colL_colJoin (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) :
    colL (colJoin y₁ y₂) = y₁ := by
  ext i j; simp [colL]

@[simp] theorem colR_colJoin (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) :
    colR (colJoin y₁ y₂) = y₂ := by
  ext i j; simp [colR]

@[simp] theorem colJoin_colL_colR (y : Matrix (Fin m) (Fin (r + s)) R) : colJoin (colL y) (colR y) = y := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp [colL]
  · simp [colR]

theorem colJoin_injective {y₁ y₁' : Matrix (Fin m) (Fin r) R} {y₂ y₂' : Matrix (Fin m) (Fin s) R}
    (h : colJoin y₁ y₂ = colJoin y₁' y₂') : y₁ = y₁' ∧ y₂ = y₂' :=
  ⟨by rw [← colL_colJoin y₁ y₂, h, colL_colJoin], by rw [← colR_colJoin y₁ y₂, h, colR_colJoin]⟩

def joinEquiv : Matrix (Fin m) (Fin r) R × Matrix (Fin m) (Fin s) R ≃ Matrix (Fin m) (Fin (r + s)) R where
  toFun z := colJoin z.1 z.2
  invFun y := (colL y, colR y)
  left_inv z := by simp
  right_inv y := by simp

theorem colJoin_map {R' : Type*} (f : R → R') (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) :
    (colJoin y₁ y₂).map f = colJoin (y₁.map f) (y₂.map f) := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp

theorem colJoin_add [Add R] (y₁ y₁' : Matrix (Fin m) (Fin r) R) (y₂ y₂' : Matrix (Fin m) (Fin s) R) :
    colJoin (y₁ + y₁') (y₂ + y₂') = colJoin y₁ y₂ + colJoin y₁' y₂' := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp

theorem colJoin_neg [Neg R] (y₁ : Matrix (Fin m) (Fin r) R) (y₂ : Matrix (Fin m) (Fin s) R) :
    colJoin (-y₁) (-y₂) = -colJoin y₁ y₂ := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp

theorem colJoin_sub [Sub R] (y₁ y₁' : Matrix (Fin m) (Fin r) R) (y₂ y₂' : Matrix (Fin m) (Fin s) R) :
    colJoin (y₁ - y₁') (y₂ - y₂') = colJoin y₁ y₂ - colJoin y₁' y₂' := by
  ext i k
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k <;> simp

end Join

variable {D : D7}

theorem rat_colJoin {m r s : ℕ} (p : Matrix (Fin m) (Fin r) D.host.E) (q : Matrix (Fin m) (Fin s) D.host.E) :
    rat (colJoin p q) = colJoin (rat p) (rat q) :=
  colJoin_map _ p q

def cellTerm (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r s : ℕ} (b : Matrix (Fin r) (Fin r) D.host.E)
    (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p : Matrix (Fin V.rank) (Fin r) D.host.E) (q : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) : ℂ :=
  ψ (trA (Matrix.trace (inner V (rat q) y₂))) *
    (ψ (halfTr (Matrix.trace (HMul.hMul (rat b) (inner V (y₁ - rat p) (y₁ - rat p)) : Mx D r r))) *
      Φ (HMul.hMul (colJoin (rat p - y₁) (rat q)) (rat a)))

end GlobalTheory.CompanionTheory.EisUnfold

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSchwartzFunctionIntegrable
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSchwartzFunctionIntegrable
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Phase

def flat (S : Type) [AddCommGroup S] [TopologicalSpace S] (n M : ℕ) :
    (Fin n → Fin M → S) ≃ₜ+ (Fin 1 → Fin (n * M) → S) where
  toFun X _ p := X (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  invFun Y a i := Y 0 (finProdFinEquiv (a, i))
  left_inv X := by
    funext a i
    simp
  right_inv Y := by
    funext a p
    rw [Subsingleton.elim a 0]
    exact congrArg (Y 0) (finProdFinEquiv.apply_symm_apply p)
  map_add' X Y := by
    funext a p
    rfl
  continuous_toFun := continuous_pi fun _ => continuous_pi fun p =>
    (continuous_apply _).comp (continuous_apply _)
  continuous_invFun := continuous_pi fun _ => continuous_pi fun _ =>
    (continuous_apply _).comp (continuous_apply _)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem projInf_flat_symm {n M : ℕ} (Y : Fin 1 → Fin (n * M) → AF F ⊗[F] E) :
    projInf ((flat _ n M).symm Y) = (flat _ n M).symm (projInf Y) := rfl

theorem projFin_flat_symm {n M : ℕ} (Y : Fin 1 → Fin (n * M) → AF F ⊗[F] E) :
    projFin ((flat _ n M).symm Y) = (flat _ n M).symm (projFin Y) := rfl

theorem isSchwartzBruhat_flat {n M : ℕ} {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ}
    (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ) :
    GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (Φ ∘ (flat _ n M).symm) := by
  obtain ⟨k, P, Q, hP, hQ, hs⟩ := hΦ
  refine ⟨k, fun i => P i ∘ (flat _ n M).symm, fun i => Q i ∘ (flat _ n M).symm, fun i => ?_,
    fun i => ⟨(hQ i).1.comp_continuous (flat _ n M).symm.continuous,
      (hQ i).2.comp_homeomorph (flat _ n M).symm.toHomeomorph⟩, fun Y => ?_⟩
  · obtain ⟨N, e, c1, c2, f, hf⟩ := hP i
    refine ⟨N, (flat (Ainf F ⊗[F] E) n M).symm.toAddEquiv.trans e, c1.comp (flat _ n M).symm.continuous,
      (flat _ n M).continuous.comp c2, f, fun X => ?_⟩
    exact hf _
  · simp only [Function.comp_apply, hs, projInf_flat_symm, projFin_flat_symm]

theorem continuous_integrable [NumberField E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {n M : ℕ}
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : dx.IsAddHaarMeasure)
    {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ} (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ) :
    Continuous Φ ∧ Integrable Φ dx := by
  obtain ⟨h1, -, -, -, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI := hBor n M
  haveI := hBor 1 (n * M)
  let e := flat (AF F ⊗[F] E) n M
  haveI : (dx.map e).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map _ e.toAddEquiv.toAddMonoidHom e.continuous e.surjective
      e.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  obtain ⟨c, hi⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiInt.continuous_integrable_of_isSchwartzBruhat F E σ hCM (n * M)
    (dx.map e) inferInstance _ (isSchwartzBruhat_flat hΦ)
  have hcomp : (Φ ∘ e.symm) ∘ e = Φ := by
    funext X
    simp
  refine ⟨hcomp ▸ c.comp e.continuous, ?_⟩
  have := (e.toHomeomorph.measurableEmbedding.integrable_map_iff).1 hi
  rwa [show (Φ ∘ (flat _ n M).symm) ∘ e.toHomeomorph = Φ from hcomp] at this

theorem integrable_mul_phase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), dx.IsAddHaarMeasure →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
  ∀ b : HermR (AF F) σ n, Integrable (fun X => Φ X * ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X)))) dx := by
  intro F E _ _ _ _ _ σ hCM M J n ψ hψ dx hdx Φ hΦ b
  obtain ⟨h1, -, -, -, -, htr, -, hBor, -, hgram⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := h1
  haveI := hBor n M
  obtain ⟨hc, hi⟩ := continuous_integrable σ hCM dx hdx hΦ
  have hph : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E =>
      ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X))) := by
    refine hψ.1.comp (continuous_const.mul (htr.comp ?_))
    exact (continuous_const.matrix_mul (hgram n M J)).matrix_trace
  refine hi.mono (hc.mul hph).aestronglyMeasurable (Filter.Eventually.of_forall fun X => ?_)
  rw [norm_mul, hψ.2.1, mul_one]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Phase
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSchwartzFunctionIntegrableStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_schwartz_function_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), dx.IsAddHaarMeasure →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
  ∀ b : HermR (AF F) σ n, Integrable (fun X => Φ X * ψ (algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
      (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X)))) dx := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.integrable_mul_phase | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.integrable_mul_phase | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Phase.integrable_mul_phase <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMultiplierTemperate
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMultiplierTemperate
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WSum

section Tempered

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem tempered_mul_entry {l m n : Type*} [Fintype m] {M : W → Matrix l m ℂ} {N : W → Matrix m n ℂ}
    (hM : ∀ i j, Function.HasTemperateGrowth fun x => M x i j)
    (hN : ∀ i j, Function.HasTemperateGrowth fun x => N x i j) (i : l) (j : n) :
    Function.HasTemperateGrowth fun x => (M x * N x) i j := by
  simp only [Matrix.mul_apply]
  exact Function.HasTemperateGrowth.sum fun k _ => (hM i k).mul (hN k j)

theorem tempered_trace {n : Type*} [Fintype n] {M : W → Matrix n n ℂ}
    (hM : ∀ i j, Function.HasTemperateGrowth fun x => M x i j) :
    Function.HasTemperateGrowth fun x => (M x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Function.HasTemperateGrowth.sum fun k _ => hM k k

end Tempered

variable {D : D7} {r : ℕ}

def quadForm (D : D7) {m n : ℕ} (c : D.host.E) (G : Matrix (Fin m) (Fin m) D.host.E)
    (a : Matrix (Fin n) (Fin n) D.host.E) (X : D.what₂.Tau → Fin m → Fin n → ℂ) : ℝ :=
  -∑ τ, (tauE D τ c * Matrix.trace (a.map (tauE D τ) *
    ((Matrix.of (X τ))ᴴ * (G.map (tauE D τ) * Matrix.of (X τ))))).re

theorem tempered_quadForm (D : D7) {m n : ℕ} (c : D.host.E) (G : Matrix (Fin m) (Fin m) D.host.E)
    (a : Matrix (Fin n) (Fin n) D.host.E) :
    Function.HasTemperateGrowth fun X : D.what₂.Tau → Fin m → Fin n → ℂ => ((quadForm D c G a X : ℝ) : ℂ) := by
  have hc : ∀ (τ : D.what₂.Tau) (i : Fin m) (j : Fin n),
      Function.HasTemperateGrowth fun X : D.what₂.Tau → Fin m → Fin n → ℂ => Matrix.of (X τ) i j := fun τ i j =>
    (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) i).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) τ))).hasTemperateGrowth)
  have hs : ∀ (τ : D.what₂.Tau) (i : Fin n) (j : Fin m),
      Function.HasTemperateGrowth fun X : D.what₂.Tau → Fin m → Fin n → ℂ => (Matrix.of (X τ))ᴴ i j := fun τ i j =>
    (((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) j).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin m → Fin n → ℂ) τ)))).hasTemperateGrowth)
  have hg : ∀ τ : D.what₂.Tau, Function.HasTemperateGrowth fun X : D.what₂.Tau → Fin m → Fin n → ℂ =>
      tauE D τ c * Matrix.trace (a.map (tauE D τ) *
        ((Matrix.of (X τ))ᴴ * (G.map (tauE D τ) * Matrix.of (X τ)))) := fun τ =>
    (Function.HasTemperateGrowth.const _).mul (tempered_trace
      (tempered_mul_entry (fun _ _ => Function.HasTemperateGrowth.const _)
        (tempered_mul_entry (hs τ)
          (tempered_mul_entry (fun _ _ => Function.HasTemperateGrowth.const _) (hc τ)))))
  have hsum := Function.HasTemperateGrowth.sum (s := Finset.univ) fun τ (_ : τ ∈ Finset.univ) =>
    ((-(Complex.ofRealCLM.comp Complex.reCLM)).hasTemperateGrowth).comp (hg τ)
  convert hsum using 1
  funext X
  simp [quadForm]

theorem theta_incA {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : D.host.E) :
    θ τ (infPart D (incA D e)) = tauE D τ e :=
  (hθ τ).1 e

theorem compAt_mul' (θ : InfFam D) (τ : D.what₂.Tau) {l m n : ℕ} (x : Mx D l m) (y : Mx D m n) :
    compAt θ τ (HMul.hMul x y : Mx D l n) = compAt θ τ x * compAt θ τ y := by
  have := Matrix.map_mul (L := x) (M := y) (f := (θ τ).comp (infPart D))
  exact this

theorem compAt_adj {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ} (y : Mx D m n) :
    compAt θ τ (adj y) = (compAt θ τ y)ᴴ := by
  ext i j
  simp only [compAt, adj, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
  rw [GlobalTheory.PhaseReal.infPart_cA, GlobalTheory.Mem.VolExists.infEmb_sigR (Formalism.MainNotions.UnusedSlot34.isCMExt_D D) (hθ τ)]
  rfl

theorem compAt_rat {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) D.host.E) : compAt θ τ (rat M) = M.map (tauE D τ) := by
  ext i j
  simp only [compAt, rat, Matrix.map_apply]
  exact theta_incA hθ τ _

theorem multM_eq_quadForm {θ : InfFam D} (hθ : IsInfFam θ) (α : D.host.F) (V : HSp D) (a : HermE D r)
    (y : Mx D V.rank r) :
    multM θ α V a y = quadForm D (algebraMap D.host.F D.host.E α) (HSpace.gram V) a.1
      (fun τ i j => compAt θ τ y i j) := by
  unfold multM lam quadForm
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_mul, map_mul, theta_incA hθ, GlobalTheory.PhaseReal.theta_pair θ hθ]
  congr 3
  show _ * compAt θ τ (inner V y y) = _
  congr 1
  unfold GlobalTheory.StdUnn.inner
  rw [compAt_mul', compAt_mul', compAt_adj hθ, gA, compAt_rat hθ]
  rfl

theorem multM_tempered : ∀ (D : D7) (r : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (α : D.host.F) (V : HSp D) (a : HermE D r), ∃ q : (D.what₂.Tau → Fin V.rank → Fin r → ℂ) → ℂ, q.HasTemperateGrowth ∧ ∀ y, ((multM θ α V a y : ℝ) : ℂ) = q (fun τ i j => compAt θ τ y i j) := by
  intro D r θ hθ α V a
  refine ⟨fun X => ((quadForm D (algebraMap D.host.F D.host.E α) (HSpace.gram V) a.1 X : ℝ) : ℂ),
    tempered_quadForm D _ _ _, fun y => ?_⟩
  rw [multM_eq_quadForm hθ]

end GlobalTheory.CompanionTheory.WSum
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMultiplierTemperateStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_multiplier_temperate : ∀ (D : D7) (r : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (α : D.host.F) (V : HSp D) (a : HermE D r), ∃ q : (D.what₂.Tau → Fin V.rank → Fin r → ℂ) → ℂ, q.HasTemperateGrowth ∧ ∀ y, ((multM θ α V a y : ℝ) : ℂ) = q (fun τ i j => compAt θ τ y i j) := by
  first | exact @GlobalTheory.CompanionTheory.WSum.multM_tempered | exact GlobalTheory.CompanionTheory.WSum.multM_tempered | (intros; apply GlobalTheory.CompanionTheory.WSum.multM_tempered <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieActionSkewAdjointL2
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieActionSkewAdjointL2
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary PositivityTheory.S2.Clozel Filter Topology
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.PeterssonSkew

theorem integral_deriv_eq_zero {Q : Type*} [MeasurableSpace Q] (ν : Measure Q) [IsFiniteMeasure ν]
    (u v u' v' : ℝ → Q → ℂ) (C : ℝ)
    (hu : ∀ t q, HasDerivAt (fun s => u s q) (u' t q) t) (hv : ∀ t q, HasDerivAt (fun s => v s q) (v' t q) t)
    (bu : ∀ t q, ‖u t q‖ ≤ C) (bv : ∀ t q, ‖v t q‖ ≤ C) (bu' : ∀ t q, ‖u' t q‖ ≤ C) (bv' : ∀ t q, ‖v' t q‖ ≤ C)
    (mu : ∀ t, AEStronglyMeasurable (u t) ν) (mv : ∀ t, AEStronglyMeasurable (v t) ν)
    (mu' : AEStronglyMeasurable (u' 0) ν) (mv' : AEStronglyMeasurable (v' 0) ν)
    (hc : ∀ t, ∫ q, u t q * conj (v t q) ∂ν = ∫ q, u 0 q * conj (v 0 q) ∂ν) :
    ∫ q, (u' 0 q * conj (v 0 q) + u 0 q * conj (v' 0 q)) ∂ν = 0 := by
  have mc : ∀ {f : Q → ℂ}, AEStronglyMeasurable f ν → AEStronglyMeasurable (fun q => conj (f q)) ν :=
    fun h => Complex.continuous_conj.comp_aestronglyMeasurable h
  have hC : 0 ≤ C ∨ IsEmpty Q := by
    by_cases h : Nonempty Q
    · obtain ⟨q⟩ := h
      exact Or.inl ((norm_nonneg _).trans (bu 0 q))
    · exact Or.inr (not_nonempty_iff.1 h)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun t q => u t q * conj (v t q))
    (F' := fun t q => u' t q * conj (v t q) + u t q * conj (v' t q))
    (bound := fun _ => C * C + C * C) Filter.univ_mem
    (Eventually.of_forall fun t => (mu t).mul (mc (mv t)))
    (Integrable.of_bound ((mu 0).mul (mc (mv 0))) (C * C) (Eventually.of_forall fun q => by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (bu 0 q) (bv 0 q) (norm_nonneg _) ((norm_nonneg _).trans (bu 0 q))))
    ((mu'.mul (mc (mv 0))).add ((mu 0).mul (mc mv')))
    (Eventually.of_forall fun q t _ => by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul, RCLike.norm_conj]
      · exact mul_le_mul (bu' t q) (bv t q) (norm_nonneg _) ((norm_nonneg _).trans (bu' t q))
      · exact mul_le_mul (bu t q) (bv' t q) (norm_nonneg _) ((norm_nonneg _).trans (bu t q)))
    (integrable_const _)
    (Eventually.of_forall fun q t _ => (hu t q).mul (hv t q).star)
  have h0 : HasDerivAt (fun t : ℝ => ∫ q, u t q * conj (v t q) ∂ν) 0 0 := by
    simp only [hc]
    exact hasDerivAt_const _ _
  exact key.2.unique h0

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


open scoped Matrix.Norms.Operator in
theorem exists_curve (X : Lie E a) : ∃ c : ℝ → Matrix.GeneralLinearGroup (Fin a) (Cinf E), c 0 = 1 ∧
    (∀ s t, c (s + t) = c s * c t) ∧ HasDerivAt (fun t => toL (c t).val) X 0 := by
  set Y : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of X with hY
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  have hadd : ∀ s t : ℝ, NormedSpace.exp ((s + t) • Y) = NormedSpace.exp (s • Y) * NormedSpace.exp (t • Y) := fun s t => by
    rw [add_smul]
    exact NormedSpace.exp_add_of_commute (((Commute.refl Y).smul_left s).smul_right t)
  have hone : ∀ t : ℝ, NormedSpace.exp (t • Y) * NormedSpace.exp ((-t) • Y) = 1 := fun t => by
    rw [← hadd, add_neg_cancel, zero_smul, NormedSpace.exp_zero]
  refine ⟨fun t => ⟨NormedSpace.exp (t • Y), NormedSpace.exp ((-t) • Y), hone t, by simpa using hone (-t)⟩,
    Units.ext (by simp [NormedSpace.exp_zero]), fun s t => Units.ext (hadd s t), ?_⟩
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_translate {X : Lie E a} {c : ℝ → Matrix.GeneralLinearGroup (Fin a) (Cinf E)} (h0 : c 0 = 1)
    (hadd : ∀ s t, c (s + t) = c s * c t) (hX : HasDerivAt (fun t => toL (c t).val) X 0) (φ : Sm E a) (g : GA E a)
    (t : ℝ) : HasDerivAt (fun s => φ.1 (g * infGL E a (c s))) (lieD X φ.1 (g * infGL E a (c t))) t := by
  have h := hasDerivAt_curve φ (g * infGL E a (c t)) c X h0 hX
  have h2 : HasDerivAt (fun s => φ.1 (g * infGL E a (c t) * infGL E a (c (s - t))))
      (lieD X φ.1 (g * infGL E a (c t))) t := HasDerivAt.comp_sub_const t t (by simpa using h)
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [mul_assoc, ← map_mul, ← hadd]
  simp

theorem pet_mul_right (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {φ ψ : GA E a → ℂ}
    (hφ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ) (hψ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ ψ) (g : GA E a) :
    pet (GlobalTheory.UnitaryBC.latticeGL E a) μ (fun x => φ (x * g)) (fun x => ψ (x * g)) =
      pet (GlobalTheory.UnitaryBC.latticeGL E a) μ φ ψ := by
  rw [← MemL2Quotient.inner_toL2_eq_theta_pairing (hφ.mul_right g) (hψ.mul_right g), ← right_translate_toL2, ← right_translate_toL2, ← MemL2Quotient.inner_toL2_eq_theta_pairing hφ hψ]
  exact LinearIsometry.inner_map_map
    { toLinearMap := (R (GlobalTheory.UnitaryBC.latticeGL E a) μ g :
        L2 (GlobalTheory.UnitaryBC.latticeGL E a) μ →L[ℂ] L2 (GlobalTheory.UnitaryBC.latticeGL E a) μ).toLinearMap
      norm_map' := norm_R g } _ _

theorem pet_lie_add (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : Lie E a) (φ ψ : Sm E a)
    (hφ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1) (hψ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ ψ.1)
    (hφ' : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X φ).1)
    (hψ' : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X ψ).1)
    (C : ℝ) (bφ : ∀ g, ‖φ.1 g‖ ≤ C) (bψ : ∀ g, ‖ψ.1 g‖ ≤ C)
    (bφ' : ∀ g, ‖(lie E a X φ).1 g‖ ≤ C) (bψ' : ∀ g, ‖(lie E a X ψ).1 g‖ ≤ C) :
    pet (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X φ).1 ψ.1 +
      pet (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 (lie E a X ψ).1 = 0 := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  obtain ⟨c, h0, hadd, hX⟩ := exists_curve X
  have e0 : infGL E a (c 0) = 1 := by rw [h0, map_one]
  have key := integral_deriv_eq_zero (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GlobalTheory.UnitaryBC.latticeGL E a) μ)
    (fun t q => φ.1 (q.out * infGL E a (c t))) (fun t q => ψ.1 (q.out * infGL E a (c t)))
    (fun t q => lieD X φ.1 (q.out * infGL E a (c t))) (fun t q => lieD X ψ.1 (q.out * infGL E a (c t))) C
    (fun t q => hasDerivAt_translate h0 hadd hX φ q.out t) (fun t q => hasDerivAt_translate h0 hadd hX ψ q.out t)
    (fun _ _ => bφ _) (fun _ _ => bψ _) (fun _ _ => bφ' _) (fun _ _ => bψ' _)
    (fun t => (hφ.mul_right (infGL E a (c t))).2.aestronglyMeasurable) (fun t => (hψ.mul_right (infGL E a (c t))).2.aestronglyMeasurable)
    (by simp only [e0, mul_one]; exact hφ'.2.aestronglyMeasurable) (by simp only [e0, mul_one]; exact hψ'.2.aestronglyMeasurable)
    (fun t => by
      have h1 := pet_mul_right μ hφ hψ (infGL E a (c t))
      simp only [e0, mul_one]
      exact h1)
  simp only [e0, mul_one] at key
  exact (integral_add (hφ'.integrable_mul_conj hψ) (hφ.integrable_mul_conj hψ')).symm.trans key

theorem lie_skew_adjoint : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a) (hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1), (∀ φ ∈ π.V, ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) → ∀ (X : Lie E a) (φ ψ : π.V), inner ℂ (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm ψ) (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm (π.op (.lie X) φ)) = -inner ℂ (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm (π.op (.lie X) ψ)) (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm φ) := by
  intro E _ _ _ a μ _ _ π hm hb X φ ψ
  have hL : ∀ f : π.V, ∃ C : ℝ, ∀ g, ‖f.1.1 g‖ ≤ C := fun f => hb f.1 f.2
  obtain ⟨C₁, b₁⟩ := hL φ
  obtain ⟨C₂, b₂⟩ := hL ψ
  obtain ⟨C₃, b₃⟩ := hL (π.op (.lie X) φ)
  obtain ⟨C₄, b₄⟩ := hL (π.op (.lie X) ψ)
  have h := pet_lie_add μ X φ.1 ψ.1 (hm _ φ.2) (hm _ ψ.2) (hm _ (π.op (.lie X) φ).2) (hm _ (π.op (.lie X) ψ).2)
    (max (max C₁ C₂) (max C₃ C₄))
    (fun g => (b₁ g).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (fun g => (b₂ g).trans ((le_max_right _ _).trans (le_max_left _ _)))
    (fun g => (b₃ g).trans ((le_max_left _ _).trans (le_max_right _ _)))
    (fun g => (b₄ g).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have e1 := MemL2Quotient.inner_toL2_eq_theta_pairing (hm _ (π.op (.lie X) φ).2) (hm _ ψ.2)
  have e2 := MemL2Quotient.inner_toL2_eq_theta_pairing (hm _ φ.2) (hm _ (π.op (.lie X) ψ).2)
  change inner ℂ (hm _ ψ.2).toL2 (hm _ (π.op (.lie X) φ).2).toL2 =
    -inner ℂ (hm _ (π.op (.lie X) ψ).2).toL2 (hm _ φ.2).toL2
  rw [e1, e2]
  exact eq_neg_of_add_eq_zero_left h

end GlobalTheory.CompanionTheory.PeterssonSkew
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieActionSkewAdjointL2Statement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_action_skew_adjoint_L2 : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a) (hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1), (∀ φ ∈ π.V, ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) → ∀ (X : Lie E a) (φ ψ : π.V), inner ℂ (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm ψ) (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm (π.op (.lie X) φ)) = -inner ℂ (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm (π.op (.lie X) ψ)) (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm φ) := by
  first | exact @GlobalTheory.CompanionTheory.PeterssonSkew.lie_skew_adjoint | exact GlobalTheory.CompanionTheory.PeterssonSkew.lie_skew_adjoint | (intros; apply GlobalTheory.CompanionTheory.PeterssonSkew.lie_skew_adjoint <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreMeasureUnramified
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreMeasureUnramified
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.AvgV

theorem ae_lift_eq {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure V} {ν : Measure X} {q : V → Y} {ι : X → Y} {W : Set V} {B : Set X} {fib : X → Measure V}
    (h : IsFibreFamily μ q ι W ν B fib) {g : V → X} (hg : ∀ x, q x = ι (g x)) (hι : Function.Injective ι)
    (b : X) : ∀ᵐ x ∂(fib b), g x = b := by
  refine measure_mono_null ?_ (h.1 b)
  intro x hx hx'
  exact hx (hι ((hg x).symm.trans hx'.1))

theorem fibre_mass_on {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure V} {ν : Measure X} {q : V → Y} {ι : X → Y} {W : Set V} {B : Set X}
    {fib : X → Measure V} (h : IsFibreFamily μ q ι W ν B fib) {g : V → X} (hg : ∀ x, q x = ι (g x))
    (hι : Function.Injective ι) (hgm : Measurable g) {A : Set V} {S : Set X} (hA : MeasurableSet A)
    (hS : MeasurableSet S) (hW : A ∩ g ⁻¹' S ⊆ W) :
    μ (A ∩ g ⁻¹' S) = ∫⁻ s in S, fib s A ∂ν := by
  have hT : MeasurableSet (A ∩ g ⁻¹' S) := hA.inter (hgm hS)
  have e := h.2.1 ((A ∩ g ⁻¹' S).indicator 1) (measurable_one.indicator hT)
  simp only [lintegral_indicator_one hT] at e
  rw [Measure.restrict_apply hT, Set.inter_eq_left.2 hW] at e
  rw [e, ← lintegral_indicator hS]
  refine lintegral_congr fun b => ?_
  have hae := ae_lift_eq h hg hι b
  by_cases hb : b ∈ S
  · rw [Set.indicator_of_mem hb]
    refine measure_congr ?_
    filter_upwards [hae] with x hx
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    show g x ∈ S
    rwa [hx]
  · rw [Set.indicator_of_notMem hb]
    refine measure_mono_null (t := {x | ¬ g x = b}) ?_ hae
    intro x hx hxb
    apply hb
    rw [← hxb]
    exact hx.2

theorem avg_gen {V X Y : Type} {_ : TopologicalSpace V} {_ : MeasurableSpace V} {_ : TopologicalSpace X}
    {_ : MeasurableSpace X} {_ : AddCommGroup X} {μ : Measure V} {ν : Measure X} {q : V → Y} {ι : X → Y}
    {W : Set V} {B : Set X} {fib : X → Measure V} (h : IsFibreFamily μ q ι W ν B fib) {g : V → X}
    (hg : ∀ x, q x = ι (g x)) (hι : Function.Injective ι) (hgc : Continuous g) (hV2 : T2Space V)
    (hVb : BorelSpace V) (hX2 : T2Space X) (hXb : BorelSpace X) (hXg : IsTopologicalAddGroup X)
    (hXl : LocallyCompactSpace X) (hXs : SecondCountableTopology X) (hμ : IsFiniteMeasureOnCompacts μ)
    (hν : ν.IsAddHaarMeasure) (hB : IsOpen B) (hWB : ∀ x, g x ∈ B → x ∈ W) {c : X} (hc : c ∈ B) {A : Set V}
    (hAc : IsCompact A) (hAo : IsOpen A) {U : ℕ → Set X} (hU : ∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : X) ∈ U k)
    (hUt : Filter.Tendsto U Filter.atTop (nhds (0 : X)).smallSets) :
    (∀ k, MeasurableSet (A ∩ {x | c - g x ∈ U k}) ∧ μ (A ∩ {x | c - g x ∈ U k}) ≠ ⊤) ∧
      Filter.Tendsto (fun k => (μ (A ∩ {x | c - g x ∈ U k})).toReal / (ν (U k)).toReal) Filter.atTop
        (nhds (fib c A).toReal) := by
  haveI : ν.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
  have hBc := hB.mem_nhds hc

  let S : ℕ → Set X := fun k => {s | c - s ∈ U k}
  have hSo : ∀ k, IsOpen (S k) := fun k => (hU k).2.1.preimage (continuous_const.sub continuous_id)
  have hSm : ∀ k, MeasurableSet (S k) := fun k => (hSo k).measurableSet
  have hSc : ∀ k, c ∈ S k := fun k => by
    show c - c ∈ U k
    rw [sub_self]
    exact (hU k).2.2
  have hSU : ∀ k, ν (S k) = ν (U k) := fun k =>
    (Measure.measurePreserving_sub_left _ c).measure_preimage (hU k).2.1.measurableSet.nullMeasurableSet
  have hpos : ∀ k, ν (S k) ≠ 0 := fun k => (hSo k).measure_ne_zero _ ⟨c, hSc k⟩
  have htop : ∀ k, ν (S k) ≠ ⊤ := fun k => by
    rw [hSU]
    exact (hU k).1.measure_lt_top.ne
  have hl : Filter.Tendsto S Filter.atTop (nhds c).smallSets := by
    rw [Filter.tendsto_smallSets_iff]
    intro t ht
    have hcont : Filter.Tendsto (fun u : X => c - u) (nhds 0) (nhds c) := by
      have : Continuous fun u : X => c - u := continuous_const.sub continuous_id
      simpa using this.tendsto 0
    have h0 := (Filter.tendsto_smallSets_iff.1 hUt) _ (hcont ht)
    filter_upwards [h0] with k hk s hs
    have := hk (show c - s ∈ U k from hs)
    simpa using this

  obtain ⟨k0, hk0⟩ := (hl.eventually (Filter.eventually_smallSets_subset.2 hBc)).exists
  have hNc : IsCompact (S k0) := (Homeomorph.subLeft c).isCompact_preimage.2 (hU k0).1
  let A' : Set V := A ∩ g ⁻¹' S k0
  have hA'c : IsCompact A' := hAc.inter_right (hNc.isClosed.preimage hgc)
  have hA'o : IsOpen A' := hAo.inter ((hSo k0).preimage hgc)
  have hA'm : MeasurableSet A' := hA'o.measurableSet
  have hA'W : A' ⊆ W := fun x hx => hWB x (hk0 hx.2)

  let φ : V → ℝ := A'.indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hA'o.frontier_eq, hA'c.isClosed.closure_eq]
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro hA'c fun x hx => ?_
    exact Set.indicator_of_notMem hx _
  have hts : tsupport φ ⊆ W := by
    refine subset_trans (closure_minimal (fun x hx => ?_) hA'c.isClosed) hA'W
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  obtain ⟨hI, hC⟩ := h.2.2 φ hφc hφs hts
  have hint : ∀ s, ∫ x, φ x ∂(fib s) = (fib s A').toReal := fun s => by
    simp [φ, integral_indicator hA'm, Measure.real]
  have hG : ContinuousAt (fun s => (fib s A').toReal) c := by
    have h := hC.continuousAt hBc
    simpa only [hint] using h
  have hfin : ∀ᶠ s in nhds c, fib s A' ≠ ⊤ := by
    filter_upwards [hBc] with s hs
    have h := hI s hs
    rw [integrable_indicator_iff hA'm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  have hcv : fib c A' = fib c A := by
    refine measure_congr ?_
    filter_upwards [ae_lift_eq h hg hι c] with x hx
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    show g x ∈ S k0
    rw [hx]
    exact hSc k0
  refine ⟨fun k => ?_, ?_⟩
  · have hO : IsOpen (A ∩ {x | c - g x ∈ U k}) := hAo.inter ((hSo k).preimage hgc)
    exact ⟨hO.measurableSet, ne_top_of_le_ne_top hAc.measure_lt_top.ne (measure_mono Set.inter_subset_left)⟩
  · have key := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV.tendsto_mean ν (fun s => fib s A') c hG hfin S hSm hl hpos htop
    simp only [hcv] at key
    refine key.congr' ?_
    filter_upwards [hl.eventually (Filter.eventually_smallSets_subset.2 ((hSo k0).mem_nhds (hSc k0)))] with k hk
    have e : A ∩ {x | c - g x ∈ U k} = A' ∩ g ⁻¹' S k := by
      ext x
      exact ⟨fun h => ⟨⟨h.1, hk h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [hSU k, e, fibre_mass_on h hg hι hgc.measurable hA'm (hSm k) (fun x hx => hA'W hx.1)]

end GlobalTheory.CompanionTheory.SiegelND.Coef.AvgV

theorem GlobalTheory.CompanionTheory.SiegelND.Coef.avgV_tendsto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ mv : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ c : HermR (Fv F v) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det → ∀ A : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → ∀ U : ℕ → Set (HermR (Fv F v) σ n), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : HermR (Fv F v) σ n) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets → (∀ k, MeasurableSet (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k}) ∧ GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k}) ≠ ⊤) ∧ Filter.Tendsto (fun k => (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k})).toReal / (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k)).toReal) Filter.atTop (nhds (mv c A).toReal) := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ d b v lv hlv mv hmv c hc A hAc hAo U hU hUt
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  obtain ⟨-, hW, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM (Fv F v) d b lv hlv.1
  obtain ⟨e1, e2, e3, e4, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM (Fv F v) n
  have hgc : Continuous (gramH hCM hJ (Fv F v) : (Fin n → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ n) :=
    Continuous.subtype_mk (a10 n M J) _
  have hUo : IsOpen {r : Fv F v | IsUnit r} := by
    have : {r : Fv F v | IsUnit r} = {r | r ≠ 0} := by
      ext r
      simp [isUnit_iff_ne_zero]
    rw [this]
    exact isOpen_ne
  have hB : IsOpen {S : HermR (Fv F v) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} :=
    PI.VolStabS.isOpen_unitHerm (Fv F v) hUo σ n
  exact AvgV.avg_gen (q := gramR (Fv F v) σ J) (ι := Subtype.val) (g := gramH hCM hJ (Fv F v)) hmv
    (fun _ => rfl) Subtype.val_injective hgc inferInstance (a8 n M) e3 e4 inferInstance e1 e2
    (hW n M).toIsFiniteMeasureOnCompacts (hH n) hB (fun _ h => h) hc hAc hAo hU hUt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreMeasureUnramifiedStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_gram_fibre_measure_unramified : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ mv : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ c : HermR (Fv F v) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det → ∀ A : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → ∀ U : ℕ → Set (HermR (Fv F v) σ n), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : HermR (Fv F v) σ n) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets → (∀ k, MeasurableSet (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k}) ∧ GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k}) ≠ ⊤) ∧ Filter.Tendsto (fun k => (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ {X | c - gramH hCM hJ (Fv F v) X ∈ U k})).toReal / (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k)).toReal) Filter.atTop (nhds (mv c A).toReal) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.avgV_tendsto | exact GlobalTheory.CompanionTheory.SiegelND.Coef.avgV_tendsto | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.avgV_tendsto <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFourierCharacterOfMatrix
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFourierCharacterOfMatrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem continuous_chiT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ T : Matrix (Fin n) (Fin n) E, Continuous (chiT σ ψ T) := by
  intro F E _ _ _ _ _ σ _ M J _ n _ ψ hψ T
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (AF F ⊗[F] E) := GlobalTheory.CompanionTheory.SW.TopK.isTopRing (AF F)
  have htr : Continuous (Algebra.trace (AF F) (AF F ⊗[F] E)) := GlobalTheory.CompanionTheory.SW.TopK.continuous_trace (AF F)
  unfold chiT
  refine hψ.1.comp (Continuous.neg (continuous_const.mul (htr.comp ?_)))
  exact (continuous_const.matrix_mul continuous_subtype_val).matrix_trace

end GlobalTheory.CompanionTheory.SiegelND.Coef
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFourierCharacterOfMatrixStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_fourier_character_of_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ T : Matrix (Fin n) (Fin n) E, Continuous (chiT σ ψ T) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.continuous_chiT | exact GlobalTheory.CompanionTheory.SiegelND.Coef.continuous_chiT | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.continuous_chiT <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreMeasureStandardVolume
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreMeasureStandardVolume
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

theorem GlobalTheory.CompanionTheory.SiegelND.Coef.finV_compactOpenN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ mv : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ c : HermR (Fv F v) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det → ∀ A : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → MeasurableSet A ∧ mv c A ≠ ⊤ := by
  intro F E _ _ _ _ _ σ hσ M J hJ n _ d b v lv hlv mv hm c _ A hAc hAo
  have hR := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  obtain ⟨h1, h2, h3, h4, -⟩ := id hR
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 n M
  obtain ⟨-, hW, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := (GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin F E σ hσ M J hJ (Fv F v) hR n _ _ mv (hW n M) (hH n) hm c).1
  exact ⟨hAo.measurableSet, hAc.measure_lt_top.ne⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreMeasureStandardVolumeStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_gram_fibre_measure_standard_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ mv : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ c : HermR (Fv F v) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det → ∀ A : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → MeasurableSet A ∧ mv c A ≠ ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.finV_compactOpenN | exact GlobalTheory.CompanionTheory.SiegelND.Coef.finV_compactOpenN | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.finV_compactOpenN <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorVanishing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorVanishing
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem exists_evVal : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (v : V) (v' : V'), ∃ A, EvVal ν ψ T B v v' A := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hB v v'
  obtain ⟨r, hr⟩ := GlobalTheory.T.mirabolic_pairing_conductor_bound ν ψ c T T' B s hψ hc hT hT' hB 1 v v'
  refine ⟨JJ ν ψ T B (box (n + 1) (c * r⁻¹) : Set (Fin (n + 1) → k)) v v', c * r⁻¹, fun t ht => ?_⟩
  have hc' : valuation k ((c * (c * r⁻¹)⁻¹ : kˣ) : k) ≤ valuation k (r : k) := by
    have : c * (c * r⁻¹)⁻¹ = r := by
      rw [_root_.mul_inv_rev, inv_inv, mul_left_comm, mul_inv_cancel, mul_one]
    rw [this]
  have hsub : ∀ x ∈ box (n + 1) (c * r⁻¹), ((1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t := by
    intro x hx
    rw [Units.val_one, one_mulVec]
    rw [GlobalTheory.CompanionTheory.BZOnto.PerpSmall.mem_box] at hx ⊢
    exact fun i => show valuation k (x i) ≤ valuation k (t : k) from
      le_trans (show valuation k (x i) ≤ valuation k ((c * r⁻¹ : kˣ) : k) from hx i) ht
  have h := hr (c * r⁻¹) hc' t hsub
  rw [← h]
  simp only [Units.val_one, one_mulVec]
  rfl

end GlobalTheory.CompanionTheory.MirPair
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorVanishingStatement
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_pairing_exists_eventual_value : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (v : V) (v' : V'), ∃ A, EvVal ν ψ T B v v' A := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.exists_evVal | exact GlobalTheory.CompanionTheory.MirPair.exists_evVal | (intros; apply GlobalTheory.CompanionTheory.MirPair.exists_evVal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSecondTermFromParts
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSecondTermFromParts
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCells

theorem term_of_covariance : PositivityTheory.GramSchwartzFunctions.EC.HeisSch → PositivityTheory.GramSchwartzFunctions.EC.Covar → PositivityTheory.GramSchwartzFunctions.EC.Zero →
    PositivityTheory.GramSchwartzFunctions.EC.Unfold2 → PositivityTheory.GramSchwartzFunctions.EC.ThetaInv → PositivityTheory.GramSchwartzFunctions.EC.Term2 := by
  intro hHeis hCovar hZero hUnf hTheta D n V ψ χ θ μ ω hS Φ r hr μr hμr c a hc b γ hγ hmat
  obtain ⟨-, -, hψ, -, -, hθ, ⟨𝓕, hcov⟩, -⟩ := id hS
  have hinv : mat γ * mat γ⁻¹ = 1 := by
    simp only [mat]
    rw [map_inv]
    simp
  rw [hZero D ψ hψ θ hθ V n μ 𝓕 hcov (ω γ Φ).1 (ω γ Φ).2,
    ← hUnf D ψ hψ θ hθ V n r hr μ 𝓕 hcov μr hμr c a hc b Φ.1 Φ.2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [← hmat]
  have hΨ := hHeis D ψ hψ θ hθ V n (HMul.hMul (zy y) (mat γ)) Φ.1 Φ.2
  have h1 := hCovar D n V ψ χ θ μ ω hS γ hγ (HMul.hMul (zy y) (mat γ)) Φ
    ⟨Heisenberg₂ ψ V (HMul.hMul (zy y) (mat γ)) Φ.1, hΨ⟩ rfl
  have h2 := hTheta D n V ψ χ θ μ ω hS ⟨Heisenberg₂ ψ V (HMul.hMul (zy y) (mat γ)) Φ.1, hΨ⟩ γ hγ
  have hv : HMul.hMul (HMul.hMul (zy y) (mat γ)) (mat γ⁻¹) = zy y := by
    rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
  rw [hv] at h1
  rw [h1] at h2
  exact h2

end GlobalTheory.CompanionTheory.EisCells
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSecondTermFromPartsStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_second_term_from_parts : PositivityTheory.GramSchwartzFunctions.EC.HeisSch → PositivityTheory.GramSchwartzFunctions.EC.Covar → PositivityTheory.GramSchwartzFunctions.EC.Zero → PositivityTheory.GramSchwartzFunctions.EC.Unfold2 → PositivityTheory.GramSchwartzFunctions.EC.ThetaInv → PositivityTheory.GramSchwartzFunctions.EC.Term2 := by
  first | exact @GlobalTheory.CompanionTheory.EisCells.term_of_covariance | exact GlobalTheory.CompanionTheory.EisCells.term_of_covariance | (intros; apply GlobalTheory.CompanionTheory.EisCells.term_of_covariance <;> assumption)
end
end
