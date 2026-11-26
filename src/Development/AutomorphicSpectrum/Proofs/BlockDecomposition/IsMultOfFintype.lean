module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SchemeDescendsToSubalgebra
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartLatQCech
public import Development.WeilBound.CoreStatements.HodgeTatePoints.A12
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

def gconv (g g' : ℝ → ℝ) (r : ℝ) : ℝ := ∫ t, g t * g' (r - t)

theorem gconv_comm (g g' : ℝ → ℝ) : gconv g g' = gconv g' g := by
  funext r
  unfold gconv
  rw [← integral_sub_left_eq_self (fun t => g t * g' (r - t)) volume r]
  simp [mul_comm]

variable {n : ℕ}

def KReg {V : Type} [NormedAddCommGroup V] (k : Mat n → V) : Prop :=
  ContinuousOn k (GLs n) ∧ ∃ R, ∀ y ∈ GLs n, R < lg y → k y = 0

theorem inv_mem_GLs {y : Mat n} (hy : y ∈ GLs n) : y⁻¹ ∈ GLs n := by
  have : y.det ≠ 0 := hy
  change (y⁻¹).det ≠ 0
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero this

section
variable [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n)

theorem isMult_of_fintype {ι : Type} [Fintype ι] {k : Mat n → (E.V →L[ℂ] E.V)} {val : Inf n → ℂ} {T : ℝ}
    (c : ι → ℂ) (w : ι → List (Bool × ℕ)) (g : ι → ℝ → ℝ) (ks : ι → Mat n → (E.V →L[ℂ] E.V))
    (h1 : ∀ i, IsBump (g i) T ∧ IsKer μ E (w i) (g i) (ks i)) (h2 : ∀ y ∈ GLs n, k y = ∑ i, c i • ks i y)
    (h3 : ∀ χ, val χ = ∑ i, c i * zVal (w i) χ * coshT (g i) (cas χ)) : IsMult μ E k val T := by
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, c ∘ e.symm, w ∘ e.symm, g ∘ e.symm, ks ∘ e.symm, fun i => h1 _, fun y hy => ?_, fun χ => ?_⟩
  · rw [h2 y hy]
    exact (Equiv.sum_comp e.symm (fun i => c i • ks i y)).symm
  · rw [h3 χ]
    exact (Equiv.sum_comp e.symm (fun i => c i * zVal (w i) χ * coshT (g i) (cas χ))).symm
end

theorem zVal_append (w w' : List (Bool × ℕ)) (χ : Inf n) : zVal (w ++ w') χ = zVal w χ * zVal w' χ := by
  simp [zVal]

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def EpowT (s : Bool) : ℕ → Fin n → Fin n → (Mat n → V) → (Mat n → V)
  | 0, a, b => fun f => if a = b then f else 0
  | m + 1, a, b => fun f => ∑ c, Eu s c a (EpowT s m c b f)

def gelT (s : Bool) (m : ℕ) (f : Mat n → V) : Mat n → V := ∑ a, EpowT s m a a f

end Ops

section Alg

variable {A : Type} [Ring A]

noncomputable def Epw (e : Fin n → Fin n → A) : ℕ → Fin n → Fin n → A
  | 0, a, b => if a = b then 1 else 0
  | m + 1, a, b => ∑ c, e a c * Epw e m c b

def trE (e : Fin n → Fin n → A) (m : ℕ) : A := ∑ a, Epw e m a a

noncomputable def bco (N : A) (τ : ℕ → A) : ℕ → ℕ → A
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | m + 1, 0 => N * bco N τ m 0 - τ m
  | m + 1, j + 1 => bco N τ m j + N * bco N τ m (j + 1)

noncomputable def phiSeq (N : A) (τ : ℕ → A) (m : ℕ) : A :=
  τ m - ∑ j : Fin m, bco N τ m j * phiSeq N τ j
termination_by m
decreasing_by exact j.isLt

end Alg

def gser (c : Fin n → ℂ) : PowerSeries ℂ := PowerSeries.mk (GlobalTheory.Dec.gelfVal c)

end GlobalTheory.CompanionTheory.WaveMult
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.RCalc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_fderiv_field {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (A : E →L[ℝ] E) :
    ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g (A g)) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply A.contDiff.contDiffOn

theorem fderiv_field_bracket {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (A B : E →L[ℝ] E)
    {g : E} (hg : g ∈ U) :
    fderiv ℝ (fun y => fderiv ℝ f y (B y)) g (A g) - fderiv ℝ (fun y => fderiv ℝ f y (A y)) g (B g) =
      fderiv ℝ f g (B (A g) - A (B g)) := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  have h2 : DifferentiableAt ℝ (fderiv ℝ f) g :=
    ((h1.contDiffAt (hU.mem_nhds hg)).differentiableAt (by simp))
  have hs : IsSymmSndFDerivAt ℝ f g :=
    (hf.contDiffAt (hU.mem_nhds hg)).isSymmSndFDerivAt (by simp)
  have hA := (h2.hasFDerivAt.clm_apply A.hasFDerivAt).fderiv
  have hB := (h2.hasFDerivAt.clm_apply B.hasFDerivAt).fderiv
  rw [hA, hB]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, map_sub]
  rw [hs.eq (A g) (B g)]
  abel

theorem fderiv_add_apply' {f h : E → F} {g : E} (hf : DifferentiableAt ℝ f g) (hh : DifferentiableAt ℝ h g) (v : E) :
    fderiv ℝ (f + h) g v = fderiv ℝ f g v + fderiv ℝ h g v := by
  rw [fderiv_add hf hh]; rfl

end General

theorem fderiv_csmul_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {g : E} (hf : DifferentiableAt ℝ f g) (c : ℂ) (v : E) :
    fderiv ℝ (c • f) g v = c • fderiv ℝ f g v := by
  rw [fderiv_const_smul (R := ℂ) hf c]; rfl

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage this

def mulR (X : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

def mulL (x : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x)

@[simp] theorem mulR_apply (X g : Mat n) : mulR X g = g * X := rfl
@[simp] theorem mulL_apply (x g : Mat n) : mulL x g = x * g := rfl

theorem differentiableAt_of_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    DifferentiableAt ℝ f g :=
  ((hf.contDiffAt (isOpen_GLs.mem_nhds hg)).differentiableAt (by simp))

theorem Rd_contDiffOn (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Rd X f) (GLs n) :=
  contDiffOn_fderiv_field isOpen_GLs hf (mulR X)

theorem Rd_bracket (X Y : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (Rd Y f) g - Rd Y (Rd X f) g = Rd (X * Y - Y * X) f g := by
  have := fderiv_field_bracket isOpen_GLs hf (mulR X) (mulR Y) hg
  have e : (mulR Y) ((mulR X) g) - (mulR X) ((mulR Y) g) = g * (X * Y - Y * X) := by
    show g * X * Y - g * Y * X = _
    simp [mul_sub, mul_assoc]
  exact this.trans (congrArg (fderiv ℝ f g) e)

theorem Rd_congr (X : Mat n) {f h : Mat n → V} (e : Set.EqOn f h (GLs n)) : Set.EqOn (Rd X f) (Rd X h) (GLs n) := by
  intro g hg
  have : f =ᶠ[nhds g] h := Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg) e
  simp [Rd, this.fderiv_eq]

theorem Rd_add_left (X Y : Mat n) (f : Mat n → V) : Rd (X + Y) f = Rd X f + Rd Y f := by
  funext g; simp [Rd, mul_add]

theorem Rd_smul_left (r : ℝ) (X : Mat n) (f : Mat n → V) : Rd (r • X) f = r • Rd X f := by
  funext g
  simp only [Rd, Pi.smul_apply, mul_smul_comm, map_smul]

theorem Rd_add {f h : Mat n → V} (X : Mat n) (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) :
    Set.EqOn (Rd X (f + h)) (Rd X f + Rd X h) (GLs n) := by
  intro g hg
  exact fderiv_add_apply' (differentiableAt_of_smooth hf hg) (differentiableAt_of_smooth hh hg) _

theorem Rd_smul (c : ℂ) (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Rd X (c • f)) (c • Rd X f) (GLs n) := by
  intro g hg
  exact fderiv_csmul_apply (differentiableAt_of_smooth hf hg) c _

def IBP : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → Cpt f →
    ∀ X, ∫ y : G n, Rd X f y.val ∂μ = 0

end GlobalTheory.CompanionTheory.RCalc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Rr
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev Ix (n : ℕ) := Bool × Fin n × Fin n

def hm (p : Ix n) : Mat n :=
  if p.1 then Matrix.single p.2.1 p.2.2 1 + Matrix.single p.2.2 p.2.1 1
  else Matrix.single p.2.1 p.2.2 Complex.I - Matrix.single p.2.2 p.2.1 Complex.I

def sk (p : Ix n) : Mat n :=
  if p.1 then Matrix.single p.2.1 p.2.2 1 - Matrix.single p.2.2 p.2.1 1
  else Matrix.single p.2.1 p.2.2 Complex.I + Matrix.single p.2.2 p.2.1 Complex.I

section Calc

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]

def Rr (X : Mat n) (f : Mat n → W) : Mat n → W := fun g => fderiv ℝ f g (g * X)

def Sm (u : ℝ → Mat n → W) : Prop := ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ GLs n)

def dt (u : ℝ → Mat n → W) : ℝ → Mat n → W := fun s y => deriv (fun r => u r y) s

def Rt (X : Mat n) (u : ℝ → Mat n → W) : ℝ → Mat n → W := fun s => Rr X (u s)

def dens (u : ℝ → Mat n → W) (s : ℝ) (y : Mat n) : ℝ :=
  ‖dt u s y‖ ^ 2 + (1 / 4) * ∑ p : Ix n, ‖Rt (hm p) u s y‖ ^ 2 + ‖u s y‖ ^ 2

end Calc

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : GLs n = (fun g : Mat n => g.det) ⁻¹' {0}ᶜ := by ext g; simp [GLs]
  rw [this]
  exact isOpen_compl_singleton.preimage (Continuous.matrix_det continuous_id)

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n := by
  have := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  exact this.ne_zero

end GlobalTheory.CompanionTheory.WaveSpd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageDerivativeL1Bound
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveK

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Norms

variable [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]

end Norms

def WaveUniq : Prop :=
  ∀ (n : ℕ) (E : KMod n) (u v : ℝ → Mat n → E.V), IsWave E u → IsWave E v → (∀ g ∈ GLs n, u 0 g = v 0 g) →
    ∀ t, ∀ x ∈ GLs n, u t x = v t x

end GlobalTheory.CompanionTheory.WaveK
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DwCons
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SobGL

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev Idx (n : ℕ) := Bool × Fin n × Fin n

def cm {n : ℕ} (t : Idx n → ℝ) : Mat n := ∑ p, t p • bs p

def pd {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℝ V] :
    List ι → ((ι → ℝ) → V) → ((ι → ℝ) → V) :=
  fun L F => L.foldr (fun i H t => fderiv ℝ H t (Pi.single i 1)) F

def Dw {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    List (Idx n) → (Mat n → V) → (Mat n → V) :=
  fun L f => L.foldr (fun p H y => fderiv ℝ H y (bs p)) f

theorem pd_nil {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : (ι → ℝ) → V) : pd [] F = F := rfl

theorem pd_cons {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : ι) (L : List ι) (F : (ι → ℝ) → V) :
    pd (i :: L) F = fun t => fderiv ℝ (pd L F) t (Pi.single i 1) := rfl

theorem Dw_nil {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : Mat n → V) :
    Dw [] f = f := rfl

theorem Dw_cons {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (p : Idx n)
    (L : List (Idx n)) (f : Mat n → V) :
    Dw (p :: L) f = fun y => fderiv ℝ (Dw L f) y (bs p) := rfl

end GlobalTheory.CompanionTheory.SobGL
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeas
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.ConeHaar

open PositivityTheory.RgBcC

def coneW (n : ℕ) (v : Fin n × Fin n → ℝ) : ℝ≥0∞ := ENNReal.ofReal (((hOf v).det.re ^ n)⁻¹)

def coneMeas (n : ℕ) : Measure (Fin n × Fin n → ℝ) :=
  (volume.restrict (cone n)).withDensity (coneW n)

end GlobalTheory.CompanionTheory.ConeHaar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchemeModelsSpread
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchemeModelsSpread
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels

namespace GlobalTheory.CompanionTheory.NoethApprox

theorem schemeModels : GlobalTheory.SpreadingModels.SchemeModels := by
  intro R _ Y f h₁ h₂ h₃
  obtain ⟨R₀, i, φ, Y₀, f₀, π, a, b, c, d, e⟩ := GlobalTheory.SpreadScheme.hasModel (V := R) f
  exact ⟨R₀, i, φ, Y₀, f₀, π, a, b, d, c, e⟩

end GlobalTheory.CompanionTheory.NoethApprox
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchemeModelsSpreadStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scheme_models_spread : GlobalTheory.SpreadingModels.SchemeModels := by
  first | exact @GlobalTheory.CompanionTheory.NoethApprox.schemeModels | exact GlobalTheory.CompanionTheory.NoethApprox.schemeModels | (intros; apply GlobalTheory.CompanionTheory.NoethApprox.schemeModels <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapQdetEtr
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CapelliMap

variable {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]

theorem map_Tm (φ : A →ₐ[ℂ] B) {n : ℕ} (X : Fin n → Fin n → A) (u : ℂ) (a b : Fin n) :
    φ (Formalism.REAL.Tm X u a b) = Formalism.REAL.Tm (fun a b => φ (X a b)) u a b := by
  unfold Formalism.REAL.Tm
  split_ifs <;> simp

theorem map_qminor (φ : A →ₐ[ℂ] B) {n t : ℕ} (X : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (u : ℂ) :
    φ (Formalism.REAL.qminor X a b u) = Formalism.REAL.qminor (fun a b => φ (X a b)) a b u := by
  unfold Formalism.REAL.qminor
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 2
  congr 1
  funext k
  exact map_Tm φ X _ _ _

theorem map_qdet (φ : A →ₐ[ℂ] B) {n : ℕ} (X : Fin n → Fin n → A) (u : ℂ) :
    φ (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun a b => φ (X a b)) u := by
  unfold Formalism.REAL.qdet
  exact map_qminor φ X id id u

theorem map_epow (φ : A →ₐ[ℂ] B) {n : ℕ} (X : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) :
    φ (Formalism.REAL.epow X k a b) = Formalism.REAL.epow (fun a b => φ (X a b)) k a b := by
  induction k generalizing a b with
  | zero => by_cases h : a = b <;> simp [Formalism.REAL.epow, h]
  | succ m ih => simp [Formalism.REAL.epow, map_sum, map_mul, ih, apply_ite]

theorem map_etr (φ : A →ₐ[ℂ] B) {n : ℕ} (X : Fin n → Fin n → A) (k : ℕ) :
    φ (Formalism.REAL.etr X k) = Formalism.REAL.etr (fun a b => φ (X a b)) k := by
  unfold Formalism.REAL.etr
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl (fun a _ => map_epow φ X k a a)

theorem map_qdet_etr : ∀ (A B : Type) [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (φ : A →ₐ[ℂ] B) (n : ℕ) (X : Fin n → Fin n → A) (u : ℂ) (k : ℕ),
    φ (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun a b => φ (X a b)) u ∧
      φ (Formalism.REAL.etr X k) = Formalism.REAL.etr (fun a b => φ (X a b)) k := by
  intro A B _ _ _ _ φ n X u k
  exact ⟨map_qdet φ X u, map_etr φ X k⟩

end GlobalTheory.CompanionTheory.CapelliMap
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelExistence
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelExistence
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.WaveKer

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Local

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_germ (X : Mat n) {f : Mat n → V} {x : Mat n} (h : f =ᶠ[𝓝 x] 0) :
    Rd X f =ᶠ[𝓝 x] 0 := by
  filter_upwards [h.eventuallyEq_nhds] with y hy
  simp only [Rd, Pi.zero_apply]
  rw [hy.fderiv_eq]
  have : fderiv ℝ (0 : Mat n → V) y = 0 := by
    simpa using fderiv_const_apply (𝕜 := ℝ) (x := y) (0 : V)
  rw [this]
  rfl

theorem Eu_germ (s : Bool) (a b : Fin n) {f : Mat n → V} {x : Mat n} (h : f =ᶠ[𝓝 x] 0) :
    Eu s a b f =ᶠ[𝓝 x] 0 := by
  filter_upwards [Rd_germ (Matrix.single a b 1) h, Rd_germ (Matrix.single a b Complex.I) h]
    with y h1 h2
  simp only [Eu, Pi.smul_apply, Pi.add_apply, h1, h2, Pi.zero_apply, smul_zero, add_zero]

theorem Epow_germ (s : Bool) (m : ℕ) (a b : Fin n) {f : Mat n → V} {x : Mat n}
    (h : f =ᶠ[𝓝 x] 0) : Epow s m a b f =ᶠ[𝓝 x] 0 := by
  induction m generalizing a b with
  | zero =>
    by_cases hab : a = b
    · simpa [Epow, hab] using h
    · simp [Epow, hab]
  | succ m ih =>
    have : ∀ᶠ y in 𝓝 x, ∀ c, Eu s a c (Epow s m c b f) y = 0 :=
      eventually_all.2 fun c => Eu_germ s a c (ih c b)
    filter_upwards [this] with y hy
    simp [Epow, Finset.sum_apply, hy]

theorem gel_germ (s : Bool) (m : ℕ) {f : Mat n → V} {x : Mat n} (h : f =ᶠ[𝓝 x] 0) :
    gel s m f =ᶠ[𝓝 x] 0 := by
  have : ∀ᶠ y in 𝓝 x, ∀ a, Epow s m a a f y = 0 :=
    eventually_all.2 fun a => Epow_germ s m a a h
  filter_upwards [this] with y hy
  simp [gel, Finset.sum_apply, hy]

theorem zOp_germ (w : List (Bool × ℕ)) {f : Mat n → V} {x : Mat n} (h : f =ᶠ[𝓝 x] 0) :
    zOp w f =ᶠ[𝓝 x] 0 := by
  induction w with
  | nil => simpa [zOp] using h
  | cons p w ih => exact gel_germ p.1 p.2 ih

end Local

theorem one_mem_GLs (n : ℕ) : (1 : Mat n) ∈ GLs n := by simp [GLs]

theorem mul_mem_GLs {n : ℕ} {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, det_mul] at *
  exact mul_ne_zero hx hy

theorem unitary_mem_GLs {n : ℕ} (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n := by
  intro h
  have h1 := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 k.2)
  rw [det_mul, h, mul_zero, det_one] at h1
  exact zero_ne_one h1

theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem isOpen_GLs (n : ℕ) : IsOpen (GLs n) := by
  have hc : Continuous fun g : Mat n => g.det := continuous_id.matrix_det
  exact isOpen_ne.preimage hc

theorem lg_one_nonneg (hL : LgFacts) (n : ℕ) : 0 ≤ lg (1 : Mat n) := by
  have h := (hL n).1 1 (one_mem_GLs n) 1 (one_mem_GLs n)
  rw [one_mul] at h
  linarith

theorem ker_support (hL : LgFacts) (hE : WaveEx) (hU : KerUniq) {n : ℕ}
    [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (c₀ : ℝ)
    (hc : ∀ (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → ∀ (t : ℝ), ∀ x ∈ GLs n,
      (∀ y ∈ GLs n, lg y ≤ c₀ * (1 + |t|) → u 0 (x * y) = 0) → u t x = 0)
    {w : List (Bool × ℕ)} {g : ℝ → ℝ} {T : ℝ} {k : Mat n → (E.V →L[ℂ] E.V)} (hT : 0 ≤ T)
    (hg : IsBump g T) (hk : IsKer μ E w g k) {y : Mat n} (hy : y ∈ GLs n)
    (hlt : (max c₀ 0 + lg (1 : Mat n) + 1) * (1 + T) < lg y) : k y = 0 := by
  obtain ⟨hsub, -, hinv, hsm, -, -, -⟩ := hL n
  have hL0 := lg_one_nonneg hL n
  have hM0 : 0 ≤ max c₀ 0 := le_max_right _ _
  have hGo := isOpen_GLs n
  set A : ℝ := (max c₀ 0 + lg (1 : Mat n) + 1) * (1 + T) with hA
  have hUo : IsOpen (GLs n ∩ lg ⁻¹' Set.Ioi A) :=
    hsm.continuousOn.isOpen_inter_preimage hGo isOpen_Ioi
  refine hU n μ E k (GLs n ∩ lg ⁻¹' Set.Ioi A) hUo Set.inter_subset_left ?_
    hk.1.continuousOn ?_ ?_ y ⟨hy, hlt⟩
  · intro z hz k₂
    refine ⟨mul_mem_GLs hz.1 (unitary_mem_GLs k₂), ?_⟩
    have h := hinv z hz.1 1 k₂
    simp only [OneMemClass.coe_one, one_mul] at h
    simpa [h] using hz.2
  · intro z hz k₂
    have h := hk.2.2.1 z hz 1 k₂
    simpa using h
  · intro f hf _ hoff
    obtain ⟨u, hu, hu0⟩ := hE n E f hf
    have hact : act μ E k f 1 = act μ E k (u 0) 1 := by
      simp only [act]
      congr 1
      funext z
      rw [one_mul, hu0 _ (val_mem_GLs z)]
    have hzero : ∀ x ∈ GLs n, lg x < lg (1 : Mat n) + 1 → ∀ t, |t| ≤ T → u t x = 0 := by
      intro x hx hlx t ht
      refine hc E u hu t x hx fun z hz hlz => ?_
      rw [hu0 _ (mul_mem_GLs hx hz)]
      refine hoff _ (mul_mem_GLs hx hz) ?_
      rintro ⟨-, hbig⟩
      have hbig' : A < lg (x * z) := hbig
      have h0 := hsub x hx z hz
      have h1 : c₀ * (1 + |t|) ≤ max c₀ 0 * (1 + |t|) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      have h2 : max c₀ 0 * (1 + |t|) ≤ max c₀ 0 * (1 + T) :=
        mul_le_mul_of_nonneg_left (by linarith) hM0
      have h3 : lg (1 : Mat n) + 1 ≤ (lg (1 : Mat n) + 1) * (1 + T) := by nlinarith
      have h4 : A = max c₀ 0 * (1 + T) + (lg (1 : Mat n) + 1) * (1 + T) := by rw [hA]; ring
      linarith
    have hF : (fun x' => ∫ t, (g t : ℂ) • u t x') =ᶠ[𝓝 (1 : Mat n)] 0 := by
      have hN : GLs n ∩ lg ⁻¹' Set.Iio (lg (1 : Mat n) + 1) ∈ 𝓝 (1 : Mat n) :=
        (hsm.continuousOn.isOpen_inter_preimage hGo isOpen_Iio).mem_nhds
          ⟨one_mem_GLs n, Set.mem_preimage.2 (Set.mem_Iio.2 (lt_add_one _))⟩
      filter_upwards [hN] with x hx
      have h0 : ∀ t, (g t : ℂ) • u t x = 0 := by
        intro t
        by_cases ht : |t| ≤ T
        · rw [hzero x hx.1 hx.2 t ht, smul_zero]
        · rw [hg.2.2 t (not_le.1 ht)]
          simp
      simp [h0]
    rw [hact, hk.2.2.2 u hu 1 (one_mem_GLs n)]
    exact (zOp_germ w hF).self_of_nhds

theorem asmKerEx : AsmKerEx := by
  intro hL _ hS hE hU hO n
  obtain ⟨c₀, hc⟩ := hS n
  refine ⟨max c₀ 0 + lg (1 : Mat n) + 1, ?_⟩
  intro _ _ μ _ E
  refine ⟨fun w g T hg => hO n μ E w g T hg, ?_⟩
  rintro k val T hT ⟨m, c, w, g, ks, hi, hsum, -⟩ y hy hlt
  rw [hsum y hy]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [ker_support hL hE hU μ E c₀ hc hT (hi i).1 (hi i).2 hy hlt, smul_zero]

end GlobalTheory.CompanionTheory.WaveKer
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelExistenceStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wave_kernel_existence : PositivityTheory.RgBcC.AsmKerEx := by
  first | exact @GlobalTheory.CompanionTheory.WaveKer.asmKerEx | exact GlobalTheory.CompanionTheory.WaveKer.asmKerEx | (intros; apply GlobalTheory.CompanionTheory.WaveKer.asmKerEx <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefSmoothOnG
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.CoefSmooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem coef_smoothOnG (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H) :
    Formalism.REAL.SmoothOnG ε (fun g => ⟪w, σ g (v : H)⟫_ℂ) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := v.2 g₀ hg₀
  refine ⟨U, fun x => ⟪w, F x⟫_ℂ, hU, hgU, ?_, fun g hg hgJ => ?_⟩
  · exact (((innerSL ℂ w).restrictScalars ℝ).contDiff.comp_contDiffOn hF)
  · exact congrArg (fun z => ⟪w, z⟫_ℂ) (hfF g hg hgJ)

theorem coef_smooth : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H),
    Formalism.REAL.SmoothOnG ε (fun g => ⟪w, σ g (v : H)⟫_ℂ) :=
  fun n ε H _ _ σ v w => coef_smoothOnG n ε H σ v w

end GlobalTheory.CompanionTheory.CoefSmooth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EwordCoef
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.CoefWord

theorem eword_coef : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H) (l : List (Fin n × Fin n)), ∀ g ∈ Formalism.MainNotions.S.UJset ε, Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ) g = ⟪w, σ g (((l.map fun ab => GlobalTheory.SmoothVecMod.unitAct hσ ab.1 ab.2).prod v : GlobalTheory.SmoothVecMod.smoothVec ε σ) : H)⟫_ℂ := by
  intro n ε H _ _ σ hσ v w l
  induction l with
  | nil =>
    intro g _
    rfl
  | cons p l ih =>
    intro g hg
    have hg' : Formalism.REAL.inUJ ε g := hg
    set u : GlobalTheory.SmoothVecMod.smoothVec ε σ :=
      (l.map fun ab => GlobalTheory.SmoothVecMod.unitAct hσ ab.1 ab.2).prod v with hu
    have h1 : Formalism.REAL.Eword ε (p :: l) (fun x => ⟪w, σ x (v : H)⟫_ℂ) g =
        Formalism.REAL.EabV ε p.1 p.2 (Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ)) g := rfl
    have h2 : Formalism.REAL.EabV ε p.1 p.2 (Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ)) g =
        Formalism.REAL.EabV ε p.1 p.2 (fun x => innerSL ℂ w (σ x (u : H))) g :=
      GlobalTheory.SmoothVecMod.eabV_congr (fun x hx => ih x hx) p.1 p.2 hg'
    have h3 := GlobalTheory.CapelliCoef.eabV_pair (innerSL ℂ w) (f := fun x => σ x (u : H)) u.2 p.1 p.2 hg'
    have h4 := GlobalTheory.SmoothVecMod.rep_eabV hσ u.2 p.1 p.2 hg'
    rw [h1, h2, ← h3, ← h4]
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rfl

end GlobalTheory.CompanionTheory.CoefWord
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalChartLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalChartLattice
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.GenericFibre

theorem isMultiHomogIdeal_map_rat {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    IsMultiHomogIdeal (P.map (MvPolynomial.map (Int.castRingHom ℚ))) := by
  obtain ⟨S, hS, rfl⟩ := hP
  refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · exact Ideal.map_span _ _

theorem finiteDimensional_chartLatQ :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (D : ℕ) (b : K → ℤ),
      ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (D + 1) → FiniteDimensional ℚ (chartLatQ y b 1) := by
  intro K _ ι _ Ω _ _ y D b hV
  classical
  letI : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  letI : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  obtain ⟨e⟩ := ChartLatQCech.proof K ι Ω y (D + 1) b hV
  have hQ := isMultiHomogIdeal_map_rat hV.2.1.2.1
  have hG := QuotPartGraded.proof ℚ K ι _ hQ
  have hS := PositivityTheory.HtPt.Ktw.a11 ℚ K ι _
    (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.quotPart ℚ (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) (mCoordIdeal y)))
    inferInstance inferInstance hG
  haveI := hS.1 b 0
  exact Module.Finite.equiv e.symm

end GlobalTheory.CompanionTheory.GenericFibre
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalChartLatticeStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_chart_lattice : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (b : K → ℤ), IsArithVar (mCoordIdeal y) (D + 1) → FiniteDimensional ℚ (chartLatQ y b 1) := by
  first | exact @GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ | exact GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ | (intros; apply GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbelianSchemeBaseChangeExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbelianSchemeBaseChangeExists
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Axis

theorem exists_abelianScheme_baseChange_ringHom :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (A' : Over (Sp R')) (_ : GrpObj A') (φ : A'.left ⟶ A.left), IsAbelianScheme A' ∧
      SmoothOfRelativeDimension g A'.hom ∧ IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) := by
  intro R R' _ _ _ A _ g hA hg
  exact ⟨(Over.pullback (spMap (algebraMap R R'))).obj A, Functor.grpObjObj,
    Limits.pullback.fst A.hom (spMap (algebraMap R R')),
    GlobalTheory.AbLaw.CubeGen.isAb_baseChange hA _,
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback _ _) hg,
    IsPullback.of_hasPullback _ _⟩

end GlobalTheory.CompanionTheory.Axis
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbelianSchemeBaseChangeExistsStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_base_change_exists : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (A' : Over (Sp R')) (_ : GrpObj A') (φ : A'.left ⟶ A.left), IsAbelianScheme A' ∧
      SmoothOfRelativeDimension g A'.hom ∧ IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) := by
  first | exact @GlobalTheory.CompanionTheory.Axis.exists_abelianScheme_baseChange_ringHom | exact GlobalTheory.CompanionTheory.Axis.exists_abelianScheme_baseChange_ringHom | (intros; apply GlobalTheory.CompanionTheory.Axis.exists_abelianScheme_baseChange_ringHom <;> assumption)
end
end
