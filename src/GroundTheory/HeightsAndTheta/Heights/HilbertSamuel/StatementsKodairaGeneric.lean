module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKleimanScheme
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FrechetDerivEvaluation
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Reading

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section Objects

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def NefOnGenericDeg (P : Ideal (MRing ι)) (a : K → ℤ) : Prop :=
  ∀ W : Ideal (MRing ι), IsArithVar W 2 → P ≤ W → 0 ≤ genDeg W 1 a

variable {Ω : Type} [Field Ω] [CharZero Ω]

def chartRingQ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : Subalgebra ℚ Ω :=
  Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)

def chartLatQ (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : Submodule ℚ Ω where
  carrier := {s | ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ chartRingQ y c}
  zero_mem' := fun c _ => by simp
  add_mem' := fun {s t} hs ht c hc => by rw [add_mul]; exact add_mem (hs c hc) (ht c hc)
  smul_mem' := fun r s hs c hc => by
    rw [smul_mul_assoc]
    exact Subalgebra.smul_mem _ (hs c hc) r

end Objects

def KodairaGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → NefOnGenericDeg (mCoordIdeal y) a →
    0 < genDeg (mCoordIdeal y) D a →
    ∃ (k : ℕ) (e : Ω), 1 ≤ k ∧ e ≠ 0 ∧ e ∈ chartLatQ y ((k : ℤ) • a - 1) 1

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBergman
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights
  GroundTheory.Heights₂.Heights.CP

noncomputable section

def PolydiscSubmean.Statement : Prop :=
  ∀ (D n : ℕ) (lam : Fin D → ℝ) (R : ℝ) (f : (Fin D → ℂ) → ℂ), 0 < n → 0 < R →
    (∀ j, 0 ≤ lam j) → AnalyticOnNhd ℂ f (Metric.closedBall 0 (R / Real.sqrt n)) →
    ‖f 0‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * ∏ j, gaussDiscMass (lam j) R ≤
      ∫ z in Metric.closedBall (0 : Fin D → ℂ) (R / Real.sqrt n),
        ‖f z‖ ^ 2 * Real.exp (-(n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2)

def LocalBergmanBound.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L)
    (dV : SmoothVolume A), W.IsSemipositive →
    ∀ (V : ℕ → Submodule ℂ (Fin A.n → X → ℂ)) [∀ n, FiniteDimensional ℂ (V n)],
      (∀ n, V n ≤ L.sections n) → ∀ (x : X) (ε : ℝ), 0 < ε →
        ∀ᶠ n : ℕ in atTop, bergman W dV (V n) n x ≤ (bergmanDens W dV x + ε) * (n : ℝ) ^ D

def UniformBergmanBound.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W₀ W₁ : Weight L)
    (dV : SmoothVolume A), W₀.IsSemipositive → W₁.IsSemipositive →
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ (V : Submodule ℂ (Fin A.n → X → ℂ)) [FiniteDimensional ℂ V], V ≤ L.sections n →
        ∀ x : X, bergman (W₀.lerp W₁ t) dV V n x ≤ C * (n : ℝ) ^ D

def IntegralOfBergman.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L)
    (dV : SmoothVolume A) (n : ℕ) (V : Submodule ℂ (Fin A.n → X → ℂ)) [FiniteDimensional ℂ V],
    V ≤ L.sections n → ∫ x, bergman W dV V n x ∂dV.μ = Module.finrank ℂ V

def L1Convergence.Statement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (g : ℕ → Ω → ℝ)
    (b : Ω → ℝ) (C : ℝ), (∀ n, Integrable (g n) μ) → Integrable b μ →
    (∀ n x, 0 ≤ g n x ∧ g n x ≤ C) →
    (∀ (x : Ω) (ε : ℝ), 0 < ε → ∀ᶠ n in atTop, g n x ≤ b x + ε) →
    (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∫ x, b x ∂μ - ε ≤ ∫ x, g n x ∂μ) →
    Tendsto (fun n => ∫ x, |g n x - b x| ∂μ) atTop (𝓝 0)

def BergmanL1Convergence.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L)
    (dV : SmoothVolume A), W.IsSemipositive →
    ∀ (V : ℕ → Submodule ℂ (Fin A.n → X → ℂ)) [∀ n, FiniteDimensional ℂ (V n)],
      (∀ n, V n ≤ L.sections n) →
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        (∫ x, bergmanDens W dV x ∂dV.μ - ε) * (n : ℝ) ^ D ≤ Module.finrank ℂ (V n)) →
      Tendsto (fun n : ℕ => ∫ x, |((n : ℝ) ^ D)⁻¹ * bergman W dV (V n) n x - bergmanDens W dV x|
        ∂dV.μ) atTop (𝓝 0)

lemma lerp_self_φ {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
    {L : HolLineBundle A} (W : Weight L) (t : ℝ) : (W.lerp W t).φ = W.φ := by
  funext j x
  simp [Weight.lerp]

def MetricChange.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W₀ W₁ : Weight L)
    (dV : SmoothVolume A), W₀.IsSemipositive → W₁.IsSemipositive →
    ∀ (V : ℕ → Submodule ℂ (Fin A.n → X → ℂ)) [∀ n, FiniteDimensional ℂ (V n)],
      (∀ n, V n ≤ L.sections n) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        (∫ x, bergmanDens (W₀.lerp W₁ t) dV x ∂dV.μ - ε) * (n : ℝ) ^ D ≤
          Module.finrank ℂ (V n)) →
      ∀ (e : ∀ n, Module.Basis (Fin (Module.finrank ℂ (V n))) ℂ (V n)) (ε : ℝ), 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          |chiGram W₁ dV n (fun a => (e n a : Fin A.n → X → ℂ)) -
              chiGram W₀ dV n (fun a => (e n a : Fin A.n → X → ℂ)) -
            (n : ℝ) ^ (D + 1) / 2 * ∫ t in (0 : ℝ)..1,
              ∫ x, Weight.diff W₁ W₀ x * bergmanDens (W₀.lerp W₁ t) dV x ∂dV.μ| ≤
            ε * (n : ℝ) ^ (D + 1)

def SupNormAgainstL2.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W : Weight L)
    (dV : SmoothVolume A), W.IsSemipositive →
    (∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ s ∈ L.sections n, ∀ x : X,
      Real.sqrt (ptNormSq W n s x) ≤ C * Real.sqrt ((n : ℝ) ^ D) * Real.sqrt (sectionL2NormSq W dV n s)) ∧
    ∀ (n : ℕ), ∀ s ∈ L.sections n, ∀ M : ℝ, (∀ x : X, Real.sqrt (ptNormSq W n s x) ≤ M) →
      Real.sqrt (sectionL2NormSq W dV n s) ≤ M

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

namespace NefOnGenericOfSemipos

theorem hasFDerivAt_eval {σ : Type*} [Fintype σ] (g : MvPolynomial σ ℂ) (z : σ → ℂ) :
    HasFDerivAt (fun x : σ → ℂ => eval x g)
      (∑ i, eval z (pderiv i g) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i) z :=
  _root_.UpperTheory.Reformulated.B.FrechetDerivEvaluation.hasFDerivAt_eval g z

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem maDensity_nonneg {P P0 W : Ideal (MRing ι)} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hP0 : P0 ≤ P) (hPW : P ≤ W)
    (hs : IsSemipositiveRel P0 P A) {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (1 + 1) → ℂ)}
    {y : Fin 1 → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin 1 → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSheet W Ψ y w γ) :
    0 ≤ maDensity (fun _ y' => Real.log (A.h (γ y'))) y := by
  have hA : AnalyticAt ℂ γ y := sheet_analyticAt osgood h
  have hz : γ y ∈ mcPts W := h.2.self_of_nhds.2.1
  have hne : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0 := hz.1
  have hzP : γ y ∈ mcPts P := ⟨hz.1, fun f hf => hz.2 f (hPW hf)⟩
  have hφ : ContDiffAt ℝ 2 (fun z => Real.log (A.h z)) (γ y) :=
    ((hs.1.contDiffAt (isOpen_blockNonzero.mem_nhds hne)).of_le
      (WithTop.coe_le_coe.mpr le_top)).log (A.pos _ hne).ne'
  have htan : IsConeTangent (Int.castRingHom ℂ) P0 (γ y) (fderiv ℂ γ y (Pi.single 0 1)) := by
    intro f hf
    have h0 : (fun y' => eval (γ y') (map (Int.castRingHom ℂ) f)) =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
      filter_upwards [h.2] with y' hy'
      exact hy'.2.1.2 f (hPW (hP0 hf))
    have hd := (hasFDerivAt_eval (map (Int.castRingHom ℂ) f) (γ y)).comp y
      hA.differentiableAt.hasFDerivAt
    have h00 := (hasFDerivAt_const (𝕜 := ℂ) (0 : ℂ) y).congr_of_eventuallyEq h0
    have := congrArg (fun L => L (Pi.single 0 1)) (hd.unique h00)
    simpa using this
  have hlevi : 0 ≤ ReciprocityTheory.AnForm.levi (fun z => Real.log (A.h z)) (γ y)
      (fderiv ℂ γ y (Pi.single 0 1)) := hs.2 (γ y) hzP _ htan
  have key := ReciprocityTheory.AnForm.levi_comp (Pi.single 0 1) hA hφ
  rw [← key] at hlevi
  unfold ReciprocityTheory.AnForm.levi at hlevi
  simp only [Function.comp_def] at hlevi
  rw [maDensity_one]
  apply div_nonneg _ (by positivity)
  linarith

theorem geomDeg_one_nonneg {P P0 W : Ideal (MRing ι)} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hP0 : P0 ≤ P)
    (hs : IsSemipositiveRel P0 P A) (hPW : P ≤ W) : 0 ≤ geomDeg W A 1 := by
  classical
  unfold geomDeg ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    refine MeasureTheory.integral_nonneg fun y => ?_
    refine finsum_nonneg fun w => finsum_nonneg fun _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · simpa only [one_mul] using maDensity_nonneg hP0 hPW hs hγ.choose_spec
    · exact le_rfl
  · exact le_rfl

end NefOnGenericOfSemipos

theorem NefOnGenericOfSemipos.proof : NefOnGenericOfSemipos.Statement :=
  fun _ _ _ _ _ _ _ hP0 hs _ _ hPW => NefOnGenericOfSemipos.geomDeg_one_nonneg hP0 hs hPW

theorem ArithmeticVolumeBig.of_moriwakiBig_only (hM : MoriwakiBigStatement) : ArithmeticVolumeBig.Statement :=
  ArithmeticVolumeBig.of_moriwakiBig NefOnGenericOfSemipos.proof hM

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedModOfSubsingleton
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GeneratedMod (S : Type*) [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] (ι : K → Type*)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M]
    [Module S M] [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) : Prop :=
  ∀ I : KH.Cell K ι 0, ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d,
    ∃ (t : MRingOver S ι) (a : K → ℕ) (r : ℕ) (p : Fin r → MRingOver S ι) (z : Fin r → KH.CechC S ι M 0),
      t ∈ KH.cellMon S I.1 ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t a ∧ (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (p j) a) ∧
      (∀ j, z j ∈ KH.cechZc ι 𝓜 d 0) ∧ t • x = ∑ j, p j • z j I

def H1GenAmple (S : Type) [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M),
    Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
    ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c →
      Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1) ∧ GeneratedMod S ι 𝓜 (e + c • N)

section Point

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [∀ k, Subsingleton (ι k)]




omit [Fintype K] [∀ k, Subsingleton (ι k)] in
theorem isMultiHomog_one_zero : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRingOver S ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    rw [mem_support_iff, coeff_one] at hm
    split_ifs at hm with h
    · exact h.symm
    · exact absurd rfl hm
  simp [this]

end Point

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLiftModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def LiftModel.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (N : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → KH.AmpleV ℚ (KH.genIdeal y) N →
    (∃ c : ℕ, 1 ≤ c ∧ KH.AmpleV ℚ (KH.genIdeal y) (c • N - fun _ => 1)) →
    (∀ ℓ : ℕ, ℓ.Prime → KH.AmpleV (ZMod ℓ) (fibreIdeal ℓ y) N) →
    ∃ (a : ℕ) (ι' : Type) (_ : Fintype ι') (x' : ι' → Ω),
      1 ≤ a ∧ (∀ j, x' j ∈ chartLat y (a • N) 1) ∧ KH.GeneratesOn y (a • N) x' ∧
        Birational (fun p : Σ _ : Unit, ι' => x' p.2)

section Inhabitant

end Inhabitant

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNonvanishingDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

def NonvanishingDense.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (f : MRing ι), IsArithVar P d → f ∉ P →
    mcPts P ⊆ closure {z | z ∈ mcPts P ∧ eval z (map (Int.castRingHom ℂ) f) ≠ 0}

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegGeomDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def GenDegGeomDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → IsSmoothHerm A →
    geomDeg (mCoordIdeal y) A D = (genDeg (mCoordIdeal y) D A.a : ℝ)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SemiposTwist.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P0 P : Ideal (MRing ι)) (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (p q : ℕ), IsSemipositiveRel P0 P L → IsSemipositiveRel P0 P (HermLine.zcomb L (fsH ι) q p)

def GenOnFibres.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) (w : Fin n → Ω),
    (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    KH.GeneratedV ℚ (KH.genIdeal y) a ∧ ∀ ℓ : ℕ, ℓ.Prime → KH.GeneratedV (ZMod ℓ) (fibreIdeal ℓ y) a

def AmpleOfGenTwist.Statement : Prop :=
  ∀ (S : Type) [Field S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (α : K → ℤ) (p q : ℕ),
    IsMultiHomogIdeal V → KH.GeneratedV S V α → 1 ≤ p →
    KH.AmpleV S V ((q : ℤ) • α + fun _ => (p : ℤ))

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

section Objects

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

def blockMapC {J : Type} (k₀ : K) (M : Matrix J (ι k₀) ℤ) (z : (Σ k, ι k) → ℂ) : J → ℂ :=
  fun j => ∑ i, (M j i : ℂ) * z ⟨k₀, i⟩

def IsBlockImage {Ω : Type} [Field Ω] {J : Type} [Fintype J] (y : (Σ k, ι k) → Ω) (k₀ : K)
    (M : Matrix J (ι k₀) ℤ) (N : Matrix (ι k₀) J ℤ) (x : J → Ω) : Prop :=
  (∀ j, x j = ∑ i, (M j i : Ω) * y ⟨k₀, i⟩) ∧ ∀ i, y ⟨k₀, i⟩ = ∑ j, (N i j : Ω) * x j

end Objects

def BlockImageDatum.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    ∃ (d₀ : HSMBlockDatum D K ι Ω) (r : ℕ) (M : Matrix (Ix (Fin r)) (ι d.k₀) ℤ)
      (N : Matrix (ι d.k₀) (Ix (Fin r)) ℤ) (d' : HSMDatum D Ω (Fin r)),
      d₀.y = d.y ∧ d₀.k₀ = d.k₀ ∧ IsBlockImage d.y d.k₀ M N d'.x ∧
      (∀ z ∈ mcPts (mCoordIdeal d.y), d₀.A.h z = d'.m.ρ (blockMapC d.k₀ M z)) ∧
      ∀ n, blockChi d₀ n = resChi d' n

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionRingFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    ∃ (r : ℕ) (d : Fin r → ℕ) (e : Fin r → Ω), (∀ i, e i ∈ chartLat y a (d i)) ∧
      ∀ n : ℕ, chartLat y a n ≤ AddSubgroup.closure
        {s | ∃ (i : Fin r) (μ : Fin q → ℕ), d i + ∑ j, μ j = n ∧ s = e i * ∏ j, w j ^ μ j}

def SectionBounded.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (q : ℕ) (w : Fin q → Ω),
    (∀ j, w j ∈ chartLat y A.a 1) → KH.GeneratesOn y A.a w → (∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)) →
    ∀ (n : ℕ) (s : Ω), s ∈ chartLat y A.a n → ∃ C : ℝ, IsBoundedH (mCoordIdeal y) y A n C s

def SectionBoundedMul.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (n m : ℕ) (C C' : ℝ) (s t : Ω),
    s ∈ chartLat y A.a n → t ∈ chartLat y A.a m →
    IsBoundedH (mCoordIdeal y) y A n C s → IsBoundedH (mCoordIdeal y) y A m C' t →
    IsBoundedH (mCoordIdeal y) y A (n + m) (C * C') (s * t)

section Inhabitants

open ProjLine

theorem isBoundedH_one_of_isSmallH {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {τ : ℕ} {s : Ω}
    (h : IsSmallH P y A τ s) : IsBoundedH P y A τ 1 s := by
  intro dg dh g h' z hg hh hdeg he hz
  rw [one_mul]
  exact h dg dh g h' z hg hh hdeg he hz

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsSemipositiveRelTrivLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def ArithmeticVolumeDegreeZero.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A → genDeg (mCoordIdeal y) D A.a ≤ 0 →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A) ≤ arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D

namespace ArithmeticVolumeDegreeZero

end ArithmeticVolumeDegreeZero

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingWeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

def EmbeddingWeight.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (Λ : (F →+* ℂ) → ℝ),
    (∀ sg, 0 < Λ sg) → (∀ sg, Λ (NumberField.ComplexEmbedding.conjugate sg) = Λ sg) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    ∃ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, B.a = 0 ∧ IsSmoothHerm B ∧ IsConjInvariantH B ∧
      ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → B.h =ᶠ[𝓝 z] fun _ => Λ sg

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BlockResolutionMetricObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

def blockCGram (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Σ k, ι k) ℚ) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun k l => ∫ x, pairValH d.A n (b k) (b l) (blockPt d x) ∂d.dV


open Classical in
def blockCChi (d : HSMBlockDatum D K ι Ω) (n : ℕ) : ℝ :=
  if h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM d.y d.k₀ n p.2 then
    -(1 / 2) * Real.log (blockCGram d n h.choose.2).det.re
  else 0

def blockInterpPot (d : HSMBlockDatum D K ι Ω) (A A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (t : ℝ) : LocPot d.R.X where
  U := d.R.U
  isOpen_U := d.R.isOpen_U
  mem_U := d.R.mem_U
  φ x y := (1 - t) * Real.log (A.h (d.R.lift x y)) + t * Real.log (A'.h (d.R.lift x y))

def blockMetricInt (d : HSMBlockDatum D K ι Ω) (A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) : ℝ :=
  ∫ t in (0 : ℝ)..1, mInt d.R.A (fun _ => blockInterpPot d d.A A' t)
    fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x))

def blockMixPot (A A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (D i : ℕ) : Fin D → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z => if j.val < i then Real.log (A'.h z) else Real.log (A.h z)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeroneseParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory

noncomputable section

namespace Veronese

abbrev Idx (D : ℕ) : Type := {p : Fin (D + 1) × Fin (D + 1) // p.1 ≤ p.2}

def Fld (D : ℕ) : Type := FractionRing (MvPolynomial (Fin (D + 1)) ℚ)

instance instField (D : ℕ) : Field (Fld D) :=
  inferInstanceAs (Field (FractionRing (MvPolynomial (Fin (D + 1)) ℚ)))

instance instCharZero (D : ℕ) : CharZero (Fld D) :=
  inferInstanceAs (CharZero (FractionRing (MvPolynomial (Fin (D + 1)) ℚ)))

instance instAlgebra (D : ℕ) : Algebra (MvPolynomial (Fin (D + 1)) ℚ) (Fld D) :=
  inferInstanceAs (Algebra (MvPolynomial (Fin (D + 1)) ℚ) (FractionRing (MvPolynomial (Fin (D + 1)) ℚ)))

instance instIsFractionRing (D : ℕ) : IsFractionRing (MvPolynomial (Fin (D + 1)) ℚ) (Fld D) :=
  Localization.isLocalization

def t (D : ℕ) (i : Fin (D + 1)) : Fld D := algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Fld D) (X i)

def x (D : ℕ) : Ix (Idx D) → Fld D := fun q => t D q.2.1.1 * t D q.2.1.2

def map (D : ℕ) (w : Fin (D + 1) → ℂ) : Ix (Idx D) → ℂ := fun q => w q.2.1.1 * w q.2.1.2

def wt {D : ℕ} (q : Ix (Idx D)) : ℝ := if q.2.1.1 = q.2.1.2 then 1 else 2

def scale (D : ℕ) (z : Ix (Idx D) → ℂ) : Ix (Idx D) → ℂ := fun q => (Real.sqrt (wt q) : ℂ) * z q

theorem wt_pos {D : ℕ} (q : Ix (Idx D)) : 0 < wt q := by
  unfold wt
  split_ifs <;> norm_num

theorem scale_ne_zero {D : ℕ} {z : Ix (Idx D) → ℂ} (hz : z ≠ 0) : scale D z ≠ 0 := by
  intro h
  apply hz
  funext q
  have h1 := congrFun h q
  have h2 : (Real.sqrt (wt q) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (wt_pos q)).ne'
  simpa [scale, h2] using h1

def metric (D : ℕ) : ConeMetric ℂ (Ix (Idx D)) where
  ρ z := (fsMetric (ι := Ix (Idx D))).ρ (scale D z)
  pos z hz := (fsMetric (ι := Ix (Idx D))).pos _ (scale_ne_zero hz)
  smul c z := by
    have : scale D (c • z) = c • scale D z := by
      funext q
      simp only [scale, Pi.smul_apply, smul_eq_mul]
      ring
    rw [this, (fsMetric (ι := Ix (Idx D))).smul]

def gram (D n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Ix (Idx D)) ℚ) : Matrix (Fin r) (Fin r) ℝ :=
  fun k l => (1 / 2) *
    ((∫ p : CP D, pairVal (metric D) n (b k) (b l) (map D p.rep) ∂CP.fsMeasure D).re +
      (∫ p : CP D, pairVal (metric D) n (b k) (b l) (conjPt (map D p.rep)) ∂CP.fsMeasure D).re)


open Classical in
def chi (D n : ℕ) : ℝ :=
  if h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix (Idx D)) ℚ), IsSecBasis (x D) n p.2 then
    -(1 / 2) * Real.log (gram D n h.choose.2).det
  else 0

end Veronese

open Veronese

def VeroneseArith.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D → IsArithVar (ι := GlobalTheory (Idx D)) (coordIdeal ℤ (Veronese.x D)) (D + 1)

def VeroneseSemipos.Statement : Prop :=
  ∀ D : ℕ, IsSemipositiveRel (ι := GlobalTheory (Idx D)) ⊥ (coordIdeal ℤ (Veronese.x D))
    (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofCone (Veronese.metric D))

def VeroneseResolution.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D → ∃ (J : Ideal (MRing (GlobalTheory (Idx D))))
    (R : AnRes (ι := GlobalTheory (Idx D)) (coordIdeal ℤ (Veronese.x D)) J D)
    (_ : MeasurableSpace R.X) (_ : BorelSpace R.X) (dV : Measure R.X),
    IsSmoothVolume R.A dV ∧
    ∀ g : (Ix (Idx D) → ℂ) → ℂ, (∀ (c : ℂ) (z : Ix (Idx D) → ℂ), c ≠ 0 → g (c • z) = g z) →
      ∫ y, g (R.lift y y) ∂dV = ∫ p : CP D, g (Veronese.map D p.rep) ∂CP.fsMeasure D

def VeroneseChi.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D → ∀ n : ℕ, Veronese.chi D n = chiP D (2 * n)

def VeroneseTop.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D → ∀ I : AllFam, I.IsFamily →
    top I (Veronese.x D) (Veronese.metric D) D = 2 ^ (D + 1) * hhOf I D

def VeroneseGenDeg.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D → genDeg (ι := GlobalTheory (Idx D)) (coordIdeal ℤ (Veronese.x D)) D 1 = 2 ^ D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEuclideanSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def imageLattice {E V : Type*} [AddCommGroup E] [AddCommGroup V] (φ : E →+ V) : Submodule ℤ V :=
  AddSubgroup.toIntSubmodule φ.range

def EuclideanSections.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmallGeneratedDatum P0 y D A → IsConjInvariantH A →
    ∃ (r : ℕ → ℕ) (φ : ∀ n : ℕ, chartLat y A.a n →+ EuclideanSpace ℝ (Fin (r n))),
      (∀ n, Function.Injective (φ n)) ∧
      (∀ n, DiscreteTopology (imageLattice (φ n))) ∧
      (∀ n [DiscreteTopology (imageLattice (φ n))], IsZLattice ℝ (imageLattice (φ n))) ∧
      (∀ (n : ℕ) (c : ℝ) (s : chartLat y A.a n), 0 ≤ c →
        IsBoundedH (mCoordIdeal y) y A n c (s : Ω) → ‖φ n s‖ ≤ c) ∧
      (∃ C : ℝ, ∀ n : ℕ, (r n : ℝ) ≤ C * ((n : ℝ) + 1) ^ D) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ∀ [DiscreteTopology (imageLattice (φ n))] [IsZLattice ℝ (imageLattice (φ n))],
          -Real.log (ZLattice.covolume (imageLattice (φ n))) ≤
            (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + ε) *
              ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallPacking
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SmallPacking.Statement : Prop := PackingStatement

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBirationalModelExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def BirationalModelExists.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ),
    IsArithVar P d → ∃ (Ω : Type) (_ : Field Ω) (y : (Σ k, ι k) → Ω), mCoordIdeal y = P ∧ Birational y

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibreVar
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

def GenericFibreVar.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → IsProjVarF (KH.genIdeal y) D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionSup
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def resolutionVolumeL2Complex (d : HSMDatum D Ω κ) (n : ℕ) (f : MvPolynomial (Ix κ) ℂ) : ℝ :=
  Real.sqrt (∫ y, ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2 ∂d.dV)

def ResolutionSupBound.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MvPolynomial (Ix κ) ℂ, f.IsHomogeneous n →
      ∀ z ∈ pts (coordIdeal ℤ d.x),
        ptNorm d.m (RingHom.id ℂ) n f z ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionPointHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def SmallSectionPointHeight.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (τ : ℕ) (s : Ω) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    1 ≤ τ → s ∈ chartLatNm y A.a τ → s ≠ 0 → IsSmallH (mCoordIdeal y) y A τ s →
    ∃ f : MRing ι, (∃ d, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d) ∧ f ∉ mCoordIdeal y ∧
      ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal y ≤ W → f ∉ W → 0 ≤ II K ι W 1 ![A]

theorem SmallSectionPointHeight.chartLat_le_chartLatNm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : chartLat y a τ ≤ chartLatNm y a τ := by
  intro s hs c hc
  have h := hs c hc
  exact (mem_integralClosure_iff _ _).mpr (isIntegral_algebraMap (x := (⟨_, h⟩ : chartRingZ y c)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNestedLattice
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def ChangeOfLatticeNested.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric (C := ℂ) (ι := Ix κ)),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    (fun n : ℕ => latLogIndex x (matAct B x) n -
        (top I (matAct B x) m' D - top I x m D) * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D

namespace ChangeOfLatticeNested

theorem matAct_one {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J] [DecidableEq J] (x : J → Ω) :
    matAct (1 : Matrix J J ℚ) x = x := by
  funext i
  simp only [matAct, Matrix.one_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

end ChangeOfLatticeNested

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
