module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothAutomorphicOpenInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchLieDerivativeExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVector

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CompanionTheory.CuspFinGL

theorem cuspRapidDecaySiegelGL : GlobalTheory.Published.CuspRapidDecaySiegelGL := by
  intro E _ _ _ a φ hφ
  have hs := GlobalTheory.CompanionTheory.ArchSmooth.sm_mem_archSmooth E a φ
  have hc : Continuous φ.1 := ContAut.continuous_of_isOpen_stab E a φ hφ.1.level
  exact GlobalTheory.CompanionTheory.SiegelDecay.rapid_decay_of_one_parabolic_bounds E a φ.1 hc
    (GlobalTheory.CompanionTheory.GGPS.ggps_bound E a φ.1 hs (GlobalTheory.CompanionTheory.LeftInv.isLeftInvariant_of_isAutForm E a φ hφ.1)
      (GlobalTheory.CompanionTheory.AutLevel.exists_open_level E a φ hφ.1) (GlobalTheory.CompanionTheory.CuspBridge.isCuspidal_of_isCuspForm E a φ hφ)
      (GlobalTheory.T.arch_lie_derivative_exists E a φ hs hφ.1) (GlobalTheory.CompanionTheory.BoxBound.box_bound E a φ hφ.1))

theorem cuspFormsBoundedGL : GlobalTheory.Published.CuspFormsBoundedGL :=
  GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay cuspRapidDecaySiegelGL

end GlobalTheory.CompanionTheory.CuspFinGL
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Free

def e0 (K : Type) [Zero K] [One K] (M : ℕ) : Fin 1 → Fin (M + 2) → K :=
  fun _ => Fin.cons 1 fun _ => 0

def consA {K : Type} [Zero K] [One K] {M n : ℕ} (a : Fin 1 → Fin n → K) (Y : Fin n → Fin M → K) :
    Fin (n + 1) → Fin (M + 2) → K :=
  Fin.cons (Fin.cons 1 fun _ => 0) fun j => Fin.cons (a 0 j) (Fin.cons 0 (Y j))

section PiLocalization₂

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]

def stageInt (σ : E →ₐ[F] E) {M n d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (lam : Measure R) (m' : Measure (Fin n → Fin M → R ⊗[F] E))
    (φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞) (g : HA R σ (hypOne J)) : ℝ≥0∞ :=
  ∫⁻ Y, ∫⁻ a, φ (actW R σ (hypOne J) g (consA a Y)) ∂(coordW R b lam 1 n) ∂m'

end PiLocalization₂

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def latStab (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (g : HA (Fv F v) σ J) : Prop :=
  ∀ x : Fin 1 → Fin M → Fv F v ⊗[F] E, actW (Fv F v) σ J g x ∈ latV b v ↔ x ∈ latV b v

def primV (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) :=
  {y | ∃ g : HA (Fv F v) σ (hypOne J), latStab σ (hypOne J) b v g ∧
    actW (Fv F v) σ (hypOne J) g (e0 _ M) = y}

def purePr (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞)
    (y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E) : ℝ≥0∞ :=
  {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E | ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v}.indicator
    (fun Y => Ψinf (projInf Y) * ∏ v ∈ S, Ψ v (projV v (projFin Y))) y

def ratA (n : ℕ) : AddSubgroup (Fin 1 → Fin n → AF F ⊗[F] E) where
  carrier := Set.range (ratTup (AF F) : (Fin 1 → Fin n → E) → Fin 1 → Fin n → AF F ⊗[F] E)
  zero_mem' := ⟨0, by funext a i; simp [ratTup]⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by funext a i; simp [ratTup]⟩
  neg_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by funext a i; simp [ratTup]⟩

def IsCovolOne {n : ℕ} (dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E)) : Prop :=
  dA.IsAddHaarMeasure ∧ ∃ D : Set (Fin 1 → Fin n → AF F ⊗[F] E),
    IsAddFundamentalDomain (ratA (F := F) (E := E) n) D dA ∧ dA D = 1

end Adelic

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

section Lat

variable (K : Type) [Field K] [NumberField K]

def intVec (m : ℕ) : Submodule (𝓞 K) (Fin m → K) where
  carrier := {v | ∀ i, ∃ o : 𝓞 K, algebraMap (𝓞 K) K o = v i}
  add_mem' := by
    intro v w hv hw i
    obtain ⟨o, ho⟩ := hv i
    obtain ⟨p, hp⟩ := hw i
    exact ⟨o + p, by simp [ho, hp]⟩
  zero_mem' := fun _ => ⟨0, by simp⟩
  smul_mem' := by
    intro a v hv i
    obtain ⟨o, ho⟩ := hv i
    exact ⟨a * o, by simp [ho, Algebra.smul_def]⟩

abbrev FQ : Type := (Fin 1 → K) ⧸ intVec K 1

def den (x : K) : Ideal (𝓞 K) :=
  Ideal.torsionOf (𝓞 K) (FQ K) (Submodule.Quotient.mk fun _ => x)

def idx (c : Submodule (𝓞 K) K) : ℕ :=
  (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex c.toAddSubgroup

def zetaR (r : ℝ) : ℝ := ∑' I : Ideal (𝓞 K), (Ideal.absNorm I : ℝ) ^ (-r)

variable {K}

def lam {m : ℕ} (c : Matrix (Fin m) (Fin m) K) : Submodule (𝓞 K) (Fin m → K) :=
  intVec K m ⊔ (intVec K m).map (c.mulVecLin.restrictScalars (𝓞 K))

def IsLat {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) : Prop :=
  L.FG ∧ Submodule.span K (L : Set (Fin m → K)) = ⊤

def tor {m : ℕ} (c : Matrix (Fin m) (Fin m) K) (u : Fin m → K) : Ideal (𝓞 K) :=
  Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ lam c) (Submodule.Quotient.mk u)

def lastFib {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Submodule (𝓞 K) K :=
  (lam C).comap (LinearMap.single (𝓞 K) (fun _ : Fin (m + 1) => K) (Fin.last m))

theorem isLat_intVec (m : ℕ) : IsLat (intVec K m) := by
  refine ⟨?_, ?_⟩
  · have h : intVec K m = (⊤ : Submodule (𝓞 K) (Fin m → 𝓞 K)).map
        (LinearMap.compLeft (Algebra.linearMap (𝓞 K) K) (Fin m)) := by
      ext v
      simp only [Submodule.mem_map, Submodule.mem_top, true_and]
      constructor
      · intro hv
        choose o ho using hv
        exact ⟨o, funext fun i => ho i⟩
      · rintro ⟨o, rfl⟩ i
        exact ⟨o i, rfl⟩
    rw [h]
    exact Submodule.FG.map _ Module.Finite.fg_top
  · rw [eq_top_iff]
    intro v _
    have hv : v = ∑ i, v i • (Pi.single i (1 : K) : Fin m → K) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    intro j
    by_cases h : j = i
    · subst h
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Pi.single_apply, h]⟩

end Lat

section GlobalTheory

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def blk {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (d : E) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) E := fun i j =>
  Fin.lastCases (motive := fun _ => E)
    (Fin.lastCases (motive := fun _ => E) d (fun b => σ (u b)) j)
    (fun a => Fin.lastCases (motive := fun _ => E) (u a) (fun b => c a b) j) i

variable [NumberField E]

def sO (σ : E →ₐ[F] E) : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (σ : E →+* E)

end GlobalTheory

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

variable {D : D7} {ρ r s p : ℕ}

def rowT (y : Mx D (r + s) p) : Mx D r p := fun i j => y (Fin.castAdd s i) j

def rowB (y : Mx D (r + s) p) : Mx D s p := fun i j => y (Fin.natAdd r i) j

def rowJ (x : Mx D r p) (z : Mx D s p) : Mx D (r + s) p :=
  fun i j => Fin.addCases (motive := fun _ => AE D) (fun a => x a j) (fun b => z b j) i

def IsBlockSL2Embedding (b : HermE D (r + s)) (b₁ : HermE D r) (b₂ : HermE D s) : Prop :=
  (∀ i j, b.1 (Fin.castAdd s i) (Fin.castAdd s j) = b₁.1 i j) ∧
  (∀ i j, b.1 (Fin.natAdd r i) (Fin.natAdd r j) = b₂.1 i j) ∧
  (∀ i j, b.1 (Fin.castAdd s i) (Fin.natAdd r j) = 0) ∧ ∀ i j, b.1 (Fin.natAdd r j) (Fin.castAdd s i) = 0

def Total (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (b₀ : HermE D ρ) (μ : Measure (Mx D ρ p)) : Prop :=
  ∀ u : Mx D ρ p → ℂ, Continuous u → (∃ B : ℝ, ∀ y, ‖u y‖ ≤ B) →
    (∀ Ω, IsTh ψ χ θ b₀ μ Ω → ∫ y, u y * conj (Ω 1 y) ∂μ = 0) → u = 0

abbrev V1 (D : D7) : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral 1

def WeilCont : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle,
    IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ Φ : schwartzA θ V.rank n,
      Continuous fun u : G D n × Mx D V.rank n => (ω u.1 Φ).1 u.2

def WeilKFin : Prop :=
  ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle,
    IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω →
    ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l → ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ,
      (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) → ∀ Φ : schwartzA θ V.rank n, Φ.1 ∈ fockA θ V n l s →
      ∃ W : Submodule ℂ (Mx D V.rank n → ℂ), FiniteDimensional ℂ W ∧ W ≤ fockA θ V n l s ∧ ∀ k ∈ K D n, (ω k Φ).1 ∈ W

def OrbitMaj : Prop :=
  ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ l : D.what₂.Tau → ℝ, (∀ τ, l τ ≠ 0) →
    ∀ f ∈ fockA θ (V1 D) n l (fun _ => 1), ∀ A₁ A₂ : Set (Mx D n n), IsCompact A₁ → IsCompact A₂ →
      ∃ M ∈ schwartzA θ (V1 D).rank n, (∀ y, 0 ≤ (M y).re ∧ (M y).im = 0) ∧
        ∀ a : GL (Fin n) (AE D), a.1 ∈ A₁ → (a⁻¹).1 ∈ A₂ → ∀ y : Mx D (V1 D).rank n,
          ‖f (HMul.hMul y a.1 : Mx D (V1 D).rank n)‖ ≤ ‖M y‖

def IwaCpt : Prop :=
  ∀ (D : D7) (n : ℕ) (C : Set (G D n)), IsCompact C → ∃ (A₁ A₂ : Set (Mx D n n)) (R : ℝ), IsCompact A₁ ∧ IsCompact A₂ ∧
    ∀ h ∈ C, ∃ (m t k : G D n) (a : GL (Fin n) (AE D)) (b : Mx D n n), k ∈ K D n ∧ h = m * t * k ∧
      mat m = blk4 a.1 0 0 (adj (a⁻¹).1) ∧ mat t = blk4 1 b 0 1 ∧ a.1 ∈ A₁ ∧ (a⁻¹).1 ∈ A₂ ∧
      (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ≤ R

def FockTranslateSchwartzMajorant : Prop :=
  ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle,
    IsHeckeChar D χ → ResEta D χ 1 → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D (V1 D).rank n)) (𝓕 : Set (Mx D (V1 D).rank n)), IsCovolOne (ratMx D (V1 D).rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ (V1 D).rank n), IsWeilSch ψ χ θ (V1 D) μ ω →
    ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l → (∀ τ, l τ ≠ 0) → ∀ Φ : schwartzA θ (V1 D).rank n,
      Φ.1 ∈ fockA θ (V1 D) n l (fun _ => 1) → ∀ C : Set (G D n), IsCompact C →
      ∃ M ∈ schwartzA θ (V1 D).rank n, ∀ h ∈ C, ∀ y, ‖(ω h Φ).1 y‖ ≤ ‖M y‖

def SchwTensor : Prop :=
  ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ r s p : ℕ, ∀ φ ∈ schwartzA θ r p, ∀ φ' ∈ schwartzA θ s p,
    (fun y : Mx D (r + s) p => φ (rowT y) * φ' (rowB y)) ∈ schwartzA θ (r + s) p

def ProdTh : Prop :=
  ∀ (D : D7) (r s p : ℕ) (μr : Measure (Mx D r p)) (𝓕r : Set (Mx D r p)) (μs : Measure (Mx D s p)) (𝓕s : Set (Mx D s p)),
    IsCovolOne (ratMx D r p) μr 𝓕r → IsCovolOne (ratMx D s p) μs 𝓕s → ∀ ψ, IsCharAF D.host.F ψ →
    ∀ (χr χs : (AE D)ˣ →* Circle) (θ : InfFam D), IsInfFam θ → ∀ (br : HermE D r) (bs : HermE D s) (b : HermE D (r + s)),
    IsBlockSL2Embedding b br bs → ∀ Ωr Ωs, IsTh ψ χr θ br μr Ωr → IsTh ψ χs θ bs μs Ωs →
      IsTh ψ (χr * χs) θ b ((μr.prod μs).map fun z => rowJ z.1 z.2) fun h y => Ωr h (rowT y) * Ωs h (rowB y)

def ProdMeas : Prop :=
  ∀ (D : D7) (r s p : ℕ) (μr : Measure (Mx D r p)) (𝓕r : Set (Mx D r p)) (μs : Measure (Mx D s p)) (𝓕s : Set (Mx D s p))
    (μ : Measure (Mx D (r + s) p)) (𝓕 : Set (Mx D (r + s) p)),
    IsCovolOne (ratMx D r p) μr 𝓕r → IsCovolOne (ratMx D s p) μs 𝓕s → IsCovolOne (ratMx D (r + s) p) μ 𝓕 →
    μ = (μr.prod μs).map fun z => rowJ z.1 z.2

def EucTotal : Prop :=
  ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z]
    (lam : Measure Z) [lam.IsAddHaarMeasure] (ι : Type) [Fintype ι] (c : ι → Z →L[ℝ] ℂ), (∀ z, (∀ k, c k z = 0) → z = 0) →
    ∀ A : Subalgebra ℂ (Z → ℂ), (∀ k, (fun z => c k z) ∈ A) → (∀ k, (fun z => conj (c k z)) ∈ A) →
    ∀ (g : Z → ℝ), Continuous g → (∀ z, 0 < g z) → ∀ C a : ℝ, 0 < a → (∀ z, g z ≤ C * Real.exp (-a * ‖z‖ ^ 2)) →
    ∀ w : Z → ℂ, Continuous w → (∃ B : ℝ, ∀ z, ‖w z‖ ≤ B) → (∀ P ∈ A, ∫ z, w z * P z * (g z : ℂ) ∂lam = 0) → w = 0

def FockTotal : Prop :=
  ∀ (D : D7) (p : ℕ) (θ : InfFam D), IsInfFam θ → ∀ l : D.what₂.Tau → ℝ, (∀ τ, l τ ≠ 0) →
    ∀ (μ : Measure (Mx D (V1 D).rank p)) (𝓕 : Set (Mx D (V1 D).rank p)), IsCovolOne (ratMx D (V1 D).rank p) μ 𝓕 →
    ∀ u : Mx D (V1 D).rank p → ℂ, Continuous u → (∃ B : ℝ, ∀ y, ‖u y‖ ≤ B) →
      (∀ φ ∈ fockA θ (V1 D) p l (fun _ => 1), ∫ y, u y * conj (φ y) ∂μ = 0) → u = 0

def OneTotal : Prop :=
  ∀ (D : D7) (p : ℕ) (μ : Measure (Mx D 1 p)) (𝓕 : Set (Mx D 1 p)), IsCovolOne (ratMx D 1 p) μ 𝓕 →
    ∀ ψ, IsCharAF D.host.F ψ → ∀ b₀ : HermE D 1, b₀.1.det ≠ 0 → ∀ χ, IsHeckeChar D χ → ResEta D χ 1 →
    ∀ θ, IsInfFam θ → Total ψ χ θ b₀ μ

def ZeroTotal : Prop :=
  ∀ (D : D7) (p : ℕ) (μ : Measure (Mx D 0 p)) (𝓕 : Set (Mx D 0 p)), IsCovolOne (ratMx D 0 p) μ 𝓕 →
    ∀ ψ, IsCharAF D.host.F ψ → ∀ b₀ : HermE D 0, ∀ θ, IsInfFam θ → Total ψ 1 θ b₀ μ

def StepTotal : Prop :=
  ∀ (D : D7) (r s p : ℕ) (μr : Measure (Mx D r p)) (𝓕r : Set (Mx D r p)) (μs : Measure (Mx D s p)) (𝓕s : Set (Mx D s p))
    (μ : Measure (Mx D (r + s) p)) (𝓕 : Set (Mx D (r + s) p)),
    IsCovolOne (ratMx D r p) μr 𝓕r → IsCovolOne (ratMx D s p) μs 𝓕s → IsCovolOne (ratMx D (r + s) p) μ 𝓕 →
    ∀ ψ, IsCharAF D.host.F ψ → ∀ (χr χs : (AE D)ˣ →* Circle) (θ : InfFam D), IsInfFam θ →
    ∀ (br : HermE D r) (bs : HermE D s) (b : HermE D (r + s)), IsBlockSL2Embedding b br bs →
      Total ψ χr θ br μr → Total ψ χs θ bs μs → Total ψ (χr * χs) θ b μ

end GlobalTheory.CompanionTheory.ThTot

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def tupIn {M n : ℕ} (L : Set (R ⊗[F] E)) : Set (Fin n → Fin M → R ⊗[F] E) :=
  {X | ∀ i k, X i k ∈ L}

def eMat {n : ℕ} (l : Fin n) (a : Fin n → R ⊗[F] E) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)).updateCol l a

def dMat {n : ℕ} (l : Fin n) (s : R ⊗[F] E) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  Matrix.diagonal (Function.update 1 l s)

def cjM (σ : E →ₐ[F] E) {n : ℕ} (g y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  (g.map (sigR R σ))ᵀ * y * g

def nearNF {M n : ℕ} (O L : Set (R ⊗[F] E)) (t : R ⊗[F] E) (j : ℕ) : Set (Fin n → Fin M → R ⊗[F] E) :=
  {X | X ∈ tupIn R L ∧ ∃ (l : Fin n) (a : Fin n → R ⊗[F] E), (∀ i, a i ∈ O) ∧ a l = 1 ∧
    ∀ k, ∑ i, X i k * a i ∈ (fun x => t ^ j * x) '' L}

def goodT {M n : ℕ} (O L : Set (R ⊗[F] E)) (S : Finset ((R ⊗[F] E)ˣ × (R ⊗[F] E))) (j : ℕ) :
    Set (Fin n → Fin M → R ⊗[F] E) :=
  tupIn R L \ ⋃ p ∈ S, nearNF R O L (p.1 : R ⊗[F] E) j

def gramIn (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (Y : Set (HermR R σ n)) :
    Set (Fin n → Fin M → R ⊗[F] E) :=
  {X | ∃ y ∈ Y, gramR R σ J X = (y : Matrix (Fin n) (Fin n) (R ⊗[F] E))}

def cjPre (σ : E →ₐ[F] E) {n : ℕ} (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (Y : Set (HermR R σ n)) :
    Set (HermR R σ n) :=
  {y | ∃ z ∈ Y, cjM R σ g (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = (z : Matrix (Fin n) (Fin n) (R ⊗[F] E))}

variable [TopologicalSpace R] [MeasurableSpace R]

def IsOrdData (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (O : Subring (R ⊗[F] E)) (S : Finset ((R ⊗[F] E)ˣ × (R ⊗[F] E))) : Prop :=
  IsCompact (O : Set (R ⊗[F] E)) ∧ IsOpen (O : Set (R ⊗[F] E)) ∧ (∀ x ∈ O, sigR R σ x ∈ O) ∧
  (∀ p ∈ S, (p.1 : R ⊗[F] E) ∈ O ∧ p.2 ≠ 0 ∧ (∀ x, p.2 * x = 0 → (p.1 : R ⊗[F] E) * x = x) ∧
    Filter.Tendsto (fun j : ℕ => p.2 * (p.1 : R ⊗[F] E) ^ j) Filter.atTop (nhds 0) ∧
    ∃ θ : ℝ≥0, θ < 1 ∧ ∀ Y : Set (R ⊗[F] E),
      coordK R b lam ((fun x => (p.1 : R ⊗[F] E) * x) '' Y) = θ * coordK R b lam Y) ∧
  ∀ (n M : ℕ) (X : Fin n → Fin M → R ⊗[F] E), ¬ LinearIndependent (R ⊗[F] E) X →
    ∃ p ∈ S, ∃ (l : Fin n) (a : Fin n → R ⊗[F] E), (∀ i, a i ∈ O) ∧ a l = 1 ∧
      ∀ k, p.2 * ∑ i, X i k * a i = 0

end Alg

section Help

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem rmul_mul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (g h : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    rmul R (rmul R X g) h = rmul R X (g * h) := by
  funext a i
  simp only [rmul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => mul_assoc _ _ _

theorem hR_sum_right (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin M → R ⊗[F] E)
    (y : Fin n → Fin M → R ⊗[F] E) (w : Fin n → R ⊗[F] E) :
    hR R σ J x (fun k => ∑ e, y e k * w e) = ∑ e, hR R σ J x (y e) * w e := by
  simp only [hR, hform, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hR_sum_left (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin n → Fin M → R ⊗[F] E)
    (y : Fin M → R ⊗[F] E) (w : Fin n → R ⊗[F] E) :
    hR R σ J (fun k => ∑ c, x c k * w c) y = ∑ c, sigR R σ (w c) * hR R σ J (x c) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hform, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem gramR_rmul (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    gramR R σ J (rmul R X g) = cjM R σ g (gramR R σ J X) := by
  ext a c
  change hR R σ J (fun i => ∑ e, X e i * g e a) (fun i => ∑ e, X e i * g e c) = _
  rw [hR_sum_right]
  simp only [hR_sum_left]
  rfl

theorem cjM_mul (σ : E →ₐ[F] E) {n : ℕ} (g h y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    cjM R σ (g * h) y = cjM R σ h (cjM R σ g y) := by
  simp only [cjM, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]

theorem cjM_one (σ : E →ₐ[F] E) {n : ℕ} (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    cjM R σ 1 y = y := by
  simp [cjM, Matrix.map_one, map_zero, map_one]

theorem cjM_mem (σ : E →ₐ[F] E) (hσ : ∀ x, sigR R σ (sigR R σ x) = x) {n : ℕ}
    (g y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (hy : y ∈ HermR R σ n) : cjM R σ g y ∈ HermR R σ n := by
  intro a c
  have hy' : ∀ a c, sigR R σ (y c a) = y a c := hy
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cjM, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_mul, hσ, hy']
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

def negCol {n : ℕ} (l : Fin n) (a : Fin n → R ⊗[F] E) : Fin n → R ⊗[F] E :=
  fun i => if i = l then 1 else - a i

theorem eMat_mul_negCol {n : ℕ} (l : Fin n) (a : Fin n → R ⊗[F] E) (hl : a l = 1) :
    eMat R l a * eMat R l (negCol R l a) = 1 := by
  ext i k
  simp only [Matrix.mul_apply, eMat, Matrix.updateCol_apply, Matrix.one_apply]
  by_cases hk : k = l
  · subst hk
    simp only [if_true, negCol]
    have : ∀ c, (if c = k then a i else if i = c then (1 : R ⊗[F] E) else 0) * (if c = k then 1 else - a c) =
        (if c = k then a i else 0) + (if c = i then (if i = k then 0 else - a i) else 0) := by
      intro c
      by_cases h1 : c = k
      · subst h1
        by_cases h2 : c = i
        · subst h2; simp
        · simp [h2]
      · by_cases h2 : c = i
        · subst h2; simp [h1]
        · simp [h1, h2, Ne.symm h2]
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h : i = k
    · subst h; simp [hl]
    · simp [h]
  · simp only [hk, if_false]
    have : ∀ c, (if c = l then a i else if i = c then (1 : R ⊗[F] E) else 0) * (if c = k then 1 else 0) =
        if c = k then (if i = k then 1 else 0) else 0 := by
      intro c
      by_cases h1 : c = k
      · subst h1; simp [hk]
      · simp [h1]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem dMat_mul {n : ℕ} (l : Fin n) (s t : R ⊗[F] E) (h : s * t = 1) : dMat R l s * dMat R l t = 1 := by
  rw [dMat, dMat, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases hi : i = l
  · subst hi; simpa using h
  · simp [Function.update_of_ne hi]

theorem sigR_sigR (σ : E →ₐ[F] E) (h : ∀ e, σ (σ e) = e) (x : R ⊗[F] E) : sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, h]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem isCompact_tupIn [TopologicalSpace (R ⊗[F] E)] {M n : ℕ} {L : Set (R ⊗[F] E)} (hL : IsCompact L) :
    IsCompact (tupIn (M := M) (n := n) R L) := by
  have : tupIn (M := M) (n := n) R L = Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => L := by
    ext X
    simp [tupIn]
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hL

end Help

end GlobalTheory.CompanionTheory.AvgFree
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHalfTr
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermPoisson

variable {D : D7} {r : ℕ}

section Gen

variable {F E A : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [CommRing A] [Algebra F A]

theorem trace_one_tmul' (e : E) :
    Algebra.trace A (A ⊗[F] E) ((1 : A) ⊗ₜ[F] e) = algebraMap F A (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem ann_gen (P : A → Prop) (hP : ∀ x : A, (∀ t : F, P (algebraMap F A t * x)) → ∃ c : F, x = algebraMap F A c)
    (z : A ⊗[F] E) (h : ∀ e : E, P (Algebra.trace A (A ⊗[F] E) (((1 : A) ⊗ₜ[F] e) * z))) :
    ∃ w : E, z = (1 : A) ⊗ₜ[F] w := by
  classical
  let b := Module.finBasis F E
  have hnd := traceForm_nondegenerate F E
  let d := (Algebra.traceForm F E).dualBasis hnd b
  let B := Algebra.TensorProduct.basis A b
  have hB : ∀ k, B k = (1 : A) ⊗ₜ[F] b k := fun k => Algebra.TensorProduct.basis_apply _ _
  have hz : ∑ k, B.repr z k • ((1 : A) ⊗ₜ[F] b k) = z := by
    simpa only [hB] using B.sum_repr z
  have ht : ∀ e : E, Algebra.trace A (A ⊗[F] E) (((1 : A) ⊗ₜ[F] e) * z) =
      ∑ k, B.repr z k * algebraMap F A (Algebra.trace F E (e * b k)) := by
    intro e
    conv_lhs => rw [← hz]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, Algebra.TensorProduct.tmul_mul_tmul, mul_one, map_smul, trace_one_tmul', smul_eq_mul]
  have hak : ∀ k, ∃ c : F, B.repr z k = algebraMap F A c := fun k => by
    refine hP _ fun t => ?_
    have h1 := h (t • d k)
    rw [ht] at h1
    have h2 : ∀ l, Algebra.trace F E (t • d k * b l) = if l = k then t else 0 := fun l => by
      have h3 : Algebra.trace F E (d k * b l) = if l = k then 1 else 0 :=
        LinearMap.BilinForm.apply_dualBasis_left hnd b k l
      rw [smul_mul_assoc, map_smul, h3]
      split_ifs <;> simp
    simp only [h2] at h1
    have h4 : ∑ l, B.repr z l * algebraMap F A (if l = k then t else 0) =
        algebraMap F A t * B.repr z k := by
      rw [Finset.sum_eq_single k (fun l _ hl => by rw [if_neg hl, map_zero, mul_zero])
        (fun hk => absurd (Finset.mem_univ k) hk), if_pos rfl, mul_comm]
    rwa [h4] at h1
  choose c hc using hak
  refine ⟨∑ k, c k • b k, ?_⟩
  rw [← hz, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hc k, TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

end Gen

theorem halfTr_add' (a b : AE D) : halfTr (a + b) = halfTr a + halfTr b := by
  simp only [halfTr, trA, map_add (f := _), mul_add]

theorem halfTr_zero' : halfTr (0 : AE D) = 0 := by
  simp [halfTr]

theorem halfTr_neg' (a : AE D) : halfTr (-a) = -halfTr a := by
  simp only [halfTr, trA, map_neg, mul_neg]

theorem halfTr_add_cA (w : AE D) : halfTr (w + cA D w) = Algebra.trace (AF D.host.F) (AE D) w := by
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) + algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
    rw [← map_add (f := _), add_halves, map_one]
  simp only [halfTr, trA, map_add (f := _), Formalism.IndefR.Datum.Brg.trace_cA, mul_add]
  rw [← add_mul, h2, one_mul]

theorem halfTr_incA' (e : D.host.E) :
    halfTr (incA D e) = algebraMap D.host.F (AF D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E e) := by
  rw [halfTr, trA, Formalism.IndefR.Fin.trace_incA, map_mul]

theorem continuous_halfTr' : Continuous (halfTr : AE D → AF D.host.F) :=
  continuous_const.mul Formalism.IndefR.Fin.cont_trace

def hE (i j : Fin r) (w : AE D) : Mx D r r :=
  Matrix.single j i w + Matrix.single i j (cA D w)

theorem adj_single' (a b : Fin r) (v : AE D) :
    adj (Matrix.single a b v : Mx D r r) = Matrix.single b a (cA D v) := by
  ext k l
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.single_apply]
  by_cases h : a = l ∧ b = k
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h, if_neg (by tauto), map_zero]

theorem hE_mem (i j : Fin r) (w : AE D) : hE i j w ∈ hermA D r := by
  change adj (hE i j w) = hE i j w
  rw [hE, adj_add, adj_single', adj_single', cA_cA, add_comm]

theorem trace_hE_mul (i j : Fin r) (w : AE D) {z : Mx D r r} (hz : z ∈ hermA D r) :
    Matrix.trace (HMul.hMul (hE i j w) z : Mx D r r) = w * z i j + cA D (w * z i j) := by
  have h : adj z = z := hz
  have hji : z j i = cA D (z i j) := (congrFun (congrFun h j) i).symm
  rw [hE, Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul, hji, map_mul]
  rfl

theorem rat_single' (a b : Fin r) (e : D.host.E) :
    (rat (Matrix.single a b e) : Mx D r r) = Matrix.single a b (incA D e) := by
  ext k l
  simp only [rat, Matrix.map_apply, Matrix.single_apply]
  by_cases h : a = k ∧ b = l
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, map_zero]

theorem hE_rat (i j : Fin r) (e : D.host.E) : hE i j (incA D e) ∈ ratMx D r r := by
  refine ⟨Matrix.single j i e + Matrix.single i j (star e), ?_⟩
  show rat _ = _
  rw [rat_add, rat_single', rat_single', hE, GlobalTheory.DualPairCheck.cA_incA]

theorem ann_E {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (z : AE D)
    (h : ∀ e : D.host.E, ψ (Algebra.trace (AF D.host.F) (AE D) (incA D e * z)) = 1) :
    ∃ w : D.host.E, z = incA D w :=
  ann_gen (F := D.host.F) (E := D.host.E) (A := AF D.host.F) (fun x => ψ x = 1)
    (fun x hx => GlobalTheory.T.adelic_character_orthogonal_is_rational D.host.F D.sp.cm.totReal ψ hψ x hx) z h

def chi (ψ : AddChar (AF D.host.F) ℂ) (m : Mx D r r) (b : hermA D r) : ℂ :=
  ψ (halfTr (Matrix.trace (HMul.hMul m b.1 : Mx D r r)))

theorem chi_add_left (ψ : AddChar (AF D.host.F) ℂ) (m m' : Mx D r r) (b : hermA D r) :
    chi ψ (m + m') b = chi ψ m b * chi ψ m' b := by
  simp only [chi]
  rw [Matrix.add_mul, Matrix.trace_add, halfTr_add', AddChar.map_add_eq_mul]

theorem chi_add_right (ψ : AddChar (AF D.host.F) ℂ) (m : Mx D r r) (b c : hermA D r) :
    chi ψ m (b + c) = chi ψ m b * chi ψ m c := by
  simp only [chi, AddSubgroup.coe_add]
  rw [Matrix.mul_add, Matrix.trace_add, halfTr_add', AddChar.map_add_eq_mul]

theorem chi_zero_left (ψ : AddChar (AF D.host.F) ℂ) (b : hermA D r) : chi ψ (0 : Mx D r r) b = 1 := by
  simp only [chi]
  rw [Matrix.zero_mul, Matrix.trace_zero, halfTr_zero', AddChar.map_zero_eq_one]

theorem chi_zero_right (ψ : AddChar (AF D.host.F) ℂ) (m : Mx D r r) : chi ψ m (0 : hermA D r) = 1 := by
  simp only [chi, AddSubgroup.coe_zero]
  rw [Matrix.mul_zero, Matrix.trace_zero, halfTr_zero', AddChar.map_zero_eq_one]

theorem chi_neg_left (ψ : AddChar (AF D.host.F) ℂ) (m : Mx D r r) (b : hermA D r) :
    chi ψ (-m) b = ψ (-halfTr (Matrix.trace (HMul.hMul m b.1 : Mx D r r))) := by
  simp only [chi]
  rw [Matrix.neg_mul, Matrix.trace_neg, halfTr_neg']

theorem chi_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {m : Mx D r r}
    (hm : m ∈ ratMx D r r) (c : ratHerm D r) : chi ψ m c.1 = 1 := by
  obtain ⟨γ, rfl⟩ := hm
  obtain ⟨δ, hδ⟩ := AddSubgroup.mem_comap.1 c.2
  have hδ' : rat δ = c.1.1 := hδ
  have h1 : (HMul.hMul (rat γ) c.1.1 : Mx D r r) = rat (γ * δ) := by rw [← hδ', rat_mul]
  have h2 : Matrix.trace (rat (γ * δ) : Mx D r r) = incA D (Matrix.trace (γ * δ)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [rat, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  show ψ (halfTr (Matrix.trace (HMul.hMul (rat γ) c.1.1 : Mx D r r))) = 1
  rw [h1, h2, halfTr_incA']
  exact hψ.2.2.1 _

theorem continuous_chi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (m : Mx D r r) :
    Continuous (chi ψ m : hermA D r → ℂ) := by
  refine hψ.1.comp (continuous_halfTr'.comp ?_)
  exact (continuous_const.matrix_mul continuous_subtype_val).matrix_trace

theorem star_psi' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (a : AF D.host.F) :
    star (ψ a) = ψ (-a) := by
  have h1 : ψ a * star (ψ a) = 1 := by
    have := hψ.2.1 a
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, this]
    simp
  rw [AddChar.map_neg_eq_inv]
  exact eq_inv_of_mul_eq_one_right h1

theorem rat_of_chi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (z : hermA D r)
    (h : ∀ t : ratHerm D r, chi ψ t.1.1 z = 1) : z ∈ ratHerm D r := by
  have key : ∀ i j, ∃ w : D.host.E, z.1 i j = incA D w := fun i j => by
    refine ann_E hψ _ fun e => ?_
    have h1 := h ⟨⟨hE i j (incA D e), hE_mem _ _ _⟩, AddSubgroup.mem_comap.2 (hE_rat i j e)⟩
    have h2 : chi ψ (hE i j (incA D e)) z = ψ (halfTr (Matrix.trace (HMul.hMul (hE i j (incA D e)) z.1 : Mx D r r))) := rfl
    rw [show chi ψ (hE i j (incA D e)) z = 1 from h1] at h2
    rw [trace_hE_mul i j _ z.2, halfTr_add_cA] at h2
    exact h2.symm
  choose w hw using key
  refine AddSubgroup.mem_comap.2 ⟨Matrix.of w, ?_⟩
  ext i j
  exact (hw i j).symm

theorem exists_chi_ne {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (u : ratHerm D r)
    (hu : u ≠ 0) : ∃ b : hermA D r, chi ψ u.1.1 b ≠ 1 := by
  obtain ⟨γ, hγ⟩ := AddSubgroup.mem_comap.1 u.2
  have hγ' : rat γ = u.1.1 := hγ
  obtain ⟨x₀, hx₀⟩ := hψ.2.2.2
  obtain ⟨i, j, hij⟩ : ∃ i j, γ i j ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hu
    apply Subtype.ext
    apply Subtype.ext
    have : γ = 0 := Matrix.ext fun i j => hc i j
    rw [← hγ', this, rat_zero]
    rfl
  obtain ⟨e₀, he₀⟩ := Algebra.trace_surjective D.host.F D.host.E 1
  let w : AE D := incA D (γ i j)⁻¹ * (x₀ • incA D e₀)
  refine ⟨⟨hE i j w, hE_mem _ _ _⟩, ?_⟩
  have h1 : chi ψ u.1.1 ⟨hE i j w, hE_mem _ _ _⟩ =
      ψ (halfTr (Matrix.trace (HMul.hMul (hE i j w) u.1.1 : Mx D r r))) := by
    simp only [chi]
    rw [Matrix.trace_mul_comm]
  rw [h1, trace_hE_mul i j _ u.1.2, halfTr_add_cA]
  have h2 : w * u.1.1 i j = x₀ • incA D e₀ := by
    rw [← hγ']
    show incA D (γ i j)⁻¹ * (x₀ • incA D e₀) * incA D (γ i j) = _
    rw [mul_comm, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hij, map_one, one_mul]
  rw [h2, map_smul, Formalism.IndefR.Fin.trace_incA, he₀, map_one, smul_eq_mul, mul_one]
  exact hx₀

end GlobalTheory.CompanionTheory.HermPoisson
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

section Gen

variable {V H : Type} [MeasurableSpace V] [MeasurableSpace H]

def DenLE (μ : Measure V) (ν : Measure H) (q : V → H) (S : Set V) (C : ℝ≥0∞) : Prop :=
  ∀ Y, MeasurableSet Y → μ (S ∩ q ⁻¹' Y) ≤ C * ν Y

end Gen

section Box

variable {K W : Type} [CommRing K] [Fintype W] {n M : ℕ}

def boxK (κ : K ≃+* (W → ℂ)) (r : Fin n → W → ℝ) : Set (Fin n → Fin M → K) :=
  {X | ∀ a i w, ‖κ (X a i) w‖ ≤ r a w}

def nearK (κ : K ≃+* (W → ℂ)) (w : W) (s : Fin n → ℂ) (ε : ℝ) : Set (Fin n → Fin M → K) :=
  {X | ∀ i, ‖∑ b, s b * κ (X b i) w‖ < ε}

def goodK (κ : K ≃+* (W → ℂ)) (R ε : ℝ) : Set (Fin n → Fin M → K) :=
  boxK κ (fun _ _ => R) \ ⋃ w : W, ⋃ a : Fin n, ⋃ s ∈ {s : Fin n → ℂ | s a = 1 ∧ ∀ b, ‖s b‖ ≤ 1}, nearK κ w s ε

def shearK (a : Fin n) (s : Fin n → K) (X : Fin n → Fin M → K) : Fin n → Fin M → K :=
  Function.update X a (fun i => X a i + ∑ b, s b * X b i)

def shearM (a : Fin n) (s : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  1 + Matrix.of fun b c => if c = a then s b else 0

end Box

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def IsSplitK (e : Ainf F ≃+* (NumberField.InfinitePlace F → ℝ)) (σ : E →ₐ[F] E)
    (κ : Ainf F ⊗[F] E ≃+* (NumberField.InfinitePlace F → ℂ)) : Prop :=
  IsHomeomorph κ ∧ (∀ x w, κ (sigR (Ainf F) σ x) w = (starRingEnd ℂ) (κ x w)) ∧
    ∀ a w, κ (algebraMap (Ainf F) (Ainf F ⊗[F] E) a) w = (e a w : ℂ)

end Split

end GlobalTheory.CompanionTheory.WhitFree.AvgInf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatTuple
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SW.Core
open scoped Matrix TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def InNOh {d : ℕ} (b : Module.Basis (Fin d) F E) (N : ℕ) (x : Af F ⊗[F] E) : Prop :=
  ∀ k, ∃ y ∈ Oh F, (Algebra.TensorProduct.basis (Af F) b).repr x k = (N : Af F) * y

def latN {d : ℕ} (b : Module.Basis (Fin d) F E) (n M N : ℕ) :
    AddSubgroup (Fin n → Fin M → Af F ⊗[F] E) where
  carrier := {X | ∀ a i, InNOh b N (X a i)}
  zero_mem' := fun a i k => ⟨0, fun v => zero_mem _, by simp⟩
  add_mem' := by
    intro X Y hX hY a i k
    obtain ⟨x, hx, ex⟩ := hX a i k
    obtain ⟨y, hy, ey⟩ := hY a i k
    refine ⟨x + y, fun v => add_mem (hx v) (hy v), ?_⟩
    simp only [Pi.add_apply, map_add (f := _), Finsupp.add_apply, ex, ey, mul_add]
  neg_mem' := by
    intro X hX a i k
    obtain ⟨x, hx, ex⟩ := hX a i k
    refine ⟨-x, fun v => neg_mem (hx v), ?_⟩
    simp only [Pi.neg_apply, map_neg, Finsupp.neg_apply, ex, mul_neg]

def gram2 (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y : Fin n → Fin M → Af F ⊗[F] E) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
  fun a c => hR (Af F) σ J (X a) (Y c)

def phaseB (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψf : Af F → ℂ)
    (b : HermR (Af F) σ n) (X : Fin n → Fin M → Af F ⊗[F] E) : ℂ :=
  ψf (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gramR (Af F) σ J X)))

def pairB (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψf : Af F → ℂ)
    (b : HermR (Af F) σ n) (X Y : Fin n → Fin M → Af F ⊗[F] E) : ℂ :=
  ψf (Algebra.trace (Af F) (Af F ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gram2 σ J X Y)))

def ratTuple [NumberField E] {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : ℕ) (ρ : Fin M → Fin n → 𝓞 E) :
    Fin n → Fin M → Af F ⊗[F] E :=
  fun a j => inclR (Af F) ((s : E) * (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a)) j)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterEtaCondition
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterEtaCondition
open PositivityTheory.Rg.Rsw

namespace GlobalTheory.CompanionTheory.HeckeEtaExist

theorem heckeEta : HeckeEta :=
  GlobalTheory.RawLift.exists_hecke_resEta

end GlobalTheory.CompanionTheory.HeckeEtaExist
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterEtaConditionStatement
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_character_eta_condition : HeckeEta := by
  first | exact @GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta | exact GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta | (intros; apply GlobalTheory.CompanionTheory.HeckeEtaExist.heckeEta <;> assumption)
end
end
