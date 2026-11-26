module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteGeneralizedEigenspaceCofiniteDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFacts
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
public import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedWhittakerNewform

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) (x : R ⊗[F] E) :
    sigR R' σ (Algebra.TensorProduct.map f (AlgHom.id F E) x) =
      Algebra.TensorProduct.map f (AlgHom.id F E) (sigR R σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def hermMap {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {n : ℕ} (S : HermR R σ n) : HermR R' σ n :=
  ⟨(S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).map (Algebra.TensorProduct.map f (AlgHom.id F E)), by
    intro a b
    have h : sigR R σ ((S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) b a) = (S : Matrix _ _ _) a b := S.2 a b
    simp only [Matrix.map_apply]
    rw [sigR_map, h]⟩

theorem hermMap_sub {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {n : ℕ} (S T : HermR R σ n) :
    hermMap f σ (S - T) = hermMap f σ S - hermMap f σ T := by
  apply Subtype.ext
  funext a b
  simp [hermMap]

theorem hermMap_hermOf {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) :
    hermMap f σ (HeckeCharacterZeroLocus.SiegelWeilU.hermOf R σ T hT) = HeckeCharacterZeroLocus.SiegelWeilU.hermOf R' σ T hT := by
  apply Subtype.ext
  funext a b
  simp [hermMap, HeckeCharacterZeroLocus.SiegelWeilU.hermOf, HeckeCharacterZeroLocus.SiegelWeilU.inclR]

theorem sigR_hR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → R ⊗[F] E) :
    sigR R σ (hR R σ J y x) = hR R σ J x y := by
  have h2 : ∀ z : R ⊗[F] E, sigR R σ (sigR R σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR, hσ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h3 : ∀ i j, sigR R σ (JR R J i j) = JR R J j i := by
    intro i j
    simp [sigR, JR, inclR, hJ j i]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, map_sum, map_mul, h2, h3]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hermMap_hR {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (hR R σ J x y) =
      hR R' σ J (fun i => Algebra.TensorProduct.map f (AlgHom.id F E) (x i))
        (fun i => Algebra.TensorProduct.map f (AlgHom.id F E) (y i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, map_sum, map_mul, sigR_map]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [JR, inclR]

end Alg

section Cm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_invol {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ]
  simp

def gramH {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : HermR R σ n :=
  ⟨gramR R σ J X, fun a c => sigR_hR R σ (sig_invol hCM) hJ.1 (X a) (X c)⟩

theorem hermMap_gramH {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    hermMap f σ (gramH hCM hJ R X) =
      gramH hCM hJ R' (fun a i => Algebra.TensorProduct.map f (AlgHom.id F E) (X a i)) := by
  apply Subtype.ext
  funext a c
  exact hermMap_hR f σ J (X a) (X c)

end Cm

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def boxFN {M n : ℕ} (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)) :
    Set (Fin n → Fin M → Af F ⊗[F] E) :=
  {X | ∀ v, projV v X ∈ A v}

def pureN {M n : ℕ} (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (X : Fin n → Fin M → AF F ⊗[F] E) : ℂ :=
  φ (projInf X) * (boxFN A).indicator (fun _ => (1 : ℂ)) (projFin X)

def hermInf (σ : E →ₐ[F] E) {n : ℕ} (S : HermR (AF F) σ n) : HermR (Ainf F) σ n := hermMap (fstA F) σ S

def hermFin (σ : E →ₐ[F] E) {n : ℕ} (S : HermR (AF F) σ n) : HermR (Af F) σ n := hermMap (sndA F) σ S

def hermV (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (S : HermR (Af F) σ n) : HermR (Fv F v) σ n :=
  hermMap (evalV F v) σ S

def latH {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    Set (HermR (Fv F v) σ n) :=
  {S | (∀ i, algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E)
        ((S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i i) ∈ v.adicCompletionIntegers F) ∧
    ∀ i j, i < j → ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr
      ((S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i j) k ∈ v.adicCompletionIntegers F}

def intH {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Set (HermR (Af F) σ n) :=
  {y | ∀ v, v ∉ S → hermV σ v y ∈ latH σ b v n}

def boxH {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n)) : Set (HermR (Af F) σ n) :=
  {y | (∀ v ∈ S, hermV σ v y ∈ U v) ∧ ∀ v, v ∉ S → hermV σ v y ∈ latH σ b v n}

def testH {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) {n : ℕ} (ρ : HermR (Ainf F) σ n → ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n))
    (y : HermR (AF F) σ n) : ℂ :=
  (ρ (hermInf σ y) : ℂ) * (boxH σ b n S U).indicator (fun _ => (1 : ℂ)) (hermFin σ y)

def fouH (σ : E →ₐ[F] E) {n : ℕ} (ψ : AddChar (AF F) ℂ) (db : Measure (HermR (AF F) σ n))
    (τ : HermR (AF F) σ n → ℂ) (b : HermR (AF F) σ n) : ℂ :=
  ∫ y, τ y * ψ (pairHerm (AF F) σ n y b) ∂db

def chiT (σ : E →ₐ[F] E) {n : ℕ} (ψ : AddChar (AF F) ℂ) (T : Matrix (Fin n) (Fin n) E)
    (y : HermR (AF F) σ n) : ℂ :=
  ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
    (Matrix.trace (T.map (inclR (AF F)) * (y : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))))))

def coefSN {d : ℕ} (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (ψ : AddChar (AF F) ℂ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (T : Matrix (Fin n) (Fin n) E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ℂ :=
  ∫ y, (intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y) *
    (GlobalTheory.CompanionTheory.SiegelND.starN σ J ψ dx Φ y * chiT σ ψ T y) ∂db

end Adelic

end GlobalTheory.CompanionTheory.SiegelND.Coef
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def starLoc (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (ψR : R → ℂ) (dx : Measure (Fin n → Fin M → R ⊗[F] E))
    (Φ : (Fin n → Fin M → R ⊗[F] E) → ℂ) (b : HermR R σ n) : ℂ :=
  ∫ X, Φ X * ψR (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * gramR R σ J X))) ∂dx

def psiFin (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (y : Af F) : ℂ := ψ (pairA F 0 y)

def hermInf (σ : E →ₐ[F] E) {n : ℕ} (b : HermR (AF F) σ n) : HermR (Ainf F) σ n :=
  ⟨(b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)), by
    intro i j
    have h := congrArg (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) (b.2 i j)
    simp only [Matrix.map_apply]
    rw [← h]
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
    congr 1
    ext <;> simp⟩

def hermFin (σ : E →ₐ[F] E) {n : ℕ} (b : HermR (AF F) σ n) : HermR (Af F) σ n :=
  ⟨(b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)), by
    intro i j
    have h := congrArg (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) (b.2 i j)
    simp only [Matrix.map_apply]
    rw [← h]
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
    congr 1
    ext <;> simp⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Frame

section Gen

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def trM {R : Type} {M n : ℕ} (X : Fin n → Fin M → R) : Matrix (Fin M) (Fin n) R :=
  Matrix.of fun i a => X a i

def framesE (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E) :
    Set (Fin n → Fin M → E) :=
  {X | LinearIndependent E X ∧ gramE σ J X = T}

def IsBlockM {n : ℕ} (t : ℕ) (T : Matrix (Fin n) (Fin n) E) : Prop :=
  ∃ h : t < n, (∀ i j : Fin n, (t ≤ i.1 ∨ t ≤ j.1) → T i j = 0) ∧
    (T.submatrix (Fin.castLE h.le) (Fin.castLE h.le)).det ≠ 0

def IsGramFibFree (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n))
    (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) : Prop :=
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val {X | LinearIndependent (R ⊗[F] E) X} ν Set.univ m

end Gen

section Glob

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def SWFree (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (T : Matrix (Fin n) (Fin n) E)
    (hT : ∀ a b, σ (T b a) = T a b) : Prop :=
  ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F))
    (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) →
    ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 →
    ∀ (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
      (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)),
      IsGramFibFree (Ainf F) σ J n (coordW (Ainf F) b laminf n M) (coordHerm (Ainf F) σ b laminf n) minf →
      (∀ v, IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v)) →
      IsEulerProd b (thetaMeas σ J μ 𝓕 (framesE σ J T)) 1 (minf (hermOf (Ainf F) σ T hT))
        (fun v => m v (hermOf (Fv F v) σ T hT))

end Glob

section D

open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hermE_symm {D : D7} {r : ℕ} (β : PositivityTheory.GramSchwartzFunctions.HermE D r) (a b : Fin r) :
    D.sp.cm.sig (β.1 b a) = β.1 a b := by
  have h := congrFun (congrFun β.2 a) b
  simpa [Matrix.map_apply, Matrix.transpose_apply] using h

theorem trM_mem_framesE_iff {D : D7} (V : HSp D) {r : ℕ} (X : Fin r → Fin V.rank → D.host.E)
    (T : Matrix (Fin r) (Fin r) D.host.E) :
    X ∈ framesE D.sp.cm.sig V.gram T ↔ (trM X).rank = r ∧ PositivityTheory.GramSchwartzFunctions.BC.gramQ V (trM X) = T := by
  have hg : HeckeCharacterZeroLocus.SiegelWeilU.gramE D.sp.cm.sig V.gram X = PositivityTheory.GramSchwartzFunctions.BC.gramQ V (trM X) := by
    refine Matrix.ext fun a b => ?_
    simp only [HeckeCharacterZeroLocus.SiegelWeilU.gramE, HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, PositivityTheory.GramSchwartzFunctions.BC.gramQ, trM,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [mul_assoc]; rfl
  have hr : LinearIndependent D.host.E X ↔ (trM X).rank = r := by
    have h1 : (trM X).rank = (Matrix.of X).rank := by
      have : trM X = Matrix.transpose (Matrix.of X) := rfl
      rw [this, Matrix.rank_transpose]
    rw [h1, Matrix.rank_eq_finrank_span_row]
    have := linearIndependent_iff_card_eq_finrank_span (R := D.host.E) (b := X)
    refine this.trans ?_
    rw [Fintype.card_fin, eq_comm]
    exact Iff.rfl
  simp only [framesE, Set.mem_ofPred_eq, hr, hg]

end D

end GlobalTheory.CompanionTheory.WeilSiegel.Frame
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRs
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WSum

variable {D : D7} {r : ℕ}

def rs (σ : (D.what₂.Tau → ℂ) →+ AE D) (s : ℝ) : AE D := σ fun _ => (s : ℂ)

theorem rs_add (σ : (D.what₂.Tau → ℂ) →+ AE D) (s t : ℝ) : rs σ (s + t) = rs σ s + rs σ t := by
  unfold rs
  rw [← map_add (f := _)]
  congr 1
  funext x
  simp

theorem rs_zero (σ : (D.what₂.Tau → ℂ) →+ AE D) : rs σ 0 = 0 := by
  unfold rs
  have : (fun _ : D.what₂.Tau => ((0 : ℝ) : ℂ)) = 0 := by funext; simp
  rw [this, map_zero]

theorem finPart_cA (z : AE D) :
    finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

theorem cA_rs {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (s : ℝ) :
    cA D (rs σ s) = rs σ s := by
  refine sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)
  · have h0 : finPart D (rs σ s) = 0 := hσ.fin _
    rw [RingHom.map_sub, finPart_cA, h0, map_zero, sub_zero]
  · have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
    rw [RingHom.map_sub, RingHom.map_sub, GlobalTheory.PhaseReal.infPart_cA,
      GlobalTheory.Mem.VolExists.infEmb_sigR hcm (hσ.inf τ)]
    unfold rs
    rw [hσ.comp]
    simp

theorem continuous_rs {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) :
    Continuous (rs σ) :=
  hσ.cont.comp (continuous_pi fun _ => Complex.continuous_ofReal)

def path {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (a : HermE D r) :
    ℝ →+ hermA D r where
  toFun s := ⟨rs σ s • a.1.map (incA D), by
    show adj (rs σ s • a.1.map (incA D)) = rs σ s • a.1.map (incA D)
    rw [adj_smul, cA_rs hσ]
    congr 1
    exact GlobalTheory.CompanionTheory.HermPoisson.rat_mem_hermA a⟩
  map_zero' := by
    apply Subtype.ext
    show rs σ 0 • a.1.map (incA D) = 0
    rw [rs_zero, zero_smul]
  map_add' s t := by
    apply Subtype.ext
    show rs σ (s + t) • a.1.map (incA D) = rs σ s • a.1.map (incA D) + rs σ t • a.1.map (incA D)
    rw [rs_add, add_smul]

def lam (θ : InfFam D) (α : D.host.F) (t : AE D) : ℝ :=
  -∑ τ, (θ τ (infPart D (incA D (algebraMap D.host.F D.host.E α) * t))).re

def multM (θ : InfFam D) (α : D.host.F) (V : HSp D) (a : HermE D r) (y : Mx D V.rank r) : ℝ :=
  lam θ α (Matrix.trace (HMul.hMul (a.1.map (incA D)) (inner V y y) : Mx D r r))

def pairF (θ : InfFam D) (α : D.host.F) (a β : HermE D r) : ℝ :=
  lam θ α (incA D (Matrix.trace (β.1 * a.1)))

end GlobalTheory.CompanionTheory.WSum
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_level : Ad3.R.B0 → Ad3.R.F1 := by
  first | exact @GlobalTheory.CompanionTheory.RSLift.adelic_lift_exists | exact GlobalTheory.CompanionTheory.RSLift.adelic_lift_exists | (intros; apply GlobalTheory.CompanionTheory.RSLift.adelic_lift_exists <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightContinuousPos
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.CompanionTheory.Iwasawa

theorem continuous_of_mul_compact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {P K : Set G} {f : G → ℝ}
    (hP : IsClosed P) (hK : IsCompact K) (hf : ContinuousOn f P)
    (hd : ∀ x, ∃ p ∈ P, ∃ k ∈ K, x = p * k) (hv : ∀ p ∈ P, ∀ k ∈ K, f (p * k) = f p) : Continuous f := by
  refine continuous_iff_isClosed.2 fun C hC => ?_
  have hD : IsClosed (P ∩ f ⁻¹' C) := hf.preimage_isClosed_of_isClosed hP hC
  convert hD.mul_right_of_isCompact hK using 1
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, k, hk, rfl⟩ := hd x
    exact Set.mem_mul.2 ⟨p, ⟨hp, by simpa [Set.mem_preimage, hv p hp k hk] using hx⟩, k, hk, rfl⟩
  · rintro ⟨p, ⟨hp, hc⟩, k, hk, rfl⟩
    simpa [Set.mem_preimage, hv p hp k hk] using hc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem topRing_AE : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)

theorem t2Space_cm_host_adeles : T2Space (AE F E) := by
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  exact GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)

theorem topologicalGroup_unitary_double : IsTopologicalGroup (G2 σ Y) := by
  haveI := topRing_AE (F := F) (E := E)
  infer_instance

def parT (x : G2 σ Y) : Matrix (Fin n) (Fin n) (AE F E) := (mat2 x * dC n (AE F E)).toRows₁

theorem continuous_mat2 : Continuous (mat2 : G2 σ Y → _) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_parT : Continuous (parT : G2 σ Y → _) := by
  haveI := topRing_AE (F := F) (E := E)
  have h : Continuous fun x : G2 σ Y => mat2 x * dC n (AE F E) := continuous_mat2.matrix_mul continuous_const
  exact continuous_matrix fun i j => h.matrix_elem _ _

theorem parT_eq {p : G2 σ Y} {t : GL (Fin n) (AE F E)} (h : IsPar p t) : parT p = t.1 := by
  rw [parT, isPar_iff.1 h, dC, diagCols, Matrix.fromRows_mul, Matrix.one_mul, Matrix.toRows₁_fromRows]

theorem exists_isPar_iff {x : G2 σ Y} : (∃ t, IsPar x t) ↔ mat2 x * dC n (AE F E) = dC n (AE F E) * parT x ∧
    mat2 x⁻¹ * dC n (AE F E) = dC n (AE F E) * parT x⁻¹ ∧ parT x * parT x⁻¹ = 1 ∧ parT x⁻¹ * parT x = 1 := by
  constructor
  · rintro ⟨t, h⟩
    have h' := IsPar.inv h
    rw [parT_eq h, parT_eq h']
    exact ⟨isPar_iff.1 h, isPar_iff.1 h', Units.mul_inv t, Units.inv_mul t⟩
  · rintro ⟨h1, -, h3, h4⟩
    exact ⟨⟨parT x, parT x⁻¹, h3, h4⟩, isPar_iff.2 h1⟩

theorem isClosed_siegel_stabiliser : IsClosed (par2 σ Y : Set (G2 σ Y)) := by
  haveI := topRing_AE (F := F) (E := E)
  haveI := t2Space_cm_host_adeles (F := F) (E := E)
  haveI := topologicalGroup_unitary_double (σ := σ) (Y := Y)
  have ci : Continuous fun x : G2 σ Y => parT x⁻¹ := continuous_parT.comp continuous_inv
  have cm : Continuous fun x : G2 σ Y => mat2 x⁻¹ := continuous_mat2.comp continuous_inv
  have e : (par2 σ Y : Set (G2 σ Y)) = {x | mat2 x * dC n (AE F E) = dC n (AE F E) * parT x} ∩
      ({x | mat2 x⁻¹ * dC n (AE F E) = dC n (AE F E) * parT x⁻¹} ∩
      ({x | parT x * parT x⁻¹ = 1} ∩ {x | parT x⁻¹ * parT x = 1})) := by
    ext x
    exact mem_parabolic_GL2_iff.trans exists_isPar_iff
  rw [e]
  exact (isClosed_eq (continuous_mat2.matrix_mul continuous_const) (continuous_const.matrix_mul continuous_parT)).inter
    ((isClosed_eq (cm.matrix_mul continuous_const) (continuous_const.matrix_mul ci)).inter
    ((isClosed_eq (continuous_parT.matrix_mul ci) continuous_const).inter
    (isClosed_eq (ci.matrix_mul continuous_parT) continuous_const)))

def parU (p : par2 σ Y) : GL (Fin n) (AE F E) :=
  ⟨parT p.1, parT p.1⁻¹, (exists_isPar_iff.1 (mem_parabolic_GL2_iff.1 p.2)).2.2.1, (exists_isPar_iff.1 (mem_parabolic_GL2_iff.1 p.2)).2.2.2⟩

theorem isPar_parU (p : par2 σ Y) : IsPar p.1 (parU p) := isPar_iff.2 (exists_isPar_iff.1 (mem_parabolic_GL2_iff.1 p.2)).1

theorem continuous_parU : Continuous (parU : par2 σ Y → GL (Fin n) (AE F E)) := by
  haveI := topRing_AE (F := F) (E := E)
  haveI := topologicalGroup_unitary_double (σ := σ) (Y := Y)
  exact Units.continuous_iff.2 ⟨continuous_parT.comp continuous_subtype_val,
    continuous_parT.comp (continuous_inv.comp continuous_subtype_val)⟩

theorem continuous_detGL : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) (AE F E) → (AE F E)ˣ) := by
  haveI := topRing_AE (F := F) (E := E)
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_det
  · exact Units.continuous_coe_inv.matrix_det

theorem continuous_pos {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ}
    (hK : IsCompact (K : Set (G2 σ Y))) (ha : IsHgt K a) : Continuous a ∧ ∀ x, 0 < a x := by
  haveI := topologicalGroup_unitary_double (σ := σ) (Y := Y)
  have v1 : ∀ p t, IsPar p t → a p = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) := fun p t h => by
    simpa using ha.val p t h 1 K.one_mem
  refine ⟨continuous_of_mul_compact (P := par2 σ Y) isClosed_siegel_stabiliser hK ?_ ?_ ?_, fun x => ?_⟩
  · refine continuousOn_iff_continuous_restrict.2 ?_
    exact (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp (continuous_detGL.comp continuous_parU))).congr
      fun p => (v1 _ _ (isPar_parU p)).symm
  · intro x
    obtain ⟨p, t, h, k, hk, e⟩ := ha.iwa x
    exact ⟨p, mem_parabolic_GL2_iff.2 ⟨t, h⟩, k, hk, e⟩
  · intro p hp k hk
    obtain ⟨t, h⟩ := mem_parabolic_GL2_iff.1 hp
    rw [ha.val p t h k hk, v1 p t h]
  · obtain ⟨p, t, h, k, hk, rfl⟩ := ha.iwa x
    rw [ha.val p t h k hk]
    have u : absE F E (Matrix.GeneralLinearGroup.det t) ≠ 0 := fun h0 => by
      have e := map_mul (absE F E) (Matrix.GeneralLinearGroup.det t) (Matrix.GeneralLinearGroup.det t)⁻¹
      rw [mul_inv_cancel, map_one, h0, zero_mul] at e
      exact one_ne_zero e
    exact_mod_cast pos_iff_ne_zero.2 u

theorem height_continuous_pos : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → Continuous a ∧ ∀ x, 0 < a x :=
  fun F E _ _ _ _ _ σ B n Y r s hB hn hY b K a hb hK ha =>
    continuous_pos (GlobalTheory.T.isCompact_standard_maximal F E σ B n Y r s hB hn hY b K a hb hK ha) ha

end GlobalTheory.CompanionTheory.Iwasawa
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintConstMulSum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgEqLevel
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgLevel

theorem avg_eq_level : ∀ {H : Type} [Group H] (S : Subgroup H) (u : H → ℂ), S ≤ rStab u →
    S.index ≠ 0 → avg u = ((S.index : ℂ))⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  intro H _ S u hS hfin
  have hmul := Subgroup.relIndex_mul_index hS
  have hm : S.relIndex (rStab u) ≠ 0 := fun h0 => hfin (by rw [← hmul, h0, zero_mul])
  have hmC : ((S.relIndex (rStab u) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
  rw [GlobalTheory.CompanionTheory.HintLevel.finsum_out_of_le u hS le_rfl hm, ← hmul, avg, Nat.cast_mul, mul_inv,
    mul_mul_mul_comm, inv_mul_cancel₀ hmC, one_mul]

end GlobalTheory.CompanionTheory.AvgLevel
end
end

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.DiagAvg

theorem avg_conj {G : Type} [Group G] (K K' : Subgroup G) (X : Finset G) (hXK : ∀ x ∈ X, x ∈ K)
    (hX : ∀ k ∈ K, ∃! x ∈ X, x⁻¹ * k ∈ K') (f : G → ℂ) (hl : ∀ u ∈ K', ∀ g, f (u * g) = f g ∧ f (g * u) = f g)
    (g : G) :
    avg (fun k : K => f ((k : G)⁻¹ * g * k)) = ((X.card : ℂ))⁻¹ * ∑ x ∈ X, f (x⁻¹ * g * x) := by
  set S : Subgroup K := K'.subgroupOf K with hSdef
  set u : K → ℂ := fun k => f ((k : G)⁻¹ * g * k) with hu
  have hS : S ≤ rStab u := by
    intro s hs k
    have hs' : (s : G) ∈ K' := Subgroup.mem_subgroupOf.1 hs
    show f (((k * s : K) : G)⁻¹ * g * ((k * s : K) : G)) = f ((k : G)⁻¹ * g * k)
    have e : ((k * s : K) : G)⁻¹ * g * ((k * s : K) : G) = (s : G)⁻¹ * ((k : G)⁻¹ * g * k) * s := by
      simp only [Subgroup.coe_mul]; group
    rw [e, (hl _ hs' _).2, (hl _ (K'.inv_mem hs') _).1]
  let φ : {x // x ∈ X} → K ⧸ S := fun x => ((⟨x.1, hXK _ x.2⟩ : K) : K ⧸ S)
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have h1 : (x.1)⁻¹ * y.1 ∈ K' := by
        have h2 := QuotientGroup.eq.1 hxy
        exact Subgroup.mem_subgroupOf.1 h2
      have hy := hX y.1 (hXK _ y.2)
      exact Subtype.ext (hy.unique ⟨x.2, h1⟩ ⟨y.2, by simp [K'.one_mem]⟩)
    · intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨x, ⟨hxX, hxk⟩, -⟩ := hX k.1 k.2
      exact ⟨⟨x, hxX⟩, QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hxk)⟩
  let e := Equiv.ofBijective φ hφ
  have hindex : S.index = X.card := by
    show Nat.card (K ⧸ S) = _
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  have hne : S.index ≠ 0 := by
    rw [hindex]
    obtain ⟨x, ⟨hxX, -⟩, -⟩ := hX 1 K.one_mem
    exact (Finset.card_pos.2 ⟨x, hxX⟩).ne'
  rw [GlobalTheory.CompanionTheory.AvgLevel.avg_eq_level S u hS hne, hindex]
  congr 1
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype, ← Finset.sum_coe_sort X]
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul S (⟨x.1, hXK _ x.2⟩ : K)
  show u (φ x).out = u ⟨x.1, hXK _ x.2⟩
  have hφx : (φ x).out = (⟨x.1, hXK _ x.2⟩ : K) * s := hs
  rw [hφx]
  exact hS s.2 _

theorem hint_const_mul_sum {H ι : Type} [Group H] (A L : Subgroup H) (hLA : L ≤ A) (hfin : L.relIndex A ≠ 0)
    (s : Finset ι) (v : ι → H → ℂ) (c : ℂ) (hst : ∀ i ∈ s, L ≤ rStab (v i))
    (hsupp : ∀ i ∈ s, (Function.support fun q : H ⧸ L => v i q.out).Finite) :
    hint A (fun z => c * ∑ i ∈ s, v i z) = c * ∑ i ∈ s, hint A (v i) := by
  have hL : L ≤ rStab (fun z => c * ∑ i ∈ s, v i z) := by
    intro l hl z
    show c * ∑ i ∈ s, v i (z * l) = c * ∑ i ∈ s, v i z
    congr 1
    exact Finset.sum_congr rfl fun i hi => hst i hi hl z
  rw [GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H A L _ hLA hL hfin,
    Finset.sum_congr rfl fun i hi => GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H A L (v i) hLA (hst i hi) hfin,
    ← Finset.mul_sum]
  have h1 : ∑ᶠ q : H ⧸ L, c * ∑ i ∈ s, v i q.out = c * ∑ i ∈ s, ∑ᶠ q : H ⧸ L, v i q.out := by
    simp only [Finset.mul_sum]
    rw [finsum_sum_comm s (fun (q : H ⧸ L) i => c * v i q.out) fun i hi =>
      (hsupp i hi).subset fun q hq => right_ne_zero_of_mul hq]
    exact Finset.sum_congr rfl fun i _ => (mul_finsum _ _).symm
  rw [h1]
  ring

theorem support_finite {G H : Type} [Group G] [Group H] (L : Subgroup H) (K' : Subgroup G) (θ : H → G)
    (hθ : ∀ z z', (θ z)⁻¹ * θ z' ∈ K' → z⁻¹ * z' ∈ L) (f : G → ℂ) (hr : ∀ u ∈ K', ∀ g, f (g * u) = f g)
    (hfin : {q : G ⧸ K' | f q.out ≠ 0}.Finite) :
    (Function.support fun q : H ⧸ L => f (θ q.out)).Finite := by
  refine Set.Finite.of_finite_image (f := fun q : H ⧸ L => ((θ q.out : G) : G ⧸ K')) (hfin.subset ?_) ?_
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul K' (θ q.out)
    show f ((θ q.out : G) : G ⧸ K').out ≠ 0
    rw [hs, hr _ s.2]
    exact hq
  · intro q _ q' _ hqq
    have h2 : ((q.out : H) : H ⧸ L) = q'.out := QuotientGroup.eq.2 (hθ _ _ (QuotientGroup.eq.1 hqq))
    simpa using h2

theorem finite_cosets {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K' : Subgroup G)
    (ho : IsOpen (K' : Set G)) (f : G → ℂ) (hc : HasCompactSupport f) : {q : G ⧸ K' | f q.out ≠ 0}.Finite := by
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover (fun i : G ⧸ K' => {g : G | i.out⁻¹ * g ∈ K'})
    (fun i => ho.preimage (continuous_const.mul continuous_id)) fun g _ =>
      Set.mem_iUnion.2 ⟨(g : G ⧸ K'), QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : G ⧸ K'))⟩
  refine t.finite_toSet.subset fun q hq => ?_
  obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport f hq))
  have h1 : ((i.out : G) : G ⧸ K') = q.out := QuotientGroup.eq.2 hqi
  have h2 : i = q := by simpa using h1
  exact h2 ▸ hi

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_toAdd_mul {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (Z l : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    blk h w m (Multiplicative.toAdd (Z * l)) =
      blk h w m (Multiplicative.toAdd Z) * blk h w 1 (Multiplicative.toAdd l) := by
  rw [GlobalTheory.LeviFubini.blk_mul_blk]
  simp [add_comm]

theorem ct_eq_diag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w (n := n)) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ f : GLw n w → ℂ, IsHk K' f → ∀ m, ct h w f m = ((X.card : ℂ))⁻¹ * ∑ x ∈ X, phi3 h w f x x m := by
  intro E _ _ _ n a b h w K' hopen hle hnorm X hXK hX f hf m
  have hbi : ∀ u ∈ K', ∀ g, f (u * g) = f g ∧ f (g * u) = f g := fun u hu g =>
    ⟨by simpa using hf.2.2.2 u hu 1 K'.one_mem g, by simpa using hf.2.2.2 1 K'.one_mem u hu g⟩
  have hcos := finite_cosets K' hopen f hf.2.2.1
  obtain ⟨hLA, hfin⟩ := GlobalTheory.CompanionTheory.UnipLevel.unip_level E a b n h w K' hopen hle
  set L := (K'.subgroupOf (GlobalTheory.LeviFubini.parB h w)).comap (GlobalTheory.LeviFubini.uN h w) with hLdef
  have hmem : ∀ Y, Y ∈ L ↔ blk h w 1 (Multiplicative.toAdd Y) ∈ K' := fun Y => Iff.rfl
  have hstep : (fun Z : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      avg fun k : GlobalTheory.LFun.KGL w (n := n) => f ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd Z) * k)) =
      fun Z => ((X.card : ℂ))⁻¹ * ∑ x ∈ X, f (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x) :=
    funext fun Z => avg_conj _ K' X hXK hX f hbi _
  have hst : ∀ x ∈ X, L ≤ rStab (fun Z : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      f (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x)) := by
    intro x hx l hl Z
    show f (x⁻¹ * blk h w m (Multiplicative.toAdd (Z * l)) * x) = f (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x)
    have hU : x⁻¹ * blk h w 1 (Multiplicative.toAdd l) * x ∈ K' := by
      simpa using hnorm x⁻¹ ((GlobalTheory.LFun.KGL w (n := n)).inv_mem (hXK x hx)) _ ((hmem l).1 hl)
    have e : x⁻¹ * blk h w m (Multiplicative.toAdd (Z * l)) * x =
        (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x) * (x⁻¹ * blk h w 1 (Multiplicative.toAdd l) * x) := by
      rw [blk_toAdd_mul]; group
    rw [e]
    exact (hbi _ hU _).2
  have hsupp : ∀ x ∈ X, (Function.support fun q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ L =>
      f (x⁻¹ * blk h w m (Multiplicative.toAdd q.out) * x)).Finite := by
    intro x hx
    refine support_finite L K' (fun Z => x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x) ?_ f
      (fun u hu g => (hbi u hu g).2) hcos
    intro z z' hz
    rw [hmem]
    have hb : blk h w m (Multiplicative.toAdd z') =
        blk h w m (Multiplicative.toAdd z) * blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) := by
      rw [← blk_toAdd_mul, mul_inv_cancel_left]
    have e : (x⁻¹ * blk h w m (Multiplicative.toAdd z) * x)⁻¹ * (x⁻¹ * blk h w m (Multiplicative.toAdd z') * x) =
        x⁻¹ * blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) * x := by
      rw [hb]; group
    have hz' : x⁻¹ * blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) * x ∈ K' := e ▸ hz
    have := hnorm x (hXK x hx) _ hz'
    have e2 : x * (x⁻¹ * blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) * x) * x⁻¹ =
        blk h w 1 (Multiplicative.toAdd (z⁻¹ * z')) := by group
    rwa [e2] at this
  simp only [ct, phi3]
  rw [hstep, hint_const_mul_sum (intMat a b w) L hLA hfin X
    (fun x Z => f (x⁻¹ * blk h w m (Multiplicative.toAdd Z) * x)) _ hst hsupp, ← Finset.mul_sum]
  ring

end GlobalTheory.CompanionTheory.DiagAvg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieSkewAdjointL2
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieSkewAdjointL2
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.LieSkew

theorem continuous_infGL_map (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E) :=
    ((continuous_infEq E).prodMk continuous_const :
      Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  refine Continuous.units_map _ ?_
  exact continuous_const.add (continuous_id.matrix_map hs)

theorem inner_R_R {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] (g : G) (F F' : L2 Γ μ) :
    inner ℂ (R Γ μ g F) (R Γ μ g F') = inner ℂ F F' :=
  (LinearIsometry.mk (R Γ μ g).toLinearMap (norm_R g)).inner_map_map F F'

theorem lie_skew : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : GlobalTheory.CuspRep.Lie E a) (φ ψ : Sm E a) (hφ : MemL2Quotient (latticeGL E a) μ φ.1) (hψ : MemL2Quotient (latticeGL E a) μ ψ.1) (hXφ : MemL2Quotient (latticeGL E a) μ (lie E a X φ).1) (hXψ : MemL2Quotient (latticeGL E a) μ (lie E a X ψ).1), Continuous φ.1 → Continuous ψ.1 → Continuous (lie E a X φ).1 → Continuous (lie E a X ψ).1 → inner ℂ hXφ.toL2 hψ.toL2 = - inner ℂ hφ.toL2 hXψ.toL2 := by
  intro E _ _ _ a μ _ _ X φ ψ hφ hψ hXφ hXψ cφ cψ cXφ cXψ
  obtain ⟨c, hc, h0, hadd, hd, -⟩ := GlobalTheory.T.one_parameter_subgroup_exists E a X
  have hγ : Continuous fun t => infGL E a (c t) := (continuous_infGL_map E a).comp hc
  have hγ0 : infGL E a (c 0) = 1 := by rw [h0, map_one]
  have hγa : ∀ s t, infGL E a (c (s + t)) = infGL E a (c s) * infGL E a (c t) := fun s t => by
    rw [hadd, map_mul]
  have d1 := GlobalTheory.T.hasDerivAt_right_translate_toL2 (GA E a) (latticeGL E a) μ φ.1 (lie E a X φ).1 hφ hXφ
    (fun t => infGL E a (c t)) cφ cXφ hγ hγ0 hγa (fun g => hasDerivAt_curve φ g c X h0 hd) 0
  have d2 := GlobalTheory.T.hasDerivAt_right_translate_toL2 (GA E a) (latticeGL E a) μ ψ.1 (lie E a X ψ).1 hψ hXψ
    (fun t => infGL E a (c t)) cψ cXψ hγ hγ0 hγa (fun g => hasDerivAt_curve ψ g c X h0 hd) 0
  have d3 := d1.inner ℂ d2
  have hconst : (fun t : ℝ => inner ℂ (R (latticeGL E a) μ (infGL E a (c t)) hφ.toL2)
      (R (latticeGL E a) μ (infGL E a (c t)) hψ.toL2)) = fun _ => inner ℂ hφ.toL2 hψ.toL2 :=
    funext fun t => inner_R_R _ μ _ _ _
  rw [hconst] at d3
  have h := d3.unique (hasDerivAt_const (0 : ℝ) _)
  simp only [hγ0, map_one, ContinuousLinearMap.one_apply] at h
  exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans h)

end GlobalTheory.CompanionTheory.LieSkew
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieSkewAdjointL2Statement
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_skew_adjoint_l2 : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : GlobalTheory.CuspRep.Lie E a) (φ ψ : Sm E a) (hφ : MemL2Quotient (latticeGL E a) μ φ.1) (hψ : MemL2Quotient (latticeGL E a) μ ψ.1) (hXφ : MemL2Quotient (latticeGL E a) μ (lie E a X φ).1) (hXψ : MemL2Quotient (latticeGL E a) μ (lie E a X ψ).1), Continuous φ.1 → Continuous ψ.1 → Continuous (lie E a X φ).1 → Continuous (lie E a X ψ).1 → inner ℂ hXφ.toL2 hψ.toL2 = - inner ℂ hφ.toL2 hXψ.toL2 := by
  first | exact @GlobalTheory.CompanionTheory.LieSkew.lie_skew | exact GlobalTheory.CompanionTheory.LieSkew.lie_skew | (intros; apply GlobalTheory.CompanionTheory.LieSkew.lie_skew <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIsoFrameFirstCols
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise

noncomputable section
namespace GlobalTheory.CompanionTheory.RegInt

variable {D : D7} {V : HSp D} {r : ℕ}

def firstCols (X : Matrix (Fin V.rank) (Fin r) D.host.E) (j : Fin r) :
    Matrix (Fin V.rank) (Fin (j.val + 1)) D.host.E := X.submatrix id (Fin.castLE j.2)

def root (t : Fin r → ℝ) (j : Fin r) : ℝ := if h : j.val + 1 < r then t j / t ⟨j.val + 1, h⟩ else t j

theorem isIsoFrame_firstCols {X Y : Matrix (Fin V.rank) (Fin r) D.host.E}
    (hW : GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y) (j : Fin r) : IsIsoFrame V (firstCols X j) := by
  refine ⟨Nat.succ_pos _, ?_, ?_⟩
  · have h1 : LinearIndependent D.host.E (fun i : Fin r => fun a : Fin V.rank => X a i) := by
      refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
      have h3 : ∀ a, ∑ l, g l * X a l = 0 := fun a => by
        have := congrFun hg a
        simpa [Finset.sum_apply, mul_comm] using this
      have h4 : (fun l => (D.sp.cm.sig : D.host.E →+* D.host.E) (g l)) ᵥ*
          Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X = 0 := by
        funext a
        have := congrArg (D.sp.cm.sig : D.host.E →+* D.host.E) (h3 a)
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul, map_zero] at this
        simpa [Matrix.vecMul, dotProduct, Formalism.UG.cT] using this
      have h5 := congrArg (fun v => v ᵥ* (V.gram * Y)) h4
      simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul, ← Matrix.mul_assoc, hW.xy, Matrix.vecMul_one] at h5
      have h6 := congrFun h5 i
      simpa using h6
    have h2 : (firstCols X j).transpose = (fun i : Fin r => fun a : Fin V.rank => X a i) ∘ Fin.castLE j.2 := by
      funext i a; rfl
    change LinearIndependent D.host.E (firstCols X j).transpose
    rw [h2]
    exact h1.comp _ (Fin.castLE_injective _)
  · have h := hW.xx
    refine Matrix.ext fun a b => ?_
    have := congrFun (congrFun h (Fin.castLE j.2 a)) (Fin.castLE j.2 b)
    simpa [Matrix.mul_apply, Formalism.UG.cT, firstCols] using this

end GlobalTheory.CompanionTheory.RegInt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteVectorMeasureIsAddHaar
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteVectorMeasureIsAddHaar
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.CutOff

variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ)

noncomputable def rowInfEquiv : (Fin k → InfiniteAdeleRing E) ≃+ (Fin k → Cinf E) :=
  AddEquiv.piCongrRight fun _ => (infEq E).symm.toAddEquiv

theorem nuInf_isAddHaarMeasure : (nuInf E k).IsAddHaarMeasure := by
  have hc : Continuous (rowInfEquiv E k) :=
    continuous_pi fun i => (GASplit.continuous_infEq_symm E).comp (continuous_apply i)
  have hc' : Continuous (rowInfEquiv E k).symm :=
    continuous_pi fun i => (continuous_infEq E).comp (continuous_apply i)
  have hp : (Measure.pi fun _ : Fin k => GroundTheory.Global.infiniteAdeleMeasure E).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  exact AddEquiv.isAddHaarMeasure_map _ (rowInfEquiv E k) hc hc'

end GlobalTheory.CompanionTheory.CutOff
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfiniteVectorMeasureIsAddHaarStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinite_vector_measure_isAddHaar : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (k : ℕ), (nuInf E k).IsAddHaarMeasure := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.nuInf_isAddHaarMeasure | exact GlobalTheory.CompanionTheory.CutOff.nuInf_isAddHaarMeasure | (intros; apply GlobalTheory.CompanionTheory.CutOff.nuInf_isAddHaarMeasure <;> assumption)
end
end
