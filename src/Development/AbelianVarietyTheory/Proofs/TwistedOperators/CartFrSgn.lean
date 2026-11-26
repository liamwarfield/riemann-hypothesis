module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BcParamEqOfSatUEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridHeckeCharactersExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqValueEqOneAtInertPlaceOfRestrictsToQuadratic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairLift

def NoLow (X : ProvA) (p q : ℕ) {r s : ℕ} (lam' : Ix r s → ℚ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ p → i ≤ q → ∀ (MM : GKMod (p - i) (q - i))
    (f : Pol (p - i) (q - i) r s →ₗ[ℂ] TensorProduct ℂ MM.V (X.ds r s lam').HK.V),
    Formalism.BasicNotions.TH.IsIntw (X.fock (p - i) (q - i) r s) MM (X.ds r s lam').HK f → f = 0

structure Rule (X : ProvA) {p q r s : ℕ} (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ) : Prop where
  pos : 1 ≤ p + q
  pos' : 1 ≤ r + s
  par : IsParam lam
  par' : IsParam lam'
  down : Formalism.MainNotions.SchurIrreducible.ARiiiDown X lam lam'
  line : Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam lam'
  low : NoLow X p q lam'

def RulePar (X : ProvA) (S S' : SPar) (aS aT : ℚ) : Prop :=
  ∃ (p q r s : ℕ) (l₁ l₂ l₁' l₂' : List ℚ), l₁.length = p ∧ l₂.length = q ∧ l₁'.length = r ∧ l₂'.length = s ∧
    Rule X (ofBlocks l₁ l₂ : Ix p q → ℚ) (ofBlocks l₁' l₂' : Ix r s → ℚ) ∧
    S = dualPar (signed l₁ l₂ aT) ∧ S' = dualPar (signed l₁' l₂' aS)

def ThetaPar (t : ℕ) (P P' : SPar) (c c' : ℚ) : Prop :=
  ∃ al be ga de : List ℚ, P = signed (al ++ be) (ga ++ de) c ∧
    ((Formalism.MainNotions.SchurIrreducible.DataAR t al be ga de ∧ P' = signed (al ++ block t ++ de) (ga ++ be) c') ∨
      (Formalism.MainNotions.SchurIrreducible.DataARm t al be ga de ∧ P' = signed (al ++ de) (ga ++ block t ++ be) c'))

def PairPar (S S' : SPar) (aS aT : ℚ) : Prop :=
  ∃ (t : ℕ) (P P' : SPar), S = dualPar P ∧ S' = dualPar P' ∧
    ((ThetaPar t P P' aT aS ∧ GlobalTheory.SignedHC.FarFrom aT (((t : ℚ) + 3) / 2) P) ∨ ThetaPar t P' P aS aT)

def partner (t : ℕ) (b : Bool) (c c' : ℚ) (P : SPar) : SPar :=
  (P.image fun x => (x.1 - c + c', if x.1 < c then !x.2 else x.2)) ∪ (TPar.block c' t).image fun x => (x, b)

def GapOver (P : SPar) (h : ℚ) : Prop := ∀ x ∈ P, ∀ y ∈ P, x.2 ≠ y.2 → h < |x.1 - y.1|

def att (c : ℚ) (n : ℕ) : ℚ := if Odd n then c - 1 / 2 else c

variable {D : D7}

structure Inputs (D : D7) (X : ProvA) : Prop where
  chosen : GlobalTheory.Chain.RealIt.ChosenSeries X
  hc : GlobalTheory.Published.HarishChandraModules
  decay : GlobalTheory.Published.CuspRapidDecay
  bridge : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D
  vacChar : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D
  lie : LieFockAll D
  cpt : CompactFockAll D
  dense : FockDense D
  laws : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.LiftProps D
  const : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTerm D
  ext : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.GKExtension D

def IsWeilExp (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (aS aT : D.what₂.Tau → ℚ) (ω : WRep V W) : Prop :=
  ∃ χS χT : (AE D)ˣ →* Circle, IsWeilDatumO ψ V W χS χT ω ∧ ∀ τ, HasInfExp D χS τ (aS τ) ∧ HasInfExp D χT τ (aT τ)

def LowFock (D : D7) (X : ProvA) : Prop :=
  ∀ (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ), (∀ τ, RulePar X (S τ) (S' τ) (aS τ) (aT τ)) →
    ∀ (i : ℕ) (V' W : HSp D) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ →
    1 ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.SigLowered S i V' → ∀ ω' : WRep V' W, IsWeilExp ψ V' W aS aT ω' →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ F ∈ MultT θ M' ∅ 1, ∀ (v : SmT M') (A : Fr V') (f₀ : WO V' W → ℂ), IsVacF ψ θ A (Fr.ofModel M') f₀ → ∀ P,
      Lift.liftInt ν 𝓕 (thetaKO ω') (ptF ψ θ A (Fr.ofModel M') f₀ P) (F v) = 0

def LowAll (D : D7) (X : ProvA) : Prop :=
  ∀ (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ), (∀ τ, RulePar X (S τ) (S' τ) (aS τ) (aT τ)) →
    ∀ (i : ℕ) (V' W : HSp D) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ →
    1 ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.SigLowered S i V' → ∀ ω' : WRep V' W, IsWeilExp ψ V' W aS aT ω' →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ F ∈ MultT θ M' ∅ 1, ∀ (v : SmT M') (f' : WO V' W → ℂ), IsThetaFunO ψ V' W f' →
      Lift.liftInt ν 𝓕 (thetaKO ω') f' (F v) = 0

def CuspAll (D : D7) (X : ProvA) : Prop :=
  ∀ (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ), (∀ τ, RulePar X (S τ) (S' τ) (aS τ) (aT τ)) →
    ∀ (V W : HSp D) (_M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ →
    ∀ ω : WRep V W, IsWeilExp ψ V W aS aT ω →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ F ∈ MultT θ M' ∅ 1, ∀ (v : SmT M') (f : WO V W → ℂ), IsThetaFunO ψ V W f →
      IsCuspFun V (Lift.liftInt ν 𝓕 (thetaKO ω) f (F v))

def LiftsM (θ : InfFam D) {A B : HSp D} {SA SB : D.what₂.Tau → SPar} (MA : DSModel A SA) (MB : DSModel B SB) {P : Type}
    (ν : Measure (GA D A)) (𝓕 : Set (GA D A)) (K : P → GA D B → GA D A → ℂ) (It : P → SmT MA → SmT MB) : Prop :=
  ∀ F ∈ MultT θ MA ∅ 1, ∃ F' ∈ MultT θ MB ∅ 1, ∀ (p : P) (v : SmT MA) (h : GA D B),
    IntegrableOn (fun g => K p h g * F v g) 𝓕 ν ∧ ∫ g in 𝓕, K p h g * F v g ∂ν = F' (It p v) h

def PairLifts (D : D7) (X : ProvA) : Prop :=
  ∀ (S S' : D.what₂.Tau → SPar) (aS aT : D.what₂.Tau → ℚ), (∀ τ, RulePar X (S τ) (S' τ) (aS τ) (aT τ)) →
    ∀ (V W : HSp D) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ →
    ∀ ω : WRep V W, IsWeilExp ψ V W aS aT ω →
    ∀ (f₀ : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsVacVec ψ θ M M' f₀ →
      IsItW θ M M' ω (ptOf ψ θ M M' f₀) It →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ f, IsVacF ψ θ (Fr.ofModel M) (Fr.ofModel M') f →
      LiftsM θ M' M ν 𝓕 (fun P g h => thetaKO ω g h (ptOf ψ θ M M' f P)) fun P v => It P v

structure IsIntwF {V W : HSp D} {S S' : D.what₂.Tau → SPar} {Z P : Type} (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (ω : GA D V × GA D W →* Module.End ℂ (Z → ℂ)) (pt : P → (Z → ℂ))
    (It : P → SmT M' →ₗ[ℂ] SmT M) : Prop where
  ne : ∃ φ, It φ ≠ 0
  bdd : ∀ φ w, ∃ c : ℝ, ∀ v : M'.Vec,
    ‖ellT M w (inclT M (It φ (PiTensorProduct.tprod ℂ v)))‖ ≤ c * ∏ τ, ‖(v τ : M'.H τ)‖
  eqK : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ φ', pt φ' = ω (atTau θ V τ g, 1) (pt φ) →
    ∀ v, inclT M (It φ' v) = actT M τ g (inclT M (It φ v))
  eqg : ∀ τ, ∀ Y ∈ lieAt V τ, ∀ φ φ', (∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ Y t, 1) (pt φ) z) (pt φ' z) 0) →
    ∀ v, DerT M τ Y (It φ v) (It φ' v)
  invK : ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ φ' v v', pt φ' = ω (1, atTau θ W τ h) (pt φ) →
    inclT M' v' = actT M' τ h (inclT M' v) → It φ' v' = It φ v
  invg : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ φ' v v', (∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (pt φ) z) (pt φ' z) 0) →
    DerT M' τ Y v v' → It φ' v + It φ v' = 0

structure ModelTr (σ : ℂ →+* ℂ) (ε : Bool) (θ : InfFam D) {V : HSp D} {S S₁ : D.what₂.Tau → SPar}
    (M₁ : DSModel (sgn ε V) S₁) (M : DSModel V S) (κ : SmT M₁ ≃+ SmT M) : Prop where
  smul : ∀ (c : ℂ) x, κ (c • x) = σ c • κ x
  cart : ∀ τ, cart M₁ τ = sgnM ε (cart M τ)
  act : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ x y,
    inclT M₁ y = actT M₁ τ g (inclT M₁ x) ↔ inclT M (κ y) = actT M τ g (inclT M (κ x))
  der : ∀ τ, ∀ Y ∈ lieAt V τ, ∀ x y, DerT M₁ τ Y x y ↔ DerT M τ Y (κ x) (κ y)
  ell : ∀ w₁, ∃ w, ∀ x, ellT M₁ w₁ (inclT M₁ x) = σ (ellT M w (inclT M (κ x)))
  vec : ∀ v₁ : M₁.Vec, ∃ v : M.Vec, κ (PiTensorProduct.tprod ℂ v₁) = PiTensorProduct.tprod ℂ v ∧
    ∀ τ, ‖(v τ : M.H τ)‖ = ‖(v₁ τ : M₁.H τ)‖
  mult : ∀ F ∈ MultT θ M ∅ 1, ∃ F₁ ∈ MultT θ M₁ ∅ 1, ∀ x g, F₁ x g = σ (F (κ x) (ofSgn ε V g))
  mult' : ∀ F₁ ∈ MultT θ M₁ ∅ 1, ∃ F ∈ MultT θ M ∅ 1, ∀ x g, F₁ x g = σ (F (κ x) (ofSgn ε V g))

structure SgnLaw (θ : InfFam D) (ε : Bool) (V : HSp D) : Prop where
  rat : ∀ g, g ∈ GQ (sgn ε V) ↔ ofSgn ε V g ∈ GQ V
  fin : ∀ g, g ∈ GfC (sgn ε V) ↔ ofSgn ε V g ∈ GfC V
  inf : ∀ g, g ∈ GinfC (sgn ε V) ↔ ofSgn ε V g ∈ GinfC V
  grp : ∀ τ, Formalism.QuantumDeterminants.UH (gramAt D (sgn ε V) τ) = Formalism.QuantumDeterminants.UH (gramAt D V τ)
  lie : ∀ τ, lieAt (sgn ε V) τ = lieAt V τ
  atTau : ∀ τ g, ofSgn ε V (atTau θ (sgn ε V) τ g) = atTau θ V τ g
  meas : ∀ (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 ν →
    ∃ ν₁ : Measure (GA D (sgn ε V)), ν₁.IsHaarMeasure ∧ IsFundamentalDomain (GQ (sgn ε V)) (ofSgn ε V ⁻¹' 𝓕) ν₁ ∧
      ∀ φ : GA D V → ℂ, (IntegrableOn (fun g => φ (ofSgn ε V g)) (ofSgn ε V ⁻¹' 𝓕) ν₁ ↔ IntegrableOn φ 𝓕 ν) ∧
        ∫ g in ofSgn ε V ⁻¹' 𝓕, φ (ofSgn ε V g) ∂ν₁ = ∫ g in 𝓕, φ g ∂ν

def adjO (S T : HSp D) (y : WO T S) : WO S T :=
  HMul.hMul (HMul.hMul (T.gram⁻¹.map (incA D)) ((y : Matrix (Fin S.rank) (Fin T.rank) (AE D)).map (cA D)).transpose)
    (S.gram.map (incA D))

def dag (S T : HSp D) (f : WO S T → ℂ) : WO T S → ℂ := fun y => starRingEnd ℂ (f (adjO S T y))

structure AdjLaw (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Prop where
  invol : ∀ x : WO S T, adjO S T (adjO T S x) = x
  add : ∀ y y' : WO T S, adjO S T (y + y') = adjO S T y + adjO S T y'
  cont : Continuous (adjO S T)
  sympl : ∀ y y' : WO T S, symplO S T (adjO S T y) (adjO S T y') = -symplO T S y y'
  act : ∀ (g : GA D S) (h : GA D T) (y : WO T S), adjO S T (actO T S h g y) = actO S T g h (adjO S T y)
  rat : ∀ y : WO T S, adjO S T y ∈ ratL T S ↔ y ∈ ratL S T
  half : ∀ (e : AE D) (y : WO T S), IsHalf e y → IsHalf (cA D e) (adjO S T y)
  Heisenberg₂ : ∀ (y : WO T S) (f : WO S T → ℂ), heisO ψ T S y (dag S T f) = dag S T (heisO ψ S T (adjO S T y) f)
  theta : ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ T S (dag S T f)

def frSgn (ε : Bool) {V : HSp D} (A : Fr V) : Fr (sgn ε V) where
  ε τ a := xor ε (A.ε τ a)
  fr := A.fr
  fr_unit := A.fr_unit
  fr_gram τ := by
    cases ε
    · simp only [Bool.false_xor]
      exact A.fr_gram τ
    · have e : gramAt D (neg V) τ = -gramAt D V τ := by ext i j; simp [gramAt, neg_gram]
      have h : Formalism.REAL.Jm (fun a => xor true (A.ε τ a)) = -Formalism.REAL.Jm (A.ε τ) := by
        ext a b
        by_cases hab : a = b
        · subst hab; cases h : A.ε τ a <;> simp [Formalism.REAL.Jm, h]
        · simp [Formalism.REAL.Jm, hab]
      show _ = gramAt D (neg V) τ
      rw [e, h, ← A.fr_gram τ, Matrix.mul_neg, Matrix.neg_mul]

theorem cart_frSgn (ε : Bool) {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) : (frSgn ε A).cart τ = sgnM ε (A.cart τ) := by

  have hJ : Formalism.REAL.Jm (fun a => xor ε (A.ε τ a)) = sgnM ε (Formalism.REAL.Jm (A.ε τ)) := by
    cases ε
    · simp [sgnM]
    · simp only [sgnM, cond_true, Formalism.REAL.Jm, Bool.true_xor]
      rw [Matrix.diagonal_neg]
      congr 1
      funext a
      cases A.ε τ a <;> simp
  show (A.fr τ)⁻¹ * Formalism.REAL.Jm (fun a => xor ε (A.ε τ a)) * A.fr τ = sgnM ε ((A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * A.fr τ)
  rw [hJ]
  cases ε
  · rfl
  · simp only [sgnM, cond_true, Matrix.mul_neg, Matrix.neg_mul]

end GlobalTheory.PairLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitarySphericalReps
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.LFun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IsPosReal (z : ℂ) : Prop := z.im = 0 ∧ 0 < z.re

variable {D : D7}




end GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps

end
end

noncomputable section

namespace GlobalTheory.LPositivity

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.UnitarySphericalReps
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)

section Analysis

theorem isPosReal_iff {z : ℂ} : IsPosReal z ↔ ∃ r : ℝ, 0 < r ∧ z = r :=
  ⟨fun h => ⟨z.re, h.2, Complex.ext rfl (by simpa using h.1)⟩, by rintro ⟨r, hr, rfl⟩; exact ⟨rfl, hr⟩⟩

theorem isPosReal_prod {ι : Type} (s : Finset ι) {f : ι → ℂ} (h : ∀ i ∈ s, IsPosReal (f i)) :
    IsPosReal (∏ i ∈ s, f i) := by
  refine Finset.prod_induction f IsPosReal (fun a b ha hb => ?_) ⟨rfl, one_pos⟩ h
  obtain ⟨x, hx, rfl⟩ := isPosReal_iff.1 ha
  obtain ⟨y, hy, rfl⟩ := isPosReal_iff.1 hb
  exact isPosReal_iff.2 ⟨x * y, mul_pos hx hy, by simp⟩

theorem isPosReal_of_hasProd {ι : Type} {f : ι → ℂ} {a : ℂ} (ha : HasProd f a) (h0 : a ≠ 0)
    (h : ∀ i, IsPosReal (f i)) : IsPosReal a := by
  have hc : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le continuous_const Complex.continuous_re)
  have := hc.mem_of_tendsto ha (Eventually.of_forall fun s =>
    ⟨(isPosReal_prod s fun i _ => h i).1, (isPosReal_prod s fun i _ => h i).2.le⟩)
  exact ⟨this.1, this.2.lt_of_ne fun e => h0 (Complex.ext e.symm this.1)⟩

theorem isPosReal_eulerFac {B : Multiset ℂˣ} {x : ℂ} (hB : B.map star = B) (hx : star x = x)
    (h : ∀ b ∈ B, ‖(b : ℂ) * x‖ < 1) : IsPosReal (eulerFac B x) := by
  have hre : ∀ b ∈ B, 0 < (1 - (b : ℂ) * x).re := fun b hb => by
    have := (Complex.re_le_norm _).trans_lt (h b hb)
    rw [Complex.sub_re, Complex.one_re]
    linarith
  set u : ℂ := (B.map fun b : ℂˣ => Complex.log (1 - (b : ℂ) * x)).sum with hu
  have h1 : eulerPoly B x = Complex.exp u := by
    rw [hu, Complex.exp_multiset_sum, Multiset.map_map, eulerPoly]
    refine congrArg _ (Multiset.map_congr rfl fun b hb => (Complex.exp_log fun e => ?_).symm)
    simpa [e] using hre b hb
  have h2 : starRingEnd ℂ u = u := by
    conv_rhs => rw [hu, ← hB, Multiset.map_map]
    rw [hu, map_multiset_sum, Multiset.map_map]
    refine congrArg _ (Multiset.map_congr rfl fun b hb => ?_)
    have h3 : (1 - (b : ℂ) * x).arg ≠ Real.pi := fun e => by
      have := (Complex.arg_eq_pi_iff.1 e).1
      linarith [hre b hb]
    simp only [Function.comp_apply, Units.coe_star]
    rw [← Complex.log_conj _ h3, map_sub, map_one, map_mul, show starRingEnd ℂ x = x from hx]
    rfl
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2
  exact isPosReal_iff.2 ⟨(Real.exp r)⁻¹, by positivity, by rw [eulerFac, h1, hr]; simp⟩

variable {K : Type} [Field K] [NumberField K]

theorem star_npow (w : HeightOneSpectrum (𝓞 K)) (s : ℝ) : star (npow w (-(s : ℂ))) = npow w (-(s : ℂ)) := by
  rw [npow, ← Complex.ofReal_neg, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg _)]
  exact Complex.conj_ofReal _

theorem norm_lt_one_of_bounded {T : Set (HeightOneSpectrum (𝓞 K))} {c : Fam K} {r : ℕ} {κ : ℝ} (h : Bounded T c r κ)
    {s : ℂ} (hs : κ < s.re) {w : HeightOneSpectrum (𝓞 K)} (hw : w ∉ T) :
    ∀ b ∈ c w, ‖(b : ℂ) * npow w (-s)‖ < 1 := fun _ hb =>
  (h.norm_le le_rfl hw hb).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_absNorm w) (by linarith))

end Analysis

section Normalising

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end Normalising

section Transport

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

end Transport

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {h : w.under (𝓞 F) = v}
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GLoc σ J v) V} {B : Multiset ℂˣ}
  (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : Submodule.IsFullLattice E L) (hd : IsSelfDualAt σ J L v)

include hc hJ hL hd

theorem exists_inert_chart (h : w.under (𝓞 F) = v) (hv : IsInertAt F E v w) :
    ∃ c ϖ e, IsUnramInv ϖ c (qV F v) ∧ IsInertChart σ J L h c e ∧ Continuous e ∧ Continuous e.symm := by
  obtain ⟨-, ⟨c, hcj, -⟩, -, -, H⟩ := (exists_isInertChart σ hc v).2 w h hv
  obtain ⟨⟨ϖ, hU⟩, H⟩ := H c hcj
  obtain ⟨e, he⟩ := H n J L hJ hL.fg hL.span_eq_top hd
  exact ⟨c, ϖ, e, hU, he⟩


end Local

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem split_or_inert (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) ∨ IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w := by
  haveI := D.host.isCMField_hostE
  haveI := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  set v := w.under (𝓞 D.host.F) with hv
  rcases (GlobalTheory.quadratic_unramified_iff_inert_or_split D.host.F D.host.E (isCMExt_host D).2.2.1 v).1
    (fun u _ => Algebra.unramified_iff_forall.1 inferInstance ⟨u.asIdeal, u.isPrime⟩) with h | h
  · exact Or.inr ((h.isMaximal (Ideal.map_ne_bot_of_ne_bot v.ne_bot)).eq_of_le w.isPrime.ne_top Ideal.map_comap_le)
  · obtain ⟨P, Q, hne, e⟩ := Set.ncard_eq_two.1 h
    have hP : P ∈ v.asIdeal.primesOver (𝓞 D.host.E) := by simp [e]
    have hQ : Q ∈ v.asIdeal.primesOver (𝓞 D.host.E) := by simp [e]
    have := hP.2
    have := hQ.2
    exact Or.inl ⟨⟨P, hP.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩,
      ⟨Q, hQ.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, fun e => hne (congrArg (·.asIdeal) e),
      hP.2.over.symm, hQ.2.over.symm⟩

variable {D : D7} {V : HSp D}

theorem star_eq_inv {z : ℂˣ} (h : ‖(z : ℂ)‖ = 1) : star z = z⁻¹ :=
  Units.ext (by simpa using (Complex.inv_eq_conj h).symm)

end Global

end GlobalTheory.LPositivity

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinZeta.LevelOff

open Filter

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ind_tmul_mul (Sb : Finset (HeightOneSpectrum (𝓞 F))) (z : Af F ⊗[F] E) :
    (GlobalTheory.AdeleIdem.ind Sb ⊗ₜ[F] (1 : E)) * z =
      ∑ v ∈ Sb, (GlobalTheory.AdelicU.singleFin v).rTensor E
        (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z) := by
  classical
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      LinearMap.rTensor_tmul]
    rw [← TensorProduct.sum_tmul]
    congr 1
    refine GlobalTheory.AdelicU.af_ext fun u => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_sum]
    by_cases hu : u ∈ Sb
    · rw [Finset.sum_eq_single u (fun v _ hv => GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hv) _)
        (fun h => absurd hu h), GlobalTheory.AdelicU.evalV_singleFin_self]
      show (if u ∈ Sb then (1 : Fv F u) else 0) * _ = _
      rw [if_pos hu, one_mul]
    · rw [Finset.sum_eq_zero (fun v hv => GlobalTheory.AdelicU.evalV_singleFin_ne (fun e : u = v => hu (e ▸ hv)) _)]
      show (if u ∈ Sb then (1 : Fv F u) else 0) * _ = _
      rw [if_neg hu, zero_mul]
  | add x y hx hy => rw [mul_add, hx, hy, ← Finset.sum_add_distrib]; simp only [map_add (f := _)]

theorem ind_tmul_mul_eq_zero (Sb : Finset (HeightOneSpectrum (𝓞 F))) (z : Af F ⊗[F] E)
    (h : ∀ v ∈ Sb, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z = 0) :
    (GlobalTheory.AdeleIdem.ind Sb ⊗ₜ[F] (1 : E)) * z = 0 := by
  rw [ind_tmul_mul]
  exact Finset.sum_eq_zero fun v hv => by rw [h v hv, map_zero]

theorem one_sub_ind_tmul_mul (Sb : Finset (HeightOneSpectrum (𝓞 F))) (z : Af F ⊗[F] E)
    (h : ∀ v ∈ Sb, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z = 0) :
    ((1 - GlobalTheory.AdeleIdem.ind Sb) ⊗ₜ[F] (1 : E)) * z = z := by
  rw [TensorProduct.sub_tmul, sub_mul, ← Algebra.TensorProduct.one_def, one_mul, ind_tmul_mul_eq_zero Sb z h, sub_zero]

open Filter GlobalTheory.AdelicU

variable {D : D7}

theorem mem_KsphC_iff (V : HSp D) (g : GA D V) : g ∈ KsphC V ∅ ↔ g ∈ GfC V ∧ ∀ v, projV V v g ∈ Kv V v := by
  have e : g ∈ KsphC V ∅ ↔ g ∈ ((levelOff D.sp.cm.sig V.gram (frameLat V) ∅ : Subgroup _) : Set (GA D V)) := by
    rw [KsphC_eq]
  rw [e, SetLike.mem_coe, mem_levelOff, GfC_eq]
  simp

theorem eq_L0sub {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hB : IsBaseFrame V β Λ 1) : Λ = GlobalTheory.LevSplit.L0sub V := by
  obtain ⟨-, -, -, h01, h10⟩ := hB
  ext x
  constructor
  · intro hx
    show x ∈ L0c D V
    simpa using h10 x hx
  · intro hx
    simpa using h01 x hx

theorem finE_mem_St_iff {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hB : IsBaseFrame V β Λ 1) {g : GA D V} (hg : g ∈ GfC V) : Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β ↔ g ∈ KsphC V ∅ := by
  have hfr : Formalism.L2.DIV.IsFrame β (GlobalTheory.LevSplit.L0sub V) := eq_L0sub hB ▸ hB.1
  have e1 := GlobalTheory.LevSplit.mem_St_iff β _ hfr (Formalism.IndefR.Lev.finE V g)
  have e2 := GlobalTheory.LevSplit.ksph_iff V g
  exact e1.trans ⟨fun h => e2.2 ⟨hg, h⟩, fun h => (e2.1 h).2⟩

theorem finE_mem_St_of_mem_levG {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {Lv : LevDat D.host.E ℂ V.rank}
    {g : GA D V} (hg : g ∈ levG V β Lv) : Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β :=
  Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hg.2)

open Filter GlobalTheory.AdelicU

variable {D : D7}

theorem evalV_finPart (v : HeightOneSpectrum (𝓞 D.host.F)) (w : AE D) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E) (Formalism.L2.Theta.finPart D w) =
      compFin D.host.F D.host.E v w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, _root_.map_zero, RingHom.map_zero]
  | tmul a e => rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), _root_.map_add (f := _), RingHom.map_add (f := _), hx, hy]

theorem redFn_eq_one_of_proj {V : HSp D} (β : GL (Fin V.rank) (EAf D)) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    {h : GA D V} (hS : Formalism.IndefR.Lev.finE V h ∈ Formalism.L2.DIV.St β) (h1 : ∀ v ∈ Sb, projV V v h = 1)
    {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ Sb) :
    Formalism.L2.DIV.redFn β PP (Formalism.IndefR.Lev.finE V h) = 1 := by
  classical
  set b : FiniteAdeleRing (𝓞 D.host.F) D.host.F := 1 - GlobalTheory.AdeleIdem.ind Sb with hbdef
  have hb : b ∈ Formalism.UG.intAd D.host.F := sub_mem (one_mem _) (GlobalTheory.AdeleIdem.ind_mem Sb)
  refine GlobalTheory.LevSplit.redFn_eq_one β PP _ hS ⟨_, GlobalTheory.AdeleIdem.one_tmul_mem hb⟩ ?_ ?_
  · refine GlobalTheory.AdeleIdem.resS_eq_zero PP ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) rfl hb ?_
    simp [hbdef, GlobalTheory.AdeleIdem.ind_apply, hPP]
  · ext i j
    set w : AE D := (Formalism.L2.Theta.mt V h - 1) i j with hw
    have e0 : ((Formalism.L2.Theta.mt V h) - 1).map (GlobalTheory.LevSplit.finSw D) = (Formalism.L2.Theta.mt V h).map (GlobalTheory.LevSplit.finSw D) - 1 := by
      rw [Matrix.map_sub _ (RingHom.map_sub _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
    have ex : ((Formalism.IndefR.Lev.finE V h).1 - 1) i j = Formalism.IndefR.Lev.swapAE D (Formalism.L2.Theta.finPart D w) := by
      rw [GlobalTheory.LevSplit.finE_val, ← e0]
      rfl
    have hz : ∀ v ∈ Sb, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)
        (Formalism.L2.Theta.finPart D w) = 0 := by
      intro v hv
      rw [evalV_finPart]
      have e1 : (Formalism.L2.Theta.mt V h).map (compFin D.host.F D.host.E v) = 1 := by
        have e2 : (matHom _ D.sp.cm.sig V.gram (projV V v h)).1 = 1 := by
          rw [h1 v hv, MonoidHom.map_one, Units.val_one]
        exact e2
      have e3 : ((Formalism.L2.Theta.mt V h) - 1).map (compFin D.host.F D.host.E v) = 0 := by
        rw [Matrix.map_sub _ (RingHom.map_sub _), Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), e1, sub_self]
      exact congrFun (congrFun e3 i) j
    rw [Matrix.smul_apply, smul_eq_mul, ex]
    show Formalism.IndefR.Lev.swapAE D (b ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = _
    rw [← RingHom.map_mul]
    refine congrArg (Formalism.IndefR.Lev.swapAE D) ?_
    exact one_sub_ind_tmul_mul Sb _ hz

open GlobalTheory.AdelicU

theorem level_offS : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Lv : LevDat D.host.E ℂ V.rank) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), IsBaseFrame V β Λ 1 → (∀ PP, PP ∈ Lv.Pg ∨ PP ∈ Lv.Q → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ Sb) → SphOff (levG V β Lv : Set (GA D V)) (levChi V β Lv) Sb ∧ (∀ g ∈ GfC V, g ∈ levG V β Lv ↔ (∃ k ∈ levG V β Lv, ∀ v ∈ Sb, projV V v g = projV V v k) ∧ ∀ v ∉ Sb, projV V v g ∈ Kv V v) ∧ (∀ g : GA D V, {v | projV V v g ∉ Kv V v}.Finite) ∧ ∀ k ∈ levG V β Lv, ‖levChi V β Lv k‖ = 1 := by
  intro D V β Λ Lv Sb hB hPl
  have hsplit := GlobalTheory.LevSplit.lev_split V β Λ 1 Lv hB
  have hK : ∀ k ∈ levG V β Lv, ∀ v, projV V v k ∈ Kv V v := fun k hk =>
    ((mem_KsphC_iff V k).1 ((finE_mem_St_iff hB hk.1).1 (finE_mem_St_of_mem_levG hk))).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP
    rw [GlobalTheory.GoodPrimes.offS_iff] at hP
    obtain ⟨e, f, hpe⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.1 P
    have h1P : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
      rw [Nat.cast_one]
      exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    obtain ⟨h1, h2, -⟩ := hsplit.2 P e f hpe h1P fun PP hPP =>
      ⟨fun e => by subst e; exact hP (hPl _ hPP),
       fun hc => hP (by rw [← GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc]; exact hPl PP hPP)⟩
    exact ⟨e, f, hpe, h1, h2⟩
  · intro g hg
    constructor
    · intro h
      exact ⟨⟨g, h, fun _ _ => rfl⟩, fun v _ => hK g h v⟩
    · rintro ⟨⟨k, hk, heq⟩, hoff⟩
      have hxf : g * k⁻¹ ∈ GfC V := mul_mem hg (inv_mem hk.1)
      have hx1 : ∀ v ∈ Sb, projV V v (g * k⁻¹) = 1 := fun v hv => by
        rw [MonoidHom.map_mul, MonoidHom.map_inv, heq v hv, mul_inv_cancel]
      have hxK : g * k⁻¹ ∈ KsphC V ∅ := (mem_KsphC_iff V _).2 ⟨hxf, fun v => by
        by_cases hv : v ∈ Sb
        · rw [hx1 v hv]; exact one_mem _
        · rw [MonoidHom.map_mul, MonoidHom.map_inv]; exact mul_mem (hoff v hv) (inv_mem (hK k hk v))⟩
      have hxS := (finE_mem_St_iff hB hxf).2 hxK
      have hxl : g * k⁻¹ ∈ levG V β Lv := ⟨hxf, GlobalTheory.LevSplit.mem_lev_of_red _ _ β Lv _
        (GlobalTheory.LevSplit.finE_mem_UA V _) hxS fun PP hPP => redFn_eq_one_of_proj β Sb hxS hx1 (hPl PP hPP)⟩
      have e : g = g * k⁻¹ * k := by rw [inv_mul_cancel_right]
      rw [e]
      exact mul_mem hxl hk
  · intro g
    haveI := SelfDual.isLattice_frameLat V
    exact Filter.eventually_cofinite.1 (eventually_proj_mem_stabLoc D.sp.cm.sig V.gram (frameLat V) g)
  · intro k hk
    obtain ⟨n, hn, h⟩ := hsplit.1 k hk
    exact Complex.norm_eq_one_of_pow_eq_one h hn.ne'

end GlobalTheory.FinZeta.LevelOff

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datumLevel_hyperspecial_off_finite_places : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (Lv : LevDat D.host.E ℂ V.rank) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), IsBaseFrame V β Λ 1 → (∀ PP, PP ∈ Lv.Pg ∨ PP ∈ Lv.Q → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ Sb) → SphOff (levG V β Lv : Set (GA D V)) (levChi V β Lv) Sb ∧ (∀ g ∈ GfC V, g ∈ levG V β Lv ↔ (∃ k ∈ levG V β Lv, ∀ v ∈ Sb, projV V v g = projV V v k) ∧ ∀ v ∉ Sb, projV V v g ∈ Kv V v) ∧ (∀ g : GA D V, {v | projV V v g ∉ Kv V v}.Finite) ∧ ∀ k ∈ levG V β Lv, ‖levChi V β Lv k‖ = 1 := by
  first | exact @GlobalTheory.FinZeta.LevelOff.level_offS | exact GlobalTheory.FinZeta.LevelOff.level_offS | (intros; apply GlobalTheory.FinZeta.LevelOff.level_offS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def KerLe {A B Z₁ Z₂ : Type} [AddCommMonoid Z₁] [AddCommMonoid Z₂] (q₁ : A → B → Z₁) (q₂ : A → B → Z₂) : Prop :=
  ∀ (n : ℕ) (a : Fin n → A) (b : Fin n → B), ∑ i, q₁ (a i) (b i) = 0 → ∑ i, q₂ (a i) (b i) = 0

def AbsIrr {G K : Type} [AddCommGroup K] [Module ℂ K] (a : G → Module.End ℂ K) : Prop :=
  (∀ N : Submodule ℂ K, (∀ g, ∀ x ∈ N, a g x ∈ N) → N = ⊥ ∨ N = ⊤) ∧
    ∀ T : Module.End ℂ K, (∀ g, T ∘ₗ a g = a g ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id

def intersection_update_fsHerm_neg_one {ι : Type} {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (i : ι) (f : Module.End ℂ (K i)) :
    Module.End ℂ (⨂[ℂ] j, K j) :=
  PiTensorProduct.map (Function.update (fun j => (LinearMap.id : K j →ₗ[ℂ] K j)) i f)

theorem position_tprod {ι : Type} {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (i : ι)
    (f : Module.End ℂ (K i)) (v : ∀ j, K j) :
    intersection_update_fsHerm_neg_one i f (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v i (f (v i))) := by
  unfold intersection_update_fsHerm_neg_one
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext j
  rcases eq_or_ne j i with rfl | hji
  · simp
  · simp [hji]

section Cover

variable {p q r s : ℕ}

def AdjRule {Y Z : Type} [AddCommGroup Y] [Module ℂ Y] [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z) : Prop :=
  ∀ (X : Mat p q) P P' y y', ⟪B (fockAct1 p q r s X P) y, B P' y'⟫_ℂ = ⟪B P y, B (fockAct1 p q r s (adjZ X) P') y'⟫_ℂ

def InvRule (N : GKMod r s) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z) : Prop :=
  ∀ (Y : Mat r s) P y, B (fockAct2 p q r s Y P) y = B P (N.act (adjZ Y) y)


variable (p q r s) in
def UnitaryImage : Prop :=
  ∀ (Y Z : Type) [AddCommGroup Y] [Module ℂ Y] [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] Z), AdjRule B →
    ∃ (A : UGKMod p q) (j : A.M.V →ₗ[ℂ] Z) (B' : Pol p q r s →ₗ[ℂ] Y →ₛₗ[starRingEnd ℂ] A.M.V),
      Function.Injective j ∧ (∀ P y, j (B' P y) = B P y) ∧ Submodule.span ℂ {x | ∃ P y, B' P y = x} = ⊤ ∧
        ∀ X P y, B' (fockAct1 p q r s X P) y = A.M.act X (B' P y)

def contr {A V H : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H) (y : V) : A ⊗[ℂ] V →ₗ[ℂ] A :=
  (TensorProduct.rid ℂ A).toLinearMap ∘ₗ LinearMap.lTensor A (innerₛₗ ℂ (ι y) ∘ₗ ι)


variable (p q) in
def FiniteSupport {T : GrpData r s} (R : DSRep T) : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (B : Pol p q r s →ₗ[ℂ] R.HK.V →ₛₗ[starRingEnd ℂ] A), InvRule R.HK B →
    ∀ P, ∃ E : Submodule ℂ R.HK.V, FiniteDimensional ℂ E ∧ ∀ y, (∀ e ∈ E, ⟪R.ι y, R.ι e⟫_ℂ = 0) → B P y = 0

def TensorForm : Prop :=
  ∀ (U A V H : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι →
    (∀ t : A ⊗[ℂ] V, (∀ y, contr ι y t = 0) → t = 0) ∧
    ∀ B : U →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] A,
      (∀ P, ∃ E : Submodule ℂ V, FiniteDimensional ℂ E ∧ ∀ y, (∀ e ∈ E, ⟪ι y, ι e⟫_ℂ = 0) → B P y = 0) →
      ∃ f : U →ₗ[ℂ] A ⊗[ℂ] V, ∀ P y, contr ι y (f P) = B P y

structure IsCoverPair (N : GKMod r s) {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (B : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z) : Prop where
  skew : ∀ X ∈ upq p q, ∀ P P' y y',
    ⟪B (fockAct1 p q r s X P) y, B P' y'⟫_ℂ + ⟪B P y, B (fockAct1 p q r s X P') y'⟫_ℂ = 0
  inv : ∀ Y ∈ upq r s, ∀ P y, B (fockAct2 p q r s Y P) y + B P (N.act Y y) = 0


variable (p q) in
def CoverKer (N : GKMod r s) : Prop :=
  ∀ (Z₁ Z₂ : Type) [NormedAddCommGroup Z₁] [InnerProductSpace ℂ Z₁] [NormedAddCommGroup Z₂] [InnerProductSpace ℂ Z₂]
    (B₁ : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z₁) (B₂ : Pol p q r s →ₗ[ℂ] N.V →ₛₗ[starRingEnd ℂ] Z₂),
    IsCoverPair N B₁ → IsCoverPair N B₂ → B₁ ≠ 0 → KerLe (fun P y => B₁ P y) fun P y => B₂ P y

end Cover

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel W S')

structure IsKAct (τ : D.what₂.Tau) (a : Matrix (Fin V.rank) (Fin V.rank) ℂ → Module.End ℂ (kFin M τ)) : Prop where
  der : ∀ X ∈ lieAt V τ, ∀ v : kFin M τ,
    HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (a X v : M.H τ) 0
  skew : ∀ X ∈ lieAt V τ, ∀ v w : kFin M τ, ⟪a X v, w⟫_ℂ + ⟪v, a X w⟫_ℂ = 0

def KSm : Prop := ∀ τ, kFin M τ ≤ M.sm τ

abbrev KT : Type := ⨂[ℂ] τ, kFin M τ


variable {M} in
def inclK (h : KSm M) : KT M →ₗ[ℂ] SmT M := PiTensorProduct.map fun τ => Submodule.inclusion (h τ)

def kOp (τ : D.what₂.Tau) {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ maxCpt M τ) : Module.End ℂ (kFin M τ) :=
  (M.rep τ k : M.H τ →ₗ[ℂ] M.H τ).restrict fun _ hv => rep_mem_kFin M τ hk hv

def sOp (τ : D.what₂.Tau) (aT : ℚ) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) : Module.End ℂ (LPol W.rank V.rank) :=
  locS (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) + (-((aT : ℂ) * X.trace)) • 1

def tOp (τ : D.what₂.Tau) (aS : ℚ) (Y : Matrix (Fin W.rank) (Fin W.rank) ℂ) : Module.End ℂ (LPol W.rank V.rank) :=
  locT (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) + ((aS : ℂ) * Y.trace) • 1

structure IsLocPair (τ : D.what₂.Tau) (aS aT : ℚ) (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ))
    {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] (B : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z) :
    Prop where
  skew : ∀ X ∈ lieAt V τ, ∀ P P' y y', ⟪B (sOp M M' τ aT X P) y, B P' y'⟫_ℂ + ⟪B P y, B (sOp M M' τ aT X P') y'⟫_ℂ = 0
  inv : ∀ Y ∈ lieAt W τ, ∀ P y, B (tOp M M' τ aS Y P) y + B P (a' Y y) = 0

def LocKer (τ : D.what₂.Tau) (aS aT : ℚ) (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)) : Prop :=
  ∀ (Z₁ Z₂ : Type) [NormedAddCommGroup Z₁] [InnerProductSpace ℂ Z₁] [NormedAddCommGroup Z₂] [InnerProductSpace ℂ Z₂]
    (B₁ : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z₁) (B₂ : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z₂),
    IsLocPair M M' τ aS aT a' B₁ → IsLocPair M M' τ aS aT a' B₂ → B₁ ≠ 0 →
      KerLe (fun P y => B₁ P y) fun P y => B₂ P y

def IsCuspGrow (θ : InfFam D) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  IsAutFun V φ ∧ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ IsCuspFun V φ ∧ GlobalTheory.Grow.UnifModGrowth V θ φ

def kMean (τ : D.what₂.Tau) (e : Formalism.REAL.KG (M.ε τ) → ℂ) (w : M.H τ) : M.H τ :=
  ∫ k, e k • M.σ τ (Formalism.REAL.toMK k) w ∂(Formalism.REAL.muK (M.ε τ))

def IsCoefFam {G : Type} [Group G] [TopologicalSpace G] {n : ℕ} (c : Fin n → G → ℂ) : Prop :=
  (∀ i, Continuous (c i)) ∧ ∀ (k₀ : G) (i : Fin n), ∃ d : Fin n → ℂ, ∀ k, c i (k₀ * k) = ∑ j, d j * c j k

end GlobalTheory.Chain.IoLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitian
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaPairingLaws

theorem ipO_self {D : D7} {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (f : Mx D m n → ℂ) :
    ipO μ 𝓕 f f = (nrm2 μ 𝓕 f : ℂ) := by
  unfold ipO nrm2
  rw [← integral_complex_ofReal]
  congr 1
  funext w
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private theorem countable_ratL' {D : D7} (S T : HSp D) : Countable ↥(ratL T S) := by
  haveI : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := D.host.E)
  haveI : Countable (Matrix (Fin T.rank) (Fin S.rank) D.host.E) :=
    inferInstanceAs (Countable (Fin T.rank → Fin S.rank → D.host.E))
  have h : (ratL T S : Set (WO S T)).Countable := by
    rw [ratL, AddMonoidHom.coe_range]
    exact Set.countable_range _
  exact h.to_subtype

theorem ipO_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsCovolOne (ratL T S) μ 𝓕 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IntegrableOn (fun w => f w * (starRingEnd ℂ) (g w)) 𝓕 μ ∧ ipO μ 𝓕 g f = (starRingEnd ℂ) (ipO μ 𝓕 f g) ∧ (∀ c : ℂ, ipO μ 𝓕 (c • f) g = c * ipO μ 𝓕 f g ∧ ipO μ 𝓕 f (c • g) = (starRingEnd ℂ) c * ipO μ 𝓕 f g) ∧ (∀ f', IsThetaFunO ψ S T f' → ipO μ 𝓕 (f + f') g = ipO μ 𝓕 f g + ipO μ 𝓕 f' g ∧ ipO μ 𝓕 g (f + f') = ipO μ 𝓕 g f + ipO μ 𝓕 g f') ∧ ipO μ 𝓕 f f = (nrm2 μ 𝓕 f : ℂ) ∧ (nrm2 μ 𝓕 f = 0 → f = 0) ∧ (∀ w, ipO μ 𝓕 (heisO ψ S T w f) (heisO ψ S T w g) = ipO μ 𝓕 f g ∧ ipO μ 𝓕 (heisO ψ S T w f) g = ipO μ 𝓕 f (heisO ψ S T (-w) g)) ∧ ∀ μ' 𝓕', IsCovolOne (ratL T S) μ' 𝓕' → ipO μ' 𝓕' f g = ipO μ 𝓕 f g := by
  intro D ψ S T μ 𝓕 hψ hμ f g hf hg
  have hμ₀ := hμ
  unfold IsCovolOne at hμ₀
  obtain ⟨hHaar, hFD, -⟩ := hμ₀
  haveI := hHaar
  obtain ⟨-, hL2⟩ := GlobalTheory.ThetaSquare.theta_square_integrable D S T
  obtain ⟨hSq, hHeis, -⟩ := hL2 ψ hψ
  obtain ⟨-, hInvol, hPres, hUnit, -⟩ := hHeis
  obtain ⟨-, -, ⟨-, hHL⟩, -⟩ := (GlobalTheory.ThetaAllChar.thetaFacts D).std hψ S T

  have hInt : ∀ a b : WO S T → ℂ, IsThetaFunO ψ S T a → IsThetaFunO ψ S T b →
      IntegrableOn (fun w => a w * (starRingEnd ℂ) (b w)) 𝓕 μ :=
    fun a b ha hb => (hHL μ μ 𝓕 𝓕 hμ hμ a b ha hb).2.1
  refine ⟨hInt f g hf hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    unfold ipO
    rw [← integral_conj]
    congr 1
    funext w
    rw [map_mul, Complex.conj_conj, mul_comm]
  · intro c
    constructor
    · unfold ipO
      rw [← integral_const_mul]
      congr 1
      funext w
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_mul, map_add]
      ring
    · unfold ipO
      rw [← integral_const_mul]
      congr 1
      funext w
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_mul, map_add]
      ring
  · intro f' hf'
    constructor
    · unfold ipO
      rw [← integral_add (hInt f g hf hg) (hInt f' g hf' hg)]
      congr 1
      funext w
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_mul, map_add]
      ring
    · unfold ipO
      rw [← integral_add (hInt g f hg hf) (hInt g f' hg hf')]
      congr 1
      funext w
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, map_mul, map_add]
      ring
  · exact ipO_self μ 𝓕 f
  ·

    intro h0
    haveI := countable_ratL' S T
    haveI : BorelSpace (WO S T) := ⟨rfl⟩
    haveI : MeasurableConstVAdd ↥(ratL T S) (WO S T) := ⟨fun γ => measurable_const_add (γ : WO S T)⟩
    haveI : VAddInvariantMeasure ↥(ratL T S) (WO S T) μ :=
      ⟨fun γ s _ => measure_preimage_add μ (γ : WO S T) s⟩
    unfold nrm2 at h0
    have hI : IntegrableOn (fun w => ‖f w‖ ^ 2) 𝓕 μ := by
      refine (hInt f f hf hf).norm.congr (Filter.Eventually.of_forall fun w => ?_)
      simp only [norm_mul, Complex.norm_conj, sq]
    have hae : (fun w => ‖f w‖ ^ 2) =ᵐ[μ.restrict 𝓕] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun w => sq_nonneg ‖f w‖) hI).1 h0
    have hae' : ∀ᵐ w ∂μ.restrict 𝓕, f w = 0 :=
      hae.mono fun w hw => by simpa using hw
    have htopen : IsOpen {x : WO S T | f x ≠ 0} := isOpen_ne_fun hf.cont continuous_const
    have hts : μ ({x : WO S T | f x ≠ 0} ∩ 𝓕) = 0 := by
      rw [← Measure.restrict_apply₀' hFD.nullMeasurableSet]
      exact ae_iff.1 hae'
    have hzero : μ {x : WO S T | f x ≠ 0} = 0 := by
      refine hFD.measure_zero_of_invariant _ (fun γ => ?_) hts
      ext y
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change f ((↑(-γ) : WO S T) + y) ≠ 0 ↔ f y ≠ 0
      rw [← norm_ne_zero_iff, (hSq f hf).1 (↑(-γ)) (-γ).2 y, norm_ne_zero_iff]
    have hempty := (htopen.measure_eq_zero_iff μ).1 hzero
    funext x
    by_contra hx
    have hmem : x ∈ {x : WO S T | f x ≠ 0} := hx
    rw [hempty] at hmem
    exact hmem
  · intro w
    refine ⟨hUnit μ 𝓕 hHaar hFD w f g hf hg, ?_⟩
    have hg' : IsThetaFunO ψ S T (heisO ψ S T (-w) g) := hPres (-w) g hg
    have e := hInvol (-w) g
    rw [neg_neg] at e
    calc ipO μ 𝓕 (heisO ψ S T w f) g
        = ipO μ 𝓕 (heisO ψ S T w f) (heisO ψ S T w (heisO ψ S T (-w) g)) := by rw [e]
      _ = ipO μ 𝓕 f (heisO ψ S T (-w) g) := hUnit μ 𝓕 hHaar hFD w f _ hf hg'
  ·
    intro μ' 𝓕' h'
    have a := (hHL μ' μ 𝓕' 𝓕 h' hμ f g hf hg).2.2
    have b := (hHL μ μ 𝓕 𝓕 hμ hμ f g hf hg).2.2
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.RealDirectionThetaNonzero.heisO_apply_zero] at a b
    unfold ipO
    rw [a, b]

end GlobalTheory.ThetaPairingLaws
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitianStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_inner_product_hermitian : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsCovolOne (ratL T S) μ 𝓕 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IntegrableOn (fun w => f w * (starRingEnd ℂ) (g w)) 𝓕 μ ∧ ipO μ 𝓕 g f = (starRingEnd ℂ) (ipO μ 𝓕 f g) ∧ (∀ c : ℂ, ipO μ 𝓕 (c • f) g = c * ipO μ 𝓕 f g ∧ ipO μ 𝓕 f (c • g) = (starRingEnd ℂ) c * ipO μ 𝓕 f g) ∧ (∀ f', IsThetaFunO ψ S T f' → ipO μ 𝓕 (f + f') g = ipO μ 𝓕 f g + ipO μ 𝓕 f' g ∧ ipO μ 𝓕 g (f + f') = ipO μ 𝓕 g f + ipO μ 𝓕 g f') ∧ ipO μ 𝓕 f f = (nrm2 μ 𝓕 f : ℂ) ∧ (nrm2 μ 𝓕 f = 0 → f = 0) ∧ (∀ w, ipO μ 𝓕 (heisO ψ S T w f) (heisO ψ S T w g) = ipO μ 𝓕 f g ∧ ipO μ 𝓕 (heisO ψ S T w f) g = ipO μ 𝓕 f (heisO ψ S T (-w) g)) ∧ ∀ μ' 𝓕', IsCovolOne (ratL T S) μ' 𝓕' → ipO μ' 𝓕' f g = ipO μ 𝓕 f g := by
  first | exact @GlobalTheory.ThetaPairingLaws.ipO_laws | exact GlobalTheory.ThetaPairingLaws.ipO_laws | (intros; apply GlobalTheory.ThetaPairingLaws.ipO_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsAreCoverDiscreteSeriesOfHarishChandra
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsAreCoverDiscreteSeriesOfHarishChandra
namespace GlobalTheory.CoverModel

theorem modelsAreCoverSeries_all :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
      ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D :=
  modelsAreCoverSeries

end GlobalTheory.CoverModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsAreCoverDiscreteSeriesOfHarishChandraStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaModels_are_coverDiscreteSeries_of_harishChandra : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D := by
  first | exact @GlobalTheory.CoverModel.modelsAreCoverSeries_all | exact GlobalTheory.CoverModel.modelsAreCoverSeries_all | (intros; apply GlobalTheory.CoverModel.modelsAreCoverSeries_all <;> assumption)
end
end
