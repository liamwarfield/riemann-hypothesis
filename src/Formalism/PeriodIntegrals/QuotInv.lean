module

public import Mathlib

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.QuotInv
open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace PI

abbrev MtM (m : ℕ) := Fin m → Fin m → ℂ

def lmulQ {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) (x : MtM m) : MtM m := a * Matrix.of x

def rmulQ {m : ℕ} (a : Matrix (Fin m) (Fin m) ℂ) (x : MtM m) : MtM m := Matrix.of x * a

def IsMatGroup {m : ℕ} (G : Set (Matrix (Fin m) (Fin m) ℂ)) : Prop :=
  IsClosed G ∧ (1 : Matrix (Fin m) (Fin m) ℂ) ∈ G ∧ (∀ a ∈ G, ∀ b ∈ G, a * b ∈ G) ∧
    ∀ a ∈ G, a⁻¹ ∈ G ∧ a * a⁻¹ = 1

def IsHaarOnM {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (MtM m)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ {x | Matrix.of x ∉ S} = 0 ∧
    ∀ s ∈ S, μ.map (lmulQ s) = μ

def IsRightInvM {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (MtM m)) : Prop :=
  ∀ s ∈ S, μ.map (rmulQ s) = μ

def IsQuotM {m : ℕ} (μG μS ν : Measure (MtM m)) : Prop :=
  ∀ f : MtM m → ℝ≥0∞, Measurable f →
    ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂ν

def QuotientSetting {m : ℕ} (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS ν : Measure (MtM m)) : Prop :=
  IsMatGroup G ∧ IsMatGroup S ∧ S ⊆ G ∧ IsHaarOnM G μG ∧ IsHaarOnM S μS ∧ IsRightInvM G μG ∧ IsRightInvM S μS ∧
    IsQuotM μG μS ν

def QuotInv : Prop :=
  ∀ (m : ℕ) (G S : Set (Matrix (Fin m) (Fin m) ℂ)) (μG μS ν : Measure (MtM m)), QuotientSetting G S μG μS ν →
    ∀ F : MtM m → ℝ≥0∞, Measurable F →
      (∀ s ∈ S, ∀ x : MtM m, Matrix.of x ∈ G → F (fun i j => (s * Matrix.of x) i j) = F x) →
      ∀ g ∈ G, ∫⁻ x, F (fun i j => (Matrix.of x * g) i j) ∂ν = ∫⁻ x, F x ∂ν

end PI

end
end

section -- merged from Formalism.PeriodIntegrals.RhsWLim
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal ContDiff

namespace PI.RhsWLim

def UH {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) : Set (Matrix ι ι ℂ) :=
  {g | gᴴ * H * g = H}

def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val, by omega⟩

def esI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨2 * r + k - a.val, by omega⟩

def Hpk (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  if i.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if j.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if r ≤ i.val ∧ i.val ≤ r + k ∧ i = j then (if i.val = r + k then -1 else 1)
  else 0

def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ := Pi.single i 1

abbrev Mt (k r : ℕ) := Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ

def lmulM {k r : ℕ} (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x : Mt k r) : Mt k r :=
  a * Matrix.of x

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

abbrev GV (k r : ℕ) : Set (Mat k r) := UH (Hpk k r)

def UWb (k r : ℕ) : Set (Mat k r) :=
  {g | g ∈ GV k r ∧ ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)}

def IsHaarOn {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (μ : Measure (Mt k r)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ {x | Matrix.of x ∉ S} = 0 ∧
    ∀ s ∈ S, μ.map (lmulM s) = μ

def realifyFun {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : Fin m × Fin m × Bool → ℝ :=
  fun p => if p.2.2 then (X p.1 p.2.1).im else (X p.1 p.2.1).re

def unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ⟨x (i, j, false), x (i, j, true)⟩

def lieOf {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ S}

def lieE {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Submodule ℝ (EuclideanSpace ℝ (Fin m × Fin m × Bool)) :=
  Submodule.span ℝ ((fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieOf S)

def wI (k r : ℕ) (j : Fin (k + 1)) : Fin (2 * r + k + 1) := ⟨r + j.val, by omega⟩

def herm {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ := star w ⬝ᵥ (H *ᵥ v)

def inWb (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → v i = 0

def Tz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : ℝ := -(herm (Hpk k r) z z).re

def UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    g *ᵥ z = z}

def Hb (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j => if j = Fin.last k then -1 else 1

def wbPart (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => v (wI k r j)

def IsSection (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Prop :=
  (∀ i j : Fin (k + 1), ContDiffOn ℝ ∞ (fun ζ => μsec ζ i j) {ζ : ℂ | Tz k r z * Tz k r z' < Complex.normSq ζ}) ∧
  ∀ ζ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ →
    Matrix.conjTranspose (μsec ζ) * Hb k * μsec ζ = Hb k ∧ herm (Hb k) (μsec ζ *ᵥ wbPart k r z') (wbPart k r z) = ζ

def embWb (k r : ℕ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Mat k r := fun i j =>
  if h : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then μ ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩
  else if i = j ∧ ¬ (r ≤ i.val ∧ i.val ≤ r + k) then 1 else 0

def zWeight (k : ℕ) (T T' : ℝ) (ζ : ℂ) : ℝ :=
  if T * T' ≤ Complex.normSq ζ then (Complex.normSq ζ - T * T') ^ (k - 1) else 0

def volU (j : ℕ) : ℝ := ∏ i ∈ Finset.range j, (2 * Real.pi) ^ (i + 1) / (i.factorial : ℝ)

def wbConst (k : ℕ) (T T' a a' : ℝ) : ℝ :=
  2 * volU k ^ 2 / ((T * T') ^ k * volU (k - 1) * a * a')

variable {k r : ℕ}

def expBall (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (ρ : ℝ) : Set (Mt k r) :=
  (fun x : lieE S =>
      fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) '' Metric.ball 0 ρ

def rhsW (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (φ : Mt k r → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
    ∫⁻ h, ∫⁻ h', φ (fun i j => (Matrix.of h * embWb k r (μsec ζ) * (Matrix.of h')⁻¹) i j) ∂μW' ∂μW

def zeta0 (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : ℂ := ((2 * Real.sqrt (Tz k r z * Tz k r z') : ℝ) : ℂ)

def mBase (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  embWb k r (μsec (zeta0 k r z z'))

def bBall (k r : ℕ) (ρ : ℝ) : Set (Mt k r) := expBall (k := k) (r := r) (UWb k r) ρ

def mBall (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ρ : ℝ) :
    Set (Mt k r) :=
  {x | (fun i j => ((mBase k r z z' μsec)⁻¹ * Matrix.of x) i j) ∈ bBall k r ρ}

def bVol (k r : ℕ) (ρ : ℝ) : ℝ :=
  (volume (Metric.ball (0 : lieE (UWb k r)) ρ)).toReal

structure WbData (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop where
  k_pos : 1 ≤ k
  z_mem : inWb k r z
  z'_mem : inWb k r z'
  T_pos : 0 < Tz k r z
  T'_pos : 0 < Tz k r z'
  haarW : IsHaarOn (UWset k r z) μW
  haarW' : IsHaarOn (UWset k r z') μW'
  a_pos : 0 < a
  a'_pos : 0 < a'
  massW : μW Set.univ = ENNReal.ofReal a
  massW' : μW' Set.univ = ENNReal.ofReal a'
  sec : IsSection k r z z' μsec

def RhsWLim : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ) μsec,
    WbData k r z z' μW μW' a a' μsec →
    Tendsto (fun ρ : ℝ => (rhsW k r z z' μW μW' μsec ((mBall k r z z' μsec ρ).indicator 1)).toReal / bVol k r ρ)
      (𝓝[>] 0) (𝓝 (wbConst k (Tz k r z) (Tz k r z') a a')⁻¹)

end PI.RhsWLim
end
end

section -- merged from Formalism.PeriodIntegrals.WeilQuotMeas
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix

namespace PI.WeilQuotMeas

def WeilQuotient : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ (μ : Measure G) (ν : Measure H), μ.IsHaarMeasure → μ.IsMulRightInvariant → ν.IsHaarMeasure →
      ν.IsMulRightInvariant →
      ∃ ρ : Measure (G ⧸ H), ρ ≠ 0 ∧ (∀ K : Set (G ⧸ H), IsCompact K → ρ K < ⊤) ∧
        (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ ((fun y => g • y) ⁻¹' s) = ρ s) ∧
        (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μ = ∫⁻ y, (∫⁻ h, f (y.out * h) ∂ν) ∂ρ) ∧
        ∀ ρ' : Measure (G ⧸ H), (∀ K : Set (G ⧸ H), IsCompact K → ρ' K < ⊤) →
          (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ' ((fun y => g • y) ⁻¹' s) = ρ' s) →
          ∃ c : ℝ≥0∞, ρ' = c • ρ

def WqUnique : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ ρ ρ' : Measure (G ⧸ H), ρ ≠ 0 →
      (∀ K : Set (G ⧸ H), IsCompact K → ρ K < ⊤) →
      (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ ((fun y => g • y) ⁻¹' s) = ρ s) →
      (∀ K : Set (G ⧸ H), IsCompact K → ρ' K < ⊤) →
      (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ' ((fun y => g • y) ⁻¹' s) = ρ' s) →
      ∃ c : ℝ≥0∞, ρ' = c • ρ

end PI.WeilQuotMeas
end
end

section -- merged from Formalism.PeriodIntegrals.Transference
open Module
open scoped InnerProductSpace

noncomputable section

namespace PI

def TransferenceCover : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (lam : ℝ), 0 < lam →
    (∀ y : E, y ≠ 0 → (∀ x ∈ Λ, ∃ n : ℤ, inner ℝ x y = (n : ℝ)) → lam ≤ ‖y‖) →
    ∀ x : E, ∃ l ∈ Λ, ‖x - l‖ * lam ≤ (finrank ℝ E : ℝ) / 2

def succMin {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) (i : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∃ v : Fin i → EuclideanSpace ℝ (Fin N),
    (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t}

def dualZ {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) : Submodule ℤ (EuclideanSpace ℝ (Fin N)) where
  carrier := {x | ∀ y ∈ M, ∃ z : ℤ, ⟪x, y⟫_ℝ = z}
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨z1, h1⟩ := ha y hy
    obtain ⟨z2, h2⟩ := hb y hy
    exact ⟨z1 + z2, by rw [inner_add_left, h1, h2]; push_cast; ring⟩
  zero_mem' := fun y _ => ⟨0, by simp⟩
  smul_mem' := by
    intro c a ha y hy
    obtain ⟨z, h⟩ := ha y hy
    exact ⟨c * z, by rw [← Int.cast_smul_eq_zsmul ℝ c a, real_inner_smul_left, h]; push_cast; ring⟩

def TransferenceMinima : Prop :=
  ∀ (N : ℕ) (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))),
    DiscreteTopology M → Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ →
    ∀ i, 1 ≤ i → i ≤ N → succMin M i * succMin (dualZ M) (N + 1 - i) ≤ N

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.LongWeylElementSquare
noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped ENNReal

namespace PI.SwBig

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

def UH {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) : Set (Matrix ι ι ℂ) :=
  {g | gᴴ * H * g = H}

def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val, by omega⟩

def esI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨2 * r + k - a.val, by omega⟩

def Hpk (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  if i.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if j.val < r ∧ i.val + j.val = 2 * r + k then 1
  else if r ≤ i.val ∧ i.val ≤ r + k ∧ i = j then (if i.val = r + k then -1 else 1)
  else 0

def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ := Pi.single i 1

def Nset (k r : ℕ) : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      g i (eI k r a) = if i = eI k r a then 1 else 0) ∧
    (∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      g i j = if i = j then 1 else 0)}

def bigCell (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  if hj : j.val < r then (if i = esI k r ⟨j.val, hj⟩ then c ⟨j.val, hj⟩ else 0)
  else if hj2 : j.val ≤ r + k then
    (if hi : r ≤ i.val ∧ i.val ≤ r + k then μ ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ else 0)
  else
    (if i.val = 2 * r + k - j.val then (star (c ⟨2 * r + k - j.val, by omega⟩))⁻¹ else 0)

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

abbrev GV (k r : ℕ) : Set (Mat k r) := UH (Hpk k r)

def UWb (k r : ℕ) : Set (Mat k r) :=
  {g | g ∈ GV k r ∧ ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)}

def w0B (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := bigCell k r 1 1

def LongWeylElementSquare : Prop := ∀ k r : ℕ, w0B k r * w0B k r = 1

def tv (k r : ℕ) (c : Fin r → ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if h : i.val < r then c ⟨i.val, h⟩
  else if h2 : i.val ≤ r + k then 1
  else (star (c ⟨2 * r + k - i.val, by have := i.isLt; omega⟩))⁻¹

def tM (k r : ℕ) (c : Fin r → ℂ) : Mat k r := Matrix.diagonal (tv k r c)

def dv (k r : ℕ) (x : Fin r → ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if h : i.val < r then x ⟨i.val, h⟩
  else if h2 : i.val ≤ r + k then 0
  else -star (x ⟨2 * r + k - i.val, by have := i.isLt; omega⟩)

def tD (k r : ℕ) (x : Fin r → ℂ) : Mat k r := Matrix.diagonal (dv k r x)

def Phi (k r : ℕ) (X : Mat k r) (x : Fin r → ℂ) (Z X' : Mat k r) : Mat k r :=
  w0B k r * NormedSpace.exp X * w0B k r * tM k r (1 + x) * NormedSpace.exp Z * NormedSpace.exp (-X')

def LmL (k r : ℕ) : (Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) →ₗ[ℝ] Mat k r where
  toFun p := w0B k r * p.1 * w0B k r + tD k r p.2.1 + p.2.2.1 - p.2.2.2
  map_add' p q := by
    have : tD k r (p.2.1 + q.2.1) = tD k r p.2.1 + tD k r q.2.1 := by
      unfold tD; rw [Matrix.diagonal_add]; congr 1; funext i; unfold dv
      split_ifs <;> simp [star_add] <;> ring
    simp only [Prod.fst_add, Prod.snd_add, this, Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c p := by
    have : tD k r (c • p.2.1) = c • tD k r p.2.1 := by
      have hd : ∀ i, dv k r (c • p.2.1) i = (c : ℂ) * dv k r p.2.1 i := by
        intro i; unfold dv; split_ifs <;> simp [Complex.real_smul]
      unfold tD; ext i j; simp only [Matrix.diagonal_apply, Matrix.smul_apply, hd]
      split_ifs <;> simp [Complex.real_smul]
    simp only [Prod.smul_fst, Prod.smul_snd, this, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, smul_add,
      smul_sub]

def Lm (k r : ℕ) : (Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap (LmL k r)

def GaussUniq : Prop := ∀ (k r : ℕ) (n₁ n₂ m₁ m₂ u₁ u₂ : Mat k r) (c₁ c₂ : Fin r → ℂ),
  n₁ ∈ Nset k r → n₂ ∈ Nset k r → m₁ ∈ UWb k r → m₂ ∈ UWb k r →
  u₁ ∈ Nset k r → u₂ ∈ Nset k r → (∀ a, c₂ a ≠ 0) →
  n₁ * bigCell k r c₁ 1 * m₁ * u₁⁻¹ = n₂ * bigCell k r c₂ 1 * m₂ * u₂⁻¹ →
  n₁ = n₂ ∧ c₁ = c₂ ∧ m₁ = m₂ ∧ u₁ = u₂

def PhiForm : Prop := ∀ (k r : ℕ) (X : Mat k r) (x : Fin r → ℂ) (Z X' : Mat k r),
  Phi k r X x Z X' =
    w0B k r * (NormedSpace.exp X * bigCell k r (1 + x) 1 * NormedSpace.exp Z * (NormedSpace.exp X')⁻¹)

def BigCellG : Prop := ∀ (k r : ℕ) (c : Fin r → ℂ), (∀ a, c a ≠ 0) → bigCell k r c 1 ∈ UH (Hpk k r)

def PhiDeriv : Prop := ∀ k r : ℕ,
  HasStrictFDerivAt (fun p : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r => Phi k r p.1 p.2.1 p.2.2.1 p.2.2.2)
    (Lm k r) 0

end PI.SwBig
end
end

section -- merged from Formalism.PeriodIntegrals.LatDefs
noncomputable section

namespace PI

def lat2 (w₁ w₂ : ℂ) : AddSubgroup ℂ := AddSubgroup.closure {w₁, w₂}

def area (Λ : AddSubgroup ℂ) : ℝ :=
  sInf {a : ℝ | 0 < a ∧ ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, a = |((starRingEnd ℂ) w₁ * w₂).im|}

def U1 (Λ : AddSubgroup ℂ) (ω : ℂ) (G : ℂ → ℂ) : ℂ → ℂ :=
  fun z => G (z + ω) * Complex.exp (-(Real.pi : ℂ) * z * (starRingEnd ℂ) ω / (area Λ : ℂ) -
    (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * (area Λ : ℂ)))

def eisG (Λ : AddSubgroup ℂ) (k : ℕ) : ℂ :=
  ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k)

def g2 (Λ : AddSubgroup ℂ) : ℂ := 60 * eisG Λ 2

def g3 (Λ : AddSubgroup ℂ) : ℂ := 140 * eisG Λ 3

def discr (Λ : AddSubgroup ℂ) : ℂ := g2 Λ ^ 3 - 27 * g3 Λ ^ 2

end PI

end
end

section -- merged from Formalism.PeriodIntegrals.KerIso
noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KerIso

def IsIsom {K E : Type} [Field K] [Field E] [Algebra K E] (cj : E → E) {n : Type} [Fintype n]
    (g : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) : Prop :=
  ∀ x y, ∑ w, algebraMap K E (g x w) * cj (algebraMap K E (g y w))
      = algebraMap K E (∑ a, Algebra.trace K E (x a * cj (y a)))

def AtP {K E : Type} [Field K] [NumberField K] [Field E] [Algebra K E] {n : Type} [Fintype n] (M : Set E)
    (g : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) (p : ℕ) : Prop :=
  (∀ x : Fin 4 → E, (∀ a, x a ∈ M) → ∃ s : ℕ, Nat.Coprime s p ∧
    ∀ w, (s : K) * g x w ∈ (algebraMap (𝓞 K) K).range) ∧
  ∀ v : Fin 4 × n → K, (∀ w, v w ∈ (algebraMap (𝓞 K) K).range) →
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ a, (s : E) * g.symm v a ∈ M

def detRel {K E : Type} [Field K] [Field E] [Algebra K E] {n : Type} [Fintype n]
    (g g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)) : K :=
  LinearMap.det ((g₀.symm.trans g : (Fin 4 × n → K) ≃ₗ[K] _) : (Fin 4 × n → K) →ₗ[K] (Fin 4 × n → K))

def ordK {K : Type} [Field K] [NumberField K] (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : K) : ℤ :=
  -WithZero.log (𝔭.valuation K x)

def IsConj (K : Type) {E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E) : Prop :=
  (∀ x, cj (cj x) = x) ∧ (∀ k : K, ∃ k' : K, cj (algebraMap K E k) = algebraMap K E k') ∧
    ∃ k : K, cj (algebraMap K E k) ≠ algebraMap K E k

def DetOrdIndep : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [Algebra K E] (n : Type) [Fintype n] (M : Set E) (p : ℕ)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (g g' g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)),
    p.Prime → ((p : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal → AtP M g p → AtP M g' p →
      ordK 𝔭 (detRel g g₀) = ordK 𝔭 (detRel g' g₀)

def DetOrdFin : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (n : Type) [Fintype n]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), I ≠ 0 →
    ∀ (S : ℕ → Prop) (pp : ℕ → IsDedekindDomain.HeightOneSpectrum (𝓞 K))
      (gp : ℕ → ((Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K))) (g₀ : (Fin 4 → E) ≃ₗ[K] (Fin 4 × n → K)),
      (∀ p, p.Prime → S p → ((p : ℕ) : 𝓞 K) ∈ (pp p).asIdeal) →
      (∀ p, p.Prime → S p → AtP {x : E | x ∈ I} (gp p) p) →
        {p : ℕ | p.Prime ∧ S p ∧ ordK (pp p) (detRel (gp p) g₀) ≠ 0}.Finite

def SplitsAt (K : Type) {E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E) (p : ℕ) : Prop :=
  ∃ P : Ideal (𝓞 K), P.IsPrime ∧ ((p : ℕ) : 𝓞 K) ∈ P ∧ ∃ a b : 𝓞 K,
    cj (algebraMap K E (a : K)) = algebraMap K E (b : K) ∧ a ∈ P ∧ b ∉ P

def SelfDualI (K : Type) {E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Prop :=
  ∀ y : E, y ∈ I ↔ ∀ x ∈ I, Algebra.trace K E (x * cj y) ∈ (algebraMap (𝓞 K) K).range

end PI.KerIso
end
end

section -- merged from Formalism.PeriodIntegrals.PhNormUnits
noncomputable section

open Classical

namespace PI.PhNormUnits

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

def zc {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) : ℂ_[p] := algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p])

section Ops

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

def add (l ex : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex

def mulBy (l ex : PowerSeries ℂ_[p]) (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex

def phAt (ph : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a ph

def be (l ex ph : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  phAt ph (add l ex a b) - phAt ph a - phAt ph b

end Ops

def Target : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X → p ≠ 2 →
    ((2 : ℂ_[p]), (2 : ℂ_[p])) ∈ S → (∀ α ∈ S, α.swap ∈ S) → (∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) →
    (∀ α ∈ S, ∀ β ∈ S, α * β ∈ S) →
    (∀ α ∈ S, IntegralMv (mulBy l ex α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    (∀ α ∈ S, ∃ n : ℤ_[p], α.1 + α.2 = zc n) → (∀ α ∈ S, ∃ n : ℤ_[p], α.1 * α.2 = zc n) →
    (∀ α ∈ S, ∃ β ∈ S, ∃ γ ∈ S, ‖β.1‖ = 1 ∧ ‖β.2‖ = 1 ∧ ‖γ.1‖ = 1 ∧ ‖γ.2‖ = 1 ∧ α = β + γ) →
    Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)) →
    (∀ α ∈ S, ‖α.1‖ = 1 → ‖α.2‖ = 1 → Simeq (phAt ph (mulBy l ex α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * phAt ph (Xv ()))) →
    ∀ α ∈ S, Simeq (phAt ph (mulBy l ex α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * phAt ph (Xv ()))

end PI.PhNormUnits
end
end

section -- merged from Formalism.PeriodIntegrals.PhMeasCore
open MeasureTheory Matrix
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI

namespace PhMeasCore

variable {n : ℕ}

def Jm (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => if ε a then 1 else -1

def UJset (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) := {g | gᴴ * Jm ε * g = Jm ε}

def UH (Hm : Matrix (Fin n) (Fin n) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) := {g | gᴴ * Hm * g = Hm}

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def SmoothOnH {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (Hm : Matrix (Fin n) (Fin n) ℂ)
    (f : Matrix (Fin n) (Fin n) ℂ → E) : Prop :=
  ∀ g₀, g₀ᴴ * Hm * g₀ = Hm → ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → E),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, g ∈ UH Hm → f g = F g

end Smooth

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def smoothVecs (Hm : Matrix (Fin n) (Fin n) ℂ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Set H :=
  {v | SmoothOnH Hm (fun g => σ g v)}

def InLie (Hm X : Matrix (Fin n) (Fin n) ℂ) : Prop := Xᴴ * Hm + Hm * X = 0

def dsig (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) (v : H) : H :=
  deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) 0

def dsigW (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : List (Matrix (Fin n) (Fin n) ℂ) → H → H
  | [], v => v
  | X :: w, v => dsig σ X (dsigW σ w v)

def IsCWCont {Wp : Type*} [NormedAddCommGroup Wp] (Hm : Matrix (Fin n) (Fin n) ℂ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (B : H → Wp) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Matrix (Fin n) (Fin n) ℂ))),
    (∀ w ∈ Ws, ∀ X ∈ w, InLie Hm X) ∧
    ∀ v ∈ smoothVecs Hm σ, ‖B v‖ ≤ C * (Ws.map fun w => ‖dsigW σ w v‖).sum

end PhMeasCore


open PhMeasCore in
def PhMeasCore : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Wp : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (B : H → Wp) (w : H),
    (∃ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P ∧ Pᴴ * Jm ε * P = Hm ∧
      (σ (P⁻¹ * 1 * P) = 1 ∧ ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, σ (P⁻¹ * (a * b) * P) = (σ (P⁻¹ * a * P)).comp (σ (P⁻¹ * b * P))) ∧
      ∀ v : H, ContinuousOn (fun g => σ (P⁻¹ * g * P) v) (UJset ε)) →
    (∀ v ∈ smoothVecs Hm σ, ∀ v' ∈ smoothVecs Hm σ, B (v + v') = B v + B v') →
    (∀ c : ℂ, ∀ v ∈ smoothVecs Hm σ, B (c • v) = c • B v) →
    IsCWCont Hm σ B →
    w ∈ smoothVecs Hm σ →
    Measurable (Set.indicator {x : Fin n → Fin n → ℂ | Matrix.of x ∈ UH Hm} (fun x => ‖B (σ (Matrix.of x) w)‖))

end PI

end
end

section -- merged from Formalism.PeriodIntegrals.ArtSch
namespace PI.ArtSch

open scoped NNReal

noncomputable section

section
variable (l : ℕ) [Fact l.Prime]

theorem OC_l_not_unit : ¬ IsUnit ((l : ℕ) : PadicComplexInt l) := by
  have key : Valued.v ((l : ℕ) : ℂ_[l]) = ‖((l : ℕ) : ℚ_[l])‖₊ := by
    have e1 : ((l : ℕ) : ℂ_[l]) = (((l : ℕ) : PadicAlgCl l) : ℂ_[l]) := by
      exact (map_natCast (UniformSpace.Completion.coeRingHom : PadicAlgCl l →+* ℂ_[l]) l).symm
    rw [e1, Valued.valuedCompletion_apply, ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l))]
    apply NNReal.eq
    exact PadicAlgCl.norm_extends l _
  rw [(PadicComplexInt.integers l).isUnit_iff_valuation_eq_one, map_natCast, key]
  intro h
  have h2 : ‖((l : ℕ) : ℚ_[l])‖ = 1 := by
    have h3 := congrArg NNReal.toReal h
    simpa using h3
  exact absurd h2 (ne_of_lt Padic.norm_p_lt_one)

instance factOC : Fact (¬ IsUnit ((l : ℕ) : PadicComplexInt l)) := ⟨OC_l_not_unit l⟩

abbrev OC : Type := ↥(PadicComplexInt l)

abbrev OCb : Type := PreTilt (OC l) l

instance domOCb : IsDomain (OCb l) :=
  PreTilt.isDomain (PadicComplex l) (PadicComplex.valued l).v (OC l) (PadicComplexInt.integers l) l

abbrev Cb : Type := FractionRing (OCb l)

instance charCb : CharP (Cb l) l := charP_of_injective_algebraMap' (OCb l) l

abbrev WCb : Type := WittVector l (Cb l)

abbrev valb : Valuation (OCb l) ℝ≥0 :=
  PreTilt.val (PadicComplex l) (PadicComplex.valued l).v (OC l) (PadicComplexInt.integers l) l

end

def Main : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (x : WCb l), ∃ y : WCb l, WittVector.map (frobenius (Cb l) l) y - y = x

def WittLift : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] [CharP k p], (∀ a : k, ∃ y : k, y ^ p - y = a) →
    ∀ x : WittVector p k, ∃ y : WittVector p k, WittVector.map (frobenius k p) y - y = x

def TiltAS : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (a : Cb l), ∃ y : Cb l, y ^ l - y = a

def RootModP : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (c b : ModP (OC l) l), ∃ z : ModP (OC l) l, z ^ l - c * z - b = 0

def TiltDiv : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (x y : OCb l), valb l x ≤ valb l y → y ∣ x

def TiltSmall : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (e : OCb l), valb l e < 1 → ∃ w : OCb l, w ^ l - w = e

def TiltGlue : Prop := RootModP → TiltDiv → TiltSmall → TiltAS

theorem main_of (hW : WittLift) (hT : TiltAS) : Main := by
  intro l _ x
  exact hW l (Cb l) (hT l) x

end

end PI.ArtSch
end

section -- merged from Formalism.PeriodIntegrals.KerLat
noncomputable section
open NumberField

namespace PI.KerLat

def PerPair : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Module.finrank ℚ K = 2 → (∃ k : K, (φ k).im ≠ 0) → cc ≠ ⊥ → δ ≠ 0 →
      ∃ L : PeriodPair, L.lattice.toAddSubgroup = AddSubgroup.closure {w : ℂ | ∃ c ∈ cc, w = δ * φ (c : K)}

end PI.KerLat
end
end

section -- merged from Formalism.PeriodIntegrals.ClassNumImQ
open NumberField

namespace PI.ClassNumImQ

def QuadData (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K) : Prop :=
  d.Prime ∧ d % 4 = 3 ∧ 3 < d ∧ b ^ 2 = -(d : K) ∧ IntermediateField.adjoin ℚ {b} = ⊤

def IntBasis : Prop :=
  ∀ (d : ℕ) (K : Type) [Field K] [NumberField K] (b : K), QuadData d K b →
    IsIntegral ℤ ((1 + b) / 2) ∧ ∀ x : 𝓞 K, ∃ m n : ℤ, (x : K) = m + n * ((1 + b) / 2)

end PI.ClassNumImQ
end

section -- merged from Formalism.PeriodIntegrals.TransferenceCoverRad
open scoped InnerProductSpace

noncomputable section

namespace PI

def TransferenceCoverDiv : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (M : Submodule ℤ V), DiscreteTopology M → Submodule.span ℝ (M : Set V) = ⊤ →
    ∀ κ : ℝ, 0 < κ → (∀ y : V, (∀ x ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → y ≠ 0 → κ ≤ ‖y‖) →
    ∀ x : V, ∃ y ∈ M, ‖x - y‖ ≤ (Module.finrank ℝ V : ℝ) / (2 * κ)

def dualLat {N : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin N))) : Set (EuclideanSpace ℝ (Fin N)) :=
  {y | ∀ x ∈ L, ∃ z : ℤ, inner ℝ x y = (z : ℝ)}

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.WwCauchyBinet
noncomputable section

namespace PI.WwCauchyBinet

namespace KM

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)

def ColChoice (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def nablaX (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) : MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) =>
    (MvPolynomial.X (s, (i : ℕ), J s c k) : MvPolynomial (Lt × ℕ × Fin N0) ℤ))

end KM

def DeX {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (y : Lt → Fin N → ℕ → k) :
    MvPolynomial (Lt × ℕ × Fin N) k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) =>
    ∑ a : Fin N, MvPolynomial.C (y s a (j : ℕ)) * MvPolynomial.X (s, (i : ℕ), a))

def minY {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (J : KM.ColChoice N nu)
    (y : Lt → Fin N → ℕ → k) : k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) => y s (J s c i) (j : ℕ))

def WwCauchyBinet : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (k : Type) [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (y : Lt → Fin N → ℕ → k),
    DeX N nu y = ∑ᶠ J : KM.ColChoice N nu, MvPolynomial.C (minY N nu J y) *
      MvPolynomial.map (Int.castRingHom k) (KM.nablaX N nu J)

end PI.WwCauchyBinet
end
end

section -- merged from Formalism.PeriodIntegrals.FglGram
noncomputable section

open Classical

namespace PI.FglGram

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

def hP {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] (x y : ι → ℂ_[p] × ℂ_[p]) : ℂ_[p] × ℂ_[p] :=
  ∑ k, x k * (y k).swap

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

section

variable {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) {σ : Type*}

def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a l

def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x ex

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a + lg l b)

def sub (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := pt ex (lg l a - lg l b)

def mulBy (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  pt ex (MvPowerSeries.C c * lg l a)

def lin {ι : Type*} [Fintype ι] (c : ι → ℂ_[p]) (a : ι → MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries σ ℂ_[p] :=
  pt ex (∑ j, MvPowerSeries.C (c j) * lg l (a j))

def phAt (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a ph

def be (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  phAt ph (add l ex a b) - phAt ph a - phAt ph b

end

def PhOn {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) {κ ι : Type*} [Fintype κ] [Fintype ι]
    (b : ι → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries ι ℂ_[p] :=
  ∑ k, phAt ph (lin l ex (fun e => (b e k).1) (fun e => Xv e))

def GramRhs {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) {κ : Type*} [Fintype κ] {k : ℕ}
    (A : Fin k → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (Fin k) ℂ_[p] :=
  ∑ j, MvPowerSeries.C (hP (A j) (A j)).1 * phAt ph (Xv j) +
    ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), be l ex ph (mulBy l ex (hP (A j) (A j')).1 (Xv j)) (Xv j')

def Data {p : ℕ} [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) : Prop :=
  PowerSeries.constantCoeff ex = 0 ∧ PowerSeries.subst ex l = PowerSeries.X ∧ PowerSeries.constantCoeff ph = 0

def CubeRelationOfParallelogram : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), Data l ex ph →
    Simeq (phAt ph (add l ex (Xv 0) (Xv 1)) + phAt ph (sub l ex (Xv 0) (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (2 * phAt ph (Xv 0) + 2 * phAt ph (Xv 1)) →
    Simeq (phAt ph (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2)) + phAt ph (sub l ex (Xv 0) (Xv 1)) +
        phAt ph (sub l ex (Xv 1) (Xv 2)) + phAt ph (sub l ex (Xv 2) (Xv 0)) : MvPowerSeries (Fin 3) ℂ_[p])
      (3 * (phAt ph (Xv 0) + phAt ph (Xv 1) + phAt ph (Xv 2))) →
    Simeq (phAt ph (add l ex (add l ex (Xv 0) (Xv 1)) (Xv 2)) - phAt ph (add l ex (Xv 0) (Xv 1)) -
        phAt ph (add l ex (Xv 1) (Xv 2)) - phAt ph (add l ex (Xv 2) (Xv 0)) +
        phAt ph (Xv 0) + phAt ph (Xv 1) + phAt ph (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) 0

def PhGram : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Data l ex ph →
    (∀ α ∈ S, α.swap ∈ S) →
    (∀ α ∈ S, IntegralMv (mulBy l ex α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    (∀ α ∈ S, Simeq (phAt ph (mulBy l ex α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * phAt ph (Xv ()))) →
    (∀ α ∈ S, Simeq (be l ex ph (mulBy l ex α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (be l ex ph (Xv 0) (mulBy l ex α.2 (Xv 1)))) →
    Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)) →
    ∀ (κ : Type) [Fintype κ] (k : ℕ) (A : Fin k → κ → ℂ_[p] × ℂ_[p]), (∀ j i, A j i ∈ S) →
      Simeq (PhOn l ex ph A) (GramRhs l ex ph A)

def GramUnit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), Data l ex ph →
    ∀ (n : ℕ) (de : Fin n → Fin n → ℂ_[p] × ℂ_[p]), (∀ i j, hP (de i) (de j) = if i = j then 1 else 0) →
      GramRhs l ex ph de = ∑ j, phAt ph (Xv j)

end PI.FglGram
end
end
