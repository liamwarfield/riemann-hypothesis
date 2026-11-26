module

public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.PeriodIntegrals.QuotInv
public import Formalism.PeriodIntegrals.UnimodLocStd
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.PeriodIntegrals.UnimodGenus

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.KFinSmooth
noncomputable section

namespace PI

open PI.UpqRep

def KFinSmooth : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDSHpk k r ε lam σ →
    ∀ v : H, IsKFinHpk (k := k) (r := r) σ v → v ∈ smoothVecs (k := k) (r := r) σ

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.IsLowUnitH
open MeasureTheory Matrix Finset Topology
open scoped InnerProductSpace ContDiff ComplexOrder

noncomputable section

namespace PI.UpqRep

def rdM {m : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (X : Matrix (Fin m) (Fin m) ℂ)
    (f : Matrix (Fin m) (Fin m) ℂ → V) : Matrix (Fin m) (Fin m) ℂ → V :=
  fun g => deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0

section KF

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsKFin {n : ℕ} (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧ IsKStableOn ε σ S

end KF

def thetaJ {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  -(Jm ε * Xᴴ * Jm ε)

def reJ {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (X + thetaJ ε X)

def imJ {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (-(Complex.I / 2)) • (X - thetaJ ε X)

def rdC {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => rdM (reJ ε X) f g + Complex.I * rdM (imJ ε X) f g

def rdCWord {n : ℕ} (ε : Fin n → Bool) :
    List (Matrix (Fin n) (Fin n) ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ) → Matrix (Fin n) (Fin n) ℂ → ℂ
  | [], f => f
  | X :: w, f => rdC ε X (rdCWord ε w f)

def gelfandOp {n : ℕ} (ε : Fin n → Bool) (k : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => ∑ a : Fin (k + 1) → Fin n,
    rdCWord ε (List.ofFn fun i : Fin (k + 1) => Matrix.single (a i) (a (finRotate (k + 1) i)) (1 : ℂ)) f g

def IsEquiv {n : ℕ} {H' H : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ε : Fin n → Bool) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ U : H' ≃ₗᵢ[ℂ] H, ∀ g ∈ UJset ε, ∀ v : H', U (σ' g v) = σ g (U v)

section Eig

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def Eig (ε : Fin n → Bool) (c : ℕ → ℂ) (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ x y : H, ∃ F : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
    (∀ g ∈ UJset ε, F g = ⟪x, Ψ g y⟫_ℂ) ∧ ∀ (k : ℕ), ∀ g ∈ UJset ε, gelfandOp ε k F g = c k * F g

end Eig

def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val, by omega⟩

def wI (k r : ℕ) (j : Fin (k + 1)) : Fin (2 * r + k + 1) := ⟨r + j.val, by omega⟩

def esI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨2 * r + k - a.val, by omega⟩

def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ := Pi.single i 1

def herm {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ := star w ⬝ᵥ (H *ᵥ v)

def inWb (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → v i = 0

def Tz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : ℝ := -(herm (Hpk k r) z z).re

def UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    g *ᵥ z = z}

def blockW (k r : ℕ) (h : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  fun i j =>
    if hi : r ≤ i.val ∧ i.val < r + k then
      (if hj : r ≤ j.val ∧ j.val < r + k then h ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ else 0)
    else (if i = j then 1 else 0)

def IsFrameW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  g ∈ UH (Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
      g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    g *ᵥ (((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) = z

section Second

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsHCTypeW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ g, IsFrameW k r z g ∧ IsHCTypeU k u (fun h => π (g * blockW k r h * g⁻¹))

def InLieHpk (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  Xᴴ * Hpk k r + Hpk k r * X = 0

def dsig (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : H) : H :=
  deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) 0

def dsigW (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) :
    List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) → H → H
  | [], v => v
  | X :: w, v => dsig σ X (dsigW σ w v)

def IsLowUnitH (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H) : Prop :=
  ∃ P, IsCayleyU k r ε P ∧ IsLowUnit ε lam (fun g => σ (P⁻¹ * g * P)) w

end Second

end PI.UpqRep

end
end

section -- merged from Formalism.PeriodIntegrals.QuotSetU
open MeasureTheory Matrix

noncomputable section

namespace PI

namespace QuotSetU

def herm {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ := star w ⬝ᵥ (H *ᵥ v)

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

def inWb (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → v i = 0

def Tz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : ℝ := -(herm (Hpk k r) z z).re

def Nset (k r : ℕ) : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      g i (eI k r a) = if i = eI k r a then 1 else 0) ∧
    (∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      g i j = if i = j then 1 else 0)}

def UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    g *ᵥ z = z}

def Sset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {s | ∃ h ∈ UWset k r z, ∃ m ∈ Nset k r, s = h * m}

end QuotSetU


open QuotSetU in
def QuotSetU : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    IsMatGroup (UH (Hpk k r)) ∧ IsMatGroup (Sset k r z) ∧ Sset k r z ⊆ UH (Hpk k r) ∧
    (∀ μG : Measure (MtM (2 * r + k + 1)), IsHaarOnM (UH (Hpk k r)) μG → IsRightInvM (UH (Hpk k r)) μG) ∧
    (∀ μS : Measure (MtM (2 * r + k + 1)), IsHaarOnM (Sset k r z) μS → IsRightInvM (Sset k r z) μS)

end PI

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryApproxFin
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI.UnitaryApproxFin

def UnitaryApproxFin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    (∀ e, σ (σ e) = e) → (∃ θ, σ θ ≠ θ) → PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J → IsUnit J.det →
    ∀ (T : Finset (HeightOneSpectrum (𝓞 F)))
      (g : (v : HeightOneSpectrum (𝓞 F)) → GL n (E ⊗[F] v.adicCompletion F)),
      (∀ v ∈ T, g v ∈ PI.UnitaryApproxDefs.UPts σ J (v.adicCompletion F)) → ∀ D : 𝓞 F, D ≠ 0 →
    ∃ γ ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J, ∀ v ∈ T, ∀ i j,
      ∃ s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (v.adicCompletion F) (PI.UnitaryApproxDefs.intOE E) (v.adicCompletionIntegers F).toSubring,
        ((g v : GL n (E ⊗[F] v.adicCompletion F)) : Matrix n n (E ⊗[F] v.adicCompletion F)) i j -
            PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) ((γ : Matrix n n E) i j) =
          PI.UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (D : F)) * s

end PI.UnitaryApproxFin
end
end

section -- merged from Formalism.PeriodIntegrals.SwSand
noncomputable section

open Matrix MeasureTheory Filter Topology Classical
open scoped ENNReal NNReal

namespace PI.SwSand

open PI.SwBig

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

abbrev Mt (k r : ℕ) := Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ

def realifyFun {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : Fin m × Fin m × Bool → ℝ :=
  fun p => if p.2.2 then (X p.1 p.2.1).im else (X p.1 p.2.1).re

def unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ⟨x (i, j, false), x (i, j, true)⟩

def lieOf {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ S}

def lieE {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Submodule ℝ (EuclideanSpace ℝ (Fin m × Fin m × Bool)) :=
  Submodule.span ℝ ((fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieOf S)

variable {k r : ℕ}

def dg (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℕ :=
  if i.val < r then i.val else if i.val ≤ r + k then r else i.val - k

def Fil (p : ℕ) (X : Mat k r) : Prop := ∀ i j, dg k r j < dg k r i + p → X i j = 0

theorem Fil.add {p : ℕ} {X Y : Mat k r} (hX : Fil p X) (hY : Fil p Y) : Fil p (X + Y) := by
  unfold PI.SwSand.Fil at hX hY ⊢
  intro i j h
  rw [Matrix.add_apply, hX i j h, hY i j h, add_zero]

theorem Fil.smul {p : ℕ} {X : Mat k r} (c : ℂ) (hX : Fil p X) : Fil p (c • X) := by
  unfold PI.SwSand.Fil at hX ⊢
  intro i j h
  rw [Matrix.smul_apply, hX i j h, smul_zero]

theorem Fil.zero (p : ℕ) : Fil p (0 : Mat k r) := by
  unfold PI.SwSand.Fil
  intro i j _
  exact Matrix.zero_apply i j

def adjH (X : Mat k r) : Mat k r := Hpk k r * Xᴴ * Hpk k r

theorem adjH_add (X Y : Mat k r) : adjH (X + Y) = adjH X + adjH Y := by
  simp only [adjH, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem adjH_smul (c : ℂ) (X : Mat k r) : adjH (c • X) = star c • adjH X := by
  simp only [adjH, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]

def lieN (k r : ℕ) : Set (Mat k r) := {X | Fil 1 X ∧ adjH X + X = 0}

theorem lieN_smul {X : Mat k r} (hX : X ∈ lieN k r) (t : ℝ) : ((t : ℂ) • X) ∈ lieN k r := by
  obtain ⟨h1, h2⟩ := hX
  show Fil 1 ((t : ℂ) • X) ∧ adjH ((t : ℂ) • X) + (t : ℂ) • X = 0
  refine ⟨h1.smul _, ?_⟩
  rw [adjH_smul, Complex.star_def, Complex.conj_ofReal, ← smul_add, h2, smul_zero]

theorem lieN_add {X Y : Mat k r} (hX : X ∈ lieN k r) (hY : Y ∈ lieN k r) : X + Y ∈ lieN k r := by
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  show Fil 1 (X + Y) ∧ adjH (X + Y) + (X + Y) = 0
  refine ⟨hX1.add hY1, ?_⟩
  rw [adjH_add, add_add_add_comm, hX2, hY2, add_zero]

theorem zero_mem_lieN : (0 : Mat k r) ∈ lieN k r := by
  show Fil 1 (0 : PI.SwBig.Mat k r) ∧ adjH (0 : PI.SwBig.Mat k r) + 0 = 0
  exact ⟨PI.SwSand.Fil.zero 1, by simp [adjH]⟩

def lieNS (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := lieN k r
  add_mem' := lieN_add
  zero_mem' := zero_mem_lieN
  smul_mem' := fun c X hX => by
    show c • X ∈ lieN k r
    rw [← Complex.coe_smul]; exact lieN_smul hX c

def RL : Mat k r →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) where
  toFun X := (WithLp.equiv 2 _).symm (realifyFun X)
  map_add' X Y := by
    ext p
    rcases p with ⟨i, j, b⟩
    cases b <;> simp [realifyFun]
  map_smul' c X := by
    ext p
    rcases p with ⟨i, j, b⟩
    cases b <;> simp [realifyFun]

def expBall (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (ρ : ℝ) : Set (Mt k r) :=
  (fun x : lieE S =>
      fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) '' Metric.ball 0 ρ

def gBall (k r : ℕ) (ρ : ℝ) : Set (Mt k r) := expBall (k := k) (r := r) (UH (Hpk k r)) ρ

def rhoS (k r : ℕ) (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (x : Mt k r) : ℝ≥0∞ :=
  ⨅ (Y : lieE S)
    (_ : (fun i j => NormedSpace.exp (unrealify (Y : EuclideanSpace ℝ _)) i j : Mt k r) = x),
    (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)

def Qf (k r : ℕ) (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r) : ℝ≥0∞ :=
  rhoS k r (Nset k r) n ^ 2 + ENNReal.ofReal (2 * ∑ a, ‖c a - 1‖ ^ 2) + rhoS k r (UWb k r) m ^ 2 +
    rhoS k r (Nset k r) n' ^ 2

def Psi (k r : ℕ) (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r) : Mt k r :=
  fun i j => (w0B k r * (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹)) i j

def Sandwich : Prop :=
  ∀ (k r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
    ∀ (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r), Matrix.of n ∈ Nset k r → Matrix.of m ∈ UWb k r →
      Matrix.of n' ∈ Nset k r →
      (Psi k r n c m n' ∈ gBall k r ρ → Qf k r n c m n' < ENNReal.ofReal (((1 + ε) * ρ) ^ 2)) ∧
      (Qf k r n c m n' < ENNReal.ofReal (((1 - ε) * ρ) ^ 2) → Psi k r n c m n' ∈ gBall k r ρ)

def Mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

def uH (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | adjH X + X = 0}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_ofPred_eq] at *
    rw [adjH_add, show adjH X + adjH Y + (X + Y) = (adjH X + X) + (adjH Y + Y) by abel, hX, hY, add_zero]
  zero_mem' := by simp [adjH]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_ofPred_eq] at *
    rw [← Complex.coe_smul, adjH_smul, Complex.star_def, Complex.conj_ofReal, ← smul_add, hX, smul_zero]

def uWb (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | adjH X + X = 0 ∧ ∀ i j, ¬ (Mid k r i ∧ Mid k r j) → X i j = 0}
  add_mem' := by
    intro X Y hX hY
    refine ⟨(uH k r).add_mem hX.1 hY.1, fun i j h => ?_⟩
    simp [hX.2 i j h, hY.2 i j h]
  zero_mem' := ⟨(uH k r).zero_mem, fun i j _ => rfl⟩
  smul_mem' := by
    intro c X hX
    refine ⟨(uH k r).smul_mem c hX.1, fun i j h => ?_⟩
    simp [hX.2 i j h]

def Vs (k r : ℕ) : Submodule ℝ (Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) :=
  (lieNS k r).prod ((⊤ : Submodule ℝ (Fin r → ℂ)).prod ((uWb k r).prod (lieNS k r)))

def LieG : Prop := ∀ k r : ℕ, lieE (UH (Hpk k r)) = (uH k r).map RL

def LieWb : Prop := ∀ k r : ℕ, (∀ Z ∈ uWb k r, NormedSpace.exp Z ∈ UWb k r) ∧
  lieE (UWb k r) = (uWb k r).map RL

def LIso : Prop := ∀ k r : ℕ, (∀ v ∈ Vs k r, Lm k r v ∈ uH k r) ∧ (∀ Y ∈ uH k r, ∃ v ∈ Vs k r, Lm k r v = Y) ∧
  ∀ v ∈ Vs k r, ‖RL (Lm k r v)‖ ^ 2 = ‖RL v.1‖ ^ 2 + 2 * ∑ a, ‖v.2.1 a‖ ^ 2 + ‖RL v.2.2.1‖ ^ 2 + ‖RL v.2.2.2‖ ^ 2

def LieEN : Prop := ∀ k r : ℕ, lieE (Nset k r) = (lieNS k r).map RL

def ExpN : Prop := ∀ (k r : ℕ) (X : Mat k r), X ∈ lieN k r → NormedSpace.exp X ∈ Nset k r

def SandwichOf : Prop :=
  LieG → LieWb → GaussUniq → PhiForm → BigCellG → PhiDeriv → LIso → LongWeylElementSquare → LieEN → ExpN → Sandwich

end PI.SwSand
end
end

section -- merged from Formalism.PeriodIntegrals.AreaLat
open Classical

namespace PI

def AreaLat : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 →
    area (lat2 w₁ w₂) = |((starRingEnd ℂ) w₁ * w₂).im| ∧
    ∀ a ∈ lat2 w₁ w₂, ∀ b ∈ lat2 w₁ w₂, ∃ n : ℤ, ((starRingEnd ℂ) a * b).im = n * ((starRingEnd ℂ) w₁ * w₂).im

end PI
end

section -- merged from Formalism.PeriodIntegrals.SelfDualOfDiff
noncomputable section
open NumberField

namespace PI.KerIso

def SplitOfJacobi : Prop :=
  ∀ (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (cj : E ≃ₐ[ℚ] E) (d p : ℕ) (s : K),
    d % 8 = 7 → s * s = -(d : K) → cj (algebraMap K E s) = -algebraMap K E s → p.Prime →
    (p = 2 ∨ jacobiSym (-(d : ℤ)) p = 1) → SplitsAt K cj p

end PI.KerIso
end
end

section -- merged from Formalism.PeriodIntegrals.SymDist
open Matrix

noncomputable section

namespace PI

def symD {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) : ℝ :=
  sInf {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
    ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = k * NormedSpace.exp X ∧
    t = Real.sqrt (Formalism.REAL.hs X)}

def SymDist : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g k : Formalism.REAL.UJ ε), symD ε (g * k) ≤ symD ε g + symD ε k

end PI

end
end

section -- merged from Formalism.PeriodIntegrals.HCMult
noncomputable section

namespace PI

open PI.UpqRep

def HCMult : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S →
      FiniteDimensional ℂ (eqImg (fun k : KG ε => σ (toMK k)) S)

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.WeylForK
noncomputable section

namespace PI

open PI.UpqRep

def nPl {N : ℕ} (ε : Fin N → Bool) : ℕ := (Finset.univ.filter (fun a => ε a = true)).card

def nMi {N : ℕ} (ε : Fin N → Bool) : ℕ := (Finset.univ.filter (fun a => ε a = false)).card

def WeylForK : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (Λ : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H),
    IsURepOn (Kset ε) σ → IsKTypeOf ε σ Λ S →
    (Module.finrank ℂ S : ℝ) =
      (∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b => a < b ∧ ε a = ε b),
        ((Λ + rhoC ε) a - (Λ + rhoC ε) b)) /
      ((∏ i ∈ Finset.range (nPl ε), (i.factorial : ℝ)) * ∏ i ∈ Finset.range (nMi ε), (i.factorial : ℝ))

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.FinOrdAd
noncomputable section

namespace PI

open NumberField IsDedekindDomain TensorProduct Matrix ComplexOrder

namespace FinOrdAdDefs

section UnitaryGroups

variable {A : Type} [CommRing A] {ι : Type} [Fintype ι] [DecidableEq ι]

def cT (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

def IsHerm (σ : A →+* A) (J : Matrix ι ι A) : Prop := cT σ J = J

def hform (σ : A →+* A) (J : Matrix ι ι A) (x y : ι → A) : A :=
  ∑ i, ∑ j, σ (x i) * J i j * y j

theorem cT_mul (σ : A →+* A) {m p q : Type} [Fintype p] (M : Matrix m p A) (N : Matrix p q A) :
    cT σ (M * N) = cT σ N * cT σ M := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one (σ : A →+* A) : cT σ (1 : Matrix ι ι A) = 1 := by
  simp [cT]

def UJ (σ : A →+* A) (J : Matrix ι ι A) : Subgroup (GL ι A) where
  carrier := {g | cT σ (g : Matrix ι ι A) * J * (g : Matrix ι ι A) = J}
  one_mem' := by simp [cT_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    calc cT σ ((a : Matrix ι ι A) * (b : Matrix ι ι A)) * J * ((a : Matrix ι ι A) * (b : Matrix ι ι A))
        = cT σ (b : Matrix ι ι A) * (cT σ (a : Matrix ι ι A) * J * (a : Matrix ι ι A)) *
            (b : Matrix ι ι A) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    calc cT σ ((g⁻¹ : GL ι A) : Matrix ι ι A) * J * ((g⁻¹ : GL ι A) : Matrix ι ι A)
        = cT σ ((g⁻¹ : GL ι A) : Matrix ι ι A) * (cT σ (g : Matrix ι ι A) * J * (g : Matrix ι ι A))
            * ((g⁻¹ : GL ι A) : Matrix ι ι A) := by rw [hg]
      _ = cT σ ((g : Matrix ι ι A) * ((g⁻¹ : GL ι A) : Matrix ι ι A)) * J
            * ((g : Matrix ι ι A) * ((g⁻¹ : GL ι A) : Matrix ι ι A)) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]

def bc {B : Type} [CommRing B] (φ : A →+* B) : GL ι A →* GL ι B :=
  Units.map (RingHom.mapMatrix φ).toMonoidHom

end UnitaryGroups

section Points

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {ι : Type} [Fintype ι] [DecidableEq ι]

def sigR (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] : E ⊗[F] R →+* E ⊗[F] R :=
  (Algebra.TensorProduct.map σ (AlgHom.id F R)).toRingHom

def inclE (R : Type) [CommRing R] [Algebra F R] : E →+* E ⊗[F] R :=
  Algebra.TensorProduct.includeLeftRingHom

def UPts (σ : E →ₐ[F] E) (J : Matrix ι ι E) (R : Type) [CommRing R] [Algebra F R] :
    Subgroup (GL ι (E ⊗[F] R)) := UJ (sigR σ R) (J.map (inclE (F := F) R))

def IsDef (σ : E →ₐ[F] E) (J : Matrix ι ι E) : Prop :=
  ∀ ι' : F →+* ℝ,
    (∀ x : ι → E, x ≠ 0 → ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x ∧ 0 < ι' a) ∨
    (∀ x : ι → E, x ≠ 0 → ∃ a : F, algebraMap F E a = hform (σ : E →+* E) J x x ∧ ι' a < 0)

@[reducible] def tensTop (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (E ⊗[F] R) :=
  letI : Algebra R (E ⊗[F] R) := Algebra.TensorProduct.rightAlgebra
  moduleTopology R (E ⊗[F] R)

end Points

end FinOrdAdDefs

open FinOrdAdDefs in
def FinOrdAd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  (∀ φ : F →+* ℂ, ∃ r : F →+* ℝ, ∀ x, φ x = (r x : ℂ)) →
  ∀ (σ : E →ₐ[F] E) (k : ℕ) (J : Matrix (Fin k) (Fin k) E), IsHerm (σ : E →+* E) J → IsDef σ J →
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  ∀ U : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
    U ≤ UPts σ J (FiniteAdeleRing (𝓞 F) F) →
    IsCompact (U : Set (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) →
  ∀ y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F),
  ∀ γ ∈ UJ (σ : E →+* E) J,
    bc (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)) γ ∈ U.map (MulAut.conj y).toMonoidHom →
    IsOfFinOrder γ

open FinOrdAdDefs in
def DefPosDef : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  (∀ φ : F →+* ℂ, ∃ r : F →+* ℝ, ∀ x, φ x = (r x : ℂ)) →
  ∀ (σ : E →ₐ[F] E) (k : ℕ) (J : Matrix (Fin k) (Fin k) E), 0 < k → IsHerm (σ : E →+* E) J → IsDef σ J →
    (∀ (φ : E →+* ℂ) (x : E), φ (σ x) = (starRingEnd ℂ) (φ x)) ∧
    (∀ φ : E →+* ℂ, (J.map φ).PosDef ∨ (-(J.map φ)).PosDef)

open FinOrdAdDefs in
def TensCpctDen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
  letI := tensTop (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  ∀ C : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F), IsCompact C →
    ∃ N : ℕ, 0 < N ∧ ∀ e : E, inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F) e ∈ C → IsIntegral ℤ ((N : E) * e)

end PI
end
end
