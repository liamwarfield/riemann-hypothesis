module

public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
noncomputable section

namespace Formalism.MainNotions.PlaceDegreeData

open MeasureTheory NumberField Matrix Finset IsDedekindDomain
open scoped InnerProductSpace ComplexOrder
open Formalism.MainNotions.S

def qOf {n : ℕ} (ε : Fin n → Bool) : ℕ := (univ.filter fun a => ε a = false).card

def pOf {n : ℕ} (ε : Fin n → Bool) : ℕ := (univ.filter fun a => ε a = true).card

def decBound {n : ℕ} (q : ℕ) (h : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.exp (-(h / 8) * min (Formalism.REAL.hs X) (Real.sqrt (Formalism.REAL.hs X) / Real.sqrt (2 * (q : ℝ))))

def fdegAll (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    (w : ∀ v, H v) : ℝ :=
  ∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)

def HidaSetting (I : AutInst) (n₀ : ℕ) (A b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ)
    (μf : Measure I.Gf) (g g₀ : ℕ) (e : I.Gf → ℂ) : Prop :=
  n₀ ≤ I.n ∧ (∃ p q : ℕ, (∀ v, I.pAt v = p ∧ I.qAt v = q) ∧ q ^ 2 ≤ I.n) ∧ 2 ≤ b ∧
    Real.log (Real.log I.rd) ≤ I.n ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (lam v)) ∧ (∀ v a, |lam v a| ≤ b ^ 2) ∧
    I.IsAdmIdem μf g g₀ e ∧ 1 ≤ g ∧ (g : ℝ) ≤ b ^ A ∧ g₀.Prime ∧ 4 * I.n < g₀ ∧ SplitsCompl I.E g₀

def q0At (I : AutInst) (v : InfinitePlace I.F) : ℕ := min (I.pAt v) (I.qAt v)

section HC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end HC

def CountData (I : AutInst) {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] (lam : InfinitePlace I.F → Fin I.n → ℝ)
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (σs : I.Ginf → (Hs →L[ℂ] Hs))
    (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (e : I.Gf → ℂ)
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) : Prop :=
  (∀ v, IsDS (I.ε v) (lam v) (σ v)) ∧ (∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v)) ∧
    I.IsHilbTensor σ σs tens ∧ μf.IsHaarMeasure ∧ I.IsFundDom (I.muA μf) fund ∧
    I.IsRightReg μf fund R ∧ I.IsRConvF μf fund R e Re

def phA {G : Type*} [Group G] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (d : ℝ)
    (σ : G →* (H →L[ℂ] H)) (w : H) : G → ℂ :=
  fun g => (d : ℂ) * star ⟪w, σ g w⟫_ℂ

def IsOpIntA {G : Type*} [Group G] [MeasurableSpace G] (μ : Measure G) {Hp : Type*} [NormedAddCommGroup Hp]
    [InnerProductSpace ℂ Hp] (π : G →* (Hp →L[ℂ] Hp)) (φ : G → ℂ) (P : Hp →L[ℂ] Hp) : Prop :=
  Integrable φ μ ∧ ∀ x y : Hp, ⟪x, P y⟫_ℂ = ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ

def PointsLemma (_D : Formalism.BasicNotions.D7) (n₀ : ℕ) (A C c cb : ℝ) : Prop :=
  ∀ (I : AutInst) (b : ℝ) (lam : InfinitePlace I.F → Fin I.n → ℝ) (g g₀ : ℕ) (e : I.Gf → ℂ)
    (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    [∀ v, CompleteSpace (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v)
    (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (μf : Measure I.Gf) [SigmaFinite μf]
    (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
    (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund) (h : ℝ),
    HidaSetting I n₀ A b lam μf g g₀ e → CountData I lam σ w σs tens μf fund R e Re →
    (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) →
    C * (I.n : ℝ) ^ 19 * (I.f : ℝ) ^ 5 * Real.log (b * I.rd) ≤ h →
    Real.log (I.f : ℝ) ≤ Real.sqrt (I.n : ℝ) →
    Real.log (Real.log b) ≤ cb * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ) →
    |(I.Dcount σs μf fund R Re : ℝ) - I.Dstar (fdegAll I σ w) μf fund e| ≤
      Real.exp (-c * (I.n : ℝ) * (I.f : ℝ) * Real.log (I.n : ℝ)) * I.Dstar (fdegAll I σ w) μf fund e

def RowsTie (D : Formalism.BasicNotions.D7) (X : RowsAut) : Prop :=
  (∃ pl : InfinitePlace X.I.F ≃ D.what₂.Tau, AutTie D X pl) ∧ (∀ v, Formalism.QuantumDeterminants.IsHCParam (X.lam v)) ∧
    (SplitsCompl D.host.E (D.host.g 0) → SplitsCompl X.I.E X.g₀)

end Formalism.MainNotions.PlaceDegreeData
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff ENNReal
open Formalism.MainNotions.S

noncomputable section

namespace Formalism.MainNotions.CayleySignature

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def lam48 (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Fin (2 * r + k + 1) → ℝ :=
  fun i => if h : i.val < k - 1 then v ⟨i.val, h⟩
    else -b ⟨i.val - (k - 1), by have := i.isLt; omega⟩

def eps48 (k r : ℕ) : Fin (2 * r + k + 1) → Bool :=
  fun i => if i.val < k - 1 then true else decide ((i.val - (k - 1)) % 2 = 0)

def InterlacingCondition (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  (∀ i : Fin (k - 1), v i < u ⟨i.val, by have := i.isLt; omega⟩ ∧
      u ⟨i.val + 1, by have := i.isLt; omega⟩ < v i) ∧
    ∀ h : 0 < k, -b ⟨0, by omega⟩ < u ⟨k - 1, by omega⟩

def HalfIntegralDifference (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∀ i s, ∃ j : ℤ, u i - lam48 k r v b s = (j : ℝ) + 1 / 2

def rk48 (k r : ℕ) : ℕ := 2 * r + k + 1

def GapBig (k r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∃ t : ℕ, Odd t ∧ rk48 k r + 5 ≤ t ∧ 1801 ≤ rk48 k r + t ∧
    ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
      2 * ((rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 < b ⟨j.val + 1, hj⟩ - b j

def GapC (C : ℝ) (k r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2),
    C * (rk48 k r : ℝ) ^ 3 < b ⟨j.val + 1, hj⟩ - b j

def LowGapGe (h : ℝ) (r : ℕ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∀ (j : Fin (2 * r + 2)) (hj : j.val + 1 < 2 * r + 2), h ≤ b ⟨j.val + 1, hj⟩ - b j

def RealPlaceNumericalSetting (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ)
    (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  1 ≤ k ∧ Even k ∧ Formalism.QuantumDeterminants.inWb k r z ∧ 0 < Formalism.QuantumDeterminants.Tz k r z ∧ (∀ a, c a ≠ 0) ∧
    Formalism.QuantumDeterminants.IsHCParam u ∧ Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) ∧ InterlacingCondition k r u v b ∧
    HalfIntegralDifference k r u v b ∧ GapBig k r b

end Formalism.MainNotions.CayleySignature
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate
open MeasureTheory Matrix Filter Topology NumberField
open scoped ContDiff ComplexOrder nonZeroDivisors

noncomputable section

namespace Formalism.MainNotions.S.GramWordSpace

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def IsDiffOpOn {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ) (U : Set (Fin m → ℂ))
    (R : ((Fin m → ℂ) → E) → (Fin m → ℂ) → E) : Prop :=
  ∃ a : ∀ k : Fin (d + 1), (Fin m → ℂ) → (ContinuousMultilinearMap ℝ (fun _ : Fin k.val => (Fin m → ℂ)) E →L[ℝ] E),
    (∀ k, ContDiffOn ℝ ∞ (a k) U) ∧
    ∀ (φ : (Fin m → ℂ) → E), ∀ x ∈ U, ContDiffAt ℝ d φ x → R φ x = ∑ k : Fin (d + 1), a k x (iteratedFDeriv ℝ k.val φ x)

def IsRadQQd (L : Lev) (R : ℂ → Matrix (Fin 2) (Fin 2) L.POp) : Prop :=
  L.IsRadQQ R ∧ ∀ (Y : ℂ) (a b : Fin 2), IsDiffOpOn (2 * L.r + L.k0 + 2) L.BD (R Y a b)

abbrev GFn {k0 r : ℕ} (L : LocBessel (k0 + 1) r) :=
  Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)

abbrev Sec (k0 : ℕ) := ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ

export Formalism.MainNotions.S.UnitaryLevelOperators (levOf headEl cutF)

def lev {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (μsec : Sec k0) (j : ℕ) (hj : j ≤ r) : Lev :=
  (levOf L μsec).down j (r - j) (by show j + (r - j) = r; omega)

def headAt (k r j : ℕ) (hj : j ≤ r) (h : Matrix (Fin j) (Fin j) ℂ)
    (g : Matrix (Fin (2 * (r - j) + k + 1)) (Fin (2 * (r - j) + k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  fun p q => headEl k j (r - j) h g (Fin.cast (by omega) p) (Fin.cast (by omega) q)

def fullPt {r j : ℕ} (hj : j ≤ r) (p : Point ℂ j) : Point ℂ (r + 1) :=
  ⟨p.1 ++ List.replicate (r + 1 - j) ((1 : ℂ), 1), by
    refine ⟨fun b hb => ?_, ?_⟩
    · rcases List.mem_append.1 hb with hb | hb
      · exact p.2.1 b hb
      · rw [List.eq_of_mem_replicate hb]; exact ⟨one_ne_zero, le_rfl⟩
    · simp [p.2.2]; omega⟩


open Classical in
def orbJ {k r : ℕ} (L : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : L.Wq →L[ℂ] L.Wp :=
  if h : ∃ ν : Measure (PairSp k r), ∃ μR : Measure (Mt k r), IsRootMeas L γ g μR ∧ IsOrbQuot L g μR ν then
    OrbInt L F g h.choose else 0

def sliceJ {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (μsec : Sec k0) (j : ℕ) (hj : j ≤ r) (F : GFn L) (p : Point ℂ j) :
    (lev L μsec j hj).GF :=
  fun g => orbJ L F (fullPt hj p) (headAt (k0 + 1) r j hj (ptMat p) g)

def IsCellOp (Lt : Lev) (j : ℕ) (hj : j ≤ Lt.r) (Θ : Lt.GF → Lt.GF) : Prop :=
  Lt.IsInv Θ ∧ ∃ (N : ℕ) (ws : Fin N → List (Fin (2 * Lt.r + (Lt.k0 + 1) + 1) × Fin (2 * Lt.r + (Lt.k0 + 1) + 1)))
    (a : Fin N → Mat Lt.k0 Lt.r → (Lt.Hom →L[ℂ] Lt.Hom)),
    (∀ n, ∃ U : Set (Mat Lt.k0 Lt.r), IsOpen U ∧
      UH (Hpk (Lt.k0 + 1) Lt.r) ∩ {g | Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g ⟨j, by omega⟩ ≠ 0} ⊆ U ∧
      ContDiffOn ℝ ∞ (a n) U) ∧
    ∀ F : Lt.GF, SmoothOnH (Hpk (Lt.k0 + 1) Lt.r) F → ∀ g ∈ UH (Hpk (Lt.k0 + 1) Lt.r),
      Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g ⟨j, by omega⟩ ≠ 0 → Θ F g = ∑ n, a n g (Lt.Eword (ws n) F g)

def minorsNe (Lt : Lev) (E : List ℕ) : Set (Mat Lt.k0 Lt.r) :=
  {g | ∀ l ∈ E, ∀ hl : l < Lt.r + 2, Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g ⟨l, hl⟩ ≠ 0}

def CkAt (Lt : Lev) (o : ℕ) (F : Lt.GF) (g₀ : Mat Lt.k0 Lt.r) : Prop :=
  ∃ (U : Set (Mat Lt.k0 Lt.r)) (F' : Lt.GF), IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ o F' U ∧
    ∀ g ∈ U, g ∈ UH (Hpk (Lt.k0 + 1) Lt.r) → F g = F' g

def IsInvC (Lt : Lev) (o : ℕ) (Θ : Lt.GF → Lt.GF) : Prop :=
  ∀ h ∈ UWset (Lt.k0 + 1) Lt.r Lt.z, ∀ n ∈ Nset (Lt.k0 + 1) Lt.r, ∀ h' ∈ UWset (Lt.k0 + 1) Lt.r Lt.z',
    ∀ n' ∈ Nset (Lt.k0 + 1) Lt.r, ∀ F : Lt.GF, (∀ g ∈ UH (Hpk (Lt.k0 + 1) Lt.r), CkAt Lt o F g) →
      ∀ g ∈ UH (Hpk (Lt.k0 + 1) Lt.r), Θ (Lt.act h n h' n' F) g = Lt.act h n h' n' (Θ F) g

def BigPosR (Lt : Lev) : Set (Mat Lt.k0 Lt.r) :=
  {g | g ∈ UH (Hpk (Lt.k0 + 1) Lt.r) ∧ (∀ l : Fin (Lt.r + 2), Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g l ≠ 0) ∧
    0 < Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g}

def IsCellOpAt (Lt : Lev) (E : List ℕ) (o : ℕ) (dP : ℝ) (Θ : Lt.GF → Lt.GF) : Prop :=
  Lt.IsInv Θ ∧ ∃ (N : ℕ) (ws : Fin N → List (Fin (2 * Lt.r + (Lt.k0 + 1) + 1) × Fin (2 * Lt.r + (Lt.k0 + 1) + 1)))
    (a : Fin N → Mat Lt.k0 Lt.r → (Lt.Hom →L[ℂ] Lt.Hom)),
    (∀ n, (ws n).length ≤ o) ∧
    (∀ n, ∃ U : Set (Mat Lt.k0 Lt.r), IsOpen U ∧
      UH (Hpk (Lt.k0 + 1) Lt.r) ∩ minorsNe Lt E ∩ {g | 0 < Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g} ⊆ U ∧
      ContDiffOn ℝ ∞ (a n) U) ∧
    (∀ n, ∀ w : List (Fin (2 * Lt.r + (Lt.k0 + 1) + 1) × Fin (2 * Lt.r + (Lt.k0 + 1) + 1)), ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∃ C : ℝ, ∀ g ∈ UH (Hpk (Lt.k0 + 1) Lt.r), ε ≤ Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g →
        (∀ l ∈ E, ∀ hl : l < Lt.r + 2, δ ≤ Complex.normSq (Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g ⟨l, hl⟩)) →
        ‖Lt.EwordV w (a n) g‖ ≤ C * (1 + Lev.matNorm g) ^ (dP + 3 * ((Lt.r : ℝ) + 1) * w.length)) ∧
    IsInvC Lt (Finset.univ.sup fun n => (ws n).length) Θ ∧
    ∀ F : Lt.GF, ∀ g ∈ UH (Hpk (Lt.k0 + 1) Lt.r), g ∈ minorsNe Lt E →
      0 < Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g → CkAt Lt (Finset.univ.sup fun n => (ws n).length) F g →
      Θ F g = ∑ n, a n g (Lt.Eword (ws n) F g)

def RadC (Lt : Lev) (o : ℕ) (Θ : Lt.GF → Lt.GF) (R : Lt.POp) : Prop :=
  ∀ J : Lt.GF, (∀ g ∈ BigPosR Lt, CkAt Lt o J g) →
    (∀ h ∈ UWset (Lt.k0 + 1) Lt.r Lt.z, ∀ n ∈ Nset (Lt.k0 + 1) Lt.r, ∀ h' ∈ UWset (Lt.k0 + 1) Lt.r Lt.z',
      ∀ n' ∈ Nset (Lt.k0 + 1) Lt.r, ∀ g ∈ BigPosR Lt, Lt.act h n h' n' J g = J g) →
    ∀ x ∈ Lt.BD, Lt.B (Θ J) x = R (Lt.B J) x

def IsInvL (Lt : Lev) (o : ℕ) (Θ : Lt.GF → Lt.GF) : Prop :=
  ∀ h ∈ UWset (Lt.k0 + 1) Lt.r Lt.z, ∀ n ∈ Nset (Lt.k0 + 1) Lt.r, ∀ h' ∈ UWset (Lt.k0 + 1) Lt.r Lt.z',
    ∀ n' ∈ Nset (Lt.k0 + 1) Lt.r, ∀ J : Lt.GF, (∀ g ∈ BigPosR Lt, CkAt Lt o J g) →
      ∀ g ∈ BigPosR Lt, Θ (Lt.act h n h' n' J) g = Lt.act h n h' n' (Θ J) g

def IsLetters (Lt : Lev) (j : ℕ) (hj : j ≤ Lt.r) (w : Word) (Θ : AuxiliarySlotStates w.length → Lt.GF → Lt.GF) : Prop :=
  ∀ β, IsCellOp Lt j hj (Θ β) ∧ Lt.Rad (Θ β) (uw (m := Lt.r) (E := Lt.Hom) w j hj β) ∧
    IsCellOpAt Lt [j] (w.length * j) ((w.length * j + w.length * j ^ 2 : ℕ) : ℝ) (Θ β) ∧
    RadC Lt (w.length * j) (Θ β) (uw (m := Lt.r) (E := Lt.Hom) w j hj β) ∧ IsInvL Lt (w.length * j) (Θ β)

def pt0 : Point ℂ 0 := ⟨[], by simp⟩

structure GramMap (k0 r : ℕ) extends ValMap (k0 + 1) r where
  top : ∀ (B : LocBessel (k0 + 1) r), Set ℝ → Word → GFn B → List (ℂ × ℕ) → List (ℂ × ℕ) → ℂ
  top_nil : ∀ (B : LocBessel (k0 + 1) r) (I : Set ℝ) (F : GFn B) (p p' : List (ℂ × ℕ)),
    top B I [] F p p' = hsInner (V B F p) (V B F p')

structure Dat (D : D7) (k0 : ℕ) where
  hk : k0 + 1 = D.R.k
  B : D.what₂.Tau → LocBessel (k0 + 1) D.R.rS
  μsec : D.what₂.Tau → Sec k0
  l : D.what₂.Tau → Fin (k0 + 1)
  a : D.what₂.Tau → ℝ
  b : D.what₂.Tau → ℝ
  a1 : D.what₂.Tau → ℝ
  b1 : D.what₂.Tau → ℝ
  f : ∀ v, GFn (B v)
  R : ∀ v (j : ℕ) (hj : j ≤ D.R.rS), ℂ → Matrix (Fin 2) (Fin 2) (lev (B v) (μsec v) j hj).POp
  Th : ∀ v (j : ℕ) (_ : j ≤ D.R.rS) (w : Word), AuxiliarySlotStates w.length → GFn (B v) → GFn (B v)

abbrev GWord (D : D7) := D.what₂.Tau → Word

abbrev Head (D : D7) (j : ℕ) := D.what₂.Tau → Point ℂ j

def Len {D : D7} (m : ℕ) (w : GWord D) : Prop := ∀ v, (w v).length ≤ m

def NN (D : D7) (Ks : ℕ) : ℕ := 4 * Ks * (D.R.rS + 1)

namespace Dat

variable {D : D7} {k0 : ℕ} (X : Dat D k0)

abbrev lv (v : D.what₂.Tau) (j : ℕ) (hj : j ≤ D.R.rS) : Lev := lev (X.B v) (X.μsec v) j hj

def T (v : D.what₂.Tau) : ℝ := Tz (k0 + 1) D.R.rS (X.B v).z
def T' (v : D.what₂.Tau) : ℝ := Tz (k0 + 1) D.R.rS (X.B v).z'

def I (v : D.what₂.Tau) : Set ℝ := Set.Icc (X.a v) (X.b v)
def I1 (v : D.what₂.Tau) : Set ℝ := Set.Icc (X.a1 v) (X.b1 v)

def sg (v : D.what₂.Tau) : ℝ := sCut (X.B v).u (X.B v).u' (X.I v)

def loc (v : D.what₂.Tau) : LocalDataRealPlace D where
  lam := fun s => (X.B v).lam (Fin.cast (by have := X.hk; omega) s)
  u := fun i => (X.B v).u (Fin.cast X.hk.symm i)
  u' := fun i => (X.B v).u' (Fin.cast X.hk.symm i)
  l := Fin.cast X.hk (X.l v)
  a := X.a v
  b := X.b v
  a1 := X.a1 v
  b1 := X.b1 v

def admitted (w : GWord D) : Prop := ∀ v, Admissible (X.I v) (w v)

def brk (w : GWord D) : ℝ := ∏ v, brkW (X.B v).lam ((w v).map Prod.snd)

def Fv (χ : ℝ → ℝ) (ε : ℝ) (v : D.what₂.Tau) : GFn (X.B v) := cutF (X.B v).z (X.B v).z' χ ε (X.f v)

def gramLow (v : D.what₂.Tau) (j : ℕ) (hj : j ≤ D.R.rS) (w : Word) (F : GFn (X.B v)) (p p' : Point ℂ j) : ℂ :=
  (X.lv v j hj).form ((X.lv v j hj).wmod (X.R v j hj) (X.sg v) (X.B v).u (X.B v).u' w).RR
    (fun β => (X.lv v j hj).B (sliceJ (X.B v) (X.μsec v) j hj (X.Th v j hj w β F) p))
    (fun β => (X.lv v j hj).B (sliceJ (X.B v) (X.μsec v) j hj (X.Th v j hj w β F) p'))

def energy (w : GWord D) (χ : ℝ → ℝ) (ε : ℝ) : ℂ :=
  ∏ v, X.gramLow v 0 (Nat.zero_le _) (w v) (X.Fv χ ε v) pt0 pt0

def jn2 : ℂ := ∏ v, (X.B v).beta (X.μsec v) (X.f v) (X.f v)

def Std (Ks : ℕ) (C₀ Cg : ℝ) : Prop :=
  4 ≤ Ks ∧ ∀ v,
    (∀ i, (X.B v).ε i = epsSH D.R (Fin.cast (by have := X.hk; omega) i)) ∧ (X.B v).c = cStd ∧
    IsSection (k0 + 1) D.R.rS (X.B v).z (X.B v).z' (X.μsec v) ∧
    IsCutS (X.B v).u (X.B v).u' (X.I v) ∧
    ((X.B v).u (X.l v) ≠ (X.B v).u' (X.l v) ∧
      min (-(X.B v).u (X.l v)) (-(X.B v).u' (X.l v)) + 2 ≤ X.a v ∧ X.a v ≤ X.b v ∧
      X.b v ≤ max (-(X.B v).u (X.l v)) (-(X.B v).u' (X.l v)) - 2) ∧
    (∃ ρ : Fin k0 → ℝ, Interlace (X.B v).u ρ ∧ Interlace (X.B v).u' ρ) ∧
    X.I1 v ⊆ X.I v ∧ X.a1 v ≤ X.b1 v ∧ ((NN D Ks : ℕ) : ℝ) ^ 3 / 2 ≤ X.b1 v - X.a1 v ∧
    InterlaceS (by omega : k0 + 1 ≤ 2 * D.R.rS + (k0 + 1) + 1) (X.B v).u (X.B v).lam ∧
    InterlaceS (by omega : k0 + 1 ≤ 2 * D.R.rS + (k0 + 1) + 1) (X.B v).u' (X.B v).lam ∧
    C₀ * ((D.R.k : ℝ) * (NN D Ks : ℕ) * ((D.R.rS : ℝ) + 1) ^ 2 + ((NN D Ks : ℕ) : ℝ) ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2 +
      ((NN D Ks : ℕ) : ℝ) ^ 3) ≤ X.b v - X.a v ∧
    GapAtLeast (X.B v).ε (X.B v).lam
      (Cg * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) * (((NN D Ks : ℕ) : ℝ) * (D.R.r : ℝ) ^ 2 + (D.R.r : ℝ) ^ 3)) ∧
    UnitaryLevelOperators.IsKFinCoefT (X.B v).σ (X.f v) ∧
    (∀ (j : ℕ) (hj : j ≤ D.R.rS), IsRadQQd (X.lv v j hj) (X.R v j hj)) ∧
    ∀ (j : ℕ) (hj : j ≤ D.R.rS) (w : Word), IsLetters (levOf (X.B v) (X.μsec v)) j hj w (X.Th v j hj w)

end Dat

section Weights

variable {D : D7} {k0 : ℕ} (Gm : GramMap k0 D.R.rS) (X : Dat D k0)


end Weights

section Lattices

variable (D : D7)

end Lattices

section Estimates

variable (D : D7) {k0 : ℕ} (Gm : GramMap k0 D.R.rS)

def E (k0 : ℕ) (Ks : ℕ) (C₀ Cg : ℝ) : Prop :=
  ∀ X : Dat D k0, X.Std Ks C₀ Cg → ∀ χ : ℝ → ℝ, IsCutoff χ → ∀ w : GWord D, X.admitted w → Len (NN D Ks) w →
    Tendsto (fun ε => X.energy w χ ε) (𝓝[>] 0) (𝓝 ((X.brk w : ℂ) * X.jn2))

end Estimates

section TopLevel

variable (D : D7) {k0 : ℕ} (Gm : GramMap k0 D.R.rS)

end TopLevel

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Gm : ∀ k0 r : ℕ, GramMap k0 r)

end Family

end Formalism.MainNotions.S.GramWordSpace

end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.ThinScalesBound
noncomputable section

open ValuativeRel MeasureTheory ComplexConjugate ComplexOrder
open Formalism.MainNotions.S.Loc

namespace Formalism.MainNotions.ThinScalesBound


open scoped Classical in
def ThOK {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (m : ℕ) (s : ℕ+) (N : ℕ) (h : Fin N → Pt E m)
    (Th : E ⧸ M.Rsub → Fin N → Fin N → ℂ) : Prop :=
  let N0 := M.Kk m
  let Ns (t : Eˣ) (p q : Pt E m) :=
    ((M.modK ((t : E) * t) ^ ((s : ℕ) * ((s : ℕ) - 1) / 2) : ℝ) : ℂ) *
      M.Kk (m + s) (p.snoc t s) (q.snoc t s)

  (∀ x, (Matrix.of fun a b => Th x a b).PosSemidef) ∧

  (∀ x a b, M.detMod (h a) ≠ M.detMod (h b) → Th x a b = 0) ∧

  (∃ Λ : Submodule M.R E, IsCompact (Λ : Set E) ∧ IsOpen (Λ : Set E) ∧
    ∀ t ∉ Λ, ∀ a b, Th (Submodule.Quotient.mk t) a b = 0) ∧

  (∀ t : Eˣ, (Matrix.of fun a b => Th (Submodule.Quotient.mk (t : E)) a b -
      Ns t (h a) (h b)).PosSemidef) ∧

  (∀ c : ℝ, (Matrix.of fun (a b : {a : Fin N // M.detMod (h a) = c}) =>
      ((c⁻¹ ^ (2 * (s : ℕ)) : ℝ) : ℂ) * N0 (h a) (h b) - ∑' x : E ⧸ M.Rsub, Th x a b).PosSemidef) ∧

  ((s : ℕ) = 1 →
    (∀ (t : Eˣ) a b, Th (Submodule.Quotient.mk (t : E)) a b = Ns t (h a) (h b)) ∧
    ∀ a b, M.detMod (h a) = M.detMod (h b) →
      ∑' x : E ⧸ M.Rsub, Th x a b = ((M.detMod (h a))⁻¹ ^ 2 : ℝ) * N0 (h a) (h b)) ∧

  ((∀ a, M.InGLR (h a)) →
    (∀ a b, N0 (h a) (h b) = 1) ∧
    ∀ x, (Matrix.of fun a b => (if x = 0 then (1 : ℂ) else 0) * N0 (h a) (h b) -
      Th x a b).PosSemidef)

def FamilyTheoremThreePassage {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (g : SplitG M.L), M.split = some g →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t : Term V M r), H.IsTerm t →
  ∀ nn ∈ H.NGrp t.abelian₂ t.f, ∀ nn' ∈ H.NGrp t.abelian₂ t.f',
    (∀ x ∈ t.abelian₂, nn x - nn' x ∈ H.smulLat (algebraMap F E (g.q : F)) t.abelian₂) →
    ∃ uL uU : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      (∀ a b, uL a b ∈ M.R ∧ uU a b ∈ M.R) ∧
      (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      H.ZZplus ⟨t.abelian₂, fun a => nn (t.f a), fun a => nn' (t.f' a), t.T, t.T'⟩ =
        uL * H.ZZplus t * uU

def FrameK {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f : Fin (r + 1) → V) (T : F) : Prop :=
  (∀ a b : Fin (r + 1), (a ≠ Fin.last r ∨ b ≠ Fin.last r) → H.h (f a) (f b) = 0) ∧
    H.h (f (Fin.last r)) (f (Fin.last r)) = - algebraMap F E T

def FamilyLocalModel {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r), H.IsGeneric t₁ →
  ∀ (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'),
    FrameK H f₂ t₁.T → FrameK H f₂' t₁.T' →
    H.Ident t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ φ φ' →
    H.SendsTo φ.toLinearMap 1 1 (t₁.f (Fin.last r)) (f₂ (Fin.last r)) →
    H.SendsTo φ'.toLinearMap 1 1 (t₁.f' (Fin.last r)) (f₂' (Fin.last r)) →
  let S : Set (Submodule M.L.O V) := {Λ₂ | H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
    H.Respects t₁ ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ φ φ'}
  let P₁ := H.ZZplus t₁
  let P₂ := HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T'
  (H.Dl t₁.f t₁.f' r = 0 →
    ∀ (Z₁ Z₂ : M.Mat (r + 1)), Z₁.Z.map M.R.subtype = P₁ → Z₂.Z.map M.R.subtype = P₂ →
      Nat.card S = M.nIso Z₁ Z₂) ∧
  (IsUnit (H.Dl t₁.f t₁.f' r) →
    ∀ (Y₁ Y₂ : M.Mat r) (be₁ be₂ al₁ al₂ : Fin r → M.R),
      (∀ a b : Fin r, (Y₁.Z a b : E) = P₁ a.castSucc b.castSucc ∧
        (Y₂.Z a b : E) = P₂ a.castSucc b.castSucc) →
      (∀ a : Fin r, (be₁ a : E) = P₁ a.castSucc (Fin.last r) ∧ (be₂ a : E) = P₂ a.castSucc (Fin.last r) ∧
        (al₁ a : E) = P₁ (Fin.last r) a.castSucc ∧ (al₂ a : E) = P₂ (Fin.last r) a.castSucc) →
      Nat.card S = M.nIsoBA Y₁ Y₂ be₁ be₂ al₁ al₂)

def AllLoc (P : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E],
    Model F E → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK → P M

def T2 (D : Formalism.BasicNotions.D7) : Prop := AllLoc (fun M => FamilyLocalModel M D.R.rS D.R.r)

end Formalism.MainNotions.ThinScalesBound

end
end
