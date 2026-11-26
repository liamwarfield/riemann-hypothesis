module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorVanishesBigCell
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadicalUnipotentFirstBasisEqOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockRelationTwistedHeight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.WbPartOfInWb
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairOperatorCommute

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCoreCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

section defs

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Rc (Z : Q.Mx k r) (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => RdV (hpart1 (Hpk k r) Z) f g + Complex.I • RdV (hpart2 (Hpk k r) Z) f g

def wordR (w : List (Q.Mx k r)) (f : Q.Mx k r → E) : Q.Mx k r → E :=
  w.foldr (fun Z h => Rc Z h) f

def dZV (f : ℂ → E) (ζ : ℂ) : E := (1 / 2 : ℂ) • (fderiv ℝ f ζ 1 - Complex.I • fderiv ℝ f ζ Complex.I)

def dZbV (f : ℂ → E) (ζ : ℂ) : E := (1 / 2 : ℂ) • (fderiv ℝ f ζ 1 + Complex.I • fderiv ℝ f ζ Complex.I)

end defs

def GLc (k r : ℕ) (Z : Q.Mx k r) : Prop :=
  Q.inLieLev k r (Fin.last r) (hpart1 (Hpk k r) Z) ∧ Q.inLieLev k r (Fin.last r) (hpart2 (Hpk k r) Z)

def GWc (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Z : Q.Mx k r) : Prop :=
  P.QrD.InLieW k r z (hpart1 (Hpk k r) Z) ∧ P.QrD.InLieW k r z (hpart2 (Hpk k r) Z)

def Dp (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (Q.Mx k r) := {g | 0 < Q.GGl k r z z' g}

def mu0 (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ζ : ℂ) : Q.Mx k r := NF.muZ k r (TheSec.theSection k r z z') ζ

def etaZ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ζ : ℂ) : Q.Mx k r :=
  (mu0 k r z z' ζ)⁻¹ * Matrix.of fun i j => NF.dZ (fun w => mu0 k r z z' w i j) ζ

def etaZb (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ζ : ℂ) : Q.Mx k r :=
  (mu0 k r z z' ζ)⁻¹ * Matrix.of fun i j => NF.dZb (fun w => mu0 k r z z' w i j) ζ

def RcLin : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (D : Set (Q.Mx k r)) (f : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r (Fin.last r) D f → ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D,
    ∀ (a : ℂ) (Z Z' : Q.Mx k r), GLc k r Z → GLc k r Z' → Rc (a • Z + Z') f g = a • Rc Z f g + Rc Z' f g

def RcSmooth : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (D : Set (Q.Mx k r)) (f f' : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r (Fin.last r) D f → Q.SmoothLev k r (Fin.last r) D f' → ∀ Z : Q.Mx k r, GLc k r Z →
      Q.SmoothLev k r (Fin.last r) D (Rc Z f) ∧
      (∀ (a : ℂ), ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, Rc Z (fun x => a • f x + f' x) g = a • Rc Z f g + Rc Z f' g) ∧
      ∀ (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℂ E'] (L : E →L[ℂ] E'), ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D,
        Rc Z (fun x => L (f x)) g = L (Rc Z f g)

def RcComm : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (D : Set (Q.Mx k r)) (f : Q.Mx k r → E),
    IsOpen D → Q.SmoothLev k r (Fin.last r) D f → ∀ Z₁ Z₂ : Q.Mx k r, GLc k r Z₁ → GLc k r Z₂ →
    ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D,
      Rc Z₁ (Rc Z₂ f) g - Rc Z₂ (Rc Z₁ f) g = Rc (Z₁ * Z₂ - Z₂ * Z₁) f g

def LeftCov : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)), IsCRepOn (UWset k r z) π → ContinuousOn π (UWset k r z) → inWb k r z →
    ∀ (D : Set (Q.Mx k r)) (F : Q.Mx k r → (Wq →L[ℂ] Wp)), IsOpen D → (∀ h ∈ UWset k r z, ∀ g ∈ D, h * g ∈ D) →
    Q.SmoothLev k r (Fin.last r) D F →
    (∀ h ∈ UWset k r z, ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, F (h * g) = (π h).comp (F g)) →
    ∀ μ ∈ Q.Glev k r (Fin.last r) ∩ D, ∀ B : Q.Mx k r, GWc k r z B →
      GLc k r (μ⁻¹ * B * μ) ∧ Rc (μ⁻¹ * B * μ) F μ = (P.QrD.ecOp π B).comp (F μ)

def RightCov : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)), IsCRepOn (UWset k r z') π' → ContinuousOn π' (UWset k r z') → inWb k r z' →
    ∀ (D : Set (Q.Mx k r)) (F : Q.Mx k r → (Wq →L[ℂ] Wp)), IsOpen D → (∀ h ∈ UWset k r z', ∀ g ∈ D, g * h ∈ D) →
    Q.SmoothLev k r (Fin.last r) D F →
    (∀ h ∈ UWset k r z', ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, F (g * h) = (F g).comp (π' h)) →
    ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, ∀ A : Q.Mx k r, GWc k r z' A →
      GLc k r A ∧ Rc A F g = (F g).comp (P.QrD.ecOp π' A)

def SecDeriv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ ζ : ℂ, (Tz k r z * Tz k r z') < Complex.normSq ζ →
      GLc k r (etaZ k r z z' ζ) ∧ GLc k r (etaZb k r z z' ζ) ∧ (mu0 k r z z' ζ) ∈ Q.Glev k r (Fin.last r) ∩ Dp k r z z' ∧
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : Q.Mx k r → E),
        Q.SmoothLev k r (Fin.last r) (Dp k r z z') F →
        Rc (etaZ k r z z' ζ) F (mu0 k r z z' ζ) = dZV (fun w => F (mu0 k r z z' w)) ζ ∧
        Rc (etaZb k r z z' ζ) F (mu0 k r z z' ζ) = dZbV (fun w => F (mu0 k r z z' w)) ζ

def Decomp : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ a b : Fin (k + 1), ∃ (n₁ n₂ : ℕ) (B₁ : Fin n₁ → Q.Mx k r) (b₁ : Fin n₁ → ℂ → ℂ) (B₂ : Fin n₂ → Q.Mx k r)
      (b₂ : Fin n₂ → ℂ → ℂ) (β₁ β₂ : ℂ → ℂ),
      (∀ t, GWc k r z' (B₁ t)) ∧ (∀ t, GWc k r z (B₂ t)) ∧ (∀ t, PS (Tz k r z * Tz k r z') (b₁ t)) ∧ (∀ t, PS (Tz k r z * Tz k r z') (b₂ t)) ∧
      PS (Tz k r z * Tz k r z') β₁ ∧ PS (Tz k r z * Tz k r z') β₂ ∧
      ∀ ζ : ℂ, (Tz k r z * Tz k r z') < Complex.normSq ζ →
        Matrix.single (wI k r a) (wI k r b) (1 : ℂ) =
          ∑ t, b₁ t ζ • B₁ t + (mu0 k r z z' ζ)⁻¹ * (∑ t, b₂ t ζ • B₂ t) * (mu0 k r z z' ζ) +
            β₁ ζ • etaZ k r z z' ζ + β₂ ζ • etaZb k r z z' ζ

def PSCalc : Prop :=
  ∀ (TT : ℝ), 0 < TT →
    (∀ c : ℂ, PS TT (fun _ => c)) ∧ PS TT id ∧ PS TT (fun ζ => conj ζ) ∧ PS TT (sig TT) ∧ PS TT (fun ζ => (gg TT ζ)⁻¹) ∧
    (∀ f g, PS TT f → PS TT g → PS TT (fun ζ => f ζ + g ζ) ∧ PS TT (fun ζ => f ζ * g ζ)) ∧
    (∀ f, PS TT f → PS TT (NF.dZ f) ∧ PS TT (NF.dZb f)) ∧
    ∀ (V V' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V'],
      (∀ f g : ℂ → V, PSV TT f → PSV TT g → PSV TT (fun ζ => f ζ + g ζ)) ∧
      (∀ (a : ℂ → ℂ) (f : ℂ → V), PS TT a → PSV TT f → PSV TT (fun ζ => a ζ • f ζ)) ∧
      (∀ (L : V →ₗ[ℂ] V') (f : ℂ → V), PSV TT f → PSV TT (fun ζ => L (f ζ))) ∧
      (∀ (f : ℂ → V), PSV TT f → PSV TT (dZV f) ∧ PSV TT (dZbV f)) ∧
      (∀ v : V, PSV TT (fun _ => v))

def LowerUnipotentMatrixWords : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ Y : ℂ, ∃ (n : ℕ) (κ : Fin n → ℂ → ℂ) (w : Fin n → List (Q.Mx k r)),
      (∀ i, PS (Tz k r z * Tz k r z') (κ i)) ∧ (∀ i, ∀ Z ∈ w i, ∃ a b : Fin (k + 1), Z = Matrix.single (wI k r a) (wI k r b) 1) ∧
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : Q.Mx k r → E),
        Q.SmoothLev k r (Fin.last r) (Dp k r z z') F → ∀ ζ : ℂ, (Tz k r z * Tz k r z') < Complex.normSq ζ →
          Q.tL k r z z' (Fin.last r) Y 1 0 F (mu0 k r z z' ζ) = ∑ i, κ i ζ • wordR (w i) F (mu0 k r z z' ζ)

def WordPSV : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z' →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (X₀ : Wq →L[ℂ] Wp),
      (∀ c ∈ OmX P.r, ∀ ζ ∈ Gauge.GC.Ann P,
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = X₀) →
      ∀ c ∈ OmX P.r, ∀ w : List (Q.Mx P.k P.r), (∀ Z ∈ w, GLc P.k P.r Z) →
        PSV P.TT (fun ζ => wordR w ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c) (NF.muZ P.k P.r Bs.μsec ζ))

def WordPSVOfCut : Prop :=
  RcLin → RcSmooth → RcComm → LeftCov → RightCov → SecDeriv → Decomp → PSCalc → WordPSV

def CorePolyOfCut : Prop := LowerUnipotentMatrixWords → WordPSV → PSCalc → CorePoly

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbeddedGroupMeasurePreserving
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k p ρ : ℕ}

theorem embedding_map_embedded_group : MMapEmbG := by
  intro k p ρ Z γ y₁ y₂
  simp only [U.mMap, U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]

theorem embedded_group_measure_preserving : EmbGMuP := by
  intro k p ρ y q
  simp only [U.muP, U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]

private theorem wMat_mul_self_eq_one (d : ℕ) : G.wMat d * G.wMat d = 1 := by
  ext i j
  simp only [G.wMat, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  split_ifs <;> simp_all

private theorem wMat_mul_wMat_mul' (d : ℕ) {m : Type*} (X : Matrix (Fin d) m ℂ) : G.wMat d * (G.wMat d * X) = X := by
  rw [← Matrix.mul_assoc, wMat_mul_self_eq_one, Matrix.one_mul]

theorem embedding_map_lower_unipotent : MMapLZU := by
  intro k p ρ l Z u γ hl
  simp only [U.mMap, U.muP, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.conjTranspose_mul, Matrix.mul_inv_rev,
    Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_nonsing_inv l hl,
    Matrix.mul_assoc, wMat_mul_wMat_mul']

theorem embedded_group_right_action : EmbGRn := by
  intro k p ρ y x hy
  have h1 : Matrix.of (rcAct y x).1 = y * Matrix.of x.1 := rfl
  have h2 : (rcAct y x).2 = x.2 := rfl
  have h3 : yᴴ * (Hpk k ρ * y) = Hpk k ρ := by rw [← Matrix.mul_assoc, hy]
  have h4 : ∀ M : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ, yᴴ * (Hpk k ρ * (y * M)) = Hpk k ρ * M := by
    intro M
    rw [← Matrix.mul_assoc (Hpk k ρ), ← Matrix.mul_assoc, h3]
  simp only [U.Rn, U.embG, Ux5.block3_mul_blocks, h1, h2, Matrix.conjTranspose_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul,
    Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h3, h4,
    neg_zero, smul_zero]

private theorem wP_inv_mul_wP_eq_one {p : ℕ} (σ : Equiv.Perm (Fin p)) : U.wP σ⁻¹ * U.wP σ = 1 := by
  ext a c
  have h : σ (σ⁻¹ a) = a := σ.apply_symm_apply a
  simp only [U.wP, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, h]

private theorem isUnit_det_wP {p : ℕ} (σ : Equiv.Perm (Fin p)) : IsUnit (U.wP σ).det :=
  Matrix.isUnit_det_of_left_inverse (wP_inv_mul_wP_eq_one σ)

theorem lh_lower {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : G.IsLowerUni (lhOf σ v) := by
  have hinv : (U.wP σ)⁻¹ = U.wP σ⁻¹ := Matrix.inv_eq_left_inv (wP_inv_mul_wP_eq_one σ)
  have hentry : ∀ a b, lhOf σ v a b = U.lowW σ v (σ a) (σ b) := by
    intro a b
    rw [lhOf, hinv]
    simp only [Matrix.mul_apply, U.wP, Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, Equiv.Perm.inv_eq_iff_eq, Finset.sum_ite_eq']
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp only [Matrix.transpose_apply, hentry]
    simp [U.lowW]
  · simp only [Matrix.transpose_apply, hentry]
    have h1 : σ j ≠ σ i := fun h => (ne_of_lt hij) (σ.injective h)
    have h2 : ¬ (i < j) := not_lt.mpr hij.le
    simp [U.lowW, Matrix.one_apply, h1, h2]

theorem head_hermitian_eq : HeadHEq := by
  intro p σ d v u
  refine ⟨?_, lh_lower σ v⟩
  simp only [U.headH, lhOf, U.hMat, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U.wP σ)⁻¹ (U.wP σ), Matrix.nonsing_inv_mul _ (isUnit_det_wP σ), Matrix.one_mul]

private theorem blk2_fin_zero_eq {p : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B' : Matrix (Fin p) (Fin 0) ℂ)
    (C : Matrix (Fin 0) (Fin p) ℂ) (D : Matrix (Fin 0) (Fin 0) ℂ) : U.blk2 A B' C D = A := by
  ext i j
  have hi : finSumFinEquiv.symm i = Sum.inl i := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by first | rfl | simp [finSumFinEquiv_apply_left])
  have hj : finSumFinEquiv.symm j = Sum.inl j := by
    rw [Equiv.symm_apply_eq]
    exact Fin.ext (by first | rfl | simp [finSumFinEquiv_apply_left])
  simp [U.blk2, Matrix.reindex_apply, hi, hj]

theorem lower_corner_hermitian_zero : ZjHZero := by
  intro p σ d η Z
  simp only [U.ZjH, U.Zj, blk2_fin_zero_eq, Matrix.one_mul, Matrix.mul_one]

theorem lh_unit {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : IsUnit (lhOf σ v).det := by
  have hL : (U.lowW σ v).det = 1 := by
    rw [Matrix.det_of_lowerTriangular _ ?_]
    · simp [U.lowW]
    · intro i j hij
      have h1 : i < j := OrderDual.toDual_lt_toDual.mp hij
      have h2 : ¬ j < i := not_lt.mpr h1.le
      simp [U.lowW, Matrix.one_apply, ne_of_lt h1, h2]
  simp only [lhOf, Matrix.det_mul, hL, mul_one]
  exact (isUnit_det_wP σ).mul (Matrix.isUnit_nonsing_inv_det _ (isUnit_det_wP σ))

theorem gamma_xi_split : GaXiSplit := by
  intro k p ρ σ d ξ Z h ν h' ν' g hh hν hh'
  have hZ : U.ZjH σ d ξ.2 Z = lhOf σ ξ.2.2.1 * U.hMat σ d * G.upper ξ.2.2.2 := by
    rw [lower_corner_hermitian_zero p σ d ξ.2 Z]
    exact (head_hermitian_eq p σ d ξ.2.2.1 ξ.2.2.2).1
  have hγ : h⁻¹ * ν⁻¹ * g * ν' * h' = (h⁻¹ * ν⁻¹) * g * (ν' * h') := by
    simp only [Matrix.mul_assoc]
  have hE : U.embG k p ρ (ν' * h') = U.embG k p ρ ν' * U.embG k p ρ h' := by
    simp only [U.embG, Ux5.block3_mul_blocks, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
  simp only [U.gaXi]
  rw [PBM.rn_inv, hZ]
  show U.Rn k p ρ (-ξ.1.1) * U.mMap k p ρ (lhOf σ ξ.2.2.1 * U.hMat σ d * G.upper ξ.2.2.2) (h⁻¹ * ν⁻¹ * g * ν' * h') *
      U.Rn k p ρ ξ.1.2 = _
  rw [embedding_map_lower_unipotent k p ρ _ _ _ _ (lh_unit σ ξ.2.2.1), hγ, embedding_map_embedded_group, hE]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U.embG k p ρ h') (U.muP k p ρ (G.upper ξ.2.2.2)),
    embedded_group_measure_preserving k p ρ h' (G.upper ξ.2.2.2), Matrix.mul_assoc, embedded_group_right_action k p ρ h' ξ.1.2 hh']

theorem embG_nset {k p ρ : ℕ} {y : B.Mat k ρ} (hy : y ∈ QuantumDeterminants.Nset k ρ) : U.embG k p ρ y ∈ QuantumDeterminants.Nset k (p + ρ) := by
  rw [WeylGroupFacts.nset_iff] at hy ⊢
  refine ⟨?_, ?_⟩
  · show (U.embG k p ρ y)ᴴ * Hpk k (p + ρ) * U.embG k p ρ y = Hpk k (p + ρ)
    have hy1 : yᴴ * Hpk k ρ * y = Hpk k ρ := hy.1
    rw [Formalism.FourierDecayAlt.P.hermitian_group_blocks k p ρ, U.embG, Ux3.block3_conjTranspose, Ux3.block3_mul, Ux3.block3_mul]
    congr 1 <;> simp [hy1]
  · intro i c hc hi
    obtain ⟨x, rfl⟩ := (U.eB k p ρ).surjective i
    obtain ⟨w, rfl⟩ := (U.eB k p ρ).surjective c
    rw [U.embG, Ux3.block3_apply]
    simp only [(U.eB k p ρ).apply_eq_iff_eq]
    rcases x with ((x | x) | x) <;> rcases w with ((w | w) | w) <;>
      simp only [Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val] at hc hi <;>
      first
      | (simp [Matrix.one_apply]; done)
      | (exfalso; have := x.isLt; have := w.isLt; omega)
      | skip
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, Sum.inl.injEq, Sum.inr.injEq]
    exact hy.2 x w (by omega) (by omega)

theorem left_factor_mem : LeftMem := by
  intro k p ρ z x l h ν hz hl hh hν
  have hH := Formalism.FourierDecayAlt.P.Ux3.hpk_det k ρ
  have hhu : IsUnit h.det := WeylGroupFacts.isUnit_of_uh hh.1
  have hclN := Formalism.FourierDecayAlt.P.unipotent_radical_closed k (p + ρ)

  have hlH : G.IsUpperUni lᴴ := by
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · rw [Matrix.conjTranspose_apply, show l i i = lᵀ i i from rfl, hl.1 i, star_one]
    · rw [Matrix.conjTranspose_apply, show l j i = lᵀ i j from rfl, hl.2 i j hij, star_zero]
  have hlu : IsUnit (lᴴ).det := by rw [Formalism.FourierDecayAlt.P.G4.upperUni_det hlH]; exact isUnit_one
  have hmu : U.muP k p ρ (lᴴ)⁻¹ ∈ QuantumDeterminants.Nset k (p + ρ) := by
    rw [← Formalism.FourierDecayAlt.P.PBM.leviElement_inv _ hlu]
    refine hclN.inv_mem _ (Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset _ ⟨fun i j hij => hlH.2 i j hij, hlH.1⟩)
  have hRn : U.Rn k p ρ (rcAct h x) ∈ QuantumDeterminants.Nset k (p + ρ) :=
    (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.2 (by rw [← (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).2.1]; exact ⟨rcAct h x, rfl⟩)
  have hνN : U.embG k p ρ ν⁻¹ ∈ QuantumDeterminants.Nset k (p + ρ) :=
    embG_nset ((Formalism.FourierDecayAlt.P.unipotent_radical_closed k ρ).inv_mem ν hν)
  have hW : U.embG k p ρ h⁻¹ ∈ UWset k (p + ρ) (liftVec k p ρ z) := by
    rw [← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_eq_embG]; exact Formalism.FourierDecayAlt.P.Dx2.Tower.lev_UW p ρ z _ (WeylGroupFacts.uw_inv hh)
  refine ⟨U.embG k p ρ h⁻¹, hW, U.Rn k p ρ (rcAct h x) * U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ ν⁻¹,
    hclN.mul_mem _ (hclN.mul_mem _ hRn _ hmu) _ hνN, ?_⟩
  have e1 : U.embG k p ρ h * U.Rn k p ρ x = U.Rn k p ρ (rcAct h x) * U.embG k p ρ h := embedded_group_right_action k p ρ h x hh.1
  have e2 : U.embG k p ρ h⁻¹ * U.embG k p ρ h = 1 := by
    rw [← Formalism.FourierDecayAlt.P.Dx2.Split.embG_mul, Matrix.nonsing_inv_mul _ hhu, Formalism.FourierDecayAlt.P.PBM.embG_one]
  have e3 : U.Rn k p ρ x = U.embG k p ρ h⁻¹ * U.Rn k p ρ (rcAct h x) * U.embG k p ρ h := by
    rw [Matrix.mul_assoc, ← e1, ← Matrix.mul_assoc, e2, Matrix.one_mul]
  have e4 : U.embG k p ρ h * U.embG k p ρ (h⁻¹ * ν⁻¹) = U.embG k p ρ ν⁻¹ := by
    rw [← Formalism.FourierDecayAlt.P.Dx2.Split.embG_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hhu, Matrix.one_mul]
  have e5 : U.embG k p ρ h * U.muP k p ρ (lᴴ)⁻¹ = U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ h := embedded_group_measure_preserving k p ρ h _
  calc U.Rn k p ρ x * U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ (h⁻¹ * ν⁻¹)
      = U.embG k p ρ h⁻¹ * U.Rn k p ρ (rcAct h x) * (U.embG k p ρ h * U.muP k p ρ (lᴴ)⁻¹) *
          U.embG k p ρ (h⁻¹ * ν⁻¹) := by rw [e3]; simp only [Matrix.mul_assoc]
    _ = U.embG k p ρ h⁻¹ * U.Rn k p ρ (rcAct h x) * U.muP k p ρ (lᴴ)⁻¹ *
          (U.embG k p ρ h * U.embG k p ρ (h⁻¹ * ν⁻¹)) := by rw [e5]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [e4]; simp only [Matrix.mul_assoc]

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.Tower
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k : ℕ}

theorem lift_lift_V (j ρ n r : ℕ) (hn : 1 + ρ = n) (h1 : j + n = r) (h2 : j + 1 + ρ = r)
    (v : Fin (2 * ρ + k + 1) → ℂ) :
    D.castV h1 (liftVec k j n (D.castV hn (liftVec k 1 ρ v))) = D.castV h2 (liftVec k (j + 1) ρ v) := by
  funext i
  simp only [D.castV, liftVec, Fin.coe_cast]
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk, Fin.coe_cast] at *) <;> first | rfl | omega | (congr 1 <;> ext <;> simp only [Fin.val_mk, Fin.coe_cast] <;> omega)

theorem lift_lift_M (j ρ n r : ℕ) (hn : 1 + ρ = n) (h1 : j + n = r) (h2 : j + 1 + ρ = r) (y : B.Mat k ρ) :
    D.castM h1 (ιLev k j n (D.castM hn (ιLev k 1 ρ y))) = D.castM h2 (ιLev k (j + 1) ρ y) := by
  ext p q
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply, finCongr_symm, finCongr_apply, Fin.coe_cast, ιLev]
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk, Fin.coe_cast] at *) <;> first | rfl | omega | (congr 1 <;> ext <;> simp only [Fin.val_mk, Fin.coe_cast] <;> omega)

theorem castV_inj {a b : ℕ} (h : a = b) {v w : Fin (2 * a + k + 1) → ℂ} (e : D.castV h v = D.castV h w) : v = w := by
  subst h
  funext i
  simpa [D.castV] using congrFun e i

section tower

variable {r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem levTower_bs_z_eq_castV_liftVec (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) :
    (T.bs j).z = D.castV (by omega : 1 + (r - (j + 1)) = r - j) (liftVec k 1 (r - (j + 1)) (T.bs (j + 1)).z) := by
  have e1 := T.z_lev j (by omega)
  have e2 := T.z_lev (j + 1) hj
  rw [← lift_lift_V j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)] at e2
  have e3 := castV_inj _ (e1.trans e2.symm)
  funext i
  have hi := i.isLt
  have hi' : i.val ≤ 2 * (r - j) + k := by omega
  have := congrFun e3 ⟨i.val + j, by omega⟩
  simpa [liftVec, hi'] using this

theorem levTower_bs_z'_eq_castV_liftVec (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) :
    (T.bs j).z' = D.castV (by omega : 1 + (r - (j + 1)) = r - j) (liftVec k 1 (r - (j + 1)) (T.bs (j + 1)).z') := by
  have e1 := T.z'_lev j (by omega)
  have e2 := T.z'_lev (j + 1) hj
  rw [← lift_lift_V j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)] at e2
  have e3 := castV_inj _ (e1.trans e2.symm)
  funext i
  have hi := i.isLt
  have hi' : i.val ≤ 2 * (r - j) + k := by omega
  have := congrFun e3 ⟨i.val + j, by omega⟩
  simpa [liftVec, hi'] using this

theorem tower_π (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) (y : B.Mat k (r - (j + 1))) :
    (T.bs (j + 1)).π y = (T.bs j).π (D.castM (by omega : 1 + (r - (j + 1)) = r - j) (ιLev k 1 (r - (j + 1)) y)) := by
  rw [T.π_lev (j + 1) hj y, T.π_lev j (by omega),
    lift_lift_M j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)]

theorem tower_π' (T : D.LevTower k r Wp Wq) (j : ℕ) (hj : j + 1 ≤ r) (y : B.Mat k (r - (j + 1))) :
    (T.bs (j + 1)).π' y = (T.bs j).π' (D.castM (by omega : 1 + (r - (j + 1)) = r - j) (ιLev k 1 (r - (j + 1)) y)) := by
  rw [T.π'_lev (j + 1) hj y, T.π'_lev j (by omega),
    lift_lift_M j (r - (j + 1)) (r - j) r (by omega) (by omega) (by omega)]

end tower

end Formalism.FourierDecayAlt.P.PBH
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactCoefficientAppend
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

open Formalism.FourierDecayAlt.P.PBJ

section lev0

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem ptG_one (TT : ℝ) (ζ : ℂ) : D.ptG TT 0 [(1, ζ)] = Complex.normSq ζ - TT := by
  simp [D.ptG, D.ptMatN, D.ptEntry, Matrix.det_fin_one]

theorem isLocPt_one {ζ : ℂ} (hζ : ζ ≠ 0) : D.IsLocPt [(1, ζ)] (0 + 1) := by
  refine ⟨?_, ?_⟩
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact ⟨le_refl _, hζ⟩
  · simp [D.ptSize]

theorem orbJ_one_eq (S : B.RealPlaceData k ρ Wp Wq) {γ : B.Mat k ρ} (hγ : γ ∈ B.GV k ρ)
    (hpos : 0 < Gf k ρ S.z S.z' γ) {d : Fin (ρ + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
    (hZ : Zhat k ρ S.z S.z' γ = C2.monoP 1 d) (F : B.Mat k ρ → (Wq →L[ℂ] Wp)) :
    D.orbJ S γ (D.muR S γ 1) F = B.JF S F γ := by
  have : IsEmpty (C2.Lstidx (1 : Equiv.Perm (Fin (ρ + 1)))) := ⟨fun q => by
    obtain ⟨⟨a, b⟩, h1, h2⟩ := q
    simp only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, id] at h2
    exact absurd h1 (not_lt.2 h2.le)⟩
  have hone : D.rhoOfU S γ 1 = 1 := by
    unfold D.rhoOfU
    split_ifs with hex
    · have h1mem : (1 : B.Mat k ρ) ∈ C6.Rset γ := by
        refine ⟨WeylGroupFacts.mem_n_one, ?_⟩
        rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hγ)]
        exact WeylGroupFacts.mem_n_one
      exact Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj S hγ hpos hd hZ hex.choose_spec.1 h1mem
        (hex.choose_spec.2.trans (Formalism.FourierDecayAlt.P.Dx2.Rad.uMap_one S.z ⟨S.z_mem, S.T_pos⟩).symm)
    · rfl
  have hlow : C2.lowOf (fun q : C2.Lstidx (1 : Equiv.Perm (Fin (ρ + 1))) => q.1) isEmptyElim = 1 := by
    unfold C2.lowOf
    ext i j
    simp
  have hR : D.muR S γ 1 = Measure.dirac (Matrix.of.symm (1 : B.Mat k ρ)) := by
    unfold D.muR
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty _ isEmptyElim, Measure.map_dirac' Subsingleton.measurable,
      hlow, Matrix.conjTranspose_one, hone]
  have hact : ∀ p, C6.actR γ 1 p = p := by
    intro p
    unfold C6.actR
    rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hγ), Matrix.one_mul,
      Matrix.one_mul]
    rfl
  have hθ : ∀ θ, D.IsNormCut S γ (D.muR S γ 1) θ → ∀ p, S.inSS p → θ p = 1 := by
    intro θ hθ p hp
    have h := hθ.2.2 p hp
    rw [hR, integral_dirac] at h
    change θ (C6.actR γ (1 : B.Mat k ρ) p) = 1 at h
    rw [hact p] at h
    exact h
  unfold D.orbJ
  split_ifs with hex
  · have h1 := hθ _ hex.choose_spec.1
    calc ∫ p, hex.choose p • D.orbIntegrand S γ F p ∂S.μSS = ∫ p, D.orbIntegrand S γ F p ∂S.μSS := by
          refine integral_congr_ae ?_
          filter_upwards [Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_inSS S] with p hp
          rw [h1 p hp, one_smul]
      _ = B.Jtau S (1, 1) F γ := rfl
      _ = B.JF S F γ := Formalism.FourierDecayAlt.P.bessel_function_trivial_index k ρ Wp Wq S F γ
  · have hni : ¬ Integrable (fun p => D.orbIntegrand S γ F p) S.μSS := by
      intro hI
      apply hex
      refine ⟨fun _ => 1, ⟨measurable_const, fun _ => zero_le_one, fun p _ => ?_⟩, by simpa using hI⟩
      rw [hR, integral_dirac]
    rw [← Formalism.FourierDecayAlt.P.bessel_function_trivial_index k ρ Wp Wq S F γ]
    exact (integral_undef hni).symm

theorem vector_level_zero_eq_jacquet (hρ : ρ = 0) (B0 : B.RealPlaceData k ρ Wp Wq) (ν : Fin (2 * ρ + k + 1) → ℂ) (m : B.Mat k ρ)
    (hb : D.IsBaseFrame B0 ν m) (Φ : B.Mat k ρ → (Wq →L[ℂ] Wp)) (ζ : ℂ)
    (hζ : Tz k ρ B0.z * Tz k ρ B0.z' < Complex.normSq ζ) (γ0 : B.Mat k ρ) (hγ0 : γ0 ∈ B.GV k ρ)
    (hZ : Zhat k ρ B0.z B0.z' γ0 = D.ptMatN [(1, ζ)] (ρ + 1)) (hD : D.IsDFrame B0 ν m γ0) :
    D.vecV B0 ν m Φ [(1, ζ)] = B.JF B0 Φ γ0 := by
  subst hρ
  have hTT : 0 < Tz k 0 B0.z * Tz k 0 B0.z' := mul_pos B0.T_pos B0.T'_pos
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h, Complex.normSq_zero] at hζ; linarith
  have hloc := isLocPt_one hζ0
  have hG : 0 < D.ptG (Tz k 0 B0.z * Tz k 0 B0.z') 0 [(1, ζ)] := by rw [ptG_one]; linarith
  rw [Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep k 0 Wp Wq B0 ν m Φ [(1, ζ)] hloc γ0 hb hG hγ0 hZ hD]
  have hw : (hloc.2 ▸ D.ptPerm [(1, ζ)] : Equiv.Perm (Fin (0 + 1))) = 1 := by
    refine Equiv.ext fun a => Fin.ext ?_
    have h1 := a.isLt
    have h2 := ((hloc.2 ▸ D.ptPerm [(1, ζ)] : Equiv.Perm (Fin (0 + 1))) a).isLt
    simp only [Equiv.Perm.coe_one, id]
    omega
  obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' [(1, ζ)] (0 + 1) hloc.2 hloc.1
  rw [hw] at hmono
  have hpos : 0 < Gf k 0 B0.z B0.z' γ0 := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec k 0 _ _ [(1, ζ)] γ0 hloc hZ]; exact hG
  rw [hw]
  exact orbJ_one_eq B0 hγ0 hpos hnz (hZ.trans hmono) Φ

theorem vector_level_zero_degenerate (hρ : ρ = 0) (B0 : B.RealPlaceData k ρ Wp Wq) (ν : Fin (2 * ρ + k + 1) → ℂ) (m : B.Mat k ρ)
    (Φ : B.Mat k ρ → (Wq →L[ℂ] Wp)) (ζ : ℂ) (hζ : Complex.normSq ζ ≤ Tz k ρ B0.z * Tz k ρ B0.z') :
    D.vecV B0 ν m Φ [(1, ζ)] = 0 := by
  subst hρ
  unfold D.vecV
  rw [dite_eq_right]
  rintro ⟨_, h⟩
  rw [ptG_one] at h
  linarith

theorem exists_frame_level_zero (hρ : ρ = 0) (B0 : B.RealPlaceData k ρ Wp Wq) (ν : Fin (2 * ρ + k + 1) → ℂ) (m : B.Mat k ρ)
    (hb : D.IsBaseFrame B0 ν m) (ζ : ℂ) (hζ : Tz k ρ B0.z * Tz k ρ B0.z' < Complex.normSq ζ) :
    ∃ γ0 ∈ B.GV k ρ, Zhat k ρ B0.z B0.z' γ0 = D.ptMatN [(1, ζ)] (ρ + 1) ∧ D.IsDFrame B0 ν m γ0 := by
  subst hρ
  have hTT : 0 < Tz k 0 B0.z * Tz k 0 B0.z' := mul_pos B0.T_pos B0.T'_pos
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h, Complex.normSq_zero] at hζ; linarith
  have hG : 0 < D.ptG (Tz k 0 B0.z * Tz k 0 B0.z') 0 [(1, ζ)] := by rw [ptG_one]; linarith
  exact Formalism.FourierDecayAlt.P.exists_isotropic_frame k 0 Wp Wq B0 ν m [(1, ζ)] hb (isLocPt_one hζ0) hG

theorem jacquet_integral_level_zero (hρ : ρ = 0) (B0 : B.RealPlaceData k ρ Wp Wq) (hN : B0.μN = D.muN k ρ)
    (Φ : B.Mat k ρ → (Wq →L[ℂ] Wp)) (γ : B.Mat k ρ) :
    B.JF B0 Φ γ = ∫ p : Mt k ρ × Mt k ρ, (B0.π (Matrix.of p.1)).comp
      ((Φ ((Matrix.of p.1)⁻¹ * γ * Matrix.of p.2)).comp (B0.π' (Matrix.of p.2)⁻¹)) ∂(B0.μW.prod B0.μW') := by
  subst hρ
  have : SigmaFinite B0.μW := Formalism.FourierDecayAlt.P.Dx2.MN.sigma_of_haar B0.haarW
  have : SigmaFinite B0.μW' := Formalism.FourierDecayAlt.P.Dx2.MN.sigma_of_haar B0.haarW'
  have hN0 : B0.μN = Measure.dirac (Matrix.of.symm (1 : B.Mat k 0)) := hN
  have hmeas : (B0.μW.prod B0.μN).prod (B0.μW'.prod B0.μN) = (B0.μW.prod B0.μW').map
      (fun p : Mt k 0 × Mt k 0 => ((p.1, Matrix.of.symm (1 : B.Mat k 0)), (p.2, Matrix.of.symm (1 : B.Mat k 0)))) := by
    rw [hN0, Measure.prod_dirac, Measure.prod_dirac,
      Measure.map_prod_map (f := fun x : Mt k 0 => (x, Matrix.of.symm (1 : B.Mat k 0)))
        (g := fun x : Mt k 0 => (x, Matrix.of.symm (1 : B.Mat k 0))) _ _ (by fun_prop) (by fun_prop)]
    rfl
  have hemb : MeasurableEmbedding (fun p : Mt k 0 × Mt k 0 =>
      ((p.1, Matrix.of.symm (1 : B.Mat k 0)), (p.2, Matrix.of.symm (1 : B.Mat k 0)))) :=
    (MeasurableEmbedding.id.prodMk_right _).prodMap (MeasurableEmbedding.id.prodMk_right _)
  have hpsi : ∀ (z : Fin (2 * 0 + k + 1) → ℂ) (g : B.Mat k 0), Formalism.QuantumDeterminants.psi k 0 z cStd g = 1 := by
    intro z g; simp [Formalism.QuantumDeterminants.psi, Formalism.QuantumDeterminants.ell]
  unfold B.JF besselJ
  rw [hmeas, hemb.integral_map]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [hpsi, star_one, mul_one, one_smul, Equiv.apply_symm_apply, inv_one]

end lev0

end Formalism.FourierDecayAlt.P.PBM
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomCut
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.AdmissibleLieWords
open scoped ComplexConjugate Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def nuG (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  unitH k r (PI.UnitaryGroupMassFormula.GsFr.omW k r z z' g)

def nuG' (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  unitH k r (PI.UnitaryGroupMassFormula.GsFr.omW' k r z z' g)

def PpG (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : B.Mat k r :=
  PI.UnitaryGroupMassFormula.GsFr.Pm k r z' - PI.UnitaryGroupMassFormula.GsFr.Rk k r (nuG' z z' g) (nuG' z z' g) * PI.UnitaryGroupMassFormula.GsFr.Pm k r z'

def ioG (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : B.Mat k r :=
  PI.UnitaryGroupMassFormula.GsFr.Phi k r z z' g * PpG z z' g

def posG (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ 0 < Gf k r z z' g}

def geG (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (ε : ℝ) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ ε ≤ Gf k r z z' g}

def GeomSmooth : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    B.CkOn ⊤ (posG k r z z') (nuG z z') ∧ B.CkOn ⊤ (posG k r z z') (nuG' z z') ∧
      B.CkOn ⊤ (posG k r z z') (ioG z z')

def GeomEqvNu : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, ∀ h' ∈ UWset k r z', ∀ n' ∈ Nset k r, ∀ g ∈ posG k r z z',
      nuG z z' g = h *ᵥ nuG z z' (h⁻¹ * n⁻¹ * g * n' * h') ∧
        nuG' z z' g = h' *ᵥ nuG' z z' (h⁻¹ * n⁻¹ * g * n' * h')

def GeomEqvIo : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, ∀ h' ∈ UWset k r z', ∀ n' ∈ Nset k r, ∀ g ∈ posG k r z z',
      ioG z z' g = h * ioG z z' (h⁻¹ * n⁻¹ * g * n' * h') * h'⁻¹

def GeomAtGq : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 1 ≤ k →
    C2.StdZ k r z → C2.StdZ k r z' → IsSection k r z z' μsec →
    ∀ (c : Fin r → ℂ) (ζ : ℂ), (∀ l, c l ≠ 0) → Tz k r z * Tz k r z' < Complex.normSq ζ →
      nuG z z' (bigCell k r c (μsec ζ)) = phD c • nu0 k r z z' μsec ζ ∧
        nuG' z z' (bigCell k r c (μsec ζ)) = conj (phD c) • nu0' k r z z' μsec ζ ∧
          ioG z z' (bigCell k r c (μsec ζ)) = io0 k r z z' μsec ζ

def GeomBd0 : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' →
    ∃ C : ℝ, ∀ g ∈ posG k r z z', ‖nuG z z' g‖ ≤ C ∧ ‖nuG' z z' g‖ ≤ C ∧ ‖ioG z z' g‖ ≤ C

def UBLInvSqrt : Prop :=
  ∀ (k r d : ℕ) (P : B.Mat k r → ℂ), U.IsPolyDeg d P → ∀ (S : Set (B.Mat k r)), S ⊆ B.GV k r →
    ∀ c : ℝ, 0 < c → (∀ g ∈ S, c ≤ (P g).re) → ∀ n : ℕ,
      UBL (fun g => (((Real.sqrt (P g).re)⁻¹ : ℝ) : ℂ)) S n 0 d

def GeomUBL : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → C2.StdZ k r z → C2.StdZ k r z' → ∀ ε : ℝ, 0 < ε →
    (∃ e γ : ℕ, e ≤ 4 * (r + 1) ∧ γ ≤ 2 * (r + 1) ∧ ∀ n, UBL (nuG z z') (geG k r z z' ε) n e γ) ∧
    (∃ e γ : ℕ, e ≤ 4 * (r + 1) ∧ γ ≤ 2 * (r + 1) ∧ ∀ n, UBL (nuG' z z') (geG k r z z' ε) n e γ) ∧
    (∃ e γ : ℕ, e ≤ 4 * (r + 1) ∧ γ ≤ 2 * (r + 1) ∧ ∀ n, UBL (ioG z z') (geG k r z z' ε) n e γ)

def GeomAssemble : Prop :=
  GeomSmooth → GeomEqvNu → GeomEqvIo → GeomAtGq → GeomBd0 → GeomUBL → SSnGeom

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HerAnalyticFOfCls
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Gen

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
variable {𝒜 : StarSubalgebra ℂ A}

theorem Ts_mem (σ : Site A) (hp : σ.p ∈ 𝒜) (hc : σ.c ∈ 𝒜) (hci : σ.ci ∈ 𝒜) (Y : ℂ) (i j : Fin 2) :
    Ts σ Y i j ∈ 𝒜 := by
  unfold Ts Formalism.YangianSpanCharacter.T.Tm
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  · exact add_mem (algebraMap_mem 𝒜 Y) hp
  · exact neg_mem hc
  · exact hci
  · exact zero_mem 𝒜

theorem bT_mem (σ : Site A) (hp : σ.p ∈ 𝒜) (hc : σ.c ∈ 𝒜) (hci : σ.ci ∈ 𝒜) (w : List (Letter ℂ S)) :
    bT σ w ∈ entSub 𝒜 := by
  induction w with
  | nil => exact (entSub 𝒜).one_mem
  | cons l w ih =>
    rw [bT]
    refine (entSub 𝒜).mul_mem (ins_mem _ fun i j => ?_) ih
    show io ((if l.plus then Ts σ l.pt else (Ts σ l.pt).map star) i j) ∈ entSub 𝒜
    apply io_mem
    split_ifs
    · exact Ts_mem σ hp hc hci l.pt i j
    · exact (star_mem (Ts_mem σ hp hc hci l.pt i j) : star _ ∈ 𝒜)

end Gen

section Lev

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

end Lev

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadTypesAtOfWeight
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Topx1
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBI

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem exAt (p : KB.Pl P Wp Wq) {ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ}
    {m₀r : B.Mat P.k (P.r - P.r)} (hLev : LevFrame p ν'r m₀r)
    (Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
      (p.T.bs P.r).π')
    (x : (Fin (JC.parLev P P.r).r → ℂ) × Q.Mx (JC.parLev P P.r).k (JC.parLev P P.r).r)
    (hx : x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z')
    {γ₀ : B.Mat P.k (P.r - P.r)} (hγG : γ₀ ∈ B.GV P.k (P.r - P.r))
    (hζ : Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ =
      Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)
    (hγF : D.IsDFrame (p.T.bs P.r) ν'r m₀r γ₀) :
    ∑ ρ : M.Ty P, (p.TP.E ρ).comp ((Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀) =
      (Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀ := by
  classical
  have hV := grpInt_at_dframe p hLev Ψ x hx hγG hζ hγF
  have hPl : Q.IsPlace (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' :=
    Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T ⟨P.r, by omega⟩ p.hP
  have hn : P.r + (P.r - P.r) = P.r := by omega
  have hz : D.castV hn (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) = p.T.base.z := p.T.z_lev P.r le_rfl
  have hν : D.castV hn (liftVec P.k P.r (P.r - P.r) (m₀r *ᵥ ν'r)) = p.m₀ *ᵥ p.ν' := by
    rw [← Formalism.FourierDecayAlt.P.DiagonalScalarMatrices.castV_mulVec_lift hn, hLev.1, hLev.2.1]
  have hπ : (p.T.bs P.r).π = fun y => p.T.base.π (D.castM hn (ιLev P.k P.r (P.r - P.r) y)) :=
    funext fun y => p.T.π_lev P.r le_rfl y
  have hcap : ∀ (Bs : Fin (P.k - 1) → Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (w : ℂ) (v : Wp),
      Q.capRep P.k (P.r - P.r) (p.T.bs P.r).π Bs w v =
        Q.capRep P.k P.r p.T.base.π (fun c => D.castV hn (liftVec P.k P.r (P.r - P.r) (Bs c))) w v := by
    intro Bs w v
    rw [Formalism.FourierDecayAlt.P.DiagonalScalarMatrices.capRep_lift_cast hn, hπ]
  have hfr : ∀ Bs : Fin (P.k - 1) → Fin (2 * (P.r - P.r) + P.k + 1) → ℂ,
      Q.IsFrameOf P.k (P.r - P.r) [(p.T.bs P.r).z, m₀r *ᵥ ν'r] Bs →
        Q.IsFrameOf P.k P.r [p.T.base.z, p.m₀ *ᵥ p.ν'] (fun c => D.castV hn (liftVec P.k P.r (P.r - P.r) (Bs c))) := by
    intro Bs hB
    have h := Formalism.FourierDecayAlt.P.DiagonalScalarMatrices.frame_lift_cast hn _ Bs hB
    simpa only [List.map_cons, List.map_nil, hz, hν] using h
  let TP' : Top.TypeProj (JC.parLev P P.r) (p.T.bs P.r).π (p.T.bs P.r).z (m₀r *ᵥ ν'r) :=
    { E := p.TP.E
      idem := p.TP.idem
      orth := p.TP.orth
      selfAdj := p.TP.selfAdj
      eigen := fun Bs hB ρ w v => (hcap Bs w _).trans (p.TP.eigen _ (hfr Bs hB) ρ w v)
      full := fun Bs hB ρ v h => p.TP.full _ (hfr Bs hB) ρ v fun w => (hcap Bs w v).symm.trans (h w) }
  exact types_of_grpInt (JC.parLev P P.r) (p.T.bs P.r) ν'r m₀r TP' hPl hLev.2.2 _ hV

def HeadWeightAt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (Cb : ℝ) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → LevFrame p ν'r m₀r →
    ∀ x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z',
    ∀ γ₀ ∈ B.GV P.k (P.r - P.r),
      Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ =
        Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 →
      D.IsDFrame (p.T.bs P.r) ν'r m₀r γ₀ →
    (∀ h : C.LPt, D.IsLocPt h P.r →
        ∀ (y : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
          (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π') e,
        (P5.act ((Fr.ofWord L st (D.positionted w)).d L) y e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀ =
          ∑ ρ : M.Ty P, ((Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w
              (h ++ [(1, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)]) e ρ ^ 2 : ℝ) : ℂ) •
            (p.TP.E ρ).comp ((y e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀))

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem head_types_at_of_weight : PBI.HeadWeightAt → PBI.HeadTypesAt := by
  intro hW Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb ν'r m₀r hD hI hC hCut hLev x hx γ₀ hγG hζ hγF
  exact ⟨fun Ψ => PBI.exAt p hLev Ψ x hx hγG hζ hγF,
    hW Wp Wq P p F w X μ L st Cb ν'r m₀r hD hI hC hCut hLev x hx γ₀ hγG hζ hγF⟩

end Formalism.FourierDecayAlt.P
end
end
