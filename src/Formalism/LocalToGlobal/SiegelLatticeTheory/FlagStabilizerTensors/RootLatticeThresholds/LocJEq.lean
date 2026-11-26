module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RootHaarLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEq
noncomputable section

open scoped Classical
open MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.LocJEq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

theorem transp_mem (τ : D.what₂.Tau) {m : MatKR D.R.k D.R.rS} (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    C.Q τ * m * C.Qi τ ∈ UJset (X.B.I.ε (vOf X τ)) := by
  obtain ⟨-, h2, h3, -⟩ := C.isT τ
  have hm' : mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm
  show (C.Q τ * m * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * m * C.Qi τ) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ))
  calc (C.Q τ * m * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * m * C.Qi τ)
      = (C.Qi τ)ᴴ * (mᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * m) * C.Qi τ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ := by
        rw [h3, hm']
    _ = (C.Q τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
        rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

def Smap (τ : D.what₂.Tau) (γ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  Matrix.of.symm (C.Qi τ * umat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹)

theorem smap_cont (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : Continuous (Smap C τ γ) := by
  have hc : Continuous fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => umat (γ⁻¹ * z) :=
    (Units.continuous_val.comp continuous_subtype_val).comp (continuous_const.mul continuous_id)
  have h2 : Continuous fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      C.Qi τ * umat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹ :=
    ((continuous_const.matrix_mul hc).matrix_mul continuous_const).matrix_mul continuous_const
  exact h2

theorem sig_mul (τ : D.what₂.Tau) {a b : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ} (ha : a ∈ UJset (X.B.I.ε (vOf X τ)))
    (hb : b ∈ UJset (X.B.I.ε (vOf X τ))) (x : X.B.H (vOf X τ)) :
    X.B.σ (vOf X τ) (a * b) x = X.B.σ (vOf X τ) a (X.B.σ (vOf X τ) b x) := by
  rw [(X.ds (vOf X τ)).2.2.1.1.2 a ha b hb]
  rfl

theorem sig_one (τ : D.what₂.Tau) (x : X.B.H (vOf X τ)) : X.B.σ (vOf X τ) 1 x = x := by
  rw [(X.ds (vOf X τ)).2.2.1.1.1]
  rfl

theorem umat_mem (τ : D.what₂.Tau) (z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : umat z ∈ UJset (X.B.I.ε (vOf X τ)) := z.2

theorem QQi_left (τ : D.what₂.Tau) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) : C.Q τ * (C.Qi τ * M) = M := by
  rw [← Matrix.mul_assoc, (C.isT τ).2.1, Matrix.one_mul]

variable (hB : WuBessel C)

theorem wloc_eq (u : D.what₂.Word) (τ : D.what₂.Tau) (z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    X.Wloc u (vOf X τ) z = bOf hB u τ (X.B.σ (vOf X τ) (umat z) (X.B.w (vOf X τ))) :=
  (hB u τ).choose_spec.2 z

private theorem isUnit_det_y (τ : D.what₂.Tau) : IsUnit (C.y τ).det := by
  obtain ⟨h1, h2, h3, -⟩ := C.isT τ
  set J := Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) with hJdef
  have hy : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
  have hJ : J * J = 1 := by rw [hJdef, Formalism.REAL.Jm_mul_self]
  have hK : (C.Qi τ * J * (C.Qi τ)ᴴ) * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS = 1 := by
    rw [← h3]
    calc C.Qi τ * J * (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * J * C.Q τ)
        = C.Qi τ * (J * ((C.Q τ * C.Qi τ)ᴴ * (J * C.Q τ))) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, ← Matrix.mul_assoc J J, hJ, Matrix.one_mul, h1]
  refine Matrix.isUnit_det_of_left_inverse (B := C.Qi τ * J * (C.Qi τ)ᴴ * (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) ?_
  calc C.Qi τ * J * (C.Qi τ)ᴴ * (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ
      = (C.Qi τ * J * (C.Qi τ)ᴴ) * ((C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hy, hK]

theorem y_facts (τ : D.what₂.Tau) :
    C.Q τ * (C.y τ)⁻¹ * C.Qi τ ∈ UJset (X.B.I.ε (vOf X τ)) ∧ C.Q τ * C.y τ * C.Qi τ ∈ UJset (X.B.I.ε (vOf X τ)) ∧
      (C.Q τ * (C.y τ)⁻¹ * C.Qi τ) * (C.Q τ * C.y τ * C.Qi τ) = 1 := by
  have hu := isUnit_det_y C τ
  have hyi : (C.y τ)⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
    have hy : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
    have e1 : C.y τ * (C.y τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
    show ((C.y τ)⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ)⁻¹ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
    calc ((C.y τ)⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ)⁻¹
        = ((C.y τ)⁻¹)ᴴ * ((C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ) * (C.y τ)⁻¹ := by rw [hy]
      _ = (C.y τ * (C.y τ)⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ * (C.y τ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by
          rw [e1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  refine ⟨transp_mem C τ hyi, transp_mem C τ (C.y_mem τ), ?_⟩
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  have e2 : (C.y τ)⁻¹ * C.y τ = 1 := Matrix.nonsing_inv_mul _ hu
  calc C.Q τ * (C.y τ)⁻¹ * C.Qi τ * (C.Q τ * C.y τ * C.Qi τ)
      = C.Q τ * ((C.y τ)⁻¹ * ((C.Qi τ * C.Q τ) * (C.y τ * C.Qi τ))) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [h1, Matrix.one_mul, ← Matrix.mul_assoc (C.y τ)⁻¹ (C.y τ), e2, Matrix.one_mul, h2]

theorem phi_def (u u' : D.what₂.Word) (τ : D.what₂.Tau) (m : MatKR D.R.k D.R.rS) :
    (locS hB u u' τ).Φ m = bOf hB u τ (X.B.σ (vOf X τ) (C.Q τ * m * C.Qi τ)
      (X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ)))) := rfl

theorem phi'_def (u u' : D.what₂.Word) (τ : D.what₂.Tau) (m : MatKR D.R.k D.R.rS) :
    (locS hB u u' τ).Φ' m = sclOf hB u u' τ • bOf hB u' τ (X.B.σ (vOf X τ) (C.Q τ * m * C.Qi τ)
      (X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ)))) := rfl

theorem phi_S (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z)) = X.Wloc u (vOf X τ) z := by
  obtain ⟨hy1, hy2, hy3⟩ := y_facts C τ
  have hg : uMat γ * umat γ⁻¹ = 1 := Units.mul_inv (γ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ)
  have hg' : ∀ M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, uMat γ * (umat γ⁻¹ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hg, Matrix.one_mul]
  have hM : C.Q τ * (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z)) * C.Qi τ =
      umat z * (C.Q τ * (C.y τ)⁻¹ * C.Qi τ) := by
    rw [show Matrix.of (Smap C τ γ z) = C.Qi τ * (umat γ⁻¹ * umat z) * C.Q τ * (C.y τ)⁻¹ from rfl]
    simp only [trG, Matrix.mul_assoc, QQi_left C τ, hg']
  have key : X.B.σ (vOf X τ) (C.Q τ * (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z)) * C.Qi τ)
      (X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ))) =
      X.B.σ (vOf X τ) (umat z) (X.B.w (vOf X τ)) := by
    rw [hM, sig_mul τ (umat_mem τ z) hy1, ← sig_mul τ hy1 hy2, hy3, sig_one τ]
  rw [phi_def C hB u u' τ, wloc_eq C hB u τ z, key]

theorem phi'_S (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (locS hB u u' τ).Φ' (Matrix.of (Smap C τ γ z)) = sclOf hB u u' τ • X.Wloc u' (vOf X τ) (γ⁻¹ * z) := by
  obtain ⟨hy1, hy2, hy3⟩ := y_facts C τ
  have hM : C.Q τ * Matrix.of (Smap C τ γ z) * C.Qi τ = umat (γ⁻¹ * z) * (C.Q τ * (C.y τ)⁻¹ * C.Qi τ) := by
    rw [show Matrix.of (Smap C τ γ z) = C.Qi τ * (umat γ⁻¹ * umat z) * C.Q τ * (C.y τ)⁻¹ from rfl]
    show _ = (umat γ⁻¹ * umat z) * _
    simp only [Matrix.mul_assoc, QQi_left C τ]
  have key : X.B.σ (vOf X τ) (C.Q τ * Matrix.of (Smap C τ γ z) * C.Qi τ)
      (X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ))) =
      X.B.σ (vOf X τ) (umat (γ⁻¹ * z)) (X.B.w (vOf X τ)) := by
    rw [hM, sig_mul τ (umat_mem τ (γ⁻¹ * z)) hy1, ← sig_mul τ hy1 hy2, hy3, sig_one τ]
  rw [phi'_def C hB u u' τ, wloc_eq C hB u' τ (γ⁻¹ * z), key]

theorem smulRight_smul {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] (a : V) (b : V') (c : ℂ) (hc : (starRingEnd ℂ) c = c) :
    (innerSL ℂ (c • b)).smulRight a = c • Formalism.L2.SG.TermOp.rk1 a b := by
  ext x
  simp [Formalism.L2.SG.TermOp.rk1, inner_smul_left, hc, smul_smul]

theorem locJ_map_eq (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))))
    (hG : AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of x))) (ν.map (Smap C τ γ))) :
    (locS hB u u' τ).J (ν.map (Smap C τ γ)) (trG (C.Q τ) (C.Qi τ) γ) =
      ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) •
        (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ)); Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) γ) := by
  have hc : (starRingEnd ℂ) (sclOf hB u u' τ) = sclOf hB u u' τ := by
    unfold sclOf; exact Complex.conj_ofReal _
  have hpt : ∀ z, (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of (Smap C τ γ z)))).smulRight
      ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z))) =
      sclOf hB u u' τ • Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) z) (X.Wloc u' (vOf X τ) (γ⁻¹ * z)) := by
    intro z
    rw [phi_S C hB, phi'_S C hB]
    exact smulRight_smul _ _ _ hc
  unfold LocS.J ampJ Jv Formalism.L2.SG.TermOp.OO
  rw [Measure.restrict_univ, integral_map (smap_cont C τ γ).measurable.aemeasurable hG,
    integral_congr_ae (ae_of_all _ hpt)]
  erw [integral_smul, smul_smul]
  rfl

def ujOf' {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M ∈ UJset ε) : Formalism.REAL.UJ ε :=
  ⟨⟨M, Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε, by
      have h : Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε * M = 1 := by
        have hM' : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε := hM
        rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM', Formalism.REAL.Jm_mul_self]
      rw [← Matrix.inv_eq_left_inv h]
      exact Matrix.mul_nonsing_inv M (Matrix.isUnit_det_of_left_inverse h), by
      have hM' : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε := hM
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM', Formalism.REAL.Jm_mul_self]⟩, hM⟩

theorem umat_ujOf' {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M ∈ UJset ε) :
    umat (ujOf' M hM) = M := rfl

theorem unit_det_y (τ : D.what₂.Tau) : IsUnit (C.y τ).det := isUnit_det_y C τ

theorem back_smap (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) :
    umat γ * (C.Q τ * (C.Qi τ * (umat γ⁻¹ * A) * C.Q τ * (C.y τ)⁻¹) * C.y τ * C.Qi τ) = A := by
  have hy : (C.y τ)⁻¹ * C.y τ = 1 := Matrix.nonsing_inv_mul _ (unit_det_y C τ)
  obtain ⟨-, h2, -, -⟩ := C.isT τ
  have hg : umat γ * umat γ⁻¹ = 1 := Units.mul_inv (γ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ)
  calc umat γ * (C.Q τ * (C.Qi τ * (umat γ⁻¹ * A) * C.Q τ * (C.y τ)⁻¹) * C.y τ * C.Qi τ)
      = umat γ * ((C.Q τ * C.Qi τ) * (umat γ⁻¹ * A) * C.Q τ * ((C.y τ)⁻¹ * C.y τ) * C.Qi τ) := by
        simp only [Matrix.mul_assoc]
    _ = A := by
        rw [h2, hy, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc (umat γ⁻¹ * A) (C.Q τ) (C.Qi τ), h2,
          Matrix.mul_one, ← Matrix.mul_assoc, hg, Matrix.one_mul]

theorem smap_val (τ : D.what₂.Tau) (γ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix.of (Smap C τ γ z) = C.Qi τ * (umat γ⁻¹ * umat z) * C.Q τ * (C.y τ)⁻¹ := by
  rfl

theorem range_smap (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Set.range (Smap C τ γ) =
      {x | umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ))} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    show umat γ * (C.Q τ * Matrix.of (Smap C τ γ z) * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ))
    rw [smap_val C τ γ z, back_smap C τ γ (umat z)]
    exact umat_mem τ z
  · intro hx
    have hx' : umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ)) := hx
    refine ⟨ujOf' _ hx', ?_⟩
    apply Matrix.of.injective
    rw [smap_val C τ γ (ujOf' _ hx'), umat_ujOf' _ hx']
    have hg : umat γ⁻¹ * umat γ = 1 := Units.inv_mul (γ : (Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ)ˣ)
    obtain ⟨h1, -, -, -⟩ := C.isT τ
    have hy : C.y τ * (C.y τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (unit_det_y C τ)
    calc C.Qi τ * (umat γ⁻¹ * (umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ))) * C.Q τ * (C.y τ)⁻¹
        = (C.Qi τ * C.Q τ) * Matrix.of x * (C.y τ * ((C.Qi τ * C.Q τ) * (C.y τ)⁻¹)) := by
          rw [← Matrix.mul_assoc (umat γ⁻¹) (umat γ), hg, Matrix.one_mul]
          simp only [Matrix.mul_assoc]
      _ = Matrix.of x := by
          rw [h1, Matrix.one_mul, Matrix.one_mul, hy, Matrix.mul_one]

end Formalism.L2.SG.Pf.LocJEq
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOfCore
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BaseOf

variable {k r : ℕ}

theorem trG_closedEmb {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h2 : Q * Qi = 1) :
    Topology.IsClosedEmbedding (fun γ : Formalism.REAL.UJ ε => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ) : Mt k r)) := by
  subst hn
  have h1 : Qi * Q = 1 := mul_eq_one_comm.mp h2
  obtain ⟨hemb, -⟩ := Formalism.REAL.isClosedEmbeddingMatrix (2 * r + k + 1) ε
  let L : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ ≃ₜ Mt k r :=
    { toFun := fun M => Matrix.of.symm (Qi * M * Q)
      invFun := fun M => Q * Matrix.of M * Qi
      left_inv := fun M => by
        show Q * Matrix.of (Matrix.of.symm (Qi * M * Q)) * Qi = M
        rw [Equiv.apply_symm_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul,
          Matrix.mul_assoc, h2, Matrix.mul_one]
      right_inv := fun M => by
        show Matrix.of.symm (Qi * (Q * Matrix.of M * Qi) * Q) = M
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
        rfl
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  exact L.isClosedEmbedding.comp hemb

private theorem isUnit_det_of_mem_UH_Hpk {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : IsUnit g.det := by
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at hd
  have hH : (Hpk k r).det ≠ 0 := (Formalism.FourierDecayAlt.P.B2x2.hpk_unit k r).ne_zero
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at hd
  exact hH hd.symm

private theorem measurable_inv_apply (i j : Fin (2 * r + k + 1)) :
    Measurable fun x : Mt k r => (Matrix.of x)⁻¹ i j := by
  have e : (fun x : Mt k r => (Matrix.of x)⁻¹ i j) =
      fun x => (Matrix.of x).det⁻¹ * (Matrix.of x).adjugate i j := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [e]
  have hc : Continuous fun x : Mt k r =>
      (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := continuous_id
  exact hc.matrix_det.measurable.inv.mul (hc.matrix_adjugate.matrix_elem i j).measurable

theorem muS_swap {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {μW : Measure (Mt k r)} (hW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) {μN : Measure (Mt k r)}
    (hNB : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN) :
    (μN.prod μW).map (fun p => (Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2) : Mt k r)) = Formalism.MainNotions.S.muS μW μN := by
  haveI : SigmaFinite μW := hW.1
  haveI : IsFiniteMeasureOnCompacts μN := ⟨fun K hK => hNB.finite_compact K hK⟩
  haveI : SigmaFinite μN := inferInstance
  have hconj := Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r z μN hz hT hNB
  have hco : ∀ i j, Measurable fun p : Mt k r × Mt k r => p.1 i j :=
    fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_fst)
  have hco2 : ∀ i j, Measurable fun p : Mt k r × Mt k r => p.2 i j :=
    fun i j => (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_snd)
  have hmul12 : Measurable fun p : Mt k r × Mt k r => (Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2) : Mt k r) := by
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.of_symm_apply]
    exact Finset.measurable_sum _ fun l _ => (hco i l).mul (hco2 l j)
  have hmul21 : Measurable fun p : Mt k r × Mt k r => (Matrix.of.symm (Matrix.of p.2 * Matrix.of p.1) : Mt k r) := by
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.of_symm_apply]
    exact Finset.measurable_sum _ fun l _ => (hco2 i l).mul (hco l j)
  have hcm : Measurable (Function.uncurry fun (h n : Mt k r) => conjM (Matrix.of h) n) := by
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    simp only [Function.uncurry, conjM, Matrix.mul_apply, Matrix.of_apply]
    exact Finset.measurable_sum _ fun l _ =>
      (Finset.measurable_sum _ fun m _ => (hco i m).mul (hco2 m l)).mul ((measurable_inv_apply l j).comp measurable_fst)
  have haeW : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := ae_iff.mpr hW.2.2.1
  have hsk : MeasurePreserving (fun p : Mt k r × Mt k r => (p.1, conjM (Matrix.of p.1) p.2))
      (μW.prod μN) (μW.prod μN) :=
    (MeasurePreserving.id μW).skew_product hcm (haeW.mono fun x hx => hconj _ hx)
  have hae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := by
    rw [ae_iff]
    refine measure_mono_null (show {p : Mt k r × Mt k r | ¬ (Matrix.of p.1 ∈ UWset k r z)} ⊆
        {x : Mt k r | Matrix.of x ∉ UWset k r z} ×ˢ (Set.univ : Set (Mt k r)) from
      fun p hp => ⟨hp, Set.mem_univ _⟩) ?_
    rw [Measure.prod_prod, hW.2.2.1, zero_mul]
  calc (μN.prod μW).map (fun p => (Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2) : Mt k r))
      = ((μW.prod μN).map Prod.swap).map (fun p => (Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2) : Mt k r)) := by
        rw [Measure.prod_swap]
    _ = (μW.prod μN).map (fun p => (Matrix.of.symm (Matrix.of p.2 * Matrix.of p.1) : Mt k r)) := by
        rw [Measure.map_map hmul12 measurable_swap]
        rfl
    _ = ((μW.prod μN).map (fun p : Mt k r × Mt k r => (p.1, conjM (Matrix.of p.1) p.2))).map
          (fun p => (Matrix.of.symm (Matrix.of p.2 * Matrix.of p.1) : Mt k r)) := by
        rw [hsk.map_eq]
    _ = (μW.prod μN).map (fun p : Mt k r × Mt k r =>
          (Matrix.of.symm (Matrix.of (conjM (Matrix.of p.1) p.2) * Matrix.of p.1) : Mt k r)) := by
        rw [Measure.map_map hmul21 hsk.measurable]
        rfl
    _ = Formalism.MainNotions.S.muS μW μN := by
        unfold Formalism.MainNotions.S.muS
        refine Measure.map_congr (hae.mono fun p hp => ?_)
        have hu := isUnit_det_of_mem_UH_Hpk hp.1
        funext i j
        show ((Matrix.of p.1 * Matrix.of p.2 * (Matrix.of p.1)⁻¹) * Matrix.of p.1) i j =
          (Matrix.of p.1 * Matrix.of p.2) i j
        rw [Matrix.mul_assoc _ _ (Matrix.of p.1), Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem muS_loc {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {μW : Measure (Mt k r)} (hW : Formalism.MainNotions.S.IsHaarOn (UWset k r z) μW) (hW1 : μW Set.univ = 1)
    {μN : Measure (Mt k r)} (hNB : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN) :
    ∃ μS : Measure (Formalism.REAL.UJ ε),
      Formalism.L2.SG.RealObj.IsHaarLoc {γ | Formalism.L2.SG.RealObj.trG Q Qi γ ∈ Sset k r z} μS ∧
      μS.map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ)) =
        (μN.prod μW).map (fun p => Matrix.of.symm (Matrix.of p.1 * Matrix.of p.2)) := by
  have hSμ := Formalism.L2.SG.Pf.Choice.isHaarOn_muS_gen hz hT hW hW1 hNB
  rw [muS_swap hz hT hW hNB]
  subst hn
  have h1' : Qi * Q = 1 := mul_eq_one_comm.mp h2
  obtain ⟨T, hTdef⟩ : ∃ T : Formalism.REAL.UJ ε → Mt k r,
      T = fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ) := ⟨_, rfl⟩
  have hemb : MeasurableEmbedding T := by
    rw [hTdef]
    exact (trG_closedEmb rfl ε h2).measurableEmbedding
  have hJ : Qiᴴ * Hpk k r * Qi = Formalism.REAL.Jm ε := by
    rw [← hg]
    calc Qiᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * Qi = (Q * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * Qi) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hUHrange : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, M ∈ UH (Hpk k r) →
      ∃ γ : Formalism.REAL.UJ ε, Formalism.L2.SG.RealObj.trG Q Qi γ = M := by
    intro M hM
    have hMd := isUnit_det_of_mem_UH_Hpk hM
    have hQd : IsUnit (Q.det * Qi.det) := by
      rw [← Matrix.det_mul, h2, Matrix.det_one]
      exact isUnit_one
    have hu : IsUnit (Q * M * Qi) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_mul]
      have e : Q.det * M.det * Qi.det = (Q.det * Qi.det) * M.det := by ring
      rw [e]
      exact hQd.mul hMd
    have hmem : hu.unit ∈ Formalism.REAL.UJ ε := by
      show Formalism.REAL.inUJ ε ((hu.unit : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
      rw [IsUnit.unit_spec]
      unfold Formalism.REAL.inUJ
      have hM' : Mᴴ * Hpk k r * M = Hpk k r := hM
      calc (Q * M * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * M * Qi)
          = Qiᴴ * (Mᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * M) * Qi := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε := by rw [hg, hM', hJ]
    refine ⟨⟨hu.unit, hmem⟩, ?_⟩
    show Qi * ((hu.unit : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) * Q = M
    rw [IsUnit.unit_spec]
    simp only [Matrix.mul_assoc]
    rw [h1', Matrix.mul_one, ← Matrix.mul_assoc, h1', Matrix.one_mul]
  have hrange : ∀ᵐ x ∂(Formalism.MainNotions.S.muS μW μN), x ∈ Set.range T := by
    have h0 : ∀ᵐ x ∂(Formalism.MainNotions.S.muS μW μN), Matrix.of x ∈ Sset k r z := ae_iff.mpr hSμ.2.2.1
    refine h0.mono fun x hx => ?_
    obtain ⟨h, hh, m, hm, hx'⟩ := hx
    have hUH : Matrix.of x ∈ UH (Hpk k r) := by
      rw [hx']
      show (h * m)ᴴ * Hpk k r * (h * m) = Hpk k r
      have hh' : hᴴ * Hpk k r * h = Hpk k r := hh.1
      have hm' : mᴴ * Hpk k r * m = Hpk k r := hm.1
      calc (h * m)ᴴ * Hpk k r * (h * m) = mᴴ * (hᴴ * Hpk k r * h) * m := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Hpk k r := by rw [hh', hm']
    obtain ⟨γ, hγ⟩ := hUHrange _ hUH
    exact ⟨γ, by rw [hTdef]; exact hγ⟩
  have hmap : (Measure.comap T (Formalism.MainNotions.S.muS μW μN)).map T = Formalism.MainNotions.S.muS μW μN := by
    rw [hemb.map_comap, Measure.restrict_eq_self_of_ae_mem hrange]
  have hmulT : ∀ s x : Formalism.REAL.UJ ε,
      T (s * x) = lmulM (Formalism.L2.SG.RealObj.trG Q Qi s) (T x) := by
    intro s x
    rw [hTdef]
    show (Qi * (((s * x : Formalism.REAL.UJ ε) : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) :
        Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * Q) =
      (Qi * ((s : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) :
        Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * Q) *
      (Qi * ((x : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) :
        Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * Q)
    rw [Subgroup.coe_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q Qi, h2, Matrix.one_mul]
  have hTm : Measurable T := hemb.measurable
  refine ⟨Measure.comap T (Formalism.MainNotions.S.muS μW μN), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact SigmaFinite.of_map _ hTm.aemeasurable (by rw [hmap]; exact hSμ.1)
  · intro h0
    apply hSμ.2.1
    rw [← hmap, h0, Measure.map_zero]
  · rw [hemb.comap_apply]
    refine measure_mono_null ?_ hSμ.2.2.1
    rintro _ ⟨γ, hγ, rfl⟩
    rw [hTdef]
    exact hγ
  · intro s hs
    have hLm : Measurable (lmulM (Formalism.L2.SG.RealObj.trG Q Qi s) : Mt k r → Mt k r) := by
      refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
      simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
      exact Finset.measurable_sum _ fun l _ => measurable_const.mul ((measurable_pi_apply j).comp (measurable_pi_apply l))
    have hsm : Measurable fun x : Formalism.REAL.UJ ε => s * x := measurable_const_mul s
    have e1 : ((Measure.comap T (Formalism.MainNotions.S.muS μW μN)).map (fun x => s * x)).map T =
        (Measure.comap T (Formalism.MainNotions.S.muS μW μN)).map T := by
      rw [Measure.map_map hTm hsm]
      have hc : T ∘ (fun x => s * x) = lmulM (Formalism.L2.SG.RealObj.trG Q Qi s) ∘ T := funext (hmulT s)
      rw [hc, ← Measure.map_map hLm hTm, hmap, hSμ.2.2.2 _ hs]
    calc (Measure.comap T (Formalism.MainNotions.S.muS μW μN)).map (fun x => s * x)
        = Measure.comap T (((Measure.comap T (Formalism.MainNotions.S.muS μW μN)).map (fun x => s * x)).map T) :=
          (hemb.comap_map _).symm
      _ = Measure.comap T ((Measure.comap T (Formalism.MainNotions.S.muS μW μN)).map T) := by rw [e1]
      _ = Measure.comap T (Formalism.MainNotions.S.muS μW μN) := hemb.comap_map _
  · subst hTdef
    exact hmap

theorem haarG_B {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h2 : Q * Qi = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Hpk k r) :
    Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.B.GV k r)
      ((Formalism.REAL.muG ε).map (fun γ => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ) : Mt k r))) := by
  have hSK := Formalism.L2.SG.Pf.Choice.haar_tr hn ε Q Qi h2 hg
  have hce := trG_closedEmb hn ε h2
  obtain ⟨hz, hT1⟩ := Formalism.FourierDecayAlt.P.base_vector_exists k r
  have hT0 : 0 < Tz k r (bvec (wI k r (Fin.last k))) := by rw [hT1]; exact one_pos
  have hright := (quotient_measure_unitary_group k r _ hz hT0).2.2.2.1 _ hSK
  obtain ⟨hsf, hne, hcon, hleft⟩ := hSK
  refine ⟨hcon, hleft, hright, fun K hK => ?_, hne⟩
  rw [Measure.map_apply hce.measurable hK.isClosed.measurableSet]
  exact (hce.isCompact_preimage hK).measure_lt_top

theorem sec_exists (hk : 1 ≤ k) (z z' : Fin (2 * r + k + 1) → ℂ) (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hf : ∃ g, Formalism.MainNotions.S.IsFrameW k r z g) (hf' : ∃ g, Formalism.MainNotions.S.IsFrameW k r z' g) :
    ∃ μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsSection k r z z' μsec := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  exact Formalism.MainNotions.S.Inh.big_cell_section_exists k0 r z z' hT hT' hf hf'

open Formalism.BasicNotions in
theorem k_pos (D : D7) : 1 ≤ D.R.k := by
  have h := D.R.m_add_three_le_k
  omega

end Formalism.L2.SG.Pf.BaseOf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierOf
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

structure CarrierIn {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : Type 1 where
  Wp : InfinitePlace D.host.E → Type
  Wq : InfinitePlace D.host.E → Type
  [pN : ∀ x, NormedAddCommGroup (Wp x)]
  [pI : ∀ x, InnerProductSpace ℂ (Wp x)]
  [qN : ∀ x, NormedAddCommGroup (Wq x)]
  [qI : ∀ x, InnerProductSpace ℂ (Wq x)]
  [pF : ∀ x, FiniteDimensional ℂ (Wp x)]
  [qF : ∀ x, FiniteDimensional ℂ (Wq x)]
  nf : ℕ
  pl : Fin nf ≃ InfinitePlace D.host.E
  emb : Fin nf → (D.host.E →+* ℂ)
  hemb : ∀ v, InfinitePlace.mk (emb v) = pl v
  G : Formalism.FourierDecayAlt.Sz.Glob (InfinitePlace D.host.E)
  CA : ℝ
  de : ℕ → ℝ
  de' : ℕ → ℝ
  l : ℕ
  grid : Fin nf → ℕ → Finset ℝ
  grid1 : Fin nf → Finset ℝ
  hv : G.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2
  T : ∀ j : Fin nf, Formalism.FourierDecayAlt.D.LevTower G.k G.r (Wp (pl j)) (Wq (pl j))
  hT : ∀ j, Formalism.QuantumDeterminants.Tz G.k G.r (T j).base.z = ((D.mem u).A.T : ℝ) ∧
    Formalism.QuantumDeterminants.Tz G.k G.r (T j).base.z' = ((D.mem u').A.T : ℝ)
  fc : ∀ j : Fin nf, Formalism.FourierDecayAlt.B.Mat G.k G.r → (Wq (pl j) →L[ℂ] Wp (pl j))
  χ : ℝ → ℝ
  sg : Fin nf → ℂ
  ν' : Fin nf → Fin (2 * G.r + G.k + 1) → ℂ
  m₀ : Fin nf → Formalism.FourierDecayAlt.B.Mat G.k G.r
  top : ∀ j : Fin nf, (Formalism.FourierDecayAlt.B.Mat G.k G.r → (Wq (pl j) →L[ℂ] Wp (pl j))) → List Formalism.FourierDecayAlt.C.Letter →
    Formalism.FourierDecayAlt.C.LPt → Formalism.FourierDecayAlt.C.LPt → ℂ
  A₀ : ℝ
  τ : Fin nf ≃ InfinitePlace X.B.I.F
  Q : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin X.B.I.n) (Fin (2 * G.r + G.k + 1)) ℂ
  Qi : ∀ _ : InfinitePlace X.B.I.F, Matrix (Fin (2 * G.r + G.k + 1)) (Fin X.B.I.n) ℂ
  eP : ∀ v, Wp (pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u v
  eQ : ∀ v, Wq (pl (τ.symm v)) ≃ₗᵢ[ℂ] X.Vloc u' v

attribute [instance] CarrierIn.pN CarrierIn.pI CarrierIn.qN CarrierIn.qI CarrierIn.pF CarrierIn.qF

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def sOf (I : CarrierIn X u u') : Formalism.FourierDecayAlt.C.HidaSetting D.host.E I.Wp I.Wq where
  f := I.nf
  pl := I.pl
  emb := I.emb
  hemb := I.hemb
  G := I.G
  CA := I.CA
  de := I.de
  de' := I.de'
  T := ((D.mem u).A.T : ℝ)
  T' := ((D.mem u').A.T : ℝ)
  l := I.l
  grid := I.grid
  grid1 := I.grid1
  pd := fun j => Formalism.FourierDecayAlt.D.componentFamilySetting_ofSetting (I.T j) (I.fc j) I.χ (I.sg j) (I.ν' j) (I.m₀ j) (I.top j)
    ((I.G.g1 * I.G.g2 : ℕ) : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E) 1
  hv := I.hv
  hT := I.hT

structure ModelsFor {Wp Wq : InfinitePlace D.host.E → Type} [∀ x, NormedAddCommGroup (Wp x)]
    [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) where
  L : ∀ v : Fin S.f, Formalism.FourierDecayAlt.R.LevelData (Formalism.FourierDecayAlt.MA.A (Formalism.FourierDecayAlt.D.parOf S v)
    (Formalism.FourierDecayAlt.MA.DQ (Formalism.FourierDecayAlt.D.parOf S v))) (Formalism.FourierDecayAlt.D.parOf S v).r
  j : ∀ v : Fin S.f, Formalism.FourierDecayAlt.M.Ty (Formalism.FourierDecayAlt.D.parOf S v) →
    Formalism.FourierDecayAlt.MA.SmQ (Formalism.FourierDecayAlt.D.parOf S v).r (Formalism.FourierDecayAlt.D.parOf S v).TT
  lam : ∀ v : Fin S.f, Fin ((Formalism.FourierDecayAlt.D.parOf S v).k + 2 * (Formalism.FourierDecayAlt.D.parOf S v).r + 1) → ℝ
  c : Formalism.FourierDecayAlt.LE.Cut
  Cm : Fin S.f → ℝ
  σ : Fin S.f → ℝ
  Lw : ℕ → Fin S.f → ℝ
  Ll : ℕ → ℕ → Fin S.f → ℝ
  Ll' : ℕ → ℕ → Fin S.f → ℝ

def CarrierOf (I : CarrierIn X u u') (Mo : ModelsFor (sOf I)) : Parts X u u' where
  Wp := I.Wp
  Wq := I.Wq
  S := sOf I
  T := I.T
  f := I.fc
  χ := I.χ
  ν' := I.ν'
  m₀ := I.m₀
  top := I.top
  A₀ := I.A₀
  τ := I.τ
  Q := I.Q
  Qi := I.Qi
  eP := I.eP
  eQ := I.eQ
  L := Mo.L
  j := Mo.j
  lam := Mo.lam
  c := Mo.c
  Cm := Mo.Cm
  σ := Mo.σ
  Lw := Mo.Lw
  Ll := Mo.Ll
  Ll' := Mo.Ll'

end Formalism.L2.SG.Pf.Carrier
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPf
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.JointPf

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def OOQuot (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) → ∀ y : ∀ v, X.Vloc u' v,
      (haveI := FiniteDimensional.complete ℂ (X.Vpi u);
        Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w))
          (X.tensU u' y) =
      X.tensU u (fun v => (haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
        Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v)) (y v))

def PlaceJ (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' →
    ∀ (v : InfinitePlace X.B.I.F) (y : X.Vloc u' v),
      X.piLoc u v (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u v) v h⁻¹)
        ((haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
          Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v))
          (X.piLoc u' v (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u' v) v h') y)) =
      P.eP v
        (((((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (P.S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
            (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
          Formalism.FourierDecayAlt.D.vecV (P.T (P.τ.symm v)).base (P.ν' (P.τ.symm v)) (P.m₀ (P.τ.symm v)) (P.f (P.τ.symm v))
            (Formalism.FourierDecayAlt.D.toStd P.S.G.r P.S.g 1 (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p)))
          ((P.eQ v).symm y))

theorem jointTensor_of_steps (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hQ : OOQuot X u u' νq νl) (hP : PlaceJ P sc i0 i0' νl) : P.JointTensor sc i0 i0' νq := by
  unfold Formalism.L2.SG.Pf.Carrier.Parts.JointTensor
  intro p w hpw hγ hG h h' hF x
  rw [X.tensU_equiv, hQ w hγ hG, X.tensU_equiv]
  · exact congrArg (fun f => X.tensU u f) (funext fun v => hP p w hpw hγ hG h h' hF v (x v))
  all_goals
    first
    | exact hF.2.1
    | (intro v y hy
       have h1 := hF.1 v y hy
       nth_rewrite 1 [← h1]
       rw [Matrix.mulVec_mulVec, Pi.inv_apply]
       simp only [uMat]
       rw [← Units.val_mul, ← MulMemClass.coe_mul, inv_mul_cancel, OneMemClass.coe_one, Units.val_one,
         Matrix.one_mulVec])

end Formalism.L2.SG.Pf.Carrier.JointPf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.HermitianMatrixIdentities
noncomputable section

open Matrix Formalism.QuantumDeterminants

namespace Formalism.L2.SG.HermitianMatrixIdentities

variable {k r : ℕ}

theorem hpk_isUnit : IsUnit (Hpk k r).det := by
  exact Formalism.FourierDecayAlt.P.B2x5.isUnit_det_Hpk k r

theorem star_dot_conjT' {n m : Type*} [Fintype n] [Fintype m] (Q : Matrix n m ℂ) (x : m → ℂ) (y : n → ℂ) :
    star x ⬝ᵥ (Qᴴ *ᵥ y) = star (Q *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem herm_sum_left (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) {ι : Type} (s : Finset ι)
    (c : ι → ℂ) (v : ι → Fin (2 * r + k + 1) → ℂ) (w : Fin (2 * r + k + 1) → ℂ) :
    herm H (∑ i ∈ s, c i • v i) w = ∑ i ∈ s, c i * herm H (v i) w := by
  classical
  unfold herm
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.mulVec_add, dotProduct_add, ih,
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_sum_right (H : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) {ι : Type} (s : Finset ι)
    (c : ι → ℂ) (v : Fin (2 * r + k + 1) → ℂ) (w : ι → Fin (2 * r + k + 1) → ℂ) :
    herm H v (∑ i ∈ s, c i • w i) = ∑ i ∈ s, star (c i) * herm H v (w i) := by
  classical
  unfold herm
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, star_add, add_dotProduct, ih, star_smul,
    smul_dotProduct, smul_eq_mul]

private lemma isUnit_det_of_mem_UH_Hpk' {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : IsUnit g.det := by
  have hH := hpk_isUnit (k := k) (r := r)
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  have h3 : gᴴ.det * g.det * (Hpk k r).det = 1 * (Hpk k r).det := by linear_combination h2
  have h4 := mul_right_cancel₀ hH.ne_zero h3
  exact isUnit_iff_exists.mpr ⟨gᴴ.det, by rw [mul_comm]; exact h4, h4⟩

theorem herm_UH {ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hρ : ρ ∈ UH (Hpk k r))
    (x y : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) (ρ *ᵥ x) y = herm (Hpk k r) x (ρ⁻¹ *ᵥ y) := by
  have hρ' : ρᴴ * Hpk k r * ρ = Hpk k r := hρ
  have hdet := isUnit_det_of_mem_UH_Hpk' hρ
  have hinv : (ρ⁻¹)ᴴ * ρᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.conjTranspose_one]
  have hkey : (ρ⁻¹)ᴴ * Hpk k r = Hpk k r * ρ := by
    calc (ρ⁻¹)ᴴ * Hpk k r = (ρ⁻¹)ᴴ * (ρᴴ * Hpk k r * ρ) := by rw [hρ']
      _ = ((ρ⁻¹)ᴴ * ρᴴ) * Hpk k r * ρ := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * ρ := by rw [hinv, Matrix.one_mul]
  unfold herm
  rw [← star_dot_conjT' (ρ⁻¹) y (Hpk k r *ᵥ x)]
  simp only [Matrix.mulVec_mulVec, hkey]

private lemma mulVec_fvec_eq_sum_uMap_smul_of_mem_Nset {z : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.FourierDecayAlt.C2.StdZ k r z)
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r) (b : Fin (r + 1)) :
    m *ᵥ fvec k r z b = ∑ c, Formalism.FourierDecayAlt.C2.uMap k r z m c b • fvec k r z c := by
  have hF := Formalism.QuantumDeterminants.N_F hz.1 hm
  rw [Formalism.FourierDecayAlt.P.C2x5.uMap_eq hz m _ (Formalism.FourierDecayAlt.P.C2x5.colEq hF)]
  exact Formalism.FourierDecayAlt.P.C2x5.colEq hF b

theorem zhat_uMap {z z' : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.FourierDecayAlt.C2.StdZ k r z) (hz' : Formalism.FourierDecayAlt.C2.StdZ k r z')
    {δ ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hδ : δ ∈ UH (Hpk k r)) (hρ : ρ ∈ Nset k r)
    (hρ' : δ⁻¹ * ρ * δ ∈ Nset k r) :
    Zhat k r z z' δ * Formalism.FourierDecayAlt.C2.uMap k r z' (δ⁻¹ * ρ * δ) =
      (Formalism.FourierDecayAlt.C2.uMap k r z ρ⁻¹)ᴴ * Zhat k r z z' δ := by
  have hδd := isUnit_det_of_mem_UH_Hpk' hδ
  have hρU : ρ ∈ UH (Hpk k r) := hρ.1
  have hρi : ρ⁻¹ ∈ Nset k r := Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hρ
  have hδs : δ * (δ⁻¹ * ρ * δ) = ρ * δ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hδd, Matrix.one_mul]
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply]

  have e1 : ∑ c, Zhat k r z z' δ a c * Formalism.FourierDecayAlt.C2.uMap k r z' (δ⁻¹ * ρ * δ) c b =
      herm (Hpk k r) (δ *ᵥ ((δ⁻¹ * ρ * δ) *ᵥ fvec k r z' b)) (fvec k r z a) := by
    rw [mulVec_fvec_eq_sum_uMap_smul_of_mem_Nset hz' hρ' b, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
    rw [herm_sum_left]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [Zhat]
    ring
  have e2 : ∑ c, (Formalism.FourierDecayAlt.C2.uMap k r z ρ⁻¹)ᴴ a c * Zhat k r z z' δ c b =
      herm (Hpk k r) (δ *ᵥ fvec k r z' b) (ρ⁻¹ *ᵥ fvec k r z a) := by
    rw [mulVec_fvec_eq_sum_uMap_smul_of_mem_Nset hz hρi a, herm_sum_right]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [Zhat, Matrix.conjTranspose_apply]
  rw [e1, e2, Matrix.mulVec_mulVec, hδs, ← Matrix.mulVec_mulVec, herm_UH hρU]

end Formalism.L2.SG.HermitianMatrixIdentities

end
end
