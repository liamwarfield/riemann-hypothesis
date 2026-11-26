module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RDIota
public import Development.WeilBound.ThetaLifts.TowerModels.ModelEx

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.UnitaryGroupInverseFormula
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.OrthogonalFormMulTranspose
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DenseC
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DenseCP
noncomputable section

open Matrix

namespace PositivityTheory.SiegelWeilFormula.Krd.CP

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem cay_inU {J Y : Matrix ι ι ℂ} (hY : Yᴴ * J + J * Y = 0) (hu : IsUnit (1 - Y).det) :
    ((1 + Y) * (1 - Y)⁻¹)ᴴ * J * ((1 + Y) * (1 - Y)⁻¹) = J := by
  have hY' : Yᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left hY
  have h1 : J * (1 - Y) = (1 + Y)ᴴ * J := by
    rw [conjTranspose_add, conjTranspose_one, Matrix.add_mul, hY', Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul,
      sub_eq_add_neg]
  have h2 : J * (1 + Y) = (1 - Y)ᴴ * J := by
    rw [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, hY', Matrix.mul_add, Matrix.mul_one, Matrix.one_mul,
      sub_neg_eq_add]
  have hc : (1 - Y) * (1 + Y) = (1 + Y) * (1 - Y) := by noncomm_ring
  have hB : (1 + Y)ᴴ * J * (1 + Y) = (1 - Y)ᴴ * J * (1 - Y) := by
    rw [← h1, Matrix.mul_assoc, hc, ← Matrix.mul_assoc, h2]
  have hA : ((1 - Y)⁻¹)ᴴ * (1 - Y)ᴴ = 1 := by
    rw [← conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, conjTranspose_one]
  calc ((1 + Y) * (1 - Y)⁻¹)ᴴ * J * ((1 + Y) * (1 - Y)⁻¹)
      = ((1 - Y)⁻¹)ᴴ * ((1 + Y)ᴴ * J * (1 + Y)) * (1 - Y)⁻¹ := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = ((1 - Y)⁻¹)ᴴ * (1 - Y)ᴴ * J * ((1 - Y) * (1 - Y)⁻¹) := by
        rw [hB]; simp only [Matrix.mul_assoc]
    _ = J := by rw [hA, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]

theorem cay_surj {J h : Matrix ι ι ℂ} (hh : hᴴ * J * h = J) (hu : IsUnit (1 + h).det) :
    ∃ Y : Matrix ι ι ℂ, Yᴴ * J + J * Y = 0 ∧ IsUnit (1 - Y).det ∧ (1 + Y) * (1 - Y)⁻¹ = h := by
  obtain ⟨P, hP⟩ : ∃ P : Matrix ι ι ℂ, P = 1 + h := ⟨_, rfl⟩
  rw [← hP] at hu
  have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hu
  obtain ⟨Y, hYd⟩ : ∃ Y : Matrix ι ι ℂ, Y = (h - 1) * P⁻¹ := ⟨_, rfl⟩
  have e1 : 1 - Y = (2 : ℂ) • P⁻¹ := by
    calc 1 - Y = P * P⁻¹ - (h - 1) * P⁻¹ := by rw [hPi, hYd]
      _ = (P - (h - 1)) * P⁻¹ := by rw [← Matrix.sub_mul]
      _ = ((2 : ℂ) • 1) * P⁻¹ := by rw [hP, two_smul]; congr 1; abel
      _ = (2 : ℂ) • P⁻¹ := by rw [Matrix.smul_mul, Matrix.one_mul]
  have e2 : 1 + Y = (2 : ℂ) • (h * P⁻¹) := by
    calc 1 + Y = P * P⁻¹ + (h - 1) * P⁻¹ := by rw [hPi, hYd]
      _ = (P + (h - 1)) * P⁻¹ := by rw [← Matrix.add_mul]
      _ = ((2 : ℂ) • h) * P⁻¹ := by rw [hP, two_smul]; congr 1; abel
      _ = (2 : ℂ) • (h * P⁻¹) := by rw [Matrix.smul_mul]
  have hdet : IsUnit (1 - Y).det := by
    rw [e1, Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.2 two_ne_zero)).mul ((Matrix.isUnit_nonsing_inv_det_iff).2 hu)
  refine ⟨Y, ?_, hdet, ?_⟩
  · have hPc : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, hPi, conjTranspose_one]
    have eY : Y * P = h - 1 := by rw [hYd, Matrix.mul_assoc, hiP, Matrix.mul_one]
    have eYh : Pᴴ * Yᴴ = (h - 1)ᴴ := by rw [← conjTranspose_mul, eY]
    have key : Pᴴ * (Yᴴ * J + J * Y) * P = 0 := by
      have e3 : Pᴴ * (Yᴴ * J + J * Y) * P = (Pᴴ * Yᴴ) * J * P + Pᴴ * J * (Y * P) := by noncomm_ring
      rw [e3, eYh, eY, hP, conjTranspose_sub, conjTranspose_add, conjTranspose_one]
      have e4 : (hᴴ - 1) * J * (1 + h) + (1 + hᴴ) * J * (h - 1) = (2 : ℂ) • (hᴴ * J * h - J) := by
        rw [two_smul]; noncomm_ring
      rw [e4, hh, sub_self, smul_zero]
    calc Yᴴ * J + J * Y = ((P⁻¹)ᴴ * Pᴴ) * (Yᴴ * J + J * Y) * (P * P⁻¹) := by
          rw [hPc, hPi, Matrix.one_mul, Matrix.mul_one]
      _ = (P⁻¹)ᴴ * (Pᴴ * (Yᴴ * J + J * Y) * P) * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [key, Matrix.mul_zero, Matrix.zero_mul]
  · rw [e1, e2]
    have hinv : ((2 : ℂ) • P⁻¹)⁻¹ = (2 : ℂ)⁻¹ • P := by
      refine Matrix.inv_eq_left_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul, hPi]
    rw [hinv, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul, Matrix.mul_assoc, hiP,
      Matrix.mul_one]

theorem scalar_avoid {J h : Matrix ι ι ℂ} (hh : hᴴ * J * h = J) {V : Set (Matrix ι ι ℂ)} (hV : IsOpen V) (hhV : h ∈ V) :
    ∃ μ : ℂ, star μ * μ = 1 ∧ μ • h ∈ V ∧ IsUnit (1 + μ • h).det := by
  obtain ⟨q, hqd⟩ : ∃ q : Polynomial ℂ, q = (1 + (Polynomial.X : Polynomial ℂ) • h.map Polynomial.C).det := ⟨_, rfl⟩
  have hq : ∀ μ : ℂ, q.eval μ = (1 + μ • h).det := by
    intro μ
    rw [hqd, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij] <;> ring
  have hq0 : q ≠ 0 := fun h0 => by
    have := hq 0
    rw [h0, Polynomial.eval_zero, zero_smul, add_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hg : Continuous fun θ : ℝ => Complex.exp (θ * Complex.I) • h :=
    (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).smul continuous_const
  have hO : IsOpen ((fun θ : ℝ => Complex.exp (θ * Complex.I) • h) ⁻¹' V) := hV.preimage hg
  have h0O : (0 : ℝ) ∈ (fun θ : ℝ => Complex.exp (θ * Complex.I) • h) ⁻¹' V := by
    simp only [Set.mem_preimage, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
    exact hhV
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hO 0 h0O
  have hδ' : (0 : ℝ) < min δ 1 := lt_min hδ one_pos
  have hSinf : (Set.Ioo (0 : ℝ) (min δ 1)).Infinite := Set.Ioo_infinite hδ'
  have hinj : Set.InjOn (fun θ : ℝ => Complex.exp (θ * Complex.I)) (Set.Ioo (0 : ℝ) (min δ 1)) := by
    intro a ha b hb hab
    have hpi : (1 : ℝ) < Real.pi := lt_trans (by norm_num) Real.pi_gt_three
    have hIoc : ∀ t ∈ Set.Ioo (0 : ℝ) (min δ 1), t ∈ Set.Ioc (-Real.pi) Real.pi := fun t ht =>
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, min_le_right δ 1]⟩
    have e := congrArg Complex.arg hab
    simp only [Complex.exp_mul_I] at e
    rwa [Complex.arg_cos_add_sin_mul_I (hIoc a ha), Complex.arg_cos_add_sin_mul_I (hIoc b hb)] at e
  obtain ⟨μ, ⟨θ, hθ, rfl⟩, hμ⟩ := (hSinf.image hinj).exists_notMem_finset q.roots.toFinset
  refine ⟨Complex.exp (θ * Complex.I), ?_, ?_, ?_⟩
  · rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [show (θ : ℂ) * -Complex.I + θ * Complex.I = 0 by ring, Complex.exp_zero]
  · refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hθ.1]
    exact lt_of_lt_of_le hθ.2 (min_le_left δ 1)
  · rw [isUnit_iff_ne_zero, ← hq]
    intro h0
    exact hμ (Multiset.mem_toFinset.2 ((Polynomial.mem_roots hq0).2 h0))

end PositivityTheory.SiegelWeilFormula.Krd.CP

end
end

noncomputable section

open Matrix Topology

namespace PositivityTheory.SiegelWeilFormula.Krd.DC

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def InU (J h : Matrix ι ι ℂ) : Prop := hᴴ * J * h = J

def InLie (J Y : Matrix ι ι ℂ) : Prop := Yᴴ * J + J * Y = 0

def cay (Y : Matrix ι ι ℂ) : Matrix ι ι ℂ := (1 + Y) * (1 - Y)⁻¹

def proj (J : Matrix ι ι ℂ) (d : ℂ) (Y : Matrix ι ι ℂ) : Matrix ι ι ℂ := Y - d⁻¹ • (J * Yᴴ * J)

theorem cay_inU {J Y : Matrix ι ι ℂ} (hY : InLie J Y) (hu : IsUnit (1 - Y).det) : InU J (cay Y) := by
  exact PositivityTheory.SiegelWeilFormula.Krd.CP.cay_inU hY hu

theorem cay_surj {J h : Matrix ι ι ℂ} (hh : InU J h) (hu : IsUnit (1 + h).det) :
    ∃ Y, InLie J Y ∧ IsUnit (1 - Y).det ∧ cay Y = h := by
  exact PositivityTheory.SiegelWeilFormula.Krd.CP.cay_surj hh hu

theorem isOpen_dom : IsOpen {Y : Matrix ι ι ℂ | IsUnit (1 - Y).det} := by
  have hc : Continuous fun Y : Matrix ι ι ℂ => (1 - Y).det :=
    (continuous_const.sub continuous_id).matrix_det
  have he : {Y : Matrix ι ι ℂ | IsUnit (1 - Y).det} = (fun Y : Matrix ι ι ℂ => (1 - Y).det) ⁻¹' {0}ᶜ := by
    ext Y
    simp [isUnit_iff_ne_zero]
  rw [he]
  exact isOpen_compl_singleton.preimage hc

theorem continuousOn_cay : ContinuousOn (cay (ι := ι)) {Y | IsUnit (1 - Y).det} := by
  intro Y hY
  apply ContinuousAt.continuousWithinAt
  have hinv : ContinuousAt (fun Z : Matrix ι ι ℂ => (1 - Z)⁻¹) Y := by
    have h1 : ContinuousAt Inv.inv (1 - Y) := by
      apply continuousAt_matrix_inv
      have h2 := NormedRing.inverse_continuousAt hY.unit
      rwa [hY.unit_spec] at h2
    exact h1.comp (continuous_const.sub continuous_id).continuousAt
  show ContinuousAt (fun Z : Matrix ι ι ℂ => (1 + Z) * (1 - Z)⁻¹) Y
  exact (continuous_const.add continuous_id).continuousAt.mul hinv

theorem inLie_proj {J : Matrix ι ι ℂ} {c d : ℂ} (hc : Jᴴ = c • J) (hcc : c * c = 1) (hd : J * J = d • 1) (hd0 : d ≠ 0)
    (hds : star d = d) (Y : Matrix ι ι ℂ) : InLie J (proj J d Y) := by
  have hJJ : ∀ X : Matrix ι ι ℂ, J * (J * X) = d • X := by
    intro X
    rw [← Matrix.mul_assoc, hd, Matrix.smul_mul, Matrix.one_mul]
  have hsd : star d⁻¹ = d⁻¹ := by rw [star_inv₀, hds]
  unfold InLie proj
  rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_mul, conjTranspose_mul,
    conjTranspose_conjTranspose, hc, hsd]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.mul_assoc, hJJ, hd, Matrix.mul_one]
  rw [hcc, mul_one, inv_mul_cancel₀ hd0, one_smul, one_smul]
  abel

theorem proj_half {J : Matrix ι ι ℂ} {d : ℂ} (hd : J * J = d • 1) (hd0 : d ≠ 0) {Y : Matrix ι ι ℂ} (hY : InLie J Y) :
    proj J d ((1 / 2 : ℂ) • Y) = Y := by
  have h1 : J * Yᴴ * J = -(d • Y) := by
    have h2 : Yᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left hY
    rw [Matrix.mul_assoc, h2, Matrix.mul_neg, ← Matrix.mul_assoc, hd, Matrix.smul_mul, Matrix.one_mul]
  unfold proj
  rw [conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, h1]
  ext i j
  simp
  field_simp
  ring

theorem continuous_proj (J : Matrix ι ι ℂ) (d : ℂ) : Continuous (proj J d) := by
  unfold proj
  have h1 : Continuous fun Y : Matrix ι ι ℂ => J * Yᴴ * J :=
    (continuous_const.mul continuous_id.matrix_conjTranspose).mul continuous_const
  exact continuous_id.sub (h1.const_smul d⁻¹)

theorem lie_dense {J : Matrix ι ι ℂ} {c d : ℂ} (hc : Jᴴ = c • J) (hcc : c * c = 1) (hd : J * J = d • 1) (hd0 : d ≠ 0)
    (hds : star d = d) {S : Set (Matrix ι ι ℂ)} (hS : Dense S) (hSp : ∀ X ∈ S, proj J d X ∈ S) {Y : Matrix ι ι ℂ}
    (hY : InLie J Y) {U : Set (Matrix ι ι ℂ)} (hU : IsOpen U) (hYU : Y ∈ U) : ∃ X ∈ S, InLie J X ∧ X ∈ U := by
  have hW : IsOpen (proj J d ⁻¹' U) := hU.preimage (continuous_proj J d)
  have hmem : (1 / 2 : ℂ) • Y ∈ proj J d ⁻¹' U := by
    show proj J d ((1 / 2 : ℂ) • Y) ∈ U
    rw [proj_half hd hd0 hY]
    exact hYU
  obtain ⟨X, hXS, hXW⟩ := hS.exists_mem_open hW ⟨_, hmem⟩
  exact ⟨proj J d X, hSp X hXS, inLie_proj hc hcc hd hd0 hds X, hXW⟩

theorem scalar_avoid {J h : Matrix ι ι ℂ} (hh : InU J h) {V : Set (Matrix ι ι ℂ)} (hV : IsOpen V) (hhV : h ∈ V) :
    ∃ μ : ℂ, star μ * μ = 1 ∧ μ • h ∈ V ∧ IsUnit (1 + μ • h).det := by
  exact PositivityTheory.SiegelWeilFormula.Krd.CP.scalar_avoid hh hV hhV

theorem inU_smul {J h : Matrix ι ι ℂ} (hh : InU J h) {μ : ℂ} (hμ : star μ * μ = 1) : InU J (μ • h) := by
  unfold InU at *
  simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hh]
  rw [mul_comm μ, hμ, one_smul]

theorem densG {J : Matrix ι ι ℂ} {c d : ℂ} (hc : Jᴴ = c • J) (hcc : c * c = 1) (hd : J * J = d • 1) (hd0 : d ≠ 0)
    (hds : star d = d) {S : Set (Matrix ι ι ℂ)} (hS : Dense S) (hSp : ∀ X ∈ S, proj J d X ∈ S)
    (hSc : ∀ X ∈ S, IsUnit (1 - X).det → cay X ∈ S) {V : Set (Matrix ι ι ℂ)} (hV : IsOpen V) {h : Matrix ι ι ℂ}
    (hhV : h ∈ V) (hh : InU J h) : ∃ h' ∈ V, h' ∈ S ∧ InU J h' := by
  obtain ⟨μ, hμ, hμV, hμu⟩ := scalar_avoid hh hV hhV
  obtain ⟨Y, hYL, hYu, hYc⟩ := cay_surj (inU_smul hh hμ) hμu
  have hU : IsOpen ({Y : Matrix ι ι ℂ | IsUnit (1 - Y).det} ∩ cay ⁻¹' V) :=
    continuousOn_cay.isOpen_inter_preimage isOpen_dom hV
  have hYU : Y ∈ {Y : Matrix ι ι ℂ | IsUnit (1 - Y).det} ∩ cay ⁻¹' V := by
    refine ⟨hYu, ?_⟩
    show cay Y ∈ V
    rw [hYc]
    exact hμV
  obtain ⟨X, hXS, hXL, hXU⟩ := lie_dense hc hcc hd hd0 hds hS hSp hYL hU hYU
  exact ⟨cay X, hXU.2, hSc X hXS hXU.1, cay_inU hXL hXU.1⟩

end PositivityTheory.SiegelWeilFormula.Krd.DC

end
end

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Krd.DM

open PositivityTheory.SiegelWeilFormula.Krd.DC

variable {n : ℕ}

def QR (R : Type) [Ring R] (n : ℕ) (ε : ℤˣ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  Matrix.fromBlocks 0 1 (((ε : ℤ) : R) • 1) 0

theorem eps_sq (ε : ℤˣ) (R : Type) [Ring R] : ((ε : ℤ) : R) * ((ε : ℤ) : R) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

theorem orthogonal_form_mul_transpose (R : Type) [CommRing R] (ε : ℤˣ) : QR R n ε * (QR R n ε)ᵀ = 1 := by
  simp only [QR, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.transpose_zero, Matrix.transpose_one,
    Matrix.transpose_smul]
  simp [smul_smul, eps_sq]

theorem QR_det_ne (K : Type) [Field K] (ε : ℤˣ) : (QR K n ε).det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det (orthogonal_form_mul_transpose (n := n) K ε)
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem QR_map {K L : Type} [Field K] [Field L] (f : K →+* L) (ε : ℤˣ) : (QR K n ε).map f = QR L n ε := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rcases eq_or_ne i j with rfl | hij <;> simp [QR, Matrix.one_apply, *]

theorem inU_iff (ε : ℤˣ) (h : M2 n) : InU (Qc n ε)ᵀ h ↔ hᵀ * Qc n ε * h.map star = Qc n ε := by
  have e : ∀ A : M2 n, (hᴴ * A * h)ᵀ = hᵀ * Aᵀ * h.map star := fun A => by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc]
    congr 1
  unfold InU
  constructor
  · intro hh
    have := congrArg Matrix.transpose hh
    rwa [e, Matrix.transpose_transpose] at this
  · intro hh
    apply Matrix.transpose_injective
    rw [e, Matrix.transpose_transpose, hh]

theorem J_herm (ε : ℤˣ) : ((Qc n ε)ᵀ)ᴴ = ((ε : ℤ) : ℂ) • (Qc n ε)ᵀ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rcases eq_or_ne i j with rfl | hij <;>
    simp [Qc, Matrix.conjTranspose_apply, Matrix.one_apply, ← mul_assoc, eps_sq, *] <;>
    exact fun h => absurd h.symm hij

theorem J_sq (ε : ℤˣ) : (Qc n ε)ᵀ * (Qc n ε)ᵀ = ((ε : ℤ) : ℂ) • 1 := by
  rw [show ((ε : ℤ) : ℂ) • (1 : M2 n) = Matrix.fromBlocks (((ε : ℤ) : ℂ) • 1) 0 0 (((ε : ℤ) : ℂ) • 1) by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]]
  simp [Qc, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]

theorem eps_ne (ε : ℤˣ) : ((ε : ℤ) : ℂ) ≠ 0 := by
  intro h; have := eps_sq ε ℂ; rw [h, zero_mul] at this; exact zero_ne_one this

theorem eps_star (ε : ℤˣ) : star ((ε : ℤ) : ℂ) = ((ε : ℤ) : ℂ) := by simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def ratS (τ : E →+* ℂ) : Set (M2 n) := Set.range fun X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E => X.map τ

theorem dense_ratS (h : IsCMExt F E σ) (τ : E →+* ℂ) : Dense (ratS (n := n) τ) := by
  show DenseRange fun X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E => X.map τ
  exact DenseRange.piMap fun _ => DenseRange.piMap fun _ => PositivityTheory.ThKG.Tow.Pln.denseRange_emb h τ

theorem map_conjT (h : IsCMExt F E σ) (τ : E →+* ℂ) (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) :
    (X.map τ)ᴴ = (X.map σ)ᵀ.map τ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]
  exact (h.2.2.2 τ (X j i)).symm

theorem map_smul_τ (τ : E →+* ℂ) (c : E) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) :
    (c • M).map τ = τ c • M.map τ := by
  ext i j
  simp

theorem QT_map (τ : E →+* ℂ) (ε : ℤˣ) : (QR E n ε)ᵀ.map τ = (Qc n ε)ᵀ := by
  rw [Matrix.transpose_map, QR_map]
  rfl

theorem proj_ratS (h : IsCMExt F E σ) (τ : E →+* ℂ) (ε : ℤˣ) :
    ∀ X ∈ ratS (n := n) τ, proj (Qc n ε)ᵀ ((ε : ℤ) : ℂ) X ∈ ratS τ := by
  rintro _ ⟨X, rfl⟩
  refine ⟨X - ((ε : ℤ) : E)⁻¹ • ((QR E n ε)ᵀ * (X.map σ)ᵀ * (QR E n ε)ᵀ), ?_⟩
  show (X - ((ε : ℤ) : E)⁻¹ • ((QR E n ε)ᵀ * (X.map σ)ᵀ * (QR E n ε)ᵀ)).map τ = X.map τ - ((ε : ℤ) : ℂ)⁻¹ • ((Qc n ε)ᵀ * (X.map τ)ᴴ * (Qc n ε)ᵀ)
  rw [map_conjT h τ X, Matrix.map_sub _ (map_sub τ), map_smul_τ, Matrix.map_mul, Matrix.map_mul, QT_map, map_inv₀, map_intCast]

theorem map_inv_of (τ : E →+* ℂ) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) (hM : IsUnit (M.map τ).det) :
    (M⁻¹).map τ = (M.map τ)⁻¹ := by
  have e : (M.map τ).det = τ M.det := (RingHom.map_det τ M).symm
  have h0 : M.det ≠ 0 := fun h0 => by rw [e, h0, map_zero] at hM; exact not_isUnit_zero hM
  have hu : IsUnit M.det := isUnit_iff_ne_zero.2 h0
  symm
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu, Matrix.map_one _ (map_zero τ) (map_one τ)]

theorem cay_ratS (τ : E →+* ℂ) : ∀ X ∈ ratS (n := n) τ, IsUnit (1 - X).det → cay X ∈ ratS τ := by
  rintro _ ⟨X, rfl⟩ hu
  simp only at hu
  have e1 : (1 - X).map τ = 1 - X.map τ := by rw [Matrix.map_sub _ (map_sub τ), Matrix.map_one _ (map_zero τ) (map_one τ)]
  have e2 : (1 + X).map τ = 1 + X.map τ := by rw [Matrix.map_add _ (map_add τ), Matrix.map_one _ (map_zero τ) (map_one τ)]
  refine ⟨(1 + X) * (1 - X)⁻¹, ?_⟩
  show ((1 + X) * (1 - X)⁻¹).map τ = (1 + X.map τ) * (1 - X.map τ)⁻¹
  rw [Matrix.map_mul, e2, map_inv_of τ _ (e1 ▸ hu), e1]

theorem rat_unitary (h : IsCMExt F E σ) (τ : E →+* ℂ) (ε : ℤˣ) (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E)
    (hX : InU (Qc n ε)ᵀ (X.map τ)) : Xᵀ * QR E n ε * X.map σ = QR E n ε := by
  rw [inU_iff] at hX
  have e : (X.map σ).map τ = (X.map τ).map star := by ext i j; exact h.2.2.2 τ (X i j)
  apply Matrix.map_injective τ.injective
  show (Xᵀ * QR E n ε * X.map σ).map τ = (QR E n ε).map τ
  rw [Matrix.map_mul, Matrix.map_mul, e, Matrix.transpose_map, QR_map]
  exact hX

theorem dense_pts (h : IsCMExt F E σ) (τ : E →+* ℂ) (ε : ℤˣ) {V : Set (M2 n)} (hV : IsOpen V) {h0 : M2 n}
    (h0V : h0 ∈ V) (h0U : InU (Qc n ε)ᵀ h0) :
    ∃ X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E, X.map τ ∈ V ∧ InU (Qc n ε)ᵀ (X.map τ) := by
  obtain ⟨h', hV', ⟨X, rfl⟩, hU⟩ := densG (J_herm ε) (eps_sq ε ℂ) (J_sq ε) (eps_ne ε) (eps_star ε) (dense_ratS h τ)
    (proj_ratS h τ ε) (cay_ratS τ) hV h0V h0U
  exact ⟨X, hV', hU⟩

end PositivityTheory.SiegelWeilFormula.Krd.DM

end
end

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Krd.DM

open PositivityTheory.SiegelWeilFormula.Krd.DC

variable {n : ℕ}

theorem JJ_sq : JJ n * JJ n = -1 := by
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp [JJ, Matrix.fromBlocks_multiply]

theorem unitary_group_inverse_formula (g : M2 n) (hg : InG g) : -(JJ n * gᴴ * JJ n) * g = 1 := by
  have hg' : gᴴ * JJ n * g = JJ n := hg
  rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', JJ_sq, neg_neg]

def mkG (g : M2 n) (hg : InG g) : GR n :=
  ⟨⟨g, -(JJ n * gᴴ * JJ n), mul_eq_one_comm.1 (unitary_group_inverse_formula g hg), unitary_group_inverse_formula g hg⟩, hg⟩

theorem mR_mkG (g : M2 n) (hg : InG g) : mR (mkG g hg) = g := rfl

def phi (ζ : ℂ) (h : M2 n) : M2 n := dZ n ζ * h * dZ n ζ⁻¹

theorem inG_phi {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) {h : M2 n} (hh : InU (Qc n ε)ᵀ h) :
    InG (phi ζ h) :=
  inG_conj hζ h ((inU_iff ε h).1 hh)

def Phi {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (h : {h : M2 n // InU (Qc n ε)ᵀ h}) : GR n :=
  mkG (phi ζ h.1) (inG_phi hζ h.2)

theorem continuous_Phi {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) :
    Continuous (Phi (n := n) hζ) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · show Continuous fun h : {h : M2 n // InU (Qc n ε)ᵀ h} => phi ζ h.1
    exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  · show Continuous fun h : {h : M2 n // InU (Qc n ε)ᵀ h} => -(JJ n * (phi ζ h.1)ᴴ * JJ n)
    exact ((continuous_const.matrix_mul (((continuous_const.matrix_mul continuous_subtype_val).matrix_mul
      continuous_const).matrix_conjTranspose)).matrix_mul continuous_const).neg

theorem Phi_surj {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) (y : GR n) :
    ∃ h : {h : M2 n // InU (Qc n ε)ᵀ h}, Phi hζ h = y := by
  refine ⟨⟨dZ n ζ⁻¹ * mR y * dZ n ζ, (inU_iff ε _).2 ((unitary_iff hζ (mR y)).2 y.2)⟩, ?_⟩
  have h0 := zeta_ne hζ
  apply Subtype.ext
  apply Units.ext
  show dZ n ζ * (dZ n ζ⁻¹ * mR y * dZ n ζ) * dZ n ζ⁻¹ = mR y
  simp only [← Matrix.mul_assoc, dZ_mul_inv h0, Matrix.one_mul]
  rw [Matrix.mul_assoc, dZ_mul_inv h0, Matrix.mul_one]

theorem exists_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hcm : IsCMExt F E σ) (τ : E →+* ℂ) {ε : ℤˣ} {ζ : ℂ} (hζ : ε = -1 ∧ ζ = 1 ∨ ε = 1 ∧ ζ = Complex.I) {O : Set (GR n)}
    (hO : IsOpen O) {y : GR n} (hy : y ∈ O) :
    ∃ (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) (hX : InU (Qc n ε)ᵀ (X.map τ)), Phi hζ ⟨X.map τ, hX⟩ ∈ O := by
  obtain ⟨h0, rfl⟩ := Phi_surj hζ y
  obtain ⟨V, hV, hVe⟩ := isOpen_induced_iff.1 (hO.preimage (continuous_Phi hζ))
  have h0V : h0.1 ∈ V := by
    have : h0 ∈ Subtype.val ⁻¹' V := by rw [hVe]; exact hy
    exact this
  obtain ⟨X, hXV, hXU⟩ := dense_pts hcm τ ε hV h0V h0.2
  refine ⟨X, hXU, ?_⟩
  have : (⟨X.map τ, hXU⟩ : {h : M2 n // InU (Qc n ε)ᵀ h}) ∈ Subtype.val ⁻¹' V := hXV
  rw [hVe] at this
  exact this

end PositivityTheory.SiegelWeilFormula.Krd.DM

end
end

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Krd.DM

open PositivityTheory.SiegelWeilFormula.Krd.DC

theorem conj_unitE {K ι : Type} [CommRing K] [Fintype ι] [DecidableEq ι] (f : K →+* K) (b bi Z D Q : Matrix ι ι K)
    (hb : b * bi = 1) (hQ : bᵀ * D * b.map f = Q) (hZ : Zᵀ * Q * Z.map f = Q) :
    (b * Z * bi)ᵀ * D * (b * Z * bi).map f = D := by
  have h1 : (1 : Matrix ι ι K).map f = 1 := Matrix.map_one _ (map_zero f) (map_one f)
  have hD : D = biᵀ * Q * bi.map f := by
    calc D = (b * bi)ᵀ * D * (b * bi).map f := by
          rw [hb, Matrix.transpose_one, h1, Matrix.one_mul, Matrix.mul_one]
      _ = biᵀ * (bᵀ * D * b.map f) * bi.map f := by
          rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = biᵀ * Q * bi.map f := by rw [hQ]
  calc (b * Z * bi)ᵀ * D * (b * Z * bi).map f = biᵀ * (Zᵀ * (bᵀ * D * b.map f) * Z.map f) * bi.map f := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.map_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
    _ = D := by rw [hQ, hZ, ← hD]

theorem det_ne_of {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] (f : K →+* K) {A D : Matrix ι ι K}
    (h : Aᵀ * D * A.map f = D) (hD : D.det ≠ 0) : A.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul] at this
  exact hD this.symm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_cA {p q : Type} (M : Matrix p q E) : (incM F M).map (cA σ) = incM F (M.map σ) := by
  ext i j
  rfl

theorem incM_alt_bis {p q : Type} (M : Matrix p q E) : (incM F M)ᵀ = incM F Mᵀ :=
  Matrix.transpose_map.symm

variable (d : SD σ)

theorem dblJ_det {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε) : (dbl d.Y.J).det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det hε
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul] at this
  exact QR_det_ne E ε this.symm

def bX (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E :=
  d.b.1 * X * (d.b⁻¹).1

theorem bX_unitary {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    {X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E} (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) :
    (bX d X)ᵀ * dbl d.Y.J * (bX d X).map σ = dbl d.Y.J :=
  conj_unitE (σ : E →+* E) d.b.1 (d.b⁻¹).1 X (dbl d.Y.J) (QR E d.n ε) (Units.mul_inv d.b) hε hX

def ratG {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) : d.G :=
  ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F))
    (Matrix.nonsingInvUnit (bX d X) (isUnit_iff_ne_zero.2 (det_ne_of (σ : E →+* E) (bX_unitary d hε hX) (dblJ_det d hε)))),
    by
      show (incM F (bX d X))ᵀ * dbl (incM F d.Y.J) * (incM F (bX d X)).map (cA σ) = dbl (incM F d.Y.J)
      rw [dbl_incM d, incM_cA, incM_alt_bis, ← incM_mul, ← incM_mul, bX_unitary d hε hX]⟩

theorem ratG_mem {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) :
    ratG d hε X hX ∈ rat2 σ d.Y :=
  Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩

theorem inFrame_ratG {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) :
    inFrame d.b (ratG d hε X hX) = incM F X := by
  show incM F (d.b⁻¹).1 * incM F (bX d X) * incM F d.b.1 = incM F X
  rw [← incM_mul, ← incM_mul]
  congr 1
  simp only [bX, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem inFrame_mul (x z : d.G) : inFrame d.b (x * z) = inFrame d.b x * inFrame d.b z := by
  show incM F (d.b⁻¹).1 * (mat2 x * mat2 z) * incM F d.b.1 =
    (incM F (d.b⁻¹).1 * mat2 x * incM F d.b.1) * (incM F (d.b⁻¹).1 * mat2 z * incM F d.b.1)
  calc incM F (d.b⁻¹).1 * (mat2 x * mat2 z) * incM F d.b.1 =
      incM F (d.b⁻¹).1 * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 z * incM F d.b.1 := by
        rw [bb d, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem inFrame_inj {x z : d.G} (h : inFrame d.b x = inFrame d.b z) : x = z := by
  have e : ∀ u : d.G, mat2 u = incM F d.b.1 * inFrame d.b u * incM F (d.b⁻¹).1 := fun u => by
    simp only [inFrame, ← Matrix.mul_assoc, bb d, Matrix.one_mul]
    rw [Matrix.mul_assoc, bb d, Matrix.mul_one]
  apply Subtype.ext
  apply Units.ext
  show mat2 x = mat2 z
  rw [e x, e z, h]

theorem J_unit (ε : ℤˣ) {n : ℕ} : IsUnit (Qc n ε)ᵀ.det := by
  refine Matrix.isUnit_det_of_right_inverse (B := ((ε : ℤ) : ℂ)⁻¹ • (Qc n ε)ᵀ) ?_
  rw [Matrix.mul_smul, J_sq, smul_smul, inv_mul_cancel₀ (eps_ne ε), one_smul]

theorem det_of_inU {ε : ℤˣ} {n : ℕ} {h : M2 n} (hh : InU (Qc n ε)ᵀ h) : IsUnit h.det := by
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  have := congrArg Matrix.det hh
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
  exact (J_unit ε).ne_zero this.symm

end PositivityTheory.SiegelWeilFormula.Krd.DM


open PositivityTheory.SiegelWeilFormula.Krd PositivityTheory.SiegelWeilFormula.Krd.DM PositivityTheory.SiegelWeilFormula.Krd.DC in
theorem PositivityTheory.SiegelWeilFormula.Krd.denseW : PositivityTheory.SiegelWeilFormula.DenseW := by
  intro F E _ _ _ _ _ σ d R w y O hO hy
  have h0 := zeta_ne R.hζ
  have hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n R.ε := R.hε
  obtain ⟨X, hXU, hXO⟩ := exists_rat d.cm (d.B.emb w).1 R.hζ hO hy
  have hX := rat_unitary d.cm (d.B.emb w).1 R.ε X hXU
  refine ⟨ratG d hε X hX, ratG_mem d hε X hX, _, hXO, ratG d hε X hX * (R.ι w (Phi R.hζ ⟨_, hXU⟩))⁻¹,
    (inv_mul_cancel_right _ _).symm, fun y'' => ?_⟩
  set y' := Phi R.hζ ⟨X.map (d.B.emb w).1, hXU⟩ with hy'
  set A := inFrame d.b (ratG d hε X hX * (R.ι w y')⁻¹) with hA
  have hAC : A * inFrame d.b (R.ι w y') = incM F X := by
    rw [hA, ← inFrame_mul, inv_mul_cancel_right, inFrame_ratG]
  have hC : d.cw w (inFrame d.b (R.ι w y')) = X.map (d.B.emb w).1 := by
    have e := R.at_w w y'
    rw [show mR y' = dZ d.n R.ζ * X.map (d.B.emb w).1 * dZ d.n R.ζ⁻¹ from rfl, Matrix.mul_assoc _ (dZ _ R.ζ⁻¹),
      dZ_inv_mul h0, Matrix.mul_one] at e
    have := congrArg (fun M => dZ d.n R.ζ⁻¹ * M) e
    simpa only [← Matrix.mul_assoc, dZ_inv_mul h0, Matrix.one_mul] using this
  have hdet := det_of_inU hXU
  have hAw : d.cw w A = 1 := by
    have e : d.cw w A * X.map (d.B.emb w).1 = X.map (d.B.emb w).1 := by
      have := congrArg (d.cw w) hAC
      rwa [cw_mul, hC, cw_incM] at this
    calc d.cw w A = d.cw w A * X.map (d.B.emb w).1 * (X.map (d.B.emb w).1)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = 1 := by rw [e, Matrix.mul_nonsing_inv _ hdet]
  apply inFrame_inj d
  rw [inFrame_mul d _ (R.ι w y''), inFrame_mul d (R.ι w y''), ← hA]
  refine Place.cw_ext d (fun w' => ?_) ?_
  · rw [cw_mul, cw_mul]
    by_cases hw : w' = w
    · subst hw; rw [hAw, Matrix.one_mul, Matrix.mul_one]
    · rw [R.off_w w w' y'' hw, Matrix.one_mul, Matrix.mul_one]
  · rw [fin_mul, fin_mul, R.off_f w y'', ← fin_mul, ← fin_mul, Matrix.mul_one, Matrix.one_mul]

end
