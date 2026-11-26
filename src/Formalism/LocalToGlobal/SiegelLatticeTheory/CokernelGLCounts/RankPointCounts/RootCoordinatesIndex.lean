module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepPinExistsOfPlace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RelPtR

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealFrameCoordinates
noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.RealFrameCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word)

def g0 (γ : X.B.I.Ginf) (τ : D.what₂.Tau) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (γ (vOf X τ))

private theorem rdE_pos_rank_point_counts (D : D7) : 0 < D.host.rdE := by
  simp only [Formalism.BasicNotions.Host.rdE]
  apply Real.rpow_pos_of_pos
  rw [abs_pos]
  exact_mod_cast NumberField.discr_ne_zero (K := D.host.E)

private theorem frS_eq_inv_rdE (D : D7) : frS D = ((D.host.rdE : ℝ) : ℂ)⁻¹ := by
  have hne := (rdE_pos_rank_point_counts D).ne'
  have hpi := Real.pi_ne_zero
  have h : D.host.ka / (2 * Real.pi) = D.host.rdE⁻¹ := by
    simp only [Formalism.BasicNotions.Host.ka, Formalism.BasicNotions.Host.v]
    field_simp <;> ring
  simp only [frS, h, Complex.ofReal_inv]

private theorem rhoF_eq_frS_pow (D : D7) (a : Fin (D.R.rS + 1)) :
    ((rhoF D a : ℝ) : ℂ) = frS D ^ (D.R.rS - (a : ℕ)) := by
  have hpos := rdE_pos_rank_point_counts D
  have ha : (a : ℕ) ≤ D.R.rS := Nat.lt_succ_iff.mp a.isLt
  rw [frS_eq_inv_rdE]
  simp only [rhoF]
  rw [show (-((D.R.rS : ℝ) - ((a : ℕ) : ℝ))) = -(((D.R.rS - (a : ℕ) : ℕ) : ℝ)) by rw [Nat.cast_sub ha],
    Real.rpow_neg hpos.le, Real.rpow_natCast, Complex.ofReal_inv, Complex.ofReal_pow, inv_pow]

private theorem Q_mulVec_fvec_eq_smul_frm (τ : D.what₂.Tau) (a : Fin (D.R.rS + 1)) :
    C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) a =
      ((rhoF D a : ℝ) : ℂ) • Formalism.L2.SG.RealObj.frm X u 1 (vOf X τ) a := by
  obtain ⟨-, h2, -, h4⟩ := C.isT τ
  induction a using Fin.lastCases with
  | last =>
    simp only [Formalism.QuantumDeterminants.fvec, Fin.val_last, lt_self_iff_false, dite_false, zB, Matrix.mulVec_mulVec, h2,
      Matrix.one_mulVec, rhoF_eq_frS_pow, Nat.sub_self, pow_zero, one_smul, Formalism.L2.SG.RealObj.frm,
      Formalism.L2.SG.RealObj.famSc, Formalism.L2.SG.RealObj.fam, Fin.snoc_last, Complex.ofReal_one, one_pow, inv_one]
  | cast i =>
    obtain ⟨hq, -⟩ := h4 i i rfl
    simp only [Formalism.QuantumDeterminants.fvec, Fin.coe_castSucc, i.isLt, dite_true, Fin.eta, Formalism.QuantumDeterminants.bvec, hq, rhoF_eq_frS_pow,
      Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc, Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc,
      Complex.ofReal_one, one_pow, inv_one, one_smul]

private theorem herm_Hpk_eq_hJ_Q_mulVec (τ : D.what₂.Tau) (x y : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) x y =
      hJ (X.B.I.ε (vOf X τ)) (C.Q τ *ᵥ y) (C.Q τ *ᵥ x) := by
  obtain ⟨-, -, h3, -⟩ := C.isT τ
  rw [← h3]
  simp only [Formalism.QuantumDeterminants.herm, hJ, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

private theorem Q_mulVec_g0_mulVec_eq (γ : X.B.I.Ginf) (τ : D.what₂.Tau) (w : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) :
    C.Q τ *ᵥ ((g0 C γ τ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) *ᵥ w) =
      uMat (γ (vOf X τ)) *ᵥ (C.Q τ *ᵥ w) := by
  obtain ⟨-, h2, -, -⟩ := C.isT τ
  simp only [g0, Formalism.L2.SG.RealObj.trG, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem zhat_conjugator_scaled (γ : X.B.I.Ginf) (τ : D.what₂.Tau) (a b : Fin (D.R.rS + 1)) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (g0 C γ τ) a b =
      ((rhoF D a * rhoF D b : ℝ) : ℂ) * Formalism.L2.SG.RealObj.ZX X u u' 1 γ (vOf X τ) a b := by
  simp only [Formalism.QuantumDeterminants.Zhat]
  rw [herm_Hpk_eq_hJ_Q_mulVec C τ, Q_mulVec_g0_mulVec_eq C γ τ, Q_mulVec_fvec_eq_smul_frm C u τ, Q_mulVec_fvec_eq_smul_frm C u' τ]
  have hs : ∀ x : ℝ, star (x : ℂ) = (x : ℂ) := fun x => Complex.conj_ofReal x
  simp only [Formalism.L2.SG.RealObj.ZX, Formalism.L2.SG.RealObj.Zhat, hJ, Matrix.mulVec_smul, star_smul, hs,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  push_cast
  ring

private theorem ptEntry_locBlocksFrom_eq (D : D7) (τ : D.what₂.Tau) :
    ∀ (L : List (D.host.E × ℕ)) (A i j : ℕ),
      ptEntry (locBlocksFrom D (rhoReal D) τ A L) i j =
        ((D.host.rdE ^ (-((D.R.rS : ℤ) - ((A + i : ℕ) : ℤ))) *
          D.host.rdE ^ (-((D.R.rS : ℤ) - ((A + j : ℕ) : ℤ))) : ℝ) : ℂ) * plEmb D τ (ptEntry L i j) := by
  have hne : D.host.rdE ≠ 0 := (rdE_pos_rank_point_counts D).ne'
  intro L
  induction L with
  | nil =>
    intro A i j
    simp only [locBlocksFrom, ptEntry, map_zero, mul_zero]
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    intro A i j
    simp only [locBlocksFrom, ptEntry]
    by_cases h1 : i < s ∧ j < s
    · rw [if_pos h1, if_pos h1]
      by_cases h2 : i + j + 1 = s
      · rw [if_pos h2, if_pos h2]
        have hz : rhoReal D (A + 1) s = D.host.rdE ^ (-((D.R.rS : ℤ) - ((A + i : ℕ) : ℤ))) *
            D.host.rdE ^ (-((D.R.rS : ℤ) - ((A + j : ℕ) : ℤ))) := by
          rw [← zpow_add₀ hne]
          simp only [rhoReal]
          congr 1
          push_cast
          omega
        rw [hz]
      · rw [if_neg h2, if_neg h2, map_zero, mul_zero]
    · rw [if_neg h1, if_neg h1]
      by_cases h3 : s ≤ i ∧ s ≤ j
      · rw [if_pos h3, if_pos h3, ih]
        obtain ⟨h3i, h3j⟩ := h3
        rw [show A + s + (i - s) = A + i by omega, show A + s + (j - s) = A + j by omega]
      · rw [if_neg h3, if_neg h3, map_zero, mul_zero]

theorem zhat_conjugator_eq_point (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (hrep : Formalism.L2.SG.RealObj.IsPtRep X u u' w γ)
    (τ : D.what₂.Tau) :
    ZhatO D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (g0 C γ τ) = ptMat (ptLoc D τ w) := by
  funext a b
  have hv : X.pl (vOf X τ) = τ := X.pl.apply_symm_apply τ
  have hpe : ∀ x, plEmb D τ x = embS D τ x := fun x => rfl
  have hρ : ∀ c : Fin (D.R.rS + 1), rhoF D c = D.host.rdE ^ (-((D.R.rS : ℤ) - ((c : ℕ) : ℤ))) := by
    intro c
    simp only [rhoF]
    rw [← Real.rpow_intCast]
    norm_num
  have hr := congrFun (congrFun (hrep (vOf X τ)) a) b
  simp only [Formalism.L2.SG.RealObj.ZhatO, Formalism.L2.SG.RealObj.ptC, Matrix.map_apply, X.φ_eq,
    RingEquiv.apply_symm_apply, hv, ptMat] at hr
  simp only [ZhatO, zhat_conjugator_scaled C u u' γ τ, ptMat, ptLoc, ptLocS, locBlocks, ptEntry_locBlocksFrom_eq, Nat.zero_add, hpe, hρ]
  rw [← hr]
  push_cast
  ring

theorem frS_mul_rd (D : D7) : frS D * (D.host.rdE : ℂ) = 1 := by
  rw [frS_eq_inv_rdE]
  exact inv_mul_cancel₀ (by exact_mod_cast (rdE_pos_rank_point_counts D).ne')

theorem rho_eq (D : D7) (b : Fin (D.R.rS + 1)) :
    ((rhoF D b : ℝ) : ℂ) = ((D.host.rdE : ℂ) ^ (D.R.rS - b.val))⁻¹ := by
  rw [rhoF_eq_frS_pow, frS_eq_inv_rdE, inv_pow]

theorem hpk_esI (k r : ℕ) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    (Formalism.QuantumDeterminants.Hpk k r *ᵥ v) (Formalism.QuantumDeterminants.esI k r a) = v (Formalism.QuantumDeterminants.eI k r a) := by
  have ha := a.isLt
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (Formalism.QuantumDeterminants.eI k r a)]
  · have h1 : Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.esI k r a) (Formalism.QuantumDeterminants.eI k r a) = 1 := by
      simp only [Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.esI, Formalism.QuantumDeterminants.eI, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ a.val := fun h => hj (Fin.ext (by simp [Formalism.QuantumDeterminants.eI, h]))
    have h0 : Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.esI k r a) j = 0 := by
      simp only [Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.esI, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> first | rfl | (exfalso; omega)
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

def cMg (γ : X.B.I.Ginf) (τ : D.what₂.Tau) (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
  C.Qi τ * ((uMat (γ (vOf X τ)))⁻¹ * uMat y * uMat (γ (vOf X τ))) * C.Q τ

private theorem mulVec_apply_eq_herm_single {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ) (i : Fin m) :
    (H *ᵥ x) i = Formalism.QuantumDeterminants.herm H x (Pi.single i 1) := by
  have hs : star (Pi.single i 1 : Fin m → ℂ) = Pi.single i 1 := by
    ext j
    by_cases h : j = i <;> simp [Pi.single_apply, h]
  simp [Formalism.QuantumDeterminants.herm, hs, dotProduct, Pi.single_apply]

private theorem Q_mulVec_cMg_mulVec_eq (γ : X.B.I.Ginf) (τ : D.what₂.Tau) (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (f : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) :
    C.Q τ *ᵥ (cMg C γ τ y *ᵥ f) =
      ((uMat (γ (vOf X τ)))⁻¹ * uMat y * uMat (γ (vOf X τ))) *ᵥ (C.Q τ *ᵥ f) := by
  obtain ⟨-, h2, -, -⟩ := C.isT τ
  simp only [cMg, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem stCoordV_eq (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (τ : D.what₂.Tau)
    (y : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (p : Formalism.L2.SG.RealObj.FreeE w) :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) y p =
      (cMg C γ τ y *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u' τ) p.1.2)
        (Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨p.1.1.1, by have := p.2.1; have := p.1.2.isLt; omega⟩) := by
  obtain ⟨-, -, -, h4⟩ := C.isT τ
  have hlt : p.1.1.1 < D.R.rS := by have := p.2.1; have := p.1.2.isLt; omega
  have hs : ∀ x : ℝ, star (x : ℂ) = (x : ℂ) := fun x => Complex.conj_ofReal x
  have hU : uMat ((γ (vOf X τ))⁻¹ * y * γ (vOf X τ)) =
      (uMat (γ (vOf X τ)))⁻¹ * uMat y * uMat (γ (vOf X τ)) := by
    simp [uMat, Matrix.coe_units_inv]
  have hc : (star (frS D ^ (D.R.rS - ((⟨p.1.1.1, hlt⟩ : Fin D.R.rS) : ℕ))))⁻¹ =
      (D.host.rdE : ℂ) ^ (D.R.rS - p.1.1.1) := by
    rw [frS_eq_inv_rdE, ← Complex.ofReal_inv, ← Complex.ofReal_pow, hs, Complex.ofReal_pow, Complex.ofReal_inv,
      inv_pow, inv_inv]
  obtain ⟨-, hf⟩ := h4 ⟨p.1.1.1, hlt⟩ ⟨p.1.1.1, hlt⟩ rfl
  rw [← hpk_esI D.R.k D.R.rS ⟨p.1.1.1, hlt⟩
      (cMg C γ τ y *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u' τ) p.1.2),
    mulVec_apply_eq_herm_single, herm_Hpk_eq_hJ_Q_mulVec C τ, hf, hc, Q_mulVec_cMg_mulVec_eq C γ τ, Q_mulVec_fvec_eq_smul_frm C u' τ]
  simp only [Formalism.L2.SG.NGPin.stCoordV, hU, rho_eq, Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc,
    Complex.ofReal_one, one_pow, inv_one, one_smul, hJ, Matrix.mulVec_smul, star_smul, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hs, star_pow]
  ring

end Formalism.L2.SG.RealFrameCoordinates

end
end

noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.RootCoordinatesIndex

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ) (τ : D.what₂.Tau)

abbrev eV (a : Fin D.R.rS) : Fin X.B.I.n → ℂ := rv X.B.I (vOf X τ) (X.eR a)

theorem frS_ne (D : D7) : frS D ≠ 0 := by
  intro h0
  have := Formalism.L2.SG.RealFrameCoordinates.frS_mul_rd D
  rw [h0, zero_mul] at this
  exact zero_ne_one this

theorem Q_e (a : Fin D.R.rS) :
    C.Q τ *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 = frS D ^ (D.R.rS - a.val) • eV τ a :=
  ((C.isT τ).2.2.2 a a rfl).1

theorem Qi_e (a : Fin D.R.rS) :
    C.Qi τ *ᵥ eV τ a = (frS D ^ (D.R.rS - a.val))⁻¹ • Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 := by
  obtain ⟨hQiQ, _, _, _⟩ := C.isT τ
  have h := congrArg (fun x => C.Qi τ *ᵥ x) (Q_e C τ a)
  simp only [Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec, Matrix.mulVec_smul] at h
  rw [h, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (frS_ne D)), one_smul]

theorem Qi_spanLt (a : ℕ) (x : Fin X.B.I.n → ℂ) (hx : x ∈ spanLt (eV (X := X) τ) a) (i : Fin (2 * D.R.rS + D.R.k + 1))
    (hi : a ≤ i.val) : (C.Qi τ *ᵥ x) i = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨b, hb, rfl⟩ := hx'
    rw [Qi_e, Pi.smul_apply, Pi.single_apply, if_neg, smul_zero]
    intro h
    have := congrArg Fin.val h
    simp only [Formalism.QuantumDeterminants.eI] at this
    simp only [Set.mem_setOf_eq] at hb
    omega
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, Pi.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [Matrix.mulVec_smul, Pi.smul_apply, hx, smul_zero]

theorem Q_spanLt (a : ℕ) (ha : a ≤ D.R.rS) (w : Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (hw : ∀ i : Fin (2 * D.R.rS + D.R.k + 1), a ≤ i.val → w i = 0) : C.Q τ *ᵥ w ∈ spanLt (eV (X := X) τ) a := by
  have hw' : w = ∑ i, w i • Pi.single i (1 : ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hw', Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : a ≤ i.val
  · rw [hw i hi, zero_smul, Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  · have hir : i.val < D.R.rS := by omega
    have e : i = Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨i.val, hir⟩ := Fin.ext rfl
    rw [Matrix.mulVec_smul, e, Q_e]
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i.val, hir⟩, ?_, rfl⟩))
    simp only [Set.mem_setOf_eq]
    omega

theorem hpk_eI (k r : ℕ) (a : Fin r) (v : Fin (2 * r + k + 1) → ℂ) :
    (Formalism.QuantumDeterminants.Hpk k r *ᵥ v) (Formalism.QuantumDeterminants.eI k r a) = v (Formalism.QuantumDeterminants.esI k r a) := by
  have hrow : ∀ j, Formalism.QuantumDeterminants.Hpk k r (Formalism.QuantumDeterminants.eI k r a) j = if j = Formalism.QuantumDeterminants.esI k r a then 1 else 0 := by
    intro j
    have ha := a.isLt
    have hj := j.isLt
    simp only [Formalism.QuantumDeterminants.Hpk, Formalism.QuantumDeterminants.esI, Formalism.QuantumDeterminants.eI, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | rfl | omega | (exfalso; omega)
  simp only [Matrix.mulVec, dotProduct, hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

theorem hJ_e (a : Fin D.R.rS) (y : Fin X.B.I.n → ℂ) :
    hJ (X.B.I.ε (vOf X τ)) (eV τ a) y = star ((frS D ^ (D.R.rS - a.val))⁻¹) * (C.Qi τ *ᵥ y) (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) := by
  obtain ⟨_, hQQi, hH, _⟩ := C.isT τ
  have he : eV τ a = (frS D ^ (D.R.rS - a.val))⁻¹ • (C.Q τ *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1) := by
    rw [Q_e, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (frS_ne D)), one_smul]
  have hy : y = C.Q τ *ᵥ (C.Qi τ *ᵥ y) := by rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
  conv_lhs => rw [he, hy]
  unfold hJ
  rw [star_smul, smul_dotProduct, ← Formalism.L2.SG.Pf.LTL.star_dot_conjT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH,
    Pi.star_single, star_one, single_dotProduct, one_mul, hpk_eI, smul_eq_mul]

variable {C τ}

theorem inN_iff (z : Fin X.B.I.n → ℂ) (hz : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS (C.Qi τ *ᵥ z))
    (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) (hg : gᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * g = Formalism.REAL.Jm (X.B.I.ε (vOf X τ))) :
    InN (X.B.I.ε (vOf X τ)) (eV τ) z g ↔ C.Qi τ * g * C.Q τ ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS := by
  obtain ⟨hQiQ, hQQi, hH, _⟩ := C.isT τ
  have hstar_ne : ∀ a : Fin D.R.rS, star ((frS D ^ (D.R.rS - a.val))⁻¹) ≠ 0 := fun a =>
    star_ne_zero.2 (inv_ne_zero (pow_ne_zero _ (frS_ne D)))
  have hcol : ∀ (M : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) i j,
      M i j = (M *ᵥ Pi.single j 1) i := fun M i j => by rw [Matrix.mulVec_single_one]; rfl
  constructor
  · rintro ⟨⟨hIe, hIz⟩, hperp⟩
    refine ⟨?_, fun a i hai => ?_, fun i j hj1 hj2 hi => ?_⟩
    ·
      show (C.Qi τ * g * C.Q τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.Qi τ * g * C.Q τ) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
      have hQiQ' : (C.Qi τ)ᴴ * (C.Q τ)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQQi, Matrix.conjTranspose_one]
      rw [← hH]
      calc (C.Qi τ * g * C.Q τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * (C.Qi τ * g * C.Q τ)
          = (C.Q τ)ᴴ * (gᴴ * ((C.Qi τ)ᴴ * (C.Q τ)ᴴ) * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * ((C.Q τ * C.Qi τ) * g)) *
              C.Q τ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hQiQ', hQQi, Matrix.mul_one, Matrix.one_mul, hg]
    ·
      rw [hcol (C.Qi τ * g * C.Q τ) i (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a)]
      have h1 : (C.Qi τ * g * C.Q τ) *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 =
          Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 +
            frS D ^ (D.R.rS - a.val) • (C.Qi τ *ᵥ ((g - 1) *ᵥ eV τ a)) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Q_e, Matrix.mulVec_smul, Matrix.mulVec_smul,
          Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Qi_e, smul_sub, smul_smul,
          mul_inv_cancel₀ (pow_ne_zero _ (frS_ne D)), one_smul]
        abel
      rw [h1, Pi.add_apply, Pi.smul_apply, Qi_spanLt C τ a.val _ (hIe a) i hai, smul_zero, add_zero, Pi.single_apply]
    ·
      rw [hcol (C.Qi τ * g * C.Q τ) i j]
      have horth : ∀ b : Fin D.R.rS, hJ (X.B.I.ε (vOf X τ)) (eV τ b) (C.Q τ *ᵥ Pi.single j 1) = 0 := by
        intro b
        rw [hJ_e, Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec, Pi.single_apply, if_neg, mul_zero]
        intro h
        have := congrArg Fin.val h
        simp only [Formalism.QuantumDeterminants.esI] at this
        have := b.isLt
        omega
      have h1 : (C.Qi τ * g * C.Q τ) *ᵥ Pi.single j 1 =
          Pi.single j 1 + C.Qi τ *ᵥ ((g - 1) *ᵥ (C.Q τ *ᵥ Pi.single j 1)) := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
        simp only [Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec, Matrix.mul_assoc]
        abel
      rw [h1, Pi.add_apply, Qi_spanLt C τ D.R.rS _ (hperp _ horth) i hi, add_zero, Pi.single_apply]
  · rintro ⟨_, hce, hcw⟩
    have hg' : g = C.Q τ * (C.Qi τ * g * C.Q τ) * C.Qi τ := by
      simp only [← Matrix.mul_assoc]
      rw [hQQi, Matrix.one_mul, Matrix.mul_assoc, hQQi, Matrix.mul_one]
    set m := C.Qi τ * g * C.Q τ with hm
    have key : ∀ x, (g - 1) *ᵥ x = C.Q τ *ᵥ ((m - 1) *ᵥ (C.Qi τ *ᵥ x)) := by
      intro x
      conv_lhs => rw [hg']
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]

    have hmW : ∀ x : Fin (2 * D.R.rS + D.R.k + 1) → ℂ, (∀ a, x (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) = 0) →
        ∀ i : Fin (2 * D.R.rS + D.R.k + 1), D.R.rS ≤ i.val → ((m - 1) *ᵥ x) i = 0 := by
      intro x hx i hi
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj1 : j.val < D.R.rS
      · have e : j = Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨j.val, hj1⟩ := Fin.ext rfl
        have := hce ⟨j.val, hj1⟩ i (by simp only; omega)
        rw [Matrix.sub_apply, e, this, Matrix.one_apply, sub_self, zero_mul]
      · by_cases hj2 : j.val ≤ D.R.rS + D.R.k
        · rw [Matrix.sub_apply, hcw i j (by omega) hj2 hi, Matrix.one_apply, sub_self, zero_mul]
        · have hjr : 2 * D.R.rS + D.R.k - j.val < D.R.rS := by have := j.isLt; omega
          have e : j = Formalism.QuantumDeterminants.esI D.R.k D.R.rS ⟨2 * D.R.rS + D.R.k - j.val, hjr⟩ := by
            ext; simp only [Formalism.QuantumDeterminants.esI]; have := j.isLt; omega
          rw [e, hx, mul_zero]
    refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
    · rw [key, Qi_e, Matrix.mulVec_smul, Matrix.mulVec_smul]
      refine Submodule.smul_mem _ _ (Q_spanLt C τ a.val a.isLt.le _ fun i hi => ?_)
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, ← hcol m i (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a), hce a i hi,
        Pi.single_apply, sub_self]
    · rw [key]
      refine Q_spanLt C τ D.R.rS le_rfl _ (hmW _ (fun a => hz _ (Or.inr ?_)))
      simp only [Formalism.QuantumDeterminants.esI]
      have := a.isLt
      omega
    · rw [key]
      refine Q_spanLt C τ D.R.rS le_rfl _ (hmW _ fun a => ?_)
      have h1 := hy a
      rw [hJ_e] at h1
      exact (mul_eq_zero.1 h1).resolve_left (hstar_ne a)

end Formalism.L2.SG.RootCoordinatesIndex

end
