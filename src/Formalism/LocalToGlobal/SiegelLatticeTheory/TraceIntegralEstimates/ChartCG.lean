module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.HHRed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootPatterns

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ChartC
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.StCoordVCoef
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ChartLaw
noncomputable section

open scoped Matrix
open Finset Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

namespace Formalism.L2.S.Pv.Chart

variable {n r : ℕ} (ε : Fin n → Bool)

theorem hJ_add (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  simp only [hJ, Matrix.mulVec_add, dotProduct_add]

theorem hJ_smul (x y : Fin n → ℂ) (c : ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  simp only [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_zero (x : Fin n → ℂ) : hJ ε x 0 = 0 := by
  simp only [hJ, Matrix.mulVec_zero, dotProduct_zero]

theorem hJ_sum {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (g : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, g i) = ∑ i ∈ s, hJ ε x (g i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, hJ_zero]
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hJ_add, ih]

variable (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
  (hdual : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
include hdual

theorem span_expand (b : ℕ) (v : Fin n → ℂ) (hv : v ∈ spanLt e b) :
    v = ∑ c, hJ ε (f c) v • e c ∧ ∀ c : Fin r, b ≤ c.1 → hJ ε (f c) v = 0 := by
  unfold spanLt at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, hd, rfl⟩ := hx
    rw [Set.mem_setOf_eq] at hd
    refine ⟨?_, fun c hc => ?_⟩
    · simp_rw [hdual, ite_smul, one_smul, zero_smul]
      rw [Finset.sum_ite_eq' Finset.univ d (fun c => e c), if_pos (Finset.mem_univ d)]
    · rw [hdual, if_neg]
      intro h
      subst h
      omega
  | zero =>
    refine ⟨?_, fun c _ => hJ_zero ε _⟩
    simp_rw [hJ_zero, zero_smul, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    refine ⟨?_, fun c hc => by rw [hJ_add, hx.2 c hc, hy.2 c hc, add_zero]⟩
    simp_rw [hJ_add, add_smul]
    rw [Finset.sum_add_distrib, ← hx.1, ← hy.1]
  | smul a x _ hx =>
    refine ⟨?_, fun c hc => by rw [hJ_smul, hx.2 c hc, mul_zero]⟩
    simp_rw [hJ_smul, mul_smul]
    rw [← Finset.smul_sum, ← hx.1]

include hfz

theorem hJ_fam (c : Fin r) (b : Fin (r + 1)) (hcb : c.1 < b.1) : hJ ε (f c) (fam e z b) = 0 := by
  induction b using Fin.lastCases with
  | last => simp only [fam, Fin.snoc_last]; exact hfz c
  | cast b' =>
    simp only [fam, Fin.snoc_castSucc]
    rw [hdual, if_neg]
    intro h
    subst h
    simp at hcb

theorem sub_mem_spanLt {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (b : Fin (r + 1)) :
    (g - 1) *ᵥ fam e z b ∈ spanLt e b.1 := by
  induction b using Fin.lastCases with
  | last => simpa only [fam, Fin.snoc_last, Fin.val_last] using hg.2
  | cast b' => simpa only [fam, Fin.snoc_castSucc, Fin.coe_castSucc] using hg.1 b'

theorem expand {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (b : Fin (r + 1)) :
    g *ᵥ fam e z b = fam e z b + ∑ c : Fin r, (if c.1 < b.1 then hJ ε (f c) (g *ᵥ fam e z b) else 0) • e c := by
  obtain ⟨hw, hw0⟩ := span_expand ε e f hdual b.1 _ (sub_mem_spanLt ε e f z hdual hfz hg b)
  have hgw : g *ᵥ fam e z b = fam e z b + (g - 1) *ᵥ fam e z b := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have hc : ∀ c : Fin r, (if c.1 < b.1 then hJ ε (f c) (g *ᵥ fam e z b) else 0) =
      hJ ε (f c) ((g - 1) *ᵥ fam e z b) := by
    intro c
    split_ifs with h
    · rw [hgw, hJ_add, hJ_fam ε e f z hdual hfz c b h, zero_add]
    · exact (hw0 c (not_lt.mp h)).symm
  simp_rw [hc]
  rw [← hw]
  exact hgw

theorem coef_diag {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (a : Fin r) :
    hJ ε (f a) (g *ᵥ e a) = 1 := by
  have hw0 := (span_expand ε e f hdual a.1 _ (hg.1 a)).2 a le_rfl
  have hgw : g *ᵥ e a = e a + (g - 1) *ᵥ e a := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [hgw, hJ_add, hw0, hdual, if_pos rfl, add_zero]

theorem coef_low {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (a c : Fin r) (h : c.1 < a.1) :
    hJ ε (f a) (g *ᵥ e c) = 0 := by
  have hw0 := (span_expand ε e f hdual c.1 _ (hg.1 c)).2 a h.le
  have hgw : g *ᵥ e c = e c + (g - 1) *ᵥ e c := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  rw [hgw, hJ_add, hw0, hdual, if_neg (fun h' => by subst h'; exact lt_irrefl _ h), add_zero]

theorem coef_mul {g₁ g₂ : Matrix (Fin n) (Fin n) ℂ} (h₁ : InS e z g₁) (h₂ : InS e z g₂) (a : Fin r)
    (b : Fin (r + 1)) (hab : a.1 < b.1) :
    hJ ε (f a) ((g₁ * g₂) *ᵥ fam e z b) = hJ ε (f a) (g₁ *ᵥ fam e z b) + hJ ε (f a) (g₂ *ᵥ fam e z b) +
      ∑ c : Fin r, if a.1 < c.1 ∧ c.1 < b.1 then hJ ε (f a) (g₁ *ᵥ e c) * hJ ε (f c) (g₂ *ᵥ fam e z b) else 0 := by
  have hx := expand ε e f z hdual hfz h₂ b
  conv_lhs => rw [← Matrix.mulVec_mulVec, hx]
  rw [Matrix.mulVec_add, Matrix.mulVec_sum, hJ_add, hJ_sum]
  simp_rw [Matrix.mulVec_smul, hJ_smul]
  rw [add_assoc]
  congr 1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ (Finset.mem_univ a),
    if_pos hab, coef_diag ε e f z hdual hfz h₁ a, mul_one, if_neg (by omega), zero_add]
  congr 1
  refine Finset.sum_congr rfl fun c hc => ?_
  have hca : c ≠ a := Finset.ne_of_mem_erase hc
  rcases lt_or_gt_of_ne (fun h' : c.1 = a.1 => hca (Fin.ext h')) with h | h
  · rw [coef_low ε e f z hdual hfz h₁ a c h, mul_zero, if_neg (by omega)]
  · by_cases hcb : c.1 < b.1
    · rw [if_pos hcb, if_pos ⟨h, hcb⟩, mul_comm]
    · rw [if_neg hcb, if_neg (by omega), zero_mul]

end Formalism.L2.S.Pv.Chart

end
end

noncomputable section

open scoped Matrix
open Finset NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj

namespace Formalism.L2.S.Pv.Chart

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hJ_conj {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) : hJ ε x y = star (hJ ε y x) := by
  unfold hJ Formalism.REAL.Jm
  simp only [Matrix.mulVec_diagonal, dotProduct, star_sum, star_mul']
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [mul_comm]

theorem blkOf_mono {K : Type*} : ∀ (l : List (K × ℕ)) (i j : ℕ), i ≤ j → blkOf l i ≤ blkOf l j
  | [], _, _, _ => le_rfl
  | (x, s) :: bs, i, j, h => by
    unfold blkOf
    by_cases hi : i < s
    · rw [if_pos hi]; exact Nat.zero_le _
    · have hj : ¬ j < s := fun hj => hi (lt_of_le_of_lt h hj)
      rw [if_neg hi, if_neg hj]
      exact Nat.succ_le_succ (blkOf_mono bs (i - s) (j - s) (Nat.sub_le_sub_right h s))

variable {D : D7} {w : Point D.host.E (D.R.rS + 1)}

theorem blk_mid (p : FreeE w) (c : Fin (D.R.rS + 1)) (h : p.1.1 < c ∧ c < p.1.2) :
    blkOf w.1 p.1.1.1 = blkOf w.1 c.1 ∧ blkOf w.1 c.1 = blkOf w.1 p.1.2.1 := by
  have h1 := blkOf_mono w.1 p.1.1.1 c.1 (le_of_lt h.1)
  have h2 := blkOf_mono w.1 c.1 p.1.2.1 (le_of_lt h.2)
  have h3 := p.2.2
  omega

def midL (p : FreeE w) (c : Fin (D.R.rS + 1)) (h : p.1.1 < c ∧ c < p.1.2) : FreeE w :=
  ⟨(p.1.1, c), h.1, (blk_mid p c h).1⟩

def midR (p : FreeE w) (c : Fin (D.R.rS + 1)) (h : p.1.1 < c ∧ c < p.1.2) : FreeE w :=
  ⟨(c, p.1.2), h.2, (blk_mid p c h).2⟩

def BX (p : FreeE w) (x y : FreeE w → ℂ) : ℂ :=
  ∑ c : Fin (D.R.rS + 1), if h : p.1.1 < c ∧ c < p.1.2 then x (midL p c h) * y (midR p c h) else 0

theorem BX_zero (p : FreeE w) (x : FreeE w → ℂ) : BX p x 0 = 0 := by
  unfold BX; simp

theorem BX_lower (p : FreeE w) (x x' y y' : FreeE w → ℂ)
    (h : ∀ q : FreeE w, q.1.2.val - q.1.1.val < p.1.2.val - p.1.1.val → x q = x' q ∧ y q = y' q) :
    BX p x y = BX p x' y' := by
  unfold BX
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with hc
  · have h1 := h (midL p c hc) (by
      simp only [midL]; have := hc.1; have := hc.2
      have : c.val < p.1.2.val := hc.2
      have : p.1.1.val < c.val := hc.1
      omega)
    have h2 := h (midR p c hc) (by
      simp only [midR]
      have : c.val < p.1.2.val := hc.2
      have : p.1.1.val < c.val := hc.1
      omega)
    rw [h1.1, h2.2]
  · rfl

theorem BX_measurable (p : FreeE w) : Measurable (fun z : (FreeE w → ℂ) × (FreeE w → ℂ) => BX p z.1 z.2) := by
  unfold BX
  refine Finset.measurable_sum _ fun c _ => ?_
  split_ifs with hc
  · exact ((measurable_pi_apply _).comp measurable_fst).mul ((measurable_pi_apply _).comp measurable_snd)
  · exact measurable_const

section Law

variable (X : HidaSetting D) (v : InfinitePlace X.B.I.F)

theorem dual_v (a b : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.eR b)) = if a = b then 1 else 0 := by
  rw [hJ_conj, show X.eR b = X.crd (X.eX b) from rfl, show X.fR a = X.crd (X.fY a) from rfl,
    Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, X.ef]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, map_zero, star_zero]

theorem fz_v (u' : D.what₂.Word) (a : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u')) = 0 := by
  rw [show X.zR u' = X.crd (X.zu u') from rfl, show X.fR a = X.crd (X.fY a) from rfl,
    Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth u' a).2, map_zero]

theorem ha_free (q : FreeE w) : q.1.1.1 < D.R.rS := by have := q.2.1; have := q.1.2.isLt; omega

theorem stCoordV_coef (u' : D.what₂.Word) (γ : X.B.I.Ginf) (y : Formalism.REAL.UJ (X.B.I.ε v)) (q : FreeE w) :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ v y q =
      (D.host.rdE : ℂ) ^ (D.R.rS - q.1.1.1) * ((D.host.rdE : ℂ) ^ (D.R.rS - q.1.2.1))⁻¹ *
        hJ (X.B.I.ε v) (rv X.B.I v (X.fR ⟨q.1.1.1, ha_free q⟩))
          (uMat ((γ v)⁻¹ * y * γ v) *ᵥ fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) q.1.2) := by
  unfold Formalism.L2.SG.NGPin.stCoordV frm famSc
  rw [Matrix.mulVec_smul, hJ_smul]
  ring

theorem stCoordV_mul {u u' : D.what₂.Word} {γ : X.B.I.Ginf} {y₁ y₂ : Formalism.REAL.UJ (X.B.I.ε v)}
    (h₁ : y₁ ∈ Formalism.L2.SG.NGPin.StV X u u' γ v) (h₂ : y₂ ∈ Formalism.L2.SG.NGPin.StV X u u' γ v) (p : FreeE w) :
    Formalism.L2.SG.NGPin.stCoordV X u' w γ v (y₁ * y₂) p =
      Formalism.L2.SG.NGPin.stCoordV X u' w γ v y₁ p + Formalism.L2.SG.NGPin.stCoordV X u' w γ v y₂ p +
        BX p (Formalism.L2.SG.NGPin.stCoordV X u' w γ v y₁) (Formalism.L2.SG.NGPin.stCoordV X u' w γ v y₂) := by
  have hdual := dual_v X v
  have hfz := fz_v X v u'
  have hS₁ : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat ((γ v)⁻¹ * y₁ * γ v)) := h₁.2.1
  have hS₂ : InS (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat ((γ v)⁻¹ * y₂ * γ v)) := h₂.2.1
  have hmul : uMat ((γ v)⁻¹ * (y₁ * y₂) * γ v) = uMat ((γ v)⁻¹ * y₁ * γ v) * uMat ((γ v)⁻¹ * y₂ * γ v) := by
    rw [show (γ v)⁻¹ * (y₁ * y₂) * γ v = ((γ v)⁻¹ * y₁ * γ v) * ((γ v)⁻¹ * y₂ * γ v) by group]; rfl
  have hrd : (D.host.rdE : ℂ) ≠ 0 := by
    have := Formalism.MainNotions.S.Pv.HH.one_le_rdE D
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one this))
  have hab : (⟨p.1.1.1, ha_free p⟩ : Fin D.R.rS).1 < p.1.2.1 := p.2.1
  unfold BX
  simp only [stCoordV_coef X v u' γ]
  rw [hmul, coef_mul (X.B.I.ε v) _ _ _ hdual hfz hS₁ hS₂ ⟨p.1.1.1, ha_free p⟩ p.1.2 hab,
    Fin.sum_univ_castSucc, dite_eq_right (fun h => (not_lt.2 (Fin.le_last _)) h.2), add_zero]
  rw [mul_add, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : p.1.1 < c.castSucc ∧ c.castSucc < p.1.2
  · rw [dite_eq_left hc, if_pos ⟨hc.1, hc.2⟩]
    simp only [midL, midR]
    have e1 : fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) c.castSucc = rv X.B.I v (X.eR c) := by
      unfold fam; rw [Fin.snoc_castSucc]
    rw [e1]
    simp only [Fin.val_castSucc, Fin.eta]
    have hpow : (D.host.rdE : ℂ) ^ (D.R.rS - c.castSucc.1) ≠ 0 := pow_ne_zero _ hrd
    field_simp
  · rw [dite_eq_right hc, if_neg (fun h => hc ⟨h.1, h.2⟩), mul_zero]

end Law

end Formalism.L2.S.Pv.Chart

end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.ChartLoc
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.BigCellDensity
open scoped ComplexConjugate

namespace Formalism.L2.S.Pv.Chart

theorem locChart (k r : ℕ) (hk : 1 ≤ k) (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hz' : inWb k r z') (hT' : 0 < Tz k r z') (p : Point ℂ (r + 1))
    (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hg : g₀ ∈ UH (Hpk k r)) (hZ : Formalism.MainNotions.S.ZhatO k r z z' g₀ = ptMat p) :
    ∃ ψ : (rootPat p → ℂ) → Mt k r,
      (∀ y, Matrix.of (ψ y) ∈ Formalism.MainNotions.S.Rset k r g₀ ∧ rootCoords k r z' p (ψ y) = y) ∧
      ∀ x : Mt k r, Matrix.of x ∈ Formalism.MainNotions.S.Rset k r g₀ → ψ (rootCoords k r z' p x) = x := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  obtain ⟨Ds, hDz, hDz'⟩ := Formalism.MainNotions.S.Pv.AmpDDPf.bsetting_of (k0 + 1) r hk z' z ⟨hz', hT'⟩ ⟨hz, hT⟩
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed (k0 + 1) r
  have hgG : g₀ ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r := hg
  have hu : IsUnit g₀.det := hG.unit g₀ hgG
  have hgi : g₀⁻¹ ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r := hG.inv_mem g₀ hgG
  set w := wPt p with hw
  let d : Fin (r + 1) → ℂ := fun a => (-1 : ℂ) ^ (r - (w a).val) * star (dPt p (w a))
  have hd : ∀ a, d a ≠ 0 := fun a => mul_ne_zero (pow_ne_zero _ (by norm_num)) (star_ne_zero.2 (dPt_ne p (w a)))
  have hmono : ptMat p = Formalism.FourierDecayAlt.C2.monoP w (dPt p) := by rw [← ptMatN_swap, ptMatN_mono]
  have hZ' : Formalism.QuantumDeterminants.Zhat (k0 + 1) r Ds.z Ds.z' g₀⁻¹ = Formalism.FourierDecayAlt.C2.monoP w d := by
    ext i a
    rw [hDz, hDz', Formalism.L2.SG.Pf.RootHaarLoc.zhat_inv z z' hg hu i a]
    have h1 := congrFun (congrFun hZ a) i
    unfold Formalism.MainNotions.S.ZhatO at h1
    have hs : ((-1 : ℂ) ^ (r - i.val)) * (-1 : ℂ) ^ (r - i.val) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have h2 : Formalism.QuantumDeterminants.Zhat (k0 + 1) r z z' g₀ a i = (-1 : ℂ) ^ (r - i.val) * ptMat p a i := by
      rw [← h1, ← mul_assoc, hs, one_mul]
    rw [h2, hmono]
    simp only [Formalism.FourierDecayAlt.C2.monoP, Matrix.of_apply]
    by_cases hai : a = w i
    · have hia : i = w a := by rw [hai, wPt_invol]
      rw [if_pos hai, if_pos hia]
      simp only [d, star_mul', star_pow, star_neg, star_one]
      rw [← hia]
    · have hia : ¬ i = w a := fun h => hai (by rw [h, wPt_invol])
      rw [if_neg hai, if_neg hia, mul_zero, star_zero]
  have hset : Formalism.FourierDecayAlt.C6.Rset g₀⁻¹ = Formalism.MainNotions.S.Rset (k0 + 1) r g₀ := by
    ext x
    simp only [Formalism.FourierDecayAlt.C6.Rset, Formalism.MainNotions.S.Rset, Set.mem_setOf_eq, Matrix.nonsing_inv_nonsing_inv _ hu]
  have hGd := good_of Ds hgi hd hZ'
  refine ⟨fun y => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g₀⁻¹ w (Tinv p y)), fun y => ⟨?_, ?_⟩, fun x hx => ?_⟩
  · have := (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_spec Ds hgi hd hGd (Tinv p y)).1
    rw [← hset]
    simpa only [Equiv.apply_symm_apply] using this
  · exact Formalism.L2.SG.Pf.RootHaarLoc.rootCoords_psiG z' Ds hDz p hgi hd hZ' y
  · rw [← hset] at hx
    exact Formalism.L2.SG.Pf.RootHaarLoc.psi_rootCoordsG z' Ds hDz p hgi hd hZ' x hx

end Formalism.L2.S.Pv.Chart

end
end

noncomputable section

open scoped Matrix Classical
open MeasureTheory Finset NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.L2.SG.LocWSOf

namespace Formalism.L2.S.Pv.Chart

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ) (u u' : D.what₂.Word)
  (w : Point D.host.E (D.R.rS + 1)) (γ : X.B.I.Ginf) (τ : D.what₂.Tau)

include C

theorem place_chart (hrep : IsPtRep X u u' w γ) :
    ∃ ψ : (rootPat (ptLoc D τ w) → ℂ) → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS,
      (∀ y, Matrix.of (ψ y) ∈ Formalism.MainNotions.S.Rset D.R.k D.R.rS (Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ) ∧
        rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (ptLoc D τ w) (ψ y) = y) ∧
      ∀ x, Matrix.of x ∈ Formalism.MainNotions.S.Rset D.R.k D.R.rS (Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ) →
        ψ (rootCoords D.R.k D.R.rS (zB X (C.Qi τ) u' τ) (ptLoc D τ w) x) = x := by
  obtain ⟨hzW, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  obtain ⟨hzW', hTz'⟩ := Formalism.L2.SG.Pf.zTr C u' τ
  have hT : ∀ u0 : D.what₂.Word, 0 < Tr D u0 := fun u0 => by
    unfold Tr
    exact Nat.cast_pos.2 (D.mem u0).A.T_prime.pos
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hg0 : Formalism.L2.SG.RealFrameCoordinates.g0 C γ τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
    Formalism.L2.SG.Pf.LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _
  exact locChart D.R.k D.R.rS hk _ _ hzW (by rw [hTz]; exact hT u) hzW' (by rw [hTz']; exact hT u') (ptLoc D τ w) _
    hg0 (Formalism.L2.SG.RealFrameCoordinates.zhat_conjugator_eq_point C u u' w γ hrep τ)

theorem stCoordV_inj (hrep : IsPtRep X u u' w γ) {y₁ y₂ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))}
    (h₁ : y₁ ∈ Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ)) (h₂ : y₂ ∈ Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ))
    (h : Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) y₁ = Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) y₂) :
    y₁ = y₂ := by
  obtain ⟨ψ, -, hψ⟩ := place_chart C u u' w γ τ hrep
  rw [Formalism.L2.SG.RootPatterns.stCoordV_comp C u' w γ τ] at h
  have h' := (MeasurableEquiv.piCongrLeft (fun _ : FreeE w => ℂ) (Formalism.L2.SG.RootPatterns.idxF τ w)).injective h
  have m₁ := (Formalism.L2.SG.RealConjugatorData.stV_iff C γ τ u u' y₁).1 h₁
  have m₂ := (Formalism.L2.SG.RealConjugatorData.stV_iff C γ τ u u' y₂).1 h₂
  have e := congrArg ψ h'
  simp only [Function.comp_apply] at e
  rw [hψ (Formalism.L2.SG.RealConjugatorData.cMr C γ τ y₁) m₁, hψ (Formalism.L2.SG.RealConjugatorData.cMr C γ τ y₂) m₂] at e
  exact (Formalism.L2.SG.RealConjugatorData.cMr_closedEmb C γ τ).injective e

theorem stCoordV_surj (hrep : IsPtRep X u u' w γ) (x : FreeE w → ℂ) :
    ∃ y ∈ Formalism.L2.SG.NGPin.StV X u u' γ (vOf X τ), Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ) y = x := by
  obtain ⟨ψ, hψ, -⟩ := place_chart C u u' w γ τ hrep
  set e := MeasurableEquiv.piCongrLeft (fun _ : FreeE w => ℂ) (Formalism.L2.SG.RootPatterns.idxF τ w)
  obtain ⟨hm, hc⟩ := hψ (e.symm x)
  obtain ⟨y, hy⟩ := Formalism.L2.SG.RealConjugatorData.rset_range C γ τ _ hm
  refine ⟨y, (Formalism.L2.SG.RealConjugatorData.stV_iff C γ τ u u' y).2 (by rw [hy]; exact hm), ?_⟩
  rw [Formalism.L2.SG.RootPatterns.stCoordV_comp C u' w γ τ]
  simp only [Function.comp_apply]
  rw [hy, hc, e.apply_symm_apply]

theorem stCoordV_meas : Measurable (Formalism.L2.SG.NGPin.stCoordV X u' w γ (vOf X τ)) := by
  rw [Formalism.L2.SG.RootPatterns.stCoordV_comp C u' w γ τ]
  exact (MeasurableEquiv.measurable _).comp ((Formalism.L2.SG.RootPatterns.rootCoords_cont _ _ _ _).measurable.comp
    (Formalism.L2.SG.RealConjugatorData.cMr_measEmb C γ τ).measurable)

end Formalism.L2.S.Pv.Chart

end
end

noncomputable section

open scoped Matrix Classical
open MeasureTheory Finset NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
  Formalism.L2.SG.LocWSOf

namespace Formalism.L2.S.Pv.Chart

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isClosed_inN {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | InN ε e z g} := by
  have hS : ∀ (S : Submodule ℂ (Fin n → ℂ)) (x : Fin n → ℂ),
      IsClosed {g : Matrix (Fin n) (Fin n) ℂ | (g - 1) *ᵥ x ∈ S} := fun S x =>
    S.closed_of_finiteDimensional.preimage ((continuous_id.sub continuous_const).matrix_mulVec continuous_const)
  unfold InN InS
  simp only [Set.setOf_and, Set.setOf_forall]
  exact ((isClosed_iInter fun a => hS _ _).inter (hS _ _)).inter
    (isClosed_iInter fun y => isClosed_iInter fun _ => hS _ _)

variable {D : D7}

theorem isClosed_stV (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (v : InfinitePlace X.B.I.F) :
    IsClosed (Formalism.L2.SG.NGPin.StV X u u' γ v) := by
  have hu : Continuous fun y : Formalism.REAL.UJ (X.B.I.ε v) => uMat y :=
    Units.continuous_val.comp continuous_subtype_val
  have hc : Continuous fun y : Formalism.REAL.UJ (X.B.I.ε v) => uMat ((γ v)⁻¹ * y * γ v) :=
    hu.comp ((continuous_const.mul continuous_id).mul continuous_const)
  exact ((isClosed_inN _ _ _).preimage hu).inter ((isClosed_inN _ _ _).preimage hc)

theorem chartC_holds : Formalism.L2.SG.NGCut.StabilizerCovolume.ChartC := by
  intro D X Y u u' t hrel hG w hw γw s s' hrep hs hs' hpt
  have : Nonempty D.what₂.Word := ⟨u⟩
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  have hτ : ∀ v : InfinitePlace X.B.I.F, ∃ τ, vOf X τ = v := fun v => ⟨X.pl v, X.pl.symm_apply_apply v⟩
  have hpl : ∀ z ∈ StInf X u u' γw, ∀ v, z v ∈ Formalism.L2.SG.NGPin.StV X u u' γw v := by
    intro z hz v
    rw [Formalism.L2.SG.NGPin.stInf_eq_pi] at hz
    exact hz v (Set.mem_univ _)
  refine ⟨BX, fun p => BX_measurable p, fun p x x' y y' h => BX_lower p x x' y y' h, fun p x => BX_zero p x,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Formalism.L2.SG.NGPin.stCoord_eq]
    refine Measurable.of_eval fun v => ?_
    obtain ⟨τ, rfl⟩ := hτ v
    exact (stCoordV_meas C u' w γw τ).comp (measurable_pi_apply _)
  · rw [Formalism.L2.SG.NGPin.stInf_eq_pi]
    exact MeasurableSet.univ_pi fun v => (isClosed_stV X u u' γw v).measurableSet
  · intro z₁ h₁ z₂ h₂ heq
    rw [Formalism.L2.SG.NGPin.stCoord_eq] at heq
    funext v
    obtain ⟨τ, rfl⟩ := hτ v
    exact stCoordV_inj C u u' w γw τ hrep (hpl z₁ h₁ _) (hpl z₂ h₂ _) (congrFun heq (vOf X τ))
  · intro x
    have hex : ∀ v, ∃ y ∈ Formalism.L2.SG.NGPin.StV X u u' γw v,
        Formalism.L2.SG.NGPin.stCoordV X u' w γw v y = x v := by
      intro v
      obtain ⟨τ, rfl⟩ := hτ v
      exact stCoordV_surj C u u' w γw τ hrep (x (vOf X τ))
    choose y hy hyx using hex
    refine ⟨y, ?_, ?_⟩
    · rw [Formalism.L2.SG.NGPin.stInf_eq_pi]; exact fun v _ => hy v
    · rw [Formalism.L2.SG.NGPin.stCoord_eq]; funext v; exact hyx v
  · intro z₁ h₁ z₂ h₂
    refine ⟨?_, ?_⟩
    · have hN := Formalism.L2.SG.Pf.psiInfChar_holds D X u
      have hN' := Formalism.L2.SG.Pf.psiInfChar_holds D X u'
      refine ⟨(hN.2.1 _ h₁.1 _ h₂.1).1, ?_⟩
      have e : γw⁻¹ * (z₁ * z₂) * γw = (γw⁻¹ * z₁ * γw) * (γw⁻¹ * z₂ * γw) := by group
      rw [e]
      exact (hN'.2.1 _ h₁.2 _ h₂.2).1
    · rw [Formalism.L2.SG.NGPin.stCoord_eq]
      funext v p
      exact stCoordV_mul X v (hpl z₁ h₁ v) (hpl z₂ h₂ v) p
  · intro r hr
    obtain ⟨hr1, hr2⟩ := hr
    refine ⟨?_, ?_⟩
    · have := Formalism.L2.SG.Pf.FormTranspose.sinf_conj X u (Formalism.L2.SG.Pf.Sinf.sinf_inv' X u hs) hr1
      simpa only [inv_inv] using this
    · have hγ : γw = s⁻¹ * t.pt.1 * s' := by rw [hpt]; group
      have := Formalism.L2.SG.Pf.FormTranspose.sinf_conj X u' (Formalism.L2.SG.Pf.Sinf.sinf_inv' X u' hs') hr2
      rw [hγ]
      convert this using 1
      group

end Formalism.L2.S.Pv.Chart

end
