module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomUBL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLines
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelPlaceBuilt2OfBdd

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeom
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.GeometryEquivarianceEmbedding
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.AdmissibleLieWords
open PI.UnitaryGroupMassFormula.GsFr PI.UnitaryGroupMassFormula.DLm.Gram
open Matrix

noncomputable section

namespace S3

variable {k r : ℕ}

def Fsp (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) :=
  Submodule.span ℂ (Set.range (fvec k r z))

lemma fv_mem (z : Fin (2 * r + k + 1) → ℂ) (b : Fin (r + 1)) : fvec k r z b ∈ Fsp k r z :=
  Submodule.subset_span ⟨b, rfl⟩

lemma X_le (z : Fin (2 * r + k + 1) → ℂ) : Xsp k r ≤ Fsp k r z := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, rfl⟩
  have h := fv_mem z (Fin.castSucc a)
  unfold fvec at h
  rw [dite_eq_left (show ((Fin.castSucc a : Fin (r + 1)) : ℕ) < r from a.isLt)] at h
  exact h

lemma lift_unique' {z z' : Fin (2 * r + k + 1) → ℂ} {y : B.Mat k r} (hd : (Zhat k r z z' y).det ≠ 0)
    {x : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Fsp k r z')
    (horth : ∀ a, herm (Hpk k r) (y *ᵥ x) (fvec k r z a) = 0) : x = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hx
  have hZc : Zhat k r z z' y *ᵥ c = 0 := by
    funext a
    have := horth a
    rw [mv_sum] at this
    simp only [mulVec_smul] at this
    rw [hm_sum_l] at this
    simp only [mulVec, dotProduct, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun b _ => by simp only [Zhat]; ring
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hd hZc
  rw [hc0]
  simp

private lemma mem_xsp_of_apply_eq_zero_of_le {w : Fin (2 * r + k + 1) → ℂ} (h : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → w i = 0) :
    w ∈ Xsp k r := by
  have hw : w = ∑ a : Fin r, w (eI k r a) • bvec (eI k r a) := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply]
    by_cases hi : i.val < r
    · have hsum : ∀ a : Fin r, w (eI k r a) * (if i = eI k r a then 1 else 0) =
          if a = ⟨i.val, hi⟩ then w i else 0 := by
        intro a
        by_cases ha : a = ⟨i.val, hi⟩
        · subst ha
          have : i = eI k r ⟨i.val, hi⟩ := Fin.ext rfl
          rw [if_pos this, if_pos rfl, mul_one, ← this]
        · have hne : i ≠ eI k r a := by
            intro h'
            apply ha
            ext
            have := congrArg Fin.val h'
            simp only [eI] at this
            simp only [Fin.val_mk]
            omega
          rw [if_neg hne, if_neg ha, mul_zero]
      rw [Finset.sum_congr rfl (fun a _ => hsum a), Finset.sum_ite_eq']
      simp
    · rw [h i (by omega)]
      symm
      apply Finset.sum_eq_zero
      intro a _
      have hne : i ≠ eI k r a := by
        intro h'
        have := congrArg Fin.val h'
        simp only [eI] at this
        omega
      rw [if_neg hne, mul_zero]
  rw [hw]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

lemma N_wb_X {n : B.Mat k r} (hn : n ∈ Nset k r) {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) :
    n *ᵥ v - v ∈ Xsp k r := by
  apply mem_xsp_of_apply_eq_zero_of_le
  intro i hi
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
  rw [sub_eq_zero]
  have key : ∀ j, n i j * v j = if j = i then v i else 0 := by
    intro j
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hv j hj, mul_zero]
      split_ifs with h
      · subst h
        exact (hv _ hj).symm
      · rfl
    · rw [hn.2.2 i j (by omega) (by omega) hi]
      by_cases h : j = i
      · subst h
        simp
      · simp [h, Ne.symm h]
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  simp

lemma sset_N {z : Fin (2 * r + k + 1) → ℂ} {n : B.Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z := by
  refine ⟨1, ?_, n, hn, (one_mul n).symm⟩
  unfold UWset
  simp [UH]

lemma N_Fsp {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {n : B.Mat k r} (hn : n ∈ Nset k r)
    {x : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Fsp k r z) : n *ᵥ x ∈ Fsp k r z := by
  have hcol : ∀ b, n *ᵥ fvec k r z b ∈ Fsp k r z := by
    intro b
    have hsplit : n *ᵥ fvec k r z b = fvec k r z b + (n *ᵥ fvec k r z b - fvec k r z b) := by abel
    rw [hsplit]
    refine Submodule.add_mem _ (fv_mem z b) (X_le z ?_)
    unfold fvec
    split_ifs with hb
    · apply mem_xsp_of_apply_eq_zero_of_le
      intro i hi
      rw [Pi.sub_apply, bvec, Matrix.mulVec_single_one]
      show n i (eI k r ⟨b.val, hb⟩) - (Pi.single (eI k r ⟨b.val, hb⟩) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) i = 0
      rw [hn.2.1 ⟨b.val, hb⟩ i (by simp only; omega), Pi.single_apply, sub_self]
    · exact N_wb_X hn hz.1
  refine Submodule.span_induction (p := fun x _ => n *ᵥ x ∈ Fsp k r z) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨b, rfl⟩
    exact hcol b
  · simp [Submodule.zero_mem]
  · intro x y _ _ hx hy
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ c hx

lemma UW_Fsp {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z)
    {x : Fin (2 * r + k + 1) → ℂ} (hx : x ∈ Fsp k r z) : h *ᵥ x = x := by
  have hfv : ∀ b, h *ᵥ fvec k r z b = fvec k r z b := by
    intro b
    unfold fvec
    split_ifs with hb
    · exact (hh.2.1 ⟨b, hb⟩).1
    · first
      | exact hh.2.2
      | exact hh.2.2.1
  refine Submodule.span_induction (p := fun x _ => h *ᵥ x = x) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨b, rfl⟩
    exact hfv b
  · simp
  · intro x y _ _ hx hy
    rw [Matrix.mulVec_add, hx, hy]
  · intro c x _ hx
    rw [Matrix.mulVec_smul, hx]

lemma N_orth {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {n : B.Mat k r} (hn : n ∈ Nset k r)
    {p : Fin (2 * r + k + 1) → ℂ} (hp : ∀ b, herm (Hpk k r) p (fvec k r z b) = 0) (a : Fin (r + 1)) :
    herm (Hpk k r) (n *ᵥ p) (fvec k r z a) = 0 := by
  have hdet : IsUnit n.det := by
    by_contra hnd
    have h0 : n⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit n hnd
    have hm := (Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hn).1
    rw [h0] at hm
    have hm' : (0 : B.Mat k r)ᴴ * Hpk k r * 0 = Hpk k r := hm
    rw [Matrix.mul_zero] at hm'
    have := congrFun (congrFun hm' ⟨r + k, by omega⟩) ⟨r + k, by omega⟩
    simp [Hpk] at this
  have hinv : n * n⁻¹ = 1 := Matrix.mul_nonsing_inv n hdet
  have hU : ∀ x y, herm (Hpk k r) (n *ᵥ x) (n *ᵥ y) = herm (Hpk k r) x y := by
    intro x y
    have hh' : nᴴ * Hpk k r * n = Hpk k r := hn.1
    show star (n *ᵥ y) ⬝ᵥ (Hpk k r *ᵥ (n *ᵥ x)) = star y ⬝ᵥ (Hpk k r *ᵥ x)
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh']
  have horthF : ∀ g ∈ Fsp k r z, herm (Hpk k r) p g = 0 := by
    intro g hg
    refine Submodule.span_induction (p := fun g _ => herm (Hpk k r) p g = 0) ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨b, rfl⟩
      exact hp b
    · show star (0 : Fin (2 * r + k + 1) → ℂ) ⬝ᵥ (Hpk k r *ᵥ p) = 0
      simp
    · intro x y _ _ hx hy
      have hx' : star x ⬝ᵥ (Hpk k r *ᵥ p) = 0 := hx
      have hy' : star y ⬝ᵥ (Hpk k r *ᵥ p) = 0 := hy
      show star (x + y) ⬝ᵥ (Hpk k r *ᵥ p) = 0
      rw [star_add, add_dotProduct, hx', hy', add_zero]
    · intro c x _ hx
      have hx' : star x ⬝ᵥ (Hpk k r *ᵥ p) = 0 := hx
      show star (c • x) ⬝ᵥ (Hpk k r *ᵥ p) = 0
      rw [star_smul, smul_dotProduct, hx', smul_zero]
  have hf : n⁻¹ *ᵥ fvec k r z a ∈ Fsp k r z := N_Fsp hz (Formalism.QuantumDeterminants.WeylGroupFacts.mem_n_inv hn) (fv_mem z a)
  calc herm (Hpk k r) (n *ᵥ p) (fvec k r z a)
      = herm (Hpk k r) (n *ᵥ p) (n *ᵥ (n⁻¹ *ᵥ fvec k r z a)) := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    _ = herm (Hpk k r) p (n⁻¹ *ᵥ fvec k r z a) := hU _ _
    _ = 0 := horthF _ hf

private theorem herm_hpk_mulVec_of_mem_uh {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ w) = Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v w := by
  have hh' : hᴴ * Formalism.QuantumDeterminants.Hpk k r * h = Formalism.QuantumDeterminants.Hpk k r := hh
  show star (h *ᵥ w) ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ (h *ᵥ v)) = star w ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ v)
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh']

lemma UW_orth {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z)
    {p : Fin (2 * r + k + 1) → ℂ} (hp : ∀ b, herm (Hpk k r) p (fvec k r z b) = 0) (a : Fin (r + 1)) :
    herm (Hpk k r) (h *ᵥ p) (fvec k r z a) = 0 := by
  rw [← UW_Fsp hh (fv_mem z a), herm_hpk_mulVec_of_mem_uh hh.1]
  exact hp a

lemma prW_NUW {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {n h : B.Mat k r} (hn : n ∈ Nset k r)
    (hh : h ∈ UWset k r z) {q : Fin (2 * r + k + 1) → ℂ} (hq : ∀ b, herm (Hpk k r) q (fvec k r z b) = 0) :
    PI.UnitaryGroupMassFormula.GsFr.prW k r z (n *ᵥ (h *ᵥ q)) = h *ᵥ PI.UnitaryGroupMassFormula.GsFr.prW k r z q := by
  have hX : ∀ a : Fin r, (h *ᵥ q) (esI k r a) = 0 := fun a => by
    rw [← herm_bvec_eI (h *ᵥ q) a, ← fvec_lt z a]; exact UW_orth hh hq _
  rw [prW_N hn hX, prW_UW hz hh]

lemma omW'_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) {y : B.Mat k r} (hy : y ∈ B.GV k r) :
    omW' k r z z' (n * y * n') = omW' k r z z' y := by
  have Nc := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  unfold omW'
  rw [xcofL_N hz hz' hn hn' y, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← mulVec_mulVec, ← mulVec_mulVec,
    show n⁻¹ *ᵥ (n *ᵥ xcofL k r z z' y) = xcofL k r z z' y by
      rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ (Nc.unit n hn), one_mulVec],
    prW_N (Nc.inv_mem n' hn') (ginv_xcofL_esI z z' hy)]

lemma unitH_UH {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (v : Fin (2 * r + k + 1) → ℂ) :
    unitH k r (h *ᵥ v) = h *ᵥ unitH k r v := by
  show ((((Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ v)).re)⁻¹ : ℝ) : ℂ) • (h *ᵥ v)) =
    h *ᵥ ((((Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re)⁻¹ : ℝ) : ℂ) • v)
  rw [herm_hpk_mulVec_of_mem_uh hh, Matrix.mulVec_smul]

private theorem rk_mulVec_eq_herm_smul (p q v : Fin (2 * r + k + 1) → ℂ) :
    Rk k r p q *ᵥ v = Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v q • p := by
  have e1 : Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v q = (star q ᵥ* Formalism.QuantumDeterminants.Hpk k r) ⬝ᵥ v := by
    show star q ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ v) = _
    exact Matrix.dotProduct_mulVec _ _ _
  rw [e1]
  ext i
  simp only [Rk, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem dw_mulVec_eq_wbPart (v : Fin (2 * r + k + 1) → ℂ) : Dw k r *ᵥ v = PI.UnitaryGroupMassFormula.GsFr.wbPart k r v := by
  ext i
  simp only [Dw, Matrix.mulVec_diagonal, PI.UnitaryGroupMassFormula.GsFr.wbPart]
  split_ifs <;> simp

lemma PpG_mulVec (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ) :
    PpG z z' g *ᵥ v = PI.UnitaryGroupMassFormula.GsFr.prW k r z' v -
      herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' v) (nuG' z z' g) • nuG' z z' g := by
  show (Pm k r z' - Rk k r (nuG' z z' g) (nuG' z z' g) * Pm k r z') *ᵥ v = _
  have hPm : Pm k r z' *ᵥ v = PI.UnitaryGroupMassFormula.GsFr.prW k r z' v := by
    show (Dw k r + ((Tz k r z' : ℂ))⁻¹ • (Rk k r z' z' * Dw k r)) *ᵥ v = _
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, rk_mulVec_eq_herm_smul, dw_mulVec_eq_wbPart]
    show _ = PI.UnitaryGroupMassFormula.GsFr.wbPart k r v +
      (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.wbPart k r v) z' / (Tz k r z' : ℂ)) • z'
    rw [smul_smul, div_eq_inv_mul]
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, rk_mulVec_eq_herm_smul, hPm]

lemma ioG_mulVec (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ) :
    ioG z z' g *ᵥ v = Phi k r z z' g *ᵥ (PpG z z' g *ᵥ v) := by
  show (PI.UnitaryGroupMassFormula.GsFr.Phi k r z z' g * PpG z z' g) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec]

lemma lift_eq {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z')
    {n h n' h' g y : B.Mat k r} (hn : n ∈ Nset k r) (hh : h ∈ UWset k r z) (hn' : n' ∈ Nset k r)
    (hh' : h' ∈ UWset k r z') (hd : (Zhat k r z z' g).det ≠ 0) (hdy : (Zhat k r z z' y).det ≠ 0)
    (he : g * (n' * h') = n * h * y) {w : Fin (2 * r + k + 1) → ℂ} (hw : inWb k r w) :
    Lm k r z z' g *ᵥ (h' *ᵥ w) = n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w)) := by
  have hsum : ∀ (M : B.Mat k r) (u : Fin (2 * r + k + 1) → ℂ), Lm k r z z' M *ᵥ u - u ∈ Fsp k r z' := by
    intro M u
    rw [Lm_mulVec, add_sub_cancel_left]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (fv_mem z' c)
  have e1 := hsum g (h' *ᵥ w)
  have e2 : n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w)) - h' *ᵥ w ∈ Fsp k r z' := by
    have e3 : n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w)) - h' *ᵥ w =
        n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w - w)) + (n' *ᵥ (h' *ᵥ w) - h' *ᵥ w) := by
      rw [mulVec_sub, mulVec_sub]; abel
    rw [e3]
    refine Submodule.add_mem _ ?_ (X_le z' (N_wb_X hn' (uw_inWb hz'.1 hh' hw)))
    rw [UW_Fsp hh' (hsum y w)]
    exact N_Fsp hz' hn' (hsum y w)
  have hD : Lm k r z z' g *ᵥ (h' *ᵥ w) - n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w)) ∈ Fsp k r z' := by
    have : Lm k r z z' g *ᵥ (h' *ᵥ w) - n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w)) =
        (Lm k r z z' g *ᵥ (h' *ᵥ w) - h' *ᵥ w) - (n' *ᵥ (h' *ᵥ (Lm k r z z' y *ᵥ w)) - h' *ᵥ w) := by abel
    rw [this]; exact Submodule.sub_mem _ e1 e2
  have hg2 : ∀ x : Fin (2 * r + k + 1) → ℂ, g *ᵥ (n' *ᵥ (h' *ᵥ x)) = n *ᵥ (h *ᵥ (y *ᵥ x)) := by
    intro x
    rw [mulVec_mulVec _ n' h', mulVec_mulVec, he, ← mulVec_mulVec, ← mulVec_mulVec]
  refine sub_eq_zero.1 (lift_unique' hd hD fun a => ?_)
  rw [mulVec_sub, hm_sub_l, lift_orth hd, hg2, N_orth hz hn (UW_orth hh (lift_orth hdy w)) a, sub_zero]

lemma det_tilde {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z')
    {n h n' h' g : B.Mat k r} (hn : n ∈ Nset k r) (hh : h ∈ UWset k r z) (hn' : n' ∈ Nset k r)
    (hh' : h' ∈ UWset k r z') (hd : (Zhat k r z z' g).det ≠ 0) :
    (Zhat k r z z' (h⁻¹ * (n⁻¹ * g * n') * h')).det ≠ 0 := by
  have Nc := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have hF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz
  have hF' := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z' hz'
  rw [zhat_UW (Wz.inv_mem h hh) hh', zhat_N hz hz' (Nc.inv_mem n hn) hn' g,
    Matrix.nonsing_inv_nonsing_inv n (Nc.unit n hn), Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    unitri_det (hF.1 n (sset_N hn)).2.1, unitri_det (hF'.1 n' (sset_N hn')).2.1]
  simpa using hd

end S3

open S3 in
theorem geometry_equivariance_embedding : GeomEqvIo := by
  intro k r z z' hk hz hz' h hh n hn h' hh' n' hn' g hg
  have Nc := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have Wz := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z
  have Wz' := Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z'
  set y := h⁻¹ * n⁻¹ * g * n' * h' with hy_def
  have hyA : y = h⁻¹ * (n⁻¹ * g * n') * h' := by simp only [hy_def, Matrix.mul_assoc]
  have hgy : g * (n' * h') = n * h * y := by
    rw [hy_def]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc h h⁻¹, Matrix.mul_nonsing_inv _ (Wz.unit h hh), Matrix.one_mul,
      ← Matrix.mul_assoc n n⁻¹, Matrix.mul_nonsing_inv _ (Nc.unit n hn), Matrix.one_mul]
  have hd : (Zhat k r z z' g).det ≠ 0 := det_ne_of_G hz hz' hg.2
  have hdy : (Zhat k r z z' y).det ≠ 0 := by rw [hyA]; exact det_tilde hz hz' hn hh hn' hh' hd
  have hom : omW' k r z z' g = h' *ᵥ omW' k r z z' y := by
    rw [hyA, omW'_UW hz hz' (Wz.inv_mem h hh) hh', omW'_N hz hz' (Nc.inv_mem n hn) hn' hg.1, mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (Wz'.unit h' hh'), one_mulVec]
  have hν' : nuG' z z' g = h' *ᵥ nuG' z z' y := by
    unfold nuG'; rw [hom, unitH_UH hh'.1]
  have hP : ∀ v, PpG z z' g *ᵥ (h' *ᵥ v) = h' *ᵥ (PpG z z' y *ᵥ v) := by
    intro v
    rw [PpG_mulVec, PpG_mulVec, hν', prW_UW hz' hh', Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hh'.1, mulVec_sub, mulVec_smul]
  have hPw : ∀ v, inWb k r (PpG z z' y *ᵥ v) := by
    intro v i hi
    have h1 := (prW_mem hz' v).1 i hi
    have h2 : omW' k r z z' y i = 0 := (prW_mem hz' _).1 i hi
    simp only [PpG_mulVec, nuG', unitH, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, h2, mul_zero, sub_zero]
  have hPhi : ∀ w, inWb k r w → Phi k r z z' g *ᵥ (h' *ᵥ w) = h *ᵥ (Phi k r z z' y *ᵥ w) := by
    intro w hw
    rw [Phi_mulVec, Phi_mulVec, lift_eq hz hz' hn hh hn' hh' hd hdy hgy hw, mulVec_mulVec _ n' h', mulVec_mulVec,
      hgy, ← mulVec_mulVec, ← mulVec_mulVec, prW_NUW hz hn hh (lift_orth hdy w)]
  have key : ∀ v, ioG z z' g *ᵥ (h' *ᵥ v) = h *ᵥ (ioG z z' y *ᵥ v) := by
    intro v; rw [ioG_mulVec, ioG_mulVec, hP, hPhi _ (hPw v)]
  have hm : ioG z z' g * h' = h * ioG z z' y := by
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    rw [mulVec_mulVec, mulVec_mulVec] at this
    simpa [Matrix.mulVec_single_one] using this
  calc ioG z z' g = ioG z z' g * h' * h'⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Wz'.unit h' hh'), Matrix.mul_one]
    _ = h * ioG z z' y * h'⁻¹ := by rw [hm]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.EmbeddingMulVecFactorization
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.AdmissibleLieWords
open PI.UnitaryGroupMassFormula.GsFr PI.UnitaryGroupMassFormula.DLm.Gram
open Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace S5

variable {k r : ℕ}

lemma W_bound {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Fin (2 * r + k + 1) → ℂ, inWb k r v → herm (Hpk k r) v z = 0 →
      ‖v‖ ^ 2 ≤ C * (herm (Hpk k r) v v).re := by
  have hc1 : Continuous fun v : Fin (2 * r + k + 1) → ℂ => herm (Hpk k r) v z := by
    unfold herm; fun_prop
  have hc2 : Continuous fun v : Fin (2 * r + k + 1) → ℂ => (herm (Hpk k r) v v).re := by
    unfold herm; fun_prop
  have hWb : IsClosed {v : Fin (2 * r + k + 1) → ℂ | inWb k r v} := by
    simp only [inWb, Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_eq (continuous_apply i) continuous_const
  set K : Set (Fin (2 * r + k + 1) → ℂ) :=
    Metric.sphere 0 1 ∩ ({v | inWb k r v} ∩ {v | herm (Hpk k r) v z = 0}) with hK
  have hKc : IsCompact K := (isCompact_sphere 0 1).inter_right (hWb.inter (isClosed_eq hc1 continuous_const))
  have hpos : ∀ v ∈ K, 0 < (herm (Hpk k r) v v).re := by
    rintro v ⟨hv1, hv2, hv3⟩
    refine posV hz hv2 hv3 ?_
    rintro rfl
    simp at hv1
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (f := fun v => ((herm (Hpk k r) v v).re)⁻¹)
    (hc2.continuousOn.inv₀ fun v hv => (hpos v hv).ne')
  refine ⟨max C 0, le_max_right _ _, fun v hv hvz => ?_⟩
  by_cases h0 : v = 0
  · subst h0; simp [herm]
  have hn : 0 < ‖v‖ := norm_pos_iff.2 h0
  set c : ℂ := ((‖v‖⁻¹ : ℝ) : ℂ) with hc
  have hwK : c • v ∈ K := by
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, hc, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hn), inv_mul_cancel₀ hn.ne']
    · intro i hi; simp [hv i hi]
    · show herm (Hpk k r) (c • v) z = 0
      rw [hm_smul_l, hvz, mul_zero]
  have hf : (herm (Hpk k r) (c • v) (c • v)).re = ‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re := by
    rw [hm_smul_l, hm_smul_r, hc, Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
      Complex.re_ofReal_mul]
    ring
  have hb := hC (c • v) hwK
  have hp := hpos _ hwK
  rw [hf] at hp hb
  have ht : 0 < (herm (Hpk k r) v v).re := by
    have : 0 < ‖v‖⁻¹ ^ 2 := by positivity
    exact pos_of_mul_pos_right hp this.le
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp)] at hb
  have hb2 : 1 ≤ C * (‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re) := by
    rw [inv_le_iff_one_le_mul₀ hp] at hb; linarith
  have e : ‖v‖ ^ 2 * (‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re) = (herm (Hpk k r) v v).re := by
    field_simp
  calc ‖v‖ ^ 2 = ‖v‖ ^ 2 * 1 := by ring
    _ ≤ ‖v‖ ^ 2 * (C * (‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re)) :=
        mul_le_mul_of_nonneg_left hb2 (by positivity)
    _ = C * (‖v‖ ^ 2 * (‖v‖⁻¹ ^ 2 * (herm (Hpk k r) v v).re)) := by ring
    _ = C * (herm (Hpk k r) v v).re := by rw [e]
    _ ≤ max C 0 * (herm (Hpk k r) v v).re := mul_le_mul_of_nonneg_right (le_max_left _ _) ht.le

private theorem herm_Hpk_smul_left (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (c • x) y = c * Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) x y := by
  show star y ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ (c • x)) = c * (star y ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ x))
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem herm_Hpk_smul_right_eq_star_mul (c : ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) x (c • y) = star c * Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) x y := by
  show star (c • y) ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ x) = star c * (star y ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ x))
  rw [star_smul, smul_dotProduct, smul_eq_mul]

lemma unitH_facts {z v : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hv : v ∈ Wsp k r z) :
    unitH k r v ∈ Wsp k r z ∧ (herm (Hpk k r) (unitH k r v) (unitH k r v)).re ≤ 1 := by
  obtain ⟨hw, ho⟩ := hv
  set s : ℝ := (Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re)⁻¹ with hs
  have hU : unitH k r v = (s : ℂ) • v := rfl
  rw [hU]
  refine ⟨⟨fun i hi => by rw [Pi.smul_apply, hw i hi, smul_zero], ?_⟩, ?_⟩
  · show Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) ((s : ℂ) • v) z = 0
    rw [herm_Hpk_smul_left, ho, mul_zero]
  · show (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) ((s : ℂ) • v) ((s : ℂ) • v)).re ≤ 1
    rw [herm_Hpk_smul_left, herm_Hpk_smul_right_eq_star_mul, Complex.star_def, Complex.conj_ofReal, ← mul_assoc,
      ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    by_cases hpos : 0 < (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re
    · exact le_of_eq (by rw [hs, ← mul_inv, Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ hpos.ne'])
    · rw [hs, Real.sqrt_eq_zero'.2 (not_lt.1 hpos)]
      simp

lemma lift_X' {z z' : Fin (2 * r + k + 1) → ℂ} {y : B.Mat k r} (hy : y ∈ B.GV k r)
    {u : Fin (2 * r + k + 1) → ℂ} (huW : u ∈ Wsp k r z') (huo : herm (Hpk k r) u (omW' k r z z' y) = 0) :
    Lm k r z z' y *ᵥ u - u ∈ Xsp k r := by
  have e : ∑ a, (Zhat k r z z' y).adjugate (Fin.last r) a * herm (Hpk k r) (y *ᵥ u) (fvec k r z a) = 0 := by
    have h1 : ∑ a, (Zhat k r z z' y).adjugate (Fin.last r) a * herm (Hpk k r) (y *ᵥ u) (fvec k r z a) =
        herm (Hpk k r) (y *ᵥ u) (xcofL k r z z' y) := by
      unfold xcofL; rw [hm_sum_r]; simp only [star_star]
    rw [h1, ← ginv_cancel hy (xcofL k r z z' y), Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy, ← herm_prW_r huW]
    exact huo
  have hlast : gam k r z z' y u (Fin.last r) = 0 := by
    simp only [gam, wv, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct]
    rw [e, mul_zero]
  have hS : Lm k r z z' y *ᵥ u - u = ∑ c, gam k r z z' y u c • fvec k r z' c := by rw [Lm_mulVec]; abel
  rw [hS]
  refine Submodule.sum_mem _ fun c _ => ?_
  by_cases hc : c = Fin.last r
  · rw [hc, hlast, zero_smul]; exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (fv_X z' c hc)

lemma phi_iso' {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {y : B.Mat k r} (hy : y ∈ B.GV k r)
    (hd : (Zhat k r z z' y).det ≠ 0) {u : Fin (2 * r + k + 1) → ℂ} (huW : u ∈ Wsp k r z')
    (huo : herm (Hpk k r) u (omW' k r z z' y) = 0) :
    herm (Hpk k r) (Phi k r z z' y *ᵥ u) (Phi k r z z' y *ᵥ u) = herm (Hpk k r) u u := by
  rw [Phi_mulVec]
  have hx := sub_prW_X hz (lift_orth hd u)
  have hP := prW_mem hz (y *ᵥ (Lm k r z z' y *ᵥ u))
  have hL := lift_X' hy huW huo
  rw [← herm_add_X hP.1 hP.1 hx hx, aps, Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_UH hy, ← herm_add_X huW.1 huW.1 hL hL, aps]

lemma Pp_facts {z z' : Fin (2 * r + k + 1) → ℂ} (hz' : C2.StdZ k r z') (g : B.Mat k r)
    (v : Fin (2 * r + k + 1) → ℂ) :
    PpG z z' g *ᵥ v ∈ Wsp k r z' ∧ herm (Hpk k r) (PpG z z' g *ᵥ v) (omW' k r z z' g) = 0 ∧
      (herm (Hpk k r) (PpG z z' g *ᵥ v) (PpG z z' g *ᵥ v)).re ≤
        (herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' v) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' v)).re := by
  have hH : (Hpk k r)ᴴ = Hpk k r := (Formalism.QuantumDeterminants.hpkFacts k r).1
  have hPe : PpG z z' g *ᵥ v = PI.UnitaryGroupMassFormula.GsFr.prW k r z' v -
      herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' v) (nuG' z z' g) • nuG' z z' g := by
    unfold PpG
    rw [sub_mulVec, ← mulVec_mulVec, Pm_mulVec, Rk_mulVec]
  set p := PI.UnitaryGroupMassFormula.GsFr.prW k r z' v with hp
  set om := omW' k r z z' g with hom
  have hpW : p ∈ Wsp k r z' := prW_mem hz' v
  have homW : om ∈ Wsp k r z' := prW_mem hz' _
  have hνW : nuG' z z' g ∈ Wsp k r z' := Wsp_smul _ homW
  rw [hPe]
  refine ⟨Wsp_sub hpW (Wsp_smul _ hνW), ?_⟩
  by_cases h0 : om = 0
  · have hν0 : nuG' z z' g = 0 := by
      show unitH k r om = 0
      rw [h0]; simp [unitH]
    rw [hν0, h0]
    simp [herm]
  have ht := posV hz' homW.1 homW.2 h0
  have hνν : herm (Hpk k r) (nuG' z z' g) (nuG' z z' g) = 1 := nz_unit ht
  set c := herm (Hpk k r) p (nuG' z z' g) with hcdef
  set u := p - c • nuG' z z' g with hu
  have huν : herm (Hpk k r) u (nuG' z z' g) = 0 := by
    rw [hu, hm_sub_l, hm_smul_l, hνν, mul_one, sub_self]
  have hνu : herm (Hpk k r) (nuG' z z' g) u = 0 := by
    rw [hm_symm _ hH, huν, star_zero]
  refine ⟨(nz_orth ht u).1 huν, ?_⟩
  have hpu : p = u + c • nuG' z z' g := by rw [hu, sub_add_cancel]
  have e : herm (Hpk k r) p p = herm (Hpk k r) u u + c * star c := by
    conv_lhs => rw [hpu]
    rw [hm_add_l, hm_add_r, hm_add_r, hm_smul_l, hm_smul_l, hm_smul_r, hm_smul_r, huν, hνu, hνν]
    ring
  rw [e, Complex.add_re]
  have : 0 ≤ (c * star c).re := by
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]; exact Complex.normSq_nonneg _
  linarith

lemma embedding_mul_vec_factorization (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (v : Fin (2 * r + k + 1) → ℂ) :
    ioG z z' g *ᵥ v = Phi k r z z' g *ᵥ (PpG z z' g *ᵥ v) := by
  show (PI.UnitaryGroupMassFormula.GsFr.Phi k r z z' g * PpG z z' g) *ᵥ v = _
  rw [← Matrix.mulVec_mulVec]

lemma sq_bound {x C : ℝ} (hx : 0 ≤ x) (hC : 0 ≤ C) (h : x ^ 2 ≤ C) : x ≤ C + 1 := by
  nlinarith [sq_nonneg (x - 1)]

end S5

open S5 in
theorem geometry_boundedness_at_zero : GeomBd0 := by
  intro k r z z' hk hz hz'
  obtain ⟨C1, hC1, hW⟩ := W_bound hz
  obtain ⟨C2, hC2, hW'⟩ := W_bound hz'
  set M := ∑ j : Fin (2 * r + k + 1),
    |(herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1)) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))).re|
    with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hν : ∀ g, ‖nuG z z' g‖ ≤ C1 + 1 := by
    intro g
    have hu := unitH_facts hz (prW_mem hz (xcof k r z z' g))
    have h1 := hW _ hu.1.1 hu.1.2
    refine sq_bound (norm_nonneg _) hC1 (h1.trans ?_)
    have := mul_le_mul_of_nonneg_left hu.2 hC1
    simpa [nuG, omW] using this
  have hν' : ∀ g, ‖nuG' z z' g‖ ≤ C2 + 1 := by
    intro g
    have hu := unitH_facts hz' (prW_mem hz' (g⁻¹ *ᵥ xcofL k r z z' g))
    have h1 := hW' _ hu.1.1 hu.1.2
    refine sq_bound (norm_nonneg _) hC2 (h1.trans ?_)
    have := mul_le_mul_of_nonneg_left hu.2 hC2
    simpa [nuG', omW'] using this
  refine ⟨(C1 + 1) + (C2 + 1) + (C1 * M + 1), fun g hg => ⟨?_, ?_, ?_⟩⟩
  · have := hν g; have := mul_nonneg hC1 hM0; linarith
  · have := hν' g; have := mul_nonneg hC1 hM0; linarith
  · have hCM := mul_nonneg hC1 hM0
    have hC : 0 ≤ (C1 + 1) + (C2 + 1) + (C1 * M + 1) := by linarith
    rw [Matrix.norm_le_iff hC]
    intro i j
    have hd := det_ne_of_G hz hz' hg.2
    obtain ⟨huW, huo, hle⟩ := Pp_facts (z := z) hz' g (Pi.single j 1)
    have hiso := phi_iso' hz hg.1 hd huW huo
    set q := Phi k r z z' g *ᵥ (PpG z z' g *ᵥ Pi.single j 1) with hq
    have hqW : q ∈ Wsp k r z := by rw [hq, Phi_mulVec]; exact prW_mem hz _
    have h1 := hW q hqW.1 hqW.2
    rw [hiso] at h1
    have hpM : (herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))
        (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))).re ≤ M :=
      (le_abs_self _).trans (Finset.single_le_sum (f := fun j : Fin (2 * r + k + 1) =>
        |(herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))
          (PI.UnitaryGroupMassFormula.GsFr.prW k r z' (Pi.single j 1))).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))
    have h2 : ‖q‖ ^ 2 ≤ C1 * M := h1.trans (mul_le_mul_of_nonneg_left (hle.trans hpM) hC1)
    have h3 := sq_bound (norm_nonneg q) hCM h2
    have e : ioG z z' g i j = q i := by
      rw [hq, ← embedding_mul_vec_factorization]
      simp
    rw [e]
    have := norm_le_pi_norm q i
    have := hν g
    have := hν' g
    linarith

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeomAssemble
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords
open scoped ComplexConjugate Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bd_of_ubl {k r : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (z z' : Fin (2 * r + k + 1) → ℂ) (φ : B.Mat k r → F) (e γ : ℕ) (Bg : ℝ)
    (hBg : (e : ℝ) + γ ≤ Bg) (ε : ℝ)
    (h0 : ∃ C0 : ℝ, ∀ g ∈ geG k r z z' ε, ‖φ g‖ ≤ C0) (hU : ∀ n : ℕ, UBL φ (geG k r z z' ε) n e γ) (m : ℕ) :
    ∃ C : ℝ, ∀ u w : List (B.Mat k r),
      (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) → u.length + w.length ≤ m →
      ∀ g ∈ B.GV k r, ε ≤ Gf k r z z' g → ‖B.dLR u w φ g‖ ≤ C * B.gN g ^ (Bg * m) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    obtain ⟨C0, hC0⟩ := h0
    refine ⟨C0, fun u w _ _ hl g hg hgε => ?_⟩
    have hu : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu hw
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    exact hC0 g ⟨hg, hgε⟩
  · obtain ⟨⟨C, hC0, hUB⟩, -⟩ := hU m
    refine ⟨C, fun u w hu hw hl g hg hgε => ?_⟩
    have hA : admitted m (wL u ++ wR w) := ⟨u, w, hu, hw, hl, rfl⟩
    have hb := hUB _ hA g ⟨hg, hgε⟩
    rw [dLR_eq]
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    have h1 : 1 ≤ B.gN g := gN_ge_one hg
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le h1
    rw [len_LR]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hl' : ((u.length + w.length : ℕ) : ℝ) ≤ m := by exact_mod_cast hl
    have he : (0 : ℝ) ≤ e := Nat.cast_nonneg _
    have hγ : (0 : ℝ) ≤ γ := Nat.cast_nonneg _
    push_cast at hl' ⊢
    nlinarith [mul_le_mul_of_nonneg_left hl' hγ, mul_le_mul_of_nonneg_left hm1 he,
      mul_le_mul_of_nonneg_right hBg (by linarith : (0 : ℝ) ≤ m)]

theorem geometry_assembly_holds : GeomAssemble := by
  intro hS hEn hEi hAt hB0 hU
  refine ⟨6, by norm_num, ?_⟩
  intro Cc Cb hCc hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  set Bs := (T v).base with hBs
  have hk : 1 ≤ S.G.k := Bs.k_pos
  have hz : C2.StdZ S.G.k S.G.r Bs.z := ⟨Bs.z_mem, Bs.T_pos⟩
  have hz' : C2.StdZ S.G.k S.G.r Bs.z' := ⟨Bs.z'_mem, Bs.T'_pos⟩
  refine ⟨nuG Bs.z Bs.z', nuG' Bs.z Bs.z', ioG Bs.z Bs.z', ?_⟩
  obtain ⟨s1, s2, s3⟩ := hS _ _ _ _ hk hz hz'
  obtain ⟨C0, hC0⟩ := hB0 _ _ _ _ hk hz hz'
  have hr0 : (0 : ℝ) ≤ S.G.r := Nat.cast_nonneg _
  have hBg : ∀ e γ : ℕ, e ≤ 4 * (S.G.r + 1) → γ ≤ 2 * (S.G.r + 1) → (e : ℝ) + γ ≤ Cb * ((S.G.r : ℝ) + 1) := by
    intro e γ he hγ
    have he' : (e : ℝ) ≤ 4 * ((S.G.r : ℝ) + 1) := by exact_mod_cast he
    have hγ' : (γ : ℝ) ≤ 2 * ((S.G.r : ℝ) + 1) := by exact_mod_cast hγ
    nlinarith
  have hpos : ∀ ε : ℝ, 0 < ε → ∀ g ∈ geG S.G.k S.G.r Bs.z Bs.z' ε, g ∈ posG S.G.k S.G.r Bs.z Bs.z' :=
    fun ε hε g hg => ⟨hg.1, lt_of_lt_of_le hε hg.2⟩
  refine ⟨s1, s2, s3, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp g hg
    obtain ⟨h1, h2⟩ := hEn _ _ _ _ hk hz hz' _ hp.1 _ hp.2.1 _ hp.2.2.1 _ hp.2.2.2 g hg
    exact ⟨h1, h2, hEi _ _ _ _ hk hz hz' _ hp.1 _ hp.2.1 _ hp.2.2.1 _ hp.2.2.2 g hg⟩
  · intro ε hε m
    obtain ⟨⟨e, γ, he, hγ, hu⟩, -, -⟩ := hU _ _ _ _ hk hz hz' ε hε
    exact bd_of_ubl Bs.z Bs.z' _ e γ _ (hBg e γ he hγ) ε ⟨C0, fun g hg => (hC0 g (hpos ε hε g hg)).1⟩ hu m
  · intro ε hε m
    obtain ⟨-, ⟨e, γ, he, hγ, hu⟩, -⟩ := hU _ _ _ _ hk hz hz' ε hε
    exact bd_of_ubl Bs.z Bs.z' _ e γ _ (hBg e γ he hγ) ε ⟨C0, fun g hg => (hC0 g (hpos ε hε g hg)).2.1⟩ hu m
  · intro ε hε m
    obtain ⟨-, -, ⟨e, γ, he, hγ, hu⟩⟩ := hU _ _ _ _ hk hz hz' ε hε
    exact bd_of_ubl Bs.z Bs.z' _ e γ _ (hBg e γ he hγ) ε ⟨C0, fun g hg => (hC0 g (hpos ε hε g hg)).2.2⟩ hu m
  · intro q hq
    have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r Bs.z * Tz S.G.k S.G.r Bs.z' := by
      show (D.parOf S v).T * (D.parOf S v).T' = _
      rw [hPl.2.2.2.1, hPl.2.2.2.2.1]
    have hq2 : Tz S.G.k S.G.r Bs.z * Tz S.G.k S.G.r Bs.z' < Complex.normSq q.2 := hTT ▸ hq.2
    exact hAt _ _ _ _ Bs.μsec hk hz hz' Bs.sec q.1 q.2 hq.1 hq2

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothHermitianRankTwo
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.QuantumDeterminants PI.UnitaryGroupMassFormula.GsFr
open scoped Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace S1

variable {k r : ℕ}

lemma smooth_hermitian_rank_two {s : Set (B.Mat k r)} {p q : B.Mat k r → Fin (2 * r + k + 1) → ℂ}
    (hp : Sm p s) (hq : Sm q s) : Sm (fun x => Rk k r (p x) (q x)) s := by
  unfold Sm Rk at *
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  simp only [Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Pi.star_apply]
  have hs : ∀ l, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => star (q x l)) s := fun l => by
    have h := Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_pi.mp hq l)
    simpa [Function.comp_def] using h
  exact (contDiffOn_pi.mp hp i).mul (ContDiffOn.sum fun l _ => (hs l).mul contDiffOn_const)

lemma s_unitH {s : Set (B.Mat k r)} {v : B.Mat k r → Fin (2 * r + k + 1) → ℂ} (hv : Sm v s)
    (hp : ∀ x ∈ s, 0 < (Formalism.QuantumDeterminants.herm (Hpk k r) (v x) (v x)).re) : Sm (fun x => unitH k r (v x)) s := by
  unfold Sm unitH Formalism.QuantumDeterminants.herm at *
  have hvi : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => v x i) s := fun i => contDiffOn_pi.mp hv i
  have hsi : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => star (v x i)) s := fun i => by
    have h := Complex.conjCLE.contDiff.comp_contDiffOn (hvi i)
    simpa [Function.comp_def] using h
  have hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => star (v x) ⬝ᵥ Hpk k r *ᵥ v x) s := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    exact ContDiffOn.sum fun i _ => (hsi i).mul (ContDiffOn.sum fun j _ => contDiffOn_const.mul (hvi j))
  have hre : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (star (v x) ⬝ᵥ Hpk k r *ᵥ v x).re) s := by
    have h := Complex.reCLM.contDiff.comp_contDiffOn hh
    simpa [Function.comp_def] using h
  have hsq := hre.sqrt fun x hx => (hp x hx).ne'
  have hinv := hsq.inv fun x hx => (Real.sqrt_pos.mpr (hp x hx)).ne'
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (((Real.sqrt (star (v x) ⬝ᵥ Hpk k r *ᵥ v x).re)⁻¹ : ℝ) : ℂ)) s := by
    have h := Complex.ofRealCLM.contDiff.comp_contDiffOn hinv
    simpa [Function.comp_def] using h
  exact hc.smul hv

end S1

open S1 in
theorem geometry_smoothness_holds : GeomSmooth := by
  intro k r z z' _hk hz hz'
  let fd : B.Mat k r → ℂ := fun g => (Zhat k r z z' g).det
  let f1 : B.Mat k r → ℝ := fun g =>
    (Formalism.QuantumDeterminants.herm (Hpk k r) (omW k r z z' g) (omW k r z z' g)).re
  let f2 : B.Mat k r → ℝ := fun g =>
    (Formalism.QuantumDeterminants.herm (Hpk k r) (omS k r z z' g) (omS k r z z' g)).re
  have hid : Sm (fun g : B.Mat k r => g) Set.univ := contDiffOn_id
  have cd : Continuous fd := (contDiffOn_univ.1 (s_det (s_Zhat z z' hid))).continuous
  have c1 : Continuous f1 :=
    (contDiffOn_univ.1 (s_re (s_herm _ (s_omW z z' hid) (s_omW z z' hid)))).continuous
  have c2 : Continuous f2 :=
    (contDiffOn_univ.1 (s_re (s_herm _ (s_omS (s := Set.univ) z z') (s_omS z z')))).continuous
  let U : Set (B.Mat k r) := (fd ⁻¹' {0}ᶜ ∩ {g | 0 < f1 g}) ∩ {g | 0 < f2 g}
  have hU : IsOpen U :=
    ((isOpen_compl_singleton.preimage cd).inter (isOpen_lt continuous_const c1)).inter
      (isOpen_lt continuous_const c2)
  have hmem : ∀ g ∈ posG k r z z', g ∈ U := by
    intro g hg
    obtain ⟨hgV, hG⟩ := hg
    refine ⟨⟨det_ne_of_G hz hz' hG, ?_⟩, ?_⟩
    · have hm : omW k r z z' g ∈ Wsp k r z := prW_mem hz _
      exact posV hz hm.1 hm.2 (omW_ne hz hz' hgV hG)
    · have hm : omS k r z z' g ∈ Wsp k r z' := prW_mem hz' _
      have hω : omS k r z z' g ≠ 0 := by rw [← omS_eq z z' hgV]; exact omW'_ne hz hz' hgV hG
      exact posV hz' hm.1 hm.2 hω
  have sU : Sm (fun g : B.Mat k r => g) U := contDiffOn_id
  have hd0 : ∀ g ∈ U, (Zhat k r z z' g).det ≠ 0 := fun g hg => hg.1.1
  have hnu : Sm (fun g => nuG z z' g) U := s_unitH (s_omW z z' sU) fun g hg => hg.1.2
  have hnuS : Sm (fun g => unitH k r (omS k r z z' g)) U := s_unitH (s_omS z z') fun g hg => hg.2
  have hdi : Sm (fun g => -((Zhat k r z z' g).det)⁻¹) U := ((s_det (s_Zhat z z' sU)).inv hd0).neg
  have hL : Sm (fun g => Lm k r z z' g) U := by
    unfold Lm
    exact contDiffOn_const.add (ContDiffOn.sum fun c _ => ContDiffOn.sum fun a _ =>
      s_msmul (hdi.mul (s_adj (s_Zhat z z' sU) c a)) (s_mmul contDiffOn_const sU))
  have hP : Sm (fun g => Phi k r z z' g) U := by
    unfold Phi
    exact s_mmul (s_mmul contDiffOn_const sU) hL
  have hio : Sm (fun g => Phi k r z z' g *
      (Pm k r z' - Rk k r (unitH k r (omS k r z z' g)) (unitH k r (omS k r z z' g)) * Pm k r z')) U :=
    s_mmul hP (contDiffOn_const.sub (s_mmul (smooth_hermitian_rank_two hnuS hnuS) contDiffOn_const))
  refine ⟨fun g₀ hg₀ => ⟨U, fun g => nuG z z' g, hU, hmem g₀ hg₀, hnu, fun g _ _ => rfl⟩,
    fun g₀ hg₀ => ⟨U, fun g => unitH k r (omS k r z z' g), hU, hmem g₀ hg₀, hnuS, fun g _ hgV => ?_⟩,
    fun g₀ hg₀ => ⟨U, _, hU, hmem g₀ hg₀, hio, fun g _ hgV => ?_⟩⟩
  · show unitH k r (omW' k r z z' g) = _
    rw [omS_eq z z' hgV]
  · show Phi k r z z' g * (Pm k r z' - Rk k r (unitH k r (omW' k r z z' g)) (unitH k r (omW' k r z z' g)) *
      Pm k r z') = _
    rw [omS_eq z z' hgV]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.GeometryEquivarianceFirstVector
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom

open Formalism.QuantumDeterminants PI.UnitaryGroupMassFormula.GsFr
open scoped Matrix

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace S2

variable {k r : ℕ}

private theorem herm_hpk_mulVec_of_mem_uh {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ w) = Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v w := by
  have hh' : hᴴ * Formalism.QuantumDeterminants.Hpk k r * h = Formalism.QuantumDeterminants.Hpk k r := hh
  show star (h *ᵥ w) ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ (h *ᵥ v)) = star w ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ v)
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hh']

lemma unitH_UH {h : B.Mat k r} (hh : h ∈ UH (Hpk k r)) (v : Fin (2 * r + k + 1) → ℂ) :
    unitH k r (h *ᵥ v) = h *ᵥ unitH k r v := by
  show ((((Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ v)).re)⁻¹ : ℝ) : ℂ) • (h *ᵥ v)) =
    h *ᵥ ((((Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re)⁻¹ : ℝ) : ℂ) • v)
  rw [herm_hpk_mulVec_of_mem_uh hh, Matrix.mulVec_smul]

lemma omW_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (g : B.Mat k r) :
    omW k r z z' (n * g * n') = omW k r z z' g := by
  show prW k r z (xcof k r z z' (n * g * n')) = prW k r z (xcof k r z z' g)
  rw [xcof_N hz hz' hn hn' g]
  exact prW_N hn (fun a => xcof_esI z z' g a)

lemma omW'_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) {g : B.Mat k r} (hg : g ∈ B.GV k r) :
    omW' k r z z' (n * g * n') = omW' k r z z' g := by
  have hh : nᴴ * Hpk k r * n = Hpk k r := hn.1
  have hleft : (Hpk k r * nᴴ * Hpk k r) * n = 1 := by
    calc (Hpk k r * nᴴ * Hpk k r) * n = Hpk k r * (nᴴ * Hpk k r * n) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hh, WeylGroupFacts.hpk_sq]
  have hnn : n⁻¹ * n = 1 := by
    rw [Matrix.inv_eq_left_inv hleft]
    exact hleft
  show prW k r z' ((n * g * n')⁻¹ *ᵥ xcofL k r z z' (n * g * n')) = prW k r z' (g⁻¹ *ᵥ xcofL k r z z' g)
  rw [xcofL_N hz hz' hn hn' g, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, Matrix.mul_assoc, hnn, Matrix.mul_one, ← Matrix.mulVec_mulVec]
  exact prW_N (WeylGroupFacts.mem_n_inv hn') (fun a => ginv_xcofL_esI z z' hg a)

end S2

open S2 in
theorem geometry_equivariance_first_vector : GeomEqvNu := by
  intro k r z z' _ hz hz' h hh n hn h' hh' n' hn' g hg
  have hy : h⁻¹ * n⁻¹ * g * n' * h' = h⁻¹ * (n⁻¹ * g * n') * h' := by simp only [Matrix.mul_assoc]
  have hhi := WeylGroupFacts.uw_inv hh
  have hhi' := WeylGroupFacts.uw_inv hh'
  have hni := WeylGroupFacts.mem_n_inv hn
  have hu : h * h⁻¹ = 1 := Matrix.mul_nonsing_inv h (RankOneEmbeddings.In.uw_unit hh)
  have hu' : h' * h'⁻¹ = 1 := Matrix.mul_nonsing_inv h' (RankOneEmbeddings.In.uw_unit hh')
  constructor
  · show unitH k r (omW k r z z' g) = h *ᵥ unitH k r (omW k r z z' (h⁻¹ * n⁻¹ * g * n' * h'))
    rw [hy, omW_UW hz hhi hh', omW_N hz hz' hni hn', unitH_UH hhi.1, Matrix.mulVec_mulVec, hu,
      Matrix.one_mulVec]
  · show unitH k r (omW' k r z z' g) = h' *ᵥ unitH k r (omW' k r z z' (h⁻¹ * n⁻¹ * g * n' * h'))
    rw [hy, omW'_UW hz hz' hhi hh', omW'_N hz hz' hni hn' hg.1, unitH_UH hhi'.1, Matrix.mulVec_mulVec,
      hu', Matrix.one_mulVec]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Geom
end

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem second_shift_geometry_holds : SSn.SSnGeom :=
  SSn.Geom.geometry_assembly_holds SSn.Geom.geometry_smoothness_holds SSn.Geom.geometry_equivariance_first_vector SSn.Geom.geometry_equivariance_embedding
    SSn.Geom.geometry_at_level_function SSn.Geom.geometry_boundedness_at_zero SSn.Geom.geometry_unipotent_bound_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
end

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem kappa_quadratic_bound_holds : JABddKapQQ :=
  jABddKapQQ_of_shared second_shift_geometry_holds rho_projection_existence gauge_lines_holds SSn.Rep.datum_unit_norm_holds

theorem jABddOpQQ_of_ssnRep (h : SSn.SSnRep) : JABddOpQQ :=
  jABddOpQQ_of_bddLeaves bounded_scalar_transfer_holds kappa_quadratic_bound_holds
    (SSn.jABddSSnQQ_of_leaves SSn.ChainPf.chain_bound_holds second_shift_geometry_holds h)
    (SSn.jABddSSnStarQQ_of_leaves SSn.ChainPf.chain_bound_holds second_shift_geometry_holds h)

end Formalism.FourierDecayAlt.P.CutMP.JA

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_ssnRep (hJ : JfSmoothDS) (hG : Gauge.GC.GenTransfer) (h : JA.SSn.SSnRep) :
    Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_bdd hJ hG (JA.jABddOpQQ_of_ssnRep h)

end Formalism.FourierDecayAlt.P.CutMP
