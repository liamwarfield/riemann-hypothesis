module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.RowS
noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows.CornerBlockIndex

variable {ι : Type} {a m : ℕ}

abbrev V (ι : Type) (a m : ℕ) : Type := UnipotentBlockColumnIndex a (m + 1) (m + 1) → ι → ℂ

def mm (hm : m + 1 < a) : Fin a := ⟨m, by omega⟩

def ix (hm : m + 1 < a) (j : Fin a) (hj : (j : ℕ) < m + 1) : UnipotentBlockColumnIndex a (m + 1) (m + 1) :=
  ⟨(j, ⟨m + 1, hm⟩), hj, le_rfl, le_rfl⟩

def t0 (hm : m + 1 < a) : UnipotentBlockColumnIndex a (m + 1) (m + 1) := ix hm (mm hm) (Nat.lt_succ_self m)

def O (ι : Type) (hm : m + 1 < a) : Set (V ι a m) := {x | ∀ i, x (t0 hm) i ≠ 0}

def rowS (hm : m + 1 < a) (x : V ι a m) : Fin a → ι → ℂ :=
  fun j => if h : (j : ℕ) < m + 1 then x (ix hm j h) else 0

def rowT (hm : m + 1 < a) (x : V ι a m) : Fin a → ι → ℂ :=
  fun j => if h : (j : ℕ) < m + 1 then
    (if (j : ℕ) = m then (x (t0 hm))⁻¹ else -(x (ix hm j h) * (x (t0 hm))⁻¹)) else 0

def sM (hm : m + 1 < a) (x : V ι a m) : LieI ι a :=
  Matrix.of.symm ((1 : Matrix (Fin a) (Fin a) (ι → ℂ)).updateRow (mm hm) (rowS hm x))

def sI (hm : m + 1 < a) (x : V ι a m) : LieI ι a :=
  Matrix.of.symm ((1 : Matrix (Fin a) (Fin a) (ι → ℂ)).updateRow (mm hm) (rowT hm x))

def e (ι : Type) (hm : m + 1 < a) : V ι a m := Pi.single (t0 hm) 1

def xi (hm : m + 1 < a) (h : GL (Fin a) (ι → ℂ)) : V ι a m := fun t => h.val (mm hm) t.1.1

end PositivityTheory.jumpWindows.CornerBlockIndex

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.IntegralMem
section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.BlockIndexEqCornerIff
noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows.CornerBlockIndex

variable {ι : Type} {a m : ℕ}

theorem mul_upd {n R : Type} [Fintype n] [DecidableEq n] [CommRing R] (A : Matrix n n R) (p : n)
    (r : n → R) (i j : n) :
    (A * (1 : Matrix n n R).updateRow p r) i j = A i p * r j + if j = p then 0 else A i j := by
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
  simp only [Matrix.updateRow_self]
  congr 1
  split_ifs with hj
  · subst hj
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hl),
      Matrix.one_apply_ne (Finset.ne_of_mem_erase hl), mul_zero]
  · rw [Finset.sum_eq_single j]
    · rw [Matrix.updateRow_ne hj, Matrix.one_apply_eq, mul_one]
    · intro l hl hlj
      rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hl), Matrix.one_apply_ne hlj, mul_zero]
    · intro hj'; exact absurd (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩) hj'

theorem of_sM (hm : m + 1 < a) (x : V ι a m) :
    Matrix.of (sM hm x) = (1 : Matrix (Fin a) (Fin a) (ι → ℂ)).updateRow (mm hm) (rowS hm x) := rfl

theorem of_sI (hm : m + 1 < a) (x : V ι a m) :
    Matrix.of (sI hm x) = (1 : Matrix (Fin a) (Fin a) (ι → ℂ)).updateRow (mm hm) (rowT hm x) := rfl

theorem rowS_mm (hm : m + 1 < a) (x : V ι a m) : rowS hm x (mm hm) = x (t0 hm) := by
  unfold rowS
  rw [dite_eq_left (by simp [mm])]
  rfl

theorem rowT_mm (hm : m + 1 < a) (x : V ι a m) : rowT hm x (mm hm) = (x (t0 hm))⁻¹ := by
  unfold rowT
  rw [dite_eq_left (by simp [mm]), if_pos (by simp [mm])]

theorem rowT_ne (hm : m + 1 < a) (x : V ι a m) {j : Fin a} (hj : j ≠ mm hm) :
    rowT hm x j = -(rowS hm x j * (x (t0 hm))⁻¹) := by
  have hj' : (j : ℕ) ≠ m := fun h => hj (Fin.ext h)
  unfold rowT rowS
  split_ifs <;> first | (exfalso; omega) | rfl | simp

theorem mul_inv_cancel_at_t0_of_mem_O (hm : m + 1 < a) {x : V ι a m} (hx : x ∈ O ι hm) :
    x (t0 hm) * (x (t0 hm))⁻¹ = 1 := by
  funext i
  simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
  exact mul_inv_cancel₀ (hx i)

theorem block_index_eq_corner_iff (hm : m + 1 < a) (t : UnipotentBlockColumnIndex a (m + 1) (m + 1)) : t = t0 hm ↔ t.1.1 = mm hm := by
  constructor
  · rintro rfl; rfl
  · intro h
    apply Subtype.ext
    apply Prod.ext h
    apply Fin.ext
    obtain ⟨-, h1, h2⟩ := t.2
    show (t.1.2 : ℕ) = m + 1
    omega

theorem rowS_xi (hm : m + 1 < a) {h : GL (Fin a) (ι → ℂ)} (hh : GlobalTheory (m + 1) h) (k : Fin a) :
    rowS hm (xi hm h) k = h.val (mm hm) k := by
  unfold rowS
  split_ifs with hk
  · rfl
  · rw [hh _ _ (Or.inr (by omega)), Matrix.one_apply_ne]
    intro e; apply hk; rw [← e]; simp [mm]

theorem sI_mul_sM (hm : m + 1 < a) {x : V ι a m} (hx : x ∈ O ι hm) :
    Matrix.of (sI hm x) * Matrix.of (sM hm x) = 1 := by
  have hi1 := mul_inv_cancel_at_t0_of_mem_O hm hx
  refine Matrix.ext fun i j => ?_
  rw [of_sI, of_sM, mul_upd]
  by_cases hi : i = mm hm
  · subst hi
    simp only [Matrix.updateRow_self]
    by_cases hj : j = mm hm
    · subst hj
      rw [if_pos rfl, add_zero, rowT_mm, rowS_mm, Matrix.one_apply_eq, mul_comm, hi1]
    · rw [if_neg hj, rowT_mm, rowT_ne hm x hj, Matrix.one_apply_ne (Ne.symm hj)]
      ring
  · rw [Matrix.updateRow_ne hi, Matrix.one_apply_ne hi, zero_mul, zero_add]
    split_ifs with hj
    · subst hj; rw [Matrix.one_apply_ne hi]
    · rfl

theorem sM_mul_sI (hm : m + 1 < a) {x : V ι a m} (hx : x ∈ O ι hm) :
    Matrix.of (sM hm x) * Matrix.of (sI hm x) = 1 := by
  have hi1 := mul_inv_cancel_at_t0_of_mem_O hm hx
  refine Matrix.ext fun i j => ?_
  rw [of_sI, of_sM, mul_upd]
  by_cases hi : i = mm hm
  · subst hi
    simp only [Matrix.updateRow_self]
    by_cases hj : j = mm hm
    · subst hj
      rw [if_pos rfl, add_zero, rowT_mm, rowS_mm, Matrix.one_apply_eq, hi1]
    · rw [if_neg hj, rowS_mm, rowT_ne hm x hj, Matrix.one_apply_ne (Ne.symm hj)]
      linear_combination (-(rowS hm x j)) * hi1
  · rw [Matrix.updateRow_ne hi, Matrix.one_apply_ne hi, zero_mul, zero_add]
    split_ifs with hj
    · subst hj; rw [Matrix.one_apply_ne hi]
    · rfl


open Classical in
def uM (hm : m + 1 < a) (x : V ι a m) : GL (Fin a) (ι → ℂ) :=
  if hx : x ∈ O ι hm then ⟨Matrix.of (sM hm x), Matrix.of (sI hm x), sM_mul_sI hm hx, sI_mul_sM hm hx⟩ else 1

theorem uM_val (hm : m + 1 < a) {x : V ι a m} (hx : x ∈ O ι hm) : (uM hm x).val = Matrix.of (sM hm x) := by
  simp [uM, hx]

theorem uM_inv_val (hm : m + 1 < a) {x : V ι a m} (hx : x ∈ O ι hm) :
    (uM hm x)⁻¹.val = Matrix.of (sI hm x) := by
  simp [uM, hx]

theorem e_mem (hm : m + 1 < a) : e ι hm ∈ O ι hm := by
  intro i
  simp [e]

theorem rowS_e (hm : m + 1 < a) :
    rowS hm (e ι hm) = (1 : Matrix (Fin a) (Fin a) (ι → ℂ)) (mm hm) := by
  funext j
  by_cases hj : j = mm hm
  · subst hj; rw [rowS_mm]; simp [e]
  · have h0 : (1 : Matrix (Fin a) (Fin a) (ι → ℂ)) (mm hm) j = 0 := Matrix.one_apply_ne (Ne.symm hj)
    rw [h0]
    unfold rowS
    split_ifs with h
    · simp only [e]
      rw [Pi.single_eq_of_ne]
      intro h'; exact hj ((block_index_eq_corner_iff hm _).1 h')
    · rfl

theorem uM_e (hm : m + 1 < a) : uM hm (e ι hm) = 1 := by
  apply Units.ext
  rw [uM_val hm (e_mem hm), of_sM, rowS_e, Matrix.updateRow_eq_self]
  rfl

theorem xi_one (hm : m + 1 < a) : xi hm (1 : GL (Fin a) (ι → ℂ)) = e ι hm := by
  funext t
  simp only [xi, e, Units.val_one, Pi.single_apply, Matrix.one_apply, block_index_eq_corner_iff]
  by_cases h : t.1.1 = mm hm
  · simp [h]
  · simp [h, Ne.symm h]

theorem blk_uM (hm : m + 1 < a) (x : V ι a m) : GlobalTheory (m + 1) (uM hm x) := by
  intro i j hij
  by_cases hx : x ∈ O ι hm
  · rw [uM_val hm hx, of_sM]
    by_cases hi : i = mm hm
    · subst hi
      have hj : ¬ (j : ℕ) < m + 1 := by simp [mm] at hij; omega
      have hne : mm hm ≠ j := by intro h; subst h; simp [mm] at hj
      rw [Matrix.updateRow_self, Matrix.one_apply_ne hne]
      simp [rowS, hj]
    · rw [Matrix.updateRow_ne hi]
  · simp [uM, hx]

theorem mir_mul (hm : m + 1 < a) {h : GL (Fin a) (ι → ℂ)} (hh : GlobalTheory (m + 1) h) (hx : xi hm h ∈ O ι hm) :
    Mir m (h * (uM hm (xi hm h))⁻¹) := by
  have hi1 := mul_inv_cancel_at_t0_of_mem_O hm hx
  have e0 : xi hm h (t0 hm) = h.val (mm hm) (mm hm) := rfl
  rw [e0] at hi1
  intro i k hik
  rw [Units.val_mul, uM_inv_val hm hx, of_sI, mul_upd]
  by_cases hk : k = mm hm
  · subst hk
    rw [rowT_mm, if_pos rfl, add_zero, e0]
    by_cases hi : i = mm hm
    · subst hi; rw [hi1, Matrix.one_apply_eq]
    · have h2 : m + 1 ≤ (i : ℕ) := by
        rcases hik with h1 | h1
        · have : (i : ℕ) ≠ m := fun e => hi (Fin.ext e)
          omega
        · simp [mm] at h1
      rw [hh i (mm hm) (Or.inl h2), Matrix.one_apply_ne hi, zero_mul]
  · rw [if_neg hk, rowT_ne hm _ hk, rowS_xi hm hh, e0]
    by_cases hi : i = mm hm
    · subst hi
      rw [Matrix.one_apply_ne (Ne.symm hk)]
      linear_combination (-(h.val (mm hm) k)) * hi1
    · rcases hik with h1 | h1
      · have h2 : m + 1 ≤ (i : ℕ) := by
          have : (i : ℕ) ≠ m := fun e => hi (Fin.ext e)
          omega
        rw [hh i (mm hm) (Or.inl h2), hh i k (Or.inl h2), Matrix.one_apply_ne hi]
        ring
      · have h2 : m + 1 ≤ (k : ℕ) := h1
        rw [hh (mm hm) k (Or.inr h2), hh i k (Or.inr h2), Matrix.one_apply_ne (Ne.symm hk)]
        ring

theorem orb_sI [Fintype ι] {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] (hm : m + 1 < a)
    (ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)) (v : X) {x : V ι a m} (hx : x ∈ O ι hm) :
    orb ρ v (sI hm x) = ρ (uM hm x)⁻¹ v := by
  have hu : IsUnit (Matrix.of (sI hm x)) := ⟨(uM hm x)⁻¹, uM_inv_val hm hx⟩
  rw [orb, dite_eq_left hu, show hu.unit = (uM hm x)⁻¹ from Units.ext (by rw [IsUnit.unit_spec, uM_inv_val hm hx])]

end PositivityTheory.jumpWindows.CornerBlockIndex

end
end

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows.CornerBlockIndex

variable {ι : Type} {a m : ℕ}

variable [Fintype ι]

theorem isOpen_O (hm : m + 1 < a) : IsOpen (O ι hm) := by
  have h : PositivityTheory.jumpWindows.CornerBlockIndex.O ι hm =
      ⋂ i : ι, {x : PositivityTheory.jumpWindows.CornerBlockIndex.V ι a m | x (PositivityTheory.jumpWindows.CornerBlockIndex.t0 hm) i ≠ 0} := by
    ext x
    simp [PositivityTheory.jumpWindows.CornerBlockIndex.O]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_ne_fun ((continuous_apply i).comp (continuous_apply _)) continuous_const

theorem cd_sM (hm : m + 1 < a) : ContDiff ℝ ∞ (sM hm : V ι a m → LieI ι a) := by
  show ContDiff ℝ ∞ (fun x => (PositivityTheory.jumpWindows.CornerBlockIndex.sM hm x : Fin a → Fin a → ι → ℂ))
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_pi.2 fun k => ?_
  simp only [PositivityTheory.jumpWindows.CornerBlockIndex.sM, PositivityTheory.jumpWindows.CornerBlockIndex.rowS, Matrix.of_symm_apply, Matrix.updateRow_apply]
  split_ifs <;> first
    | exact contDiff_const
    | exact (contDiff_apply ℝ (fun _ => ℂ) k).comp (contDiff_apply ℝ (fun _ => (ι → ℂ)) _)
    | fun_prop

theorem cd_sI (hm : m + 1 < a) : ContDiffOn ℝ ∞ (sI hm : V ι a m → LieI ι a) (O ι hm) := by
  have hc : ∀ q k, ContDiff ℝ ∞ (fun x : PositivityTheory.jumpWindows.CornerBlockIndex.V ι a m => x q k) := fun q k =>
    (contDiff_apply ℝ (fun _ => ℂ) k).comp (contDiff_apply ℝ (fun _ => (ι → ℂ)) q)
  have hne : ∀ x ∈ PositivityTheory.jumpWindows.CornerBlockIndex.O ι hm, ∀ k : ι, x (PositivityTheory.jumpWindows.CornerBlockIndex.t0 hm) k ≠ 0 :=
    fun x hx => hx
  show ContDiffOn ℝ ∞ (fun x => (PositivityTheory.jumpWindows.CornerBlockIndex.sI hm x : Fin a → Fin a → ι → ℂ)) _
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => contDiffOn_pi.2 fun k => ?_
  simp only [PositivityTheory.jumpWindows.CornerBlockIndex.sI, PositivityTheory.jumpWindows.CornerBlockIndex.rowT, Matrix.of_symm_apply, Matrix.updateRow_apply]
  split_ifs <;> (try simp only [Pi.inv_apply, Pi.neg_apply, Pi.mul_apply]) <;> first
    | exact contDiffOn_const
    | exact (hc _ k).contDiffOn.inv fun x hx => hne x hx k
    | exact ((hc _ k).contDiffOn.mul ((hc _ k).contDiffOn.inv fun x hx => hne x hx k)).neg
    | (apply ContDiffOn.neg
       apply ContDiffOn.mul
       · exact (hc _ k).contDiffOn
       · exact (hc _ k).contDiffOn.inv fun x hx => hne x hx k)

theorem contOn_uM (hm : m + 1 < a) : ContinuousOn (uM hm : V ι a m → GL (Fin a) (ι → ℂ)) (O ι hm) := by
  rw [Units.isEmbedding_embedProduct.isInducing.continuousOn_iff]
  have h1 : ContinuousOn (fun x : V ι a m => ((Matrix.of (sM hm x) : Matrix (Fin a) (Fin a) (ι → ℂ)),
      MulOpposite.op (Matrix.of (sI hm x) : Matrix (Fin a) (Fin a) (ι → ℂ)))) (O ι hm) :=
    (cd_sM hm).continuous.continuousOn.prodMk
      (MulOpposite.continuous_op.comp_continuousOn (cd_sI hm).continuousOn)
  refine h1.congr fun x hx => ?_
  simp [uM_val hm hx, uM_inv_val hm hx]

theorem nhds_good (hm : m + 1 < a) {U : Set (GL (Fin a) (ι → ℂ))} (hU : U ∈ 𝓝 (1 : GL (Fin a) (ι → ℂ))) :
    O ι hm ∩ uM hm ⁻¹' U ∈ 𝓝 (e ι hm) := by
  have hb : PositivityTheory.jumpWindows.CornerBlockIndex.O ι hm ∈ 𝓝 (PositivityTheory.jumpWindows.CornerBlockIndex.e ι hm) :=
    (PositivityTheory.jumpWindows.CornerBlockIndex.isOpen_O (ι := ι) hm).mem_nhds (PositivityTheory.jumpWindows.CornerBlockIndex.e_mem hm)
  refine Filter.inter_mem hb ?_
  have hc : ContinuousAt (PositivityTheory.jumpWindows.CornerBlockIndex.uM hm : PositivityTheory.jumpWindows.CornerBlockIndex.V ι a m → GL (Fin a) (ι → ℂ))
      (PositivityTheory.jumpWindows.CornerBlockIndex.e ι hm) :=
    (PositivityTheory.jumpWindows.CornerBlockIndex.contOn_uM hm).continuousAt hb
  apply hc.preimage_mem_nhds
  rw [PositivityTheory.jumpWindows.CornerBlockIndex.uM_e]
  exact hU

theorem cd_cut (hm : m + 1 < a) {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {ρ : GL (Fin a) (ι → ℂ) →* (X →L[ℂ] X)} {v : X} (hv : SmV ρ v) {η : V ι a m → ℂ}
    (hη : ContDiff ℝ ∞ η) (hs : tsupport η ⊆ O ι hm) :
    ContDiff ℝ ∞ (fun x => η x • orb ρ v (sI hm x)) := by
  have ho := PositivityTheory.jumpWindows.CornerBlockIndex.isOpen_O (ι := ι) hm
  have hv' : ContDiffOn ℝ ∞ (PositivityTheory.jumpWindows.orb ρ v) {M : PositivityTheory.jumpWindows.LieI ι a | IsUnit (Matrix.of M)} := hv
  have hmaps : Set.MapsTo (PositivityTheory.jumpWindows.CornerBlockIndex.sI hm) (PositivityTheory.jumpWindows.CornerBlockIndex.O ι hm)
      {M : PositivityTheory.jumpWindows.LieI ι a | IsUnit (Matrix.of M)} := by
    intro x hx
    show IsUnit (Matrix.of (PositivityTheory.jumpWindows.CornerBlockIndex.sI hm x))
    exact ⟨⟨Matrix.of (PositivityTheory.jumpWindows.CornerBlockIndex.sI hm x), Matrix.of (PositivityTheory.jumpWindows.CornerBlockIndex.sM hm x),
      PositivityTheory.jumpWindows.CornerBlockIndex.sI_mul_sM hm hx, PositivityTheory.jumpWindows.CornerBlockIndex.sM_mul_sI hm hx⟩, rfl⟩
  have hcomp : ContDiffOn ℝ ∞ (PositivityTheory.jumpWindows.orb ρ v ∘ PositivityTheory.jumpWindows.CornerBlockIndex.sI hm) (PositivityTheory.jumpWindows.CornerBlockIndex.O ι hm) :=
    ContDiffOn.comp hv' (PositivityTheory.jumpWindows.CornerBlockIndex.cd_sI hm) hmaps
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport η
  · have hxO : PositivityTheory.jumpWindows.CornerBlockIndex.O ι hm ∈ 𝓝 x := ho.mem_nhds (hs hx)
    exact hη.contDiffAt.smul (hcomp.contDiffAt hxO)
  · have h0 : η =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
    refine (contDiffAt_const (c := (0 : X))).congr_of_eventuallyEq ?_
    filter_upwards [h0] with y hy
    simp only [Pi.zero_apply] at hy
    simp [hy]

theorem integral_mem {α X : Type} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] {Y : Submodule ℂ X} (hY : IsClosed (Y : Set X)) {f : α → X}
    (hf : Integrable f μ) (hfY : ∀ x, f x ∈ Y) : ∫ x, f x ∂μ ∈ Y := by
  have hcomplete : CompleteSpace Y := @IsClosed.completeSpace_coe X _ _ (Y : Set X) hY
  have hgm : AEStronglyMeasurable (fun x => (⟨f x, hfY x⟩ : Y)) μ :=
    (Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff).1 hf.aestronglyMeasurable
  have hgi : Integrable (fun x => (⟨f x, hfY x⟩ : Y)) μ :=
    hf.mono hgm (Filter.Eventually.of_forall fun x => le_rfl)
  have key : ∫ x, f x ∂μ = Y.subtypeL (∫ x, (⟨f x, hfY x⟩ : Y) ∂μ) := by
    rw [← Y.subtypeL.integral_comp_comm hgi]
    first | rfl | simp
  rw [key]
  first | exact (∫ x, (⟨f x, hfY x⟩ : Y) ∂μ).2 | simp

end PositivityTheory.jumpWindows.CornerBlockIndex

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.BlkUInvVal
noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows.CornerBlockIndex

variable {ι : Type} {a m : ℕ}

variable [Fintype ι]

def betL (l : (ι → ℂ) →L[ℝ] ℝ) (x : V ι a m) : V ι a m →ₗ[ℝ] ℝ where
  toFun y := l (∑ t, x t * y t)
  map_add' y y' := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c y := by simp [Finset.mul_sum]

def bet (l : (ι → ℂ) →L[ℝ] ℝ) : V ι a m →L[ℝ] V ι a m →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => LinearMap.toContinuousLinearMap (betL l x)
      map_add' := fun x x' => by ext y; simp [betL, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by ext y; simp [betL, Finset.mul_sum] }

theorem bet_apply (l : (ι → ℂ) →L[ℝ] ℝ) (x y : V ι a m) : bet l x y = l (∑ t, x t * y t) := by
  rfl

theorem bet_nondeg (hm : m + 1 < a) {χ : AddChar (ι → ℂ) ℂ} (hχ : ∀ z, (∀ w, χ (z * w) = 1) → z = 0)
    {l : (ι → ℂ) →L[ℝ] ℝ} (hl : ∀ z, χ z = Complex.exp ((l z : ℝ) * Complex.I)) :
    ∀ y : V ι a m, (∀ x, bet l x y = 0) → y = 0 := by
  intro y hy
  funext t
  show y t = 0
  apply hχ
  intro w
  have h1 := hy (Pi.single t w)
  rw [bet_apply] at h1
  have hs : ∑ s, (Pi.single t w : V ι a m) s * y s = y t * w := by
    rw [Finset.sum_eq_single t]
    · simp [mul_comm]
    · intro s _ hs
      simp [Pi.single_apply, hs]
    · simp
  rw [hs] at h1
  rw [hl, h1]
  simp

def Lb (_hm : m + 1 < a) : V ι a m →L[ℝ] LieI ι a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => Matrix.of.symm (posM Subtype.val y)
      map_add' := fun y y' => by rw [posM_add]; rfl
      map_smul' := fun c y => by
        ext i j k
        simp only [posM, Matrix.sum_apply, Matrix.single_apply, Pi.smul_apply, Matrix.of_symm_apply]
        rw [Finset.sum_apply, Finset.sum_apply, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        split_ifs <;> simp }

theorem blkU_val (hm : m + 1 < a) (y : V ι a m) : (blkU y : GL (Fin a) (ι → ℂ)).val = 1 + Matrix.of (Lb hm y) := by
  rfl

theorem blkU_inv_val (hm : m + 1 < a) (y : V ι a m) :
    (blkU y : GL (Fin a) (ι → ℂ))⁻¹.val = 1 - Matrix.of (Lb hm y) := by
  rfl

theorem lastE_eq {R : Type} [CommRing R] (hm : m + 1 < a) (y : UnipotentBlockColumnIndex a (m + 1) (m + 1) → R) :
    lastE (m + 1) y = y (t0 hm) := by
  unfold lastE
  rw [Finset.sum_eq_single (t0 hm)]
  · simp [t0, ix, mm]
  · intro t _ ht
    rw [if_neg]
    intro h1
    apply ht
    obtain ⟨⟨i, k⟩, h1', h2', h3'⟩ := t
    simp only at h1 h1' h2' h3'
    apply Subtype.ext
    simp only [t0, ix, mm]
    ext <;> simp <;> omega
  · simp

end PositivityTheory.jumpWindows.CornerBlockIndex

end
end

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

open CornerBlockIndex in
theorem mirabolic_induction_step_exists : S2 → S3 → S5 → S6 → S8 → MirabolicColumnBlock → S7 := by
  intro h2 h3 h5 h6 h8 h10 ι _ a X _ _ _ ρ hρ m hm χ hχc hχn hχnd U hU
  obtain ⟨l, hl⟩ := h8 ι χ hχc hχn
  have hβ : ∀ y : CornerBlockIndex.V ι a m, (∀ x, CornerBlockIndex.bet (a := a) (m := m) l x y = 0) → y = 0 :=
    CornerBlockIndex.bet_nondeg hm hχnd hl
  let μ : Measure (CornerBlockIndex.V ι a m) := Measure.addHaar
  obtain ⟨c, hc0, hc⟩ := h5 (CornerBlockIndex.V ι a m) μ (CornerBlockIndex.bet l) hβ
  obtain ⟨f, hfW, hfc, hfd, hfr, hfe⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (CornerBlockIndex.nhds_good hm hU)
  let η : CornerBlockIndex.V ι a m → ℂ := fun x => (f x : ℂ)
  have hηd : ContDiff ℝ ∞ η := Complex.ofRealCLM.contDiff.comp hfd
  have hηc : HasCompactSupport η := hfc.comp_left Complex.ofReal_zero
  have hηO : tsupport η ⊆ CornerBlockIndex.O ι hm :=
    (tsupport_comp_subset Complex.ofReal_zero f).trans (hfW.trans Set.inter_subset_left)
  have hfO : tsupport f ⊆ CornerBlockIndex.O ι hm := hfW.trans Set.inter_subset_left
  have hne : ∀ x, η x ≠ 0 → x ∈ tsupport f := by
    intro x hx
    apply subset_tsupport
    intro h0
    apply hx
    simp [η, h0]
  refine ⟨fun h => η (CornerBlockIndex.xi hm h), fun h => h * (CornerBlockIndex.uM hm (CornerBlockIndex.xi hm h))⁻¹, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [η, CornerBlockIndex.xi_one, hfe]
  · simp [CornerBlockIndex.xi_one, CornerBlockIndex.uM_e]
  · intro h hb hη
    exact CornerBlockIndex.mir_mul hm hb (hfO (hne _ hη))
  · intro h
    exact ⟨f (CornerBlockIndex.xi hm h), (hfr ⟨_, rfl⟩).1, rfl⟩
  · refine ⟨CornerBlockIndex.uM hm '' tsupport f, ?_, ?_, ?_, ?_⟩
    · exact hfc.isCompact.image_of_continuousOn ((CornerBlockIndex.contOn_uM hm).mono hfO)
    · rintro _ ⟨x, hx, rfl⟩
      exact (hfW hx).2
    · rintro _ ⟨x, _, rfl⟩
      exact CornerBlockIndex.blk_uM hm x
    · intro h _ hη
      exact ⟨_, ⟨_, hne _ hη, rfl⟩, by group⟩
  · intro v hv
    let F : CornerBlockIndex.V ι a m → X := fun x => η x • orb ρ v (CornerBlockIndex.sI hm x)
    have hFd : ContDiff ℝ ∞ F := CornerBlockIndex.cd_cut hm hv hηd hηO
    have hFc : HasCompactSupport F := hηc.smul_right
    obtain ⟨𝒢, h𝒢, hG⟩ := h6 ι a X ρ hρ (CornerBlockIndex.V ι a m) μ (CornerBlockIndex.bet l) hβ (CornerBlockIndex.O ι hm) (CornerBlockIndex.sI hm)
      (CornerBlockIndex.sM hm) (CornerBlockIndex.isOpen_O hm) (CornerBlockIndex.cd_sI hm) (CornerBlockIndex.cd_sM hm).contDiffOn
      (fun x hx => CornerBlockIndex.sI_mul_sM hm hx)
    have hGmem : FT μ (CornerBlockIndex.bet l) F ∈ 𝒢 := hG η v hηd hηc hηO hv
    obtain ⟨hint, hsm⟩ := h3 ι a X ρ hρ (CornerBlockIndex.V ι a m) μ (fun y => blkU y) (CornerBlockIndex.Lb hm)
      (CornerBlockIndex.blkU_val hm) (CornerBlockIndex.blkU_inv_val hm) 𝒢 h𝒢 _ hGmem
    have hFint : ∀ y, Integrable (fun x => Complex.exp (-↑((CornerBlockIndex.bet l x) y) * Complex.I) • F x) μ := by
      intro y
      apply Continuous.integrable_of_hasCompactSupport
      · exact Continuous.smul (by fun_prop) hFd.continuous
      · exact hFc.smul_left
    refine ⟨c⁻¹ • ∫ y, ρ (blkU y) (FT μ (CornerBlockIndex.bet l) F y) ∂μ, (h2 ι a X ρ hρ).2.2.1 _ _ hsm, ?_⟩
    intro Y hYc hYinv hvY
    have hFY : ∀ x, F x ∈ Y := by
      intro x
      apply Y.smul_mem
      unfold orb
      split_ifs
      · exact hYinv _ _ hvY
      · exact Y.zero_mem
    have hGY : ∀ y, FT μ (CornerBlockIndex.bet l) F y ∈ Y := fun y =>
      CornerBlockIndex.integral_mem hYc (hFint y) (fun x => Y.smul_mem _ (hFY x))
    refine ⟨Y.smul_mem _ (CornerBlockIndex.integral_mem hYc hint (fun y => hYinv _ _ (hGY y))), ?_⟩
    intro Λ hΛ h hb
    let L : X →L[ℂ] ℂ := Λ.comp (ρ h)
    let φ : CornerBlockIndex.V ι a m → ℂ := fun x => L (F x)
    have hφd : ContDiff ℝ ∞ φ := (L.restrictScalars ℝ).contDiff.comp hFd
    have hφc : HasCompactSupport φ := hFc.comp_left (map_zero L)
    have hkey : ∀ y, L (ρ (blkU y) (FT μ (CornerBlockIndex.bet l) F y)) =
        Complex.exp (↑((CornerBlockIndex.bet l (CornerBlockIndex.xi hm h)) y) * Complex.I) * FT μ (CornerBlockIndex.bet l) φ y := by
      intro y
      obtain ⟨y', hcomm, hy'⟩ := (h10 (ι → ℂ) a (m + 1)).2.2.2.2.2.2.2 h hb y
      have ht0 : ((CornerBlockIndex.t0 hm : UnipotentBlockColumnIndex a (m + 1) (m + 1)) : Fin a × Fin a).1 = CornerBlockIndex.mm hm :=
        (CornerBlockIndex.block_index_eq_corner_iff hm _).1 rfl
      have e1 : L (ρ (blkU y) (FT μ (CornerBlockIndex.bet l) F y)) =
          Λ (ρ (blkU y') (ρ h (FT μ (CornerBlockIndex.bet l) F y))) := by
        simp only [L, ContinuousLinearMap.comp_apply]
        rw [← ContinuousLinearMap.mul_apply, ← map_mul, hcomm, map_mul, ContinuousLinearMap.mul_apply]
      have e2 : Λ (ρ h (FT μ (CornerBlockIndex.bet l) F y)) = FT μ (CornerBlockIndex.bet l) φ y := by
        show L (∫ x, Complex.exp (-↑((CornerBlockIndex.bet l x) y) * Complex.I) • F x ∂μ) = _
        rw [← L.integral_comp_comm (hFint y)]
        unfold FT
        congr 1
        funext x
        exact L.map_smul _ _
      rw [e1, hΛ _ (hYinv _ _ (hGY y)), e2, CornerBlockIndex.lastE_eq hm, hy', ht0, hl, CornerBlockIndex.bet_apply]
      rfl
    have hmain : Λ (ρ h (c⁻¹ • ∫ y, ρ (blkU y) (FT μ (CornerBlockIndex.bet l) F y) ∂μ)) = φ (CornerBlockIndex.xi hm h) := by
      have : Λ (ρ h (c⁻¹ • ∫ y, ρ (blkU y) (FT μ (CornerBlockIndex.bet l) F y) ∂μ)) =
          c⁻¹ * ∫ y, L (ρ (blkU y) (FT μ (CornerBlockIndex.bet l) F y)) ∂μ := by
        rw [L.integral_comp_comm hint]
        simp only [L, ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]
      rw [this]
      simp_rw [hkey]
      rw [hc φ hφd hφc (CornerBlockIndex.xi hm h)]
      field_simp
    rw [hmain]
    show L (η (CornerBlockIndex.xi hm h) • orb ρ v (CornerBlockIndex.sI hm (CornerBlockIndex.xi hm h))) = _
    rw [map_smul, smul_eq_mul]
    by_cases h0 : η (CornerBlockIndex.xi hm h) = 0
    · simp [h0]
    · congr 1
      rw [CornerBlockIndex.orb_sI hm ρ v (hfO (hne _ h0))]
      simp only [L, ContinuousLinearMap.comp_apply, map_mul, ContinuousLinearMap.mul_apply]

end PositivityTheory.jumpWindows

end
