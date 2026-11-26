module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesTor
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScalarOfMultOne
public import Formalism.LocalRingCardinality.DataTies

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSpec
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

noncomputable section

namespace GlobalTheory.AdelicLattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem incl_mem_lamAf (L : Submodule (𝓞 E) (Fin n → E)) {x : Fin n → E} (hx : x ∈ L) :
    (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) ∈ lamAf (F := F) L :=
  Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩

theorem exists_approx (L : Submodule (𝓞 E) (Fin n → E)) (g : ℕ) (hg : 1 ≤ g)
    (y : Fin n → E ⊗[F] Af F) (hy : y ∈ lamAf (F := F) L) :
    ∃ x ∈ L, ∃ z ∈ lamAf (F := F) L,
      y = (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) + (g : E ⊗[F] Af F) • z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, x.2, 0, zero_mem _, by simp⟩
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by funext i; simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, z, hz, rfl⟩ := ha
    obtain ⟨x', hx', z', hz', rfl⟩ := hb
    refine ⟨x + x', add_mem hx hx', z + z', add_mem hz hz', ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _)]
    ring
  | smul s a _ ha =>
    obtain ⟨x, hx, z, hz, rfl⟩ := ha
    obtain ⟨r, hr, w, hw, e⟩ := Formalism.UG.P.csSpan_approx (F := F) (E := E) Formalism.UG.P.csGlob_intAdApprox
      (g : 𝓞 F) (Nat.cast_ne_zero.2 (by omega)) s.2
    rw [GlobalTheory.AutInhab.levelafC_natCast] at e
    refine ⟨(⟨r, hr⟩ : 𝓞 E) • x, L.smul_mem _ hx,
      (⟨w, hw⟩ : IntAf F E) • (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) + s • z,
      add_mem (Submodule.smul_mem _ _ (incl_mem_lamAf L hx)) (Submodule.smul_mem _ _ hz), ?_⟩
    funext i
    show (s : E ⊗[F] Af F) * (Formalism.UG.inclE (F := F) (Af F) (x i) + (g : E ⊗[F] Af F) * z i) =
      Formalism.UG.inclE (F := F) (Af F) (r * x i) + (g : E ⊗[F] Af F) *
        (w * Formalism.UG.inclE (F := F) (Af F) (x i) + (s : E ⊗[F] Af F) * z i)
    rw [map_mul]
    linear_combination Formalism.UG.inclE (F := F) (Af F) (x i) * e

theorem incl_mem_iff (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) ∈ lamAf (F := F) L ↔ x ∈ L := by
  refine ⟨fun h => ?_, incl_mem_lamAf L⟩
  rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin n) L (Module.Finite.iff_fg.2 hfg) hspan]
  show ((1⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
      (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) ∈ Formalism.UG.latS (F := F) (Af F) (IntAf F E) L
  rw [inv_one, Units.val_one, one_mulVec]
  refine Submodule.span_mono ?_ h
  rintro _ ⟨y, rfl⟩
  exact ⟨y, y.2, rfl⟩

theorem span_lamAf (L : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Submodule.span (E ⊗[F] Af F) (lamAf (F := F) L : Set (Fin n → E ⊗[F] Af F)) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨m, hm, hy⟩ := GlobalTheory.AutInhab.lamAf_absorbs (F := F) L hspan y
  obtain ⟨u, hu⟩ := GlobalTheory.AutInhab.isUnit_natCast (F := F) (E := E) m hm
  have : y = ((u⁻¹ : (E ⊗[F] Af F)ˣ) : E ⊗[F] Af F) • ((m : E ⊗[F] Af F) • y) := by
    rw [smul_smul, ← hu, Units.inv_mul, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hy)

theorem adelicLattice_spec : ∀ (I : AutInst) (g : ℕ), 1 ≤ g → (∀ y ∈ I.Lf, ∃ x ∈ I.L, ∃ z ∈ I.Lf, y = (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) + (g : (I.E ⊗[I.F] Af I.F)) • z) ∧ (∀ x : Fin I.n → I.E, (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) ∈ I.Lf ↔ x ∈ I.L) ∧ Submodule.span (I.E ⊗[I.F] Af I.F) (I.Lf : Set (Fin I.n → (I.E ⊗[I.F] Af I.F))) = ⊤ ∧ I.Lf.FG ∧ ∀ y : Fin I.n → (I.E ⊗[I.F] Af I.F), ∃ m : ℕ, 1 ≤ m ∧ (m : (I.E ⊗[I.F] Af I.F)) • y ∈ I.Lf :=
  fun I g hg => ⟨exists_approx I.L g hg, incl_mem_iff I.L I.L_fg I.L_span, span_lamAf I.L I.L_span,
    GlobalTheory.AutInhab.lamAf_fg I.L I.L_fg, GlobalTheory.AutInhab.lamAf_absorbs I.L I.L_span⟩

end GlobalTheory.AdelicLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryTorusScaleBesselCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryTorusScaleBesselCharacter
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TorusScale

variable {k r : ℕ}

def dS (k r : ℕ) (l : ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then l ^ (r - i.val)
  else if r + k < i.val then (star (l ^ (r - (2 * r + k - i.val))))⁻¹ else 1

theorem dS_ne {l : ℂ} (hl : l ≠ 0) (i : Fin (2 * r + k + 1)) : dS k r l i ≠ 0 := by
  unfold dS
  split_ifs
  · exact pow_ne_zero _ hl
  · exact inv_ne_zero (star_ne_zero.2 (pow_ne_zero _ hl))
  · exact one_ne_zero

theorem dS_eI (l : ℂ) (a : Fin r) : dS k r l (eI k r a) = l ^ (r - a.val) := by
  unfold dS eI; simp [a.isLt]

theorem dS_mid (l : ℂ) (i : Fin (2 * r + k + 1)) (h : ¬ (i.val < r ∨ r + k < i.val)) : dS k r l i = 1 := by
  unfold dS
  rw [if_neg (by omega), if_neg (by omega)]

theorem dS_pair {l : ℂ} (hl : l ≠ 0) (i j : Fin (2 * r + k + 1)) (hi : i.val < r) (hij : i.val + j.val = 2 * r + k) :
    star (dS k r l i) * dS k r l j = 1 := by
  unfold dS
  rw [if_pos hi, if_neg (by omega), if_pos (by omega)]
  have : 2 * r + k - j.val = i.val := by omega
  rw [this]
  exact mul_inv_cancel₀ (star_ne_zero.2 (pow_ne_zero _ hl))

theorem diag_inv {n : Type} [Fintype n] [DecidableEq n] (d : n → ℂ) (hd : ∀ i, d i ≠ 0) :
    (diagonal d)⁻¹ = diagonal fun i => (d i)⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (hd i)

theorem conj_diag {n : Type} [Fintype n] [DecidableEq n] (d : n → ℂ) (hd : ∀ i, d i ≠ 0) (M : Matrix n n ℂ) (i j : n) :
    (diagonal d * M * (diagonal d)⁻¹) i j = d i * M i j * (d j)⁻¹ := by
  rw [diag_inv d hd]
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem diag_mem_UH (d : Fin (2 * r + k + 1) → ℂ) (h : ∀ i j, Hpk k r i j ≠ 0 → star (d i) * d j = 1) :
    diagonal d ∈ UH (Hpk k r) := by
  show (diagonal d)ᴴ * Hpk k r * diagonal d = Hpk k r
  ext i j
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hM : Hpk k r i j = 0
  · rw [hM]; ring
  · have := h i j hM
    rw [Pi.star_apply, mul_right_comm, this, one_mul]

theorem dS_Hpk {l : ℂ} (hl : l ≠ 0) (i j : Fin (2 * r + k + 1)) (h : Hpk k r i j ≠ 0) :
    star (dS k r l i) * dS k r l j = 1 := by
  by_cases h1 : i.val < r ∧ i.val + j.val = 2 * r + k
  · exact dS_pair hl i j h1.1 h1.2
  by_cases h2 : j.val < r ∧ i.val + j.val = 2 * r + k
  · have := congrArg star (dS_pair hl j i h2.1 (by omega))
    rw [star_mul, star_star, star_one] at this
    exact this
  by_cases h3 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
  · rw [← h3.2.2, dS_mid l i (by omega)]; simp
  exfalso
  unfold Hpk at h
  rw [if_neg h1, if_neg h2, if_neg h3] at h
  exact h rfl

theorem conj_mem_N (d : Fin (2 * r + k + 1) → ℂ) (hd : ∀ i, d i ≠ 0)
    (h : ∀ i j, Hpk k r i j ≠ 0 → star (d i) * d j = 1) {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hn : n ∈ Nset k r) : diagonal d * n * (diagonal d)⁻¹ ∈ Nset k r := by
  obtain ⟨h1, h2, h3⟩ := hn
  refine ⟨?_, fun a i hi => ?_, fun i j a b c => ?_⟩
  · refine Pv.Frames.UH_mul (Pv.Frames.UH_mul (diag_mem_UH d h) h1) ?_
    rw [diag_inv d hd]
    refine diag_mem_UH _ fun i j hij => ?_
    rw [star_inv₀, ← mul_inv, h i j hij, inv_one]
  · rw [conj_diag d hd, h2 a i hi]
    split_ifs with e
    · rw [e, mul_one, mul_inv_cancel₀ (hd _)]
    · ring
  · rw [conj_diag d hd, h3 i j a b c]
    split_ifs with e
    · rw [e, mul_one, mul_inv_cancel₀ (hd _)]
    · ring

theorem conj_mem_N_iff (d : Fin (2 * r + k + 1) → ℂ) (hd : ∀ i, d i ≠ 0)
    (h : ∀ i j, Hpk k r i j ≠ 0 → star (d i) * d j = 1) (n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    n ∈ Nset k r ↔ diagonal d * n * (diagonal d)⁻¹ ∈ Nset k r := by
  refine ⟨conj_mem_N d hd h, fun hn => ?_⟩
  have hd' : ∀ i, (d i)⁻¹ ≠ 0 := fun i => inv_ne_zero (hd i)
  have := conj_mem_N (fun i => (d i)⁻¹) hd'
    (fun i j hij => by rw [star_inv₀, ← mul_inv, h i j hij, inv_one]) hn
  convert this using 1
  ext i j
  rw [conj_diag _ hd', conj_diag _ hd]
  have := hd i
  have := hd j
  field_simp

theorem UW_col {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (i j : Fin (2 * r + k + 1)) (hj : j.val < r ∨ r + k < j.val) :
    h i j = if i = j then 1 else 0 := by
  have key : h *ᵥ bvec j = bvec j := by
    rcases hj with hj | hj
    · exact (hh.2.1 ⟨j.val, hj⟩).1
    · have := (hh.2.1 ⟨2 * r + k - j.val, by omega⟩).2
      have e : esI k r ⟨2 * r + k - j.val, by omega⟩ = j := by
        apply Fin.ext
        have := j.isLt
        show 2 * r + k - (2 * r + k - j.val) = j.val
        omega
      rwa [e] at this
  have := congrFun key i
  simpa [bvec, Pi.single_apply] using this

theorem Hpk_outer (i j p : Fin (2 * r + k + 1)) (hj : j.val < r ∨ r + k < j.val) (hij : i.val + j.val = 2 * r + k) :
    Hpk k r j p = if p = i then 1 else 0 := by
  unfold Hpk
  by_cases e : p = i
  · subst e
    rw [if_pos rfl]
    by_cases h1 : j.val < r
    · rw [if_pos ⟨h1, by omega⟩]
    · rw [if_neg (by omega), if_pos (by omega)]
  · have e' : p.val ≠ i.val := fun x => e (Fin.ext x)
    rw [if_neg e, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem UW_row {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (i j : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    h i j = if j = i then 1 else 0 := by
  have hi0 := i.isLt
  let q : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩
  have hq : q.val < r ∨ r + k < q.val := by show 2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val; omega
  have hiq : i.val + q.val = 2 * r + k := by show i.val + (2 * r + k - i.val) = _; omega
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have := congrFun (congrFun hU q) j
  rw [Hpk_outer i q j hq hiq, Matrix.mul_assoc, Matrix.mul_apply] at this
  simp only [Matrix.conjTranspose_apply, UW_col hh _ q hq] at this
  rw [Finset.sum_eq_single q (fun b _ hb => by simp [hb]) (by simp), Matrix.mul_apply] at this
  simp only [Hpk_outer i q _ hq hiq] at this
  simpa using this

theorem dS_comm (l : ℂ) {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : diagonal (dS k r l) * h = h * diagonal (dS k r l) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hj : j.val < r ∨ r + k < j.val
  · rw [UW_col hh i j hj]
    split_ifs with e
    · rw [e]; ring
    · ring
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [UW_row hh i j hi]
    split_ifs with e
    · rw [e]; ring
    · ring
  rw [dS_mid l i hi, dS_mid l j hj]; ring

theorem diag_fix (d : Fin (2 * r + k + 1) → ℂ) (hd : ∀ i : Fin (2 * r + k + 1), ¬ (i.val < r ∨ r + k < i.val) → d i = 1)
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : diagonal d *ᵥ z = z := by
  funext i
  rw [Matrix.mulVec_diagonal]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [hz i h]; ring
  · rw [hd i h, one_mul]

theorem inv_fix {l : ℂ} (hl : l ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    (diagonal (dS k r l))⁻¹ *ᵥ z = z := by
  rw [diag_inv _ (dS_ne hl)]
  exact diag_fix _ (fun i hi => by rw [dS_mid l i hi, inv_one]) hz

theorem ell_conj {l : ℂ} (hl : l ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ell k r z (diagonal (dS k r l) * M * (diagonal (dS k r l))⁻¹) = l * ell k r z M := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [conj_diag _ (dS_ne hl), dS_eI, dS_eI]
    have e : r - a.val = (r - (a.val + 1)) + 1 := by omega
    rw [e, pow_succ]
    have := pow_ne_zero (r - (a.val + 1)) hl
    field_simp
  · have hra : r - a.val = 1 := by have := a.isLt; omega
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_fix hl hz, Matrix.mulVec_diagonal, dS_eI, hra, pow_one]

theorem pow_bound {x : ℝ} (hx : 0 < x) {m : ℕ} (hm : m ≤ r) :
    (x / 2) ^ m ≤ max (x / 2) (2 / x) ^ r ∧ (2 / x) ^ m ≤ max (x / 2) (2 / x) ^ r := by
  have h1 : 1 ≤ max (x / 2) (2 / x) := by
    rcases le_total x 2 with h | h
    · exact le_max_of_le_right ((one_le_div hx).2 h)
    · exact le_max_of_le_left ((one_le_div two_pos).2 h)
  exact ⟨(pow_le_pow_left₀ (by positivity) (le_max_left _ _) m).trans (pow_le_pow_right₀ h1 hm),
    (pow_le_pow_left₀ (by positivity) (le_max_right _ _) m).trans (pow_le_pow_right₀ h1 hm)⟩

theorem exists_torus_scale : ∀ (k r : ℕ) (c : ℂ), c ≠ 0 → ∃ t ∈ GG k r, (∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r) ∧ (∀ z, inWb k r z → t *ᵥ z = z ∧ (∀ h ∈ UWset k r z, t * h = h * t) ∧ ∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) ∧ ∀ a : Fin (r + 1), ∃ s : ℂ, s ≠ 0 ∧ ‖s‖ ≤ max (‖c‖ / 2) (2 / ‖c‖) ^ r ∧ ‖s‖⁻¹ ≤ max (‖c‖ / 2) (2 / ‖c‖) ^ r ∧ ∀ z, inWb k r z → t⁻¹ *ᵥ fvec k r z a = s • fvec k r z a := by
  intro k r c hc
  have hS : cStd ≠ 0 := by unfold cStd; simp
  have hl : cStd / c ≠ 0 := div_ne_zero hS hc
  have hn : ‖cStd / c‖ = 2 / ‖c‖ := by unfold cStd; simp
  have hx : 0 < ‖c‖ := norm_pos_iff.2 hc
  refine ⟨diagonal (dS k r (cStd / c)), diag_mem_UH _ (dS_Hpk hl), conj_mem_N_iff _ (dS_ne hl) (dS_Hpk hl),
    fun z hz => ⟨diag_fix _ (dS_mid _) hz, fun h hh => dS_comm _ hh, fun n _ => ?_⟩, fun a => ?_⟩
  · unfold psi
    rw [ell_conj hl hz, ← mul_assoc, mul_div_cancel₀ _ hc]
  · have hb := pow_bound (r := r) hx (Nat.sub_le r a.val)
    refine ⟨((cStd / c) ^ (r - a.val))⁻¹, inv_ne_zero (pow_ne_zero _ hl), ?_, ?_, fun z hz => ?_⟩
    · rw [norm_inv, norm_pow, hn, ← inv_pow, inv_div]; exact hb.1
    · rw [norm_inv, inv_inv, norm_pow, hn]; exact hb.2
    · unfold fvec
      split_ifs with h
      · rw [diag_inv _ (dS_ne hl)]
        funext i
        rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
        by_cases e : i = eI k r ⟨a.val, h⟩
        · rw [e, dS_eI]
        · simp [bvec, e]
      · have : r - a.val = 0 := by omega
        rw [inv_fix hl hz, this]; simp

end GlobalTheory.TorusScale

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryTorusScaleBesselCharacterStatement
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryTorus_scale_besselCharacter : ∀ (k r : ℕ) (c : ℂ), c ≠ 0 → ∃ t ∈ GG k r, (∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r) ∧ (∀ z, inWb k r z → t *ᵥ z = z ∧ (∀ h ∈ UWset k r z, t * h = h * t) ∧ ∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) ∧ ∀ a : Fin (r + 1), ∃ s : ℂ, s ≠ 0 ∧ ‖s‖ ≤ max (‖c‖ / 2) (2 / ‖c‖) ^ r ∧ ‖s‖⁻¹ ≤ max (‖c‖ / 2) (2 / ‖c‖) ^ r ∧ ∀ z, inWb k r z → t⁻¹ *ᵥ fvec k r z a = s • fvec k r z a := by
  first | exact @GlobalTheory.TorusScale.exists_torus_scale | exact GlobalTheory.TorusScale.exists_torus_scale | (intros; apply GlobalTheory.TorusScale.exists_torus_scale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountHypPAtAddQAt
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

theorem countHyp_one_le_rd (I : AutInst) : 1 ≤ I.rd := by
  have hd : (1 : ℝ) ≤ |(discr I.E : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |discr I.E| := Int.one_le_abs (NumberField.discr_ne_zero I.E)
    exact_mod_cast h1
  show 1 ≤ |(discr I.E : ℝ)| ^ ((1 : ℝ) / (2 * (I.f : ℝ)))
  exact Real.one_le_rpow hd (by positivity)

theorem countHyp_card_places (I : AutInst) : Fintype.card (InfinitePlace I.F) = I.f := by
  have : IsTotallyReal I.F := I.cm.totReal
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero,
    add_zero]
  exact (IsTotallyReal.finrank I.F).symm

theorem countHyp_pAt_add_qAt (I : AutInst) (v : InfinitePlace I.F) : I.pAt v + I.qAt v = I.n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin I.n)))
    (fun a => I.ε v a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h
  exact h

theorem countHyp_numerics : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → 0 ≤ Cg ∧ 1 ≤ B.I.rd ∧ 1 ≤ B.I.f ∧ Fintype.card (InfinitePlace B.I.F) = B.I.f ∧ p + q = B.I.n ∧ 2 * q + 2 ≤ B.I.n ∧ (∀ v, rkR (B.I.ε v) = q) ∧ min p q = q ∧ 0 < (∏ v, d v) ∧ 16 ≤ bigX B b ∧ 0 < tauStar B q b ∧ (1 ≤ q → tauStar B q b < 1 / 2 ∧ (B.I.n : ℝ) ^ 19 ≤ b ^ 2) ∧ ∃ h : ℝ, h = 8 * 10 ^ 14 * (Cg + 4) * (B.I.n : ℝ) ^ 19 * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd) ∧ GapGe B h ∧ HBig B 40 h ∧ HBig B 32 h ∧ 8 * (B.I.n : ℝ) * q < h ∧ 120 * (B.I.n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ h ∧ 40 * (B.I.n : ℝ) ^ 2 * Real.sqrt q ≤ h := by
  intro B Cg n₀ d p q b hn₀ hC
  unfold CountHyp at hC
  obtain ⟨hDS, hSig, hn, hq2, -, -, hb, -, hlam, hg1, hgC, -, -, -, hgap⟩ := hC
  have hrd : 1 ≤ B.I.rd := countHyp_one_le_rd B.I
  have hcard : Fintype.card (InfinitePlace B.I.F) = B.I.f := countHyp_card_places B.I
  have hf : 1 ≤ B.I.f := Module.finrank_pos
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace B.I.F) := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨hp₀, hq₀⟩ := hSig v₀
  have hpq : p + q = B.I.n := by rw [← hp₀, ← hq₀]; exact countHyp_pAt_add_qAt B.I v₀
  have h2q : 2 * q + 2 ≤ B.I.n := by
    rcases Nat.lt_or_ge q 3 with h | h
    · omega
    · nlinarith
  have hqp : q ≤ p := by omega
  have hmin : min p q = q := min_eq_right hqp
  have hrk : ∀ v, rkR (B.I.ε v) = q := by
    intro v
    obtain ⟨hp, hq⟩ := hSig v
    show min (B.I.pAt v) (B.I.qAt v) = q
    rw [hp, hq, hmin]
  have hd : 0 < ∏ v, d v := by
    refine Finset.prod_pos fun v _ => ?_
    obtain ⟨-, -, -, ⟨hdv, -⟩⟩ := hDS v
    exact hdv
  have hCg : 0 ≤ Cg := by
    by_contra hneg
    have h1 : b ^ Cg < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (lt_of_not_ge hneg)
    have h2 : (1 : ℝ) ≤ B.g := by exact_mod_cast hg1
    linarith
  have hnr : (8 : ℝ) ≤ B.I.n := by exact_mod_cast le_trans hn₀ hn
  have hfr : (1 : ℝ) ≤ B.I.f := by exact_mod_cast hf
  have hgr : (1 : ℝ) ≤ B.g := by exact_mod_cast hg1
  have hX : 16 ≤ bigX B b := by
    show 16 ≤ (B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b
    have a1 : 8 ≤ (B.I.n : ℝ) * B.I.f := by nlinarith
    have a2 : 8 ≤ (B.I.n : ℝ) * B.I.f * B.I.rd := by nlinarith
    have a3 : 8 ≤ (B.I.n : ℝ) * B.I.f * B.I.rd * B.g := by nlinarith
    nlinarith
  have htpos : 0 < tauStar B q b := by
    show 0 < (bigX B b)⁻¹ ^ (11 * q)
    have : 0 < bigX B b := by linarith
    positivity

  have hL : Real.log 2 ≤ Real.log (b * B.I.rd) := Real.log_le_log (by norm_num) (by nlinarith)
  have hlog2 := Real.log_two_gt_d9
  have hF5 : (1 : ℝ) ≤ (B.I.f : ℝ) ^ 5 := one_le_pow₀ hfr
  have hP1 : 2 ≤ (Cg + 4) * Real.log (b * B.I.rd) := by nlinarith
  have hP : 2 ≤ (Cg + 4) * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd) := by
    have : (Cg + 4) * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd)
        = ((Cg + 4) * Real.log (b * B.I.rd)) * (B.I.f : ℝ) ^ 5 := by ring
    rw [this]
    nlinarith
  have hN : 0 ≤ (B.I.n : ℝ) ^ 19 := by positivity
  have hbig : 10 ^ 15 * (B.I.n : ℝ) ^ 19 ≤
      8 * 10 ^ 14 * (Cg + 4) * (B.I.n : ℝ) ^ 19 * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd) := by
    have : 8 * 10 ^ 14 * (Cg + 4) * (B.I.n : ℝ) ^ 19 * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd)
        = 8 * 10 ^ 14 * (B.I.n : ℝ) ^ 19 * ((Cg + 4) * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd)) := by
      ring
    rw [this]
    nlinarith
  have hn1 : (1 : ℝ) ≤ B.I.n := by linarith
  have hn2 : (B.I.n : ℝ) ^ 2 ≤ (B.I.n : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
  have hn3 : (B.I.n : ℝ) ^ 3 ≤ (B.I.n : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
  have hqn : (q : ℝ) ≤ B.I.n := by exact_mod_cast (show q ≤ B.I.n by omega)
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hsq : Real.sqrt q ≤ B.I.n := by
    calc Real.sqrt q ≤ Real.sqrt ((B.I.n : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = B.I.n := Real.sqrt_sq (by positivity)
  have hs40 : 40 * (B.I.n : ℝ) ^ 2 * Real.sqrt q ≤
      8 * 10 ^ 14 * (Cg + 4) * (B.I.n : ℝ) ^ 19 * (B.I.f : ℝ) ^ 5 * Real.log (b * B.I.rd) := by
    have e1 : 40 * (B.I.n : ℝ) ^ 2 * Real.sqrt q ≤ 40 * (B.I.n : ℝ) ^ 2 * B.I.n :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have e2 : 40 * (B.I.n : ℝ) ^ 2 * B.I.n = 40 * (B.I.n : ℝ) ^ 3 := by ring
    linarith
  refine ⟨hCg, hrd, hf, hcard, hpq, h2q, hrk, hmin, hd, hX, htpos, ?_, _, rfl, hgap, ?_, ?_, ?_, ?_, hs40⟩
  · intro hq1
    constructor
    · show (bigX B b)⁻¹ ^ (11 * q) < 1 / 2
      have hXp : 0 < bigX B b := by linarith
      have hi : (bigX B b)⁻¹ ≤ 16⁻¹ := inv_anti₀ (by norm_num) hX
      have hi0 : 0 ≤ (bigX B b)⁻¹ := inv_nonneg.mpr hXp.le
      have hpow : (bigX B b)⁻¹ ^ (11 * q) ≤ (bigX B b)⁻¹ :=
        pow_le_of_le_one hi0 (by linarith [show (16 : ℝ)⁻¹ ≤ 1 by norm_num]) (by omega)
      have : (16 : ℝ)⁻¹ < 1 / 2 := by norm_num
      linarith
    · have hpc : 0 < (Finset.univ.filter fun a => B.I.ε v₀ a = true).card := by
        show 0 < B.I.pAt v₀
        omega
      have hqc : 0 < (Finset.univ.filter fun a => B.I.ε v₀ a = false).card := by
        show 0 < B.I.qAt v₀
        omega
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hpc
      obtain ⟨a', ha'⟩ := Finset.card_pos.mp hqc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
      have hne : B.I.ε v₀ a ≠ B.I.ε v₀ a' := by rw [ha, ha']; decide
      have hg := hgap v₀ a a' hne
      obtain ⟨l1, l2⟩ := abs_le.mp (hlam v₀ a)
      obtain ⟨l3, l4⟩ := abs_le.mp (hlam v₀ a')
      have hdiff : |B.lam v₀ a - B.lam v₀ a'| ≤ 2 * b ^ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have hb0 : 0 ≤ b ^ 2 := by positivity
      linarith
  · intro v
    rw [hrk v]
    linarith
  · intro v
    rw [hrk v]
    have : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
    nlinarith
  · have hpos : 0 < (B.I.n : ℝ) ^ 19 := by positivity
    have e1 : 8 * (B.I.n : ℝ) * q ≤ 8 * (B.I.n : ℝ) ^ 2 := by nlinarith
    linarith
  · have r1 : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (B.I.n : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow hq0 hqn (by norm_num)
    have r2 : (B.I.n : ℝ) ^ ((3 : ℝ) / 2) ≤ (B.I.n : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    rw [Real.rpow_two] at r2
    have e1 : 120 * (B.I.n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (B.I.n : ℝ) * (B.I.n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (r1.trans r2) (by positivity)
    have e2 : 120 * (B.I.n : ℝ) * (B.I.n : ℝ) ^ 2 = 120 * (B.I.n : ℝ) ^ 3 := by ring
    linarith

end GlobalTheory.Dec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerRepK
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec.FormF

variable {n : ℕ}

lemma toMK_cont (ε : Fin n → Bool) : Continuous (fun k : KG ε => toMK k) :=
  (isClosedEmbeddingMatrix n ε).1.continuous.comp continuous_subtype_val

lemma inner_rep {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsURepOn G σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G)
    (x y : H) : ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  LinearIsometry.inner_map_map (⟨(σ g : H →ₗ[ℂ] H), h.2.1 g hg⟩ : H →ₗᵢ[ℂ] H) x y

lemma inner_rep_K {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsURepOn (Kset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Kset ε) (x y : H) : ⟪σ g x, y⟫_ℂ = ⟪x, σ (star g) y⟫_ℂ := by
  rw [← inner_rep h hg x, ← ContinuousLinearMap.comp_apply (σ g) (σ (star g)), ← h.1.2 _ hg _ (Kset_star ε hg),
    Unitary.mul_star_self_of_mem hg.1, h.1.1, ContinuousLinearMap.one_apply]

theorem rangeType : ∀ (n : ℕ) (ε : Fin n → Bool) (abelian₂ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (T : S →L[ℂ] H'), IsKTypeOf ε σ abelian₂ S → (∀ k ∈ Kset ε, ∀ x y : S, (y : H) = σ k x → T y = σ' k (T x)) → T ≠ 0 → IsKTypeOf ε σ' abelian₂ (LinearMap.range (T : S →ₗ[ℂ] H')) := by
  intro n ε abelian₂ H _ _ σ S H' _ _ σ' T hS hT hT0
  haveI := hS.1
  have hinj : Function.Injective T := by
    rcases hS.2.2.1 ((LinearMap.ker (T : S →ₗ[ℂ] H')).map S.subtype) (Submodule.map_subtype_le _ _) (by
      rintro k hk _ ⟨x, hx, rfl⟩
      refine ⟨⟨σ k x, hS.2.1 k hk x x.2⟩, ?_, rfl⟩
      have hx' : T x = 0 := hx
      change T _ = 0
      rw [hT k hk x _ rfl, hx', map_zero]) with h | h
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have : (x : H) ∈ (LinearMap.ker (T : S →ₗ[ℂ] H')).map S.subtype := ⟨x, hx, rfl⟩
      rw [h] at this
      exact Subtype.ext this
    · exfalso
      apply hT0
      ext x
      have : (x : H) ∈ (LinearMap.ker (T : S →ₗ[ℂ] H')).map S.subtype := by rw [h]; exact x.2
      obtain ⟨y, hy, hxy⟩ := this
      have : y = x := Subtype.ext hxy
      subst this
      exact hy
  have hT' : ∀ k (hk : k ∈ Kset ε) (x : S), σ' k (T x) = T ⟨σ k x, hS.2.1 k hk x x.2⟩ :=
    fun k hk x => (hT k hk x _ rfl).symm
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · rintro k hk _ ⟨x, rfl⟩
    exact ⟨_, (hT' k hk x).symm⟩
  · intro S' hle hst
    rcases hS.2.2.1 ((S'.comap (T : S →ₗ[ℂ] H')).map S.subtype) (Submodule.map_subtype_le _ _) (by
      rintro k hk _ ⟨x, hx, rfl⟩
      refine ⟨⟨σ k x, hS.2.1 k hk x x.2⟩, ?_, rfl⟩
      have hx' : T x ∈ S' := hx
      change T _ ∈ S'
      rw [← hT' k hk x]
      exact hst k hk _ hx') with h | h
    · left
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨x, rfl⟩ := hle hz
      have : (x : H) ∈ (S'.comap (T : S →ₗ[ℂ] H')).map S.subtype := ⟨x, hz, rfl⟩
      rw [h] at this
      have : x = 0 := Subtype.ext this
      simp [this]
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨x, rfl⟩
      have : (x : H) ∈ (S'.comap (T : S →ₗ[ℂ] H')).map S.subtype := by rw [h]; exact x.2
      obtain ⟨y, hy, hxy⟩ := this
      have : y = x := Subtype.ext hxy
      subst this
      exact hy
  · obtain ⟨v, hv, hv0, hwt⟩ := hS.2.2.2.1
    refine ⟨T ⟨v, hv⟩, ⟨_, rfl⟩, fun h => hv0 (congrArg Subtype.val (hinj (h.trans (map_zero T).symm))), ?_⟩
    intro θ hθ
    rw [← map_smul]
    exact (hT _ hθ ⟨v, hv⟩ _ (hwt θ hθ).symm).symm
  · rintro μ _ ⟨x, rfl⟩ h0 hwt
    refine hS.2.2.2.2 μ x x.2 (fun h => h0 (by have : x = 0 := Subtype.ext h; simp [this])) fun θ hθ => ?_
    have := hwt θ hθ
    change σ' _ (T x) = _ • T x at this
    rw [hT' _ hθ, ← map_smul] at this
    exact congrArg Subtype.val (hinj this)

theorem psEntry : PhiPos → ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), FiniteDimensional ℂ W → (∀ v : W, ContinuousOn (fun k => τ k v) (Kset ε)) → ∀ x : Matrix (Fin n) (Fin n) ℂ, x.PosDef → ∀ u y : W, ⟪y, ps ε lam τ w x u⟫_ℂ = (Module.finrank ℂ W : ℂ) * ∫ k : KG ε, Phi lam ((toMK k)⁻¹ * x * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, u⟫_ℂ) ∂(muK ε) := by
  intro hP n ε lam W _ _ τ w hW hτ x hx u y
  haveI := FiniteDimensional.complete ℂ W
  have hk : Continuous (fun k : KG ε => toMK k) :=
    (isClosedEmbeddingMatrix n ε).1.continuous.comp continuous_subtype_val
  have h1 : Continuous (fun k : KG ε => τ (toMK k) w) := (hτ w).comp_continuous hk fun k => k.2
  have h2 : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * x * toMK k)) := by
    have e : ∀ k : KG ε, (toMK k)⁻¹ = (toMK k)ᴴ := fun k => K_inv k.2
    simp only [e]
    unfold Phi
    refine continuous_finsetProd _ fun i _ => Continuous.zpow₀ ?_ _ fun k => Or.inl ?_
    · unfold leadMinor
      exact (((hk.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hk).matrix_submatrix _ _).matrix_det
    · exact (hP n lam _ (hx.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC k.2).1))).1 i
  have h3 : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * x * toMK k) •
      (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) :=
    h2.smul (((ContinuousLinearMap.smulRightL ℂ W W).continuous.comp ((innerSL ℂ).continuous.comp h1)).clm_apply h1)
  have h4 := h3.integrable_of_hasCompactSupport (μ := muK ε) (HasCompactSupport.of_compactSpace _)
  unfold ps
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, ContinuousLinearMap.integral_apply h4,
    ← integral_inner (h4.apply_continuousLinearMap u)]
  congr 2
  funext k
  simp [inner_smul_right, mul_comm]

theorem muConj : ∀ (n : ℕ) (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ), ∫ k : KG ε, F ((toMK k).map star) ∂(muK ε) = ∫ k : KG ε, F (toMK k) ∂(muK ε) := by
  intro n ε F
  let c0 : (Matrix (Fin n) (Fin n) ℂ)ˣ →* (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    Units.map (RingHom.mapMatrix (starRingEnd ℂ)).toMonoidHom
  let c : KG ε → KG ε := fun k => ⟨⟨c0 k.1.1, UJ_star k.1.2⟩, K_star k.2⟩
  have hc : ∀ k, toMK (c k) = (toMK k).map star := fun k => rfl
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hcc : ∀ k, c (c k) = k := fun k => hemb.injective (by simp only [hc, map_star_star])
  have hcont : Continuous c := by
    rw [hemb.continuous_iff]
    exact hemb.continuous.matrix_map continuous_star
  let e : KG ε ≃ₜ* KG ε :=
    { toFun := c, invFun := c, left_inv := hcc, right_inv := hcc
      map_mul' := fun a b => hemb.injective (by
        change (toMK a * toMK b).map star = (toMK a).map star * (toMK b).map star
        exact map_star_mul _ _)
      continuous_toFun := hcont, continuous_invFun := hcont }
  haveI := (compact_haar_holds n ε).1
  haveI : IsProbabilityMeasure ((muK ε).map e) := inferInstance
  haveI : ((muK ε).map e).IsHaarMeasure := e.isHaarMeasure_map _
  have h : (muK ε).map e = muK ε := Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
  have := integral_map_equiv (μ := muK ε) e.toHomeomorph.toMeasurableEquiv (fun k => F (toMK k))
  rw [show (muK ε).map e.toHomeomorph.toMeasurableEquiv = muK ε from h] at this
  exact this.symm

theorem avgMap : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ρ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (u : H), FiniteDimensional ℂ W → IsURepOn (Kset ε) ρ → CompleteSpace H → IsURepOn (Kset ε) σ → ∃ T : W →L[ℂ] H, (∀ k ∈ Kset ε, ∀ x, T (ρ k x) = σ k (T x)) ∧ ∀ (x : W) (φ : H →L[ℂ] ℂ), Integrable (fun k : KG ε => ⟪ρ (toMK k) w, x⟫_ℂ * φ (σ (toMK k) u)) (muK ε) ∧ φ (T x) = ∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ * φ (σ (toMK k) u) ∂(muK ε) := by
  intro n ε W _ _ ρ w H _ _ σ u hW hρ hH hσ
  have h1 : Continuous (fun k : KG ε => ρ (toMK k) w) := (hρ.2.2 w).comp_continuous (toMK_cont ε) fun k => k.2
  have h2 : Continuous (fun k : KG ε => σ (toMK k) u) := (hσ.2.2 u).comp_continuous (toMK_cont ε) fun k => k.2
  have hi : ∀ x : W, Integrable (fun k : KG ε => ⟪ρ (toMK k) w, x⟫_ℂ • σ (toMK k) u) (muK ε) := fun x =>
    ((h1.inner continuous_const).smul h2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let T : W →ₗ[ℂ] H :=
    { toFun := fun x => ∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ • σ (toMK k) u ∂(muK ε)
      map_add' := fun x y => by simp only [inner_add_right, add_smul]; exact integral_add (hi x) (hi y)
      map_smul' := fun c x => by simp only [inner_smul_right, mul_smul, integral_smul, RingHom.id_apply] }
  refine ⟨LinearMap.toContinuousLinearMap T, fun k hk x => ?_, fun x φ => ⟨?_, ?_⟩⟩
  · obtain ⟨k0, rfl⟩ : k ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hk
    change ∫ k : KG ε, ⟪ρ (toMK k) w, ρ (toMK k0) x⟫_ℂ • σ (toMK k) u ∂(muK ε) =
      σ (toMK k0) (∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ • σ (toMK k) u ∂(muK ε))
    rw [← ContinuousLinearMap.integral_comp_comm _ (hi x), ← integral_mul_left_eq_self _ k0]
    congr 1
    funext k
    have e : toMK (k0 * k) = toMK k0 * toMK k := rfl
    simp only [e, hρ.1.2 _ k0.2 _ k.2, hσ.1.2 _ k0.2 _ k.2, ContinuousLinearMap.comp_apply, inner_rep hρ k0.2,
      map_smul]
  · simpa using φ.integrable_comp (hi x)
  · change φ (∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ • σ (toMK k) u ∂(muK ε)) = _
    rw [← ContinuousLinearMap.integral_comp_comm _ (hi x)]
    simp

theorem avgSchur : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ρ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), FiniteDimensional ℂ W → IsURepOn (Kset ε) ρ → (∀ S : Submodule ℂ W, IsKStableOn ε ρ S → S = ⊥ ∨ S = ⊤) → w ≠ 0 → ∃ c : ℂ, c ≠ 0 ∧ ∀ (x : W) (φ : W →L[ℂ] ℂ), ∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ * φ (ρ (toMK k) w) ∂(muK ε) = c * φ x := by
  intro n ε W _ _ ρ w hW hρ hirr hw
  haveI := FiniteDimensional.complete ℂ W
  haveI : Nontrivial W := ⟨⟨w, 0, hw⟩⟩
  obtain ⟨T, hT, hTi⟩ := avgMap n ε W ρ w W ρ w hW hρ inferInstance hρ
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T : W →ₗ[ℂ] W)
  have hTc : ∀ x, T x = c • x := by
    rcases hirr (Module.End.eigenspace (T : W →ₗ[ℂ] W) c) (fun k hk x hx => by
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      change T _ = _ at hx ⊢
      rw [hT k hk, hx, map_smul]) with h | h
    · exact absurd h hc
    · intro x
      have : x ∈ Module.End.eigenspace (T : W →ₗ[ℂ] W) c := by rw [h]; trivial
      exact Module.End.mem_eigenspace_iff.1 this
  refine ⟨c, ?_, fun x φ => by rw [← (hTi x φ).2, hTc, map_smul, smul_eq_mul]⟩
  rintro rfl
  have h1 : Continuous (fun k : KG ε => ρ (toMK k) w) := (hρ.2.2 w).comp_continuous (toMK_cont ε) fun k => k.2
  have h0 := (hTi w (innerSL ℂ w)).2
  rw [hTc, zero_smul, map_zero] at h0
  have e : ∀ k : KG ε, ⟪ρ (toMK k) w, w⟫_ℂ * innerSL ℂ w (ρ (toMK k) w) =
      ((‖⟪w, ρ (toMK k) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [innerSL_apply_apply, ← inner_conj_symm, Complex.conj_mul']; simp
  simp only [e, integral_ofReal] at h0
  have hc2 : Continuous (fun k : KG ε => ‖⟪w, ρ (toMK k) w⟫_ℂ‖ ^ 2) := (continuous_const.inner h1).norm.pow 2
  have hpos := hc2.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := muK ε) (x := 1)
    (HasCompactSupport.of_compactSpace _) (fun k => by positivity) (by
      have : toMK (1 : KG ε) = 1 := rfl
      simpa [this, hρ.1.1] using hw)
  have : (0 : ℝ) = ∫ k : KG ε, ‖⟪w, ρ (toMK k) w⟫_ℂ‖ ^ 2 ∂(muK ε) := by exact_mod_cast h0
  linarith

end GlobalTheory.Dec.FormF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeSizeConsequencesOfWordIndependentHyps
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeSizeConsequencesOfWordIndependentHyps
noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.SizesProof

theorem vand_pos {n : ℕ} {x : Fin n → ℝ} (h : StrictAnti x) : 0 < Formalism.MainNotions.S.vand x :=
  Finset.prod_pos fun _ _ => Finset.prod_pos fun _ hb => sub_pos.2 (h (Finset.mem_filter.1 hb).2)

theorem sizes_of_hyp : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), D.host.rdE ≤ large₂.sc.b →
    HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → Sizes D large₂ Cl Cg CT := by
  intro D large₂ C' Cl Cg cb Cu cT CT C0 hb h
  obtain ⟨⟨-, -, hmf, hfk, -, -, -, -, -, -, -, hg1, hg1', hg2, hg2', -, -, -, hv, -, -, hgap, hT, hCl, hCl0⟩, -, -⟩ := h
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hbe : Real.exp 1 < large₂.sc.b := Real.exp_lt_exp.2 hL
  have hb1 : 1 < large₂.sc.b := lt_trans (by simpa using Real.exp_lt_exp.2 (zero_lt_one (α := ℝ))) hbe
  have hm : D.R.m = 2 * D.R.rS + 2 := by
    have := D.R.two_le_m; obtain ⟨a, ha⟩ := D.R.m_even; unfold Ranks.rS; omega
  have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
  have hk : (1 : ℝ) ≤ D.R.k := by have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hkb : (1 : ℝ) ≤ D.R.k * large₂.sc.b := by nlinarith
  have h8 : (1 : ℝ) ≤ (D.R.k * large₂.sc.b) ^ 8 := one_le_pow₀ hkb
  have hrd : D.host.rdE = 2 * D.host.v := by unfold Host.v; ring
  have hgg : 1 ≤ gg D := by unfold gg; nlinarith
  have hu : ∀ w τ, StrictAnti (uS D w τ) := fun w τ => by
    have hk0 : D.R.k = (D.R.k - 1) + 1 := by have := D.R.m_add_three_le_k; omega
    have key : ∀ (i : ℕ) (hi : i + 1 < D.R.k), uS D w τ ⟨i + 1, hi⟩ < uS D w τ ⟨i, by omega⟩ := fun i hi => by
      have a := (D.hcW w τ).u_gt_v ⟨i, by omega⟩
      have b := (D.hcW w τ).v_gt_u ⟨i, by omega⟩
      unfold uS; exact_mod_cast b.trans a
    rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
    have hac' : a < c := hac
    induction c, hac' using Nat.le_induction with
    | base => exact key a hc
    | succ c hc' ih => exact (key c hc).trans (ih (by omega) hc')
  refine ⟨hL, Real.log_exp _, hbe, hm, hr, D.what₂.card_Tau, hCl, hmf.trans hfk, hv, hrd, rfl, hrd ▸ hb, hgg, ?_, ?_, ?_,
    fun w => (hT w).2, fun w τ => ⟨vand_pos (hu w τ), ?_⟩, ?_⟩
  · rw [two_mul, Real.rpow_add (by linarith)]
    exact mul_le_mul hg1' hg2' (by linarith) (by linarith)
  · have : large₂.sc.b ^ (8 : ℝ) ≤ large₂.sc.b ^ Cg := by
      refine le_trans ?_ (hg1.trans hg1')
      rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact pow_le_pow_left₀ (by linarith) (by nlinarith) 8
    exact (Real.rpow_le_rpow_left_iff hb1).1 this
  · refine le_trans ?_ (hg1.trans hg1')
    exact le_trans (by nlinarith) (le_self_pow₀ hkb (by norm_num))
  · have h1 : 0 < D.host.ka := div_pos Real.pi_pos (by linarith)
    have h2 : 0 < D.host.rdE := by linarith
    have h3 : 0 < gg D := by linarith
    have h4 : 0 < VV D τ := mul_pos (D.dsig_pos τ) (Finset.prod_pos fun i _ => by positivity)
    have h5 := vand_pos (hu w τ)
    unfold Tcrit; positivity
  · intro τ
    have hp : 0 ≤ Cl * D.R.k * (D.R.m : ℝ) ^ 4 := by positivity
    have key : ∀ (i : ℕ) (hi : i + 1 < 2 * D.R.rS + D.R.k + 1),
        Cl * D.R.k * (D.R.m : ℝ) ^ 4 < lamD D τ ⟨i, by omega⟩ - lamD D τ ⟨i + 1, hi⟩ := fun i hi => by
      have := hgap τ ⟨i, by omega⟩ (by simpa [hr] using hi)
      have h0 : (0 : ℝ) ≤ D.R.r * (D.R.m : ℝ) ^ 10 := by positivity
      exact lt_of_le_of_lt (le_add_of_nonneg_right h0) this
    rintro ⟨a, ha⟩ ⟨c, hc⟩ hac
    have hac' : a < c := hac
    induction c, hac' using Nat.le_induction with
    | base => exact key a hc
    | succ c hc' ih =>
      have := key c hc
      have := ih (by omega) hc'
      linarith

end GlobalTheory.Amp.SizesProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeSizeConsequencesOfWordIndependentHypsStatement
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitudeSizeConsequences_of_wordIndependentHyps : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), D.host.rdE ≤ large₂.sc.b → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → Sizes D large₂ Cl Cg CT := by
  first | exact @GlobalTheory.Amp.SizesProof.sizes_of_hyp | exact GlobalTheory.Amp.SizesProof.sizes_of_hyp | (intros; apply GlobalTheory.Amp.SizesProof.sizes_of_hyp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormDetInnerLeOfDetEqOne
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.PlueckerBound

theorem norm_det_inner_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {b : ℕ}
    (u w : Fin b → E) :
    ‖(Matrix.of fun a a' => ⟪u a, w a'⟫_ℂ).det‖ ≤ (∏ a, ‖u a‖) * ∏ a, ‖w a‖ := by
  have h := GlobalTheory.Hadamard.norm_det_apply_le (𝕜 := ℂ) (fun a => innerSL ℂ (u a)) w
  simp only [innerSL_apply_apply, innerSL_apply_norm] at h
  rw [mul_comm]
  exact h

theorem det_inner_sum_smul {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {b : ℕ}
    (u v : Fin b → E) (t : Matrix (Fin b) (Fin b) ℂ) :
    (Matrix.of fun a a' => ⟪u a, ∑ i, t i a' • v i⟫_ℂ).det
      = (Matrix.of fun a a' => ⟪u a, v a'⟫_ℂ).det * t.det := by
  rw [← Matrix.det_mul]
  congr 1
  ext a a'
  simp [Matrix.mul_apply, inner_sum, inner_smul_right, mul_comm]

theorem norm_det_inner_le_of_det_eq_one (n b : ℕ) (v u : Fin b → EuclideanSpace ℂ (Fin n))
    (t : Matrix (Fin b) (Fin b) ℂ) (ht : t.det = 1)
    (_h : ∀ a a', a ≠ a' → ⟪∑ i, t i a • v i, ∑ i, t i a' • v i⟫_ℂ = 0) :
    ‖(Matrix.of fun a a' => ⟪u a, v a'⟫_ℂ).det‖ ≤ (∏ a, ‖u a‖) * ∏ a, ‖∑ i, t i a • v i‖ := by
  have h := norm_det_inner_le u (fun a => ∑ i, t i a • v i)
  rwa [det_inner_sum_smul, ht, mul_one] at h

end GlobalTheory.PlueckerBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MuGPreimageConj
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem muG_preimage_conj {n : ℕ} (ε : Fin n → Bool) (u : Formalism.REAL.UJ ε) (B : Set (Formalism.REAL.UJ ε)) :
    Formalism.REAL.muG ε ((fun g => u⁻¹ * g * u) ⁻¹' B) = Formalism.REAL.muG ε B := by
  haveI : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  haveI : (Formalism.REAL.muG ε).IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
  have : (fun g => u⁻¹ * g * u) ⁻¹' B = (fun g => u⁻¹ * g) ⁻¹' ((fun g => g * u) ⁻¹' B) := rfl
  rw [this, measure_preimage_mul, measure_preimage_mul_right]

theorem gauge_map_of_iso : ∀ (n n' : ℕ) (ε : Fin n → Bool) (ε' : Fin n' → Bool), n = n' → ∀ (T : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε') (u : Formalism.REAL.UJ ε), (∀ g, Formalism.REAL.hs (uMat (T (u * g * u⁻¹)) - 1) = Formalism.REAL.hs (uMat g - 1)) → ∀ c c' : ℝ, IsGauge ε c → IsGauge ε' c' → (ENNReal.ofReal c • Formalism.REAL.muG ε).map T = ENNReal.ofReal c' • Formalism.REAL.muG ε' := by
  intro n n' ε ε' hn T u hT c c' hc hc'
  subst hn
  haveI : (Formalism.REAL.muG ε).IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
  haveI : (Formalism.REAL.muG ε').IsHaarMeasure := by unfold Formalism.REAL.muG; infer_instance
  haveI : ((Formalism.REAL.muG ε).map T).IsHaarMeasure := T.isHaarMeasure_map _
  obtain ⟨a, ha⟩ : ∃ a : NNReal, (Formalism.REAL.muG ε).map T = a • Formalism.REAL.muG ε' :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hball : ∀ r : ℝ, Formalism.REAL.muG ε {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} =
      a * Formalism.REAL.muG ε' {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} := by
    intro r
    have h1 := congrArg (fun m : Measure (Formalism.REAL.UJ ε') =>
      m {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}) ha
    have h2 := MeasurableEquiv.map_apply (μ := Formalism.REAL.muG ε) T.toHomeomorph.toMeasurableEquiv
      {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r}
    have h3 : (T : Formalism.REAL.UJ ε → Formalism.REAL.UJ ε') ⁻¹' {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} =
        (fun g => u⁻¹ * g * u) ⁻¹' {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} := by
      ext g
      have := hT (u⁻¹ * g * u)
      rw [show u * (u⁻¹ * g * u) * u⁻¹ = g by group] at this
      simp only [Set.mem_preimage, Set.mem_setOf_eq, this]
    change (Formalism.REAL.muG ε).map T _ = Formalism.REAL.muG ε ((T : Formalism.REAL.UJ ε → Formalism.REAL.UJ ε') ⁻¹' _) at h2
    rw [h3, muG_preimage_conj] at h2
    rw [← h2]
    simpa using h1
  have hω : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (n ^ 2))) 1)).toReal :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have hca : c' = c * a := by
    have h1 := Filter.Tendsto.const_mul c' hc
    have h2 := Filter.Tendsto.const_mul (c * a) hc'
    have h3 := tendsto_nhds_unique h1 (h2.congr fun r => by
      rw [hball r, ENNReal.toReal_mul, ENNReal.coe_toReal]; ring)
    exact mul_right_cancel₀ hω.ne' h3
  rw [Measure.map_smul _ (show AEMeasurable (⇑T) (Formalism.REAL.muG ε) from T.continuous.measurable.aemeasurable), ha, hca, ENNReal.ofReal_mul' a.coe_nonneg, ENNReal.ofReal_coe_nnreal, mul_smul]
  rfl

end GlobalTheory.FlagMeas
end
