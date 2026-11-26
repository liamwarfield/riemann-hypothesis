module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalisationScaledIdealMemIff
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FinrankLeOfMapLe
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwistedIsRealOrderLattice
public import Formalism.HermitianCurvature.StatementJ
public import Formalism.HermitianCurvature.StatementFr

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalConditionsAndQuotientSplitting
namespace Formalism.FourierDecayAlt.P

theorem lattice_facts_general : Formalism.FourierDecayAlt.S6.LatticesGeneral :=
  assemble_lattice_facts degreeFacts_statement different_power_conj_stable
    unramRelative twistedLatticeBetween twistedLatticeIndex dual_lattice_subset
    traceDualGe scaledIdealNorm covolumeIndex

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PoissonJointFirstReduction
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open MeasureTheory Formalism.H
open scoped FourierTransform ComplexConjugate nonZeroDivisors

namespace Formalism.FourierDecayAlt.P

namespace Jx4

theorem rd_pos (E : Type) [Field E] [NumberField E] [IsCMField E] : 0 < S6.rd E := by
  have h : (0 : ℝ) < ((|NumberField.discr E| : ℤ) : ℝ) := by
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero E)
  unfold S6.rd
  exact Real.rpow_pos_of_pos h _

end Jx4

theorem poisson_level_joint : Formalism.FourierDecayAlt.J.PoissonStepJoint := by
  intro hF hJ E W _ D V _ _ _ _ _ ι _ π hπ Λ _ _ emb dmap hFr hW
  intro ε hε i hi1 hi2 w Y hY κ hκ t₀ B hB S hS
  obtain ⟨φ, Cφ, hc, hb, hnn, hdiag, hhat⟩ := hW ε hε i hi1 hi2 w Y hY κ hκ
  obtain ⟨hinj, hmem, hd0, hdual⟩ := hFr i hi1 hi2
  have key := hJ hF V ι π hπ (Λ i) E (emb i) (dmap i) (D.La i 1) (D.Lad i) φ Cφ
    (D.Nhat ε i w Y κ) hinj hmem hd0 hdual hc hb hnn hhat t₀ B hB S (fun t ht => (hS t ht).2)
  refine Eq.trans_le ?_ key
  exact Finset.sum_congr rfl fun t ht => hdiag t (hS t ht).1

theorem lattice_x_eq_lambda_one : Formalism.FourierDecayAlt.J.XIsLamOne := by
  intro m i C ka N I A g B
  have h : 2 * (i - 1) + 1 - 1 = 2 * i - 2 := by omega
  refine ⟨?_, ?_⟩
  · unfold Sz.xThreshold Sz.lamThreshold
    rw [h]
  · unfold Sz.xHat Sz.lamHat
    rw [h]

theorem frame_product_identities : Formalism.FourierDecayAlt.J.FrameProducts := by
  intro r i s C rd g N I A TT hi hs hrd hg
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hrd0 : rd ≠ 0 := hrd.ne'
  have hg0 : g ≠ 0 := hg.ne'
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have e1 : 2 * r + 2 - 1 = 2 * r + 1 := by omega
  constructor
  · have hz : rd ^ (S6.nuBlock (r : ℤ) ((n + 1 : ℕ) : ℤ) ((t + 1 : ℕ) : ℤ) + 1) =
        rd ^ (2 * r + 1) / rd ^ (2 * n + t) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hrd0]
      congr 1
      unfold S6.nuBlock
      push_cast
      ring
    have e2 : 2 * (n + 1 - 1) + (t + 1) - 1 = 2 * n + t := by omega
    unfold Sz.lamThreshold Sz.lamHat
    rw [hz, e1, e2]
    have b1 : C * (2 * Real.pi / g) * N / I = (2 * Real.pi / g) * (C * N / I) := by ring
    have b2 : C * (2 * Real.pi / rd) * N / (g * I) = (2 * Real.pi / (rd * g)) * (C * N / I) := by ring
    rw [b1, b2, mul_pow, mul_pow]
    generalize C * N / I = X
    simp only [div_eq_mul_inv, mul_pow, inv_pow, mul_inv, inv_inv]
    ring
  · have hz : rd ^ (S6.nuBlock (r : ℤ) ((n + 1 : ℕ) : ℤ) ((r : ℤ) + 2 - ((n + 1 : ℕ) : ℤ))) =
        rd ^ r / rd ^ n := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hrd0]
      congr 1
      unfold S6.nuBlock
      push_cast
      ring
    have key : ∀ P a : ℝ, 0 ≤ a → √P * a = √(P * a ^ 2) := fun P a ha => by
      rw [Real.sqrt_mul' _ (sq_nonneg a), Real.sqrt_sq ha]
    rw [hz, key _ _ (mul_nonneg hg.le (div_nonneg (pow_nonneg hrd.le _) (pow_nonneg hrd.le _)))]
    unfold Sz.lamPrimeHat Sz.lamPrimeSq
    congr 1
    have e3 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    have e4 : 2 * (n + 1 - 1) = 2 * n := by omega
    have e5 : 2 * (n + 1) - 2 = 2 * n := by omega
    rw [e1, e3, e4, e5]
    have b3 : C * (2 * Real.pi / rd) * N / I = (2 * Real.pi / rd) * (C * N / I) := by ring
    rw [b3, mul_pow]
    generalize C * N / I = X
    generalize (Real.sqrt TT)⁻¹ = Y
    simp only [div_eq_mul_inv, mul_pow, inv_pow, mul_inv, inv_inv]
    have hg1 : g * g⁻¹ = 1 := mul_inv_cancel₀ hg0
    have hr1 : rd * rd⁻¹ = 1 := mul_inv_cancel₀ hrd0
    linear_combination
      (C * A * Y * X ^ (2 * n) * ((2 * Real.pi) ^ (2 * r + 1))⁻¹ * (2 * Real.pi) ^ (2 * n + 1) *
          g ^ (2 * r + 2) * (g ^ (2 * n))⁻¹ * rd ^ (2 * r) * (rd ^ (2 * n))⁻¹) * hg1 -
        (C * A * Y * X ^ (2 * n) * ((2 * Real.pi) ^ (2 * r + 1))⁻¹ * (2 * Real.pi) ^ (2 * n + 1) *
          g ^ (2 * r + 2) * (g ^ (2 * n))⁻¹ * rd ^ (2 * r) * (rd ^ (2 * n))⁻¹) * hr1

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FreeOf2RmatrixTranspose
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr

namespace Formalism.FourierDecayAlt.P.Fr4

section

variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

theorem free_one (c : S) : FreeOf c (1 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.one_right _

theorem free_zero (c : S) : FreeOf c (0 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.zero_right _

theorem free_mul {c : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (hy : FreeOf c y) : FreeOf c (x * y) :=
  fun i j => (hx i j).mul_right (hy i j)

theorem free_add {c : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (hy : FreeOf c y) : FreeOf c (x + y) :=
  fun i j => (hx i j).add_right (hy i j)

theorem free_sub {c : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (hy : FreeOf c y) : FreeOf c (x - y) :=
  fun i j => (hx i j).sub_right (hy i j)

theorem free_neg {c : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf c x) : FreeOf c (-x) :=
  fun i j => (hx i j).neg_right

theorem free_smul {c : S} {x : SlopeTestRemainingChoices S A} (k : ℂ) (hx : FreeOf c x) : FreeOf c (k • x) :=
  fun i j => (hx i j).smul_right k

theorem free_pow {c : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (n : ℕ) : FreeOf c (x ^ n) :=
  fun i j => (hx i j).pow_right n

theorem free_star [StarRing A] {c : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf c x) : FreeOf c (star x) := by
  intro i j
  have h := (hx j i).star_star
  rwa [Wd1.star_eU] at h

theorem free_io (c : S) (x : A) : FreeOf c (io x : SlopeTestRemainingChoices S A) := by
  intro i j
  show (eU c i j : SlopeTestRemainingChoices S A) * io x = io x * eU c i j
  ext u v
  unfold io
  rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Wd1.eU_apply]
  split_ifs <;> simp

theorem free_eU {a c : S} (hc : c ≠ a) (k l : Fin 2) : FreeOf c (eU a k l : SlopeTestRemainingChoices S A) :=
  fun i j => Wd1.eU_comm_of_ne hc i j k l

theorem freeOf2_mul {c : S} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) (hN : FreeOf2 c N) : FreeOf2 c (M * N) := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact free_add (free_mul (hM _ _) (hN _ _)) (free_mul (hM _ _) (hN _ _))

theorem freeOf2_transpose {c : S} {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) : FreeOf2 c Mᵀ :=
  fun i j => hM j i

theorem freeOf2_matrix_entries {c : S} {x y z w : SlopeTestRemainingChoices S A} (hx : FreeOf c x) (hy : FreeOf c y) (hz : FreeOf c z)
    (hw : FreeOf c w) : FreeOf2 c !![x, y; z, w] := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact hx
  · exact hy
  · exact hz
  · exact hw

theorem freeOf2_one (c : S) : FreeOf2 c (1 : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  by_cases h : i = j
  · rw [h, Matrix.one_apply_eq]; exact free_one c
  · rw [Matrix.one_apply_ne h]; exact free_zero c

theorem freeOf2_rmatrix {a c : S} (hc : c ≠ a) (D : ℂ) : FreeOf2 c (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  unfold Rh0
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc j i))

theorem freeOf2_rmatrix_transpose {a c : S} (hc : c ≠ a) (D : ℂ) : FreeOf2 c (Rht0 a D : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  unfold Rht0
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc i j))

theorem freeOf2_lift (c : S) (M : M2 A) : FreeOf2 c (lift0 M : M2 (SlopeTestRemainingChoices S A)) :=
  fun i j => free_io c (M i j)

end

section

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

theorem free_l (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) (Y : ℂ) : FreeOf c (f.l L Y) :=
  free_add (free_io c _) (free_mul (free_io c _) (h.2.2.2.2.2.2.2.2 Y))

theorem free_d (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) : FreeOf c (f.d L) :=
  free_mul (free_pow (free_io c _) _) h.2.2.2.2.2.2.1

theorem free_di (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) : FreeOf c (f.di L) :=
  free_mul h.2.2.2.2.2.2.2.1 (free_pow (free_io c _) _)

theorem free_m (L : LevelData A r) {f : FrameData S A} {c : S} (h : f.Free c) (Y : ℂ) : FreeOf c (f.m L Y) :=
  free_mul (free_mul (free_di L h) (free_star (free_l L h _))) (free_d L h)

theorem free_DD {f : FrameData S A} {c : S} (h : f.Free c) (Y Ya : ℂ) : FreeOf c (f.DD Y Ya) :=
  free_smul _ (free_sub (h.2.2.2.2.2.2.2.2 Y) (h.2.2.2.2.2.2.2.2 Ya))

theorem free_tz (L : LevelData A r) (c : S) : FreeOf c (tz L : SlopeTestRemainingChoices S A) := free_io c _

theorem plus_free (L : LevelData A r) {f : FrameData S A} {a c : S} (hc : c ≠ a) (h : f.Free c) (Ya : ℂ) :
    (f.plus L a Ya).Free c := by
  obtain ⟨hRR, hTT, hF, hFi, hx, hxi, hcc, hci, hee⟩ := id h
  have z := free_zero (A := A) c
  have o := free_one (A := A) c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact free_mul hRR (Wd1.ins_free hc _ (hTT Ya))
  · exact fun Y => freeOf2_mul (hTT Y) (freeOf2_rmatrix hc _)
  · exact free_mul (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries (free_io c _) z z (free_io c _))
      (freeOf2_matrix_entries o z (free_mul (free_io c _) (free_l L h Ya)) (free_io c _)))) hF
  · exact free_mul hFi (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries o z (free_neg (free_l L h Ya)) (free_io c _))
      (freeOf2_matrix_entries (free_io c _) z z (free_io c _))))
  · exact fun Y => free_mul (hx Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))
  · exact fun Y => free_mul (hxi Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))
  · exact free_mul hcc (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hxi _)) z z (hx _)))
  · exact free_mul hci (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hx _)) z z (hxi _)))
  · exact fun Y => Wd1.ins_free hc _ (freeOf2_matrix_entries (free_add (free_sub (hee Y) (free_DD h Y Ya)) (free_tz L c))
      (free_neg (free_smul _ o)) z (free_mul (free_mul (hxi _) (hee Y)) (hx _)))

theorem minus_free (L : LevelData A r) {f : FrameData S A} {b c : S} (hc : c ≠ b) (h : f.Free c) (Yb : ℂ) :
    (f.minus L b Yb).Free c := by
  obtain ⟨hRR, hTT, hF, hFi, hx, hxi, hcc, hci, hee⟩ := id h
  have z := free_zero (A := A) c
  have o := free_one (A := A) c
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact free_mul hRR (Wd1.ins_free hc _ (freeOf2_transpose (hTT Yb)))
  · exact fun Y => freeOf2_mul (freeOf2_rmatrix_transpose hc _) (hTT Y)
  · exact free_mul (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries (free_io c _) z z (free_io c _))
      (freeOf2_matrix_entries o z (free_mul (free_io c _) (free_m L h Yb)) (free_io c _)))) hF
  · exact free_mul hFi (Wd1.ins_free hc _ (freeOf2_mul (freeOf2_matrix_entries o z (free_neg (free_m L h Yb)) (free_io c _))
      (freeOf2_matrix_entries (free_io c _) z z (free_io c _))))
  · exact fun Y => free_mul (hx Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))
  · exact fun Y => free_mul (hxi Y) (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ o) z z o))
  · exact free_mul hcc (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hxi _)) z z (hx _)))
  · exact free_mul hci (Wd1.ins_free hc _ (freeOf2_matrix_entries (free_smul _ (hx _)) z z (hxi _)))
  · exact fun Y => Wd1.ins_free hc _ (freeOf2_matrix_entries (hee Y) z (free_neg (free_smul _ (free_mul (hxi _) (hxi _))))
      (free_add (free_sub (free_mul (free_mul (hxi _) (hee Y)) (hx _)) (free_DD h Y Yb)) (free_tz L c)))

theorem start_free (st : Start A) (c : S) : (st.frame : FrameData S A).Free c :=
  ⟨free_one c, fun _ => freeOf2_lift c _, free_one c, free_one c, fun _ => free_io c _, fun _ => free_io c _,
    free_one c, free_one c, fun _ => free_io c _⟩

end

end Formalism.FourierDecayAlt.P.Fr4

namespace Formalism.FourierDecayAlt.P

theorem frame_free_of_new_position : Formalism.FourierDecayAlt.Fr.FrameFree := by
  intro A S _ _ _ _ _ _ r L st w c
  induction w with
  | nil => intro _; exact Fr4.start_free st c
  | cons l w ih =>
    intro hc
    rw [List.map_cons, List.mem_cons, not_or] at hc
    have h := ih hc.2
    show (if l.plus then (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt else (ofWord L st w).minus L l.intersection_update_fsHerm_neg_one l.pt).Free c
    split_ifs
    · exact Fr4.plus_free L hc.1 h l.pt
    · exact Fr4.minus_free L hc.1 h l.pt

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LastBlockDecay
namespace Formalism.FourierDecayAlt.P.PBK

open MeasureTheory Filter Topology
open scoped InnerProductSpace

noncomputable section

section dil

theorem map_mul_volume (ρ : ℂ) (hρ : ρ ≠ 0) :
    Measure.map (fun z : ℂ => ρ * z) volume = ENNReal.ofReal ((‖ρ‖ ^ 2)⁻¹) • (volume : Measure ℂ) := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ ρ) = ‖ρ‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Algebra.norm_complex_apply, Algebra.norm_apply]
    rfl
  have hne : LinearMap.det (LinearMap.mulLeft ℝ ρ) ≠ 0 := by
    rw [hdet]
    positivity
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ) hne
  rw [hdet, abs_of_nonneg (by positivity)] at h
  exact h

def mulEquiv (ρ : ℂ) (hρ : ρ ≠ 0) : ℂ ≃ᵐ ℂ := (Homeomorph.mulLeft₀ ρ hρ).toMeasurableEquiv

theorem mulEquiv_apply (ρ : ℂ) (hρ : ρ ≠ 0) (z : ℂ) : mulEquiv ρ hρ z = ρ * z := rfl

theorem map_mulEquiv (ρ : ℂ) (hρ : ρ ≠ 0) :
    Measure.map (mulEquiv ρ hρ) volume = ENNReal.ofReal ((‖ρ‖ ^ 2)⁻¹) • (volume : Measure ℂ) := by
  have h : ⇑(mulEquiv ρ hρ) = fun z => ρ * z := funext (mulEquiv_apply ρ hρ)
  rw [h]
  exact map_mul_volume ρ hρ

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_comp_mul_C (g : ℂ → E) (ρ : ℂ) (hρ : ρ ≠ 0) :
    ∫ z, g (ρ * z) = (‖ρ‖ ^ 2)⁻¹ • ∫ z, g z := by
  have h := integral_map_equiv (μ := (volume : Measure ℂ)) (mulEquiv ρ hρ) g
  rw [map_mulEquiv, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)] at h
  exact h.symm

theorem memLp_comp_mul {p : ENNReal} {f : ℂ → E} (hf : MemLp f p volume) (ρ : ℂ) (hρ : ρ ≠ 0) :
    MemLp (fun z => f (ρ * z)) p volume := by
  have h1 : MemLp f p (Measure.map (mulEquiv ρ hρ) volume) := by
    rw [map_mulEquiv]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact h1.comp_of_map (mulEquiv ρ hρ).measurable.aemeasurable

theorem integral_norm_dil_sq (f : ℂ → E) (ρ : ℂ) (hρ : ρ ≠ 0) :
    ∫ z, ‖‖ρ‖ • f (ρ * z)‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 := by
  have hρ0 : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have e : (fun z => ‖‖ρ‖ • f (ρ * z)‖ ^ 2) = fun z => ‖ρ‖ ^ 2 * ‖f (ρ * z)‖ ^ 2 := by
    funext z
    rw [norm_smul, norm_norm, mul_pow]
  rw [e, integral_const_mul, integral_comp_mul_C (fun z => ‖f z‖ ^ 2) ρ hρ, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ (by positivity), one_mul]

theorem memLp_dil {f : ℂ → E} (hf : MemLp f 2 volume) (ρ : ℂ) (hρ : ρ ≠ 0) :
    MemLp (fun z => ‖ρ‖ • f (ρ * z)) 2 volume :=
  (memLp_comp_mul hf ρ hρ).const_smul ‖ρ‖

theorem integrable_sq_of_memLp {u : ℂ → E} (hu : MemLp u 2 volume) : Integrable (fun z => ‖u z‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu

theorem tendsto_dil_cpt (g : ℂ → E) (hgc : Continuous g) (hgs : HasCompactSupport g) (ζ : ℂ) (hζ : ζ ≠ 0) :
    Tendsto (fun ρ : ℂ => ∫ z, ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2) (𝓝 ζ) (𝓝 0) := by
  obtain ⟨M, hM⟩ := hgc.bounded_above_of_compact_support hgs
  obtain ⟨R, hR⟩ := hgs.isCompact.isBounded.subset_closedBall (0 : ℂ)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hζ0 : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  have hzero : ∀ w : ℂ, max R 0 < ‖w‖ → g w = 0 := by
    intro w hw
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have h1 := hR hmem
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    linarith [le_max_left R 0]
  have hR0 : 0 ≤ max R 0 := le_max_right R 0
  have hr0 : 0 ≤ 2 * max R 0 / ‖ζ‖ := by positivity
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (F := fun ρ z => ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2)
    (f := fun z => ‖‖ζ‖ • g (ζ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2)
    (μ := volume) (l := 𝓝 ζ)
    ((Metric.closedBall (0 : ℂ) (2 * max R 0 / ‖ζ‖)).indicator fun _ => (3 * ‖ζ‖ * M) ^ 2) ?_ ?_ ?_ ?_
  · simpa using hlim
  · refine Filter.Eventually.of_forall fun ρ => ?_
    have hc : Continuous fun z => ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2 := by fun_prop
    exact hc.aestronglyMeasurable
  · have hball : Metric.ball ζ (‖ζ‖ / 2) ∈ 𝓝 ζ := Metric.ball_mem_nhds ζ (by positivity)
    filter_upwards [hball] with ρ hρ
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Metric.mem_ball, dist_eq_norm] at hρ
    have hρlo : ‖ζ‖ / 2 ≤ ‖ρ‖ := by
      have h1 := norm_sub_norm_le ζ ρ
      rw [norm_sub_rev] at h1
      linarith
    have hρhi : ‖ρ‖ ≤ 2 * ‖ζ‖ := by
      have h1 := norm_le_insert' ρ ζ
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) (2 * max R 0 / ‖ζ‖)
    · rw [Set.indicator_of_mem hz]
      have h1 : ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ≤ 3 * ‖ζ‖ * M := by
        calc ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖
            ≤ ‖‖ρ‖ • g (ρ * z)‖ + ‖‖ζ‖ • g (ζ * z)‖ := norm_sub_le _ _
          _ = ‖ρ‖ * ‖g (ρ * z)‖ + ‖ζ‖ * ‖g (ζ * z)‖ := by
              rw [norm_smul, norm_smul, norm_norm, norm_norm]
          _ ≤ 2 * ‖ζ‖ * M + ‖ζ‖ * M :=
              add_le_add (mul_le_mul hρhi (hM _) (norm_nonneg _) (by positivity))
                (mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))
          _ = 3 * ‖ζ‖ * M := by ring
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    · rw [Set.indicator_of_notMem hz]
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
      have e1 : g (ρ * z) = 0 := by
        apply hzero
        rw [norm_mul]
        calc max R 0 = ‖ζ‖ / 2 * (2 * max R 0 / ‖ζ‖) := by field_simp
          _ < ‖ζ‖ / 2 * ‖z‖ := by gcongr
          _ ≤ ‖ρ‖ * ‖z‖ := by gcongr
      have e2 : g (ζ * z) = 0 := by
        apply hzero
        rw [norm_mul]
        calc max R 0 ≤ ‖ζ‖ / 2 * (2 * max R 0 / ‖ζ‖) := by field_simp; rfl
          _ < ‖ζ‖ / 2 * ‖z‖ := by gcongr
          _ ≤ ‖ζ‖ * ‖z‖ := by gcongr; linarith
      rw [e1, e2]
      simp
  · exact (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  · refine Filter.Eventually.of_forall fun z => ?_
    have hc : Continuous fun ρ : ℂ => ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2 := by fun_prop
    exact hc.tendsto ζ

theorem tendsto_dil (f : ℂ → E) (hf : MemLp f 2 volume) (ζ : ℂ) (hζ : ζ ≠ 0) :
    Tendsto (fun ρ : ℂ => ∫ z, ‖‖ρ‖ • f (ρ * z) - ‖ζ‖ • f (ζ * z)‖ ^ 2) (𝓝 ζ) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hf' : MemLp f (ENNReal.ofReal 2) volume := by simpa using hf
  obtain ⟨g, hgs, hfg, hgc, hgm⟩ :=
    hf'.exists_hasCompactSupport_integral_rpow_sub_le two_pos (ε := ε / 12) (by positivity)
  have hfg' : ∫ z, ‖f z - g z‖ ^ 2 ≤ ε / 12 := by
    have e : (fun z => ‖f z - g z‖ ^ (2 : ℝ)) = fun z => ‖f z - g z‖ ^ 2 := by
      funext z
      exact Real.rpow_two _
    rw [e] at hfg
    exact hfg
  have hgm2 : MemLp g 2 volume := by simpa using hgm
  have hT := tendsto_dil_cpt g hgc hgs ζ hζ
  rw [Metric.tendsto_nhds] at hT
  filter_upwards [hT (ε / 6) (by positivity), eventually_ne_nhds hζ] with ρ hρT hρ0
  have hnn : ∀ (h : ℂ → ℝ), 0 ≤ ∫ z, ‖h z‖ ^ 2 := fun h => integral_nonneg fun _ => by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => by positivity)] at hρT ⊢
  have h3 : ∀ a b c : E, ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
    intro a b c
    have h1 := norm_add₃_le (a := a) (b := b) (c := c)
    have h2 : ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖a‖ - ‖c‖)]
  have hdfg : MemLp (fun z => f z - g z) 2 volume := hf.sub hgm2
  have hdgf : MemLp (fun z => g z - f z) 2 volume := hgm2.sub hf
  have iA := integrable_sq_of_memLp (memLp_dil hdfg ρ hρ0)
  have iB := integrable_sq_of_memLp ((memLp_dil hgm2 ρ hρ0).sub (memLp_dil hgm2 ζ hζ))
  have iC := integrable_sq_of_memLp (memLp_dil hdgf ζ hζ)
  have iL := integrable_sq_of_memLp ((memLp_dil hf ρ hρ0).sub (memLp_dil hf ζ hζ))
  have hA := integral_norm_dil_sq (fun w => f w - g w) ρ hρ0
  have hC := integral_norm_dil_sq (fun w => g w - f w) ζ hζ
  have hgf : ∫ z, ‖g z - f z‖ ^ 2 = ∫ z, ‖f z - g z‖ ^ 2 := by
    congr 1
    funext z
    rw [norm_sub_rev]
  have hmono : ∫ z, ‖‖ρ‖ • f (ρ * z) - ‖ζ‖ • f (ζ * z)‖ ^ 2 ≤
      ∫ z, 3 * (‖‖ρ‖ • (f (ρ * z) - g (ρ * z))‖ ^ 2 +
        ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2 + ‖‖ζ‖ • (g (ζ * z) - f (ζ * z))‖ ^ 2) := by
    refine integral_mono iL (((iA.add iB).add iC).const_mul 3) fun z => ?_
    have e : ‖ρ‖ • f (ρ * z) - ‖ζ‖ • f (ζ * z) = ‖ρ‖ • (f (ρ * z) - g (ρ * z)) +
        (‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)) + ‖ζ‖ • (g (ζ * z) - f (ζ * z)) := by
      rw [smul_sub, smul_sub]
      abel
    simp only
    rw [e]
    exact h3 _ _ _
  have hs1 : ∫ z, (‖‖ρ‖ • (f (ρ * z) - g (ρ * z))‖ ^ 2 +
        ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2 + ‖‖ζ‖ • (g (ζ * z) - f (ζ * z))‖ ^ 2) =
      (∫ z, (‖‖ρ‖ • (f (ρ * z) - g (ρ * z))‖ ^ 2 + ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2)) +
        ∫ z, ‖‖ζ‖ • (g (ζ * z) - f (ζ * z))‖ ^ 2 :=
    integral_add (iA.add iB) iC
  have hs2 : ∫ z, (‖‖ρ‖ • (f (ρ * z) - g (ρ * z))‖ ^ 2 + ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2) =
      (∫ z, ‖‖ρ‖ • (f (ρ * z) - g (ρ * z))‖ ^ 2) + ∫ z, ‖‖ρ‖ • g (ρ * z) - ‖ζ‖ • g (ζ * z)‖ ^ 2 :=
    integral_add iA iB
  rw [integral_const_mul, hs1, hs2] at hmono
  rw [hA, hC, hgf] at hmono
  linarith

theorem tendsto_inner_dil {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (b c : ℂ → H)
    (hb : MemLp b 2 volume) (hc : MemLp c 2 volume) (ζ : ℂ) (hζ : ζ ≠ 0) :
    Tendsto (fun ρ : ℂ => ∫ z, ‖⟪b z, ((‖ρ‖ : ℝ) : ℂ) • c (ρ * z)⟫_ℂ - ⟪b z, ((‖ζ‖ : ℝ) : ℂ) • c (ζ * z)⟫_ℂ‖)
      (𝓝 ζ) (𝓝 0) := by
  have hT := tendsto_dil c hc ζ hζ
  set K : ℝ := (∫ z, ‖b z‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
  have hG : Tendsto (fun ρ : ℂ => K * (∫ z, ‖‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)‖ ^ 2) ^ (1 / (2 : ℝ)))
      (𝓝 ζ) (𝓝 0) := by
    have h1 := ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).tendsto 0).comp hT
    rw [Real.zero_rpow (by norm_num)] at h1
    simpa using h1.const_mul K
  refine squeeze_zero' (Filter.Eventually.of_forall fun ρ => integral_nonneg fun _ => norm_nonneg _) ?_ hG
  filter_upwards [eventually_ne_nhds hζ] with ρ hρ0
  have hb2 : MemLp b (ENNReal.ofReal 2) volume := by simpa using hb
  have hd : MemLp (fun z => ‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)) 2 volume :=
    (memLp_dil hc ρ hρ0).sub (memLp_dil hc ζ hζ)
  have hd2 : MemLp (fun z => ‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)) (ENNReal.ofReal 2) volume := by
    simpa using hd
  have hint : Integrable (fun z => ‖b z‖ * ‖‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)‖) volume :=
    hb.norm.integrable_mul hd.norm
  have hpt : ∀ z, ‖⟪b z, ((‖ρ‖ : ℝ) : ℂ) • c (ρ * z)⟫_ℂ - ⟪b z, ((‖ζ‖ : ℝ) : ℂ) • c (ζ * z)⟫_ℂ‖ ≤
      ‖b z‖ * ‖‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)‖ := by
    intro z
    rw [← inner_sub_right, Complex.coe_smul, Complex.coe_smul]
    exact norm_inner_le_norm _ _
  calc ∫ z, ‖⟪b z, ((‖ρ‖ : ℝ) : ℂ) • c (ρ * z)⟫_ℂ - ⟪b z, ((‖ζ‖ : ℝ) : ℂ) • c (ζ * z)⟫_ℂ‖
      ≤ ∫ z, ‖b z‖ * ‖‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)‖ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hint
          (Filter.Eventually.of_forall hpt)
    _ ≤ K * (∫ z, ‖‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hb2 hd2
    _ = K * (∫ z, ‖‖ρ‖ • c (ρ * z) - ‖ζ‖ • c (ζ * z)‖ ^ 2) ^ (1 / (2 : ℝ)) := by
        congr 2
        congr 1
        funext z
        exact Real.rpow_two _

theorem tendsto_dil_real (ab : ℂ → ℝ) (hab : MemLp ab 2 volume) :
    Tendsto (fun ρ : ℂ => ∫ z, (‖ρ‖ * ab (ρ * z) - ab z) ^ 2) (𝓝 1) (𝓝 0) := by
  have h := tendsto_dil ab hab 1 one_ne_zero
  refine h.congr fun ρ => ?_
  congr 1
  funext z
  rw [Real.norm_eq_abs, sq_abs, norm_one, one_smul, one_mul, smul_eq_mul]

end dil

end

end Formalism.FourierDecayAlt.P.PBK
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.LatticeSummability
open MeasureTheory Set Finset Function

noncomputable section

namespace Formalism.FourierDecayAlt.P.LatticeSummability

open Formalism.FourierDecayAlt.crystallineComparison

theorem mfac_nonneg (K : ℕ) {L : ℝ} (hL : 0 ≤ L) (a : ℝ) (ha : 0 ≤ a) : 0 ≤ mfac K L a := by
  unfold mfac
  split_ifs
  · exact zero_le_one
  · exact le_min zero_le_one (by positivity)

theorem mfac_anti (K : ℕ) {L : ℝ} (hL : 0 < L) {b b' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b') :
    mfac K L b' ≤ mfac K L b := by
  unfold mfac
  by_cases hb0 : b = 0
  · rw [if_pos hb0]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hb'0 : b' ≠ 0 := by linarith
    rw [if_neg hb0, if_neg hb'0]
    refine min_le_min le_rfl (pow_le_pow_left₀ (div_nonneg hL.le (by linarith)) ?_ K)
    exact div_le_div_of_nonneg_left hL.le hbpos hbb

end Formalism.FourierDecayAlt.P.LatticeSummability
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChebyshevToThreshold
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J

open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.Jx10

theorem pull {α X : Type} [DecidableEq X] (η : α → X) (F : Finset α) (k : X → X → ℂ)
    (h : A5.IsPSD (F.image η) k) : A5.IsPSD F (fun x y => k (η x) (η y)) := by
  unfold Formalism.FourierDecayAlt.A5.IsPSD at h ⊢
  intro a
  show (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y)).im = 0 ∧
    0 ≤ (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y)).re
  set b : X → ℂ := fun u => ∑ z ∈ F.filter (fun z => η z = u), a z with hb
  have hmaps : ∀ x ∈ F, η x ∈ F.image η := fun x hx => Finset.mem_image_of_mem η hx
  have rhs : ∀ u v, b u * conj (b v) * k u v =
      ∑ x ∈ F.filter (fun z => η z = u), ∑ y ∈ F.filter (fun z => η z = v),
        a x * conj (a y) * k (η x) (η y) := by
    intro u v
    simp only [hb]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y hy => ?_)
    have h1 := (Finset.mem_filter.mp hx).2
    have h2 := (Finset.mem_filter.mp hy).2
    rw [h1, h2] <;> ring
  have key : (∑ x ∈ F, ∑ y ∈ F, a x * conj (a y) * k (η x) (η y)) =
      ∑ u ∈ F.image η, ∑ v ∈ F.image η, b u * conj (b v) * k u v := by
    simp_rw [rhs]
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_fiberwise_of_maps_to hmaps]
  rw [key]
  exact h b

theorem inter_of_module (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule ℤ E)
    (hL : ∀ (a : 𝓞 (maximalRealSubfield E)) (t : E), t ∈ L →
      algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L) (t : E)
    (h : ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal → t ∈ S6.locAt E P L) : t ∈ L := by
  by_contra ht
  let I : Ideal (𝓞 (maximalRealSubfield E)) :=
    { carrier := {a | algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add (f := _), add_mul] at ha hb ⊢
        exact L.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c {a} ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, mul_assoc] at ha ⊢
        exact hL c _ ha }
  have hI : I ≠ ⊤ := by
    intro hI
    apply ht
    have h1 : (1 : 𝓞 (maximalRealSubfield E)) ∈ I := by
      rw [hI]
      exact Submodule.mem_top
    have h2 : algebraMap (𝓞 (maximalRealSubfield E)) E 1 * t ∈ L := h1
    simpa using h2
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨a, haP, haL⟩ := h P hP
  exact haP (hIP haL)

end Formalism.FourierDecayAlt.P.Jx10

namespace Formalism.FourierDecayAlt.P


open Classical in
theorem local_kernel_psd : Formalism.FourierDecayAlt.J.LocalKernelPSD := by
  intro hag hgram K _ _ _ R ψ hLD α η Y
  rw [(hag α Y _).1, ← (hag α Y _).2]
  exact Jx10.pull η Y (A5.Kp R ψ) (hgram K R ψ hLD (Y.image η))

theorem intersection_of_local : Formalism.FourierDecayAlt.J.IntersectionOfLocal := by
  intro E _ _ _ L hL t
  obtain ⟨hL1, -⟩ := hL
  constructor
  · intro ht P hP
    unfold Formalism.FourierDecayAlt.S6.locAt
    rw [Set.mem_setOf_eq]
    refine ⟨1, fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1), ?_⟩
    rw [map_one, one_mul]
    exact ht
  · intro h
    exact Jx10.inter_of_module E L hL1 t h

theorem lattice_of_local : Formalism.FourierDecayAlt.J.LatticeOfLocal := by
  intro E _ _ _ L hL Q _ pl M hcov hM
  have hint := intersection_of_local E L hL
  ext t
  rw [AddSubgroup.mem_iInf, Submodule.mem_toAddSubgroup, hint]
  constructor
  · intro h p
    rw [hM]
    intro P _ hP
    exact h P hP
  · intro h P hP
    obtain ⟨p, hp⟩ := hcov P hP
    exact (hM p t).mp (h p) P hp hP

theorem pull_lattice_typed : Formalism.FourierDecayAlt.J.PullLatticeTyped := by
  intro hT E _ _ _ g ν s hg hpd P hP hgP K _ o σ hσ R u α ψ η Θ hR hu t
  rw [hT E g ν s hg hpd P hP hgP K o σ hσ t]
  show (u : K × K) * (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) t ∈ R ↔ _
  rw [hR, hu]
  have e : (((g : K)⁻¹, (-1) ^ s * (g : K)⁻¹) : K × K) *
      (σ.prod (σ.comp (IsCMField.complexConj E).toAlgHom.toRingHom)) t =
      (σ t / (g : K), (-1) ^ s * σ (IsCMField.complexConj E t) / (g : K)) := by
    ext
    · simp [div_eq_mul_inv, mul_comm]
    · simp [div_eq_mul_inv]; ring
  rw [e]

end Formalism.FourierDecayAlt.P
end
