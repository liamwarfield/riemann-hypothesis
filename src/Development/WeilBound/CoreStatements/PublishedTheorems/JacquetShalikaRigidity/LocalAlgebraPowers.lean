module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.FiniteInfinitePlaceProduct

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LocalAlgebraPowers
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LocalAlgebraPowers

theorem pad_self {k : ℕ} (l : Fin k → ℤ) : pad k l = l := by
  funext a
  simp [pad, a.2]

theorem rhoPair_pad {m k : ℕ} (hkm : k ≤ m) (l : Fin k → ℤ) :
    rhoPair (pad m l) = rhoPair l + ((m : ℤ) - k) * ∑ i, l i := by
  obtain ⟨d, rfl⟩ : ∃ d, m = k + d := ⟨m - k, by omega⟩
  simp only [rhoPair, pad, Fin.sum_univ_add, Fin.coe_castAdd, Fin.coe_natAdd, Fin.is_lt, dif_pos]
  simp only [show ∀ j : Fin d, ¬ (k + (j : ℕ) < k) from fun j => by omega, dif_neg, not_false_eq_true,
    mul_zero, Finset.sum_const_zero, add_zero]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

theorem antitone_pad {m k : ℕ} (hkm : k < m) (l : Fin k → ℤ) :
    Antitone (pad m l) ↔ Antitone l ∧ ∀ i, 0 ≤ l i := by
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have := h (show (⟨i, by omega⟩ : Fin m) ≤ ⟨j, by omega⟩ from hij)
      simpa [pad, i.isLt, j.isLt] using this
    · have := h (show (⟨i, by omega⟩ : Fin m) ≤ ⟨k, hkm⟩ from Fin.mk_le_mk.mpr i.isLt.le)
      simpa [pad, i.isLt] using this
  · rintro ⟨hl, h0⟩ a b hab
    have hab' : (a : ℕ) ≤ b := hab
    by_cases hb : (b : ℕ) < k
    · have ha : (a : ℕ) < k := lt_of_le_of_lt hab' hb
      simp only [pad, ha, hb, dif_pos]
      exact hl (Fin.mk_le_mk.mpr hab')
    · simp only [pad, hb, dif_neg, not_false_eq_true]
      split_ifs
      · exact h0 _
      · exact le_rfl

theorem antitone_pad_iff {m k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) (l : Fin k → ℤ) (hl : Antitone l)
    (h : k < m ∨ ∀ i : Fin k, (i : ℕ) + 1 = k → 0 ≤ l i) : Antitone (pad m l) ↔ ∀ i, 0 ≤ l i := by
  rcases lt_or_eq_of_le hkm with hlt | heq
  · rw [antitone_pad hlt l]
    simp [hl]
  · subst heq
    have h' := h.resolve_left (lt_irrefl _)
    have hall : ∀ i, 0 ≤ l i := by
      intro i
      have hlast : 0 ≤ l ⟨k - 1, by omega⟩ := h' _ (by simp; omega)
      exact le_trans hlast (hl (Fin.mk_le_mk.mpr (by omega)))
    rw [pad_self]
    exact ⟨fun _ => hall, fun _ => hl⟩

variable {E : Type} [Field E] [NumberField E] {S : Finset (Pl E)}

theorem nq_pos (w : Off E S) : 0 < nq w := by
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [nq, Ideal.absNorm_eq_zero_iff] at h
  exact w.1.ne_bot h

theorem qF_eq' (w : Off E S) : qF (w.1.adicCompletion E) = nq w := PositivityTheory.JacquetShalikaLocal.SatakeEigenvalues.qF_eq w.1

theorem sqrtQ_eq (w : Off E S) :
    sqrtQ (w.1.adicCompletion E) = Complex.exp ((Real.log (nq w) / 2 : ℝ)) := by
  have hpos : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  rw [sqrtQ, qF_eq', ← Complex.ofReal_exp]
  norm_cast
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]
  congr 1
  ring

theorem conj_sqrtQ_zpow (w : Off E S) (j : ℤ) :
    conj (sqrtQ (w.1.adicCompletion E) ^ j) = sqrtQ (w.1.adicCompletion E) ^ j := by
  rw [map_zpow₀]
  congr 1
  simp [sqrtQ, Complex.conj_ofReal]

theorem cast_eq_exp (w : Off E S) : (nq w : ℂ) = Complex.exp (Real.log (nq w)) := by
  have hpos : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_exp, Real.exp_log hpos]

theorem cpow_eq (w : Off E S) (z : ℂ) : (nq w : ℂ) ^ z = Complex.exp (Real.log (nq w) * z) := by
  have hpos : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (nq_pos w).ne'), ← Complex.ofReal_natCast,
    ← Complex.ofReal_log hpos.le]

theorem zpow_eq (w : Off E S) (j : ℤ) : (nq w : ℂ) ^ j = Complex.exp (j * Real.log (nq w)) := by
  rw [cast_eq_exp, ← Complex.exp_int_mul]

theorem sqrt_zpow_eq (w : Off E S) (j : ℤ) :
    sqrtQ (w.1.adicCompletion E) ^ j = Complex.exp (j * (Real.log (nq w) / 2 : ℝ)) := by
  rw [sqrtQ_eq, ← Complex.exp_int_mul]

theorem rpow_cpow_eq (w : Off E S) (N : ℤ) (z : ℂ) :
    ((((nq w : ℝ) ^ N : ℝ)) : ℂ) ^ z = Complex.exp ((N * Real.log (nq w) : ℝ) * z) := by
  have hq : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  have hx : (0 : ℝ) < (nq w : ℝ) ^ N := zpow_pos hq N
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le, Real.log_zpow]

theorem local_inputs_from_literature {m k : ℕ} (q : ℕ) (α : Fin m → ℂˣ) (β : Fin k → ℂˣ) (s : ℂ) (l : Fin k → ℤ) :
    loc q α β s l = loc q α β 0 l * (q : ℂ) ^ (-s * ((∑ i, l i : ℤ) : ℂ)) := by
  unfold loc
  split_ifs <;> simp

end LocalAlgebraPowers

open LocalAlgebraPowers in
theorem localHeckeAlgebra_statement : LocalHeckeAlgebra := by
  intro E _ _ S m k α α' w χ hχ hk hkm
  have hψ := hχ.1
  have hq : (0 : ℝ) < nq w := by exact_mod_cast nq_pos w
  refine ⟨?_, fun l => ⟨fun s => ?_, fun hcase => ?_, fun hneg => ?_⟩⟩
  · have hp : pad m (0 : Fin k → ℤ) = 0 := by
      funext a
      simp [pad]
    have hA : Antitone (0 : Fin k → ℤ) ∧ ∀ i, 0 ≤ (0 : Fin k → ℤ) i :=
      ⟨fun _ _ _ => le_rfl, fun _ => le_rfl⟩
    simp only [aLoc, loc, if_pos hA, hp, halfModulus_zero, schur_zero, map_one, Pi.zero_apply,
      Finset.sum_const_zero, Int.cast_zero, mul_zero, neg_zero, Complex.cpow_zero, one_pow, mul_one]
    simp [hA.1]
  · have key : ∀ a b c d g : ℂ, a + 2 * b + c + d = g → ∀ L : ℂ,
        Complex.exp a * (Complex.exp b ^ 2 * Complex.exp c * L * Complex.exp d) = L * Complex.exp g := by
      intro a b c d g h L
      rw [← h, Complex.exp_add, Complex.exp_add, Complex.exp_add, two_mul, Complex.exp_add]
      ring
    rw [local_inputs_from_literature]
    simp only [aLoc, halfModulus_eq]
    rw [rpow_cpow_eq, sqrt_zpow_eq, zpow_eq, cpow_eq, cpow_eq]
    refine key _ _ _ _ _ ?_ _
    push_cast
    ring
  · rw [sphericalWhittaker_torusPow hψ, sphericalWhittaker_torusPow hψ]
    by_cases hA : Antitone l ∧ ∀ i, 0 ≤ l i
    · have hpA : Antitone (pad m l) := (antitone_pad_iff hk hkm l hA.1 hcase).mpr hA.2
      have hfac : halfModulus (w.1.adicCompletion E) (pad m l) * conj (halfModulus (w.1.adicCompletion E) l) =
          halfModulus (w.1.adicCompletion E) l ^ 2 *
            (nq w : ℂ) ^ (-(((m : ℂ) - k) / 2) * ((∑ i, l i : ℤ) : ℂ)) := by
        rw [halfModulus_eq, halfModulus_eq, rhoPair_pad hkm, conj_sqrtQ_zpow, sqrt_zpow_eq, sqrt_zpow_eq,
          cpow_eq, sq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [if_pos hpA, if_pos hA.1]
      simp only [aLoc, loc, if_pos hA, neg_zero, zero_mul, Complex.cpow_zero, mul_one, map_mul]
      linear_combination ((evalAt (α w)) (schur (pad m l)) * conj ((evalAt (α' w)) (schur l))) * hfac
    · have hR : aLoc α α' w l = 0 := by
        simp only [aLoc, loc, if_neg hA, mul_zero]
      rw [hR]
      by_cases hl : Antitone l
      · have hpA : ¬ Antitone (pad m l) := fun h => hA ⟨hl, (antitone_pad_iff hk hkm l hl hcase).mp h⟩
        rw [if_neg hpA, zero_mul]
      · rw [if_neg hl, map_zero, mul_zero]
  · have hA : ¬ (Antitone l ∧ ∀ i, 0 ≤ l i) := by
      rintro ⟨-, h⟩
      obtain ⟨i, hi⟩ := hneg
      exact absurd (h i) (not_le.mpr hi)
    simp only [aLoc, loc, if_neg hA, mul_zero]

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.MeasureInverseInduction
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace MeasureInverseInduction

set_option synthInstance.maxHeartbeats 400000

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem countGL : Countable (GL (Fin k) E) := by
  haveI : Countable E := GroundTheory.Global.countable_numberField E
  haveI : Countable (Matrix (Fin k) (Fin k) E) := inferInstanceAs (Countable (Fin k → Fin k → E))
  exact Units.val_injective.countable

theorem blk_ratGL {j : ℕ} {γ : GL (Fin k) E} (h : GlobalTheory j γ) : GlobalTheory j (ratGL E k γ) := by
  intro i c hic
  change algebraMap E (Ad E) (γ.val i c) = _
  rw [h i c hic, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem lint_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) (F : GA E k → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ h, F h ∂nuG Γ d = ∑' γ : Γ, ∫⁻ h, F (ratGL E k γ * h) ∂nuD E k d := by
  rw [nuG, lintegral_sum_measure]
  exact tsum_congr fun γ => lintegral_map hF (measurable_const_mul _)

theorem inv_step (ν : Measure (GA E k)) (hinvν : Measure.map (fun h => h⁻¹) ν = ν) (g : GA E k)
    (hc : ∀ F : GA E k → ℝ≥0∞, Measurable F → ∫⁻ h, F (g * h * g⁻¹) ∂ν = ∫⁻ h, F h ∂ν)
    (f : GA E k → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ h, f (g * h)⁻¹ ∂ν = ∫⁻ h, f (g⁻¹ * h) ∂ν := by
  have hG : Measurable fun x : GA E k => f (g⁻¹ * (g * x * g⁻¹)) :=
    hf.comp ((measurable_const_mul _).comp ((measurable_mul_const _).comp (measurable_const_mul _)))
  calc ∫⁻ h, f (g * h)⁻¹ ∂ν = ∫⁻ h, f (g⁻¹ * (g * h⁻¹ * g⁻¹)) ∂ν :=
        lintegral_congr fun h => by congr 1; group
    _ = ∫⁻ x, f (g⁻¹ * (g * x * g⁻¹)) ∂Measure.map (fun h => h⁻¹) ν := (lintegral_map hG measurable_inv).symm
    _ = ∫⁻ x, f (g⁻¹ * (g * x * g⁻¹)) ∂ν := by rw [hinvν]
    _ = ∫⁻ x, f (g⁻¹ * x) ∂ν := hc (fun y => f (g⁻¹ * y)) (hf.comp (measurable_const_mul _))

def invE (Γ : Set (GL (Fin k) E)) (hΓ : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) : Γ ≃ Γ where
  toFun γ := ⟨γ.1⁻¹, hΓ _ γ.2⟩
  invFun γ := ⟨γ.1⁻¹, hΓ _ γ.2⟩
  left_inv γ := Subtype.ext (inv_inv γ.1)
  right_inv γ := Subtype.ext (inv_inv γ.1)

theorem inv_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ)
    (hinvν : Measure.map (fun h => h⁻¹) (nuD E k d) = nuD E k d)
    (hconj : ∀ γ ∈ Γ, ∀ F : GA E k → ℝ≥0∞, Measurable F →
      ∫⁻ h, F (ratGL E k γ * h * (ratGL E k γ)⁻¹) ∂nuD E k d = ∫⁻ h, F h ∂nuD E k d)
    (hΓ : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) :
    Measure.map (fun h => h⁻¹) (nuG Γ d) = nuG Γ d := by
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  calc ∫⁻ h, f h ∂Measure.map (fun h => h⁻¹) (nuG Γ d) = ∫⁻ h, f h⁻¹ ∂nuG Γ d :=
        lintegral_map hf measurable_inv
    _ = ∑' γ : Γ, ∫⁻ h, f (ratGL E k γ * h)⁻¹ ∂nuD E k d := lint_nuG Γ d _ (hf.comp measurable_inv)
    _ = ∑' γ : Γ, ∫⁻ h, f (ratGL E k γ.1⁻¹ * h) ∂nuD E k d := tsum_congr fun γ => by
        rw [inv_step _ hinvν _ (hconj γ.1 γ.2) f hf, map_inv (ratGL E k) γ.1]
    _ = ∑' γ : Γ, ∫⁻ h, f (ratGL E k γ * h) ∂nuD E k d :=
        (invE Γ hΓ).tsum_eq (fun γ : Γ => ∫⁻ h, f (ratGL E k γ * h) ∂nuD E k d)
    _ = ∫⁻ h, f h ∂nuG Γ d := (lint_nuG Γ d f hf).symm

theorem sf_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) [SFinite (nuD E k d)] : SFinite (nuG Γ d) := by
  haveI : Countable (GL (Fin k) E) := countGL
  rw [nuG]; infer_instance

theorem ae_nuG (Γ : Set (GL (Fin k) E)) (d : ℕ) (hae : ∀ᵐ u ∂nuD E k d, UU (k - d) u) :
    ∀ᵐ h ∂nuG Γ d, ∃ γ u, γ ∈ Γ ∧ UU (k - d) u ∧ h = ratGL E k γ * u := by
  haveI : Countable (GL (Fin k) E) := countGL
  rw [ae_iff] at hae ⊢
  rw [nuG, Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero]
  intro γ
  rw [(measurableEmbedding_mulLeft (ratGL E k γ)).map_apply]
  exact measure_mono_null (t := {u | ¬ UU (k - d) u})
    (fun u hu hUU => hu ⟨γ.1, u, γ.2, hUU, rfl⟩) hae

theorem nuD_ne_zero (hsf : ∀ d ≤ k, SFinite (nuD E k d)) : ∀ d ≤ k, nuD E k d ≠ 0 := by
  intro d
  induction d with
  | zero =>
    intro _ h
    have h1 := congrArg (fun μ : Measure (GA E k) => μ Set.univ) h
    simp [nuD] at h1
  | succ d ih =>
    intro hd h
    haveI := hsf d (by omega)
    have hm : Measurable fun p : (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1)) → Ad E) × GA E k => blkU p.1 * p.2 :=
      (((continuous_posU (isNil_blk k _ _)).comp continuous_fst).mul continuous_snd).measurable
    have h3 := (Measure.map_eq_zero_iff hm.aemeasurable).mp h
    have h2 := congrArg (fun μ => μ (vecDomain E (UnipotentBlockColumnIndex k (k - (d + 1)) (k - (d + 1))) ×ˢ Set.univ)) h3
    simp only [Measure.prod_prod, vecMeasure_vecDomain, one_mul, Measure.coe_zero, Pi.zero_apply] at h2
    exact ih (by omega) (Measure.measure_univ_eq_zero.mp h2)

variable [_root_.NumberField.IsTotallyComplex E]

theorem main_nuG (hD0 : D0) (hN1 : N1) (Γ : Set (GL (Fin k) E)) (d : ℕ) (hd : d ≤ k)
    (hinv : ∀ γ ∈ Γ, γ⁻¹ ∈ Γ) (hblk : ∀ γ ∈ Γ, GlobalTheory (k - d) γ) :
    SFinite (nuG Γ d) ∧ Measure.map (fun h => h⁻¹) (nuG Γ d) = nuG Γ d ∧
      ∀ᵐ h ∂nuG Γ d, ∃ γ u, γ ∈ Γ ∧ UU (k - d) u ∧ h = ratGL E k γ * u := by
  obtain ⟨hsf, hae, hinvν, -, hconj⟩ := hN1 E k d hd
  haveI := hsf
  refine ⟨sf_nuG Γ d, inv_nuG Γ d hinvν (fun γ hγ F hF => ?_) hinv, ae_nuG Γ d hae⟩
  rw [hconj _ (blk_ratGL (hblk γ hγ)) F hF, (hD0 E k).2.2.2.1 γ, inv_one, ENNReal.ofReal_one, one_pow, one_mul]

end MeasureInverseInduction

open MeasureInverseInduction in
set_option synthInstance.maxHeartbeats 400000 in
theorem galois_fixed_adelic_matrices_descend : D0 → N0 → N1 → N3 := by
  intro hD0 hN0 hN1 E _ _ _ k
  have hP : ∀ m < k, SFinite (nuP E k m) ∧ Measure.map (fun h => h⁻¹) (nuP E k m) = nuP E k m ∧
      ∀ᵐ h ∂nuP E k m, ∃ γ u, IsMir m γ ∧ UU (m + 1) u ∧ h = ratGL E k γ * u := by
    intro m hm
    have hN := hN0 E k (m + 1) (by omega) (by omega)
    have h6 : ∀ γ : GL (Fin k) E, IsMir m γ → IsMir m γ⁻¹ ∧ GlobalTheory (m + 1) γ := by
      simpa only [Nat.add_sub_cancel] using hN.2.2.2.2.2.1
    have e : k - (k - (m + 1)) = m + 1 := by omega
    obtain ⟨h1, h2, h3⟩ := main_nuG hD0 hN1 {γ | IsMir m γ} (k - (m + 1)) (by omega)
      (fun γ hγ => (h6 γ hγ).1) (fun γ hγ => by rw [e]; exact (h6 γ hγ).2)
    refine ⟨h1, h2, ?_⟩
    filter_upwards [h3] with h ⟨γ, u, hγ, hu, hh⟩
    exact ⟨γ, u, hγ, by rwa [e] at hu, hh⟩
  have hB : ∀ j ≤ k, SFinite (nuB E k j) ∧ Measure.map (fun h => h⁻¹) (nuB E k j) = nuB E k j ∧
      ∀ᵐ h ∂nuB E k j, ∃ γ u, GlobalTheory j γ ∧ UU j u ∧ h = ratGL E k γ * u := by
    intro j hj
    have hinv : ∀ γ : GL (Fin k) E, GlobalTheory j γ → GlobalTheory j γ⁻¹ := by
      intro γ hγ
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        have : γ = 1 := Units.ext (Matrix.ext fun i c => hγ i c (Or.inl (Nat.zero_le _)))
        subst this
        rw [inv_one]
        exact hγ
      · exact (hN0 E k j hpos hj).2.2.2.1 γ hγ
    have e : k - (k - j) = j := by omega
    obtain ⟨h1, h2, h3⟩ := main_nuG hD0 hN1 {γ | GlobalTheory j γ} (k - j) (by omega)
      (fun γ hγ => hinv γ hγ) (fun γ hγ => by rw [e]; exact hγ)
    refine ⟨h1, h2, ?_⟩
    filter_upwards [h3] with h ⟨γ, u, hγ, hu, hh⟩
    exact ⟨γ, u, hγ, by rwa [e] at hu, hh⟩
  have hall : ∀ γ : GL (Fin k) E, γ ∈ {γ : GL (Fin k) E | GlobalTheory k γ} := fun γ i c h =>
    absurd h (not_or.mpr ⟨not_le.mpr i.isLt, not_le.mpr c.isLt⟩)
  have hK : ∀ F : GA E k → ℝ≥0∞, Measurable F → ∫⁻ h, F h ∂nuB E k k = ∑' γ : GL (Fin k) E, F (ratGL E k γ) := by
    intro F hF
    rw [nuB, lint_nuG _ _ F hF, Nat.sub_self]
    simp only [nuD, lintegral_dirac, mul_one]
    exact (Equiv.subtypeUnivEquiv hall).tsum_eq (fun γ => F (ratGL E k γ))
  have h4 : 1 ≤ k → (∀ᵐ h ∂nuP E k 0, UU 0 h) ∧ nuP E k 0 ≠ 0 := by
    intro hk
    obtain ⟨-, -, hae⟩ := hP 0 (by omega)
    refine ⟨?_, ?_⟩
    · filter_upwards [hae] with h ⟨γ, u, hγ, hu, hh⟩
      have : γ = 1 := Units.ext (Matrix.ext fun i c => hγ i c (Or.inl (Nat.zero_le _)))
      rw [hh, this, map_one, one_mul]
      exact ⟨hu.1, hu.2.1, fun i c hc => absurd hc (Nat.not_lt_zero _)⟩
    · intro h0
      haveI : Countable (GL (Fin k) E) := countGL
      have h1 : nuP E k 0 Set.univ = 0 := by simp [h0]
      rw [nuP, nuG, Measure.sum_apply_of_countable, ENNReal.tsum_eq_zero] at h1
      have h2 := h1 ⟨1, show IsMir 0 (1 : GL (Fin k) E) from fun i c _ => rfl⟩
      rw [(measurableEmbedding_mulLeft _).map_apply, Set.preimage_univ, Measure.measure_univ_eq_zero] at h2
      exact nuD_ne_zero (fun d hd => (hN1 E k d hd).1) _ (by omega) h2
  exact ⟨hP, hB, hK, h4⟩

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LogNormEstimates
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LogNormEstimates

theorem log_le {D a b : ℝ} (hD : 0 < D) (ha : 0 < a) (h1 : a ≤ D) (h2 : D ≤ b) :
    |Real.log D| ≤ |Real.log a| + |Real.log b| := by
  have l1 := Real.log_le_log ha h1
  have l2 := Real.log_le_log hD h2
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log a), abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b), abs_nonneg (Real.log a)]

theorem norm_le {p : ℂ} {D a b : ℝ} (hD : 0 < D) (ha : 0 < a) (h : p ≠ 0 → a ≤ D ∧ D ≤ b) (z z₀ : ℂ) :
    ‖p * (D : ℂ) ^ z‖ ≤ ‖p * (D : ℂ) ^ z₀‖ * Real.exp ((|Real.log a| + |Real.log b|) * |z.re - z₀.re|) := by
  by_cases hp : p = 0
  · simp [hp]
  obtain ⟨h1, h2⟩ := h hp
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  have e : D ^ z.re = D ^ z₀.re * D ^ (z.re - z₀.re) := by
    rw [← Real.rpow_add hD]; congr 1; ring
  rw [e, ← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Real.rpow_def_of_pos hD]
  apply Real.exp_le_exp.2
  calc Real.log D * (z.re - z₀.re) ≤ |Real.log D * (z.re - z₀.re)| := le_abs_self _
    _ = |Real.log D| * |z.re - z₀.re| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (log_le hD ha h1 h2) (abs_nonneg _)

theorem re_eq (p : ℂ) {D : ℝ} (hD : 0 < D) (σ u : ℝ) :
    (p * (D : ℂ) ^ ((σ : ℂ) + u * Complex.I)).re = D ^ σ * (p * (D : ℂ) ^ ((u : ℂ) * Complex.I)).re := by
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hD.ne'), ← Complex.ofReal_cpow hD.le σ,
    show p * (((D ^ σ : ℝ) : ℂ) * (D : ℂ) ^ ((u : ℂ) * Complex.I)) =
      ((D ^ σ : ℝ) : ℂ) * (p * (D : ℂ) ^ ((u : ℂ) * Complex.I)) by ring, Complex.re_ofReal_mul]

set_option synthInstance.maxHeartbeats 400000 in
theorem msc {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ} :
    MeasurableSingletonClass (GA E k) := inferInstance

end LogNormEstimates

theorem log_norm_estimate_of_Q : Q1 → D0 → N3 → C0 → D1 := by
  intro hQ1 hD0 hN3 hC0
  unfold D1 ForMu
  intro E _ _ _ k μ _ hk β hβ S P u z₀ hPc hPinv hP1 hpos hint
  obtain ⟨hDpos, hDmul, hDc, -, hDUU, -⟩ := hD0 E k
  obtain ⟨hG0o, h1G0, hG0inv, -⟩ := hC0 E k S
  obtain ⟨hNP, -, -, hN0⟩ := hN3 E k
  obtain ⟨hνs, hνinv, -⟩ := hNP 0 (by omega)
  obtain ⟨a, b, ha, hab⟩ := hpos
  have hD1 : Dt (1 : GA E k) = 1 := by
    have h := hDmul 1 1
    simp only [mul_one] at h
    exact (mul_left_cancel₀ (hDpos 1).ne' (by rw [mul_one]; exact h.symm))
  have hG0m : MeasurableSet (G0 (k := k) S) := hG0o.measurableSet
  have hcont : ∀ z : ℂ, Continuous fun g : GA E k => P g * (Dt g : ℂ) ^ z := fun z =>
    hPc.mul ((Complex.continuous_ofReal.comp hDc).cpow continuous_const
      fun g => Complex.ofReal_mem_slitPlane.2 (hDpos g))
  set L := |Real.log a| + |Real.log b| with hL
  have hL0 : 0 ≤ L := by positivity
  have hdom : ∀ g ∈ G0 (k := k) S, ∀ z : ℂ,
      ‖P g * (Dt g : ℂ) ^ z‖ ≤ ‖P g * (Dt g : ℂ) ^ z₀‖ * Real.exp (L * |z.re - z₀.re|) := by
    intro g hg z
    exact LogNormEstimates.norm_le (hDpos g) ha (fun hp => ⟨(hab g hg hp).1, (hab g hg hp).2.1⟩) z z₀
  have hintG : ∀ z : ℂ, Integrable (fun g => P g * (Dt g : ℂ) ^ z) ((μ.withDensity β).restrict (G0 S)) := by
    intro z
    refine Integrable.mono' ((hint.norm.mul_const (Real.exp (L * |z.re - z₀.re|))).restrict)
      (hcont z).aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem hG0m fun g hg => hdom g hg z
  refine ⟨fun z₁ => ?_, fun σ => ?_⟩
  · have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (μ.withDensity β).restrict (G0 S))
      (F := fun z g => P g * (Dt g : ℂ) ^ z)
      (F' := fun z g => P g * (Dt g : ℂ) ^ z * ((Real.log (Dt g) : ℝ) : ℂ)) (x₀ := z₁)
      (bound := fun g => ‖P g * (Dt g : ℂ) ^ z₀‖ * Real.exp (L * (|z₁.re - z₀.re| + 1)) * L) (Metric.ball_mem_nhds z₁ zero_lt_one)
      (Filter.Eventually.of_forall fun z => (hcont z).aestronglyMeasurable) (hintG z₁)
      ((hcont z₁).mul (Complex.continuous_ofReal.comp (hDc.log fun g => (hDpos g).ne'))).aestronglyMeasurable
      ?_ (((hint.norm.mul_const _).mul_const _).restrict) ?_
    · exact hderiv.2.differentiableAt
    · refine ae_restrict_of_forall_mem hG0m fun g hg z hz => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      by_cases hp : P g = 0
      · simp only [hp, zero_mul, norm_zero]; positivity
      have hlog := LogNormEstimates.log_le (hDpos g) ha (hab g hg hp).1 (hab g hg hp).2.1
      have hz' : |z.re - z₀.re| ≤ |z₁.re - z₀.re| + 1 := by
        have h1 : |z.re - z₁.re| ≤ 1 := by
          have := Complex.abs_re_le_norm (z - z₁)
          rw [Metric.mem_ball, dist_eq_norm] at hz
          rw [Complex.sub_re] at this; linarith
        calc |z.re - z₀.re| = |(z.re - z₁.re) + (z₁.re - z₀.re)| := by ring_nf
          _ ≤ |z.re - z₁.re| + |z₁.re - z₀.re| := abs_add_le _ _
          _ ≤ _ := by linarith
      have e1 := hdom g hg z
      have e2 : Real.exp (L * |z.re - z₀.re|) ≤ Real.exp (L * (|z₁.re - z₀.re| + 1)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hz' hL0)
      calc ‖P g * (Dt g : ℂ) ^ z‖ * |Real.log (Dt g)|
          ≤ (‖P g * (Dt g : ℂ) ^ z₀‖ * Real.exp (L * (|z₁.re - z₀.re| + 1))) * L := by
            apply mul_le_mul _ hlog (abs_nonneg _) (by positivity)
            exact e1.trans (mul_le_mul_of_nonneg_left e2 (norm_nonneg _))
        _ = _ := rfl
    · refine Filter.Eventually.of_forall fun g z _ => ?_
      have hD := hDpos g
      have h := ((hasDerivAt_id z).const_cpow (c := (Dt g : ℂ))
        (Or.inl (Complex.ofReal_ne_zero.2 hD.ne'))).const_mul (P g)
      have e : P g * ((Dt g : ℂ) ^ id z * Complex.log (Dt g) * 1) =
          P g * (Dt g : ℂ) ^ z * ((Real.log (Dt g) : ℝ) : ℂ) := by
        rw [Complex.ofReal_log hD.le]; simp only [id, mul_one]; ring
      exact h.congr_deriv e
  · set f : GA E k → ℝ := fun g => (P g * (Dt g : ℂ) ^ ((u : ℂ) * Complex.I)).re with hf
    have hfc : Continuous f := Complex.continuous_re.comp (hcont _)
    set O : Set (GA E k) := G0 S ∩ {g | 0 < f g} with hO
    have hOo : IsOpen O := hG0o.inter (isOpen_lt continuous_const hfc)
    have hOm : MeasurableSet O := hOo.measurableSet
    have h1O : (1 : GA E k) ∈ O := by
      refine ⟨h1G0, ?_⟩
      show 0 < (P 1 * ((Dt (1 : GA E k) : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I)).re
      rw [hD1, Complex.ofReal_one, Complex.one_cpow, mul_one]; exact hP1
    have hOinv : ∀ n g, UU 0 n → (n * g ∈ O ↔ g ∈ O) := by
      intro n g hn
      simp only [hO, hf, Set.mem_inter_iff, Set.mem_setOf_eq, hG0inv n g hn, hPinv n hn g, hDmul, hDUU 0 n hn,
        one_mul]
    haveI : MeasurableSingletonClass (GA E k) := LogNormEstimates.msc
    set_option synthInstance.maxHeartbeats 400000 in
    have hμO : μ O ≠ 0 := (hOo.measure_pos μ ⟨1, h1O⟩).ne'
    have hβO : μ.withDensity β O ≠ 0 := by
      intro h0
      apply hμO
      have hin : ∀ g, ∫⁻ r, O.indicator 1 (r * g) ∂nuP E k 0 = O.indicator 1 g * nuP E k 0 Set.univ := by
        intro g
        rw [← lintegral_const]
        apply lintegral_congr_ae
        filter_upwards [(hN0 hk).1] with r hr
        by_cases hg : g ∈ O
        · simp [Set.indicator_apply, hg, (hOinv r g hr).2 hg]
        · simp [Set.indicator_apply, hg, mt (hOinv r g hr).1 hg]
      have key := hQ1 (GA E k) μ (Measure.dirac 1) (nuP E k 0) {1} (fun _ => 1) β
        (by rw [Measure.map_dirac' measurable_inv, inv_one]) (by rw [ae_dirac_eq]; exact rfl)
        ⟨measurable_const, fun g => by simp⟩ hβ.1
        (fun g => by
          simp only [lintegral_dirac, mul_one]
          calc ∫⁻ r, β (r⁻¹ * g) ∂nuP E k 0 = ∫⁻ r, β (r * g) ∂(Measure.map (fun h => h⁻¹) (nuP E k 0)) :=
                (lintegral_map (hβ.1.comp (measurable_mul_const g)) measurable_inv).symm
            _ = 1 := by rw [hνinv]; exact hβ.2 g)
        (O.indicator 1) (measurable_one.indicator hOm) (by rintro h rfl g; simp)
      have hw : μ.withDensity (fun _ => (1 : ℝ≥0∞)) = μ := withDensity_one
      rw [hw, lintegral_indicator_one hOm] at key
      rw [key]
      simp_rw [hin]
      rw [lintegral_mul_const _ (measurable_one.indicator hOm), lintegral_indicator_one hOm, h0, zero_mul]
    intro hzero
    have hFi := hintG ((σ : ℂ) + u * Complex.I)
    have hre := integral_re hFi
    rw [hzero] at hre
    simp only [RCLike.re_to_complex, Complex.zero_re] at hre
    have hpos' := (setIntegral_pos_iff_support_of_nonneg_ae (s := G0 S) (μ := μ.withDensity β)
      (f := fun g => (P g * (Dt g : ℂ) ^ ((σ : ℂ) + u * Complex.I)).re)
      (ae_restrict_of_forall_mem hG0m fun g hg => ?_) hFi.re).2 ?_
    · linarith
    · by_cases hp : P g = 0
      · simp [hp]
      show 0 ≤ (P g * (Dt g : ℂ) ^ ((σ : ℂ) + u * Complex.I)).re
      rw [LogNormEstimates.re_eq _ (hDpos g)]
      exact mul_nonneg (Real.rpow_nonneg (hDpos g).le _) (hab g hg hp).2.2
    · refine lt_of_lt_of_le (pos_iff_ne_zero.2 hβO) (measure_mono fun g hg => ⟨?_, hg.1⟩)
      rw [Function.mem_support, LogNormEstimates.re_eq _ (hDpos g)]
      exact (mul_pos (Real.rpow_pos_of_pos (hDpos g) σ) hg.2).ne'

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.UpperBlockProducts
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace UpperBlockProducts

theorem blk_corner {R S : Type} [CommRing R] [CommRing S] {a : ℕ} (s : R →ₙ+* S) {j : ℕ} {g : GL (Fin a) R}
    (hg : GlobalTheory j g) : GlobalTheory j (cornerGL a s g) := by
  intro i c hic
  change (1 : Matrix (Fin a) (Fin a) S) i c - s ((1 : Matrix (Fin a) (Fin a) R) i c) + s (g.val i c) = _
  rw [hg i c hic, sub_add_cancel]

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem blk_fl (v : Pl E) {j : ℕ} {c : GL (Fin k) (v.adicCompletion E)} (hc : GlobalTheory j c) : GlobalTheory j (fl k v c) :=
  blk_corner (sFin E) (blk_corner (sLoc E v) hc)

theorem posM_blk_zero {j : ℕ} (Y : UnipotentBlockColumnIndex k j j → Ad E) (i c : Fin k) (h : (c : ℕ) ≤ i) :
    posM Subtype.val Y i c = 0 := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [if_neg]
  rintro ⟨h1, h2⟩
  obtain ⟨t1, t2, t3⟩ := t.2
  rw [h1, h2] at *
  omega

theorem uu_blkU {j : ℕ} (Y : UnipotentBlockColumnIndex k j j → Ad E) : UU 0 (blkU Y : GA E k) := by
  refine ⟨fun i c hci => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · change (1 + posM Subtype.val Y) i c = 0
    rw [Matrix.add_apply, posM_blk_zero Y i c (le_of_lt hci), Matrix.one_apply_ne hci.ne', add_zero]
  · change (1 + posM Subtype.val Y) i i = 1
    rw [Matrix.add_apply, posM_blk_zero Y i i le_rfl, Matrix.one_apply_eq, add_zero]

theorem uu_mul {u u' : GA E k} (hu : UU 0 u) (hu' : UU 0 u') : UU 0 (u * u') := by
  refine ⟨fun i c hci => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hu.1 i l h, zero_mul]
    · rw [hu'.1 l c (lt_of_lt_of_le hci h), mul_zero]
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, hu.2.1, hu'.2.1, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hu.1 i l h, zero_mul]
      · rw [hu'.1 l i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

end UpperBlockProducts

open UpperBlockProducts UnipotentCharacter in
theorem finite_place_of_jump_windows : jumpWindows.S2 → jumpWindows.S9 → jumpWindows.MirabolicColumnBlock → jumpWindows.G0 → jumpWindows.G5 → jumpWindows.G5b → P2 → FinitePlaceStep := by
  intro hS2 hS9 hS10 hG0 hG5 hG5b hP2 E _ _ _ k wt ρ J hW ψ hψ S Y hY n m v hv hmv hm0 U hU x C hxY hsm hlev hB
  obtain ⟨-, -, i3, i4, i5, -, i7, i8, -, i10, -, -, -, i14, -⟩ := hG0 E k
  obtain ⟨g5a, g5r, -, g5c⟩ := hG5 E k ψ hψ
  obtain ⟨-, b2, b3, b4, b5⟩ := hG5b E k S
  obtain ⟨s10dec, -, -, s10blk1, -⟩ := hS10 (v.adicCompletion E) k (m v + 1)
  obtain ⟨p2law, p2norm, p2uu, p2whit, -, p2good, -⟩ := hP2 E k ψ hψ
  obtain ⟨s0, sadd, ssmul, -, sT, -⟩ := hS2 (InfinitePlace E) k (XB E k) (ρ.comp (infGL E k)) hW.poly
  let U' : Set (GL (Fin k) (v.adicCompletion E)) := {u | repW k v u (J x) = J x} ∩ (fl k v) ⁻¹' U
  have hU' : U' ∈ 𝓝 (1 : GL (Fin k) (v.adicCompletion E)) :=
    Filter.inter_mem (hlev v hv) ((i14 v).continuousAt.preimage_mem_nhds (by rw [map_one]; exact hU))
  have hne : ∃ y, chi ψ v y ≠ 1 := by
    obtain ⟨y, hy⟩ := hψ.loc v
    exact ⟨y, hy⟩
  obtain ⟨T, c, η, r, hη1, hr1, hrMir, hηr, ⟨Cl, hClc, hClU, hClB, hCl⟩, hmain⟩ :=
    hS9 (v.adicCompletion E) k (m v) hmv (chi ψ v) (chi_cont hψ v) hne (XB E k) (repW k v) U' hU'
  have hClU' : ∀ c ∈ Cl, fl k v c ∈ U := fun c hc => (hClU hc).2
  have inS : ∀ u, InS S (fl k v u : GA E k) := fun u w hw => i5 v w u (fun e => hw (e ▸ hv))
  have stab : ∀ u, ∀ z ∈ Y, repW k v u z ∈ Y := fun u z hz => hY.stable _ (inS u) z hz
  have hJx' : J (∑ t ∈ T, c t • ρ (fl k v t) x) = ∑ t ∈ T, c t • repW k v t (J x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hW.inter, repW_apply]
  have hJY : J (∑ t ∈ T, c t • ρ (fl k v t) x) ∈ Y := by
    rw [hJx']
    exact Y.sum_mem fun t _ => Y.smul_mem _ (stab t _ hxY)
  have hgood' : Good ψ (k - 1) (J (∑ t ∈ T, c t • ρ (fl k v t) x)) := hY.good _ hJY
  have key : ∀ g' : GA E k, cLoc v g' = 1 → ∀ h, GlobalTheory (m v + 1) h →
      Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) (g' * fl k v h) = η h * Wh ψ (J x) (g' * fl k v (r h)) := by
    intro g' hg' h hh
    obtain ⟨Λ, hΛ⟩ := g5a g'
    have hcond : ∀ z ∈ Y, ∀ y : UnipotentBlockColumnIndex k (m v + 1) (m v + 1) → v.adicCompletion E,
        (Λ : XB E k →ₗ[ℂ] ℂ) (repW k v (blkU y) z) = chi ψ v (lastE (m v + 1) y) * (Λ : XB E k →ₗ[ℂ] ℂ) z := by
      intro z hz y
      show Λ _ = _ * Λ _
      rw [hΛ _ (hY.good _ (stab _ z hz)),
        hΛ _ (hY.good _ hz), repW_apply, g5r, i8 v g' hg', i10,
        (g5c z (hY.good _ hz)).2.2 (m v + 1) (Nat.succ_pos _), lastE_loc, chi_apply]
    have := hmain (J x) (fun u hu => hu.1) Y stab hxY (Λ : XB E k →ₗ[ℂ] ℂ) hcond h hh
    change Λ _ = η h * Λ _ at this
    have hsum : ∑ t ∈ T, c t • repW k v t (J x) ∈ Y := by rw [← hJx']; exact hJY
    rw [hΛ _ (hY.good _ (stab _ _ hsum)), hΛ _ (hY.good _ (stab _ _ hxY)),
      repW_apply, repW_apply, g5r, g5r] at this
    rw [hJx']
    exact this
  have hpre : Pre ψ 0 (Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x))) :=
    p2whit (k - 1) (by omega) _ (p2good _ _ hgood')
  have hlawW : ∀ u, UU 0 u → ∀ z, Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) (u * z) =
      psN ψ u * Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) z :=
    fun u hu z => p2law 0 _ hpre u (p2uu u hu) z
  have hpsN : ∀ u : GA E k, psN ψ u ≠ 0 := fun u e0 => by
    have h1 := p2norm u
    rw [e0, norm_zero] at h1
    exact zero_ne_one h1
  refine ⟨∑ t ∈ T, c t • ρ (fl k v t) x, fl k v '' Cl, ?_, hJY, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨c₂, hc₂, rfl⟩
    exact hClU' c₂ hc₂
  · refine sum_of _ s0 sadd ssmul T c _ fun t => sT (ρ (fl k v t)) (fun g z => ?_) x hsm
    simp only [MonoidHom.comp_apply]
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, i7 _ (i3 v t) g, map_mul, ContinuousLinearMap.mul_apply]
  · rw [hJx']
    exact sum_of _ b5 b4 b3 T c _ fun t => by rw [repW_apply]; exact b2 _ _ hlev
  · rintro _ ⟨c₂, hc₂, rfl⟩
    exact blk_fl v (hClB c₂ hc₂)
  obtain ⟨hCc, hCS, ⟨t₀, ht₀, hW1⟩, hCb⟩ := hB
  refine ⟨hCc.mul (hClc.image (i14 v)), ?_, ?_, ?_⟩
  · rintro _ ⟨c₁, hc₁, _, ⟨c₂, hc₂, rfl⟩, rfl⟩ w hw
    rw [map_mul, hCS c₁ hc₁ w hw, inS c₂ w hw, one_mul]
  · have h1 := key 1 (map_one _) 1 s10blk1
    rw [hr1] at h1
    simp only [map_one, mul_one] at h1
    obtain ⟨s₁, hs₁, hηs₁⟩ := hηr 1
    have hs₁' : 0 < s₁ := lt_of_le_of_ne hs₁ fun e0 => hη1 (by rw [hηs₁, ← e0, Complex.ofReal_zero])
    refine ⟨s₁ * t₀, mul_pos hs₁' ht₀, ?_⟩
    rw [h1, hηs₁, hW1]
    push_cast
    ring
  · intro g hg hg0
    obtain ⟨hgI, hgL⟩ := hg
    have hgv : Mir (m v + 1) (cLoc v g) := by simpa using hgL v
    obtain ⟨y, h, hh, hdec⟩ := s10dec _ hgv
    set g' : GA E k := g * (fl k v (cLoc v g))⁻¹ with hg'def
    have hg' : cLoc v g' = 1 := by rw [hg'def, map_mul, map_inv, i4, mul_inv_cancel]
    have e : g = blkU (fun t => sFin E (sLoc E v (y t))) * (g' * fl k v h) := by
      rw [← i10, ← mul_assoc, ← i8 v g' hg', mul_assoc, ← map_mul, ← hdec, hg'def, inv_mul_cancel_right]
    have hWg : Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) g =
        ψ (lastE (m v + 1) fun t => sFin E (sLoc E v (y t))) * (η h * Wh ψ (J x) (g' * fl k v (r h))) := by
      rw [e, (g5c _ hgood').2.2 (m v + 1) (Nat.succ_pos _), key g' hg' h hh]
    have hηh : η h ≠ 0 := fun e0 => hg0 (by rw [hWg, e0]; simp)
    have hW'' : Wh ψ (J x) (g' * fl k v (r h)) ≠ 0 := fun e0 => hg0 (by rw [hWg, e0]; simp)
    obtain ⟨c₂, hc₂, hhc⟩ := hCl h hh hηh
    have hOm : Om n m (g' * fl k v (r h)) := by
      refine ⟨?_, fun w => ?_⟩
      · rw [map_mul, hg'def, map_mul, map_inv, i3, i3, inv_one, mul_one, mul_one]
        exact hgI
      · rcases eq_or_ne w v with rfl | hwv
        · rw [map_mul, hg', i4, one_mul]
          exact hrMir h hh hηh
        · rw [map_mul, hg'def, map_mul, map_inv, i5 v w _ hwv, i5 v w _ hwv, inv_one, mul_one, mul_one]
          simpa [hwv] using hgL w
    obtain ⟨nn₀, c₁, hc₁, t₁, hnn₀, hnnS, hgeq₀, ht₁, hWv⟩ := hCb _ hOm hW''
    obtain ⟨sh, hsh, hηsh⟩ := hηr h
    have hYg : (blkU fun t => sFin E (sLoc E v (y t)) : GA E k) = fl k v (blkU y) := (i10 v _ y).symm
    have h2 : nn₀ * (c₁ * fl k v c₂) = g' * fl k v h := by
      rw [hhc, map_mul, ← mul_assoc g', hgeq₀, mul_assoc]
    have hcc : Wh ψ (J (∑ t ∈ T, c t • ρ (fl k v t) x)) (c₁ * fl k v c₂) = ((sh * t₁ : ℝ) : ℂ) := by
      have h1 := hlawW nn₀ hnn₀ (c₁ * fl k v c₂)
      rw [h2, key g' hg' h hh, hWv, hηsh] at h1
      apply mul_left_cancel₀ (hpsN nn₀)
      rw [← h1]
      push_cast
      ring
    have huu : UU 0 ((blkU fun t => sFin E (sLoc E v (y t))) * nn₀ : GA E k) := uu_mul (uu_blkU _) hnn₀
    refine ⟨(blkU fun t => sFin E (sLoc E v (y t))) * nn₀, c₁ * fl k v c₂,
      Set.mem_image2_of_mem hc₁ ⟨c₂, hc₂, rfl⟩, sh * t₁, huu, ?_, ?_, mul_nonneg hsh ht₁, ?_⟩
    · intro w hw
      rw [map_mul, hYg, i5 v w _ (fun e0 => hw (e0 ▸ hv)), hnnS w hw, one_mul]
    · rw [mul_assoc, h2]
      exact e
    · have hg2 : g = ((blkU fun t => sFin E (sLoc E v (y t))) * nn₀) * (c₁ * fl k v c₂) := by
        rw [mul_assoc, h2]
        exact e
      rw [hg2, hlawW _ huu, hcc]

end PositivityTheory.AdelicQuotientData

end
end
