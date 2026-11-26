module

public import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.ClusteredLetterwiseBoxes
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertLongOrbitWordConditionsOfLargeScale

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeWordConditionsOfLargeScale
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexConjugationOrbitOneRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexConjugationOrbitOneRealPlace
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.ConjWord

theorem cc_comm {fr : Formalism.HC.Frame} (g : fr.GG) : g * fr.cc = fr.cc * g := mul_comm _ _

theorem plc_cc_mul {fr : Formalism.HC.Frame} (g : fr.GG) : plc (fr.cc * g) = plc g := UpperTheory.KStar.Words.placeOf_cc_mul g

theorem conj_word_one_place {fr : Formalism.HC.Frame} (τ : fr.GG) :
    orderOf fr.cc = 2 ∧ ∀ i : ZMod (orderOf fr.cc), plc (letter τ fr.cc i) = plc τ := by
  refine ⟨fr.orderOf_cc, fun i => ?_⟩
  unfold letter
  generalize i.val = k
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ fr.cc k, ← mul_assoc, cc_comm, plc_cc_mul, ih]

end GlobalTheory.HTW.ConjWord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexConjugationOrbitOneRealPlaceStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexConjugation_orbit_one_realPlace : ∀ {fr : Formalism.HC.Frame} (τ : fr.GG), orderOf fr.cc = 2 ∧ ∀ i : ZMod (orderOf fr.cc), plc (letter τ fr.cc i) = plc τ := by
  first | exact @GlobalTheory.HTW.ConjWord.conj_word_one_place | exact GlobalTheory.HTW.ConjWord.conj_word_one_place | (intros; apply GlobalTheory.HTW.ConjWord.conj_word_one_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingSignAlternateOfSignNeg
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingSignAlternateOfSignNeg
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem signs_alternate_inert : ∀ {fr : Formalism.HC.Frame} (ε : ℤˣ) (τ φ : fr.GG), φ.1.2 = -1 →
    Alternates (fun i : ZMod (orderOf φ) => pos ε (letter τ φ i)) ∧
      Alternates (fun i : ZMod (orderOf φ) => !pos ε (letter τ φ i)) := by
  intro e ε τ φ hφ
  have hsnd : ∀ k : ℕ, (τ * φ ^ k).1.2 = τ.1.2 * (-1) ^ k := by
    intro k; simp [Prod.snd_mul, Prod.fst_mul, Prod.pow_fst, Prod.pow_snd, hφ]
  have hn : 0 < orderOf φ := orderOf_pos φ
  have h1 : ((-1 : ℤˣ)) ^ orderOf φ = 1 := by
    have h : (φ ^ orderOf φ).1.2 = 1 := by rw [pow_orderOf_eq_one]; rfl
    rwa [Prod.pow_fst, Prod.pow_snd, hφ] at h
  haveI : NeZero (orderOf φ) := ⟨hn.ne'⟩
  have key : ∀ i : ZMod (orderOf φ), (letter τ φ (i + 1)).1.2 = -(letter τ φ i).1.2 := by
    intro i
    unfold letter
    rw [hsnd, hsnd, ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    have hm : ((-1 : ℤˣ)) ^ ((i.val + 1) % orderOf φ) = (-1) ^ (i.val + 1) := by
      conv_rhs => rw [← Nat.mod_add_div (i.val + 1) (orderOf φ), pow_add, pow_mul, h1, one_pow, mul_one]
    rw [hm, pow_succ]
    simp
  have hA : Alternates (fun i : ZMod (orderOf φ) => pos ε (letter τ φ i)) := by
    intro i
    simp only [pos]
    rw [key i]
    rcases Int.units_eq_one_or (letter τ φ i).1.2 with h | h <;>
      rcases Int.units_eq_one_or ε with h' | h' <;> simp [h, h'] <;> decide
  refine ⟨hA, fun i => ?_⟩
  have h := hA i
  simp only at h ⊢
  rw [h]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingSignAlternateOfSignNegStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddingSign_alternate_of_sign_neg : ∀ {fr : Formalism.HC.Frame} (ε : ℤˣ) (τ φ : fr.GG), φ.1.2 = -1 → Alternates (fun i : ZMod (orderOf φ) => pos ε (letter τ φ i)) ∧ Alternates (fun i : ZMod (orderOf φ) => !pos ε (letter τ φ i)) := by
  first | exact @GlobalTheory.signs_alternate_inert | exact GlobalTheory.signs_alternate_inert | (intros; apply GlobalTheory.signs_alternate_inert <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordBoxesAndSizes
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordMiAddHiLeTwoHeight
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizesSumLeParametersPageHeightStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_roundedSizes_le_height : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C → (bHat L : ℝ) + (etaHat L : ℝ) + (sHat L : ℝ) ≤ hPage L := by
  first | exact @GlobalTheory.HTW.bHat_add_etaHat_add_sHat_le_hPage | exact GlobalTheory.HTW.bHat_add_etaHat_add_sHat_le_hPage | (intros; apply GlobalTheory.HTW.bHat_add_etaHat_add_sHat_le_hPage <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordMiAddHiLeTwoHeight
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem WordData.Mi_add_hi_le_two_mul {n : ℕ} (W : WordData n) (hB : W.Box) (hT : W.ThickOr) (i : ZMod n) :
    W.Mi i + W.hi i ≤ 2 * (W.b + W.η + W.S) := by
  obtain ⟨-, -, hw, -, -, -⟩ := hB
  have hs : W.sz i ≤ (W.b : ℤ) + W.η := by
    rcases hT i with h | h
    · exact h.2
    · omega
  unfold WordData.Mi WordData.hi
  split_ifs <;> omega

theorem pageWord_Mi_add_hi_le {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG)
    (hR : Roomy L C) (i : ZMod (orderOf φ)) :
    (((pageWord L j ε τ φ).Mi i + (pageWord L j ε τ φ).hi i : ℕ) : ℝ) ≤ 2 * hPage L := by
  have h1 := WordData.Mi_add_hi_le_two_mul _ (GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR) (GlobalTheory.T.twistedDualOrbitPageWord_thickOr L C j ε τ φ hR) i
  have h2 := GlobalTheory.T.sum_roundedSizes_le_height L C hR
  have h3 : (((pageWord L j ε τ φ).Mi i + (pageWord L j ε τ φ).hi i : ℕ) : ℝ)
      ≤ ((2 * (bHat L + etaHat L + sHat L) : ℕ) : ℝ) := Nat.cast_le.mpr h1
  refine h3.trans ?_
  push_cast
  linarith

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordMiAddHiLeTwoHeightStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualPageWord_Mi_add_hi_le_two_height : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → ∀ i, (((pageWord L j ε τ φ).Mi i + (pageWord L j ε τ φ).hi i : ℕ) : ℝ) ≤ 2 * hPage L := by
  first | exact @GlobalTheory.HTW.pageWord_Mi_add_hi_le | exact GlobalTheory.HTW.pageWord_Mi_add_hi_le | (intros; apply GlobalTheory.HTW.pageWord_Mi_add_hi_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordNonThickSizeBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordNonThickSizeBounds
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem abs_szT_sub_floor_le {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) :
    |((szT P j s : ℤ) : ℝ) - ((⌊P.e j⌋ : ℤ) : ℝ)| ≤ ((R.t : ℝ) + 1) / 2 := by
  have h0 : (0 : ℤ) ≤ ((R.t : ℤ) + 1) / 2 := by omega
  have h1 : 2 * (((R.t : ℤ) + 1) / 2) ≤ (R.t : ℤ) + 1 := by omega
  have h0' : (0 : ℝ) ≤ ((((R.t : ℤ) + 1) / 2 : ℤ) : ℝ) := by exact_mod_cast h0
  have h1' : 2 * ((((R.t : ℤ) + 1) / 2 : ℤ) : ℝ) ≤ (R.t : ℝ) + 1 := by exact_mod_cast h1
  unfold szT
  generalize ((R.t : ℤ) + 1) / 2 = q at h0' h1'
  cases s
  · simp only [Bool.false_eq_true, if_false, Int.cast_sub]
    rw [abs_le]; constructor <;> linarith
  · simp only [if_true, Int.cast_add]
    rw [abs_le]; constructor <;> linarith

theorem pageWord_not_thick_size : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → ∀ i, ¬ (pageWord L j ε τ φ).thick i → ∃ s : ℝ, L.sc.w'' D.R.n ≤ s ∧ s ≤ (wMax D : ℝ) ∧ s ≤ 8 / 5 * L.sc.b' ∧ |(((pageWord L j ε τ φ).sz i : ℤ) : ℝ) - s| ≤ ((D.R.t : ℝ) + 1) / 2 := by
  intro D L C j ε τ φ hR i hi
  have hnt : ¬ Thick D.host (letter τ φ i) := fun h => hi ((GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding L C j ε τ φ hR i).2 h)
  have h1 := GlobalTheory.T.floor_size_bounds_not_thick_embedding L C (letter τ φ i) j hR hnt
  have h2 := (GlobalTheory.T.maxSizeAtNonThickPlace_le_and_bound L C hR).2 (letter τ φ i) j hnt
  refine ⟨((⌊(hcAt D (letter τ φ i)).e j⌋ : ℤ) : ℝ), h1.1, ?_, h1.2, ?_⟩
  · exact_mod_cast h2
  · exact abs_szT_sub_floor_le _ j _

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordNonThickSizeBoundsStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualOrbitPageWord_nonThick_size_bounds : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → ∀ i, ¬ (pageWord L j ε τ φ).thick i → ∃ s : ℝ, L.sc.w'' D.R.n ≤ s ∧ s ≤ (wMax D : ℝ) ∧ s ≤ 8 / 5 * L.sc.b' ∧ |(((pageWord L j ε τ φ).sz i : ℤ) : ℝ) - s| ≤ ((D.R.t : ℝ) + 1) / 2 := by
  first | exact @GlobalTheory.HTW.pageWord_not_thick_size | exact GlobalTheory.HTW.pageWord_not_thick_size | (intros; apply GlobalTheory.HTW.pageWord_not_thick_size <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordBoxesAndSizes
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem recWord_wordBox : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ}
    (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ → WordBox L (recWord L j ε g) := by
  intro D L C j ε n g ψ hR hO
  obtain ⟨hn, hg⟩ := hO
  subst hn
  have hgl : g = letter (g 0) ψ := funext fun a => hg a
  rw [hgl]
  have hb := GlobalTheory.HTW.bHat_window L C hR
  refine ⟨?_, ?_, hb.1, hb.2⟩
  · intro a
    obtain ⟨-, hM, hh, -⟩ := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε (g 0) ψ hR a
    rw [hM, hh]
    exact GlobalTheory.T.twistedDualPageWord_Mi_add_hi_le_two_height L C j ε (g 0) ψ hR a
  · intro a hnt
    obtain ⟨hsz, -, -, hth⟩ := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε (g 0) ψ hR a
    obtain ⟨s, hs1, hs2, -, hs3⟩ := GlobalTheory.T.twistedDualOrbitPageWord_nonThick_size_bounds L C j ε (g 0) ψ hR a (fun h => hnt (hth.2 h))
    refine ⟨s, hs1, le_trans hs2 (GlobalTheory.T.maxSizeAtNonThickPlace_le_windowEnds L).1, ?_⟩
    have hc : (((recWord L j ε (letter (g 0) ψ)).sz a : ℕ) : ℝ) = (((pageWord L j ε (g 0) ψ).sz a : ℤ) : ℝ) := by
      rw [← hsz]; push_cast; rfl
    rw [hc]; exact hs3

end GlobalTheory.HTW.Rec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordBoxesAndSizesStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualSizeWord_boxesAndSizes : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ → WordBox L (recWord L j ε g) := by
  first | exact @GlobalTheory.HTW.Rec.recWord_wordBox | exact GlobalTheory.HTW.Rec.recWord_wordBox | (intros; apply GlobalTheory.HTW.Rec.recWord_wordBox <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordInertDichotomy
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordInertPrimeDichotomy
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordConjHypATAllThick
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlternatingWordLargeSizeNumericalBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlternatingWordLargeSizeNumericalBounds
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem alternatingWord_numerical_bounds :
    ∀ (l : ℕ) (B η S M b : ℝ), 11 ≤ l → 100 ≤ B → 0 ≤ η → 0 ≤ S → 2 * η + S ≤ B / 10 →
      |M - B| ≤ η → |b - B| ≤ η → (M + S) / 2 ≤ b ∧
      2 * ((M + S + η) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 + (Real.logb l (2 * (M + S + η)) + 1))
        + η + 1 ≤ b := by
  intro l B η S M b hl hB hη hS hBS hM hb
  have hl' : (11:ℝ) ≤ l := by exact_mod_cast hl
  rw [abs_le] at hM hb
  obtain ⟨hM1, hM2⟩ := hM
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨by linarith, ?_⟩
  have hx1 : M + S + η ≤ 11/10 * B := by linarith
  have hx0 : 100 ≤ M + S + η := by linarith
  have hfrac : (2 * (l:ℝ) - 1) / ((l:ℝ) - 1) ^ 2 ≤ 21/100 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  have hfrac0 : 0 ≤ (2 * (l:ℝ) - 1) / ((l:ℝ) - 1) ^ 2 :=
    div_nonneg (by linarith) (sq_nonneg _)
  have h1 : (M + S + η) * (2 * (l:ℝ) - 1) / ((l:ℝ) - 1) ^ 2 ≤ 231/1000 * B := by
    rw [mul_div_assoc]
    nlinarith [mul_le_mul_of_nonneg_left hfrac (show 0 ≤ M + S + η by linarith),
      mul_le_mul_of_nonneg_right hx1 hfrac0]
  have hlogl : 1 ≤ Real.log l := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlog100 : Real.log 100 < 5 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h := Real.exp_one_gt_d9
    have he : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [he]
    calc (100:ℝ) < 2.7182818283 ^ 5 := by norm_num
      _ ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) h.le 5
  have hlogy : Real.log (2 * (M + S + η)) ≤ 2 * (M + S + η) / 100 - 1 + Real.log 100 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 2 * (M + S + η) / 100 by linarith)
    rw [Real.log_div (by linarith) (by norm_num)] at this
    linarith
  have hlogb : Real.logb l (2 * (M + S + η)) ≤ 2 * (M + S + η) / 100 + 4 := by
    rw [Real.logb, div_le_iff₀ (by linarith)]
    have : 0 ≤ Real.log (2 * (M + S + η)) := Real.log_nonneg (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hlogl (show 0 ≤ 2 * (M + S + η) / 100 + 4 by linarith)]
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlternatingWordLargeSizeNumericalBoundsStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternatingWord_large_size_numerical_bounds : ∀ (l : ℕ) (B η S M b : ℝ), 11 ≤ l → 100 ≤ B → 0 ≤ η → 0 ≤ S → 2 * η + S ≤ B / 10 → |M - B| ≤ η → |b - B| ≤ η → (M + S) / 2 ≤ b ∧ 2 * ((M + S + η) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + 3 + (Real.logb l (2 * (M + S + η)) + 1)) + η + 1 ≤ b := by
  first | exact @GlobalTheory.alternatingWord_numerical_bounds | exact GlobalTheory.alternatingWord_numerical_bounds | (intros; apply GlobalTheory.alternatingWord_numerical_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordConjHypATAllThick
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem bHat_large_of_roomy {D : D7} (L : SizeData₂ D) (C : ℝ) (h : Roomy L C) :
    (100 : ℝ) ≤ bHat L ∧ 2 * (etaHat L : ℝ) + sHat L ≤ (bHat L : ℝ) / 10 := by
  obtain ⟨hC, hw, hr, hwb, -, hb⟩ := h
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ D.host.Lw := Nat.cast_nonneg _
  have hb' : (0 : ℝ) ≤ L.sc.b' := by linarith
  have hCL : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbb : 100 * L.sc.b' ≤ L.sc.b := le_trans (mul_le_mul_of_nonneg_right hCL hb') hb
  have h1 : (etaHat L : ℝ) ≤ L.etaSz + D.R.t + 2 := by
    have := Nat.floor_le he.le
    unfold etaHat
    push_cast
    linarith
  have h2 : (sHat L : ℝ) ≤ L.Sc := Nat.floor_le hS.le
  have h3 : ⌈L.sc.b⌉₊ ≤ bHat L + D.R.t := by
    unfold bHat
    omega
  have h4 : L.sc.b ≤ (bHat L : ℝ) + D.R.t := by
    have h5 : ((⌈L.sc.b⌉₊ : ℕ) : ℝ) ≤ (bHat L : ℝ) + D.R.t := by exact_mod_cast h3
    exact le_trans (Nat.le_ceil _) h5
  constructor <;> linarith

theorem conjWord_hypAT {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ : D.R.GG) (l : ℕ)
    (hR : Roomy L C) (hl : 11 ≤ l) (hτ : Thick D.host τ) :
    (pageWord L j ε τ (D.R.cc)).HypAT l ∧ ∀ i, (pageWord L j ε τ (D.R.cc)).thick i := by
  obtain ⟨hord, hplc⟩ := GlobalTheory.T.complexConjugation_orbit_one_realPlace τ
  have hth : ∀ i, (pageWord L j ε τ (D.R.cc)).thick i := by
    intro i
    rw [GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding L C j ε τ (D.R.cc) hR i]
    unfold Thick at hτ ⊢
    rw [hplc i]
    exact hτ
  refine ⟨⟨?_, ?_, ?_⟩, hth⟩
  · rw [hord]; exact even_two
  · exact (GlobalTheory.T.embeddingSign_alternate_of_sign_neg ε τ (D.R.cc) rfl).2
  · intro M hM i
    obtain ⟨hB, hroom⟩ := bHat_large_of_roomy L C hR
    have hη : (0 : ℝ) ≤ etaHat L := Nat.cast_nonneg _
    have hS : (0 : ℝ) ≤ sHat L := Nat.cast_nonneg _
    have key : ∀ k, (bHat L : ℝ) ≤ ((pageWord L j ε τ (D.R.cc)).sz k : ℝ) ∧
        ((pageWord L j ε τ (D.R.cc)).sz k : ℝ) ≤ (bHat L : ℝ) + etaHat L := by
      intro k
      obtain ⟨h1, h2⟩ := hth k
      have h1' : ((bHat L : ℕ) : ℤ) ≤ (pageWord L j ε τ (D.R.cc)).sz k := h1
      have h2' : (pageWord L j ε τ (D.R.cc)).sz k ≤ ((bHat L : ℕ) : ℤ) + ((etaHat L : ℕ) : ℤ) := h2
      exact ⟨by exact_mod_cast h1', by exact_mod_cast h2'⟩
    obtain ⟨k, hk⟩ := hM.1
    have hMk := key k
    rw [hk] at hMk
    have hi := key i
    obtain ⟨h1, h2⟩ := GlobalTheory.T.alternatingWord_large_size_numerical_bounds l (bHat L) (etaHat L) (sHat L) (M : ℝ)
      ((pageWord L j ε τ (D.R.cc)).sz i : ℝ) hl hB hη hS hroom
      (abs_le.2 ⟨by linarith [hMk.1], by linarith [hMk.2]⟩)
      (abs_le.2 ⟨by linarith [hi.1], by linarith [hi.2]⟩)
    refine ⟨?_, h1, h2⟩
    have : (1 : ℝ) ≤ ((pageWord L j ε τ (D.R.cc)).sz i : ℝ) := by linarith [hi.1]
    exact_mod_cast this

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordConjHypATAllThickStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualOrbitPageWord_conj_hypAT_allThick : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ : D.R.GG) (l : ℕ), Roomy L C → 11 ≤ l → Thick D.host τ → (pageWord L j ε τ (D.R.cc)).HypAT l ∧ ∀ i, (pageWord L j ε τ (D.R.cc)).thick i := by
  first | exact @GlobalTheory.HTW.conjWord_hypAT | exact GlobalTheory.HTW.conjWord_hypAT | (intros; apply GlobalTheory.HTW.conjWord_hypAT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeNonthickLetterNoThreeThick
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrderOfEqMaxTwoOfSignNegImplicit
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrderOfEqMaxTwoOfSignNegImplicit
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem orderOf_moving (fr : Formalism.HC.Frame) (φ : fr.GG) (h : φ.1.2 = -1) : orderOf φ = Nat.lcm 2 (orderOf φ.2) :=
  UpperTheory.KStar.Words.orderOf_moving φ h

theorem orderOf_moving_stmt : ∀ {fr : Formalism.HC.Frame} (φ : fr.GG), φ.1.2 = -1 → orderOf φ = Nat.lcm 2 (orderOf φ.2) :=
  fun {fr} φ h => orderOf_moving fr φ h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrderOfEqMaxTwoOfSignNegImplicitStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderOf_eq_max_two_of_sign_neg_implicit : ∀ {fr : Formalism.HC.Frame} (φ : fr.GG), φ.1.2 = -1 → orderOf φ = Nat.lcm 2 (orderOf φ.2) := by
  first | exact @GlobalTheory.orderOf_moving_stmt | exact GlobalTheory.orderOf_moving_stmt | (intros; apply GlobalTheory.orderOf_moving_stmt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordNoThreeMarkedOfAtMostOne
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordNoThreeMarkedOfAtMostOne
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem noThree_of_atMostOne : ∀ {n : ℕ} (th : ZMod n → Prop), 2 ≤ n → (∀ a b, th a → th b → a = b) → NoThree th ∧ ∃ i, ¬ th i := by
  intro n th hn hone
  have h10 : (1 : ZMod n) ≠ 0 := by
    have : Fact (1 < n) := ⟨by omega⟩
    exact one_ne_zero
  have key : ∀ i : ZMod n, ¬ (th i ∧ th (i + 1)) := by
    rintro i ⟨ha, hb⟩
    exact h10 (by linear_combination (hone _ _ ha hb).symm)
  refine ⟨fun i h => key i ⟨h.1, h.2.1⟩, ?_⟩
  by_cases h0 : th 0
  · exact ⟨0 + 1, fun h1 => key 0 ⟨h0, h1⟩⟩
  · exact ⟨0, h0⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordNoThreeMarkedOfAtMostOneStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclicWord_noThreeMarked_of_atMostOne : ∀ {n : ℕ} (th : ZMod n → Prop), 2 ≤ n → (∀ a b, th a → th b → a = b) → NoThree th ∧ ∃ i, ¬ th i := by
  first | exact @GlobalTheory.noThree_of_atMostOne | exact GlobalTheory.noThree_of_atMostOne | (intros; apply GlobalTheory.noThree_of_atMostOne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordNoThreeMarkedOfAtMostTwoInWindow
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordNoThreeMarkedOfAtMostTwoInWindow
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem _root_.GlobalTheory.noThree_of_windowTwo : ∀ {n : ℕ} (th : ZMod n → Prop) (L : ℕ),
    3 ≤ L → _root_.GlobalTheory.HTW.WindowTwo th L →
    _root_.GlobalTheory.HTW.NoThree th ∧ ∃ i, ¬ th i := by
  intro n th L hL hw
  have key : ∀ i, ¬(th i ∧ th (i + 1) ∧ th (i + 2)) := by
    intro i h
    have := hw i 0 1 2 (by norm_num) (by norm_num) (by omega)
    simp only [Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat] at this
    exact this h
  refine ⟨key, ?_⟩
  by_contra hall
  push_neg at hall
  exact key 0 ⟨hall _, hall _, hall _⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordNoThreeMarkedOfAtMostTwoInWindowStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclicWord_noThreeMarked_of_atMostTwoInWindow : ∀ {n : ℕ} (th : ZMod n → Prop) (L : ℕ), 3 ≤ L → WindowTwo th L → NoThree th ∧ ∃ i, ¬ th i := by
  first | exact @GlobalTheory.noThree_of_windowTwo | exact GlobalTheory.noThree_of_windowTwo | (intros; apply GlobalTheory.noThree_of_windowTwo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtMostOneThickShortOrbit
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtMostOneThickShortOrbit
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem short_orbit_one_thick : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG),
    orderOf φ.2 ≤ 4 * H.Lw → ∀ a b : ZMod (orderOf φ), Thick H (letter τ φ a) →
      Thick H (letter τ φ b) → plc (letter τ φ a) = plc (letter τ φ b) := by
  intro R H τ φ hord a b ha hb
  have key : ∀ g : R.GG, Thick H g → ∃ s ∈ H.T2, R.tau2 (R.dig s + H.u0) = plc g := by
    intro g hg
    unfold Thick Host.thickPlaces at hg
    simpa [Finset.mem_image] using hg
  exact UpperTheory.KStar.Words.thick_one_place H.T2 H.second_set_range H.u0 τ φ
    ((Nat.le_of_dvd (orderOf_pos _) (R.toFrame.orderOf_hH_dvd φ.2)).trans hord) a.val b.val (key _ ha) (key _ hb)

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtMostOneThickShortOrbitStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atMostOneThick_short_orbit : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), orderOf φ.2 ≤ 4 * H.Lw → ∀ a b : ZMod (orderOf φ), Thick H (letter τ φ a) → Thick H (letter τ φ b) → plc (letter τ φ a) = plc (letter τ φ b) := by
  first | exact @GlobalTheory.HTW.short_orbit_one_thick | exact GlobalTheory.HTW.short_orbit_one_thick | (intros; apply GlobalTheory.HTW.short_orbit_one_thick <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeNonthickLetterNoThreeThick
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.InertWord

theorem inert_nothree_nonthick : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), 3 ≤ H.Lw → φ.1.2 = -1 →
    ¬ (φ = R.cc ∧ Thick H τ) →
    NoThree (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) ∧
      ∃ i : ZMod (orderOf φ), ¬ Thick H (letter τ φ i) := by
  intro R H τ φ hL hφ hnot
  have h2 : 2 ≤ orderOf φ := by
    rw [GlobalTheory.T.orderOf_eq_max_two_of_sign_neg_implicit φ hφ]
    exact Nat.le_of_dvd (Nat.lcm_pos two_pos (orderOf_pos _)) (Nat.dvd_lcm_left _ _)
  by_cases hc : φ = R.cc
  · have hτ : ¬ Thick H τ := fun h => hnot ⟨hc, h⟩
    subst hc
    have hno : ∀ i : ZMod (orderOf (R.cc)), ¬ Thick H (letter τ (R.cc) i) := by
      intro i h
      apply hτ
      have := (GlobalTheory.T.complexConjugation_orbit_one_realPlace τ).2 i
      unfold Thick at h ⊢
      rw [this] at h
      exact h
    exact GlobalTheory.T.cyclicWord_noThreeMarked_of_atMostOne _ h2 (fun a b ha _ => absurd ha (hno a))
  · by_cases hlen : 4 * H.Lw < orderOf φ.2
    · exact GlobalTheory.T.cyclicWord_noThreeMarked_of_atMostTwoInWindow _ H.Lw hL (GlobalTheory.T.atMostTwoThick_in_window_long_orbit H τ φ hlen)
    · have h1 : φ ≠ 1 := by
        rintro rfl
        exact absurd (show (1 : ℤˣ) = -1 from hφ) (by decide)
      have adj : ∀ i : ZMod (orderOf φ), ¬ (Thick H (letter τ φ i) ∧ Thick H (letter τ φ (i + 1))) := fun i h =>
        UpperTheory.KStar.Words.placeOf_letter_succ_ne τ φ h1 hc i
          (GlobalTheory.T.atMostOneThick_short_orbit H τ φ (not_lt.mp hlen) (i + 1) i h.2 h.1)
      refine ⟨fun i h => adj i ⟨h.1, h.2.1⟩, ?_⟩
      by_contra hall
      have hall' : ∀ i, Thick H (letter τ φ i) := fun i => by_contra fun hi => hall ⟨i, hi⟩
      exact adj 0 ⟨hall' 0, hall' (0 + 1)⟩

end GlobalTheory.HTW.InertWord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeNonthickLetterNoThreeThickStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPrime_nonthick_letter_no_three_thick : ∀ {R : Ranks} (H : Host R) (τ φ : R.GG), 3 ≤ H.Lw → φ.1.2 = -1 → ¬ (φ = R.cc ∧ Thick H τ) → NoThree (fun i : ZMod (orderOf φ) => Thick H (letter τ φ i)) ∧ ∃ i : ZMod (orderOf φ), ¬ Thick H (letter τ φ i) := by
  first | exact @GlobalTheory.HTW.InertWord.inert_nothree_nonthick | exact GlobalTheory.HTW.InertWord.inert_nothree_nonthick | (intros; apply GlobalTheory.HTW.InertWord.inert_nothree_nonthick <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordInertPrimeDichotomy
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_inert_dichotomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ)
    (τ φ : D.R.GG) (l : ℕ), Roomy L C → 11 ≤ l → φ.1.2 = -1 →
    (pageWord L j ε τ φ).Box ∧ ((pageWord L j ε τ φ).HypNT ∨
      (φ = D.R.cc ∧ (pageWord L j ε τ φ).HypAT l ∧ ∀ i, (pageWord L j ε τ φ).thick i)) := by
  intro D L C j ε τ φ l hR hl hφ
  refine ⟨GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR, ?_⟩
  by_cases h : φ = D.R.cc ∧ Thick D.host τ
  · obtain ⟨rfl, hτ⟩ := h
    exact Or.inr ⟨rfl, GlobalTheory.T.twistedDualOrbitPageWord_conj_hypAT_allThick L C j ε τ l hR hl hτ⟩
  · left
    have hLw : 3 ≤ D.host.Lw := by
      have := L.weightLength_ge_depth
      omega
    obtain ⟨h3, i, hi⟩ := GlobalTheory.T.inertPrime_nonthick_letter_no_three_thick D.host τ φ hLw hφ h
    have hth := GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding L C j ε τ φ hR
    refine ⟨(GlobalTheory.T.embeddingSign_alternate_of_sign_neg ε τ φ hφ).2, ⟨i, fun h' => hi ((hth i).1 h')⟩, ?_⟩
    intro k hk
    exact h3 k ⟨(hth _).1 hk.1, (hth _).1 hk.2.1, (hth _).1 hk.2.2⟩

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordInertPrimeDichotomyStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualPageWord_inert_prime_dichotomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG) (l : ℕ), Roomy L C → 11 ≤ l → φ.1.2 = -1 → (pageWord L j ε τ φ).Box ∧ ((pageWord L j ε τ φ).HypNT ∨ (φ = D.R.cc ∧ (pageWord L j ε τ φ).HypAT l ∧ ∀ i, (pageWord L j ε τ φ).thick i)) := by
  first | exact @GlobalTheory.HTW.pageWord_inert_dichotomy | exact GlobalTheory.HTW.pageWord_inert_dichotomy | (intros; apply GlobalTheory.HTW.pageWord_inert_dichotomy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordInertDichotomy
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem alternates_parity {n : ℕ} [NeZero n] {up : ZMod n → Bool} (h : Alternates up) :
    ∃ d : ℕ, ∀ a : ZMod n, up a = decide ((a.val + d) % 2 = 1) := by
  refine ⟨if up 0 then 1 else 0, fun a => ?_⟩
  have key : ∀ k : ℕ, up (k : ZMod n) = decide ((k + (if up 0 then 1 else 0)) % 2 = 1) := by
    intro k
    induction k with
    | zero => cases h0 : up 0 <;> simp [h0]
    | succ k ih =>
      have e : ((k + 1 : ℕ) : ZMod n) = (k : ZMod n) + 1 := by push_cast; rfl
      rw [e, h, ih]
      generalize (if up 0 = true then 1 else 0) = d
      by_cases hk : (k + d) % 2 = 1
      · have : ¬ (k + 1 + d) % 2 = 1 := by omega
        simp [hk, this]
      · have : (k + 1 + d) % 2 = 1 := by omega
        simp [hk, this]
  simpa using key a.val

theorem recWord_dichotomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ}
    (g : ZMod n → D.R.GG) (ψ : D.R.GG) (l : ℕ), Roomy L C → IsOrbit g ψ → 11 ≤ l → ψ.1.2 = -1 →
    WordsNT (recWord L j ε g) ∨ ∃ d, WordsAT l (recWord L j ε g) d := by
  intro D L C j ε n g ψ l hR hO hl hψ
  obtain ⟨rfl, hg⟩ := hO
  obtain ⟨τ, rfl⟩ : ∃ τ, g = letter τ ψ := ⟨g 0, funext hg⟩
  clear hg
  have hT := GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord L C j ε τ ψ hR
  obtain ⟨hBox, hcase⟩ := GlobalTheory.T.twistedDualPageWord_inert_prime_dichotomy L C j ε τ ψ l hR hl hψ
  have hsz : ∀ a, (((recWord L j ε (letter τ ψ)).sz a : ℕ) : ℤ) = (pageWord L j ε τ ψ).sz a :=
    fun a => (hT a).1
  have hη : ∀ a, etaHat L < (recWord L j ε (letter τ ψ)).sz a := fun a => by
    have h6 : ((etaHat L : ℕ) : ℤ) < (pageWord L j ε τ ψ).sz a := hBox.2.2.2.2.2 a
    rw [← hsz a] at h6
    exact_mod_cast h6
  have hSmall : Small (recWord L j ε (letter τ ψ)) :=
    ⟨hBox.1, hBox.2.1, hBox.2.2.1, hBox.2.2.2.1, hBox.2.2.2.2.1, hη⟩
  rcases hcase with ⟨halt, ⟨a, ha⟩, hthree⟩ | ⟨-, ⟨hev, halt, hbig⟩, -⟩
  · left
    refine ⟨hSmall, halt, ⟨a, fun h => ha ((hT a).2.2.2.1 h)⟩, fun i h => hthree i ?_⟩
    exact ⟨(hT _).2.2.2.1 h.1, (hT _).2.2.2.1 h.2.1, (hT _).2.2.2.1 h.2.2⟩
  · right
    haveI : NeZero (orderOf ψ) := ⟨(orderOf_pos ψ).ne'⟩
    obtain ⟨d, hd⟩ := alternates_parity (up := (recWord L j ε (letter τ ψ)).up) halt
    refine ⟨d, hev, hd, hSmall, fun a => ?_, fun M hM a => ?_⟩
    · have hmax : max (etaHat L) ((recWord L j ε (letter τ ψ)).sz a + sHat L) =
          (recWord L j ε (letter τ ψ)).sz a + sHat L := max_eq_right (by have := hη a; omega)
      change (if (!pos ε (letter τ ψ a)) = true then etaHat L else
          max (etaHat L) ((recWord L j ε (letter τ ψ)).sz a + sHat L)) = _ ∧
        (if (!pos ε (letter τ ψ a)) = true then
          max (etaHat L) ((recWord L j ε (letter τ ψ)).sz a + sHat L) else etaHat L) = _
      rw [hmax]
      exact ⟨rfl, rfl⟩
    · have hM' : IsGreatest (Set.range (pageWord L j ε τ ψ).sz) (M : ℤ) := by
        obtain ⟨⟨b, hb⟩, hub⟩ := hM
        refine ⟨⟨b, by rw [← hsz b, hb]⟩, ?_⟩
        rintro _ ⟨c, rfl⟩
        rw [← hsz c]
        exact_mod_cast hub ⟨c, rfl⟩
      obtain ⟨-, h2, h3⟩ := hbig M hM' a
      rw [← hsz a] at h2 h3
      push_cast at h2 h3
      exact ⟨h2, h3⟩

end GlobalTheory.HTW.Rec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordInertDichotomyStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualSizeWord_inert_dichotomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG) (ψ : D.R.GG) (l : ℕ), Roomy L C → IsOrbit g ψ → 11 ≤ l → ψ.1.2 = -1 → WordsNT (recWord L j ε g) ∨ ∃ d, WordsAT l (recWord L j ε g) d := by
  first | exact @GlobalTheory.HTW.Rec.recWord_dichotomy | exact GlobalTheory.HTW.Rec.recWord_dichotomy | (intros; apply GlobalTheory.HTW.Rec.recWord_dichotomy <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeWordConditionsOfLargeScale
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem jointCD_of_large : ∀ eps ez A : ℝ, 0 < eps → 0 < ez → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L)
    (HW : HWOf D.loc), L.sc.eps = eps → L.sc.ez = ez → Pm.CLw ≤ A → x0 ≤ L.sc.x → LocalSituation.adm7 D →
    (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.JointCD L HW := by
  intro eps ez A heps hez
  obtain ⟨x1, h1⟩ := GlobalTheory.T.roomy_of_large_scale eps 100 A heps le_rfl
  obtain ⟨x2, h2⟩ := GlobalTheory.T.eleven_le_inertOddPrimeImagQuadratic_large_scale ez hez
  refine ⟨max x1 x2, ?_⟩
  intro D L Pm HW he hZ hA hx hadm hfont hja i hin r ρ π hpt w hw
  have hR : Roomy L 100 := h1 D L Pm he hA (le_trans (le_max_left _ _) hx)
  have h11 : 11 ≤ D.nd.l i := h2 D L _ hZ (le_trans (le_max_right _ _) hx) Fact.out hin
  have hn2 := hin.ne_two
  have hj := hin.2.2.2
  refine ⟨GlobalTheory.T.placeCompletion_le_maxUnramified_away_2qd D.nbr i w hw hin.1 hin.2.1 hin.2.2.1, ?_⟩
  intro Cx hG
  obtain ⟨ε, g, hg, hB⟩ := GlobalTheory.T.wordConditions_common_natural_representation L 100 HW i r ρ π w hw Cx hG hR hadm hfont hja hpt hin.1 hin.2.1 hin.2.2.1
  have hs := (GlobalTheory.T.frobG_isArithFrobAt_and_sign_eq_jacobiSym D (D.nd.l i) hin.1 hin.2.1 hin.2.2.1).2
  have hm : (DV.frobG D (D.nd.l i)).1.2 = -1 := by
    refine (Int.units_eq_one_or _).resolve_left fun h => hj ?_
    rw [← hs, h]; rfl
  have hm' : ((DV.frobG D (D.nd.l i))⁻¹).1.2 = -1 := by
    change ((DV.frobG D (D.nd.l i)).1.2)⁻¹ = -1
    rw [hm]; rfl
  refine ⟨_, hB, GlobalTheory.T.thickLetterWord_hypotheses_of_common_conditions L HW i r ρ π w hw Cx hG _ hn2 hB, h11,
    GlobalTheory.T.twistedDualSizeWord_boxesAndSizes L 100 _ ε g _ hR hg, ?_⟩
  rcases GlobalTheory.T.twistedDualSizeWord_inert_dichotomy L 100 _ ε g _ _ hR hg h11 hm' with h | ⟨d, hd⟩
  · exact Or.inl h
  · exact Or.inr ⟨d, hd, GlobalTheory.T.alternatingWord_hypotheses_every_lattice_surjection L HW i r ρ π w hw Cx hG _ d h11 hB hd⟩

end GlobalTheory.HTW.RecS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPrimeWordConditionsOfLargeScaleStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPrimeWordConditions_of_large_scale : ∀ eps ez A : ℝ, 0 < eps → 0 < ez → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (HW : HWOf D.loc), L.sc.eps = eps → L.sc.ez = ez → Pm.CLw ≤ A → x0 ≤ L.sc.x → LocalSituation.adm7 D → (∀ i, TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → LJ.ConclusionJa D → RecS.JointCD L HW := by
  first | exact @GlobalTheory.HTW.RecS.jointCD_of_large | exact GlobalTheory.HTW.RecS.jointCD_of_large | (intros; apply GlobalTheory.HTW.RecS.jointCD_of_large <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamJEpsPos
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem famJ_CLw_eq {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    (Fm.params x hx i).CLw = Fm.PK.getD 7 0 := by
  rw [← Fm.params_K x hx i]
  rfl

theorem famJ_eps_pos {eps : ℝ} (Fm : FamP eps) : 0 < eps := by
  obtain ⟨i⟩ := Fm.Ix_zero
  rw [← Fm.L_eps 0 i]
  exact (Fm.L 0 i).sc.eps_pos

theorem famJ_ez_pos {eps : ℝ} (Fm : FamP eps) : 0 < Fm.ez := by
  obtain ⟨i⟩ := Fm.Ix_zero
  rw [← Fm.L_ez 0 i]
  exact (Fm.L 0 i).sc.ez_pos

theorem fam_joints : ∀ {eps : ℝ} (Fm : FamP eps) (C₂ : ℝ), (∀ D : D7, LocalSituation.adm7 D) →
    (∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) →
    ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) (HW : HWOf (Fm.D x i).loc),
      LJ.ConclusionJa (Fm.D x i) → RecS.JointB (Fm.L x i) HW C₂ ∧ RecS.JointCD (Fm.L x i) HW := by
  intro eps Fm C₂ h7 hF
  obtain ⟨xB, hB⟩ := GlobalTheory.T.inertLongOrbitWordConditions_of_large_scale eps Fm.ez C₂ (Fm.PK.getD 7 0) (famJ_eps_pos Fm) (famJ_ez_pos Fm)
  obtain ⟨xC, hC⟩ := GlobalTheory.T.inertPrimeWordConditions_of_large_scale eps Fm.ez (Fm.PK.getD 7 0) (famJ_eps_pos Fm) (famJ_ez_pos Fm)
  refine ⟨max xB xC, fun x hx h1 i HW hJ => ⟨?_, ?_⟩⟩
  · refine hB _ _ (Fm.params x h1 i) HW (Fm.L_eps x i) (Fm.L_ez x i) (famJ_CLw_eq Fm x h1 i).le ?_ (h7 _) (hF _) hJ
    rw [Fm.L_x x i h1]
    exact (le_max_left _ _).trans hx
  · refine hC _ _ (Fm.params x h1 i) HW (Fm.L_eps x i) (Fm.L_ez x i) (famJ_CLw_eq Fm x h1 i).le ?_ (h7 _) (hF _) hJ
    rw [Fm.L_x x i h1]
    exact (le_max_right _ _).trans hx

end GlobalTheory.HTW.RecS
end

open NumberField IsDedekindDomain Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem HTW.RecS.fam_jointBCD : ∀ {eps : ℝ} (Fm : FamP eps) (R : KillingConditions.RowK), (∀ D : D7, LocalSituation.adm7 D) → (∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (j : Fm.Ix x) (HW : HWOf (Fm.D x j).loc) (X : KillingConditions.HubData (Fm.D x j)), GlobalTheory.HTW.LJ.ConclusionJa (Fm.D x j) → (∀ i, TwistedPlaces.TwLoc (Fm.D x j) i → TwistedPlaces.InertK (Fm.D x j) ((Fm.D x j).nd.l i) → ∀ π ∈ (Fm.D x j).nd.Zgood i, GlobalTheory.HTW.RecS.PtIn i (X.r i) (X.ρ i) π) → KillingConditions.JointParametersHubConditions (Fm.L x j) HW X R := by
  intro eps Fm R a b
  obtain ⟨x0, h⟩ := GlobalTheory.HTW.RecS.fam_joints Fm R.C₂ a b
  exact ⟨x0, fun x hx h1 j HW X hJ hP =>
    GlobalTheory.Survey.ClusteredLetterwiseBoxes.frozenBCD_of _ HW X R (h x hx h1 j HW hJ).1 (h x hx h1 j HW hJ).2 hP⟩

end GlobalTheory
