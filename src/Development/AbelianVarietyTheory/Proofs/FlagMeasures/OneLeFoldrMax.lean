module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeAbsolutelyConvergentOperatorNormLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureEqNormalFormRootMeasure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataBothAmplitudeSides

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellPointBlockEndsLeadingMinors
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellPointBlockEndsLeadingMinors
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.PtMinor

noncomputable def minor (bs : List (ℂ × ℕ)) (m : ℕ) : ℂ := (Matrix.of fun a b : Fin m => ptEntry bs a b).det

def ends (c : ℕ) (bs : List (ℂ × ℕ)) : List ℕ := ((bs.map Prod.snd).scanl (· + ·) c).tail

theorem ends_nil (c : ℕ) : ends c [] = [] := by simp [ends]

theorem ends_cons (c : ℕ) (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) :
    ends c ((t, s) :: bs) = (c + s) :: ends (c + s) bs := by
  cases bs <;> simp [ends]

theorem det_anti (t : ℂ) (ht : t ≠ 0) (s : ℕ) :
    (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0).det ≠ 0 := by
  have : (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0) =
      (Matrix.diagonal fun _ : Fin s => t).submatrix (Fin.revPerm : Equiv.Perm (Fin s)) id := by
    ext a b
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.diagonal_apply, Fin.revPerm_apply, id, Fin.ext_iff,
      Fin.val_rev]
    have := a.2
    exact if_congr (by omega) rfl rfl
  rw [this, Matrix.det_permute]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s))) with h | h <;> simp [h, ht]

theorem minor_cons (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) (m : ℕ) :
    minor ((t, s) :: bs) (s + m) =
      (Matrix.of fun a b : Fin s => if a.val + b.val + 1 = s then t else 0).det * minor bs m := by
  unfold minor
  rw [← Matrix.det_fromBlocks_zero₂₁ _ (0 : Matrix (Fin s) (Fin m) ℂ),
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv]
  congr 1
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [ptEntry]

theorem minor_lt (t : ℂ) (s : ℕ) (bs : List (ℂ × ℕ)) (m : ℕ) (h1 : 1 ≤ m) (h2 : m < s) :
    minor ((t, s) :: bs) m = 0 := by
  unfold minor
  refine Matrix.det_eq_zero_of_row_eq_zero ⟨0, h1⟩ fun j => ?_
  have := j.2
  simp only [Matrix.of_apply, ptEntry]
  split_ifs <;> first | rfl | omega

theorem ends_bd (bs : List (ℂ × ℕ)) (h : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) (c : ℕ) :
    (∀ x ∈ ends c bs, c < x ∧ x ≤ c + (bs.map Prod.snd).sum) ∧ (ends c bs).Nodup ∧
      (bs ≠ [] → c + (bs.map Prod.snd).sum ∈ ends c bs) := by
  induction bs generalizing c with
  | nil => simp [ends_nil]
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    have hs : 1 ≤ s := (h (t, s) (by simp)).2
    obtain ⟨i1, i2, i3⟩ := ih (fun b hb => h b (by simp [hb])) (c + s)
    rw [ends_cons]
    simp only [List.map_cons, List.sum_cons, List.mem_cons, List.nodup_cons]
    refine ⟨?_, ⟨fun hm => ?_, i2⟩, fun _ => ?_⟩
    · rintro x (rfl | hx)
      · omega
      · have := i1 x hx
        omega
    · have := i1 _ hm
      omega
    · by_cases hb : bs = []
      · subst hb; simp
      · right
        rw [← add_assoc]
        exact i3 hb

theorem minor_ne_iff (bs : List (ℂ × ℕ)) (h : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) (c l : ℕ) (hl : 1 ≤ l) :
    minor bs l ≠ 0 ↔ c + l ∈ ends c bs := by
  induction bs generalizing c l with
  | nil =>
    have : minor [] l = 0 := Matrix.det_eq_zero_of_row_eq_zero ⟨0, hl⟩ fun j => by simp [ptEntry]
    simp [this, ends_nil]
  | cons p bs ih =>
    obtain ⟨t, s⟩ := p
    have ht : t ≠ 0 := (h (t, s) (by simp)).1
    have h' : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b hb => h b (by simp [hb])
    have hb := (ends_bd bs h' (c + s)).1
    rw [ends_cons, List.mem_cons]
    rcases lt_or_ge l s with hls | hls
    · rw [minor_lt t s bs l hl hls]
      refine ⟨fun h0 => absurd rfl h0, ?_⟩
      rintro (h1 | h1)
      · omega
      · have := hb _ h1
        omega
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hls
      rw [minor_cons, mul_ne_zero_iff, and_iff_right (det_anti t ht s)]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [minor]
      · rw [ih h' (c + s) m hm, add_assoc]
        refine ⟨Or.inr, ?_⟩
        rintro (h1 | h1)
        · omega
        · exact h1

theorem one_le_max_inv (x : ℝ) (hx : 0 < x) : 1 ≤ max x x⁻¹ := by
  rcases le_total 1 x with h | h
  · exact le_max_of_le_left h
  · exact le_max_of_le_right ((one_le_inv₀ hx).2 h)

theorem list_prod (L : List ℕ) (f : ℕ → ℝ) (hf : ∀ l ∈ L, 1 ≤ f l) (a a' : ℝ) (ha : 0 ≤ a) (ha' : a ≤ a') :
    1 ≤ (L.map fun l => f l ^ a).prod ∧ (L.map fun l => f l ^ a).prod ≤ (L.map fun l => f l ^ a').prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    obtain ⟨i1, i2⟩ := ih fun l hl => hf l (by simp [hl])
    have hx : 1 ≤ f x := hf x (by simp)
    have h1 := Real.one_le_rpow hx ha
    have h2 := Real.rpow_le_rpow_of_exponent_le hx ha'
    simp only [List.map_cons, List.prod_cons]
    exact ⟨one_le_mul_of_one_le_of_one_le h1 i1, mul_le_mul h2 i2 (by linarith) (by linarith)⟩

theorem one_le_foldr (L : List ℝ) : 1 ≤ L.foldr max 1 := by
  induction L with
  | nil => simp
  | cons x L ih => exact le_max_of_le_right ih

theorem blockEnds_minors : ∀ (D : D7) (z z' : (Fin (2 * D.R.rS + D.R.k + 1) → ℂ)) (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)), inWb D.R.k D.R.rS z → inWb D.R.k D.R.rS z' → 0 < Tz D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z' → RelPt D z z' γ p → (∀ l : ℕ, 1 ≤ l → (DminN z z' γ l ≠ 0 ↔ l ∈ ptBlockEnds p)) ∧ (ptBlockEnds p).Nodup ∧ (∀ l ∈ ptBlockEnds p, 1 ≤ l ∧ l ≤ D.R.rS + 1) ∧ D.R.rS + 1 ∈ ptBlockEnds p ∧ DminN z z' γ 0 = 1 ∧ 0 < Gf D.R.k D.R.rS z z' γ ∧ Gf D.R.k D.R.rS z z' γ ≤ ‖DminN z z' γ (D.R.rS + 1)‖ ^ 2 ∧ ∀ b C C₂ : ℝ, 1 ≤ b → 0 ≤ C → C ≤ C₂ → 1 ≤ lossV b C D.R.m z z' γ p ∧ lossV b C D.R.m z z' γ p ≤ lossV b C₂ D.R.m z z' γ p ∧ 1 ≤ lossP b C D.R.m z z' γ p ∧ lossP b C D.R.m z z' γ p ≤ lossP b C₂ D.R.m z z' γ p := by
  intro D z z' γ p hz hz' hT hT' hRel
  obtain ⟨hU, ⟨L, U, hL, hU', hZ⟩, hG⟩ := hRel
  have hp := p.2.1
  have hsum := p.2.2
  obtain ⟨e1, e2, e3⟩ := ends_bd p.1 hp 0
  rw [zero_add, hsum] at e1 e3
  have key : ∀ (l : ℕ) (hl : l ≤ D.R.rS + 1),
      Complex.normSq (DminN z z' γ l) = Complex.normSq (minor p.1 l) := by
    intro l hl
    have h1 := Formalism.MainNotions.S.Bridge.normSq_leadMinor_ZhatO D.R.k D.R.rS z z' γ l hl
    rw [hZ, Formalism.MainNotions.S.Bridge.leadMinor_cell L (ptMat p) U hL hU' l hl] at h1
    rw [DminN, dite_eq_left (Nat.lt_succ_of_le hl)]
    exact h1.symm
  have hiff : ∀ l : ℕ, 1 ≤ l → (DminN z z' γ l ≠ 0 ↔ l ∈ ptBlockEnds p) := by
    intro l hl
    by_cases hl' : l ≤ D.R.rS + 1
    · have h2 := minor_ne_iff p.1 hp 0 l hl
      rw [zero_add] at h2
      rw [Ne, ← Complex.normSq_eq_zero, key l hl', Complex.normSq_eq_zero]
      exact h2
    · rw [DminN, dite_eq_right (by omega)]
      exact ⟨fun h0 => absurd rfl h0, fun hm => absurd (e1 l hm).2 hl'⟩
  have hG0 : 0 < Gf D.R.k D.R.rS z z' γ :=
    lt_of_le_of_ne (Formalism.QuantumDeterminants.gNonneg D.R.k D.R.rS z z' hz hz' hT hT' γ hU) (Ne.symm hG)
  refine ⟨hiff, e2, fun l hl => e1 l hl, e3 fun h0 => ?_, ?_, hG0, ?_, fun b C C₂ hb hC hC2 => ?_⟩
  · rw [h0] at hsum
    simp at hsum
  · simp [DminN, Formalism.QuantumDeterminants.Dmin]
  · rw [DminN, dite_eq_left (by omega), ← Complex.normSq_eq_norm_sq]
    have := mul_nonneg (mul_pos hT hT').le
      (Complex.normSq_nonneg (Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS z z' γ ⟨D.R.rS, by omega⟩))
    exact sub_le_self _ this
  · have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
    have hr : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
    have ex : ∀ x : ℝ, 0 ≤ x → 0 ≤ C * x ∧ C * x ≤ C₂ * x := fun x hx =>
      ⟨mul_nonneg hC hx, mul_le_mul_of_nonneg_right hC2 hx⟩
    obtain ⟨p1, p2⟩ := list_prod (ptBlockEnds p) (fun l => max ‖DminN z z' γ l‖ ‖DminN z z' γ l‖⁻¹)
      (fun l hl => one_le_max_inv _ (norm_pos_iff.2 ((hiff l (e1 l hl).1).2 hl))) _ _ (ex _ hm).1 (ex _ hm).2
    have g := one_le_max_inv _ hG0
    have a1 := Real.one_le_rpow hb (ex _ (pow_nonneg hm 4)).1
    have a2 := Real.rpow_le_rpow_of_exponent_le hb (ex _ (pow_nonneg hm 4)).2
    have g1 := Real.one_le_rpow g (ex _ (pow_nonneg hm 2)).1
    have g2 := Real.rpow_le_rpow_of_exponent_le g (ex _ (pow_nonneg hm 2)).2
    have c1 := Real.one_le_rpow hb (ex _ hm).1
    have c2 := Real.rpow_le_rpow_of_exponent_le hb (ex _ hm).2
    have f := one_le_foldr ((ptBlockEnds p).map fun l => max 1 ‖DminN z z' γ l‖⁻¹)
    have q1 := one_le_mul_of_one_le_of_one_le c1 f
    have q2 := mul_le_mul_of_nonneg_right c2 (zero_le_one.trans f)
    refine ⟨one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le a1 g1) p1, ?_,
      Real.one_le_rpow q1 (ex _ (pow_nonneg hr 3)).1, ?_⟩
    · exact mul_le_mul (mul_le_mul a2 g2 (by linarith) (by linarith)) p2 (by linarith)
        (mul_nonneg (by linarith) (by linarith))
    · exact (Real.rpow_le_rpow (by linarith) q2 (ex _ (pow_nonneg hr 3)).1).trans
        (Real.rpow_le_rpow_of_exponent_le (q1.trans q2) (ex _ (pow_nonneg hr 3)).2)

end GlobalTheory.Amp.PtMinor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellPointBlockEndsLeadingMinorsStatement
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cellPoint_blockEnds_leadingMinors : ∀ (D : D7) (z z' : (Fin (2 * D.R.rS + D.R.k + 1) → ℂ)) (γ : MatKR D.R.k D.R.rS) (p : Point ℂ (D.R.rS + 1)), inWb D.R.k D.R.rS z → inWb D.R.k D.R.rS z' → 0 < Tz D.R.k D.R.rS z → 0 < Tz D.R.k D.R.rS z' → RelPt D z z' γ p → (∀ l : ℕ, 1 ≤ l → (DminN z z' γ l ≠ 0 ↔ l ∈ ptBlockEnds p)) ∧ (ptBlockEnds p).Nodup ∧ (∀ l ∈ ptBlockEnds p, 1 ≤ l ∧ l ≤ D.R.rS + 1) ∧ D.R.rS + 1 ∈ ptBlockEnds p ∧ DminN z z' γ 0 = 1 ∧ 0 < Gf D.R.k D.R.rS z z' γ ∧ Gf D.R.k D.R.rS z z' γ ≤ ‖DminN z z' γ (D.R.rS + 1)‖ ^ 2 ∧ ∀ b C C₂ : ℝ, 1 ≤ b → 0 ≤ C → C ≤ C₂ → 1 ≤ lossV b C D.R.m z z' γ p ∧ lossV b C D.R.m z z' γ p ≤ lossV b C₂ D.R.m z z' γ p ∧ 1 ≤ lossP b C D.R.m z z' γ p ∧ lossP b C D.R.m z z' γ p ≤ lossP b C₂ D.R.m z z' γ p := by
  first | exact @GlobalTheory.Amp.PtMinor.blockEnds_minors | exact GlobalTheory.Amp.PtMinor.blockEnds_minors | (intros; apply GlobalTheory.Amp.PtMinor.blockEnds_minors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantMomentBoundBothSides
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantMomentBoundBothSides
noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.MomBoth

def swapW {k r : ℕ} (W : LocW k r) : LocW k r where
  Wp := W.Wq
  Wq := W.Wp
  π := W.π'
  π' := W.π
  z := W.z'
  z' := W.z
  μG := W.μG
  μW := W.μW'
  μW' := W.μW
  μN := W.μN
  νS := W.νS'
  νS' := W.νS

def swapS {k r : ℕ} {W : LocW k r} (A : LocS W) : LocS (swapW W) where
  H := A.H
  σ := A.σ
  B := A.B'
  B' := A.B
  v0 := A.v0
  cN := A.cN
  deg := A.deg

theorem goodW_swap {D : D7} {τ : D.what₂.Tau} {w w' : D.what₂.Word} {θ : ℝ} {W : LocW D.R.k D.R.rS}
    (h : GoodW D τ w w' θ W) : GoodW D τ w' w θ (swapW W) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h2, h1, h4, h3, h6, h5, h7, h10, h11, h8, h9, h12, h14, h13⟩

theorem goodS_swap {D : D7} {W : LocW D.R.k D.R.rS} {lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} {A : LocS W}
    (h : GoodS D lam A) : GoodS D lam (swapS A) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h4, h3, h5, h6, h7, h8, h10, h9, h11⟩

theorem hypTT_swap {D : D7} {w w' : D.what₂.Word} (h : HypTT D w w') : HypTT D w' w := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h2, h1, h4, h3, h5.symm⟩

theorem one_le_b (s : Scale) : 1 ≤ s.b := by
  unfold Scale.b Scale.L
  exact Real.one_le_exp (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _)

theorem momBd_one (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 CMo : ℝ) (hm : 4 ≤ D.R.m)
    (hM : MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 25 CMo) (hZ : HypZ D large₂ C' Cl Cg cb Cu cT CT C0)
    (τ : D.what₂.Tau) (w w' : D.what₂.Word) (hT : HypTT D w w') (θ : ℝ) (hθ : normWin D large₂ C1 θ)
    (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (hl : l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3) (S : LocS W) (hS : GoodS D lam' S) :
    MomBd W.z W.νS S.Φ (24 * D.R.rS ^ 3 + 1) (large₂.sc.b ^ (max CMo 0 * D.R.m)) := by
  intro a
  have hr : 1 ≤ D.R.rS := by unfold Ranks.rS; omega
  have hr3 : (1 : ℝ) ≤ (D.R.rS : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hr)
  have hb := one_le_b large₂.sc
  have h := hM hZ τ w w' hT θ hθ W hW lam' hl S hS a (24 * D.R.rS ^ 3 + 1) (by push_cast; linarith)
  refine h.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
  refine Real.rpow_le_rpow_of_exponent_le hb ?_
  have h1 : CMo ≤ max CMo 0 := le_max_left _ _
  have h2 : (0 : ℝ) ≤ (D.R.m : ℝ) * ((24 * D.R.rS ^ 3 + 1 : ℕ) : ℝ) := by positivity
  have h3 := mul_le_mul_of_nonneg_right h1 h2
  rw [Nat.cast_mul 2, Nat.cast_ofNat]
  nlinarith

theorem momBd_both : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 CMo : ℝ), 4 ≤ D.R.m →
    MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 25 CMo → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
    ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ S : LocS W, GoodS D lam' S →
      MomBd W.z W.νS S.Φ (24 * D.R.rS ^ 3 + 1) (large₂.sc.b ^ (max CMo 0 * D.R.m)) ∧
      MomBd W.z' W.νS' S.Φ' (24 * D.R.rS ^ 3 + 1) (large₂.sc.b ^ (max CMo 0 * D.R.m)) := by
  intro D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CMo hm hM hZ τ w w' hT θ hθ W hW lam' hl S hS
  exact ⟨momBd_one D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CMo hm hM hZ τ w w' hT θ hθ W hW lam' hl S hS,
    momBd_one D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CMo hm hM hZ τ w' w (hypTT_swap hT) θ hθ (swapW W)
      (goodW_swap hW) lam' hl (swapS S) (goodS_swap hS)⟩

end GlobalTheory.Amp.MomBoth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantMomentBoundBothSidesStatement
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorantMomentBound_both_sides : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 CMo : ℝ), 4 ≤ D.R.m → MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 25 CMo → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W → ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ S : LocS W, GoodS D lam' S → MomBd W.z W.νS S.Φ (24 * D.R.rS ^ 3 + 1) (large₂.sc.b ^ (max CMo 0 * D.R.m)) ∧ MomBd W.z' W.νS' S.Φ' (24 * D.R.rS ^ 3 + 1) (large₂.sc.b ^ (max CMo 0 * D.R.m)) := by
  first | exact @GlobalTheory.Amp.MomBoth.momBd_both | exact GlobalTheory.Amp.MomBoth.momBd_both | (intros; apply GlobalTheory.Amp.MomBoth.momBd_both <;> assumption)
end
end

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.AbsRange

theorem one_le_foldr_max (L : List ℝ) : 1 ≤ L.foldr max 1 := by
  induction L with
  | nil => simp
  | cons a L ih => exact le_trans ih (le_max_right _ _)

theorem le_foldr_max (L : List ℝ) (x : ℝ) (hx : x ∈ L) : x ≤ L.foldr max 1 := by
  induction L with
  | nil => simp at hx
  | cons a L ih =>
    rcases List.mem_cons.1 hx with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem ratio_le (r k N e : ℕ) (b v g θ θ' ka X Cg : ℝ) (hb : 2 ≤ b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b) (hg : 1 ≤ g)
    (hgb : g ≤ b ^ (2 * Cg)) (hka : ka = Real.pi / v) (hθ0 : 0 < θ) (hθ : θ ≤ b ^ X) (hθ' : b ^ (-X) ≤ θ')
    (hN : N ≤ r ^ 2) (he : e ≤ r * k) :
    (2 * v) ^ (-((r : ℝ) * k)) * θ * 2 ^ (r * (k + 1) + r * (r - 1)) / (θ' * (2 * ka / g / (2 * Real.pi)) ^ N) ≤
      b ^ (2 * X + (2 + 2 * Cg) * (r : ℝ) ^ 2) * v⁻¹ ^ e := by
  have hb0 : 0 < b := by linarith
  have hv0 : 0 < v := by linarith
  have hg0 : 0 < g := by linarith
  have hθ'0 : 0 < θ' := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ'
  have hpi := Real.pi_pos
  have e1 : r * (k + 1) + r * (r - 1) = r * k + r ^ 2 := by
    cases r with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel]; ring
  have e2 : (2 * v) ^ (-((r : ℝ) * k)) = ((2 * v) ^ (r * k))⁻¹ := by
    rw [Real.rpow_neg (by positivity), ← Real.rpow_natCast]; push_cast; rfl
  have e3 : 2 * ka / g / (2 * Real.pi) = (v * g)⁻¹ := by
    rw [hka]; field_simp
  have e4 : (2 * v) ^ (-((r : ℝ) * k)) * θ * 2 ^ (r * (k + 1) + r * (r - 1)) / (θ' * (2 * ka / g / (2 * Real.pi)) ^ N)
      = (θ * θ'⁻¹ * (2 ^ (r ^ 2) * (v * g) ^ N)) * v⁻¹ ^ (r * k) := by
    rw [e1, e2, e3, pow_add, mul_pow 2 v, inv_pow, inv_pow]
    field_simp
  rw [e4]
  have h1 : θ'⁻¹ ≤ b ^ X := by
    have := inv_anti₀ (Real.rpow_pos_of_pos hb0 _) hθ'
    rwa [Real.rpow_neg hb0.le, inv_inv] at this
  have h2 : (v * g) ^ N ≤ (b * b ^ (2 * Cg)) ^ (r ^ 2) := by
    refine le_trans (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hv hg) hN) ?_
    exact pow_le_pow_left₀ (by positivity) (mul_le_mul (by linarith) hgb hg0.le hb0.le) _
  have h3 : (2 : ℝ) ^ (r ^ 2) ≤ b ^ (r ^ 2) := pow_le_pow_left₀ (by norm_num) hb _
  have h4 : v⁻¹ ^ (r * k) ≤ v⁻¹ ^ e := pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hv) he
  have e5 : b ^ (2 * X + (2 + 2 * Cg) * (r : ℝ) ^ 2) =
      b ^ X * b ^ X * (b ^ (r ^ 2) * (b * b ^ (2 * Cg)) ^ (r ^ 2)) := by
    rw [← mul_pow, ← mul_assoc, ← Real.rpow_add hb0, Real.rpow_add hb0 (2 * X), Real.rpow_mul hb0.le (2 + 2 * Cg),
      Real.rpow_add hb0 2, Real.rpow_two, two_mul X, sq b, ← Real.rpow_natCast _ (r ^ 2)]
    push_cast; rfl
  rw [e5]
  gcongr

theorem absBd_le (r k : ℕ) (b v Q A De Dd C M m : ℝ) (hr : 1 ≤ r) (hm : m = 2 * r + 2) (hb : Real.exp 1 ≤ b)
    (hv : 0 < v) (hM : 0 ≤ M) (hDe : 1 ≤ De) (hD : 0 ≤ Dd)
    (hQ : Q ≤ b ^ (A * (m * (r : ℝ) ^ 3)) * v⁻¹ ^ (r * (k - 2 - r)))
    (hC : A + 44 + 24 * M ≤ C) (hC1 : 14 ≤ C) (hC2 : 8 * Real.pi * Real.exp 1 ≤ C) :
    Q * absBd k r (b ^ (M * m)) De Dd ≤
      (b ^ (C * m) * De) ^ (C * (r : ℝ) ^ 3) * (C / (k * v)) ^ (r * (k - 2 - r)) * (Dd ^ (k - 2 - r))⁻¹ := by
  have hb1 : 1 ≤ b := le_trans (Real.one_le_exp (by norm_num)) hb
  have hb0 : 0 < b := by linarith
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hm0 : 0 ≤ m := by linarith
  have hpi := Real.pi_pos
  have h1 : (4 * r : ℝ) ≤ b ^ m := by
    have a1 : Real.exp m ≤ b ^ m := by
      rw [← Real.exp_one_rpow]; exact Real.rpow_le_rpow (Real.exp_pos 1).le hb hm0
    have a2 : (r : ℝ) + 1 + 1 ≤ Real.exp (r + 1) := Real.add_one_le_exp _
    have a3 : Real.exp m = Real.exp (r + 1) * Real.exp (r + 1) := by rw [← Real.exp_add, hm]; ring_nf
    nlinarith
  have h2 : (4 * r : ℝ) ^ (44 * r ^ 3) ≤ b ^ (44 * (m * (r : ℝ) ^ 3)) := by
    refine le_trans (pow_le_pow_left₀ (by positivity) h1 _) (le_of_eq ?_)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]; push_cast; ring_nf
  have h3 : (b ^ (M * m)) ^ (24 * r ^ 3) = b ^ (24 * M * (m * (r : ℝ) ^ 3)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le]; push_cast; ring_nf
  have h4 : De ^ (14 * r ^ 2) ≤ De ^ (C * (r : ℝ) ^ 3) := by
    rw [← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hDe ?_
    push_cast
    have : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 3 := pow_le_pow_right₀ hr' (by norm_num)
    exact mul_le_mul hC1 this (by positivity) (by linarith)
  have h5 : (8 * Real.pi * Real.exp 1 / k) ^ (r * (k - 2 - r)) ≤ (C / k) ^ (r * (k - 2 - r)) := by
    gcongr
  have h6 : b ^ (A * (m * (r : ℝ) ^ 3)) * b ^ (44 * (m * (r : ℝ) ^ 3)) * b ^ (24 * M * (m * (r : ℝ) ^ 3)) ≤
      (b ^ (C * m)) ^ (C * (r : ℝ) ^ 3) := by
    rw [← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_mul hb0.le]
    refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
    have t : 0 ≤ m * (r : ℝ) ^ 3 := by positivity
    have c : A + 44 + 24 * M ≤ C * C := by nlinarith
    have := mul_le_mul_of_nonneg_right c t
    nlinarith
  have hC0 : 0 ≤ C := by linarith
  calc Q * absBd k r (b ^ (M * m)) De Dd
      ≤ (b ^ (A * (m * (r : ℝ) ^ 3)) * v⁻¹ ^ (r * (k - 2 - r))) *
        (b ^ (44 * (m * (r : ℝ) ^ 3)) * b ^ (24 * M * (m * (r : ℝ) ^ 3)) * De ^ (C * (r : ℝ) ^ 3) *
          (C / k) ^ (r * (k - 2 - r)) * (Dd ^ (k - 2 - r))⁻¹) := by
        unfold absBd
        rw [h3]
        refine mul_le_mul hQ ?_ (by positivity) (by positivity)
        gcongr
    _ = (b ^ (A * (m * (r : ℝ) ^ 3)) * b ^ (44 * (m * (r : ℝ) ^ 3)) * b ^ (24 * M * (m * (r : ℝ) ^ 3))) *
          De ^ (C * (r : ℝ) ^ 3) * (C / (k * v)) ^ (r * (k - 2 - r)) * (Dd ^ (k - 2 - r))⁻¹ := by
        rw [show C / (k * v) = C / k * v⁻¹ by rw [← div_div, div_eq_mul_inv], mul_pow]; ring
    _ ≤ _ := by
        rw [Real.mul_rpow (by positivity) (by linarith)]
        gcongr

theorem abs_range : ∀ Cg cb Cu cT CT C0 C1 CMo : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ m₀ : ℝ, ∀ Cn : ℝ,
    ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), Big D large₂ Cl m₀ → MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 25 CMo →
      ABSr D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro Cg cb Cu cT CT C0 C1 CMo
  refine ⟨8 * |C1| + 2 * |Cg| + 46 + 24 * max CMo 0 + 8 * Real.pi * Real.exp 1, fun C hC => ⟨4, ?_⟩⟩
  intro Cn D large₂ C' Cl hBig hMom hZ τ w w' hTT θ hθ W hW lam' hlam S hS γ p hp θ' hθ' νR hνR hDr
  obtain ⟨hrd, -, hm4⟩ := hBig
  have hm4' : 4 ≤ D.R.m := by exact_mod_cast hm4
  obtain ⟨-, -, hb, hm, -, -, -, hk, hv, -, hka, hvb, hg, hgb, -⟩ :=
    GlobalTheory.T.amplitudeSizeConsequences_of_wordIndependentHyps D large₂ C' Cl Cg cb Cu cT CT C0 hrd hZ
  have hb2 : 2 ≤ large₂.sc.b := by linarith
  have hb0 : 0 < large₂.sc.b := by linarith
  have hv0 : 0 < D.host.v := by linarith
  have hg0 : 0 < gg D := by linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ.1
  have hθ'0 : 0 < θ' := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ'.1
  have hpi := Real.pi_pos
  have hka0 : 0 < D.host.ka := by rw [hka]; positivity
  have hr : 1 ≤ D.R.rS := by omega
  have hk' : 2 * D.R.rS + 6 ≤ D.R.k := by
    have : D.R.m * 2 ≤ D.R.m ^ 4 := by
      rw [show D.R.m ^ 4 = D.R.m * D.R.m ^ 3 by ring]
      exact Nat.mul_le_mul_left _ (le_trans (by norm_num) (Nat.pow_le_pow_left hm4' 3))
    omega
  obtain ⟨hM1, hM2⟩ := GlobalTheory.T.majorantMomentBound_both_sides D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CMo hm4' hMom hZ τ w w' hTT θ hθ W hW
    lam' hlam S hS
  obtain ⟨-, -, hμN, hS1, hS2⟩ := GlobalTheory.T.local_data_both_amplitude_sides D τ w w' θ W lam' S hθ0 hv0 hTT hW hS
  rw [hμN] at hS1 hS2
  have hDr' : Dr D.R.k D.R.rS W.z W.z' γ = ‖DminN W.z W.z' γ D.R.rS‖ := by
    unfold Dr DminN; rw [dite_eq_left (by omega)]
  have hTF : TwoFl D.R.k D.R.rS W.z W.z' γ :=
    ⟨hS1.1, hS2.1, hS1.2.1, hS2.2.1, hp.1, hp.2.2, by rw [hDr']; exact norm_ne_zero_iff.2 hDr⟩
  obtain ⟨hends, -, -, -, hD0, -⟩ := GlobalTheory.T.cellPoint_blockEnds_leadingMinors D W.z W.z' γ p hS1.1 hS2.1 hS1.2.1 hS2.2.1 hp
  set De : ℝ := ((ptBlockEnds p).map fun l => max 1 ‖DminN W.z W.z' γ l‖⁻¹).foldr max 1 with hDe
  have hDe1 : 1 ≤ De := one_le_foldr_max _
  have hOK : DeOK D.R.k D.R.rS W.z W.z' γ De := by
    refine ⟨hDe1, fun l _ hl => ?_⟩
    have e : Dmin D.R.k D.R.rS W.z W.z' γ l = DminN W.z W.z' γ l.val := by
      unfold DminN; rw [dite_eq_left l.2]
    rw [e] at hl ⊢
    rcases Nat.eq_zero_or_pos l.val with h0 | h0
    · rw [h0, hD0]; simpa using hDe1
    · exact le_trans (le_max_right 1 _)
        (le_foldr_max _ _ (List.mem_map.2 ⟨l.val, (hends l.val h0).1 hl, rfl⟩))
  obtain ⟨p', μR, hroot, hquot⟩ := hνR
  obtain ⟨hN, hnorm⟩ := GlobalTheory.T.rootMeasure_eq_normalFormRootMeasure D W.z W.z' p' γ μR θ' hTF hroot hθ'0.le (by positivity)
  have hM0 : 0 ≤ max CMo 0 := le_max_right _ _
  have hH : 1 ≤ large₂.sc.b ^ (max CMo 0 * D.R.m) := Real.one_le_rpow (by linarith) (by positivity)
  obtain ⟨hint, hbd⟩ := GlobalTheory.T.amplitude_absolutelyConvergent_operatorNorm_le D.R.k D.R.rS W.z W.z' W.π W.π' _ _ W.μG W.μW W.μW' W.νS W.νS' _ νR S.Φ S.Φ' γ
    S.cN _ _ _ De hr hk' (by positivity) (by positivity) hH hS1 hS2 hM1 hM2 hTF hOK hnorm hquot
  refine ⟨hint, le_trans hbd ?_⟩
  rw [hDr']
  have hmr : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by exact_mod_cast hm
  have hr' : (1 : ℝ) ≤ D.R.rS := by exact_mod_cast hr
  have a1 := abs_nonneg C1
  have a2 := abs_nonneg Cg
  have a3 : 0 ≤ 8 * Real.pi * Real.exp 1 := by positivity
  refine absBd_le D.R.rS D.R.k large₂.sc.b D.host.v _ (8 * |C1| + 2 * |Cg| + 2) De _ C (max CMo 0) D.R.m hr hmr hb.le hv0
    hM0 hDe1 (norm_nonneg _) ?_ (by linarith) (by linarith) (by linarith)
  refine le_trans (ratio_le D.R.rS D.R.k _ (D.R.rS * (D.R.k - 2 - D.R.rS)) large₂.sc.b D.host.v (gg D) θ θ' D.host.ka _ Cg
    hb2 hv hvb hg hgb hka hθ0 hθ.2 hθ'.1 hN (Nat.mul_le_mul_left _ (by omega))) ?_
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith) ?_) (by positivity)
  have r3 : (D.R.rS : ℝ) ≤ (D.R.rS : ℝ) ^ 3 := le_self_pow₀ hr' (by norm_num)
  have r23 : (D.R.rS : ℝ) ^ 2 ≤ (D.R.rS : ℝ) ^ 3 := pow_le_pow_right₀ hr' (by norm_num)
  have m0 : (1 : ℝ) ≤ D.R.m := by linarith
  have b1 : (D.R.m : ℝ) ^ 2 ≤ 4 * (D.R.m * (D.R.rS : ℝ) ^ 3) := by
    have : (D.R.m : ℝ) ≤ 4 * (D.R.rS : ℝ) ^ 3 := by linarith
    nlinarith
  have b2 : (D.R.rS : ℝ) ^ 2 ≤ D.R.m * (D.R.rS : ℝ) ^ 3 := by nlinarith
  have c1 : C1 * (D.R.m : ℝ) ^ 2 ≤ |C1| * (4 * (D.R.m * (D.R.rS : ℝ) ^ 3)) :=
    mul_le_mul (le_abs_self _) b1 (by positivity) a1
  have c2 : Cg * (D.R.rS : ℝ) ^ 2 ≤ |Cg| * (D.R.m * (D.R.rS : ℝ) ^ 3) :=
    mul_le_mul (le_abs_self _) b2 (by positivity) a2
  nlinarith

end GlobalTheory.Amp.AbsRange
