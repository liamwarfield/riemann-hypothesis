module

public import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.InertPlacesGoodSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarBoundOfMultiplicity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowBoundsOfNonThickLetter
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowBoundsOfNonThickLetter
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.RowNT

theorem logb_le_of_le_four_exp {l x large₂ : ℝ} (hl : 11 ≤ l) (hLg : 0 ≤ large₂) (hx0 : 0 ≤ x)
    (hx : x ≤ 4 * Real.exp large₂) : Real.logb l x ≤ 3 + large₂ := by
  rcases hx0.eq_or_lt with h | hpos
  · subst h; simp; linarith
  have hlogl : 1 ≤ Real.log l := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have h4 : Real.log x ≤ Real.log 4 + large₂ := by
    have := Real.log_le_log hpos hx
    rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
  have h43 : Real.log 4 ≤ 3 := by have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith
  unfold Real.logb
  rcases le_or_gt (Real.log x) 0 with hn | hp
  · have : Real.log x / Real.log l ≤ 0 := div_nonpos_of_nonpos_of_nonneg hn (by linarith)
    linarith
  · have : Real.log x / Real.log l ≤ Real.log x := div_le_self hp.le hlogl
    linarith

theorem lift_shape_le {l H hB e : ℝ} (hl : 11 ≤ l) (hB1 : 1 ≤ hB) (hH0 : 0 ≤ H) (hH : H ≤ 2 * hB)
    (he : e ≤ 23 * (1 + H / l + (1 + Real.logb l (H + 1)))) :
    e ≤ 69 * (1 + hB / l + Real.logb l hB) := by
  have hl1 : 1 < l := by linarith
  have hl0 : 0 < l := by linarith
  have h1 : H / l ≤ 2 * hB / l := div_le_div_of_nonneg_right hH hl0.le
  have h2 : Real.logb l (H + 1) ≤ Real.logb l (3 * hB) :=
    Real.logb_le_logb_of_le hl1 (by linarith) (by linarith)
  have h3 : Real.logb l (3 * hB) = Real.logb l 3 + Real.logb l hB :=
    Real.logb_mul (by norm_num) (by linarith)
  have h4 : Real.logb l 3 ≤ 1 := by
    have := Real.logb_le_logb_of_le hl1 (show (0:ℝ) < 3 by norm_num) (show (3:ℝ) ≤ l by linarith)
    rwa [Real.logb_self_eq_one hl1] at this
  have h5 : 0 ≤ Real.logb l hB := Real.logb_nonneg hl1 hB1
  have h6 : 0 ≤ hB / l := div_nonneg (by linarith) hl0.le
  have h7 : 2 * hB / l = 2 * (hB / l) := by ring
  linarith

theorem bound_real {l n r m h w η S lg band e' hB wP eta₃ Sc large₂ ind cE : ℝ}
    (hl : 11 ≤ l) (hn : 0 ≤ n) (hr : 0 ≤ r) (hm : 0 ≤ m)
    (hh : h ≤ hB) (hw : w ≤ wP) (hη : η ≤ eta₃) (hS : S ≤ Sc) (h0w : 0 ≤ w) (h0η : 0 ≤ η)
    (h0S : 0 ≤ S) (h0h : 0 ≤ h) (hlg : lg ≤ 3 + large₂) (hLg : 1 ≤ large₂) (hband : band ≤ ind)
    (hind0 : 0 ≤ ind) (he : e' ≤ 69 * cE) (hcE : 0 ≤ cE) :
    320 * (n + 1) * r * (h / l ^ 2 + (w + η) / l + S + 1 + lg + η * band) + 320 * n * m * e' ≤
      368 * ((n + 1) * r * (hB / l ^ 2)) +
        2082 * ((n + 1) * r * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind)) + 22365 * (n * m * cE) := by
  have hl0 : 0 < l := by linarith
  have hA : 0 ≤ (n + 1) * r := mul_nonneg (by linarith) hr
  have e1 : h / l ^ 2 ≤ hB / l ^ 2 := div_le_div_of_nonneg_right hh (by positivity)
  have e2 : (w + η) / l ≤ (wP + eta₃) / l := div_le_div_of_nonneg_right (by linarith) hl0.le
  have e3 : η * band ≤ eta₃ * ind := by
    have hb0 : 0 ≤ band ∨ band < 0 := le_or_gt 0 band
    rcases hb0 with hb0 | hb0
    · exact mul_le_mul hη hband hb0 (by linarith)
    · have : η * band ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0η hb0.le
      have : 0 ≤ eta₃ * ind := mul_nonneg (by linarith) hind0
      linarith
  have e4 : 0 ≤ (wP + eta₃) / l := div_nonneg (by linarith) hl0.le
  have e5 : 0 ≤ eta₃ * ind := mul_nonneg (by linarith) hind0
  have e6 : 0 ≤ hB / l ^ 2 := div_nonneg (by linarith) (by positivity)
  have hbr : h / l ^ 2 + (w + η) / l + S + 1 + lg + η * band ≤
      hB / l ^ 2 + 6 * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind) := by
    nlinarith
  have k1 : 320 * (n + 1) * r * (h / l ^ 2 + (w + η) / l + S + 1 + lg + η * band) ≤
      320 * ((n + 1) * r) * (hB / l ^ 2 + 6 * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind)) := by
    rw [mul_assoc 320 (n + 1) r]
    exact mul_le_mul_of_nonneg_left hbr (by positivity)
  have k2 : 320 * n * m * e' ≤ 320 * n * m * (69 * cE) :=
    mul_le_mul_of_nonneg_left he (by positivity)
  have hf : 0 ≤ (n + 1) * r * ((wP + eta₃) / l + Sc + large₂ + eta₃ * ind) :=
    mul_nonneg hA (by linarith)
  have hH : 0 ≤ (n + 1) * r * (hB / l ^ 2) := mul_nonneg hA e6
  have hM : 0 ≤ n * m * cE := by positivity
  nlinarith

end GlobalTheory.NLink.RowNT

namespace GlobalTheory.NLink.RowNT

attribute [local instance] Formalism.MainNotions.N.nLet_neZero

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : WordDat (nLet i w hw)), ArcLiftingSetup.aux₃ D HW F 320 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → π ∈ D.nd.Zgood i → WordBase L HW i r ρ π w hw Cx hG Wd → WordBox L Wd → WordsNT Wd → RowL i r ρ π w hw Cx (bdCD L (bandOf L HW 320 i r ρ w) (D.nd.l i) w (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
  intro D L P HW F C₂ i r ρ π w hw Cx hG Wd h17 h54 hpar h11 hπ hb hbox hN
  intro T₁ T₂ Fm h2 h1 hF
  classical
  have hp : ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p = D.nd.l i := (D.loc _).PD_p _
  have hcA := caseA_of_unram (D.loc (D.nd.l i)) (HW (D.nd.l i)) hG hb.unram (by omega)
  have hT := h17 (D.nd.l i) (D.nbr i w hw).Kw Cx.LL hG hb.unram
  have hS := GlobalTheory.Survey.InertPlacesGoodSet.setting_of_wordsNT (by omega) hb hN inferInstance T₁ T₂ Fm h2 h1 hF
  have hX := (hT (by rw [hp]; exact h11) T₁ T₂ Fm Wd.b Wd.w Wd.S Wd.η Wd.m Wd.up Wd.sz Wd.Mi Wd.hi hS
    hN.w20 hN.η20 hN.twenty_words_le_b hN.some_nt).1 hN.alt
  rw [hp] at hX
  have hrk : Module.finrank ↥Cx.LL.1 T₂.V = D.R.r := by
    obtain ⟨e, -⟩ := h2
    rw [e.finrank_eq]; simp
  have hnl : Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) = TwistedPlaces.nLam D w := by
    have e : K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 := inf_eq_left.2 hb.unram
    rw [e]
    exact hb.deg
  have hO := h54.2.2.2.2.2.2.2.2.2.2.1 (D.nd.l i) (D.nbr i w hw).Kw 1 Cx.LL hG T₁ Wd.Mi Wd.hi
    (hb.t1 T₁ h1).1 (hb.t1 T₁ h1).2.2
  have hl : (11 : ℝ) ≤ (D.nd.l i : ℝ) := by exact_mod_cast h11
  have hb1 : (1 : ℝ) ≤ L.sc.b := TwistedPlaces.one_le_b L
  have hSc := L.Sc_pos
  have hEt := L.etaSz_pos
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hB1 : (1 : ℝ) ≤ TwistedPlaces.hB L := by unfold TwistedPlaces.hB; linarith
  have hB2 : TwistedPlaces.hB L ≤ 2 * L.sc.b := by unfold TwistedPlaces.hB; unfold EmbeddingTypeJumps.ParametersPolynomiallyBounded at hpar; linarith
  have hHm : (LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) ≤ 2 * TwistedPlaces.hB L := by
    have hfl : LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi ≤ ⌊2 * TwistedPlaces.hB L⌋₊ := by
      unfold LiftingTheory.Hmax
      apply Finset.sup_le
      intro k _
      apply Nat.le_floor
      exact hbox.box_le _
    calc (LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) ≤ (⌊2 * TwistedPlaces.hB L⌋₊ : ℝ) := by exact_mod_cast hfl
      _ ≤ 2 * TwistedPlaces.hB L := Nat.floor_le (by linarith)
  have he : (TruncatedSeriesCountingBounds.eLift ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 Cx.LL hG) T₁ Wd.Mi Wd.hi : ℝ) ≤
      69 * coreE L (D.nd.l i) := by
    have hO' : (TruncatedSeriesCountingBounds.eLift ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 Cx.LL hG) T₁ Wd.Mi Wd.hi : ℝ) ≤
        23 * (1 + (LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) / ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p +
          (1 + Real.logb ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p
            ((LiftingTheory.Hmax (nLet i w hw) Wd.Mi Wd.hi : ℝ) + 1))) := hO.1 hcA
    rw [hp] at hO'
    unfold coreE
    exact GlobalTheory.NLink.RowNT.lift_shape_le hl hB1 (Nat.cast_nonneg _) hHm hO'
  have hh : (TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ) ≤ TwistedPlaces.hB L := by
    have hwb : (Wd.w : ℝ) ≤ Wd.b := by have := hN.w20; exact_mod_cast (by omega : Wd.w ≤ Wd.b)
    have hle := hb.h_le
    unfold TruncatedSeriesCountingBounds.hB
    split_ifs
    · push_cast; linarith
    · push_cast; have : (0:ℝ) ≤ Wd.η := Nat.cast_nonneg _; linarith
  have hlg : Real.logb (D.nd.l i : ℝ) (2 * (TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz : ℝ)) ≤ 3 + TwistedPlaces.large₂ L := by
    apply GlobalTheory.NLink.RowNT.logb_le_of_le_four_exp hl (by linarith [TwistedPlaces.L_ge_one L]) (by positivity)
    rw [← TwistedPlaces.b_eq]; linarith
  have hband : ((if TruncatedSeriesCountingBounds.Band (D.nd.l i) Wd.b Wd.S Wd.η Wd.sz
        (Real.logb (↑(D.nd.l i)) (2 * ↑(TruncatedSeriesCountingBounds.hB Wd.b Wd.w Wd.S Wd.η Wd.sz))) 320 then 1 else 0) : ℝ) ≤
      (if bandOf L HW 320 i r ρ w then 1 else 0) := by
    split_ifs with hx hy
    · exact le_rfl
    · exact absurd ⟨h11, π, hπ, hw, Cx, hG, Wd, hb, hbox, hN, hx⟩ hy
    · norm_num
    · exact le_rfl
  have key := GlobalTheory.NLink.RowNT.bound_real (l := (D.nd.l i : ℝ)) (n := (TwistedPlaces.nLam D w : ℝ))
    (r := (D.R.r : ℝ)) (m := (D.R.m : ℝ)) hl (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hh hb.w_le hb.η_le hb.S_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hlg (TwistedPlaces.L_ge_one L) hband (by split_ifs <;> norm_num) he
    (by unfold coreE; have := Real.logb_nonneg (by linarith : (1:ℝ) < D.nd.l i) hB1
        have : 0 ≤ TwistedPlaces.hB L / (D.nd.l i : ℝ) := div_nonneg (by linarith) (by linarith)
        linarith)
  obtain ⟨mm, k, e1, e2, e3⟩ := hX
  refine ⟨mm, k, e1, e2, e3.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))⟩
  have hnlR : ((Module.finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw) : ℕ) : ℝ) = (TwistedPlaces.nLam D w : ℝ) := by
    exact_mod_cast hnl
  have hrkR : ((Module.finrank ↥Cx.LL.1 T₂.V : ℕ) : ℝ) = (D.R.r : ℝ) := by exact_mod_cast hrk
  have hmR : ((Wd.m : ℕ) : ℝ) = (D.R.m : ℝ) := by exact_mod_cast hb.m_eq
  rw [hnlR, hrkR, hmR]
  simp only [bdCD, coreH, coreF, coreM, flat, rowC, KillingConditions.RowK.K₁, KillingConditions.RowK.K₂, KillingConditions.RowK.K₃]
  refine le_trans key (le_of_eq ?_)
  norm_num

end GlobalTheory.NLink.RowNT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowBoundsOfNonThickLetterStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowBounds_of_nonThick_letter : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : WordDat (nLet i w hw)), ArcLiftingSetup.aux₃ D HW F 320 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → π ∈ D.nd.Zgood i → WordBase L HW i r ρ π w hw Cx hG Wd → WordBox L Wd → WordsNT Wd → RowL i r ρ π w hw Cx (bdCD L (bandOf L HW 320 i r ρ w) (D.nd.l i) w (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
  first | exact @GlobalTheory.NLink.RowNT.main | exact GlobalTheory.NLink.RowNT.main | (intros; apply GlobalTheory.NLink.RowNT.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowBoundsOfAllLettersThick
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowBoundsOfAllLettersThick
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.RowsThick

theorem logb_le_of_log_le {l x A : ℝ} (hl : 1 ≤ Real.log l) (hx : Real.log x ≤ A) (hA : 0 ≤ A) :
    Real.logb l x ≤ A := by
  unfold Real.logb
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem one_le_log_of_eleven {l : ℝ} (hl : 11 ≤ l) : 1 ≤ Real.log l := by
  have h1 : Real.exp 1 ≤ l := by linarith [Real.exp_one_lt_d9]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log l := Real.log_le_log (Real.exp_pos 1) h1

theorem colBd_le_row {l n r m S η H H' e e' hB eta₃ wP Sc large₂ flt : ℝ}
    (hl : 11 ≤ l) (hn : 0 ≤ n) (hr : 0 ≤ r) (hm : 0 ≤ m) (hS0 : 0 ≤ S) (hS : S ≤ Sc) (hη0 : 0 ≤ η)
    (hη : η ≤ eta₃) (hH0 : 0 ≤ H) (hH : H ≤ hB + eta₃) (hetaB : eta₃ ≤ hB) (hB1 : 1 ≤ hB)
    (hBb : hB ≤ 2 * Real.exp large₂) (hLg : 1 ≤ large₂) (hwP : 0 ≤ wP)
    (hflt : (wP + eta₃) / l + Sc + large₂ ≤ flt)
    (he : e ≤ 32 * H / l ^ 2 + 4 * S + 10 * η / (l - 1) + 25 * (Real.logb l (2 * H) + 1))
    (hH'0 : 0 ≤ H') (hH' : H' ≤ H)
    (he' : e' ≤ 23 * (1 + H' / l + (1 + Real.logb l (H' + 1)))) :
    (n + 1) * r * e + 4 * n * m * e' + 3 / 2 * n * (r * S + 2 * m * ((H + 1) / (l - 1) + 1)) ≤
      368 * ((n + 1) * r * (hB / l ^ 2)) + 2082 * ((n + 1) * r * flt) +
        22365 * (n * m * (1 + hB / l + Real.logb l hB)) := by
  have hlog := one_le_log_of_eleven hl
  have hl0 : 0 < l := by linarith
  have hl1 : 0 < l - 1 := by linarith
  have hetaP0 : 0 ≤ eta₃ := hη0.trans hη
  have hSc0 : 0 ≤ Sc := hS0.trans hS
  have hlB : 0 < Real.log l := by linarith

  have hlam : Real.logb l (2 * H) ≤ 7 + large₂ := by
    apply logb_le_of_log_le hlog _ (by linarith)
    rcases hH0.eq_or_lt with h0 | hpos
    · rw [← h0]; simp; linarith
    · have h8 : 2 * H ≤ 8 * Real.exp large₂ := by linarith
      calc Real.log (2 * H) ≤ Real.log (8 * Real.exp large₂) := Real.log_le_log (by linarith) h8
        _ = Real.log 8 + large₂ := by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
        _ ≤ 7 + large₂ := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)]

  have hlogB : 0 ≤ Real.logb l hB := Real.logb_nonneg (by linarith) hB1
  have hlamB : Real.logb l (H' + 1) ≤ 1 + Real.logb l hB := by
    have h3 : Real.log (H' + 1) ≤ Real.log l + Real.log hB := by
      calc Real.log (H' + 1) ≤ Real.log (3 * hB) := Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 3 + Real.log hB := Real.log_mul (by norm_num) (by linarith)
        _ ≤ Real.log l + Real.log hB := by
          have := Real.log_le_log (show (0 : ℝ) < 3 by norm_num) (show (3 : ℝ) ≤ l by linarith)
          linarith
    unfold Real.logb
    calc Real.log (H' + 1) / Real.log l ≤ (Real.log l + Real.log hB) / Real.log l :=
          div_le_div_of_nonneg_right h3 hlB.le
      _ = 1 + Real.log hB / Real.log l := by rw [add_div, div_self hlB.ne']

  have hu0 : 0 ≤ eta₃ / l := div_nonneg hetaP0 hl0.le
  have hv0 : 0 ≤ hB / l := div_nonneg (by linarith) hl0.le
  have hw0 : 0 ≤ wP / l := div_nonneg hwP hl0.le
  have hE0 : 0 ≤ hB / l ^ 2 := div_nonneg (by linarith) (by positivity)
  have hHl : 32 * H / l ^ 2 ≤ 32 * (hB / l ^ 2) + 3 * (eta₃ / l) := by
    have a1 : H / l ^ 2 ≤ (hB + eta₃) / l ^ 2 := div_le_div_of_nonneg_right hH (by positivity)
    have a2 : eta₃ / l ^ 2 = (eta₃ / l) / l := by rw [div_div, sq]
    have a3 : (eta₃ / l) / l ≤ (eta₃ / l) / 11 := div_le_div_of_nonneg_left hu0 (by norm_num) hl
    have a4 := add_div hB eta₃ (l ^ 2)
    rw [mul_div_assoc]
    linarith
  have hηl : 10 * η / (l - 1) ≤ 11 * (eta₃ / l) := by
    rw [div_le_iff₀ hl1]
    have a1 : 11 * (eta₃ / l) * (l - 1) = 11 * eta₃ - 11 * (eta₃ / l) := by field_simp
    have a2 : eta₃ / l ≤ eta₃ / 11 := div_le_div_of_nonneg_left hetaP0 (by norm_num) hl
    rw [a1]; linarith
  have hwe : (wP + eta₃) / l = wP / l + eta₃ / l := add_div _ _ _
  set E1 := hB / l ^ 2 with hE1
  set M1 := 1 + hB / l + Real.logb l hB with hM1
  set cD := (H + 1) / (l - 1) + 1 with hcD
  have hflt0 : 0 ≤ flt := by linarith
  have he1 : e ≤ 32 * E1 + 225 * flt := by linarith
  have he2 : e' ≤ 69 * M1 := by
    have a1 : H' / l ≤ 2 * (hB / l) := by
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by linarith) hl0.le
    linarith
  have hcD4 : cD ≤ 4 * M1 := by
    have a1 : (H + 1) / (l - 1) ≤ 4 * (hB / l) := by
      rw [div_le_iff₀ hl1]
      have b1 : 4 * (hB / l) * (l - 1) = 4 * hB - 4 * (hB / l) := by field_simp
      have b2 : hB / l ≤ hB / 11 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hl
      rw [b1]; linarith
    rw [hcD]; linarith
  have hM0 : 0 ≤ M1 := by linarith
  have h1 : (n + 1) * r * e ≤ (n + 1) * r * (32 * E1 + 225 * flt) :=
    mul_le_mul_of_nonneg_left he1 (by positivity)
  have h2 : n * m * e' ≤ n * m * (69 * M1) := mul_le_mul_of_nonneg_left he2 (by positivity)
  have h3 : n * r * S ≤ (n + 1) * r * flt := by
    have : S ≤ flt := by linarith
    calc n * r * S ≤ n * r * flt := mul_le_mul_of_nonneg_left this (by positivity)
      _ ≤ (n + 1) * r * flt := by
        have q1 : (n + 1) * r * flt = n * r * flt + r * flt := by ring
        have q2 := mul_nonneg hr hflt0
        linarith
  have h4 : n * m * cD ≤ n * m * (4 * M1) := mul_le_mul_of_nonneg_left hcD4 (by positivity)
  have p1 : 0 ≤ (n + 1) * r * E1 := by positivity
  have p2 : 0 ≤ (n + 1) * r * flt := by positivity
  have p3 : 0 ≤ n * m * M1 := by positivity
  linarith

attribute [local instance] nLet_neZero

section Facts

variable {D : D7} (L : SizeData₂ D)

theorem one_le_b : 1 ≤ L.sc.b := by
  unfold Scale.b
  apply Real.one_le_exp
  unfold Scale.L
  exact Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _

theorem Lg_ge_one : 1 ≤ TwistedPlaces.large₂ L := by
  unfold TwistedPlaces.large₂ Scale.L
  exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem placeWeight_nonneg : 0 ≤ TwistedPlaces.wP L := by
  have hx : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hb' : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := one_le_b L
    positivity
  have hw : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w''
    positivity
  have hB : 0 ≤ TwistedPlaces.wB L := by
    unfold TwistedPlaces.wB
    have := L.etaSz_pos
    exact le_max_of_le_left (by linarith)
  unfold TwistedPlaces.wP
  positivity

theorem one_le_hB : 1 ≤ TwistedPlaces.hB L := by
  unfold TwistedPlaces.hB
  have := one_le_b L
  have := L.Sc_pos
  have := L.etaSz_pos
  have : (0 : ℝ) ≤ D.R.t := by positivity
  linarith

theorem etaP_le_hB : TwistedPlaces.eta₃ L ≤ TwistedPlaces.hB L := by
  unfold TwistedPlaces.eta₃ TwistedPlaces.hB
  have := one_le_b L
  have := L.Sc_pos
  linarith

end Facts

theorem Hmax_le {n : ℕ} [NeZero n] (d : ℕ) (b : ZMod n → ℕ) (S η : ℕ) :
    LiftingTheory.Hmax n (RamifiedCoefficientChains.MiW d b S η) (RamifiedCoefficientChains.hiW d b S η) ≤ RamifiedCoefficientChains.hpar n b S + η := by
  unfold LiftingTheory.Hmax
  apply Finset.sup_le
  intro k _
  have : b (k : ZMod n) ≤ Finset.univ.sup b := Finset.le_sup (Finset.mem_univ _)
  unfold RamifiedCoefficientChains.MiW RamifiedCoefficientChains.hiW RamifiedCoefficientChains.hpar
  split_ifs <;> omega

theorem hpar_le_of_thick {n : ℕ} [NeZero n] {b0 η : ℕ} {sz : ZMod n → ℕ} (S : ℕ)
    (h : ∀ a, TruncatedSeriesCountingBounds.Thick b0 η sz a) : RamifiedCoefficientChains.hpar n sz S ≤ b0 + η + S := by
  unfold RamifiedCoefficientChains.hpar
  have : Finset.univ.sup sz ≤ b0 + η := Finset.sup_le fun a _ => (h a).2
  omega

theorem rowL_of_allThick : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : WordDat (nLet i w hw)) (d : ℕ) (bd : Prop), RamifiedCoefficientChains.aux₃ D HW F 25 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → WordBase L HW i r ρ π w hw Cx hG Wd → WordBox L Wd → WordBaseC (HW := HW) ρ π hG Wd → @WordsAT (D.nd.l i) _ (nLet_neZero i w hw) Wd d → RowL i r ρ π w hw Cx (bdCD L bd (D.nd.l i) w (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
  intro D L P HW F C₂ i r ρ π w hw Cx hG Wd d bd hP04 hP54 hPar h11 hb hbox hC hA
  intro T₁ T₂ F' h2 h1 hF
  have hp : ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p = D.nd.l i := (D.loc _).PD_p _
  have hl' : (((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).p : ℝ) = (D.nd.l i : ℝ) := by rw [hp]
  have hS := GlobalTheory.Survey.InertPlacesGoodSet.setCS_of_wordsAT h11 hb hC hA T₁ T₂ F' h2 h1 hF
  obtain ⟨e, he, hcol, -⟩ :=
    hP04 (D.nd.l i) (D.nbr i w hw).Kw Cx.LL hG d T₁ T₂ F' Wd.sz Wd.S Wd.η Wd.m hS trivial
  have hO := (hP54.2.2.2.2.2.2.2.2.2.2.1 (D.nd.l i) (D.nbr i w hw).Kw 1 Cx.LL hG T₁
    (RamifiedCoefficientChains.MiW d Wd.sz Wd.S Wd.η) (RamifiedCoefficientChains.hiW d Wd.sz Wd.S Wd.η) hS.2.2.2.2.2.1.1
    (RamifiedCoefficientChains.jumpsLet_win _ hS)).1 hS.1
  have hrk : Module.finrank ↥Cx.LL.1 T₂.V = D.R.r := by
    obtain ⟨e, -⟩ := h2
    rw [e.finrank_eq]; simp
  have hn : nLet i w hw = TwistedPlaces.nLam D w := by
    have h0 : Loc.K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 := inf_eq_left.mpr hb.unram
    unfold nLet
    rw [h0]
    exact hb.deg
  have hnR : ((nLet i w hw : ℕ) : ℝ) = (TwistedPlaces.nLam D w : ℝ) := by exact_mod_cast hn
  obtain ⟨mm, k, hmm, hk, hle⟩ := hcol
  refine ⟨mm, k, hmm, hk, hle.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg k))⟩
  have hK : (rowC C₂).K₁ = 368 ∧ (rowC C₂).K₂ = 2082 ∧ (rowC C₂).K₃ = 22365 := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [rowC, KillingConditions.RowK.K₁, KillingConditions.RowK.K₂, KillingConditions.RowK.K₃] <;> norm_num
  rw [hK.1, hK.2.1, hK.2.2]
  unfold RamifiedCoefficientChains.colBd RamifiedCoefficientChains.cD bdCD coreH coreF coreM coreE
  rw [hl', hrk, hb.m_eq, hnR]
  unfold RamifiedCoefficientChains.eBd RamifiedCoefficientChains.lam at he
  rw [hl'] at he hO
  have hHn := Hmax_le d Wd.sz Wd.S Wd.η
  have hth := hpar_le_of_thick Wd.S hA.thick
  have hHle : (((RamifiedCoefficientChains.hpar (nLet i w hw) Wd.sz Wd.S + Wd.η : ℕ)) : ℝ) ≤ TwistedPlaces.hB L + TwistedPlaces.eta₃ L := by
    have a1 : RamifiedCoefficientChains.hpar (nLet i w hw) Wd.sz Wd.S + Wd.η ≤ Wd.b + Wd.η + Wd.S + Wd.η := by omega
    have a2 : (((RamifiedCoefficientChains.hpar (nLet i w hw) Wd.sz Wd.S + Wd.η : ℕ)) : ℝ) ≤ ((Wd.b + Wd.η + Wd.S + Wd.η : ℕ) : ℝ) := by
      exact_mod_cast a1
    push_cast at a2 ⊢
    linarith [hb.h_le, hb.η_le]
  have hBb : TwistedPlaces.hB L ≤ 2 * Real.exp (TwistedPlaces.large₂ L) := by
    change TwistedPlaces.hB L ≤ 2 * L.sc.b
    unfold TwistedPlaces.hB
    unfold EmbeddingTypeJumps.ParametersPolynomiallyBounded at hPar
    linarith
  have hflt : (TwistedPlaces.wP L + TwistedPlaces.eta₃ L) / (D.nd.l i : ℝ) + L.Sc + TwistedPlaces.large₂ L ≤ flat L bd (D.nd.l i) := by
    unfold flat
    have h0 : 0 ≤ TwistedPlaces.eta₃ L := by have := L.etaSz_pos; unfold TwistedPlaces.eta₃; positivity
    split_ifs <;> linarith
  exact GlobalTheory.RowsThick.colBd_le_row (η := (Wd.η : ℝ))
    (H' := ((LiftingTheory.Hmax (nLet i w hw) (RamifiedCoefficientChains.MiW d Wd.sz Wd.S Wd.η) (RamifiedCoefficientChains.hiW d Wd.sz Wd.S Wd.η) : ℕ) : ℝ))
    (eta₃ := TwistedPlaces.eta₃ L) (wP := TwistedPlaces.wP L) (Sc := L.Sc) (large₂ := TwistedPlaces.large₂ L)
    (by exact_mod_cast h11) (by positivity) (by positivity) (by positivity) (by positivity) hb.S_le
    (by positivity) hb.η_le (by positivity) hHle (etaP_le_hB L) (one_le_hB L) hBb (Lg_ge_one L)
    (placeWeight_nonneg L) hflt he (by positivity) (by exact_mod_cast hHn) hO

end GlobalTheory.RowsThick
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowBoundsOfAllLettersThickStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowBounds_of_all_letters_thick : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : WordDat (nLet i w hw)) (d : ℕ) (bd : Prop), RamifiedCoefficientChains.aux₃ D HW F 25 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → WordBase L HW i r ρ π w hw Cx hG Wd → WordBox L Wd → WordBaseC (HW := HW) ρ π hG Wd → @WordsAT (D.nd.l i) _ (nLet_neZero i w hw) Wd d → RowL i r ρ π w hw Cx (bdCD L bd (D.nd.l i) w (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
  first | exact @GlobalTheory.RowsThick.rowL_of_allThick | exact GlobalTheory.RowsThick.rowL_of_allThick | (intros; apply GlobalTheory.RowsThick.rowL_of_allThick <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowsCDRowConditionLocalBounds
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink.RowsCD

theorem lt_ratIn {x y : ℝ} (h : x < y) : x < ((Formalism.MainNotions.N.ratIn x y : ℚ) : ℝ) := by
  unfold Formalism.MainNotions.N.ratIn
  rw [dite_eq_left h]
  exact (exists_rat_btwn h).choose_spec.1

theorem flat_pos {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) : 0 < Formalism.MainNotions.N.flat L bd l := by
  unfold Formalism.MainNotions.N.flat
  have hE : 0 < Formalism.MainNotions.TwistedPlaces.eta₃ L := by
    unfold Formalism.MainNotions.TwistedPlaces.eta₃; have := L.etaSz_pos; positivity
  have hW : 0 ≤ Formalism.MainNotions.TwistedPlaces.wP L := by
    unfold Formalism.MainNotions.TwistedPlaces.wP Formalism.MainNotions.TwistedPlaces.wB
    have h1 := Formalism.MainNotions.TwistedPlaces.w''_nonneg L
    have h2 := L.etaSz_pos
    have h3 := le_max_left (L.sc.w'' D.R.n + L.etaSz)
      ((⨆ t : D.host.TT, (L.bT t : ℝ)) + L.sc.b' / L.sc.x + L.etaSz)
    have h4 : (0 : ℝ) ≤ ((D.R.t : ℝ) + 1) / 2 := by positivity
    linarith
  have h1 : 0 ≤ (Formalism.MainNotions.TwistedPlaces.wP L + Formalism.MainNotions.TwistedPlaces.eta₃ L) / (l : ℝ) :=
    div_nonneg (by linarith) (Nat.cast_nonneg _)
  have h3 := Formalism.MainNotions.TwistedPlaces.L_ge_one L
  have h4 := L.Sc_pos
  by_cases hb : bd
  · rw [if_pos hb]; linarith
  · rw [if_neg hb]; linarith

theorem coreF_pos {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 < Formalism.MainNotions.N.coreF L bd l lam := by
  unfold Formalism.MainNotions.N.coreF
  have hr : (0 : ℝ) < D.R.r := by linarith [Formalism.MainNotions.TwistedPlaces.k_le_r D, Formalism.MainNotions.TwistedPlaces.k_ge_five D]
  have hn : (0 : ℝ) < (Formalism.MainNotions.TwistedPlaces.nLam D lam : ℝ) + 1 := by positivity
  exact mul_pos (mul_pos hn hr) (flat_pos L bd l)

theorem bdCD_lt {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E))
    (K₁ K₂ K₃ : ℝ) : Formalism.MainNotions.N.bdCD L bd l lam K₁ K₂ K₃ < Formalism.MainNotions.N.bdCD L bd l lam K₁ (K₂ + 1) K₃ := by
  have e : Formalism.MainNotions.N.bdCD L bd l lam K₁ (K₂ + 1) K₃ =
      Formalism.MainNotions.N.bdCD L bd l lam K₁ K₂ K₃ + Formalism.MainNotions.N.coreF L bd l lam := by
    unfold Formalism.MainNotions.N.bdCD; ring
  rw [e]
  linarith [coreF_pos L bd l lam]

end GlobalTheory.NLink.RowsCD

theorem GlobalTheory.NLink.lengthBoundAtPlaces_of_jointCond : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), ArcLiftingSetup.aux₃ D HW F 320 → RamifiedCoefficientChains.aux₃ D HW F 25 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → π ∈ D.nd.Zgood i → LocalRepresentationCongruenceCondition L HW i r ρ π → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc (lenRowCD L (fun lam => bandOf L HW 320 i r ρ lam) (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃ (D.nd.l i)) := by
  intro D L P HW F C₂ i r ρ π dc h17 h04 h54 h67 hl hπ hJ w hw _ C hC
  have hl2 : D.nd.l i ≠ 2 := by omega
  obtain ⟨hur, hW⟩ := hJ w hw
  have hg : Good (D.nbr i w hw).Kw 1 C.LL := hC.good_one hl2 (le_trans (le_inf le_rfl hur) le_sup_left)
  obtain ⟨Wd, hB, hBox, hcase⟩ := hW C hg
  have hrow : RowL i r ρ π w hw C (bdCD L (bandOf L HW 320 i r ρ w) (D.nd.l i) w
      (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃) := by
    rcases hcase with hNT | ⟨hC', d, hAT⟩
    · exact GlobalTheory.T.rowBounds_of_nonThick_letter D L P HW F C₂ i r ρ π w hw C hg Wd h17 h54 h67 hl hπ hB hBox hNT
    · exact GlobalTheory.T.rowBounds_of_all_letters_thick D L P HW F C₂ i r ρ π w hw C hg Wd d _ h04 h54 h67 hl hB hBox hC' hAT
  exact GlobalTheory.T.rowBound_at_place_of_latticeColengthBound D i r ρ π w hw C _ _ hrow
    (GlobalTheory.NLink.RowsCD.lt_ratIn (GlobalTheory.NLink.RowsCD.bdCD_lt L _ _ w _ _ _)).le
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowsCDRowConditionLocalBoundsStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowsCD_rowCondition_localBounds : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), ArcLiftingSetup.aux₃ D HW F 320 → RamifiedCoefficientChains.aux₃ D HW F 25 → LiftingTheory.aux₃ D HW F 10 23 32 32 → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → π ∈ D.nd.Zgood i → LocalRepresentationCongruenceCondition L HW i r ρ π → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc (lenRowCD L (fun lam => bandOf L HW 320 i r ρ lam) (rowC C₂).K₁ (rowC C₂).K₂ (rowC C₂).K₃ (D.nd.l i)) := by
  first | exact @GlobalTheory.NLink.lengthBoundAtPlaces_of_jointCond | exact GlobalTheory.NLink.lengthBoundAtPlaces_of_jointCond | (intros; apply GlobalTheory.NLink.lengthBoundAtPlaces_of_jointCond <;> assumption)
end
