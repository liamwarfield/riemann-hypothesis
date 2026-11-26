module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeRegularEntries
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeRegularEntries
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.FrameReg

open GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FrameChange

theorem stepCols_ne_empty {N j : ℕ} (i : Fin N) : stepCols N j i ≠ ∅ := by
  intro e
  have hi := i.2
  by_cases h : (i : ℕ) + 1 ≤ j
  · have : (⟨N - j, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h]
      omega
    simp [e] at this
  · have : (⟨0, by omega⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h]
      omega
    simp [e] at this

theorem minor_singleton {R : Type} [CommRing R] {N : ℕ} (h : Matrix (Fin N) (Fin N) R) (a b : Fin N) :
    minorIJ h {a} {b} = h a b := by
  unfold minorIJ
  rw [dite_eq_left (by simp)]
  haveI : Unique (Fin ({b} : Finset (Fin N)).card) := inferInstanceAs (Unique (Fin 1))
  rw [det_unique]
  show h _ _ = _
  congr 1
  · exact Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ _ _)
  · exact Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ _ _)

theorem minor_empty {R : Type} [CommRing R] {N : ℕ} (h : Matrix (Fin N) (Fin N) R) :
    minorIJ h ∅ ∅ = 1 := by
  unfold minorIJ
  rw [dite_eq_left rfl]
  haveI : IsEmpty (Fin (∅ : Finset (Fin N)).card) := inferInstanceAs (IsEmpty (Fin 0))
  exact det_isEmpty

theorem stepCols_eq_singleton_of_zero {N j : ℕ} (i : Fin N) (hi : (i : ℕ) = 0) (hj : 1 ≤ j) (hN : j ≤ N) :
    stepCols N j i = {⟨N - j, by omega⟩} := by
  ext a
  have := a.2
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
  rw [if_pos (by omega)]
  omega

theorem stepCols_om {N j : ℕ} (i : Fin N) (hi : (i : ℕ) = j) :
    stepCols N j i = {⟨0, by have := i.2; omega⟩} := by
  ext a
  have := a.2
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
  rw [if_neg (by omega)]
  omega

theorem isStepRows_singleton_low {N j : ℕ} (i : Fin N) (hi : (i : ℕ) = 0) (hj : 2 ≤ j) (hN : j ≤ N) (r : Fin N)
    (hr : N - j ≤ (r : ℕ)) : IsStepRows N j i {r} := by
  refine ⟨by rw [stepCols_eq_singleton_of_zero i hi (by omega) hN]; simp, ?_⟩
  rw [if_pos (by omega), Finset.singleton_subset_iff]
  simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hr

theorem isStepRows_om {N j : ℕ} (i : Fin N) (hi : (i : ℕ) = j) (r : Fin N)
    (hr : (r : ℕ) < N - j) : IsStepRows N j i {r} := by
  refine ⟨by rw [stepCols_om i hi]; simp, ?_⟩
  rw [if_neg (by omega), Finset.singleton_subset_iff]
  simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hr

section Reg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem regAt_zpow {s : Ω} (h : RegAt x (mCoordIdeal z) s) (h' : RegAt x (mCoordIdeal z) s⁻¹) (n : ℤ) :
    RegAt x (mCoordIdeal z) (s ^ n) := by
  have a : s ∈ regRing x z := h
  have b : s⁻¹ ∈ regRing x z := h'
  show s ^ n ∈ regRing x z
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast]; exact Subring.pow_mem _ a n
  · rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]; exact Subring.pow_mem _ b n

theorem coord_ne (hz : z ∈ mcPts (mCoordIdeal x)) {q : Σ k, ι k} (hq : (X q : MRing ι) ∉ mCoordIdeal z) :
    x q ≠ 0 := by
  have := ValRing.aeval_ne_zero_of_notMem hz (isMultiHomog_X_single q) hq
  simpa using this

theorem regAt_ratio (hz : z ∈ mcPts (mCoordIdeal x)) {k : K} (a b : ι k)
    (hb : (X ⟨k, b⟩ : MRing ι) ∉ mCoordIdeal z) : RegAt x (mCoordIdeal z) (x ⟨k, a⟩ / x ⟨k, b⟩) := by
  have hx := coord_ne hz hb
  refine ⟨_, X ⟨k, a⟩, X ⟨k, b⟩, isMultiHomog_X_single _, isMultiHomog_X_single _, hb, ?_⟩
  simp [div_mul_cancel₀ _ hx]

end Reg

section Model

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j)
  {zb : (Σ k, baseIdx ι M.blk k) → ℂ} {F₁ F₂ : FrameData ι Ψ N M.Ω M.blk}


include M in
theorem twist_ratio (hz : zb ∈ mcPts (mCoordIdeal M.x)) (hG₁ : M.GoodAt F₁ (mCoordIdeal zb))
    (hG₂ : M.GoodAt F₂ (mCoordIdeal zb)) (p : Ψ × Fin N) :
    RegAt M.x (mCoordIdeal zb)
      ((∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') / ∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') := by
  rw [← Finset.prod_div_distrib]
  refine Subring.prod_mem (regRing M.x zb) fun k _ => ?_
  rw [← div_zpow]
  refine regAt_zpow (regAt_ratio hz _ _ (hG₁.1 k)) ?_ _
  rw [inv_div]
  exact regAt_ratio hz _ _ (hG₂.1 k)

theorem detFac_improper (hz : zb ∈ mcPts (mCoordIdeal M.x)) (hF₁ : M.IsFrame F₁) (hF₂ : M.IsFrame F₂)
    (hG₁ : M.GoodAt F₁ (mCoordIdeal zb)) (hG₂ : M.GoodAt F₂ (mCoordIdeal zb)) (p : Ψ × Fin N)
    (hp : M.blk p = none) :
    RegAt M.x (mCoordIdeal zb) (detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1)) ∧
      RegAt M.x (mCoordIdeal zb) (detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1))⁻¹ := by
  have hT₁ := hF₁.1 p.1
  have hT₂ := hF₂.1 p.1
  have hu₁ : IsUnit (F₁.T p.1).det := hT₁.2.isUnit
  have hC : IsBlockDiag j ((F₁.T p.1)⁻¹ * F₂.T p.1) := (hT₁.1.inv hu₁).mul hT₂.1
  have hm := ((GlobalTheory.T.block_diagonal_minor_vanishing M.Ω N j p.2 M.j_le).2.2.2 _ _ hT₁.1 hC).2
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu₁] at hm
  have e₁ := hF₁.2.2.2 p hp
  have e₂ := hF₂.2.2.2 p hp
  have hr := twist_ratio M hz hG₁ hG₂ p
  have hr' := twist_ratio M hz hG₂ hG₁ p
  have hl := M.lam_ne_zero p hp
  have hd₁ := detFac_ne_zero M.j_le p.2 hT₁.1 hT₁.2
  have hA₁ : (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (coord_ne hz (hG₁.1 k'))
  have hA₂ : (∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (coord_ne hz (hG₂.1 k'))
  obtain ⟨v₁, rv₁, ri₁⟩ := hG₁.2.2 p hp
  obtain ⟨v₂, rv₂, ri₂⟩ := hG₂.2.2 p hp
  generalize detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) = D at *
  generalize detFac j p.2 (F₂.T p.1) = d₂ at *
  generalize detFac j p.2 (F₁.T p.1) = d₁ at *
  generalize (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') = A₁ at *
  generalize (∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') = A₂ at *
  have key : A₁ * F₁.υ p * D = A₂ * F₂.υ p := by rw [← e₁, ← e₂, hm]; ring
  have hD : D = A₂ / A₁ * (F₂.υ p * (F₁.υ p)⁻¹) := by
    field_simp
    linear_combination key
  have hD' : D⁻¹ = A₁ / A₂ * (F₁.υ p * (F₂.υ p)⁻¹) := by
    rw [hD]
    field_simp
  rw [hD', hD]
  exact ⟨ValRing.regAt_mul hr (ValRing.regAt_mul rv₂ ri₁), ValRing.regAt_mul hr' (ValRing.regAt_mul rv₁ ri₂)⟩

end Model

section Model2

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j)
  {zb : (Σ k, baseIdx ι M.blk k) → ℂ} {F₁ F₂ : FrameData ι Ψ N M.Ω M.blk}

theorem minor_change (hz : zb ∈ mcPts (mCoordIdeal M.x)) (hF₁ : M.IsFrame F₁) (hF₂ : M.IsFrame F₂)
    (hG₁ : M.GoodAt F₁ (mCoordIdeal zb)) (hG₂ : M.GoodAt F₂ (mCoordIdeal zb)) (p : Ψ × Fin N) (k : K)
    (hp : M.blk p = some k) {I₀ I' : Finset (Fin N)} (hI₀ : IsStepRows N j p.2 I₀)
    (hI' : IsStepRows N j p.2 I') :
    minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I₀ I' =
      (detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1))⁻¹ *
        ((∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') / ∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') *
        ∑ m : ι k, F₁.u' I₀ ⟨k, m⟩ * F₂.u ⟨k, m⟩ I' := by
  have hj := M.j_le
  have hT₁ := hF₁.1 p.1
  have hT₂ := hF₂.1 p.1
  have hu₁ : IsUnit (F₁.T p.1).det := hT₁.2.isUnit
  have hi := GlobalTheory.T.block_diagonal_minor_vanishing M.Ω N j p.2 hj
  have hC : IsBlockDiag j ((F₁.T p.1)⁻¹ * F₂.T p.1) := (hT₁.1.inv hu₁).mul hT₂.1
  have hdet : ((F₁.T p.1)⁻¹ * F₂.T p.1).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv]
    exact mul_ne_zero (by simpa using hT₁.2) hT₂.2
  have hD := detFac_ne_zero hj p.2 hC hdet
  have hd₁ := detFac_ne_zero hj p.2 hT₁.1 hT₁.2
  have hm := (hi.2.2.2 _ _ hT₁.1 hC).2
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu₁] at hm
  have hA₁ : (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (coord_ne hz (hG₁.1 k'))
  have hE : IsBlockDiag j (unitCols I' (stepCols N j p.2) hI'.1 : Matrix (Fin N) (Fin N) M.Ω) :=
    unitCols_blockDiag _ _ _ (stepRows_same_side hI')
  have hmin : ∀ I, minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1 * unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2) =
      minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' := fun I => by
    rw [hi.1]
    simp only [minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hr : ∀ m : ι k, ∑ I, F₂.u ⟨k, m⟩ I * minorIJ (unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2) =
      F₂.u ⟨k, m⟩ I' := fun m => by
    simp only [minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

  have rel : ∀ m : ι k, detFac j p.2 (F₂.T p.1) * (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') *
      ∑ I, F₁.u ⟨k, m⟩ I * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' =
      detFac j p.2 (F₁.T p.1) * (∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') * F₂.u ⟨k, m⟩ I' := fun m => by
    have e1 := hF₁.2.1 p k hp m _ (hC.mul hE)
    have e2 := hF₂.2.1 p k hp m _ hE
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu₁] at e1
    simp only [hmin] at e1
    rw [hr m] at e2
    linear_combination (-detFac j p.2 (F₂.T p.1)) * e1 + detFac j p.2 (F₁.T p.1) * e2

  have hread : ∑ m : ι k, F₁.u' I₀ ⟨k, m⟩ * ∑ I, F₁.u ⟨k, m⟩ I * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' =
      minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I₀ I' := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ I, ∑ m : ι k, F₁.u' I₀ ⟨k, m⟩ * (F₁.u ⟨k, m⟩ I * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I') =
        if I₀ = I then minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' else 0 := fun I => by
      by_cases hI : IsStepRows N j p.2 I
      · have e := hF₁.2.2.1 p k hp I₀ I hI₀ hI
        calc _ = (∑ m : ι k, F₁.u' I₀ ⟨k, m⟩ * F₁.u ⟨k, m⟩ I) * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' := by
              rw [Finset.sum_mul]
              exact Finset.sum_congr rfl fun m _ => (mul_assoc _ _ _).symm
          _ = _ := by rw [e]; split_ifs <;> simp
      · have h0 : minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' = 0 := by
          rw [← hmin I]
          exact (hi.2.1 _ I (hC.mul hE) hI).resolve_right (stepCols_ne_empty p.2)
        simp [h0]
    simp only [this]
    simp
  have hsum : detFac j p.2 (F₂.T p.1) * (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') *
      minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I₀ I' =
      detFac j p.2 (F₁.T p.1) * (∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') *
        ∑ m : ι k, F₁.u' I₀ ⟨k, m⟩ * F₂.u ⟨k, m⟩ I' := by
    rw [← hread, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    linear_combination F₁.u' I₀ ⟨k, m⟩ * rel m
  rw [hm] at hsum
  generalize detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) = D at *
  generalize detFac j p.2 (F₁.T p.1) = d₁ at *
  generalize (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') = A₁ at *
  field_simp
  have h2 : d₁ * (D * A₁ * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I₀ I') =
      d₁ * ((∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k') * ∑ m : ι k, F₁.u' I₀ ⟨k, m⟩ * F₂.u ⟨k, m⟩ I') := by
    linear_combination hsum
  have h3 := mul_left_cancel₀ hd₁ h2
  linear_combination h3

theorem minor_reg (hz : zb ∈ mcPts (mCoordIdeal M.x)) (hF₁ : M.IsFrame F₁) (hF₂ : M.IsFrame F₂)
    (hG₁ : M.GoodAt F₁ (mCoordIdeal zb)) (hG₂ : M.GoodAt F₂ (mCoordIdeal zb)) (p : Ψ × Fin N) (k : K)
    (hp : M.blk p = some k) {I₀ I' : Finset (Fin N)} (hI₀ : IsStepRows N j p.2 I₀)
    (hI' : IsStepRows N j p.2 I')
    (hD : RegAt M.x (mCoordIdeal zb) (detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1))⁻¹) :
    RegAt M.x (mCoordIdeal zb) (minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I₀ I') := by
  rw [minor_change M hz hF₁ hF₂ hG₁ hG₂ p k hp hI₀ hI']
  exact ValRing.regAt_mul (ValRing.regAt_mul hD (twist_ratio M hz hG₁ hG₂ p))
    (reg_sum hz _ _ fun m _ => ValRing.regAt_mul (hG₁.2.1 _ _).2 (hG₂.2.1 _ _).1).1

theorem detW_reg (hz : zb ∈ mcPts (mCoordIdeal M.x)) (hF₁ : M.IsFrame F₁) (hF₂ : M.IsFrame F₂)
    (hG₁ : M.GoodAt F₁ (mCoordIdeal zb)) (hG₂ : M.GoodAt F₂ (mCoordIdeal zb)) (τ : Ψ) (hjN : j < N) :
    RegAt M.x (mCoordIdeal zb) (minorIJ ((F₁.T τ)⁻¹ * F₂.T τ) (wIdx N j) (wIdx N j)) ∧
      RegAt M.x (mCoordIdeal zb) (minorIJ ((F₁.T τ)⁻¹ * F₂.T τ) (wIdx N j) (wIdx N j))⁻¹ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have e : wIdx N 0 = ∅ := by
      ext a
      have := a.2
      simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      omega
    rw [e, minor_empty, inv_one]
    exact ⟨ValRing.regAt_one _ _, ValRing.regAt_one _ _⟩
  · let i : Fin N := ⟨j - 1, by omega⟩
    have hi : (i : ℕ) + 1 = j := by show j - 1 + 1 = j; omega
    have hp : M.blk (τ, i) = none := (M.blk_none _).2 fun h => h.1 hi
    have h := detFac_improper M hz hF₁ hF₂ hG₁ hG₂ (τ, i) hp
    have e : detFac j i ((F₁.T τ)⁻¹ * F₂.T τ) = minorIJ ((F₁.T τ)⁻¹ * F₂.T τ) (wIdx N j) (wIdx N j) := by
      unfold detFac
      rw [if_pos (by omega), if_neg (by omega), mul_one]
    rw [← e]
    exact h

end Model2

theorem change_regular : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal M.x) → M.IsFrame F₁ → M.IsFrame F₂ → M.GoodAt F₁ (mCoordIdeal zb) → M.GoodAt F₂ (mCoordIdeal zb) → ∀ (τ : Ψ) (r s : Fin N), RegAt M.x (mCoordIdeal zb) (((F₁.T τ)⁻¹ * F₂.T τ) r s) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M zb F₁ F₂ hz hF₁ hF₂ hG₁ hG₂ τ r s
  have hjN := M.j_le
  have hT₁ := hF₁.1 τ
  have hT₂ := hF₂.1 τ
  have hu₁ : IsUnit (F₁.T τ).det := hT₁.2.isUnit
  have hC : IsBlockDiag j ((F₁.T τ)⁻¹ * F₂.T τ) := (hT₁.1.inv hu₁).mul hT₂.1
  have hr₀ := r.2
  have hs₀ := s.2
  by_cases hrs : ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)
  swap
  · rw [hC r s hrs]
    exact ValRing.regAt_zero _ _
  have proper : ∀ i : Fin N, IsProperStep N j i → ∃ k, M.blk (τ, i) = some k := fun i hi => by
    rcases h : M.blk (τ, i) with _ | k
    · exact absurd hi ((M.blk_none _).1 h)
    · exact ⟨k, rfl⟩
  by_cases hr : (r : ℕ) < N - j
  ·
    have hs := hrs.1 hr
    obtain ⟨hW, hW'⟩ := detW_reg M hz hF₁ hF₂ hG₁ hG₂ τ (by omega : j < N)
    by_cases h2 : 2 ≤ N - j
    · let i : Fin N := ⟨j, by omega⟩
      obtain ⟨k, hk⟩ := proper i ⟨by show j + 1 ≠ j; omega, by show j + 1 ≠ N; omega⟩
      have e : detFac j i ((F₁.T τ)⁻¹ * F₂.T τ) = minorIJ ((F₁.T τ)⁻¹ * F₂.T τ) (wIdx N j) (wIdx N j) := by
        unfold detFac
        rw [if_pos (by show j ≤ j + 1; omega), if_neg (by show ¬ j + 1 = N; omega), mul_one]
      have := minor_reg M hz hF₁ hF₂ hG₁ hG₂ (τ, i) k hk (isStepRows_om i rfl r hr)
        (isStepRows_om i rfl s hs) (by show RegAt _ _ (detFac j i _)⁻¹; rw [e]; exact hW')
      rwa [minor_singleton] at this
    ·
      have hNj : j + 1 = N := by omega
      let i : Fin N := ⟨N - 1, by omega⟩
      have hp : M.blk (τ, i) = none := (M.blk_none _).2 fun h => h.2 (by show N - 1 + 1 = N; omega)
      have h := (detFac_improper M hz hF₁ hF₂ hG₁ hG₂ (τ, i) hp).1
      have hd : minorIJ ((F₁.T τ)⁻¹ * F₂.T τ) (wIdx N j) (wIdx N j) * ((F₁.T τ)⁻¹ * F₂.T τ) r s =
          detFac j i ((F₁.T τ)⁻¹ * F₂.T τ) := by
        have e : omIdx N j = {r} := by
          ext a
          have := a.2
          simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
          omega
        have ers : r = s := Fin.ext (by omega)
        unfold detFac
        rw [if_pos (by show j ≤ N - 1 + 1; omega), if_pos (by show N - 1 + 1 = N; omega), e, minor_singleton, ers]
      have hdet : ((F₁.T τ)⁻¹ * F₂.T τ).det ≠ 0 := by
        rw [Matrix.det_mul, Matrix.det_nonsing_inv]
        exact mul_ne_zero (by simpa using hT₁.2) hT₂.2
      have hne := detFac_ne_zero hjN i hC hdet
      have hW0 : minorIJ ((F₁.T τ)⁻¹ * F₂.T τ) (wIdx N j) (wIdx N j) ≠ 0 := fun h0 => hne (by
        rw [← hd, h0, zero_mul])
      have e2 : ((F₁.T τ)⁻¹ * F₂.T τ) r s =
          (minorIJ ((F₁.T τ)⁻¹ * F₂.T τ) (wIdx N j) (wIdx N j))⁻¹ * detFac j i ((F₁.T τ)⁻¹ * F₂.T τ) := by
        rw [← hd, inv_mul_cancel_left₀ hW0]
      rw [e2]
      exact ValRing.regAt_mul hW' h
  ·
    have hs : ¬ (s : ℕ) < N - j := fun h => hr (hrs.2 h)
    by_cases h2 : 2 ≤ j
    · let i : Fin N := ⟨0, by omega⟩
      obtain ⟨k, hk⟩ := proper i ⟨by show 0 + 1 ≠ j; omega, by show 0 + 1 ≠ N; omega⟩
      have e : detFac j i ((F₁.T τ)⁻¹ * F₂.T τ) = 1 := by
        unfold detFac
        rw [if_neg (by show ¬ j ≤ 0 + 1; omega), if_neg (by show ¬ 0 + 1 = N; omega), mul_one]
      have := minor_reg M hz hF₁ hF₂ hG₁ hG₂ (τ, i) k hk (isStepRows_singleton_low i rfl h2 hjN r (by omega))
        (isStepRows_singleton_low i rfl h2 hjN s (by omega))
        (by show RegAt _ _ (detFac j i _)⁻¹; rw [e, inv_one]; exact ValRing.regAt_one _ _)
      rwa [minor_singleton] at this
    · have hj1 : j = 1 := by omega
      subst hj1
      let i : Fin N := ⟨0, by omega⟩
      have hp : M.blk (τ, i) = none := (M.blk_none _).2 fun h => h.1 rfl
      have h := (detFac_improper M hz hF₁ hF₂ hG₁ hG₂ (τ, i) hp).1
      have e : detFac 1 i ((F₁.T τ)⁻¹ * F₂.T τ) = ((F₁.T τ)⁻¹ * F₂.T τ) r s := by
        have ew : wIdx N 1 = {r} := by
          ext a
          have := a.2
          simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
          omega
        have ers : r = s := Fin.ext (by omega)
        unfold detFac
        rw [if_pos (by show 1 ≤ 0 + 1; omega), ew, minor_singleton, ← ers]
        split_ifs with hN1
        · have eo : omIdx N 1 = ∅ := by
            ext a
            have := a.2
            have hN1' : 0 + 1 = N := hN1
            simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            omega
          rw [eo, minor_empty, mul_one]
        · rw [mul_one]
      rw [← e]
      exact h

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.FrameReg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameChangeRegularEntriesStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_change_regular_entries : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal M.x) → M.IsFrame F₁ → M.IsFrame F₂ → M.GoodAt F₁ (mCoordIdeal zb) → M.GoodAt F₂ (mCoordIdeal zb) → ∀ (τ : Ψ) (r s : Fin N), RegAt M.x (mCoordIdeal zb) (((F₁.T τ)⁻¹ * F₂.T τ) r s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.FrameReg.change_regular | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.FrameReg.change_regular | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.FrameReg.change_regular <;> assumption)
end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Scal

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem reg_prod_zpow (hz : z ∈ mcPts (mCoordIdeal x)) {κ : Type} [Fintype κ] (t : κ → Ω) (e : κ → ℤ)
    (h0 : ∀ k, t k ≠ 0) (ht : ∀ k, RegAt x (mCoordIdeal z) (t k)) (ht' : ∀ k, RegAt x (mCoordIdeal z) (t k)⁻¹) :
    RegAt x (mCoordIdeal z) (∏ k, t k ^ e k) ∧
      valAt x (∏ k, t k ^ e k) z = ∏ k, valAt x (t k) z ^ e k := by
  let u : κ → (regRing x z)ˣ := fun k =>
    ⟨⟨t k, ht k⟩, ⟨(t k)⁻¹, ht' k⟩, Subtype.ext (mul_inv_cancel₀ (h0 k)), Subtype.ext (inv_mul_cancel₀ (h0 k))⟩
  let f : (regRing x z)ˣ →* Ωˣ := Units.map (regRing x z).subtype.toMonoidHom
  let g : (regRing x z)ˣ →* ℂˣ := Units.map (regVal x hz).toMonoidHom
  let U : (regRing x z)ˣ := ∏ k, u k ^ e k
  have h1 : ((U : regRing x z) : Ω) = ∏ k, t k ^ e k := by
    have e1 : ((U : regRing x z) : Ω) = ((f U : Ωˣ) : Ω) := rfl
    rw [e1, map_prod, Units.coe_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  have h2 : valAt x ((U : regRing x z) : Ω) z = ∏ k, valAt x (t k) z ^ e k := by
    have e1 : valAt x ((U : regRing x z) : Ω) z = ((g U : ℂˣ) : ℂ) := rfl
    rw [e1, map_prod, Units.coe_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  rw [← h1]
  exact ⟨(U : regRing x z).2, h2⟩

theorem reg_detFac (hz : z ∈ mcPts (mCoordIdeal x)) {N : ℕ} (j : ℕ) (i : Fin N) {A : Matrix (Fin N) (Fin N) Ω}
    (hA : ∀ a b, RegAt x (mCoordIdeal z) (A a b)) :
    RegAt x (mCoordIdeal z) (detFac j i A) ∧ valAt x (detFac j i A) z = detFac j i (valMat x z A) := by
  have h₁ := reg_minor hz hA (wIdx N j) (wIdx N j)
  have h₂ := reg_minor hz hA (omIdx N j) (omIdx N j)
  unfold detFac
  split_ifs
  · exact ⟨ValRing.regAt_mul h₁.1 h₂.1, (reg_mul hz h₁.1 h₂.1).2.trans (by rw [h₁.2, h₂.2])⟩
  · rw [mul_one, mul_one]; exact h₁
  · rw [one_mul, one_mul]; exact h₂
  · rw [mul_one, mul_one]; exact ⟨ValRing.regAt_one x z, CovMap.LocImg.FV.valAt_one' hz⟩

theorem ratio_reg (hz : z ∈ mcPts (mCoordIdeal x)) {k : K} {c₁ c₂ : ι k}
    (h₁ : (X ⟨k, c₁⟩ : MRing ι) ∉ mCoordIdeal z) (h₂ : (X ⟨k, c₂⟩ : MRing ι) ∉ mCoordIdeal z) :
    x ⟨k, c₂⟩ / x ⟨k, c₁⟩ ≠ 0 ∧ RegAt x (mCoordIdeal z) (x ⟨k, c₂⟩ / x ⟨k, c₁⟩) ∧
      valAt x (x ⟨k, c₂⟩ / x ⟨k, c₁⟩) z = z ⟨k, c₂⟩ / z ⟨k, c₁⟩ := by
  have hne : ∀ {c : ι k}, (X ⟨k, c⟩ : MRing ι) ∉ mCoordIdeal z → z ⟨k, c⟩ ≠ 0 := fun {c} hc h0 => hc (by
    show mConeMap z (X ⟨k, c⟩) = 0
    rw [mConeMap, aeval_X, h0, map_zero, zero_mul])
  obtain ⟨hx₁, hv⟩ := CovGraph.isValueAt_coord_ratio K ι Ω x z k c₁ hz (hne h₁)
  obtain ⟨hx₂, -⟩ := CovGraph.isValueAt_coord_ratio K ι Ω x z k c₂ hz (hne h₂)
  refine ⟨div_ne_zero hx₂ hx₁, ⟨fun l => if l = k then 1 else 0, X ⟨k, c₂⟩, X ⟨k, c₁⟩,
    isMultiHomog_X_single ⟨k, c₂⟩, isMultiHomog_X_single ⟨k, c₁⟩, h₁, ?_⟩, ?_⟩
  · simp only [aeval_X]
    field_simp
  · rw [valAt_eq hz (hv c₂), inv_mul_eq_div]

end Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j) {F₁ F₂ : FrameData ι Ψ N M.Ω M.blk}


include M in
theorem detFac_change (h₁ : M.IsFrame F₁) (h₂ : M.IsFrame F₂) (p : Ψ × Fin N) :
    detFac j p.2 (F₂.T p.1) = detFac j p.2 (F₁.T p.1) * detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) := by
  have hT₁ := h₁.1 p.1
  have hu₁ : IsUnit (F₁.T p.1).det := hT₁.2.isUnit
  have h := ((GlobalTheory.T.block_diagonal_minor_vanishing M.Ω N j p.2 M.j_le).2.2.2 _ _ hT₁.1 ((hT₁.1.inv hu₁).mul (h₂.1 p.1).1)).2
  rwa [Matrix.mul_nonsing_inv_cancel_left _ _ hu₁] at h

theorem prod_ratio (c₁ : ∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) (p : Ψ × Fin N) :
    (∏ k', (M.x ⟨k', F₂.c k'⟩ / M.x ⟨k', F₁.c k'⟩) ^ M.b p k') * ∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k' =
      ∏ k', M.x ⟨k', F₂.c k'⟩ ^ M.b p k' := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k' _ => ?_
  rw [← mul_zpow, div_mul_cancel₀ _ (c₁ k')]


open CovMap.LocImg.FrameChange in
theorem frame_rel (h₁ : M.IsFrame F₁) (h₂ : M.IsFrame F₂) (c₁ : ∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) (p : Ψ × Fin N) (k : K)
    (hp : M.blk p = some k) (m : ι k) (I' : Finset (Fin N)) (hI' : IsStepRows N j p.2 I') :
    detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) * ∑ I, F₁.u ⟨k, m⟩ I * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' =
      (∏ k', (M.x ⟨k', F₂.c k'⟩ / M.x ⟨k', F₁.c k'⟩) ^ M.b p k') * F₂.u ⟨k, m⟩ I' := by
  have hj := M.j_le
  have hT₁ := h₁.1 p.1
  have hT₂ := h₂.1 p.1
  have hu₁ : IsUnit (F₁.T p.1).det := hT₁.2.isUnit
  have hA₁ : (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (c₁ k')
  have hS : IsBlockDiag j ((F₁.T p.1)⁻¹ * F₂.T p.1) := (hT₁.1.inv hu₁).mul hT₂.1
  have hE : IsBlockDiag j (unitCols I' (stepCols N j p.2) hI'.1 : Matrix (Fin N) (Fin N) M.Ω) :=
    unitCols_blockDiag _ _ _ (stepRows_same_side hI')
  have e1 := h₁.2.1 p k hp m _ (hS.mul hE)
  have e2 := h₂.2.1 p k hp m _ hE
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu₁] at e1
  have hm : ∀ I, minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1 * unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2) =
      minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' := fun I => by
    rw [(GlobalTheory.T.block_diagonal_minor_vanishing M.Ω N j p.2 hj).1]
    simp only [minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hr : ∑ I, F₂.u ⟨k, m⟩ I * minorIJ (unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2) =
      F₂.u ⟨k, m⟩ I' := by
    simp only [minor_unitCols, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [hm] at e1
  rw [hr] at e2
  have hd := detFac_change M h₁ h₂ p
  have hA := prod_ratio M (F₂ := F₂) c₁ p
  apply mul_left_cancel₀ hA₁
  linear_combination (-detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1)) * e1 + e2 -
    (∑ I, M.coef ⟨k, m⟩ I * minorIJ (F₂.T p.1 * unitCols I' (stepCols N j p.2) hI'.1) I (stepCols N j p.2)) * hd -
    F₂.u ⟨k, m⟩ I' * hA

theorem frame_none (h₁ : M.IsFrame F₁) (h₂ : M.IsFrame F₂) (c₁ : ∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0) (p : Ψ × Fin N)
    (hp : M.blk p = none) :
    F₂.υ p * ∏ k', (M.x ⟨k', F₂.c k'⟩ / M.x ⟨k', F₁.c k'⟩) ^ M.b p k' =
      detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) * F₁.υ p := by
  have hA₁ : (∏ k', M.x ⟨k', F₁.c k'⟩ ^ M.b p k') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (c₁ k')
  have e1 := h₁.2.2.2 p hp
  have e2 := h₂.2.2.2 p hp
  have hd := detFac_change M h₁ h₂ p
  have hA := prod_ratio M (F₂ := F₂) c₁ p
  apply mul_left_cancel₀ hA₁
  linear_combination (detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1)) * e1 - e2 + M.lam p * hd + F₂.υ p * hA

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal M.x) → M.IsFrame F₁ → M.IsFrame F₂ → M.GoodAt F₁ (mCoordIdeal zb) → M.GoodAt F₂ (mCoordIdeal zb) → (∀ τ, IsBlockDiag j (valMat M.x zb ((F₁.T τ)⁻¹ * F₂.T τ)) ∧ (valMat M.x zb ((F₁.T τ)⁻¹ * F₂.T τ)).det ≠ 0) ∧ ∀ p : Ψ × Fin N, (∀ k, M.blk p = some k → ∀ h : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j h → ∀ m : ι k, detFac j p.2 (valMat M.x zb ((F₁.T p.1)⁻¹ * F₂.T p.1)) * plk M F₁ zb p.2 ⟨k, m⟩ (valMat M.x zb ((F₁.T p.1)⁻¹ * F₂.T p.1) * h) = (∏ k', (zb ⟨k', F₂.c k'⟩ / zb ⟨k', F₁.c k'⟩) ^ M.b p k') * plk M F₂ zb p.2 ⟨k, m⟩ h) ∧ (M.blk p = none → valAt M.x (F₂.υ p) zb * (∏ k', (zb ⟨k', F₂.c k'⟩ / zb ⟨k', F₁.c k'⟩) ^ M.b p k') = detFac j p.2 (valMat M.x zb ((F₁.T p.1)⁻¹ * F₂.T p.1)) * valAt M.x (F₁.υ p) zb) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M zb F₁ F₂ hz hF₁ hF₂ hG₁ hG₂
  have hj := M.j_le
  have r₁₂ := GlobalTheory.T.frame_change_regular_entries K ι Φ y Ψ N j M zb F₁ F₂ hz hF₁ hF₂ hG₁ hG₂
  have r₂₁ := GlobalTheory.T.frame_change_regular_entries K ι Φ y Ψ N j M zb F₂ F₁ hz hF₂ hF₁ hG₂ hG₁
  have hprod : ∀ τ, ((F₁.T τ)⁻¹ * F₂.T τ) * ((F₂.T τ)⁻¹ * F₁.T τ) = 1 := fun τ => by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hF₂.1 τ).2.isUnit,
      Matrix.nonsing_inv_mul _ (hF₁.1 τ).2.isUnit]
  have hSS : ∀ τ, valMat M.x zb ((F₁.T τ)⁻¹ * F₂.T τ) * valMat M.x zb ((F₂.T τ)⁻¹ * F₁.T τ) = 1 := fun τ => by
    rw [← (regMat_mul hz (r₁₂ τ) (r₂₁ τ)).2, hprod]
    exact CovMap.LocImg.FV.valMat_one hz
  have hbd : ∀ τ, IsBlockDiag j ((F₁.T τ)⁻¹ * F₂.T τ) := fun τ =>
    ((hF₁.1 τ).1.inv (hF₁.1 τ).2.isUnit).mul (hF₂.1 τ).1
  have hbd' : ∀ τ, IsBlockDiag j ((F₂.T τ)⁻¹ * F₁.T τ) := fun τ =>
    ((hF₂.1 τ).1.inv (hF₂.1 τ).2.isUnit).mul (hF₁.1 τ).1
  refine ⟨fun τ => ⟨CovMap.LocImg.FV.valMat_blockDiag hz (hbd τ), fun h0 => ?_⟩, fun p => ?_⟩
  · have h := congrArg Matrix.det (hSS τ)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
    exact zero_ne_one h
  have ht := fun k : NonPluckerBlocks M.blk => ratio_reg hz (hG₁.1 k) (hG₂.1 k)
  have ht' := fun k : NonPluckerBlocks M.blk => ratio_reg hz (hG₂.1 k) (hG₁.1 k)
  have c₁ : ∀ k, M.x ⟨k, F₁.c k⟩ ≠ 0 := fun k h => (ht' k).1 (by rw [h, zero_div])
  obtain ⟨hrR, hrV⟩ := reg_prod_zpow hz (fun k : NonPluckerBlocks M.blk => M.x ⟨k, F₂.c k⟩ / M.x ⟨k, F₁.c k⟩) (M.b p)
    (fun k => (ht k).1) (fun k => (ht k).2.1) (fun k => by rw [inv_div]; exact (ht' k).2.1)
  simp only [fun k : NonPluckerBlocks M.blk => (ht k).2.2] at hrV
  obtain ⟨hdR, hdV⟩ := reg_detFac hz j p.2 (r₁₂ p.1)
  refine ⟨fun k hk h hh m => ?_, fun hp => ?_⟩
  · have hdet : ((F₁.T p.1)⁻¹ * F₂.T p.1).det ≠ 0 := fun h0 => by
      have h := congrArg Matrix.det (hprod p.1)
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h
      exact zero_ne_one h
    have hdne := CovMap.LocImg.FrameChange.detFac_ne_zero hj p.2 (hbd p.1) hdet
    obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = (∏ k', (M.x ⟨k', F₂.c k'⟩ / M.x ⟨k', F₁.c k'⟩) ^ M.b p k') /
        detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) := ⟨_, rfl⟩
    have hρ' : detFac j p.2 ((F₁.T p.1)⁻¹ * F₂.T p.1) * ρ =
        ∏ k', (M.x ⟨k', F₂.c k'⟩ / M.x ⟨k', F₁.c k'⟩) ^ M.b p k' := by
      rw [hρ, mul_comm]; exact div_mul_cancel₀ _ hdne
    have hrel : ∀ (m : ι k) (I' : Finset (Fin N)), IsStepRows N j p.2 I' →
        ∑ I, F₁.u ⟨k, m⟩ I * minorIJ ((F₁.T p.1)⁻¹ * F₂.T p.1) I I' = ρ * F₂.u ⟨k, m⟩ I' := fun m I' hI' => by
      apply mul_left_cancel₀ hdne
      rw [← mul_assoc, hρ']
      exact frame_rel M hF₁ hF₂ c₁ p k hk m I' hI'
    have hstep : IsStepRows N j p.2 (stepCols N j p.2) := CovMap.LocImg.FV.isStepRows_stepCols p.2
    have hinv : ∑ m : ι k, F₂.u' (stepCols N j p.2) ⟨k, m⟩ * F₂.u ⟨k, m⟩ (stepCols N j p.2) = 1 := by
      rw [hF₂.2.2.1 p k hk _ _ hstep hstep, if_pos rfl]
    obtain ⟨hρR, hval⟩ := CovMap.LocImg.FV.reg_values hz p.2 (fun (m : ι k) I => F₁.u ⟨k, m⟩ I)
      (fun (m : ι k) I => F₂.u ⟨k, m⟩ I) (fun m : ι k => F₂.u' (stepCols N j p.2) ⟨k, m⟩) _ ρ _ hstep
      (fun m I => (hG₁.2.1 _ _).1) (fun m I => (hG₂.2.1 _ _).1) (fun m => (hG₂.2.1 _ _).2) (r₁₂ p.1) hrel hinv
    have hmove : ∑ I, valAt M.x (F₁.u ⟨k, m⟩ I) zb *
          minorIJ (valMat M.x zb ((F₁.T p.1)⁻¹ * F₂.T p.1) * h) I (stepCols N j p.2) =
        valAt M.x ρ zb * ∑ I, valAt M.x (F₂.u ⟨k, m⟩ I) zb * minorIJ h I (stepCols N j p.2) :=
      CovMap.LocImg.FV.sum_minor_mul hj p.2 (fun (m : ι k) I => valAt M.x (F₁.u ⟨k, m⟩ I) zb)
        (fun (m : ι k) I => valAt M.x (F₂.u ⟨k, m⟩ I) zb) _ _ hval h hh m
    have hv : detFac j p.2 (valMat M.x zb ((F₁.T p.1)⁻¹ * F₂.T p.1)) * valAt M.x ρ zb =
        ∏ k', (zb ⟨k', F₂.c k'⟩ / zb ⟨k', F₁.c k'⟩) ^ M.b p k' := by
      rw [← hdV, ← (reg_mul hz hdR hρR).2, hρ', hrV]
    rw [plk, plk, hmove, ← mul_assoc, hv]
  · have e := congrArg (fun s => valAt M.x s zb) (frame_none M hF₁ hF₂ c₁ p hp)
    rw [(reg_mul hz (hG₂.2.2 p hp).2.1 hrR).2, (reg_mul hz hdR (hG₁.2.2 p hp).2.1).2, hrV, hdV] at e
    exact e

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.Scal
