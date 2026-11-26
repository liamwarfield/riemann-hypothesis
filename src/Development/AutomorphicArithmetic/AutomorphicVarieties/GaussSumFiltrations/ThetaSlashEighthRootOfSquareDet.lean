module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertThetaSeriesPeriodicInversionFormula
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.LatticeNormalizedGaussSumEighthRoot

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.LatticeGaussSumTwistDualEqIndicator
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem sum_isReps_add_shift {V : Type} [AddCommGroup V] (A B : AddSubgroup V) (T : Finset V)
    (hT : IsReps A B T) (f : V → ℂ) (hf : ∀ x ∈ B, ∀ m ∈ A, f (x + m) = f x) (s : V) (hs : s ∈ B) :
    ∑ x ∈ T, f (x + s) = ∑ x ∈ T, f x := by
  classical
  obtain ⟨hTB, huniq⟩ := hT
  have key : ∀ x ∈ B, ∃ y ∈ T, x - y ∈ A := fun x hx => by
    obtain ⟨y, ⟨hy, hxy⟩, _⟩ := huniq x hx
    exact ⟨y, hy, hxy⟩
  choose! g hgT hgA using key
  have hfx : ∀ x ∈ T, f (x + s) = f (g (x + s)) := by
    intro x hx
    have hxs : x + s ∈ B := B.add_mem (hTB x hx) hs
    have h := hf (g (x + s)) (hTB _ (hgT _ hxs)) _ (hgA _ hxs)
    rw [← h]
    congr 1
    abel
  rw [Finset.sum_congr rfl hfx]
  apply Finset.sum_nbij (fun x => g (x + s))
  · intro x hx
    exact hgT _ (B.add_mem (hTB x hx) hs)
  · intro x hx x' hx' h
    simp only [Finset.mem_coe] at hx hx'
    have h1 := hgA _ (B.add_mem (hTB x hx) hs)
    have h2 := hgA _ (B.add_mem (hTB x' hx') hs)
    simp only at h
    rw [h] at h1
    have hd : x - x' ∈ A := by
      have h3 := A.sub_mem h1 h2
      convert h3 using 1
      abel
    obtain ⟨y, _, hy⟩ := huniq x (hTB x hx)
    have e1 := hy x ⟨hx, by rw [sub_self]; exact A.zero_mem⟩
    have e2 := hy x' ⟨hx', hd⟩
    rw [e1, e2]
  · intro y hy
    simp only [Finset.mem_coe] at hy
    have hys : y - s ∈ B := B.sub_mem (hTB y hy) hs
    refine ⟨g (y - s), hgT _ hys, ?_⟩
    have hxs : g (y - s) + s ∈ B := B.add_mem (hTB _ (hgT _ hys)) hs
    apply (huniq _ hxs).unique ⟨hgT _ hxs, hgA _ hxs⟩ ⟨hy, ?_⟩
    have h4 := A.neg_mem (hgA _ hys)
    convert h4 using 1
    abel
  · intro x hx
    rfl

theorem gaussSum_dual_shift : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ (N : ℕ) (a b c d : F) (T : Finset (κ → F)), 0 < N → (∀ y ∈ dualL F G, (N : F) • y ∈ LL F κ ∧ IsIntegral ℤ ((N : F) * QF G y)) → IsIntegral ℤ a → IsIntegral ℤ b → IsIntegral ℤ (c / N) → IsIntegral ℤ d → a * d - b * c = 1 → c ≠ 0 → IsReps (aL κ c) (aL κ (1 : F)) T → ∀ y ∈ dualL F G, (∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c)) * et (d / c * QF G y) = oneL y * ∑ x ∈ T, et (a / c * QF G x) := by
  intro F _ _ κ _ _ G hG N a b c d T hN hNy ha hb hcN hd hdet hc hT y hy
  obtain ⟨hBsymm, hsmul, hBadd, hint, hLLiff, haL, het, hLLdual⟩ := GlobalTheory.T.evenPos_gramForm_integral_lattice_properties F κ G hG
  obtain ⟨-, -, hdd, -, -⟩ := GlobalTheory.T.dualLattice_index_eq_discr_pow_mul_det_pow F κ G hG
  have etadd : ∀ u v : F, et (u + v) = et u * et v := fun u v => (het u v).1
  have etint : ∀ u : F, IsIntegral ℤ u → et u = 1 := fun u hu => (het u 0).2.2.2 hu
  have etiff : ∀ u : F, et u = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F u = n := fun u => (het u 0).2.2.1
  have hLLsmul : ∀ r : F, IsIntegral ℤ r → ∀ x ∈ LL F κ, r • x ∈ LL F κ := by
    intro r hr x hx
    rw [hLLiff] at hx ⊢
    intro i
    simpa [Pi.smul_apply, smul_eq_mul] using hr.mul (hx i)
  have hB1 : ∀ x, x ∈ aL κ (1 : F) ↔ x ∈ LL F κ := by
    intro x
    rw [haL]
    constructor
    · rintro ⟨l, hl, rfl⟩
      simpa using hl
    · intro hx
      exact ⟨x, hx, by simp⟩
  have hdualet : ∀ w ∈ dualL F G, ∀ l ∈ LL F κ, et (BF G w l) = 1 := by
    intro w hw l hl
    exact (etiff _).2 (hw l hl)
  have hexp : ∀ (x : κ → F) (r : F) (z : κ → F),
      QF G (x + r • z) = QF G x + r * BF G x z + r ^ 2 * QF G z := by
    intro x r z
    rw [(hBsymm x (r • z)).2, (hBsymm x (r • z)).1, (hsmul r z x).1, (hsmul r z x).2.1,
      (hBsymm z x).1]
  have hBlin : ∀ (y x : κ → F) (r : F) (z : κ → F),
      BF G y (x + r • z) = BF G y x + r * BF G y z := by
    intro y x r z
    rw [(hBsymm y (x + r • z)).1, hBadd, (hsmul r z y).1, (hBsymm x y).1, (hBsymm z y).1]
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hcw : ∀ w ∈ dualL F G, c • w ∈ LL F κ := by
    intro w hw
    have e : c • w = (c / N) • ((N : F) • w) := by
      rw [smul_smul]
      congr 1
      field_simp
    rw [e]
    exact hLLsmul _ hcN _ (hNy w hw).1
  have hcQ : ∀ w ∈ dualL F G, IsIntegral ℤ (a * c * QF G w) := by
    intro w hw
    have e : a * c * QF G w = a * (c / N) * ((N : F) * QF G w) := by
      field_simp
    rw [e]
    exact (ha.mul hcN).mul (hNy w hw).2
  have haB : ∀ x ∈ LL F κ, ∀ w ∈ dualL F G, et (a * BF G x w) = 1 := by
    intro x hx w hw
    rw [← (hsmul a x w).1, (hBsymm _ w).1]
    exact hdualet w hw _ (hLLsmul a ha x hx)
  have hg : ∀ x ∈ aL κ (1 : F), ∀ m ∈ aL κ c,
      et (a / c * QF G (x + m)) = et (a / c * QF G x) := by
    intro x hx m hm
    rw [hB1] at hx
    obtain ⟨l, hl, rfl⟩ := (haL c m).1 hm
    rw [hexp]
    have e : a / c * (QF G x + c * BF G x l + c ^ 2 * QF G l)
        = a / c * QF G x + (a * BF G x l + a * c * QF G l) := by
      field_simp
      ring
    rw [e, etadd, etint _ ((ha.mul ((hint x hx).2 l hl)).add (hcQ l (hLLdual hl))), mul_one]
  by_cases hyL : y ∈ LL F κ
  · have h1 : oneL y = 1 := by simp [oneL, hyL]
    rw [h1, one_mul, Finset.sum_mul]
    have hs : d • y ∈ aL κ (1 : F) := (hB1 _).2 (hLLsmul d hd y hyL)
    refine Eq.trans ?_ (sum_isReps_add_shift (aL κ c) (aL κ 1) T hT
      (fun x => et (a / c * QF G x)) hg (d • y) hs)
    apply Finset.sum_congr rfl
    intro x hxT
    have hx : x ∈ LL F κ := (hB1 x).1 (hT.1 x hxT)
    rw [hexp]
    have key : a / c * (QF G x + d * BF G x y + d ^ 2 * QF G y)
        = a / c * QF G x + BF G y x / c + d / c * QF G y
          + (b * BF G x y + b * d * QF G y) := by
      rw [(hBsymm x y).1]
      field_simp
      linear_combination (BF G y x + d * QF G y) * hdet
    rw [key, etadd, etint _ ((hb.mul ((hint x hx).2 y hyL)).add ((hb.mul hd).mul (hint y hyL).1)),
      mul_one, etadd, etadd]
  · have h0 : oneL y = 0 := by simp [oneL, hyL]
    rw [h0, zero_mul]
    obtain ⟨w, hw, hnot⟩ : ∃ w ∈ dualL F G, et (BF G y w) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hyL (hdd y (fun ν hν => (etiff _).1 (hcon ν hν)))
    have hs : c • w ∈ aL κ (1 : F) := (hB1 _).2 (hcw w hw)
    have hf : ∀ x ∈ aL κ (1 : F), ∀ m ∈ aL κ c,
        et (a / c * QF G (x + m)) * et (BF G y (x + m) / c)
          = et (a / c * QF G x) * et (BF G y x / c) := by
      intro x hx m hm
      rw [hg x hx m hm]
      congr 1
      obtain ⟨l, hl, rfl⟩ := (haL c m).1 hm
      rw [hBlin y x c l]
      have e : (BF G y x + c * BF G y l) / c = BF G y x / c + BF G y l := by
        field_simp
      rw [e, etadd, hdualet y hy l hl, mul_one]
    have h := sum_isReps_add_shift (aL κ c) (aL κ 1) T hT
      (fun x => et (a / c * QF G x) * et (BF G y x / c)) hf (c • w) hs
    have hmul : ∑ x ∈ T, et (a / c * QF G (x + c • w)) * et (BF G y (x + c • w) / c)
        = et (BF G y w) * ∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hxT
      have hx : x ∈ LL F κ := (hB1 x).1 (hT.1 x hxT)
      rw [hexp, hBlin]
      have e1 : a / c * (QF G x + c * BF G x w + c ^ 2 * QF G w)
          = a / c * QF G x + (a * BF G x w + a * c * QF G w) := by
        field_simp
        ring
      have e2 : (BF G y x + c * BF G y w) / c = BF G y x / c + BF G y w := by
        field_simp
      rw [e1, e2, etadd, etadd, etadd, haB x hx w hw, etint _ (hcQ w hw)]
      ring
    have hsum : ∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c) = 0 := by
      rw [hmul] at h
      have h5 : (et (BF G y w) - 1) * ∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c) = 0 := by
        rw [sub_mul, h, one_mul, sub_self]
      exact (mul_eq_zero.1 h5).resolve_left (sub_ne_zero.2 hnot)
    rw [hsum, zero_mul]

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_gaussSum_twist_dual_eq_indicator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ (N : ℕ) (a b c d : F) (T : Finset (κ → F)), 0 < N → (∀ y ∈ dualL F G, (N : F) • y ∈ LL F κ ∧ IsIntegral ℤ ((N : F) * QF G y)) → IsIntegral ℤ a → IsIntegral ℤ b → IsIntegral ℤ (c / N) → IsIntegral ℤ d → a * d - b * c = 1 → c ≠ 0 → IsReps (aL κ c) (aL κ (1 : F)) T → ∀ y ∈ dualL F G, (∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c)) * et (d / c * QF G y) = oneL y * ∑ x ∈ T, et (a / c * QF G x) := by
  first | exact @GlobalTheory.HilbertThetaSeries.gaussSum_dual_shift | exact GlobalTheory.HilbertThetaSeries.gaussSum_dual_shift | (intros; apply GlobalTheory.HilbertThetaSeries.gaussSum_dual_shift <;> assumption)
end

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.ThetaLevel

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem pos_toInf {γ : GL (Fin 2) F} (h : γ.val.det = 1) : Pos (toInf γ) := by
  intro v
  have e : (↑(toInf γ) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det = rhom γ.val.det := by
    rw [RingHom.map_det]
    rfl
  rw [e, h, map_one]
  exact one_pos

def low (x : F) : GL (Fin 2) F where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem natCast_int (N : ℕ) : IsIntegral ℤ (N : F) := by
  exact isIntegral_natCast N

theorem decomp (γ : GL (Fin 2) F) (hdet : γ.val.det = 1) (hc : γ.val 1 0 ≠ 0) :
    γ = aff 1 (γ.val 0 0 / γ.val 1 0) * wm (Units.mk0 _ hc) * aff 1 (γ.val 1 1 / γ.val 1 0) := by
  have had : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = 1 := by rw [← hdet, Matrix.det_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, wm, Matrix.mul_apply, Fin.sum_univ_succ] <;> field_simp <;> linear_combination (-1 : F) * had

private theorem sl0_mul_of_pos (k : ℕ) (g h : GL (Fin 2) (InfinitePlace F → ℝ)) (hh : Pos h)
    (f : Hn F → ℂ) : sl0 k (g * h) f = sl0 k h (sl0 k g f) := by
  funext z
  simp only [sl0]
  have hact : act (g * h) z = act g (act h z) := by
    funext v
    simp only [act, map_mul, mul_smul]
  have hden : ∀ v, UpperHalfPlane.denom (cmp v (g * h)) (z v) =
      UpperHalfPlane.denom (cmp v g) (act h z v) * UpperHalfPlane.denom (cmp v h) (z v) := by
    intro v
    have hpos : 0 < ((cmp v h).det : ℝ) := by
      have e : ((cmp v h).det : ℝ) =
          (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v := by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two]
        simp [cmp]
      rw [e]
      exact hh v
    rw [map_mul, UpperHalfPlane.denom_cocycle_σ]
    simp only [UpperHalfPlane.σ, if_pos hpos, ContinuousAlgEquiv.refl_apply]
    rfl
  rw [hact, Finset.prod_congr rfl (fun v _ => hden v), Finset.prod_mul_distrib, mul_inv, mul_pow]
  ring

private theorem sl0_smul (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (ζ : ℂ)
    (f : Hn F → ℂ) : sl0 k h (ζ • f) = ζ • sl0 k h f := by
  funext z
  simp only [sl0, Pi.smul_apply, smul_eq_mul]
  ring

theorem main_abcd {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) (hG : EvenPos G) (t : ℕ)
    (ht : G.det = (t : ℤ) ^ 2) (k : ℕ) (hk : Fintype.card κ = 2 * k) (N : ℕ) (hN0 : 0 < N)
    (hN : ∀ y ∈ dualL F G, (N : F) • y ∈ LL F κ ∧ IsIntegral ℤ ((N : F) * QF G y))
    (a b c d : F) (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b) (hcN : IsIntegral ℤ (c / N)) (hd : IsIntegral ℤ d)
    (had : a * d - b * c = 1) (hc : c ≠ 0) :
    ∃ ζ : ℂ, ζ ^ 8 = 1 ∧
      sl0 k (toInf (aff 1 (a / c) * wm (Units.mk0 c hc) * aff 1 (d / c))) (th G oneL) = ζ • th G oneL := by
  have hNF : (N : F) ≠ 0 := by exact_mod_cast hN0.ne'
  have hcI : IsIntegral ℤ c := by
    have h1 := (natCast_int (F := F) N).mul hcN
    rwa [mul_div_cancel₀ _ hNF] at h1
  obtain ⟨T, hT, -, hTle, -⟩ := GlobalTheory.T.exists_finite_reps_scaled_lattice_card_norm F κ c 1 hc one_ne_zero (by rwa [div_one])
  obtain ⟨hsymm, hsc, -, hint, hLL, haL, het, hLd⟩ := GlobalTheory.T.evenPos_gramForm_integral_lattice_properties F κ G hG
  have hsupp : ∀ x : κ → F, (fun x => oneL x * et (a / c * QF G x)) x ≠ 0 → x ∈ aL κ (1 : F) := by
    intro x hx
    have hxL : x ∈ LL F κ := by
      by_contra hn
      apply hx
      simp [oneL, hn]
    exact (haL 1 x).2 ⟨x, hxL, (one_smul F x).symm⟩
  have hper : ∀ x l : κ → F, l ∈ aL κ c →
      (fun x => oneL x * et (a / c * QF G x)) (x + l) = (fun x => oneL x * et (a / c * QF G x)) x := by
    intro x l hl
    obtain ⟨m, hm, rfl⟩ := (haL c l).1 hl
    have hcm : c • m ∈ LL F κ := by
      rw [hLL]
      intro i
      rw [Pi.smul_apply, smul_eq_mul]
      exact hcI.mul ((hLL m).1 hm i)
    by_cases hx : x ∈ LL F κ
    · have hxl : x + c • m ∈ LL F κ := add_mem hx hcm
      simp only [oneL, if_pos hx, if_pos hxl, one_mul]
      rw [(hsymm x (c • m)).2, (hsymm x (c • m)).1, (hsc c m x).1, (hsc c m x).2.1]
      have e : a / c * (QF G x + c * BF G m x + c ^ 2 * QF G m) =
          a / c * QF G x + (a * BF G m x + a * c * QF G m) := by
        field_simp
        ring
      have hi : IsIntegral ℤ (a * BF G m x + a * c * QF G m) :=
        (ha.mul ((hint m hm).2 x hx)).add ((ha.mul hcI).mul (hint m hm).1)
      rw [e, (het (a / c * QF G x) (a * BF G m x + a * c * QF G m)).1,
        (het (a * BF G m x + a * c * QF G m) 0).2.2.2 hi, mul_one]
    · have hxl : x + c • m ∉ LL F κ := by
        intro h
        apply hx
        simpa using sub_mem h hcm
      simp [oneL, hx, hxl]
  have hW' := GlobalTheory.T.hilbertThetaSeries_periodic_inversion_formula F κ G hG t ht k hk c 1 (Units.mk0 c hc) T
    (fun x => oneL x * et (a / c * QF G x)) hc one_ne_zero hTle hT hsupp hper
  have hW : Pos (toInf (wm (Units.mk0 c hc))) := pos_toInf (by simp [wm, Matrix.det_fin_two, hc])
  have hB : Pos (toInf (aff 1 (d / c))) := pos_toInf (by simp [aff, Matrix.det_fin_two])
  rw [map_mul, sl0_mul_of_pos _ _ _ hB, map_mul, sl0_mul_of_pos _ _ _ hW, GlobalTheory.T.thetaSeries_translation_twists_coefficients, hW',
    GlobalTheory.T.thetaSeries_translation_twists_coefficients]
  refine ⟨wC k t c c * ∑ x ∈ T, et (a / c * QF G x),
    GlobalTheory.T.lattice_normalized_gaussSum_eighth_root F κ G hG t ht k hk N a b c d T hN0 hN ha hb hcN hd had hc hT, ?_⟩
  funext z
  simp only [th, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  congr 1
  funext y
  have key : wT G k t c (↑(Units.mk0 c hc)) T (fun x => oneL x * et (a / c * QF G x)) y *
      et (d / c * QF G y) = wC k t c c * (∑ x ∈ T, et (a / c * QF G x)) * oneL y := by
    have hcc : (c / c) • y = y := by rw [div_self hc, one_smul]
    by_cases hy : y ∈ dualL F G
    · have hsum : ∑ x ∈ T, oneL x * et (a / c * QF G x) * et (BF G y x / c) =
          ∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxL : x ∈ LL F κ := by
          obtain ⟨l, hl, hxl⟩ := (haL 1 x).1 (hT.1 x hx)
          rw [hxl, one_smul]
          exact hl
        simp [oneL, hxL]
      have h62 := GlobalTheory.T.lattice_gaussSum_twist_dual_eq_indicator F κ G hG N a b c d T hN0 hN ha hb hcN hd had hc hT y hy
      simp only [wT, Units.val_mk0, hcc, hy, ↓reduceIte]
      rw [hsum, mul_assoc, h62]
      ring
    · have hyL : y ∉ LL F κ := fun h => hy (hLd h)
      simp only [wT, Units.val_mk0, hcc, hy, ↓reduceIte, oneL, hyL]
      ring
  rw [key]
  ring

theorem main_ne {κ : Type} [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ) (hG : EvenPos G) (t : ℕ)
    (ht : G.det = (t : ℤ) ^ 2) (k : ℕ) (hk : Fintype.card κ = 2 * k) (N : ℕ) (hN0 : 0 < N)
    (hN : ∀ y ∈ dualL F G, (N : F) • y ∈ LL F κ ∧ IsIntegral ℤ ((N : F) * QF G y))
    (γ : GL (Fin 2) F) (hγ : InGam N γ) (hc : γ.val 1 0 ≠ 0) :
    ∃ ζ : ℂ, ζ ^ 8 = 1 ∧ sl0 k (toInf γ) (th G oneL) = ζ • th G oneL := by
  obtain ⟨hdet, ha, hb, hcN, hd⟩ := hγ
  have had : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact hdet
  rw [decomp γ hdet hc]
  exact main_abcd G hG t ht k hk N hN0 hN _ _ _ _ ha hb hcN hd had hc

theorem low_inGam (N : ℕ) (hN0 : 0 < N) : InGam N (low (-(N : F))) := by
  have hNF : (N : F) ≠ 0 := by exact_mod_cast hN0.ne'
  refine ⟨by simp [low, Matrix.det_fin_two], by simp [low, isIntegral_one], by simp [low, isIntegral_zero], ?_, by simp [low, isIntegral_one]⟩
  have : (low (-(N : F))).val 1 0 / N = -1 := by simp [low, hNF]
  rw [this]; exact isIntegral_one.neg

end GlobalTheory.HilbertThetaSeries.ThetaLevel


open GlobalTheory.HilbertThetaSeries.ThetaLevel in
theorem GlobalTheory.HilbertThetaSeries.theta_level_eighth_root : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∃ N : ℕ, 0 < N ∧ ∀ γ : GL (Fin 2) F, InGam N γ → ∃ ζ : ℂ, ζ ^ 8 = 1 ∧ sl0 k (toInf γ) (th G oneL) = ζ • th G oneL := by
  intro F _ _ _ κ _ _ G hG t ht k hk
  obtain ⟨N, hN0, hN⟩ := (GlobalTheory.T.dualLattice_index_eq_discr_pow_mul_det_pow F κ G hG).2.1
  refine ⟨N, hN0, fun γ hγ => ?_⟩
  by_cases hc : γ.val 1 0 = 0
  · have hNF : (N : F) ≠ 0 := by exact_mod_cast hN0.ne'
    obtain ⟨hdet, ha, hb, hcN, hd⟩ := hγ
    have hdet' : γ.val 0 0 * γ.val 1 1 = 1 := by
      rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
      exact hdet
    have hd0 : γ.val 1 1 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hdet'
      exact zero_ne_one hdet'
    have hNI : IsIntegral ℤ (N : F) := natCast_int N
    have e3 : ∀ i j, (γ * low (N : F)).val i j =
        γ.val i 0 * (low (N : F)).val 0 j + γ.val i 1 * (low (N : F)).val 1 j := by
      intro i j
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hγ3 : InGam N (γ * low (N : F)) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [Units.val_mul, Matrix.det_mul, hdet]
        simp [low, Matrix.det_fin_two]
      · rw [e3]
        simp only [low, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, mul_one]
        exact ha.add (hb.mul hNI)
      · rw [e3]
        simpa [low] using hb
      · rw [e3]
        simp only [low, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.empty_val', Matrix.cons_val_fin_one, mul_one, hc, zero_mul, zero_add]
        rw [mul_div_cancel_right₀ _ hNF]
        exact hd
      · rw [e3]
        simpa [low, hc] using hd
    have hc3 : (γ * low (N : F)).val 1 0 ≠ 0 := by
      rw [e3]
      simpa [low, hc] using mul_ne_zero hd0 hNF
    have hlow : (low (-(N : F))).val 1 0 ≠ 0 := by
      simpa [low] using hNF
    obtain ⟨ζ1, h1, e1⟩ := main_ne G hG t ht k hk N hN0 hN _ hγ3 hc3
    obtain ⟨ζ2, h2, e2⟩ := main_ne G hG t ht k hk N hN0 hN _ (low_inGam N hN0) hlow
    have hγe : γ = γ * low (N : F) * low (-(N : F)) := by
      rw [mul_assoc]
      conv_lhs => rw [← mul_one γ]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [low, Matrix.mul_apply, Fin.sum_univ_succ]
    have hP : Pos (toInf (low (-(N : F)))) := pos_toInf (by simp [low, Matrix.det_fin_two])
    refine ⟨ζ1 * ζ2, by rw [mul_pow, h1, h2, one_mul], ?_⟩
    rw [hγe, map_mul, sl0_mul_of_pos _ _ _ hP, e1, sl0_smul, e2, smul_smul]
  · exact main_ne G hG t ht k hk N hN0 hN γ hγ hc

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_slash_eighth_root_of_square_det : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∃ N : ℕ, 0 < N ∧ ∀ γ : GL (Fin 2) F, InGam N γ → ∃ ζ : ℂ, ζ ^ 8 = 1 ∧ sl0 k (toInf γ) (th G oneL) = ζ • th G oneL := by
  first | exact @GlobalTheory.HilbertThetaSeries.theta_level_eighth_root | exact GlobalTheory.HilbertThetaSeries.theta_level_eighth_root | (intros; apply GlobalTheory.HilbertThetaSeries.theta_level_eighth_root <;> assumption)
