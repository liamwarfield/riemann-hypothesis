module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMinimumLowerBoundHolds

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TwoSidedBoostBounds
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries BoostLowerBounds ImaginaryMajorants
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace TwoSidedBoostBounds

variable {r : ℕ} (X : Data E r)

theorem boost_upper (τ : X.Ψ) {z : Frame X.Ψ r} (hz : z ∈ X.dom) {e : Fin r → ℂ}
    (hee : hermC τ.1 X.Gm e e = 0) (he0 : e ≠ 0) {σ : ℝ} (hσ : 0 < σ) (w : Fin r → ℂ) :
    X.maj z τ (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w) ≤
      max (σ ^ 2) (σ ^ 2)⁻¹ * X.maj z τ w := by
  have hσ' : 0 < σ⁻¹ := inv_pos.2 hσ
  have ha : 0 < σ ^ 2 := by positivity
  have hl := BoostLowerBounds.boost_lower (X := X) (τ := τ) (z := z) hz hee he0 hσ'
    (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w)
  simp only [inv_inv] at hl
  obtain ⟨hm, hff, hef, hfe⟩ := BoostLowerBounds.plane_facts (X := X) (τ := τ) (z := z) hz hee he0
  rw [RankOneBoostIsometries.boost_comp X τ hm hee hff hef hfe hσ] at hl
  simp only [inv_pow, inv_inv] at hl
  have hmm : max (σ ^ 2) (σ ^ 2)⁻¹ * min (σ ^ 2)⁻¹ (σ ^ 2) = 1 := by
    rcases le_total (σ ^ 2) (σ ^ 2)⁻¹ with h | h
    · rw [max_eq_right h, min_eq_right h, inv_mul_cancel₀ ha.ne']
    · rw [max_eq_left h, min_eq_left h, mul_inv_cancel₀ ha.ne']
  have hM : 0 ≤ max (σ ^ 2) (σ ^ 2)⁻¹ := le_max_of_le_left ha.le
  calc X.maj z τ (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w)
      = max (σ ^ 2) (σ ^ 2)⁻¹ * (min (σ ^ 2)⁻¹ (σ ^ 2) *
          X.maj z τ (Matrix.mulVec (boost X τ e (X.jp z τ e) (X.maj z τ e) σ⁻¹) w)) := by
        rw [← mul_assoc, hmm, one_mul]
    _ ≤ max (σ ^ 2) (σ ^ 2)⁻¹ * X.maj z τ w := mul_le_mul_of_nonneg_left hl hM

theorem c_pos (τ : X.Ψ) : 0 < X.c τ := by
  unfold Data.c
  have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero _).2 X.ξ0_ne
  have := norm_pos_iff.2 h
  linarith

theorem maj_two_sided {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    (s : X.Ψ → ℂ) (hy : X.flow ξ s x ∈ X.dom) (τ : X.Ψ) (w : Fin r → ℂ) :
    0 < 1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ) ∧
    min (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
        (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ /
        (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 * X.maj x τ w ≤
      X.maj (X.flow ξ s x) τ w ∧
    X.maj (X.flow ξ s x) τ w ≤ max (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
        (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ *
        (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 * X.maj x τ w := by
  obtain ⟨_, hξξ, hξ0⟩ := hξ
  have hiso : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := fun τ => by
    rw [hermC_emb, hξξ, map_zero]
  have he0 : ∀ τ : X.Ψ, Data.emb τ.1 ξ ≠ 0 := fun τ h => hξ0 (funext fun a => by
    have := congrFun h a
    simpa [Data.emb] using this)
  have hIsoV : X.IsIsoV (fun τ => Data.emb τ.1 ξ) := fun τ => ⟨hiso τ, he0 τ⟩
  have hm0 : 0 ≤ X.maj x τ (Data.emb τ.1 ξ) := MajorantConjugateTransfer.maj_nonneg X hx τ _
  have hc0 : 0 ≤ X.c τ := (c_pos X τ).le
  have hyd : X.flow ξ (fun τ => ((s τ).re : ℂ)) x ∈ X.dom :=
    ((flowDomainCriterion_holds r X (fun τ => Data.emb τ.1 ξ) hIsoV x hx (fun τ => ((s τ).re : ℂ))).1).2
      (fun τ => by simp)
  have hsplit := flow_split (X := X) (ξ := ξ) hiso s x
  have hyd2 : X.flow ξ (fun τ => I * ((s τ).im : ℂ)) (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) ∈ X.dom :=
    hsplit ▸ hy
  have hmy : X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ) =
      X.maj x τ (Data.emb τ.1 ξ) := by
    rw [majorant_realFlow_transfer X ξ (fun τ => (s τ).re) hx hyd τ (hiso τ) (Data.emb τ.1 ξ),
      Data.flow_fix (X := X) (τ := τ) (ξ := ξ) _ _ (hiso τ)]
  have hq : 0 < 1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ) := by
    have h := ((flowDomainCriterion_holds r X (fun τ => Data.emb τ.1 ξ) hIsoV x hx s).1).1 hy τ
    simp only [Data.ttV, div_div_eq_mul_div, div_one] at h
    have e1 : (s τ).im * (X.c τ * X.maj x τ (Data.emb τ.1 ξ)) =
        X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ) := by ring
    linarith
  have hq' : 0 < 1 + X.c τ * (s τ).im *
      X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ) := by
    rw [hmy]; exact hq
  have hlow := ImaginaryMajorants.maj_imag_flow (X := X) hyd ξ (fun τ => (s τ).im) hyd2 τ (hiso τ) (he0 τ) hq' w
  have heq := ImaginaryMajorants.maj_imag_eq (X := X) hyd ξ (fun τ => (s τ).im) hyd2 τ (hiso τ) (he0 τ) hq' w
  have hsq : 0 < Real.sqrt (1 + X.c τ * (s τ).im *
      X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ (Data.emb τ.1 ξ)) := Real.sqrt_pos.2 hq'
  have hup := boost_upper X τ hyd (hiso τ) (he0 τ) hsq w
  rw [Real.sq_sqrt hq'.le] at hup
  simp only [hmy] at hlow heq hup
  have hyw := majorant_realFlow_transfer X ξ (fun τ => (s τ).re) hx hyd τ (hiso τ) w
  have hup1 := FlowMatrixMajorants.maj_flow_le (X := X) (τ := τ) (ξ := ξ) hx (-(s τ).re) w
  simp only [Complex.ofReal_neg, abs_neg] at hup1
  have hlo1 := FlowMatrixMajorants.maj_flow_le (X := X) (τ := τ) (ξ := ξ) hx ((s τ).re)
    (Matrix.mulVec (X.flowMat ξ τ (-((s τ).re : ℂ))) w)
  rw [FlowMatrixMajorants.flowMat_inv (X := X) (τ := τ) (ξ := ξ) (hiso τ)] at hlo1
  rw [← hyw] at hup1 hlo1
  have hP : 0 < (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 := by positivity
  have hmin0 : 0 ≤ min (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
      (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ := le_min hq.le (inv_nonneg.2 hq.le)
  have hmax0 : 0 ≤ max (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
      (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ := le_max_of_le_left hq.le
  have hdiv : X.maj x τ w / (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 ≤
      X.maj (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) τ w := by
    rw [div_le_iff₀ hP, mul_comm]
    exact hlo1
  rw [hsplit]
  refine ⟨hq, ?_, ?_⟩
  · calc _ = min (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))
          (1 + X.c τ * (s τ).im * X.maj x τ (Data.emb τ.1 ξ))⁻¹ *
          (X.maj x τ w / (1 + X.c τ * |(s τ).re| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiv hmin0
      _ ≤ _ := hlow
  · rw [heq]
    calc _ ≤ _ := hup
      _ ≤ _ := mul_le_mul_of_nonneg_left hup1 hmax0
      _ = _ := by ring

end TwoSidedBoostBounds

end ReciprocityTheory.ChartRestriction.G.FD
end

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MajorantConjugateTransfer TwoSidedBoostBounds
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace MinimumGrowthBounds

variable {r : ℕ} (X : Data E r)

theorem minimumSq_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) : 0 ≤ X.firstMinimumSq x := by
  apply Real.sInf_nonneg
  rintro t ⟨v, _, _, rfl⟩
  exact Finset.sum_nonneg fun τ _ =>
    mul_nonneg (TwoSidedBoostBounds.c_pos (X := X) τ).le (MajorantConjugateTransfer.maj_nonneg (X := X) hx τ _)

theorem minimumSq_two_sided_bounds {x y : Frame X.Ψ r} (hx : x ∈ X.dom) (hy : y ∈ X.dom) {k1 k2 : ℝ}
    (hk1 : 0 ≤ k1) (hk2 : 0 < k2) (hlow : ∀ τ w, k1 * X.maj x τ w ≤ X.maj y τ w)
    (hup : ∀ τ w, X.maj y τ w ≤ k2 * X.maj x τ w) :
    k1 * X.firstMinimumSq x ≤ X.firstMinimumSq y ∧ X.firstMinimumSq y ≤ k2 * X.firstMinimumSq x := by
  have hc : ∀ τ, 0 ≤ X.c τ := fun τ => (TwoSidedBoostBounds.c_pos (X := X) τ).le
  have e : ∀ g' : (Fin r → E) → ℝ, (¬ ∃ v ∈ X.Λ, v ≠ 0) → {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g' v} = ∅ := by
    intro g' hne
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨v, hv, hv', _⟩
    exact hne ⟨v, hv, hv'⟩
  have key1 : ∀ (g h : (Fin r → E) → ℝ) (a : ℝ), 0 ≤ a → (∀ v, 0 ≤ g v) → (∀ v, a * g v ≤ h v) →
      a * sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g v} ≤ sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = h v} := by
    intro g h a ha hg hgh
    by_cases hne : ∃ v ∈ X.Λ, v ≠ 0
    · obtain ⟨v0, hv0, hv0'⟩ := hne
      refine le_csInf ⟨_, v0, hv0, hv0', rfl⟩ ?_
      rintro t ⟨v, hv, hv', rfl⟩
      have hb : BddBelow {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g v} := ⟨0, by
        rintro s ⟨w, _, _, rfl⟩
        exact hg w⟩
      exact (mul_le_mul_of_nonneg_left (csInf_le hb ⟨v, hv, hv', rfl⟩) ha).trans (hgh v)
    · rw [e g hne, e h hne, Real.sInf_empty, mul_zero]
  have key2 : ∀ (g h : (Fin r → E) → ℝ) (a : ℝ), 0 < a → (∀ v, 0 ≤ g v) → (∀ v, g v ≤ a * h v) →
      sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g v} ≤ a * sInf {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = h v} := by
    intro g h a ha hg hgh
    by_cases hne : ∃ v ∈ X.Λ, v ≠ 0
    · obtain ⟨v0, hv0, hv0'⟩ := hne
      rw [← div_le_iff₀' ha]
      refine le_csInf ⟨_, v0, hv0, hv0', rfl⟩ ?_
      rintro t ⟨v, hv, hv', rfl⟩
      rw [div_le_iff₀' ha]
      have hb : BddBelow {t | ∃ v ∈ X.Λ, v ≠ 0 ∧ t = g v} := ⟨0, by
        rintro s ⟨w, _, _, rfl⟩
        exact hg w⟩
      exact (csInf_le hb ⟨v, hv, hv', rfl⟩).trans (hgh v)
    · rw [e g hne, e h hne, Real.sInf_empty, mul_zero]
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
  refine ⟨key1 _ _ k1 hk1 ?_ ?_, key2 _ _ k2 hk2 ?_ ?_⟩
  · intro v
    exact Finset.sum_nonneg fun τ _ => mul_nonneg (hc τ) (MajorantConjugateTransfer.maj_nonneg (X := X) hx τ _)
  · intro v
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ _ =>
      (mul_left_comm _ _ _).trans_le (mul_le_mul_of_nonneg_left (hlow τ _) (hc τ))
  · intro v
    exact Finset.sum_nonneg fun τ _ => mul_nonneg (hc τ) (MajorantConjugateTransfer.maj_nonneg (X := X) hy τ _)
  · intro v
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ _ =>
      (mul_le_mul_of_nonneg_left (hup τ _) (hc τ)).trans_eq (mul_left_comm _ _ _)

theorem sqrt_rpow_le (A : ℝ) {k1 k2 L Ly : ℝ} (hk1 : 0 < k1) (hk12 : k1 ≤ k2) (hL : 0 ≤ L)
    (h1 : k1 * L ≤ Ly) (h2 : Ly ≤ k2 * L) :
    Real.sqrt Ly ^ (-A) ≤ max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * Real.sqrt L ^ (-A) := by
  rcases hL.eq_or_lt with hL0 | hLpos
  · subst hL0
    have hLy : Ly = 0 := le_antisymm (by linarith) (by linarith)
    subst hLy
    simp only [Real.sqrt_zero]
    by_cases hA : A = 0
    · subst hA
      simp
    · rw [Real.zero_rpow (neg_ne_zero.mpr hA), mul_zero]
  · have hs : ∀ z : ℝ, 0 ≤ z → Real.sqrt z ^ (-A) = z ^ (-A / 2) := by
      intro z hz
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz]
      congr 1
      ring
    have hLy : 0 < Ly := lt_of_lt_of_le (mul_pos hk1 hLpos) h1
    rw [hs Ly hLy.le, hs L hL]
    have hLy_eq : Ly = Ly / L * L := (div_mul_cancel₀ Ly hLpos.ne').symm
    have hs1 : k1 ≤ Ly / L := by
      rw [le_div_iff₀ hLpos]
      exact h1
    have hs2 : Ly / L ≤ k2 := by
      rw [div_le_iff₀ hLpos]
      exact h2
    have hspos : 0 < Ly / L := lt_of_lt_of_le hk1 hs1
    rw [hLy_eq, Real.mul_rpow hspos.le hL]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL _)
    rcases le_total 0 (-A / 2) with hp | hp
    · exact (Real.rpow_le_rpow hspos.le hs2 hp).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos hk1 hs1 hp).trans (le_max_left _ _)

theorem nfac_pos (la : Wt X.Ψ r) {y : Frame X.Ψ r} (hy : y ∈ X.dom) : 0 < X.nfac la y := by
  have hd : ∀ τ i, dmin X.Gm y τ i ≠ 0 := by
    intro τ i h0
    have h1 := (hy τ).2 i
    rw [h0] at h1
    simp at h1
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
  exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _))) _

theorem growth (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (C A : ℝ)
    (hmod : ∀ z ∈ X.dom, X.pnorm la P z ≤ C * X.la1 z ^ (-A)) {x y : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hy : y ∈ X.dom) {k1 k2 : ℝ} (hk1 : 0 < k1) (hk12 : k1 ≤ k2)
    (hlow : ∀ τ w, k1 * X.maj x τ w ≤ X.maj y τ w) (hup : ∀ τ w, X.maj y τ w ≤ k2 * X.maj x τ w)
    {R : ℝ} (hR : X.nfac la x / X.nfac la y ≤ R) :
    ‖P y‖ * X.nfac la x ≤ max C 0 * max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * R * X.la1 x ^ (-A) := by
  have hny := nfac_pos X la hy
  have hnx := nfac_pos X la hx
  obtain ⟨b1, b2⟩ := minimumSq_two_sided_bounds X hx hy hk1.le (lt_of_lt_of_le hk1 hk12) hlow hup
  have hla : X.la1 y ^ (-A) ≤ max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * X.la1 x ^ (-A) :=
    sqrt_rpow_le A hk1 hk12 (minimumSq_nonneg X hx) b1 b2
  have hq0 : 0 ≤ X.nfac la x / X.nfac la y := div_nonneg hnx.le hny.le
  have hR0 : 0 ≤ R := le_trans hq0 hR
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hly : 0 ≤ X.la1 y ^ (-A) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hPy : ‖P y‖ * X.nfac la y ≤ max C 0 * X.la1 y ^ (-A) :=
    calc ‖P y‖ * X.nfac la y = X.pnorm la P y := rfl
      _ ≤ C * X.la1 y ^ (-A) := hmod y hy
      _ ≤ max C 0 * X.la1 y ^ (-A) := mul_le_mul_of_nonneg_right (le_max_left _ _) hly
  have hny' := hny.ne'
  calc ‖P y‖ * X.nfac la x = (‖P y‖ * X.nfac la y) * (X.nfac la x / X.nfac la y) := by
        field_simp
    _ ≤ (max C 0 * X.la1 y ^ (-A)) * R := mul_le_mul hPy hR hq0 (mul_nonneg hC0 hly)
    _ ≤ (max C 0 * (max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * X.la1 x ^ (-A))) * R := by gcongr
    _ = max C 0 * max (k1 ^ (-A / 2)) (k2 ^ (-A / 2)) * R * X.la1 x ^ (-A) := by ring

end MinimumGrowthBounds

end ReciprocityTheory.ChartRestriction.G.FD
