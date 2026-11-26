module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSchurW
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroupA

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JMixedA
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.MixedNormBounds

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ConjugateNormInequalities

variable {k r : ℕ}

theorem gN_map_conj (M : Mat k r) : gN (M.map (starRingEnd ℂ)) = gN M := by
  simp only [gN, Matrix.map_apply, Complex.normSq_conj]

theorem gN_le_gbar {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hE : IsUnit (embWb k r γ).det) (y : Mat k r) :
    gN y ≤ (gN (embWb k r γ) * gN (embWb k r γ)⁻¹) ^ 2 * gN (gbar k r γ y) := by
  obtain ⟨y', hy'⟩ : ∃ y', y' = gbar k r γ y := ⟨_, rfl⟩
  have h1 : gN y = gN (gbar k r γ y') := by rw [hy', InvGrp.gbar_gbar hE]
  rw [h1, ← hy']
  unfold gbar
  set E := embWb k r γ
  have hE0 := gN_nonneg E
  have hEi0 := gN_nonneg E⁻¹
  calc gN (E * (E⁻¹ * y' * E).map (starRingEnd ℂ) * E⁻¹)
      ≤ gN E * gN ((E⁻¹ * y' * E).map (starRingEnd ℂ)) * gN E⁻¹ :=
        (gN_mul_le _ _).trans (mul_le_mul_of_nonneg_right (gN_mul_le _ _) hEi0)
    _ = gN E * gN (E⁻¹ * y' * E) * gN E⁻¹ := by rw [gN_map_conj]
    _ ≤ gN E * (gN E⁻¹ * gN y' * gN E) * gN E⁻¹ := by
        gcongr
        exact (gN_mul_le _ _).trans (mul_le_mul_of_nonneg_right (gN_mul_le _ _) hE0)
    _ = (gN E * gN E⁻¹) ^ 2 * gN y' := by ring

theorem rpow_bound {A B K a : ℝ} (hA : 0 < A) (hK : 0 < K) (ha : 0 ≤ a) (h : A ≤ K * B) :
    B ^ (-a) ≤ K ^ a * A ^ (-a) := by
  have hB : A / K ≤ B := by rw [div_le_iff₀ hK, mul_comm]; exact h
  have hAK : 0 < A / K := div_pos hA hK
  calc B ^ (-a) ≤ (A / K) ^ (-a) := Real.rpow_le_rpow_of_nonpos hAK hB (by linarith)
    _ = K ^ a * A ^ (-a) := by
      rw [Real.div_rpow hA.le hK.le, Real.rpow_neg hK.le, div_eq_mul_inv, inv_inv, mul_comm]

theorem inner_sig_sig (X : SigData k r) {h : Mat k r} (hh : h ∈ GV k r) (a b : X.Hs) :
    ⟪X.σ h a, X.σ h b⟫_ℂ = ⟪a, b⟫_ℂ := (⟨(X.σ h).toLinearMap, X.rep.2.1 h hh⟩ : X.Hs →ₗᵢ[ℂ] X.Hs).inner_map_map a b

theorem inner_sig_left (X : SigData k r) (hG : IsClosedSubgroup (GV k r)) {h : Mat k r} (hh : h ∈ GV k r)
    (a b : X.Hs) : ⟪X.σ h a, b⟫_ℂ = ⟪a, X.σ h⁻¹ b⟫_ℂ := by
  have hi : h⁻¹ ∈ GV k r := hG.inv_mem h hh
  have hb : X.σ h (X.σ h⁻¹ b) = b := by
    have e := X.rep.1.2 h hh h⁻¹ hi
    rw [Matrix.mul_nonsing_inv _ (hG.unit h hh), X.rep.1.1] at e
    have e2 := congrArg (fun T : X.Hs →L[ℂ] X.Hs => T b) e
    simpa using e2.symm
  conv_lhs => rw [← hb]
  exact inner_sig_sig X hh a _

theorem exists_inner_ne (X : SigData k r) (hG : IsClosedSubgroup (GV k r)) (v : X.Hs) (hv : v ≠ 0) :
    ∃ g ∈ GV k r, ⟪v, X.σ g X.w⟫_ℂ ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  let S : Submodule ℂ X.Hs :=
    { carrier := {u | ∀ g ∈ GV k r, ⟪v, X.σ g u⟫_ℂ = 0}
      add_mem' := by
        intro a b ha hb g hg
        rw [map_add (f := _), inner_add_right, ha g hg, hb g hg, add_zero]
      zero_mem' := by
        intro g hg
        rw [map_zero, inner_zero_right]
      smul_mem' := by
        intro c a ha g hg
        rw [map_smul, inner_smul_right, ha g hg, mul_zero] }
  have hSc : IsClosed (S : Set X.Hs) := by
    have e : (S : Set X.Hs) = ⋂ g ∈ GV k r, (fun u => ⟪v, X.σ g u⟫_ℂ) ⁻¹' {0} := by
      ext u
      show (∀ g ∈ GV k r, ⟪v, X.σ g u⟫_ℂ = 0) ↔ _
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    rw [e]
    exact isClosed_biInter fun g _ => isClosed_singleton.preimage (continuous_const.inner (X.σ g).continuous)
  have hSi : ∀ g ∈ GV k r, ∀ u ∈ S, X.σ g u ∈ S := by
    intro g hg u hu g' hg'
    have e := X.rep.1.2 g' hg' g hg
    have e2 : X.σ g' (X.σ g u) = X.σ (g' * g) u := by rw [e]; rfl
    show ⟪v, X.σ g' (X.σ g u)⟫_ℂ = 0
    rw [e2]
    exact hu _ (hG.mul_mem g' hg' g hg)
  have hw : X.w ∈ S := fun g hg => hcon g hg
  rcases X.irr S hSc hSi with h | h
  · have h0 : X.w = 0 := by
      rw [h] at hw
      exact (Submodule.mem_bot ℂ).mp hw
    have h1 := X.w_norm
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  · have hv' : v ∈ S := by rw [h]; exact Submodule.mem_top
    have h0 := hv' 1 hG.one_mem
    rw [X.rep.1.1, ContinuousLinearMap.one_apply, inner_self_eq_zero] at h0
    exact hv h0

end ReciprocityTheory.ChartRestriction.DS.Mult1.MixedNormBounds
end
end

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ConjugateNormInequalities MixedNormBounds

theorem stMixed (h : UnitaryGroupStructuralFacts) : StMixed := by
  obtain ⟨hB2, -, -, -, hUWb, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hInt, hLow, -, -, -, hCG, -⟩ := hB2
  intro k r Wp _ _ _ D X hD hSq γ hγ haM C hC u hu
  have hG := hCG k r
  have hEG : embWb k r γ ∈ GV k r := by
    have hmem : embWb k r γ ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ, hγ.1, rfl⟩
    exact hmem.1
  have hE := hG.unit _ hEG
  obtain ⟨d, hd⟩ := stSchurG k r Wp D X hD hSq
  obtain ⟨C₁, hC₁⟩ := hu
  have hn1 : (1 : ℝ) ≤ nR k r := by simp only [nR]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have ha0 : 0 ≤ X.a := le_trans (by simp only [aM]; positivity) haM
  set b := AG k r + 1 with hb
  have hb0 : 0 ≤ b := by simp only [hb, AG]; positivity
  have hab : b ≤ X.a := by
    refine le_trans ?_ haM
    simp only [hb, AG, aM]
    nlinarith [mul_le_mul hn1 hn1 zero_le_one (by linarith), sq_nonneg (nR k r)]
  have hCw : C X.w ≠ 0 := by
    intro h0
    have h1 := C.norm_map X.w
    rw [h0, norm_zero, X.w_norm] at h1
    exact zero_ne_one h1
  obtain ⟨g₂, hg₂, hc₀⟩ := exists_inner_ne X hG (C X.w) hCw
  have hg2i : g₂⁻¹ ∈ GV k r := hG.inv_mem _ hg₂

  set K : ℝ := (gN (embWb k r γ) * gN (embWb k r γ)⁻¹) ^ 2 with hK
  have hK0 : 0 < K := by
    have h1 := hLow k r _ hEG
    have h2 := hLow k r _ (hG.inv_mem _ hEG)
    have : 1 ≤ gN (embWb k r γ) * gN (embWb k r γ)⁻¹ := by nlinarith
    simp only [hK]; positivity
  set c : ℝ := max (gN (Hpk k r) ^ 2) 1 with hc
  have hc0 : 0 < c := lt_of_lt_of_le one_pos (le_max_right _ _)
  set Lc : ℝ := c * gN g₂⁻¹ with hLc
  have hL0 : 0 < Lc := mul_pos hc0 (by linarith [hLow k r _ hg2i])
  set K₁ : ℝ := max C₁ 0 * K ^ X.a with hK₁
  set K₂ : ℝ := max X.Cw 0 * Lc ^ X.a with hK₂
  have hK₁0 : 0 ≤ K₁ := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hK0.le _)
  have hK₂0 : 0 ≤ K₂ := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hL0.le _)

  have f1 : ∀ y ∈ GV k r, ‖⟪C X.w, X.σ y (C u)⟫_ℂ‖ ≤ K₁ * gN y ^ (-X.a) := by
    intro y hy
    have hgb := InvGrp.gbar_mem_GV hG hEG y hy
    have e : ⟪C X.w, X.σ y (C u)⟫_ℂ = ⟪X.σ (gbar k r γ y) u, X.w⟫_ℂ := by
      rw [← hC y hy X.w u, inner_sig_left X hG hgb]
      rfl
    rw [e, norm_inner_symm]
    have hb1 : ‖⟪X.w, X.σ (gbar k r γ y) u⟫_ℂ‖ ≤ C₁ * gN (gbar k r γ y) ^ (-X.a) := hC₁ _ hgb
    have hy1 := hLow k r y hy
    have hrb := rpow_bound (by linarith) hK0 ha0 (gN_le_gbar hE y)
    calc ‖⟪X.w, X.σ (gbar k r γ y) u⟫_ℂ‖ ≤ C₁ * gN (gbar k r γ y) ^ (-X.a) := hb1
      _ ≤ max C₁ 0 * gN (gbar k r γ y) ^ (-X.a) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (gN_nonneg _) _)
      _ ≤ max C₁ 0 * (K ^ X.a * gN y ^ (-X.a)) := mul_le_mul_of_nonneg_left hrb (le_max_right _ _)
      _ = K₁ * gN y ^ (-X.a) := by rw [hK₁]; ring
  have f2 : ∀ g ∈ GV k r, ‖⟪X.σ g₂ X.w, X.σ g X.w⟫_ℂ‖ ≤ K₂ * gN g ^ (-X.a) := by
    intro g hg
    have hm := hG.mul_mem _ hg2i _ hg
    have e : ⟪X.σ g₂ X.w, X.σ g X.w⟫_ℂ = ⟪X.w, X.σ (g₂⁻¹ * g) X.w⟫_ℂ := by
      rw [inner_sig_left X hG hg₂, X.rep.1.2 _ hg2i _ hg]
      rfl
    rw [e]
    have hb1 := X.dec _ hm
    have hle : gN g ≤ Lc * gN (g₂⁻¹ * g) := by
      calc gN g ≤ gN (Hpk k r) ^ 2 * (gN g₂⁻¹ * gN (g₂⁻¹ * g)) := gN_le_mul hg2i g
        _ ≤ c * (gN g₂⁻¹ * gN (g₂⁻¹ * g)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg (gN_nonneg _) (gN_nonneg _))
        _ = Lc * gN (g₂⁻¹ * g) := by rw [hLc]; ring
    have hrb := rpow_bound (by linarith [hLow k r g hg]) hL0 ha0 hle
    calc ‖⟪X.w, X.σ (g₂⁻¹ * g) X.w⟫_ℂ‖ ≤ X.Cw * gN (g₂⁻¹ * g) ^ (-X.a) := hb1
      _ ≤ max X.Cw 0 * gN (g₂⁻¹ * g) ^ (-X.a) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (gN_nonneg _) _)
      _ ≤ max X.Cw 0 * (Lc ^ X.a * gN g ^ (-X.a)) := mul_le_mul_of_nonneg_left hrb (le_max_right _ _)
      _ = K₂ * gN g ^ (-X.a) := by rw [hK₂]; ring

  set c₀ : ℂ := ⟪C X.w, X.σ g₂ X.w⟫_ℂ with hc₀def
  set I : ℝ≥0∞ := ∫⁻ g : Mt k r, ENNReal.ofReal (gN (Matrix.of g) ^ (-b)) ∂D.μG with hI
  have hIfin : I < ∞ := hInt k r D.μG b D.haarG (AB_le_AG k r)
  refine ⟨d / ‖c₀‖ * (K₁ * K₂ * c⁻¹ ^ (-(X.a - b)) * I.toReal), fun x hx => ?_⟩
  have hexp : -(X.a - AG k r - 1) = -(X.a - b) := by rw [hb]; ring
  rw [hexp]
  have hX1 : 1 ≤ gN x := hLow k r x hx
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.1.ne'
  obtain ⟨-, hEq⟩ := hd.2 (X.σ x (C u)) (C X.w) X.w (X.σ g₂ X.w)
  have hmc : mc X (C u) X.w x = (d : ℂ) / c₀ *
      ∫ g : Mt k r, mc X (X.σ x (C u)) (C X.w) (Matrix.of g) * star (mc X X.w (X.σ g₂ X.w) (Matrix.of g)) ∂D.μG := by
    rw [hEq]
    simp only [mc, ← hc₀def]
    field_simp
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ GV k r := by
    rw [ae_iff]; exact measure_mono_null (fun g hg => hg) D.haarG.conc
  have hpt : ∀ᵐ g ∂D.μG,
      ENNReal.ofReal ‖mc X (X.σ x (C u)) (C X.w) (Matrix.of g) * star (mc X X.w (X.σ g₂ X.w) (Matrix.of g))‖ ≤
        ENNReal.ofReal (K₁ * K₂ * (gN x * c⁻¹) ^ (-(X.a - b))) * ENNReal.ofReal (gN (Matrix.of g) ^ (-b)) := by
    filter_upwards [hae] with g hg
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    set G : Mat k r := Matrix.of g
    have hGx : G * x ∈ GV k r := hG.mul_mem _ hg _ hx
    have hA := hLow k r _ hGx
    have hB := hLow k r _ hg
    have e1 : mc X (X.σ x (C u)) (C X.w) G = ⟪C X.w, X.σ (G * x) (C u)⟫_ℂ := by
      unfold mc; rw [X.rep.1.2 G hg x hx]; rfl
    have hXle : gN x ≤ c * (gN G * gN (G * x)) :=
      (gN_le_mul hg x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (mul_nonneg (gN_nonneg _) (gN_nonneg _)))
    have key := real_key hA hB (by linarith) hc0 hb0 hab hXle
    rw [e1, norm_mul, norm_star]
    calc ‖⟪C X.w, X.σ (G * x) (C u)⟫_ℂ‖ * ‖mc X X.w (X.σ g₂ X.w) G‖
        ≤ (K₁ * gN (G * x) ^ (-X.a)) * (K₂ * gN G ^ (-X.a)) :=
          mul_le_mul (f1 _ hGx) (f2 _ hg) (norm_nonneg _) (mul_nonneg hK₁0 (Real.rpow_nonneg (by linarith) _))
      _ = K₁ * K₂ * (gN (G * x) ^ (-X.a) * gN G ^ (-X.a)) := by ring
      _ ≤ K₁ * K₂ * ((gN x * c⁻¹) ^ (-(X.a - b)) * gN G ^ (-b)) :=
          mul_le_mul_of_nonneg_left key (mul_nonneg hK₁0 hK₂0)
      _ = K₁ * K₂ * (gN x * c⁻¹) ^ (-(X.a - b)) * gN G ^ (-b) := by ring
  have hnorm : ‖∫ g : Mt k r, mc X (X.σ x (C u)) (C X.w) (Matrix.of g) *
      star (mc X X.w (X.σ g₂ X.w) (Matrix.of g)) ∂D.μG‖ ≤
      (ENNReal.ofReal (K₁ * K₂ * (gN x * c⁻¹) ^ (-(X.a - b))) * I).toReal :=
    (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIfin.ne)
      ((lintegral_mono_ae hpt).trans_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)))
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hnorm
  have hc₀n : 0 < ‖c₀‖ := norm_pos_iff.2 hc₀
  calc ‖mc X (C u) X.w x‖
      = d / ‖c₀‖ * ‖∫ g : Mt k r, mc X (X.σ x (C u)) (C X.w) (Matrix.of g) *
          star (mc X X.w (X.σ g₂ X.w) (Matrix.of g)) ∂D.μG‖ := by
        rw [hmc, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hd.1.le]
    _ ≤ d / ‖c₀‖ * (K₁ * K₂ * (gN x * c⁻¹) ^ (-(X.a - b)) * I.toReal) :=
        mul_le_mul_of_nonneg_left hnorm (div_nonneg hd.1.le hc₀n.le)
    _ = d / ‖c₀‖ * (K₁ * K₂ * c⁻¹ ^ (-(X.a - b)) * I.toReal) * gN x ^ (-(X.a - b)) := by
        rw [Real.mul_rpow (gN_nonneg x) (inv_nonneg.2 hc0.le)]; ring

end ReciprocityTheory.ChartRestriction.DS.Mult1
