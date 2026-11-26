module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.ExplicitFormulaFromGluing
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeight

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronLOf
namespace PI.EF.PK

open Complex MeasureTheory intervalIntegral Real ArithmeticFunction LSeries

lemma LSeries_twist_eq_neg_logDeriv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)) s =
      -logDeriv (DirichletCharacter.LFunction χ) s := by
  have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have e : (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)) =
      ((fun n : ℕ => χ (n : ZMod N)) * fun n : ℕ => ((Λ n : ℝ) : ℂ)) := by
    funext n
    simp only [Pi.mul_apply]
    exact mul_comm _ _
  have hev : DirichletCharacter.LFunction χ =ᶠ[nhds s] LSeries (fun n : ℕ => χ (n : ZMod N)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact DirichletCharacter.LFunction_eq_LSeries χ hz
  rw [e, h, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds, neg_div]

theorem perronL_of {C : ℝ} (hC : 0 ≤ C) (h : PerronTrunc C) : PerronL C := by
  unfold PerronL psiRaw vertInt Err
  intro N _ χ u T T' hT hTu hTT' hT'
  have hu : 2 ≤ u := le_trans hT hTu
  have hc : 1 < cLine u := by
    unfold cLine
    have hlog := Real.log_pos (show (1:ℝ) < u by linarith)
    first
      | (have := one_div_pos.mpr hlog; linarith)
      | (norm_num; positivity)
      | done
  have hΛ : ∀ n : ℕ, ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod N)‖ ≤ Λ n := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (DirichletCharacter.norm_le_one χ _)
  have key := h (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)) hΛ u T' hu (by linarith)
  have hint : ∀ t : ℝ, LSeries (fun n : ℕ => ((Λ n : ℝ) : ℂ) * χ (n : ZMod N)) (↑(cLine u) + ↑t * I) =
      -logDeriv (DirichletCharacter.LFunction χ) (↑(cLine u) + ↑t * I) := by
    intro t
    apply LSeries_twist_eq_neg_logDeriv
    simpa using hc
  simp only [hint] at key
  refine key.trans ?_
  have hN : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hl0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have h1 : u ≤ N * u := le_mul_of_one_le_left hu0.le hN
  have h2 : N * u ≤ N * u * T := le_mul_of_one_le_right (by positivity) (by linarith)
  have hl1 : Real.log u ≤ Real.log (N * u * T) := Real.log_le_log hu0 (h1.trans h2)
  have hl2 : Real.log u ≤ Real.log (N * u) := Real.log_le_log hu0 h1
  have hsq : Real.log u ^ 2 ≤ Real.log (N * u * T) ^ 2 := by nlinarith
  have hA : u * Real.log u ^ 2 / T' ≤ u * Real.log (N * u * T) ^ 2 / T := by
    calc u * Real.log u ^ 2 / T' ≤ u * Real.log u ^ 2 / T :=
          div_le_div_of_nonneg_left (by positivity) hT0 hTT'
      _ ≤ u * Real.log (N * u * T) ^ 2 / T :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hu0.le) hT0.le
  exact mul_le_mul_of_nonneg_left (add_le_add hA hl2) hC

end PI.EF.PK
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.ShiftBoundOf
noncomputable section

namespace PI.EF

open Complex DirichletCharacter

theorem shiftBound_of {κ Cs Cr : ℝ} (hκ : 0 < κ) (hCs : 0 ≤ Cs) (hCr : 0 ≤ Cr) (hRP : RegularPart)
    (hCI : ContourIdentity) (hS : SidesBound κ Cs) (hR : RegAtZero Cr) :
    ShiftBound κ (Cs + Cr + 3) := by
  intro N _ χ hχ u T T' hT hTu hTT' hT'T hg
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hu2 : (2 : ℝ) ≤ u := hT.trans hTu
  have hT'2 : (2 : ℝ) ≤ T' := hT.trans hTT'
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogNT : 0 < Real.log (N * T') := Real.log_pos (by nlinarith)
  have hNO : NoOrdinate χ T' := by
    intro ρ h1 h2 h3 heq
    have h4 := hg ρ h1 h2 h3
    rw [heq, sub_self, abs_zero] at h4
    have h5 : 0 < 1 / (κ * Real.log (N * T')) := by positivity
    linarith
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
  have hx1 : 1 < cLine u := by
    unfold cLine
    have := one_div_pos.mpr hlogu
    linarith
  obtain ⟨H, hH⟩ := hRP N χ hχ (cLine u) T' hx1 (by linarith) hNO
  have hCIe := hCI N χ hχ u T' H hu2 hT'2 hNO hH
  have hSe := hS N χ hχ u T T' hT hTu hTT' hT'T hg
  have hRe := hR N χ hχ (cLine u) T' H hx1 hT'2 hH
  set R := rectInt (fun s => logDeriv (DirichletCharacter.LFunction χ) s * ((u : ℂ) ^ s / s))
    (-1 / 2) (cLine u) (-T') T' with hRdef
  set Z := ∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ with hZ
  set c : ℂ := 2 * Real.pi * I with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hcn : ‖c‖ = 2 * Real.pi := by
    rw [hc, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  have hA : vertInt χ u T' - del1 χ * u + zsum χ T' u =
      (R + c * vertInt χ u T') / c + (Z - H 0) - eps0 χ * (Real.log u : ℂ) - del1 χ := by
    rw [hCIe]
    field_simp
    ring
  rw [hA]
  have hE1 : ‖eps0 χ‖ ≤ 1 := by
    unfold eps0
    split_ifs <;> simp
  have hD1 : ‖del1 χ‖ ≤ 1 := by
    unfold del1
    split_ifs <;> simp
  have hS1 : 0 ≤ S1 χ := by
    unfold S1
    exact finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity
  have hNu : Real.log u ≤ Real.log (N * u) := Real.log_le_log (by positivity) (by nlinarith)
  have h2N : Real.log (2 * N) ≤ Real.log (N * u) := Real.log_le_log (by positivity) (by nlinarith)
  have hL : 1 ≤ u * Real.log (N * u * T) ^ 2 / T := by
    have h4 : (4 : ℝ) ≤ N * u * T := by
      calc (4 : ℝ) = 1 * 2 * 2 := by norm_num
        _ ≤ N * u * T := mul_le_mul (mul_le_mul hN1 hu2 (by norm_num) (by linarith)) hT (by norm_num)
          (by positivity)
    have hl4 : 1 ≤ Real.log (N * u * T) := by
      have h5 : Real.log 4 ≤ Real.log (N * u * T) := Real.log_le_log (by norm_num) h4
      have h6 : 1 < Real.log 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        linarith [Real.log_two_gt_d9]
      linarith
    have hsq : 1 ≤ Real.log (N * u * T) ^ 2 := by nlinarith
    rw [le_div_iff₀ hT0]
    nlinarith [mul_le_mul hTu hsq (by norm_num) (by linarith)]
  have hlogNu : 0 ≤ Real.log (N * u) := by linarith
  have hErr1 : 1 ≤ Err N u T := by unfold Err; linarith
  have hErr2 : Real.log u ≤ Err N u T := by unfold Err; linarith
  have hErr3 : Real.log (2 * N) ≤ Err N u T := by unfold Err; linarith
  have hmain : ‖(R + c * vertInt χ u T') / c‖ ≤ Cs * Err N u T := by
    rw [norm_div, hcn, div_le_iff₀ (by positivity)]
    calc ‖R + c * vertInt χ u T'‖ ≤ Cs * Err N u T := hSe
      _ ≤ Cs * Err N u T * (2 * Real.pi) :=
        le_mul_of_one_le_right (by positivity) (by linarith [Real.pi_gt_three])
  have heps : ‖eps0 χ * (Real.log u : ℂ)‖ ≤ Real.log u := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogu]
    exact mul_le_of_le_one_left hlogu.le hE1
  calc ‖(R + c * vertInt χ u T') / c + (Z - H 0) - eps0 χ * (Real.log u : ℂ) - del1 χ‖
      ≤ ‖(R + c * vertInt χ u T') / c‖ + ‖Z - H 0‖ + ‖eps0 χ * (Real.log u : ℂ)‖ + ‖del1 χ‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ Cs * Err N u T + (Cr * Real.log (2 * N) + S1 χ) + Real.log u + 1 := by
        gcongr
    _ ≤ (Cs + Cr + 3) * (Err N u T + S1 χ) := by
        nlinarith [mul_nonneg hCs hS1, mul_nonneg hCr hS1, mul_le_mul_of_nonneg_left hErr3 hCr]

end PI.EF
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Contour
noncomputable section

namespace PI.EF

open Complex Filter Topology Set DirichletCharacter

lemma mem_rect_iff {x₀ x₁ y₀ y₁ : ℝ} {s : ℂ} :
    s ∈ rect x₀ x₁ y₀ y₁ ↔ (x₀ ≤ s.re ∧ s.re ≤ x₁) ∧ (y₀ ≤ s.im ∧ s.im ≤ y₁) := by
  rw [rect, Complex.mem_reProdIm]
  simp only [Set.mem_Icc]

lemma rectInt_congr_sides {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (h : ∀ s ∈ rect x₀ x₁ y₀ y₁, (s.re = x₀ ∨ s.re = x₁ ∨ s.im = y₀ ∨ s.im = y₁) → f s = g s) :
    rectInt f x₀ x₁ y₀ y₁ = rectInt g x₀ x₁ y₀ y₁ := by
  have hre : ∀ a b : ℝ, ((a : ℂ) + b * I).re = a := fun a b => by simp
  have him : ∀ a b : ℝ, ((a : ℂ) + b * I).im = b := fun a b => by simp
  have hxI := Set.uIcc_of_le hx
  have hyI := Set.uIcc_of_le hy
  have e1 : ∀ y : ℝ, y₀ ≤ y → y ≤ y₁ → (y = y₀ ∨ y = y₁) →
      (∫ x : ℝ in x₀..x₁, f (x + y * I)) = ∫ x : ℝ in x₀..x₁, g (x + y * I) := by
    intro y hy0 hy1 hyy
    refine intervalIntegral.integral_congr fun x hxm => ?_
    rw [hxI] at hxm
    apply h
    · rw [mem_rect_iff, hre, him]
      exact ⟨hxm, hy0, hy1⟩
    · rw [hre, him]
      rcases hyy with e | e
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr e))
  have e2 : ∀ x : ℝ, x₀ ≤ x → x ≤ x₁ → (x = x₀ ∨ x = x₁) →
      (∫ y : ℝ in y₀..y₁, f (x + y * I)) = ∫ y : ℝ in y₀..y₁, g (x + y * I) := by
    intro x hx0 hx1 hxx
    refine intervalIntegral.integral_congr fun y hym => ?_
    rw [hyI] at hym
    apply h
    · rw [mem_rect_iff, hre, him]
      exact ⟨⟨hx0, hx1⟩, hym⟩
    · rw [hre, him]
      rcases hxx with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
  unfold rectInt
  rw [e1 y₀ le_rfl hy (Or.inl rfl), e1 y₁ hy le_rfl (Or.inr rfl), e2 x₁ hx le_rfl (Or.inr rfl),
    e2 x₀ le_rfl hx (Or.inl rfl)]

theorem glueContour : GlueContour := by
  intro hR hZ hF N _ χ hχ u T' H hu hT hno hreg
  have hlog : 0 < Real.log u := Real.log_pos (by linarith)
  have hc : 1 < cLine u := by
    unfold cLine
    have := one_div_pos.2 hlog
    linarith
  have hfin := hF N χ hχ T'
  set S := hfin.toFinset with hS
  have hmemS : ∀ ρ, ρ ∈ S ↔ ρ ∈ ZerosBelow χ T' := fun ρ => hfin.mem_toFinset
  have h1S : (1 : ℂ) ∉ S := by
    rw [hmemS]
    intro h
    have := h.2.1
    simp at this
  set Z := insert (1 : ℂ) S with hZdef
  set wt : ℂ → ℂ := fun ρ => if ρ = 1 then -del1 χ else (mult χ ρ : ℂ) with hwt
  have hfs : ∀ g : ℂ → ℂ, (∑ᶠ ρ ∈ ZerosBelow χ T', g ρ) = ∑ ρ ∈ S, g ρ := fun g =>
    finsum_mem_eq_finite_toFinset_sum g hfin

  have hsumZ : ∀ F : ℂ → ℂ → ℂ, ∑ ρ ∈ Z, F (wt ρ) ρ = F (-del1 χ) 1 + ∑ ρ ∈ S, F (mult χ ρ) ρ := by
    intro F
    rw [hZdef, Finset.sum_insert h1S]
    congr 1
    · simp [hwt]
    · refine Finset.sum_congr rfl fun ρ hρ => ?_
      have : ρ ≠ 1 := fun e => h1S (e ▸ hρ)
      simp [hwt, this]

  have hbd : rectInt (fun s => logDeriv (DirichletCharacter.LFunction χ) s * ((u : ℂ) ^ s / s))
        (-1 / 2) (cLine u) (-T') T' =
      rectInt (fun s => (H s + (∑ ρ ∈ Z, wt ρ / (s - ρ)) + eps0 χ / s) * ((u : ℂ) ^ s / s))
        (-1 / 2) (cLine u) (-T') T' := by
    apply rectInt_congr_sides (by linarith) (by linarith)
    intro s hs hside
    have hs' := mem_rect_iff.1 hs
    have hs1 : s ≠ 1 := by
      intro e
      have r1 : s.re = 1 := by rw [e]; simp
      have i1 : s.im = 0 := by rw [e]; simp
      rcases hside with e' | e' | e' | e' <;> linarith
    have hL : DirichletCharacter.LFunction χ s ≠ 0 := by
      intro h0
      rcases hZ N χ hχ s (by linarith [hs'.1.1]) hs1 h0 with h | ⟨h, -⟩ | ⟨h, -⟩
      · rcases hside with e | e | e | e
        · linarith [h.1]
        · linarith [h.2]
        · exact hno s h.1 h.2 h0 (by rw [e, abs_neg, abs_of_pos (by linarith)])
        · exact hno s h.1 h.2 h0 (by rw [e, abs_of_pos (by linarith)])
      · have r1 : s.re = 0 := by rw [h]; simp
        have i1 : s.im = 0 := by rw [h]; simp
        rcases hside with e' | e' | e' | e' <;> linarith
      · have r1 : s.re = -1 := by rw [h]; simp
        have i1 : s.im = 0 := by rw [h]; simp
        rcases hside with e' | e' | e' | e' <;> linarith
    rw [hreg.2 s hs hL hs1, hfs]
    have := hsumZ (fun w ρ => w / (s - ρ))
    rw [this]
    ring
  rw [hbd, hR (-1 / 2) (cLine u) (-T') T' H Z wt (eps0 χ) u (by linarith) (by norm_num) (by linarith)
    (by linarith) (by linarith) hreg.1 ?_]
  · have := hsumZ (fun w ρ => w * (((u : ℂ) ^ ρ - 1) / ρ))
    rw [this, zsum, hfs, hfs, Complex.cpow_one]
    have e : ∑ ρ ∈ S, (mult χ ρ : ℂ) * (((u : ℂ) ^ ρ - 1) / ρ) =
        ∑ ρ ∈ S, (mult χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) - ∑ ρ ∈ S, (mult χ ρ : ℂ) / ρ := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun ρ _ => by ring
    rw [e]
    ring
  · intro ρ hρ
    rw [hZdef, Finset.mem_insert] at hρ
    rcases hρ with e | hρ
    · subst e
      simp only [Complex.one_re, Complex.one_im]
      exact ⟨one_ne_zero, by norm_num, hc, by linarith, by linarith⟩
    · obtain ⟨h0, h1, him, -⟩ := (hmemS ρ).1 hρ
      rw [abs_lt] at him
      refine ⟨fun e => by rw [e] at h0; simp at h0, by linarith, by linarith, him.1, him.2⟩

end PI.EF
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.RegZero
noncomputable section

namespace PI.EF

open Complex DirichletCharacter Filter Topology

theorem regAtZero_of {Cw Cl : ℝ} (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) :
    RegAtZero (Cw + Cl) := by
  intro N _ χ hχ x₁ T' H hx₁ hT' hH
  classical
  obtain ⟨hZ0, hZ0sum⟩ := hW N χ hχ 0
  have hlog : Real.log (N * (|(0:ℝ)| + 2)) = Real.log (2 * N) := by
    rw [abs_zero, zero_add, mul_comm]
  have hne0 : ∀ ρ ∈ ZerosNear χ 0, ρ ≠ 0 := by
    rintro ρ hρ rfl
    have := hρ.1
    simp at this
  have hB : (ZerosBelow χ T').Finite := by
    refine ((Finset.Icc ⌊-T'⌋ ⌊T'⌋).finite_toSet.biUnion
      (fun k _ => (hW N χ hχ (k : ℝ)).1)).subset ?_
    intro ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hρ
    rw [abs_lt] at h3
    refine Set.mem_iUnion₂.mpr ⟨⌊ρ.im⌋, ?_, h1, h2, ?_, h4⟩
    · rw [Finset.mem_coe, Finset.mem_Icc]
      exact ⟨Int.floor_mono h3.1.le, Int.floor_mono h3.2.le⟩
    · rw [abs_le]
      constructor <;> linarith [Int.floor_le ρ.im, Int.lt_floor_add_one ρ.im]
  have hneB : ∀ ρ ∈ ZerosBelow χ T', ρ ≠ 0 := by
    rintro ρ hρ rfl
    have := hρ.1
    simp at this
  have hofR : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using h
  have h0rect : (0 : ℂ) ∈ rect (-1 / 2) x₁ (-T') T' := by
    show (0 : ℂ) ∈ Set.Icc (-1 / 2 : ℝ) x₁ ×ℂ Set.Icc (-T') T'
    rw [Complex.mem_reProdIm]
    simp only [Complex.zero_re, Complex.zero_im, Set.mem_Icc]
    constructor <;> constructor <;> linarith
  have hrect : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → (ε : ℂ) ∈ rect (-1 / 2) x₁ (-T') T' := by
    intro ε h1 h2
    show (ε : ℂ) ∈ Set.Icc (-1 / 2 : ℝ) x₁ ×ℂ Set.Icc (-T') T'
    rw [Complex.mem_reProdIm]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Set.mem_Icc]
    constructor <;> constructor <;> linarith
  have hHt : Tendsto (fun ε : ℝ => ‖H ε - H 0‖) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousWithinAt H (rect (-1 / 2) x₁ (-T') T') 0 :=
      hH.1.continuousOn.continuousWithinAt h0rect
    have hr : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝[rect (-1 / 2) x₁ (-T') T'] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hofR, ?_⟩
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 / 2 by norm_num)] with ε hε
      exact hrect ε hε.1 hε.2
    have := ((hc.tendsto.comp hr).sub_const (H 0)).norm
    simpa using this
  have hevZ : ∀ᶠ ε : ℝ in 𝓝[>] 0, (ε : ℂ) ∉ ZerosNear χ 0 := by
    have hc : (ZerosNear χ 0)ᶜ ∈ 𝓝 (0 : ℂ) :=
      hZ0.isClosed.isOpen_compl.mem_nhds (fun h => hne0 0 h rfl)
    exact hofR.eventually_mem hc
  have hpt : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ‖(∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) - H 0‖ ≤
        ‖H ε - H 0‖ + ‖(∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) +
          ∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ((ε : ℂ) - ρ)‖ +
          Cl * Real.log (2 * N) + ‖∑ᶠ ρ ∈ ZerosNear χ 0, (mult χ ρ : ℂ) / ((ε : ℂ) - ρ)‖ := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 / 2 by norm_num), hevZ] with ε hε hεZ
    obtain ⟨hε0, hε1⟩ := hε
    have hLε : DirichletCharacter.LFunction χ ε ≠ 0 := by
      intro h
      apply hεZ
      refine ⟨?_, ?_, ?_, h⟩
      · simpa using hε0
      · simp only [Complex.ofReal_re]; linarith
      · simp
    have hε1' : (ε : ℂ) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.ofReal_re, Complex.one_re] at this
      linarith
    have hreg := hH.2 ε (hrect ε hε0 hε1) hLε hε1'
    have hloc := hL N χ hχ ε (by simp only [Complex.ofReal_re]; linarith)
      (by simp only [Complex.ofReal_re]; linarith) hLε hε1'
    simp only [Complex.ofReal_im] at hloc
    rw [hlog] at hloc
    have key : (∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) - H 0 =
        (H ε - H 0) + ((∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) +
          ∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ((ε : ℂ) - ρ)) -
        (logDeriv (DirichletCharacter.LFunction χ) ε -
          (∑ᶠ ρ ∈ ZerosNear χ 0, (mult χ ρ : ℂ) / ((ε : ℂ) - ρ)) - eps0 χ / ε +
            del1 χ / (ε - 1)) -
        ∑ᶠ ρ ∈ ZerosNear χ 0, (mult χ ρ : ℂ) / ((ε : ℂ) - ρ) := by
      rw [hreg]; ring
    rw [key]
    have h4 : ∀ a b c d : ℂ, ‖a + b - c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := fun a b c d =>
      calc ‖a + b - c - d‖ ≤ ‖a + b - c‖ + ‖d‖ := norm_sub_le _ _
        _ ≤ ‖a + b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_add_le _ _
    refine (h4 _ _ _ _).trans ?_
    linarith [hloc]
  have hPt : Tendsto (fun ε : ℝ => ‖(∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) +
      ∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ((ε : ℂ) - ρ)‖) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => ∑ ρ ∈ hB.toFinset,
        ((mult χ ρ : ℂ) / ρ + (mult χ ρ : ℂ) / ((ε : ℂ) - ρ))) (𝓝[>] 0)
        (𝓝 (∑ ρ ∈ hB.toFinset, ((mult χ ρ : ℂ) / ρ + (mult χ ρ : ℂ) / (0 - ρ)))) :=
      tendsto_finsetSum _ fun ρ hρ => tendsto_const_nhds.add
        (tendsto_const_nhds.div (hofR.sub_const ρ) (by
          rw [zero_sub, neg_ne_zero]; exact hneB ρ (by simpa using hρ)))
    have h0 : (∑ ρ ∈ hB.toFinset, ((mult χ ρ : ℂ) / ρ + (mult χ ρ : ℂ) / (0 - ρ))) = 0 :=
      Finset.sum_eq_zero fun ρ _ => by rw [zero_sub, div_neg, add_neg_cancel]
    rw [h0] at h
    have := h.norm
    rw [norm_zero] at this
    refine this.congr fun ε => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ hB, finsum_mem_eq_finite_toFinset_sum _ hB,
      Finset.sum_add_distrib]
  have hQt : Tendsto (fun ε : ℝ => ‖∑ᶠ ρ ∈ ZerosNear χ 0, (mult χ ρ : ℂ) / ((ε : ℂ) - ρ)‖)
      (𝓝[>] 0) (𝓝 ‖∑ ρ ∈ hZ0.toFinset, (mult χ ρ : ℂ) / (0 - ρ)‖) := by
    have h : Tendsto (fun ε : ℝ => ∑ ρ ∈ hZ0.toFinset, (mult χ ρ : ℂ) / ((ε : ℂ) - ρ))
        (𝓝[>] 0) (𝓝 (∑ ρ ∈ hZ0.toFinset, (mult χ ρ : ℂ) / (0 - ρ))) :=
      tendsto_finsetSum _ fun ρ hρ => tendsto_const_nhds.div (hofR.sub_const ρ) (by
        rw [zero_sub, neg_ne_zero]; exact hne0 ρ (by simpa using hρ))
    refine h.norm.congr fun ε => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ hZ0]
  have hlim := ((hHt.add hPt).add
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => Cl * Real.log (2 * N)) (𝓝[>] 0) _)).add hQt
  have hmain := ge_of_tendsto hlim hpt
  have hB1 : ZerosBelow χ 1 ⊆ ZerosNear χ 0 := by
    rintro ρ ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, by rw [sub_zero]; exact h3.le, h4⟩
  have hB1f : (ZerosBelow χ 1).Finite := hZ0.subset hB1
  have hQ0 : ‖∑ ρ ∈ hZ0.toFinset, (mult χ ρ : ℂ) / (0 - ρ)‖ ≤
      S1 χ + Cw * Real.log (2 * N) := by
    refine (norm_sum_le _ _).trans ?_
    have hn : ∀ ρ, ‖(mult χ ρ : ℂ) / (0 - ρ)‖ = (mult χ ρ : ℝ) / ‖ρ‖ := fun ρ => by
      rw [norm_div, zero_sub, norm_neg, Complex.norm_natCast]
    simp only [hn]
    rw [← Finset.sum_filter_add_sum_filter_not hZ0.toFinset (fun ρ => ρ ∈ ZerosBelow χ 1)]
    have hS1 : S1 χ = ∑ ρ ∈ hZ0.toFinset.filter (fun ρ => ρ ∈ ZerosBelow χ 1),
        (mult χ ρ : ℝ) / ‖ρ‖ := by
      unfold S1
      rw [finsum_mem_eq_finite_toFinset_sum _ hB1f]
      congr 1
      ext ρ
      simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
      exact ⟨fun h => ⟨hB1 h, h⟩, fun h => h.2⟩
    have hrest : ∑ ρ ∈ hZ0.toFinset.filter (fun ρ => ρ ∉ ZerosBelow χ 1),
        (mult χ ρ : ℝ) / ‖ρ‖ ≤ Cw * Real.log (2 * N) := by
      calc _ ≤ ∑ ρ ∈ hZ0.toFinset.filter (fun ρ => ρ ∉ ZerosBelow χ 1), (mult χ ρ : ℝ) := by
            refine Finset.sum_le_sum fun ρ hρ => ?_
            rw [Finset.mem_filter] at hρ
            obtain ⟨hρ1, hρ2⟩ := hρ
            have hρZ : ρ ∈ ZerosNear χ 0 := by simpa using hρ1
            obtain ⟨h1, h2, h3, h4⟩ := hρZ
            have him : 1 ≤ |ρ.im| := by
              by_contra hlt
              push_neg at hlt
              exact hρ2 ⟨h1, h2, hlt, h4⟩
            exact div_le_self (Nat.cast_nonneg _) (him.trans (Complex.abs_im_le_norm ρ))
        _ ≤ ∑ ρ ∈ hZ0.toFinset, (mult χ ρ : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => Nat.cast_nonneg _)
        _ ≤ Cw * Real.log (2 * N) := by
            rw [← hlog, ← finsum_mem_eq_finite_toFinset_sum _ hZ0]
            exact hZ0sum
    linarith
  linarith

end PI.EF
end
end
