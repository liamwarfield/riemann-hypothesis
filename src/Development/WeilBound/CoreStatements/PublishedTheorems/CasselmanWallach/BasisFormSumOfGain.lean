module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.BasisFormSumOfGain
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace EigenGainPolynomial

theorem re_inner_self {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (w : V) :
    (inner ℂ w w).re = ‖w‖ ^ 2 := by
  have := inner_self_eq_norm_sq (𝕜 := ℂ) w
  simpa using this

theorem phi_lb (s : ℕ) (c ν x : ℝ) (hν : 0 ≤ ν) (hx : 0 ≤ x)
    (hA : ∀ y : ℝ, -1 < y → 1 - s * y + (s : ℝ) ^ 2 / 4 * y ^ 2 - c * y ^ 4 ≤ ((1 + y) ^ s)⁻¹) :
    ((1 + ν) ^ s)⁻¹ + (-(((1 + ν) ^ s)⁻¹ * s / (1 + ν))) * (x - ν)
      + (((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2)) * ((x - ν) * (x - ν))
      + (-(((1 + ν) ^ s)⁻¹ * c / (1 + ν) ^ 4)) * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))
      ≤ ((1 + x) ^ s)⁻¹ := by
  have h1 : (0 : ℝ) < 1 + ν := by linarith
  have hy1 : -1 < (x - ν) / (1 + ν) := by
    rw [lt_div_iff₀ h1]; linarith
  have hA' := hA _ hy1
  have hx1 : 1 + x = (1 + ν) * (1 + (x - ν) / (1 + ν)) := by field_simp; ring
  have ha : 0 ≤ ((1 + ν) ^ s)⁻¹ := by positivity
  calc _ = ((1 + ν) ^ s)⁻¹ * (1 - s * ((x - ν) / (1 + ν)) + (s : ℝ) ^ 2 / 4 * ((x - ν) / (1 + ν)) ^ 2
          - c * ((x - ν) / (1 + ν)) ^ 4) := by
          field_simp; ring
    _ ≤ ((1 + ν) ^ s)⁻¹ * ((1 + (x - ν) / (1 + ν)) ^ s)⁻¹ := mul_le_mul_of_nonneg_left hA' ha
    _ = ((1 + x) ^ s)⁻¹ := by rw [hx1, mul_pow, mul_inv]

theorem fc_poly {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}
    {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
    (hsym : ∀ φ x y, inner ℂ (fc b μ φ x) y = inner ℂ x (fc b μ φ y))
    (hadd : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x + ψ x) = fc b μ φ + fc b μ ψ)
    (hmul : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x * ψ x) = fc b μ φ * fc b μ ψ)
    (hconst : ∀ c : ℝ, fc b μ (fun _ => c) = (c : ℂ) • 1) (ν k0 k1 k2 k4 : ℝ) (w : V) :
    (inner ℂ w (fc b μ (fun x => k0 + k1 * (x - ν) + k2 * ((x - ν) * (x - ν))
        + k4 * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))) w)).re =
      k0 * ‖w‖ ^ 2 + k1 * (inner ℂ w (fc b μ (fun x => x - ν) w)).re
        + k2 * ‖fc b μ (fun x => x - ν) w‖ ^ 2
        + k4 * ‖fc b μ (fun x => x - ν) (fc b μ (fun x => x - ν) w)‖ ^ 2 := by
  have e1 : ∀ (k : ℝ) (f : ℝ → ℝ), fc b μ (fun x => k * f x) = (k : ℂ) • fc b μ f := by
    intro k f
    calc fc b μ (fun x => k * f x) = fc b μ (fun _ => k) * fc b μ f := hmul (fun _ => k) f
      _ = (k : ℂ) • fc b μ f := by rw [hconst, smul_mul_assoc, one_mul]
  have hT2 : fc b μ (fun x => (x - ν) * (x - ν)) = fc b μ (fun x => x - ν) * fc b μ (fun x => x - ν) :=
    hmul (fun x => x - ν) (fun x => x - ν)
  have hT4 : fc b μ (fun x => (x - ν) * (x - ν) * ((x - ν) * (x - ν))) =
      fc b μ (fun x => (x - ν) * (x - ν)) * fc b μ (fun x => (x - ν) * (x - ν)) :=
    hmul (fun x => (x - ν) * (x - ν)) (fun x => (x - ν) * (x - ν))
  have hF : fc b μ (fun x => k0 + k1 * (x - ν) + k2 * ((x - ν) * (x - ν))
        + k4 * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))) =
      (k0 : ℂ) • 1 + (k1 : ℂ) • fc b μ (fun x => x - ν) + (k2 : ℂ) • fc b μ (fun x => (x - ν) * (x - ν))
        + (k4 : ℂ) • fc b μ (fun x => (x - ν) * (x - ν) * ((x - ν) * (x - ν))) := by
    rw [hadd (fun x => k0 + k1 * (x - ν) + k2 * ((x - ν) * (x - ν)))
        (fun x => k4 * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))),
      hadd (fun x => k0 + k1 * (x - ν)) (fun x => k2 * ((x - ν) * (x - ν))),
      hadd (fun _ => k0) (fun x => k1 * (x - ν)), hconst,
      e1 k1 (fun x => x - ν), e1 k2 (fun x => (x - ν) * (x - ν)),
      e1 k4 (fun x => (x - ν) * (x - ν) * ((x - ν) * (x - ν)))]
  rw [hF, hT4, hT2]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply, Module.End.one_apply,
    inner_add_right, inner_smul_right, Complex.add_re, Complex.re_ofReal_mul]
  have r2 : ∀ u : V, inner ℂ u (fc b μ (fun x => x - ν) (fc b μ (fun x => x - ν) u)) =
      inner ℂ (fc b μ (fun x => x - ν) u) (fc b μ (fun x => x - ν) u) := fun u => (hsym _ _ _).symm
  have r4 := (hsym (fun x => x - ν) w _).symm.trans (r2 (fc b μ (fun x => x - ν) w))
  rw [r4, r2]
  simp only [re_inner_self]

theorem main {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E : Fin n → Fin n → Module.End ℂ V} {ι : Type} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
    (hsym : ∀ φ x y, inner ℂ (fc b μ φ x) y = inner ℂ x (fc b μ φ y))
    (hmono : ∀ φ ψ : ℝ → ℝ, (∀ x, 0 ≤ x → φ x ≤ ψ x) → ∀ w,
      (inner ℂ w (fc b μ φ w)).re ≤ (inner ℂ w (fc b μ ψ w)).re)
    (hadd : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x + ψ x) = fc b μ φ + fc b μ ψ)
    (hmul : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x * ψ x) = fc b μ φ * fc b μ ψ)
    (hconst : ∀ c : ℝ, fc b μ (fun _ => c) = (c : ℂ) • 1) (hid : fc b μ (fun x => x) = casimirK ε E)
    (κ c : ℝ) (s : ℕ) (c0 C cs ν : ℝ) (hc0 : 0 < c0) (hC : 0 ≤ C) (hcs0 : 0 ≤ cs)
    (hsC : c + 1 ≤ (s : ℝ) ^ 2 * c0 / 4 - s * C)
    (hν0 : 0 ≤ ν) (hνc : cs * C ≤ ν) (v : V) (hv : Eig ε E ν v)
    (hA : ∀ y : ℝ, -1 < y → 1 - s * y + (s : ℝ) ^ 2 / 4 * y ^ 2 - cs * y ^ 4 ≤ ((1 + y) ^ s)⁻¹)
    (hE : ∑ p ∈ nc ε, ‖E p.1 p.2 v‖ ^ 2 = (ν - κ) * ‖v‖ ^ 2)
    (h8 : c0 * (1 + ν) ^ 2 * ‖v‖ ^ 2 ≤ ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 v‖ ^ 2)
    (h9a : ‖∑ p ∈ nc ε, inner ℂ (E p.1 p.2 v) (Z ε E p.1 p.2 v)‖ ≤ C * (1 + ν) * ‖v‖ ^ 2)
    (h9b : ∑ p ∈ nc ε, ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
      ≤ C * (1 + ν) ^ 3 * ‖v‖ ^ 2) :
    ((1 + ν) ^ s)⁻¹ * (ν - κ + c) * ‖v‖ ^ 2 ≤ (beta ε E (fc b μ fun x => ((1 + x) ^ s)⁻¹) v v).re := by
  have h1 : (0 : ℝ) < 1 + ν := by linarith
  have ha : 0 < ((1 + ν) ^ s)⁻¹ := by positivity
  have hv' : casimirK ε E v = (ν : ℂ) • v := hv
  have hT : ∀ u, fc b μ (fun x => x - ν) u = casimirK ε E u - (ν : ℂ) • u := by
    intro u
    have hf : (fun x : ℝ => x - ν) = fun x => x + -ν := by funext x; ring
    rw [hf, hadd (fun x => x) (fun _ => -ν), hid, hconst]
    simp [sub_eq_add_neg]
  have hTE : ∀ p : Fin n × Fin n, fc b μ (fun x => x - ν) (E p.1 p.2 v) = Z ε E p.1 p.2 v := by
    intro p
    rw [hT, Z, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hv', map_smul]
  have hTZ : ∀ p : Fin n × Fin n, fc b μ (fun x => x - ν) (Z ε E p.1 p.2 v) =
      (casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v := by
    intro p
    rw [hT, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hv', map_smul]
  have hp : ∀ p ∈ nc ε,
      ((1 + ν) ^ s)⁻¹ * ‖E p.1 p.2 v‖ ^ 2
        + (-(((1 + ν) ^ s)⁻¹ * s / (1 + ν))) * (inner ℂ (E p.1 p.2 v) (Z ε E p.1 p.2 v)).re
        + (((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2)) * ‖Z ε E p.1 p.2 v‖ ^ 2
        + (-(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4))
          * ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
      ≤ (inner ℂ (E p.1 p.2 v) (fc b μ (fun x => ((1 + x) ^ s)⁻¹) (E p.1 p.2 v))).re := by
    intro p _
    have := hmono (fun x => ((1 + ν) ^ s)⁻¹ + (-(((1 + ν) ^ s)⁻¹ * s / (1 + ν))) * (x - ν)
      + (((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2)) * ((x - ν) * (x - ν))
      + (-(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4)) * ((x - ν) * (x - ν) * ((x - ν) * (x - ν))))
      (fun x => ((1 + x) ^ s)⁻¹) (fun x hx => phi_lb s cs ν x hν0 hx hA) (E p.1 p.2 v)
    rw [fc_poly hsym hadd hmul hconst, hTE, hTZ] at this
    exact this
  unfold beta
  rw [Complex.re_sum]
  refine le_trans ?_ (Finset.sum_le_sum hp)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Complex.re_sum, hE]
  have hN : 0 ≤ ‖v‖ ^ 2 := by positivity
  have hR := le_trans (Complex.re_le_norm _) h9a
  have hk1 : -(((1 + ν) ^ s)⁻¹ * s / (1 + ν)) ≤ 0 := by
    have : 0 ≤ ((1 + ν) ^ s)⁻¹ * s / (1 + ν) := by positivity
    linarith
  have hk2 : 0 ≤ ((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2) := by positivity
  have hk4 : -(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4) ≤ 0 := by
    have : 0 ≤ ((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4 := by positivity
    linarith
  have i2 := mul_le_mul_of_nonpos_left hR hk1
  have i3 := mul_le_mul_of_nonneg_left h8 hk2
  have i4 := mul_le_mul_of_nonpos_left h9b hk4
  have e2 : -(((1 + ν) ^ s)⁻¹ * s / (1 + ν)) * (C * (1 + ν) * ‖v‖ ^ 2)
      = -(((1 + ν) ^ s)⁻¹ * (s * C) * ‖v‖ ^ 2) := by
    field_simp
  have e3 : ((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2) * (c0 * (1 + ν) ^ 2 * ‖v‖ ^ 2)
      = ((1 + ν) ^ s)⁻¹ * ((s : ℝ) ^ 2 * c0 / 4) * ‖v‖ ^ 2 := by
    field_simp
  have e4 : -(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4) * (C * (1 + ν) ^ 3 * ‖v‖ ^ 2)
      = -(((1 + ν) ^ s)⁻¹ * (cs * C / (1 + ν)) * ‖v‖ ^ 2) := by
    field_simp
  rw [e2] at i2
  rw [e3] at i3
  rw [e4] at i4
  have b4 : cs * C / (1 + ν) ≤ 1 := (div_le_one h1).2 (by linarith)
  have hb4 := mul_le_mul_of_nonneg_left b4 (mul_nonneg ha.le hN)
  have hs := mul_le_mul_of_nonneg_left hsC (mul_nonneg ha.le hN)
  nlinarith

end EigenGainPolynomial

theorem eigen_gain_of_moments : A0 → A8 → A9 → A10 → FunctionalCalculusLaws → A12 := by
  intro h0 h8 h9 h10 h11 n ε V _ _ E hM ι b μ hB κ hκ c hc
  obtain ⟨-, -, -, hnorm⟩ := h0 n ε V E hM
  obtain ⟨c0, x1, hc0, h8'⟩ := h8 n ε V E hM
  obtain ⟨C, hC, h9'⟩ := h9 n ε V E hM
  obtain ⟨-, hsym, hmono, hadd, hmul, hconst, hid⟩ := h11 n ε V E hM ι b μ hB
  obtain ⟨cs, hcs, h10'⟩ := h10 (⌈4 * (C + c + 1) / c0⌉₊ + 1) (by omega)
  refine ⟨⌈4 * (C + c + 1) / c0⌉₊ + 1, max 0 (max x1 (cs * C)), by omega, le_max_left _ _, ?_⟩
  intro ν v hν hv
  have hν0 : 0 ≤ ν := le_trans (le_max_left _ _) hν
  have hνx : x1 ≤ ν := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hν
  have hνc : cs * C ≤ ν := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hν
  have hsC : c + 1 ≤ ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) ^ 2 * c0 / 4
      - ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) * C := by
    have hce := Nat.le_ceil (4 * (C + c + 1) / c0)
    have hsc : 4 * (C + c + 1) ≤ ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) * c0 := by
      have := (div_le_iff₀ hc0).1 hce
      push_cast
      nlinarith
    have hs1 : (1 : ℝ) ≤ ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈4 * (C + c + 1) / c0⌉₊]
    nlinarith
  have hv' : casimirK ε E v = (ν : ℂ) • v := hv
  have hE : ∑ p ∈ nc ε, ‖E p.1 p.2 v‖ ^ 2 = (ν - κ) * ‖v‖ ^ 2 := by
    rw [(hnorm κ hκ v).2.1, hv', inner_smul_right, Complex.re_ofReal_mul, EigenGainPolynomial.re_inner_self]
    ring
  obtain ⟨h9a, h9b⟩ := h9' ν v hν0 hv
  exact EigenGainPolynomial.main hsym hmono hadd hmul hconst hid κ c _ c0 C cs ν hc0 hC hcs hsC hν0 hνc v hv h10'
    hE (h8' ν v hνx hv) h9a h9b

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EnvelopingAlgebraGrowthBound
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace IdentityFiltrationBound

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def W (n k : ℕ) : Finset (List (Fin n × Fin n)) := (List.finite_length_le (Fin n × Fin n) k).toFinset

lemma mem_W {k : ℕ} {l : List (Fin n × Fin n)} : l ∈ W n k ↔ l.length ≤ k := by
  simp [W]

def wd (E : Fin n → Fin n → Module.End ℂ V) (l : List (Fin n × Fin n)) : Module.End ℂ V :=
  (l.map fun p => E p.1 p.2).prod

def N (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) (v : V) : ℝ := ∑ l ∈ W n k, ‖wd E l v‖

lemma N_nonneg (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) (v : V) : 0 ≤ N E k v :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma le_N (E : Fin n → Fin n → Module.End ℂ V) {k : ℕ} {l : List (Fin n × Fin n)} (hl : l.length ≤ k)
    (v : V) : ‖wd E l v‖ ≤ N E k v :=
  Finset.single_le_sum (f := fun l => ‖wd E l v‖) (fun _ _ => norm_nonneg _) (mem_W.2 hl)

lemma U_bound (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) (u : Module.End ℂ V) (hu : u ∈ U E k) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ v, ‖u v‖ ≤ c * N E k v := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact ⟨1, zero_le_one, fun v => by simpa [wd] using le_N E hl v⟩
  | zero => exact ⟨0, le_rfl, fun v => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, h⟩ := hx
    obtain ⟨d, hd, h'⟩ := hy
    refine ⟨c + d, add_nonneg hc hd, fun v => ?_⟩
    calc ‖(x + y) v‖ ≤ ‖x v‖ + ‖y v‖ := by simpa using norm_add_le (x v) (y v)
      _ ≤ c * N E k v + d * N E k v := add_le_add (h v) (h' v)
      _ = (c + d) * N E k v := by ring
  | smul a x _ hx =>
    obtain ⟨c, hc, h⟩ := hx
    refine ⟨‖a‖ * c, mul_nonneg (norm_nonneg _) hc, fun v => ?_⟩
    calc ‖(a • x) v‖ = ‖a‖ * ‖x v‖ := by simp [norm_smul]
      _ ≤ ‖a‖ * (c * N E k v) := mul_le_mul_of_nonneg_left (h v) (norm_nonneg _)
      _ = ‖a‖ * c * N E k v := by ring

lemma quad {x y P Q : ℝ} (_hx : 0 ≤ x) (hy : 0 ≤ y) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (h : x ^ 2 ≤ P * y ^ 2 + Q * x * y) : x ≤ (Q + Real.sqrt P) * y := by
  by_contra hc
  push Not at hc
  have hs := Real.sq_sqrt hP
  have hs0 := Real.sqrt_nonneg P
  have hxpos : 0 < x := lt_of_le_of_lt (mul_nonneg (add_nonneg hQ hs0) hy) hc
  have h1 : Real.sqrt P * y ≤ x := by nlinarith [mul_nonneg hQ hy]
  nlinarith [mul_pos hxpos (sub_pos.2 hc), mul_le_mul_of_nonneg_left h1 (mul_nonneg hs0 hy)]

lemma step (E : Fin n → Fin n → Module.End ℂ V) (ε : Fin n → Bool) (κ μ c : ℝ) (k : ℕ)
    (hcas : ∀ w : V, ∑ a, ∑ b, ‖E a b w‖ ^ 2 = 2 * (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2)
    (hc0 : 0 ≤ c)
    (hc : ∀ l : List (Fin n × Fin n), l.length ≤ k → ∀ v,
      ‖(casimirK ε E * wd E l - wd E l * casimirK ε E) v‖ ≤ c * N E (k + 1) v)
    (v : V) (hv : casimirK ε E v = (μ : ℂ) • v) (hμ : 0 ≤ μ) :
    N E (k + 1) v ≤ (2 * ((W n (k + 1)).card : ℝ) ^ 2 * c + ((W n (k + 1)).card : ℝ) * Real.sqrt (2 + |κ|)) *
      Real.sqrt (1 + μ) * N E k v := by
  have hx : 0 ≤ N E (k + 1) v := N_nonneg E _ v
  have hy : 0 ≤ N E k v := N_nonneg E _ v
  set x := N E (k + 1) v with hxdef
  set y := N E k v with hydef
  set M : ℝ := ((W n (k + 1)).card : ℝ) with hM
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hκ := abs_nonneg κ
  have key : ∀ l : List (Fin n × Fin n), l.length ≤ k + 1 →
      ‖wd E l v‖ ^ 2 ≤ (2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y := by
    intro l hl
    cases l with
    | nil =>
      have h1 : ‖wd E [] v‖ ≤ y := le_N E (l := []) (k := k) (Nat.zero_le _) v
      have h2 : 0 ≤ ‖wd E [] v‖ := norm_nonneg _
      nlinarith [mul_nonneg (mul_nonneg hc0 hx) hy,
        mul_nonneg (add_nonneg (mul_nonneg zero_le_two hμ) hκ) (sq_nonneg y)]
    | cons p l' =>
      have hl' : l'.length ≤ k := by simpa using hl
      have hwy : ‖wd E l' v‖ ≤ y := le_N E hl' v
      have hz := hc l' hl' v
      have hOw : casimirK ε E (wd E l' v) =
          (casimirK ε E * wd E l' - wd E l' * casimirK ε E) v + (μ : ℂ) • wd E l' v := by
        simp only [LinearMap.sub_apply, Module.End.mul_apply, hv, map_smul]
        abel
      have hsplit : wd E (p :: l') v = E p.1 p.2 (wd E l' v) := by
        simp [wd, Module.End.mul_apply]
      rw [hsplit]
      have hle : ‖E p.1 p.2 (wd E l' v)‖ ^ 2 ≤ ∑ a, ∑ b, ‖E a b (wd E l' v)‖ ^ 2 := by
        calc ‖E p.1 p.2 (wd E l' v)‖ ^ 2 ≤ ∑ b, ‖E p.1 b (wd E l' v)‖ ^ 2 :=
              Finset.single_le_sum (f := fun b => ‖E p.1 b (wd E l' v)‖ ^ 2) (fun _ _ => sq_nonneg _)
                (Finset.mem_univ _)
          _ ≤ ∑ a, ∑ b, ‖E a b (wd E l' v)‖ ^ 2 :=
              Finset.single_le_sum (f := fun a => ∑ b, ‖E a b (wd E l' v)‖ ^ 2)
                (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ _)
      have hin : (inner ℂ (wd E l' v) (casimirK ε E (wd E l' v))).re ≤
          ‖wd E l' v‖ * ‖(casimirK ε E * wd E l' - wd E l' * casimirK ε E) v‖ + μ * ‖wd E l' v‖ ^ 2 := by
        have hself : (inner ℂ (wd E l' v) (wd E l' v)).re = ‖wd E l' v‖ ^ 2 := by
          rw [inner_self_eq_norm_sq_to_K]; norm_cast
        rw [hOw, inner_add_right, Complex.add_re, inner_smul_right, Complex.re_ofReal_mul, hself]
        have := (Complex.re_le_norm (inner ℂ (wd E l' v)
          ((casimirK ε E * wd E l' - wd E l' * casimirK ε E) v))).trans (norm_inner_le_norm _ _)
        linarith
      rw [hcas] at hle
      have hw0 := norm_nonneg (wd E l' v)
      have hz0 := norm_nonneg ((casimirK ε E * wd E l' - wd E l' * casimirK ε E) v)
      have e1 := mul_le_mul hwy hz hz0 hy
      have e2 : ‖wd E l' v‖ ^ 2 ≤ y ^ 2 := by nlinarith
      have e3 := mul_le_mul_of_nonneg_left e2 hμ
      have e4 := mul_le_mul_of_nonneg_left e2 hκ
      have hk : -κ * ‖wd E l' v‖ ^ 2 ≤ |κ| * ‖wd E l' v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [neg_abs_le κ]) (sq_nonneg _)
      nlinarith [sq_nonneg y]
  have hR0 : 0 ≤ (2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y := by positivity
  have hsum : x ≤ M * Real.sqrt ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y) := by
    calc x = ∑ l ∈ W n (k + 1), ‖wd E l v‖ := rfl
      _ ≤ ∑ l ∈ W n (k + 1), Real.sqrt ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y) :=
          Finset.sum_le_sum fun l hl => (le_abs_self _).trans (Real.abs_le_sqrt (key l (mem_W.1 hl)))
      _ = M * Real.sqrt ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y) := by simp [hM]
  have hsq : x ^ 2 ≤ M ^ 2 * ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y) := by
    have := Real.sq_sqrt hR0
    have h0 := mul_nonneg hM0 (Real.sqrt_nonneg ((2 * μ + |κ| + 1) * y ^ 2 + 2 * c * x * y))
    nlinarith
  have hA : 0 ≤ 2 * μ + |κ| + 1 := by positivity
  have hq := quad (P := M ^ 2 * (2 * μ + |κ| + 1)) (Q := 2 * M ^ 2 * c) hx hy (by positivity) (by positivity)
    (by linarith)
  rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM0] at hq
  have ha : Real.sqrt (2 * μ + |κ| + 1) ≤ Real.sqrt (2 + |κ|) * Real.sqrt (1 + μ) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have ht : 1 ≤ Real.sqrt (1 + μ) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + μ by linarith)
    rwa [Real.sqrt_one] at this
  have h1 := mul_le_mul_of_nonneg_left ht (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * M ^ 2 * c) hy)
  have h2 := mul_le_mul_of_nonneg_left ha (mul_nonneg hM0 hy)
  nlinarith

end IdentityFiltrationBound

open IdentityFiltrationBound in
theorem SymmetricPowerMatrix : A0 → A1 → CasimirIsRealScalar → A6 := by
  intro h0 h1 h3 n ε V _ _ E hE
  obtain ⟨κ, hκ⟩ := h3 n ε V E hE
  obtain ⟨-, -, -, h0c⟩ := h0 n ε V E hE
  obtain ⟨hmono, -, -, -, hcomm, hK2, -⟩ := h1 n ε V E hE
  have hcas : ∀ w : V, ∑ a, ∑ b, ‖E a b w‖ ^ 2 = 2 * (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2 :=
    fun w => (h0c κ hκ w).1
  have grow : ∀ k : ℕ, ∃ G : ℝ, 0 ≤ G ∧ ∀ μ v, 0 ≤ μ → Eig ε E μ v →
      N E k v ≤ G * Real.sqrt (1 + μ) ^ k * ‖v‖ := by
    intro k
    induction k with
    | zero =>
      refine ⟨(W n 0).card, Nat.cast_nonneg _, fun μ v _ _ => ?_⟩
      simp only [pow_zero, mul_one]
      calc N E 0 v = ∑ l ∈ W n 0, ‖wd E l v‖ := rfl
        _ ≤ ∑ l ∈ W n 0, ‖v‖ := Finset.sum_le_sum fun l hl => by
            have := mem_W.1 hl
            cases l with
            | nil => simp [wd]
            | cons p l => simp at this
        _ = _ := by simp
    | succ k ih =>
      obtain ⟨G, hG, hG'⟩ := ih
      have hc : ∀ l : List (Fin n × Fin n), ∃ c : ℝ, 0 ≤ c ∧ (l.length ≤ k → ∀ v,
          ‖(casimirK ε E * wd E l - wd E l * casimirK ε E) v‖ ≤ c * N E (k + 1) v) := by
        intro l
        by_cases hl : l.length ≤ k
        · have hmem : wd E l ∈ U E k := hmono _ _ hl (Submodule.subset_span ⟨l, le_rfl, rfl⟩)
          have hin := hcomm 2 k _ hK2 _ hmem
          have h' : 2 + k - 1 = k + 1 := by omega
          rw [h'] at hin
          obtain ⟨c, hc, hc'⟩ := U_bound E (k + 1) _ hin
          exact ⟨c, hc, fun _ => hc'⟩
        · exact ⟨0, le_rfl, fun h => absurd h hl⟩
      choose c hc0 hc using hc
      have hC : ∀ l : List (Fin n × Fin n), l.length ≤ k → ∀ v,
          ‖(casimirK ε E * wd E l - wd E l * casimirK ε E) v‖ ≤ (∑ l ∈ W n k, c l) * N E (k + 1) v :=
        fun l hl v => (hc l hl v).trans (mul_le_mul_of_nonneg_right
          (Finset.single_le_sum (f := c) (fun i _ => hc0 i) (mem_W.2 hl)) (N_nonneg _ _ _))
      have hC0 : 0 ≤ ∑ l ∈ W n k, c l := Finset.sum_nonneg fun i _ => hc0 i
      refine ⟨(2 * ((W n (k + 1)).card : ℝ) ^ 2 * (∑ l ∈ W n k, c l) +
        ((W n (k + 1)).card : ℝ) * Real.sqrt (2 + |κ|)) * G, by positivity, fun μ v hμ hv => ?_⟩
      have hst := step E ε κ μ _ k hcas hC0 hC v hv hμ
      calc N E (k + 1) v ≤ _ := hst
        _ ≤ (2 * ((W n (k + 1)).card : ℝ) ^ 2 * (∑ l ∈ W n k, c l) +
            ((W n (k + 1)).card : ℝ) * Real.sqrt (2 + |κ|)) * Real.sqrt (1 + μ) *
              (G * Real.sqrt (1 + μ) ^ k * ‖v‖) :=
          mul_le_mul_of_nonneg_left (hG' μ v hμ hv) (by positivity)
        _ = _ := by ring
  intro k u hu
  obtain ⟨c, hc, hc'⟩ := U_bound E k u hu
  obtain ⟨G, hG, hG'⟩ := grow k
  refine ⟨c * G, mul_nonneg hc hG, fun μ v hμ hv => ?_⟩
  calc ‖u v‖ ≤ c * N E k v := hc' v
    _ ≤ c * (G * Real.sqrt (1 + μ) ^ k * ‖v‖) := mul_le_mul_of_nonneg_left (hG' μ v hμ hv) hc
    _ = _ := by ring

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MatrixActionSingle
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace SecondMomentAlgebra

lemma alg (n m : ℕ) (C1 C2 s T : ℝ) (hn : (1:ℝ) ≤ n) (hm : 1 ≤ m) (hC2 : 0 < C2) (hs : 1 ≤ s)
    (hs2 : 2 * C1 * (2 * (n:ℝ)) ^ m ≤ s)
    (h : (s ^ 2 / (2 * n)) ^ m ≤ C1 * s ^ (2 * m - 1) + C2 * s ^ (2 * m - 2) * T) :
    1 / (2 * (2 * (n:ℝ)) ^ m * C2) * s ^ 2 ≤ T := by
  have hA : 0 < (2 * (n:ℝ)) ^ m := by positivity
  have hs0 : 0 < s := by linarith
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have e2 : 2 * (k + 1) - 2 = 2 * k := by omega
  rw [e1, e2, div_pow, ← pow_mul] at h
  set A := (2 * (n:ℝ)) ^ (k + 1) with hAdef
  have hP : 0 < s ^ (2 * k) := by positivity
  have f1 : s ^ (2 * (k + 1)) = s ^ (2 * k) * s ^ 2 := by ring
  have f2 : s ^ (2 * k + 1) = s ^ (2 * k) * s := by ring
  rw [f1, f2, div_le_iff₀ hA] at h
  have h' : s ^ (2 * k) * s ^ 2 ≤ s ^ (2 * k) * (A * C1 * s + A * C2 * T) := by
    calc s ^ (2 * k) * s ^ 2 ≤ (C1 * (s ^ (2 * k) * s) + C2 * s ^ (2 * k) * T) * A := h
      _ = s ^ (2 * k) * (A * C1 * s + A * C2 * T) := by ring
  have h'' : s ^ 2 ≤ A * C1 * s + A * C2 * T := le_of_mul_le_mul_left h' hP
  have h2 : 2 * (A * C1 * s) ≤ s ^ 2 := by
    have := mul_le_mul_of_nonneg_right hs2 hs0.le
    nlinarith
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

lemma reEig (v : V) (μ : ℝ) : (inner ℂ v ((μ:ℂ) • v)).re = μ * ‖v‖ ^ 2 := by
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [Complex.mul_re, pow_two]

lemma cs {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ c, ∑ d, f c d) ^ 2 ≤ ((n:ℝ) * n) * ∑ c, ∑ d, f c d ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n × Fin n))) (f := fun p => f p.1 p.2)
  simpa [Fintype.sum_prod_type', Fintype.sum_prod_type, Finset.card_univ] using h

lemma zsum {n : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (hZc : ∀ a b, ε a = ε b → Z ε E a b = 0) (w : V) :
    ∑ c, ∑ d, ‖Z ε E c d w‖ ^ 2 = ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 w‖ ^ 2 := by
  rw [← Fintype.sum_prod_type' (fun c d => ‖Z ε E c d w‖ ^ 2), nc, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  split_ifs with h
  · rfl
  · simp [hZc _ _ (not_not.mp h)]

lemma scale {n : ℕ} (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (v : V) (hv : v ≠ 0) :
    ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 v‖ ^ 2 =
      ‖v‖ ^ 2 * ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 (((‖v‖ : ℂ)⁻¹) • v)‖ ^ 2 := by
  have h0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  simp only [map_smul, norm_smul, norm_inv, Complex.norm_real, norm_norm, mul_pow, ← Finset.mul_sum]
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ h0, one_pow, one_mul]

end SecondMomentAlgebra

set_option maxHeartbeats 800000 in
theorem second_moment_of_columns : A0 → A1 → FiltrationAdjointStable → CasimirIsRealScalar → A5 → A6 → ColumnOperatorMoments → A8 := by
  intro h0 h1 h1s h3c h5 h6 h8a n ε V _ _ E hM
  obtain ⟨-, -, hZc, hcas⟩ := h0 n ε V E hM
  obtain ⟨κ, hκ⟩ := h3c n ε V E hM
  set m : ℕ := 2 ^ n with hm
  have hm1 : 1 ≤ m := Nat.one_le_two_pow
  have hnm : n ≤ m := Nat.lt_two_pow_self.le
  have h5' := h5 n ε V E hM m hm1 hnm
  choose u hu w hw hdec using fun e : Fin n => h5' e e
  have hadj : ∀ e c d, ∃ w' ∈ U E (2 * m - 2), ∀ x y : V,
      inner ℂ x (w e c d y) = inner ℂ (w' x) y := fun e c d => h1s n ε V E hM _ _ (hw e c d)
  choose w' hw' hadj using hadj
  have bu : ∀ e, ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : ℝ) (v : V), 0 ≤ μ → Eig ε E μ v →
      ‖u e v‖ ≤ C * √(1 + μ) ^ (2 * m - 1) * ‖v‖ := fun e => h6 n ε V E hM _ _ (hu e)
  choose Cu hCu0 hCu using bu
  have bw : ∀ e c d, ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : ℝ) (v : V), 0 ≤ μ → Eig ε E μ v →
      ‖w' e c d v‖ ≤ C * √(1 + μ) ^ (2 * m - 2) * ‖v‖ := fun e c d => h6 n ε V E hM _ _ (hw' e c d)
  choose Cw hCw0 hCw using bw
  set C1 : ℝ := ∑ e, Cu e with hC1def
  set C2 : ℝ := ∑ e, ∑ c, ∑ d, Cw e c d + 1 with hC2def
  have hC1e : ∀ e, Cu e ≤ C1 := fun e =>
    Finset.single_le_sum (f := Cu) (fun i _ => hCu0 i) (Finset.mem_univ e)
  have hC2e : ∀ e c d, Cw e c d ≤ C2 := by
    intro e c d
    have a1 : Cw e c d ≤ ∑ d', Cw e c d' :=
      Finset.single_le_sum (f := fun d' => Cw e c d') (fun i _ => hCw0 e c i) (Finset.mem_univ d)
    have a2 : ∑ d', Cw e c d' ≤ ∑ c', ∑ d', Cw e c' d' :=
      Finset.single_le_sum (f := fun c' => ∑ d', Cw e c' d')
        (fun i _ => Finset.sum_nonneg (fun j _ => hCw0 e i j)) (Finset.mem_univ c)
    have a3 : ∑ c', ∑ d', Cw e c' d' ≤ ∑ e', ∑ c', ∑ d', Cw e' c' d' :=
      Finset.single_le_sum (f := fun e' => ∑ c', ∑ d', Cw e' c' d')
        (fun i _ => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hCw0 i j k)))
        (Finset.mem_univ e)
    linarith
  have hC2 : 0 < C2 := by
    have : 0 ≤ ∑ e, ∑ c, ∑ d, Cw e c d :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => hCw0 i j k)))
    linarith
  set N : ℝ := (2 * (n:ℝ)) ^ m with hNdef
  refine ⟨1 / ((2 * N * C2) ^ 2 * ((n:ℝ) * n + 1) + 1), max (max 1 (|κ| + 1)) ((2 * C1 * N) ^ 2),
    by positivity, ?_⟩
  intro μ v hμ hv
  have hμ1 : 1 ≤ μ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hμ
  have hμκ : |κ| + 1 ≤ μ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hμ
  have hμC : (2 * C1 * N) ^ 2 ≤ μ := le_trans (le_max_right _ _) hμ
  by_cases hv0 : v = 0
  · subst hv0
    simp
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  set v1 : V := ((‖v‖ : ℂ)⁻¹) • v with hv1def
  have hv1n : ‖v1‖ = 1 := by
    rw [hv1def, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hnv.ne']
  have hv1E : Eig ε E μ v1 := by
    have hv' : casimirK ε E v = (μ : ℂ) • v := hv
    show casimirK ε E (((‖v‖ : ℂ)⁻¹) • v) = (μ : ℂ) • (((‖v‖ : ℂ)⁻¹) • v)
    rw [map_smul, hv', smul_comm]
  rw [SecondMomentAlgebra.scale ε E v hv0]
  suffices hS : 1 / ((2 * N * C2) ^ 2 * ((n:ℝ) * n + 1) + 1) * (1 + μ) ^ 2 ≤
      ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 v1‖ ^ 2 by
    have := mul_le_mul_of_nonneg_left hS (sq_nonneg ‖v‖)
    linarith
  have hX : ∑ a, ∑ b, ‖E a b v1‖ ^ 2 = 2 * μ - κ := by
    rw [(hcas κ hκ v1).1, show casimirK ε E v1 = (μ : ℂ) • v1 from hv1E, SecondMomentAlgebra.reEig, hv1n]
    ring
  have hpos : 0 < 2 * μ - κ := by linarith [le_abs_self κ]
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hX
    simp at hX
    linarith
  obtain ⟨e0, -⟩ := hne
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt (Fin.pos e0)
  have hnr : (n:ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hN : 0 < N := by positivity
  obtain ⟨e, -, he⟩ := exists_le_of_sum_le (s := Finset.univ) ⟨e0, Finset.mem_univ _⟩
    (f := fun _ => (2 * μ - κ) / n) (g := fun e => ∑ a, ‖E a e v1‖ ^ 2) (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have : (n:ℝ) * ((2 * μ - κ) / n) = 2 * μ - κ := by field_simp
      rw [this, ← hX, Finset.sum_comm])
  have h8 := h8a n ε V E hM v1 hv1n e n
  rw [hdec e] at h8
  simp only [LinearMap.add_apply, LinearMap.sum_apply, Module.End.mul_apply, inner_add_right, inner_sum,
    Complex.add_re, Complex.re_sum] at h8
  have hs : √(1 + μ) ^ 2 = 1 + μ := Real.sq_sqrt (by linarith)
  have b1 : (inner ℂ v1 (u e v1)).re ≤ Cu e * √(1 + μ) ^ (2 * m - 1) := by
    have r := re_inner_le_norm (𝕜 := ℂ) v1 (u e v1)
    have r2 : ‖u e v1‖ ≤ Cu e * √(1 + μ) ^ (2 * m - 1) := by
      simpa [hv1n] using hCu e μ v1 (by linarith) hv1E
    rw [hv1n, one_mul] at r
    exact le_trans r r2
  have b2 : ∀ c d, (inner ℂ v1 (w e c d (Z ε E c d v1))).re ≤
      C2 * √(1 + μ) ^ (2 * m - 2) * ‖Z ε E c d v1‖ := by
    intro c d
    rw [hadj e c d]
    have r := re_inner_le_norm (𝕜 := ℂ) (w' e c d v1) (Z ε E c d v1)
    have r2 : ‖w' e c d v1‖ ≤ C2 * √(1 + μ) ^ (2 * m - 2) := by
      have := hCw e c d μ v1 (by linarith) hv1E
      rw [hv1n, mul_one] at this
      exact le_trans this (mul_le_mul_of_nonneg_right (hC2e e c d) (by positivity))
    exact le_trans r (mul_le_mul_of_nonneg_right r2 (norm_nonneg _))
  have hsum : ∑ c, ∑ d, ‖Z ε E c d v1‖ ≤ √((n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2) :=
    le_trans (le_abs_self _) (Real.abs_le_sqrt (SecondMomentAlgebra.cs (fun c d => ‖Z ε E c d v1‖)))
  set T := √((n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2) with hTdef
  have hXe : √(1 + μ) ^ 2 / (2 * n) ≤ ∑ a, ‖E a e v1‖ ^ 2 := by
    rw [hs]
    calc (1 + μ) / (2 * n) ≤ (2 * μ - κ) / n := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [le_abs_self κ]
      _ ≤ _ := he
  have hmain : (√(1 + μ) ^ 2 / (2 * n)) ^ m ≤
      C1 * √(1 + μ) ^ (2 * m - 1) + C2 * √(1 + μ) ^ (2 * m - 2) * T := by
    calc (√(1 + μ) ^ 2 / (2 * n)) ^ m ≤ (∑ a, ‖E a e v1‖ ^ 2) ^ m :=
          pow_le_pow_left₀ (by positivity) hXe m
      _ ≤ _ := h8
      _ ≤ Cu e * √(1 + μ) ^ (2 * m - 1) + ∑ c, ∑ d, C2 * √(1 + μ) ^ (2 * m - 2) * ‖Z ε E c d v1‖ :=
          add_le_add b1 (Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => b2 c d)
      _ ≤ _ := by
          simp_rw [← Finset.mul_sum]
          exact add_le_add (mul_le_mul_of_nonneg_right (hC1e e) (by positivity))
            (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hs1 : 1 ≤ √(1 + μ) := by
    have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1 + μ by linarith)
    rwa [Real.sqrt_one] at this
  have hs2 : 2 * C1 * N ≤ √(1 + μ) := by
    refine le_trans (le_abs_self _) ?_
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have key := SecondMomentAlgebra.alg n m C1 C2 (√(1 + μ)) T hn1 hm1 hC2 hs1 hs2 hmain
  rw [hs] at key
  have hS'0 : 0 ≤ ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2 := by positivity
  have hq : (1 / (2 * N * C2) * (1 + μ)) ^ 2 ≤ (n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) key 2
    rwa [hTdef, Real.sq_sqrt (by positivity)] at this
  have hq' : (1 + μ) ^ 2 ≤ (2 * N * C2) ^ 2 * ((n:ℝ) * n * ∑ c, ∑ d, ‖Z ε E c d v1‖ ^ 2) := by
    have e3 : (1 + μ) ^ 2 = (2 * N * C2) ^ 2 * (1 / (2 * N * C2) * (1 + μ)) ^ 2 := by
      field_simp
    rw [e3]
    exact mul_le_mul_of_nonneg_left hq (sq_nonneg _)
  rw [← SecondMomentAlgebra.zsum ε E hZc v1]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg hS'0 (sq_nonneg (2 * N * C2))]

end PositivityTheory.CW

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.U0Commute
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ParabolicUnipotentGL
noncomputable def UpperTheory.Reformulated.B.ParabolicUnipotentGL.IsGlRep.{u_1} :
    {n : ℕ} →
      {M : Type u_1} → [inst : AddCommGroup M] → [inst_1 : _root_.Module ℂ M] → (Fin n → Fin n → Module.End ℂ M) → Prop :=
    fun {n : ℕ} {M : Type u_1} [AddCommGroup M] [_root_.Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) ↦
      ∀ (a b c d : Fin n),
        E a b * E c d - E c d * E a b =
          (if b = c then E a d else (0 : Module.End ℂ M)) - if d = a then E c b else (0 : Module.End ℂ M)

noncomputable def UpperTheory.Reformulated.B.ParabolicUnipotentGL.U :
    {n : ℕ} →
      {V : Type} →
        [inst : AddCommGroup V] →
          [inst_1 : _root_.Module ℂ V] → (Fin n → Fin n → Module.End ℂ V) → ℕ → Submodule ℂ (Module.End ℂ V) :=
    fun {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) ↦
      Submodule.span ℂ
        {x : Module.End ℂ V |
          ∃ (l : List (Fin n × Fin n)), l.length ≤ k ∧ x = (List.map (fun (p : Fin n × Fin n) ↦ E p.1 p.2) l).prod}

namespace UpperTheory.Reformulated.B.ParabolicUnipotentGL

section helpers

variable {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)

private abbrev P (l : List (Fin n × Fin n)) : Module.End ℂ V :=
  (List.map (fun (p : Fin n × Fin n) ↦ E p.1 p.2) l).prod

private theorem U_mono {j k : ℕ} (h : j ≤ k) : U E j ≤ U E k := by
  apply Submodule.span_mono
  rintro x ⟨l, hl, rfl⟩
  exact ⟨l, hl.trans h, rfl⟩

private theorem monomial_mem_filtration_of_length_le (l : List (Fin n × Fin n)) {k : ℕ} (h : l.length ≤ k) : P E l ∈ U E k :=
  Submodule.subset_span ⟨l, h, rfl⟩

private theorem gen_mem (a b : Fin n) : E a b ∈ U E 1 := by
  have := monomial_mem_filtration_of_length_le E [(a, b)] (k := 1) (by simp)
  simpa [P] using this

private theorem mul_mem_U {j k : ℕ} {x y : Module.End ℂ V} (hx : x ∈ U E j) (hy : y ∈ U E k) :
    x * y ∈ U E (j + k) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      refine Submodule.subset_span ⟨l ++ m, ?_, ?_⟩
      · simp only [List.length_append]; omega
      · simp
    | zero => simp
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | smul c a _ ha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha

private theorem gen_comm_mem (hE : IsGlRep E) (a b c d : Fin n) :
    E a b * E c d - E c d * E a b ∈ U E 1 := by
  rw [hE a b c d]
  refine sub_mem ?_ ?_
  · split_ifs
    · exact gen_mem E _ _
    · exact zero_mem _
  · split_ifs
    · exact gen_mem E _ _
    · exact zero_mem _

private theorem gen_comm_P (hE : IsGlRep E) (a b : Fin n) (l : List (Fin n × Fin n)) :
    E a b * P E l - P E l * E a b ∈ U E l.length := by
  induction l with
  | nil => simp [P]
  | cons p t ih =>
    have e : E a b * P E (p :: t) - P E (p :: t) * E a b
        = (E a b * E p.1 p.2 - E p.1 p.2 * E a b) * P E t
          + E p.1 p.2 * (E a b * P E t - P E t * E a b) := by
      simp only [P, List.map_cons, List.prod_cons]
      noncomm_ring
    rw [e, List.length_cons, add_comm t.length 1]
    exact add_mem (mul_mem_U E (gen_comm_mem E hE _ _ _ _) (monomial_mem_filtration_of_length_le E t le_rfl))
      (mul_mem_U E (gen_mem E _ _) ih)

private theorem monomial_commutator_mem_filtration (hE : IsGlRep E) (l : List (Fin n × Fin n)) (q : Fin n × Fin n)
    (m : List (Fin n × Fin n)) :
    P E l * P E (q :: m) - P E (q :: m) * P E l ∈ U E (l.length + m.length) := by
  induction l with
  | nil => simp [P]
  | cons p t ih =>
    have e : P E (p :: t) * P E (q :: m) - P E (q :: m) * P E (p :: t)
        = E p.1 p.2 * (P E t * P E (q :: m) - P E (q :: m) * P E t)
          + (E p.1 p.2 * P E (q :: m) - P E (q :: m) * E p.1 p.2) * P E t := by
      generalize P E (q :: m) = y
      simp only [P, List.map_cons, List.prod_cons]
      noncomm_ring
    rw [e]
    refine add_mem ?_ ?_
    · exact U_mono E (by simp only [List.length_cons]; omega) (mul_mem_U E (gen_mem E _ _) ih)
    · exact U_mono E (by simp only [List.length_cons]; omega)
        (mul_mem_U E (gen_comm_P E hE _ _ (q :: m)) (monomial_mem_filtration_of_length_le E t le_rfl))

end helpers

end UpperTheory.Reformulated.B.ParabolicUnipotentGL

theorem UpperTheory.Reformulated.B.ParabolicUnipotentGL.main :
    ∀ {n : ℕ} {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V),
      UpperTheory.Reformulated.B.ParabolicUnipotentGL.IsGlRep E →
        ∀ {j k : ℕ} {x y : Module.End ℂ V},
          x ∈ UpperTheory.Reformulated.B.ParabolicUnipotentGL.U E j →
            y ∈ UpperTheory.Reformulated.B.ParabolicUnipotentGL.U E k → x * y - y * x ∈ UpperTheory.Reformulated.B.ParabolicUnipotentGL.U E (j + k - (1 : ℕ)) := by
  intro n V _ _ E hE j k x y hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl, rfl⟩ := hx
      obtain ⟨m, hm, rfl⟩ := hy
      cases m with
      | nil => simp
      | cons q t =>
        simp only [List.length_cons] at hm
        exact UpperTheory.Reformulated.B.ParabolicUnipotentGL.U_mono E (by omega) (UpperTheory.Reformulated.B.ParabolicUnipotentGL.monomial_commutator_mem_filtration E hE l q t)
    | zero => simp
    | add a b _ _ ha hb =>
      have e : x * (a + b) - (a + b) * x = (x * a - a * x) + (x * b - b * x) := by noncomm_ring
      rw [e]; exact add_mem ha hb
    | smul c a _ ha =>
      have e : x * (c • a) - (c • a) * x = c • (x * a - a * x) := by
        rw [mul_smul_comm, smul_mul_assoc, smul_sub]
      rw [e]; exact Submodule.smul_mem _ c ha
  | zero => simp
  | add a b _ _ ha hb =>
    have e : (a + b) * y - y * (a + b) = (a * y - y * a) + (b * y - y * b) := by noncomm_ring
    rw [e]; exact add_mem ha hb
  | smul c a _ ha =>
    have e : (c • a) * y - y * (c • a) = c • (a * y - y * a) := by
      rw [mul_smul_comm, smul_mul_assoc, smul_sub]
    rw [e]; exact Submodule.smul_mem _ c ha
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnitaryGroupStatement
noncomputable def UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U :
    {n : ℕ} →
      {V : Type} →
        [inst : AddCommGroup V] →
          [inst_1 : _root_.Module ℂ V] → (Fin n → Fin n → Module.End ℂ V) → ℕ → Submodule ℂ (Module.End ℂ V) :=
    fun {n : ℕ} {V : Type} [AddCommGroup V] [_root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (k : ℕ) ↦
      Submodule.span ℂ
        {x : Module.End ℂ V |
          ∃ (l : List (Fin n × Fin n)), l.length ≤ k ∧ x = (List.map (fun (p : Fin n × Fin n) ↦ E p.1 p.2) l).prod}

theorem UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.main :
    ∀ {n : ℕ} {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) {j k : ℕ}
      {x y : Module.End ℂ V},
      x ∈ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E j → y ∈ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E k → x * y ∈ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E (j + k) := by
  intro n V _ _ E j k x y hx hy
  have h : UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E j * UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E k ≤ UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U E (j + k) := by
    unfold UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.U
    rw [Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro z ⟨a, ⟨l1, hl1, rfl⟩, b, ⟨l2, hl2, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨l1 ++ l2, ?_, ?_⟩
    · simp only [List.length_append]; omega
    · simp [List.map_append, List.prod_append]
  exact h (Submodule.mul_mem_mul hx hy)
end

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CWB

open PositivityTheory.CW

namespace WordFiltrationCommute

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)

theorem U_mono {j k : ℕ} (h : j ≤ k) : U E j ≤ U E k :=
  Submodule.span_mono fun _ ⟨l, hl, hx⟩ => ⟨l, hl.trans h, hx⟩

theorem one_mem : (1 : Module.End ℂ V) ∈ U E 0 :=
  Submodule.subset_span ⟨[], by simp, by simp⟩

theorem gen_mem (a b : Fin n) : E a b ∈ U E 1 :=
  Submodule.subset_span ⟨[(a, b)], by simp, by simp⟩

theorem mul_mem {j k : ℕ} {x y : Module.End ℂ V} (hx : x ∈ U E j) (hy : y ∈ U E k) :
    x * y ∈ U E (j + k) :=
  by apply _root_.UpperTheory.Reformulated.B.EndomorphismFiltrationMulMem.main <;> assumption

theorem bracket_mem (hE : IsGlRep E) {j k : ℕ} {x y : Module.End ℂ V} (hx : x ∈ U E j) (hy : y ∈ U E k) :
    x * y - y * x ∈ U E (j + k - 1) :=
  by apply _root_.UpperTheory.Reformulated.B.ParabolicUnipotentGL.main <;> assumption

end WordFiltrationCommute

theorem word_filtration_of_length : A1 := by
  intro n ε V _ _ E hM
  have hE : IsGlRep E := hM.gl
  have hC : casimirK ε E ∈ U E 2 := by
    unfold casimirK
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    exact WordFiltrationCommute.U_mono E (by norm_num : 1 + 1 ≤ 2) (WordFiltrationCommute.mul_mem E (WordFiltrationCommute.gen_mem E a b) (WordFiltrationCommute.gen_mem E b a))
  refine ⟨fun j k h => WordFiltrationCommute.U_mono E h, WordFiltrationCommute.one_mem E, WordFiltrationCommute.gen_mem E,
    fun j k x hx y hy => WordFiltrationCommute.mul_mem E hx hy, fun j k x hx y hy => WordFiltrationCommute.bracket_mem E hE hx hy, hC,
    fun a b => ?_⟩
  have hZ := WordFiltrationCommute.bracket_mem E hE hC (WordFiltrationCommute.gen_mem E a b)
  unfold Z
  exact WordFiltrationCommute.U_mono E (by norm_num : 2 + 1 - 1 ≤ 2) hZ

end PositivityTheory.CWB

end
end
