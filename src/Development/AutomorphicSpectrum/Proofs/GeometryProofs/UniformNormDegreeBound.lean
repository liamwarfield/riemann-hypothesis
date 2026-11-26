module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerOriginComponentBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelSmallSectionsMul
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompLawsTowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormTowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormHeightEstimate
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.YBrLat

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormHeightCount
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionHeightBound
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionHeightBound
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.Plug.Count

open MvPolynomial GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem cauchy_bound {D : ℕ} (L : ℕ → ℝ) (hL : ∀ j, 0 ≤ L j) {a b : ℝ} (hb : 0 ≤ b)
    (h : a ^ D ≤ ∑ j ∈ Finset.range D, L j * a ^ j * b ^ (D - j)) :
    a ≤ (1 + ∑ j ∈ Finset.range D, L j) * b := by
  by_contra hlt
  rw [not_le] at hlt
  set S := ∑ j ∈ Finset.range D, L j with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => hL j
  have hB : 1 ≤ 1 + S := by linarith
  have hB0 : 0 < 1 + S := by linarith
  have ha0 : 0 < a := lt_of_le_of_lt (mul_nonneg hB0.le hb) hlt
  have hba : b ≤ a / (1 + S) := by rw [le_div_iff₀ hB0]; linarith
  have hterm : ∀ j ∈ Finset.range D, L j * a ^ j * b ^ (D - j) ≤ L j * (a ^ D / (1 + S)) := by
    intro j hj
    have hj' : j < D := Finset.mem_range.mp hj
    obtain ⟨m, hm⟩ : ∃ m, D - j = m + 1 := ⟨D - j - 1, by omega⟩
    have h1 : b ^ (D - j) ≤ a ^ (D - j) / (1 + S) := by
      rw [hm]
      calc b ^ (m + 1) ≤ (a / (1 + S)) ^ (m + 1) := pow_le_pow_left₀ hb hba _
        _ = a ^ (m + 1) / (1 + S) ^ (m + 1) := div_pow _ _ _
        _ ≤ a ^ (m + 1) / (1 + S) := by
            apply div_le_div_of_nonneg_left (by positivity) hB0
            calc 1 + S = (1 + S) ^ 1 := (pow_one _).symm
              _ ≤ (1 + S) ^ (m + 1) := pow_le_pow_right₀ hB (by omega)
    have h2 : a ^ j * a ^ (D - j) = a ^ D := by rw [← pow_add]; congr 1; omega
    calc L j * a ^ j * b ^ (D - j) ≤ L j * a ^ j * (a ^ (D - j) / (1 + S)) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg (hL j) (by positivity))
      _ = L j * (a ^ j * a ^ (D - j) / (1 + S)) := by ring
      _ = _ := by rw [h2]
  have hsum : a ^ D ≤ S * (a ^ D / (1 + S)) := by
    refine h.trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [hS, Finset.sum_mul]
  have hpos : 0 < a ^ D := by positivity
  have : S * (a ^ D / (1 + S)) < a ^ D := by
    rw [mul_div_assoc', div_lt_iff₀ hB0]
    nlinarith
  linarith

theorem exists_integral_bound (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω}
    (hx : x ∈ integralClosure (chartRingZ y c) Ω) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (d : K → ℕ) (G F : MRing ι) (z : (Σ k, ι k) → ℂ),
      IsMultiHomog G d → IsMultiHomog F d → aeval y G = x * aeval y F → z ∈ mcPts (mCoordIdeal y) →
      (∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖) → (∀ k, z ⟨k, c k⟩ ≠ 0) →
      ‖eval z (map (Int.castRingHom ℂ) G)‖ ≤ B * ‖eval z (map (Int.castRingHom ℂ) F)‖ := by
  classical
  obtain ⟨p, pm, hp⟩ := hx
  set D := p.natDegree with hD
  have hform : ∀ j : ℕ, ∃ (δ : K → ℕ) (e : MRing ι), IsMultiHomog e δ ∧
      aeval y e = ((p.coeff j : chartRingZ y c) : Ω) * ∏ k, y ⟨k, c k⟩ ^ δ k := fun j =>
    exists_form_of_mem_chartRingZ y c hc (p.coeff j).2
  choose δ e he hev using hform
  set Δ : K → ℕ := ∑ j ∈ Finset.range D, δ j with hΔ
  have hle : ∀ j ∈ Finset.range D, ∀ k, δ j k ≤ Δ k := by
    intro j hj k
    rw [hΔ, Finset.sum_apply]
    exact Finset.single_le_sum (f := fun j => δ j k) (fun _ _ => Nat.zero_le _) hj
  let Fm : ℕ → MRing ι := fun j => e j * chartMon c (Δ - δ j)
  have hFm : ∀ j ∈ Finset.range D, IsMultiHomog (Fm j) Δ := fun j hj =>
    homog_congr (homog_mul (he j) (homog_chartMon c (Δ - δ j))) fun k => by
      simp only [Pi.add_apply, Pi.sub_apply]
      have := hle j hj k
      omega
  have hFmv : ∀ j ∈ Finset.range D, aeval y (Fm j) =
      ((p.coeff j : chartRingZ y c) : Ω) * ∏ k, y ⟨k, c k⟩ ^ Δ k := by
    intro j hj
    simp only [Fm, map_mul, aeval_chartMon, hev]
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_add]
    congr 1
    simp only [Pi.sub_apply]
    have := hle j hj k
    omega
  refine ⟨1 + ∑ j ∈ Finset.range D, coeffNorm (Fm j),
    add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => coeffNorm_nonneg _), ?_⟩
  intro d G F z hG hF hGF hz hmax hz0
  have heq : x ^ D + ∑ j ∈ Finset.range D, ((p.coeff j : chartRingZ y c) : Ω) * x ^ j = 0 := by
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, ← hD] at hp
    have h1 : p.coeff D = 1 := pm.coeff_natDegree
    rw [h1, map_one, one_mul] at hp
    rw [add_comm]
    exact hp
  let Q : MRing ι := chartMon c Δ * G ^ D + ∑ j ∈ Finset.range D, Fm j * G ^ j * F ^ (D - j)
  have hQ : IsMultiHomog Q (Δ + D • d) := by
    refine homog_add (homog_mul (homog_chartMon c Δ) (homog_pow hG D)) (homog_sum _ fun j hj => ?_)
    refine homog_congr (homog_mul (homog_mul (hFm j hj) (homog_pow hG j)) (homog_pow hF (D - j))) fun k => ?_
    have hj' : j ≤ D := (Finset.mem_range.mp hj).le
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : j * d k + (D - j) * d k = D * d k := by rw [← add_mul]; congr 1; omega
    omega
  have hQy : aeval y Q = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Q, map_add (f := _), map_mul, map_pow, map_sum, aeval_chartMon, hGF]
    have : ∀ j ∈ Finset.range D, aeval y (Fm j) * (x * aeval y F) ^ j * aeval y F ^ (D - j) =
        (∏ k, y ⟨k, c k⟩ ^ Δ k) * aeval y F ^ D * (((p.coeff j : chartRingZ y c) : Ω) * x ^ j) := by
      intro j hj
      rw [hFmv j hj, mul_pow]
      have : aeval y F ^ D = aeval y F ^ j * aeval y F ^ (D - j) := by
        rw [← pow_add]; congr 1; have := Finset.mem_range.mp hj; omega
      rw [this]
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, mul_pow]
    calc _ = (∏ k, y ⟨k, c k⟩ ^ Δ k) * aeval y F ^ D *
          (x ^ D + ∑ j ∈ Finset.range D, ((p.coeff j : chartRingZ y c) : Ω) * x ^ j) := by ring
      _ = 0 := by rw [heq, mul_zero]
  have hQz := vanish hz hQ hQy
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Q, map_add (f := _), map_mul, map_pow, map_sum, eval_chartMon] at hQz
  set gz := eval z (map (Int.castRingHom ℂ) G) with hgz
  set fz := eval z (map (Int.castRingHom ℂ) F) with hfz
  set Pz := ∏ k, ‖z ⟨k, c k⟩‖ ^ Δ k with hPz
  have hPpos : 0 < Pz := Finset.prod_pos fun k _ => pow_pos (norm_pos_iff.mpr (hz0 k)) _
  have hmain : Pz * ‖gz‖ ^ D ≤ Pz * ∑ j ∈ Finset.range D, coeffNorm (Fm j) * ‖gz‖ ^ j * ‖fz‖ ^ (D - j) := by
    have e1 : (∏ k, z ⟨k, c k⟩ ^ Δ k) * gz ^ D =
        -∑ j ∈ Finset.range D, eval z (map (Int.castRingHom ℂ) (Fm j)) * gz ^ j * fz ^ (D - j) :=
      eq_neg_of_add_eq_zero_left hQz
    have e2 : Pz * ‖gz‖ ^ D = ‖(∏ k, z ⟨k, c k⟩ ^ Δ k) * gz ^ D‖ := by
      rw [norm_mul, norm_prod, norm_pow]
      simp only [norm_pow, hPz]
    rw [e2, e1, norm_neg, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    have := norm_eval_le hmax (hFm j hj)
    calc _ ≤ (coeffNorm (Fm j) * Pz) * ‖gz‖ ^ j * ‖fz‖ ^ (D - j) := by gcongr
      _ = _ := by ring
  have h2 := le_of_mul_le_mul_left hmain hPpos
  exact cauchy_bound (fun j => coeffNorm (Fm j)) (fun _ => coeffNorm_nonneg _) (norm_nonneg _) h2

theorem exists_upper_nm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) {s : Ω} (hs : s ∈ chartLatNm y a n)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (dg dh : K → ℕ) (g h : MRing ι) (z : (Σ k, ι k) → ℂ),
      IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + n * a k) →
      aeval y g = s * aeval y h → z ∈ mcPts (mCoordIdeal y) →
      (∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖) → (∀ k, z ⟨k, c k⟩ ≠ 0) →
      ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤
        B * ‖eval z (map (Int.castRingHom ℂ) h)‖ * ∏ k, ‖z ⟨k, c k⟩‖ ^ ((n : ℤ) * a k) := by
  obtain ⟨B, hB0, hB⟩ := exists_integral_bound y c hc (hs c hc)
  refine ⟨B, hB0, ?_⟩
  intro dg dh g h z hg hh hd hgy hz hmax hz0
  let up : K → ℕ := fun k => ((n : ℤ) * a k).toNat
  let dn : K → ℕ := fun k => (-((n : ℤ) * a k)).toNat
  have hud : ∀ k, (up k : ℤ) - dn k = (n : ℤ) * a k := fun k => by
    simp only [up, dn]; omega
  have hdeg : ∀ k, (dg + dn) k = (dh + up) k := fun k => by
    have h1 := hd k
    have h2 := hud k
    simp only [Pi.add_apply]
    omega
  have hG : IsMultiHomog (g * chartMon c dn) (dh + up) :=
    homog_congr (homog_mul hg (homog_chartMon c dn)) hdeg
  have hF : IsMultiHomog (h * chartMon c up) (dh + up) := homog_mul hh (homog_chartMon c up)
  have hval : aeval y (g * chartMon c dn) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * aeval y (h * chartMon c up) := by
    simp only [map_mul, aeval_chartMon, hgy]
    have : (∏ k, y ⟨k, c k⟩ ^ dn k) = (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ up k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k)]
      congr 1
      have := hud k
      omega
    rw [this]
    ring
  have h1 := hB _ _ _ z hG hF hval hz hmax hz0
  simp only [map_mul, eval_chartMon, norm_mul, norm_prod, norm_pow] at h1
  have hr : ∀ k, ‖z ⟨k, c k⟩‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hz0 k)
  have hDn : 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ dn k := Finset.prod_pos fun k _ => pow_pos (norm_pos_iff.mpr (hz0 k)) _
  have hUp : ∏ k, ‖z ⟨k, c k⟩‖ ^ up k = (∏ k, ‖z ⟨k, c k⟩‖ ^ ((n : ℤ) * a k)) * ∏ k, ‖z ⟨k, c k⟩‖ ^ dn k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hr k)]
    congr 1
    have := hud k
    omega
  rw [hUp] at h1
  refine le_of_mul_le_mul_right ?_ hDn
  calc _ ≤ _ := h1
    _ = _ := by ring

noncomputable def invLine (A : HermLine ι) : HermLine ι where
  a := fun k => - A.a k
  h z := (A.h z)⁻¹
  pos z hz := inv_pos.mpr (A.pos z hz)
  smul c z hc := by
    rw [A.smul c z hc, mul_inv, ← Finset.prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [zpow_neg]

theorem exists_lower_max (A : HermLine ι) (hA : IsSmoothHerm A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (z : (Σ k, ι k) → ℂ) (c : ∀ k, ι k), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      (∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖) → ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k ≤ M * A.h z := by
  have hI : IsSmoothHerm (invLine A) := by
    unfold IsSmoothHerm at hA ⊢
    exact hA.inv fun z hz => (A.pos z hz).ne'
  obtain ⟨C, hC1, hC⟩ := MetricMaxComparison.proof K ι (invLine A) hI
  refine ⟨C, by linarith, fun z c hz hmax => ?_⟩
  have h1 := hC z hz
  have hn : ∀ k, ‖fun i : ι k => z ⟨k, i⟩‖ = ‖z ⟨k, c k⟩‖ := fun k =>
    le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => hmax k i)
      (norm_le_pi_norm (fun i : ι k => z ⟨k, i⟩) (c k))
  have hz0 : ∀ k, 0 < ‖z ⟨k, c k⟩‖ := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact lt_of_lt_of_le (norm_pos_iff.mpr hi) (hmax k i)
  have h2 : (HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) (invLine A).a).h z =
      (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ := by
    show ∏ k, ‖fun i : ι k => z ⟨k, i⟩‖ ^ (- A.a k) = _
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hn k, zpow_neg]
  rw [h2] at h1
  have hP : 0 < ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k := Finset.prod_pos fun k _ => zpow_pos (hz0 k) _
  have hh : 0 < A.h z := A.pos z hz
  have h3 : (A.h z)⁻¹ ≤ C * (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ := h1
  rw [inv_le_iff_one_le_mul₀ hh] at h3
  have h4 := mul_le_mul_of_nonneg_right h3 hP.le
  rw [one_mul] at h4
  calc _ ≤ _ := h4
    _ = C * A.h z * ((∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k)⁻¹ * ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) := by ring
    _ = C * A.h z := by rw [inv_mul_cancel₀ hP.ne', mul_one]

theorem bounded_section_smooth_metric (y : (Σ k, ι k) → Ω) (A : HermLine ι) (τ : ℕ) (s : Ω) (hA : IsSmoothHerm A)
    (hs : s ∈ chartLatNm y A.a τ) :
    ∃ C : ℝ, 0 < C ∧ IsBoundedH (mCoordIdeal y) y A τ C s := by
  classical
  obtain ⟨M, hM0, hM⟩ := exists_lower_max A hA
  choose B hB0 hB using fun c hc => exists_upper_nm y A.a τ hs c hc
  refine ⟨1 + (∑ c : (∀ k, ι k), if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M ^ τ else 0), ?_, ?_⟩
  · refine add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun c' _ => ?_)
    split_ifs with hc'
    · exact mul_nonneg (hB0 c' hc') (pow_nonneg hM0 τ)
    · exact le_rfl
  intro dg dh g h z hg hh hdeg hgy hz
  have hmax : ∀ k, ∃ i, ∀ i', ‖z ⟨k, i'⟩‖ ≤ ‖z ⟨k, i⟩‖ := fun k => by
    obtain ⟨i0, _⟩ := hz.1 k
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖z ⟨k, i⟩‖) ⟨i0, Finset.mem_univ _⟩
    exact ⟨i, fun i' => hi i' (Finset.mem_univ _)⟩
  choose c hcmax using hmax
  have hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0 := fun k h0 => by
    obtain ⟨i0, hi0⟩ := hz.1 k
    have := hcmax k i0
    rw [h0, norm_zero] at this
    exact hi0 (norm_le_zero_iff.mp this)
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hz0 k (by
    have := vanish hz (homog_X ⟨k, c k⟩) (by rw [aeval_X]; exact h0)
    simpa using this)
  have h1 := hB c hyc dg dh g h z hg hh hdeg hgy hz hcmax hz0
  have h2 := hM z c hz.1 hcmax
  have hpow : ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) = (∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) ^ τ := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [mul_comm, zpow_mul, zpow_natCast]
  have h3 : ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) ≤ M ^ τ * A.h z ^ τ := by
    rw [hpow, ← mul_pow]
    exact pow_le_pow_left₀ (Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _) h2 τ
  have hCge : B c hyc * M ^ τ ≤
      ∑ c : (∀ k, ι k), if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M ^ τ else 0 := by
    have := Finset.single_le_sum (f := fun c : (∀ k, ι k) =>
        if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M ^ τ else 0)
      (fun c' _ => by
        split_ifs with hc'
        · exact mul_nonneg (hB0 c' hc') (pow_nonneg hM0 τ)
        · exact le_rfl) (Finset.mem_univ c)
    simpa only [dif_pos hyc] using this
  have hAh : 0 ≤ A.h z ^ τ := pow_nonneg (A.pos z hz.1).le τ
  calc ‖eval z (map (Int.castRingHom ℂ) g)‖
      ≤ B c hyc * ‖eval z (map (Int.castRingHom ℂ) h)‖ * ∏ k, ‖z ⟨k, c k⟩‖ ^ ((τ : ℤ) * A.a k) := h1
    _ ≤ B c hyc * ‖eval z (map (Int.castRingHom ℂ) h)‖ * (M ^ τ * A.h z ^ τ) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg (hB0 c hyc) (norm_nonneg _))
    _ = (B c hyc * M ^ τ) * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by ring
    _ ≤ (1 + ∑ c : (∀ k, ι k), if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M ^ τ else 0) *
          ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by
        have : B c hyc * M ^ τ ≤ 1 + ∑ c : (∀ k, ι k), if hc : (∀ k, y ⟨k, c k⟩ ≠ 0) then B c hc * M ^ τ else 0 := by
          linarith
        gcongr

end GlobalTheory.CompanionTheory.Ar.Plug.Count

namespace GlobalTheory.CompanionTheory.Ar.Plug.Count

theorem cmType_nonempty {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) :
    Nonempty (CMType H) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h0 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, h0]; simp
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre : (τ (H.rt : E)).re = 0 := by
    have a := congrArg Complex.re h1
    have b := congrArg Complex.im h1
    simp [sq] at a b
    by_contra hne
    have : (τ (H.rt : E)).im = 0 := by
      have : (τ (H.rt : E)).re * (τ (H.rt : E)).im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at a
    nlinarith [mul_self_nonneg (τ (H.rt : E)).re]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans H.sqrt_neg_disc_sq.symm) with h | h
  · exact ⟨⟨τ, h⟩⟩
  · refine ⟨⟨(starRingEnd ℂ).comp τ, ?_⟩⟩
    have : H.rt0 = -τ (H.rt : E) := by rw [h, neg_neg]
    rw [this]
    apply Complex.ext <;> simp [hre]

end GlobalTheory.CompanionTheory.Ar.Plug.Count

namespace GlobalTheory.CompanionTheory.Ar.Plug.Count


open MvPolynomial in
theorem charZero_of_arith {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {d : ℕ} (h : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  have hz : ∀ n : ℤ, (n : Ω) = 0 → n = 0 := by
    intro n hn
    have h1 : (C n : MRing ι) ∈ mCoordIdeal y := by
      show C n ∈ RingHom.ker (mConeMap y)
      rw [RingHom.mem_ker]
      rw [mConeMap, MvPolynomial.aeval_C, eq_intCast, ← map_intCast (MvPolynomial.C : Ω →+* MvPolynomial K Ω), hn, map_zero]
    have h2 : n ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := h1
    rw [h.2.2.1] at h2
    simpa using h2
  refine ⟨fun a b hab => ?_⟩
  have := hz ((a : ℤ) - b) (by push_cast; rw [hab, sub_self])
  omega

theorem small_shift {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {A : HermLine ι} {τ q : ℕ} {s : Ω} {c : ℝ} (hτ : 0 < τ) (hq : 0 < q) (hc : 0 < c)
    (h : GroundTheory.Heights₂.Heights.HilbertSamuel.IsBoundedH (mCoordIdeal y) y A τ c s) :
    ∃ t : ℝ, IsSmallH (mCoordIdeal y) y (Small.shiftH A (q * t)) τ s := by
  refine ⟨Real.log c / (τ * q), ?_⟩
  intro dg dh g h' z hg hh hdeg he hz
  have h0 := h dg dh g h' z hg hh hdeg he hz
  have hτ' : (τ : ℝ) ≠ 0 := by positivity
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have e1 : (Small.shiftH A ((q : ℝ) * (Real.log c / (τ * q)))).h z ^ τ = c * A.h z ^ τ := by
    show (Real.exp ((q : ℝ) * (Real.log c / (τ * q))) * A.h z) ^ τ = _
    rw [mul_pow, ← Real.exp_nat_mul]
    have : (τ : ℝ) * ((q : ℝ) * (Real.log c / (τ * q))) = Real.log c := by field_simp
    rw [this, Real.exp_log hc]
  rw [e1]
  calc _ ≤ _ := h0
    _ = _ := by ring

theorem indep_mul {Ω : Type} [Field Ω] [CharZero Ω] {r : ℕ} (v : Fin r → Ω) (hv : LinearIndependent ℚ v)
    {t : Ω} (ht : t ≠ 0) : LinearIndependent ℤ (fun i => v i * t) := by
  have h1 : LinearIndependent ℤ v :=
    hv.restrict_scalars (fun a b h => by simpa using h)
  exact h1.map' (LinearMap.mulRight ℤ t) (LinearMap.ker_eq_bot.mpr (mul_left_injective₀ ht))

end GlobalTheory.CompanionTheory.Ar.Plug.Count


open GlobalTheory.CompanionTheory.Ar.Plug.Count in
theorem GlobalTheory.CompanionTheory.Ar.Plug.many_sections : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (II : IntersectionSystem) (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ), IsFullIntersectionSystem II → T.T1 II → Top.WeightHyp T.j (reW u) g → Top.bigB0 (reW u) g < B + 1 → ∀ ε : ℝ, 0 < ε → ∃ᶠ τ : ℕ in atTop, ∃ (n : ℕ) (f : Fin n → (T.M B b).Ω), LinearIndependent ℤ f ∧ (∀ i, ∃ R, f i ∈ modelSmall (o.toTowerOrigin.Or B b) (τ • u) R) ∧ ((T.M B b).δ * (T.vol b * Top.flagDeg (reW u)) - ε) * (τ : ℝ) ^ (Top.dimFl (CMType H) (Dw.p + Dw.q)) ≤ ((Top.dimFl (CMType H) (Dw.p + Dw.q)).factorial : ℝ) * n := by
  intro hRR hG E _ _ _ H Dw l Xo c Y _ T o B b II u g hII hT1 hW hB ε hε
  have hanti : ∀ τ, StrictAnti (u τ) := fun τ a b' hab => by
    have := hW.2.1 τ a b' hab
    simpa [reW] using this
  obtain ⟨C, s, q, m, θ, hC, hs, hs0, hq, hm, hsm⟩ := GlobalTheory.T.strict_weight_growth_bound hG E H Dw l Xo c Y T o B b u hanti
  obtain ⟨hnef, hdeg, -, hpos⟩ := GlobalTheory.T.weight_threshold_limit_coefficients (CMType H) (Dw.p + Dw.q) T II B (reW u) g b s q m hII hT1 hW hB hs hs0
    (fun n => (hq n).1) hm
  have hD : 1 ≤ Top.dimFl (CMType H) (Dw.p + Dw.q) := by
    have h1 := T.j_pos
    have h2 := T.j_lt
    have hN : 2 ≤ Dw.p + Dw.q := by omega
    have h3 : 2 ≤ (Dw.p + Dw.q) * (Dw.p + Dw.q - 1) := by
      calc 2 = 2 * 1 := rfl
        _ ≤ _ := Nat.mul_le_mul hN (by omega)
    unfold Top.dimFl
    exact Nat.succ_le_of_lt (Nat.mul_pos (Fintype.card_pos_iff.mpr (cmType_nonempty H))
      (Nat.div_pos h3 two_pos))
  have hev := hdeg.eventually (lt_mem_nhds (show (T.M B b).δ * (T.vol b * Top.flagDeg (reW u)) - ε / 2 < _ by linarith))
  obtain ⟨n, hn1, hn2⟩ := (hnef.and hev).exists
  obtain ⟨P0, hP0, hsp⟩ := hn1.semipos
  have harith := (T.M B b).arith
  haveI : CharZero (T.M B b).Ω := charZero_of_arith (T.M B b).y harith
  obtain ⟨hfd, hlim⟩ := GlobalTheory.T.section_count_tendsto_geomDeg hRR hG II hII (T.M B b).K (T.M B b).ι (T.M B b).Ω (T.M B b).y
    (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Top.combLine ((T.M B b).line (Top.scale (s n))) (m n)) hD harith
    (T.M B b).birational hsp.1
    (fun W _ hW' => GroundTheory.Heights₂.Heights.HilbertSamuel.NefOnGenericOfSemipos.geomDeg_one_nonneg hP0 hsp hW')
  have hqn : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast (hq n).1
  have hqpos : (0 : ℝ) < (q n : ℝ) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) := pow_pos hqn _
  rw [lt_div_iff₀ hqpos] at hn2
  have hlt : ((T.M B b).δ * (T.vol b * Top.flagDeg (reW u)) - ε) * (q n : ℝ) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) <
      geomDeg (mCoordIdeal (T.M B b).y) (Top.combLine ((T.M B b).line (Top.scale (s n))) (m n))
        (Top.dimFl (CMType H) (Dw.p + Dw.q)) := by
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith) hqpos.le) hn2
  have hev2 := hlim.eventually (lt_mem_nhds hlt)
  rw [frequently_atTop]
  intro a
  obtain ⟨τ, hτ1, hτ2⟩ := (hev2.and (eventually_ge_atTop (a + 1))).exists
  have hτ0 : 0 < τ := by omega
  refine ⟨τ * q n, ?_, ?_⟩
  · have := Nat.le_mul_of_pos_right τ (hq n).1
    omega
  haveI := hfd τ
  obtain ⟨v, hvS, -, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq ℚ
    (chartLatNm (T.M B b).y (Top.combLine ((T.M B b).line (Top.scale (s n))) (m n)).a τ : Set (T.M B b).Ω)
  refine ⟨_, fun i => v i * θ n ^ τ, indep_mul v hli (pow_ne_zero _ (hq n).2.2), fun i => ?_, ?_⟩
  · obtain ⟨C', hC', hb⟩ := bounded_section_smooth_metric (T.M B b).y _ τ (v i) hsp.1 (hvS i)
    obtain ⟨t, ht⟩ := small_shift hτ0 (hq n).1 hC' hb
    exact ⟨_, hsm n τ t (v i) (hvS i) ht⟩
  · have hτr : (0 : ℝ) < (τ : ℝ) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) := pow_pos (by exact_mod_cast hτ0) _
    rw [lt_div_iff₀ hτr] at hτ1
    have e : (((τ * q n : ℕ) : ℝ)) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) =
        (q n : ℝ) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) * (τ : ℝ) ^ Top.dimFl (CMType H) (Dw.p + Dw.q) := by
      push_cast
      rw [mul_pow, mul_comm]
    rw [e, ← mul_assoc]
    exact hτ1.le
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullIntersectionHeightBoundStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_intersection_height_bound : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b : T.Comp) (II : IntersectionSystem) (u : GlobalTheory.AllWt.Weight Dw) (g : ℝ), IsFullIntersectionSystem II → T.T1 II → Top.WeightHyp T.j (reW u) g → Top.bigB0 (reW u) g < B + 1 → ∀ ε : ℝ, 0 < ε → ∃ᶠ τ : ℕ in atTop, ∃ (n : ℕ) (f : Fin n → (T.M B b).Ω), LinearIndependent ℤ f ∧ (∀ i, ∃ R, f i ∈ modelSmall (o.toTowerOrigin.Or B b) (τ • u) R) ∧ ((T.M B b).δ * (T.vol b * Top.flagDeg (reW u)) - ε) * (τ : ℝ) ^ (Top.dimFl (CMType H) (Dw.p + Dw.q)) ≤ ((Top.dimFl (CMType H) (Dw.p + Dw.q)).factorial : ℝ) * n := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.many_sections | exact GlobalTheory.CompanionTheory.Ar.Plug.many_sections | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.many_sections <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormHeightCount
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Plug.IndependentCountBound

open scoped ENNReal

theorem card_le_of_intIndep {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] {d n : ℕ}
    (g : Fin n → Fin d → V) (hg : LinearIndependent ℤ g) :
    (n : ℕ∞) ≤ ((Module.finrank ℚ F * d : ℕ) : ℕ∞) * Cardinal.toENat (Module.rank F V) := by
  classical
  by_cases hfin : Module.Finite F V
  · letI : Module ℚ V := Module.compHom V (algebraMap ℚ F)
    haveI : IsScalarTower ℚ F V := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    haveI : Module.Finite ℚ V := Module.Finite.trans F V
    have hq : LinearIndependent ℚ g := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hg
    have hn := hq.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_pi_fintype] at hn
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hn
    rw [← Module.finrank_mul_finrank ℚ F V] at hn
    rw [← Module.finrank_eq_rank F V, Cardinal.toENat_nat]
    have : n ≤ Module.finrank ℚ F * d * Module.finrank F V := by
      calc n ≤ _ := hn
        _ = _ := by ring
    exact_mod_cast this
  · have htop : Cardinal.toENat (Module.rank F V) = ⊤ := by
      rw [Cardinal.toENat_eq_top]
      exact not_lt.1 fun h => hfin (Module.rank_lt_aleph0_iff.1 h)
    rw [htop]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have : n = 0 := by
        by_contra hn
        have hn' : 0 < n := Nat.pos_of_ne_zero hn
        exact hg.ne_zero ⟨0, hn'⟩ (Subsingleton.elim _ _)
      simp [this]
    · have hF : 0 < Module.finrank ℚ F := Module.finrank_pos
      have : ((Module.finrank ℚ F * d : ℕ) : ℕ∞) ≠ 0 := by
        exact_mod_cast (Nat.mul_pos hF hd).ne'
      rw [ENat.mul_top this]
      exact le_top

theorem le_growth_of_frequently {D δ k₀ : ℕ} (hδ : 0 < δ) (a : ℝ) (rk : ℕ → ℕ∞)
    (H : ∀ ε : ℝ, 0 < ε → ∃ᶠ τ : ℕ in atTop, ∃ n : ℕ, ((δ : ℝ) * a - ε) * (τ : ℝ) ^ D ≤ (D.factorial : ℝ) * n ∧
      (n : ℕ∞) ≤ (δ : ℕ∞) * rk (τ + k₀)) :
    ENNReal.ofReal a ≤ GlobalTheory.CompHt.growth D rk := by
  by_contra hlt
  obtain ⟨c, h1, h2⟩ := exists_between (not_le.1 hlt)
  have hctop : c ≠ ⊤ := ne_top_of_lt h2
  have hc0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  have hcc : ENNReal.ofReal c.toReal = c := ENNReal.ofReal_toReal hctop
  have hca : c.toReal < a := (ENNReal.lt_ofReal_iff_toReal_lt hctop).1 h2
  set c' := c.toReal with hc'
  set b := (c' + a) / 2 with hb
  have hb1 : c' < b := by rw [hb]; linarith
  have hb2 : b < a := by rw [hb]; linarith
  have hbpos : 0 < b := lt_of_le_of_lt hc0 hb1
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hε : 0 < (δ : ℝ) * (a - b) := mul_pos hδ' (by linarith)
  have hlim : Tendsto (fun τ : ℕ => ((τ : ℝ) / ((τ : ℝ) + (k₀ : ℝ))) ^ D) atTop (𝓝 1) := by
    simpa using (tendsto_natCast_div_add_atTop (k₀ : ℝ)).pow D
  have hev : ∀ᶠ τ : ℕ in atTop, c' / b < ((τ : ℝ) / ((τ : ℝ) + (k₀ : ℝ))) ^ D :=
    hlim.eventually_const_lt ((div_lt_one hbpos).2 hb1)
  have hfr := ((H _ hε).and_eventually (hev.and (eventually_gt_atTop 0)))
  have hfr' : ∃ᶠ τ' : ℕ in atTop, c ≤ (D.factorial : ℝ≥0∞) * (rk τ' : ℝ≥0∞) / (τ' : ℝ≥0∞) ^ D := by
    refine (tendsto_add_atTop_nat k₀).frequently (hfr.mono ?_)
    rintro τ ⟨⟨n, hn1, hn2⟩, hn3, hn4⟩
    have hτ : (0 : ℝ) < τ := by exact_mod_cast hn4
    have hτ' : (0 : ℝ) < (τ : ℝ) + k₀ := by positivity
    have hne0 : (((τ + k₀ : ℕ) : ℝ≥0∞)) ^ D ≠ 0 := by
      have : ((τ + k₀ : ℕ) : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast (by omega : τ + k₀ ≠ 0)
      exact pow_ne_zero _ this
    have hnet : (((τ + k₀ : ℕ) : ℝ≥0∞)) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
    rw [ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl hnet)]
    cases hr : rk (τ + k₀) with
    | top =>
      have hf : (D.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast D.factorial_ne_zero
      simp [ENNReal.mul_top hf]
    | coe m =>
      rw [hr] at hn2
      have hnm : n ≤ δ * m := by exact_mod_cast hn2
      have hnm' : (n : ℝ) ≤ δ * m := by exact_mod_cast hnm
      have e1 : ((δ : ℝ) * a - (δ : ℝ) * (a - b)) = δ * b := by ring
      rw [e1] at hn1
      have hfac : (0 : ℝ) < D.factorial := by exact_mod_cast D.factorial_pos
      have h3 : (δ : ℝ) * (b * (τ : ℝ) ^ D) ≤ δ * ((D.factorial : ℝ) * m) := by
        calc (δ : ℝ) * (b * (τ : ℝ) ^ D) = δ * b * (τ : ℝ) ^ D := by ring
          _ ≤ (D.factorial : ℝ) * n := hn1
          _ ≤ (D.factorial : ℝ) * (δ * m) := by gcongr
          _ = _ := by ring
      have h4 : b * (τ : ℝ) ^ D ≤ (D.factorial : ℝ) * m := le_of_mul_le_mul_left h3 hδ'
      have h5 : c' * ((τ : ℝ) + k₀) ^ D ≤ b * (τ : ℝ) ^ D := by
        rw [div_pow, div_lt_div_iff₀ hbpos (pow_pos hτ' D)] at hn3
        nlinarith [hn3]
      have hreal : c' * (((τ + k₀ : ℕ) : ℝ)) ^ D ≤ (D.factorial : ℝ) * m := by
        push_cast
        exact h5.trans h4
      have := ENNReal.ofReal_le_ofReal hreal
      rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, hcc] at this
      simpa using this
  have : c ≤ GlobalTheory.CompHt.growth D rk := Filter.le_limsup_of_frequently_le hfr'
  exact absurd h1 (not_lt.2 this)

section Step

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}

theorem modelSmall_mono (Or : RootOrigin Y S RM Fx) (u : GlobalTheory.AllWt.Weight Dw) {R R' : ℝ} (hR : R ≤ R') :
    modelSmall Or u R ⊆ modelSmall Or u R' := by
  rintro s ⟨h1, w, hw, h2⟩
  refine ⟨h1, w, hw, fun z hz hne val hval => (h2 z hz hne val hval).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hR
    (Finset.prod_nonneg fun r _ => (zpow_pos ((Or.sing r).pos z hz.1) _).le)

variable {Or : RootOrigin Y S RM Fx} {Fr : Small.GenFrame Or} {h : GenFrEx Xo c} {Z : Comp Xo c}

def trHom (Rd : Reading Fr h Z) (v : GlobalTheory.AllWt.Weight Dw) : RM.Ω →+ Om Z where
  toFun := trOf Rd v
  map_zero' := by simp [trOf]
  map_add' s t := by simp [trOf, add_div]

set_option synthInstance.maxHeartbeats 400000 in
theorem card_le_rank (G : Top.Given) {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c}
    {e : Comp Xo c → Rul Xo c} (hL : CompLaws U h e) {x : ℝ}
    (hx : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x)
    {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} [DecidableEq (CMType H)]
    {T : Top.RootTower (CMType H) (Dw.p + Dw.q)} (o : Top.GoodOrigin Y T) {B : ℕ} {b : T.Comp}
    {Fr : Small.GenFrame (o.toTowerOrigin.Or B b)} {Z : Comp Xo c} (Rd : Reading Fr h Z) (hGeo : GeoRead Rd)
    (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) {u : GlobalTheory.AllWt.Weight Dw} (hu : ∀ τ, StrictAnti (u τ))
    {k₀ τ : ℕ} (hτ : 0 < τ + k₀) {R₀ : ℝ} (hR₀ : 0 < R₀)
    {f : Fin (o.toTowerOrigin.Or B b).Fl.deg → (T.M B b).Ω}
    (hf : ∀ i, f i ∈ modelSmall (o.toTowerOrigin.Or B b) (k₀ • u) R₀)
    (hinj : ∀ (v : GlobalTheory.AllWt.Weight Dw) (s : (T.M B b).Ω), (∀ i, trOf Rd v (s * f i) = 0) → s = 0)
    {n : ℕ} {f' : Fin n → (T.M B b).Ω} (hli : LinearIndependent ℤ f')
    (hsm : ∀ i, ∃ R, f' i ∈ modelSmall (o.toTowerOrigin.Or B b) (τ • u) R) :
    (n : ℕ∞) ≤ ((T.M B b).δ : ℕ∞) *
      Cardinal.toENat (Module.rank c.F (GlobalTheory.AllWt.cuspOn U Z ((τ + k₀) • GlobalTheory.AllWt.wtOf Dw u 0))) := by
  classical
  have hvu : (τ + k₀) • GlobalTheory.AllWt.wtOf Dw u 0 = GlobalTheory.AllWt.wtOf Dw ((τ + k₀) • u) 0 :=
    (GlobalTheory.T.tower_weight_of_zero E H Dw l Xo c (T.M B b) u).2.2.1 _
  rw [hvu, (o.toTowerOrigin.Or B b).δ_eq]
  set v : GlobalTheory.AllWt.Weight Dw := (τ + k₀) • u with hv
  have hvanti : ∀ t, StrictAnti (v t) := by
    intro t i j hij
    have h1 := hu t hij
    have h2 : (0 : ℤ) < ((τ + k₀ : ℕ) : ℤ) := by exact_mod_cast hτ
    simp only [hv, Pi.smul_apply, nsmul_eq_mul]
    exact mul_lt_mul_of_pos_left h1 h2
  have key : ∀ j i, ∃ g ∈ GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw v 0), evC h Z g = trOf Rd v (f' j * f i) := by
    intro j i
    obtain ⟨R, hR⟩ := hsm j
    have hR' := modelSmall_mono (o.toTowerOrigin.Or B b) (τ • u) (le_max_left R 0) hR
    have hm : f' j * f i ∈ modelSmall (o.toTowerOrigin.Or B b) v (max R 0 * R₀) := by
      have := GlobalTheory.T.model_small_sections_mul E H Dw l Xo c Y T o B b (τ • u) (k₀ • u) (max R 0) R₀ (le_max_right _ _) hR₀.le _ hR' _ (hf i)
      rwa [← add_smul] at this
    obtain ⟨g, hg1, hg2, hg3⟩ := GlobalTheory.T.comp_laws_tower_bound G E H Dw l Xo c r U h e hL Y T o B b Fr Z Rd hGeo v _ hm.1
    refine ⟨g, ?_, hg3⟩
    refine GlobalTheory.T.weight_zero_section_membership E H Dw l Xo c r U h e hL hp hq x Z v hvanti g hg1 hg2 fun σ hσ => ⟨_, fun z hz =>
      GlobalTheory.T.uniform_norm_tower_bound G E H Dw l Xo c r U h e hL x hx Y T o B b Fr Z Rd hGeo v _ _
        (mul_nonneg (le_max_right _ _) hR₀.le) hm.2 g hg1 hg3 σ hσ z hz⟩
  choose g hg hgev using key
  let Gm : Fin n → Fin (o.toTowerOrigin.Or B b).Fl.deg → GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw v 0) :=
    fun j i => ⟨g j i, hg j i⟩
  have hli' : LinearIndependent ℤ Gm := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    refine (Fintype.linearIndependent_iff.1 hli) a (hinj v _ fun i => ?_)
    have h1 : ∑ j, a j • g j i = 0 := by
      have := congrArg (fun w => ((w i : GlobalTheory.AllWt.cuspOn U Z (GlobalTheory.AllWt.wtOf Dw v 0)) : Rul Xo c)) ha
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [Gm] using this
    have h2 : (∑ j, a j • f' j) * f i = ∑ j, a j • (f' j * f i) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => smul_mul_assoc _ _ _
    have h3 := congrArg (evCAlg h hL.genT Z) h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at h3
    show trHom Rd v _ = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum, ← h3]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, map_zsmul]
    exact congrArg (a j • ·) (hgev j i).symm
  have := card_le_of_intIndep (F := c.F) Gm hli'
  exact this

end Step

set_option synthInstance.maxHeartbeats 400000 in
theorem vol_mul_flagDeg_le_growthOn : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → ∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → ENNReal.ofReal (T.vol (κ Z) * Top.flagDeg (reW u)) ≤ GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) := by
  intro hRR G E _ _ _ H Dw l Xo c r U h e hL x hx Y _ T o κ II hκ hII _ hT1 Z u hu
  have hj := o.toTowerOrigin.j_eq
  have hp : 1 ≤ Dw.p := hj ▸ T.j_pos
  have hq : 1 ≤ Dw.q := by
    have := T.j_lt
    omega
  have hW := GlobalTheory.T.tower_weight_of_zero E H Dw l Xo c (T.M 0 (κ Z)) u
  have hdim : GlobalTheory.CompHt.dimFlag Dw = Top.dimFl (CMType H) (Dw.p + Dw.q) := hW.2.2.2.2.2.1
  have hWH : Top.WeightHyp T.j (reW u) 1 := by
    rw [hj]
    exact hW.2.2.2.2.2.2.2.1 hp hq hu
  have hB : Top.bigB0 (reW u) 1 < (⌈Top.bigB0 (reW u) 1⌉₊ : ℝ) + 1 :=
    (Nat.le_ceil _).trans_lt (lt_add_one _)
  obtain ⟨Fr, Rd, hGeo⟩ := GlobalTheory.T.tower_origin_component_bound E H Dw l Xo c r U h e hL Y T o.toTowerOrigin κ hκ ⌈Top.bigB0 (reW u) 1⌉₊ Z
  obtain ⟨k₀, R₀, f, -, hR₀, hf, -, hinj⟩ :=
    GlobalTheory.T.generic_frame_component_bound G E H Dw l Xo c h Y T o _ (κ Z) Fr Z Rd II u 1 hII hT1 hWH hB
  have main := le_growth_of_frequently (D := Top.dimFl (CMType H) (Dw.p + Dw.q)) (k₀ := k₀)
    (T.M ⌈Top.bigB0 (reW u) 1⌉₊ (κ Z)).δ_pos (T.vol (κ Z) * Top.flagDeg (reW u))
    (fun τ => Cardinal.toENat (Module.rank c.F (GlobalTheory.AllWt.cuspOn U Z (τ • GlobalTheory.AllWt.wtOf Dw u 0)))) (fun ε hε => by
      refine ((GlobalTheory.T.full_intersection_height_bound hRR G E H Dw l Xo c Y T o _ (κ Z) II u 1 hII hT1 hWH hB ε hε).and_eventually
        (eventually_gt_atTop 0)).mono ?_
      rintro τ ⟨⟨n, f', hli, hsm, hle⟩, hτ⟩
      exact ⟨n, hle, card_le_rank G hL hx o Rd hGeo hp hq hu (by omega) hR₀ hf hinj hli hsm⟩)
  rw [GlobalTheory.CompHt.growthOn, hdim]
  exact main

end GlobalTheory.CompanionTheory.Ar.Plug.IndependentCountBound


set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.uniform_norm_height_count : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → ∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → ENNReal.ofReal (T.vol (κ Z) * Top.flagDeg (reW u)) ≤ GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) :=
  GlobalTheory.CompanionTheory.Ar.Plug.IndependentCountBound.vol_mul_flagDeg_le_growthOn
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormHeightCountStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_norm_height_count : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → ∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → ENNReal.ofReal (T.vol (κ Z) * Top.flagDeg (reW u)) ≤ GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.uniform_norm_height_count | exact GlobalTheory.CompanionTheory.Relay.uniform_norm_height_count | (intros; apply GlobalTheory.CompanionTheory.Relay.uniform_norm_height_count <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSectionsCuspLaws
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSectionsCuspLaws
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.lattice_sections_cusp_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (a : WZ E) (x : ℝ), (Lat.secZ Xo c a 0 = secZ Xo c a ∧ Lat.cuspZ U a 0 = cuspZ Xo c U a ∧ Lat.lieZ Dw x a = lieFacZ Dw x a ∧ ∀ f, f ∈ Lat.latZ U a 0 ↔ f ∈ cuspZ Xo c U a ∧ ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) ∧ ∀ b, WEq Dw a b → secZ Xo c a = secZ Xo c b ∧ cuspZ Xo c U a = cuspZ Xo c U b ∧ lieFacZ Dw x a = lieFacZ Dw x b ∧ towerWt Dw a = towerWt Dw b ∧ (∀ σ, GoodEmb c σ → laZ (U σ) a = laZ (U σ) b) ∧ ∀ Z, cuspOn U h a Z = cuspOn U h b Z ∧ latOn U h a Z = latOn U h b Z := by
  first | exact @PositivityTheory.UnitarySelfGeneration.y_br_lat | exact PositivityTheory.UnitarySelfGeneration.y_br_lat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSectionsCuspLawsStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_sections_cusp_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (a : WZ E) (x : ℝ), (Lat.secZ Xo c a 0 = secZ Xo c a ∧ Lat.cuspZ U a 0 = cuspZ Xo c U a ∧ Lat.lieZ Dw x a = lieFacZ Dw x a ∧ ∀ f, f ∈ Lat.latZ U a 0 ↔ f ∈ cuspZ Xo c U a ∧ ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) ∧ ∀ b, WEq Dw a b → secZ Xo c a = secZ Xo c b ∧ cuspZ Xo c U a = cuspZ Xo c U b ∧ lieFacZ Dw x a = lieFacZ Dw x b ∧ towerWt Dw a = towerWt Dw b ∧ (∀ σ, GoodEmb c σ → laZ (U σ) a = laZ (U σ) b) ∧ ∀ Z, cuspOn U h a Z = cuspOn U h b Z ∧ latOn U h a Z = latOn U h b Z := by
  first | exact @GlobalTheory.CompanionTheory.Relay.lattice_sections_cusp_laws | exact GlobalTheory.CompanionTheory.Relay.lattice_sections_cusp_laws | (intros; apply GlobalTheory.CompanionTheory.Relay.lattice_sections_cusp_laws <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormDegreeBound
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
namespace GlobalTheory.CompanionTheory.Ar.Plug.TopGrowth

theorem exists_intWeight_of_regDominant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : WZ E), Top.RegDominant (towerWt Dw a) → ∃ u : GlobalTheory.AllWt.Weight Dw, (∀ τ, StrictAnti (u τ)) ∧ reW u = towerWt Dw a ∧ WEq Dw a (GlobalTheory.AllWt.wtOf Dw u 0).1 := by
  intro E _ _ _ H Dw a ha
  classical
  let u : GlobalTheory.AllWt.Weight Dw := fun τ n =>
    if (n : ℕ) < Dw.p then a (τ.1, (n : ℕ)) else -a (conjEmb τ.1, Dw.p + Dw.q - 1 - (n : ℕ))
  have hre : reW u = towerWt Dw a := by
    funext τ n
    simp only [reW, towerWt, u]
    split_ifs <;> push_cast <;> rfl
  refine ⟨u, fun τ i j hij => ?_, hre, ?_⟩
  · have := ha τ i j hij
    rw [← hre] at this
    simpa [reW] using this
  · intro τ i hi
    by_cases h : τ (H.rt : E) = H.rt0
    · have hp : i < Dw.p := by simpa [Datum.mult, h] using hi
      simp [GlobalTheory.AllWt.wtOf, h, hp, u]
    · have hq : i < Dw.q := by simpa [Datum.mult, h] using hi
      have h' : conjEmb τ (H.rt : E) = H.rt0 := Small.conjEmb_rt_of_ne h
      have hidx : Dw.p + Dw.q - 1 - (Dw.p + (Dw.q - 1 - i)) = i := by omega
      have hnp : ¬ Dw.p + (Dw.q - 1 - i) < Dw.p := by omega
      simp [GlobalTheory.AllWt.wtOf, h, h', hq, u, hnp, hidx, GlobalTheory.AllWt.conjEmb_conjEmb]

theorem limsup_real_eq_of_growth : ∀ (D : ℕ) (r : ℕ → ℕ∞) (t : ℝ), 0 ≤ t → limsup (fun n : ℕ => (D.factorial : ENNReal) * (r n : ENNReal) / (n : ENNReal) ^ D) atTop = ENNReal.ofReal t → limsup (fun n : ℕ => (D.factorial : ℝ) * ((r n).toNat : ℝ) / (n : ℝ) ^ D) atTop = t := by
  intro D r t ht hlim
  have hb : ENNReal.ofReal t + 1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.one_ne_top⟩
  have hev : ∀ᶠ n : ℕ in atTop, (D.factorial : ENNReal) * (r n : ENNReal) / (n : ENNReal) ^ D < ENNReal.ofReal t + 1 :=
    eventually_lt_of_limsup_lt (by rw [hlim]; exact ENNReal.lt_add_right ENNReal.ofReal_ne_top one_ne_zero)
  have heq : (fun n : ℕ => (D.factorial : ℝ) * ((r n).toNat : ℝ) / (n : ℝ) ^ D) =ᶠ[atTop]
      fun n : ℕ => ((D.factorial : ENNReal) * (r n : ENNReal) / (n : ENNReal) ^ D).toReal := by
    filter_upwards [hev, eventually_ge_atTop 1] with n hn h1
    have hfin : r n ≠ ⊤ := by
      intro hr
      have hD : (D.factorial : ENNReal) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero D
      have hpow : (n : ENNReal) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top n)
      rw [hr, ENat.toENNReal_top, ENNReal.mul_top hD, ENNReal.top_div_of_ne_top hpow] at hn
      exact absurd hn (not_lt.2 le_top)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← hm]
    simp [ENNReal.toReal_div, ENNReal.toReal_mul]
  rw [limsup_congr heq, ENNReal.limsup_toReal_eq hb (hev.mono fun n hn => hn.le), hlim, ENNReal.toReal_ofReal ht]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem flagDeg_reW_eq [DecidableEq (CMType H)] : ∃ C : ℝ, ∀ u : GlobalTheory.AllWt.Weight Dw,
    Top.flagDeg (reW u) = C * ((GlobalTheory.CompHt.vdm u : ℤ) : ℝ) := by
  refine ⟨((Top.dimFl (CMType H) (Dw.p + Dw.q)).factorial : ℝ) * ∏ _τ : CMType H, ∏ i : Fin (Dw.p + Dw.q),
    ∏ k : Fin (Dw.p + Dw.q), (if i < k then ((k : ℝ) - (i : ℝ))⁻¹ else 1), fun u => ?_⟩
  have hv : ((GlobalTheory.CompHt.vdm u : ℤ) : ℝ) = GlobalTheory.CompHt.vdm (fun τ i => (u τ i : ℝ)) := by
    simpa using GlobalTheory.CompHt.map_vdm (Int.castRingHom ℝ) u
  rw [(Top.flagDeg_eq_weyl _ _ (reW u)).1, mul_assoc, hv]
  congr 1
  unfold GlobalTheory.CompHt.vdm
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have : Finset.Ioi i = Finset.univ.filter (fun k : Fin (Dw.p + Dw.q) => i < k) := by ext b; simp
  rw [this, Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  split_ifs
  · simp [reW, div_eq_mul_inv, mul_comm]
  · simp

theorem flagDeg_reW_mul [DecidableEq (CMType H)] (u v : GlobalTheory.AllWt.Weight Dw) :
    Top.flagDeg (reW u) * ((GlobalTheory.CompHt.vdm v : ℤ) : ℝ) = Top.flagDeg (reW v) * ((GlobalTheory.CompHt.vdm u : ℤ) : ℝ) := by
  obtain ⟨C, hC⟩ := flagDeg_reW_eq (Dw := Dw)
  rw [hC u, hC v]; ring

theorem regDominant_reW [DecidableEq (CMType H)] {u : GlobalTheory.AllWt.Weight Dw} (hu : ∀ τ, StrictAnti (u τ)) :
    Top.RegDominant (reW u) := fun τ a b hab => by
  simpa [reW] using (Int.cast_lt (R := ℝ)).2 (hu τ hab)

theorem vdm_inst (la : GlobalTheory.AllWt.Weight Dw) :
    @GlobalTheory.CompHt.vdm _ GlobalTheory.CompHt.fintypePsi _ ℤ _ la = GlobalTheory.CompHt.vdm la := by
  first | rfl | convert rfl | congr 1

theorem dimFlag_eq [DecidableEq (CMType H)] :
    GlobalTheory.CompHt.dimFlag Dw = Top.dimFl (CMType H) (Dw.p + Dw.q) := by
  simp only [GlobalTheory.CompHt.dimFlag, Formalism.DegreeFormula.dimFl, Top.dimFl]
  first | rfl | (congr 1; convert rfl) | convert rfl

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
theorem volL_eq_of_growth [DecidableEq (CMType H)] {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c}
    {e : Comp Xo c → Rul Xo c} (hL : CompLaws U h e) (Z : Comp Xo c) (a : WZ E) (u : GlobalTheory.AllWt.Weight Dw)
    (hW : WEq Dw a (GlobalTheory.AllWt.wtOf Dw u 0).1) {t : ℝ} (ht : 0 ≤ t)
    (hg : GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) = ENNReal.ofReal t) :
    volL U h a Z (Top.dimFl (CMType H) (Dw.p + Dw.q)) = t := by
  have hG0 : GlobalTheory.AllWt.wtOf Dw u 0 = ((GlobalTheory.AllWt.wtOf Dw u 0).1, 0) := Prod.ext rfl (by simp [GlobalTheory.AllWt.wtOf_snd])
  have hcusp : ∀ n : ℕ, cuspOn U h (n • a) Z = GlobalTheory.AllWt.cuspOn U Z (n • GlobalTheory.AllWt.wtOf Dw u 0) := by
    intro n
    have hWn : WEq Dw (n • a) (n • (GlobalTheory.AllWt.wtOf Dw u 0).1) := fun τ i hi => by simp [hW τ i hi]
    rw [(((GlobalTheory.T.lattice_sections_cusp_laws E H Dw l Xo c r U h e hL (n • a) 0).2 _ hWn).2.2.2.2.2 Z).1,
      (GlobalTheory.T.all_weight_sections_compat E H Dw l Xo c r U h e hL (n • (GlobalTheory.AllWt.wtOf Dw u 0).1) Z).2.2.1]
    conv_rhs => rw [hG0]
    rw [Prod.smul_mk, smul_zero]
  have hfun : (fun n : ℕ => ((Top.dimFl (CMType H) (Dw.p + Dw.q)).factorial : ℝ) *
      (Module.finrank c.F (cuspOn U h (n • a) Z) : ℝ) / (n : ℝ) ^ Top.dimFl (CMType H) (Dw.p + Dw.q)) =
      fun n : ℕ => ((GlobalTheory.CompHt.dimFlag Dw).factorial : ℝ) *
      ((Cardinal.toENat (Module.rank c.F (GlobalTheory.AllWt.cuspOn U Z (n • GlobalTheory.AllWt.wtOf Dw u 0)))).toNat : ℝ) /
        (n : ℝ) ^ GlobalTheory.CompHt.dimFlag Dw := by
    funext n; rw [hcusp n, ← dimFlag_eq]; simp [Module.finrank]
  show limsup _ atTop = t
  rw [hfun]
  exact limsup_real_eq_of_growth _ _ _ ht hg

end GlobalTheory.CompanionTheory.Ar.Plug.TopGrowth

namespace GlobalTheory.CompanionTheory.Ar.Plug


open TopGrowth in
theorem topGrowth : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → (∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) = ENNReal.ofReal (GlobalTheory.CompHt.topDeg U Z u) ∧ GlobalTheory.CompHt.topDeg U Z u = T.vol (κ Z) * Top.flagDeg (reW u) ∧ 0 < GlobalTheory.CompHt.topDeg U Z u) ∧ (∀ Z, 0 < GlobalTheory.CompHt.vZero U Z) ∧ (T.VolEq → ∀ Z Z', GlobalTheory.CompHt.vZero U Z = GlobalTheory.CompHt.vZero U Z') ∧ ∀ (Z : Comp Xo c) (a : WZ E), Top.RegDominant (towerWt Dw a) → volL U h a Z (Top.dimFl (CMType H) (Dw.p + Dw.q)) = T.vol (κ Z) * Top.flagDeg (towerWt Dw a) := by
  intro hRR hG E _ _ _ H Dw l Xo c r U h e hL x hx Y _ T o κ II hC hF hP hT1
  have hgr : ∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) →
      GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) = ENNReal.ofReal (T.vol (κ Z) * Top.flagDeg (reW u)) :=
    fun Z u hu => le_antisymm
      (GlobalTheory.T.growthOn_le_vol_mul_flagDeg hRR hG E H Dw l Xo c r U h e hL x hx Y T o κ II hC hF hP hT1 Z u hu)
      (GlobalTheory.T.uniform_norm_height_count hRR hG E H Dw l Xo c r U h e hL x hx Y T o κ II hC hF hP hT1 Z u hu)
  have hfd : ∀ u : GlobalTheory.AllWt.Weight Dw, (∀ τ, StrictAnti (u τ)) → 0 < Top.flagDeg (reW u) :=
    fun u hu => (Top.flagDeg_eq_weyl _ _ _).2.1 (TopGrowth.regDominant_reW hu)
  have hvol : ∀ Z, 0 < T.vol (κ Z) := fun Z => hP.1 _
  have hs : ∀ τ, StrictAnti ((GlobalTheory.CompHt.stdWt (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) : GlobalTheory.AllWt.Weight Dw) τ) :=
    fun τ => GlobalTheory.CompHt.strictAnti_stdWt τ
  have hvs : (0 : ℝ) < ((GlobalTheory.CompHt.vdm (GlobalTheory.CompHt.stdWt (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) : GlobalTheory.AllWt.Weight Dw) : ℤ) : ℝ) :=
    Int.cast_pos.2 (GlobalTheory.CompHt.vdm_pos hs)
  have hvZ : ∀ Z, GlobalTheory.CompHt.vZero U Z = T.vol (κ Z) *
      Top.flagDeg (reW (GlobalTheory.CompHt.stdWt (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) : GlobalTheory.AllWt.Weight Dw)) /
      ((GlobalTheory.CompHt.vdm (GlobalTheory.CompHt.stdWt (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) : GlobalTheory.AllWt.Weight Dw) : ℤ) : ℝ) := by
    intro Z
    rw [GlobalTheory.CompHt.vZero, hgr Z _ hs, ENNReal.toReal_ofReal (mul_pos (hvol Z) (hfd _ hs)).le, TopGrowth.vdm_inst]
  have htop : ∀ Z (u : GlobalTheory.AllWt.Weight Dw), GlobalTheory.CompHt.topDeg U Z u = T.vol (κ Z) * Top.flagDeg (reW u) := by
    intro Z u
    have hr := TopGrowth.flagDeg_reW_mul u (GlobalTheory.CompHt.stdWt (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) : GlobalTheory.AllWt.Weight Dw)
    rw [GlobalTheory.CompHt.topDeg, TopGrowth.vdm_inst, hvZ Z, div_mul_eq_mul_div, div_eq_iff hvs.ne']
    linear_combination (-(T.vol (κ Z))) * hr
  refine ⟨fun Z u hu => ⟨?_, htop Z u, ?_⟩, fun Z => ?_, fun hV Z Z' => ?_, fun Z a ha => ?_⟩
  · rw [hgr Z u hu, htop Z u]
  · rw [htop Z u]; exact mul_pos (hvol Z) (hfd u hu)
  · rw [hvZ Z]; exact div_pos (mul_pos (hvol Z) (hfd _ hs)) hvs
  · rw [hvZ Z, hvZ Z', hV (κ Z) (κ Z')]
  · obtain ⟨u, hu, hreW, hW⟩ := TopGrowth.exists_intWeight_of_regDominant E H Dw a ha
    have hgrowth := hgr Z u hu
    rw [hreW] at hgrowth
    exact TopGrowth.volL_eq_of_growth hL Z a u hW (mul_pos (hvol Z) ((Top.flagDeg_eq_weyl _ _ _).2.1 ha)).le hgrowth

end GlobalTheory.CompanionTheory.Ar.Plug
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniformNormDegreeBoundStatement
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_norm_degree_bound : GlobalTheory.CompanionTheory.Ar.Pub.NefRR → Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ x : ℝ, (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = x) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp) (II : IntersectionSystem), CompOf o.toTowerOrigin κ → IsFullIntersectionSystem II → T.Proportional → T.T1 II → (∀ (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw), (∀ τ, StrictAnti (u τ)) → GlobalTheory.CompHt.growthOn U Z (GlobalTheory.AllWt.wtOf Dw u 0) = ENNReal.ofReal (GlobalTheory.CompHt.topDeg U Z u) ∧ GlobalTheory.CompHt.topDeg U Z u = T.vol (κ Z) * Top.flagDeg (reW u) ∧ 0 < GlobalTheory.CompHt.topDeg U Z u) ∧ (∀ Z, 0 < GlobalTheory.CompHt.vZero U Z) ∧ (T.VolEq → ∀ Z Z', GlobalTheory.CompHt.vZero U Z = GlobalTheory.CompHt.vZero U Z') ∧ ∀ (Z : Comp Xo c) (a : WZ E), Top.RegDominant (towerWt Dw a) → volL U h a Z (Top.dimFl (CMType H) (Dw.p + Dw.q)) = T.vol (κ Z) * Top.flagDeg (towerWt Dw a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Plug.topGrowth | exact GlobalTheory.CompanionTheory.Ar.Plug.topGrowth | (intros; apply GlobalTheory.CompanionTheory.Ar.Plug.topGrowth <;> assumption)
end
