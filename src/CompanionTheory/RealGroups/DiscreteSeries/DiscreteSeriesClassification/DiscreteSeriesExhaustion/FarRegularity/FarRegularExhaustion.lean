module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InjROfVanKG
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InjUOfInjR
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EvaluationLiftDegreeZero
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SubChar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasApplyOfScalChar
open scoped InnerProductSpace
open Formalism.REAL (GlRel IsUnitary KHighest Cas etr epow)

namespace GlobalTheory.CompanionTheory.RgExhUnit

theorem etr_two_eq_cas {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) : etr E 2 = Cas E := by
  simp [etr, Cas, epow]

theorem cas_apply_of_scalChar {n : ℕ} (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (χ : Fin n → ℂ)
    (hS : CompanionTheory.RgExh.ScalChar ⟨V, E, hE⟩ χ) (u : V) :
    Cas E u = (∑ a, χ a * χ a -
      ∑ a, ((Formalism.QuantumDeterminants.rhoStd n a : ℝ) : ℂ) * ((Formalism.QuantumDeterminants.rhoStd n a : ℝ) : ℂ)) • u := by
  rcases n with _ | m
  · simp [Cas]
  · have h := GlobalTheory.CompanionTheory.CapelliGelfand.etr_eq_gelfVal_of_capelli V m E χ u hE
      (fun Y => by
        have := LinearMap.congr_fun (hS Y) u
        simpa using this) 2
    rw [etr_two_eq_cas, GlobalTheory.CasimirEigen.gelfVal_two_eq] at h
    exact h

theorem re_sum_mul_self {n : ℕ} (χ : Fin n → ℂ) :
    (∑ a, χ a * χ a).re = ∑ a, ((χ a).re ^ 2 - (χ a).im ^ 2) := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Complex.mul_re, sq]

theorem unitIneq : CompanionTheory.RgExh.U.UnitIneq := by
  intro n
  refine ⟨∑ a, Formalism.QuantumDeterminants.rhoStd n a * Formalism.QuantumDeterminants.rhoStd n a, ?_⟩
  intro ε V _ _ E hE χ γ u hU hS hu hK
  have h1 := Formalism.REAL.wdCas V n ε E γ u hE hU hK
  have hin : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [cas_apply_of_scalChar V E hE χ hS u, inner_smul_right, hin] at h1
  have h2 := congrArg Complex.re h1
  have hpos : 0 < ‖u‖ ^ 2 := by positivity
  have hsum : 0 ≤ ∑ a, ∑ b, (if ε a = ε b then 0 else ‖E a b u‖ ^ 2) := by
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    split_ifs <;> positivity
  have hrho : (∑ a, ((Formalism.QuantumDeterminants.rhoStd n a : ℝ) : ℂ) * ((Formalism.QuantumDeterminants.rhoStd n a : ℝ) : ℂ)).re =
      ∑ a, Formalism.QuantumDeterminants.rhoStd n a * Formalism.QuantumDeterminants.rhoStd n a := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Complex.mul_re]
  have hc : (∑ a, ((χ a).re ^ 2 - (χ a).im ^ 2) - ∑ a, Formalism.QuantumDeterminants.rhoStd n a * Formalism.QuantumDeterminants.rhoStd n a) * ‖u‖ ^ 2 =
      (Formalism.REAL.nsq (γ + Formalism.REAL.rhoC ε) - Formalism.REAL.nsq (Formalism.REAL.rhoC ε)) * ‖u‖ ^ 2 -
        ∑ a, ∑ b, (if ε a = ε b then 0 else ‖E a b u‖ ^ 2) := by
    rw [Complex.re_mul_ofReal, Complex.ofReal_re, Complex.sub_re, re_sum_mul_self, hrho] at h2
    exact h2
  have hnn : 0 ≤ Formalism.REAL.nsq (Formalism.REAL.rhoC ε) := by
    show 0 ≤ ∑ a, Formalism.REAL.rhoC ε a * Formalism.REAL.rhoC ε a
    exact Finset.sum_nonneg fun a _ => mul_self_nonneg _
  have hle : ∑ a, ((χ a).re ^ 2 - (χ a).im ^ 2) - ∑ a, Formalism.QuantumDeterminants.rhoStd n a * Formalism.QuantumDeterminants.rhoStd n a ≤
      Formalism.REAL.nsq (γ + Formalism.REAL.rhoC ε) - Formalism.REAL.nsq (Formalism.REAL.rhoC ε) := by
    refine le_of_mul_le_mul_right ?_ hpos
    rw [hc]
    linarith
  show _ ≤ Formalism.REAL.nsq (γ + Formalism.REAL.rhoC ε) + _
  linarith

end GlobalTheory.CompanionTheory.RgExhUnit
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TotalBound
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExhFar

open CompanionTheory.RgExh.U

theorem x_bound {ι : Type*} (s : Finset ι) (x y : ι → ℝ) (a0 : ι) (h0 : a0 ∈ s) (B M K : ℝ) (hK0 : 0 ≤ K)
    (hy : ∀ a ∈ s, |y a| ≤ B) (hM : ∀ a ∈ s, |x a0 - x a| ≤ M) (hK : |∑ a ∈ s, (y a - x a)| ≤ K) :
    |x a0| ≤ B + M + K := by
  have hm : (1 : ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨a0, h0⟩
  have e : (s.card : ℝ) * x a0 = ∑ a ∈ s, y a - ∑ a ∈ s, (y a - x a) + ∑ a ∈ s, (x a0 - x a) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have h1 : |∑ a ∈ s, y a| ≤ (s.card : ℝ) * B := by
    calc |∑ a ∈ s, y a| ≤ ∑ a ∈ s, |y a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ s, B := Finset.sum_le_sum hy
      _ = (s.card : ℝ) * B := by simp
  have h2 : |∑ a ∈ s, (x a0 - x a)| ≤ (s.card : ℝ) * M := by
    calc |∑ a ∈ s, (x a0 - x a)| ≤ ∑ a ∈ s, |x a0 - x a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ s, M := Finset.sum_le_sum hM
      _ = (s.card : ℝ) * M := by simp
  have h3 : (s.card : ℝ) * |x a0| ≤ (s.card : ℝ) * B + K + (s.card : ℝ) * M := by
    have : |(s.card : ℝ) * x a0| = (s.card : ℝ) * |x a0| := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (s.card : ℝ))]
    rw [← this, e]
    calc _ ≤ |∑ a ∈ s, y a - ∑ a ∈ s, (y a - x a)| + |∑ a ∈ s, (x a0 - x a)| := abs_add_le _ _
      _ ≤ |∑ a ∈ s, y a| + |∑ a ∈ s, (y a - x a)| + |∑ a ∈ s, (x a0 - x a)| := by
          gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith
  have h4 : (s.card : ℝ) * |x a0| ≤ (s.card : ℝ) * (B + M + K) := by nlinarith
  exact le_of_mul_le_mul_left h4 (by linarith)

theorem fiber_bound {ι : Type*} (s : Finset ι) (x y : ι → ℝ) (a0 : ι) (M X K : ℝ) (hX0 : 0 ≤ X)
    (hX : |x a0| ≤ X) (hM : ∀ a ∈ s, |x a - x a0| ≤ M) (hK : |∑ a ∈ s, (y a - x a)| ≤ K) :
    ∑ a ∈ s, ((y a - x a) ^ 2 / 2 - 2 * M ^ 2) - 2 * X * K ≤ ∑ a ∈ s, (y a ^ 2 - x a ^ 2) := by
  have h1 : ∀ a ∈ s, ((y a - x a) ^ 2 / 2 - 2 * M ^ 2) + 2 * x a0 * (y a - x a) ≤ y a ^ 2 - x a ^ 2 := by
    intro a ha
    have he : (x a - x a0) ^ 2 ≤ M ^ 2 := sq_le_sq' (by linarith [(abs_le.mp (hM a ha)).1])
      (abs_le.mp (hM a ha)).2
    nlinarith [sq_nonneg ((y a - x a) + 2 * (x a - x a0))]
  have h2 := Finset.sum_le_sum h1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h2
  have h3 : -(2 * X * K) ≤ 2 * x a0 * ∑ a ∈ s, (y a - x a) := by
    have : |x a0 * ∑ a ∈ s, (y a - x a)| ≤ X * K := by
      rw [abs_mul]
      exact mul_le_mul hX hK (abs_nonneg _) hX0
    nlinarith [(abs_le.mp this).1]
  linarith

theorem total_bound {n : ℕ} (x y : Fin n → ℝ) (lev : Fin n → ℕ) (M X K : ℝ) (hX0 : 0 ≤ X) (hK0 : 0 ≤ K)
    (hX : ∀ a, |x a| ≤ X) (hM : ∀ a b, lev a = lev b → |x a - x b| ≤ M)
    (hK : ∀ c, |∑ a ∈ univ.filter (fun a => lev a = c), (y a - x a)| ≤ K) :
    ∑ a, ((y a - x a) ^ 2 / 2 - 2 * M ^ 2) - n * (2 * X * K) ≤ ∑ a, (y a ^ 2 - x a ^ 2) := by
  have hmaps : ∀ a ∈ (univ : Finset (Fin n)), lev a ∈ univ.image lev :=
    fun a _ => Finset.mem_image_of_mem _ (Finset.mem_univ a)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun a => y a ^ 2 - x a ^ 2),
    ← Finset.sum_fiberwise_of_maps_to hmaps (fun a => (y a - x a) ^ 2 / 2 - 2 * M ^ 2)]
  have hcard : ((univ.image lev).card : ℝ) ≤ n := by
    have := Finset.card_image_le (s := (univ : Finset (Fin n))) (f := lev)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have h1 : ∑ c ∈ univ.image lev, (∑ a ∈ univ.filter (fun a => lev a = c),
      ((y a - x a) ^ 2 / 2 - 2 * M ^ 2) - 2 * X * K) ≤
      ∑ c ∈ univ.image lev, ∑ a ∈ univ.filter (fun a => lev a = c), (y a ^ 2 - x a ^ 2) := by
    refine Finset.sum_le_sum fun c hc => ?_
    obtain ⟨a0, -, rfl⟩ := Finset.mem_image.mp hc
    refine fiber_bound _ x y a0 M X K hX0 (hX a0) (fun a ha => ?_) (hK _)
    exact hM a a0 (Finset.mem_filter.mp ha).2
  rw [Finset.sum_sub_distrib] at h1
  simp only [Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ((univ.image lev).card : ℝ) * (2 * X * K) ≤ n * (2 * X * K) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  linarith

theorem two_bound {n : ℕ} (d : Fin n → ℝ) (a b : Fin n) (hab : a ≠ b) (D : ℝ) (hD : 0 ≤ D)
    (h : D ≤ |d a - d b|) : D ^ 2 / 2 ≤ ∑ c, d c ^ 2 := by
  have h1 : d a ^ 2 + d b ^ 2 ≤ ∑ c, d c ^ 2 := by
    rw [← Finset.sum_pair (f := fun c => d c ^ 2) hab]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  have h2 : D ^ 2 ≤ (d a - d b) ^ 2 := by
    rw [← sq_abs (d a - d b)]
    exact pow_le_pow_left₀ hD h 2
  nlinarith [sq_nonneg (d a + d b)]

theorem farNum : FarNum := by
  intro n C δ K hδ
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = |C| := ⟨_, rfl⟩
  obtain ⟨K', hK'⟩ : ∃ K' : ℝ, K' = |K| := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = n * Lc n := ⟨_, rfl⟩
  have hC0 : 0 ≤ C' := hC' ▸ abs_nonneg _
  have hK0 : 0 ≤ K' := hK' ▸ abs_nonneg _
  have hM0 : 0 ≤ M := by rw [hMdef, Lc]; positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 * n * M ^ 2 + 2 * n * K' * (M + K') + 2 * (n : ℝ) ^ 2 * (M + K') + (n : ℝ) ^ 3
      + n * C' ^ 2 + K' := ⟨_, rfl⟩
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ, Bc = 2 * n * K' * C' + 2 * (n : ℝ) ^ 2 * C' := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ Bc := by rw [hBc]; positivity
  refine ⟨1 + 2 * M / δ + 16 * (A + Bc) / δ ^ 2, ?_⟩
  intro χ x r lev σ N _ _ hr hsp hblk hineq hsep hbd hN a b hab
  by_contra hne
  have hq1 : 0 ≤ 2 * M / δ := by positivity
  have hq2 : 0 ≤ 16 * (A + Bc) / δ ^ 2 := by positivity
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hδN : 2 * M ≤ δ * N := by
    have : 2 * M / δ ≤ N := by linarith
    rw [div_le_iff₀ hδ] at this
    linarith
  have hδ2 : 16 * (A + Bc) + δ ^ 2 ≤ δ ^ 2 * N := by
    have : 16 * (A + Bc) / δ ^ 2 ≤ N - 1 := by linarith
    rw [div_le_iff₀ (by positivity)] at this
    linarith

  obtain ⟨y, hy⟩ : ∃ y : Fin n → ℝ, y = fun a => (χ (σ a)).re := ⟨_, rfl⟩
  have hyb : ∀ a, |y a| ≤ C' * N := by
    intro a
    rw [hy]
    refine (hbd (σ a)).1.trans ?_
    rw [hC']
    exact mul_le_mul_of_nonneg_right (le_abs_self C) hN0
  have hblk' : ∀ c, |∑ a ∈ univ.filter (fun a => lev a = c), (y a - x a)| ≤ K' := by
    intro c
    have h1 := Complex.abs_re_le_norm (∑ a ∈ univ.filter (fun a => lev a = c), χ (σ a)
      - ∑ a ∈ univ.filter (fun a => lev a = c), ((x a : ℝ) : ℂ))
    have h2 : (∑ a ∈ univ.filter (fun a => lev a = c), χ (σ a)
      - ∑ a ∈ univ.filter (fun a => lev a = c), ((x a : ℝ) : ℂ)).re
        = ∑ a ∈ univ.filter (fun a => lev a = c), (y a - x a) := by
      rw [hy, Finset.sum_sub_distrib]
      simp [Complex.re_sum]
    rw [h2] at h1
    exact h1.trans ((hblk c).trans (hK' ▸ le_abs_self K))
  have hspM : ∀ a b, lev a = lev b → |x a - x b| ≤ M := fun a b h => hMdef ▸ hsp a b h

  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = C' * N + M + K' := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hX : ∀ a, |x a| ≤ X := by
    intro a
    rw [hXdef]
    refine x_bound (univ.filter fun c => lev c = lev a) x y a (by simp) _ _ _ hK0
      (fun c _ => hyb c) (fun c hc => hspM a c (Finset.mem_filter.mp hc).2.symm) (hblk' _)

  have hlow := total_bound x y lev M X K' hX0 hK0 hX hspM hblk'
  have hD : (δ * N - M) ^ 2 / 2 ≤ ∑ c, (y c - x c) ^ 2 := by
    refine two_bound (fun c => y c - x c) a b hne _ (by linarith) ?_
    have h1 : δ * N ≤ |y a - y b| := by
      rw [hy]
      exact hsep (σ a) (σ b) (fun h => hne (σ.injective h))
    have h2 := hspM a b hab
    have h3 : |y a - y b| ≤ |(y a - x a) - (y b - x b)| + |x a - x b| := by
      have : y a - y b = ((y a - x a) - (y b - x b)) + (x a - x b) := by ring
      rw [this]
      exact abs_add_le _ _
    show δ * N - M ≤ |(y a - x a) - (y b - x b)|
    linarith

  have hYsum : ∑ a, y a ^ 2 = ∑ a, (χ a).re ^ 2 := by
    rw [hy]
    exact Equiv.sum_comp σ (fun a => (χ a).re ^ 2)
  have hIm : ∑ a, (χ a).im ^ 2 ≤ n * C' ^ 2 := by
    calc ∑ a, (χ a).im ^ 2 ≤ ∑ _a : Fin n, C' ^ 2 := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [← sq_abs (χ a).im]
          exact pow_le_pow_left₀ (abs_nonneg _) ((hbd a).2.trans (hC' ▸ le_abs_self C)) 2
      _ = n * C' ^ 2 := by simp
  have hxr : ∑ a, (x a - r a) ^ 2 ≤ ∑ a, x a ^ 2 + n * (2 * X * n + (n : ℝ) ^ 2) := by
    have : ∀ a ∈ (univ : Finset (Fin n)), (x a - r a) ^ 2 ≤ x a ^ 2 + (2 * X * n + (n : ℝ) ^ 2) := by
      intro a _
      have h1 : |x a * r a| ≤ X * n := by
        rw [abs_mul]
        exact mul_le_mul (hX a) (hr a) (abs_nonneg _) hX0
      have h2 : r a ^ 2 ≤ (n : ℝ) ^ 2 := by
        rw [← sq_abs (r a)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hr a) 2
      nlinarith [(abs_le.mp h1).1]
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_refl _
  have hKK : K ≤ K' := hK' ▸ le_abs_self K
  rw [Finset.sum_sub_distrib] at hineq
  have hup : ∑ a, y a ^ 2 ≤ ∑ a, x a ^ 2 + n * (2 * X * n + (n : ℝ) ^ 2) + n * C' ^ 2 + K' := by
    rw [hYsum]
    linarith
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div] at hlow
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlow
  have hδM : (δ * N / 2) ^ 2 ≤ (δ * N - M) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have e1 : (δ * N / 2) ^ 2 = (δ * N) ^ 2 / 4 := by ring
  have h5 : (δ * N) ^ 2 / 16 ≤ n * (2 * M ^ 2) + n * (2 * X * K') + n * (2 * X * n + (n : ℝ) ^ 2)
      + n * C' ^ 2 + K' := by
    linarith
  have e2 : n * (2 * M ^ 2) + n * (2 * X * K') + n * (2 * X * n + (n : ℝ) ^ 2) + n * C' ^ 2 + K'
      = A + Bc * N := by
    rw [hA, hBc, hXdef]
    ring
  rw [e2] at h5
  have h6 : 16 * (A + Bc) < δ ^ 2 * N := by linarith [pow_pos hδ 2]
  have h7 : 16 * (A + Bc) * N < δ ^ 2 * N * N := mul_lt_mul_of_pos_right h6 (by linarith)
  have e3 : (δ * N) ^ 2 = δ ^ 2 * N * N := by ring
  have h8 : A ≤ A * N := le_mul_of_one_le_right hA0 hN1
  rw [e3] at h5
  linarith

end GlobalTheory.CompanionTheory.RgExhFar
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FarRegOfLktUnitIneqFarNum
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.FarRegularityLevels

open CompanionTheory.RgExh CompanionTheory.RgExh.U
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open PI.UpqRep (rhoC rhoN lowK nsq vNormSq)

variable {n : ℕ}

theorem rho_sum (ε : Fin n → Bool) (a : Fin n) :
    rhoN ε a + rhoC ε a = ((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ) := by
  unfold rhoN rhoC
  have kgt := Finset.card_filter_add_card_filter_not (s := Ioi a) (fun b => ε b = ε a)
  have e1 : (Ioi a).filter (fun b => ε b = ε a) = univ.filter (fun b => a < b ∧ ε b = ε a) := by
    ext b; simp
  have e2 : (Ioi a).filter (fun b => ¬ ε b = ε a) = univ.filter (fun b => a < b ∧ ε b ≠ ε a) := by
    ext b; simp
  rw [e1, e2, Fin.card_Ioi] at kgt
  have klt := Finset.card_filter_add_card_filter_not (s := Iio a) (fun b => ε b = ε a)
  have e3 : (Iio a).filter (fun b => ε b = ε a) = univ.filter (fun b => b < a ∧ ε b = ε a) := by
    ext b; simp
  have e4 : (Iio a).filter (fun b => ¬ ε b = ε a) = univ.filter (fun b => b < a ∧ ε b ≠ ε a) := by
    ext b; simp
  rw [e3, e4, Fin.card_Iio] at klt
  have ha := a.isLt
  have kgt' : (univ.filter (fun b => a < b ∧ ε b = ε a)).card +
      (univ.filter (fun b => a < b ∧ ε b ≠ ε a)).card + (a : ℕ) + 1 = n := by omega
  have rgt : ((univ.filter (fun b => a < b ∧ ε b = ε a)).card : ℝ) +
      ((univ.filter (fun b => a < b ∧ ε b ≠ ε a)).card : ℝ) + ((a : ℕ) : ℝ) + 1 = n := by
    exact_mod_cast kgt'
  have rlt : ((univ.filter (fun b => b < a ∧ ε b = ε a)).card : ℝ) +
      ((univ.filter (fun b => b < a ∧ ε b ≠ ε a)).card : ℝ) = ((a : ℕ) : ℝ) := by
    exact_mod_cast klt
  linarith

theorem abs_rhoC_le (ε : Fin n → Bool) (a : Fin n) : |rhoC ε a| ≤ n := by
  unfold rhoC
  have h1 : ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) ≤ n := by
    have := card_filter_le (univ : Finset (Fin n)) (fun b => a < b ∧ ε b = ε a)
    rw [card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have h2 : ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) ≤ n := by
    have := card_filter_le (univ : Finset (Fin n)) (fun b => b < a ∧ ε b = ε a)
    rw [card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have h3 : (0 : ℝ) ≤ ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) := Nat.cast_nonneg _
  have h5 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

theorem two_rhoC_int (ε : Fin n → Bool) (a : Fin n) : ∃ m : ℤ, 2 * rhoC ε a = m :=
  ⟨((univ.filter fun b => a < b ∧ ε b = ε a).card : ℤ) - ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℤ), by
    unfold rhoC; push_cast; ring⟩

theorem rhoC_lt (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) : rhoC ε b < rhoC ε a := by
  unfold rhoC
  have h1 : (univ.filter fun c => b < c ∧ ε c = ε b).card < (univ.filter fun c => a < c ∧ ε c = ε a).card := by
    apply card_lt_card
    rw [ssubset_iff_of_subset]
    · exact ⟨b, by simp [hab, he], by simp⟩
    · intro c hc
      simp only [mem_filter, mem_univ, true_and] at hc ⊢
      exact ⟨hab.trans hc.1, hc.2.trans he.symm⟩
  have h2 : (univ.filter fun c => c < a ∧ ε c = ε a).card ≤ (univ.filter fun c => c < b ∧ ε c = ε b).card := by
    apply card_le_card
    intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc ⊢
    exact ⟨hc.1.trans hab, hc.2.trans he⟩
  have h1' : ((univ.filter fun c => b < c ∧ ε c = ε b).card : ℝ) <
      ((univ.filter fun c => a < c ∧ ε c = ε a).card : ℝ) := by exact_mod_cast h1
  have h2' : ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℝ) ≤
      ((univ.filter fun c => c < b ∧ ε c = ε b).card : ℝ) := by exact_mod_cast h2
  linarith


open Classical in
def levS (y : ℕ → ℝ) (L : ℝ) (m : ℕ) : ℕ := ((range m).filter fun i => L ≤ y i - y (i + 1)).card

theorem levS_mono (y : ℕ → ℝ) (L : ℝ) : Monotone (levS y L) := by
  classical
  intro a b hab
  exact card_le_card (filter_subset_filter _ (range_mono hab))

theorem levS_gap {y : ℕ → ℝ} (hy : Antitone y) {L : ℝ} {a b : ℕ} (h : levS y L a < levS y L b) :
    L ≤ y a - y b := by
  classical
  obtain ⟨i, hi, hi'⟩ := Finset.exists_mem_notMem_of_card_lt_card h
  simp only [mem_filter, mem_range, not_and] at hi hi'
  have hai : a ≤ i := by
    by_contra hc
    exact hi' (by omega) hi.2
  have h1 : y i ≤ y a := hy hai
  have h2 : y b ≤ y (i + 1) := hy (by omega)
  linarith [hi.2]

theorem levS_flat (y : ℕ → ℝ) (L : ℝ) (a m : ℕ) (h : levS y L a = levS y L (a + m)) :
    y a - y (a + m) ≤ m * L := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : levS y L a ≤ levS y L (a + m) := levS_mono y L (by omega)
    have h2 : levS y L (a + m) ≤ levS y L (a + (m + 1)) := levS_mono y L (by omega)
    have h3 : levS y L a = levS y L (a + m) := by omega
    have h4 := ih h3
    have h5 : ¬ L ≤ y (a + m) - y (a + m + 1) := by
      intro hP
      have : levS y L (a + m) < levS y L (a + (m + 1)) := by
        unfold levS
        apply card_lt_card
        rw [ssubset_iff_of_subset]
        · exact ⟨a + m, by simp [hP], by simp⟩
        · exact filter_subset_filter _ (range_mono (by omega))
      omega
    push_neg at h5
    have e : a + (m + 1) = a + m + 1 := rfl
    rw [e]
    push_cast
    linarith

theorem exists_lev (x : Fin n → ℝ) (hx : Antitone x) {L : ℝ} (hL : 0 ≤ L) :
    ∃ lev : Fin n → ℕ, Monotone lev ∧ (∀ a b, lev a < lev b → L ≤ x a - x b) ∧
      ∀ a b, lev a = lev b → |x a - x b| ≤ n * L := by
  cases n with
  | zero => exact ⟨fun a => a.elim0, fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩
  | succ m =>
    let y : ℕ → ℝ := fun i => x ⟨min i m, by omega⟩
    have hy : Antitone y := by
      intro i j hij
      apply hx
      simp only [Fin.mk_le_mk]
      omega
    have hya : ∀ a : Fin (m + 1), y a = x a := by
      intro a
      have ha := a.isLt
      simp only [y]
      congr 1
      apply Fin.ext
      simp only
      omega
    have key : ∀ a b : Fin (m + 1), a ≤ b → levS y L a = levS y L b → x a - x b ≤ ((m + 1 : ℕ) : ℝ) * L := by
      intro a b hab h
      have hab' : (a : ℕ) ≤ b := hab
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hab'
      rw [hk] at h
      have h1 := levS_flat y L a k h
      rw [← hk, hya, hya] at h1
      have h2 : (k : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
        have := b.isLt
        exact_mod_cast (by omega : k ≤ m + 1)
      nlinarith
    refine ⟨fun a => levS y L a, fun a b hab => levS_mono y L hab, fun a b h => ?_, fun a b h => ?_⟩
    · have := levS_gap hy h
      rwa [hya, hya] at this
    · rcases le_total a b with hab | hab
      · have h0 : 0 ≤ x a - x b := sub_nonneg.2 (hx hab)
        rw [abs_of_nonneg h0]
        exact key a b hab h
      · have h0 : 0 ≤ x b - x a := sub_nonneg.2 (hx hab)
        rw [abs_sub_comm, abs_of_nonneg h0]
        exact key b a hab h.symm

theorem farReg_of_lkt_unitIneq_farNum : LKTExists → Renumber → UnitIneq → COBlock → FarNum → CompanionTheory.RgExh.FarReg := by
  intro hLK hRn hUI hCO hFN n C δ hδ
  obtain ⟨K2, hK2⟩ := hUI n
  obtain ⟨K1, hK1⟩ := hCO n
  obtain ⟨N₀, hN⟩ := hFN n C δ (max K1 K2) hδ
  refine ⟨N₀, ?_⟩
  intro ε V _ _ E hE χ N hV hUn hLF hInt hSC hN₀ hsep hbd
  obtain ⟨γ, u, hu, hKH, hMin, hγint, hdom⟩ := hLK n ε V E hE hV hUn hLF hInt

  obtain ⟨s, hs⟩ : ∃ s : Equiv.Perm (Fin n), Antitone (xv ε γ ∘ s) := by
    refine ⟨Tuple.sort (fun a => - xv ε γ a), fun a b hab => ?_⟩
    have := Tuple.monotone_sort (fun a => - xv ε γ a) hab
    simp only [Function.comp_apply] at this ⊢
    linarith
  have hblk : ∀ a b, a < b → ε a = ε b → xv ε γ b < xv ε γ a := by
    intro a b hab he
    have h1 := hdom a b hab he
    have h2 := rhoC_lt ε hab he
    simp only [xv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hord : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b := by
    intro a b hab he
    by_contra hc
    have hne : s a ≠ s b := fun h => hab.ne (s.injective h)
    have hlt : s b < s a := lt_of_le_of_ne (not_lt.1 hc) hne.symm
    have h1 := hblk (s b) (s a) hlt he.symm
    have h2 := hs hab.le
    simp only [Function.comp_apply] at h2
    linarith
  obtain ⟨hE', hUn', hLF', hSC', hKH', hMin', hrho⟩ := hRn n ε V E hE s hord
  have hUn2 := hUn' hUn
  have hLF2 := hLF' hLF
  have hSC2 := hSC' χ hSC
  have hKH2 := (hKH' γ u).1 hKH
  have hMin2 := (hMin' γ).1 hMin
  have hx' : xv (ε ∘ s) (γ ∘ s) = xv ε γ ∘ s := by
    funext a
    simp only [xv, hrho, Pi.add_apply, Pi.smul_apply, Function.comp_apply]
  have hanti : Antitone (xv (ε ∘ s) (γ ∘ s)) := by rw [hx']; exact hs
  have hLc : (0 : ℝ) ≤ Lc n := by unfold Lc; positivity
  obtain ⟨lev, hmono, hgap, hspread⟩ := exists_lev _ hanti hLc
  have hG : Gapped (ε ∘ s) (γ ∘ s) lev (Lc n) := ⟨hanti, hmono, hgap⟩
  have hKU : CompanionTheory.D.DSIC.KUnit (ε ∘ s) (fun a b => E (s a) (s b)) := by
    intro a b he x y
    have h1 := hUn2 a b x y
    have h2 : Formalism.REAL.sgn (ε ∘ s) a b = 1 := if_pos he
    rw [h2] at h1
    simpa using h1
  obtain ⟨σ, hσ⟩ := hK1 (ε ∘ s) (γ ∘ s) lev V (fun a b => E (s a) (s b)) hE' χ hG hKU hLF2 hMin2 hSC2 ⟨u, hu, hKH2⟩
  have hcas := hK2 (ε ∘ s) V (fun a b => E (s a) (s b)) hE' χ (γ ∘ s) u hUn2 hSC2 hu hKH2
  have hinj : Function.Injective lev := by
    refine hN χ (xv (ε ∘ s) (γ ∘ s)) (rhoC (ε ∘ s)) lev σ N hanti hmono (abs_rhoC_le _) hspread ?_ ?_ hsep hbd hN₀
    · exact fun c => (hσ c).trans (le_max_left _ _)
    · have e : nsq (γ ∘ s + rhoC (ε ∘ s)) = ∑ a, (xv (ε ∘ s) (γ ∘ s) a - rhoC (ε ∘ s) a) ^ 2 := by
        unfold PI.UpqRep.nsq PI.UpqRep.dot
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [xv, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [← e]
      exact hcas.trans (by linarith [le_max_right K1 K2])

  have hstep : ∀ a b : Fin n, a < b → Lc n ≤ xv (ε ∘ s) (γ ∘ s) a - xv (ε ∘ s) (γ ∘ s) b := by
    intro a b hab
    exact hgap a b (lt_of_le_of_ne (hmono hab.le) fun h => hab.ne (hinj h))
  have hLbig : (n : ℝ) + 1 ≤ Lc n := by
    unfold Lc
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0]
  have hlow : lowK (ε ∘ s) (xv (ε ∘ s) (γ ∘ s) - Formalism.QuantumDeterminants.rhoStd n) = γ ∘ s := by
    funext a
    have h1 := rho_sum (ε ∘ s) a
    simp only [lowK, xv, Formalism.QuantumDeterminants.rhoStd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  refine ⟨s, xv (ε ∘ s) (γ ∘ s) - Formalism.QuantumDeterminants.rhoStd n, ⟨?_, ?_⟩, hord, ?_, u, hu, ?_⟩
  · intro a b hab
    have h1 := hstep a b hab
    have h2 : ((b : ℕ) : ℝ) < n := by exact_mod_cast b.isLt
    have h3 : (0 : ℝ) ≤ ((a : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [Formalism.QuantumDeterminants.rhoStd, Pi.sub_apply]
    linarith
  · intro a
    obtain ⟨m, hm⟩ := hγint (s a)
    obtain ⟨k, hk⟩ := two_rhoC_int (ε ∘ s) a
    refine ⟨m + k - (n : ℤ) + 1 + (a : ℕ), ?_⟩
    simp only [xv, Formalism.QuantumDeterminants.rhoStd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    push_cast
    rw [hm, hk]
    ring
  · intro μ x hx hμ
    show vNormSq (ε ∘ s) (lowK (ε ∘ s) _) ≤ _
    rw [hlow]
    exact hMin2 μ x hx hμ
  · show KHighest (ε ∘ s) (fun a b => E (s a) (s b)) (lowK (ε ∘ s) _) u
    rw [hlow]
    exact hKH2

end GlobalTheory.CompanionTheory.FarRegularityLevels
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.VanKGOf
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhVanKG

open CompanionTheory.D.LK
open CompanionTheory.D.LK.Car
open CompanionTheory.RgExh.U
open Formalism.REAL (GlRel KHighest IsWeight CasK)
open PI.UpqRep (rhoC nsq)
open CompanionTheory.D.DSIC (KRel KUnit KStab)

theorem vanKG_of (hN : NumKG) : VanKG := by
  have hC : COK := cok_of hGenCO
  have hP : WtProj := GlobalTheory.CompanionTheory.LKWtProj.wtProj
  have hM : WtMajor := GlobalTheory.CompanionTheory.KWeightMajor.wtMajor_of CompanionTheory.D.DSIC.hLowSpan
  intro n ε γ lev V _ _ E hg hE hU hF hmin B j z hB hBU hz hwt hb
  set τ := xv ε γ with hτ
  have hzw : ∀ A, IsWeight E (τ - wt A) (z A) := fun A c => by
    have := congrFun (hwt c) A
    rw [Ft_apply, filter_all, Pi.smul_apply] at this
    rw [eq_sub_of_add_eq this, Pi.sub_apply, Complex.ofReal_sub, sub_smul]
  obtain ⟨w, hw, e⟩ := hC n ε V E hE B j (τ - wt B) z hz (fun c => funext fun A => by
    by_cases h : z A = 0
    · simp [Ft_apply, h]
    · rw [Ft_apply, hzw A c, Pi.smul_apply, ← add_smul, Pi.sub_apply, Pi.sub_apply, wt_split (ε := ε) A, (hz A h).1]
      congr 1; push_cast; ring) hb
  choose S hS hSt hmem using hF
  let W : Submodule ℂ V := ⨆ A, S (z A)
  haveI : ∀ A, FiniteDimensional ℂ (S (z A)) := fun A => hS _
  have hWs : KStab ε E W := fun a b h v hv =>
    (iSup_le fun A y hy => Submodule.mem_iSup_of_mem A (hSt _ a b h y hy) : W ≤ W.comap (E a b)) hv
  obtain ⟨q, hq⟩ := exists_poly (CasK ε E) (fun x y => by
      simp only [CasK, LinearMap.sum_apply, sum_inner, inner_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      split_ifs with h
      · rw [Module.End.mul_apply, Module.End.mul_apply, hU a b h, hU b a h.symm]
      · simp) W (fun x hx => by
      simp only [CasK, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
      split_ifs with h
      · exact hWs a b h _ (hWs b a h.symm _ hx)
      · simp) (nsq (τ - wt B - rhoC ε) - nsq (rhoC ε))
  have hcq : ∀ c d, ε c = ε d → ∀ x, Polynomial.aeval (CasK ε E) q (E c d x) = E c d (Polynomial.aeval (CasK ε E) q x) :=
    fun c d h x => by
      have : Commute (E c d) (Polynomial.aeval (CasK ε E) q) := by
        rw [Polynomial.aeval_eq_sum_range]
        exact Commute.sum_right _ _ _ fun k _ => ((casK_comm hE h).pow_right k).smul_right _
      exact (LinearMap.congr_fun this.eq x).symm
  have h0 : z + lift n (Polynomial.aeval (CasK ε E) q) (bd ε E w) = 0 := by
    funext A
    by_contra hne
    rw [← e] at hne
    have hA : z A ≠ 0 := fun h => hne (by simp [h])
    obtain ⟨ν, y, hy0, hy, hs, hd, hc⟩ := hM n ε V E hE hU (fun x => ⟨S x, hS x, hSt x, hmem x⟩) (τ - wt A) _ _ hne
      (fun c => by
        simp only [Pi.add_apply, lift_apply, Pi.sub_apply, Pi.smul_apply]
        rw [map_add (f := _), ← hcq c c rfl, map_sub, map_smul, ← Module.End.mul_apply, (casK_comm hE rfl).eq,
          Module.End.mul_apply, hzw A c]
        simp only [map_smul, map_sub, smul_add, smul_sub, Pi.sub_apply, smul_comm ((τ c - wt A c : ℝ) : ℂ)])
      (hq (z A) (Submodule.mem_iSup_of_mem A (hmem _)) _ rfl)
    have hA1 := (hz A hA).1
    refine absurd (hmin ν y hy0 hy) (not_le.2 (hN n ε γ lev ν B (A.filter (cpt ε)) hg hB
      (fun i hi => ⟨(mem_filter.1 (hA1.symm ▸ hi :)).2, hBU i hi⟩) (fun i hi => (mem_filter.1 hi).2) hd (fun w hw' => ?_) ?_))
    · convert hc w hw' using 2
      funext c
      simp only [Pi.sub_apply, wt_split (ε := ε) A, hA1, hτ]
      ring
    · have h1 : nsq (τ - wt B - rhoC ε) = nsq (ν + rhoC ε) := by
        have := Complex.ofReal_injective hs
        linarith
      rw [← h1]
      congr 1
      abel
  have h1 : bd ε E (-lift n (Polynomial.aeval (CasK ε E) q) w) = z := by
    rw [map_neg, ← lift_bd _ E E fun i hi x => hcq _ _ hi x]
    exact (eq_neg_of_add_eq_zero_left h0).symm
  obtain ⟨t, ht1, ht2, ht3⟩ := hP n (allT n) ε V E hE hU (fun x => ⟨S x, hS x, hSt x, hmem x⟩) (bd ε E)
    (differential_commutes_weight_operator n _ ε V E (fun _ _ _ => rfl) hE) τ _ (h1.symm ▸ hwt)
  exact ⟨t, sup_of_supp hw fun A h => ht3 A (by simp [h]), ht1, ht2.trans h1⟩

end GlobalTheory.CompanionTheory.RgExhVanKG
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.VNormSqRenum
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgFarRen

open Formalism.REAL (GlRel IsUnitary KHighest IsWeight qdet qminor Tm sgn)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (LocFin)
open PI.UpqRep (vNormSq rhoC nsq)

variable {n : ℕ}

theorem glRel_renum {A : Type*} [Ring A] {E : Fin n → Fin n → A} (hE : GlRel E) (s : Equiv.Perm (Fin n)) :
    GlRel (fun a b => E (s a) (s b)) := by
  intro a b c d
  have h := hE (s a) (s b) (s c) (s d)
  simpa only [Equiv.apply_eq_iff_eq] using h

theorem tm_renum {A : Type*} [Ring A] [Algebra ℂ A] (E : Fin n → Fin n → A) (s : Equiv.Perm (Fin n)) (u : ℂ)
    (a b : Fin n) : Tm (fun a b => E (s a) (s b)) u a b = Tm E u (s a) (s b) := by
  simp only [Formalism.REAL.Tm, Equiv.apply_eq_iff_eq]

theorem qminor_renum {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin n → Fin n → A) (s : Equiv.Perm (Fin n))
    (a b : Fin t → Fin n) (u : ℂ) :
    qminor (fun a b => E (s a) (s b)) a b u = qminor E (s ∘ a) (s ∘ b) u := by
  unfold Formalism.REAL.qminor
  simp only [tm_renum, Function.comp_apply]

theorem qdet_renum {A : Type} [Ring A] [Algebra ℂ A] {E : Fin n → Fin n → A} (hE : GlRel E)
    (s : Equiv.Perm (Fin n)) (u : ℂ) : qdet (fun a b => E (s a) (s b)) u = qdet E u := by
  have h1 : qdet (fun a b => E (s a) (s b)) u = qminor E (id ∘ ⇑s) (id ∘ ⇑s) u := by
    unfold Formalism.REAL.qdet
    rw [qminor_renum]
    rfl
  have hsq : ((Equiv.Perm.sign s : ℤ) : A) * ((Equiv.Perm.sign s : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  rw [h1, Formalism.REAL.quantumMinorRowSkew_holds, Formalism.REAL.quantumMinorColSkew_holds A n n E hE, ← mul_assoc, hsq, one_mul]
  rfl

theorem symm_lt {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    s.symm a < s.symm b := by
  rcases lt_trichotomy (s.symm a) (s.symm b) with h | h | h
  · exact h
  · exact absurd (s.symm.injective h) (ne_of_lt hab)
  · have h' := hs (s.symm b) (s.symm a) h (by simp [he])
    simp only [Equiv.apply_symm_apply] at h'
    exact absurd h' (lt_asymm hab)

theorem kHighest_iff {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool}
    (E : Fin n → Fin n → Module.End ℂ V) {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (γ : Fin n → ℝ) (u : V) :
    KHighest ε E γ u ↔ KHighest (ε ∘ s) (fun a b => E (s a) (s b)) (γ ∘ s) u := by
  unfold Formalism.REAL.KHighest Formalism.REAL.IsWeight
  constructor
  · rintro ⟨hw, hz⟩
    exact ⟨fun a => hw (s a), fun a b hab he => hz (s a) (s b) (hs a b hab he) he⟩
  · rintro ⟨hw, hz⟩
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · simpa using hw (s.symm a)
    · have h := hz (s.symm a) (s.symm b) (symm_lt hs hab he) (by simpa using he)
      simpa using h

theorem rhoC_renum {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) : rhoC (ε ∘ s) = rhoC ε ∘ s := by
  funext a
  have h1 : (Finset.univ.filter (fun b => a < b ∧ ε (s b) = ε (s a))).card =
      (Finset.univ.filter (fun b => s a < b ∧ ε b = ε (s a))).card := by
    refine Finset.card_nbij' s s.symm ?_ ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hb ⊢
      exact ⟨hs a b hb.1 hb.2.symm, hb.2⟩
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe, Equiv.apply_symm_apply] at hc ⊢
      refine ⟨?_, hc.2⟩
      have h' := symm_lt hs hc.1 hc.2.symm
      simpa using h'
    · intro b _
      simp
    · intro c _
      simp
  have h2 : (Finset.univ.filter (fun b => b < a ∧ ε (s b) = ε (s a))).card =
      (Finset.univ.filter (fun b => b < s a ∧ ε b = ε (s a))).card := by
    refine Finset.card_nbij' s s.symm ?_ ?_ ?_ ?_
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe] at hb ⊢
      exact ⟨hs b a hb.1 hb.2, hb.2⟩
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe, Equiv.apply_symm_apply] at hc ⊢
      refine ⟨?_, hc.2⟩
      have h' := symm_lt hs hc.1 hc.2
      simpa using h'
    · intro b _
      simp
    · intro c _
      simp
  simp only [PI.UpqRep.rhoC, Function.comp_apply, h1, h2]

theorem vNormSq_renum {ε : Fin n → Bool} {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (γ : Fin n → ℝ) :
    vNormSq (ε ∘ s) (γ ∘ s) = vNormSq ε γ := by
  unfold PI.UpqRep.vNormSq PI.UpqRep.nsq PI.UpqRep.dot
  rw [rhoC_renum hs]
  exact Fintype.sum_equiv s _ _ (fun a => by simp)

theorem isMinG_iff {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool}
    (E : Fin n → Fin n → Module.End ℂ V) {s : Equiv.Perm (Fin n)}
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (γ : Fin n → ℝ) :
    IsMinG ε E γ ↔ IsMinG (ε ∘ s) (fun a b => E (s a) (s b)) (γ ∘ s) := by
  unfold CompanionTheory.RgExh.U.IsMinG
  constructor
  · intro h μ x hx hk
    have hμ : μ = (μ ∘ s.symm) ∘ s := by
      funext a
      simp
    rw [hμ] at hk ⊢
    rw [vNormSq_renum hs, vNormSq_renum hs]
    exact h _ x hx ((kHighest_iff E hs _ x).mpr hk)
  · intro h μ x hx hk
    have h' := h (μ ∘ s) x hx ((kHighest_iff E hs μ x).mp hk)
    rwa [vNormSq_renum hs, vNormSq_renum hs] at h'

theorem renumber : CompanionTheory.RgExh.U.Renumber := by
  intro n ε V _ _ E hE s hs
  refine ⟨glRel_renum hE s, fun hU a b x y => hU (s a) (s b) x y, ?_, ?_,
    fun γ u => kHighest_iff E hs γ u, fun γ => isMinG_iff E hs γ, rhoC_renum hs⟩
  · intro hL x
    obtain ⟨S, hS, hK, hx⟩ := hL x
    exact ⟨S, hS, fun a b hab v hv => hK (s a) (s b) hab v hv, hx⟩
  · intro χ hχ Y
    exact (qdet_renum hE s _).trans (hχ Y)

end GlobalTheory.CompanionTheory.RgFarRen
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantOfKHighest
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhFarReg

open Finset
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (LocFin)
open PI.UpqRep (vNormSq rhoC nsq)

variable {n : ℕ}

lemma kRel_of_glRel {V : Type} [AddCommGroup V] [Module ℂ V] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} (hE : GlRel E) : CompanionTheory.D.DSIC.KRel ε E :=
  fun a b c d _ _ => hE a b c d

lemma kUnit_of_isUnitary {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} (hU : IsUnitary ε E) : CompanionTheory.D.DSIC.KUnit ε E := by
  intro a b he x y
  rw [hU a b x y]
  simp [Formalism.REAL.sgn, he]

lemma dominant_of_kHighest {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} (hF : CompanionTheory.D.DSIC.KRel ε E) (hU : CompanionTheory.D.DSIC.KUnit ε E)
    {μ : Fin n → ℝ} {u : V} (hu : u ≠ 0) (hh : KHighest ε E μ u) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    μ b ≤ μ a := by
  have h := GlobalTheory.CompanionTheory.KWeightMajor.norm_identity hF hU he hh.1
  rw [hh.2 a b hab he, norm_zero] at h
  have hp : 0 < ‖u‖ ^ 2 := by have := norm_pos_iff.2 hu; positivity
  by_contra hc
  push Not at hc
  have : 0 < (μ b - μ a) * ‖u‖ ^ 2 := mul_pos (by linarith) hp
  have := sq_nonneg ‖E b a u‖
  nlinarith

lemma two_rhoC_int (ε : Fin n → Bool) (a : Fin n) : ∃ m : ℤ, ((2 : ℝ) • rhoC ε) a = m := by
  refine ⟨((univ.filter fun b => a < b ∧ ε b = ε a).card : ℤ) - ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℤ), ?_⟩
  simp only [Pi.smul_apply, rhoC, smul_eq_mul]
  push_cast
  ring

lemma vNormSq_nat (ε : Fin n → Bool) {μ : Fin n → ℝ} (hμ : ∀ a, ∃ m : ℤ, μ a = m) :
    ∃ k : ℕ, vNormSq ε μ = k := by
  choose m hm using hμ
  choose r hr using two_rhoC_int ε
  refine ⟨∑ a, ((m a + r a) ^ 2).toNat, ?_⟩
  have h : ∀ a, (((m a + r a) ^ 2).toNat : ℝ) = (μ a + ((2 : ℝ) • rhoC ε) a) ^ 2 := by
    intro a
    have h0 : (((m a + r a) ^ 2).toNat : ℤ) = (m a + r a) ^ 2 := Int.toNat_of_nonneg (sq_nonneg _)
    have h1 : (((m a + r a) ^ 2).toNat : ℝ) = (((m a + r a) ^ 2 : ℤ) : ℝ) := by exact_mod_cast h0
    rw [h1, hm a, hr a]
    push_cast
    ring
  rw [Nat.cast_sum]
  simp only [vNormSq, PI.UpqRep.nsq, PI.UpqRep.dot, Pi.add_apply]
  exact Finset.sum_congr rfl fun a _ => by rw [h a, sq]

theorem lktExists : LKTExists := by
  classical
  intro n ε V _ _ E hE hV hU hfin hint
  have hF : CompanionTheory.D.DSIC.KRel ε E := kRel_of_glRel hE
  have hK : CompanionTheory.D.DSIC.KUnit ε E := kUnit_of_isUnitary hU
  have hintK : ∀ (μ : Fin n → ℝ) (x : V), x ≠ 0 → KHighest ε E μ x → ∀ a, ∃ m : ℤ, μ a = m :=
    fun μ x hx hh => hint μ x hx hh.1
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨S, hfd, hS, hxS⟩ := hfin x
  obtain ⟨y, -, hy0, ν, hy⟩ := Formalism.REAL.highestWeightExists_holds V n ε E S hfd hF hK hS
    (fun h => hx (by simpa [h] using hxS))
  have hex : ∃ k : ℕ, ∃ (μ : Fin n → ℝ) (w : V), w ≠ 0 ∧ KHighest ε E μ w ∧ vNormSq ε μ = k := by
    obtain ⟨k, hk⟩ := vNormSq_nat ε (hintK ν y hy0 hy)
    exact ⟨k, ν, y, hy0, hy, hk⟩
  obtain ⟨γ, u, hu, hγ, hk⟩ := Nat.find_spec hex
  refine ⟨γ, u, hu, hγ, ?_, hintK γ u hu hγ, fun a b hab he => dominant_of_kHighest hF hK hu hγ hab he⟩
  intro μ w hw hμ
  obtain ⟨k, hk'⟩ := vNormSq_nat ε (hintK μ w hw hμ)
  rw [hk, hk']
  exact_mod_cast Nat.find_min' hex ⟨μ, w, hw, hμ, hk'⟩

end GlobalTheory.CompanionTheory.RgExhFarReg
end
end

namespace CompanionTheory.RgExh.U

theorem far_regular_exhaustion : CompanionTheory.RgExh.FarReg :=
  GlobalTheory.CompanionTheory.FarRegularityLevels.farReg_of_lkt_unitIneq_farNum GlobalTheory.CompanionTheory.RgExhFarReg.lktExists GlobalTheory.CompanionTheory.RgFarRen.renumber GlobalTheory.CompanionTheory.RgExhUnit.unitIneq
    (GlobalTheory.CompanionTheory.RgCOBlock.coBlock (GlobalTheory.CompanionTheory.RgExh.injU_of_injR (GlobalTheory.CompanionTheory.RgExhInjR.injR_of_vanKG
      (GlobalTheory.CompanionTheory.RgExhVanKG.vanKG_of GlobalTheory.CompanionTheory.ClusterNum.numKG))) GlobalTheory.CompanionTheory.GenCOUP.genCOU) GlobalTheory.CompanionTheory.RgExhFar.farNum

end CompanionTheory.RgExh.U
