module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfinite
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsCoefficientFieldChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidDecayOfOneParabolicBounds
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.SiegelDecay

theorem ratio_le_of_le {n : ℕ} {t : ℝ} (ht : 0 < t) {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) (i j : Fin n) (hij : i ≤ j) :
    ρ j / ρ i ≤ max 1 t⁻¹ ^ n := by
  set S := max 1 t⁻¹
  have hS1 : 1 ≤ S := le_max_left _ _
  have hstep : ∀ l : ℕ, ∀ (hl : l + 1 < n), ρ ⟨l + 1, hl⟩ ≤ S * ρ ⟨l, by omega⟩ := by
    intro l hl
    have h := hs ⟨l, by omega⟩ ⟨l + 1, hl⟩ rfl
    have h2 : ρ ⟨l + 1, hl⟩ ≤ t⁻¹ * ρ ⟨l, by omega⟩ := by
      rw [inv_mul_eq_div, le_div_iff₀ ht]; linarith
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hρ _).le)
  have hchain : ∀ d : ℕ, ∀ (a : ℕ) (ha : a + d < n),
      ρ ⟨a + d, ha⟩ ≤ S ^ d * ρ ⟨a, by omega⟩ := by
    intro d
    induction d with
    | zero => intro a ha; simp
    | succ d ih =>
      intro a ha
      calc ρ ⟨a + (d + 1), ha⟩ ≤ S * ρ ⟨a + d, by omega⟩ := hstep (a + d) ha
        _ ≤ S * (S ^ d * ρ ⟨a, by omega⟩) :=
            mul_le_mul_of_nonneg_left (ih a (by omega)) (by linarith)
        _ = S ^ (d + 1) * ρ ⟨a, by omega⟩ := by ring
  have hij' : (i : ℕ) ≤ j := hij
  have h1 := hchain (j - i) i (by omega)
  have hj : (⟨(i : ℕ) + (j - i), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
  rw [hj] at h1
  rw [div_le_iff₀ (hρ _)]
  calc ρ j ≤ S ^ ((j : ℕ) - i) * ρ i := h1
    _ ≤ S ^ n * ρ i :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hS1 (by omega)) (hρ _).le

theorem ratio_le_all {n : ℕ} {t : ℝ} (ht : 0 < t) {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) {A : ℝ} (hA1 : 1 ≤ A)
    (hA : ∀ i j : Fin n, i < j → ρ i / ρ j ≤ A ^ n) (i j : Fin n) :
    ρ i / ρ j ≤ max 1 t⁻¹ ^ n * A ^ n := by
  have hT : 1 ≤ max 1 t⁻¹ ^ n := one_le_pow₀ (le_max_left _ _)
  have hAn : 1 ≤ A ^ n := one_le_pow₀ hA1
  rcases lt_or_ge i j with h | h
  · exact (hA i j h).trans (le_mul_of_one_le_left (by linarith) hT)
  · exact (ratio_le_of_le ht hρ hs j i h).trans (le_mul_of_one_le_right (by linarith) hAn)

theorem le_of_ratio_le {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) (hprod : ∏ i, ρ i = 1)
    {R : ℝ} (hR : 1 ≤ R) (h : ∀ i j, ρ i / ρ j ≤ R) (i : Fin n) : ρ i ≤ R := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact i.elim0
  have h1 : ρ i ^ n = ∏ j, ρ i / ρ j := by
    rw [Finset.prod_div_distrib, hprod, div_one]
    simp
  have h2 : ρ i ^ n ≤ R ^ n := by
    rw [h1]
    calc ∏ j, ρ i / ρ j ≤ ∏ _j : Fin n, R :=
          Finset.prod_le_prod₀ (fun j _ => (div_pos (hρ i) (hρ j)).le) (fun j _ => h i j)
      _ = R ^ n := by simp
  exact (pow_le_pow_iff_left₀ (hρ i).le (by linarith) hn).1 h2

theorem inv_le_of_ratio_le {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) (hprod : ∏ i, ρ i = 1)
    {R : ℝ} (hR : 1 ≤ R) (h : ∀ i j, ρ i / ρ j ≤ R) (i : Fin n) : R⁻¹ ≤ ρ i := by
  have h1 : (ρ i)⁻¹ ≤ R := by
    refine le_of_ratio_le (ρ := fun i => (ρ i)⁻¹) (fun i => inv_pos.2 (hρ i)) ?_ hR ?_ i
    · rw [Finset.prod_inv_distrib, hprod, inv_one]
    · intro i j
      have := h j i
      rwa [inv_div_inv]
  exact inv_le_of_inv_le₀ (hρ i) h1

theorem one_le_rpow_mul_prod {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) {R : ℝ} (hR : 1 ≤ R)
    (hb : ∀ i, ρ i ≤ R) (hb' : ∀ i, R⁻¹ ≤ ρ i) (lam : Fin n → ℝ) :
    1 ≤ R ^ (∑ i, |lam i|) * ∏ i, ρ i ^ lam i := by
  have hR0 : 0 < R := by linarith
  rw [Real.rpow_sum_of_pos hR0, ← Finset.prod_mul_distrib]
  calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => ?_)
  rcases le_total 0 (lam i) with hl | hl
  · rw [abs_of_nonneg hl, ← Real.mul_rpow hR0.le (hρ i).le]
    refine Real.one_le_rpow ?_ hl
    have := mul_le_mul_of_nonneg_left (hb' i) hR0.le
    rwa [mul_inv_cancel₀ hR0.ne'] at this
  · have hρ' : ρ i ^ lam i = ((ρ i)⁻¹) ^ (-lam i) := by
      rw [Real.inv_rpow (hρ i).le, Real.rpow_neg (hρ i).le, inv_inv]
    rw [abs_of_nonpos hl, hρ', ← Real.mul_rpow hR0.le (inv_pos.2 (hρ i)).le]
    refine Real.one_le_rpow ?_ (by linarith)
    rw [← div_eq_mul_inv, one_le_div (hρ i)]
    exact hb i

theorem one_le_weight {n : ℕ} {t : ℝ} (ht : 0 < t) {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hs : ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) (hprod : ∏ i, ρ i = 1)
    {A : ℝ} (hA1 : 1 ≤ A) (hA : ∀ i j : Fin n, i < j → ρ i / ρ j ≤ A ^ n)
    (lam : Fin n → ℝ) (M : ℕ) (hM : (n : ℝ) * ∑ i, |lam i| ≤ M) :
    1 ≤ (max 1 t⁻¹ ^ n) ^ (∑ i, |lam i|) * A ^ M * ∏ i, ρ i ^ lam i := by
  have hT : 1 ≤ max 1 t⁻¹ ^ n := one_le_pow₀ (le_max_left _ _)
  have hAn : 1 ≤ A ^ n := one_le_pow₀ hA1
  have hA0 : 0 < A := by linarith
  have hR : 1 ≤ max 1 t⁻¹ ^ n * A ^ n := one_le_mul_of_one_le_of_one_le hT hAn
  have hrat := ratio_le_all ht hρ hs hA1 hA
  have h := one_le_rpow_mul_prod hρ hR (le_of_ratio_le hρ hprod hR hrat)
    (inv_le_of_ratio_le hρ hprod hR hrat) lam
  have hP : 0 ≤ ∏ i, ρ i ^ lam i :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hρ i).le _
  have hpow : (A ^ n) ^ (∑ i, |lam i|) ≤ A ^ M := by
    rw [← Real.rpow_natCast A n, ← Real.rpow_mul hA0.le, ← Real.rpow_natCast A M]
    exact Real.rpow_le_rpow_of_exponent_le hA1 hM
  rw [Real.mul_rpow (by linarith) (by linarith)] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hP)
  exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by linarith) _)

theorem rapid_decay_of_one_parabolic_bounds : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ), Continuous φ → (∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) →
    (∀ b ∈ ω, (IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det b) : ℝ) = 1) → ∀ t : ℝ, 0 < t → ∀ (r : ℕ) (hr0 : 0 < r) (hrn : r < n), ∃ N : ℕ, ∀ k : ℕ, ∃ C : ℝ,
      ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
        ∏ i, ρ i = 1 → ∀ kk ∈ maxCompact (K := K) (n := n), ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin n, ρ i / ρ j ≤ R) →
          ‖φ (b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk)‖ ≤
            C * (ρ ⟨r, hrn⟩ / ρ ⟨r - 1, lt_of_le_of_lt (Nat.sub_le r 1) hrn⟩) ^ k * R ^ N) → (∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) →
    (∀ b ∈ ω, (IdeleGroup.ideleModule K (Matrix.GeneralLinearGroup.det b) : ℝ) = 1) → ∀ t : ℝ, 0 < t → ∀ lam : Fin n → ℝ, ∃ C : ℝ,
      ∀ b ∈ ω, ∀ (r : Fin n → ℝ) (hr : ∀ i, 0 < r i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * r j ≤ r i) →
        ∏ i, r i = 1 → ∀ k ∈ maxCompact (K := K) (n := n),
          ‖φ (b * diagUnits n (fun i => posIdele (K := K) (r i) (hr i)) * k)‖ ≤ C * ∏ i, r i ^ lam i) := by
  intro K _ _ n φ hφ hyp ω hω hωB hdet t ht lam
  rcases Nat.lt_or_ge n 2 with hn | hn
  · obtain ⟨C, hC⟩ := (hω.mul (isCompact_maxCompact (K := K) (n := n))).exists_bound_of_continuousOn
      hφ.continuousOn
    refine ⟨C, fun b hb r hr hs hprod k hk => ?_⟩
    have hr1 : ∀ i, r i = 1 := by
      intro i
      have h1 : n = 1 := by
        have := i.pos
        omega
      subst h1
      have hi : i = 0 := Subsingleton.elim _ _
      simpa [hi] using hprod
    have hd : diagUnits n (fun i => posIdele (K := K) (r i) (hr i)) = 1 := by
      have h1 : (fun i => posIdele (K := K) (r i) (hr i)) = 1 := by
        funext i
        have h2 : (⟨r i, hr i⟩ : {x : ℝ // 0 < x}) = 1 := Subtype.ext (hr1 i)
        change posIdeleHom (K := K) ⟨r i, hr i⟩ = 1
        rw [h2, map_one]
      rw [h1, map_one]
    have hP : ∏ i, r i ^ lam i = 1 :=
      Finset.prod_eq_one fun i _ => by rw [hr1 i, Real.one_rpow]
    rw [hd, hP, mul_one, mul_one]
    exact hC _ (Set.mul_mem_mul hb hk)
  · set T : ℝ := max 1 t⁻¹ ^ n with hTdef
    have hT1 : 1 ≤ T := one_le_pow₀ (le_max_left _ _)
    have hT0 : 0 < T := by linarith
    set L : ℝ := ∑ i, |lam i| with hL
    obtain ⟨M, hM⟩ := exists_nat_ge ((n : ℝ) * L)
    have key : ∀ (r : ℕ) (hr : 0 < r) (hrn : r < n), ∃ D : ℝ, ∀ b ∈ ω, ∀ (ρ : Fin n → ℝ)
        (hρ : ∀ i, 0 < ρ i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) → ∏ i, ρ i = 1 →
        ∀ kk ∈ maxCompact (K := K) (n := n),
        (∀ i j : Fin n, i < j → ρ i / ρ j ≤ max 1 (ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩) ^ n) →
        ‖φ (b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk)‖ ≤
          max D 0 * ∏ i, ρ i ^ lam i := by
      intro r hr hrn
      obtain ⟨N, hN⟩ := hyp ω hω hωB hdet t ht r hr hrn
      obtain ⟨C0, hC0⟩ := hN 0
      obtain ⟨C1, hC1⟩ := hN (n * N + M)
      set E : ℝ := max C0 0 + max C1 0 with hE
      have hE0 : 0 ≤ E := add_nonneg (le_max_right _ _) (le_max_right _ _)
      have hC0E : C0 ≤ E := (le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _))
      have hC1E : C1 ≤ E := (le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _))
      have hTL : 0 < T ^ L := Real.rpow_pos_of_pos hT0 _
      have hD0 : 0 ≤ E * T ^ N * T ^ L := by positivity
      refine ⟨E * T ^ N * T ^ L, ?_⟩
      rw [max_eq_left hD0]
      intro b hb ρ hρ hs hprod kk hkk hmax
      have hgain : ρ ⟨r, hrn⟩ / ρ ⟨r - 1, lt_of_le_of_lt (Nat.sub_le r 1) hrn⟩ =
          (ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩)⁻¹ := by rw [inv_div]
      obtain ⟨α, hα⟩ : ∃ α, α = ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩ := ⟨_, rfl⟩
      rw [← hα] at hmax hgain
      have hα0 : 0 < α := by rw [hα]; exact div_pos (hρ _) (hρ _)
      set P : ℝ := ∏ i, ρ i ^ lam i with hPdef
      have hP : 0 ≤ P := Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hρ i).le _
      rcases le_or_gt α 1 with hα1 | hα1
      · rw [max_eq_left hα1] at hmax
        have hone := one_le_weight ht hρ hs hprod le_rfl hmax lam M hM
        rw [one_pow, mul_one] at hone
        have h := hC0 b hb ρ hρ hs hprod kk hkk T hT1 fun i j => by
          simpa using ratio_le_all ht hρ hs le_rfl hmax i j
        rw [pow_zero, mul_one] at h
        calc _ ≤ C0 * T ^ N := h
          _ ≤ E * T ^ N := mul_le_mul_of_nonneg_right hC0E (by positivity)
          _ ≤ E * T ^ N * (T ^ L * P) := le_mul_of_one_le_right (by positivity) hone
          _ = E * T ^ N * T ^ L * P := by ring
      · rw [max_eq_right hα1.le] at hmax
        have hone := one_le_weight ht hρ hs hprod hα1.le hmax lam M hM
        have hαn : 1 ≤ α ^ n := one_le_pow₀ hα1.le
        have h := hC1 b hb ρ hρ hs hprod kk hkk (T * α ^ n)
          (one_le_mul_of_one_le_of_one_le hT1 hαn) (ratio_le_all ht hρ hs hα1.le hmax)
        rw [hgain] at h
        have hpow : (α⁻¹) ^ (n * N + M) * (T * α ^ n) ^ N = T ^ N * (α ^ M)⁻¹ := by
          have ha : α ^ (n * N) ≠ 0 := (pow_pos hα0 _).ne'
          rw [mul_pow, ← pow_mul α n N, inv_pow, pow_add, mul_inv]
          calc (α ^ (n * N))⁻¹ * (α ^ M)⁻¹ * (T ^ N * α ^ (n * N))
              = ((α ^ (n * N))⁻¹ * α ^ (n * N)) * (T ^ N * (α ^ M)⁻¹) := by ring
            _ = T ^ N * (α ^ M)⁻¹ := by rw [inv_mul_cancel₀ ha, one_mul]
        have hX : 0 ≤ T ^ N * (α ^ M)⁻¹ := by positivity
        calc _ ≤ C1 * (α⁻¹) ^ (n * N + M) * (T * α ^ n) ^ N := h
          _ = C1 * (T ^ N * (α ^ M)⁻¹) := by rw [mul_assoc, hpow]
          _ ≤ E * (T ^ N * (α ^ M)⁻¹) := mul_le_mul_of_nonneg_right hC1E hX
          _ ≤ E * (T ^ N * (α ^ M)⁻¹) * (T ^ L * α ^ M * P) :=
              le_mul_of_one_le_right (mul_nonneg hE0 hX) hone
          _ = E * T ^ N * T ^ L * P := by
              have : α ^ M ≠ 0 := (pow_pos hα0 _).ne'
              field_simp
    choose D hD using key
    refine ⟨∑ r : Fin n, if h : 0 < (r : ℕ) then max (D r h r.2) 0 else 0, ?_⟩
    intro b hb ρ hρ hs hprod k hk
    obtain ⟨r, hr, hrn, hratio⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_le_max_pow hn ρ hρ
    have hP : 0 ≤ ∏ i, ρ i ^ lam i :=
      Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hρ i).le _
    refine (hD r hr hrn b hb ρ hρ hs hprod k hk hratio).trans
      (mul_le_mul_of_nonneg_right ?_ hP)
    have h1 := Finset.single_le_sum (f := fun r : Fin n =>
      if h : 0 < (r : ℕ) then max (D r h r.2) 0 else 0)
      (fun r _ => by split_ifs <;> simp) (Finset.mem_univ ⟨r, hrn⟩)
    simpa only [hr, dif_pos] using h1

end GlobalTheory.CompanionTheory.SiegelDecay
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientContinuous
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientContinuous
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem continuous_coef : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), IsSmooth T → ∀ (v : V) (v' : V'), Continuous (coef T B v v') := by
  intro k _ _ _ _ n V V' _ _ _ _ T B hT v v'
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hcont : Continuous fun y : Fin n → k =>
      GlobalTheory.CompanionTheory.MirFourier.unipIn k n (Multiplicative.ofAdd (y - x)) :=
    (GlobalTheory.CompanionTheory.MirFourier.continuous_unipIn n).comp
      (continuous_ofAdd.comp (continuous_id.sub continuous_const))
  have hopen : IsOpen {y : Fin n → k |
      T (GlobalTheory.CompanionTheory.MirFourier.unipIn k n (Multiplicative.ofAdd (y - x))) v = v} :=
    (hT v).preimage hcont
  have hx : x ∈ {y : Fin n → k |
      T (GlobalTheory.CompanionTheory.MirFourier.unipIn k n (Multiplicative.ofAdd (y - x))) v = v} := by
    simp
  filter_upwards [hopen.mem_nhds hx] with y hy
  have hy' : T (GlobalTheory.CompanionTheory.MirFourier.unipIn k n (Multiplicative.ofAdd (y - x))) v = v := hy
  have hsplit : GlobalTheory.CompanionTheory.MirPair.uM n y =
      GlobalTheory.CompanionTheory.MirPair.uM n x * GlobalTheory.CompanionTheory.MirFourier.unipIn k n (Multiplicative.ofAdd (y - x)) := by
    unfold GlobalTheory.CompanionTheory.MirPair.uM
    rw [← map_mul, ← ofAdd_add, add_sub_cancel]
  unfold GlobalTheory.CompanionTheory.MirPair.coef
  rw [hsplit, map_mul, Module.End.mul_apply, hy']

end GlobalTheory.CompanionTheory.MirPair
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientContinuousStatement
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_coefficient_continuous : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), IsSmooth T → ∀ (v : V) (v' : V'), Continuous (coef T B v v') := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.continuous_coef | exact GlobalTheory.CompanionTheory.MirPair.continuous_coef | (intros; apply GlobalTheory.CompanionTheory.MirPair.continuous_coef <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumFrameIdem
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

abbrev FrameIx (r : ℕ) : Type := Option (Fin r ⊕ Fin r)

variable {E : Type} [Field E] {n r : ℕ}

def frameIdem (S : E →+* E) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) :
    FrameIx r → Matrix (Fin n) (Fin n) E
  | some (Sum.inl i) => X * single i i (1 : E) * (cT S Y * J)
  | some (Sum.inr i) => Y * single i i (1 : E) * (cT S X * J)
  | none => 1 - X * (cT S Y * J) - Y * (cT S X * J)

def frameWt (t : Fin r → ℝ) : FrameIx r → ℝ
  | some (Sum.inl i) => t i
  | some (Sum.inr i) => (t i)⁻¹
  | none => 1

def frameLev (s : Fin r) : FrameIx r → ℕ
  | some (Sum.inl i) => if i ≤ s then 2 else 1
  | some (Sum.inr i) => if i ≤ s then 0 else 1
  | none => 1

theorem sum_frameIdem (S : E →+* E) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) :
    ∑ α, frameIdem S J X Y α = 1 := by
  have key : ∀ (A : Matrix (Fin n) (Fin r) E) (B : Matrix (Fin r) (Fin n) E),
      ∑ i : Fin r, (A * (Matrix.single i i (1 : E) : Matrix (Fin r) (Fin r) E) * B : Matrix (Fin n) (Fin n) E) = A * B := fun A B => by
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  simp only [frameIdem]
  rw [key, key]
  abel

theorem frameWt_pos {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) (α : FrameIx r) : 0 < frameWt t α := by
  rcases α with _ | i | i
  · exact one_pos
  · exact ht i
  · exact inv_pos.2 (ht i)

end GlobalTheory.CompanionTheory.RapidDecay

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalGeneralizedSpaceSpanClosed
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalGeneralizedSpaceSpanClosed
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CuspSubspace

theorem mem_of_mem_span_cuspForms :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E)))
      (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W)
      (J : Set (Module.End ℂ (Sm E a))),
      ∀ φ ∈ Submodule.span ℂ {φ : Sm E a | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1},
        φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1 := by
  intro E _ _ _ a L W _ _ ρ J φ hφ
  induction hφ using Submodule.span_induction with
  | mem x h => exact h
  | zero =>
    refine ⟨(GlobalTheory.CompanionTheory.AffglAssembly.genSub L ρ J).zero_mem, ?_⟩
    intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    change ∫ _ in 𝓕, (0 : ℂ) ∂μ = 0
    simp
  | add x y _ _ hx hy =>
    refine ⟨(GlobalTheory.CompanionTheory.AffglAssembly.genSub L ρ J).add_mem hx.1 hy.1, ?_⟩
    intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    have ix := (GlobalTheory.CompanionTheory.ConstTerm.integrableOn_fundamentalDomain E a r x hx.1.1.left hx.1.1.level μ 𝓕 hμ hF).2 g
    have iy := (GlobalTheory.CompanionTheory.ConstTerm.integrableOn_fundamentalDomain E a r y hy.1.1.left hy.1.1.level μ 𝓕 hμ hF).2 g
    have e : ∫ u in 𝓕, (x + y).1 (unip u * g) ∂μ =
        (∫ u in 𝓕, x.1 (unip u * g) ∂μ) + ∫ u in 𝓕, y.1 (unip u * g) ∂μ := integral_add ix iy
    rw [e, hx.2 r hr hr' μ 𝓕 hμ hF g, hy.2 r hr hr' μ 𝓕 hμ hF g, add_zero]
  | smul c x _ hx =>
    refine ⟨(GlobalTheory.CompanionTheory.AffglAssembly.genSub L ρ J).smul_mem c hx.1, ?_⟩
    intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    have e : ∫ u in 𝓕, (c • x).1 (unip u * g) ∂μ = c • ∫ u in 𝓕, x.1 (unip u * g) ∂μ :=
      integral_smul c _
    rw [e, hx.2 r hr hr' μ 𝓕 hμ hF g, smul_zero]

end GlobalTheory.CompanionTheory.CuspSubspace

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalGeneralizedSpaceSpanClosedStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_generalized_space_span_closed : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))), ∀ φ ∈ Submodule.span ℂ {φ : Sm E a | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1}, φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1 := by
  first | exact @GlobalTheory.CompanionTheory.CuspSubspace.mem_of_mem_span_cuspForms | exact GlobalTheory.CompanionTheory.CuspSubspace.mem_of_mem_span_cuspForms | (intros; apply GlobalTheory.CompanionTheory.CuspSubspace.mem_of_mem_span_cuspForms <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKerLeComapMap
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZNuPair

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def firstEmb (d : Fin 2 → ℕ) : GL (Fin (d 0)) k →* Levi k (fun a => Fin (d a)) :=
  MonoidHom.mulSingle (fun a => GL (Fin (d a)) k) 0

def secondEmb (d : Fin 2 → ℕ) : GL (Fin (d 1)) k →* Levi k (fun a => Fin (d a)) :=
  MonoidHom.mulSingle (fun a => GL (Fin (d a)) k) 1

theorem firstEmb_comm (d : Fin 2 → ℕ) (g : GL (Fin (d 0)) k) (h : GL (Fin (d 1)) k) :
    firstEmb d g * secondEmb d h = secondEmb d h * firstEmb d g :=
  Pi.mulSingle_commute (f := fun a => GL (Fin (d a)) k) (by decide : (0 : Fin 2) ≠ 1) g h

variable {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

abbrev whitKer (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X) :
    Submodule ℂ X :=
  twKer (J.comp (secondEmb d)) (unipB k (Fin (d 1))) (whitChar ψ (d 1))

theorem whitKer_le_comap (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    (g : GL (Fin (d 0)) k) : whitKer ψ d J ≤ (whitKer ψ d J).comap (J (firstEmb d g)) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, v, rfl⟩
  refine Submodule.subset_span ⟨u, J (firstEmb d g) v, ?_⟩
  simp only [map_sub, map_smul, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, firstEmb_comm]

def whit2 (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X) :
    Representation ℂ (GL (Fin (d 0)) k) (X ⧸ whitKer ψ d J) where
  toFun g := (whitKer ψ d J).mapQ (whitKer ψ d J) (J (firstEmb d g)) (whitKer_le_comap ψ d J g)
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp

theorem whit2_mk (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    (g : GL (Fin (d 0)) k) (v : X) :
    whit2 ψ d J g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (J (firstEmb d g) v) := rfl

theorem whitKer_le_comap_map (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {J : Representation ℂ (Levi k fun a => Fin (d a)) X}
    {J' : Representation ℂ (Levi k fun a => Fin (d a)) Y} (f : J.IntertwiningMap J') :
    whitKer ψ d J ≤ (whitKer ψ d J').comap f.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, v, rfl⟩
  refine Submodule.subset_span ⟨u, f v, ?_⟩
  simp [f.isIntertwining]

def whitMap (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {J : Representation ℂ (Levi k fun a => Fin (d a)) X}
    {J' : Representation ℂ (Levi k fun a => Fin (d a)) Y} (f : J.IntertwiningMap J') :
    (whit2 ψ d J).IntertwiningMap (whit2 ψ d J') :=
  .mk ((whitKer ψ d J).mapQ (whitKer ψ d J') f.toLinearMap (whitKer_le_comap_map ψ d f)) (fun g => by
    ext v
    simp [whit2_mk, f.isIntertwining])

end

end GlobalTheory.CompanionTheory.BZNuPair

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactSubgroupOfFinset
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.UnipExhaust

theorem exists_compact_subgroup_of_finset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ)
      (s : Finset (GL (Fin N) k)), (↑s : Set (GL (Fin N) k)) ⊆ unipB k (Fin N) →
      ∃ L : Subgroup (GL (Fin N) k), L ≤ unipB k (Fin N) ∧ (↑s : Set (GL (Fin N) k)) ⊆ L ∧
        IsCompact (L : Set (GL (Fin N) k)) := by
  intro k _ _ _ _ N s hs
  let c : Fin N → ℤ := fun i => ((i : ℕ) : ℤ)
  have heq : unipB k (Fin N) = GlobalTheory.InertSupp.unipOf k c := by
    ext g
    rw [GlobalTheory.SmGL.mem_unipB, GlobalTheory.InertSupp.mem_unipOf]
    constructor
    · rintro ⟨h1, h2⟩ i j hij
      have hji : j ≤ i := by
        dsimp [c] at hij
        rw [not_lt] at hij
        exact Fin.le_def.2 (by exact_mod_cast hij)
      rcases hji.lt_or_eq with h | h
      · rw [h1 i j h, Matrix.one_apply_ne (ne_of_gt h)]
      · subst h; rw [h2 j, Matrix.one_apply_eq]
    · intro h
      refine ⟨fun i j hji => ?_, fun i => ?_⟩
      · have : ¬ ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by
          have := Fin.lt_def.1 hji
          omega
        rw [h i j this, Matrix.one_apply_ne (ne_of_gt hji)]
      · rw [h i i (lt_irrefl _), Matrix.one_apply_eq]
  have hQU : (↑s : Set (GL (Fin N) k)) ⊆ GlobalTheory.InertSupp.unipOf k c := by
    simpa [← heq] using hs
  let V : ℕ → Set (GL (Fin N) k) := fun m =>
    (GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c m) : Set (GL (Fin N) k)) ∪ (GlobalTheory.InertSupp.unipOf k c : Set _)ᶜ
  have hVo : ∀ m, IsOpen (V m) := fun m =>
    (GlobalTheory.UnipCptSub.isOpen_grp c m).union (GlobalTheory.UnipCompact.isClosed_unipOf c).isOpen_compl
  have hVmono : Monotone V := by
    intro m M hmM g hg
    rcases hg with hg | hg
    · by_cases hu : g ∈ GlobalTheory.InertSupp.unipOf k c
      · left
        have key : ∀ x : GL (Fin N) k, x ∈ GlobalTheory.InertSupp.unipOf k c →
            (∀ i j, GlobalTheory.IwahoriInj.Deep ((m : ℤ) * (c i - c j)) (x.val i j)) →
            ∀ i j, GlobalTheory.IwahoriInj.Deep ((M : ℤ) * (c i - c j)) (x.val i j) := by
          intro x hx hd i j
          by_cases hij : c i < c j
          · refine (hd i j).mono ?_
            have : (m : ℤ) ≤ M := by exact_mod_cast hmM
            nlinarith
          · rw [GlobalTheory.InertSupp.mem_unipOf.1 hx i j hij]
            by_cases e : i = j
            · subst e
              simp [GlobalTheory.IwahoriInj.deep_zero_iff]
            · simp [Matrix.one_apply_ne e, GlobalTheory.IwahoriInj.deep_zero]
        exact ⟨key g hu hg.1, key g⁻¹ (inv_mem hu) hg.2⟩
      · exact Or.inr hu
    · exact Or.inr hg
  have hcov : (↑s : Set (GL (Fin N) k)) ⊆ ⋃ m, V m := fun g hg =>
    Set.mem_iUnion.2 (((GlobalTheory.UnipCompact.eventually_mem_grp (hQU hg)).exists).imp fun _ h => Or.inl h)
  obtain ⟨M, hM⟩ := s.finite_toSet.isCompact.elim_directed_cover V hVo hcov hVmono.directed_le
  refine ⟨GlobalTheory.IwahoriInj.grp k (GlobalTheory.UnipCompact.conc_mul_sub c M) ⊓ unipB k (Fin N), inf_le_right, ?_, ?_⟩
  · intro g hg
    refine ⟨?_, hs hg⟩
    rcases hM hg with h | h
    · exact h
    · exact absurd (hQU hg) h
  · rw [Subgroup.coe_inf]
    apply (GlobalTheory.IwahoriInj.isCompact_grp _).inter_right
    rw [heq]
    exact GlobalTheory.UnipCompact.isClosed_unipOf _

end GlobalTheory.CompanionTheory.UnipExhaust
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreTranslatePreservesCuspSpace
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreTranslatePreservesCuspSpace
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CuspFinGL.Transl

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem rt_comm_of_central {h : GA E a} (hc : ∀ g : GA E a, h * g = g * h) (x : GA E a) (φ : Sm E a) :
    rt E a x (rt E a h φ) = rt E a h (rt E a x φ) := by
  refine Subtype.ext (funext fun g => ?_)
  change φ.1 (g * x * h) = φ.1 (g * h * x)
  rw [mul_assoc g x h, mul_assoc g h x, hc x]

theorem rt_injective (h : GA E a) : Function.Injective (rt E a h) := fun φ ψ e => by
  refine Subtype.ext (funext fun g => ?_)
  have := congrArg (fun f : Sm E a => f.1 (g * h⁻¹)) e
  simpa using this

theorem isAutForm_rt_of_central {h : GA E a} (hc : ∀ g : GA E a, h * g = g * h) {φ : Sm E a}
    (hφ : IsAutForm φ) : IsAutForm (rt E a h φ) := by
  refine { left := ?_, level := ?_, kfin := ?_, zfin := ?_, growth := ?_ }
  · intro γ g
    change φ.1 (ratGL E a γ * g * h) = φ.1 (g * h)
    rw [mul_assoc, hφ.left]
  · have e : {k | finRep E a k (rt E a h φ) = rt E a h φ} = {k | finRep E a k φ = φ} := by
      ext k
      change rt E a (finGL E a k) (rt E a h φ) = rt E a h φ ↔ rt E a (finGL E a k) φ = φ
      rw [rt_comm_of_central hc]
      exact (rt_injective h).eq_iff
    rw [e]
    exact hφ.level
  · have := hφ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map (rt E a h))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨cptRep E a k φ, Submodule.subset_span ⟨k, rfl⟩, (rt_comm_of_central hc _ φ).symm⟩
  · have := hφ.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)).map (rt E a h))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z φ, Submodule.subset_span ⟨z, hz, rfl⟩, ?_⟩
    exact (LinearMap.congr_fun (GlobalTheory.CompanionTheory.CTFin.Slice1.commute_rt_of_mem_Zalg hz h).eq φ).symm
  · intro g
    obtain ⟨C, N, hb⟩ := hφ.growth (g * h)
    refine ⟨C, N, fun y => ?_⟩
    have e : (rt E a h φ).1 (g * infGL E a y) = φ.1 (g * h * infGL E a y) := by
      change φ.1 (g * infGL E a y * h) = _
      rw [mul_assoc g _ h, mul_assoc g h, hc]
    rw [e]
    exact hb y

theorem rt_splitCentre_mem : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))) (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))), J ⊆ Zalg E a →
    ∀ φ : Sm E a, φ ∈ genSpace L ρ J → IsCuspidal φ.1 → ∀ t : ℝ,
      rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ ∈ genSpace L ρ J ∧
        IsCuspidal (rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ).1 := by
  intro E _ _ _ a L W _ _ ρ J hJ φ hφ hcusp t
  set h := GlobalTheory.UnitaryBC.splitCentre E a t with hh
  have hc : ∀ g : GA E a, h * g = g * h := GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t
  obtain ⟨hA, hL, hK, hZ⟩ := hφ
  refine ⟨⟨isAutForm_rt_of_central hc hA, fun k hk => ?_, fun g => ?_, fun z hz => ?_⟩, ?_⟩
  · change rt E a (finGL E a k) (rt E a h φ) = rt E a h φ
    rw [rt_comm_of_central hc]
    exact congrArg (rt E a h) (hL k hk)
  · have e : (fun k : Kinf E a => (cptRep E a k (rt E a h φ)).1 g) =
        fun k : Kinf E a => (cptRep E a k φ).1 (g * h) := by
      funext k
      exact congrArg (fun f : Sm E a => f.1 g) (rt_comm_of_central hc _ φ)
    rw [e]
    exact hK (g * h)
  · have e := LinearMap.congr_fun (GlobalTheory.CompanionTheory.CTFin.Slice1.commute_rt_of_mem_Zalg (hJ hz) h).eq φ
    rw [mul_apply_eq_comp, mul_apply_eq_comp] at e
    rw [e, hZ z hz, map_zero]
  · intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    have e : ∀ x : BlockIx a r → Ad E, (rt E a h φ).1 (unip x * g) = φ.1 (unip x * (g * h)) :=
      fun x => congrArg φ.1 (mul_assoc _ _ _)
    simp only [e]
    exact hcusp r hr hr' μ 𝓕 hμ hF (g * h)

end GlobalTheory.CompanionTheory.CuspFinGL.Transl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreTranslatePreservesCuspSpaceStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_centre_translate_preserves_cusp_space : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))), J ⊆ Zalg E a → ∀ φ : Sm E a, φ ∈ genSpace L ρ J → IsCuspidal φ.1 → ∀ t : ℝ, rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ ∈ genSpace L ρ J ∧ IsCuspidal (rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ).1 := by
  first | exact @GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem | exact GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem | (intros; apply GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimOfAnnihilatingPolyEigenspaces
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimOfAnnihilatingPolyEigenspaces
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.LinAlg

open Polynomial

theorem finiteDimensional_of_roots_of_eigenspaces {M : Type} [AddCommGroup M] [Module ℂ M]
    (T : Module.End ℂ M) (s : Multiset ℂ) :
    ∀ V : Submodule ℂ M, (∀ v ∈ V, T v ∈ V) →
      (∀ v ∈ V, aeval T ((s.map fun a => (X - C a : ℂ[X])).prod) v = 0) →
      (∀ c : ℂ, FiniteDimensional ℂ (Submodule.span ℂ {v | v ∈ V ∧ T v = c • v})) →
      FiniteDimensional ℂ V := by
  induction s using Multiset.induction_on with
  | empty =>
    intro V _ hker _
    have hbot : V = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      exact (Submodule.mem_bot ℂ).mpr (by simpa using hker v hv)
    subst hbot
    infer_instance
  | cons a s ih =>
    intro V hV hker hfin
    set f : Module.End ℂ M := aeval T (X - C a : ℂ[X]) with hf
    have hfv : ∀ v, f v = T v - a • v := by
      intro v
      simp [f]
    have hWV : ∀ w ∈ V.map f, w ∈ V := by
      rintro w ⟨v, hv, rfl⟩
      rw [hfv]
      exact V.sub_mem (hV v hv) (V.smul_mem a hv)
    have hW1 : ∀ w ∈ V.map f, T w ∈ V.map f := by
      rintro w ⟨v, hv, rfl⟩
      refine ⟨T v, hV v hv, ?_⟩
      simp [hfv, map_sub, map_smul]
    have hW2 : ∀ w ∈ V.map f,
        aeval T ((s.map fun b => (X - C b : ℂ[X])).prod) w = 0 := by
      rintro w ⟨v, hv, rfl⟩
      have h := hker v hv
      rw [Multiset.map_cons, Multiset.prod_cons, mul_comm, map_mul] at h
      exact h
    have hW3 : ∀ c : ℂ, FiniteDimensional ℂ
        (Submodule.span ℂ {v | v ∈ V.map f ∧ T v = c • v}) := by
      intro c
      haveI := hfin c
      have hsub : {v | v ∈ V.map f ∧ T v = c • v} ⊆ {v | v ∈ V ∧ T v = c • v} :=
        fun v hv => ⟨hWV v hv.1, hv.2⟩
      exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)
    have hWfin : FiniteDimensional ℂ (V.map f) := ih (V.map f) hW1 hW2 hW3
    apply Module.Finite.iff_fg.mpr
    apply Submodule.fg_of_fg_map_of_fg_inf_ker f
    · exact Module.Finite.iff_fg.mp hWfin
    · haveI := hfin a
      have hle : V ⊓ LinearMap.ker f ≤ Submodule.span ℂ {v | v ∈ V ∧ T v = a • v} := by
        rintro v ⟨hv, hk⟩
        apply Submodule.subset_span
        refine ⟨hv, ?_⟩
        have h0 : f v = 0 := hk
        rw [hfv, sub_eq_zero] at h0
        exact h0
      haveI := Submodule.finiteDimensional_of_le hle
      exact Module.Finite.iff_fg.mp inferInstance

theorem finiteDimensional_of_polynomial_of_eigenspaces :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (V : Submodule ℂ M),
      (∀ v ∈ V, T v ∈ V) → ∀ p : Polynomial ℂ, p ≠ 0 →
      (∀ v ∈ V, Polynomial.aeval T p v = 0) →
      (∀ c : ℂ, FiniteDimensional ℂ (Submodule.span ℂ {v | v ∈ V ∧ T v = c • v})) →
      FiniteDimensional ℂ V := by
  intro M _ _ T V hV p hp hker hfin
  have hsplit : p = C p.leadingCoeff * (p.roots.map fun a => (X - C a : ℂ[X])).prod := by
    first
      | exact Polynomial.eq_prod_roots_of_splits_id (IsAlgClosed.splits p)
      | exact (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
          (IsAlgClosed.card_roots_eq_natDegree (k := ℂ))).symm
  refine finiteDimensional_of_roots_of_eigenspaces T p.roots V hV ?_ hfin
  intro v hv
  have h := hker v hv
  rw [hsplit, map_mul, Polynomial.aeval_C] at h
  have h' : p.leadingCoeff • aeval T ((p.roots.map fun a => (X - C a : ℂ[X])).prod) v = 0 := by
    rw [← h, Algebra.algebraMap_eq_smul_one]
    rfl
  exact (smul_eq_zero.mp h').resolve_left (Polynomial.leadingCoeff_ne_zero.mpr hp)

end GlobalTheory.CompanionTheory.LinAlg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimOfAnnihilatingPolyEigenspacesStatement
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dim_of_annihilating_poly_eigenspaces : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (V : Submodule ℂ M), (∀ v ∈ V, T v ∈ V) → ∀ p : Polynomial ℂ, p ≠ 0 → (∀ v ∈ V, Polynomial.aeval T p v = 0) → (∀ c : ℂ, FiniteDimensional ℂ (Submodule.span ℂ {v | v ∈ V ∧ T v = c • v})) → FiniteDimensional ℂ V := by
  first | exact @GlobalTheory.CompanionTheory.LinAlg.finiteDimensional_of_polynomial_of_eigenspaces | exact GlobalTheory.CompanionTheory.LinAlg.finiteDimensional_of_polynomial_of_eigenspaces | (intros; apply GlobalTheory.CompanionTheory.LinAlg.finiteDimensional_of_polynomial_of_eigenspaces <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPFinThetaGL
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj)

namespace GlobalTheory.CompanionTheory.AdelEqProof

theorem map_thetaR {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ∀ x, f (σ x) = τ (f x)) (n : ℕ) (g : GL (Fin n) A) :
    GeneralLinearGroup.map f (thetaR σ n g) = thetaR τ n (GeneralLinearGroup.map f g) := by
  apply Units.ext
  ext i j
  change f (σ ((g⁻¹ : GL (Fin n) A).val j i)) = τ (((GeneralLinearGroup.map f g)⁻¹ : GL (Fin n) B).val j i)
  rw [← map_inv]
  exact h _

theorem map_PhiU {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n : ℕ) :
    GeneralLinearGroup.map f (PhiU n A) = PhiU n B := by
  apply Units.ext
  ext i j
  change f ((PhiU n A).val i j) = (PhiU n B).val i j
  rw [phiU_val, phiU_val]
  simp [GlobalTheory.Tw.Phi, apply_ite f]

theorem map_thetaGL {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ∀ x, f (σ x) = τ (f x)) (n : ℕ) (g : GL (Fin n) A) :
    GeneralLinearGroup.map f (thetaGL n σ g) = thetaGL n τ (GeneralLinearGroup.map f g) := by
  rw [thetaGL_eq, thetaGL_eq, map_mul, map_mul, map_inv, map_PhiU, map_thetaR f σ τ h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

theorem pFin_conjAd (x : Ad E) :
    pFin E (conjAd E x) = conjFin (IsCMField.complexConj E).toRingEquiv (pFin E x) := rfl

theorem cV_conjAd (v : InfinitePlace E) (x : Ad E) :
    cV v (conjAd E x) = starRingEnd ℂ (cV v x) := by
  have h : pInf E (conjAd E x) = starRingEnd (Cinf E) (pInf E x) := by
    change (infEq E).symm ((infEq E) (starRingEnd (Cinf E) ((infEq E).symm x.1))) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  change pInf E (conjAd E x) v = _
  rw [h]
  rfl

theorem cV_algebraMap (v : InfinitePlace E) (y : E) : cV v (algebraMap E (Ad E) y) = v.embedding y :=
  pInf_algebraMap y v

theorem map_cV_ratGL (v : InfinitePlace E) (d : GL (Fin n) E) :
    GeneralLinearGroup.map (cV v) (ratGL E n d) = GeneralLinearGroup.map v.embedding d := by
  apply Units.ext
  ext i j
  exact cV_algebraMap v _

theorem map_pFin_ratGL (d : GL (Fin n) E) :
    GeneralLinearGroup.map (pFin E) (ratGL E n d) = ratF E n d := by
  apply Units.ext
  ext i j
  rfl

theorem map_cW (w : Pl E) (g : GA E n) :
    GeneralLinearGroup.map (cW w) g = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := by
  apply Units.ext
  ext i j
  rfl

theorem map_pFin_thetaGL (g : GA E n) :
    GeneralLinearGroup.map (pFin E) (thetaGL n (conjAd E) g) = thF E n (GeneralLinearGroup.map (pFin E) g) :=
  map_thetaGL _ _ _ pFin_conjAd n g

theorem map_cV_twConj (v : InfinitePlace E) (x : GA E n) (d : GL (Fin n) E) :
    GeneralLinearGroup.map (cV v) (twConj (thetaA E n) x (ratGL E n d)) =
      twConj (thetaR (starRingEnd ℂ) n) (GeneralLinearGroup.map (cV v) x) (GeneralLinearGroup.map v.embedding d) := by
  simp only [twConj, map_mul, map_inv, map_cV_ratGL]
  rw [map_thetaR (cV v) (conjAd E) (starRingEnd ℂ) (cV_conjAd v) n x]

theorem map_pFin_twConj (hT : TranslAd) (u : GL (Fin n) E) (hu : IsTransl u) (x : GA E n) (d : GL (Fin n) E) :
    GeneralLinearGroup.map (pFin E) (twConj (thetaA E n) x (ratGL E n d) * (ratGL E n u)⁻¹) =
      (GeneralLinearGroup.map (pFin E) x)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) x) := by
  have h := hT E n u hu x
  have h2 : twConj (thetaA E n) x (ratGL E n d) * (ratGL E n u)⁻¹ =
      x⁻¹ * ratGL E n (d * u⁻¹) * thetaGL n (conjAd E) x := by
    rw [h, map_mul, map_inv]
    simp only [twConj]
    group
  rw [h2, map_mul, map_mul, map_inv, map_pFin_ratGL, map_pFin_thetaGL]

theorem cpt_twConj (hT : TranslAd) (w : Pl E) (u : GL (Fin n) E) (hu : IsTransl u) (x : GA E n) (d : GL (Fin n) E) :
    cpt w u (twConj (thetaA E n) x (ratGL E n d)) = GeneralLinearGroup.map (pLoc E w)
      ((GeneralLinearGroup.map (pFin E) x)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) x)) := by
  rw [cpt, map_cW, map_pFin_twConj hT u hu]

theorem cpt'_twConj (hT : TranslAd) (w : Pl E) (u : GL (Fin n) E) (hu : IsTransl u) (x : GA E n) (d : GL (Fin n) E) :
    cpt' w u (twConj (thetaA E n) x (ratGL E n d)) = GeneralLinearGroup.map (pLoc E w) (thF E n
      ((GeneralLinearGroup.map (pFin E) x)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) x))) := by
  rw [cpt', map_cW, map_pFin_thetaGL, map_pFin_twConj hT u hu]

theorem adelEqOf : AdelEqOf := by
  intro hT E _ _ _ a b S u₁ u₂ h₁ h₂ ψ φ₁ φ₂ d₁ d₂ x
  rw [adel, orbFn, finFn]
  refine congr_arg₂ (· * ·) (Finset.prod_congr rfl fun v _ => ?_)
    (finprod_congr fun w => finprod_congr fun _ => ?_)
  · rw [map_cV_twConj, map_cV_twConj]
    rfl
  · rw [cpt_twConj hT w u₁ h₁, cpt_twConj hT w u₂ h₂, cpt'_twConj hT w u₁ h₁, cpt'_twConj hT w u₂ h₂]
    rfl

end GlobalTheory.CompanionTheory.AdelEqProof

end
end
