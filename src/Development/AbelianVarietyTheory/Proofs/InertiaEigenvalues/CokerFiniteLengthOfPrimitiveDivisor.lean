module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSplit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralPowerSeriesDivisionApproxStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralPowerSeriesDivisionApprox
namespace GlobalTheory.BK.DivApprox

open PowerSeries GlobalTheory.BK

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_coeff_mul_le' {f g : K⟦X⟧} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∀ n, ‖coeff n f‖ ≤ a) (hg : ∀ n, ‖coeff n g‖ ≤ b) (n : ℕ) :
    ‖coeff n (f * g)‖ ≤ a * b := by
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    ha hb (f := f) (g := g) (by simpa using hf) (by simpa using hg) n

omit [IsUltrametricDist K] in
theorem eq_low_add_high (f : K⟦X⟧) (n₀ : ℕ) :
    f = (PowerSeries.mk fun n => if n < n₀ then coeff n f else 0) +
      X ^ n₀ * PowerSeries.mk fun n => coeff (n + n₀) f := by
  ext n
  rw [map_add (f := _), coeff_mk, coeff_X_pow_mul', coeff_mk]
  by_cases h : n < n₀
  · rw [if_pos h, if_neg (not_le.2 h), add_zero]
  · rw [if_neg h, if_pos (not_lt.1 h), zero_add, Nat.sub_add_cancel (not_lt.1 h)]

theorem exists_inv_mem_A {O : Type} [CommRing O] [Algebra O K] [IsUnitBall O K] {u : K⟦X⟧}
    (hu : u ∈ A O K) (h0 : ‖coeff 0 u‖ = 1) : ∃ w ∈ A O K, u * w = 1 := by
  obtain ⟨v, hv⟩ := (equivA O K).surjective ⟨u, hu⟩
  have hv' : PowerSeries.map (algebraMap O K) v = u := by
    rw [← coe_equivA, hv]
  have hc : algebraMap O K (constantCoeff v) = coeff 0 u := by
    rw [← hv', coeff_map, coeff_zero_eq_constantCoeff_apply]
  have hne : coeff 0 u ≠ 0 := by
    intro h
    rw [h, norm_zero] at h0
    exact zero_ne_one h0
  obtain ⟨c, hc'⟩ := (IsUnitBall.mem_range_iff (O := O) (coeff 0 u)⁻¹).2
    (by rw [norm_inv, h0, inv_one])
  have hunit : IsUnit (constantCoeff v) := by
    refine IsUnit.of_mul_eq_one c (IsUnitBall.inj (O := O) (K := K) ?_)
    rw [map_mul, hc, hc', map_one, mul_inv_cancel₀ hne]
  obtain ⟨w, hw⟩ := (isUnit_iff_constantCoeff.2 hunit).exists_right_inv
  refine ⟨equivA O K w, (equivA O K w).2, ?_⟩
  rw [coe_equivA, ← hv', ← map_mul, hw, map_one]

theorem step {g p u w : K⟦X⟧} {n₀ : ℕ} {ρ t : ℝ} (hρ : 0 ≤ ρ) (ht : 0 ≤ t)
    (hg : g = p + X ^ n₀ * u) (huw : u * w = 1) (hw : ∀ n, ‖coeff n w‖ ≤ 1)
    (hp : ∀ n, ‖coeff n p‖ ≤ ρ) (f : K⟦X⟧) (hf : ∀ n, ‖coeff n f‖ ≤ t) :
    ∃ q r : K⟦X⟧, (∀ n, ‖coeff n q‖ ≤ t) ∧ (∀ i, n₀ ≤ i → coeff i r = 0) ∧
      (∀ i, ‖coeff i r‖ ≤ t) ∧ ∀ n, ‖coeff n (f - q * g - r)‖ ≤ t * ρ := by
  have hfe := eq_low_add_high f n₀
  set r : K⟦X⟧ := PowerSeries.mk fun n => if n < n₀ then coeff n f else 0 with hr
  set fh : K⟦X⟧ := PowerSeries.mk fun n => coeff (n + n₀) f with hfh
  have hq : ∀ n, ‖coeff n (w * fh)‖ ≤ t := fun n => by
    have := norm_coeff_mul_le' zero_le_one ht hw (g := fh)
      (fun m => by rw [hfh, coeff_mk]; exact hf _) n
    rwa [one_mul] at this
  refine ⟨w * fh, r, hq, fun i hi => ?_, fun i => ?_, fun n => ?_⟩
  · rw [hr, coeff_mk, if_neg (not_lt.2 hi)]
  · rw [hr, coeff_mk]
    split_ifs
    · exact hf _
    · rwa [norm_zero]
  · have : f - w * fh * g - r = -(w * fh * p) := by
      rw [hg]
      linear_combination hfe - X ^ n₀ * fh * huw
    rw [this, map_neg, norm_neg]
    exact norm_coeff_mul_le' ht hρ hq hp n

theorem iterate {g p u w : K⟦X⟧} {n₀ : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hg : g = p + X ^ n₀ * u) (huw : u * w = 1) (hw : ∀ n, ‖coeff n w‖ ≤ 1)
    (hp : ∀ n, ‖coeff n p‖ ≤ ρ) (f : K⟦X⟧) (hf : ∀ n, ‖coeff n f‖ ≤ 1) (k : ℕ) :
    ∃ q r : K⟦X⟧, (∀ n, ‖coeff n q‖ ≤ 1) ∧ (∀ i, n₀ ≤ i → coeff i r = 0) ∧
      (∀ i, ‖coeff i r‖ ≤ 1) ∧ ∀ n, ‖coeff n (f - q * g - r)‖ ≤ ρ ^ k := by
  induction k with
  | zero => exact ⟨0, 0, by simp, by simp, by simp, by simpa using hf⟩
  | succ k ih =>
    obtain ⟨q, r, hq, hr0, hr, he⟩ := ih
    obtain ⟨q', r', hq', hr0', hr', he'⟩ := step hρ (pow_nonneg hρ k) hg huw hw hp _ he
    have h1 : ρ ^ k ≤ 1 := pow_le_one₀ hρ hρ1
    refine ⟨q + q', r + r', fun n => ?_, fun i hi => ?_, fun n => ?_, fun n => ?_⟩
    · rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hq n) ((hq' n).trans h1))
    · rw [map_add (f := _), hr0 i hi, hr0' i hi, add_zero]
    · rw [map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hr n) ((hr' n).trans h1))
    · have : f - (q + q') * g - (r + r') = f - q * g - r - q' * g - r' := by ring
      rw [this, pow_succ]
      exact he' n

theorem exists_div_approx (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (g : K⟦X⟧) (hg : g ∈ A O K) (n₀ : ℕ)
    (h1 : ‖coeff n₀ g‖ = 1) (hlt : ∀ i < n₀, ‖coeff i g‖ < 1) (δ : ℝ) (hδ : 0 < δ)
    (f : K⟦X⟧) (hf : f ∈ A O K) :
    ∃ q ∈ A O K, ∃ r : K⟦X⟧, (∀ i, n₀ ≤ i → coeff i r = 0) ∧ (∀ i, ‖coeff i r‖ ≤ 1) ∧
      ∀ n, ‖coeff n (f - q * g - r)‖ ≤ δ := by
  set ρ : NNReal := (Finset.range n₀).sup (fun i => ‖coeff i g‖₊) with hρ
  have hρ1 : ρ < 1 := by
    rw [hρ, Finset.sup_lt_iff (by simp)]
    intro i hi
    exact_mod_cast hlt i (Finset.mem_range.1 hi)
  have hρ1' : (ρ : ℝ) < 1 := by exact_mod_cast hρ1
  obtain ⟨w, hw, huw⟩ := exists_inv_mem_A (O := O)
    (u := PowerSeries.mk fun n => coeff (n + n₀) g)
    (fun n => by rw [coeff_mk]; exact hg _) (by rw [coeff_mk, zero_add, h1])
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ hρ1'
  obtain ⟨q, r, hq, hr0, hr, he⟩ := iterate ρ.2 hρ1'.le (eq_low_add_high g n₀) huw hw
    (fun n => by
      rw [coeff_mk]
      split_ifs with h
      · exact_mod_cast Finset.le_sup (f := fun i => ‖coeff i g‖₊) (Finset.mem_range.2 h)
      · rw [norm_zero]; exact ρ.2) f hf k
  exact ⟨q, hq, r, hr0, hr, fun n => (he n).trans hk.le⟩

end GlobalTheory.BK.DivApprox
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_powerSeries_division_approx : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (g : K⟦X⟧), g ∈ A O K → ∀ n₀ : ℕ, ‖coeff n₀ g‖ = 1 → (∀ i < n₀, ‖coeff i g‖ < 1) → ∀ δ : ℝ, 0 < δ → ∀ f ∈ A O K, ∃ q ∈ A O K, ∃ r : K⟦X⟧, (∀ i, n₀ ≤ i → coeff i r = 0) ∧ (∀ i, ‖coeff i r‖ ≤ 1) ∧ ∀ n, ‖coeff n (f - q * g - r)‖ ≤ δ := by
  first | exact @GlobalTheory.BK.DivApprox.exists_div_approx | exact GlobalTheory.BK.DivApprox.exists_div_approx | (intros; apply GlobalTheory.BK.DivApprox.exists_div_approx <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokerFiniteLengthOfPrimitiveDivisor
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.CokerFinLen

theorem divApprox : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (g : K⟦X⟧), g ∈ A O K → ∀ n₀ : ℕ, ‖coeff n₀ g‖ = 1 → (∀ i < n₀, ‖coeff i g‖ < 1) → ∀ δ : ℝ, 0 < δ → ∀ f ∈ A O K, ∃ q ∈ A O K, ∃ r : K⟦X⟧, (∀ i, n₀ ≤ i → coeff i r = 0) ∧ (∀ i, ‖coeff i r‖ ≤ 1) ∧ ∀ n, ‖coeff n (f - q * g - r)‖ ≤ δ := GlobalTheory.T.exists_integral_powerSeries_division_approx

theorem exists_net {K : Type} [NormedField K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : Finset K, (∀ t ∈ T, ‖t‖ ≤ 1) ∧ ∀ x : K, ‖x‖ ≤ 1 → ∃ t ∈ T, ‖x - t‖ < δ := by
  haveI : ProperSpace K := FiniteDimensional.proper ℚ_[l] K
  obtain ⟨t, hts, ht, hcov⟩ := finite_cover_balls_of_compact (isCompact_closedBall (0 : K) 1) hδ
  refine ⟨ht.toFinset, fun y hy => by simpa using hts (ht.mem_toFinset.1 hy), fun x hx => ?_⟩
  have hx' : x ∈ Metric.closedBall (0 : K) 1 := by simpa using hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hx')
  exact ⟨y, ht.mem_toFinset.2 hy, by simpa [dist_eq_norm] using hxy⟩

theorem exists_finset_reps {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (g : K⟦X⟧) (hg : g ∈ A O K) (hprim : ∃ n, ‖coeff n g‖ = 1) (c : K) (hc : c ≠ 0) :
    ∃ R : Finset K⟦X⟧, ∀ f ∈ A O K, ∃ r ∈ R, r ∈ A O K ∧ ∃ q ∈ A O K, ∃ h ∈ A O K,
      f = r + q * g + C c * h := by
  classical
  have hδ : 0 < ‖c‖ := norm_pos_iff.2 hc
  obtain ⟨T, hT1, hT⟩ := exists_net (K := K) l hδ
  let n₀ := Nat.find hprim
  have hn₀ : ‖coeff n₀ g‖ = 1 := Nat.find_spec hprim
  have hlow : ∀ i < n₀, ‖coeff i g‖ < 1 := fun i hi =>
    lt_of_le_of_ne ((mem_A.1 hg) i) (Nat.find_min hprim hi)
  let mkR : (Fin n₀ → T) → K⟦X⟧ := fun t => PowerSeries.mk fun n =>
    if h : n < n₀ then ((t ⟨n, h⟩ : T) : K) else 0
  refine ⟨Finset.univ.image mkR, fun f hf => ?_⟩
  obtain ⟨q, hq, r, hr0, hr1, hrem⟩ := divApprox O K g hg n₀ hn₀ hlow _ hδ f hf
  choose t ht hrt using fun i : Fin n₀ => hT (coeff i r) (hr1 i)
  let r' := mkR fun i => ⟨t i, ht i⟩
  have hcoeff : ∀ n, coeff n r' = if h : n < n₀ then t ⟨n, h⟩ else 0 := fun n => by
    simp [r', mkR, coeff_mk]
  have hr'A : r' ∈ A O K := mem_A.2 fun n => by
    rw [hcoeff]; split_ifs
    · exact hT1 _ (ht _)
    · simp
  set d := f - q * g - r' with hd
  have hdn : ∀ n, ‖coeff n d‖ ≤ ‖c‖ := fun n => by
    have : d = (f - q * g - r) + (r - r') := by rw [hd]; ring
    rw [this, map_add (f := _)]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hrem n) ?_)
    rw [map_sub, hcoeff]
    split_ifs with h
    · exact (hrt ⟨n, h⟩).le
    · rw [hr0 n (not_lt.1 h), sub_zero, norm_zero]; exact hδ.le
  refine ⟨r', Finset.mem_image_of_mem mkR (Finset.mem_univ (fun i => (⟨t i, ht i⟩ : T))), hr'A, q, hq, C c⁻¹ * d,
    mem_A.2 fun n => ?_, ?_⟩
  · rw [coeff_C_mul, norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (hdn n) (norm_nonneg _)
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul, hd]; ring

theorem main : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), (∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ F.mat τ * Y = g • (1 : Matrix κ κ K⟦X⟧)) → (∀ τ, (1 : K⟦X⟧) ∈ F.rdivSet τ) → IsFiniteLength (A O K) F.coker := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F hY h1
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (K := K) (l := l) (e := e) (a := a)
  have hc : ∀ τ, ∃ c : K, c ≠ 0 ∧ ∃ Y : Matrix ι κ K⟦X⟧, (∀ i j, Y i j ∈ A O K) ∧
      F.mat τ * Y = C c • (1 : Matrix κ κ K⟦X⟧) := by
    intro τ
    obtain ⟨-, Y, ⟨B, hB⟩, hFY⟩ := h1 τ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ‖(l : K)‖ ^ m * B < 1 := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
        (norm_l_lt_one (K := K) l)).mul_const B
      rw [zero_mul] at h
      exact (h.eventually (gt_mem_nhds zero_lt_one)).exists
    refine ⟨(l : K) ^ m, pow_ne_zero _ (l_ne_zero l), C ((l : K) ^ m) • Y,
      fun i j => mem_A.2 fun n => ?_, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul, coeff_C_mul, norm_mul, norm_pow]
      calc _ ≤ ‖(l : K)‖ ^ m * B := mul_le_mul_of_nonneg_left (hB i j n) (by positivity)
        _ ≤ 1 := hm.le
    · rw [Matrix.mul_smul, hFY, one_smul]
  choose c hc0 Y₁ hY₁A hY₁ using hc
  choose Yg g hYgA hgprim hYg using hY
  have hgA : ∀ τ (j : κ), g τ ∈ A O K := fun τ j => by
    have h := congrFun (congrFun (hYg τ) j) j
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.mul_apply] at h
    rw [← h]
    exact Subalgebra.sum_mem _ fun k _ => mul_mem (F.mem τ j k) (hYgA τ k j)
  have hR : ∀ τ (j : κ), ∃ R : Finset K⟦X⟧, ∀ f ∈ A O K, ∃ r ∈ R, r ∈ A O K ∧ ∃ q ∈ A O K,
      ∃ h ∈ A O K, f = r + q * g τ + C (c τ) * h := fun τ j =>
    exists_finset_reps l (g τ) (hgA τ j) (hgprim τ) (c τ) (hc0 τ)
  choose R hR using hR
  let Sset : Set Q.M := {v | ∀ τ j, (v : Vec K a κ) τ j ∈ R τ j}
  have hS : Sset.Finite := by
    have hfin : (Set.pi Set.univ fun τ => Set.pi Set.univ fun j => ((R τ j : Set K⟦X⟧))).Finite :=
      Set.Finite.pi fun τ => Set.Finite.pi fun j => (R τ j).finite_toSet
    refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
    intro v hv
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Finset.mem_coe]
    exact hv
  have hsurj : ∀ x : F.coker, x ∈ (Submodule.Quotient.mk '' Sset : Set F.coker) := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hv : ∀ τ j, (v : Vec K a κ) τ j ∈ A O K := fun τ j => mem_tot.1 v.2 τ j
    choose r hrR hrA q hqA h hhA hdec using fun τ j => hR τ j _ (hv τ j)
    refine ⟨⟨fun τ j => r τ j, mem_tot.2 fun τ j => hrA τ j⟩, hrR, ?_⟩
    rw [Submodule.Quotient.eq]
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
    unfold Hom.imM
    rw [Submodule.mem_map]
    refine ⟨fun τ => -(Yg τ *ᵥ q τ + Y₁ τ *ᵥ h τ), mem_tot.2 fun τ i => ?_, ?_⟩
    · have hmv : ∀ (Y : Matrix ι κ K⟦X⟧) (w : κ → K⟦X⟧), (∀ i j, Y i j ∈ A O K) →
          (∀ j, w j ∈ A O K) → ∀ i, (Y *ᵥ w) i ∈ A O K := fun Y w hY hw i =>
        Subalgebra.sum_mem _ fun j _ => mul_mem (hY i j) (hw j)
      exact neg_mem (add_mem (hmv _ _ (hYgA τ) (hqA τ) i) (hmv _ _ (hY₁A τ) (hhA τ) i))
    · ext τ j
      simp only [LinearMap.restrictScalars_apply, Hom.app_apply, Matrix.mulVec_neg,
        Matrix.mulVec_add, Matrix.mulVec_mulVec, hYg, hY₁, Matrix.smul_mulVec,
        Matrix.one_mulVec, Submodule.coe_sub, Pi.sub_apply, Pi.neg_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [hdec τ j]
      ring_nf
  haveI : Finite F.coker :=
    Set.finite_univ_iff.1 ((hS.image _).subset fun x _ => hsurj x)
  exact isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨isNoetherian_of_finite _ _, isArtinian_of_finite⟩

end GlobalTheory.CokerFinLen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokerFiniteLengthOfPrimitiveDivisorStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coker_finite_length_of_primitive_divisor : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), (∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ F.mat τ * Y = g • (1 : Matrix κ κ K⟦X⟧)) → (∀ τ, (1 : K⟦X⟧) ∈ F.rdivSet τ) → IsFiniteLength (A O K) F.coker := by
  first | exact @GlobalTheory.CokerFinLen.main | exact GlobalTheory.CokerFinLen.main | (intros; apply GlobalTheory.CokerFinLen.main <;> assumption)
end
