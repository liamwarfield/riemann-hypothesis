module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ShortVectorEveryPlace

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenusOrthonormalIntegralUnimodular
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Formalism.HermitianLatticesTheory

section Gen

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem star_algebraMap_mem_range (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
  ⟨⟨star (algebraMap (𝓞 K) K r), r.isIntegral_coe.map (starRingEnd K).toIntAlgHom⟩, rfl⟩

theorem inner_sum_orthonormal (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ} (e : Fin n → V)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (a b : Fin n → K) :
    h (∑ i, a i • e i) (∑ j, b j • e j) = ∑ i, star (a i) * b i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, he,
    smul_eq_mul, starRingEnd_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem fg_of_orthonormal_basis (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n) : L.FG := by
  obtain ⟨e, -, -, rfl, -⟩ := hL
  exact Submodule.fg_span (Set.finite_range e)

theorem integral_of_orthonormal_basis (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n) :
    IsIntegralLat h L := by
  obtain ⟨e, -, -, rfl, he⟩ := hL
  intro x hx y hy
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hx
  obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 hy
  have e1 : ∑ i, a i • e i = ∑ i, (algebraMap (𝓞 K) K (a i)) • e i :=
    Finset.sum_congr rfl fun i _ => (algebraMap_smul K (a i) (e i)).symm
  have e2 : ∑ i, b i • e i = ∑ i, (algebraMap (𝓞 K) K (b i)) • e i :=
    Finset.sum_congr rfl fun i _ => (algebraMap_smul K (b i) (e i)).symm
  rw [e1, e2, inner_sum_orthonormal h e he]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨a', ha'⟩ := star_algebraMap_mem_range (a i)
  rw [← ha', ← map_mul]
  exact Submodule.mem_one.2 ⟨_, rfl⟩

theorem unimodular_of_orthonormal_basis (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n) :
    IsUnimodular h L := by
  have hint := integral_of_orthonormal_basis h L hL
  obtain ⟨e, -, hsp, rfl, he⟩ := hL
  apply le_antisymm
  · intro z hz
    rw [dualBasic_mem_dual] at hz
    have hz' : z ∈ Submodule.span K (Set.range e) := by rw [hsp]; trivial
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hz'
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 := hz (e i) (Submodule.subset_span ⟨i, rfl⟩)
    have h2 : h (e i) (∑ j, c j • e j) = c i := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, he, smul_eq_mul]
      simp [Finset.sum_ite_eq]
    rw [h2] at h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 h1
    rw [← ho, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro z hz
    rw [dualBasic_mem_dual]
    intro y hy
    exact hint y hy z hz

theorem genus_orthonormal_integral_unimodular (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n)
    (M : Submodule (𝓞 K) V) (hM : M ∈ genus h L) : IsIntegralLat h M ∧ dual h M = M := by
  have hG := (final_genusBasic (𝓞 K) K V h hs star_algebraMap_mem_range).2.2 L M (fg_of_orthonormal_basis h L hL) hM.1.fg hM.2
  exact ⟨hG.2.1 (integral_of_orthonormal_basis h L hL), hG.1.1 (unimodular_of_orthonormal_basis h L hL)⟩

theorem mass_le_of_card_class_reps_le (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (B : ℝ) (hB : 0 ≤ B)
    (hc : ∀ s, Formalism.ThetaLiftIndependence.IsClassReps h L s → (s.card : ℝ) ≤ B) : mass h L ≤ B := by
  classical
  unfold mass
  split_ifs with hs
  · refine le_trans ?_ (hc _ hs.choose_spec)
    calc ∑ M ∈ hs.choose, ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ)⁻¹ ≤ ∑ M ∈ hs.choose, (1 : ℝ) := by
          refine Finset.sum_le_sum fun M _ => ?_
          rcases Nat.eq_zero_or_pos (Nat.card (Formalism.ThetaLiftIndependence.autL h M)) with h0 | h0
          · rw [h0]; simp
          · exact inv_le_one_of_one_le₀ (by exact_mod_cast h0)
      _ = (hs.choose.card : ℝ) := by simp
  · exact hB

end Gen

end Formalism.MainNotions.BridgeLemma₂

end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.MassPowLeExpRpow
namespace Formalism.MainNotions.BridgeLemma₂

private theorem const_20736_le_exp_15 : (20736 : ℝ) ≤ Real.exp 15 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h2 : Real.exp 15 = Real.exp 1 ^ 15 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h2]
  calc (20736 : ℝ) ≤ 2 ^ 15 := by norm_num
    _ ≤ Real.exp 1 ^ 15 := pow_le_pow_left₀ (by norm_num) h1 15

theorem mass_pow_le_exp_rpow (f m : ℕ) (rd L B₁ C κ : ℝ) (hf : 1 ≤ f) (hm : 2 ≤ m) (hrd : 2 ≤ rd) (hL : 1 ≤ L) (hκ : 1 ≤ κ)
    (hlf : Real.log f ≤ m) (hlrd : Real.log rd ≤ κ * L) (hB0 : 0 ≤ B₁) (hB : B₁ ≤ 4 * f * rd) (hC : 55 * κ ≤ C ^ 2) :
    (1 + 2 * B₁) ^ (2 * (2 * f)) * (1 + 2 * (B₁ * rd)) ^ (2 * (2 * f)) * (B₁ * (B₁ * rd)) ^ (4 * (2 * f)) ≤
      (Real.exp L ^ (C * (m : ℝ) ^ 2 * f)) ^ C := by
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hfpos : (0 : ℝ) < f := by linarith
  have hrdpos : (0 : ℝ) < rd := by linarith
  have hfe : (f : ℝ) ≤ Real.exp m := (Real.log_le_iff_le_exp hfpos).1 hlf
  have hre : rd ≤ Real.exp (κ * L) := (Real.log_le_iff_le_exp hrdpos).1 hlrd
  have hfr : (1 : ℝ) ≤ f * rd := by nlinarith
  have hfr2 : (1 : ℝ) ≤ f * rd ^ 2 := by nlinarith
  have hBr0 : 0 ≤ B₁ * rd := mul_nonneg hB0 hrdpos.le
  have hBr : B₁ * rd ≤ 4 * f * rd * rd := mul_le_mul_of_nonneg_right hB hrdpos.le
  have ha : 1 + 2 * B₁ ≤ 9 * f * rd := by nlinarith
  have hb : 1 + 2 * (B₁ * rd) ≤ 9 * f * rd ^ 2 := by nlinarith
  have hc : B₁ * (B₁ * rd) ≤ 16 * (f : ℝ) ^ 2 * rd ^ 3 := by
    have h := mul_le_mul hB hBr hBr0 (by linarith)
    calc B₁ * (B₁ * rd) ≤ 4 * f * rd * (4 * f * rd * rd) := h
      _ = 16 * (f : ℝ) ^ 2 * rd ^ 3 := by ring
  have hQ0 : 0 ≤ (1 + 2 * B₁) * (1 + 2 * (B₁ * rd)) * (B₁ * (B₁ * rd)) ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  have hQ : (1 + 2 * B₁) * (1 + 2 * (B₁ * rd)) * (B₁ * (B₁ * rd)) ^ 2 ≤
      Real.exp (15 + 6 * (m : ℝ) + 9 * (κ * L)) := by
    have hc2 : (B₁ * (B₁ * rd)) ^ 2 ≤ (16 * (f : ℝ) ^ 2 * rd ^ 3) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hB0 hBr0) hc 2
    have hab : (1 + 2 * B₁) * (1 + 2 * (B₁ * rd)) ≤ (9 * f * rd) * (9 * f * rd ^ 2) :=
      mul_le_mul ha hb (by linarith) (by linarith)
    have h1 : (1 + 2 * B₁) * (1 + 2 * (B₁ * rd)) * (B₁ * (B₁ * rd)) ^ 2 ≤
        (9 * f * rd) * (9 * f * rd ^ 2) * (16 * (f : ℝ) ^ 2 * rd ^ 3) ^ 2 :=
      mul_le_mul hab hc2 (sq_nonneg _) (mul_nonneg (by linarith) (by linarith))
    have h2 : (9 * f * rd) * (9 * f * rd ^ 2) * (16 * (f : ℝ) ^ 2 * rd ^ 3) ^ 2 =
        20736 * (f : ℝ) ^ 6 * rd ^ 9 := by ring
    have hf6 : (f : ℝ) ^ 6 ≤ Real.exp m ^ 6 := pow_le_pow_left₀ hfpos.le hfe 6
    have hr9 : rd ^ 9 ≤ Real.exp (κ * L) ^ 9 := pow_le_pow_left₀ hrdpos.le hre 9
    have h3 : 20736 * (f : ℝ) ^ 6 * rd ^ 9 ≤ Real.exp 15 * Real.exp m ^ 6 * Real.exp (κ * L) ^ 9 :=
      mul_le_mul (mul_le_mul const_20736_le_exp_15 hf6 (by positivity) (by positivity)) hr9
        (pow_nonneg hrdpos.le 9) (by positivity)
    have h4 : Real.exp (15 + 6 * (m : ℝ) + 9 * (κ * L)) =
        Real.exp 15 * Real.exp m ^ 6 * Real.exp (κ * L) ^ 9 := by
      rw [Real.exp_add, Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      norm_num
    rw [h4]
    calc _ ≤ _ := h1
      _ = _ := h2
      _ ≤ _ := h3
  have key : 60 + 24 * (m : ℝ) + 36 * (κ * L) ≤ C ^ 2 * ((m : ℝ) ^ 2 * L) := by
    have y1 : 1 ≤ κ * L := by nlinarith
    have hmm : 2 * (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    have hyl : (m : ℝ) ^ 2 ≤ κ * L * (m : ℝ) ^ 2 := by nlinarith
    have hy4 : 4 * (κ * L) ≤ κ * L * (m : ℝ) ^ 2 := by nlinarith
    have hCk : 55 * κ * ((m : ℝ) ^ 2 * L) ≤ C ^ 2 * ((m : ℝ) ^ 2 * L) :=
      mul_le_mul_of_nonneg_right hC (mul_nonneg (sq_nonneg _) (by linarith))
    nlinarith
  have hexp : ((2 * (2 * f) : ℕ) : ℝ) * (15 + 6 * (m : ℝ) + 9 * (κ * L)) ≤
      L * (C * (m : ℝ) ^ 2 * f) * C := by
    have e1 : ((2 * (2 * f) : ℕ) : ℝ) * (15 + 6 * (m : ℝ) + 9 * (κ * L)) =
        (f : ℝ) * (60 + 24 * (m : ℝ) + 36 * (κ * L)) := by push_cast; ring
    have e2 : L * (C * (m : ℝ) ^ 2 * f) * C = (f : ℝ) * (C ^ 2 * ((m : ℝ) ^ 2 * L)) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left key hfpos.le
  have hpow : 4 * (2 * f) = 2 * (2 * (2 * f)) := by ring
  rw [hpow, pow_mul (B₁ * (B₁ * rd)) 2 (2 * (2 * f)), ← mul_pow, ← mul_pow, ← Real.exp_mul,
    ← Real.exp_mul]
  calc _ ≤ (Real.exp (15 + 6 * (m : ℝ) + 9 * (κ * L))) ^ (2 * (2 * f)) :=
        pow_le_pow_left₀ hQ0 hQ _
    _ = Real.exp (((2 * (2 * f) : ℕ) : ℝ) * (15 + 6 * (m : ℝ) + 9 * (κ * L))) :=
        (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (L * (C * (m : ℝ) ^ 2 * f) * C) := Real.exp_le_exp.2 hexp

end Formalism.MainNotions.BridgeLemma₂
end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.HermitianLatticesTheory

def SecondOrthogonalVector (K : Type) [Field K] [NumberField K] [StarRing K] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), h.IsSymm → IsOrthoLattice h L 2 →
    ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → IsIntegralLat h M → dual h M = M →
    ∀ x ∈ M, x ≠ 0 → ∃ y ∈ M, y ≠ 0 ∧ h x y = 0 ∧ ∀ φ : K →+* ℂ, ‖φ (h y y)‖ ≤ ‖φ (h x x)‖ * rootDiscriminant K

def PlaneClassCount (K : Type) [Field K] [NumberField K] [StarRing K] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), h.IsSymm → IsOrthoLattice h L 2 →
    ∀ s : Finset (Submodule (𝓞 K) V), Formalism.ThetaLiftIndependence.IsClassReps h L s → ∀ B₁ B₂ : ℝ,
    (∀ M ∈ s, IsIntegralLat h M) →
    (∀ M ∈ s, ∃ x ∈ M, ∃ y ∈ M, x ≠ 0 ∧ y ≠ 0 ∧ h x y = 0 ∧
      ∀ φ : K →+* ℂ, ‖φ (h x x)‖ ≤ B₁ ∧ ‖φ (h y y)‖ ≤ B₂) →
    (s.card : ℝ) ≤ (1 + 2 * B₁) ^ (2 * finrank ℚ K) * (1 + 2 * B₂) ^ (2 * finrank ℚ K) *
      (B₁ * B₂) ^ (4 * finrank ℚ K)

theorem card_class_reps_plane_le (K : Type) [Field K] [NumberField K] [StarRing K] (B₁ : ℝ)
    (hA : ShortVectorEveryPlace K B₁) (hB : SecondOrthogonalVector K) (hC : PlaneClassCount K) (hrd : 0 ≤ rootDiscriminant K)
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (hs : h.IsSymm) (hL : IsOrthoLattice h L 2)
    (s : Finset (Submodule (𝓞 K) V)) (hreps : Formalism.ThetaLiftIndependence.IsClassReps h L s) :
    (s.card : ℝ) ≤ (1 + 2 * B₁) ^ (2 * finrank ℚ K) * (1 + 2 * (B₁ * rootDiscriminant K)) ^ (2 * finrank ℚ K) *
      (B₁ * (B₁ * rootDiscriminant K)) ^ (4 * finrank ℚ K) := by
  refine hC V h L hs hL s hreps B₁ (B₁ * rootDiscriminant K)
    (fun M hM => (genus_orthonormal_integral_unimodular h hs L hL M (hreps.1 M hM)).1) fun M hM => ?_
  have hg := hreps.1 M hM
  have hMlat : Submodule.IsLattice K M := hg.1.toIsLattice
  obtain ⟨hint, huni⟩ := genus_orthonormal_integral_unimodular h hs L hL M hg
  obtain ⟨x, hx, hx0, hxB⟩ := hA V h L hs hL M hg
  obtain ⟨y, hy, hy0, hxy, hyB⟩ := hB V h L hs hL M hMlat hint huni x hx hx0
  exact ⟨x, hx, y, hy, hx0, hy0, hxy, fun φ =>
    ⟨hxB φ, (hyB φ).trans (mul_le_mul_of_nonneg_right (hxB φ) hrd)⟩⟩

end Formalism.MainNotions.BridgeLemma₂

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem plane_mass_bound_of_facts (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C B₁ : ℝ)
    (hA : ShortVectorEveryPlace D.host.E B₁) (hB : SecondOrthogonalVector D.host.E) (hCt : PlaneClassCount D.host.E)
    (hB0 : 0 ≤ B₁) (hB1 : B₁ ≤ 4 * D.R.f * D.host.rdE) (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) : UnitaryVolumeMass.Mass2At D large₂ C := by
  intro V _ _ _ _ h L hs ho
  obtain ⟨-, -, h3, -, h5, -, -, -, -, -, h11, -, -, -, -, -, -, -, h19, -⟩ := hH
  have hm := D.R.two_le_m
  have hf : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) h3
  have hL1 : 1 ≤ large₂.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hrd : 2 ≤ D.host.rdE := by
    have e : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
    rw [← e]; linarith
  have hlrd : Real.log D.host.rdE ≤ max 1 (1 / Cl) * large₂.sc.L := by
    refine le_trans h11 ?_
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  have hlf : Real.log (D.R.f : ℝ) ≤ (D.R.m : ℝ) := by
    refine le_trans h5 ?_
    rw [Real.sqrt_le_left (by positivity)]
    have h1 : D.R.rS ≤ D.R.m := by unfold Ranks.rS; omega
    have h2 : (D.R.rS : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast h1
    have h3 : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hrdE : rootDiscriminant D.host.E = D.host.rdE := rfl
  have hnum := mass_pow_le_exp_rpow D.R.f D.R.m D.host.rdE large₂.sc.L B₁ C (max 1 (1 / Cl)) hf hm hrd hL1 (le_max_left _ _) hlf hlrd hB0 hB1 hC
  have hb : large₂.sc.b = Real.exp large₂.sc.L := rfl
  rw [hb]
  refine mass_le_of_card_class_reps_le h L _ (by positivity) fun s hreps => ?_
  have hc := card_class_reps_plane_le D.host.E B₁ hA hB hCt (by rw [hrdE]; linarith) V h L hs ho s hreps
  rw [hrdE, Formalism.MainNotions.StandardLattice.finrank_host] at hc
  exact hc.trans hnum

end Formalism.MainNotions.BridgeLemma₂

end
