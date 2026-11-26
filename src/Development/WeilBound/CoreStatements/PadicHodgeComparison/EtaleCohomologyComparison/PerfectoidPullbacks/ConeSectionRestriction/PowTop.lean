module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.PowKNeZeroOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeometricGenericComponents
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.TraceChart
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocExact

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ResidStmt
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ResR
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ResidResPf
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [Field K] {R : Type} [CommRing R] [Algebra K R] {n : ℕ}

theorem resRPf_tpow_add (t : Fin (n + 1) → Rˣ) (m m' : Fin (n + 1) → ℤ) :
    tpow t (m + m') = tpow t m * tpow t m' := by
  simp only [tpow, Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul]

theorem resRPf_tpow_negOne (t : Fin (n + 1) → Rˣ) :
    tpow t (fun _ => -1) = (((∏ k, t k)⁻¹ : Rˣ) : R) := by
  unfold tpow
  congr 1
  simp only [zpow_neg_one, Finset.prod_inv_distrib]

theorem resRPf_tpow_single (t : Fin (n + 1) → Rˣ) (k : Fin (n + 1)) :
    tpow t (-Pi.single k (1 : ℤ)) = (((t k)⁻¹ : Rˣ) : R) := by
  unfold tpow
  congr 1
  rw [Finset.prod_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem resRPf_linInd (t : Fin (n + 1) → Rˣ) (ht : AlgebraicIndependent K fun k => (t k : R)) :
    LinearIndependent K (tpow t) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg m0 hm0
  set N : ℤ := ∑ m ∈ s, ∑ j, |m j| with hN
  have hbound : ∀ m ∈ s, ∀ j, 0 ≤ m j + N := by
    intro m hm j
    have h1 : |m j| ≤ ∑ j, |m j| :=
      Finset.single_le_sum (f := fun j => |m j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 : ∑ j, |m j| ≤ N :=
      Finset.single_le_sum (f := fun m : Fin (n + 1) → ℤ => ∑ j, |m j|)
        (fun m _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) hm
    have h3 := neg_abs_le (m j)
    linarith
  let e : (Fin (n + 1) → ℤ) → (Fin (n + 1) →₀ ℕ) :=
    fun m => Finsupp.equivFunOnFinite.symm (fun j => (m j + N).toNat)
  have he : ∀ m ∈ s, tpow t (m + fun _ => N) =
      MvPolynomial.aeval (fun k => (t k : R)) (MvPolynomial.monomial (e m) (1 : K)) := by
    intro m hm
    rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    unfold tpow
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl (fun j _ => ?_)
    simp only [e, Finsupp.coe_equivFunOnFinite_symm, Pi.add_apply]
    conv_lhs => rw [← Int.toNat_of_nonneg (hbound m hm j)]
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
  have hmul : ∑ m ∈ s, g m • tpow t (m + fun _ => N) = 0 := by
    simp_rw [resRPf_tpow_add, ← smul_mul_assoc]
    rw [← Finset.sum_mul, hg, zero_mul]
  have hpoly : ∑ m ∈ s, MvPolynomial.monomial (e m) (g m) = 0 := by
    apply algebraicIndependent_iff_injective_aeval.1 ht
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero, ← hmul]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [he m hm]
    simp only [MvPolynomial.aeval_monomial, map_one, one_mul, Algebra.smul_def]
  have hinj : ∀ m ∈ s, ∀ m' ∈ s, e m = e m' → m = m' := by
    intro m hm m' hm' h
    funext j
    have h0 := DFunLike.congr_fun h j
    simp only [e, Finsupp.coe_equivFunOnFinite_symm] at h0
    have h1 := hbound m hm j
    have h2 := hbound m' hm' j
    omega
  have hc := congrArg (AddMonoidAlgebra.coeff · (e m0)) hpoly
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero, Finset.sum_eq_single m0] at hc
  · simpa [MvPolynomial.coeff_monomial] using hc
  · intro m hm hne
    rw [MvPolynomial.coeff_monomial, if_neg (fun h => hne (hinj m hm m0 hm0 h))]
  · intro h
    exact absurd hm0 h

def resRPfLogD (D : Derivation K R R) : Rˣ →* Multiplicative R where
  toFun u := Multiplicative.ofAdd ((((u⁻¹ : Rˣ)) : R) * D (u : R))
  map_one' := by simp
  map_mul' u v := by
    rw [← ofAdd_add]
    congr 1
    have hu : (((u⁻¹ : Rˣ)) : R) * u = 1 := Units.inv_mul u
    have hv : (((v⁻¹ : Rˣ)) : R) * v = 1 := Units.inv_mul v
    simp only [mul_inv_rev, Units.val_mul, Derivation.leibniz, smul_eq_mul]
    linear_combination ((((v⁻¹ : Rˣ)) : R) * D (v : R)) * hu + ((((u⁻¹ : Rˣ)) : R) * D (u : R)) * hv

theorem resRPfLogD_apply (D : Derivation K R R) (u : Rˣ) :
    Multiplicative.toAdd (resRPfLogD D u) = (((u⁻¹ : Rˣ)) : R) * D (u : R) := rfl

theorem resRPf_logD (t : Fin (n + 1) → Rˣ) (D : Derivation K R R) (m : Fin (n + 1) → ℤ) :
    (((∏ j, t j ^ m j)⁻¹ : Rˣ) : R) * D (tpow t m) =
      ∑ j, m j • ((((t j)⁻¹ : Rˣ) : R) * D (t j : R)) := by
  have h := congrArg Multiplicative.toAdd (map_prod (resRPfLogD D) (fun j => t j ^ m j) Finset.univ)
  simp only [map_zpow, toAdd_prod, toAdd_zpow, resRPfLogD_apply] at h
  exact h

theorem resRPf_Dk (t : Fin (n + 1) → Rˣ) (D : Fin (n + 1) → Derivation K R R)
    (hD : ∀ k j, D k (t j) = if k = j then 1 else 0) (k : Fin (n + 1)) (m : Fin (n + 1) → ℤ) :
    D k (tpow t m) = m k • tpow t (m - Pi.single k (1 : ℤ)) := by
  have h := resRPf_logD t (D k) m
  simp only [hD, mul_ite, mul_one, mul_zero, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true] at h
  have hU : tpow t m * (((∏ j, t j ^ m j)⁻¹ : Rˣ) : R) = 1 := Units.mul_inv _
  calc D k (tpow t m) = tpow t m * ((((∏ j, t j ^ m j)⁻¹ : Rˣ) : R) * D k (tpow t m)) := by
        rw [← mul_assoc, hU, one_mul]
    _ = tpow t m * (m k • (((t k)⁻¹ : Rˣ) : R)) := by rw [h]
    _ = m k • tpow t (m - Pi.single k (1 : ℤ)) := by
        rw [mul_smul_comm, sub_eq_add_neg, resRPf_tpow_add, resRPf_tpow_single]

theorem res_R_pf (t : Fin (n + 1) → Rˣ) (ht : AlgebraicIndependent K fun k => (t k : R))
    (D : Fin (n + 1) → Derivation K R R) (hD : ∀ k j, D k (t j) = if k = j then 1 else 0) :
    ∃ res : R →ₗ[K] K, res (((∏ k, t k)⁻¹ : Rˣ) : R) = 1 ∧
      (∀ x ∈ Submodule.span K (tpow t '' {m | m ≠ fun _ => -1}), res x = 0) ∧
      ∀ k, ∀ x ∈ torusS K t Finset.univ, res (D k x) = 0 := by
  classical
  have hli := resRPf_linInd (K := K) t ht
  obtain ⟨res, hres⟩ := LinearMap.exists_extend ((Module.Basis.span hli).coord (fun _ => -1))
  have hval : ∀ m, res (tpow t m) = if m = (fun _ => -1) then 1 else 0 := by
    intro m
    have h1 : tpow t m = ((Module.Basis.span hli m : Submodule.span K (Set.range (tpow t))) : R) :=
      congrArg Subtype.val (Module.Basis.span_apply hli m).symm
    have h2 := LinearMap.congr_fun hres (Module.Basis.span hli m)
    rw [LinearMap.comp_apply, Submodule.subtype_apply] at h2
    rw [h1, h2, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  refine ⟨res, ?_, ?_, ?_⟩
  · rw [← resRPf_tpow_negOne, hval, if_pos rfl]
  · intro x hx
    have hle : Submodule.span K (tpow t '' {m | m ≠ fun _ => -1}) ≤ LinearMap.ker res := by
      rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, hval, if_neg hm]
    exact hle hx
  · intro k x hx
    have hx' : x ∈ Submodule.span K (Set.range (tpow t)) := by
      have h1 : x ∈ Subalgebra.toSubmodule (torusS K t Finset.univ) := hx
      rw [torusS, Algebra.adjoin_eq_span] at h1
      refine Submodule.span_mono ?_ h1
      intro y hy
      let M : Submonoid R :=
        { carrier := Set.range (tpow t)
          mul_mem' := by
            rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
            exact ⟨a + b, resRPf_tpow_add t a b⟩
          one_mem' := ⟨0, by simp [tpow]⟩ }
      exact (Submonoid.closure_le (S := M)).2 (Set.image_subset_range _ _) hy
    have hker : Submodule.span K (Set.range (tpow t)) ≤ LinearMap.ker (res ∘ₗ (D k : R →ₗ[K] R)) := by
      rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.comp_apply, Derivation.coeFn_coe,
        resRPf_Dk t D hD k m, map_zsmul, hval]
      by_cases h : m - Pi.single k (1 : ℤ) = fun _ => -1
      · have h' := congr_fun h k
        simp only [Pi.sub_apply, Pi.single_eq_same] at h'
        have h0 : m k = 0 := by omega
        rw [h0, zero_smul]
      · rw [if_neg h, smul_zero]
    have h2 := hker hx'
    rwa [LinearMap.mem_ker, LinearMap.comp_apply, Derivation.coeFn_coe] at h2

end CrystallineSemistableComparison.Pb
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [Field K] {R : Type} [CommRing R] [Algebra K R] {n : ℕ}

theorem res_R (t : Fin (n + 1) → Rˣ) (ht : AlgebraicIndependent K fun k => (t k : R))
    (D : Fin (n + 1) → Derivation K R R) (hD : ∀ k j, D k (t j) = if k = j then 1 else 0) :
    ∃ res : R →ₗ[K] K, res (((∏ k, t k)⁻¹ : Rˣ) : R) = 1 ∧
      (∀ x ∈ Submodule.span K (tpow t '' {m | m ≠ fun _ => -1}), res x = 0) ∧
      ∀ k, ∀ x ∈ torusS K t Finset.univ, res (D k x) = 0 :=
  res_R_pf t ht D hD

end CrystallineSemistableComparison.Pb
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ChartExt
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ResidChartPf
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

open Polynomial

variable {K : Type} [Field K] {R : Type} [CommRing R] [IsDomain R] [Algebra K R]

theorem chart_ext_scale (A T : Subalgebra K R) (w : R) (hwA : w ∈ A)
    (hscale : ∀ x ∈ T, ∃ N : ℕ, w ^ N * x ∈ A) (g : R) (hg : IsIntegral T g) :
    ∃ N : ℕ, IsIntegral A (w ^ N * g) := by
  obtain ⟨p, hpm, hp⟩ := hg
  have hmono : ∀ (x : R) (n m : ℕ), n ≤ m → w ^ n * x ∈ A → w ^ m * x ∈ A := by
    intro x n m hnm hx
    have : w ^ m * x = w ^ (m - n) * (w ^ n * x) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hnm]
    rw [this]
    exact A.mul_mem (A.pow_mem hwA _) hx
  have hc : ∀ i : ℕ, ∃ n : ℕ, w ^ n * ((p.coeff i : T) : R) ∈ A := fun i =>
    hscale _ (p.coeff i).2
  choose n hn using hc
  set N : ℕ := ∑ i ∈ Finset.range (p.natDegree + 1), n i with hN
  have hcN : ∀ i ≤ p.natDegree, w ^ N * ((p.coeff i : T) : R) ∈ A := by
    intro i hi
    refine hmono _ (n i) N ?_ (hn i)
    exact Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  set P : R[X] := p.map (algebraMap T R) with hP
  have hPm : P.Monic := hpm.map _
  have hPdeg : P.natDegree = p.natDegree := hpm.natDegree_map _
  have hPcoeff : ∀ i, P.coeff i = ((p.coeff i : T) : R) := fun i => by
    rw [hP, coeff_map]; rfl
  set Q : R[X] := P.scaleRoots (w ^ N) with hQ
  have hQm : Q.Monic := (monic_scaleRoots_iff _).2 hPm
  have hQlift : Q ∈ lifts (algebraMap A R) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    have hmem : Q.coeff i ∈ A := by
      rw [hQ, coeff_scaleRoots, hPdeg, hPcoeff]
      rcases lt_trichotomy i p.natDegree with hlt | heq | hgt
      · have h1 : (w ^ N) ^ (p.natDegree - i) = (w ^ N) ^ (p.natDegree - i - 1) * w ^ N := by
          rw [← pow_succ]; congr 1; omega
        rw [h1, mul_comm, mul_assoc]
        exact A.mul_mem (A.pow_mem (A.pow_mem hwA _) _) (hcN i hlt.le)
      · subst heq
        have : p.coeff p.natDegree = 1 := hpm.coeff_natDegree
        rw [this, Nat.sub_self, pow_zero, mul_one]
        exact A.one_mem
      · rw [coeff_eq_zero_of_natDegree_lt hgt]
        simp only [ZeroMemClass.coe_zero, zero_mul]
        exact A.zero_mem
    exact ⟨⟨_, hmem⟩, rfl⟩
  obtain ⟨q, hqQ, -, hqm⟩ := lifts_and_degree_eq_and_monic hQlift hQm
  refine ⟨N, q, hqm, ?_⟩
  rw [← eval_map, hqQ, hQ, scaleRoots_eval_mul, hP, eval_map, hp, mul_zero]

theorem chart_ext_pf (A T B0 Bu : Subalgebra K R) (hAT : A ≤ T) (hAB0 : A ≤ B0) (hB0 : B0 ≤ Bu) (hTBu : T ≤ Bu)
    (hB0FG : B0.FG) (hB0Int : ∀ b ∈ B0, IsIntegral A b) (hBuFG : Bu.FG) (hBuInt : ∀ b ∈ Bu, IsIntegral T b)
    (hFrac : ∀ r : R, ∃ b ∈ Bu, ∃ b' ∈ Bu, b' ≠ 0 ∧ r * b' = b)
    (w : R) (hwA : w ∈ A) (hw0 : w ≠ 0) (hscale : ∀ x ∈ T, ∃ N : ℕ, w ^ N * x ∈ A) :
    ∃ B' : Subalgebra K R, B0 ≤ B' ∧ B'.FG ∧ (∀ b ∈ B', IsIntegral A b) ∧
      ∀ r : R, ∃ b ∈ B', ∃ b' ∈ B', b' ≠ 0 ∧ r * b' = b := by
  classical
  obtain ⟨t, ht⟩ := hB0FG
  obtain ⟨s, hs⟩ := hBuFG
  have hkey : ∀ g : R, ∃ N : ℕ, g ∈ Bu → IsIntegral A (w ^ N * g) := by
    intro g
    by_cases hg : g ∈ Bu
    · obtain ⟨N, hN⟩ := chart_ext_scale A T w hwA hscale g (hBuInt g hg)
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => absurd h hg⟩
  choose N hN using hkey
  set u : Finset R := t ∪ s.image (fun g => w ^ N g * g) with hu
  set B' : Subalgebra K R := Algebra.adjoin K (u : Set R) with hB'
  have htB' : B0 ≤ B' := by
    rw [← ht, hB']
    exact Algebra.adjoin_mono (by rw [hu, Finset.coe_union]; exact Set.subset_union_left)
  have hwB' : w ∈ B' := htB' (hAB0 hwA)
  have hgen : ∀ g ∈ s, w ^ N g * g ∈ B' := by
    intro g hg
    apply Algebra.subset_adjoin
    rw [hu, Finset.coe_union]
    exact Or.inr (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hg))
  have hsBu : ∀ g ∈ s, g ∈ Bu := fun g hg => by
    rw [← hs]; exact Algebra.subset_adjoin (Finset.mem_coe.2 hg)

  have hpow : ∀ b ∈ Bu, ∃ L : ℕ, w ^ L * b ∈ B' := by
    intro b hb
    rw [← hs] at hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact ⟨N x, hgen x (Finset.mem_coe.1 hx)⟩
    | algebraMap k => exact ⟨0, by rw [pow_zero, one_mul]; exact B'.algebraMap_mem k⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨L1, h1⟩ := ihx
      obtain ⟨L2, h2⟩ := ihy
      refine ⟨L1 + L2, ?_⟩
      have : w ^ (L1 + L2) * (x + y) = w ^ L2 * (w ^ L1 * x) + w ^ L1 * (w ^ L2 * y) := by ring
      rw [this]
      exact B'.add_mem (B'.mul_mem (B'.pow_mem hwB' _) h1) (B'.mul_mem (B'.pow_mem hwB' _) h2)
    | mul x y _ _ ihx ihy =>
      obtain ⟨L1, h1⟩ := ihx
      obtain ⟨L2, h2⟩ := ihy
      refine ⟨L1 + L2, ?_⟩
      have : w ^ (L1 + L2) * (x * y) = (w ^ L1 * x) * (w ^ L2 * y) := by ring
      rw [this]
      exact B'.mul_mem h1 h2
  refine ⟨B', htB', ⟨u, hB'.symm⟩, ?_, ?_⟩
  · intro b hb
    rw [hB'] at hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      rw [hu, Finset.coe_union] at hx
      rcases hx with hx | hx
      · apply hB0Int
        rw [← ht]
        exact Algebra.subset_adjoin hx
      · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
        exact hN g (hsBu g hg)
    | algebraMap k =>
      have hk : algebraMap K R k ∈ A := A.algebraMap_mem k
      have : algebraMap K R k = algebraMap A R ⟨_, hk⟩ := rfl
      rw [this]
      exact isIntegral_algebraMap
    | add x y _ _ ihx ihy => exact ihx.add ihy
    | mul x y _ _ ihx ihy => exact ihx.mul ihy
  · intro r
    obtain ⟨b, hb, b', hb', hb'0, hrb⟩ := hFrac r
    obtain ⟨L1, h1⟩ := hpow b hb
    obtain ⟨L2, h2⟩ := hpow b' hb'
    refine ⟨w ^ (L1 + L2) * b, ?_, w ^ (L1 + L2) * b', ?_, ?_, ?_⟩
    · have : w ^ (L1 + L2) * b = w ^ L2 * (w ^ L1 * b) := by ring
      rw [this]; exact B'.mul_mem (B'.pow_mem hwB' _) h1
    · have : w ^ (L1 + L2) * b' = w ^ L1 * (w ^ L2 * b') := by ring
      rw [this]; exact B'.mul_mem (B'.pow_mem hwB' _) h2
    · exact mul_ne_zero (pow_ne_zero _ hw0) hb'0
    · rw [← hrb]; ring

end CrystallineSemistableComparison.Pb
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K : Type} [Field K] {R : Type} [CommRing R] [IsDomain R] [Algebra K R]

theorem chart_ext (A T B0 Bu : Subalgebra K R) (hAT : A ≤ T) (hAB0 : A ≤ B0) (hB0 : B0 ≤ Bu) (hTBu : T ≤ Bu)
    (hB0FG : B0.FG) (hB0Int : ∀ b ∈ B0, IsIntegral A b) (hBuFG : Bu.FG) (hBuInt : ∀ b ∈ Bu, IsIntegral T b)
    (hFrac : ∀ r : R, ∃ b ∈ Bu, ∃ b' ∈ Bu, b' ≠ 0 ∧ r * b' = b)
    (w : R) (hwA : w ∈ A) (hw0 : w ≠ 0) (hscale : ∀ x ∈ T, ∃ N : ℕ, w ^ N * x ∈ A) :
    ∃ B' : Subalgebra K R, B0 ≤ B' ∧ B'.FG ∧ (∀ b ∈ B', IsIntegral A b) ∧
      ∀ r : R, ∃ b ∈ B', ∃ b' ∈ B', b' ≠ 0 ∧ r * b' = b :=
  chart_ext_pf A T B0 Bu hAT hAB0 hB0 hTBu hB0FG hB0Int hBuFG hBuInt hFrac w hwA hw0 hscale

end CrystallineSemistableComparison.Pb
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.InfinityCoordAlgebraicIndependent
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

variable {K R : Type} [Field K] [CommRing R] [Algebra K R] {n : ℕ}

def u0 (t : Fin (n + 1) → Rˣ) : Fin (n + 1) → Rˣ :=
  Fin.cases (t 0)⁻¹ fun j => t j.succ * (t 0)⁻¹

def infinityDerivation (t : Fin (n + 1) → Rˣ) (D : Fin (n + 1) → Derivation K R R) : Fin (n + 1) → Derivation K R R :=
  Fin.cases (-((t 0 : R) • ∑ k, (t k : R) • D k)) fun j => (t 0 : R) • D j.succ

theorem derivation_sum_apply {ι : Type} (s : Finset ι) (f : ι → Derivation K R R) (x : R) :
    (∑ k ∈ s, f k) x = ∑ k ∈ s, f k x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

theorem infinityDerivation_coord (t : Fin (n + 1) → Rˣ) (D : Fin (n + 1) → Derivation K R R)
    (hD : ∀ k j, D k (t j) = if k = j then 1 else 0) (j l : Fin (n + 1)) :
    infinityDerivation t D j (u0 t l) = if j = l then 1 else 0 := by
  have huv : (t 0 : R) * (((t 0)⁻¹ : Rˣ) : R) = 1 := (t 0).mul_inv
  have hinv : ∀ k, D k (((t 0)⁻¹ : Rˣ) : R) = -(((t 0)⁻¹ : Rˣ) : R) ^ 2 * D k (t 0) := fun k => by
    rw [Derivation.leibniz_of_mul_eq_one (D k) (Units.inv_mul (t 0)), smul_eq_mul]
  induction j using Fin.cases <;> induction l using Fin.cases
  · simp only [infinityDerivation, u0, Fin.cases_zero, Derivation.neg_apply, Derivation.smul_apply, derivation_sum_apply, smul_eq_mul, hinv, hD]
    simp
    linear_combination ((t 0 : R) * (((t 0)⁻¹ : Rˣ) : R) + 1) * huv
  · simp only [infinityDerivation, u0, Fin.cases_zero, Fin.cases_succ, Derivation.neg_apply, Derivation.smul_apply,
      derivation_sum_apply, smul_eq_mul, Units.val_mul, Derivation.leibniz, hinv, hD]
    simp [show ∀ i : Fin n, (0 : Fin (n + 1)) = i.succ ↔ False from fun i => ⟨fun h => Fin.succ_ne_zero i h.symm, False.elim⟩]
    linear_combination ((t _ : R) * ((t 0 : R) * (((t 0)⁻¹ : Rˣ) : R) + 1)) * huv
  · simp [infinityDerivation, u0, Derivation.smul_apply, smul_eq_mul, hinv, hD, (Fin.succ_ne_zero _)]
  · simp only [infinityDerivation, u0, Fin.cases_succ, Derivation.smul_apply, smul_eq_mul, Units.val_mul, Derivation.leibniz,
      hinv, hD]
    simp [Fin.succ_ne_zero]

theorem jacobian_infinityDerivation (t : Fin (n + 1) → Rˣ) (D : Fin (n + 1) → Derivation K R R) (B : Subalgebra K R) :
    ∀ y ∈ jacS B D id, ∃ y' ∈ jacS B (infinityDerivation t D) id, y = -(((t 0)⁻¹ : Rˣ) : R) ^ (n + 2) * y' := by
  set C : Matrix (Fin (n + 1)) (Fin (n + 1)) R := Matrix.of fun j k =>
    Fin.cases (fun k => -((t 0 : R) * t k)) (fun j k => if j.succ = k then (t 0 : R) else 0) j k with hC
  have hCdet : C.det = -(t 0 : R) ^ (n + 2) := by
    rw [Matrix.det_of_isUpperTriangular]
    · rw [Fin.prod_univ_succ]
      simp [hC, Finset.prod_const, pow_succ]
      ring
    · intro i k hki
      induction i using Fin.cases with
      | zero => exact absurd hki (Fin.not_lt_zero k)
      | succ i =>
        simp only [id] at hki
        simp only [hC, Matrix.of_apply, Fin.cases_succ]
        rw [if_neg (show i.succ ≠ k from fun h => by subst h; exact lt_irrefl _ hki)]
  have hM : ∀ bs : Fin (n + 1) → B, (Matrix.of fun k l => infinityDerivation t D (id k) ((bs l : R))) =
      C * Matrix.of fun k l => D (id k) ((bs l : R)) := by
    intro bs; ext j l
    simp only [Matrix.of_apply, id, Matrix.mul_apply, hC]
    induction j using Fin.cases with
    | zero => simp [infinityDerivation, derivation_sum_apply, Finset.mul_sum, mul_assoc]
    | succ j => simp [infinityDerivation]
  have huv : (t 0 : R) * (((t 0)⁻¹ : Rˣ) : R) = 1 := (t 0).mul_inv
  intro y hy
  have key : jacS B D id ≤ (jacS B (infinityDerivation t D) id).map (AddMonoidHom.mulLeft (-(((t 0)⁻¹ : Rˣ) : R) ^ (n + 2))) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨b, bs, rfl⟩
    refine ⟨(b : R) * (Matrix.of fun k l => infinityDerivation t D (id k) ((bs l : R))).det,
      AddSubgroup.subset_closure ⟨b, bs, rfl⟩, ?_⟩
    simp only [AddMonoidHom.coe_mulLeft, hM, Matrix.det_mul, hCdet]
    have hp : (((t 0)⁻¹ : Rˣ) : R) ^ (n + 2) * (t 0 : R) ^ (n + 2) = 1 := by
      rw [← mul_pow, mul_comm, huv, one_pow]
    linear_combination ((b : R) * (Matrix.of fun k l => D (id k) ((bs l : R))).det) * hp
  obtain ⟨y', hy', rfl⟩ := key hy
  exact ⟨y', hy', rfl⟩

section torus

theorem tpow_add' {d : ℕ} (t : Fin d → Rˣ) (m m' : Fin d → ℤ) : tpow t (m + m') = tpow t m * tpow t m' := by
  simp [tpow, zpow_add, Finset.prod_mul_distrib]

theorem tpow_single {d : ℕ} (t : Fin d → Rˣ) (k : Fin d) (z : ℤ) : tpow t (Pi.single k z) = ((t k ^ z : Rˣ) : R) := by
  unfold tpow
  rw [Fintype.prod_eq_single k (fun j hj => by simp [Pi.single_apply, hj])]
  simp

theorem tpow_mem {d : ℕ} (t : Fin d → Rˣ) (S : Finset (Fin (d + 1))) {m : Fin d → ℤ} (hm : m ∈ expS S) :
    tpow t m ∈ torusS K t S :=
  Algebra.subset_adjoin ⟨m, hm, rfl⟩

theorem torusS_le_span {d : ℕ} (t : Fin d → Rˣ) (S : Finset (Fin (d + 1))) :
    (torusS K t S : Set R) ⊆ Submodule.span K (tpow t '' expS S) := by
  let M : Submonoid R :=
    { carrier := tpow t '' expS S
      one_mem' := ⟨0, ⟨fun k _ => le_refl 0, fun _ => by simp⟩, by simp [tpow]⟩
      mul_mem' := by
        rintro _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
        refine ⟨m + m', ⟨fun k hk => ?_, fun h0 => ?_⟩, tpow_add' t m m'⟩
        · have := hm.1 k hk; have := hm'.1 k hk; simp only [Pi.add_apply]; omega
        · have := hm.2 h0; have := hm'.2 h0; simp only [Pi.add_apply, Finset.sum_add_distrib]; omega }
  intro x hx
  have hx' : x ∈ Subalgebra.toSubmodule (Algebra.adjoin K (tpow t '' expS S)) := hx
  rw [Algebra.adjoin_eq_span] at hx'
  exact Submodule.span_mono (Submonoid.closure_le (S := M).2 le_rfl) hx'

theorem mem_exponentSet_zero_iff {n : ℕ} (m : Fin (n + 1) → ℤ) :
    m ∈ expS (Finset.univ.erase (0 : Fin (n + 2))) ↔ ∑ k, m k ≤ 0 := by
  simp [expS, Fin.succ_ne_zero]

def infinityExponent {n : ℕ} (e : Fin (n + 1) → ℕ) : Fin (n + 1) → ℤ := Fin.cons (-(∑ i, (e i : ℤ))) fun j => (e j.succ : ℤ)

theorem sum_u0Exp {n : ℕ} (e : Fin (n + 1) → ℕ) : ∑ k, infinityExponent e k = -(e 0 : ℤ) := by
  simp [infinityExponent, Fin.sum_univ_succ]

theorem infinityCoord_prod_pow (t : Fin (n + 1) → Rˣ) (e : Fin (n + 1) → ℕ) :
    (((∏ i, u0 t i ^ e i : Rˣ)) : R) = tpow t (infinityExponent e) := by
  unfold tpow infinityExponent
  congr 1
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [u0, Fin.cases_zero, Fin.cases_succ, Fin.cons_zero, Fin.cons_succ, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, zpow_natCast, Fin.sum_univ_succ, zpow_neg]
  rw [← Nat.cast_sum, ← Nat.cast_add, zpow_natCast, pow_add, mul_inv]
  simp only [inv_pow]
  ac_rfl

end torus

theorem infinityCoord_monomial_eq (t : Fin (n + 1) → Rˣ) (N : ℕ) (α : Fin (n + 1) → ℕ) (hα : ∑ i, α i ≤ N) :
    (t 0 : R) ^ N * ∏ i, (u0 t i : R) ^ α i =
      ∏ i, (t i : R) ^ (Fin.cons (N - ∑ i, α i) (fun j => α j.succ) : Fin (n + 1) → ℕ) i := by
  have huv : (t 0 : R) * (((t 0)⁻¹ : Rˣ) : R) = 1 := (t 0).mul_inv
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [u0, Fin.cases_zero, Fin.cases_succ, Fin.cons_zero, Fin.cons_succ, Units.val_mul, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [Fin.sum_univ_succ] at hα ⊢
  obtain ⟨k, hk⟩ : ∃ k, N = k + α 0 + ∑ j : Fin n, α j.succ := ⟨N - (α 0 + ∑ j : Fin n, α j.succ), by omega⟩
  have hk' : N - (α 0 + ∑ j : Fin n, α j.succ) = k := by omega
  rw [hk', hk]
  calc (t 0 : R) ^ (k + α 0 + ∑ j : Fin n, α j.succ) *
        ((((t 0)⁻¹ : Rˣ) : R) ^ α 0 * ((∏ j : Fin n, (t j.succ : R) ^ α j.succ) *
          (((t 0)⁻¹ : Rˣ) : R) ^ ∑ j : Fin n, α j.succ))
      = (t 0 : R) ^ k * (∏ j : Fin n, (t j.succ : R) ^ α j.succ) *
          ((t 0 : R) * (((t 0)⁻¹ : Rˣ) : R)) ^ α 0 *
          ((t 0 : R) * (((t 0)⁻¹ : Rˣ) : R)) ^ ∑ j : Fin n, α j.succ := by ring
    _ = _ := by rw [huv, one_pow, one_pow, mul_one, mul_one]

theorem infinityCoord_mem_torus (t : Fin (n + 1) → Rˣ) (j : Fin (n + 1)) :
    (u0 t j : R) ∈ torusS K t (Finset.univ.erase 0) := by
  have h := infinityCoord_prod_pow t (Pi.single j 1)
  rw [Fintype.prod_eq_single j (fun i hi => by simp [Pi.single_apply, hi])] at h
  simp only [Pi.single_eq_same, pow_one] at h
  rw [h]
  exact tpow_mem t _ ((mem_exponentSet_zero_iff _).2 (by rw [sum_u0Exp]; exact neg_nonpos.2 (Nat.cast_nonneg _)))

theorem infinityCoord_inv_mem (t : Fin (n + 1) → Rˣ) (j : Fin n) :
    (((u0 t j.succ)⁻¹ : Rˣ) : R) ∈ torusS K t (Finset.univ.erase 0) := by
  have h : (((u0 t j.succ)⁻¹ : Rˣ) : R) = tpow t (Pi.single 0 1 + Pi.single j.succ (-1)) := by
    rw [tpow_add', tpow_single, tpow_single, ← Units.val_mul]
    congr 1
    simp [u0, mul_comm]
  rw [h]
  exact tpow_mem t _ ((mem_exponentSet_zero_iff _).2 (by simp [Finset.sum_add_distrib]))

theorem infinityCoord_algebraicIndependent (t : Fin (n + 1) → Rˣ) (ht : AlgebraicIndependent K fun k => (t k : R)) :
    Function.Injective (MvPolynomial.aeval fun k => (u0 t k : R) : MvPolynomial (Fin (n + 1)) K →ₐ[K] R) := by
  classical
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro f hf
  set N := f.totalDegree
  let deg : (Fin (n + 1) →₀ ℕ) → ℕ := fun α => ∑ i, α i
  have hdeg : ∀ α ∈ f.support, deg α ≤ N := by
    intro α hα
    have := MvPolynomial.le_totalDegree hα
    refine le_trans (le_of_eq ?_) this
    simp only [deg]
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  let h : (Fin (n + 1) →₀ ℕ) → (Fin (n + 1) →₀ ℕ) := fun α =>
    Finsupp.equivFunOnFinite.symm (Fin.cons (N - deg α) (fun j => α j.succ))
  have hinj : ∀ α ∈ f.support, ∀ β ∈ f.support, h α = h β → α = β := by
    intro α hα β hβ hab
    have h0 := DFunLike.congr_fun hab 0
    have hs : ∀ j : Fin n, α j.succ = β j.succ := fun j => by
      simpa [h] using DFunLike.congr_fun hab j.succ
    simp only [h, deg, Fin.sum_univ_succ] at h0
    rw [Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_equivFunOnFinite_symm, Fin.cons_zero, Fin.cons_zero] at h0
    have ha := hdeg α hα; have hb := hdeg β hβ
    simp only [deg, Fin.sum_univ_succ] at ha hb
    have hsum : ∑ j : Fin n, α j.succ = ∑ j : Fin n, β j.succ := Finset.sum_congr rfl fun j _ => hs j
    ext i
    induction i using Fin.cases with
    | zero => omega
    | succ j => exact hs j
  let g : MvPolynomial (Fin (n + 1)) K := ∑ α ∈ f.support, MvPolynomial.monomial (h α) (f.coeff α)
  have hu : ∀ α : Fin (n + 1) →₀ ℕ, MvPolynomial.aeval (fun k => (u0 t k : R)) (MvPolynomial.monomial α (1 : K)) =
      ∏ i, (u0 t i : R) ^ α i := fun α => by
    rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have htm : ∀ α : Fin (n + 1) →₀ ℕ, MvPolynomial.aeval (fun k => (t k : R)) (MvPolynomial.monomial α (1 : K)) =
      ∏ i, (t i : R) ^ α i := fun α => by
    rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  have hg : MvPolynomial.aeval (fun k => (t k : R)) g = (t 0 : R) ^ N * MvPolynomial.aeval (fun k => (u0 t k : R)) f := by
    conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff f]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [g, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [← mul_one (f.coeff α), ← smul_eq_mul, ← MvPolynomial.smul_monomial, ← MvPolynomial.smul_monomial,
      map_smul, map_smul, hu, htm, mul_smul_comm, infinityCoord_monomial_eq t N α (hdeg α hα)]
    rfl
  rw [hf, mul_zero] at hg
  have hg0 : g = 0 := ht (hg.trans (map_zero _).symm)
  ext β
  rw [MvPolynomial.coeff_zero]
  by_contra hβ
  have hβ' : β ∈ f.support := MvPolynomial.mem_support_iff.2 hβ
  have := congrArg (AddMonoidAlgebra.coeff · (h β)) hg0
  rw [MvPolynomial.coeff_zero, MvPolynomial.coeff_sum, Finset.sum_eq_single β] at this
  · rw [MvPolynomial.coeff_monomial, if_pos rfl] at this
    exact hβ this
  · intro α hα hne
    rw [MvPolynomial.coeff_monomial, if_neg (fun e => hne (hinj α hα β hβ' e))]
  · intro hn; exact absurd hβ' hn

theorem infinityCoord_localization (t : Fin (n + 1) → Rˣ) (ht : AlgebraicIndependent K fun k => (t k : R)) :
    Function.Injective (MvPolynomial.aeval (fun k => (⟨u0 t k, infinityCoord_mem_torus t k⟩ : torusS K t (Finset.univ.erase 0))) :
      MvPolynomial (Fin (n + 1)) K →ₐ[K] torusS K t (Finset.univ.erase 0)) ∧
    ∀ a : torusS K t (Finset.univ.erase 0), ∃ f g : MvPolynomial (Fin (n + 1)) K,
      IsUnit (MvPolynomial.aeval (fun k => (⟨u0 t k, infinityCoord_mem_torus t k⟩ : torusS K t (Finset.univ.erase 0))) g) ∧
      a * MvPolynomial.aeval (fun k => (⟨u0 t k, infinityCoord_mem_torus t k⟩ : torusS K t (Finset.univ.erase 0))) g =
        MvPolynomial.aeval (fun k => (⟨u0 t k, infinityCoord_mem_torus t k⟩ : torusS K t (Finset.univ.erase 0))) f := by
  classical
  have hval : ∀ p : MvPolynomial (Fin (n + 1)) K,
      ((MvPolynomial.aeval (fun k => (⟨u0 t k, infinityCoord_mem_torus t k⟩ : torusS K t (Finset.univ.erase 0))) p :
        torusS K t (Finset.univ.erase 0)) : R) = MvPolynomial.aeval (fun k => (u0 t k : R)) p := fun p =>
    DFunLike.congr_fun (MvPolynomial.comp_aeval (fun k => (⟨u0 t k, infinityCoord_mem_torus t k⟩ : torusS K t (Finset.univ.erase 0)))
      (torusS K t (Finset.univ.erase 0)).val) p
  refine ⟨fun p q hpq => infinityCoord_algebraicIndependent t ht (by rw [← hval, ← hval, hpq]), ?_⟩
  have key : ∀ x ∈ Submodule.span K (tpow t '' expS (Finset.univ.erase (0 : Fin (n + 2)))),
      ∃ (f : MvPolynomial (Fin (n + 1)) K) (e : Fin n → ℕ),
        x * ∏ j, (u0 t j.succ : R) ^ e j = MvPolynomial.aeval (fun k => (u0 t k : R)) f := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, rfl⟩ := hx
      have hm' := (mem_exponentSet_zero_iff m).1 hm
      refine ⟨MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm
          (Fin.cons (Int.toNat (-∑ k, m k)) fun j => Int.toNat (m j.succ) : Fin (n + 1) → ℕ)) 1,
        fun j => Int.toNat (-m j.succ), ?_⟩
      rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      have e1 : ∏ j : Fin n, (u0 t j.succ : R) ^ Int.toNat (-m j.succ) =
          (((∏ i, u0 t i ^ (Fin.cons 0 (fun j => Int.toNat (-m j.succ)) : Fin (n + 1) → ℕ) i : Rˣ)) : R) := by
        rw [Fin.prod_univ_succ]; simp
      have e2 : ∏ i, (u0 t i : R) ^ (Finsupp.equivFunOnFinite.symm
          (Fin.cons (Int.toNat (-∑ k, m k)) fun j => Int.toNat (m j.succ) : Fin (n + 1) → ℕ)) i =
          (((∏ i, u0 t i ^ (Fin.cons (Int.toNat (-∑ k, m k)) fun j => Int.toNat (m j.succ) : Fin (n + 1) → ℕ) i : Rˣ))
            : R) := by
        simp
      rw [e1, e2, infinityCoord_prod_pow, infinityCoord_prod_pow, ← tpow_add']
      congr 1
      have h1 : ∑ j : Fin n, ((Int.toNat (m j.succ) : ℕ) : ℤ) - ∑ j : Fin n, ((Int.toNat (-m j.succ) : ℕ) : ℤ) =
          ∑ j : Fin n, m j.succ := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => Int.toNat_sub_toNat_neg _
      have h2 : ∑ k, m k = m 0 + ∑ j : Fin n, m j.succ := Fin.sum_univ_succ _
      have h4 : ((Int.toNat (-∑ k, m k) : ℕ) : ℤ) = -∑ k, m k := Int.toNat_of_nonneg (by linarith)
      funext i
      induction i using Fin.cases with
      | zero =>
        rw [h2] at h4
        simp only [infinityExponent, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.add_apply]
        push_cast
        linarith
      | succ j =>
        simp only [infinityExponent, Fin.cons_succ, Pi.add_apply]
        omega
    | zero => exact ⟨0, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨f1, e1, h1⟩ := hx
      obtain ⟨f2, e2, h2⟩ := hy
      refine ⟨f1 * ∏ j : Fin n, MvPolynomial.X j.succ ^ e2 j + f2 * ∏ j : Fin n, MvPolynomial.X j.succ ^ e1 j,
        e1 + e2, ?_⟩
      simp only [map_add (f := _), map_mul, map_prod, map_pow, MvPolynomial.aeval_X, Pi.add_apply, pow_add,
        Finset.prod_mul_distrib]
      rw [← h1, ← h2]; ring
    | smul c x _ hx =>
      obtain ⟨f, e, h⟩ := hx
      exact ⟨c • f, e, by rw [map_smul, ← h, smul_mul_assoc]⟩
  intro a
  obtain ⟨f, e, h⟩ := key a.1 (torusS_le_span t _ a.2)
  refine ⟨f, ∏ j : Fin n, MvPolynomial.X j.succ ^ e j, ?_, ?_⟩
  · rw [map_prod]
    refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one (fun j _ => ?_)
    rw [map_pow, MvPolynomial.aeval_X]
    refine IsUnit.pow _ (IsUnit.of_mul_eq_one ⟨_, infinityCoord_inv_mem t j⟩ (Subtype.ext ?_))
    simp
  · apply Subtype.ext
    rw [Subalgebra.coe_mul, hval, hval, ← h]
    simp [map_prod]

theorem infinityCoord_span_residue (t : Fin (n + 1) → Rˣ) :
    ∀ a ∈ torusS K t (Finset.univ.erase 0), (((t 0)⁻¹ : Rˣ) : R) ^ (n + 2) * a ∈
      Submodule.span K (tpow t '' {m | ∑ k, m k < -((n : ℤ) + 1)}) := by
  intro a ha
  have hc : (((t 0)⁻¹ : Rˣ) : R) ^ (n + 2) = tpow t (Pi.single 0 (-((n : ℤ) + 2))) := by
    rw [tpow_single, ← Units.val_pow_eq_pow_val]
    congr 1
  have key : Submodule.span K (tpow t '' expS (Finset.univ.erase (0 : Fin (n + 2)))) ≤
      (Submodule.span K (tpow t '' {m | ∑ k, m k < -((n : ℤ) + 1)})).comap
        (LinearMap.mulLeft K ((((t 0)⁻¹ : Rˣ) : R) ^ (n + 2))) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨m, hm, rfl⟩
    have hm' := (mem_exponentSet_zero_iff m).1 hm
    refine Submodule.subset_span ⟨m + Pi.single 0 (-((n : ℤ) + 2)), ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib]
      simp
      linarith
    · rw [tpow_add', ← hc, LinearMap.mulLeft_apply, mul_comm]
  exact key (torusS_le_span t _ ha)

theorem infinityCoord_span_residue_ne (t : Fin (n + 1) → Rˣ) :
    ∀ a ∈ torusS K t (Finset.univ.erase 0), (((t 0)⁻¹ : Rˣ) : R) ^ (n + 2) * a ∈
      Submodule.span K (tpow t '' {m | m ≠ fun _ => -1}) := by
  intro a ha
  refine Submodule.span_mono (Set.image_mono ?_) (infinityCoord_span_residue t a ha)
  intro m hm heq
  subst heq
  simp at hm

end CrystallineSemistableComparison.Pb
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Pb

theorem resid_alg : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (R : Type) [CommRing R] [IsDomain R] [Algebra K R]
    (t : Fin (n + 1) → Rˣ), AlgebraicIndependent K (fun k => (t k : R)) →
    ∀ (D : Fin (n + 1) → Derivation K R R), (∀ k j, D k (t j) = if k = j then 1 else 0) →
    ∀ (B : Finset (Fin (n + 2)) → Subalgebra K R), (∀ S, S.Nonempty → torusS K t S ≤ B S) → (∀ S, S.Nonempty → (B S).FG) →
    (∀ S, S.Nonempty → ∀ b ∈ B S, IsIntegral (torusS K t S) b) → (∀ i, B (Finset.univ.erase i) ≤ B Finset.univ) →
    (∀ r : R, ∃ b ∈ B Finset.univ, ∃ b' ∈ B Finset.univ, b' ≠ 0 ∧ r * b' = b) →
    ∀ (ω : Fin (n + 2) → R) (η : Fin (n + 1) → R), (∀ i, ω i ∈ jacS (B (Finset.univ.erase i)) D id) →
      (∀ k, η k ∈ jacS (B Finset.univ) D (Fin.succAbove k)) →
      ((∏ k, t k)⁻¹ : Rˣ) ≠ (∑ i, ω i + ∑ k : Fin (n + 1), (-1 : R) ^ (k : ℕ) * D k (η k) : R) :=
  by
  intro K _ _ n R _ _ _ t ht D hD B hTB hFG hInt hMono hFrac ω η hω hη heq
  have hne : ∀ i : Fin (n + 2), (Finset.univ.erase i).Nonempty := fun i => by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  have hune : (Finset.univ : Finset (Fin (n + 2))).Nonempty := Finset.univ_nonempty
  have hfin : FiniteDimensional (fldF K t) (FractionRing R) :=
    fldF_findim t (B Finset.univ) (hTB _ hune) (hFG _ hune) (hInt _ hune) hFrac
  obtain ⟨res, hres1, hres0, hresD⟩ := res_R t ht D hD

  let Φ : R →+ FractionRing R :=
    ((algebraMap (fldF K t) (FractionRing R)).toAddMonoidHom.comp
      (Algebra.trace (fldF K t) (FractionRing R)).toAddMonoidHom).comp
      (algebraMap R (FractionRing R)).toAddMonoidHom
  have hΦ : ∀ x, Φ x = algebraMap (fldF K t) (FractionRing R)
      (Algebra.trace (fldF K t) (FractionRing R) (algebraMap R (FractionRing R) x)) := fun _ => rfl

  have hchart : ∀ i : Fin (n + 2), ∃ B' : Subalgebra K R, B (Finset.univ.erase i) ≤ B' ∧
      torusS K t (Finset.univ.erase i) ≤ B' ∧ B'.FG ∧
      (∀ b ∈ B', IsIntegral (torusS K t (Finset.univ.erase i)) b) ∧
      ∀ r : R, ∃ b ∈ B', ∃ b' ∈ B', b' ≠ 0 ∧ r * b' = b := fun i => by
    obtain ⟨w, hwA, hw0, hscale⟩ := torus_scale (K := K) t i
    obtain ⟨B', hB', hFG', hInt', hFrac'⟩ := chart_ext (torusS K t (Finset.univ.erase i)) (torusS K t Finset.univ)
      (B (Finset.univ.erase i)) (B Finset.univ) (torusS_le_univ t _) (hTB _ (hne i)) (hMono i) (hTB _ hune)
      (hFG _ (hne i)) (hInt _ (hne i)) (hFG _ hune) (hInt _ hune) hFrac w hwA hw0 hscale
    exact ⟨B', hB', (hTB _ (hne i)).trans hB', hFG', hInt', hFrac'⟩

  have hω' : ∀ i, ∃ a : R, Φ (ω i) = algebraMap R (FractionRing R) a ∧ res a = 0 := by
    intro i
    obtain ⟨B', hB', hTB', hFG', hInt', hFrac'⟩ := hchart i
    induction i using Fin.cases with
    | zero =>
      obtain ⟨y', hy', hyeq⟩ := jacobian_infinityDerivation t D (B (Finset.univ.erase 0)) (ω 0) (hω 0)
      obtain ⟨hinj, hloc⟩ := infinityCoord_localization t ht
      obtain ⟨a', ha'S, ha'⟩ := trace_chart t (Finset.univ.erase 0) (fun k => ⟨u0 t k, infinityCoord_mem_torus t k⟩) hinj hloc
        (torusS_frac t _ (hne 0)) B' hTB' hFG' hInt' hFrac' (infinityDerivation t D) (fun k j => infinityDerivation_coord t D hD k j) id
        Function.injective_id y' (jacS_mono _ _ hB' _ _ hy')
      set c : R := -(((t 0)⁻¹ : Rˣ) : R) ^ (n + 2) with hc
      have hcT : c ∈ torusS K t Finset.univ := neg_mem (pow_mem (inv_mem_univ t 0) _)
      let cF : fldF K t := ⟨algebraMap R (FractionRing R) c, torus_mem_fldF t Finset.univ c hcT⟩
      refine ⟨c * a', ?_, ?_⟩
      · rw [hΦ, hyeq, RingHom.map_mul (algebraMap R (FractionRing R)) c y']
        have h1 : algebraMap R (FractionRing R) c * algebraMap R (FractionRing R) y' =
            cF • algebraMap R (FractionRing R) y' := rfl
        rw [h1, LinearMap.map_smul, smul_eq_mul, RingHom.map_mul, ha', RingHom.map_mul]
        rfl
      · rw [hc, neg_mul, map_neg, hres0 _ (infinityCoord_span_residue_ne t a' ha'S), neg_zero]
    | succ k =>
      have h0 : (0 : Fin (n + 2)) ∈ Finset.univ.erase k.succ :=
        Finset.mem_erase.mpr ⟨(Fin.succ_ne_zero k).symm, Finset.mem_univ _⟩
      obtain ⟨hinj, hloc⟩ := torusS_loc t ht _ h0
      obtain ⟨a, haS, ha⟩ := trace_chart t (Finset.univ.erase k.succ)
        (fun k => ⟨t k, t_mem_torusS t _ h0 k⟩) hinj hloc
        (torusS_frac t _ (hne _)) B' hTB' hFG' hInt' hFrac' D (fun k j => hD k j) id
        Function.injective_id (ω k.succ) (jacS_mono _ _ hB' _ _ (hω k.succ))
      exact ⟨a, ha, hres0 _ (torusS_succ_span t k a haS)⟩

  have hη' : ∀ k, ∃ b : R, Φ (D k (η k)) = algebraMap R (FractionRing R) b ∧ res b = 0 := by
    intro k
    obtain ⟨hinj, hloc⟩ := torusS_loc t ht Finset.univ (Finset.mem_univ 0)
    obtain ⟨b, hbT, hb⟩ := trace_chart t Finset.univ (fun k => ⟨t k, t_mem_torusS t _ (Finset.mem_univ 0) k⟩)
      hinj hloc (torusS_frac t _ hune) (B Finset.univ) (hTB _ hune) (hFG _ hune) (hInt _ hune) hFrac D
      (fun k j => hD k j) (Fin.succAbove k) Fin.succAbove_right_injective (η k) (hη k)
    have hDc : ∀ j, D k (t j : R) ∈ Set.range (algebraMap K R) := fun j => by
      rw [hD]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩
    exact ⟨D k b, trace_deriv t (D k) hDc (η k) b hbT hb, hresD k b hbT⟩
  choose a ha using hω'
  choose b hb using hη'

  have : Module.Free (fldF K t) (FractionRing R) := Module.Free.of_divisionRing _ _
  have hp : (((∏ k, t k)⁻¹ : Rˣ) : R) ∈ torusS K t Finset.univ := prod_inv_mem t
  let pF : fldF K t := ⟨algebraMap R (FractionRing R) (((∏ k, t k)⁻¹ : Rˣ) : R), torus_mem_fldF t _ _ hp⟩
  have hsign : ∀ (k : Fin (n + 1)) (x : R), (-1 : R) ^ (k : ℕ) * x = ((-1 : ℤ) ^ (k : ℕ)) • x := fun k x => by
    rw [zsmul_eq_mul]
    push_cast
    rfl
  have hrel : Module.finrank (fldF K t) (FractionRing R) • (((∏ k, t k)⁻¹ : Rˣ) : R) =
      ∑ i, a i + ∑ k : Fin (n + 1), ((-1 : ℤ) ^ (k : ℕ)) • b k := by
    apply IsFractionRing.injective R (FractionRing R)
    have h1 := congrArg Φ heq
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, hsign] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_nsmul, map_add (f := _), map_sum, map_sum]
    simp only [map_zsmul]
    simp only [map_zsmul, fun i => (ha i).1, fun k => (hb k).1] at h1
    rw [← h1, hΦ]
    have h2 : algebraMap R (FractionRing R) (((∏ k, t k)⁻¹ : Rˣ) : R) =
        algebraMap (fldF K t) (FractionRing R) pF := rfl
    rw [h2, Algebra.trace_algebraMap, map_nsmul]
  have hres := congrArg res hrel
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_nsmul, hres1, map_add (f := _), map_sum, map_sum] at hres
  simp only [map_zsmul, fun i => (ha i).2, fun k => (hb k).2, smul_zero, Finset.sum_const_zero, add_zero,
    nsmul_eq_mul, mul_one] at hres
  rw [Nat.cast_eq_zero] at hres
  exact (Module.finrank_pos (R := fldF K t) (M := FractionRing R)).ne' hres

end CrystallineSemistableComparison.Pb
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.Pb

theorem powK_ne_zero_main {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [ConnectedSpace X] (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) (c : HdR q 2)
    (hc : IsFirstChernDeRham q D c) : powK q c d ≠ 0 :=
  powK_ne_zero_of (by intro K _ _ X q _ n _ N i hci hiq; exact geo_setup q n N i hci hiq) resid_alg
    (by intro K _ X N _ q D i hD m e y hy s Λ; exact firstChern_local_exact q D i hD y hy s Λ) q d D hD c hc

end CrystallineSemistableComparison.Pb
