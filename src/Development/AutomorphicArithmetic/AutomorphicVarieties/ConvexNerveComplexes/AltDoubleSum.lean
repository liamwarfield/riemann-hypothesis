module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.AltDoubleSum
open Set UpperTheory.V.ConeExtensionAcyclic

private theorem UpperTheory.V.ConeExtensionAcyclic.succAbove_predAbove_val (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)) :
    ((i.succAbove j : ℕ) = if (j : ℕ) < i then (j : ℕ) else j + 1) ∧
      ((j.predAbove i : ℕ) = if (j : ℕ) < i then (i : ℕ) - 1 else i) := by
  by_cases h : (j : ℕ) < i
  · have h' : j.castSucc < i := by
      rw [Fin.lt_def, Fin.coe_castSucc]
      exact h
    rw [Fin.succAbove_of_castSucc_lt _ _ h', Fin.predAbove_of_castSucc_lt _ _ h']
    simp [h]
  · have h' : i ≤ j.castSucc := by
      rw [Fin.le_def, Fin.coe_castSucc]
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ h', Fin.predAbove_of_le_castSucc _ _ h']
    simp [h]

private theorem UpperTheory.V.ConeExtensionAcyclic.alt_double_sum {M : Type*} [AddCommGroup M] [IsAddTorsionFree M]
    (n : ℕ) (f : Fin (n + 2) → Fin (n + 1) → M)
    (hf : ∀ i j, f (i.succAbove j) (j.predAbove i) = f i j) :
    ∑ i : Fin (n + 2), ∑ j : Fin (n + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) • f i j = 0 := by
  let φ : Fin (n + 2) × Fin (n + 1) → Fin (n + 2) × Fin (n + 1) :=
    fun p => (p.1.succAbove p.2, p.2.predAbove p.1)
  have hinv : ∀ p, φ (φ p) = p := by
    rintro ⟨i, j⟩
    obtain ⟨h1, h2⟩ := UpperTheory.V.ConeExtensionAcyclic.succAbove_predAbove_val n i j
    obtain ⟨h3, h4⟩ := UpperTheory.V.ConeExtensionAcyclic.succAbove_predAbove_val n (i.succAbove j) (j.predAbove i)
    simp only [φ, Prod.mk.injEq, Fin.ext_iff]
    have hi := i.isLt
    have hj := j.isLt
    split_ifs at h1 h2 h3 h4 <;> omega
  have hsign : ∀ p : Fin (n + 2) × Fin (n + 1),
      ((-1 : ℤ) ^ (((φ p).1 : ℕ) + ((φ p).2 : ℕ))) = -((-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ))) := by
    rintro ⟨i, j⟩
    obtain ⟨h1, h2⟩ := UpperTheory.V.ConeExtensionAcyclic.succAbove_predAbove_val n i j
    simp only [φ]
    rw [h1, h2]
    split_ifs with h
    · have e : (j : ℕ) + ((i : ℕ) - 1) + 1 = (i : ℕ) + j := by omega
      rw [← neg_one_mul ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))), ← e, pow_succ]
      ring
    · rw [show (j : ℕ) + 1 + i = (i : ℕ) + j + 1 by omega, pow_succ]
      ring
  let e : Fin (n + 2) × Fin (n + 1) ≃ Fin (n + 2) × Fin (n + 1) :=
    { toFun := φ, invFun := φ, left_inv := hinv, right_inv := hinv }
  set S := ∑ i : Fin (n + 2), ∑ j : Fin (n + 1), ((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) • f i j with hS
  have hneg : S = -S := by
    rw [hS, ← Finset.sum_neg_distrib]
    simp only [← Finset.sum_neg_distrib]
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    refine Fintype.sum_equiv e _ _ ?_
    intro p
    show _ = -(((-1 : ℤ) ^ (((φ p).1 : ℕ) + ((φ p).2 : ℕ))) • f (φ p).1 (φ p).2)
    rw [hsign p]
    have hfp : f (φ p).1 (φ p).2 = f p.1 p.2 := hf p.1 p.2
    rw [hfp, neg_smul, neg_neg]
  have h2 : (2 : ℕ) • S = (2 : ℕ) • (0 : M) := by
    rw [two_nsmul, smul_zero]
    nth_rewrite 1 [hneg]
    exact neg_add_cancel S
  exact eq_of_nsmul_eq_nsmul_of_addCommute (by norm_num) (AddCommute.all _ _) h2

theorem UpperTheory.V.ConeExtensionAcyclic.bd_bd :
    ∀ (I : Type) (n : ℕ) (c : Ch I (n + 2)), bd I n (bd I (n + 1) c) = 0 := by
  intro I n c
  have hlin : (bd I n).comp (bd I (n + 1)) = 0 := by
    apply Finsupp.lhom_ext
    intro t a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, bd, Finsupp.linearCombination_single,
      map_smul, map_sum, one_smul, smul_smul, Finset.smul_sum]
    have hterm : ∀ (i : Fin (n + 2)) (j : Fin (n + 1)),
        (a * (-1) ^ (i : ℕ) * (1 * (-1) ^ (j : ℕ))) •
            (Finsupp.single ((t ∘ i.succAbove) ∘ j.succAbove) (1 : ℤ)) =
          a • (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) •
            Finsupp.single ((t ∘ i.succAbove) ∘ j.succAbove) (1 : ℤ)) := by
      intro i j
      rw [smul_smul, pow_add]
      congr 1
      ring
    simp only [hterm, ← Finset.smul_sum]
    rw [UpperTheory.V.ConeExtensionAcyclic.alt_double_sum n (fun i j => Finsupp.single ((t ∘ i.succAbove) ∘ j.succAbove) (1 : ℤ)), smul_zero]
    intro i j
    congr 1
    funext k
    simp only [Function.comp_apply]
    rw [Fin.succAbove_succAbove_succAbove_predAbove]
  exact LinearMap.congr_fun hlin c
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.BdMem
open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.bd_mem :
    ∀ {I : Type} {S : ∀ n, Set (Fin n → I)}, FaceClosed S → ∀ (n : ℕ) (c : Ch I (n + 1)), c ∈ Finsupp.supported ℤ ℤ (S (n + 1)) → bd I n c ∈ Finsupp.supported ℤ ℤ (S n) := by
  intro I S hS n c hc
  rw [bd, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
  exact Finsupp.single_mem_supported ℤ _ (hS n t (hc (Finset.mem_coe.2 ht)) j)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.Perturb
open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.perturb :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : Y → E →L[ℝ] ℝ}, LocFin q → ∀ h ∈ poly q, ∀ k : E, (∀ y, q y h = 1 → q y k = 0) → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s| ≤ ε → h + s • k ∈ poly q := by
  intro E Y _ _ q hq h hh k hk
  have hh' : ∀ y, 1 ≤ q y h := hh
  obtain ⟨S, hS, hU⟩ := hq h hh
  have hc : Continuous fun s : ℝ => h + s • k :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hT : Filter.Tendsto (fun s : ℝ => h + s • k) (nhds 0) (nhds h) := by
    have := hc.tendsto 0
    simpa using this
  have A : ∀ᶠ s in nhds (0:ℝ), ∀ y ∉ S, 1 < q y (h + s • k) := hT.eventually hU
  have B : ∀ᶠ s in nhds (0:ℝ), ∀ y ∈ S, 1 ≤ q y (h + s • k) := by
    refine (Filter.eventually_all_finite hS).2 fun y _ => ?_
    by_cases hy : q y h = 1
    · refine Filter.Eventually.of_forall fun s => ?_
      simp [hy, hk y hy]
    · have hlt : 1 < q y h := lt_of_le_of_ne (hh' y) (Ne.symm hy)
      have hcy : Continuous fun s : ℝ => q y (h + s • k) := (q y).continuous.comp hc
      have ht := hcy.tendsto 0
      simp only [zero_smul, add_zero] at ht
      exact (ht.eventually (lt_mem_nhds hlt)).mono fun s hs => hs.le
  obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.1 (A.and B)
  refine ⟨δ / 2, half_pos hδ, fun s hs => ?_⟩
  have hd : dist s 0 < δ := by
    rw [Real.dist_eq, sub_zero]
    linarith
  obtain ⟨h1, h2⟩ := hP hd
  show ∀ y, 1 ≤ q y (h + s • k)
  intro y
  by_cases hyS : y ∈ S
  · exact h2 y hyS
  · exact (h1 y hyS).le
end
