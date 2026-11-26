module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelLocalLatticeFourierPartsOrders
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteConesSiegelLevelStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinFormBilinFormsEqSumMinimiserValues

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimiserCellFunctionMinFinitelyManyCombinations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationFunctionCellEqMinIntegralComb
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalZEqOfSmulEqSum
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc

theorem evalZ_eq_of_smul_eq_sum {X : Type} [AddCommGroup X] [Module.Finite ℤ X] {φ : InvFun ℤ} {m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (h : φ.LinearOn γ) {b : LinearMap.BilinForm ℤ X} {k : ℕ} (hk : 0 < k)
    {cf : Fin m → ℕ} (he : k • b = ∑ j, cf j • γ j) : φ.evalZ b = ∑ j, ((cf j : ℝ) / k) * φ.evalZ (γ j) := by
  rw [← (linearOn_iff φ γ).1 h _ (fun j => by positivity), ← evalR_toReal]
  congr 1
  refine LinearMap.ext₂ fun x y => ?_
  have h1 := LinearMap.congr_fun₂ he x y
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul] at h1
  have h2 : (k : ℝ) * b x y = ∑ j, (cf j : ℝ) * γ j x y := by exact_mod_cast h1
  have hk' : (k : ℝ) ≠ 0 := by positivity
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
  rw [show ∑ j, (cf j : ℝ) / k * (γ j x y : ℝ) = (∑ j, (cf j : ℝ) * γ j x y) / k by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring, ← h2]
  field_simp

theorem polFn_eq_min_linear : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ r : ℕ, r ≤ g → ∀ (p : ℕ) (m : Fin p → ℕ) (γ : ∀ i, Fin (m i) → LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ i, IsCone id φ (γ i)) → ∃ (Nℓ : ℕ) (ℓ : Fin p → LinearMap.BilinForm ℤ (Fin r → ℤ) →ₗ[ℤ] ℤ), 0 < Nℓ ∧ ∀ b' : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∃ (i : Fin p) (k : ℕ) (cf : Fin (m i) → ℕ), 0 < k ∧ k • b' = ∑ j, cf j • γ i j) → (∀ i, (Nℓ : ℝ) * φ.evalZ b' ≤ ℓ i b') ∧ ∃ i, (Nℓ : ℝ) * φ.evalZ b' = ℓ i b' := by
  intro g φ _ r _ p m γ hγ
  choose N ℓ hN h1 h2 h3 using fun i => (hγ i).strict
  refine ⟨∏ i, N i, fun i => ((∏ j ∈ Finset.univ.erase i, N j : ℕ) : ℤ) • ℓ i,
    Finset.prod_pos fun i _ => hN i, ?_⟩
  rintro b' hs hp ⟨i, k, cf, hk, he⟩
  have hb : b' ∈ balForms (id : ℤ → ℤ) (Fin r → ℤ) := mem_balForms_int.2 hs
  have key : ∀ i, ((∏ j, N j : ℕ) : ℝ) = ((∏ j ∈ Finset.univ.erase i, N j : ℕ) : ℝ) * N i := fun i => by
    rw [← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have eq : ∀ i, (N i : ℝ) * φ.evalZ b' ≤ ℓ i b' := fun i => h2 i b' hb hp
  refine ⟨fun i' => ?_, i, ?_⟩
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [key i', mul_assoc]
    exact mul_le_mul_of_nonneg_left (eq i') (by positivity)
  · simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    rw [key i, mul_assoc]
    congr 1
    have hev := evalZ_eq_of_smul_eq_sum (hγ i).linear hk he
    have hl : (k : ℤ) * ℓ i b' = ∑ j, (cf j : ℤ) * ℓ i (γ i j) := by
      have := congrArg (ℓ i) he
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, map_nsmul, nsmul_eq_mul] using this
    have hl' : (k : ℝ) * ℓ i b' = ∑ j, (cf j : ℝ) * ℓ i (γ i j) := by exact_mod_cast hl
    have hk' : (k : ℝ) ≠ 0 := by positivity
    rw [hev, Finset.mul_sum, show (ℓ i b' : ℝ) = (∑ j, (cf j : ℝ) * ℓ i (γ i j)) / k by
      rw [← hl']; field_simp, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h1 i j]
    field_simp

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationFunctionCellEqMinIntegralComb
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem polFn_cell_eq_min_integral : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ r : ℕ, r ≤ g → ∀ μ : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b₀ x y = b₀ y x) → (∀ x, x ≠ 0 → 0 < b₀ x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b₀ (μ c) ≤ qW W b₀ α) → ∃ (ι : ℕ) (L : Finset ((Fin 8 → Fin r → ZMod N) → ℤ)), 1 ≤ ι ∧ ∀ (b' : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' ≤ ∑ c, (ν c : ℝ) * qW W b' (μ c)) ∧ ∃ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' = ∑ c, (ν c : ℝ) * qW W b' (μ c) := by
  classical
  intro g φ hφ W hW N _ hN3 hε r hr μ hμ b₀ hsym hpos hmin
  obtain ⟨p, m, γ, hcone, hcov⟩ := GlobalTheory.T.exists_finite_cones_siegel_level_structure g φ hφ W hW N hN3 r hr μ hμ b₀ hsym hpos hmin
  obtain ⟨Nℓ, ℓ, hNℓ, hℓ⟩ := polFn_eq_min_linear g φ hφ r hr p m γ hcone
  choose D ν hD hν using fun i : Fin p => GlobalTheory.T.linForm_bilinForms_eq_sum_minimiser_values W hW N hN3 hε r μ hμ (ℓ i)
  obtain ⟨E, hDE⟩ : ∃ E : Fin p → ℕ, ∀ i, D i * E i = ∏ j, D j :=
    ⟨fun i => ∏ j ∈ Finset.univ.erase i, D j, fun i => Finset.mul_prod_erase _ _ (Finset.mem_univ i)⟩
  have hDp : 0 < ∏ j, D j := Finset.prod_pos (fun j _ => hD j)
  refine ⟨Nℓ * ∏ j, D j, Finset.univ.image (fun i c => (N : ℤ) * (E i : ℤ) * ν i c), ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hNℓ.ne' hDp.ne')
  intro b' hs hp hm
  obtain ⟨i0, k, cf, hk, hkb⟩ := hcov b' hs hp hm
  obtain ⟨hle, i1, heq⟩ := hℓ b' hs hp ⟨i0, k, cf, hk, hkb⟩
  have key : ∀ i, ∑ c, ((((N : ℤ) * (E i : ℤ) * ν i c : ℤ)) : ℝ) * ((qW W b' (μ c) : ℤ) : ℝ)
      = ((N : ℝ) * (E i : ℝ) * (D i : ℝ)) * ((ℓ i b' : ℤ) : ℝ) := by
    intro i
    have h' : (((∑ c, ν i c * qW W b' (μ c) : ℤ)) : ℝ) = (((D i : ℤ) * ℓ i b' : ℤ) : ℝ) := by
      rw [hν i b' hs]
    push_cast at h' ⊢
    calc ∑ c, (N : ℝ) * (E i : ℝ) * (ν i c : ℝ) * (qW W b' (μ c) : ℝ)
        = (N : ℝ) * (E i : ℝ) * ∑ c, (ν i c : ℝ) * (qW W b' (μ c) : ℝ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun c _ => ?_); ring
      _ = _ := by rw [h']; ring
  have hι : ∀ i, ((Nℓ * ∏ j, D j : ℕ) : ℝ) * (N : ℝ)
      = ((N : ℝ) * (E i : ℝ) * (D i : ℝ)) * (Nℓ : ℝ) := by
    intro i; rw [← hDE i]; push_cast; ring
  refine ⟨fun ν' hν' => ?_, ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hν'
    have hc : (0 : ℝ) ≤ (N : ℝ) * (E i : ℝ) * (D i : ℝ) := by positivity
    calc ((Nℓ * ∏ j, D j : ℕ) : ℝ) * (N : ℝ) * φ.evalZ b'
        = ((N : ℝ) * (E i : ℝ) * (D i : ℝ)) * ((Nℓ : ℝ) * φ.evalZ b') := by rw [hι i]; ring
      _ ≤ ((N : ℝ) * (E i : ℝ) * (D i : ℝ)) * ((ℓ i b' : ℤ) : ℝ) := mul_le_mul_of_nonneg_left (hle i) hc
      _ = _ := (key i).symm
  · refine ⟨_, Finset.mem_image.mpr ⟨i1, Finset.mem_univ _, rfl⟩, ?_⟩
    calc ((Nℓ * ∏ j, D j : ℕ) : ℝ) * (N : ℝ) * φ.evalZ b'
        = ((N : ℝ) * (E i1 : ℝ) * (D i1 : ℝ)) * ((Nℓ : ℝ) * φ.evalZ b') := by rw [hι i1]; ring
      _ = ((N : ℝ) * (E i1 : ℝ) * (D i1 : ℝ)) * ((ℓ i1 b' : ℤ) : ℝ) := by rw [heq]
      _ = _ := (key i1).symm

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationFunctionCellEqMinIntegralCombStatement
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisationFunction_cell_eq_min_integral_comb : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ r : ℕ, r ≤ g → ∀ μ : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b₀ x y = b₀ y x) → (∀ x, x ≠ 0 → 0 < b₀ x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b₀ (μ c) ≤ qW W b₀ α) → ∃ (ι : ℕ) (L : Finset ((Fin 8 → Fin r → ZMod N) → ℤ)), 1 ≤ ι ∧ ∀ (b' : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' ≤ ∑ c, (ν c : ℝ) * qW W b' (μ c)) ∧ ∃ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' = ∑ c, (ν c : ℝ) * qW W b' (μ c) := by
  first | exact @GlobalTheory.Poinc.polFn_cell_eq_min_integral | exact GlobalTheory.Poinc.polFn_cell_eq_min_integral | (intros; apply GlobalTheory.Poinc.polFn_cell_eq_min_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsDefiniteFormsUpToAut
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntBilinFormToRealMemPsdConeOfPos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntBilinFormToRealMemPsdConeOfPos
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc

theorem toReal_mem_psdCone_of_pos_int : ∀ (r : ℕ) (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) →
    (∀ x, x ≠ 0 → 0 < b x x) → toReal b ∈ psdCone (bar := (id : ℤ → ℤ)) (X := (Fin r → ℤ)) := by
  intro r b hs hp
  refine TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 hs) fun y => ?_
  by_cases hy : y = 0
  · subst hy; simp
  · exact (hp y hy).le

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntBilinFormToRealMemPsdConeOfPosStatement
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intBilinFormToReal_mem_psdCone_of_pos : ∀ (r : ℕ) (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → toReal b ∈ psdCone (bar := (id : ℤ → ℤ)) (X := (Fin r → ℤ)) := by
  first | exact @GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int | exact GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int | (intros; apply GlobalTheory.Poinc.toReal_mem_psdCone_of_pos_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsDefiniteFormsUpToAut
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.MinSysType

theorem finite_minimiser_systems_upTo_aut : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W →
    ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, r ≤ g → ∃ S : Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)),
    ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) →
    ∃ e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ), ∀ μ' : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)),
    (∀ c u i, ((μ' c u i : ℤ) : ZMod N) = c u i) →
    (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) →
      qW W (pull e.toLinearMap b) (μ' c) ≤ qW W (pull e.toLinearMap b) α) → μ' ∈ S := by
  intro g φ hφ W hW N _ hN r hr
  classical
  have hX : IsPolFanOn id φ (Fin r → ℤ) := hφ (Fin r → ℤ) (by simpa using hr)
  obtain ⟨S₀, hS₀, hfin⟩ := hX.finite
  set F := hS₀.toFinset with hF
  let ι := Σ m : Fin (F.card + 1), (Fin m.val → F)
  let P : ι → Prop := fun i => IsCone id φ (fun j => ((i.2 j : F) : LinearMap.BilinForm ℤ (Fin r → ℤ))) ∧
    ∀ x, x ≠ 0 → 0 < ∑ j, ((i.2 j : F) : LinearMap.BilinForm ℤ (Fin r → ℤ)) x x
  let T : ι → Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)) := fun i =>
    if h : P i then Classical.choose (GlobalTheory.T.finite_minimiser_systems_smooth_cone φ W hW N hN r i.1.val _ h.1 h.2) else ∅
  refine ⟨Finset.univ.biUnion T, ?_⟩
  intro b hsym hpos
  have hpsd := GlobalTheory.T.intBilinFormToReal_mem_psdCone_of_pos r b hsym hpos
  obtain ⟨m, γ, cf, hcone, hcf, hb⟩ := GlobalTheory.T.exists_pos_combination_smoothCone_symmIntForm g φ hφ r hr b hsym hpsd
  obtain ⟨e, he⟩ := hfin m γ hcone
  refine ⟨e, fun μ' h1 h2 => ?_⟩
  let γ' : Fin m → F := fun j => ⟨pull e.toLinearMap (γ j), hS₀.mem_toFinset.2 (he j)⟩
  have hcone' := hcone.pull_equiv e
  have hinj : Function.Injective γ' := fun j k hjk => by
    have h := congrArg Subtype.val hjk
    simp only [γ'] at h
    exact hcone'.injective h
  have hm : m < F.card + 1 := by
    have := Fintype.card_le_of_injective γ' hinj
    simp only [Fintype.card_fin, Fintype.card_coe] at this
    omega
  let i : ι := ⟨⟨m, hm⟩, γ'⟩
  have hbyy : ∀ y, b y y = ∑ j, (cf j : ℤ) * γ j y y := fun y => by
    rw [hb]; simp [LinearMap.sum_apply]
  have hPi : P i := by
    refine ⟨hcone', fun x hx => ?_⟩
    simp only [i, γ', pull_apply]
    have hex : e x ≠ 0 := by simpa using hx
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ γ j (e x) (e x) := fun j _ => hcone.nonneg j _
    refine lt_of_le_of_ne (Finset.sum_nonneg hnn) fun h0 => ?_
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0.symm
    have := hpos _ hex
    rw [hbyy] at this
    simp [hz] at this
  have hmem : μ' ∈ T i := by
    simp only [T, dif_pos hPi]
    refine Classical.choose_spec (GlobalTheory.T.finite_minimiser_systems_smooth_cone φ W hW N hN r i.1.val _ hPi.1 hPi.2) (pull e.toLinearMap b) 1 cf
      one_pos hcf ?_ μ' h1 h2
    ext a c
    simp [i, γ', pull_apply, hb, LinearMap.sum_apply]
  exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hmem⟩

end GlobalTheory.Poinc.MinSysType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsDefiniteFormsUpToAutStatement
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_minimiser_systems_definite_forms_upTo_aut : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, r ≤ g → ∃ S : Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → ∃ e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ), ∀ μ' : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), (∀ c u i, ((μ' c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W (pull e.toLinearMap b) (μ' c) ≤ qW W (pull e.toLinearMap b) α) → μ' ∈ S := by
  first | exact @GlobalTheory.Poinc.MinSysType.finite_minimiser_systems_upTo_aut | exact GlobalTheory.Poinc.MinSysType.finite_minimiser_systems_upTo_aut | (intros; apply GlobalTheory.Poinc.MinSysType.finite_minimiser_systems_upTo_aut <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportMinimisersLatticeAutomorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportMinimisersLatticeAutomorphism
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory

theorem relabel_cong {N r : ℕ} (e : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ)) (x y : Fin r → ℤ)
    (h : ∀ i, ((x i : ℤ) : ZMod N) = y i) : ∀ i, ((e x i : ℤ) : ZMod N) = e y i := by
  have hd : ∀ i, (N : ℤ) ∣ x i - y i := fun i => (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h i).symm
  choose w hw using hd
  have hxy : x - y = (N : ℤ) • w := by ext i; simp [hw i]
  have he : e x - e y = (N : ℤ) • e w := by rw [← map_sub, hxy, map_smul]
  intro i
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have := congrFun he i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
  exact ⟨-(e w i), by linarith⟩

theorem qW_pull {s r : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) (f : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ))
    (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (y : Fin s → Fin r → ℤ) :
    qW W (pull f b) y = qW W b (fun u => f (y u)) := rfl

theorem relabel_minimisers : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (N : ℕ) [NeZero N] (r : ℕ) (μ : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ))), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ), ∃ σ : Equiv.Perm (Fin 8 → Fin r → ZMod N), (∀ c u i, ((e.symm (μ (σ c) u) i : ℤ) : ZMod N) = c u i) ∧ ∀ b' : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W (pull e.toLinearMap b') ((fun c u => e.symm (μ (σ c) u)) c) ≤ qW W (pull e.toLinearMap b') α) := by
  intro W N _ r μ hμ e
  have key : ∀ (f g : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ)), (∀ x, g (f x) = x) → ∀ c u i,
      ((g (μ (fun u i => ((f (μ c u) i : ℤ) : ZMod N)) u) i : ℤ) : ZMod N) = c u i := by
    intro f g hgf c u i
    rw [relabel_cong g _ (f (μ c u)) (fun j => hμ _ u j) i, hgf, hμ]
  let σ : Equiv.Perm (Fin 8 → Fin r → ZMod N) :=
    { toFun := fun c u i => ((e (μ c u) i : ℤ) : ZMod N)
      invFun := fun c u i => ((e.symm (μ c u) i : ℤ) : ZMod N)
      left_inv := fun c => by
        funext u i
        exact key e.toLinearMap e.symm.toLinearMap (fun x => e.symm_apply_apply x) c u i
      right_inv := fun c => by
        funext u i
        exact key e.symm.toLinearMap e.toLinearMap (fun x => e.apply_symm_apply x) c u i }
  refine ⟨σ, fun c u i => key e.toLinearMap e.symm.toLinearMap (fun x => e.symm_apply_apply x) c u i, ?_⟩
  intro b' hmin c α hα
  rw [qW_pull, qW_pull]
  have h1 : (fun u => e.toLinearMap ((fun c u => e.symm (μ (σ c) u)) c u)) = μ (σ c) := by
    funext u; simp
  rw [h1]
  apply hmin (σ c) (fun u => e.toLinearMap (α u))
  intro u i
  show _ = ((e (μ c u) i : ℤ) : ZMod N)
  exact relabel_cong e.toLinearMap (α u) (μ c u) (fun j => (hα u j).trans (hμ c u j).symm) i

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportMinimisersLatticeAutomorphismStatement
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transport_minimisers_latticeAutomorphism : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (N : ℕ) [NeZero N] (r : ℕ) (μ : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ))), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → ∀ e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ), ∃ σ : Equiv.Perm (Fin 8 → Fin r → ZMod N), (∀ c u i, ((e.symm (μ (σ c) u) i : ℤ) : ZMod N) = c u i) ∧ ∀ b' : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W (pull e.toLinearMap b') ((fun c u => e.symm (μ (σ c) u)) c) ≤ qW W (pull e.toLinearMap b') α) := by
  first | exact @GlobalTheory.relabel_minimisers | exact GlobalTheory.relabel_minimisers | (intros; apply GlobalTheory.relabel_minimisers <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimiserCellFunctionMinFinitelyManyCombinations
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem GlobalTheory.Poinc.finite_types : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ r : ℕ, r ≤ g → ∃ (ι : ℕ) (𝓛 : Finset (Finset ((Fin 8 → Fin r → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b (μ c) ≤ qW W b α) → ∃ L ∈ 𝓛, ∀ (b' : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' ≤ ∑ c, (ν c : ℝ) * qW W b' (μ c)) ∧ ∃ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' = ∑ c, (ν c : ℝ) * qW W b' (μ c) := by
  intro g φ hφ W hW N _ hN hε r hr
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_minimiser_systems_definite_forms_upTo_aut g φ hφ W hW N hN r hr
  have hP : ∀ μ' : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ),
      ((∀ c u i, ((μ' c u i : ℤ) : ZMod N) = c u i) ∧ ∃ b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ),
        (∀ x y, b₀ x y = b₀ y x) ∧ (∀ x, x ≠ 0 → 0 < b₀ x x) ∧
        (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b₀ (μ' c) ≤ qW W b₀ α)) →
      ∃ (ι : ℕ) (L : Finset ((Fin 8 → Fin r → ZMod N) → ℤ)), 1 ≤ ι ∧ ∀ (b' : LinearMap.BilinForm ℤ (Fin r → ℤ)),
        (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) →
        (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ' c) ≤ qW W b' α) →
        (∀ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' ≤ ∑ c, (ν c : ℝ) * qW W b' (μ' c)) ∧
          ∃ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' = ∑ c, (ν c : ℝ) * qW W b' (μ' c) :=
    fun μ' ⟨h1, b₀, h2, h3, h4⟩ => GlobalTheory.T.polarisationFunction_cell_eq_min_integral_comb g φ hφ W hW N hN hε r hr μ' h1 b₀ h2 h3 h4
  choose! ιf Lf hιf hLf using hP
  set ι : ℕ := ∏ μ' ∈ S, max (ιf μ') 1 with hιdef
  refine ⟨ι, S.biUnion fun μ' => Finset.univ.image fun σ : Equiv.Perm (Fin 8 → Fin r → ZMod N) =>
    (Lf μ').image fun ν c => ((ι / ιf μ' : ℕ) : ℤ) * ν (σ c), ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun _ _ => by omega)
  intro b hbs hbp μ hμ hmin
  obtain ⟨e, he⟩ := hS b hbs hbp
  obtain ⟨σ, hσ1, hσ2⟩ := GlobalTheory.T.exists_transport_minimisers_latticeAutomorphism W N r μ hμ e
  have hpd : ∀ x, x ≠ 0 → 0 < pull e.toLinearMap b x x := fun x hx => by
    simpa using hbp (e x) (by simpa using hx)
  have hPμ := And.intro hσ1 (⟨pull e.toLinearMap b, fun x y => hbs _ _, hpd, hσ2 b hmin⟩ :
    ∃ b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b₀ x y = b₀ y x) ∧ (∀ x, x ≠ 0 → 0 < b₀ x x) ∧
      (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) →
        qW W b₀ ((fun c u => e.symm (μ (σ c) u)) c) ≤ qW W b₀ α))
  have hmem := he _ hσ1 (hσ2 b hmin)
  have hι1 := hιf _ hPμ
  have hL := hLf _ hPμ
  set μ' : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ) := fun c u => e.symm (μ (σ c) u) with hμ'
  have hdvd : ιf μ' ∣ ι := by
    have := Finset.dvd_prod_of_mem (fun μ'' => max (ιf μ'') 1) hmem
    simpa [max_eq_left hι1] using this
  set k : ℕ := ι / ιf μ' with hk
  have hkι : (ι : ℝ) = k * ιf μ' := by exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  refine ⟨(Lf μ').image fun ν c => ((k : ℕ) : ℤ) * ν (σ.symm c),
    Finset.mem_biUnion.2 ⟨μ', hmem, Finset.mem_image.2 ⟨σ.symm, Finset.mem_univ _, rfl⟩⟩, ?_⟩
  intro b' hb's hb'p hb'min
  have key := hL (pull e.toLinearMap b') (fun x y => hb's _ _) (fun x => hb'p _) (hσ2 b' hb'min)
  have hφ' : φ.evalZ (pull e.toLinearMap b') = φ.evalZ b' := evalZ_pull φ e.surjective b'
  have hq : ∀ c, qW W (pull e.toLinearMap b') (μ' c) = qW W b' (μ (σ c)) := fun c => by
    simp [qW, μ']
  have hsum : ∀ ν : (Fin 8 → Fin r → ZMod N) → ℤ,
      ∑ c, ((((k : ℕ) : ℤ) * ν (σ.symm c) : ℤ) : ℝ) * qW W b' (μ c) =
        k * ∑ c, (ν c : ℝ) * qW W (pull e.toLinearMap b') (μ' c) := fun ν => by
    rw [Finset.mul_sum, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hq]; simp; ring
  have hlhs : (ι * N : ℝ) * φ.evalZ b' = k * ((ιf μ' * N : ℝ) * φ.evalZ (pull e.toLinearMap b')) := by
    rw [hφ', hkι]; ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  refine ⟨fun ν' hν' => ?_, ?_⟩
  · obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hν'
    rw [hsum, hlhs]
    exact mul_le_mul_of_nonneg_left (key.1 ν hν) hk0
  · obtain ⟨ν, hν, heq⟩ := key.2
    exact ⟨_, Finset.mem_image_of_mem _ hν, by rw [hsum, hlhs, heq]⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimiserCellFunctionMinFinitelyManyCombinationsStatement
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimiser_cell_function_min_finitely_many_combinations : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ r : ℕ, r ≤ g → ∃ (ι : ℕ) (𝓛 : Finset (Finset ((Fin 8 → Fin r → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b (μ c) ≤ qW W b α) → ∃ L ∈ 𝓛, ∀ (b' : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' ≤ ∑ c, (ν c : ℝ) * qW W b' (μ c)) ∧ ∃ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' = ∑ c, (ν c : ℝ) * qW W b' (μ c) := by
  first | exact @GlobalTheory.Poinc.finite_types | exact GlobalTheory.Poinc.finite_types | (intros; apply GlobalTheory.Poinc.finite_types <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BilinFormPsdOfMinimalTupleModN
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BilinFormPsdOfMinimalTupleModN
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem isE8_apply_zero_zero_pos {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : IsE8 W) : 0 < W 0 0 := by
  have h := hW.1.diag_pos (i := 0)
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply] at h
  have : (0:ℝ) < (W 0 0 : ℝ) := by push_cast at h; linarith
  exact_mod_cast this

theorem qW_add_smul_single {r : ℕ} (W : Matrix (Fin 8) (Fin 8) ℤ) (b : LinearMap.BilinForm ℤ (Fin r → ℤ))
    (μ : Fin 8 → Fin r → ℤ) (x : Fin r → ℤ) (s : ℤ) :
    qW W b (μ + s • (Pi.single 0 x : Fin 8 → Fin r → ℤ)) = qW W b μ +
      s * (∑ u, ∑ v, W u v * (b ((Pi.single 0 x : Fin 8 → Fin r → ℤ) u) (μ v) + b (μ u) ((Pi.single 0 x : Fin 8 → Fin r → ℤ) v)))
      + s ^ 2 * (W 0 0 * b x x) := by
  set e : Fin 8 → Fin r → ℤ := Pi.single 0 x with he
  have h3 : ∑ u, ∑ v, W u v * b (e u) (e v) = W 0 0 * b x x := by
    rw [Fintype.sum_eq_single 0]
    · rw [Fintype.sum_eq_single 0]
      · simp [he]
      · intro v hv; simp [he, Pi.single_apply, hv]
    · intro u hu; simp [he, Pi.single_apply, hu]
  have hpt : ∀ u v, W u v * b ((μ + s • e) u) ((μ + s • e) v) = W u v * b (μ u) (μ v)
      + s * (W u v * (b (e u) (μ v) + b (μ u) (e v))) + s ^ 2 * (W u v * b (e u) (e v)) := by
    intro u v
    simp only [Pi.add_apply, Pi.smul_apply, map_add (f := _), map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  unfold qW
  simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h3]

theorem psd_of_min : ∀ {r N : ℕ}, 0 < N → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (μ : Fin 8 → Fin r → ℤ), (∀ α : Fin 8 → Fin r → ℤ, (∀ u i, ∃ m : ℤ, α u i = μ u i + N * m) → qW W b μ ≤ qW W b α) → ∀ x, 0 ≤ b x x := by
  intro r N hN W hW b μ hmin x
  by_contra hx
  push_neg at hx
  have hW0 := isE8_apply_zero_zero_pos hW
  set e : Fin 8 → Fin r → ℤ := Pi.single 0 x with he
  set B : ℤ := ∑ u, ∑ v, W u v * (b (e u) (μ v) + b (μ u) (e v)) with hB
  set s : ℤ := (N : ℤ) * (|B| + 1) with hs
  have hmin' := hmin (μ + s • e) (by
    intro u i
    refine ⟨(|B| + 1) * e u i, ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs]
    ring)
  rw [qW_add_smul_single] at hmin'
  have hD : W 0 0 * b x x ≤ -1 := by nlinarith
  have hN1 : (1:ℤ) ≤ N := by exact_mod_cast hN
  have hBabs : -|B| ≤ B := neg_abs_le B
  have hBabs2 : B ≤ |B| := le_abs_self B
  have hA : 0 ≤ |B| := abs_nonneg B
  have hs1 : |B| + 1 ≤ s := by rw [hs]; nlinarith
  have h1 : s * B ≤ s * |B| := by nlinarith
  have h2 : s ^ 2 * (W 0 0 * b x x) ≤ - s ^ 2 := by nlinarith
  nlinarith

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BilinFormPsdOfMinimalTupleModNStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bilinForm_psd_of_minimal_tuple_modN : ∀ {r N : ℕ}, 0 < N → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)) (μ : Fin 8 → Fin r → ℤ), (∀ α : Fin 8 → Fin r → ℤ, (∀ u i, ∃ m : ℤ, α u i = μ u i + N * m) → qW W b μ ≤ qW W b α) → ∀ x, 0 ≤ b x x := by
  first | exact @GlobalTheory.Poinc.psd_of_min | exact GlobalTheory.Poinc.psd_of_min | (intros; apply GlobalTheory.Poinc.psd_of_min <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8FormValueCoprimeOddPrimePow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8FormValueCoprimeOddPrimePow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory
open Matrix

theorem exists_e8Form_value_not_dvd_prime (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) (p : ℕ) (hp : p.Prime) :
    ∃ ε : Fin 8 → ℤ, ¬ (p : ℤ) ∣ ∑ u, ∑ v, W u v * ε u * ε v := by
  by_contra h
  push_neg at h
  have hQ : ∀ ε : Fin 8 → ℤ, ∑ u, ∑ v, W u v * ε u * ε v = ε ⬝ᵥ (W *ᵥ ε) := by
    intro ε
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  have hA : ∀ i j, (p : ℤ) ∣ (W + W.transpose) i j := by
    intro i j
    have h1 := h (Pi.single i 1 + Pi.single j 1)
    have h2 := h (Pi.single i 1)
    have h3 := h (Pi.single j 1)
    rw [hQ] at h1 h2 h3
    have e : (Pi.single i 1 + Pi.single j 1 : Fin 8 → ℤ) ⬝ᵥ (W *ᵥ (Pi.single i 1 + Pi.single j 1))
        - (Pi.single i 1 : Fin 8 → ℤ) ⬝ᵥ (W *ᵥ Pi.single i 1)
        - (Pi.single j 1 : Fin 8 → ℤ) ⬝ᵥ (W *ᵥ Pi.single j 1) = (W + W.transpose) i j := by
      simp [Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.mulVec_single_one,
        single_dotProduct]
      ring
    rw [← e]
    exact dvd_sub (dvd_sub h1 h2) h3
  set A := W + W.transpose
  have hB : A = (p : ℤ) • Matrix.of (fun i j => A i j / p) := by
    ext i j
    simp [Int.mul_ediv_cancel' (hA i j)]
  have hdet : A.det = 1 := hW.2
  rw [hB, Matrix.det_smul] at hdet
  have : (p : ℤ) ∣ 1 := by
    rw [← hdet]
    exact Dvd.dvd.mul_right (dvd_pow_self _ (by simp)) _
  have := Int.eq_one_of_dvd_one (by positivity) this
  exact hp.one_lt.ne' (by exact_mod_cast this)

theorem exists_e8Form_value_coprime_oddPrimePow' : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (p k : ℕ), p.Prime → p ≠ 2 →
    ∃ ε : Fin 8 → ℤ, Nat.Coprime ((p ^ k) ^ 2) (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs) := by
  intro W hW p k hp hp2
  obtain ⟨ε, hε⟩ := exists_e8Form_value_not_dvd_prime W hW p hp
  refine ⟨ε, ?_⟩
  rw [← pow_mul]
  apply Nat.Coprime.pow_left
  apply Nat.Coprime.mul_right
  · rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact hp.one_lt.ne' h
    · exact hp2 h
  · rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    exact hε (Int.natCast_dvd.2 hd)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsE8FormValueCoprimeOddPrimePowStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_e8Form_value_coprime_oddPrimePow : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (p k : ℕ), p.Prime → p ≠ 2 → ∃ ε : Fin 8 → ℤ, Nat.Coprime ((p ^ k) ^ 2) (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs) := by
  first | exact @GlobalTheory.exists_e8Form_value_coprime_oddPrimePow' | exact GlobalTheory.exists_e8Form_value_coprime_oddPrimePow' | (intros; apply GlobalTheory.exists_e8Form_value_coprime_oddPrimePow' <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.Poinc.exists_locTuples_theta_of_adm : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), S.Big → SharpOver F W ρ.P u → (∀ w, (spMap S.R.val.toRingHom ≫ u) w ∈ genericPoints F.X) → ∃ (ι : ℕ) (K : Type) (_ : Fintype K) (Jk : K → Type) (_ : ∀ k, Fintype (Jk k)) (t : ∀ k, Jk k → Ω), 1 ≤ ι ∧ (∀ k j, t k j ≠ 0) ∧ ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, ∃ k, ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ FinalForm.u₀ u T ξ → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ (∀ j, OrdGe M T ξ (t k j) a) ∧ ∃ j, OrdEq M T ξ (t k j) a := by
  intro g n hg hn hodd F φ hφ W hW o' Ω _ _ _ _ S ρ u hBig hSharp hgen
  have hNodd : Odd S.N := by rw [ρ.N_eq]; exact (ρ.n_odd.pow).pow
  have hN2 := S.N_ge
  have hN3 : 3 ≤ S.N := by obtain ⟨j, hj⟩ := hNodd; omega
  haveI hN0 : NeZero S.N := ⟨by omega⟩
  have hn2 : ρ.n ≠ 2 := by
    intro h2; have := ρ.n_odd; rw [h2] at this; exact (Nat.not_odd_iff_even.2 even_two) this
  have hε : ∃ ε : Fin 8 → ℤ, Nat.Coprime S.N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs) := by
    rw [ρ.N_eq]; exact GlobalTheory.T.exists_e8Form_value_coprime_oddPrimePow W hW ρ.n ρ.k ρ.n_prime hn2
  have hC := GlobalTheory.T.minimiser_cell_function_min_finitely_many_combinations g φ hφ W hW.1 S.N hN3 hε
  choose ιf 𝓛f hιf using fun R : Fin (g + 1) => hC R.1 (Nat.lt_succ_iff.1 R.2)
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by omega)⟩
  haveI : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  haveI : Finite (AddSubgroup S.Gam) :=
    Finite.of_injective (fun H : AddSubgroup S.Gam => (H : Set S.Gam)) SetLike.coe_injective
  haveI : ∀ T₀ : AddSubgroup S.Gam, Finite (T₀ →+ ZMod S.N) := fun T₀ =>
    Finite.of_injective (fun f : T₀ →+ ZMod S.N => (f : T₀ → ZMod S.N)) DFunLike.coe_injective
  let Dt := Σ T₀ : AddSubgroup S.Gam, (T₀ →+ ZMod S.N) × (S.J × (T₀ → ZMod ((S.r * S.N) ^ 2))) × S.Gam
  haveI : Finite Dt := inferInstance
  let Es : Set Ω := {v | v ≠ 0} ∩ Set.range (fun d : Dt => S.FF d.1 d.2.1 d.2.2.1 / S.th d.2.2.2)
  have hEs : Es.Finite := (Set.finite_range _).inter_of_right _
  letI : Fintype Es := hEs.fintype
  let mult : Fin (g + 1) → ℕ := fun R => ∏ s ∈ Finset.univ.erase R, ιf s
  let K := Σ R : Fin (g + 1), Σ _ : {L // L ∈ 𝓛f R}, ((Fin 8 → Fin R.1 → ZMod S.N) → Es)
  let Jk : K → Type := fun k => {ν // ν ∈ k.2.1.1}
  let t : ∀ k, Jk k → Ω := fun k j => ∏ c, ((k.2.2 c : Es) : Ω) ^ ((mult k.1 : ℤ) * j.1 c)
  refine ⟨∏ R, ιf R, K, inferInstance, Jk, fun k => inferInstance, t, ?_, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2 fun R _ => by have := (hιf R).1; omega)
  · intro k j
    exact Finset.prod_ne_zero_iff.2 fun c _ => zpow_ne_zero _ (k.2.2 c).2.1
  intro M U₀ EE FinalForm hAdm hEE x
  obtain ⟨r, b₀, μ, e, hr, hsym, hpos, hμ, hmin, he, htr⟩ :=
    GlobalTheory.T.thetaModel_local_lattice_fourierParts_orders g n hg hn hodd F W hW o' Ω S ρ u hBig hSharp hgen hN0 M U₀ EE FinalForm hAdm hEE x
  let R : Fin (g + 1) := ⟨r, by omega⟩
  obtain ⟨hιR, hL⟩ := hιf R
  obtain ⟨L, hLmem, hLprop⟩ := hL b₀ hsym hpos μ hμ hmin
  have heE : ∀ c, e c ∈ Es := fun c => by
    obtain ⟨hne, T₀, c', κ, x₀, _, hc⟩ := he c
    exact ⟨hne, ⟨⟨T₀, c', κ, x₀⟩, hc.symm⟩⟩
  refine ⟨⟨R, ⟨L, hLmem⟩, fun c => ⟨e c, heE c⟩⟩, ?_⟩
  intro T ξ hthr hspec
  obtain ⟨π, hπs, hπmin, hq⟩ := htr T ξ hthr hspec

  set b' := T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap with hb'
  have hb'sym : ∀ x y, b' x y = b' y x := fun x y => T.symm _ _
  have hb'psd : ∀ x, 0 ≤ b' x x := GlobalTheory.T.bilinForm_psd_of_minimal_tuple_modN (N := S.N) (by omega) W hW b' (μ 0) fun α hα =>
    hπmin 0 α fun u i => by obtain ⟨m, hm⟩ := hα u i; simp [hm, hμ]
  obtain ⟨hle, ν₀, hν₀, heq⟩ := hLprop b' hb'sym hb'psd hπmin
  have hφeq : φ.evalZ b' = φ.evalZ T.β := by
    have hpull : pull π.toIntLinearMap T.β = b' := LinearMap.ext₂ fun _ _ => rfl
    rw [← hpull]; exact evalZ_pull φ (r := π.toIntLinearMap) hπs T.β
  have hφ0 : 0 ≤ φ.evalZ b' :=
    (hφ (Fin r → ℤ) (by rw [Module.finrank_fin_fun]; exact hr)).evalZ_nonneg (mem_balForms_int.2 hb'sym) hb'psd

  set y : Sp (FractionRing T.V) ⟶ M.Z := jK T.V ≫ ξ with hy
  set z₀ := y (IsLocalRing.closedPoint (FractionRing T.V)) with hz₀
  have hsp : ∀ w, y w ⤳ z₀ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hz₀U : z₀ ∈ U₀ := by
    obtain ⟨ξ₀, hξ₀, -⟩ := hthr
    rw [hz₀, hy, ← hξ₀]
    have hm : (ξ₀ ≫ U₀.ι) (IsLocalRing.closedPoint (FractionRing T.V)) ∈ Set.range U₀.ι := by
      exact ⟨ξ₀ (IsLocalRing.closedPoint (FractionRing T.V)), rfl⟩
    rw [U₀.range_ι] at hm; exact hm
  have hO : M.ringOn U₀ ≤ M.O z₀ := RatModel.ringOn_le_O (M := M) hz₀U
  have hOv := hAdm.1
  have hFFR : ∀ (T₀ : AddSubgroup S.Gam) c' κ, S.FF T₀ c' κ ∈ S.R := by
    intro T₀ c' κ
    haveI : Fintype T₀ := Fintype.ofFinite _
    unfold ThetaSys.FF
    rw [finsum_eq_sum_of_fintype]
    exact Subalgebra.sum_mem _ fun t _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (S.ev_mem _ _))
  have hunit : ∀ c, e c ≠ 0 ∧ e c ∈ M.O z₀ ∧ (e c)⁻¹ ∈ M.O z₀ := by
    intro c
    obtain ⟨hne, T₀, c', κ, x₀, hiso, hc⟩ := he c
    rw [hc] at hne ⊢
    have hF : S.FF T₀ c' κ ≠ 0 := (div_ne_zero_iff.1 hne).1
    have hth : S.th x₀ ≠ 0 := (div_ne_zero_iff.1 hne).2
    refine ⟨hne, hO ?_, hO ?_⟩
    · rw [div_eq_mul_inv]; exact Subalgebra.mul_mem _ (hOv.le (hFFR T₀ c' κ)) (hOv.th_unit x₀ hth)
    · rw [inv_div, div_eq_mul_inv]
      exact Subalgebra.mul_mem _ (hOv.le (S.th_mem x₀)) (hOv.FF_unit T₀ c' κ hiso hF)
  have hvne : ∀ c, M.val y (e c) ≠ 0 := by
    intro c
    have h1 := RatModel.val_mul (M := M) hsp (hunit c).2.1 (hunit c).2.2
    rw [mul_inv_cancel₀ (hunit c).1, RatModel.val_one] at h1
    exact left_ne_zero_of_mul_eq_one h1.symm
  have hpow : ∀ c, M.val y (e c ^ S.N) = M.val y (e c) ^ S.N := by
    intro c
    have := GlobalTheory.T.integralModel_value_prod_zpow_localUnits M y z₀ hsp (Finset.univ : Finset Unit) (fun _ => e c) (fun _ => (S.N : ℤ)) fun _ => hunit c
    simpa using this
  choose v w hvw using fun c => GlobalTheory.T.fractionRing_eq_uniformiser_zpow_mul_unit T.irr (M.val y (e c)) (hvne c)

  have hϖ0 : algebraMap T.V (FractionRing T.V) T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 T.irr.ne_zero
  have hunitK : ∀ (a : T.Vˣ) (k : ℤ), algebraMap T.V (FractionRing T.V) ((a ^ k : T.Vˣ) : T.V) =
      (algebraMap T.V (FractionRing T.V) (a : T.V)) ^ k := by
    intro a k
    have h1 : algebraMap T.V (FractionRing T.V) ((a ^ k : T.Vˣ) : T.V) =
        ((Units.map (algebraMap T.V (FractionRing T.V)).toMonoidHom (a ^ k) : (FractionRing T.V)ˣ) : FractionRing T.V) := rfl
    rw [h1, map_zpow, Units.val_zpow_eq_zpow_val]; rfl
  have hNv : ∀ c, (S.N : ℤ) * v c = qW W b' (μ c) := by
    intro c
    obtain ⟨hq0, w', hw'⟩ := hq c
    rw [hpow] at hw'
    have h2 : algebraMap T.V (FractionRing T.V) T.ϖ ^ ((S.N : ℤ) * v c) *
        algebraMap T.V (FractionRing T.V) ((w c ^ (S.N : ℤ) : T.Vˣ) : T.V) =
        algebraMap T.V (FractionRing T.V) T.ϖ ^ (((qW W b' (μ c)).toNat : ℕ) : ℤ) *
        algebraMap T.V (FractionRing T.V) (w' : T.V) := by
      rw [hunitK, mul_comm (S.N : ℤ) (v c), zpow_mul, zpow_natCast, zpow_natCast, ← mul_pow, ← hvw c, hw',
        map_mul, map_pow, zpow_natCast]
    have := GlobalTheory.T.uniformiser_zpow_mul_unit_exponent_unique T.irr _ _ _ _ h2
    rw [this, Int.toNat_of_nonneg hq0]
  have hmR : (∏ R', ιf R') = ιf R * mult R := (Finset.mul_prod_erase Finset.univ ιf (Finset.mem_univ R)).symm
  let E : ((Fin 8 → Fin r → ZMod S.N) → ℤ) → ℤ := fun ν => ∑ c, v c * ((mult R : ℤ) * ν c)
  have hE : ∀ ν, (S.N : ℝ) * (E ν : ℝ) = (mult R : ℝ) * ∑ c, (ν c : ℝ) * (qW W b' (μ c) : ℝ) := by
    intro ν
    simp only [E, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hNv c]; push_cast; ring
  have hzs : ∀ (f : (Fin 8 → Fin r → ZMod S.N) → ℤ) (s : Finset (Fin 8 → Fin r → ZMod S.N)),
      ∏ c ∈ s, algebraMap T.V (FractionRing T.V) T.ϖ ^ f c = algebraMap T.V (FractionRing T.V) T.ϖ ^ ∑ c ∈ s, f c := by
    intro f s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hϖ0]
  have hval : ∀ ν, M.val y (∏ c, e c ^ ((mult R : ℤ) * ν c)) = algebraMap T.V (FractionRing T.V) T.ϖ ^ E ν *
      algebraMap T.V (FractionRing T.V) ((∏ c, w c ^ ((mult R : ℤ) * ν c) : T.Vˣ) : T.V) := by
    intro ν
    rw [GlobalTheory.T.integralModel_value_prod_zpow_localUnits M y z₀ hsp _ _ _ fun c => hunit c]
    simp only [hvw, mul_zpow, Finset.prod_mul_distrib, ← zpow_mul, ← hunitK]
    rw [hzs, Units.coe_prod, map_prod]
  have hprodO : ∀ ν : (Fin 8 → Fin r → ZMod S.N) → ℤ, (∏ c, e c ^ ((mult R : ℤ) * ν c)) ∈ M.O z₀ := by
    intro ν
    refine Subalgebra.prod_mem _ fun c _ => ?_
    rcases Int.eq_nat_or_neg ((mult R : ℤ) * ν c) with ⟨k, hk | hk⟩ <;> rw [hk]
    · rw [zpow_natCast]; exact Subalgebra.pow_mem _ (hunit c).2.1 k
    · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact Subalgebra.pow_mem _ (hunit c).2.2 k
  have hιeq : ((∏ R', ιf R' : ℕ) : ℝ) = (ιf R : ℝ) * mult R := by rw [hmR]; push_cast; ring
  have hNpos : (0 : ℝ) < S.N := by exact_mod_cast (show 0 < S.N by omega)
  have hge : ∀ ν ∈ L, ((∏ R', ιf R' : ℕ) : ℝ) * φ.evalZ T.β ≤ E ν := by
    intro ν hν
    have h1 := mul_le_mul_of_nonneg_left (hle ν hν) (Nat.cast_nonneg (α := ℝ) (mult R))
    rw [← hE ν] at h1
    rw [hιeq, ← hφeq]
    refine le_of_mul_le_mul_left ?_ hNpos
    nlinarith
  have hE0 : ((E ν₀ : ℤ) : ℝ) = ((∏ R', ιf R' : ℕ) : ℝ) * φ.evalZ T.β := by
    have h1 := congrArg (HMul.hMul (mult R : ℝ)) heq
    rw [← hE ν₀] at h1
    rw [hιeq, ← hφeq]
    refine mul_left_cancel₀ hNpos.ne' ?_
    nlinarith
  have hEnn : 0 ≤ E ν₀ := by
    have : (0 : ℝ) ≤ (E ν₀ : ℝ) := by
      rw [hE0]; exact mul_nonneg (Nat.cast_nonneg _) (hφeq ▸ hφ0)
    exact_mod_cast this
  refine ⟨(E ν₀).toNat, ?_, ?_, ?_⟩
  · rw [← hE0]; exact_mod_cast Int.toNat_of_nonneg hEnn
  · intro j
    show GlobalTheory.Poinc.OrdGe M T ξ (∏ c, e c ^ ((mult R : ℤ) * j.1 c)) _
    have hle' : E ν₀ ≤ E j.1 := by
      have := hge j.1 j.2; rw [← hE0] at this; exact_mod_cast this
    obtain ⟨d, hd⟩ : ∃ d : ℕ, E j.1 = ((E ν₀).toNat : ℤ) + d := ⟨(E j.1 - E ν₀).toNat, by omega⟩
    refine ⟨hprodO j.1, T.ϖ ^ d * ((∏ c, w c ^ ((mult R : ℤ) * j.1 c) : T.Vˣ) : T.V), ?_⟩
    rw [hval, hd, map_mul, map_mul, map_pow, map_pow, zpow_add₀ hϖ0, zpow_natCast, zpow_natCast, mul_assoc]
  · refine ⟨⟨ν₀, hν₀⟩, ?_⟩
    show GlobalTheory.Poinc.OrdEq M T ξ (∏ c, e c ^ ((mult R : ℤ) * ν₀ c)) _
    refine ⟨∏ c, w c ^ ((mult R : ℤ) * ν₀ c), ?_⟩
    rw [hval, map_mul, map_pow, ← zpow_natCast, Int.toNat_of_nonneg hEnn]
