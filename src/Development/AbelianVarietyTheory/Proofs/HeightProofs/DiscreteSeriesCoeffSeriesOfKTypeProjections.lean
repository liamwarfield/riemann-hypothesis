module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRightKFourierSeriesUnitaryModerateGrowth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteResidueField
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TraceBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundTwo
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem coefBound_two :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → CoefBound ε σ → ∀ a c : H, Sm ε σ a → a ≠ 0 → Sm ε σ c → c ≠ 0 → ∀ N : ℕ, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ γ : H → H → ℂ, (∀ b, Sm ε σ b → SobFun ε σ (γ b)) → (∀ w, Sm ε σ w → SobFun ε σ (fun b => star (γ b w))) → ∀ M : ℝ, 0 ≤ M → (∀ g ∈ UJset ε, ∀ g' ∈ UJset ε, ‖γ (σ g' c) (σ g a)‖ ≤ M * (1 + hs g) ^ N * (1 + hs g') ^ N) → ∀ b w, Sm ε σ b → Sm ε σ w → ‖γ b w‖ ≤ C * M * sobNorm σ S b * sobNorm σ S w := by
  intro n ε H _ _ _ σ hS hB a c ha ha0 hc hc0 N
  obtain ⟨Sa, Ca, hSa, hCa, ba⟩ := hB a ha ha0 N
  obtain ⟨Sc, Cc, hSc, hCc, bc⟩ := hB c hc hc0 N
  refine ⟨Sa ++ Sc, Ca * Cc, words_append hSa hSc, mul_nonneg hCa hCc, ?_⟩
  intro γ h1 h2 M hM hγ b w hb hw
  have step : ∀ g' ∈ UJset ε, ‖γ (σ g' c) w‖ ≤ (Ca * M * sobNorm σ Sa w) * (1 + hs g') ^ N := by
    intro g' hg'
    obtain ⟨ℓ, hℓ, e⟩ := (h1 _ (hc.translate hS.1 hg')).exists_ext
    have hp : 0 ≤ (1 + hs g') ^ N := pow_nonneg (by linarith [hs_nonneg g']) N
    have := ba ℓ hℓ (M * (1 + hs g') ^ N) (mul_nonneg hM hp) (fun g hg => by
      rw [e _ (ha.translate hS.1 hg)]
      exact (hγ g hg g' hg').trans (le_of_eq (by ring))) w hw
    rw [e _ hw] at this
    exact this.trans (le_of_eq (by ring))
  obtain ⟨ℓ, hℓ, e⟩ := (h2 w hw).exists_ext
  have n1 := sobNorm_nonneg σ Sa w
  have n2 := sobNorm_nonneg σ Sc w
  have n3 := sobNorm_nonneg σ Sa b
  have n4 := sobNorm_nonneg σ Sc b
  have key := bc ℓ hℓ (Ca * M * sobNorm σ Sa w) (by positivity) (fun g hg => by
    rw [e _ (hc.translate hS.1 hg), norm_star]
    exact step g hg) b hb
  rw [e _ hb, norm_star] at key
  rw [sobNorm_append, sobNorm_append]
  refine key.trans ?_
  calc Cc * (Ca * M * sobNorm σ Sa w) * sobNorm σ Sc b
      = Ca * Cc * M * sobNorm σ Sc b * sobNorm σ Sa w := by ring
    _ ≤ _ := by gcongr <;> linarith

end GlobalTheory.TypeSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCommonGrowthExponentGKDiscreteSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoefBoundTwoFinSum
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum

open GlobalTheory.LowTypeDetermined

section SobSum

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem sobCont_zero_form : Sobolev₂ (lieSet ε) σ (0 : H →ₗ[ℂ] ℂ) :=
  ⟨[], 0, by simp, fun w _ => by simp⟩

theorem sobCont_add_form {ℓ ℓ' : H →ₗ[ℂ] ℂ} (h : Sobolev₂ (lieSet ε) σ ℓ) (h' : Sobolev₂ (lieSet ε) σ ℓ') :
    Sobolev₂ (lieSet ε) σ (ℓ + ℓ') := by
  obtain ⟨S, C, hS, hC⟩ := h
  obtain ⟨S', C', hS', hC'⟩ := h'
  refine ⟨S ++ S', |C| + |C'|, words_append hS hS', fun w hw => ?_⟩
  have n1 := sobNorm_nonneg σ S w
  have n2 := sobNorm_nonneg σ S' w
  have b1 : ‖ℓ w‖ ≤ C * sobNorm σ S w := hC w hw
  have b2 : ‖ℓ' w‖ ≤ C' * sobNorm σ S' w := hC' w hw
  show ‖ℓ w + ℓ' w‖ ≤ (|C| + |C'|) * sobNorm σ (S ++ S') w
  rw [sobNorm_append]
  have a1 : C * sobNorm σ S w ≤ |C| * sobNorm σ S w := mul_le_mul_of_nonneg_right (le_abs_self C) n1
  have a2 : C' * sobNorm σ S' w ≤ |C'| * sobNorm σ S' w := mul_le_mul_of_nonneg_right (le_abs_self C') n2
  have a3 := abs_nonneg C
  have a4 := abs_nonneg C'
  calc ‖ℓ w + ℓ' w‖ ≤ ‖ℓ w‖ + ‖ℓ' w‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith

theorem sobCont_smul_form (c : ℂ) {ℓ : H →ₗ[ℂ] ℂ} (h : Sobolev₂ (lieSet ε) σ ℓ) :
    Sobolev₂ (lieSet ε) σ (c • ℓ) := by
  obtain ⟨S, C, hS, hC⟩ := h
  refine ⟨S, ‖c‖ * C, hS, fun w hw => ?_⟩
  have b : ‖ℓ w‖ ≤ C * sobNorm σ S w := hC w hw
  show ‖c • ℓ w‖ ≤ ‖c‖ * C * sobNorm σ S w
  rw [norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left b (norm_nonneg c)

theorem sobCont_sum_form {ι : Type} (s : Finset ι) (f : ι → H →ₗ[ℂ] ℂ) (h : ∀ i, Sobolev₂ (lieSet ε) σ (f i)) :
    Sobolev₂ (lieSet ε) σ (∑ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using (sobCont_zero_form (ε := ε) (σ := σ) (H := H))
  · intro i s hi ih
    rw [Finset.sum_insert hi]
    exact sobCont_add_form (h i) ih

end SobSum

theorem coefBound_two_finSum : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → CoefBound ε σ → ∀ N : ℕ, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ (p : ℕ) (ℓ : Fin p → (H →ₗ[ℂ] ℂ)) (x : Fin p → H), (∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) → (∀ j, Sm ε σ (x j)) → ∀ M : ℝ, 0 ≤ M → (∀ y ∈ UJset ε, ‖∑ j, ℓ j (σ y (x j))‖ ≤ M * (1 + hs y) ^ N) → ∀ b w, Sm ε σ b → Sm ε σ w → ‖∑ j, ⟪b, x j⟫_ℂ * ℓ j w‖ ≤ C * M * sobNorm σ S b * sobNorm σ S w := by
  intro n ε H _ _ _ σ h hB N
  have hσ := h.1
  obtain ⟨a, c, ha0, hc0, haK, hcK, Z, C₀, hZ, hZU, hC₀, hA⟩ := exists_rank_one_isAvg n ε H σ h
  have ha : Sm ε σ a := h.2.2.1 a haK
  have hc : Sm ε σ c := h.2.2.1 c hcK
  obtain ⟨S, C₁, hS, hC₁, hb2⟩ := coefBound_two n ε H σ h hB a c ha ha0 hc hc0 N
  obtain ⟨K₀, hK₀⟩ := hZ.exists_bound_of_continuousOn
    (f := fun y : Mx n => (1 + hs y) ^ N) ((continuous_const.add continuous_hs).pow N).continuousOn
  set K := max K₀ 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hK : ∀ y ∈ Z, (1 + hs y) ^ N ≤ K := fun y hy =>
    ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hK₀ y hy)).trans (le_max_left _ _)
  refine ⟨S, C₁ * C₀ * K, hS, mul_nonneg (mul_nonneg hC₁ hC₀) hK0, ?_⟩
  intro p ℓ x hℓ hx M hM hgr b w hb hw
  let γ : H → H → ℂ := fun b w => ∑ j, ⟪b, x j⟫_ℂ * ℓ j w
  have h1 : ∀ b, Sm ε σ b → SobFun ε σ (γ b) := by
    intro b _
    have hL := sobCont_sum_form (ε := ε) (σ := σ) Finset.univ (fun j => ⟪b, x j⟫_ℂ • ℓ j)
      (fun j => sobCont_smul_form _ (hℓ j))
    have e : γ b = ⇑(∑ j, ⟪b, x j⟫_ℂ • ℓ j) := by
      funext w
      simp [γ, LinearMap.sum_apply]
    rw [e]
    exact sobFun_of_sobCont hL
  have h2 : ∀ w, Sm ε σ w → SobFun ε σ (fun b => star (γ b w)) := by
    intro w _
    have hL := sobCont_sum_form (ε := ε) (σ := σ) Finset.univ
      (fun j => star (ℓ j w) • (innerSL ℂ (x j) : H →ₗ[ℂ] ℂ)) (fun j => sobCont_smul_form _ (sobCont_inner _))
    have e : (fun b => star (γ b w)) = ⇑(∑ j, star (ℓ j w) • (innerSL ℂ (x j) : H →ₗ[ℂ] ℂ)) := by
      funext b
      simp only [γ, star_sum, LinearMap.sum_apply, LinearMap.smul_apply,
        ContinuousLinearMap.coe_coe, innerSL_apply_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_mul', mul_comm, ← inner_conj_symm, starRingEnd_apply, star_star]
    rw [e]
    exact sobFun_of_sobCont hL
  have h3 : ∀ g ∈ UJset ε, ∀ g' ∈ UJset ε,
      ‖γ (σ g' c) (σ g a)‖ ≤ (C₀ * K * M) * (1 + hs g) ^ N * (1 + hs g') ^ N := by
    intro g hg g' hg'
    have hg'i := inv_mem_UJ hg'
    have hinv : g'⁻¹⁻¹ = g' :=
      Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_UJ hg'))
    have e : γ (σ g' c) (σ g a) =
        ∑ j, (ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) ((fun v => ⟪c, v⟫_ℂ • a) (σ g'⁻¹ (x j))) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have hi := inner_sigma hσ hg'i c (x j)
      rw [hinv] at hi
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, map_smul, smul_eq_mul]
      rw [hi]
    have P0 : 0 ≤ (1 + hs g) ^ N := pow_nonneg (by linarith [hs_nonneg g]) N
    have P1 : 0 ≤ (1 + hs g') ^ N := pow_nonneg (by linarith [hs_nonneg g']) N
    have hbd : ∀ y ∈ Z, ‖∑ j, (ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) (σ y (σ g'⁻¹ (x j)))‖ ≤
        M * K * (1 + hs g) ^ N * (1 + hs g') ^ N := by
      intro y hy
      have hyU := hZU hy
      have hm : g * y * g'⁻¹ ∈ UJset ε := mul_mem_UJ (mul_mem_UJ hg hyU) hg'i
      have e2 : ∀ j, (ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) (σ y (σ g'⁻¹ (x j))) = ℓ j (σ (g * y * g'⁻¹) (x j)) := fun j => by
        simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
        rw [sigma_mul hσ (mul_mem_UJ hg hyU) hg'i, sigma_mul hσ hg hyU]
      simp only [e2]
      refine (hgr _ hm).trans ?_
      have q1 := one_add_hs_mul_le (g * y) g'⁻¹
      have q2 := one_add_hs_mul_le g y
      rw [hs_inv hg'] at q1
      have hy0 := hs_nonneg y
      have hgg := hs_nonneg g
      have hgg' := hs_nonneg g'
      have q : 1 + hs (g * y * g'⁻¹) ≤ (1 + hs g) * (1 + hs y) * (1 + hs g') :=
        q1.trans (mul_le_mul_of_nonneg_right q2 (by linarith))
      have qN : (1 + hs (g * y * g'⁻¹)) ^ N ≤ (1 + hs g) ^ N * (1 + hs y) ^ N * (1 + hs g') ^ N := by
        rw [← mul_pow, ← mul_pow]
        exact pow_le_pow_left₀ (by linarith [hs_nonneg (g * y * g'⁻¹)]) q N
      have hKy := hK y hy
      calc M * (1 + hs (g * y * g'⁻¹)) ^ N ≤ M * ((1 + hs g) ^ N * (1 + hs y) ^ N * (1 + hs g') ^ N) :=
            mul_le_mul_of_nonneg_left qN hM
        _ ≤ M * ((1 + hs g) ^ N * K * (1 + hs g') ^ N) := by gcongr
        _ = _ := by ring
    have key := avgBd_sobCont n ε H σ h (fun v => ⟪c, v⟫_ℂ • a) Z C₀ hZ hZU hC₀ hA (Fin p)
      (fun j => ℓ j ∘ₗ (σ g : H →ₗ[ℂ] H)) (fun j => σ g'⁻¹ (x j))
      (fun j => sobCont_translate hσ (hℓ j) hg) (fun j => (hx j).translate hσ hg'i)
      (fun j => sm_iff.2 ((smooth (Jm ε) σ).smul_mem _ (sm_iff.1 ha)))
      (M * K * (1 + hs g) ^ N * (1 + hs g') ^ N)
      (mul_nonneg (mul_nonneg (mul_nonneg hM hK0) P0) P1) hbd
    rw [e]
    exact key.trans (le_of_eq (by ring))
  have fin := hb2 γ h1 h2 (C₀ * K * M) (mul_nonneg (mul_nonneg hC₀ hK0) hM) h3 b w hb hw
  calc ‖∑ j, ⟪b, x j⟫_ℂ * ℓ j w‖ = ‖γ b w‖ := rfl
    _ ≤ _ := fin
    _ = _ := by ring

end GlobalTheory.TypeSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CaspowExpand
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum

open GlobalTheory.LowTypeDetermined

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem Dw_comb (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)} (hl : ∀ X ∈ l, X ∈ lieSet ε) {v : H}
    (hv : Sm ε σ v) (L : List (ℂ × List (Mx n))) (hL : ∀ u ∈ L, ∀ Y ∈ u.2, Y ∈ lieSet ε) :
    Sm ε σ ((L.map fun u => u.1 • Dw σ u.2 v).sum) ∧
      Dw σ l ((L.map fun u => u.1 • Dw σ u.2 v).sum) = (L.map fun u => u.1 • Dw σ (l ++ u.2) v).sum := by
  induction L with
  | nil =>
    refine ⟨(smooth (Jm ε) σ).zero_mem, ?_⟩
    have h := Dw_smul hσ hl (0 : ℂ) hv
    simpa using h
  | cons u L ih =>
    have hu : Sm ε σ (Dw σ u.2 v) := hv.word hσ (hL u List.mem_cons_self)
    obtain ⟨ih1, ih2⟩ := ih fun w hw => hL w (List.mem_cons_of_mem _ hw)
    have hs : Sm ε σ (u.1 • Dw σ u.2 v) := (smooth (Jm ε) σ).smul_mem u.1 hu
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      exact (smooth (Jm ε) σ).add_mem hs ih1
    · simp only [List.map_cons, List.sum_cons]
      rw [Dw_add hσ hl hs ih1, Dw_smul hσ hl u.1 hu, ← Dw_append, ih2]

theorem sum_neg_comb (L : List (ℂ × List (Mx n))) (f : List (Mx n) → H) :
    (L.map fun u => (-u.1) • f u.2).sum = -(L.map fun u => u.1 • f u.2).sum := by
  induction L with
  | nil => simp
  | cons u L ih =>
    simp only [List.map_cons, List.sum_cons, neg_smul, neg_add] at *
    rw [ih]

theorem sum_norm_neg (L : List (ℂ × List (Mx n))) (f : List (Mx n) → List (Mx n)) :
    ((L.map fun u => ((-u.1, f u.2) : ℂ × List (Mx n))).map fun u => ‖u.1‖).sum = (L.map fun u => ‖u.1‖).sum := by
  simp [List.map_map, Function.comp_def]

theorem sum_flatMap' {α M : Type} [AddCommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun i => (f i).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem caspow_expand : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → ∀ (d : ℕ) (X : Fin d → Mx n), (∀ i, X i ∈ lieSet ε) →
    ∀ r : ℕ, ∃ L : List (ℂ × List (Mx n)), (∀ u ∈ L, u.2.length ≤ 2 * r ∧ ∀ Y ∈ u.2, ∃ i, X i = Y) ∧
      (L.map fun u => ‖u.1‖).sum ≤ (1 + (d : ℝ)) ^ r ∧
      ∀ v, Sm ε σ v → (onePlusCas σ X)^[r] v = (L.map fun u => u.1 • Dw σ u.2 v).sum := by
  intro n ε H _ _ σ hσ d X hX r
  induction r with
  | zero =>
    refine ⟨[(1, [])], ?_, ?_, ?_⟩
    · simp
    · simp
    · intro v _; simp
  | succ r ih =>
    obtain ⟨L, hL1, hL2, hL3⟩ := ih
    have hLie : ∀ u ∈ L, ∀ Y ∈ u.2, Y ∈ lieSet ε := fun u hu Y hY => by
      obtain ⟨i, rfl⟩ := (hL1 u hu).2 Y hY
      exact hX i
    let M : Fin d → List (ℂ × List (Mx n)) := fun i => L.map fun u => (-u.1, X i :: X i :: u.2)
    refine ⟨L ++ (List.finRange d).flatMap M, ?_, ?_, ?_⟩
    · intro u hu
      rcases List.mem_append.1 hu with hu | hu
      · exact ⟨(hL1 u hu).1.trans (by omega), (hL1 u hu).2⟩
      · obtain ⟨i, -, hu⟩ := List.mem_flatMap.1 hu
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
        refine ⟨?_, ?_⟩
        · simp only [List.length_cons]; have := (hL1 w hw).1; omega
        · intro Y hY
          simp only [List.mem_cons] at hY
          rcases hY with rfl | rfl | hY
          · exact ⟨i, rfl⟩
          · exact ⟨i, rfl⟩
          · exact (hL1 w hw).2 Y hY
    · have hM : ∀ i, ((M i).map fun u => ‖u.1‖).sum = (L.map fun u => ‖u.1‖).sum := fun i => sum_norm_neg L (fun l => X i :: X i :: l)
      rw [List.map_append, List.sum_append, List.map_flatMap, sum_flatMap']
      simp only [hM, List.map_const', List.sum_replicate, List.length_finRange, nsmul_eq_mul]
      have h0 : 0 ≤ (L.map fun u => ‖u.1‖).sum := List.sum_nonneg fun x hx => by
        obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
      rw [pow_succ]
      nlinarith [pow_nonneg (by positivity : (0:ℝ) ≤ 1 + d) r]
    · intro v hv
      have hi : ∀ i, dRep σ (X i) (dRep σ (X i) (L.map fun u => u.1 • Dw σ u.2 v).sum) =
          (L.map fun u => u.1 • Dw σ (X i :: X i :: u.2) v).sum := fun i =>
        (Dw_comb hσ (l := [X i, X i]) (by simp [hX i]) hv L hLie).2
      have hMi : ∀ i, ((M i).map fun u => u.1 • Dw σ u.2 v).sum =
          -(L.map fun u => u.1 • Dw σ (X i :: X i :: u.2) v).sum := fun i => by
        rw [← sum_neg_comb L (fun l => Dw σ (X i :: X i :: l) v)]
        simp [M, List.map_map, Function.comp_def]
      rw [Function.iterate_succ_apply', hL3 v hv, onePlusCas]
      simp only [hi]
      rw [List.map_append, List.sum_append, List.map_flatMap, sum_flatMap', ← Fin.sum_univ_def]
      simp only [hMi, Finset.sum_neg_distrib, sub_eq_add_neg]

end GlobalTheory.TypeSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsOrthonormalEigen
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.EigenSpan

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem inK_smul {X : Mx n} (hX : X ∈ lieSet ε) (hXs : Xᴴ = -X) (t : ℝ) : Formalism.REAL.inK ε ((t : ℂ) • X) := by
  have h0 : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have hc : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X := by
    rw [hXs, Matrix.neg_mul] at h0
    exact neg_add_eq_zero.1 h0
  refine ⟨?_, ?_⟩
  · show ((t : ℂ) • X)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * ((t : ℂ) • X) = 0
    rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_assoc, mul_smul_comm, ← smul_add, h0,
      smul_zero]
  · rw [smul_mul_assoc, mul_smul_comm, hc]

theorem exp_mem_K {X : Mx n} (hX : X ∈ lieSet ε) (hXs : Xᴴ = -X) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.REAL.Kset ε := by
  have := (maximal_compact_facts n ε).2.2.2.1 _ (inK_smul hX hXs t)
  rwa [Complex.coe_smul] at this

theorem dRep_mem_of_kStable {X : Mx n} (hX : X ∈ lieSet ε) (hXs : Xᴴ = -X) {F : Submodule ℂ H}
    [FiniteDimensional ℂ F] (hF : IsKStableOn ε σ F) {v : H} (hv : v ∈ F) : dRep σ X v ∈ F := by
  have hc : IsClosed (F : Set H) := F.closed_of_finiteDimensional
  have hm : ∀ t : ℝ, σ (NormedSpace.exp (t • X)) v ∈ F := fun t => hF _ (exp_mem_K hX hXs t) v hv
  unfold dRep
  by_cases hd : DifferentiableAt ℝ (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) 0
  · refine hc.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [slope_def_module]
    exact (F.restrictScalars ℝ).smul_mem _ (F.sub_mem (hm t) (hm 0))
  · rw [deriv_zero_of_not_differentiableAt hd]
    exact F.zero_mem

theorem exists_kStable {p : ℕ} {x : Fin p → H} (hx : ∀ j, IsKFin ε σ (x j)) :
    ∃ F : Submodule ℂ H, FiniteDimensional ℂ F ∧ IsKStableOn ε σ F ∧ ∀ j, x j ∈ F := by
  unfold IsKFin at hx
  choose S hSfin hxS hSst using hx
  haveI : ∀ j, FiniteDimensional ℂ (S j) := hSfin
  refine ⟨⨆ j, S j, inferInstance, fun g hg v hv => ?_, fun j => Submodule.mem_iSup_of_mem j (hxS j)⟩
  refine Submodule.iSup_induction S (motive := fun v => σ g v ∈ ⨆ j, S j) hv
    (fun j v hv => Submodule.mem_iSup_of_mem j (hSst j g hg v hv)) ?_ ?_
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b ha hb; rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb

theorem inner_onePlusCas_self (hσ : IsURepOn (UJset ε) σ) {d : ℕ} {X : Fin d → Mx n} (hX : ∀ i, X i ∈ lieSet ε)
    {v : H} (hv : Sm ε σ v) :
    ⟪v, onePlusCas σ X v⟫_ℂ = ((‖v‖ ^ 2 + ∑ i, ‖dRep σ (X i) v‖ ^ 2 : ℝ) : ℂ) := by
  have h : ∀ i, ⟪v, dRep σ (X i) (dRep σ (X i) v)⟫_ℂ = -⟪dRep σ (X i) v, dRep σ (X i) v⟫_ℂ := fun i =>
    inner_dRep (isUnit_Jm ε) hσ hv (dRep_mem (isUnit_Jm ε) hσ hv (hX i)) (hX i)
  simp only [onePlusCas, inner_sub_right, inner_sum, h, Finset.sum_neg_distrib, sub_neg_eq_add,
    inner_self_eq_norm_sq_to_K]
  norm_cast

theorem exists_orthonormal_eigen : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (d : ℕ) (X : Fin d → Mx n),
    (∀ i, X i ∈ lieSet ε ∧ (X i)ᴴ = -X i) → ∀ (p : ℕ) (x : Fin p → H), (∀ j, IsKFin ε σ (x j)) →
    ∃ (q : ℕ) (e : Fin q → H) (μ : Fin q → ℝ), Orthonormal ℂ e ∧ (∀ i, IsKFin ε σ (e i)) ∧ (∀ i, 1 ≤ μ i) ∧
      (∀ i, onePlusCas σ X (e i) = (μ i : ℂ) • e i) ∧ ∀ j, x j = ∑ i, ⟪e i, x j⟫_ℂ • e i := by
  intro n ε H _ _ _ σ hS d X hX p x hx
  obtain ⟨F, hFfin, hFst, hxF⟩ := exists_kStable hx
  have hσ : IsURepOn (UJset ε) σ := hS.1
  have hXl : ∀ i, X i ∈ lieSet ε := fun i => (hX i).1
  have hKF : ∀ v ∈ F, IsKFin ε σ v := fun v hv => ⟨F, hFfin, hv, hFst⟩
  have hSm : ∀ v ∈ F, Sm ε σ v := fun v hv => hS.2.2.1 v (hKF v hv)
  have hD : ∀ i, ∀ v ∈ F, dRep σ (X i) v ∈ F := fun i v hv => dRep_mem_of_kStable (hX i).1 (hX i).2 hFst hv
  have hT : ∀ v ∈ F, onePlusCas σ X v ∈ F := fun v hv =>
    F.sub_mem hv (F.sum_mem fun i _ => hD i _ (hD i v hv))
  let T : F →ₗ[ℂ] F :=
    { toFun := fun v => ⟨onePlusCas σ X v, hT v v.2⟩
      map_add' := fun a b => Subtype.ext (by
        have h : ∀ i, dRep σ (X i) (dRep σ (X i) ((a : H) + b)) =
            dRep σ (X i) (dRep σ (X i) a) + dRep σ (X i) (dRep σ (X i) b) := fun i =>
          Dw_add hσ (l := [X i, X i]) (by simp [hXl i]) (hSm a a.2) (hSm b b.2)
        show onePlusCas σ X ((a : H) + b) = onePlusCas σ X a + onePlusCas σ X b
        simp only [onePlusCas, h, Finset.sum_add_distrib]
        abel)
      map_smul' := fun c a => Subtype.ext (onePlusCas_smul hσ hXl c (hSm a a.2)) }
  have hTv : ∀ v : F, (T v : H) = onePlusCas σ X v := fun v => rfl
  have hTs : T.IsSymmetric := fun a b => by
    rw [Submodule.coe_inner, Submodule.coe_inner, hTv, hTv]
    exact (inner_onePlusCas hσ hXl (hSm a a.2) (hSm b b.2)).symm
  let E := hTs.eigenvectorBasis (rfl : Module.finrank ℂ F = Module.finrank ℂ F)
  have hE : ∀ i, onePlusCas σ X (E i : H) = (hTs.eigenvalues rfl i : ℂ) • (E i : H) := fun i => by
    rw [← hTv]
    exact congrArg Subtype.val (hTs.apply_eigenvectorBasis rfl i)
  refine ⟨Module.finrank ℂ F, fun i => (E i : H), hTs.eigenvalues rfl, ?_, fun i => hKF _ (E i).2, fun i => ?_, hE,
    fun j => ?_⟩
  · exact E.orthonormal.comp_linearIsometry F.subtypeₗᵢ
  · have h1 := inner_onePlusCas_self hσ hXl (hSm _ (E i).2)
    have hn : ‖(E i : H)‖ = 1 := E.orthonormal.1 i
    rw [hE i, inner_smul_right, inner_self_eq_norm_sq_to_K, hn] at h1
    have h2 : hTs.eigenvalues rfl i = 1 + ∑ k, ‖dRep σ (X k) (E i : H)‖ ^ 2 := by
      simp only [RCLike.ofReal_one, Complex.ofReal_one, one_pow, mul_one] at h1
      exact_mod_cast h1
    rw [h2]
    have : 0 ≤ ∑ k, ‖dRep σ (X k) (E i : H)‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    linarith
  · have h := congrArg Subtype.val (E.sum_repr' ⟨x j, hxF j⟩)
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul, Submodule.coe_inner] at h
    exact h.symm

end GlobalTheory.TypeSum.EigenSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCommonGrowthExponentGKDiscreteSeries
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum.CoefRep

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem norm_sum_list_le {p : ℕ} (ℓ : Fin p → (H →ₗ[ℂ] ℂ)) (x : Fin p → H) (y : Mx n) :
    ∀ L : List (ℂ × List (Mx n)),
      ‖∑ j, ℓ j (σ y ((L.map fun u => u.1 • Dw σ u.2 (x j)).sum))‖ ≤
        (L.map fun u => ‖u.1‖ * ‖∑ j, ℓ j (σ y (Dw σ u.2 (x j)))‖).sum
  | [] => by simp
  | u :: L => by
    simp only [List.map_cons, List.sum_cons, map_add (f := _), map_smul, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq (norm_mul _ _)) (norm_sum_list_le ℓ x y L))

theorem exists_rewrite : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ N : ℕ,
    ∃ S : List (List (Mx n)), Words (lieSet ε) S ∧ ∃ (m : List (List (Mx n)) → ℕ) (A : List (List (Mx n)) → ℝ),
    ∀ (p : ℕ) (ℓ : Fin p → (H →ₗ[ℂ] ℂ)) (x : Fin p → H), (∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) →
    (∀ j, IsKFin ε σ (x j)) → ∀ B : ℕ → ℝ,
    (∀ k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
      ∀ y ∈ UJset ε, ‖∑ j, ℓ j (σ y (Dw σ w (x j)))‖ ≤ B k * (1 + hs y) ^ N) →
    ∃ (q : ℕ) (ℓ' : Fin q → (H →ₗ[ℂ] ℂ)) (x' : Fin q → H) (c : Fin q → ℝ),
      (∀ i, Sm ε σ (x' i)) ∧ (∀ i, 0 ≤ c i) ∧ (∀ i w, Sm ε σ w → ‖ℓ' i w‖ ≤ c i * sobNorm σ S w) ∧
      (∀ S', Words (lieSet ε) S' → ∑ i, c i * sobNorm σ S' (x' i) ≤ A S' * B (m S')) ∧
      ∀ y ∈ UJset ε, ∑ j, ℓ j (σ y (x j)) = ∑ i, ℓ' i (σ y (x' i)) := by
  intro _hHC hCW n ε H _ _ _ σ hstd N
  have hσ := hstd.1
  have hcb : CoefBound ε σ := GlobalTheory.TypeSum.coefBound_of_casselmanWallach hCW n ε H σ hstd
  obtain ⟨S, C, hS, hC, hM2⟩ := GlobalTheory.TypeSum.coefBound_two_finSum n ε H σ hstd hcb N
  obtain ⟨d, X, hX, hL1⟩ := GlobalTheory.TypeSum.TraceBound.trace_bound n ε H σ hstd
  have hL1' : ∀ T : List (List (Mx n)), ∃ (r : ℕ) (A : ℝ), Words (lieSet ε) T → ∀ (q : ℕ) (e : Fin q → H)
      (μ : Fin q → ℝ), Orthonormal ℂ e → (∀ i, IsKFin ε σ (e i)) → (∀ i, 1 ≤ μ i) →
      (∀ i, onePlusCas σ X (e i) = (μ i : ℂ) • e i) → ∑ i, sobNorm σ T (e i) ^ 2 / μ i ^ r ≤ A := by
    intro T
    by_cases hT : Words (lieSet ε) T
    · obtain ⟨r, A, h⟩ := hL1 T hT
      exact ⟨r, A, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hT⟩
  choose r A hrA using hL1'
  have hXl : ∀ i, X i ∈ lieSet ε := fun i => (hX i).1
  refine ⟨S, hS, fun S' => 2 * r (S ++ S'), fun S' => C * (1 + (d : ℝ)) ^ r (S ++ S') * max 0 (A (S ++ S')), ?_⟩
  intro p ℓ x hℓ hx B hB
  have hB0 : ∀ k, 0 ≤ B k := fun k => by
    have h := hB k [] (Nat.zero_le _) (by simp) 1 (one_mem_UJ ε)
    have hp : (0 : ℝ) < (1 + hs (1 : Mx n)) ^ N := pow_pos (by linarith [hs_nonneg (1 : Mx n)]) _
    exact (mul_nonneg_iff_of_pos_right hp).1 ((norm_nonneg _).trans h)
  obtain ⟨q, e, μ, he, heK, hμ, heig, hexp⟩ :=
    GlobalTheory.TypeSum.EigenSpan.exists_orthonormal_eigen n ε H σ hstd d X (fun i => ⟨(hX i).1, (hX i).2.1⟩) p x hx
  have heS : ∀ i, Sm ε σ (e i) := fun i => hstd.2.2.1 _ (heK i)
  have hxS : ∀ j, Sm ε σ (x j) := fun j => hstd.2.2.1 _ (hx j)
  have hμ0 : ∀ i (t : ℕ), 0 < μ i ^ t := fun i t => pow_pos (by linarith [hμ i]) t
  have hd0 : (0 : ℝ) ≤ 1 + (d : ℝ) := by positivity
  have key : ∀ (t : ℕ) (i : Fin q) (w : H), Sm ε σ w →
      ‖∑ j, ⟪e i, x j⟫_ℂ * ℓ j w‖ ≤
        C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) * sobNorm σ S w / μ i ^ t := by
    intro t i w hw
    obtain ⟨L, hL1, hL2, hL3⟩ := GlobalTheory.TypeSum.caspow_expand n ε H σ hσ d X hXl t
    have hxt : ∀ j, Sm ε σ ((onePlusCas σ X)^[t] (x j)) := fun j => sm_iterate_onePlusCas hσ hXl (hxS j) t
    have hM : 0 ≤ (1 + (d : ℝ)) ^ t * B (2 * t) := mul_nonneg (pow_nonneg hd0 _) (hB0 _)
    have hgrow : ∀ y ∈ UJset ε, ‖∑ j, ℓ j (σ y ((onePlusCas σ X)^[t] (x j)))‖ ≤
        (1 + (d : ℝ)) ^ t * B (2 * t) * (1 + hs y) ^ N := by
      intro y hy
      have e1 : ∀ j, (onePlusCas σ X)^[t] (x j) = (L.map fun u => u.1 • Dw σ u.2 (x j)).sum :=
        fun j => hL3 _ (hxS j)
      simp only [e1]
      refine (norm_sum_list_le ℓ x y L).trans ?_
      have hw0 : 0 ≤ B (2 * t) * (1 + hs y) ^ N :=
        mul_nonneg (hB0 _) (pow_nonneg (by linarith [hs_nonneg y]) _)
      calc (L.map fun u => ‖u.1‖ * ‖∑ j, ℓ j (σ y (Dw σ u.2 (x j)))‖).sum
          ≤ (L.map fun u => ‖u.1‖ * (B (2 * t) * (1 + hs y) ^ N)).sum := by
            refine List.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine hB (2 * t) u.2 (hL1 u hu).1 (fun Y hY => ?_) y hy
            obtain ⟨i, rfl⟩ := (hL1 u hu).2 Y hY
            exact hX i
        _ = (L.map fun u => ‖u.1‖).sum * (B (2 * t) * (1 + hs y) ^ N) := List.sum_map_mul_right _ _ _
        _ ≤ (1 + (d : ℝ)) ^ t * (B (2 * t) * (1 + hs y) ^ N) := mul_le_mul_of_nonneg_right hL2 hw0
        _ = _ := by ring
    have h2 := hM2 p ℓ _ hℓ hxt _ hM hgrow (e i) w (heS i) hw
    have e2 : ∀ j, ⟪e i, (onePlusCas σ X)^[t] (x j)⟫_ℂ = ((μ i : ℂ) ^ t) * ⟪e i, x j⟫_ℂ := fun j => by
      rw [inner_iterate_onePlusCas hσ hXl (heS i) (hxS j),
        iterate_onePlusCas_of_eq hσ hXl (heS i) (heig i), inner_smul_left]
      congr 1
      rw [← Complex.ofReal_pow, Complex.conj_ofReal]
    simp only [e2, mul_assoc, ← Finset.mul_sum] at h2
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith [hμ i])] at h2
    rw [le_div_iff₀ (hμ0 i t)]
    have hc := mul_comm (‖∑ j, ⟪e i, x j⟫_ℂ * ℓ j w‖) (μ i ^ t)
    linarith
  have hterm : ∀ (i : Fin q) (t : ℕ), 0 ≤ C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) / μ i ^ t :=
    fun i t => div_nonneg (mul_nonneg (mul_nonneg hC (mul_nonneg (pow_nonneg hd0 _) (hB0 _)))
      (sobNorm_nonneg σ S _)) (hμ0 i t).le
  have hbdd : ∀ i : Fin q, BddBelow (Set.range fun t : ℕ =>
      C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) / μ i ^ t) :=
    fun i => ⟨0, by rintro _ ⟨t, rfl⟩; exact hterm i t⟩
  refine ⟨q, fun i => ∑ j, ⟪e i, x j⟫_ℂ • ℓ j, e,
    fun i => ⨅ t : ℕ, C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) / μ i ^ t,
    heS, fun i => le_ciInf fun t => hterm i t, ?_, ?_, ?_⟩
  · intro i w hw
    have e3 : (∑ j, ⟪e i, x j⟫_ℂ • ℓ j) w = ∑ j, ⟪e i, x j⟫_ℂ * ℓ j w := by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [e3, mul_comm, Real.mul_iInf_of_nonneg (sobNorm_nonneg σ S w)]
    refine le_ciInf fun t => (key t i w hw).trans (le_of_eq ?_)
    ring
  · intro S' hS'
    have hW : Words (lieSet ε) (S ++ S') := words_append hS hS'
    have hA := hrA (S ++ S') hW q e μ he heK hμ heig
    set r₀ := r (S ++ S')
    have hK0 : 0 ≤ C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) :=
      mul_nonneg hC (mul_nonneg (pow_nonneg hd0 _) (hB0 _))
    calc ∑ i, (⨅ t : ℕ, C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) / μ i ^ t) * sobNorm σ S' (e i)
        ≤ ∑ i, C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * sobNorm σ S (e i) / μ i ^ r₀ * sobNorm σ S' (e i) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (ciInf_le (hbdd i) r₀) (sobNorm_nonneg σ S' _)
      _ ≤ ∑ i, C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * (sobNorm σ (S ++ S') (e i) ^ 2 / μ i ^ r₀) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have a0 := sobNorm_nonneg σ S (e i)
          have b0 := sobNorm_nonneg σ S' (e i)
          have hab : sobNorm σ S (e i) * sobNorm σ S' (e i) ≤ sobNorm σ (S ++ S') (e i) ^ 2 := by
            rw [sobNorm_append]; nlinarith
          have hm := hμ0 i r₀
          calc C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * sobNorm σ S (e i) / μ i ^ r₀ * sobNorm σ S' (e i)
              = C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * (sobNorm σ S (e i) * sobNorm σ S' (e i) / μ i ^ r₀) := by
                ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hab hm.le) hK0
      _ = C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * ∑ i, sobNorm σ (S ++ S') (e i) ^ 2 / μ i ^ r₀ := by
          rw [Finset.mul_sum]
      _ ≤ C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * max 0 (A (S ++ S')) :=
          mul_le_mul_of_nonneg_left (hA.trans (le_max_right _ _)) hK0
      _ = C * (1 + (d : ℝ)) ^ r (S ++ S') * max 0 (A (S ++ S')) * B (2 * r (S ++ S')) := by ring
  · intro y _
    have h1 : ∀ j, ℓ j (σ y (x j)) = ∑ i, ⟪e i, x j⟫_ℂ * ℓ j (σ y (e i)) := fun j => by
      conv_lhs => rw [hexp j]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul]
    simp only [h1, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    exact Finset.sum_comm

end GlobalTheory.TypeSum.CoefRep

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCommonGrowthExponentGKDiscreteSeriesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_growth_exponent_gK_discreteSeries : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ N : ℕ,
    ∃ S : List (List (Mx n)), Words (lieSet ε) S ∧ ∃ (m : List (List (Mx n)) → ℕ) (A : List (List (Mx n)) → ℝ),
    ∀ (p : ℕ) (ℓ : Fin p → (H →ₗ[ℂ] ℂ)) (x : Fin p → H), (∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) →
    (∀ j, IsKFin ε σ (x j)) → ∀ B : ℕ → ℝ,
    (∀ k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
      ∀ y ∈ UJset ε, ‖∑ j, ℓ j (σ y (Dw σ w (x j)))‖ ≤ B k * (1 + hs y) ^ N) →
    ∃ (q : ℕ) (ℓ' : Fin q → (H →ₗ[ℂ] ℂ)) (x' : Fin q → H) (c : Fin q → ℝ),
      (∀ i, Sm ε σ (x' i)) ∧ (∀ i, 0 ≤ c i) ∧ (∀ i w, Sm ε σ w → ‖ℓ' i w‖ ≤ c i * sobNorm σ S w) ∧
      (∀ S', Words (lieSet ε) S' → ∑ i, c i * sobNorm σ S' (x' i) ≤ A S' * B (m S')) ∧
      ∀ y ∈ UJset ε, ∑ j, ℓ j (σ y (x j)) = ∑ i, ℓ' i (σ y (x' i)) := by
  first | exact @GlobalTheory.TypeSum.CoefRep.exists_rewrite | exact GlobalTheory.TypeSum.CoefRep.exists_rewrite | (intros; apply GlobalTheory.TypeSum.CoefRep.exists_rewrite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesCoeffSeriesOfKTypeProjections
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TypeSum.KSeries

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem coef_eq_fam (h : Std ε σ) {p : ℕ} {ℓ : Fin p → (H →ₗ[ℂ] ℂ)} {x : Fin p → H}
    (hℓ : ∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) (hx : ∀ j, Sm ε σ (x j)) {Φ : List (Mx n) → Mx n → ℂ}
    (h0 : ∀ y ∈ UJset ε, Φ [] y = ∑ j, ℓ j (σ y (x j)))
    (hd : ∀ (l : List (Mx n)), (∀ Y ∈ l, Y ∈ lieSet ε ∧ Yᴴ = -Y) → ∀ X : Mx n, X ∈ lieSet ε → Xᴴ = -X →
      ∀ y ∈ UJset ε, HasDerivAt (fun t : ℝ => Φ l (y * NormedSpace.exp (t • X))) (Φ (X :: l) y) 0) :
    ∀ w : List (Mx n), (∀ Y ∈ w, Y ∈ lieSet ε ∧ Yᴴ = -Y) → ∀ y ∈ UJset ε,
      Φ w y = ∑ j, ℓ j (σ y (Dw σ w (x j))) := by
  intro w
  induction w with
  | nil => intro _ y hy; simpa [Dw] using h0 y hy
  | cons X l ih =>
    intro hw y hy
    have hX := hw X List.mem_cons_self
    have hl : ∀ Y ∈ l, Y ∈ lieSet ε ∧ Yᴴ = -Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    have hlL : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => (hl Y hY).1
    have d1 := hd l hl X hX.1 hX.2 y hy
    have d2 : HasDerivAt (fun t : ℝ => ∑ j, ℓ j (σ (y * NormedSpace.exp (t • X)) (Dw σ l (x j))))
        (∑ j, ℓ j (σ (y * NormedSpace.exp ((0 : ℝ) • X)) (dRep σ X (Dw σ l (x j))))) 0 :=
      HasDerivAt.fun_sum (u := Finset.univ) fun j _ => GlobalTheory.TypeSum.CoefLow.hasDerivAt_coef h (hℓ j) ((hx j).word h.1 hlL) hX.1 hy 0
    have e : (fun t : ℝ => Φ l (y * NormedSpace.exp (t • X))) =
        fun t => ∑ j, ℓ j (σ (y * NormedSpace.exp (t • X)) (Dw σ l (x j))) := by
      funext t; exact ih hl _ (mul_mem_UJ hy (exp_mem_UJ hX.1 t))
    rw [e] at d1
    rw [d1.unique d2]
    simp [Dw]

end GlobalTheory.TypeSum.KSeries

namespace GlobalTheory.TypeSum.KSeries

def pad {α : Type} [Zero α] (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → α) : ℕ × ℕ → α :=
  fun p => if h : p.2 < q p.1 then a p.1 ⟨p.2, h⟩ else 0

theorem pad_of_lt {α : Type} [Zero α] (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → α) {i r : ℕ} (h : r < q i) :
    pad q a (i, r) = a i ⟨r, h⟩ := dif_pos h

theorem pad_of_ge {α : Type} [Zero α] (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → α) {i r : ℕ} (h : ¬ r < q i) :
    pad q a (i, r) = 0 := dif_neg h

theorem pad_hasSum_fiber {α : Type} [AddCommMonoid α] [TopologicalSpace α] (q : ℕ → ℕ)
    (a : (i : ℕ) → Fin (q i) → α) (i : ℕ) : HasSum (fun r => pad q a (i, r)) (∑ r, a i r) := by
  have h1 := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) (s := Finset.range (q i))
    (f := fun r => pad q a (i, r)) (fun r hr => pad_of_ge q a fun h => hr (Finset.mem_range.2 h))
  convert h1 using 1
  rw [Finset.sum_range]
  exact Finset.sum_congr rfl fun r _ => (pad_of_lt q a r.isLt).symm

theorem pad_summable (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → ℝ) (ha : ∀ i r, 0 ≤ a i r) (b : ℕ → ℝ)
    (hb : Summable b) (hle : ∀ i, ∑ r, a i r ≤ b i) : Summable (pad q a) := by
  have nn : 0 ≤ pad q a := fun p => by
    simp only [pad, Pi.zero_apply]; split_ifs
    · exact ha _ _
    · exact le_rfl
  rw [summable_prod_of_nonneg nn]
  refine ⟨fun i => (pad_hasSum_fiber q a i).summable, ?_⟩
  refine Summable.of_nonneg_of_le (fun i => tsum_nonneg fun r => nn _) (fun i => ?_) hb
  rw [(pad_hasSum_fiber q a i).tsum_eq]
  exact hle i

theorem pad_hasSum (q : ℕ → ℕ) (a : (i : ℕ) → Fin (q i) → ℂ) (hs : Summable fun p => ‖pad q a p‖) {F : ℂ}
    (hF : HasSum (fun i => ∑ r, a i r) F) : HasSum (pad q a) F := by
  have hs' : Summable (pad q a) := hs.of_norm
  have h3 : ∑' p, pad q a p = F := (hs'.hasSum.prod_fiberwise (pad_hasSum_fiber q a)).unique hF
  rw [← h3]
  exact hs'.hasSum

end GlobalTheory.TypeSum.KSeries

namespace GlobalTheory.TypeSum.KSeries

set_option maxHeartbeats 1000000 in
theorem hasTypeAll_of_kTypes : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ f : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    (∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun ε e →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (x : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, IsKFin ε σ (x j)) ∧
        ∀ y ∈ UJset ε, (∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) = ∑ j, ℓ j (σ y (x j))) →
    GlobalTheory.TypeSum.HasTypeAll (GlobalTheory.SmoothGlob.lieSet ε) (UJset ε) σ f := by
  intro hHC hCW n ε H _ _ _ σ hσ f hf hU hyp
  obtain ⟨e, he1, he2, hP⟩ := GlobalTheory.T.exists_rightKFourierSeries_unitary_moderateGrowth n ε
  obtain ⟨N, Φ, B, hΦ0, hΦd, hΦb, hBs, hsum⟩ := hP f hf hU
  obtain ⟨S, hS, m, A, hQ⟩ := GlobalTheory.T.exists_common_growth_exponent_gK_discreteSeries hHC hCW n ε H σ hσ N
  choose p ℓ x hℓ hx heq using fun i => hyp (e i) (he1 i) (he2 i)
  have hbound : ∀ i k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
      ∀ y ∈ UJset ε, ‖∑ j, ℓ i j (σ y (Dw σ w (x i j)))‖ ≤ B i k * (1 + hs y) ^ N := by
    intro i k w hk hw y hy
    rw [← coef_eq_fam hσ (hℓ i) (fun j => hσ.2.2.1 _ (hx i j)) (fun y hy => (hΦ0 i y hy).trans (heq i y hy))
      (hΦd i) w (fun Y hY => ⟨(hw Y hY).1, (hw Y hY).2.1⟩) y hy]
    exact hΦb i k w hk hw y hy
  choose q ℓ' x' c hx' hc hℓ' hsumS heq' using fun i => hQ (p i) (ℓ i) (x i) (hℓ i) (hx i) (B i) (hbound i)
  obtain ⟨S₁, hS₁, -, ⟨Bc, hBc, hctrl⟩, A₀, hA₀, hdom⟩ := GlobalTheory.TypeSumCtrl.exists_ctrl n ε H σ hσ S hS
  have hV : ∀ a, Sm ε σ (pad q x' a) := fun a => by
    simp only [pad]; split_ifs
    · exact hx' _ _
    · exact sm_iff.2 (Submodule.zero_mem _)
  have key : ∀ S', Words (lieSet ε) S' →
      Summable (fun a : ℕ × ℕ => pad q (fun i r => A₀ * c i r) a * sobNorm σ S' (pad q x' a)) := by
    intro S' hS'
    have e1 : (fun a : ℕ × ℕ => pad q (fun i r => A₀ * c i r) a * sobNorm σ S' (pad q x' a)) =
        pad q (fun i r => A₀ * c i r * sobNorm σ S' (x' i r)) := by
      funext a; simp only [pad]; split_ifs <;> simp
    rw [e1]
    refine pad_summable q _ (fun i r => mul_nonneg (mul_nonneg hA₀ (hc i r)) (sobNorm_nonneg _ _ _))
      (fun i => A₀ * A S' * B i (m S')) ((hBs (m S')).mul_left (A₀ * A S')) fun i => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hsumS i S' hS') hA₀
  have hnorm : ∀ g ∈ UJset ε, ∀ a, ‖pad q (fun i r => ℓ' i r (σ g (x' i r))) a‖ ≤
      Bc g * (pad q (fun i r => A₀ * c i r) a * sobNorm σ S₁ (pad q x' a)) := by
    intro g hg a
    simp only [pad]
    split_ifs with h
    · have hs1 := (hx' a.1 ⟨a.2, h⟩).translate hσ.1 hg
      calc ‖ℓ' a.1 ⟨a.2, h⟩ (σ g (x' a.1 ⟨a.2, h⟩))‖
          ≤ c a.1 ⟨a.2, h⟩ * sobNorm σ S (σ g (x' a.1 ⟨a.2, h⟩)) := hℓ' _ _ _ hs1
        _ ≤ c a.1 ⟨a.2, h⟩ * (A₀ * sobNorm σ S₁ (σ g (x' a.1 ⟨a.2, h⟩))) :=
          mul_le_mul_of_nonneg_left (hdom _ hs1) (hc _ _)
        _ ≤ c a.1 ⟨a.2, h⟩ * (A₀ * (Bc g * sobNorm σ S₁ (x' a.1 ⟨a.2, h⟩))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hctrl g hg _ (hx' _ _)) hA₀) (hc _ _)
        _ = Bc g * (A₀ * c a.1 ⟨a.2, h⟩ * sobNorm σ S₁ (x' a.1 ⟨a.2, h⟩)) := by ring
    · simp
  have hterm : ∀ g a, pad q ℓ' a (σ g (pad q x' a)) = pad q (fun i r => ℓ' i r (σ g (x' i r))) a := by
    intro g a; simp only [pad]; split_ifs <;> simp
  have hsum2 : ∀ g ∈ UJset ε, HasSum (fun a : ℕ × ℕ => pad q ℓ' a (σ g (pad q x' a))) (f g) := by
    intro g hg
    simp only [hterm]
    refine pad_hasSum q _ (Summable.of_nonneg_of_le (fun a => norm_nonneg _) (hnorm g hg)
      ((key S₁ hS₁).mul_left (Bc g))) ?_
    refine (hsum g hg).congr_fun fun i => ?_
    rw [heq i g hg, heq' i g hg]
  refine ⟨S₁, hS₁, ⟨Bc, hBc, hctrl⟩, pad q x' ∘ Nat.pairEquiv.symm, pad q ℓ' ∘ Nat.pairEquiv.symm,
    pad q (fun i r => A₀ * c i r) ∘ Nat.pairEquiv.symm, ⟨⟨fun k => hV _, fun k => ?_, fun k w hw => ?_, ?_, fun g hg => ?_⟩, fun S' hS' => ?_⟩⟩
  · show 0 ≤ pad q (fun i r => A₀ * c i r) (Nat.pairEquiv.symm k)
    simp only [pad]; split_ifs
    · exact mul_nonneg hA₀ (hc _ _)
    · exact le_rfl
  · show ‖pad q ℓ' (Nat.pairEquiv.symm k) w‖ ≤ pad q (fun i r => A₀ * c i r) (Nat.pairEquiv.symm k) * sobNorm σ S₁ w
    simp only [pad]; split_ifs with h
    · calc ‖ℓ' _ _ w‖ ≤ c _ ⟨_, h⟩ * sobNorm σ S w := hℓ' _ _ _ hw
        _ ≤ c _ ⟨_, h⟩ * (A₀ * sobNorm σ S₁ w) := mul_le_mul_of_nonneg_left (hdom _ hw) (hc _ _)
        _ = A₀ * c _ ⟨_, h⟩ * sobNorm σ S₁ w := by ring
    · simp
  · exact (Nat.pairEquiv.symm.summable_iff (f := fun a : ℕ × ℕ => pad q (fun i r => A₀ * c i r) a * sobNorm σ S₁ (pad q x' a))).2 (key S₁ hS₁)
  · exact (Nat.pairEquiv.symm.hasSum_iff (f := fun a : ℕ × ℕ => pad q ℓ' a (σ g (pad q x' a)))).2 (hsum2 g hg)
  · exact (Nat.pairEquiv.symm.summable_iff (f := fun a : ℕ × ℕ => pad q (fun i r => A₀ * c i r) a * sobNorm σ S' (pad q x' a))).2 (key S' hS')

end GlobalTheory.TypeSum.KSeries
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesCoeffSeriesOfKTypeProjectionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeriesCoeffSeries_of_kTypeProjections : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.TypeSum.Mx n → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ →
    ∀ f : GlobalTheory.TypeSum.Mx n → ℂ, ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    (∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun ε e →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (x : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, IsKFin ε σ (x j)) ∧
        ∀ y ∈ UJset ε, (∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) = ∑ j, ℓ j (σ y (x j))) →
    GlobalTheory.TypeSum.HasTypeAll (GlobalTheory.SmoothGlob.lieSet ε) (UJset ε) σ f := by
  first | exact @GlobalTheory.TypeSum.KSeries.hasTypeAll_of_kTypes | exact GlobalTheory.TypeSum.KSeries.hasTypeAll_of_kTypes | (intros; apply GlobalTheory.TypeSum.KSeries.hasTypeAll_of_kTypes <;> assumption)
end
