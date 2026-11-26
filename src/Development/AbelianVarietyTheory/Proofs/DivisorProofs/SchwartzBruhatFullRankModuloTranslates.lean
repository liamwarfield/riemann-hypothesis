module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturality
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Formalism.PairingDivisors.StatementA
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoChainsCechOfIsLocallySurjectiveStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFullRankModuloTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMinorSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMinorSupport
open GlobalTheory.WeilM Matrix

namespace GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.LocMod.Inhab ValuativeRel

theorem exists_mem_nsp_eq_of_rank_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] [Nonempty T] (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) → ∀ (τ : R → D), ∀ f ∈ SB (Matrix (R ⊕ T) D k), (∀ Y : Matrix (R ⊕ T) D k, f Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) → ∃ Φ ∈ GlobalTheory.RankStrata.Nsp k (R ⊕ T) D ν, ∀ Y : Matrix (R ⊕ T) D k, Y.rank ≤ Fintype.card R → Φ Y = f Y := by
  intro k _ _ _ _ R T D _ _ _ _ _ _ _ ν ϖ hϖ hν τ f hf hsupp
  classical
  obtain ⟨a, ha⟩ := GlobalTheory.T.rank_chart_bounded_coefficients k R T D τ f hf hsupp
  obtain ⟨b, hb⟩ := GlobalTheory.T.rank_chart_shear_invariance k R T D f hf
  have hv0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have hv1 : valuation k (ϖ : k) ≤ 1 := hϖ ▸ uniformizer_lt_one.le
  have hva : ∀ x : k, (valuation k (x : k) ≤ valuation k (((ϖ⁻¹ * a : kˣ)) : k) ↔
      valuation k ((ϖ : k) * x) ≤ valuation k (a : k)) := by
    intro x
    rw [Units.val_mul, map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, le_inv_mul_iff₀ hv0]
  have hHH' : box T R a ≤ box T R (ϖ⁻¹ * a) := by
    intro C hC r q
    rw [hva, map_mul]
    exact (mul_le_of_le_one_left' hv1).trans (hC r q)
  have hdilmem : ∀ C : Matrix T R k, ((ϖ : k) • C ∈ box T R a ↔ C ∈ box T R (ϖ⁻¹ * a)) := fun C =>
    forall_congr' fun r => forall_congr' fun q => by rw [hva]; rfl
  generalize hH : box T R a = H at ha hHH' hdilmem
  generalize hH' : box T R (ϖ⁻¹ * a) = H' at hHH' hdilmem
  generalize hL : box T R b = L at hb
  haveI : Finite (H ⧸ L.addSubgroupOf H) := hH ▸ hL ▸ finite_box (Y := T) (Y' := R) (k := k) a b
  haveI : Finite (H' ⧸ H.addSubgroupOf H') := hH ▸ hH' ▸ finite_box (Y := T) (Y' := R) (k := k) (ϖ⁻¹ * a) a
  letI : Fintype (H ⧸ L.addSubgroupOf H) := Fintype.ofFinite _
  letI : Fintype (H' ⧸ H.addSubgroupOf H') := Fintype.ofFinite _

  have hinvL : ∀ (Y₁ : Matrix R D k) (C C' : Matrix T R k), C' - C ∈ L →
      f (stack Y₁ C') = f (stack Y₁ C) := by
    intro Y₁ C C' h
    have := hb (stack Y₁ C) (C' - C) h
    rwa [shear_stack, add_sub_cancel] at this
  obtain ⟨Ψ₁, hΨ₁, hSB⟩ : ∃ Ψ₁ : Matrix (R ⊕ T) D k → ℂ,
      (∀ Y, Ψ₁ Y = ∑ q : H ⧸ L.addSubgroupOf H, f (shear ((q.out : H) : Matrix T R k) Y)) ∧
      Ψ₁ ∈ SB (Matrix (R ⊕ T) D k) :=
    ⟨∑ q : H ⧸ L.addSubgroupOf H, omB ν ν (shearGL ((q.out : H) : Matrix T R k)) 1 f,
      fun Y => by simp [Finset.sum_apply, omB_shearGL],
      Submodule.sum_mem _ fun q _ => omB_mem_SB ν ν _ _ hf⟩
  have hzero : ∀ Y : Matrix (R ⊕ T) D k, (Y.submatrix Sum.inl τ).det = 0 → Ψ₁ Y = 0 := by
    intro Y hY
    rw [hΨ₁]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_contra h
    exact hsupp _ h (by rwa [submatrix_inl_eq, toRows₁_shear, ← submatrix_inl_eq])
  have hA1 : ∀ (Y₁ : Matrix R D k) (C : Matrix T R k),
      Ψ₁ (stack Y₁ C) = if C ∈ H then Ψ₁ (stack Y₁ 0) else 0 := by
    intro Y₁ C
    have h := sum_shift_out (fun C => f (stack Y₁ C)) H L (fun x y h => hinvL Y₁ x y h) (ha Y₁) C
    simp only [hΨ₁, shear_stack, zero_add]
    exact h
  have hA2 : ∀ (Y₁ : Matrix R D k) (C : Matrix T R k),
      ∑ q' : H' ⧸ H.addSubgroupOf H', Ψ₁ (stack Y₁ (C + ((q'.out : H') : Matrix T R k))) =
        if C ∈ H' then Ψ₁ (stack Y₁ 0) else 0 := by
    intro Y₁ C
    rw [Finset.sum_congr rfl fun q' _ => hA1 Y₁ _]
    exact sum_ite_out H H' hHH' _ C

  obtain ⟨lam, hlam⟩ : ∃ lam : ℂ, lam = (ν ϖ : ℂ) ^ Fintype.card T * apow (ϖ ^ Fintype.card T) ((Fintype.card D : ℂ) / 2) :=
    ⟨_, rfl⟩
  obtain ⟨n₁, hn₁, hexp⟩ : ∃ n₁ ∈ GlobalTheory.RankStrata.Nsp k (R ⊕ T) D ν, ∀ Y, n₁ Y = Ψ₁ Y - lam * Ψ₁ (dil (ϖ : k) Y) +
      lam * (∑ q' : H' ⧸ H.addSubgroupOf H', Ψ₁ (shear ((q'.out : H') : Matrix T R k) Y) -
        (Fintype.card (H' ⧸ H.addSubgroupOf H') : ℂ) * Ψ₁ Y) := by
    refine ⟨(Ψ₁ - omB ν ν (dilGL ϖ : GL (R ⊕ T) k) 1 Ψ₁) +
      lam • ∑ q' : H' ⧸ H.addSubgroupOf H', (omB ν ν (shearGL ((q'.out : H') : Matrix T R k)) 1 Ψ₁ - Ψ₁), ?_, ?_⟩
    · refine add_mem ?_ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q' _ =>
        GlobalTheory.RankStrata.sub_mem_Nsp ν _ hSB))
      rw [← neg_sub]
      exact Submodule.neg_mem _ (GlobalTheory.RankStrata.sub_mem_Nsp ν _ hSB)
    · intro Y
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, omB_dilGL,
        omB_shearGL, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hlam,
        Pi.mul_apply, Pi.natCast_apply]
  have hn₁val : ∀ Y : Matrix (R ⊕ T) D k, Y.rank ≤ Fintype.card R →
      n₁ Y = (1 - lam * Fintype.card (H' ⧸ H.addSubgroupOf H')) * Ψ₁ Y := by
    intro Y hY
    rw [hexp]
    by_cases hd : (Y.submatrix Sum.inl τ).det = 0
    · rw [hzero Y hd, hzero _ (by rwa [submatrix_inl_eq, toRows₁_dil, ← submatrix_inl_eq]),
        Finset.sum_eq_zero fun q' _ => hzero _ (by rwa [submatrix_inl_eq, toRows₁_shear, ← submatrix_inl_eq])]
      ring
    · obtain ⟨C, hC⟩ := GlobalTheory.T.rank_chart_stack_decomposition k R T D τ Y hY hd
      rw [hC, dil_stack]
      simp only [shear_stack]
      rw [hA2, hA1 _ ((ϖ : k) • C), hdilmem]
      ring

  obtain ⟨n₀, hn₀, hn₀val⟩ : ∃ n₀ ∈ GlobalTheory.RankStrata.Nsp k (R ⊕ T) D ν,
      ∀ Y, n₀ Y = Ψ₁ Y - (Fintype.card (H ⧸ L.addSubgroupOf H) : ℂ) * f Y := by
    refine ⟨∑ q : H ⧸ L.addSubgroupOf H, (omB ν ν (shearGL ((q.out : H) : Matrix T R k)) 1 f - f),
      Submodule.sum_mem _ fun q _ => GlobalTheory.RankStrata.sub_mem_Nsp ν _ hf, fun Y => ?_⟩
    simp only [hΨ₁, Finset.sum_apply, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, omB_shearGL]

  have hQ : (Fintype.card (H ⧸ L.addSubgroupOf H) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hlamne : 1 - lam * (Fintype.card (H' ⧸ H.addSubgroupOf H') : ℂ) ≠ 0 := by
    obtain ⟨r, hr, hr'⟩ := exists_apow_eq (ϖ ^ Fintype.card T) (Fintype.card D)
    have hc : (0 : ℝ) < r * Fintype.card (H' ⧸ H.addSubgroupOf H') :=
      mul_pos hr (Nat.cast_pos.2 Fintype.card_pos)
    intro h
    refine hν (Fintype.card T) Fintype.card_pos (r * Fintype.card (H' ⧸ H.addSubgroupOf H'))⁻¹ ?_
    have h1 : (ν ϖ : ℂ) ^ Fintype.card T * ((r * Fintype.card (H' ⧸ H.addSubgroupOf H') : ℝ) : ℂ) = 1 := by
      rw [hlam, hr'] at h
      push_cast
      linear_combination -h
    rw [eq_inv_of_mul_eq_one_left h1, Complex.ofReal_inv]
  refine ⟨(Fintype.card (H ⧸ L.addSubgroupOf H) : ℂ)⁻¹ •
      ((1 - lam * Fintype.card (H' ⧸ H.addSubgroupOf H'))⁻¹ • n₁ - n₀),
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hn₁) hn₀), fun Y hY => ?_⟩
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hn₁val Y hY, hn₀val]
  field_simp
  ring

end GlobalTheory.RankChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMinorSupportStatement
open GlobalTheory.WeilM Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_minor_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] [Nonempty T] (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) → ∀ (τ : R → D), ∀ f ∈ SB (Matrix (R ⊕ T) D k), (∀ Y : Matrix (R ⊕ T) D k, f Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) → ∃ Φ ∈ GlobalTheory.RankStrata.Nsp k (R ⊕ T) D ν, ∀ Y : Matrix (R ⊕ T) D k, Y.rank ≤ Fintype.card R → Φ Y = f Y := by
  first | exact @GlobalTheory.RankChart.exists_mem_nsp_eq_of_rank_le | exact GlobalTheory.RankChart.exists_mem_nsp_eq_of_rank_le | (intros; apply GlobalTheory.RankChart.exists_mem_nsp_eq_of_rank_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFullRankModuloTranslates
open GlobalTheory.WeilM Matrix

noncomputable section
namespace GlobalTheory.RankStrata

theorem exists_fullRank_sub_mem_span : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) →
    ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ Ψ₀ ∈ SB (Matrix (Fin n) (Fin d) k), (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≠ n → Ψ₀ Y = 0) ∧
      Ψ - Ψ₀ ∈ Submodule.span ℂ {Z | ∃ g : GL (Fin n) k, ∃ Ψ' ∈ SB (Matrix (Fin n) (Fin d) k), Z = GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ'} := by
  intro k _ _ _ _ n d ν ϖ hϖ hν Ψ hΨ
  classical
  have piece : ∀ ρ < n, ∀ f : Matrix (Fin n) (Fin d) k → ℂ, f ∈ SB (Matrix (Fin n) (Fin d) k) →
      ∀ (S : Fin ρ → Fin n) (τ : Fin ρ → Fin d), (∀ Y, f Y ≠ 0 → (Y.submatrix S τ).det ≠ 0) →
      ∃ Φ ∈ Nsp k (Fin n) (Fin d) ν, ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≤ ρ → Φ Y = f Y := by
    intro ρ hρ f hf S τ hS
    by_cases h0 : ∀ Y, f Y = 0
    · exact ⟨0, Submodule.zero_mem _, fun Y _ => by simp [h0 Y]⟩
    push_neg at h0
    obtain ⟨Y0, hY0⟩ := h0
    have hinj : Function.Injective S := by
      intro i j hij
      by_contra hne
      exact hS Y0 hY0 (Matrix.det_zero_of_row_eq hne (by ext l; simp [hij]))
    let e' : Fin ρ ⊕ ↥(Set.range S)ᶜ ≃ Fin n :=
      (Equiv.sumCongr (Equiv.ofInjective S hinj) (Equiv.refl _)).trans (Equiv.Set.sumCompl _)
    have he' : ∀ i, e'.symm (S i) = Sum.inl i := fun i => by
      rw [Equiv.symm_apply_eq]; simp [e']
    haveI : Nonempty ↥(Set.range S)ᶜ := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have := Fintype.card_congr e'
      simp at this
      omega
    have hT := GlobalTheory.T.schwartzBruhat_reindex_rows k (Fin ρ ⊕ ↥(Set.range S)ᶜ) (Fin n) (Fin d) ν e'
    obtain ⟨Φ', hΦ', hΦ'f⟩ := GlobalTheory.T.schwartzBruhat_minor_support k (Fin ρ) (↥(Set.range S)ᶜ) (Fin d) ν ϖ hϖ hν τ
      (fun Z => f (Z.submatrix e'.symm id)) (hT.1 f hf) (fun Z hZ => by
        have := hS _ hZ
        rwa [Matrix.submatrix_submatrix, show (e'.symm ∘ S) = Sum.inl from funext he'] at this)
    have hT2 := GlobalTheory.T.schwartzBruhat_reindex_rows k (Fin n) (Fin ρ ⊕ ↥(Set.range S)ᶜ) (Fin d) ν e'.symm
    refine ⟨_, hT2.2 Φ' hΦ', fun Y hY => ?_⟩
    simp only [Equiv.symm_symm]
    rw [hΦ'f _ (by rw [show (id : Fin d → Fin d) = ⇑(Equiv.refl (Fin d)) from rfl, Matrix.rank_submatrix]; simpa using hY)]
    simp [Matrix.submatrix_submatrix]
  have step : ∀ ρ < n, ∀ g ∈ SB (Matrix (Fin n) (Fin d) k),
      (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank < ρ → g Y = 0) →
      ∃ Φ ∈ Nsp k (Fin n) (Fin d) ν, ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≤ ρ → Φ Y = g Y := by
    intro ρ hρ g hg hg0
    haveI : T2Space k := by
      letI := IsTopologicalAddGroup.rightUniformSpace k
      haveI := isUniformAddGroup_of_addCommGroup (G := k)
      infer_instance
    have hsp := GlobalTheory.T.schwartzBruhat_partition_of_unity k (Fin n) (Fin d) ((Fin ρ → Fin n) × (Fin ρ → Fin d))
      (fun i => {Y : Matrix (Fin n) (Fin d) k | (Y.submatrix i.1 i.2).det ≠ 0})
      (fun i => isOpen_ne_fun ((continuous_id.matrix_submatrix i.1 i.2).matrix_det) continuous_const) g hg
      (fun Y hY => by
        have : ρ ≤ Y.rank := by
          by_contra h
          exact hY (hg0 Y (by omega))
        obtain ⟨S, τ, h⟩ := GlobalTheory.T.exists_nonzero_minor_of_rank k _ _ ρ Y this
        exact ⟨(S, τ), h⟩)
    refine Submodule.span_induction
      (p := fun g _ => ∃ Φ ∈ Nsp k (Fin n) (Fin d) ν, ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≤ ρ → Φ Y = g Y)
      ?_ ?_ ?_ ?_ hsp
    · rintro f ⟨hf, i, hi⟩
      exact piece ρ hρ f hf i.1 i.2 hi
    · exact ⟨0, Submodule.zero_mem _, fun _ _ => rfl⟩
    · rintro x y _ _ ⟨Φ, hΦ, h⟩ ⟨Φ', hΦ', h'⟩
      exact ⟨Φ + Φ', Submodule.add_mem _ hΦ hΦ', fun Y hY => by simp [h Y hY, h' Y hY]⟩
    · rintro c x _ ⟨Φ, hΦ, h⟩
      exact ⟨c • Φ, Submodule.smul_mem _ c hΦ, fun Y hY => by simp [h Y hY]⟩
  have ind : ∀ ρ ≤ n, ∃ Ψρ ∈ SB (Matrix (Fin n) (Fin d) k),
      (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank < ρ → Ψρ Y = 0) ∧ Ψ - Ψρ ∈ Nsp k (Fin n) (Fin d) ν := by
    intro ρ
    induction ρ with
    | zero => intro _; exact ⟨Ψ, hΨ, fun Y h => absurd h (Nat.not_lt_zero _), by simp⟩
    | succ ρ ih =>
      intro hρ
      obtain ⟨Ψρ, hSB, h0, hN⟩ := ih (by omega)
      obtain ⟨Φ, hΦ, hΦe⟩ := step ρ (by omega) Ψρ hSB h0
      refine ⟨Ψρ - Φ, Submodule.sub_mem _ hSB (Nsp_le_SB _ _ ν hΦ), fun Y hY => ?_, ?_⟩
      · simp [hΦe Y (by omega)]
      · have : Ψ - (Ψρ - Φ) = (Ψ - Ψρ) + Φ := by abel
        rw [this]; exact Submodule.add_mem _ hN hΦ
  obtain ⟨Ψ₀, h1, h2, h3⟩ := ind n le_rfl
  refine ⟨Ψ₀, h1, fun Y hY => h2 Y (lt_of_le_of_ne ?_ hY), h3⟩
  simpa using Matrix.rank_le_card_height Y

end GlobalTheory.RankStrata
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFullRankModuloTranslatesStatement
open GlobalTheory.WeilM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_full_rank_modulo_translates : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) →
    ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ Ψ₀ ∈ SB (Matrix (Fin n) (Fin d) k), (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≠ n → Ψ₀ Y = 0) ∧
      Ψ - Ψ₀ ∈ Submodule.span ℂ {Z | ∃ g : GL (Fin n) k, ∃ Ψ' ∈ SB (Matrix (Fin n) (Fin d) k), Z = GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ'} := by
  first | exact @GlobalTheory.RankStrata.exists_fullRank_sub_mem_span | exact GlobalTheory.RankStrata.exists_fullRank_sub_mem_span | (intros; apply GlobalTheory.RankStrata.exists_fullRank_sub_mem_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPrimitiveVectorCompactRescale
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.GeomZero

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  simp [Sec.res]

theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (t : Sec F U) :
    Sec.res g (n • t) = n • Sec.res g t := map_nsmul ((F.obj.map g.op).hom) n t

theorem res_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero ((F.obj.map g.op).hom)

theorem q_dvd_nsmul {q : ℕ} {i : ℤ} {U : Scheme.{0}} (t : Sec (tw q i) U) (k : ℕ) : (q * k) • t = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q * k : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp
  rw [this]
  exact zero_smul _ t

theorem eq_zero_of_geom : ∀ (q : ℕ) [NeZero q] (R : Type) [CommRing R], IsUnit (q : R) → ∀ (j : ℤ)
    (a : Ht q (sp R) 0 j), (∀ (K : Type) [Field K] [IsAlgClosed K] (f : R →+* K), pull _ (spMap f) _ 0 a = 0) → a = 0 := by
  intro q _ R _ _ j a ha
  obtain ⟨-, e, he, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q j)
  obtain ⟨s, rfl⟩ := (e (Spec (CommRingCat.of R))).surjective a
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)),
      Sec.res φ s = 0 := by
    intro K _ _ φ
    have h := ha K (Spec.preimage φ).hom
    have hφ : Spec.map (CommRingCat.ofHom (Spec.preimage φ).hom) = φ := by
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    rw [spMap, hφ, he] at h
    exact (map_eq_zero_iff _ (e _).injective).1 h
  have hs : s = 0 := by
    refine (sec_ext_glue (ZMod q) (tw q j) (Spec (CommRingCat.of R))).1 s 0 ?_
    refine (loc_iff_etale_affine_points (Spec (CommRingCat.of R)) (fun _ g => Sec.res g s = Sec.res g 0)
      (fun V W g k h => by rw [res_comp, res_comp, h])).2 ?_
    intro x
    have stab : ∀ (V W : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of R)) (k : W ⟶ V),
        (Sec.res g s = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g s = c • twGen j ζ) →
        (Sec.res (k ≫ g) s = 0 ∨ ∃ (ζ : Prim q Γ(W, ⊤)) (c : ℕ), Sec.res (k ≫ g) s = c • twGen j ζ) := by
      rintro V W g k (h | ⟨ζ, c, h⟩)
      · left; rw [res_comp, h, res_zero]
      · right; exact ⟨ζ.map k.appTop.hom, c, by rw [res_comp, h, res_nsmul, (GlobalTheory.T.tateTwist_sections_locally_generated q j).2.2.2.1]⟩
    obtain ⟨V, g, hV, hg, hx, hP⟩ := (loc_iff_etale_affine_points (Spec (CommRingCat.of R))
      (fun V g => Sec.res g s = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g s = c • twGen j ζ) stab).1
      ((GlobalTheory.T.tateTwist_sections_locally_generated q j).1 _ s) x
    refine ⟨V, g, hV, hg, hx, ?_⟩
    show Sec.res g s = Sec.res g 0
    rw [res_zero]
    rcases hP with h | ⟨ζ, c, h⟩
    · exact h
    · obtain ⟨v, -⟩ := hx
      let ψ : Spec (CommRingCat.of (AlgebraicClosure (V.residueField v))) ⟶ V :=
        Spec.map (CommRingCat.ofHom (algebraMap (V.residueField v) (AlgebraicClosure (V.residueField v)))) ≫
          V.fromSpecResidueField v
      have h0 := hgeo (AlgebraicClosure (V.residueField v)) (ψ ≫ g)
      rw [res_comp, h, res_nsmul, (GlobalTheory.T.tateTwist_sections_locally_generated q j).2.2.2.1] at h0
      haveI : Nonempty (Spec (CommRingCat.of (AlgebraicClosure (V.residueField v)))) := inferInstance
      obtain ⟨k, rfl⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q j).2.2.1 _ _ _ h0
      rw [h]
      exact q_dvd_nsmul _ k
  rw [hs, map_zero]

end GlobalTheory.EtC.GeomZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolUnifPullAlongGroupHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolUnifPullAlongGroupHom
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace PullUnifHom

open GlobalTheory.PullHermitian

variable {X Y : Scheme.{0}}

lemma chart_pull_iff' (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (j : PUnit → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull f).U j ↔ ⊤ ≤ (x ≫ f) ⁻¹ᵁ L.U (j PUnit.unit) :=
  ⟨fun h _ hp => Set.mem_iInter.1 (h hp) PUnit.unit, fun h _ hp => Set.mem_iInter.2 fun _ => h hp⟩

lemma le_left' {x : Sp ℂ ⟶ X} {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V)) : ⊤ ≤ x ⁻¹ᵁ U :=
  h.trans (fun _ hp => And.left hp)

lemma le_right' {x : Sp ℂ ⟶ X} {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V)) : ⊤ ≤ x ⁻¹ᵁ V :=
  h.trans (fun _ hp => And.right hp)

lemma valAt'_pull_g' (x : Sp ℂ ⟶ X) (L : LB Y) (f : X ⟶ Y) (i j : PUnit → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((L.pull f).U i ⊓ (L.pull f).U j)) :
    valAt' x ((L.pull f).U i ⊓ (L.pull f).U j) ((L.pull f).g i j).val =
      valAt' (x ≫ f) (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))
        (L.g (i PUnit.unit) (j PUnit.unit)).val := by
  have hi := (chart_pull_iff' x L f i).1 (le_left' h)
  have hj := (chart_pull_iff' x L f j).1 (le_right' h)
  rw [valAt'_eq_unitVal x h, valAt'_eq_unitVal _ (inf_of _ hi hj)]
  have := unitVal_linComb x L f 1 (i PUnit.unit) (j PUnit.unit) h (inf_of _ hi hj)
  exact congrArg Units.val (this.trans (zpow_one _))

theorem exists_holUnif_pull_hom : ∀ (A B : Over (Sp ℂ)) [GrpObj A] [GrpObj B] (φ : A ⟶ B) (L : LB B.left) (g : ℕ) (u' : HolUnif B L g)
    (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (χ' : u'.Λ → ℂ),
    (∀ z w, ex (z + w) = ex z * ex w) → Function.Surjective ex → (∀ z, ex z = 1 ↔ z ∈ Λ) →
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ (U : A.left.Opens) (f : Γ(A.left, U)), IsOpen {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (ex z).left U f) {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U}) →
    (∀ z, ex z ≫ φ = u'.ex z) → Λ ≤ u'.Λ → u'.IsAH Hm χ' →
    ∃ (u : HolUnif A (L.pull φ.left) g) (χ : u.Λ → ℂ), (∀ w, w ∈ u.Λ ↔ w ∈ Λ) ∧ u.IsAH Hm χ := by
  intro A B _ _ φ L g u' ex Λ Hm χ' hadd honto hker hdisc hfull hhol hφ hΛ hAH
  have keyl : ∀ z, (ex z).left ≫ φ.left = (u'.ex z).left := fun z => by rw [← Over.comp_left, hφ]
  have hch : ∀ (j : (L.pull φ.left).ι) z, (⊤ ≤ (ex z).left ⁻¹ᵁ (L.pull φ.left).U j ↔
      ⊤ ≤ (u'.ex z).left ⁻¹ᵁ L.U (j PUnit.unit)) := fun j z =>
    (chart_pull_iff' _ L _ j).trans (iff_of_eq (by rw [keyl z]))
  let u : HolUnif A (L.pull φ.left) g :=
    ⟨ex, hadd, honto, Λ, hker, hdisc, hfull, hhol, fun j z => u'.fr (j PUnit.unit) z,
     fun j => (u'.fr_hol (j PUnit.unit)).mono (fun z hz => (hch j z).1 hz),
     fun j z hz => u'.fr_ne _ _ ((hch j z).1 hz),
     fun i j z h => by
        have hi := (hch i z).1 (le_left' h)
        have hj := (hch j z).1 (le_right' h)
        show u'.fr (i PUnit.unit) z = _ * u'.fr (j PUnit.unit) z
        rw [valAt'_pull_g' _ L _ i j h, keyl z]
        exact u'.fr_compat _ _ _ (inf_of _ hi hj)⟩
  refine ⟨u, fun l => χ' ⟨l.1, hΛ l.2⟩, fun w => Iff.rfl, ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hAH
  exact ⟨h1, h2, fun l => h3 _, fun l i z hz => h4 ⟨l.1, hΛ l.2⟩ (i PUnit.unit) z ((hch i z).1 hz)⟩

end PullUnifHom
end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolUnifPullAlongGroupHomStatement
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holUnif_pull_along_groupHom : ∀ (A B : Over (Sp ℂ)) [GrpObj A] [GrpObj B] (φ : A ⟶ B) (L : LB B.left) (g : ℕ) (u' : HolUnif B L g)
    (ex : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (χ' : u'.Λ → ℂ),
    (∀ z w, ex (z + w) = ex z * ex w) → Function.Surjective ex → (∀ z, ex z = 1 ↔ z ∈ Λ) →
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ (U : A.left.Opens) (f : Γ(A.left, U)), IsOpen {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (ex z).left U f) {z | ⊤ ≤ (ex z).left ⁻¹ᵁ U}) →
    (∀ z, ex z ≫ φ = u'.ex z) → Λ ≤ u'.Λ → u'.IsAH Hm χ' →
    ∃ (u : HolUnif A (L.pull φ.left) g) (χ : u.Λ → ℂ), (∀ w, w ∈ u.Λ ↔ w ∈ Λ) ∧ u.IsAH Hm χ := by
  first | exact @GlobalTheory.PullUnifHom.exists_holUnif_pull_hom | exact GlobalTheory.PullUnifHom.exists_holUnif_pull_hom | (intros; apply GlobalTheory.PullUnifHom.exists_holUnif_pull_hom <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveChainsQuasiIsoOfLocallySurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveMapEqCechNerveOfPreservesWidePushouts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveMapEqCechNerveOfPreservesWidePushouts
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConerveNerve

variable {T : Type 1} [Category.{0} T] (Ψ : T ⥤ PShᵒᵖ) {U V : T} (g : U ⟶ V) (J : Type) [HasWidePushout U (fun _ : J => V) (fun _ => g)]

def cmp : (Ψ.obj (widePushout U (fun _ : J => V) fun _ => g)).unop ⟶
    widePullback (Ψ.obj U).unop (fun _ : J => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop) :=
  WidePullback.lift (Ψ.map (WidePushout.head _)).unop (fun i => (Ψ.map (WidePushout.ι _ i)).unop)
    (fun i => by rw [← unop_comp, ← Ψ.map_comp]; exact congrArg (fun k => (Ψ.map k).unop) (WidePushout.arrow_ι (fun _ : J => g) i))

lemma cmp_π (i : J) : cmp Ψ g J ≫ WidePullback.π _ i = (Ψ.map (WidePushout.ι _ i)).unop := by
  simp only [cmp, WidePullback.lift_π]

lemma cmp_base : cmp Ψ g J ≫ WidePullback.base _ = (Ψ.map (WidePushout.head _)).unop := by
  simp only [cmp, WidePullback.lift_base]

def coc : Cocone (WidePushoutShape.wideSpan U (fun _ : J => V) (fun _ => g) ⋙ Ψ) :=
  WidePushoutShape.mkCocone (X := op (widePullback (Ψ.obj U).unop (fun _ : J => (Ψ.obj V).unop) (fun _ => (Ψ.map g).unop)))
    (WidePullback.base _).op (fun i => (WidePullback.π _ i).op) (fun i => by
      apply Quiver.Hom.unop_inj
      exact WidePullback.π_arrow (fun _ : J => (Ψ.map g).unop) i)

lemma isIso_cmp [PreservesColimitsOfShape (WidePushoutShape J) Ψ] : IsIso (cmp Ψ g J) := by
  let hC := isColimitOfPreserves Ψ (colimit.isColimit (WidePushoutShape.wideSpan U (fun _ : J => V) (fun _ => g)))
  refine ⟨(hC.desc (coc Ψ g J)).unop, ?_, ?_⟩
  · apply Quiver.Hom.op_inj
    show hC.desc (coc Ψ g J) ≫ (cmp Ψ g J).op = 𝟙 _
    apply hC.hom_ext
    intro j
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (cmp Ψ g J).op) (hC.fac (coc Ψ g J) j)).trans ?_
    refine Eq.trans ?_ (Category.comp_id _).symm
    apply Quiver.Hom.unop_inj
    rcases j with _ | i
    · exact cmp_base Ψ g J
    · exact cmp_π Ψ g J i
  · apply WidePullback.hom_ext
    · intro i
      have := congrArg Quiver.Hom.unop (hC.fac (coc Ψ g J) (some i))
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg _ (cmp_π Ψ g J i)).trans ?_
      exact this.trans (Category.id_comp _).symm
    · have := congrArg Quiver.Hom.unop (hC.fac (coc Ψ g J) none)
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg _ (cmp_base Ψ g J)).trans ?_
      exact this.trans (Category.id_comp _).symm

end GlobalTheory.EtC.ConerveNerve

namespace GlobalTheory.EtC.ConerveNerve

theorem conerve_nerve : ∀ (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ), (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V), ∃ e : ((((Arrow.mk g).cechConerve ⋙ Ψ).leftOp : Spc) ⟶ (Arrow.mk (Ψ.map g).unop).cechNerve), IsIso e ∧ e ≫ (Arrow.mk (Ψ.map g).unop).augmentedCechNerve.hom = lev Ψ (coAug g) := by
  intro T _ _ Ψ hΨ U V g
  refine ⟨{ app := fun n => cmp Ψ g (Fin (n.unop.len + 1)), naturality := ?_ }, ?_, ?_⟩
  · intro m n f
    apply WidePullback.hom_ext
    · intro i
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine (congrArg _ (cmp_π Ψ g _ i)).trans ?_
      have hN : (Arrow.mk (Ψ.map g).unop).cechNerve.map f ≫ WidePullback.π (fun _ => (Arrow.mk (Ψ.map g).unop).hom) i =
          WidePullback.π (fun _ => (Arrow.mk (Ψ.map g).unop).hom) (f.unop.toOrderHom i) :=
        WidePullback.lift_π _ _ _ _ _
      refine Eq.trans ?_ (congrArg _ hN).symm
      refine Eq.trans ?_ (cmp_π Ψ g _ _).symm
      change (Ψ.map (WidePushout.ι _ i) ≫ Ψ.map ((Arrow.mk g).cechConerve.map f.unop)).unop = _
      refine (congrArg Quiver.Hom.unop (Ψ.map_comp _ _).symm).trans ?_
      exact congrArg (fun k => (Ψ.map k).unop) (by apply WidePushout.ι_desc)
    · refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine (congrArg _ (cmp_base Ψ g _)).trans ?_
      have hN : (Arrow.mk (Ψ.map g).unop).cechNerve.map f ≫ WidePullback.base (fun _ : Fin ((unop n).len + 1) => (Arrow.mk (Ψ.map g).unop).hom) =
          WidePullback.base (fun _ : Fin ((unop m).len + 1) => (Arrow.mk (Ψ.map g).unop).hom) := by
        apply WidePullback.lift_base
      refine Eq.trans ?_ (congrArg _ hN).symm
      refine Eq.trans ?_ (cmp_base Ψ g _).symm
      change (Ψ.map (WidePushout.head _) ≫ Ψ.map ((Arrow.mk g).cechConerve.map f.unop)).unop = _
      refine (congrArg Quiver.Hom.unop (Ψ.map_comp _ _).symm).trans ?_
      exact congrArg (fun k => (Ψ.map k).unop) (by apply WidePushout.head_desc)
  · have : ∀ n : SimplexCategoryᵒᵖ, IsIso (cmp Ψ g (Fin (n.unop.len + 1))) := fun n => by
      haveI := hΨ n.unop.len
      exact isIso_cmp Ψ g _
    exact (NatTrans.isIso_iff_isIso_app _).2 this
  · refine NatTrans.ext (funext fun n => ?_)
    exact cmp_base Ψ g _

end GlobalTheory.EtC.ConerveNerve
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveMapEqCechNerveOfPreservesWidePushoutsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechConerve_map_eq_cechNerve_of_preservesWidePushouts : ∀ (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ), (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V), ∃ e : ((((Arrow.mk g).cechConerve ⋙ Ψ).leftOp : Spc) ⟶ (Arrow.mk (Ψ.map g).unop).cechNerve), IsIso e ∧ e ≫ (Arrow.mk (Ψ.map g).unop).augmentedCechNerve.hom = lev Ψ (coAug g) := by
  first | (exact @GlobalTheory.EtC.ConerveNerve.conerve_nerve) | (exact GlobalTheory.EtC.ConerveNerve.conerve_nerve) | (intros; apply GlobalTheory.EtC.ConerveNerve.conerve_nerve <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveChainsQuasiIsoOfLocallySurjective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem chains_cech_conerve_quasiIso : ∀ (R : Type) [CommRing R] (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ), (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V), Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (Ψ.map g).unop → QuasiIso ((chains R).map (lev Ψ (coAug g))) := by
  intro R _ T _ _ Ψ hΨ U V g hg
  obtain ⟨e, he, hc⟩ := GlobalTheory.T.cechConerve_map_eq_cechNerve_of_preservesWidePushouts T Ψ hΨ U V g
  have h2 := GlobalTheory.T.quasiIso_chains_cech_of_isLocallySurjective' R _ _ (Ψ.map g).unop hg
  let h : ((Arrow.mk (Ψ.map g).unop).cechNerve : Spc) ⟶ disc.obj (Ψ.obj U).unop :=
    (Arrow.mk (Ψ.map g).unop).augmentedCechNerve.hom
  have key : lev Ψ (coAug g) = e ≫ h := hc.symm
  have h2' : QuasiIso ((chains R).map h) := h2
  rw [key, Functor.map_comp]
  haveI : IsIso ((chains R).map e) := inferInstance
  exact quasiIso_comp _ _
end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveChainsQuasiIsoOfLocallySurjectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechConerve_chains_quasiIso_of_locallySurjective : ∀ (R : Type) [CommRing R] (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ), (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V), Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (Ψ.map g).unop → QuasiIso ((chains R).map (lev Ψ (coAug g))) := by
  first | (exact @GlobalTheory.EtC.chains_cech_conerve_quasiIso) | (exact GlobalTheory.EtC.chains_cech_conerve_quasiIso) | (intros; apply GlobalTheory.EtC.chains_cech_conerve_quasiIso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalRingPointDualNumberSndLinearDerivation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalRingPointDualNumberSndLinearDerivation
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.DualEval

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem evalPt_of_eq {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}} (φ : R →+* R')
    (G' : Sp R ⟶ X) (x : Sp R' ⟶ X) (O : X.Opens) (h0 : ⊤ ≤ G' ⁻¹ᵁ O) (hx : ⊤ ≤ x ⁻¹ᵁ O)
    (e : x = spMap φ ≫ G') (f : Γ(X, O)) : evalPt x O hx f = φ (evalPt G' O h0 f) := by
  subst e
  exact evalPt_spMap_comp φ G' O h0 hx f

theorem snd_of_mul_eq {K : Type} [Field K] (u t s : DualNumber K) (ht : t.fst ≠ 0)
    (e : u * t = s) : u.snd = (s.snd - s.fst / t.fst * t.snd) / t.fst := by
  have e1 : u.fst * t.fst = s.fst := by rw [← e]; rfl
  have e2 : u.fst * t.snd + u.snd * t.fst = s.snd := by rw [← e, DualNumber.snd_mul]
  have hu : u.fst = s.fst / t.fst := by rw [eq_div_iff ht, e1]
  rw [eq_div_iff ht, ← e2, hu]
  ring

end GlobalTheory.DualEval

namespace GlobalTheory.DualEval

attribute [local instance] RingHom.ker_isPrime

section Lift

variable {S K : Type} [CommRing S] [Field K] (ψ : S →+* K)

theorem isUnit_of_lifts (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s)
    (y : (RingHom.ker ψ).primeCompl) : IsUnit (φ y) := by
  refine TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ?_
  rw [hφ]
  exact Ne.isUnit fun h0 => y.2 (by simpa [RingHom.mem_ker] using h0)

def liftAt (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) :
    Localization.AtPrime (RingHom.ker ψ) →+* DualNumber K :=
  IsLocalization.lift (M := (RingHom.ker ψ).primeCompl) (isUnit_of_lifts ψ φ hφ)

theorem liftAt_comp (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) :
    (liftAt ψ φ hφ).comp (algebraMap S (Localization.AtPrime (RingHom.ker ψ))) = φ :=
  IsLocalization.lift_comp _

theorem liftAt_mk'_mul (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) (s : S)
    (t : (RingHom.ker ψ).primeCompl) :
    liftAt ψ φ hφ (IsLocalization.mk' (Localization.AtPrime (RingHom.ker ψ)) s t) * φ t = φ s := by
  have := congrArg (liftAt ψ φ hφ)
    (IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker ψ)) s t)
  rw [map_mul] at this
  unfold liftAt at this ⊢
  rw [IsLocalization.lift_eq, IsLocalization.lift_eq] at this
  exact this

theorem psi_ne_zero (t : (RingHom.ker ψ).primeCompl) : ψ t ≠ 0 := fun h0 =>
  t.2 (by simpa [RingHom.mem_ker] using h0)

theorem liftAt_mk'_snd (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) (s : S)
    (t : (RingHom.ker ψ).primeCompl) :
    (liftAt ψ φ hφ (IsLocalization.mk' (Localization.AtPrime (RingHom.ker ψ)) s t)).snd =
      ((φ s).snd - ψ s / ψ t * (φ t).snd) / ψ t := by
  have := snd_of_mul_eq _ _ _ (by rw [hφ]; exact psi_ne_zero ψ t) (liftAt_mk'_mul ψ φ hφ s t)
  rw [hφ, hφ] at this
  exact this

theorem liftAt_isLocalHom (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) :
    IsLocalHom ((TrivSqZeroExt.fstHom K K K).toRingHom.comp (liftAt ψ φ hφ)) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker ψ).primeCompl x
  rw [IsLocalization.AtPrime.isUnit_mk'_iff]
  intro hs
  have e1 : (liftAt ψ φ hφ (IsLocalization.mk' (Localization.AtPrime (RingHom.ker ψ)) s t)).fst *
      ψ t = ψ s := by
    rw [← hφ, ← hφ, ← liftAt_mk'_mul ψ φ hφ s t]
    rfl
  have hs0 : ψ s = 0 := by simpa [RingHom.mem_ker] using hs
  rw [hs0] at e1
  have hne : (liftAt ψ φ hφ (IsLocalization.mk' (Localization.AtPrime (RingHom.ker ψ)) s t)).fst
      ≠ 0 := hx.ne_zero
  exact hne ((mul_eq_zero.1 e1).resolve_right (psi_ne_zero ψ t))

end Lift

theorem evalPt_snd_sum {X : Scheme.{0}} {S K : Type} [CommRing S] [Field K] (G : Sp S ⟶ X)
    (ψ : S →+* K) {ι : Type} [Fintype ι] (θc : ι → (S →+* DualNumber K)) (θ : S →+* DualNumber K)
    (m : ι → K) (h1 : ∀ a s, (θc a s).fst = ψ s) (h2 : ∀ s, (θ s).fst = ψ s)
    (h3 : ∀ s, (θ s).snd = ∑ a, m a * (θc a s).snd) (O : X.Opens) (f : Γ(X, O))
    (h : ⊤ ≤ (spMap θ ≫ G) ⁻¹ᵁ O) (h' : ∀ a, ⊤ ≤ (spMap (θc a) ≫ G) ⁻¹ᵁ O) :
    (evalPt (spMap θ ≫ G) O h f).snd = ∑ a, m a * (evalPt (spMap (θc a) ≫ G) O (h' a) f).snd := by
  classical
  let L := Localization.AtPrime (RingHom.ker ψ)
  let alg : S →+* L := algebraMap S L
  let fstR : DualNumber K →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom
  let G' : Sp L ⟶ X := spMap alg ≫ G
  haveI := liftAt_isLocalHom ψ θ h2
  have hm : IsLocalRing.closedPoint L ∈ G' ⁻¹ᵁ O := by
    rw [← IsLocalRing.comap_closedPoint (fstR.comp (liftAt ψ θ h2))]
    have hmor : spMap (fstR.comp (liftAt ψ θ h2)) ≫ G' = spMap fstR ≫ spMap θ ≫ G := by
      rw [← Category.assoc, ← Category.assoc, ← spMap_comp_ring, ← spMap_comp_ring,
        RingHom.comp_assoc, liftAt_comp]
    let pt : Sp K := IsLocalRing.closedPoint K
    have key : (spMap (fstR.comp (liftAt ψ θ h2)) ≫ G') pt ∈ O := by
      rw [hmor]
      exact h (Set.mem_univ ((spMap fstR) pt))
    exact key
  have h0 : ⊤ ≤ G' ⁻¹ᵁ O := ((IsLocalRing.closed_point_mem_iff (U := G' ⁻¹ᵁ O)).1 hm).ge
  have hval : ∀ (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s)
      (hx : ⊤ ≤ (spMap φ ≫ G) ⁻¹ᵁ O),
      evalPt (spMap φ ≫ G) O hx f = liftAt ψ φ hφ (evalPt G' O h0 f) := by
    intro φ hφ hx
    refine evalPt_of_eq _ G' _ O h0 hx ?_ f
    rw [← Category.assoc, ← spMap_comp_ring, liftAt_comp]
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.mk'_surjective (RingHom.ker ψ).primeCompl (evalPt G' O h0 f)
  have hA : ∀ a, (evalPt (spMap (θc a) ≫ G) O (h' a) f).snd =
      (((θc a) s).snd - ψ s / ψ t * ((θc a) t).snd) / ψ t := fun a => by
    rw [hval (θc a) (h1 a) (h' a), ← hst, liftAt_mk'_snd]
  rw [hval θ h2 h, ← hst, liftAt_mk'_snd]
  simp_rw [hA, h3, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end GlobalTheory.DualEval
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalRingPointDualNumberSndLinearDerivationStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TangentOrigin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalRingPoint_dualNumber_snd_linear_derivation : ∀ {X : Scheme.{0}} {S K : Type} [CommRing S] [Field K] (G : Sp S ⟶ X) (ψ : S →+* K) {ι : Type} [Fintype ι] (θc : ι → (S →+* DualNumber K)) (θ : S →+* DualNumber K) (m : ι → K), (∀ a s, (θc a s).fst = ψ s) → (∀ s, (θ s).fst = ψ s) → (∀ s, (θ s).snd = ∑ a, m a * (θc a s).snd) → ∀ (O : X.Opens) (f : Γ(X, O)) (h : ⊤ ≤ (spMap θ ≫ G) ⁻¹ᵁ O) (h' : ∀ a, ⊤ ≤ (spMap (θc a) ≫ G) ⁻¹ᵁ O), (evalPt (spMap θ ≫ G) O h f).snd = ∑ a, m a * (evalPt (spMap (θc a) ≫ G) O (h' a) f).snd := by
  first | exact @GlobalTheory.DualEval.evalPt_snd_sum | exact GlobalTheory.DualEval.evalPt_snd_sum | (intros; apply GlobalTheory.DualEval.evalPt_snd_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRingClassOrderUnitsEqMaxRealSubfieldUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRingClassOrderUnitsEqMaxRealSubfieldUnits
open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.OrderUnits

theorem prime_not_mem_sq {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E)
    (w : HeightOneSpectrum (𝓞 E)) (hv : (p : 𝓞 E) ∈ w.asIdeal) : (p : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  obtain ⟨P, hP, hP0⟩ := w
  have he : P.ramificationIdx ℤ = 1 := by
    have h1 := (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) (Nat.prime_iff_prime_int.mp hp)).1 hd P hP (by simpa using hv)
    have := hP.isMaximal hP0
    have : (P.under ℤ).IsMaximal := inferInstance
    have hne : P.under ℤ ≠ ⊥ := by
      intro h0
      have h1 : (p : ℤ) ∈ P.under ℤ := by rw [Ideal.under_def, Ideal.mem_comap]; simpa using hv
      rw [h0] at h1
      exact hp.ne_zero (by simpa using h1)
    have : Finite (ℤ ⧸ P.under ℤ) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
    have : Finite (P.under ℤ).ResidueField := inferInstance
    exact Ideal.ramificationIdx_eq_one_iff.2 h1
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) ≤ P := by
    rw [hmap, Ideal.span_le]; simpa using hv
  have : P.LiesOver (Ideal.span {(p : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ hP.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hb] at he
  intro h2
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h2

theorem pow_first_order {R : Type} [CommRing R] (t : R) (i : ℕ) : ∃ r, (1 + t) ^ i = 1 + i * t + t ^ 2 * r := by
  induction i with
  | zero => exact ⟨0, by simp⟩
  | succ i ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨r + i + t * r, by rw [pow_succ, hr]; push_cast; ring⟩

theorem geom_first_order {R : Type} [CommRing R] (t : R) (n : ℕ) :
    ∃ r, ∑ i ∈ Finset.range n, (1 + t) ^ i = n + (n.choose 2 : ℕ) * t + t ^ 2 * r := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨s, hs⟩ := pow_first_order t n
    refine ⟨r + s, ?_⟩
    rw [Finset.sum_range_succ, hr, hs, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    push_cast; ring

theorem root_of_unity_eq_one {R : Type} [CommRing R] [IsDomain R] {P : Ideal R} (hP : P ≠ ⊤) {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2)
    (hlP : (l : R) ∈ P) (hlP2 : (l : R) ∉ P ^ 2) {ζ : R} (hζ : IsOfFinOrder ζ) (h1 : ζ - 1 ∈ P) : ζ = 1 := by
  by_contra hne
  have hn : orderOf ζ ≠ 1 := fun h => hne (orderOf_eq_one_iff.1 h)
  obtain ⟨p, hp, m, hm⟩ := Nat.exists_prime_and_dvd hn
  have hpos := hζ.orderOf_pos
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp [hm] at hpos)
  have hη1 : ζ ^ m ≠ 1 := pow_ne_one_of_lt_orderOf hm0.ne' (by rw [hm]; nlinarith [hp.two_le])
  have hηp : (ζ ^ m) ^ p = 1 := by rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]
  have ht : ζ ^ m - 1 ∈ P := by
    obtain ⟨s, hs⟩ := sub_one_dvd_pow_sub_one ζ m
    rw [hs]; exact P.mul_mem_right _ h1
  have hsum : ∑ i ∈ Finset.range p, (ζ ^ m) ^ i = 0 := by
    have := mul_geom_sum (ζ ^ m) p
    rw [hηp, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hη1)
  obtain ⟨r, hr⟩ := geom_first_order (ζ ^ m - 1) p
  rw [add_sub_cancel, hsum] at hr
  set t := ζ ^ m - 1
  have hpe : (p : R) = -((p.choose 2 : ℕ) * t) - t ^ 2 * r := by linear_combination -hr
  have hpP : (p : R) ∈ P := by
    rw [hpe]
    exact sub_mem (neg_mem (P.mul_mem_left _ ht)) (P.mul_mem_right _ (P.pow_mem_of_mem ht 2 two_pos))
  have hpl : p = l := by
    by_contra h
    have hc : IsCoprime (p : R) (l : R) := Nat.Coprime.cast ((Nat.coprime_primes hp hl).2 h)
    obtain ⟨a, b, hab⟩ := hc
    exact hP ((Ideal.eq_top_iff_one P).2 (hab ▸ add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hlP)))
  subst hpl
  obtain ⟨k, hk⟩ := hp.dvd_choose_self two_ne_zero (lt_of_le_of_ne hp.two_le (Ne.symm hl2))
  apply hlP2
  rw [hpe, hk]
  refine sub_mem (neg_mem ?_) (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ht 2))
  rw [sq]
  push_cast
  exact Ideal.mul_mem_mul (P.mul_mem_right _ hlP) ht

theorem orderC_units (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (hc : 𝔣 ∣ c)
    (x : E) (hx0 : x ≠ 0) (hx : x ∈ orderC c) (hx' : x⁻¹ ∈ orderC c) : ∃ u : (OF E)ˣ, x = algebraMap (OF E) E u := by
  obtain ⟨h0, h1, h⟩ := h𝔣
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal 𝔣 h1
  have hM0 : M ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hle))
  obtain ⟨⟨P, -, -, hP, -⟩, -, l, hl, hl2, hlv, hd, -⟩ := h ⟨M, hM.isPrime, hM0⟩ (Ideal.dvd_iff_le.2 hle)
  have hP' : P.asIdeal.comap (algebraMap (OF E) (𝓞 E)) = M := hP
  have hlP : (l : 𝓞 E) ∈ P.asIdeal := by
    have : (l : OF E) ∈ P.asIdeal.comap (algebraMap (OF E) (𝓞 E)) := by rw [hP']; exact hlv
    simpa using this
  have hcP : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤ P.asIdeal :=
    Ideal.map_le_iff_le_comap.2 (hP' ▸ (Ideal.le_of_dvd hc).trans hle)
  obtain ⟨a, b, hb, hab⟩ := mem_orderC.1 hx
  obtain ⟨a', b', -, hab'⟩ := mem_orderC.1 hx'
  have e1 : x = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a + b) := by rw [hab, map_add (f := _)]; rfl
  have e2 : x⁻¹ = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a' + b') := by rw [hab', map_add (f := _)]; rfl
  have hu : (algebraMap (OF E) (𝓞 E) a + b) * (algebraMap (OF E) (𝓞 E) a' + b') = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [map_mul, ← e1, ← e2, mul_inv_cancel₀ hx0, map_one]
  let u : (𝓞 E)ˣ := Units.mkOfMulEqOne _ _ hu
  have huv : (u : 𝓞 E) = algebraMap (OF E) (𝓞 E) a + b := rfl
  have hbc : IsCMField.ringOfIntegersComplexConj E b ∈ Ideal.map (algebraMap (OF E) (𝓞 E)) c := by
    have : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤
        (Ideal.map (algebraMap (OF E) (𝓞 E)) c).comap (IsCMField.ringOfIntegersComplexConj E) := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, Ideal.mem_comap, AlgEquiv.commutes]
      exact Ideal.mem_map_of_mem _ hy
    exact this hb
  have hcu : ((IsCMField.unitsComplexConj E u : (𝓞 E)ˣ) : 𝓞 E) =
      algebraMap (OF E) (𝓞 E) a + IsCMField.ringOfIntegersComplexConj E b := by
    have : ((IsCMField.unitsComplexConj E u : (𝓞 E)ˣ) : 𝓞 E) = IsCMField.ringOfIntegersComplexConj E u := rfl
    rw [this, huv, map_add (f := _), AlgEquiv.commutes]
  let ζ : (𝓞 E)ˣ := u * (IsCMField.unitsComplexConj E u)⁻¹
  have hfin : IsOfFinOrder ζ := (IsCMField.unitsMulComplexConjInv E u).2
  have hfin' : IsOfFinOrder (ζ : 𝓞 E) := (Units.coeHom (𝓞 E)).isOfFinOrder hfin
  have hζ : (ζ : 𝓞 E) - 1 ∈ P.asIdeal := by
    have : (ζ : 𝓞 E) - 1 = (b - IsCMField.ringOfIntegersComplexConj E b) * ↑(IsCMField.unitsComplexConj E u)⁻¹ := by
      have h3 := (IsCMField.unitsComplexConj E u).mul_inv
      rw [hcu] at h3
      simp only [ζ, Units.val_mul, huv]
      linear_combination h3
    rw [this]
    exact P.asIdeal.mul_mem_right _ (hcP (sub_mem hb hbc))
  have hone : ζ = 1 := Units.ext (root_of_unity_eq_one P.isPrime.ne_top hl hl2 hlP (prime_not_mem_sq hl hd P hlP) hfin' hζ)
  have hreal := (IsCMField.unitsComplexConj_eq_self_iff E u).1 (mul_inv_eq_one.1 hone).symm
  obtain ⟨v, hv⟩ := (IsCMField.mem_realUnits_iff E u).1 hreal
  refine ⟨v, ?_⟩
  rw [e1, ← huv, ← hv]
  rfl

end GlobalTheory.CMVal.OrderUnits
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRingClassOrderUnitsEqMaxRealSubfieldUnitsStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmRingClassOrder_units_eq_maxRealSubfield_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (𝔣 c : Ideal (OF E)), IsBaseCond 𝔣 → 𝔣 ∣ c → ∀ x : E, x ≠ 0 → x ∈ orderC c → x⁻¹ ∈ orderC c → ∃ u : (OF E)ˣ, x = algebraMap (OF E) E u := by
  first | exact @GlobalTheory.CMVal.OrderUnits.orderC_units | exact GlobalTheory.CMVal.OrderUnits.orderC_units | (intros; apply GlobalTheory.CMVal.OrderUnits.orderC_units <;> assumption)
end
end
