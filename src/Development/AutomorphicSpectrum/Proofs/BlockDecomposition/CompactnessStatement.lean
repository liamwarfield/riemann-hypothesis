module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicDoubleCosetOfEqualCorank
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAtOfSqBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColSqOfKerBasic

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSquareCongruenceConjugation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSquareCongruenceConjugation
open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.Twist

theorem block_twist {O L : Type} [CommRing O] [Field L] [Algebra O L] {n : ℕ} (ϖ : O) (w : L)
    (hw : w = algebraMap O L ϖ) (A B C D : Matrix (Fin n) (Fin n) O) :
    (fromBlocks A B (ϖ • C) D).map (algebraMap O L) *
        fromBlocks (1 : Matrix (Fin n) (Fin n) L) 0 0 (w • 1) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) L) 0 0 (w • 1) *
        (fromBlocks A (ϖ • B) C D).map (algebraMap O L) := by
  subst hw
  rw [fromBlocks_map, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp [smul_eq_mul] <;> simp [Algebra.smul_def]

theorem twist_gam : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ → ∀ γ ∈ Gam2 (n := n) ϖ,
      ∃ j' : GL (Ix n) O, inL γ * tauM w = tauM w * inL j' ∧ resK j' = 1 := by
  intro O L _ _ _ _ _ _ n ϖ hϖ w hw γ hγ
  have hγ' : ∀ i j, (γ : Matrix (Ix n) (Ix n) O) i j - (1 : Matrix (Ix n) (Ix n) O) i j ∈
      Ideal.span {ϖ ^ 2} := by
    intro i j
    rw [← Ideal.Quotient.eq]
    have := congrArg (fun u : GL (Ix n) (O ⧸ Ideal.span {ϖ ^ 2}) => u.1 i j)
      (MonoidHom.mem_ker.1 hγ)
    simpa [Matrix.one_apply, apply_ite] using this
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  have hm : Ideal.span {ϖ ^ 2} ≤ IsLocalRing.maximalIdeal O :=
    (Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self ϖ two_ne_zero)).trans
      ((Ideal.span_singleton_le_iff_mem _).2 hϖm)
  have hC : ∀ i j, ∃ c, (γ : Matrix (Ix n) (Ix n) O) (Sum.inr i) (Sum.inl j) = ϖ * (ϖ * c) := by
    intro i j
    have h0 := hγ' (Sum.inr i) (Sum.inl j)
    simp only [Matrix.one_apply, reduceCtorEq, if_false, sub_zero] at h0
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h0
    exact ⟨c, by rw [← hc]; ring⟩
  choose C hCe using hC
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Ix n) (Ix n) O, M = fromBlocks (γ : Matrix (Ix n) (Ix n) O).toBlocks₁₁
      (ϖ • (γ : Matrix (Ix n) (Ix n) O).toBlocks₁₂) (ϖ • Matrix.of C)
      (γ : Matrix (Ix n) (Ix n) O).toBlocks₂₂ := ⟨_, rfl⟩
  have hγM : (γ : Matrix (Ix n) (Ix n) O) = fromBlocks (γ : Matrix (Ix n) (Ix n) O).toBlocks₁₁
      (γ : Matrix (Ix n) (Ix n) O).toBlocks₁₂ (ϖ • (ϖ • Matrix.of C))
      (γ : Matrix (Ix n) (Ix n) O).toBlocks₂₂ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, hCe]
  have hsc : Matrix.scalar (Fin n) (w : L) = (w : L) • (1 : Matrix (Fin n) (Fin n) L) := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hrel : (γ : Matrix (Ix n) (Ix n) O).map (algebraMap O L) *
        fromBlocks (1 : Matrix (Fin n) (Fin n) L) 0 0 (Matrix.scalar (Fin n) (w : L)) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) L) 0 0 (Matrix.scalar (Fin n) (w : L)) *
        M.map (algebraMap O L) := by
    rw [hsc, hM]
    conv_lhs => rw [hγM]
    exact block_twist ϖ (w : L) hw _ _ _ _
  have hτ : (fromBlocks (1 : Matrix (Fin n) (Fin n) L) 0 0 (Matrix.scalar (Fin n) (w : L))).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, hsc, Matrix.det_smul, Matrix.det_one]
    simp
  have hdetM : M.det = (γ : Matrix (Ix n) (Ix n) O).det := by
    have h1 := congrArg Matrix.det hrel
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at h1
    have h2 := mul_left_cancel₀ hτ h1
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      ← RingHom.map_det] at h2
    exact (IsFractionRing.injective O L h2).symm
  have hdet : IsUnit M.det := by
    rw [hdetM]
    exact Matrix.isUnits_det_units γ
  have hMm : ∀ i j, M i j - (1 : Matrix (Ix n) (Ix n) O) i j ∈ IsLocalRing.maximalIdeal O := by
    intro i j
    rw [hM]
    rcases i with i | i <;> rcases j with j | j
    · simpa [Matrix.toBlocks₁₁] using hm (hγ' (Sum.inl i) (Sum.inl j))
    · simpa using Ideal.mul_mem_right _ _ hϖm
    · simpa using Ideal.mul_mem_right _ _ hϖm
    · simpa [Matrix.toBlocks₂₂] using hm (hγ' (Sum.inr i) (Sum.inr j))
  refine ⟨Matrix.nonsingInvUnit M hdet, Units.ext ?_, Units.ext ?_⟩
  · exact hrel
  · have h3 : M.map (IsLocalRing.residue O) = (1 : Matrix (Ix n) (Ix n) O).map (IsLocalRing.residue O) := by
      ext i j
      exact Ideal.Quotient.eq.2 (hMm i j)
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at h3
    exact h3

end GlobalTheory.CompanionTheory.Jp.Twist
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSquareCongruenceConjugationStatement
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_square_congruence_conjugation : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ → ∀ γ ∈ Gam2 (n := n) ϖ,
      ∃ j' : GL (Ix n) O, inL γ * tauM w = tauM w * inL j' ∧ resK j' = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Twist.twist_gam | exact GlobalTheory.CompanionTheory.Jp.Twist.twist_gam | (intros; apply GlobalTheory.CompanionTheory.Jp.Twist.twist_gam <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRankCompletionSymmetry
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRankCompletionSymmetry
open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.CountRank

open Module

variable {k : Type} [Field k] [Fintype k]

theorem card_injective {U V : Type} [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    [FiniteDimensional k U] [FiniteDimensional k V] {e n : ℕ}
    (hU : finrank k U = e) (hV : finrank k V = n) (he : e ≤ n) :
    Nat.card {g : U →ₗ[k] V // Function.Injective g} =
      ∏ j ∈ Finset.range e, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  classical
  have : Finite V := Module.finite_of_finite k
  let b : Module.Basis (Fin e) k U := Module.finBasisOfFinrankEq k U hU
  have key : ∀ g : U →ₗ[k] V, Function.Injective g ↔ LinearIndependent k (g ∘ b) := by
    intro g
    constructor
    · intro hg
      exact b.linearIndependent.map' g (LinearMap.ker_eq_bot.mpr hg)
    · intro hli
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker] at hx
      have hsum : ∑ i, (b.repr x i) • (g ∘ b) i = 0 := by
        have h0 : g (∑ i, (b.repr x i) • b i) = 0 := by rw [b.sum_repr]; exact hx
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum] at h0
        simpa only [Function.comp_apply, map_smul] using h0
      have hc := Fintype.linearIndependent_iff.mp hli _ hsum
      apply b.repr.injective
      ext i
      simp [hc i]
  have E : {g : U →ₗ[k] V // Function.Injective g} ≃ {s : Fin e → V // LinearIndependent k s} :=
    { toFun := fun g => ⟨g.1 ∘ b, (key g.1).mp g.2⟩
      invFun := fun s => ⟨b.constr k s.1, (key _).mpr (by
          have hs : (b.constr k s.1 : U → V) ∘ b = s.1 := by
            funext i
            simp
          rw [hs]
          exact s.2)⟩
      left_inv := fun g => Subtype.ext (b.ext fun i => by simp)
      right_inv := fun s => Subtype.ext (funext fun i => by simp) }
  rw [Nat.card_congr E, card_linearIndependent (K := k) (V := V) (k := e) (by omega), hV,
    Finset.prod_range (fun j => Fintype.card k ^ n - Fintype.card k ^ j)]

theorem card_ker_eq {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {n ρ : ℕ} (hV : finrank k V = n) (hρ : ρ ≤ n) (K : Submodule k V)
    (hK : finrank k K = n - ρ) :
    Nat.card {f : V →ₗ[k] V // LinearMap.ker f = K} =
      ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  classical
  have hQ : finrank k (V ⧸ K) = ρ := by
    have := Submodule.finrank_quotient_add_finrank K
    omega
  have E : {f : V →ₗ[k] V // LinearMap.ker f = K} ≃
      {g : (V ⧸ K) →ₗ[k] V // Function.Injective g} :=
    { toFun := fun f => ⟨K.liftQ f.1 (le_of_eq f.2.symm),
        LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq f.2))⟩
      invFun := fun g => ⟨g.1.comp K.mkQ, by
        rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr g.2, Submodule.comap_bot,
          Submodule.ker_mkQ]⟩
      left_inv := fun f => Subtype.ext (Submodule.liftQ_mkQ K f.1 _)
      right_inv := fun g => Subtype.ext (Submodule.linearMap_qext K (Submodule.liftQ_mkQ K _ _)) }
  rw [Nat.card_congr E]
  exact card_injective hQ hV (by omega)

theorem card_rank_eq {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {n ρ : ℕ} (hV : finrank k V = n) (hρ : ρ ≤ n) :
    Nat.card {f : V →ₗ[k] V // finrank k (LinearMap.range f) = ρ} =
      Nat.card {K : Submodule k V // finrank k K = n - ρ} *
        ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  classical
  have : Finite V := Module.finite_of_finite k
  have : Finite (V →ₗ[k] V) := Module.finite_of_finite k
  have : Finite (Submodule k V) :=
    Finite.of_injective (fun K : Submodule k V => (K : Set V)) SetLike.coe_injective
  letI : Fintype {K : Submodule k V // finrank k K = n - ρ} := Fintype.ofFinite _
  have E : {f : V →ₗ[k] V // finrank k (LinearMap.range f) = ρ} ≃
      Σ K : {K : Submodule k V // finrank k K = n - ρ},
        {f : V →ₗ[k] V // LinearMap.ker f = K.1} :=
    { toFun := fun f => ⟨⟨LinearMap.ker f.1, by
          have h1 := LinearMap.finrank_range_add_finrank_ker f.1
          have h2 := f.2
          omega⟩, ⟨f.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by
          have h1 := LinearMap.finrank_range_add_finrank_ker p.2.1
          have h2 := p.1.2
          have h3 := p.2.2
          rw [h3] at h1
          omega⟩
      left_inv := fun f => rfl
      right_inv := by
        rintro ⟨⟨K, hK⟩, ⟨f, hf⟩⟩
        dsimp only at hf
        subst hf
        rfl }
  rw [Nat.card_congr E, Nat.card_sigma,
    Finset.sum_congr rfl (fun a _ => card_ker_eq hV hρ a.1 a.2), Finset.sum_const,
    Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card (α := {K : Submodule k V // finrank k K = n - ρ})]

theorem card_sub_le {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {n : ℕ} (hV : finrank k V = n) (d : ℕ) (hd : d ≤ n) :
    Nat.card {K : Submodule k V // finrank k K = d} ≤
      Nat.card {K : Submodule k V // finrank k K = n - d} := by
  classical
  have : Finite V := Module.finite_of_finite k
  have : Finite (Submodule k V) :=
    Finite.of_injective (fun K : Submodule k V => (K : Set V)) SetLike.coe_injective
  let eV : Module.Dual k V ≃ₗ[k] V := ((Module.finBasis k V).toDualEquiv).symm
  have hDual : ∀ K : Submodule k V,
      finrank k (K.dualAnnihilator) = finrank k V - finrank k K := by
    intro K
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq K
    omega
  let F : {K : Submodule k V // finrank k K = d} → {K : Submodule k V // finrank k K = n - d} :=
    fun K => ⟨(K.1.dualAnnihilator).map (eV : Module.Dual k V →ₗ[k] V), by
      rw [LinearEquiv.finrank_map_eq, hDual, hV, K.2]⟩
  apply Nat.card_le_card_of_injective F
  intro K₁ K₂ h
  apply Subtype.ext
  have h1 : (K₁.1.dualAnnihilator).map (eV : Module.Dual k V →ₗ[k] V) =
      (K₂.1.dualAnnihilator).map (eV : Module.Dual k V →ₗ[k] V) := congrArg Subtype.val h
  have h2 := Submodule.map_injective_of_injective eV.injective h1
  exact Subspace.dualAnnihilator_inj.mp h2

theorem card_sub_symm {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {n : ℕ} (hV : finrank k V = n) (d : ℕ) (hd : d ≤ n) :
    Nat.card {K : Submodule k V // finrank k K = d} =
      Nat.card {K : Submodule k V // finrank k K = n - d} := by
  apply le_antisymm (card_sub_le hV d hd)
  have := card_sub_le hV (n - d) (Nat.sub_le n d)
  rwa [Nat.sub_sub_self hd] at this

theorem card_matrix_rank (n ρ : ℕ) :
    Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = ρ} =
      Nat.card {f : (Fin n → k) →ₗ[k] (Fin n → k) // finrank k (LinearMap.range f) = ρ} := by
  apply Nat.card_congr
  exact Equiv.subtypeEquiv
    (Matrix.toLin' : Matrix (Fin n) (Fin n) k ≃ₗ[k] ((Fin n → k) →ₗ[k] (Fin n → k))).toEquiv
    (fun D => by
      show D.rank = ρ ↔ finrank k (LinearMap.range (Matrix.toLin' D)) = ρ
      rw [Matrix.toLin'_apply']
      rfl)

theorem rank_symm (k : Type) [Field k] [Fintype k] (n ρ : ℕ) (h : ρ ≤ n) :
    Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = ρ} *
        ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) =
      Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = n - ρ} *
        ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  have hV : finrank k (Fin n → k) = n := Module.finrank_fin_fun k
  rw [card_matrix_rank, card_matrix_rank, card_rank_eq hV h, card_rank_eq hV (Nat.sub_le n ρ),
    Nat.sub_sub_self h, card_sub_symm hV ρ h]
  ring

end GlobalTheory.CompanionTheory.Jp.CountRank
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRankCompletionSymmetryStatement
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_rank_completion_symmetry : ∀ (k : Type) [Field k] [Fintype k] (n ρ : ℕ), ρ ≤ n →
    Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = ρ} *
        ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) =
      Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = n - ρ} *
        ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.CountRank.rank_symm | exact GlobalTheory.CompanionTheory.Jp.CountRank.rank_symm | (intros; apply GlobalTheory.CompanionTheory.Jp.CountRank.rank_symm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionUniqueUpToParabolic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionUniqueUpToParabolic
open Matrix GlobalTheory.CompanionTheory.Jp

noncomputable section

namespace GlobalTheory.CompanionTheory.Jp.RedUnique

theorem exists_pM_of_low_zero {k : Type} [Field k] {n : ℕ} (g : GL (Ix n) k)
    (hg : g.1.toBlocks₂₁ = 0) :
    ∃ (a d : GL (Fin n) k) (b : Matrix (Fin n) (Fin n) k), g = pM a d b := by
  have hgb : g.1 = fromBlocks g.1.toBlocks₁₁ g.1.toBlocks₁₂ 0 g.1.toBlocks₂₂ := by
    rw [← hg, fromBlocks_toBlocks]
  have hdet : g.1.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  rw [hgb, det_fromBlocks_zero₂₁] at hdet
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ (left_ne_zero_of_mul hdet),
    GeneralLinearGroup.mkOfDetNeZero _ (right_ne_zero_of_mul hdet), g.1.toBlocks₁₂, ?_⟩
  apply Units.ext
  exact hgb

theorem low_inv_mul_pM {R : Type} [CommRing R] {n : ℕ} (a₁ d₁ a₂ d₂ : GL (Fin n) R)
    (b₁ b₂ : Matrix (Fin n) (Fin n) R) :
    (((pM a₂ d₂ b₂)⁻¹ * pM a₁ d₁ b₁ : GL (Ix n) R)).1.toBlocks₂₁ = 0 := by
  have h1 : ((pM a₁ d₁ b₁ : GL (Ix n) R)).1 = fromBlocks a₁.1 b₁ 0 d₁.1 := rfl
  have h2 : (((pM a₂ d₂ b₂)⁻¹ : GL (Ix n) R)).1 =
      fromBlocks (a₂⁻¹).1 (-((a₂⁻¹).1 * b₂ * (d₂⁻¹).1)) 0 (d₂⁻¹).1 := rfl
  rw [Units.val_mul, h1, h2, fromBlocks_multiply]
  simp [toBlocks_fromBlocks₂₁]

theorem red_unique : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (w : Lˣ) (κ : GL (Ix n) O) (h₁ h₂ : GL (Ix n) (IsLocalRing.ResidueField O)),
    IsRed (O := O) w κ h₁ → IsRed (O := O) w κ h₂ →
      ∃ (a d : GL (Fin n) (IsLocalRing.ResidueField O)) (b : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)),
        h₂ = pM a d b * h₁ := by
  intro O L _ _ _ _ _ _ n w κ h₁ h₂ r₁ r₂
  obtain ⟨a₁, d₁, b₁, κ₁, e₁, rfl⟩ := r₁
  obtain ⟨a₂, d₂, b₂, κ₂, e₂, rfl⟩ := r₂
  obtain ⟨c, hcd⟩ : ∃ c : GL (Ix n) O, c = κ₂ * κ₁⁻¹ := ⟨_, rfl⟩
  have hc : inL (L := L) c = (pM a₂ d₂ b₂)⁻¹ * pM a₁ d₁ b₁ := by
    have e : pM a₁ d₁ b₁ * inL (L := L) κ₁ = pM a₂ d₂ b₂ * inL (L := L) κ₂ := e₁.symm.trans e₂
    rw [hcd, map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← e, mul_inv_cancel_right]
  have hlow : (inL (L := L) c).1.toBlocks₂₁ = 0 := by
    rw [hc]; exact low_inv_mul_pM _ _ _ _ _ _
  have hO : ∀ i j, c.1 (Sum.inr i) (Sum.inl j) = 0 := by
    intro i j
    have h0 : algebraMap O L (c.1 (Sum.inr i) (Sum.inl j)) = 0 := congrFun (congrFun hlow i) j
    exact IsFractionRing.injective O L (h0.trans (map_zero _).symm)
  have hk : (resK c).1.toBlocks₂₁ = 0 := by
    ext i j
    change IsLocalRing.residue O (c.1 (Sum.inr i) (Sum.inl j)) = 0
    rw [hO, map_zero]
  obtain ⟨a, d, b, hp⟩ := exists_pM_of_low_zero _ hk
  refine ⟨a, d, b, ?_⟩
  rw [← hp, ← map_mul, hcd, inv_mul_cancel_right]

end GlobalTheory.CompanionTheory.Jp.RedUnique

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReductionUniqueUpToParabolicStatement
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_unique_up_to_parabolic : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (w : Lˣ) (κ : GL (Ix n) O) (h₁ h₂ : GL (Ix n) (IsLocalRing.ResidueField O)),
    IsRed (O := O) w κ h₁ → IsRed (O := O) w κ h₂ →
      ∃ (a d : GL (Fin n) (IsLocalRing.ResidueField O)) (b : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)),
        h₂ = pM a d b * h₁ := by
  first | exact @GlobalTheory.CompanionTheory.Jp.RedUnique.red_unique | exact GlobalTheory.CompanionTheory.Jp.RedUnique.red_unique | (intros; apply GlobalTheory.CompanionTheory.Jp.RedUnique.red_unique <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvariantRightTranslation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvariantRightTranslation
noncomputable section

open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.AvgRight

theorem avgK_right_invariant : ∀ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) (ϖ : O) (φ : GL (Ix n) O → ℂ),
    (∀ κ, ∀ γ ∈ Gam2 (n := n) ϖ, φ (κ * γ) = φ κ) → ∀ j : GL (Ix n) O,
      avgK ϖ (fun κ => φ (κ * j)) = avgK ϖ φ := by
  intro O _ _ n ϖ φ hφ j
  have hout : ∀ x : GL (Ix n) O,
      φ (Quotient.out (QuotientGroup.mk x : GL (Ix n) O ⧸ Gam2 (n := n) ϖ)) = φ x := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Gam2 (n := n) ϖ) x
    rw [hh]
    exact hφ x h.1 h.2
  have hshift : ∀ u : GL (Ix n) O ⧸ Gam2 (n := n) ϖ,
      φ (Quotient.out u * j) =
        φ (Quotient.out (u * (QuotientGroup.mk j : GL (Ix n) O ⧸ Gam2 (n := n) ϖ))) := by
    intro u
    rw [← hout (Quotient.out u * j)]
    congr 2
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  unfold avgK
  congr 1
  rw [finsum_congr hshift]
  exact finsum_comp_equiv (Equiv.mulRight (QuotientGroup.mk j : GL (Ix n) O ⧸ Gam2 (n := n) ϖ))
    (f := fun u => φ (Quotient.out u))

end GlobalTheory.CompanionTheory.Jp.AvgRight

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvariantRightTranslationStatement
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_invariant_right_translation : ∀ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) (ϖ : O) (φ : GL (Ix n) O → ℂ),
    (∀ κ, ∀ γ ∈ Gam2 (n := n) ϖ, φ (κ * γ) = φ κ) → ∀ j : GL (Ix n) O,
      avgK ϖ (fun κ => φ (κ * j)) = avgK ϖ φ := by
  first | exact @GlobalTheory.CompanionTheory.Jp.AvgRight.avgK_right_invariant | exact GlobalTheory.CompanionTheory.Jp.AvgRight.avgK_right_invariant | (intros; apply GlobalTheory.CompanionTheory.Jp.AvgRight.avgK_right_invariant <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardFixedLowerRightBlock
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardFixedLowerRightBlock
open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.CntHalf

variable {k : Type} [Field k] {n : ℕ}

def lowH (g : GL (Ix n) k) : Matrix (Fin n) (Ix n) k := g.1.submatrix Sum.inr id

lemma lowH_eq (g : GL (Ix n) k) : lowH g = fromCols (lowerLeftBlock g) (dBlk g) := by
  ext i (j | j) <;> simp [lowH, lowerLeftBlock, dBlk, toBlocks₂₁, toBlocks₂₂]

lemma lowH_mul (g h : GL (Ix n) k) : lowH (g * h) = lowH g * h.1 := by
  ext i j
  simp [lowH, Matrix.mul_apply]

lemma lowH_one : lowH (1 : GL (Ix n) k) = fromCols 0 1 := by
  ext i (j | j) <;> simp [lowH, Matrix.one_apply]

lemma rank_lowH (g : GL (Ix n) k) : (lowH g).rank = n := by
  have h : LinearIndependent k g.1.row := Matrix.linearIndependent_rows_of_isUnit g.isUnit
  have h2 : LinearIndependent k (lowH g).row := h.comp Sum.inr Sum.inr_injective
  simpa using h2.rank_matrix

lemma exists_lowH (M : Matrix (Fin n) (Ix n) k) (hM : M.rank = n) : ∃ g : GL (Ix n) k, lowH g = M := by
  have hli : LinearIndependent k M.row := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, ← M.rank_eq_finrank_span_row, hM]
    simp
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl (Submodule.span k (Set.range M.row))
  have hfr : Module.finrank k W' = n := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hW'
    have h2 := M.rank_eq_finrank_span_row
    simp at h1
    omega
  let b := Module.finBasisOfFinrankEq k W' hfr
  let w : Fin n → (Ix n → k) := fun i => (b i : Ix n → k)
  have hw : LinearIndependent k w := b.linearIndependent.map' W'.subtype (Submodule.ker_subtype _)
  have hspan : Submodule.span k (Set.range w) ≤ W' := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (b i).2
  have hall : LinearIndependent k (Sum.elim w M.row) :=
    LinearIndependent.sum_type hw hli (Disjoint.mono_left hspan hW'.disjoint.symm)
  let A : Matrix (Ix n) (Ix n) k := Matrix.of (Sum.elim w M.row)
  have hA : IsUnit A := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact hall
  refine ⟨hA.unit, ?_⟩
  ext i j
  rfl

lemma card_fibre (g₀ : GL (Ix n) k) :
    Nat.card {g : GL (Ix n) k // lowH g = lowH g₀} =
      Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulRight g₀⁻¹) ?_)
  intro g
  have hone : lowH g₀ * (g₀⁻¹).1 = fromCols 0 1 := by
    rw [← lowH_mul, mul_inv_cancel, lowH_one]
  have hcd : (lowerLeftBlock (g * g₀⁻¹) = 0 ∧ dBlk (g * g₀⁻¹) = 1) ↔ lowH (g * g₀⁻¹) = fromCols 0 1 := by
    rw [lowH_eq, Matrix.fromCols_inj.eq_iff]
  simp only [Equiv.coe_mulRight]
  rw [hcd, lowH_mul, ← hone]
  constructor
  · intro h; rw [h]
  · intro h
    have := congrArg (· * g₀.1) h
    simpa [Matrix.mul_assoc, ← Units.val_mul] using this

theorem card_lowerRightBlock_eq_fibre_formula (k : Type) [Field k] [Fintype k] (n : ℕ) (D : Matrix (Fin n) (Fin n) k) :
    Nat.card {g : GL (Ix n) k // dBlk g = D} =
      Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1} *
        Nat.card {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} := by
  classical
  haveI : Fintype {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} := Fintype.ofFinite _
  let f : {g : GL (Ix n) k // dBlk g = D} → {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} :=
    fun g => ⟨lowerLeftBlock g.1, by have h := rank_lowH g.1; rw [lowH_eq, g.2] at h; exact h⟩
  have hfib : ∀ C, Nat.card {x // f x = C} = Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1} := by
    intro C
    obtain ⟨g₀, hg₀⟩ := exists_lowH (Matrix.fromCols C.1 D) C.2
    rw [← card_fibre g₀]
    have hy : ∀ y : {g : GL (Ix n) k // lowH g = lowH g₀},
        Matrix.fromCols (lowerLeftBlock y.1) (dBlk y.1) = Matrix.fromCols C.1 D := by
      intro y
      rw [← lowH_eq, ← hg₀]
      exact y.2
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, ?_⟩
        invFun := fun y => ⟨⟨y.1, ?_⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · rw [hg₀, lowH_eq, x.1.2, show lowerLeftBlock x.1.1 = C.1 from congrArg Subtype.val x.2]
    · exact (Matrix.fromCols_inj (hy y)).2
    · exact Subtype.ext (Matrix.fromCols_inj (hy y)).1
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv f).symm, Nat.card_sigma,
    Finset.sum_congr rfl (fun C _ => hfib C), Finset.sum_const, smul_eq_mul, Finset.card_univ,
    ← Nat.card_eq_fintype_card, mul_comm]

end GlobalTheory.CompanionTheory.Jp.CntHalf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardFixedLowerRightBlockStatement
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_fixed_lower_right_block : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (D : Matrix (Fin n) (Fin n) k),
    Nat.card {g : GL (Ix n) k // dBlk g = D} =
      Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1} *
        Nat.card {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} := by
  first | exact @GlobalTheory.CompanionTheory.Jp.CntHalf.card_lowerRightBlock_eq_fibre_formula | exact GlobalTheory.CompanionTheory.Jp.CntHalf.card_lowerRightBlock_eq_fibre_formula | (intros; apply GlobalTheory.CompanionTheory.Jp.CntHalf.card_lowerRightBlock_eq_fibre_formula <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRankLowerLeftEqLowerRight
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRankLowerLeftEqLowerRight
open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.CntSwap

def swapW (k : Type) [Field k] (n : ℕ) : GL (Ix n) k :=
  ⟨fromBlocks 0 1 1 0, fromBlocks 0 1 1 0,
    by simp [fromBlocks_multiply, fromBlocks_one],
    by simp [fromBlocks_multiply, fromBlocks_one]⟩

lemma lowerRightBlock_mul_block_swap {k : Type} [Field k] {n : ℕ} (g : GL (Ix n) k) :
    dBlk (g * swapW k n) = lowerLeftBlock g := by
  show (g.1 * fromBlocks 0 1 1 0).toBlocks₂₂ = g.1.toBlocks₂₁
  conv_lhs => rw [← fromBlocks_toBlocks g.1]
  rw [fromBlocks_multiply]
  simp

theorem card_lower_left_rank_eq_card_lower_right_rank : ∀ (k : Type) [Field k] [Fintype k] (n i : ℕ),
    Nat.card {g : GL (Ix n) k // (lowerLeftBlock g).rank = i} = Nat.card {g : GL (Ix n) k // (dBlk g).rank = i} := by
  intro k _ _ n i
  exact Nat.card_congr ((Equiv.mulRight (swapW k n)).subtypeEquiv (fun g => by
    rw [Equiv.coe_mulRight, lowerRightBlock_mul_block_swap]))

end GlobalTheory.CompanionTheory.Jp.CntSwap
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRankLowerLeftEqLowerRightStatement
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_rank_lower_left_eq_lower_right : ∀ (k : Type) [Field k] [Fintype k] (n i : ℕ),
    Nat.card {g : GL (Ix n) k // (lowerLeftBlock g).rank = i} = Nat.card {g : GL (Ix n) k // (dBlk g).rank = i} := by
  first | exact @GlobalTheory.CompanionTheory.Jp.CntSwap.card_lower_left_rank_eq_card_lower_right_rank | exact GlobalTheory.CompanionTheory.Jp.CntSwap.card_lower_left_rank_eq_card_lower_right_rank | (intros; apply GlobalTheory.CompanionTheory.Jp.CntSwap.card_lower_left_rank_eq_card_lower_right_rank <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactnessStatement
noncomputable section
open Matrix
namespace GlobalTheory.CompanionTheory.Jp.Cmp

theorem red_unique : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (w : Lˣ) (κ : GL (Ix n) O) (h₁ h₂ : GL (Ix n) (IsLocalRing.ResidueField O)),
    IsRed (O := O) w κ h₁ → IsRed (O := O) w κ h₂ →
      ∃ (a d : GL (Fin n) (IsLocalRing.ResidueField O)) (b : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O)),
        h₂ = pM a d b * h₁ := GlobalTheory.T.reduction_unique_up_to_parabolic

theorem twist_gam : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ → ∀ γ ∈ Gam2 (n := n) ϖ,
      ∃ j' : GL (Ix n) O, inL γ * tauM w = tauM w * inL j' ∧ resK j' = 1 := GlobalTheory.T.level_square_congruence_conjugation

theorem twist_low : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ x : GL (Ix n) (IsLocalRing.ResidueField O), x.1.toBlocks₁₂ = 0 →
      ∃ j j' : GL (Ix n) O, inL j * tauM w = tauM w * inL j' ∧ resK j' = x := GlobalTheory.T.residue_upper_unipotent_lift

theorem red_rank : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ (κ : GL (Ix n) O) (h : GL (Ix n) (IsLocalRing.ResidueField O)), IsRed (O := O) w κ h →
      iD h = (lowerLeftBlock (resK κ)).rank := GlobalTheory.T.reduction_corank_eq_rank_lower_left

theorem dbl : ∀ (k : Type) [Field k] (n : ℕ) (g₁ g₂ : GL (Ix n) k), iD g₁ = iD g₂ →
    ∃ (a d : GL (Fin n) k) (b : Matrix (Fin n) (Fin n) k) (x : GL (Ix n) k),
      x.1.toBlocks₁₂ = 0 ∧ g₂ = pM a d b * g₁ * x := GlobalTheory.T.parabolic_double_coset_of_equal_corank

theorem avg_res : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fintype (IsLocalRing.ResidueField O)]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ f : GL (Ix n) (IsLocalRing.ResidueField O) → ℂ,
      avgK ϖ (fun κ => f (resK κ)) = sumG f / (Nat.card (GL (Ix n) (IsLocalRing.ResidueField O)) : ℂ) := GlobalTheory.T.average_over_maximal_compact_residue

theorem avg_right : ∀ (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) (ϖ : O) (φ : GL (Ix n) O → ℂ),
    (∀ κ, ∀ γ ∈ Gam2 (n := n) ϖ, φ (κ * γ) = φ κ) → ∀ j : GL (Ix n) O,
      avgK ϖ (fun κ => φ (κ * j)) = avgK ϖ φ := GlobalTheory.T.average_invariant_right_translation

theorem cnt_swap : ∀ (k : Type) [Field k] [Fintype k] (n i : ℕ),
    Nat.card {g : GL (Ix n) k // (lowerLeftBlock g).rank = i} = Nat.card {g : GL (Ix n) k // (dBlk g).rank = i} := GlobalTheory.T.card_rank_lower_left_eq_lower_right

theorem cnt_half : ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (D : Matrix (Fin n) (Fin n) k),
    Nat.card {g : GL (Ix n) k // dBlk g = D} =
      Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1} *
        Nat.card {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} := GlobalTheory.T.card_fixed_lower_right_block

theorem cnt_cols : ∀ (k : Type) [Field k] [Fintype k] (n ρ : ℕ) (D : Matrix (Fin n) (Fin n) k), D.rank = ρ →
    Nat.card {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} =
      Fintype.card k ^ (n * ρ) * ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) := GlobalTheory.T.card_completions_to_full_rank

theorem cnt_rank : ∀ (k : Type) [Field k] [Fintype k] (n ρ : ℕ), ρ ≤ n →
    Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = ρ} *
        ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) =
      Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = n - ρ} *
        ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := GlobalTheory.T.card_rank_completion_symmetry

theorem red_mul {O L : Type} [CommRing O] [IsLocalRing O] [Field L] [Algebra O L] {n : ℕ} {w : Lˣ}
    {κ j j' : GL (Ix n) O} {h : GL (Ix n) (IsLocalRing.ResidueField O)} (hr : IsRed (O := O) w κ h)
    (e : inL j * tauM w = tauM w * inL j') : IsRed (O := O) w (κ * j) (h * resK j') := by
  obtain ⟨a, d, b, κ', E, R⟩ := hr
  refine ⟨a, d, b, κ' * j', ?_, ?_⟩
  · rw [map_mul, mul_assoc, e, ← mul_assoc, E, map_mul, mul_assoc]
  · rw [map_mul, R]

theorem iD_mul_low {k : Type} [Field k] {n : ℕ} (g x : GL (Ix n) k) (hx : x.1.toBlocks₁₂ = 0) :
    iD (g * x) = iD g := by
  have hd : dBlk (g * x) = dBlk g * x.1.toBlocks₂₂ := by
    have e : (g * x).1 = fromBlocks g.1.toBlocks₁₁ g.1.toBlocks₁₂ g.1.toBlocks₂₁ g.1.toBlocks₂₂ *
        fromBlocks x.1.toBlocks₁₁ x.1.toBlocks₁₂ x.1.toBlocks₂₁ x.1.toBlocks₂₂ := by
      simp [fromBlocks_toBlocks]
    unfold dBlk
    rw [e, fromBlocks_multiply, toBlocks_fromBlocks₂₂, hx]
    simp
  have hu : IsUnit x.1.toBlocks₂₂.det := by
    have h0 : x.1 = fromBlocks x.1.toBlocks₁₁ 0 x.1.toBlocks₂₁ x.1.toBlocks₂₂ := by
      rw [← hx, fromBlocks_toBlocks]
    have hd : IsUnit x.1.det := (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
    rw [h0, det_fromBlocks_zero₁₂] at hd
    exact isUnit_of_mul_isUnit_right hd
  unfold iD
  rw [hd, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hu]

theorem low_mul {k : Type} [Field k] {n : ℕ} (x y : GL (Ix n) k) (hx : x.1.toBlocks₁₂ = 0) (hy : y.1.toBlocks₁₂ = 0) :
    (x * y).1.toBlocks₁₂ = 0 := by
  have e : (x * y).1 = fromBlocks x.1.toBlocks₁₁ x.1.toBlocks₁₂ x.1.toBlocks₂₁ x.1.toBlocks₂₂ *
      fromBlocks y.1.toBlocks₁₁ y.1.toBlocks₁₂ y.1.toBlocks₂₁ y.1.toBlocks₂₂ := by
    simp [fromBlocks_toBlocks]
  rw [e, fromBlocks_multiply, toBlocks_fromBlocks₁₂, hx, hy]
  simp

theorem avg_lin {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Fintype (IsLocalRing.ResidueField O)]
    {n : ℕ} {ϖ : O} (hϖ : Irreducible ϖ) {ι : Type} (s : Finset ι) (c : ℂ) (F : ι → GL (Ix n) O → ℂ) :
    avgK ϖ (fun κ => c * ∑ x ∈ s, F x κ) = c * ∑ x ∈ s, avgK ϖ (F x) := by
  haveI := Unif.finite_quotient_level_square_congruence n hϖ
  classical
  haveI := Fintype.ofFinite (GL (Ix n) O ⧸ Gam2 (n := n) ϖ)
  unfold avgK
  simp only [finsum_eq_sum_of_fintype, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

theorem sum_fib {G : Type} [Fintype G] (t : G → ℕ) (n : ℕ) (ht : ∀ g, t g ≤ n) (F : ℕ → ℂ) :
    ∑ g, F (t g) = ∑ i ∈ Finset.range (n + 1), (Nat.card {g // t g = i} : ℂ) * F i := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (n + 1)) (g := t)
    (fun x _ => Finset.mem_range.2 (Nat.lt_succ_of_le (ht x)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => F i) (fun x hx => by rw [(Finset.mem_filter.1 hx).2])]
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem card_by_rank {k : Type} [Field k] [Fintype k] (n ρ : ℕ) :
    Nat.card {g : GL (Ix n) k // (dBlk g).rank = ρ} =
      Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = ρ} *
        (Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1} *
          (Fintype.card k ^ (n * ρ) * ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j))) := by
  classical
  let e : {g : GL (Ix n) k // (dBlk g).rank = ρ} ≃
      Σ D : {D : Matrix (Fin n) (Fin n) k // D.rank = ρ}, {g : GL (Ix n) k // dBlk g = D.1} :=
    { toFun := fun g => ⟨⟨dBlk g.1, g.2⟩, ⟨g.1, rfl⟩⟩
      invFun := fun s => ⟨s.2.1, by rw [s.2.2]; exact s.1.2⟩
      left_inv := fun g => rfl
      right_inv := by
        rintro ⟨⟨D, hD⟩, ⟨g, hg⟩⟩
        dsimp only at hg
        subst hg
        rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  rw [Finset.sum_congr rfl (g := fun _ => Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1} *
          (Fintype.card k ^ (n * ρ) * ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j)))
    (fun D _ => by rw [cnt_half, cnt_cols k n ρ D.1 D.2])]
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card]

theorem count {k : Type} [Field k] [Fintype k] (n i : ℕ) (hi : i ≤ n) :
    Nat.card {g : GL (Ix n) k // iD g = i} * Fintype.card k ^ (2 * n * i) =
      Nat.card {g : GL (Ix n) k // (lowerLeftBlock g).rank = i} * Fintype.card k ^ (n * n) := by
  have h1 : Nat.card {g : GL (Ix n) k // iD g = i} = Nat.card {g : GL (Ix n) k // (dBlk g).rank = n - i} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    have : (dBlk g).rank ≤ n := by simpa using (dBlk g).rank_le_card_width
    unfold iD
    omega
  rw [h1, cnt_swap, card_by_rank, card_by_rank]
  have hr := cnt_rank k n i hi
  have e1 : n - (n - i) = i := by omega
  rw [e1]
  have e2 : n * (n - i) + 2 * n * i = n * i + n * n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hi
    simp only [Nat.add_sub_cancel_left]
    ring
  set c := Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1}
  set q := Fintype.card k
  set Ia := ∏ j ∈ Finset.range (n - i), (q ^ n - q ^ j)
  set Ib := ∏ j ∈ Finset.range i, (q ^ n - q ^ j)
  set Ra := Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = i}
  set Rb := Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = n - i}
  calc Rb * (c * (q ^ (n * (n - i)) * Ib)) * q ^ (2 * n * i)
      = (Rb * Ib) * c * q ^ (n * (n - i) + 2 * n * i) := by rw [pow_add]; ring
    _ = (Ra * Ia) * c * q ^ (n * i + n * n) := by rw [hr, e2]
    _ = Ra * (c * (q ^ (n * i) * Ia)) * q ^ (n * n) := by rw [pow_add]; ring

theorem sum_weight {k : Type} [Field k] [Fintype k] (n : ℕ) (f : ℕ → ℂ) :
    sumG (fun g : GL (Ix n) k => (Fintype.card k : ℂ) ^ (2 * n * iD g) * f (iD g)) =
      (Fintype.card k : ℂ) ^ (n * n) * sumG (fun h : GL (Ix n) k => f (lowerLeftBlock h).rank) := by
  classical
  haveI := Fintype.ofFinite (GL (Ix n) k)
  unfold sumG
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have a := sum_fib (iD (k := k) (n := n)) n (fun g => by unfold iD; omega)
    (fun i => (Fintype.card k : ℂ) ^ (2 * n * i) * f i)
  have b := sum_fib (fun h : GL (Ix n) k => (lowerLeftBlock h).rank) n
    (fun g => by simpa using (lowerLeftBlock g).rank_le_card_width) f
  rw [a, b, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have c := count (k := k) n i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  have c' := congrArg (Nat.cast : ℕ → ℂ) c
  push_cast at c'
  linear_combination (f i) * c'

theorem jpCmp : JpCmp := by
  intro O L _ _ _ _ _ _ _ n ϖ hϖ w hw Ψ hΨ T hT
  classical
  haveI := Fintype.ofFinite (GL (Ix n) (IsLocalRing.ResidueField O))
  have hinv : ∀ κ h, IsRed (O := O) w κ h → Ψ h = Ψ (T κ) := by
    intro κ h hr
    obtain ⟨a, d, b, e⟩ := red_unique O L n w κ (T κ) h (hT κ) hr
    rw [e, hΨ]
  have hγ : ∀ κ, ∀ γ ∈ Gam2 (n := n) ϖ, Ψ (T (κ * γ)) = Ψ (T κ) := by
    intro κ γ hg
    obtain ⟨j', e, r⟩ := twist_gam O L n ϖ hϖ w hw γ hg
    have := red_mul (hT κ) e
    rw [r, mul_one] at this
    exact (hinv _ _ this).symm
  have hx : ∀ x : GL (Ix n) (IsLocalRing.ResidueField O), x.1.toBlocks₁₂ = 0 →
      avgK ϖ (fun κ => Ψ (T κ * x)) = avgK ϖ (fun κ => Ψ (T κ)) := by
    intro x hl
    obtain ⟨j, j', e, r⟩ := twist_low O L n ϖ hϖ w hw x hl
    have h1 : (fun κ => Ψ (T κ * x)) = fun κ => Ψ (T (κ * j)) := by
      funext κ
      have := red_mul (hT κ) e
      rw [r] at this
      exact hinv _ _ this
    rw [h1]
    exact avg_right O n ϖ (fun κ => Ψ (T κ)) hγ j
  set Pm : Finset (GL (Ix n) (IsLocalRing.ResidueField O)) := Finset.univ.filter (fun x => x.1.toBlocks₁₂ = 0) with hPm
  have hmem : ∀ x, x ∈ Pm ↔ x.1.toBlocks₁₂ = 0 := by simp [hPm]
  have hN : (Pm.card : ℂ) ≠ 0 := by
    have : (1 : GL (Ix n) (IsLocalRing.ResidueField O)) ∈ Pm := by
      rw [hmem]; simp [← fromBlocks_one]
    exact_mod_cast (Finset.card_pos.2 ⟨_, this⟩).ne'
  let Φ : GL (Ix n) (IsLocalRing.ResidueField O) → ℂ := fun g => (Pm.card : ℂ)⁻¹ * ∑ x ∈ Pm, Ψ (g * x)
  have hΦavg : avgK ϖ (fun κ => Φ (T κ)) = avgK ϖ (fun κ => Ψ (T κ)) := by
    have := avg_lin hϖ Pm (Pm.card : ℂ)⁻¹ (fun x κ => Ψ (T κ * x))
    simp only [Φ]
    rw [this, Finset.sum_congr rfl (fun x h => hx x ((hmem x).1 h))]
    rw [Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hΦ : ∀ g₁ g₂, iD g₁ = iD g₂ → Φ g₂ = Φ g₁ := by
    intro g₁ g₂ e
    obtain ⟨a, d, b, x₀, h0, rfl⟩ := dbl _ n g₁ g₂ e
    simp only [Φ]
    congr 1
    have hinj : Set.InjOn (fun x => x₀ * x) (Pm : Set _) := fun _ _ _ _ h => mul_left_cancel h
    have him : Pm.image (fun x => x₀ * x) = Pm := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro y hy
        obtain ⟨x, hxm, rfl⟩ := Finset.mem_image.1 hy
        exact (hmem _).2 (low_mul _ _ h0 ((hmem _).1 hxm))
      · rw [Finset.card_image_of_injOn hinj]
    conv_rhs => rw [← him]
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc, mul_assoc, hΨ]
  let f : ℕ → ℂ := fun i => if h : ∃ g, iD g = i then Φ h.choose else 0
  have hf : ∀ g, Φ g = f (iD g) := by
    intro g
    have h : ∃ g', iD g' = iD g := ⟨g, rfl⟩
    simp only [f, dif_pos h]
    exact hΦ _ _ h.choose_spec
  have hnum : sumG (fun g => (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Ψ g) =
      sumG (fun g => (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Φ g) := by
    unfold sumG
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    have h1 : ∀ x ∈ Pm, ∑ g, (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Ψ (g * x) =
        ∑ g, (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Ψ g := by
      intro x hxm
      rw [← Equiv.sum_comp (Equiv.mulRight x) (fun g => (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Ψ g)]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [Equiv.coe_mulRight]
      rw [iD_mul_low g x ((hmem x).1 hxm)]
    simp only [Φ]
    have h2 : ∑ g, (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * ((Pm.card : ℂ)⁻¹ * ∑ x ∈ Pm, Ψ (g * x)) =
        (Pm.card : ℂ)⁻¹ * ∑ x ∈ Pm, ∑ g, (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Ψ (g * x) := by
      rw [Finset.sum_comm (s := Pm), Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← Finset.mul_sum]
      ring
    rw [h2, Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hq : ((Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (n * n)) ≠ 0 := by
    have : (Fintype.card (IsLocalRing.ResidueField O)) ≠ 0 := Fintype.card_ne_zero
    exact pow_ne_zero _ (by exact_mod_cast this)
  have hL : avgK ϖ (fun κ => Ψ (T κ)) = sumG (fun h : GL (Ix n) (IsLocalRing.ResidueField O) => f (lowerLeftBlock h).rank) /
      (Nat.card (GL (Ix n) (IsLocalRing.ResidueField O)) : ℂ) := by
    rw [← hΦavg, ← avg_res O n ϖ hϖ (fun h : GL (Ix n) (IsLocalRing.ResidueField O) => f (lowerLeftBlock h).rank)]
    congr 1
    funext κ
    rw [hf, red_rank O L n ϖ hϖ w hw κ _ (hT κ)]
  have hden := sum_weight (k := IsLocalRing.ResidueField O) n (fun _ => 1)
  have hone : sumG (fun _ : GL (Ix n) (IsLocalRing.ResidueField O) => (1 : ℂ)) =
      (Nat.card (GL (Ix n) (IsLocalRing.ResidueField O)) : ℂ) := by
    unfold sumG
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Nat.card_eq_fintype_card]
  simp only [mul_one] at hden
  rw [hL, hnum, hden, hone]
  have hw2 : sumG (fun g => (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * Φ g) =
      sumG (fun g : GL (Ix n) (IsLocalRing.ResidueField O) => (Fintype.card (IsLocalRing.ResidueField O) : ℂ) ^ (2 * n * iD g) * f (iD g)) := by
    unfold sumG
    exact finsum_congr fun g => by beta_reduce; rw [hf]
  rw [hw2, sum_weight]
  field_simp

end GlobalTheory.CompanionTheory.Jp.Cmp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactnessStatementStatement
open GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactness_statement : GlobalTheory.CompanionTheory.Jp.JpCmp := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Cmp.jpCmp | exact GlobalTheory.CompanionTheory.Jp.Cmp.jpCmp | (intros; apply GlobalTheory.CompanionTheory.Jp.Cmp.jpCmp <;> assumption)
end
