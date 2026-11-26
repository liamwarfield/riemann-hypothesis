module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGlNonarchimedean
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaN
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FactorizationBis

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NearIdentityUpperLowerFactorization
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NearIdentityUpperLowerFactorization
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL.IwahoriLU

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}





theorem factor (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    ∀ A : Matrix (Fin n) (Fin n) L, (∀ i j, ‖(A - 1) i j‖ ≤ r) →
      ∃ U W : Matrix (Fin n) (Fin n) L, (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → W i j = 0) ∧
        (∀ i j, ‖(U - 1) i j‖ ≤ r) ∧ (∀ i j, ‖(W - 1) i j‖ ≤ r) ∧ A = U * W :=
  _root_.UpperTheory.Reformulated.B.TriangularFactorizationNearIdentity.factor n r h0 h1

theorem iwahori_factorisation (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r < 1) (A : Matrix (Fin n) (Fin n) L) (hA : ∀ i j, ‖(A - 1) i j‖ ≤ r) :
    ∃ U W : Matrix (Fin n) (Fin n) L, (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → W i j = 0) ∧
      (∀ i j, ‖(U - 1) i j‖ ≤ r) ∧ (∀ i j, ‖(W - 1) i j‖ ≤ r) ∧ A = U * W :=
  factor n r h0 h1 A hA

end GlobalTheory.CompanionTheory.CartGL.IwahoriLU
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NearIdentityUpperLowerFactorizationStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.near_identity_upper_lower_factorization : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ), 0 ≤ r → r < 1 → ∀ A : Matrix (Fin n) (Fin n) L, (∀ i j, ‖(A - 1) i j‖ ≤ r) → ∃ U W : Matrix (Fin n) (Fin n) L, (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → W i j = 0) ∧ (∀ i j, ‖(U - 1) i j‖ ≤ r) ∧ (∀ i j, ‖(W - 1) i j‖ ≤ r) ∧ A = U * W := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.IwahoriLU.iwahori_factorisation | exact GlobalTheory.CompanionTheory.CartGL.IwahoriLU.iwahori_factorisation | (intros; apply GlobalTheory.CompanionTheory.CartGL.IwahoriLU.iwahori_factorisation <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixNearIdentityInCongruenceSubgroup
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixNearIdentityInCongruenceSubgroup
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

section SlopeTestRemainingChoices

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

theorem norm_prod_sub_prod_le {ι : Type} (s : Finset ι) (f g : ι → L) {r : ℝ} (h0 : 0 ≤ r)
    (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1) (hfg : ∀ i, ‖f i - g i‖ ≤ r) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ r :=
  _root_.Bl.FirstLemmaE.goal1 s f g h0 hf hg hfg

theorem norm_det_sub_det_le {A B : Matrix (Fin n) (Fin n) L} {r : ℝ} (h0 : 0 ≤ r)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) (hAB : ∀ i j, ‖(A - B) i j‖ ≤ r) :
    ‖A.det - B.det‖ ≤ r := by
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun σ _ => ?_
  rw [← smul_sub]
  have h := norm_prod_sub_prod_le Finset.univ (fun i => A (σ i) i) (fun i => B (σ i) i) h0
    (fun i => hA _ _) (fun i => hB _ _) (fun i => by simpa using hAB (σ i) i)
  have h' : ‖∏ i, B (σ i) i - ∏ i, A (σ i) i‖ ≤ r := by
    rw [norm_sub_rev]
    exact h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs, Units.smul_def] using h
  · simpa [hs, Units.smul_def] using h'

theorem norm_det_le_one {A : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have h : ‖∏ i, A (σ i) i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hA _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simpa [hs, Units.smul_def] using h

theorem norm_one_entry_le (i j : Fin n) : ‖(1 : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, norm_one]
  · rw [Matrix.one_apply_ne h, norm_zero]
    exact zero_le_one

theorem norm_adjugate_entry_le {A : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, ‖A i j‖ ≤ 1) (i j : Fin n) :
    ‖A.adjugate i j‖ ≤ 1 := by
  rw [Matrix.adjugate_apply]
  refine norm_det_le_one fun a b => ?_
  by_cases h : a = j
  · subst h
    rw [Matrix.updateRow_self]
    by_cases h' : b = i
    · simp [h']
    · simp [Pi.single_eq_of_ne h']
  · rw [Matrix.updateRow_ne h]
    exact hA a b

end SlopeTestRemainingChoices

theorem exists_mem_congK_of_entries : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]
    (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r < 1 → ∀ A : Matrix (Fin n) (Fin n) L,
    (∀ i j, ‖(A - 1) i j‖ ≤ r) →
    ∃ k ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1, (k : Matrix (Fin n) (Fin n) L) = A := by
  intro L _ _ n r h0 h1 hr A hA
  have hA1 : ∀ i j, ‖A i j‖ ≤ 1 := by
    intro i j
    have e : A i j = (A - 1) i j + (1 : Matrix (Fin n) (Fin n) L) i j := by simp
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((hA i j).trans h1) (norm_one_entry_le i j))
  have hd : ‖A.det - 1‖ ≤ r := by
    have := norm_det_sub_det_le h0 hA1 norm_one_entry_le hA
    rwa [Matrix.det_one] at this
  have hd1 : 1 ≤ ‖A.det‖ := by
    have e : (1 : L) = A.det + -(A.det - 1) := by ring
    have h2 : ‖(1 : L)‖ ≤ max ‖A.det‖ ‖A.det - 1‖ := by
      conv_lhs => rw [e]
      rw [← norm_neg (A.det - 1)]
      exact IsUltrametricDist.norm_add_le_max _ _
    rw [norm_one] at h2
    rcases le_max_iff.mp h2 with h | h
    · exact h
    · linarith
  have hne : A.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd1
    linarith
  have hinv : ∀ i j, ‖A⁻¹ i j‖ ≤ 1 := by
    intro i j
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv]
    exact mul_le_one₀ (inv_le_one_of_one_le₀ hd1) (norm_nonneg _) (norm_adjugate_entry_le hA1 i j)
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hne
  have hk : ((Matrix.GeneralLinearGroup.mkOfDetNeZero A hne : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) = A := rfl
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hne, ?_, hk⟩
  rw [mem_congK]
  intro i j
  refine ⟨by rw [hk]; exact hA i j, ?_⟩
  rw [Matrix.coe_units_inv, hk]
  have e : A⁻¹ - 1 = -(A⁻¹ * (A - 1)) := by
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul A hu, Matrix.mul_one]
    abel
  rw [e, Matrix.neg_apply, norm_neg]
  simpa using entry_mul zero_le_one h0 hinv hA i j

end GlobalTheory.CompanionTheory.CartGL
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MatrixNearIdentityInCongruenceSubgroupStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_near_identity_in_congruence_subgroup : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r < 1 → ∀ A : Matrix (Fin n) (Fin n) L, (∀ i j, ‖(A - 1) i j‖ ≤ r) → ∃ k ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1, (k : Matrix (Fin n) (Fin n) L) = A := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries | exact GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries | (intros; apply GlobalTheory.CompanionTheory.CartGL.exists_mem_congK_of_entries <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupNormalInMaximalCompact
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupNormalInMaximalCompact
open Matrix

namespace GlobalTheory.CompanionTheory.CartGL.Normal

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

theorem entry_le_one {A : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, ‖(A - 1) i j‖ ≤ 1) (i j : Fin n) :
    ‖A i j‖ ≤ 1 := by
  have e : A i j = (A - 1) i j + (1 : Matrix (Fin n) (Fin n) L) i j := by simp
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA i j) ?_)
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, norm_one]
  · rw [Matrix.one_apply_ne h, norm_zero]
    exact zero_le_one

theorem entry_conj {C D X : Matrix (Fin n) (Fin n) L} {r : ℝ} (h0 : 0 ≤ r)
    (hC : ∀ i j, ‖C i j‖ ≤ 1) (hD : ∀ i j, ‖D i j‖ ≤ 1) (hCD : C * D = 1)
    (hX : ∀ i j, ‖(X - 1) i j‖ ≤ r) (i j : Fin n) : ‖(C * X * D - 1) i j‖ ≤ r := by
  have e : C * X * D - 1 = C * (X - 1) * D := by
    rw [mul_sub, sub_mul, mul_one, hCD]
  rw [e]
  have h := entry_mul (mul_nonneg zero_le_one h0) zero_le_one
    (entry_mul zero_le_one h0 hC hX) hD i j
  simpa using h

theorem conj_mem_congK (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r ≤ 1) (c x : GL (Fin n) L)
    (hc : c ∈ GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl)
    (hx : x ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1) :
    c * x * c⁻¹ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
  have hC : ∀ i j, ‖((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 :=
    entry_le_one fun i j => (hc i j).1
  have hD : ∀ i j, ‖(((c⁻¹ : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 :=
    entry_le_one fun i j => (hc i j).2
  have hCD : ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((c⁻¹ : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  intro i j
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact entry_conj h0 hC hD hCD (fun i j => (hx i j).1) i j
  · have e : (c * x * c⁻¹)⁻¹ = c * x⁻¹ * c⁻¹ := by group
    rw [e, Units.val_mul, Units.val_mul]
    exact entry_conj h0 hC hD hCD (fun i j => (hx i j).2) i j

end GlobalTheory.CompanionTheory.CartGL.Normal
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupNormalInMaximalCompactStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (c x : GL (Fin n) L), c ∈ GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl → x ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 → c * x * c⁻¹ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.Normal.conj_mem_congK | exact GlobalTheory.CompanionTheory.CartGL.Normal.conj_mem_congK | (intros; apply GlobalTheory.CompanionTheory.CartGL.Normal.conj_mem_congK <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesUpperCongruence
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesUpperCongruence
open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem conj_upper_contract : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ), ‖(p : L)‖ < 1 → ∀ (a : Fin n → ℤ), Antitone a → ∀ (r : ℝ) (u : GL (Fin n) L), (∀ i j, j < i → (u : Matrix (Fin n) (Fin n) L) i j = 0) → (∀ i j, ‖((u : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r) → ∀ i j, ‖(((GlobalTheory.CompanionTheory.CartGL.dPow p a * u * (GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := by
  intro L _ _ n p hp a ha r u hlow hr i j
  have hinv : (((dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      diagonal fun i => ((p ^ (-a i) : Lˣ) : L) := rfl
  have hent : ((dPow p a * u * (dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      ((p ^ (a i - a j) : Lˣ) : L) * (u : Matrix (Fin n) (Fin n) L) i j := by
    rw [Units.val_mul, Units.val_mul, dPow_val, hinv, Matrix.mul_diagonal, Matrix.diagonal_mul,
      sub_eq_add_neg, _root_.zpow_add, Units.val_mul]
    ring
  rw [Matrix.sub_apply, hent]
  have hri := hr i j
  rw [Matrix.sub_apply] at hri
  rcases lt_trichotomy i j with hij | hij | hij
  · have hne : i ≠ j := ne_of_lt hij
    rw [Matrix.one_apply_ne hne] at hri ⊢
    rw [sub_zero] at hri ⊢
    have hexp : 0 ≤ a i - a j := sub_nonneg.mpr (ha hij.le)
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hexp
    have hpow : ‖((p ^ (a i - a j) : Lˣ) : L)‖ ≤ 1 := by
      rw [hm, zpow_natCast, Units.val_pow_eq_pow_val, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hp.le
    rw [norm_mul]
    calc _ ≤ 1 * ‖(u : Matrix (Fin n) (Fin n) L) i j‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = _ := one_mul _
      _ ≤ r := hri
  · subst hij
    simpa using hri
  · rw [hlow i j hij, mul_zero]
    rw [hlow i j hij] at hri
    exact hri

end GlobalTheory.CompanionTheory.CartGL
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesUpperCongruenceStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_conjugation_preserves_upper_congruence : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ), ‖(p : L)‖ < 1 → ∀ (a : Fin n → ℤ), Antitone a → ∀ (r : ℝ) (u : GL (Fin n) L), (∀ i j, j < i → (u : Matrix (Fin n) (Fin n) L) i j = 0) → (∀ i j, ‖((u : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r) → ∀ i j, ‖(((GlobalTheory.CompanionTheory.CartGL.dPow p a * u * (GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.conj_upper_contract | exact GlobalTheory.CompanionTheory.CartGL.conj_upper_contract | (intros; apply GlobalTheory.CompanionTheory.CartGL.conj_upper_contract <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantMonoidElementsAreAntitonePowers
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantMonoidElementsAreAntitonePowers
open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem tExp_antitone (n : ℕ) (i : Fin (n + 2)) : Antitone (tExp n i) := by
  intro j k hjk
  have hjk' : (j : ℕ) ≤ (k : ℕ) := hjk
  unfold tExp
  by_cases h : (i : ℕ) = n + 1
  · simp [h]
  · simp only [h, if_false]
    by_cases hk : (k : ℕ) < i
    · have hj : (j : ℕ) < i := lt_of_le_of_lt hjk' hk
      simp [hj, hk]
    · by_cases hj : (j : ℕ) < i <;> simp [hj, hk]

theorem closure_tGen_antitone (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ)
    (p : Lˣ) (s : GL (Fin n) L)
    (hs : s ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L))) :
    ∃ a : Fin n → ℤ, Antitone a ∧ s = dPow p a := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨tExp n i, tExp_antitone n i, rfl⟩
  | one => exact ⟨0, fun _ _ _ => le_rfl, (dPow_zero p).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, ha.add hb, (dPow_add p a b).symm⟩

end GlobalTheory.CompanionTheory.CartGL
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantMonoidElementsAreAntitonePowersStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_monoid_elements_are_antitone_powers : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ) (s : GL (Fin n) L), s ∈ Submonoid.closure (Set.range (GlobalTheory.CompanionTheory.CartGL.tGen p : Fin (n + 2) → GL (Fin n) L)) → ∃ a : Fin n → ℤ, Antitone a ∧ s = GlobalTheory.CompanionTheory.CartGL.dPow p a := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.closure_tGen_antitone | exact GlobalTheory.CompanionTheory.CartGL.closure_tGen_antitone | (intros; apply GlobalTheory.CompanionTheory.CartGL.closure_tGen_antitone <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUniformizerNonarchimedean
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUniformizerNonarchimedean
open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem exists_isUnif : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L],
    ∃ p : Lˣ, GlobalTheory.CompanionTheory.CartGL.IsUnif p := by
  intro L _ _ _
  obtain ⟨x₀, h0, h1⟩ := NormedField.exists_norm_lt_one L
  have hc : IsCompact (Metric.ball (0 : L) 1) :=
    Metric.isCompact_of_isClosed_isBounded (IsUltrametricDist.isClosed_ball 0 1) Metric.isBounded_ball
  have hx : x₀ ∈ Metric.ball (0 : L) 1 := by simpa using h1
  obtain ⟨p, hp, hmax⟩ := hc.exists_isMaxOn ⟨x₀, hx⟩ continuous_norm.continuousOn
  have hmax' : ∀ w : L, ‖w‖ < 1 → ‖w‖ ≤ ‖p‖ := fun w hw =>
    isMaxOn_iff.mp hmax w (by simpa using hw)
  have hp1 : ‖p‖ < 1 := by simpa using hp
  have hp0 : 0 < ‖p‖ := h0.trans_le (hmax' x₀ h1)
  have hpne : p ≠ 0 := norm_pos_iff.mp hp0
  refine ⟨Units.mk0 p hpne, hp1, fun x hx0 => ?_⟩
  rw [Units.val_mk0]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hy : 1 < ‖p‖⁻¹ := (one_lt_inv₀ hp0).mpr hp1
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hxpos hy
  have hyn : 0 < ‖p‖⁻¹ ^ n := zpow_pos (inv_pos.mpr hp0) n
  set w : L := p ^ (-n) * x⁻¹ with hw
  have hwn : ‖w‖ = ‖p‖⁻¹ ^ n / ‖x‖ := by
    rw [hw, norm_mul, norm_inv, norm_zpow, _root_.inv_zpow', div_eq_mul_inv]
  have hle : ‖w‖ ≤ 1 := by
    rw [hwn]; exact (div_le_one hxpos).mpr hn1
  have hgt : ‖p‖ < ‖w‖ := by
    rw [hwn, lt_div_iff₀ hxpos]
    have : ‖x‖ < ‖p‖⁻¹ ^ n * ‖p‖⁻¹ := by rwa [zpow_add_one₀ (inv_pos.mpr hp0).ne'] at hn2
    calc ‖p‖ * ‖x‖ < ‖p‖ * (‖p‖⁻¹ ^ n * ‖p‖⁻¹) := mul_lt_mul_of_pos_left this hp0
      _ = ‖p‖⁻¹ ^ n := by field_simp
  have heq : ‖w‖ = 1 := by
    by_contra hne
    exact absurd (hmax' w (lt_of_le_of_ne hle hne)) (not_le.mpr hgt)
  refine ⟨-n, ?_⟩
  rw [hwn, div_eq_one_iff_eq hxpos.ne'] at heq
  rw [← heq, _root_.inv_zpow']

end GlobalTheory.CompanionTheory.CartGL
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUniformizerNonarchimedeanStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformizer_nonarchimedean : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L], ∃ p : Lˣ, GlobalTheory.CompanionTheory.CartGL.IsUnif p := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.exists_isUnif | exact GlobalTheory.CompanionTheory.CartGL.exists_isUnif | (intros; apply GlobalTheory.CompanionTheory.CartGL.exists_isUnif <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesLowerCongruence
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesLowerCongruence
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL.Lower

theorem conj_entry {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}
    (p : Lˣ) (a : Fin n → ℤ) (w : GL (Fin n) L) (i j : Fin n) :
    (((GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ * w * GlobalTheory.CompanionTheory.CartGL.dPow p a : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) i j =
      ((p ^ (-a i) : Lˣ) : L) * (w : Matrix (Fin n) (Fin n) L) i j * ((p ^ a j : Lˣ) : L) := by
  have h : (((GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      diagonal fun i => ((p ^ (-a i) : Lˣ) : L) := rfl
  rw [Units.val_mul, Units.val_mul, h, GlobalTheory.CompanionTheory.CartGL.dPow_val, mul_diagonal, diagonal_mul]

theorem norm_conj_le {L : Type} [NontriviallyNormedField L] (p : Lˣ) (hp : ‖(p : L)‖ < 1)
    {b c : ℤ} (hbc : b ≤ c) (x : L) :
    ‖((p ^ (-b) : Lˣ) : L) * x * ((p ^ c : Lˣ) : L)‖ ≤ ‖x‖ := by
  have hp0 : (0 : ℝ) < ‖(p : L)‖ := norm_pos_iff.mpr p.ne_zero
  obtain ⟨m, hm⟩ : ∃ m : ℕ, c = b + m := ⟨(c - b).toNat, by omega⟩
  have e : ‖((p ^ (-b) : Lˣ) : L) * x * ((p ^ c : Lˣ) : L)‖ = ‖x‖ * ‖(p : L)‖ ^ m := by
    rw [norm_mul, norm_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, norm_zpow,
      norm_zpow, hm, zpow_add₀ hp0.ne', _root_.zpow_neg, zpow_natCast]
    have : ‖(p : L)‖ ^ b ≠ 0 := (zpow_pos hp0 b).ne'
    field_simp
  rw [e]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hp0.le hp.le)

theorem conj_lower_contract : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ), ‖(p : L)‖ < 1 → ∀ (a : Fin n → ℤ), Antitone a → ∀ (r : ℝ) (w : GL (Fin n) L), (∀ i j, i < j → (w : Matrix (Fin n) (Fin n) L) i j = 0) → (∀ i j, ‖((w : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r) → ∀ i j, ‖((((GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ * w * GlobalTheory.CompanionTheory.CartGL.dPow p a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := by
  intro L _ _ n p hp a ha r w hl hr i j
  rw [Matrix.sub_apply, conj_entry]
  rcases lt_trichotomy i j with h | h | h
  · have h0 := hr i j
    rw [Matrix.sub_apply, hl i j h, Matrix.one_apply_ne h.ne] at h0
    rw [hl i j h, Matrix.one_apply_ne h.ne]
    simpa using h0
  · subst h
    have hne : ((p ^ (-a i) : Lˣ) : L) * ((p ^ a i : Lˣ) : L) = 1 := by
      rw [← Units.val_mul, _root_.zpow_neg, inv_mul_cancel, Units.val_one]
    have e : ((p ^ (-a i) : Lˣ) : L) * (w : Matrix (Fin n) (Fin n) L) i i * ((p ^ a i : Lˣ) : L) =
        (w : Matrix (Fin n) (Fin n) L) i i := by
      rw [mul_right_comm, hne, one_mul]
    rw [e]
    simpa [Matrix.sub_apply] using hr i i
  · have h0 := hr i j
    rw [Matrix.sub_apply, Matrix.one_apply_ne h.ne', sub_zero] at h0
    rw [Matrix.one_apply_ne h.ne', sub_zero]
    exact (norm_conj_le p hp (ha h.le) _).trans h0

end GlobalTheory.CompanionTheory.CartGL.Lower
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesLowerCongruenceStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_conjugation_preserves_lower_congruence : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ), ‖(p : L)‖ < 1 → ∀ (a : Fin n → ℤ), Antitone a → ∀ (r : ℝ) (w : GL (Fin n) L), (∀ i j, i < j → (w : Matrix (Fin n) (Fin n) L) i j = 0) → (∀ i j, ‖((w : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r) → ∀ i j, ‖((((GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ * w * GlobalTheory.CompanionTheory.CartGL.dPow p a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.Lower.conj_lower_contract | exact GlobalTheory.CompanionTheory.CartGL.Lower.conj_lower_contract | (intros; apply GlobalTheory.CompanionTheory.CartGL.Lower.conj_lower_contract <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsOpen
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsOpen
open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem isOpen_congK : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r ≤ 1), 0 < r →
    IsOpen (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) := by
  intro L _ _ n r h0 h1 hr
  have hball : IsOpen (Metric.closedBall (0 : L) r) :=
    IsUltrametricDist.isOpen_closedBall _ hr.ne'
  have hval : Continuous fun k : GL (Fin n) L => (k : Matrix (Fin n) (Fin n) L) :=
    Units.continuous_val
  have hinv : Continuous fun k : GL (Fin n) L => ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) :=
    Units.continuous_val.comp continuous_inv
  have hset : (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) =
      ⋂ i : Fin n, ⋂ j : Fin n,
        ((fun k : GL (Fin n) L => ((k : Matrix (Fin n) (Fin n) L) - 1) i j) ⁻¹'
            Metric.closedBall (0 : L) r ∩
          (fun k : GL (Fin n) L =>
            (((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j) ⁻¹'
            Metric.closedBall (0 : L) r) := by
    ext k
    simp only [SetLike.mem_coe, mem_congK, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage,
      mem_closedBall_zero_iff]
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
  · refine hball.preimage ?_
    exact (continuous_apply_apply i j).comp (hval.sub continuous_const)
  · refine hball.preimage ?_
    exact (continuous_apply_apply i j).comp (hinv.sub continuous_const)

end GlobalTheory.CompanionTheory.CartGL
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsOpenStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_subgroup_is_open : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), 0 < r → IsOpen (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.isOpen_congK | exact GlobalTheory.CompanionTheory.CartGL.isOpen_congK | (intros; apply GlobalTheory.CompanionTheory.CartGL.isOpen_congK <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupsNeighborhoodBasis
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupsNeighborhoodBasis
open Matrix Topology

namespace GlobalTheory.CompanionTheory.CartGL

theorem exists_pi_entry_box {L : Type} [NontriviallyNormedField L] {n : ℕ}
    {A : Set (Fin n → Fin n → L)} {x : Fin n → Fin n → L} (hA : A ∈ 𝓝 x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : Fin n → Fin n → L, (∀ i j, ‖y i j - x i j‖ ≤ ε) → y ∈ A := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hA
  refine ⟨ε / 2, half_pos hε, fun y hy => hball ?_⟩
  have hd : dist y x ≤ ε / 2 := by
    rw [dist_pi_le_iff (half_pos hε).le]
    intro i
    rw [dist_pi_le_iff (half_pos hε).le]
    intro j
    rw [dist_eq_norm]
    exact hy i j
  rw [Metric.mem_ball]
  linarith

theorem exists_entry_box {L : Type} [NontriviallyNormedField L] {n : ℕ}
    {A : Set (Matrix (Fin n) (Fin n) L)} (hA : A ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) L)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ M : Matrix (Fin n) (Fin n) L,
      (∀ i j, ‖(M - 1) i j‖ ≤ ε) → M ∈ A := by
  obtain ⟨ε, hε, h⟩ := exists_pi_entry_box (x := (1 : Matrix (Fin n) (Fin n) L)) hA
  refine ⟨ε, hε, fun M hM => h M fun i j => ?_⟩
  have := hM i j
  rwa [Matrix.sub_apply] at this

theorem congK_cofinal (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ)
    (U : Set (GL (Fin n) L)) (hU : IsOpen U) (h1U : (1 : GL (Fin n) L) ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r ≤ ε →
      (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) ⊆ U := by
  have hU1 : U ∈ 𝓝 (1 : GL (Fin n) L) := hU.mem_nhds h1U
  rw [Units.isEmbedding_embedProduct.nhds_eq_comap, Filter.mem_comap, map_one] at hU1
  obtain ⟨V, hV, hVU⟩ := hU1
  obtain ⟨A, hA, B, hB, hAB⟩ :=
    (mem_nhds_prod_iff (x := (1 : Matrix (Fin n) (Fin n) L)) (y := MulOpposite.op 1)).1 hV
  have hB' : MulOpposite.op ⁻¹' B ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) L) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_entry_box hA
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_entry_box hB'
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun r h0 h1 hr k hk => hVU (hAB ⟨?_, ?_⟩)⟩
  · exact h₁ _ fun i j => ((hk i j).1.trans hr).trans (min_le_left _ _)
  · exact h₂ _ fun i j => ((hk i j).2.trans hr).trans (min_le_right _ _)

end GlobalTheory.CompanionTheory.CartGL
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupsNeighborhoodBasisStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_subgroups_neighborhood_basis : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (U : Set (GL (Fin n) L)), IsOpen U → (1 : GL (Fin n) L) ∈ U → ∃ ε : ℝ, 0 < ε ∧ ∀ (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r ≤ ε → (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) ⊆ U := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.congK_cofinal | exact GlobalTheory.CompanionTheory.CartGL.congK_cofinal | (intros; apply GlobalTheory.CompanionTheory.CartGL.congK_cofinal <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntitonePowersInDominantMonoid
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntitonePowersInDominantMonoid
open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

theorem exists_tExp_eq_indicator (b : Fin n → ℤ) (hb : Antitone b) :
    ∃ i : Fin (n + 2), tExp n i = fun j => if 0 < b j then 1 else 0 := by
  classical
  have hex : ∃ i : ℕ, i = n ∨ ∃ h : i < n, b ⟨i, h⟩ ≤ 0 := ⟨n, Or.inl rfl⟩
  have hle : Nat.find hex ≤ n := Nat.find_min' hex (Or.inl rfl)
  refine ⟨⟨Nat.find hex, by omega⟩, ?_⟩
  funext j
  have hne : Nat.find hex ≠ n + 1 := by omega
  simp only [tExp, hne, if_false]
  by_cases hj : (j : ℕ) < Nat.find hex
  · have hnot := Nat.find_min hex hj
    have hpos : 0 < b j := by
      by_contra hcon
      exact hnot (Or.inr ⟨j.2, not_lt.mp hcon⟩)
    rw [if_pos hj, if_pos hpos]
  · have hspec := Nat.find_spec hex
    have hnpos : ¬ 0 < b j := by
      rcases hspec with h | ⟨h, h'⟩
      · have := j.2
        omega
      · have hmono : b j ≤ b ⟨Nat.find hex, h⟩ := hb (by
          rw [Fin.le_def]
          exact not_lt.mp hj)
        omega
    rw [if_neg hj, if_neg hnpos]

theorem dPow_mem_closure_of_nonneg (p : Lˣ) (N : ℕ) :
    ∀ b : Fin n → ℤ, Antitone b → (∀ j, 0 ≤ b j) → (∀ j, b j ≤ N) →
      dPow p b ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  induction N with
  | zero =>
    intro b _ h0 hN
    have hb : b = 0 := by
      funext j
      have h1 := h0 j
      have h2 := hN j
      simp only [Nat.cast_zero] at h2
      simp only [Pi.zero_apply]
      omega
    rw [hb, dPow_zero]
    exact Submonoid.one_mem _
  | succ N ih =>
    intro b hb h0 hN
    obtain ⟨i, hi⟩ := exists_tExp_eq_indicator b hb
    have hdecomp : b = (fun j => b j - if 0 < b j then 1 else 0) + tExp n i := by
      rw [hi]
      funext j
      simp
    rw [hdecomp, dPow_add]
    refine Submonoid.mul_mem _ (ih _ ?_ ?_ ?_) (Submonoid.subset_closure ⟨i, rfl⟩)
    · intro x y hxy
      have hm := hb hxy
      have hx := h0 x
      have hy := h0 y
      show (b y - if 0 < b y then 1 else 0) ≤ (b x - if 0 < b x then 1 else 0)
      split_ifs <;> omega
    · intro j
      have h1 := h0 j
      show 0 ≤ (b j - if 0 < b j then 1 else 0)
      split_ifs <;> omega
    · intro j
      have h1 := h0 j
      have h2 := hN j
      push_cast at h2
      show (b j - if 0 < b j then 1 else 0) ≤ (N : ℤ)
      split_ifs <;> omega

theorem dPow_mem_closure_of_ge (p : Lˣ) (C : ℕ) :
    ∀ a : Fin n → ℤ, Antitone a → (∀ j, -(C : ℤ) ≤ a j) →
      dPow p a ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  induction C with
  | zero =>
    intro a ha h0
    have hbd : ∀ j, a j ≤ ((∑ k, (a k).natAbs : ℕ) : ℤ) := by
      intro j
      have h1 : (a j).natAbs ≤ ∑ k, (a k).natAbs :=
        Finset.single_le_sum (f := fun k => (a k).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
      omega
    refine dPow_mem_closure_of_nonneg p _ a ha (fun j => ?_) hbd
    have := h0 j
    simpa using this
  | succ C ih =>
    intro a ha h0
    have hlast : tExp n (Fin.last (n + 1)) = fun _ => -1 := by
      funext j
      simp [tExp]
    have hdecomp : a = (fun j => a j + 1) + tExp n (Fin.last (n + 1)) := by
      rw [hlast]
      funext j
      simp
    rw [hdecomp, dPow_add]
    refine Submonoid.mul_mem _ (ih _ ?_ ?_)
      (Submonoid.subset_closure ⟨Fin.last (n + 1), rfl⟩)
    · intro x y hxy
      have := ha hxy
      show a y + 1 ≤ a x + 1
      omega
    · intro j
      have := h0 j
      push_cast at this
      show -(C : ℤ) ≤ a j + 1
      omega

theorem dPow_antitone_mem_closure (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]
    (n : ℕ) (p : Lˣ) (a : Fin n → ℤ) (ha : Antitone a) :
    dPow p a ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  refine dPow_mem_closure_of_ge p (∑ k, (a k).natAbs) a ha (fun j => ?_)
  have h1 : (a j).natAbs ≤ ∑ k, (a k).natAbs :=
    Finset.single_le_sum (f := fun k => (a k).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
  omega

end GlobalTheory.CompanionTheory.CartGL
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntitonePowersInDominantMonoidStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antitone_powers_in_dominant_monoid : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ) (a : Fin n → ℤ), Antitone a → GlobalTheory.CompanionTheory.CartGL.dPow p a ∈ Submonoid.closure (Set.range (GlobalTheory.CompanionTheory.CartGL.tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.dPow_antitone_mem_closure | exact GlobalTheory.CompanionTheory.CartGL.dPow_antitone_mem_closure | (intros; apply GlobalTheory.CompanionTheory.CartGL.dPow_antitone_mem_closure <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsCompact
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsCompact
open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem isCompact_entryBall (L : Type) [NontriviallyNormedField L] [ProperSpace L] (n : ℕ) (r : ℝ) :
    IsCompact {M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r} := by
  have h : IsCompact (Set.univ.pi fun i : Fin n => Set.univ.pi fun j : Fin n =>
      Metric.closedBall ((1 : Matrix (Fin n) (Fin n) L) i j) r) :=
    isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _
  have e : {M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r} =
      (Set.univ.pi fun i : Fin n => Set.univ.pi fun j : Fin n =>
        Metric.closedBall ((1 : Matrix (Fin n) (Fin n) L) i j) r) := by
    ext M
    constructor
    · intro hM i _ j _
      have := hM i j
      rw [Matrix.sub_apply] at this
      exact mem_closedBall_iff_norm.2 this
    · intro hM i j
      have := mem_closedBall_iff_norm.1 (hM i (Set.mem_univ _) j (Set.mem_univ _))
      rw [Matrix.sub_apply]
      exact this
  rw [e]
  exact h

theorem isCompact_congK (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L]
    (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    IsCompact (congK L n r h0 h1 : Set (GL (Fin n) L)) := by
  have hS := isCompact_entryBall L n r
  have hS' := hS.image MulOpposite.continuous_op
  have h := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hS.prod hS')
  have e : (congK L n r h0 h1 : Set (GL (Fin n) L)) =
      Units.embedProduct (Matrix (Fin n) (Fin n) L) ⁻¹'
        ({M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r} ×ˢ
          (MulOpposite.op '' {M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r})) := by
    ext k
    simp only [SetLike.mem_coe, mem_congK, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply,
      Set.mem_image, Set.mem_setOf_eq, MulOpposite.op_inj, exists_eq_right]
    exact ⟨fun hk => ⟨fun i j => (hk i j).1, fun i j => (hk i j).2⟩,
      fun hk i j => ⟨hk.1 i j, hk.2 i j⟩⟩
  rw [e]
  exact h

end GlobalTheory.CompanionTheory.CartGL
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsCompactStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_subgroup_is_compact : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), IsCompact (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.isCompact_congK | exact GlobalTheory.CompanionTheory.CartGL.isCompact_congK | (intros; apply GlobalTheory.CompanionTheory.CartGL.isCompact_congK <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CompactSubgroupFiniteOpenCosets
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CompactSubgroupFiniteOpenCosets
namespace GlobalTheory.CompanionTheory.CosetCover

theorem exists_finite_coset_cover :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K₀ K : Subgroup G),
      IsCompact (K₀ : Set G) → IsOpen (K : Set G) →
        ∃ (d : ℕ) (c : Fin d → G), (∀ i, c i ∈ K₀) ∧ ∀ g ∈ K₀, ∃ i, ∃ κ ∈ K, g = κ * c i := by
  intro G _ _ _ K₀ K hK₀ hK
  classical
  obtain ⟨t, ht⟩ := hK₀.elim_finite_subcover
    (fun g : K₀ => (fun x => x * (g : G)⁻¹) ⁻¹' (K : Set G))
    (fun g => hK.preimage (continuous_mul_const _))
    (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩, by simp⟩)
  refine ⟨t.card, fun i => ((t.equivFin.symm i : K₀) : G), fun i => (t.equivFin.symm i : K₀).2,
    fun g hg => ?_⟩
  obtain ⟨a, ha, hga⟩ := Set.mem_iUnion₂.1 (ht hg)
  refine ⟨t.equivFin ⟨a, ha⟩, g * (a : G)⁻¹, hga, ?_⟩
  simp

end GlobalTheory.CompanionTheory.CosetCover
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CompactSubgroupFiniteOpenCosetsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_subgroup_finite_open_cosets : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K₀ K : Subgroup G), IsCompact (K₀ : Set G) → IsOpen (K : Set G) → ∃ (d : ℕ) (c : Fin d → G), (∀ i, c i ∈ K₀) ∧ ∀ g ∈ K₀, ∃ i, ∃ κ ∈ K, g = κ * c i := by
  first | exact @GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover | exact GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover | (intros; apply GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGL
open CompanionTheory.Rg.Fl Matrix
namespace GlobalTheory.CompanionTheory.CartGL

theorem stCartanGL : StCartanGL := by
  unfold CompanionTheory.Rg.Fl.StCartanGL CompanionTheory.Rg.Fl.HasCartan
  intro L _ _ _ n U hU
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_uniformizer_nonarchimedean L
  have hp1 : ‖(p : L)‖ < 1 := by
    unfold GlobalTheory.CompanionTheory.CartGL.IsUnif at hp
    exact hp.1
  obtain ⟨ε, hε, hεU⟩ := GlobalTheory.T.congruence_subgroups_neighborhood_basis L n (U : Set (GL (Fin n) L)) hU U.one_mem
  obtain ⟨r, hr0, hr1, hrε⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ r ≤ ε :=
    ⟨min ε (1 / 2), lt_min hε (by norm_num), lt_of_le_of_lt (min_le_right _ _) (by norm_num), min_le_left _ _⟩
  have h0 : 0 ≤ r := hr0.le
  have h1 : r ≤ 1 := hr1.le
  refine ⟨GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1, fun x hx => hεU r h0 h1 hrε hx,
    GlobalTheory.T.congruence_subgroup_is_open L n r h0 h1 hr0, GlobalTheory.T.congruence_subgroup_is_compact L n r h0 h1, ?_⟩
  obtain ⟨d, c, hc, hcK⟩ := GlobalTheory.T.compact_subgroup_finite_open_cosets (GL (Fin n) L) (GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl)
    (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1) (GlobalTheory.T.congruence_subgroup_is_compact L n 1 zero_le_one le_rfl) (GlobalTheory.T.congruence_subgroup_is_open L n r h0 h1 hr0)
  refine ⟨d, n + 2, ?_⟩
  unfold CompanionTheory.Rg.Fl.IsCartan
  refine ⟨c, GlobalTheory.CompanionTheory.CartGL.tGen p, ?_, ?_, ?_, ?_⟩
  · intro i k
    constructor
    · intro hk
      exact GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact L n r h0 h1 (c i) k (hc i) hk
    · intro hk
      have h2 := GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact L n r h0 h1 (c i)⁻¹ _ (Subgroup.inv_mem _ (hc i)) hk
      have e : (c i)⁻¹ * (c i * k * (c i)⁻¹) * (c i)⁻¹⁻¹ = k := by group
      rwa [e] at h2
  · intro i j
    show GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n i) * GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n j) =
      GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n j) * GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n i)
    rw [← GlobalTheory.CompanionTheory.CartGL.dPow_add, ← GlobalTheory.CompanionTheory.CartGL.dPow_add, add_comm]
  · intro g
    obtain ⟨a, ha, k₁, hk₁, k₂, hk₂, rfl⟩ := GlobalTheory.T.cartan_decomposition_gl_nonarchimedean L n p hp g
    obtain ⟨i, κ₁, hκ₁, rfl⟩ := hcK k₁ hk₁
    obtain ⟨j, κ₂, hκ₂, rfl⟩ := hcK k₂ hk₂
    refine ⟨i, j, GlobalTheory.CompanionTheory.CartGL.dPow p a, GlobalTheory.T.antitone_powers_in_dominant_monoid L n p a ha, κ₁, hκ₁, (c j)⁻¹ * κ₂ * c j, ?_, ?_⟩
    · have h2 := GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact L n r h0 h1 (c j)⁻¹ κ₂ (Subgroup.inv_mem _ (hc j)) hκ₂
      rwa [inv_inv] at h2
    · group
  · intro s hs s' hs' k hk
    obtain ⟨a₁, ha₁, rfl⟩ := GlobalTheory.T.dominant_monoid_elements_are_antitone_powers L n p s hs
    obtain ⟨a₂, ha₂, rfl⟩ := GlobalTheory.T.dominant_monoid_elements_are_antitone_powers L n p s' hs'
    have hkA : ∀ i j, ‖((k : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := fun i j =>
      (GlobalTheory.CompanionTheory.CartGL.mem_congK.mp hk i j).1
    obtain ⟨Um, Wm, hUl, hWu, hUr, hWr, hUW⟩ := GlobalTheory.T.near_identity_upper_lower_factorization L n r h0 hr1 (k : Matrix (Fin n) (Fin n) L) hkA
    obtain ⟨kU, -, hkUv⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 Um hUr
    obtain ⟨kW, -, hkWv⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 Wm hWr
    have hk_eq : k = kU * kW := Units.ext (by rw [Units.val_mul, hkUv, hkWv, hUW])
    have hA : GlobalTheory.CompanionTheory.CartGL.dPow p a₁ * kU * (GlobalTheory.CompanionTheory.CartGL.dPow p a₁)⁻¹ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
      have hb := GlobalTheory.T.dominant_conjugation_preserves_upper_congruence L n p hp1 a₁ ha₁ r kU (fun i j hij => by rw [hkUv]; exact hUl i j hij)
        (fun i j => by rw [hkUv]; exact hUr i j)
      obtain ⟨k', hk', hk'v⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 _ hb
      rw [← Units.ext hk'v]
      exact hk'
    have hB : (GlobalTheory.CompanionTheory.CartGL.dPow p a₂)⁻¹ * kW * GlobalTheory.CompanionTheory.CartGL.dPow p a₂ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
      have hb := GlobalTheory.T.dominant_conjugation_preserves_lower_congruence L n p hp1 a₂ ha₂ r kW (fun i j hij => by rw [hkWv]; exact hWu i j hij)
        (fun i j => by rw [hkWv]; exact hWr i j)
      obtain ⟨k', hk', hk'v⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 _ hb
      rw [← Units.ext hk'v]
      exact hk'
    refine ⟨_, hA, _, hB, ?_⟩
    rw [hk_eq]
    group

end GlobalTheory.CompanionTheory.CartGL
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGLStatement
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CartanDecompositionGL : StCartanGL := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.stCartanGL | exact GlobalTheory.CompanionTheory.CartGL.stCartanGL | (intros; apply GlobalTheory.CompanionTheory.CartGL.stCartanGL <;> assumption)
end
