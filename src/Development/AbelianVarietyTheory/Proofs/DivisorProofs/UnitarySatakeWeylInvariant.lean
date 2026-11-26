module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractingAutChainCosetSumScalingOfUnimodularit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureProjectiveOverStandardOpenRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankThreeRootIndexOfCards
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeCoeffAdjacentSwapOfLeviReduction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCellSumLeviReductionOfSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCellSumLeviReductionOfSteps
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem exists_diag_zpow {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L}
    (hσ : σ ϖ = ϖ) (h0 : ϖ ≠ 0) {r : ℕ} (b : Fin r → ℤ) (hb : ∀ i, b i.rev = -b i) :
    ∃ s : GU σ r, mat s = Matrix.diagonal (fun i => ϖ ^ b i) := by
  obtain ⟨s, hs, -⟩ := P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ b i) (fun i => by
    rw [map_zpow₀, hσ, hb, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])
  exact ⟨s, hs⟩

theorem leviStep_of_steps (hR : RankOne) (hE : EmbExists) (hM : EmbMem) (hT : EmbTorus) (hL : LeviRad)
    (hS : UnipSplit) (hC : Contract) (hJ : TorusConj) : LeviStep := by
  intro L _ _ ϖ σ q n r e β γ b B B' Q d t t' h hU hD hb hbd hB hB' hBB hd ht ht' hQ hidx hcar hh
  have hv := hU.2.1
  have hϖ : σ ϖ = ϖ := hU.2.2.1
  have h0 : ϖ ≠ 0 := by
    intro h0
    have := hU.2.2.2.1
    rw [h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  have hinj : Function.Injective e := hD.1.injective
  obtain ⟨ι, hι⟩ := hE L σ n r e hinj hD.2.1
  obtain ⟨s₀, hs₀⟩ := exists_diag_zpow hϖ h0 b hb
  obtain ⟨s, hs⟩ := exists_diag_zpow hϖ h0 (fun i => B (e i)) (fun i => by rw [hD.2.1, hB])
  obtain ⟨s', hs'⟩ := exists_diag_zpow hϖ h0 (fun i => B' (e i)) (fun i => by rw [hD.2.1, hB'])
  obtain ⟨z, hz, hz', hzc⟩ := hT L σ n r e ι hinj hι (fun a => ϖ ^ B a) (fun a => ϖ ^ B' a) t t' s s' ht ht' hs hs'
    (fun a ha => by simp only [hBB a ha])
  have hMem := hM L σ n r e β γ ι hv hD hι
  have hCon := fun g hg => hC L ϖ σ q r γ b s₀ g hU hbd hs₀ hg
  have hnorm : s₀ ∈ Subgroup.normalizer ((rootU σ γ : Subgroup (GU σ r)) : Set (GU σ r)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => (hCon g hg).1, fun hg => ?_⟩
    have := (hCon _ hg).2.1
    simpa [mul_assoc] using this
  set c : MulAut (rootU σ γ) := (rootU σ γ).normalizerMonoidHom ⟨s₀, hnorm⟩ with hc
  have hc1 : ∀ a, ((c a : rootU σ γ) : GU σ r) = s₀ * a * s₀⁻¹ := fun a => rfl
  have hcz : ∀ (j : ℤ) a, (((c ^ j) a : rootU σ γ) : GU σ r) = s₀ ^ j * a * (s₀ ^ j)⁻¹ := fun j a => by
    rw [hc, ← map_zpow, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  have hcn : ∀ (j : ℕ) a, (((c ^ j) a : rootU σ γ) : GU σ r) = s₀ ^ j * a * (s₀ ^ j)⁻¹ := fun j a => by
    rw [hc, ← map_pow, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  have hcomap : (KU σ n).comap (ι.comp (rootU σ γ).subtype) = (KU σ r ⊓ rootU σ γ).subgroupOf (rootU σ γ) := by
    ext a
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun ha => ⟨(hMem a).1.1 ha, a.2⟩, fun ha => (hMem a).1.2 ha.1⟩
  have hLR := hL L σ n β hv
  refine hR (GU σ n) (rootU σ γ) (KU σ n) (radU σ Fin.val) (radU σ β) (ι.comp (rootU σ γ).subtype) c Q d h t t'
    hh.1 (P.finite_supp (KU σ n) (P.isCommensurated_integral_unitary_of_unramified hU n) h hh) ?_ ?_ ?_ ?_ ?_ ?_ hQ ?_ ?_ ?_ ?_
  · intro u hu i j hij
    exact hu i j (hD.2.2.1 hij)
  · intro a
    exact (hMem a).2.2 a.2.1
  · intro u hu
    obtain ⟨a, ha, u', hu', e1⟩ := hS L σ n r e β γ ι hD hι u hu
    exact ⟨⟨a, ha⟩, u', hu', e1⟩
  · intro a u' hu'
    exact (hLR _ ((hMem a).2.1 a.2.2) u' hu').2
  · intro a u' hu'
    exact (hLR _ ((hMem a).2.1 a.2.2) u' hu').1
  · intro a ha
    exact (hMem _).1.2 ((hCon a a.2).2.2.1 ((hMem a).1.1 ha))
  · rw [hcomap, ← Subgroup.relIndex_map_map_of_injective _ _ (rootU σ γ).subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le inf_le_right, ← hidx s₀ hs₀, Subgroup.map_map]
    congr 1
    conv_rhs => rw [← Subgroup.map_subgroupOf_eq_of_le (inf_le_right : KU σ r ⊓ rootU σ γ ≤ _), Subgroup.map_map]
    rfl
  · intro a
    obtain ⟨j, hj⟩ := (hCon a a.2).2.2.2
    refine ⟨j, (hMem _).1.2 ?_⟩
    rw [← hcn] at hj
    exact hj
  · intro a
    have e1 := hJ L ϖ σ r γ b (fun i => B' (e i)) d s₀ s' a h0 hd hs₀ hs' a.2.2
    show t' * ι a * t'⁻¹ = ι ((c ^ d) a : rootU σ γ)
    rw [hcz, ← e1, hz', map_mul, map_mul, map_inv, mul_assoc (ι s'), (hzc a).eq]
    group
  · intro a
    obtain ⟨k₁, hk₁, k₂, hk₂, e1⟩ := hcar s s' hs hs' a a.2
    have hk : ι k₂ ∈ leviU σ β := (hMem _).2.1 hk₂.2
    refine ⟨ι k₁, (hMem _).1.2 hk₁, ι k₂, (hMem _).1.2 hk₂.1, fun u hu => (hLR _ hk u hu).1, fun u hu => ?_, ?_⟩
    · simpa using (hLR _ (inv_mem hk) u hu).1
    · show (ι a)⁻¹ * t' = ι k₁ * (t * ι a) * ι k₂
      have e2 := congrArg ι e1
      simp only [map_mul, map_inv] at e2
      rw [hz, hz', ← mul_assoc, e2, mul_assoc (ι s), (hzc a).eq]
      simp only [mul_assoc]
      rw [(hzc k₂).eq]

end GlobalTheory.SatakeWeyl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCellSumLeviReductionOfStepsStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryCellSumLeviReduction_of_steps : GlobalTheory.SatakeWeyl.RankOne → GlobalTheory.SatakeWeyl.EmbExists → GlobalTheory.SatakeWeyl.EmbMem → GlobalTheory.SatakeWeyl.EmbTorus → GlobalTheory.SatakeWeyl.LeviRad → GlobalTheory.SatakeWeyl.UnipSplit → GlobalTheory.SatakeWeyl.Contract → GlobalTheory.SatakeWeyl.TorusConj → GlobalTheory.SatakeWeyl.LeviStep := by
  first | exact @GlobalTheory.SatakeWeyl.leviStep_of_steps | exact GlobalTheory.SatakeWeyl.leviStep_of_steps | (intros; apply GlobalTheory.SatakeWeyl.leviStep_of_steps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUnipotentRadicalSplittingOfLeviPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUnipotentRadicalSplittingOfLeviPart
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem antiJ_eq_one_rev {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (i j : Fin n) :
    antiJ L n i j = if i.rev = j then 1 else 0 := by
  have := antiJ_mul_apply (1 : Matrix (Fin n) (Fin n) L) i j
  rw [Matrix.mul_one] at this
  rw [this, Matrix.one_apply]

theorem exists_mat_submatrix {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n r : ℕ}
    (e : Fin r → Fin n) (he : Function.Injective e) (hrev : ∀ i, e i.rev = (e i).rev) (m : GU σ n)
    (hm : ∀ a b, (a ∉ Set.range e ∨ b ∉ Set.range e) → mat m a b = (1 : Matrix (Fin n) (Fin n) L) a b) :
    ∃ a : GU σ r, mat a = (mat m).submatrix e e := by
  apply exists_mat
  ext i j
  have h1 : cT σ (mat m) * antiJ L n * mat m = antiJ L n := m.2
  have h2 := congrFun (congrFun h1 (e i)) (e j)
  rw [Matrix.mul_apply] at h2 ⊢
  simp only [P.fSatake_cTJ] at h2 ⊢
  rw [antiJ_eq_one_rev] at h2 ⊢
  rw [← hrev] at h2
  simp only [he.eq_iff] at h2
  rw [← h2]
  refine Fintype.sum_of_injective e he _ _ ?_ ?_
  · intro l hl
    rw [hm l (e j) (Or.inl hl), Matrix.one_apply_ne (fun h => hl ⟨j, h.symm⟩), mul_zero]
  · intro l
    simp only [Matrix.submatrix_apply, hrev]

theorem unipSplit_of_leviPart (hL : LeviPart) : UnipSplit := by
  intro L _ _ σ n r e β γ ι hB hι u hu
  obtain ⟨hmono, hrev, hβ, hβrev, hβe, hγ⟩ := hB
  have hu' : ∀ i j : Fin n, j.val ≤ i.val → mat u i j = (1 : Matrix (Fin n) (Fin n) L) i j := hu
  have htri : (mat u).BlockTriangular β := by
    intro a b hab
    have hba : b < a := hβ.reflect_lt hab
    rw [hu' a b hba.le, Matrix.one_apply_ne hba.ne']
  obtain ⟨m, hmL, hmu, hrad⟩ := hL L σ n β hβrev u htri
  have hmL' : ∀ i j, β i ≠ β j → mat m i j = 0 := hmL
  have hm : ∀ a b, (a ∉ Set.range e ∨ b ∉ Set.range e) → mat m a b = (1 : Matrix (Fin n) (Fin n) L) a b := by
    intro a b hab
    by_cases h : β a = β b
    · rcases hβe a b h with rfl | ⟨h1, h2⟩
      · rw [hmu a a rfl, hu' a a le_rfl]
      · rcases hab with h' | h'
        · exact absurd h1 h'
        · exact absurd h2 h'
    · rw [hmL' a b h, Matrix.one_apply_ne (fun e' : a = b => h (congrArg β e'))]
  obtain ⟨a, ha⟩ := exists_mat_submatrix e hmono.injective hrev m hm
  have hιa : ι a = m := by
    apply mat_injective
    ext x y
    by_cases hxy : x ∉ Set.range e ∨ y ∉ Set.range e
    · rw [(hι a).2 x y hxy, hm x y hxy]
    · push Not at hxy
      obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ := hxy
      rw [(hι a).1 i j, ha, Matrix.submatrix_apply]
  refine ⟨a, ⟨?_, ?_⟩, m⁻¹ * u, hrad, by rw [hιa, mul_inv_cancel_left]⟩
  · intro i j hij
    have hij' : j ≤ i := hij
    rw [ha, Matrix.submatrix_apply]
    by_cases h : β (e i) = β (e j)
    · rw [hmu _ _ h, hu' _ _ (hmono.monotone hij'), Matrix.one_apply, Matrix.one_apply]
      simp only [hmono.injective.eq_iff]
    · rw [hmL' _ _ h, Matrix.one_apply_ne (fun e' : i = j => h (by rw [e']))]
  · intro i j hij
    rw [ha, Matrix.submatrix_apply]
    exact hmL' _ _ fun h => hij ((hγ i j).1 h)

end GlobalTheory.SatakeWeyl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryUnipotentRadicalSplittingOfLeviPartStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryUnipotentRadicalSplitting_of_leviPart : GlobalTheory.SatakeWeyl.LeviPart → GlobalTheory.SatakeWeyl.UnipSplit := by
  first | exact @GlobalTheory.SatakeWeyl.unipSplit_of_leviPart | exact GlobalTheory.SatakeWeyl.unipSplit_of_leviPart | (intros; apply GlobalTheory.SatakeWeyl.unipSplit_of_leviPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallerUnitaryEmbeddingPreservesIntegralParts
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallerUnitaryEmbeddingPreservesIntegralParts
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem embMem : EmbMem := by
  intro L _ _ σ n r e β γ ι hσ hD hι g
  obtain ⟨he, -, -, -, -, hβγ⟩ := hD
  obtain ⟨h1, h2⟩ := hι g
  have hcases : ∀ a b : Fin n, (∃ i j, a = e i ∧ b = e j) ∨ (a ∉ Set.range e ∨ b ∉ Set.range e) := by
    intro a b
    by_cases ha : a ∈ Set.range e
    · by_cases hb : b ∈ Set.range e
      · obtain ⟨i, rfl⟩ := ha
        obtain ⟨j, rfl⟩ := hb
        exact Or.inl ⟨i, j, rfl, rfl⟩
      · exact Or.inr (Or.inr hb)
    · exact Or.inr (Or.inl ha)
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_KU_iff hσ, mem_KU_iff hσ]
    refine ⟨fun h i j => h1 i j ▸ h (e i) (e j), fun h a b => ?_⟩
    rcases hcases a b with ⟨i, j, rfl, rfl⟩ | hab
    · rw [h1]; exact h i j
    · rw [h2 a b hab, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  · intro hg a b hab
    rcases hcases a b with ⟨i, j, rfl, rfl⟩ | h
    · rw [h1]
      exact hg i j fun hij => hab ((hβγ i j).2 hij)
    · rw [h2 a b h]
      exact Matrix.one_apply_ne fun h' => hab (h' ▸ rfl)
  · intro hg a b hab
    rcases hcases a b with ⟨i, j, rfl, rfl⟩ | h
    · have hji : j ≤ i := he.le_iff_le.1 hab
      rw [h1, hg i j hji, Matrix.one_apply, Matrix.one_apply]
      simp only [he.injective.eq_iff]
    · exact h2 a b h

end GlobalTheory.SatakeWeyl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallerUnitaryEmbeddingPreservesIntegralPartsStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smaller_unitary_embedding_preserves_integral_parts : GlobalTheory.SatakeWeyl.EmbMem := by
  first | exact @GlobalTheory.SatakeWeyl.embMem | exact GlobalTheory.SatakeWeyl.embMem | (intros; apply GlobalTheory.SatakeWeyl.embMem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDiagonalFactorizationAlongEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDiagonalFactorizationAlongEmbedding
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl


open Classical in
theorem emb_mul_diagonal {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n r : ℕ}
    {e : Fin r → Fin n} {ι : GU σ r →* GU σ n} (he : Function.Injective e) (hι : IsEmb e ι)
    (D : Fin n → L) (s : GU σ r) (hs : mat s = Matrix.diagonal (D ∘ e)) :
    mat (ι s) * Matrix.diagonal (fun a => if a ∈ Set.range e then 1 else D a) = Matrix.diagonal D := by
  ext a b
  rw [Matrix.mul_diagonal]
  by_cases hb : b ∈ Set.range e
  · rw [if_pos hb, mul_one]
    by_cases ha : a ∈ Set.range e
    · obtain ⟨i, rfl⟩ := ha
      obtain ⟨j, rfl⟩ := hb
      rw [(hι s).1, hs]
      simp [Matrix.diagonal_apply, he.eq_iff]
    · have hab : a ≠ b := fun h => ha (h ▸ hb)
      rw [(hι s).2 a b (Or.inl ha), Matrix.one_apply_ne hab, Matrix.diagonal_apply_ne _ hab]
  · rw [if_neg hb, (hι s).2 a b (Or.inr hb)]
    by_cases hab : a = b
    · subst hab
      simp
    · rw [Matrix.one_apply_ne hab, Matrix.diagonal_apply_ne _ hab, zero_mul]

theorem embTorus : EmbTorus := by
  classical
  intro L _ _ σ n r e ι he hι D D' t t' s s' ht ht' hs hs' hD
  have h1 := emb_mul_diagonal he hι D s hs
  have h2 := emb_mul_diagonal he hι D' s' hs'
  have hZ : (fun a => if a ∈ Set.range e then (1 : L) else D' a) =
      fun a => if a ∈ Set.range e then (1 : L) else D a := by
    funext a
    by_cases ha : a ∈ Set.range e
    · rw [if_pos ha, if_pos ha]
    · rw [if_neg ha, if_neg ha, hD a ha]
  have hz : mat ((ι s)⁻¹ * t) = Matrix.diagonal (fun a => if a ∈ Set.range e then (1 : L) else D a) := by
    rw [mat_mul, ht, ← h1, ← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]
  refine ⟨(ι s)⁻¹ * t, by group, ?_, fun g => ?_⟩
  · apply mat_injective
    rw [mat_mul, hz, ← hZ, ht', ← h2]
  · apply mat_injective
    rw [mat_mul, mat_mul (ι g), hz]
    ext a b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hab : a = b
    · subst hab
      exact mul_comm _ _
    · by_cases ha : a ∈ Set.range e
      · by_cases hb : b ∈ Set.range e
        · rw [if_pos ha, if_pos hb, one_mul, mul_one]
        · rw [(hι g).2 a b (Or.inr hb), Matrix.one_apply_ne hab, mul_zero, zero_mul]
      · rw [(hι g).2 a b (Or.inl ha), Matrix.one_apply_ne hab, mul_zero, zero_mul]

end GlobalTheory.SatakeWeyl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDiagonalFactorizationAlongEmbeddingStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_diagonal_factorization_along_embedding : GlobalTheory.SatakeWeyl.EmbTorus := by
  first | exact @GlobalTheory.SatakeWeyl.embTorus | exact GlobalTheory.SatakeWeyl.embTorus | (intros; apply GlobalTheory.SatakeWeyl.embTorus <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLeviCentreDiagonalConjugationEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLeviCentreDiagonalConjugationEq
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl.TorusConjProof

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ}


omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_inv_diag {ϖ : L} (hϖ : ϖ ≠ 0) {s : GU σ r} {b : Fin r → ℤ}
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ b i)) : mat s⁻¹ = Matrix.diagonal (fun i => ϖ ^ (-b i)) := by
  have h : mat s * Matrix.diagonal (fun i => ϖ ^ (-b i)) = 1 := by
    rw [hs, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ, add_neg_cancel, zpow_zero]
  calc mat s⁻¹ = mat s⁻¹ * (mat s * Matrix.diagonal (fun i => ϖ ^ (-b i))) := by rw [h, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]


omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_zpow_diag {ϖ : L} (hϖ : ϖ ≠ 0) {s : GU σ r} {b : Fin r → ℤ}
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ b i)) (d : ℤ) :
    mat (s ^ d) = Matrix.diagonal (fun i => ϖ ^ (d * b i)) := by
  induction d using Int.induction_on with
  | zero => simp [mat_one]
  | succ k ih =>
    rw [zpow_add_one, mat_mul, ih, hs, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ]
    congr 1
    ring
  | pred k ih =>
    rw [zpow_sub_one, mat_mul, ih, mat_inv_diag hϖ hs, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← zpow_add₀ hϖ]
    congr 1
    ring


omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_conj_apply {ϖ : L} (hϖ : ϖ ≠ 0) {s : GU σ r} {b : Fin r → ℤ}
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ b i)) (g : GU σ r) (i j : Fin r) :
    mat (s * g * s⁻¹) i j = ϖ ^ (b i - b j) * mat g i j := by
  rw [mat_mul, mat_mul, mat_inv_diag hϖ hs, hs, Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg,
    zpow_add₀ hϖ]
  ring

theorem torusConj : GlobalTheory.SatakeWeyl.TorusConj := by
  intro L _ _ ϖ σ r γ b b' d s s' g hϖ hb hs hs' hg
  apply mat_injective
  ext i j
  rw [mat_conj_apply hϖ hs', mat_conj_apply hϖ (mat_zpow_diag hϖ hs d)]
  by_cases h : γ i = γ j
  · rw [hb i j h, mul_sub]
  · have h0 : mat g i j = 0 := hg i j h
    rw [h0, mul_zero, mul_zero]

end GlobalTheory.SatakeWeyl.TorusConjProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLeviCentreDiagonalConjugationEqStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_levi_centre_diagonal_conjugation_eq : GlobalTheory.SatakeWeyl.TorusConj := by
  first | exact @GlobalTheory.SatakeWeyl.TorusConjProof.torusConj | exact GlobalTheory.SatakeWeyl.TorusConjProof.torusConj | (intros; apply GlobalTheory.SatakeWeyl.TorusConjProof.torusConj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractingAutomorphismSubgroupChainIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractingAutomorphismSubgroupChainIndex
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem chain_comap_eq {A : Type} [Group A] (U : Subgroup A) (c : MulAut A) (j : ℤ) :
    U.comap (c ^ j).toMonoidHom = (U.map c.toMonoidHom).comap (c ^ (j + 1)).toMonoidHom := by
  ext a
  have h : (c ^ (j + 1)) a = c ((c ^ j) a) := by
    rw [add_comm, zpow_add, zpow_one, MulAut.mul_apply]
  simp only [Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, h]
  constructor
  · intro ha
    exact ⟨_, ha, rfl⟩
  · rintro ⟨x, hx, hxa⟩
    rw [← c.injective hxa]
    exact hx

theorem chain_step {A : Type} [Group A] (U : Subgroup A) (c : MulAut A) (hc : ∀ a ∈ U, c a ∈ U) (j : ℤ) :
    U.comap (c ^ j).toMonoidHom ≤ U.comap (c ^ (j + 1)).toMonoidHom ∧
      (U.comap (c ^ j).toMonoidHom).relIndex (U.comap (c ^ (j + 1)).toMonoidHom) =
        (U.map c.toMonoidHom).relIndex U := by
  rw [chain_comap_eq U c j]
  refine ⟨Subgroup.comap_mono ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hc x hx
  · rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective]
    exact (c ^ (j + 1)).surjective

theorem chainIndex : ChainIndex := by
  intro A _ U c Q hc hQ j l
  induction l with
  | zero => simp
  | succ l ih =>
    obtain ⟨h1, h2⟩ := chain_step U c hc (j + l)
    have e : j + ((l + 1 : ℕ) : ℤ) = j + l + 1 := by push_cast; ring
    rw [e]
    refine ⟨ih.1.trans h1, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ ih.1 h1, ih.2, h2, hQ, pow_succ]

end GlobalTheory.SatakeWeyl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractingAutomorphismSubgroupChainIndexStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contracting_automorphism_subgroup_chain_index : GlobalTheory.SatakeWeyl.ChainIndex := by
  first | exact @GlobalTheory.SatakeWeyl.chainIndex | exact GlobalTheory.SatakeWeyl.chainIndex | (intros; apply GlobalTheory.SatakeWeyl.chainIndex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexCosetSumUnimodularityOfFiniteIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexCosetSumUnimodularityOfFiniteIndex
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem finsum_quotient_subgroupOf {A : Type} [Group A] (Γ W : Subgroup A) (F : A → ℂ)
    (hΓ : ∀ a, F a ≠ 0 → a ∈ Γ) (hF : ∀ w ∈ W, ∀ a, F (a * w) = F a) :
    ∑ᶠ y : A ⧸ W, F y.out = ∑ᶠ y : Γ ⧸ W.subgroupOf Γ, F (y.out : Γ) := by
  have hout : ∀ a : A, F (QuotientGroup.mk a : A ⧸ W).out = F a := by
    intro a
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul W a
    rw [hw, hF w w.2]
  let e : Γ ⧸ W.subgroupOf Γ → A ⧸ W := fun y => QuotientGroup.mk ((y.out : Γ) : A)
  have hinj : Function.Injective e := by
    intro y z h
    have h1 : ((y.out : Γ) : A)⁻¹ * ((z.out : Γ) : A) ∈ W := QuotientGroup.eq.1 h
    have h2 : (QuotientGroup.mk y.out : Γ ⧸ W.subgroupOf Γ) = QuotientGroup.mk z.out :=
      QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (by simpa using h1))
    simpa using h2
  have hsupp : (Function.support fun y : A ⧸ W => F y.out) ⊆ Set.range e := by
    intro y hy
    have hm : y.out ∈ Γ := hΓ _ hy
    refine ⟨QuotientGroup.mk ⟨y.out, hm⟩, ?_⟩
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (W.subgroupOf Γ) ⟨y.out, hm⟩
    have hw' : ((w : Γ) : A) ∈ W := Subgroup.mem_subgroupOf.1 w.2
    show (QuotientGroup.mk _ : A ⧸ W) = y
    rw [hw, Subgroup.coe_mul, QuotientGroup.mk_mul_of_mem _ hw']
    exact QuotientGroup.out_eq' y
  calc ∑ᶠ y : A ⧸ W, F y.out = ∑ᶠ y ∈ Set.range e, F y.out := by
        rw [← finsum_mem_univ]
        apply finsum_mem_inter_support_eq
        rw [Set.univ_inter, Set.inter_eq_right.2 hsupp]
    _ = ∑ᶠ y, F (e y).out := finsum_mem_range hinj
    _ = _ := finsum_congr fun y => hout _

theorem unimod_of_unimodFin : UnimodFin → Unimod := by
  intro H A _ Γ U V f _ _ hUi hVi hΓ hfV hfU
  have h := H Γ (U.subgroupOf Γ) (V.subgroupOf Γ) (fun a => f a) hUi hVi
    (fun v hv a => hfV _ (Subgroup.mem_subgroupOf.1 hv) _)
    (fun u hu a => hfU _ (Subgroup.mem_subgroupOf.1 hu) _)
  rw [finsum_quotient_subgroupOf Γ U f hΓ hfU,
    finsum_quotient_subgroupOf Γ V (fun a => f a⁻¹) (fun a ha => (inv_mem_iff.1 (hΓ _ ha)))
      (fun w hw a => by rw [mul_inv_rev, hfV _ (inv_mem hw)])]
  exact h

end GlobalTheory.SatakeWeyl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexCosetSumUnimodularityOfFiniteIndexStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndexCosetSumUnimodularity_of_finiteIndex : GlobalTheory.SatakeWeyl.UnimodFin → GlobalTheory.SatakeWeyl.Unimod := by
  first | exact @GlobalTheory.SatakeWeyl.unimod_of_unimodFin | exact GlobalTheory.SatakeWeyl.unimod_of_unimodFin | (intros; apply GlobalTheory.SatakeWeyl.unimod_of_unimodFin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIndexLeftRightCosetSumsEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIndexLeftRightCosetSumsEq
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem sum_out_left_translate {A : Type} [Group A] (U : Subgroup A) [Fintype (A ⧸ U)] (F : A → ℂ)
    (hF : ∀ u ∈ U, ∀ a, F (a * u) = F a) (g : A) :
    ∑ y : A ⧸ U, F (g * y.out) = ∑ y : A ⧸ U, F y.out := by
  refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun y => ?_
  have h1 : (MulAction.toPerm g y : A ⧸ U) = ((g * y.out : A) : A ⧸ U) := by
    rw [MulAction.toPerm_apply, ← MulAction.Quotient.coe_smul_out, smul_eq_mul]
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U (g * y.out)
  rw [h1, hu, hF u u.2]

theorem unimodFin : UnimodFin := by
  intro A _ U V f hU hV hl hr
  haveI : U.FiniteIndex := ⟨hU⟩
  haveI : V.FiniteIndex := ⟨hV⟩
  letI : Fintype (A ⧸ U) := Fintype.ofFinite _
  letI : Fintype (A ⧸ V) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have e1 : ∀ x : A ⧸ U, ∑ y : A ⧸ V, f (y.out⁻¹ * x.out) = ∑ y : A ⧸ V, f y.out⁻¹ := by
    intro x
    have := sum_out_left_translate V (fun a => f a⁻¹)
      (fun v hv a => by simp only [mul_inv_rev]; exact hl _ (V.inv_mem hv) _) x.out⁻¹
    simpa [mul_inv_rev] using this
  have e2 : ∀ y : A ⧸ V, ∑ x : A ⧸ U, f (y.out⁻¹ * x.out) = ∑ x : A ⧸ U, f x.out :=
    fun y => sum_out_left_translate U f hr _
  have := Finset.sum_comm (s := (Finset.univ : Finset (A ⧸ U))) (t := (Finset.univ : Finset (A ⧸ V)))
    (f := fun x y => f (y.out⁻¹ * x.out))
  simp only [e1, e2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact this

end GlobalTheory.SatakeWeyl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteIndexLeftRightCosetSumsEqStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_index_left_right_coset_sums_eq : GlobalTheory.SatakeWeyl.UnimodFin := by
  first | exact @GlobalTheory.SatakeWeyl.unimodFin | exact GlobalTheory.SatakeWeyl.unimodFin | (intros; apply GlobalTheory.SatakeWeyl.unimodFin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumLeftRightInvarianceNormaliser
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumLeftRightInvarianceNormaliser
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem cellInv_holds : CellInv := by
  classical
  intro G _ K N h g k₁ k₂ hh hk₁ hk₂ hN hN'
  unfold cellSum
  rw [← finsum_comp_equiv (MulAction.toPerm k₁ : Equiv.Perm (G ⧸ K))]
  refine finsum_congr fun x => ?_
  obtain ⟨k, hk⟩ : ∃ k : K, (k₁ • x).out = k₁ * x.out * k := by
    rw [← MulAction.Quotient.mk_smul_out]
    exact QuotientGroup.mk_out_eq_mul K _
  rw [MulAction.toPerm_apply, hk]
  have e : h (k₁ * x.out * k) = h x.out := hh ⟨k₁, hk₁⟩ k _
  rw [e]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨u, hu, k', hk', e'⟩
    refine ⟨k₂ * u * k₂⁻¹, hN u hu, k₂ * k' * (k : G)⁻¹, K.mul_mem (K.mul_mem hk₂ hk') (K.inv_mem k.2), ?_⟩
    have : x.out = k₁⁻¹ * (k₁ * x.out * k) * (k : G)⁻¹ := by group
    rw [this, e']; group
  · rintro ⟨u, hu, k', hk', e'⟩
    refine ⟨k₂⁻¹ * u * k₂, hN' u hu, k₂⁻¹ * k' * k, K.mul_mem (K.mul_mem (K.inv_mem hk₂) hk') k.2, ?_⟩
    rw [e']; group

end GlobalTheory.SatakeWeyl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumLeftRightInvarianceNormaliserStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_sum_left_right_invariance_normaliser : GlobalTheory.SatakeWeyl.CellInv := by
  first | exact @GlobalTheory.SatakeWeyl.cellInv_holds | exact GlobalTheory.SatakeWeyl.cellInv_holds | (intros; apply GlobalTheory.SatakeWeyl.cellInv_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2CartanDoubleCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2CartanDoubleCosets
noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl.Four

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}

def unitaryFourUpperLeftBlock (g : GU σ 4) : Matrix (Fin 2) (Fin 2) L := !![mat g 0 0, mat g 0 1; mat g 1 0, mat g 1 1]

theorem unitaryFourUpperLeftBlock_mul_of_mem_levi {g : GU σ 4} (g' : GU σ 4) (hg : g ∈ leviU σ ![0, 0, 1, 1]) :
    unitaryFourUpperLeftBlock (g * g') = unitaryFourUpperLeftBlock g * unitaryFourUpperLeftBlock g' := by
  have h02 := hg 0 2 (by decide)
  have h03 := hg 0 3 (by decide)
  have h12 := hg 1 2 (by decide)
  have h13 := hg 1 3 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitaryFourUpperLeftBlock, mat_mul, Matrix.mul_apply, Fin.sum_univ_four, h02, h03, h12, h13]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem unitaryFourUpperLeftBlock_one : unitaryFourUpperLeftBlock (1 : GU σ 4) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitaryFourUpperLeftBlock, mat_one]

theorem unitaryFourUpperLeftBlock_injective_on_levi {g g' : GU σ 4} (hg : g ∈ leviU σ ![0, 0, 1, 1]) (hg' : g' ∈ leviU σ ![0, 0, 1, 1])
    (h : unitaryFourUpperLeftBlock g = unitaryFourUpperLeftBlock g') : g = g' := by
  have h1 : unitaryFourUpperLeftBlock g⁻¹ * unitaryFourUpperLeftBlock g' = 1 := by
    rw [← h, ← unitaryFourUpperLeftBlock_mul_of_mem_levi _ (inv_mem hg), inv_mul_cancel, unitaryFourUpperLeftBlock_one]
  have h2 : unitaryFourUpperLeftBlock g' * unitaryFourUpperLeftBlock g'⁻¹ = 1 := by
    rw [← unitaryFourUpperLeftBlock_mul_of_mem_levi _ hg', mul_inv_cancel, unitaryFourUpperLeftBlock_one]
  have h3 : unitaryFourUpperLeftBlock g⁻¹ = unitaryFourUpperLeftBlock g'⁻¹ := left_inv_eq_right_inv h1 h2
  have low : ∀ i j : Fin 4, mat g⁻¹ j.rev i.rev = mat g'⁻¹ j.rev i.rev → mat g i j = mat g' i j := by
    intro i j e
    have e1 := mat_inv_apply g⁻¹ i j
    have e2 := mat_inv_apply g'⁻¹ i j
    rw [inv_inv] at e1 e2
    rw [e1, e2, e]
  have off : ∀ i j : Fin 4, (![0, 0, 1, 1] : Fin 4 → ℕ) i ≠ ![0, 0, 1, 1] j → mat g i j = mat g' i j :=
    fun i j e => by rw [hg i j e, hg' i j e]
  apply mat_injective
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrFun (congrFun h 0) 0
  · exact congrFun (congrFun h 0) 1
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact congrFun (congrFun h 1) 0
  · exact congrFun (congrFun h 1) 1
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact low _ _ (congrFun (congrFun h3 1) 1)
  · exact low _ _ (congrFun (congrFun h3 0) 1)
  · exact off _ _ (by decide)
  · exact off _ _ (by decide)
  · exact low _ _ (congrFun (congrFun h3 1) 0)
  · exact low _ _ (congrFun (congrFun h3 0) 0)

theorem exists_lift (h1 : ∀ x, σ (σ x) = x) (h2 : ∀ x, Valued.v (σ x) = Valued.v x) {p r u w : L}
    (hp : p ∈ intL L) (hr : r ∈ intL L) (hu : u ∈ intL L) (hw : w ∈ intL L) (hd : p * w - r * u = -1) :
    ∃ k ∈ KU σ 4 ⊓ leviU σ ![0, 0, 1, 1], unitaryFourUpperLeftBlock k = !![p, r; u, w] := by
  have hd' : σ p * σ w - σ r * σ u = -1 := by simpa using congrArg σ hd
  have hs : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => by
    show Valued.v (σ x) ≤ 1
    rw [h2]; exact hx
  obtain ⟨k, hk⟩ := exists_mat (σ := σ) !![p, r, 0, 0; u, w, 0, 0; 0, 0, -σ p, σ r; 0, 0, σ u, -σ w] (by
    ext i j
    rw [Matrix.mul_apply]
    simp only [P.fSatake_cTJ]
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four, antiJ, h1, Fin.rev] <;>
      first | linear_combination hd | linear_combination -hd | linear_combination hd' | linear_combination -hd' | ring)
  refine ⟨k, ⟨(mem_KU_iff h2 k).2 fun i j => ?_, fun i j hij => ?_⟩, ?_⟩
  · rw [hk]
    fin_cases i <;> fin_cases j <;> simp [hp, hr, hu, hw, hs _ hp, hs _ hr, hs _ hu, hs _ hw]
  · rw [hk]
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  · simp [unitaryFourUpperLeftBlock, hk]

theorem exists_conj {A D ξ : L} (hA : A ≠ 0) (hD : D ≠ 0) :
    ∃ p ∈ intL L, ∃ r ∈ intL L, ∃ u ∈ intL L, ∃ w ∈ intL L, p * w - r * u = -1 ∧
      !![D, -(A * ξ); 0, A] = !![p, r; u, w] * !![A, A * ξ; 0, D] * !![p, r; u, w] := by
  have mem : ∀ x : L, x ∈ intL L ↔ Valued.v x ≤ 1 := fun x => Iff.rfl
  by_cases h1 : ξ ∈ intL L
  · refine ⟨-ξ, neg_mem h1, 1, one_mem _, 1, one_mem _, 0, zero_mem _, by ring, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  by_cases h2 : A * ξ / D ∈ intL L
  · refine ⟨0, zero_mem _, 1, one_mem _, 1, one_mem _, -(A * ξ / D), neg_mem h2, by ring, ?_⟩
    obtain ⟨ζ, hζ⟩ : ∃ ζ, A * ξ = D * ζ := ⟨A * ξ / D, by field_simp⟩
    rw [hζ, mul_div_cancel_left₀ _ hD]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  have hξ : ξ ≠ 0 := fun e => h1 (e ▸ zero_mem _)
  have inv : ∀ x : L, x ∉ intL L → x⁻¹ ∈ intL L := fun x hx => by
    rw [mem] at hx ⊢
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (not_le.1 hx).le
  refine ⟨1, one_mem _, 0, zero_mem _, -(ξ⁻¹ - (A * ξ / D)⁻¹), neg_mem (sub_mem (inv _ h1) (inv _ h2)),
    -1, neg_mem (one_mem _), by ring, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem cartanFour : GlobalTheory.SatakeWeyl.CartanFour := by
  intro L _ _ ϖ σ q hU x y s s' hs hs' a ha
  obtain ⟨h1, h2, -, h4, -⟩ := hU
  have hϖ : ϖ ≠ 0 := fun e => by rw [e, map_zero] at h4; exact WithZero.zero_ne_coe h4
  have dl : ∀ (t : GU σ 4) (d : Fin 4 → L), mat t = Matrix.diagonal d → t ∈ leviU σ ![0, 0, 1, 1] :=
    fun t d e i j hij => by rw [e]; exact Matrix.diagonal_apply_ne _ fun e => hij (e ▸ rfl)
  have hsl := dl _ _ hs
  have hsl' := dl _ _ hs'
  have us : unitaryFourUpperLeftBlock s = !![ϖ ^ x, 0; 0, ϖ ^ y] := by simp [unitaryFourUpperLeftBlock, hs]
  have us' : unitaryFourUpperLeftBlock s' = !![ϖ ^ y, 0; 0, ϖ ^ x] := by simp [unitaryFourUpperLeftBlock, hs']
  have ua : unitaryFourUpperLeftBlock a = !![1, mat a 0 1; 0, 1] := by
    simp [unitaryFourUpperLeftBlock, ha.1 0 0 (by decide), ha.1 1 0 (by decide), ha.1 1 1 (by decide)]
  obtain ⟨p, hp, r, hr, u, hu, w, hw, hd, e⟩ :=
    exists_conj (ξ := mat a 0 1) (zpow_ne_zero x hϖ) (zpow_ne_zero y hϖ)
  obtain ⟨k, hk, uk⟩ := exists_lift h1 h2 hp hr hu hw hd
  refine ⟨k, hk.1, k, hk, ?_⟩
  rw [inv_mul_eq_iff_eq_mul]
  refine unitaryFourUpperLeftBlock_injective_on_levi hsl' (mul_mem ha.2 (mul_mem (mul_mem hk.2 (mul_mem hsl ha.2)) hk.2)) ?_
  have usa : unitaryFourUpperLeftBlock (s * a) = !![ϖ ^ x, ϖ ^ x * mat a 0 1; 0, ϖ ^ y] := by
    rw [unitaryFourUpperLeftBlock_mul_of_mem_levi _ hsl, us, ua]; simp
  rw [unitaryFourUpperLeftBlock_mul_of_mem_levi _ ha.2, unitaryFourUpperLeftBlock_mul_of_mem_levi _ (mul_mem hk.2 (mul_mem hsl ha.2)), unitaryFourUpperLeftBlock_mul_of_mem_levi _ hk.2, usa, uk, ← e, us', ua]
  simp [mul_comm]

end GlobalTheory.SatakeWeyl.Four

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2CartanDoubleCosetsStatement
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryFourLeviGL2_cartan_doubleCosets : GlobalTheory.SatakeWeyl.CartanFour := by
  first | exact @GlobalTheory.SatakeWeyl.Four.cartanFour | exact GlobalTheory.SatakeWeyl.Four.cartanFour | (intros; apply GlobalTheory.SatakeWeyl.Four.cartanFour <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeWeylInvariant
noncomputable section

open Formalism.UG

namespace GlobalTheory.SatakeWeyl

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L} {q n m : ℕ}

theorem mem_radU_iff (u : GU σ n) : u ∈ radU σ (Fin.val : Fin n → ℕ) ↔ IsUnipU u := by
  refine ⟨fun h => ⟨fun i j hij => ?_, fun i => ?_⟩, fun h i j hij => ?_⟩
  · exact (h i j (le_of_lt hij)).trans (Matrix.one_apply_ne (ne_of_gt hij))
  · exact (h i i le_rfl).trans (Matrix.one_apply_eq i)
  · rcases hij.eq_or_lt with e | e
    · obtain rfl : j = i := Fin.ext e
      exact (h.2 j).trans (Matrix.one_apply_eq j).symm
    · exact (h.1 i j e).trans (Matrix.one_apply_ne (ne_of_gt (show j < i from e))).symm

theorem satU_eq (T : (Fin m → ℤ) → GU σ n) (hT : ∀ a, mat (T a) = tMat ϖ n m a) (h : GU σ n → ℂ) (α : Fin m → ℂ) :
    SatU ϖ q h α = ∑ᶠ a : Fin m → ℤ, (∏ i, α i ^ a i) *
      ((q : ℂ) ^ 0 * (∏ i : Fin m, (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
        cellSum (KU σ n) (radU σ Fin.val) h (T a)) := by
  unfold SatU cellSum
  refine finsum_congr fun a => ?_
  rw [Finset.prod_mul_distrib, pow_zero, one_mul, mul_assoc]
  congr 2
  refine finsum_congr fun x => ?_
  congr 1
  refine propext ⟨?_, ?_⟩
  · rintro ⟨u, hu, k, hk, e⟩
    exact ⟨u, (mem_radU_iff u).2 hu, k, hk, mat_injective (by rw [mat_mul, mat_mul, hT]; exact e)⟩
  · rintro ⟨u, hu, k, hk, e⟩
    refine ⟨u, (mem_radU_iff u).1 hu, k, hk, ?_⟩
    have := congrArg mat e
    rw [mat_mul, mat_mul, hT] at this
    exact this

theorem sum_perm (S : (Fin m → ℤ) → ℂ) (π : Equiv.Perm (Fin m)) (hS : ∀ a, S (a ∘ π) = S a) (α : Fin m → ℂ) :
    ∑ᶠ a : Fin m → ℤ, (∏ i, (α ∘ π) i ^ a i) * S a = ∑ᶠ a : Fin m → ℤ, (∏ i, α i ^ a i) * S a := by
  rw [← finsum_comp_equiv (Equiv.arrowCongr π.symm (Equiv.refl ℤ))]
  refine finsum_congr fun a => ?_
  have e : (Equiv.arrowCongr π.symm (Equiv.refl ℤ)) a = a ∘ π := by ext i; simp
  rw [e, hS]
  congr 1
  exact Equiv.prod_comp π (fun i => α i ^ a i)

theorem sum_neg (S : (Fin m → ℤ) → ℂ) (j : Fin m) (hS : ∀ a, S (Function.update a j (-a j)) = S a) (α : Fin m → ℂ) :
    ∑ᶠ a : Fin m → ℤ, (∏ i, Function.update α j (α j)⁻¹ i ^ a i) * S a =
      ∑ᶠ a : Fin m → ℤ, (∏ i, α i ^ a i) * S a := by
  have hinv : Function.Involutive fun a : Fin m → ℤ => Function.update a j (-a j) := fun a => by simp
  rw [← finsum_comp_equiv hinv.toPerm]
  refine finsum_congr fun a => ?_
  rw [Function.Involutive.coe_toPerm, hS]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i = j
  · subst hi
    simp
  · rw [Function.update_of_ne hi, Function.update_of_ne hi]

theorem perm_of_swap (S : (Fin m → ℤ) → ℂ)
    (hS : ∀ (i j : Fin m), j.val = i.val + 1 → ∀ a, S (a ∘ Equiv.swap i j) = S a) (π : Equiv.Perm (Fin m)) :
    ∀ a, S (a ∘ π) = S a := by
  cases m with
  | zero => intro a; congr 1; funext i; exact i.elim0
  | succ m =>
    have hπ : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
    induction hπ using Submonoid.closure_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hS _ _ (by simp)
    | one => intro a; rfl
    | mul x y _ _ hx hy => intro a; rw [← hx a, ← hy (a ∘ x)]; rfl

theorem satWeyl_of_coeff (hswap : CoeffSwap) (hneg : CoeffNeg) : SatWeyl := by
  intro L _ _ _ ϖ σ q n m hU hm hm' α _ h hh
  choose T hT using fun a : Fin m → ℤ => P.fSatake_tMat_exists (n := n) hU hm a
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  have hp : ∀ f : Fin m → ℤ, ∏ i, (q : ℂ) ^ f i = (q : ℂ) ^ ∑ i, f i := fun f =>
    (map_prod (zpowersHom ℂˣ (Units.mk0 (q : ℂ) hq)) (fun i => Multiplicative.ofAdd (f i)) Finset.univ) |>
      congrArg (Units.coeHom ℂ) |> fun e => by
        simpa [map_prod, ← ofAdd_sum] using e.symm
  set S : (Fin m → ℤ) → ℂ := fun a => (q : ℂ) ^ 0 *
    (∏ i : Fin m, (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
      cellSum (KU σ n) (radU σ Fin.val) h (T a) with hSdef
  have h1 : ∀ π : Equiv.Perm (Fin m), ∀ a, S (a ∘ π) = S a := by
    refine perm_of_swap S fun i j hij a => ?_
    have hne : i ≠ j := fun e => by rw [e] at hij; omega
    simp only [hSdef]
    rw [hswap L ϖ σ q n m hU hm hm' h hh a i j hij _ _ (hT a) (hT _), ← mul_assoc, hp, hp, pow_zero, one_mul, one_mul,
      ← zpow_add₀ hq]
    congr 2
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_add_of_mem i j (by simp) (by simp) hne]
    · simp only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right, hij]
      push_cast
      ring
    · rintro c - ⟨hc, hc'⟩
      simp only [Function.comp, Equiv.swap_apply_of_ne_of_ne hc hc', sub_self]
  have h2 : ∀ j : Fin m, j.val + 1 = m → ∀ a, S (Function.update a j (-a j)) = S a := by
    intro j hj a
    simp only [hSdef]
    rw [hneg L ϖ σ q n m hU hm hm' h hh a j hj _ _ (hT a) (hT _), ← mul_assoc, hp, hp, pow_zero, one_mul, one_mul,
      ← zpow_add₀ hq]
    congr 2
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · rw [Function.update_self]
      ring
    · intro c _ hc
      rw [Function.update_of_ne hc, sub_self]
    · simp
  have h3 : ∀ j : Fin m, ∀ a, S (Function.update a j (-a j)) = S a := by
    intro j a
    have hj := j.2
    let l : Fin m := ⟨m - 1, by omega⟩
    rw [← h1 (Equiv.swap j l) a, ← h2 l (by show m - 1 + 1 = m; omega) (a ∘ Equiv.swap j l),
      ← h1 (Equiv.swap j l) (Function.update a j (-a j))]
    congr 1
    rw [Function.update_comp_equiv]
    simp
  refine ⟨fun π => ?_, fun i => ?_⟩
  · rw [satU_eq T hT, satU_eq T hT]
    exact sum_perm S π (h1 π) α
  · rw [satU_eq T hT, satU_eq T hT]
    exact sum_neg S i (h3 i) α

theorem satWeyl : SatWeyl := by
  have hr : RankOne := GlobalTheory.T.cellSumRankOneReflectionSymmetry_of_steps GlobalTheory.T.cell_sum_two_stage_descent_unipotent GlobalTheory.T.cell_sum_left_right_invariance_normaliser
    (GlobalTheory.T.contractingAutChainCosetSumScaling_of_unimodularity (GlobalTheory.T.relIndexCosetSumUnimodularity_of_finiteIndex GlobalTheory.T.finite_index_left_right_coset_sums_eq) GlobalTheory.T.contracting_automorphism_subgroup_chain_index)
  have hl : LeviStep := GlobalTheory.T.unitaryCellSumLeviReduction_of_steps hr GlobalTheory.T.exists_smaller_unitary_group_embedding GlobalTheory.T.smaller_unitary_embedding_preserves_integral_parts GlobalTheory.T.unitary_diagonal_factorization_along_embedding GlobalTheory.T.unitary_levi_normalizes_unipotent_radical
    (GlobalTheory.T.unitaryUnipotentRadicalSplitting_of_leviPart GlobalTheory.T.unitary_block_triangular_levi_part_unitary) GlobalTheory.T.unitary_dominant_diagonal_conjugation_contracts GlobalTheory.T.unitary_levi_centre_diagonal_conjugation_eq
  have hi : IntIndex := GlobalTheory.T.card_integers_mod_uniformizer_eq_q_sq
  have ht : TraceZeroIndex := GlobalTheory.T.traceZeroIntegersModUniformizerCard_of_cardSq hi
  exact satWeyl_of_coeff (GlobalTheory.T.unitarySatakeCoeff_adjacentSwap_of_leviReduction hl (GlobalTheory.T.unitaryFourLeviGL2RootIndex_of_cardSq hi) GlobalTheory.T.unitaryFourLeviGL2_cartan_doubleCosets)
    (GlobalTheory.T.unitarySatakeCoeff_lastSignChange_of_leviReduction hl (GlobalTheory.T.unitaryRankTwoRootIndex_of_traceZeroCard ht) (GlobalTheory.T.unitaryRankThreeRootIndex_of_cards hi ht))

end GlobalTheory.SatakeWeyl

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeWeylInvariantStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySatake_weylInvariant : Formalism.UG.SatWeyl := by
  first | exact @GlobalTheory.SatakeWeyl.satWeyl | exact GlobalTheory.SatakeWeyl.satWeyl | (intros; apply GlobalTheory.SatakeWeyl.satWeyl <;> assumption)
end
