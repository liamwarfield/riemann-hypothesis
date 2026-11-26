module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CartanDecompositionCongruence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingDoubleCosetMeasurable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingDoubleCosetVolumeBound

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEmbeddingMemLeviStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_embedding_mem_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (g : Levi k (fun a => Fin (d a))), leviEmb k (stdBlocks d hd) g ∈ GroundTheory.Automorphic.Parabolic.levi k N (Zl.JC.blockIdx d hd) := by
  intro k _ _ _ _ h N d hd g
  rw [GroundTheory.Automorphic.Parabolic.mem_levi]
  intro i j hij
  obtain ⟨⟨a, x⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := (stdBlocks d hd).surjective j
  have hab : a ≠ b := by
    simpa [Zl.JC.blockIdx] using hij
  exact leviEmb_apply_ne k (stdBlocks d hd) g hab x y
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusContractingBlockLtOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusContractingBlockLtOne
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JCModulus

theorem prod_zpow_eq {ι : Type*} {x : ℝ} (hx : x ≠ 0) (s : Finset ι) (f : ι → ℤ) :
    ∏ a ∈ s, x ^ f a = x ^ ∑ a ∈ s, f a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add₀ hx, ih]

theorem exponent_eq {h : ℕ} (d : Fin h → ℕ) (j : Fin h) :
    ∑ a, (if a ≤ j then (d a : ℤ) * modExp (fun a => Fin (d a)) a else 0) =
      (∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ) := by
  set f : Fin h → Fin h → ℤ := fun a b =>
    (d a : ℤ) * ((d b : ℤ) * ((if a < b then 1 else 0) - (if b < a then 1 else 0))) with hf
  have hm : ∀ a, (d a : ℤ) * modExp (fun a => Fin (d a)) a = ∑ b, f a b := by
    intro a
    rw [← Finset.mul_sum]
    congr 1
    simp [modExp, Finset.sum_filter, mul_sub, Finset.sum_sub_distrib]
  have hanti : ∀ a b, f b a = - f a b := by
    intro a b
    simp only [hf]
    ring
  have hcancel : ∑ a with a ≤ j, ∑ b with b ≤ j, f a b = 0 := by
    have h1 : ∑ a with a ≤ j, ∑ b with b ≤ j, f a b = ∑ a with a ≤ j, ∑ b with b ≤ j, f b a :=
      Finset.sum_comm
    have h2 : ∑ a with a ≤ j, ∑ b with b ≤ j, f b a = - ∑ a with a ≤ j, ∑ b with b ≤ j, f a b := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => hanti a b
    omega
  have hcross : ∑ a with a ≤ j, ∑ b with j < b, f a b =
      (∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    have hab : a < b := lt_of_le_of_lt (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2
    simp [hf, hab, hab.not_gt]
  calc ∑ a, (if a ≤ j then (d a : ℤ) * modExp (fun a => Fin (d a)) a else 0)
      = ∑ a with a ≤ j, ∑ b, f a b := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun a _ => by rw [hm]
    _ = ∑ a with a ≤ j, ((∑ b with b ≤ j, f a b) + ∑ b with j < b, f a b) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ≤ j)]
        simp only [not_le]
    _ = _ := by rw [Finset.sum_add_distrib, hcancel, zero_add, hcross]

theorem nabs_lt_one_of_valuation_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : kˣ) (ht : ValuativeRel.valuation k (t : k) < 1) :
    nabs k t < 1 := by
  obtain ⟨-, -, hle, hone, -⟩ := nabs_properties k
  have h1 : nabs k (1 : kˣ) = 1 := (hone 1).2 (by simp)
  refine lt_of_le_of_ne ?_ fun h => ht.ne ((hone t).1 h)
  rw [← h1]
  exact (hle t 1).2 (by simpa using ht.le)

theorem modulus_zj_lt_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) →
    ∀ (t : kˣ), ValuativeRel.valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h →
    modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) < 1 := by
  intro k _ _ _ _ h N d _ hpos t ht j hj
  have hx1 := nabs_lt_one_of_valuation_lt_one k t ht
  obtain ⟨hmul, hx0', -, hone, -⟩ := nabs_properties k
  have hx0 := hx0' t
  have hdet : ∀ a, nabs k (Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a)) =
      if a ≤ j then nabs k t ^ d a else 1 := by
    intro a
    have hpow : ∀ n : ℕ, nabs k (t ^ n) = nabs k t ^ n := by
      intro n
      induction n with
      | zero => simpa using (hone 1).2 (by simp)
      | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
    by_cases ha : a ≤ j
    · have h1 : Matrix.GeneralLinearGroup.det (Zl.JC.zj d t j a) = t ^ d a := by
        apply Units.ext
        simp [Zl.JC.zj, ha, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.det_diagonal]
      rw [h1, hpow, if_pos ha]
    · have h1 : Zl.JC.zj d t j a = 1 := by simp [Zl.JC.zj, ha]
      rw [h1, if_neg ha, map_one]
      exact (hone 1).2 (by simp)
  have hE : 0 < (∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ) := by
    refine mul_pos (Finset.sum_pos (fun a _ => by exact_mod_cast hpos a) ⟨j, by simp⟩)
      (Finset.sum_pos (fun a _ => by exact_mod_cast hpos a) ⟨⟨j.val + 1, hj⟩, ?_⟩)
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Fin.lt_def.2 (Nat.lt_succ_self _)⟩
  have hmod : modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) =
      nabs k t ^ ((∑ a with a ≤ j, (d a : ℤ)) * ∑ b with j < b, (d b : ℤ)) := by
    rw [← exponent_eq, ← prod_zpow_eq hx0.ne']
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [hdet]
    split_ifs with ha
    · rw [zpow_mul, zpow_natCast]
    · simp
  rw [hmod]
  exact zpow_lt_one₀ hx0 hx1 hE

end GlobalTheory.CompanionTheory.JCModulus
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusContractingBlockLtOneStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_contracting_block_lt_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) → ∀ (t : kˣ), ValuativeRel.valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h → modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j) < 1 := by
  first | exact @GlobalTheory.CompanionTheory.JCModulus.modulus_zj_lt_one | exact GlobalTheory.CompanionTheory.JCModulus.modulus_zj_lt_one | (intros; apply GlobalTheory.CompanionTheory.JCModulus.modulus_zj_lt_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientScalarActionMod
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientScalarActionMod
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.SubQuotScalar

theorem sub_smul_mem_of_equiv_subQuot :
    ∀ {M W X : Type} [Group M] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
      (ρ : Representation ℂ M W) (σ : Representation ℂ M X) (S T : Subrepresentation ρ),
      Nonempty ((subQuot S T).Equiv σ) → ∀ (g : M) (c : ℂ), (∀ x, σ g x = c • x) →
        ∀ s ∈ S.toSubmodule, ρ g s - c • s ∈ T.toSubmodule := by
  intro M W X _ _ _ _ _ ρ σ S T he g c hσ s hs
  obtain ⟨e⟩ := he
  have hinj : Function.Injective e.toIntertwiningMap.toLinearMap := e.left_inv.injective
  have key : e.toIntertwiningMap.toLinearMap
        (GlobalTheory.SmGL.subQuot S T g (Submodule.Quotient.mk ⟨s, hs⟩)) =
      e.toIntertwiningMap.toLinearMap (c • Submodule.Quotient.mk ⟨s, hs⟩) := by
    rw [map_smul, ← hσ]
    exact LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) _
  have h2 := hinj key
  have h3 : (Submodule.Quotient.mk ⟨ρ g s, S.2 g hs⟩ :
        ↥S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) =
      Submodule.Quotient.mk (c • (⟨s, hs⟩ : ↥S.toSubmodule)) := h2
  rw [Submodule.Quotient.eq] at h3
  exact h3

end GlobalTheory.CompanionTheory.SubQuotScalar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubquotientScalarActionModStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subquotient_scalar_action_mod : ∀ {M W X : Type} [Group M] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ M W) (σ : Representation ℂ M X) (S T : Subrepresentation ρ), Nonempty ((subQuot S T).Equiv σ) → ∀ (g : M) (c : ℂ), (∀ x, σ g x = c • x) → ∀ s ∈ S.toSubmodule, ρ g s - c • s ∈ T.toSubmodule := by
  first | exact @GlobalTheory.CompanionTheory.SubQuotScalar.sub_smul_mem_of_equiv_subQuot | exact GlobalTheory.CompanionTheory.SubQuotScalar.sub_smul_mem_of_equiv_subQuot | (intros; apply GlobalTheory.CompanionTheory.SubQuotScalar.sub_smul_mem_of_equiv_subQuot <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothRepIsSmoothFoundation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothRepIsSmoothFoundation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.SmoothTransfer

theorem isSmooth_found : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → GroundTheory.Automorphic.IsSmooth π := by
  intro k _ _ _ _ N V _ _ π h
  exact h

end GlobalTheory.CompanionTheory.SmoothTransfer
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothRepIsSmoothFoundationStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_rep_is_smooth_foundation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → GroundTheory.Automorphic.IsSmooth π := by
  first | exact @GlobalTheory.CompanionTheory.SmoothTransfer.isSmooth_found | exact GlobalTheory.CompanionTheory.SmoothTransfer.isSmooth_found | (intros; apply GlobalTheory.CompanionTheory.SmoothTransfer.isSmooth_found <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleCentralLeviCongruence
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleCentralLeviCongruence
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JacquetCoeff

theorem exists_coeff_geometric : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GroundTheory.Automorphic.IsAdmissible π → ∀ {h : ℕ} (β : Fin N → Fin h), Monotone β → ∀ (m : ℕ), 1 ≤ m → ∀ (a : GL (Fin N) k) (ha : a ∈ GroundTheory.Automorphic.Parabolic.levi k N β), (∀ y ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a * y = y * a) → (∀ u ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N β, a * u * a⁻¹ ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N β) → (∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β, a⁻¹ * z * a ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β) → ∀ (y : GroundTheory.Automorphic.Parabolic.JacquetModule k N β π) (Λ : ℂ), y ≠ 0 → (∀ g : GroundTheory.Automorphic.Parabolic.levi k N β, (g : GL (Fin N) k) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π g y = y) → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ y = Λ • y → ∃ (w : V) (l : Module.Dual ℂ V), (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, π g w = w) ∧ (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, l ∘ₗ π g = l) ∧ ∀ j : ℕ, l (π (a ^ j) w) = Λ ^ j := by
  classical
  intro k _ _ _ _ N V _ _ π hπ h β _ m hm a ha hcomm _ hconj y Λ hy hyK hΛ
  have hKc := GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k N m
  have hKo := GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m
  have hyfix : y ∈ GroundTheory.Automorphic.fixedVectors (GroundTheory.Automorphic.Parabolic.jacquetAction k N β π)
      ((GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m).subgroupOf
        (GroundTheory.Automorphic.Parabolic.levi k N β)) :=
    fun g hg => hyK g (Subgroup.mem_subgroupOf.1 hg)
  obtain ⟨⟨w, hw⟩, hwy⟩ :=
    GroundTheory.Automorphic.Parabolic.jacquetFixedMap_surjective_congruenceSubgroup β hπ hm ⟨y, hyfix⟩
  have hqw : Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) w = y :=
    congrArg Subtype.val hwy
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π),
      f y = 1 := by
    have h0 : ¬ ∀ f : Module.Dual ℂ (GroundTheory.Automorphic.Parabolic.JacquetModule k N β π), f y = 0 :=
      fun h' => hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 h')
    push_neg at h0
    obtain ⟨f, hf⟩ := h0
    exact ⟨(f y)⁻¹ • f, by simp [hf]⟩

  have hpowc : ∀ j : ℕ, ∀ g ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a ^ j * g = g * a ^ j := by
    intro j g hg
    exact ((show Commute a g from hcomm g hg).pow_left j)
  have hpowz : ∀ j : ℕ, ∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓
      GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β,
      (a ^ j)⁻¹ * z * a ^ j ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓
        GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β := by
    intro j
    induction j with
    | zero => intro z hz; simpa using hz
    | succ j ih =>
      intro z hz
      have := hconj _ (ih z hz)
      have e : (a ^ (j + 1))⁻¹ * z * a ^ (j + 1) = a⁻¹ * ((a ^ j)⁻¹ * z * a ^ j) * a := by
        rw [pow_succ]; group
      rwa [e]
  have hq : ∀ j : ℕ, Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) (π (a ^ j) w) =
      Λ ^ j • y := by
    intro j
    induction j with
    | zero => simp [hqw]
    | succ j ih =>
      have e : π (a ^ (j + 1)) w = π a (π (a ^ j) w) := by
        rw [pow_succ', map_mul, Module.End.mul_apply]
      have e2 := GroundTheory.Automorphic.Parabolic.jacquetAction_mk (F := k) (n := N) (β := β) π ⟨a, ha⟩
        (π (a ^ j) w)
      rw [e]
      refine e2.symm.trans ?_
      rw [ih, map_smul, hΛ, smul_smul, pow_succ]
  have hkey : ∀ j : ℕ, Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype)
      (GroundTheory.Automorphic.fixedProj π hπ.1 hKc hKo (π (a ^ j) w) : V) =
      Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) (π (a ^ j) w) := by
    intro j
    refine GroundTheory.Automorphic.Parabolic.mk_fixedProj_eq hπ.1 hKc hKo
      (GroundTheory.Automorphic.Parabolic.congruenceSubgroup_iwahoriFactorization' β hm)
      (fun z hz => ?_) (fun g hg => ?_)
    · have hz' := (Subgroup.mem_inf.1 (hpowz j z hz)).1
      have hzeq : z = a ^ j * ((a ^ j)⁻¹ * z * a ^ j) * (a ^ j)⁻¹ := by group
      have : π z (π (a ^ j) w) = π (a ^ j) (π ((a ^ j)⁻¹ * z * a ^ j) w) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [this, hw _ hz']
    · have hc := hpowc j g (Subgroup.mem_inf.1 hg).2
      rw [← Module.End.mul_apply, ← map_mul, ← hc, map_mul, Module.End.mul_apply,
        hw g (Subgroup.mem_inf.1 hg).1]
  refine ⟨w, f ∘ₗ Representation.Coinvariants.mk
      (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N β).subtype) ∘ₗ
      (GroundTheory.Automorphic.fixedVectors π
        (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m)).subtype ∘ₗ
      GroundTheory.Automorphic.fixedProj π hπ.1 hKc hKo, hw, ?_, ?_⟩
  · intro g hg
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [GroundTheory.Automorphic.fixedProj_apply_act hπ.1 hKc hKo hg]
  · intro j
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
    rw [hkey j, hq j, map_smul, hf, smul_eq_mul, mul_one]

end GlobalTheory.CompanionTheory.JacquetCoeff
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleCentralLeviCongruenceStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_central_levi_congruence : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), GroundTheory.Automorphic.IsAdmissible π → ∀ {h : ℕ} (β : Fin N → Fin h), Monotone β → ∀ (m : ℕ), 1 ≤ m → ∀ (a : GL (Fin N) k) (ha : a ∈ GroundTheory.Automorphic.Parabolic.levi k N β), (∀ y ∈ GroundTheory.Automorphic.Parabolic.levi k N β, a * y = y * a) → (∀ u ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N β, a * u * a⁻¹ ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N β) → (∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β, a⁻¹ * z * a ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N β) → ∀ (y : GroundTheory.Automorphic.Parabolic.JacquetModule k N β π) (Λ : ℂ), y ≠ 0 → (∀ g : GroundTheory.Automorphic.Parabolic.levi k N β, (g : GL (Fin N) k) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π g y = y) → GroundTheory.Automorphic.Parabolic.jacquetAction k N β π ⟨a, ha⟩ y = Λ • y → ∃ (w : V) (l : Module.Dual ℂ V), (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, π g w = w) ∧ (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, l ∘ₗ π g = l) ∧ ∀ j : ℕ, l (π (a ^ j) w) = Λ ^ j := by
  first | exact @GlobalTheory.CompanionTheory.JacquetCoeff.exists_coeff_geometric | exact GlobalTheory.CompanionTheory.JacquetCoeff.exists_coeff_geometric | (intros; apply GlobalTheory.CompanionTheory.JacquetCoeff.exists_coeff_geometric <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingCentralUnipotentCongruence
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingCentralUnipotentCongruence
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

noncomputable section

namespace GlobalTheory.CompanionTheory.ZjContract

open GroundTheory.Automorphic GroundTheory.Automorphic.Parabolic GroundTheory.Automorphic.GLnLocal
open GroundTheory.Automorphic.Iwasawa ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem diagGL_conj_mem {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α} {m : ℕ}
    (D : Fin n → kˣ)
    (hlt : ∀ i l, β i < β l → valuation k ((D i : k) * ((D l)⁻¹ : kˣ)) ≤ 1)
    (heq : ∀ i l, β i = β l → D i = D l)
    {u : GL (Fin n) k} (hu : u ∈ congruenceSubgroup k n m ⊓ unipotentRadical k n β) :
    diagGL k n D * u * (diagGL k n D)⁻¹ ∈
      congruenceSubgroup k n m ⊓ unipotentRadical k n β := by
  have hb : ∀ w ∈ congruenceSubgroup k n m ⊓ unipotentRadical k n β, ∀ i l,
      valuation k ((diagGL k n D * w * (diagGL k n D)⁻¹ : GL (Fin n) k) i l -
        (1 : Matrix (Fin n) (Fin n) k) i l) ≤
          valuation k ((uniformizer k : 𝒪[k]) : k) ^ m := by
    intro w hw i l
    obtain ⟨hwK, hwN⟩ := Subgroup.mem_inf.1 hw
    obtain ⟨hwP, hw1⟩ := mem_unipotentRadical.1 hwN
    rw [diagGL_conj_apply]
    rcases lt_trichotomy (β i) (β l) with h | h | h
    · have hil : i ≠ l := fun e => h.ne (by rw [e])
      have hK := ((mem_congruenceSubgroup_iff k n).1 hwK).2 i l
      rw [one_apply_ne hil, sub_zero] at hK ⊢
      have e : (D i : k) * w i l * (((D l)⁻¹ : kˣ) : k) =
          ((D i : k) * (((D l)⁻¹ : kˣ) : k)) * w i l := by ring
      rw [e, map_mul]
      exact (mul_le_mul' (hlt i l h) hK).trans (by rw [one_mul])
    · rw [hw1 i l h, heq i l h]
      have : (D l : k) * (1 : Matrix (Fin n) (Fin n) k) i l * (((D l)⁻¹ : kˣ) : k) =
          (1 : Matrix (Fin n) (Fin n) k) i l := by
        rw [mul_right_comm, Units.mul_inv, one_mul]
      rw [this, sub_self, map_zero]
      exact zero_le
    · have hil : i ≠ l := fun e => h.ne' (by rw [e])
      have h0 : w i l = 0 := hwP h
      rw [h0, mul_zero, zero_mul, one_apply_ne hil, sub_zero, map_zero]
      exact zero_le
  have hP : diagGL k n D ∈ blockUpper k n β := levi_le_blockUpper (diagGL_mem_levi D)
  have hentry : ∀ w ∈ congruenceSubgroup k n m ⊓ unipotentRadical k n β, ∀ i l,
      valuation k ((diagGL k n D * w * (diagGL k n D)⁻¹ : GL (Fin n) k) i l) ≤ 1 := by
    intro w hw i l
    have he : valuation k ((1 : Matrix (Fin n) (Fin n) k) i l) ≤ 1 := by
      by_cases h : i = l <;> simp [Matrix.one_apply, h]
    have eq : (diagGL k n D * w * (diagGL k n D)⁻¹ : GL (Fin n) k) i l =
        ((diagGL k n D * w * (diagGL k n D)⁻¹ : GL (Fin n) k) i l -
          (1 : Matrix (Fin n) (Fin n) k) i l) + (1 : Matrix (Fin n) (Fin n) k) i l := by ring
    rw [eq]
    exact ((valuation k).map_add _ _).trans
      (max_le ((hb w hw i l).trans (pow_le_one' (valuation_uniformizer_lt_one k).le m)) he)
  refine Subgroup.mem_inf.2 ⟨(mem_congruenceSubgroup_iff k n).2 ⟨?_, hb u hu⟩,
    conj_mem_unipotentRadical hP (Subgroup.mem_inf.1 hu).2⟩
  refine (mem_integralGL_iff k n).2 ⟨hentry u hu, ?_⟩
  have eq : (diagGL k n D * u * (diagGL k n D)⁻¹)⁻¹ =
      diagGL k n D * u⁻¹ * (diagGL k n D)⁻¹ := by group
  rw [eq]
  exact hentry _ (Subgroup.inv_mem _ hu)

def zjDiag {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) : Fin N → kˣ :=
  fun i => if Zl.JC.blockIdx d hd i ≤ j then t else 1

theorem leviEmb_zj {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) :
    leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) = diagGL k N (zjDiag d hd t j) := by
  apply Units.ext
  ext x y
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks d hd).surjective x
  obtain ⟨⟨b, l⟩, rfl⟩ := (stdBlocks d hd).surjective y
  rw [coe_diagGL]
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    have hb : Zl.JC.blockIdx d hd (stdBlocks d hd ⟨a, i⟩) = a := by simp [Zl.JC.blockIdx]
    by_cases hil : i = l
    · subst hil
      rw [diagonal_apply_eq]
      by_cases hj : a ≤ j
      · have hz : Zl.JC.zj d t j a = Matrix.GeneralLinearGroup.scalar (Fin (d a)) t := if_pos hj
        have hD : zjDiag d hd t j (stdBlocks d hd ⟨a, i⟩) = t := by
          simp only [zjDiag, hb, if_pos hj]
        rw [hz, hD]
        simp
      · have hz : Zl.JC.zj d t j a = 1 := if_neg hj
        have hD : zjDiag d hd t j (stdBlocks d hd ⟨a, i⟩) = 1 := by
          simp only [zjDiag, hb, if_neg hj]
        rw [hz, hD]
        simp
    · have hne : stdBlocks d hd ⟨a, i⟩ ≠ stdBlocks d hd ⟨a, l⟩ := fun e =>
        hil (by simpa using (stdBlocks d hd).injective e)
      rw [diagonal_apply_ne _ hne]
      by_cases hj : a ≤ j
      · have hz : Zl.JC.zj d t j a = Matrix.GeneralLinearGroup.scalar (Fin (d a)) t := if_pos hj
        rw [hz]
        simp [hil]
      · have hz : Zl.JC.zj d t j a = 1 := if_neg hj
        rw [hz]
        simp [hil]
  · rw [leviEmb_apply_ne k _ _ hab, diagonal_apply_ne]
    intro e
    exact hab (congrArg Sigma.fst ((stdBlocks d hd).injective e))

theorem zjDiag_ratio {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) {t : kˣ}
    (ht : valuation k (t : k) ≤ 1) (j : Fin h) {i l : Fin N}
    (hil : Zl.JC.blockIdx d hd i < Zl.JC.blockIdx d hd l) :
    valuation k ((zjDiag d hd t j i : k) * (((zjDiag d hd t j l)⁻¹ : kˣ) : k)) ≤ 1 := by
  unfold zjDiag
  by_cases hi : Zl.JC.blockIdx d hd i ≤ j
  · by_cases hl : Zl.JC.blockIdx d hd l ≤ j
    · simp [if_pos hi, if_pos hl]
    · simpa [if_pos hi, if_neg hl] using ht
  · have hl : ¬ Zl.JC.blockIdx d hd l ≤ j := fun e => hi (hil.le.trans e)
    simp [if_neg hi, if_neg hl]

theorem zjDiag_eq {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) {i l : Fin N}
    (hil : Zl.JC.blockIdx d hd i = Zl.JC.blockIdx d hd l) :
    zjDiag d hd t j i = zjDiag d hd t j l := by
  simp only [zjDiag, hil]

theorem zj_contract : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ), ValuativeRel.valuation k (t : k) ≤ 1 → ∀ (j : Fin h) (m : ℕ), (∀ u ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd), leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) * u * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j))⁻¹ ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd)) ∧ (∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N (Zl.JC.blockIdx d hd), (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j))⁻¹ * z * leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N (Zl.JC.blockIdx d hd)) := by
  intro k _ _ _ _ h N d hd t ht j m
  rw [leviEmb_zj]
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · exact diagGL_conj_mem _ (fun i l hil => zjDiag_ratio d hd ht j hil)
      (fun i l hil => zjDiag_eq d hd t j hil) hu
  · have key := diagGL_conj_mem (β := OrderDual.toDual ∘ Zl.JC.blockIdx d hd)
      (zjDiag d hd t j)⁻¹
      (fun i l hil => by
        have hil' : Zl.JC.blockIdx d hd l < Zl.JC.blockIdx d hd i := hil
        have := zjDiag_ratio d hd ht j hil'
        simpa [Pi.inv_apply, mul_comm] using this)
      (fun i l hil => by
        have hil' : Zl.JC.blockIdx d hd i = Zl.JC.blockIdx d hd l := hil
        simp only [Pi.inv_apply, zjDiag_eq d hd t j hil'])
      (u := z) hz
    rw [map_inv, inv_inv] at key
    exact key

end GlobalTheory.CompanionTheory.ZjContract

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingCentralUnipotentCongruenceStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contracting_central_unipotent_congruence : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ), ValuativeRel.valuation k (t : k) ≤ 1 → ∀ (j : Fin h) (m : ℕ), (∀ u ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd), leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) * u * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j))⁻¹ ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (Zl.JC.blockIdx d hd)) ∧ (∀ z ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N (Zl.JC.blockIdx d hd), (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j))⁻¹ * z * leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m ⊓ GroundTheory.Automorphic.Parabolic.oppositeUnipotentRadical k N (Zl.JC.blockIdx d hd)) := by
  first | exact @GlobalTheory.CompanionTheory.ZjContract.zj_contract | exact GlobalTheory.CompanionTheory.ZjContract.zj_contract | (intros; apply GlobalTheory.CompanionTheory.ZjContract.zj_contract <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LpCoefficientCenterNormPreserved
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LpCoefficientCenterNormPreserved
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.CoeffCentral

theorem norm_coeff_central : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (p : ℝ), CoeffLp p π → ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ (v : V) (l : Module.Dual ℂ V), IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l} → ‖l (π z v)‖ = ‖l v‖ := by
  intro k _ _ _ _ N V _ _ π p h z hz v l hl
  borelize (AdGL k N)
  obtain ⟨F, hF, -⟩ := h MeasureTheory.Measure.haar inferInstance v l hl
  have h1 : (QuotientGroup.mk z : AdGL k N) = QuotientGroup.mk 1 := by
    rw [QuotientGroup.mk_one]
    exact (QuotientGroup.eq_one_iff z).2 hz
  have h2 := hF z
  rw [h1, hF 1] at h2
  simpa using h2.symm

end GlobalTheory.CompanionTheory.CoeffCentral
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LpCoefficientCenterNormPreservedStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lp_coefficient_center_norm_preserved : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (p : ℝ), CoeffLp p π → ∀ z ∈ Subgroup.center (GL (Fin N) k), ∀ (v : V) (l : Module.Dual ℂ V), IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l} → ‖l (π z v)‖ = ‖l v‖ := by
  first | exact @GlobalTheory.CompanionTheory.CoeffCentral.norm_coeff_central | exact GlobalTheory.CompanionTheory.CoeffCentral.norm_coeff_central | (intros; apply GlobalTheory.CompanionTheory.CoeffCentral.norm_coeff_central <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfPowTendstoZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfPowTendstoZero
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.Val

theorem valuation_lt_one_of_tendsto_pow_zero :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      ∀ t : kˣ, Filter.Tendsto (fun n : ℕ => (t : k) ^ n) Filter.atTop (nhds 0) →
        ValuativeRel.valuation k (t : k) < 1 := by
  intro k _ _ _ _ t ht
  by_contra hge
  have hge' : 1 ≤ ValuativeRel.valuation k (t : k) := not_lt.mp hge
  have hU : {x : k | ValuativeRel.valuation k x < 1} ∈ nhds (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem one_ne_zero
  obtain ⟨n, hn⟩ := (ht.eventually hU).exists
  have hn' : ValuativeRel.valuation k ((t : k) ^ n) < 1 := hn
  rw [map_pow] at hn'
  exact absurd hn' (not_lt.mpr (one_le_pow₀ hge'))

end GlobalTheory.CompanionTheory.Val
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfPowTendstoZeroStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_lt_one_of_pow_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ t : kˣ, Filter.Tendsto (fun n : ℕ => (t : k) ^ n) Filter.atTop (nhds 0) → ValuativeRel.valuation k (t : k) < 1 := by
  first | exact @GlobalTheory.CompanionTheory.Val.valuation_lt_one_of_tendsto_pow_zero | exact GlobalTheory.CompanionTheory.Val.valuation_lt_one_of_tendsto_pow_zero | (intros; apply GlobalTheory.CompanionTheory.Val.valuation_lt_one_of_tendsto_pow_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiTensorCentralBlockScalar
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiTensorCentralBlockScalar
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.JCScalar

theorem piTensor_zj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL (k := k)) (t : kˣ) (c : Fin h → ℂ), (∀ i, Zl.ScalarBy (x i) t (c i)) → ∀ (j : Fin h) (v : PiTensorProduct ℂ (fun a => (x a).2.rep.V)), piTensor (fun a => (x a).rep) (Zl.JC.zj (fun a => (x a).1) t j) v = (∏ i ∈ Finset.univ.filter (· ≤ j), c i) • v := by
  intro k _ _ _ _ h x t c hc j v
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, smul_comm, piTensor_tprod]
    congr 1
    have hf : ∀ a, (x a).rep (Zl.JC.zj (fun a => (x a).1) t j a) (f a)
        = (if a ≤ j then c a else 1) • f a := by
      intro a
      by_cases ha : a ≤ j
      · simp only [Zl.JC.zj, if_pos ha]
        exact hc a (f a)
      · simp [Zl.JC.zj, if_neg ha]
    simp only [hf]
    rw [MultilinearMap.map_smul_univ, Finset.prod_filter]
    simp only [RingHom.id_apply]
  | add a b ha hb => rw [map_add (f := _), ha, hb, smul_add]

end GlobalTheory.CompanionTheory.JCScalar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiTensorCentralBlockScalarStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pi_tensor_central_block_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL (k := k)) (t : kˣ) (c : Fin h → ℂ), (∀ i, Zl.ScalarBy (x i) t (c i)) → ∀ (j : Fin h) (v : PiTensorProduct ℂ (fun a => (x a).2.rep.V)), piTensor (fun a => (x a).rep) (Zl.JC.zj (fun a => (x a).1) t j) v = (∏ i ∈ Finset.univ.filter (· ≤ j), c i) • v := by
  first | exact @GlobalTheory.CompanionTheory.JCScalar.piTensor_zj | exact GlobalTheory.CompanionTheory.JCScalar.piTensor_zj | (intros; apply GlobalTheory.CompanionTheory.JCScalar.piTensor_zj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeOneOfPowerBounds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeOneOfPowerBounds
open Filter Topology

namespace GlobalTheory.CompanionTheory.Casselman

theorem le_one_of_forall_sqrt_mul_rpow_lt :
    ∀ (δ r : ℝ), 0 < δ → δ < 1 → 0 ≤ r →
      (∀ ε : ℝ, 0 < ε → δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε) < 1) → r ≤ 1 := by
  intro δ r hδ hδ1 hr h
  by_contra hlt
  rw [not_le] at hlt
  have hx : 0 < Real.sqrt δ * r := mul_pos (Real.sqrt_pos.mpr hδ) (by linarith)
  have hcont : ContinuousAt (fun ε : ℝ => δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε)) 0 := by
    apply ContinuousAt.mul continuousAt_const
    exact (Real.continuousAt_const_rpow hx.ne').comp
      (continuous_const.add continuous_id).continuousAt
  have h0 : δ⁻¹ * (Real.sqrt δ * r) ^ ((2 : ℝ) + 0) = r ^ 2 := by
    rw [add_zero, Real.rpow_two, mul_pow, Real.sq_sqrt hδ.le, inv_mul_cancel_left₀ hδ.ne']
  have h1 : (1 : ℝ) < δ⁻¹ * (Real.sqrt δ * r) ^ ((2 : ℝ) + 0) := by
    rw [h0]
    nlinarith
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 1 < δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε) :=
    hcont.eventually (lt_mem_nhds h1)
  obtain ⟨ε, hε1, hε0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[Set.Ioi (0 : ℝ)] 0, x ∈ Set.Ioi (0 : ℝ))).exists
  exact lt_asymm (h ε hε0) hε1

end GlobalTheory.CompanionTheory.Casselman
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeOneOfPowerBoundsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_one_of_power_bounds : ∀ (δ r : ℝ), 0 < δ → δ < 1 → 0 ≤ r → (∀ ε : ℝ, 0 < ε → δ⁻¹ * (Real.sqrt δ * r) ^ (2 + ε) < 1) → r ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt | exact GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt | (intros; apply GlobalTheory.CompanionTheory.Casselman.le_one_of_forall_sqrt_mul_rpow_lt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LtOneOfPowerBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LtOneOfPowerBound
namespace GlobalTheory.CompanionTheory.Casselman

theorem lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one :
    ∀ (δ r : ℝ), 0 < δ → 0 ≤ r → δ⁻¹ * (Real.sqrt δ * r) ^ (2 : ℝ) < 1 → r < 1 := by
  intro δ r hδ hr h
  have h2 : (Real.sqrt δ * r) ^ (2 : ℝ) = δ * r ^ 2 := by
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt hδ.le]
  rw [h2, ← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul] at h
  nlinarith

end GlobalTheory.CompanionTheory.Casselman
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LtOneOfPowerBoundStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lt_one_of_power_bound : ∀ (δ r : ℝ), 0 < δ → 0 ≤ r → δ⁻¹ * (Real.sqrt δ * r) ^ (2 : ℝ) < 1 → r < 1 := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one | exact GlobalTheory.CompanionTheory.Casselman.lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one | (intros; apply GlobalTheory.CompanionTheory.Casselman.lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantFunctionalOpenStabilizer
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantFunctionalOpenStabilizer
namespace GlobalTheory.CompanionTheory.Smooth

def linearFormStabiliser {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) : Subgroup G where
  carrier := {g : G | l ∘ₗ ρ g = l}
  mul_mem' := by
    intro a b ha hb
    have ha' : l ∘ₗ ρ a = l := ha
    have hb' : l ∘ₗ ρ b = l := hb
    show l ∘ₗ ρ (a * b) = l
    rw [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ha', hb']
  one_mem' := by
    show l ∘ₗ ρ 1 = l
    rw [map_one]
    rfl
  inv_mem' := by
    intro a ha
    have ha' : l ∘ₗ ρ a = l := ha
    show l ∘ₗ ρ a⁻¹ = l
    conv_lhs => rw [← ha']
    rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]
    rfl

theorem isOpen_linearForm_stabiliser {G V : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (hK : IsOpen (K : Set G)) (l : Module.Dual ℂ V)
    (hl : ∀ x ∈ K, l ∘ₗ ρ x = l) : IsOpen {g : G | l ∘ₗ ρ g = l} :=
  Subgroup.isOpen_mono (H₁ := K) (H₂ := linearFormStabiliser ρ l) (fun x hx => hl x hx) hK

end GlobalTheory.CompanionTheory.Smooth
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantFunctionalOpenStabilizerStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_functional_open_stabilizer : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G), IsOpen (K : Set G) → ∀ l : Module.Dual ℂ V, (∀ x ∈ K, l ∘ₗ ρ x = l) → IsOpen {g : G | l ∘ₗ ρ g = l} := by
  first | exact @GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser | exact GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser | (intros; apply GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NotMemLpOfGrowth
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NotMemLpOfGrowth
open MeasureTheory

namespace GlobalTheory.CompanionTheory.Casselman

theorem mul_rpow_lt_one_of_memLp_geometric {X : Type} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) (f : X → ℝ) (p : ℝ) (hp : 0 < p)
    (hf : MeasureTheory.MemLp f (ENNReal.ofReal p) μ) (E : ℕ → Set X)
    (hE : ∀ j, MeasurableSet (E j)) (hdisj : Pairwise (Function.onFun Disjoint E))
    (c D B r : ℝ) (hc : 0 < c) (hB : 0 < B) (hr : 0 ≤ r)
    (hμ : ∀ j : ℕ, ENNReal.ofReal (c * D ^ j) ≤ μ (E j))
    (hlow : ∀ j : ℕ, ∀ x ∈ E j, B * r ^ j ≤ |f x|) : D * r ^ p < 1 := by
  by_contra hcon
  have hq : 1 ≤ D * r ^ p := not_lt.1 hcon
  have hrp : 0 ≤ r ^ p := Real.rpow_nonneg hr p
  have hD : 0 ≤ D := by
    by_contra hD
    have : D * r ^ p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_le.1 hD).le hrp
    linarith
  have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have hI := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 ENNReal.ofReal_ne_top hf.aestronglyMeasurable).1
    hf.eLpNorm_lt_top
  rw [ENNReal.toReal_ofReal hp.le] at hI
  have ha : 0 < c * B ^ p := mul_pos hc (Real.rpow_pos_of_pos hB p)
  have hterm : ∀ j : ℕ, ENNReal.ofReal (c * B ^ p) ≤ ∫⁻ x in E j, ‖f x‖ₑ ^ p ∂μ := by
    intro j
    have hBr : 0 ≤ B * r ^ j := mul_nonneg hB.le (pow_nonneg hr j)
    have h1 : ∫⁻ _ in E j, ENNReal.ofReal ((B * r ^ j) ^ p) ∂μ ≤ ∫⁻ x in E j, ‖f x‖ₑ ^ p ∂μ := by
      refine setLIntegral_mono' (hE j) fun x hx => ?_
      rw [← ENNReal.ofReal_rpow_of_nonneg hBr hp.le, Real.enorm_eq_ofReal_abs]
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hlow j x hx)) hp.le
    rw [setLIntegral_const] at h1
    refine le_trans ?_ h1
    refine le_trans ?_ (mul_le_mul_right (hμ j) _)
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hBr p)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : (B * r ^ j) ^ p * (c * D ^ j) = c * B ^ p * (D * r ^ p) ^ j := by
      rw [Real.mul_rpow hB.le (pow_nonneg hr j), mul_pow, ← Real.rpow_natCast r j,
        ← Real.rpow_natCast (r ^ p) j, ← Real.rpow_mul hr, ← Real.rpow_mul hr, mul_comm (j : ℝ) p]
      ring
    rw [e]
    exact le_mul_of_one_le_right ha.le (one_le_pow₀ hq)
  have htop : ∑' j : ℕ, ∫⁻ x in E j, ‖f x‖ₑ ^ p ∂μ = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ)
      (ENNReal.ofReal_pos.2 ha).ne']
    exact ENNReal.tsum_le_tsum hterm
  have hle : ∑' j : ℕ, ∫⁻ x in E j, ‖f x‖ₑ ^ p ∂μ ≤ ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
    rw [← lintegral_iUnion hE hdisj]
    exact setLIntegral_le_lintegral _ _
  rw [htop] at hle
  exact absurd (lt_of_le_of_lt hle hI) (lt_irrefl _)

end GlobalTheory.CompanionTheory.Casselman
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NotMemLpOfGrowthStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_mem_Lp_of_growth : ∀ {X : Type} [MeasurableSpace X] (μ : MeasureTheory.Measure X) (f : X → ℝ) (p : ℝ), 0 < p → MeasureTheory.MemLp f (ENNReal.ofReal p) μ → ∀ (E : ℕ → Set X), (∀ j, MeasurableSet (E j)) → Pairwise (Function.onFun Disjoint E) → ∀ (c D B r : ℝ), 0 < c → 0 < B → 0 ≤ r → (∀ j : ℕ, ENNReal.ofReal (c * D ^ j) ≤ μ (E j)) → (∀ j : ℕ, ∀ x ∈ E j, B * r ^ j ≤ |f x|) → D * r ^ p < 1 := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric | exact GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric | (intros; apply GlobalTheory.CompanionTheory.Casselman.mul_rpow_lt_one_of_memLp_geometric <;> assumption)
end
end

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult MeasureTheory

namespace Zl.JC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem claim {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) {h : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N)
    (hjm : Zc.jm x hd π ≠ 0) (t : kˣ) (hv : ValuativeRel.valuation k (t : k) < 1) (c : Fin h → ℂ)
    (hc : ∀ i, Zl.ScalarBy (x i) t (c i)) (j : Fin h) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ (w : V) (l : Module.Dual ℂ V),
      (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, π g w = w) ∧
      (∀ g ∈ GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m, l ∘ₗ π g = l) ∧
      ∀ r : ℕ, l (π ((leviEmb k (stdBlocks (fun a => (x a).1) hd) (zj (fun a => (x a).1) t j)) ^ r) w) =
        ((((deltaHalf k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j) : ℂˣ) : ℂ)) *
          ∏ i ∈ Finset.univ.filter (· ≤ j), c i) ^ r := by
  classical
  have := hi
  have hsF : GroundTheory.Automorphic.IsSmooth π := GlobalTheory.T.smooth_rep_is_smooth_foundation k N π hs
  have hadm : GroundTheory.Automorphic.IsAdmissible π := GroundTheory.Automorphic.Parabolic.isAdmissible_of_isIrreducible hsF
  obtain ⟨S, T, hST⟩ := GlobalTheory.T.jacquet_multiplicity_ne_zero_subquotient k x hd π hjm
  have hscal := GlobalTheory.T.pi_tensor_central_block_scalar k x t c hc j
  set Λ : ℂ := ∏ i ∈ Finset.univ.filter (· ≤ j), c i with hΛdef
  set δ : ℂ := ((deltaHalf k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j) : ℂˣ) : ℂ) with hδdef
  have hmod : ∀ s ∈ S.toSubmodule, jac (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s - Λ • s
      ∈ T.toSubmodule :=
    GlobalTheory.T.subquotient_scalar_action_mod _ _ S T hST (zj (fun a => (x a).1) t j) Λ hscal
  have := GlobalTheory.T.pi_tensor_irreducible_nontrivial k x
  have hΛ : Λ ≠ 0 := by
    intro h0
    obtain ⟨v, hv0⟩ := exists_ne (0 : PiTensorProduct ℂ (fun a => (x a).2.rep.V))
    apply hv0
    have h2 : piTensor (fun a => (x a).rep) (zj (fun a => (x a).1) t j)⁻¹
        (piTensor (fun a => (x a).rep) (zj (fun a => (x a).1) t j) v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hscal v, h0, zero_smul, map_zero] at h2
    exact h2.symm
  have hδ : δ ≠ 0 := Units.ne_zero _
  have hjacU : ∀ s, jacU (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s =
      δ • jac (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s := by
    intro s
    simp only [jac, twist_apply, smul_smul]
    rw [hδdef, ← Units.val_mul, MonoidHom.inv_apply, mul_inv_cancel, Units.val_one, one_smul]
  obtain ⟨e, -, he2⟩ := GlobalTheory.T.jacquet_module_equiv_foundation k N π h (fun a => (x a).1) hd
  have ha := GlobalTheory.T.levi_embedding_mem_levi k h N (fun a => (x a).1) hd (zj (fun a => (x a).1) t j)
  have hcen := GlobalTheory.T.block_central_element_commutes_levi k h N (fun a => (x a).1) hd t j
  have hmono := GlobalTheory.T.block_index_monotone h N (fun a => (x a).1) hd
  set W := S.toSubmodule.map e.toLinearMap
  set T' := (S.toSubmodule ⊓ T.toSubmodule).map e.toLinearMap
  have hle : T' ≤ W := Submodule.map_mono inf_le_left
  have hSU : ∀ s ∈ S.toSubmodule, jacU (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s ∈ S.toSubmodule := by
    intro s hs'
    rw [hjacU]
    exact S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule _ hs')
  have hWst : ∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N (blockIdx (fun a => (x a).1) hd) π ⟨_, ha⟩ w ∈ W := by
    rintro _ ⟨s, hs', rfl⟩
    refine ⟨_, hSU s hs', ?_⟩
    exact he2 _ ha s
  have hWmod : ∀ w ∈ W, GroundTheory.Automorphic.Parabolic.jacquetAction k N (blockIdx (fun a => (x a).1) hd) π ⟨_, ha⟩ w -
      (δ * Λ) • w ∈ T' := by
    rintro _ ⟨s, hs', rfl⟩
    refine ⟨δ • (jac (stdBlocks (fun a => (x a).1) hd) π (zj (fun a => (x a).1) t j) s - Λ • s), ⟨?_, ?_⟩, ?_⟩
    · exact S.toSubmodule.smul_mem _ (S.toSubmodule.sub_mem (S.apply_mem_toSubmodule _ hs') (S.toSubmodule.smul_mem _ hs'))
    · exact T.toSubmodule.smul_mem _ (hmod s hs')
    · simp only [LinearEquiv.coe_coe]
      rw [← he2 _ ha s, hjacU]
      simp only [map_smul, map_sub, smul_sub, smul_smul]
  have hex : ∃ w ∈ W, w ∉ T' := by
    obtain ⟨s, hsS, hsT⟩ := GlobalTheory.T.subquotient_nontrivial_exists_mem _ _ S T hST inferInstance
    refine ⟨e s, ⟨s, hsS, rfl⟩, ?_⟩
    rintro ⟨s', hs', hes⟩
    have : s' = s := e.injective hes
    exact hsT (this ▸ hs'.2)
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.admissible_central_levi_fixed_submodule k N π hadm (blockIdx (fun a => (x a).1) hd) hmono _ ha hcen W T' (δ * Λ)
    (mul_ne_zero hδ hΛ) hle hWst hWmod hex
  obtain ⟨y, hy0, hyfix, hyeig⟩ := hm₀ (max m₀ 1) (le_max_left _ _)
  obtain ⟨hcN, hcNbar⟩ := GlobalTheory.T.contracting_central_unipotent_congruence k h N (fun a => (x a).1) hd t hv.le j (max m₀ 1)
  obtain ⟨w, l, hw, hl, hcoef⟩ := GlobalTheory.T.admissible_central_levi_congruence k N π hadm (blockIdx (fun a => (x a).1) hd) hmono (max m₀ 1)
    (le_max_right _ _) _ ha hcen hcN hcNbar y (δ * Λ) hy0 hyfix hyeig
  exact ⟨max m₀ 1, le_max_right _ _, w, l, hw, hl, hcoef⟩

theorem lpBound {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) {h : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N)
    (hpos : ∀ a, 0 < (x a).1) (hjm : Zc.jm x hd π ≠ 0) (t : kˣ) (hv : ValuativeRel.valuation k (t : k) < 1)
    (c : Fin h → ℂ) (hc : ∀ i, Zl.ScalarBy (x i) t (c i)) (j : Fin h) (hj : j.val + 1 < h) (p : ℝ) (hp : 0 < p)
    (hL : CoeffLp p π) :
    (modulus k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j))⁻¹ *
      (Real.sqrt (modulus k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j)) *
        ‖∏ i ∈ Finset.univ.filter (· ≤ j), c i‖) ^ p < 1 := by
  classical
  obtain ⟨m, hm, w, l, hw, hl, hcoef⟩ := claim π hs hi x hd hjm t hv c hc j
  borelize (AdGL k N)
  have hopen : IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l} :=
    GlobalTheory.T.invariant_functional_open_stabilizer π (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m)
      (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m) l hl
  obtain ⟨F, hF, hFmem⟩ := hL (Measure.haar (G := AdGL k N)) inferInstance w l hopen
  obtain ⟨hmeas, hdisj⟩ := GlobalTheory.T.contracting_double_coset_measurable k h N (fun a => (x a).1) hd hpos t hv j hj m hm
  obtain ⟨c0, hc0, hvol⟩ := GlobalTheory.T.contracting_double_coset_volume_bound k h N (fun a => (x a).1) hd hpos t hv j hj m hm
    (Measure.haar (G := AdGL k N)) inferInstance
  set δ : ℂ := ((deltaHalf k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j) : ℂˣ) : ℂ) with hδdef
  set Λ : ℂ := ∏ i ∈ Finset.univ.filter (· ≤ j), c i
  have hnorm : ‖δ * Λ‖ = Real.sqrt (modulus k (fun a => Fin ((x a).1)) (zj (fun a => (x a).1) t j)) * ‖Λ‖ := by
    rw [norm_mul, hδdef, val_deltaHalf, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [← hnorm]
  refine GlobalTheory.T.not_mem_Lp_of_growth (Measure.haar (G := AdGL k N)) F p hp hFmem _ hmeas hdisj c0 _ 1 ‖δ * Λ‖ hc0 one_pos
    (norm_nonneg _) hvol ?_
  rintro r _ ⟨g, ⟨x1, hx1, y1, hy1, rfl⟩, rfl⟩
  rw [hF, one_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hw y1 hy1]
  have h1 : l (π x1 (π ((leviEmb k (stdBlocks (fun a => (x a).1) hd) (zj (fun a => (x a).1) t j)) ^ r) w)) =
      l (π ((leviEmb k (stdBlocks (fun a => (x a).1) hd) (zj (fun a => (x a).1) t j)) ^ r) w) :=
    LinearMap.congr_fun (hl x1 hx1) _
  rw [h1, hcoef r, norm_pow]
  exact le_of_eq (abs_of_nonneg (by positivity)).symm

theorem totalNorm {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) {h : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N)
    (hjm : Zc.jm x hd π ≠ 0) (t : kˣ) (hv : ValuativeRel.valuation k (t : k) < 1)
    (c : Fin h → ℂ) (hc : ∀ i, Zl.ScalarBy (x i) t (c i)) (hh : 0 < h) (p : ℝ) (hL : CoeffLp p π) :
    ∏ i, ‖c i‖ = 1 := by
  classical
  set jl : Fin h := ⟨h - 1, by omega⟩
  obtain ⟨m, hm, w, l, hw, hl, hcoef⟩ := claim π hs hi x hd hjm t hv c hc jl
  obtain ⟨hsc, hmod1⟩ := GlobalTheory.T.last_block_central_scalar_modulus_one k h N (fun a => (x a).1) hd t jl (by simp [jl]; omega)
  have hopen : IsOpen {g : GL (Fin N) k | l ∘ₗ π g = l} :=
    GlobalTheory.T.invariant_functional_open_stabilizer π (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m)
      (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m) l hl
  have hcent : leviEmb k (stdBlocks (fun a => (x a).1) hd) (zj (fun a => (x a).1) t jl) ∈
      Subgroup.center (GL (Fin N) k) := by
    rw [hsc]
    refine Subgroup.mem_center_iff.2 fun g => Units.ext ?_
    exact (Matrix.scalar_commute (t : k) (fun _ => Commute.all _ _) g.val).symm.eq
  have hc1 := GlobalTheory.T.lp_coefficient_center_norm_preserved k N π p hL _ hcent w l hopen
  have h0 := hcoef 0
  have h1 := hcoef 1
  simp only [pow_zero, map_one, Module.End.one_apply] at h0
  simp only [pow_one] at h1
  rw [h1, h0, norm_one, norm_mul, val_deltaHalf, hmod1, Real.sqrt_one, Complex.ofReal_one, norm_one, one_mul,
    norm_prod] at hc1
  have hfilt : Finset.univ.filter (· ≤ jl) = Finset.univ := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact Fin.le_iff_val_le_val.2 (by simp [jl]; omega)
  rw [hfilt] at hc1
  exact hc1

theorem casselmanNecSq_holds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : Zl.CasselmanNecSq k := by
  intro N V _ _ π hN hs hi hsq h x hd hpos hjm t ht c hc
  have hv := GlobalTheory.T.valuation_lt_one_of_pow_tendsto_zero k t ht
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · simp at hd; omega
    · exact hh
  refine ⟨fun j hj => ?_, totalNorm π hs hi x hd hjm t hv c hc hh 2 hsq⟩
  have key := lpBound π hs hi x hd hpos hjm t hv c hc j hj 2 two_pos hsq
  have := GlobalTheory.T.lt_one_of_power_bound _ _ (modulus_pos k _) (norm_nonneg _) key
  rwa [norm_prod] at this

theorem casselmanNecTemp_holds (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : Zl.CasselmanNecTemp k := by
  intro N V _ _ π hN hs hi htemp h x hd hpos hjm t ht c hc
  have hv := GlobalTheory.T.valuation_lt_one_of_pow_tendsto_zero k t ht
  have hh : 0 < h := by
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · simp at hd; omega
    · exact hh
  refine ⟨fun j hj => ?_, totalNorm π hs hi x hd hjm t hv c hc hh (2 + 1) (htemp 1 one_pos)⟩
  have hlt := GlobalTheory.T.modulus_contracting_block_lt_one k h N (fun a => (x a).1) hd hpos t hv j hj
  have := GlobalTheory.T.le_one_of_power_bounds _ _ (modulus_pos k _) hlt (norm_nonneg _)
    (fun ε hε => lpBound π hs hi x hd hpos hjm t hv c hc j hj (2 + ε) (by linarith) (htemp ε hε))
  rwa [norm_prod] at this

end Zl.JC

end
