module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreading

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UMLeviMulUMLevi
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

open ValuativeRel Topology GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

variable {k : Type} [Field k]

theorem uM_levi_mul_uM_levi (n : ℕ) (y y' : Fin n → k) (b b' : GL (Fin n) k) :
    uM k n y * levi k n b * (uM k n y' * levi k n b') =
      uM k n (y + (b : Matrix (Fin n) (Fin n) k).mulVec y') * levi k n (b * b') := by
  rw [mul_assoc, ← mul_assoc (GlobalTheory.BZMir.levi k n b), GlobalTheory.CompanionTheory.BZPsiPG.levi_mul_uM,
    GlobalTheory.CompanionTheory.BZPsiPG.uM_add, map_mul]
  simp only [mul_assoc]

theorem mirProj_levi_eq (n : ℕ) (g : GL (Fin n) k) : mirabolicProjection k n (levi k n g) = g :=
  GlobalTheory.CompanionTheory.MirLevi.mirProj_levi n g

theorem mirProj_uM (n : ℕ) (y : Fin n → k) : mirabolicProjection k n (uM k n y) = 1 :=
  GlobalTheory.CompanionTheory.MirLevi.mirProj_uv n y

theorem uM_injective (n : ℕ) : Function.Injective (uM k n) := by
  intro y y' h
  funext a
  have entry : ∀ z : Fin n → k, ((GlobalTheory.CompanionTheory.BZPsiPG.uM k n z : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.last n) = z a := by
    intro z
    change (1 + GlobalTheory.BZMir.colMat k n z) (Fin.castSucc a) (Fin.last n) = z a
    simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]
  rw [← entry y, ← entry y', h]

theorem uM_levi_inj (n : ℕ) {y y' : Fin n → k} {g g' : GL (Fin n) k}
    (h : uM k n y * levi k n g = uM k n y' * levi k n g') : y = y' ∧ g = g' := by
  have hg : g = g' := by
    have hp := congrArg (GlobalTheory.BZMir.mirabolicProjection k n) h
    simpa only [map_mul, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mirProj_levi_eq, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mirProj_uM, one_mul] using hp
  subst hg
  exact ⟨GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.uM_injective n (mul_right_cancel h), rfl⟩

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def latt (n : ℕ) (c : kˣ) : AddSubgroup (Fin n → k) where
  carrier := {y | ∀ j, y j ∈ cball c}
  add_mem' ha hb j := add_mem_cball (ha j) (hb j)
  zero_mem' j := by simp [cball]
  neg_mem' ha j := neg_mem_cball (ha j)

theorem mem_latt {n : ℕ} {c : kˣ} {y : Fin n → k} : y ∈ latt n c ↔ ∀ j, y j ∈ cball c :=
  Iff.rfl

theorem latt_eq_pi (n : ℕ) (c : kˣ) : (latt n c : Set (Fin n → k)) = Set.univ.pi fun _ => cball c := by
  ext y
  simp only [SetLike.mem_coe, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mem_latt, Set.mem_univ_pi]

theorem isOpen_latt (n : ℕ) (c : kˣ) : IsOpen (latt n c : Set (Fin n → k)) := by
  rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt_eq_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ => GlobalTheory.SplitWeil.isOpen_cball c

theorem isCompact_latt (n : ℕ) (c : kˣ) : IsCompact (latt n c : Set (Fin n → k)) := by
  rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt_eq_pi]
  exact isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_cball c

theorem isClosed_latt (n : ℕ) (c : kˣ) : IsClosed (latt n c : Set (Fin n → k)) :=
  AddSubgroup.isClosed_of_isOpen _ (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_latt n c)

theorem exists_latt_subset {n : ℕ} {U : Set (Fin n → k)} (hU : U ∈ 𝓝 (0 : Fin n → k)) :
    ∃ c : kˣ, (latt n c : Set (Fin n → k)) ⊆ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  have hmem : (⋂ j, t j) ∈ 𝓝 (0 : k) := Filter.iInter_mem.2 fun j => by simpa using ht j
  obtain ⟨c, hc⟩ := GlobalTheory.SplitWeil.exists_cball_subset hmem
  refine ⟨c, fun y hy => hsub (Set.mem_pi.2 fun j _ => ?_)⟩
  exact Set.mem_iInter.1 (hc (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mem_latt.1 hy j)) j

theorem mulVec_mem_latt {n : ℕ} {c : kˣ} {κ : GL (Fin n) k} (hκ : κ ∈ KO k (Fin n)) {y : Fin n → k}
    (hy : y ∈ latt n c) : (κ : Matrix (Fin n) (Fin n) k).mulVec y ∈ latt n c := by
  rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mem_latt] at hy ⊢
  have hint := ((GlobalTheory.SplitFlip.mem_KO_iff κ).1 hκ).1
  intro j
  change valuation k ((κ : Matrix (Fin n) (Fin n) k).mulVec y j) ≤ valuation k (c : k)
  simp only [Matrix.mulVec, dotProduct]
  apply Valuation.map_sum_le
  intro i _
  rw [map_mul]
  calc valuation k ((κ : Matrix (Fin n) (Fin n) k) j i) * valuation k (y i)
      ≤ 1 * valuation k (c : k) :=
        mul_le_mul' ((Valuation.mem_integer_iff _ _).1 (hint j i)) (hy i)
    _ = valuation k (c : k) := one_mul _

def Bgrp (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (h : K₁ ≤ KO k (Fin n)) : Subgroup (Mir k n) where
  carrier := {p | ∃ y ∈ latt n c, ∃ b ∈ K₁, p = uM k n y * levi k n b}
  mul_mem' := by
    rintro _ _ ⟨y, hy, b, hb, rfl⟩ ⟨y', hy', b', hb', rfl⟩
    exact ⟨_, add_mem hy (mulVec_mem_latt (h hb) hy'), _, mul_mem hb hb', uM_levi_mul_uM_levi n y y' b b'⟩
  one_mem' := ⟨0, zero_mem _, 1, one_mem _, by rw [uM_zero, map_one, one_mul]⟩
  inv_mem' := by
    rintro _ ⟨y, hy, b, hb, rfl⟩
    refine ⟨_, mulVec_mem_latt (h (inv_mem hb)) (neg_mem hy), b⁻¹, inv_mem hb, ?_⟩
    rw [_root_.mul_inv_rev, ← map_inv, GlobalTheory.CompanionTheory.BZPsiPG.Cont.uM_inv, levi_mul_uM]

theorem mem_Bgrp {n : ℕ} {c : kˣ} {K₁ : Subgroup (GL (Fin n) k)} {h : K₁ ≤ KO k (Fin n)} {p : Mir k n} :
    p ∈ Bgrp n c K₁ h ↔ ∃ y ∈ latt n c, ∃ b ∈ K₁, p = uM k n y * levi k n b :=
  Iff.rfl

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralVanishingSubgroup
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralVanishingSubgroup
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

theorem fibV_one_bump : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (z : V ⊗[ℂ] W) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ (h : HPG k i t) (β : Mir k (i + t)), β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK → b.1.1.1 ((h : Mir k (i + t)) * β) = hRep τ σ h z) → (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → fibV b 1 = (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt t c : Set (Fin t → k)).indicator (fun _ => z) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ c K₁ hK z b h1 h2
  funext v
  by_cases hv : v ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt t c
  · rw [Set.indicator_of_mem (show v ∈ (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt t c : Set (Fin t → k)) from hv)]
    have hm : midV k i t v ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt (i + t) c := by
      intro j
      induction j using Fin.addCases with
      | left j =>
        show Fin.append (0 : Fin i → k) v (Fin.castAdd t j) ∈ _
        rw [Fin.append_left]
        exact (zero_mem (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt i c)) j
      | right j =>
        show Fin.append (0 : Fin i → k) v (Fin.natAdd i j) ∈ _
        rw [Fin.append_right]
        exact hv j
    have hp : uM k (i + t) (midV k i t v) * levi k (i + t) 1 ∈
        GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK := ⟨_, hm, 1, one_mem _, rfl⟩
    have e := h1 1 _ hp
    rw [map_one] at e
    simpa [fibV] using e
  · rw [Set.indicator_of_notMem (show v ∉ (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt t c : Set (Fin t → k)) from hv)]
    apply h2
    rintro ⟨h, β, hβ, e⟩
    obtain ⟨x, q, hq⟩ := GlobalTheory.T.parabolic_unipotent_levi_decomp k i t h
    obtain ⟨y, hy, b', hb', rfl⟩ := hβ
    rw [hq, uM_levi_mul_uM_levi] at e
    obtain ⟨e1, e2⟩ := uM_levi_inj _ (show uM k (i + t) (midV k i t v) * levi k (i + t) 1 = _ from e)
    have hq' : (q : GL (Fin (i + t)) k) = b'⁻¹ := eq_inv_of_mul_eq_one_left e2.symm
    apply hv
    intro j
    have e3 := congrFun e1 (Fin.natAdd i j)
    have e4 : midV k i t v (Fin.natAdd i j) = v j := Fin.append_right _ _ _
    have e5 : topV k i t x (Fin.natAdd i j) = 0 := Fin.append_right _ _ _
    rw [Pi.add_apply, e4, e5, zero_add, hq'] at e3
    rw [e3]
    exact mulVec_mem_latt (hK (inv_mem hb')) hy _

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralVanishingSubgroupStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_integral_vanishing_subgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (z : V ⊗[ℂ] W) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ (h : HPG k i t) (β : Mir k (i + t)), β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK → b.1.1.1 ((h : Mir k (i + t)) * β) = hRep τ σ h z) → (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → fibV b 1 = (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt t c : Set (Fin t → k)).indicator (fun _ => z) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.fibV_one_bump | exact GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.fibV_one_bump | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.fibV_one_bump <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTensorFixedParabolicNearOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTensorFixedParabolicNearOne
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.Stab

theorem hRep_fix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ z : V ⊗[ℂ] W, ∃ U ∈ nhds (1 : Mir k (i + t)), ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ U → hRep τ σ h z = z := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ z
  have hs : IsSmooth (hRep τ σ) :=
    isSmooth_comp (isSmooth_extTensor hτ hσ) _ (GlobalTheory.CompanionTheory.BZPhiPG.Onto.continuous_pgProj k i t)
  obtain ⟨O, hO, e⟩ := isOpen_induced_iff.1 (hs z)
  have hmem : ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ O ↔ hRep τ σ h z = z := fun h =>
    Set.ext_iff.1 e h
  have h1 : (1 : Mir k (i + t)) ∈ O := (hmem 1).2 (by simp)
  exact ⟨O, hO.mem_nhds h1, fun h hh => (hmem h).1 hh⟩

end GlobalTheory.CompanionTheory.BZPsiPG.Stab
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTensorFixedParabolicNearOneStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_tensor_fixed_parabolic_near_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ z : V ⊗[ℂ] W, ∃ U ∈ nhds (1 : Mir k (i + t)), ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ U → hRep τ σ h z = z := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.Stab.hRep_fix | exact GlobalTheory.CompanionTheory.BZPsiPG.Stab.hRep_fix | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.Stab.hRep_fix <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralVanishingOpenSubgroup
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralVanishingOpenSubgroup
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibInvK

theorem fibV_mul_right_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (z : V ⊗[ℂ] W) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ (h : HPG k i t) (β : Mir k (i + t)), β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK → b.1.1.1 ((h : Mir k (i + t)) * β) = hRep τ σ h z) → (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → ∀ b' ∈ K₁, ∀ g : GL (Fin (i + t)) k, fibV b (g * b') = fibV b g := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ c K₁ hK z b hval hzero b' hb' g
  have hβ : GlobalTheory.BZMir.levi k (i + t) b' ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK := by
    show ∃ y ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt (i + t) c, ∃ a ∈ K₁,
      GlobalTheory.BZMir.levi k (i + t) b' = GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) y * GlobalTheory.BZMir.levi k (i + t) a
    exact ⟨0, zero_mem _, b', hb', by rw [GlobalTheory.CompanionTheory.BZPsiPG.uM_zero, one_mul]⟩
  have key : ∀ p : GlobalTheory.BZMir.Mir k (i + t), ∀ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK,
      b.1.1.1 (p * β) = b.1.1.1 p := by
    intro p β hβ
    by_cases hp : ∃ h : GlobalTheory.BZMir.Leib.HPG k i t,
        ∃ β₀ ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : GlobalTheory.BZMir.Mir k (i + t)) * β₀
    · obtain ⟨h, β₀, hβ₀, rfl⟩ := hp
      rw [mul_assoc, hval h (β₀ * β) (Subgroup.mul_mem _ hβ₀ hβ), hval h β₀ hβ₀]
    · have hp' : ¬ ∃ h : GlobalTheory.BZMir.Leib.HPG k i t,
          ∃ β₀ ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK,
            p * β = (h : GlobalTheory.BZMir.Mir k (i + t)) * β₀ := by
        rintro ⟨h, β₀, hβ₀, he⟩
        refine hp ⟨h, β₀ * β⁻¹, Subgroup.mul_mem _ hβ₀ (Subgroup.inv_mem _ hβ), ?_⟩
        rw [← mul_assoc, ← he, mul_inv_cancel_right]
      rw [hzero _ hp', hzero _ hp]
  funext v
  unfold GlobalTheory.CompanionTheory.BZPsiPG.fibV
  rw [map_mul, ← mul_assoc]
  exact key _ _ hβ

end GlobalTheory.CompanionTheory.BZPsiPG.FibInvK

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralVanishingOpenSubgroupStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_integral_vanishing_open_subgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (z : V ⊗[ℂ] W) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ (h : HPG k i t) (β : Mir k (i + t)), β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK → b.1.1.1 ((h : Mir k (i + t)) * β) = hRep τ σ h z) → (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → ∀ b' ∈ K₁, ∀ g : GL (Fin (i + t)) k, fibV b (g * b') = fibV b g := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibInvK.fibV_mul_right_eq | exact GlobalTheory.CompanionTheory.BZPsiPG.FibInvK.fibV_mul_right_eq | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibInvK.fibV_mul_right_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralSupportSubgroup
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralSupportSubgroup
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ

theorem smInt_zero_fun {X Z : Type} [MeasurableSpace X] [AddCommGroup Z] [Module ℂ Z]
    (μ : MeasureTheory.Measure X) (φ : X → Z) (h : ∀ x, φ x = 0) : smInt μ φ = 0 := by
  unfold smInt
  apply finsum_eq_zero_of_forall_eq_zero
  intro v
  by_cases hv : v = 0
  · rw [hv, smul_zero]
  · have hempty : φ ⁻¹' {v} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hv (hx.symm.trans (h x))
    rw [hempty]
    simp

theorem mem_of_eq_mul (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k))
    (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (y : Fin (i + t) → k) (g : GL (Fin (i + t)) k)
    (h : HPG k i t) (β : Mir k (i + t)) (hβ : β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK)
    (e : uM k (i + t) y * levi k (i + t) g = (h : Mir k (i + t)) * β) :
    ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b' := by
  obtain ⟨y', _, b', hb', hβe⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.mem_Bgrp.1 hβ
  obtain ⟨x, q, hx⟩ := GlobalTheory.T.parabolic_unipotent_levi_decomp k i t h
  have e2 : uM k (i + t) y * levi k (i + t) g =
      uM k (i + t) (topV k i t x + ((q : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y') *
        levi k (i + t) ((q : GL (Fin (i + t)) k) * b') := by
    calc uM k (i + t) y * levi k (i + t) g = (h : Mir k (i + t)) * β := e
      _ = uM k (i + t) (topV k i t x) * levi k (i + t) (q : GL (Fin (i + t)) k) *
            (uM k (i + t) y' * levi k (i + t) b') := by rw [hx, hβe]
      _ = _ := GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.uM_levi_mul_uM_levi _ _ _ _ _
  exact ⟨q, b', hb', (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.uM_levi_inj _ e2).2⟩

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → ∀ g : GL (Fin (i + t)) k, (¬ ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b') → fibInt μ b g = 0 := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ _ μ c K₁ hK b hb g hg
  have hz : ∀ v, fibV b g v = 0 := by
    intro v
    by_contra hne
    have hex : ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK,
        uM k (i + t) (midV k i t v) * levi k (i + t) g = (h : Mir k (i + t)) * β := by
      by_contra hno
      exact hne (hb _ hno)
    obtain ⟨h, β, hβ, e⟩ := hex
    exact hg (mem_of_eq_mul k i t c K₁ hK _ g h β hβ e)
  show clT τ W (smInt μ (fibV b g)) = 0
  rw [smInt_zero_fun μ _ hz, map_zero]

end GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreIntegralSupportSubgroupStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_integral_support_subgroup : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin (i + t))) (b : cIndSpace (HPG k i t) (hRep τ σ)), (∀ p : Mir k (i + t), (¬ ∃ h : HPG k i t, ∃ β ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp (i + t) c K₁ hK, p = (h : Mir k (i + t)) * β) → b.1.1.1 p = 0) → ∀ g : GL (Fin (i + t)) k, (¬ ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b') → fibInt μ b g = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ.main | exact GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ.main | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibOffQ.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreSubgroupOpenCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreSubgroupOpenCompact
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

open GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

variable {k : Type} [Field k]

theorem colv_uM_mul_levi (n : ℕ) (y : Fin n → k) (b : GL (Fin n) k) :
    GlobalTheory.CompanionTheory.MirLevi.colv (uM k n y * levi k n b) = y := by
  have hu : ((GlobalTheory.CompanionTheory.BZPsiPG.uM k n y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + GlobalTheory.BZMir.colMat k n y := by
    first
    | rfl
    | (ext a c; simp [GlobalTheory.CompanionTheory.BZPsiPG.uM, GlobalTheory.BZMir.unip])
  have hL : ((GlobalTheory.BZMir.levi k n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      GlobalTheory.BZMir.glEmbMat k n (b : Matrix (Fin n) (Fin n) k) := rfl
  funext i
  simp only [GlobalTheory.CompanionTheory.MirLevi.colv, Subgroup.coe_mul, Units.val_mul, hu, hL]
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem eq_uM_colv_mul_levi (n : ℕ) (p : Mir k n) :
    p = uM k n (GlobalTheory.CompanionTheory.MirLevi.colv p) * levi k n (mirabolicProjection k n p) := by
  have hl (g : GL (Fin n) k) : mirabolicProjection k n (levi k n g) = g := by
    apply Units.ext
    ext i j
    change GlobalTheory.BZMir.blockMat k n (GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k)) i j = (g : Matrix (Fin n) (Fin n) k) i j
    simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.glEmbMat]
  have h1 : GlobalTheory.BZMir.mirabolicProjection k n
      (p * (GlobalTheory.BZMir.levi k n (GlobalTheory.BZMir.mirabolicProjection k n p))⁻¹) = 1 := by
    rw [map_mul, map_inv, hl, mul_inv_cancel]
  have hm : p * (levi k n (mirabolicProjection k n p))⁻¹ ∈ MirUin k n := by
    let q := p * (levi k n (mirabolicProjection k n p))⁻¹
    have hrow : ∀ j, ((q : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j =
        GlobalTheory.BZMir.eLast k n j :=
      fun j => congrFun ((GlobalTheory.BZMir.mem_Mir_iff k (q : GL (Fin (n + 1)) k)).1 q.2) j
    have hblock : ∀ i j : Fin n,
        ((q : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc j) =
          (1 : Matrix (Fin n) (Fin n) k) i j :=
      fun i j => congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) h1
    change q ∈ MirUin k n
    rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU, MonoidHom.mem_range]
    refine ⟨Multiplicative.ofAdd fun i =>
      ((q : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n), ?_⟩
    apply Units.ext
    ext i j
    change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + GlobalTheory.BZMir.colMat k n (fun i =>
      ((q : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n))) i j =
      ((q : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j
    rw [Matrix.add_apply, GlobalTheory.BZMir.colMat]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · simp [Matrix.one_apply, Fin.castSucc_ne_last, hblock]
    · simp [Matrix.one_apply, Fin.castSucc_ne_last]
    · simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm, hrow, GlobalTheory.BZMir.eLast]
    · simp [hrow, GlobalTheory.BZMir.eLast]
  obtain ⟨y, hy⟩ := GlobalTheory.CompanionTheory.BZPsiPG.exists_uM_of_mem k n hm
  have hp : p = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y *
      GlobalTheory.BZMir.levi k n (GlobalTheory.BZMir.mirabolicProjection k n p) := by
    rw [← hy, inv_mul_cancel_right]
  have hy' : GlobalTheory.CompanionTheory.MirLevi.colv p = y := by
    rw [hp]
    exact GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.colv_uM_mul_levi n y _
  rw [hy']
  exact hp

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_colv (n : ℕ) : Continuous (GlobalTheory.CompanionTheory.MirLevi.colv : Mir k n → Fin n → k) := by
  show Continuous fun p : GlobalTheory.BZMir.Mir k n => fun i : Fin n =>
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n)
  first
  | exact continuous_pi fun i =>
      (Units.continuous_val.comp continuous_subtype_val).matrix_elem (Fin.castSucc i) (Fin.last n)
  | exact continuous_pi fun i => (continuous_apply (Fin.last n)).comp
      ((continuous_apply (Fin.castSucc i)).comp (Units.continuous_val.comp continuous_subtype_val))
  | fun_prop

theorem coe_Bgrp_eq (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (h : K₁ ≤ KO k (Fin n)) :
    (Bgrp n c K₁ h : Set (Mir k n)) =
      GlobalTheory.CompanionTheory.MirLevi.colv ⁻¹' (latt n c : Set (Fin n → k)) ∩ mirabolicProjection k n ⁻¹' (K₁ : Set (GL (Fin n) k)) := by
  have hl (g : GL (Fin n) k) : mirabolicProjection k n (levi k n g) = g := by
    apply Units.ext
    ext i j
    change GlobalTheory.BZMir.blockMat k n (GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k)) i j = (g : Matrix (Fin n) (Fin n) k) i j
    simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.glEmbMat]
  have hu (y : Fin n → k) : mirabolicProjection k n (uM k n y) = 1 := by
    apply Units.ext
    ext i j
    change GlobalTheory.BZMir.blockMat k n (1 + GlobalTheory.BZMir.colMat k n y) i j = (1 : Matrix (Fin n) (Fin n) k) i j
    simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]
  ext p
  change (∃ y ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt n c, ∃ b ∈ K₁,
      p = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * GlobalTheory.BZMir.levi k n b) ↔
    (GlobalTheory.CompanionTheory.MirLevi.colv p ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt n c ∧ GlobalTheory.BZMir.mirabolicProjection k n p ∈ K₁)
  constructor
  · rintro ⟨y, hy, b, hb, rfl⟩
    refine ⟨?_, ?_⟩
    · rwa [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.colv_uM_mul_levi]
    · rwa [map_mul, hu, hl, one_mul]
  · rintro ⟨hy, hb⟩
    exact ⟨_, hy, _, hb, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.eq_uM_colv_mul_levi n p⟩

theorem coe_Bgrp_eq_image (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (h : K₁ ≤ KO k (Fin n)) :
    (Bgrp n c K₁ h : Set (Mir k n)) =
      (fun q : (Fin n → k) × GL (Fin n) k => uM k n q.1 * levi k n q.2) ''
        ((latt n c : Set (Fin n → k)) ×ˢ (K₁ : Set (GL (Fin n) k))) := by
  ext p
  change (∃ y ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt n c, ∃ b ∈ K₁,
      p = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * GlobalTheory.BZMir.levi k n b) ↔ _
  constructor
  · rintro ⟨y, hy, b, hb, rfl⟩
    exact ⟨(y, b), ⟨hy, hb⟩, rfl⟩
  · rintro ⟨⟨y, b⟩, ⟨hy, hb⟩, rfl⟩
    exact ⟨y, hy, b, hb, rfl⟩

theorem isOpen_isCompact_Bgrp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k))
    (h : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin n)), IsOpen (K₁ : Set (GL (Fin n) k)) →
    IsOpen (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp n c K₁ h : Set (Mir k n)) ∧
      IsCompact (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp n c K₁ h : Set (Mir k n)) := by
  intro k _ _ _ _ n c K₁ h hK
  have hc : Continuous (levi k n) ∧ Continuous (uM k n) ∧ Continuous (mirabolicProjection k n) := by
    refine ⟨GlobalTheory.CompanionTheory.BZMirFun.continuous_levi k n, GlobalTheory.CompanionTheory.BZPsiPG.Cont.continuous_uM k n, ?_⟩
    have hval : Continuous fun g : Mir k n =>
        ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
      Units.continuous_val.comp continuous_subtype_val
    have hblock : Continuous fun g : Mir k n =>
        ((mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      exact (continuous_apply (Fin.castSucc j)).comp ((continuous_apply (Fin.castSucc i)).comp hval)
    refine Units.continuous_iff.2 ⟨hblock, ?_⟩
    have heq : (fun g : Mir k n => (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
        fun g => ((mirabolicProjection k n g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
      funext g
      rw [map_inv]
    show Continuous (fun g : Mir k n => (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
    rw [heq]
    exact hblock.comp continuous_inv
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.coe_Bgrp_eq]
    exact ((GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_latt n c).preimage (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.continuous_colv n)).inter
      (hK.preimage hc.2.2)
  · rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.coe_Bgrp_eq_image]
    have hK₁ : IsCompact (K₁ : Set (GL (Fin n) k)) :=
      (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin n)).of_isClosed_subset
        (K₁.isClosed_of_isOpen hK) (SetLike.coe_subset_coe.mpr h)
    exact ((GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isCompact_latt n c).prod hK₁).image
      ((hc.2.1.comp continuous_fst).mul (hc.1.comp continuous_snd))

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreSubgroupOpenCompactStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_subgroup_open_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (h : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin n)), IsOpen (K₁ : Set (GL (Fin n) k)) → IsOpen (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp n c K₁ h : Set (Mir k n)) ∧ IsCompact (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp n c K₁ h : Set (Mir k n)) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_isCompact_Bgrp | exact GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_isCompact_Bgrp | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_isCompact_Bgrp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNormalOpenSubgroupCompact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNormalOpenSubgroupCompact
open Matrix

namespace GlobalTheory.CompanionTheory.OpenCore

theorem exists_open_core {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K S : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (hSo : IsOpen (S : Set G)) :
    ∃ K₁ : Subgroup G, K₁ ≤ K ∧ IsOpen (K₁ : Set G) ∧ K₁ ≤ S ∧ K₁.relIndex K ≠ 0 ∧
      ∀ κ ∈ K, ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hHo : IsOpen ((S.subgroupOf K : Subgroup K) : Set K) := hSo.preimage continuous_subtype_val
  haveI : Finite (K ⧸ S.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hHo
  haveI : (S.subgroupOf K).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hN : IsOpen (((S.subgroupOf K).normalCore : Subgroup K) : Set K) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _
      ((S.subgroupOf K).normalCore_isClosed ((S.subgroupOf K).isClosed_of_isOpen hHo))
  refine ⟨(S.subgroupOf K).normalCore.map K.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.coe_map]
    exact hKo.isOpenMap_subtype_val _ hN
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (Subgroup.normalCore_le _ hx)
  · have e : ((S.subgroupOf K).normalCore.map K.subtype).relIndex K = (S.subgroupOf K).normalCore.index := by
      rw [Subgroup.relIndex, ← Subgroup.comap_subtype,
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective K)]
    rw [e]
    exact (inferInstance : (S.subgroupOf K).normalCore.FiniteIndex).1
  · rintro κ hκ _ ⟨x, hx, rfl⟩
    refine ⟨⟨κ, hκ⟩ * x * (⟨κ, hκ⟩ : K)⁻¹, (Subgroup.normalCore_normal _).conj_mem x hx ⟨κ, hκ⟩, ?_⟩
    simp

theorem exists_open_normal_subgroup_KO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (U : Set (GL (Fin n) k)) (hU : U ∈ nhds (1 : GL (Fin n) k)) :
    ∃ K₁ : Subgroup (GL (Fin n) k), K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin n) ∧ IsOpen (K₁ : Set (GL (Fin n) k)) ∧
      (K₁ : Set (GL (Fin n) k)) ⊆ U ∧ K₁.relIndex (GlobalTheory.SplitWeil.KO k (Fin n)) ≠ 0 ∧
      ∀ κ ∈ GlobalTheory.SplitWeil.KO k (Fin n), ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁ := by
  obtain ⟨S, hSo, hSU⟩ := GlobalTheory.SmGL.ProdIrr.exists_openSubgroup_GL U hU
  obtain ⟨K₁, h1, h2, h3, h4, h5⟩ := exists_open_core (GlobalTheory.SplitWeil.KO k (Fin n)) S
    GlobalTheory.SplitFlip.isOpen_KO GlobalTheory.SplitFlip.isCompact_KO hSo
  exact ⟨K₁, h1, h2, fun g hg => hSU g (h3 hg), h4, h5⟩

end GlobalTheory.CompanionTheory.OpenCore
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNormalOpenSubgroupCompactStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_open_subgroup_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (U : Set (GL (Fin n) k)), U ∈ nhds (1 : GL (Fin n) k) → ∃ K₁ : Subgroup (GL (Fin n) k), K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin n) ∧ IsOpen (K₁ : Set (GL (Fin n) k)) ∧ (K₁ : Set (GL (Fin n) k)) ⊆ U ∧ K₁.relIndex (GlobalTheory.SplitWeil.KO k (Fin n)) ≠ 0 ∧ ∀ κ ∈ GlobalTheory.SplitWeil.KO k (Fin n), ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁ := by
  first | exact @GlobalTheory.CompanionTheory.OpenCore.exists_open_normal_subgroup_KO | exact GlobalTheory.CompanionTheory.OpenCore.exists_open_normal_subgroup_KO | (intros; apply GlobalTheory.CompanionTheory.OpenCore.exists_open_normal_subgroup_KO <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedGeneratedByKFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedGeneratedByKFinite
namespace GlobalTheory.CompanionTheory.CosetSum

theorem mem_of_translated_bumps : ∀ {Γ J : Type} [Group Γ] [AddCommGroup J] [Module ℂ J] (Q K K₁ : Subgroup Γ) (π : Representation ℂ Q J) (M : Submodule ℂ (Γ → J)) (Gf : Γ → J), K₁ ≤ K → K₁.relIndex K ≠ 0 → (∀ κ ∈ K, ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁) → (∀ g : Γ, ∃ q : Q, ∃ κ ∈ K, g = (q : Γ) * κ) → (∀ φ ∈ M, ∀ x : Γ, (fun g => φ (g * x)) ∈ M) → (∀ φ ∈ M, ∀ (q : Q) (g : Γ), φ ((q : Γ) * g) = π q (φ g)) → (∀ (q : Q) (g : Γ), Gf ((q : Γ) * g) = π q (Gf g)) → (∀ (g : Γ), ∀ b ∈ K₁, Gf (g * b) = Gf g) → (∀ κ ∈ K, ∃ φ ∈ M, (∀ (q : Q), ∀ b ∈ K₁, φ ((q : Γ) * b) = π q (Gf κ)) ∧ ∀ g : Γ, (¬ ∃ q : Q, ∃ b ∈ K₁, g = (q : Γ) * b) → φ g = 0) → Gf ∈ M := by
  intro Γ J _ _ _ Q K K₁ π M Gf hle hidx hconj hdec htr hlawM hlaw hinv hb
  classical
  let H : Subgroup K := K₁.subgroupOf K
  haveI hHn : H.Normal := ⟨fun n hn g => by
    have hn' : (n : Γ) ∈ K₁ := Subgroup.mem_subgroupOf.1 hn
    refine Subgroup.mem_subgroupOf.2 ?_
    simpa using hconj g g.2 n hn'⟩
  haveI : H.FiniteIndex := ⟨hidx⟩
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let P : Γ → Prop := fun x => ∃ q : Q, ∃ b ∈ K₁, x = (q : Γ) * b
  have hPmul : ∀ x, ∀ b ∈ K₁, P x → P (x * b) := by
    rintro x b hb' ⟨q, c, hc, rfl⟩
    exact ⟨q, c * b, K₁.mul_mem hc hb', by simp [mul_assoc]⟩
  have hb2 : ∀ κ : K, ∃ φ ∈ M, (∀ (q : Q), ∀ b ∈ K₁, φ ((q : Γ) * b) = π q (Gf κ)) ∧
      ∀ g : Γ, (¬ P g) → φ g = 0 := fun κ => hb κ κ.2
  choose φ hφM hφ1 hφ0 using hb2
  have key : ∀ κ' κ : K, φ κ ((κ' : Γ) * (κ : Γ)⁻¹) =
      if P ((κ' : Γ) * (κ : Γ)⁻¹) then Gf κ' else 0 := by
    intro κ' κ
    split_ifs with h
    · obtain ⟨q, b, hbm, e⟩ := h
      rw [e, hφ1 κ q b hbm, ← hlaw]
      have hκ' : (κ' : Γ) = q * b * κ := by rw [← e]; group
      have e2 : (q : Γ) * κ = κ' * ((κ : Γ)⁻¹ * b⁻¹ * κ) := by rw [hκ']; group
      have hm : (κ : Γ)⁻¹ * b⁻¹ * κ ∈ K₁ := by
        simpa using hconj _ (K.inv_mem κ.2) _ (K₁.inv_mem hbm)
      rw [e2, hinv _ _ hm]
    · exact hφ0 κ _ h
  let r : K ⧸ H → K := Quotient.out
  have hr : ∀ δ : K ⧸ H, ((r δ : K) : K ⧸ H) = δ := fun δ => QuotientGroup.out_eq' δ
  have hPcl : ∀ x y : K, (x : K ⧸ H) = y → P x → P y := by
    intro x y hxy hx
    have hm : x⁻¹ * y ∈ H := QuotientGroup.eq.1 hxy
    have hm' : (x : Γ)⁻¹ * y ∈ K₁ := by simpa using Subgroup.mem_subgroupOf.1 hm
    have := hPmul _ _ hm' hx
    simpa using this
  let Pd : K ⧸ H → Prop := fun ε => P (r ε)
  have hPd : ∀ x : K, P x ↔ Pd (x : K ⧸ H) := fun x =>
    ⟨hPcl _ _ (hr _).symm, hPcl _ _ (hr _)⟩
  let Φ : Γ → J := ∑ δ : K ⧸ H, (fun g => φ (r δ) (g * ((r δ : K) : Γ)⁻¹))
  have hΦM : Φ ∈ M := M.sum_mem fun δ _ => htr _ (hφM _) _
  let n : ℕ := (Finset.univ.filter Pd).card
  have hΦ : ∀ κ' : K, Φ κ' = n • Gf κ' := by
    intro κ'
    have h1 : Φ κ' = ∑ δ : K ⧸ H, if Pd ((κ' : K ⧸ H) * δ⁻¹) then Gf κ' else 0 := by
      simp only [Φ, Finset.sum_apply]
      refine Finset.sum_congr rfl fun δ _ => ?_
      rw [key]
      have hcl : (((κ' * (r δ)⁻¹ : K)) : K ⧸ H) = (κ' : K ⧸ H) * δ⁻¹ := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hr]
      have := hPd (κ' * (r δ)⁻¹)
      rw [hcl] at this
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      simp only [this]
    rw [h1]
    have h2 := Equiv.sum_comp ((Equiv.inv (K ⧸ H)).trans (Equiv.mulLeft (κ' : K ⧸ H)))
      (fun ε => if Pd ε then Gf κ' else 0)
    simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulLeft] at h2
    rw [h2, ← Finset.sum_filter, Finset.sum_const]
  have hn : n ≠ 0 := by
    have h1 : Pd 1 := by
      have : (r 1 : Γ) ∈ K₁ := by
        have : r 1 ∈ H := (QuotientGroup.eq_one_iff _).1 (hr 1)
        exact Subgroup.mem_subgroupOf.1 this
      exact ⟨1, _, this, by simp⟩
    exact (Finset.card_pos.2 ⟨1, by simpa using h1⟩).ne'
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hΨM : (n : ℂ)⁻¹ • Φ ∈ M := M.smul_mem _ hΦM
  have hEq : (n : ℂ)⁻¹ • Φ = Gf := by
    funext g
    obtain ⟨q, κ, hκ, rfl⟩ := hdec g
    have hK : ((n : ℂ)⁻¹ • Φ) κ = Gf κ := by
      have := hΦ ⟨κ, hκ⟩
      simp only at this
      rw [Pi.smul_apply, this, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hnC, one_smul]
    rw [hlawM _ hΨM, hK, hlaw]
  exact hEq ▸ hΨM

end GlobalTheory.CompanionTheory.CosetSum
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedGeneratedByKFiniteStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_generated_by_K_finite : ∀ {Γ J : Type} [Group Γ] [AddCommGroup J] [Module ℂ J] (Q K K₁ : Subgroup Γ) (π : Representation ℂ Q J) (M : Submodule ℂ (Γ → J)) (Gf : Γ → J), K₁ ≤ K → K₁.relIndex K ≠ 0 → (∀ κ ∈ K, ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁) → (∀ g : Γ, ∃ q : Q, ∃ κ ∈ K, g = (q : Γ) * κ) → (∀ φ ∈ M, ∀ x : Γ, (fun g => φ (g * x)) ∈ M) → (∀ φ ∈ M, ∀ (q : Q) (g : Γ), φ ((q : Γ) * g) = π q (φ g)) → (∀ (q : Q) (g : Γ), Gf ((q : Γ) * g) = π q (Gf g)) → (∀ (g : Γ), ∀ b ∈ K₁, Gf (g * b) = Gf g) → (∀ κ ∈ K, ∃ φ ∈ M, (∀ (q : Q), ∀ b ∈ K₁, φ ((q : Γ) * b) = π q (Gf κ)) ∧ ∀ g : Γ, (¬ ∃ q : Q, ∃ b ∈ K₁, g = (q : Γ) * b) → φ g = 0) → Gf ∈ M := by
  first | exact @GlobalTheory.CompanionTheory.CosetSum.mem_of_translated_bumps | exact GlobalTheory.CompanionTheory.CosetSum.mem_of_translated_bumps | (intros; apply GlobalTheory.CompanionTheory.CosetSum.mem_of_translated_bumps <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteImageCompactRightInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteImageCompactRightInvariant
namespace GlobalTheory.CompanionTheory.TopGroup

theorem finite_image_of_right_invariant_near_one :
    ∀ {Γ X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (K : Set Γ),
      IsCompact K → ∀ Gf : Γ → X, {s : Γ | ∀ x, Gf (x * s) = Gf x} ∈ nhds (1 : Γ) →
        (Gf '' K).Finite := by
  intro Γ X _ _ _ K hK Gf hS
  have hU : ∀ k ∈ K, {y : Γ | k⁻¹ * y ∈ {s : Γ | ∀ x, Gf (x * s) = Gf x}} ∈ nhds k := by
    intro k _
    have hc : Continuous fun y : Γ => k⁻¹ * y := continuous_const.mul continuous_id
    refine hc.continuousAt.preimage_mem_nhds ?_
    show _ ∈ nhds (k⁻¹ * k)
    rw [inv_mul_cancel]
    exact hS
  obtain ⟨t, -, hcover⟩ := hK.elim_nhds_subcover _ hU
  refine (t.finite_toSet.image Gf).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 (hcover hy)
  refine ⟨k, hk, ?_⟩
  have h := hyk k
  rw [mul_inv_cancel_left] at h
  exact h.symm

end GlobalTheory.CompanionTheory.TopGroup
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteImageCompactRightInvariantStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_image_compact_right_invariant : ∀ {Γ X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (K : Set Γ), IsCompact K → ∀ Gf : Γ → X, {s : Γ | ∀ x, Gf (x * s) = Gf x} ∈ nhds (1 : Γ) → (Gf '' K).Finite := by
  first | exact @GlobalTheory.CompanionTheory.TopGroup.finite_image_of_right_invariant_near_one | exact GlobalTheory.CompanionTheory.TopGroup.finite_image_of_right_invariant_near_one | (intros; apply GlobalTheory.CompanionTheory.TopGroup.finite_image_of_right_invariant_near_one <;> assumption)
end
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

open Topology GlobalTheory.SplitWeil

theorem fibInt_translate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) (f : cIndSpace (HPG k i t) (hRep τ σ)) (x g : GL (Fin (i + t)) k), fibInt μ (prodPG τ σ (levi k (i + t) x) f) g = fibInt μ f (g * x) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ _ μ f x g
  have h : fibV (prodPG τ σ (levi k (i + t) x) f) g = fibV f (g * x) := funext fun v =>
    congrArg f.1.1.1 (show uM k (i + t) (midV k i t v) * levi k (i + t) g * levi k (i + t) x =
      uM k (i + t) (midV k i t v) * levi k (i + t) (g * x) by rw [map_mul, mul_assoc])
  exact congrArg (fun φ => clT τ W (smInt μ φ)) h

theorem fibInt_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (g : GL (Fin (i + t)) k), (∀ f₁ f₂ : cIndSpace (HPG k i t) (hRep τ σ), fibInt μ (f₁ + f₂) g = fibInt μ f₁ g + fibInt μ f₂ g) ∧ ∀ (a : ℂ) (f : cIndSpace (HPG k i t) (hRep τ σ)), fibInt μ (a • f) g = a • fibInt μ f g := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ g
  have hr := fun f => GlobalTheory.T.fibre_function_locally_constant_compact k i t τ σ hτ hσ f g
  have hp := SmIntEl.smInt_properties (W := V ⊗[ℂ] W) (W' := V ⊗[ℂ] W) μ
  refine ⟨fun f₁ f₂ => ?_, fun a f => ?_⟩
  · have h : smInt μ (fibV (f₁ + f₂) g) = smInt μ (fibV f₁ g) + smInt μ (fibV f₂ g) :=
      hp.1 (fibV f₁ g) (fibV f₂ g) (hr f₁).1 (hr f₁).2 (hr f₂).1 (hr f₂).2
    exact (congrArg (clT τ W) h).trans (map_add _ _ _)
  · have e : fibV (a • f) g = (a • (LinearMap.id : (V ⊗[ℂ] W) →ₗ[ℂ] (V ⊗[ℂ] W))) ∘ fibV f g :=
      funext fun v => map_smul (evL (τ := τ) (σ := σ) (uM k (i + t) (midV k i t v) * levi k (i + t) g)) a f
    have h1 := hp.2.1 (a • (LinearMap.id : (V ⊗[ℂ] W) →ₗ[ℂ] (V ⊗[ℂ] W))) (fibV f g) (hr f).1 (hr f).2
    have h : smInt μ (fibV (a • f) g) = a • smInt μ (fibV f g) := (congrArg (smInt μ) e).trans h1
    exact (congrArg (clT τ W) h).trans (map_smul _ _ _)

theorem exists_nhds_prod {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (F : X → Y → Z) (hF : Continuous fun p : X × Y => F p.1 p.2) (x : X) (y : Y) {U : Set Z} (hU : U ∈ 𝓝 (F x y)) :
    ∃ A ∈ 𝓝 x, ∃ B ∈ 𝓝 y, ∀ a ∈ A, ∀ b ∈ B, F a b ∈ U := by
  have h : (fun p : X × Y => F p.1 p.2) ⁻¹' U ∈ 𝓝 (x, y) := hF.continuousAt.preimage_mem_nhds hU
  rw [nhds_prod_eq, Filter.mem_prod_iff] at h
  obtain ⟨A, hA, B, hB, hsub⟩ := h
  exact ⟨A, hA, B, hB, fun a ha b hb => hsub (Set.mk_mem_prod ha hb)⟩

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_latt_nhds {n : ℕ} {U : Set (Mir k n)} (hU : U ∈ 𝓝 (1 : Mir k n)) :
    ∃ c : kˣ, ∃ A ∈ 𝓝 (1 : GL (Fin n) k), ∀ y ∈ latt n c, ∀ b ∈ A, uM k n y * levi k n b ∈ U := by
  have hc := GlobalTheory.T.continuous_levi_unipotent_proj k n
  have hcont : Continuous fun p : (Fin n → k) × GL (Fin n) k => uM k n p.1 * levi k n p.2 :=
    (hc.2.1.comp continuous_fst).mul (hc.1.comp continuous_snd)
  have h00 : uM k n 0 * levi k n 1 = 1 := by rw [uM_zero, map_one, one_mul]
  obtain ⟨A, hA, B, hB, h⟩ := exists_nhds_prod (fun y b => uM k n y * levi k n b) hcont 0 1
    (by rw [h00]; exact hU)
  obtain ⟨c, hcA⟩ := exists_latt_subset hA
  exact ⟨c, B, hB, fun y hy b hb => h y (hcA hy) b hb⟩

theorem exists_level {n : ℕ} {Z : Type} (Zs : Set Z) (hZ : Zs.Finite) (U : Z → Set (Mir k n))
    (hU : ∀ z, U z ∈ 𝓝 (1 : Mir k n)) {A' : Set (GL (Fin n) k)} (hA' : A' ∈ 𝓝 (1 : GL (Fin n) k)) :
    ∃ (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (hK : K₁ ≤ KO k (Fin n)), IsOpen (K₁ : Set (GL (Fin n) k)) ∧
      (K₁ : Set (GL (Fin n) k)) ⊆ A' ∧ K₁.relIndex (KO k (Fin n)) ≠ 0 ∧
      (∀ κ ∈ KO k (Fin n), ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁) ∧ ∀ z ∈ Zs, ∀ p ∈ Bgrp n c K₁ hK, p ∈ U z := by
  have hI : (⋂ z ∈ Zs, U z) ∈ 𝓝 (1 : Mir k n) := (Filter.biInter_mem hZ).2 fun z _ => hU z
  obtain ⟨c, A, hA, hcA⟩ := exists_latt_nhds hI
  obtain ⟨K₁, hK, hopen, hsub, hidx, hnorm⟩ := GlobalTheory.T.exists_normal_open_subgroup_compact k n _ (Filter.inter_mem hA hA')
  refine ⟨c, K₁, hK, hopen, fun x hx => (hsub hx).2, hidx, hnorm, ?_⟩
  rintro z hz _ ⟨y, hy, b, hb, rfl⟩
  exact Set.mem_iInter₂.1 (hcA y hy b (hsub hb).1) z hz

variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def fibLin (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    [μ.IsAddHaarMeasure] :
    cIndSpace (HPG k i t) (hRep τ σ) →ₗ[ℂ] (GL (Fin (i + t)) k → Jacquet τ (MirUin k i) ⊗[ℂ] W) where
  toFun f := fun g => fibInt μ f g
  map_add' f₁ f₂ := funext fun g => (fibInt_linear k i t τ σ hτ hσ μ g).1 f₁ f₂
  map_smul' a f := funext fun g => (fibInt_linear k i t τ σ hτ hσ μ g).2 a f

theorem clT_surjective (τ : Representation ℂ (Mir k i) V) (W : Type) [AddCommGroup W] [Module ℂ W] :
    Function.Surjective (clT τ W) :=
  LinearMap.rTensor_surjective W (Submodule.mkQ_surjective _)

theorem exists_bump_fib (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    [μ.IsAddHaarMeasure] (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ KO k (Fin (i + t)))
    (hopen : IsOpen (K₁ : Set (GL (Fin (i + t)) k))) (z : V ⊗[ℂ] W)
    (hz : ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ Bgrp (i + t) c K₁ hK → hRep τ σ h z = z) :
    ∃ b : cIndSpace (HPG k i t) (hRep τ σ),
      (∀ (q : Qp k i t), ∀ b' ∈ K₁, fibInt μ b ((q : GL (Fin (i + t)) k) * b') =
        (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ) • qRep τ σ q (clT τ W z)) ∧
      ∀ g : GL (Fin (i + t)) k, (¬ ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b') → fibInt μ b g = 0 := by
  have hBo := GlobalTheory.T.fibre_subgroup_open_compact k (i + t) c K₁ hK hopen
  obtain ⟨b, hb1, hb2⟩ := GlobalTheory.T.exists_induced_section_supported_open (HPG k i t) (hRep τ σ) (Bgrp (i + t) c K₁ hK) hBo.1 hBo.2 z hz
  have hone : fibInt μ b 1 = (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ) • clT τ W z := by
    have h1 := GlobalTheory.T.fibre_integral_vanishing_subgroup k i t τ σ c K₁ hK z b hb1 hb2
    have h2 := (SmIntEl.smInt_properties (W := V ⊗[ℂ] W) (W' := V ⊗[ℂ] W) μ).2.2.2 _ z (isCompact_latt t c)
      (isOpen_latt t c) (isClosed_latt t c)
    exact (congrArg (fun φ => clT τ W (smInt μ φ)) h1).trans ((congrArg (clT τ W) h2).trans (map_smul _ _ _))
  refine ⟨b, fun q b' hb' => ?_, GlobalTheory.T.fibre_integral_support_subgroup k i t τ σ μ c K₁ hK b hb2⟩
  have e1 : fibInt μ b b' = fibInt μ b 1 := by
    have h := GlobalTheory.T.fibre_integral_vanishing_open_subgroup k i t τ σ c K₁ hK z b hb1 hb2 b' hb' 1
    have h' : fibV b b' = fibV b 1 := (congrArg (fibV b) (one_mul b').symm).trans h
    exact congrArg (fun φ => clT τ W (smInt μ φ)) h'
  exact (GlobalTheory.T.fibre_integral_intertwines_unipotent k i t τ σ hτ hσ μ b q b').trans
    ((congrArg (qRep τ σ q) (e1.trans hone)).trans (map_smul _ _ _))

end

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

open Topology GlobalTheory.SplitWeil

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem smooth_right_inv {Γ J : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup J] [Module ℂ J]
    (H : Subgroup Γ) (π : Representation ℂ H J) (G : smoothPart (ind H π)) :
    {s : Γ | ∀ x, G.1.1 (x * s) = G.1.1 x} ∈ 𝓝 (1 : Γ) := by
  have h1 : {s : Γ | ind H π s G.1 = G.1} ∈ 𝓝 (1 : Γ) := IsOpen.mem_nhds G.2 (by simp)
  exact Filter.mem_of_superset h1 fun s hs x => congrFun (congrArg Subtype.val hs) x

theorem exists_fib_mem (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    [μ.IsAddHaarMeasure] (c : kˣ) (K₁ : Subgroup (GL (Fin (i + t)) k)) (hK : K₁ ≤ KO k (Fin (i + t)))
    (hopen : IsOpen (K₁ : Set (GL (Fin (i + t)) k))) (z : V ⊗[ℂ] W) (a : Jacquet τ (MirUin k i) ⊗[ℂ] W)
    (ha : clT τ W z = a)
    (hz : ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ Bgrp (i + t) c K₁ hK → hRep τ σ h z = z) :
    ∃ φ ∈ LinearMap.range (fibLin τ σ hτ hσ μ),
      (∀ (q : Qp k i t), ∀ b' ∈ K₁, φ ((q : GL (Fin (i + t)) k) * b') = qRep τ σ q a) ∧
      ∀ g : GL (Fin (i + t)) k, (¬ ∃ q : Qp k i t, ∃ b' ∈ K₁, g = (q : GL (Fin (i + t)) k) * b') → φ g = 0 := by
  subst ha
  have hcc0 : (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ) ≠ 0 := by
    have h1 : 0 < μ (latt t c : Set (Fin t → k)) := (isOpen_latt t c).measure_pos μ ⟨0, zero_mem _⟩
    have h2 : μ (latt t c : Set (Fin t → k)) ≠ ⊤ := (isCompact_latt t c).measure_lt_top.ne
    exact_mod_cast (ENNReal.toReal_pos h1.ne' h2).ne'
  refine Exists.elim (exists_bump_fib τ σ hτ hσ μ c K₁ hK hopen z hz) fun b hb => ?_
  refine ⟨(((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ)⁻¹ • (fibLin τ σ hτ hσ μ b),
    Submodule.smul_mem _ _ ⟨b, rfl⟩, fun q b' hb' => ?_, fun g hg => ?_⟩
  · exact (congrArg (fun a => (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ)⁻¹ • a) (hb.1 q b' hb')).trans
      (inv_smul_smul₀ hcc0 _)
  · exact (congrArg (fun a => (((μ (latt t c : Set (Fin t → k))).toReal : ℝ) : ℂ)⁻¹ • a) (hb.2 g hg)).trans (smul_zero _)

theorem mem_range_fibLin (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (hτ : IsSmooth τ) (hσ : IsSmooth σ)
    [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    [μ.IsAddHaarMeasure] (Gf : GL (Fin (i + t)) k → Jacquet τ (MirUin k i) ⊗[ℂ] W)
    (hlaw : ∀ (q : Qp k i t) (g : GL (Fin (i + t)) k), Gf ((q : GL (Fin (i + t)) k) * g) = qRep τ σ q (Gf g))
    (hinv : {s : GL (Fin (i + t)) k | ∀ x, Gf (x * s) = Gf x} ∈ 𝓝 (1 : GL (Fin (i + t)) k)) :
    Gf ∈ LinearMap.range (fibLin τ σ hτ hσ μ) := by
  have hfin : (Gf '' (KO k (Fin (i + t)) : Set (GL (Fin (i + t)) k))).Finite :=
    GlobalTheory.T.finite_image_compact_right_invariant _ GlobalTheory.SplitFlip.isCompact_KO Gf hinv
  obtain ⟨pre, hpre⟩ : ∃ pre : Jacquet τ (MirUin k i) ⊗[ℂ] W → V ⊗[ℂ] W, ∀ a, clT τ W (pre a) = a :=
    ⟨Function.surjInv (clT_surjective τ W), Function.surjInv_eq _⟩
  choose Ust hUst hUfix using GlobalTheory.T.smooth_tensor_fixed_parabolic_near_one k i t τ σ hτ hσ
  obtain ⟨c, K₁, hK, hopen, hsub, hidx, hnorm, hlev⟩ := exists_level _ (hfin.image pre) Ust hUst hinv
  have hfix : ∀ κ ∈ KO k (Fin (i + t)), ∀ h : HPG k i t,
      (h : Mir k (i + t)) ∈ Bgrp (i + t) c K₁ hK → hRep τ σ h (pre (Gf κ)) = pre (Gf κ) :=
    fun κ hκ h hh => hUfix _ h (hlev _ ⟨_, ⟨κ, hκ, rfl⟩, rfl⟩ _ hh)
  refine GlobalTheory.T.induced_generated_by_K_finite (Qp k i t) (KO k (Fin (i + t))) K₁ (qRep τ σ) (LinearMap.range (fibLin τ σ hτ hσ μ)) Gf hK hidx hnorm
    (fun g => ?_) ?_ ?_ hlaw (fun g b hb => hsub hb g) ?_
  · obtain ⟨q, κ, hκ, e⟩ := GlobalTheory.T.iwasawa_decomp_parabolic_maximal_compact k i t g
    exact ⟨q, κ, hκ, e⟩
  · rintro _ ⟨f, rfl⟩ x
    exact ⟨prodPG τ σ (levi k (i + t) x) f, funext fun g => fibInt_translate k i t τ σ μ f x g⟩
  · rintro _ ⟨f, rfl⟩ q g
    exact GlobalTheory.T.fibre_integral_intertwines_unipotent k i t τ σ hτ hσ μ f q g
  · intro κ hκ
    exact exists_fib_mem τ σ hτ hσ μ c K₁ hK hopen (pre (Gf κ)) (Gf κ) (hpre _) (hfix κ hκ)

end

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

namespace GlobalTheory.CompanionTheory.BZPsiPG

open Topology GlobalTheory.SplitWeil FibOnto

theorem exists_fibInt_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure], ∀ G : smoothPart (ind (Qp k i t) (qRep τ σ)), ∃ f : cIndSpace (HPG k i t) (hRep τ σ), ∀ g, fibInt μ f g = G.1.1 g := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ _ _ μ _ G
  have hM := mem_range_fibLin τ σ hτ hσ μ G.1.1 G.1.2 (smooth_right_inv _ _ G)
  exact ⟨Classical.choose hM, fun g => congrFun (Classical.choose_spec hM) g⟩

end GlobalTheory.CompanionTheory.BZPsiPG

end
