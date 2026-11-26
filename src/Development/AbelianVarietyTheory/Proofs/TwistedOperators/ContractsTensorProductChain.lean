module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearMapTensorOfPairing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFourierJacobiSubgroupIffParabolicMulColumn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalForallMapMemStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContractsTensorProductChain
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContractsTensorProductChain
noncomputable section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

theorem exists_piTensor_succ_equiv (m : ℕ) (F : Fin (m + 1) → Type) [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)] :
    ∃ e : ((⨂[ℂ] j : Fin m, F j.succ) ⊗[ℂ] F 0) ≃ₗ[ℂ] (⨂[ℂ] j, F j),
      ∀ (f : ∀ j, F j), e (PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ f 0) = PiTensorProduct.tprod ℂ f := by
  let σ : Fin m ⊕ Unit ≃ Fin (m + 1) :=
    { toFun := Sum.elim Fin.succ (fun _ => 0)
      invFun := fun k => Fin.cases (motive := fun _ => Fin m ⊕ Unit) (Sum.inr ()) Sum.inl k
      left_inv := by rintro (j | ⟨⟩) <;> simp
      right_inv := by intro k; cases k using Fin.cases <;> simp }
  refine ⟨(TensorProduct.congr (LinearEquiv.refl ℂ _)
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Unit => F 0) ()).symm).trans
      ((PiTensorProduct.tmulEquivDep ℂ (fun i : Fin m ⊕ Unit => F (σ i))).trans
        (PiTensorProduct.reindex ℂ F σ.symm).symm), fun f => ?_⟩
  have h1 : TensorProduct.congr (LinearEquiv.refl ℂ (⨂[ℂ] j : Fin m, F j.succ))
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Unit => F 0) ()).symm
      (PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ f 0) =
      PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ PiTensorProduct.tprod ℂ (fun _ : Unit => f 0) := by
    rw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, PiTensorProduct.subsingletonEquiv_symm_apply']
  have h2 : PiTensorProduct.tmulEquivDep ℂ (fun i : Fin m ⊕ Unit => F (σ i))
      (PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ PiTensorProduct.tprod ℂ (fun _ : Unit => f 0)) =
      PiTensorProduct.tprod ℂ (fun i => f (σ i)) := by
    rw [← LinearEquiv.eq_symm_apply, PiTensorProduct.tmulEquivDep_symm_apply]
    all_goals rfl
  have h3 : (PiTensorProduct.reindex ℂ F σ.symm).symm (PiTensorProduct.tprod ℂ (fun i => f (σ i))) =
      PiTensorProduct.tprod ℂ f := by
    rw [LinearEquiv.symm_apply_eq, PiTensorProduct.reindex_tprod]
    all_goals rfl
  show (PiTensorProduct.reindex ℂ F σ.symm).symm (PiTensorProduct.tmulEquivDep ℂ (fun i : Fin m ⊕ Unit => F (σ i))
    (TensorProduct.congr (LinearEquiv.refl ℂ (⨂[ℂ] j : Fin m, F j.succ))
      (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Unit => F 0) ()).symm
      (PiTensorProduct.tprod ℂ (fun j : Fin m => f j.succ) ⊗ₜ f 0))) = PiTensorProduct.tprod ℂ f
  rw [h1]
  exact (congrArg (PiTensorProduct.reindex ℂ F σ.symm).symm h2).trans h3

theorem exists_piTensor_succ_equiv_map (m : ℕ) (F : Fin (m + 1) → Type) [∀ j, AddCommGroup (F j)]
    [∀ j, Module ℂ (F j)] :
    ∃ e : ((⨂[ℂ] j : Fin m, F j.succ) ⊗[ℂ] F 0) ≃ₗ[ℂ] (⨂[ℂ] j, F j),
      ∀ (A : ∀ j, F j →ₗ[ℂ] F j) (t : ⨂[ℂ] j : Fin m, F j.succ) (a : F 0),
        PiTensorProduct.map A (e (t ⊗ₜ a)) = e (PiTensorProduct.map (fun j : Fin m => A j.succ) t ⊗ₜ A 0 a) := by
  obtain ⟨e, he⟩ := exists_piTensor_succ_equiv m F
  refine ⟨e, fun A t a => ?_⟩
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    have h1 := he (Fin.cons a f : ∀ j, F j)
    have h2 := he (fun j => A j ((Fin.cons a f : ∀ j, F j) j))
    simp only [Fin.cons_succ, Fin.cons_zero] at h1 h2
    simp only [← TensorProduct.smul_tmul', map_smul, PiTensorProduct.map_tprod, h1, h2]
  | add x y hx hy =>
    simp only [TensorProduct.add_tmul, map_add (f := _), hx, hy]

private theorem factor_dual_lemma {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (p : X →ₗ[ℂ] Y) (hp : Function.Surjective p) (l : Module.Dual ℂ X) (hl : ∀ x, p x = 0 → l x = 0) :
    ∃ l' : Module.Dual ℂ Y, ∀ x, l x = l' (p x) := by
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)
  refine ⟨l ∘ₗ s, fun x => ?_⟩
  have hps : p (s (p x)) = p x := by rw [← LinearMap.comp_apply p s, hs, LinearMap.id_apply]
  have h0 : p (x - s (p x)) = 0 := by rw [map_sub, hps, sub_self]
  have h1 := hl _ h0
  rw [map_sub, sub_eq_zero] at h1
  rw [LinearMap.comp_apply]
  exact h1

private theorem lTensor_ker_lemma_2 {Q N P : Type} [AddCommGroup Q] [Module ℂ Q] [AddCommGroup N] [Module ℂ N]
    [AddCommGroup P] [Module ℂ P] (g : N →ₗ[ℂ] P) (hg : Function.Surjective g)
    (l : Module.Dual ℂ (Q ⊗[ℂ] N)) (hl : ∀ q n, g n = 0 → l (q ⊗ₜ n) = 0) :
    ∀ z, LinearMap.lTensor Q g z = 0 → l z = 0 := by
  intro z hz
  obtain ⟨y, rfl⟩ := ((lTensor_exact Q (LinearMap.exact_subtype_ker_map g) hg) z).mp hz
  clear hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul q k =>
    rw [LinearMap.lTensor_tmul]
    exact hl q k.1 (LinearMap.mem_ker.mp k.2)
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, add_zero]

theorem contracts_chain : ∀ (m : ℕ) (G : Fin (m + 1) → Type) [∀ j, Monoid (G j)] (F : Fin m → Type) [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)] (V : Fin (m + 1) → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (φ : ∀ j : Fin m, Representation ℂ (G j.castSucc × G j.succ) (F j)) (σ : ∀ j, Representation ℂ (G j) (V j)), (∀ j : Fin m, Contracts (φ j) (σ j.castSucc) (σ j.succ)) → ∃ π : ((⨂[ℂ] j, F j) ⊗[ℂ] V 0) →ₗ[ℂ] V (Fin.last m), Function.Surjective π ∧ (∀ (g : ∀ j, G j) (f : ⨂[ℂ] j, F j) (v : V 0), π (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ[ℂ] σ 0 (g 0) v) = σ (Fin.last m) (g (Fin.last m)) (π (f ⊗ₜ[ℂ] v))) ∧ ∀ l : Module.Dual ℂ ((⨂[ℂ] j, F j) ⊗[ℂ] V 0), (∀ g : ∀ j, G j, g (Fin.last m) = 1 → ∀ (f : ⨂[ℂ] j, F j) (v : V 0), l (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ[ℂ] σ 0 (g 0) v) = l (f ⊗ₜ[ℂ] v)) → ∀ x, π x = 0 → l x = 0 := by
  intro m
  induction m with
  | zero =>
    intro G _ F _ _ V _ _ φ σ _
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ((⨂[ℂ] j : Fin 0, F j) ⊗[ℂ] V 0) ≃ₗ[ℂ] V 0,
        ∀ (f : ⨂[ℂ] j : Fin 0, F j) (v : V 0), ψ (f ⊗ₜ v) = PiTensorProduct.isEmptyEquiv (Fin 0) f • v :=
      ⟨(TensorProduct.congr (PiTensorProduct.isEmptyEquiv (Fin 0)) (LinearEquiv.refl ℂ (V 0))).trans
        (TensorProduct.lid ℂ (V 0)), fun f v => by simp⟩
    have hmap : ∀ (A : ∀ j : Fin 0, F j →ₗ[ℂ] F j) (f : ⨂[ℂ] j : Fin 0, F j),
        PiTensorProduct.isEmptyEquiv (Fin 0) (PiTensorProduct.map A f) =
          PiTensorProduct.isEmptyEquiv (Fin 0) f := by
      intro A f
      induction f using PiTensorProduct.induction_on with
      | smul_tprod r x => simp [PiTensorProduct.map_tprod]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    refine ⟨ψ.toLinearMap, ψ.surjective, ?_, ?_⟩
    · intro g f v
      simp only [LinearEquiv.coe_coe]
      rw [hψ, hψ, hmap, map_smul]
      all_goals rfl
    · intro l _ x hx
      have hx' : ψ x = 0 := hx
      rw [ψ.map_eq_zero_iff] at hx'
      rw [hx', map_zero]
  | succ m ih =>
    intro G _ F _ _ V _ _ φ σ hc
    obtain ⟨e, he⟩ := exists_piTensor_succ_equiv_map m F
    have hc0 : Contracts (φ 0) (σ 0) (σ (Fin.succ 0)) := hc 0
    obtain ⟨π₀, hs₀, he₀, hk₀⟩ := hc0
    obtain ⟨π', hs', he', hk'⟩ := ih (fun j => G j.succ) (fun j => F j.succ) (fun j => V j.succ)
      (fun j => φ j.succ) (fun j => σ j.succ) (fun j => hc j.succ)
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ((⨂[ℂ] j, F j) ⊗[ℂ] V 0) ≃ₗ[ℂ]
        ((⨂[ℂ] j : Fin m, F j.succ) ⊗[ℂ] (F 0 ⊗[ℂ] V 0)),
        ∀ t a v, ψ (e (t ⊗ₜ a) ⊗ₜ v) = t ⊗ₜ (a ⊗ₜ v) :=
      ⟨(TensorProduct.congr e.symm (LinearEquiv.refl ℂ _)).trans (TensorProduct.assoc ℂ _ _ _),
        fun t a v => by simp⟩
    refine ⟨π' ∘ₗ LinearMap.lTensor _ π₀ ∘ₗ ψ.toLinearMap,
      hs'.comp ((LinearMap.lTensor_surjective _ hs₀).comp ψ.surjective), ?_, ?_⟩
    · intro g f v
      show π' (LinearMap.lTensor _ π₀ (ψ (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ
        σ 0 (g 0) v))) = σ (Fin.last (m + 1)) (g (Fin.last (m + 1))) (π' (LinearMap.lTensor _ π₀ (ψ (f ⊗ₜ v))))
      obtain ⟨y, rfl⟩ := e.surjective f
      induction y using TensorProduct.induction_on with
      | zero =>
        simp only [map_zero, TensorProduct.zero_tmul]
        all_goals exact (map_zero _).symm
      | tmul t a =>
        rw [he, hψ, hψ, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
        have h0 : π₀ (φ 0 (g (Fin.castSucc 0), g (Fin.succ 0)) a ⊗ₜ σ 0 (g 0) v) =
            σ (Fin.succ 0) (g (Fin.succ 0)) (π₀ (a ⊗ₜ v)) := he₀ _ _ a v
        rw [h0]
        exact he' (fun j => g j.succ) t (π₀ (a ⊗ₜ v))
      | add y₁ y₂ h₁ h₂ =>
        simp only [map_add (f := _), TensorProduct.add_tmul] at h₁ h₂ ⊢
        rw [h₁, h₂]
    · intro l hl x hx
      obtain ⟨L, hL⟩ : ∃ L : Module.Dual ℂ ((⨂[ℂ] j : Fin m, F j.succ) ⊗[ℂ] (F 0 ⊗[ℂ] V 0)),
          ∀ z, L z = l (ψ.symm z) := ⟨l ∘ₗ ψ.symm.toLinearMap, fun z => rfl⟩
      have hLe : ∀ t a v, L (t ⊗ₜ (a ⊗ₜ v)) = l (e (t ⊗ₜ a) ⊗ₜ v) := by
        intro t a v
        rw [hL, ← hψ t a v, LinearEquiv.symm_apply_apply]

      have hA : ∀ t u, π₀ u = 0 → L (t ⊗ₜ u) = 0 := by
        intro t u hu
        refine hk₀ (L.comp (TensorProduct.mk ℂ _ _ t)) ?_ u hu
        intro h a v
        simp only [LinearMap.comp_apply, TensorProduct.mk_apply, hLe]
        obtain ⟨gs, hg0, hg0', hg1, hg2, hg3, hgl⟩ : ∃ gs : ∀ j, G j, gs (Fin.castSucc 0) = h ∧ gs 0 = h ∧
            gs (Fin.succ 0) = 1 ∧ (∀ j : Fin m, gs j.succ.castSucc = 1) ∧ (∀ j : Fin m, gs j.succ.succ = 1) ∧
            gs (Fin.last (m + 1)) = 1 :=
          ⟨Pi.mulSingle (Fin.castSucc 0) h, Pi.mulSingle_eq_same _ _, Pi.mulSingle_eq_same _ _,
            Pi.mulSingle_eq_of_ne (by simp [Fin.ext_iff]) _, fun j => Pi.mulSingle_eq_of_ne (by simp [Fin.ext_iff]) _,
            fun j => Pi.mulSingle_eq_of_ne (by simp [Fin.ext_iff]) _, Pi.mulSingle_eq_of_ne (by simp [Fin.ext_iff]) _⟩
        have hinv := hl gs hgl (e (t ⊗ₜ a)) v
        rw [← hinv, he]
        simp only [hg0, hg0', hg1, hg2, hg3, ← Prod.one_eq_mk, map_one, PiTensorProduct.map_one,
          Module.End.one_apply]
        all_goals rfl
      have hB := lTensor_ker_lemma_2 π₀ hs₀ L (fun q n hn => hA q n hn)
      obtain ⟨L', hL'⟩ := factor_dual_lemma (LinearMap.lTensor _ π₀) (LinearMap.lTensor_surjective _ hs₀) L hB

      have hD : ∀ g' : ∀ j : Fin (m + 1), G j.succ, g' (Fin.last m) = 1 → ∀ t w,
          L' (PiTensorProduct.map (fun j : Fin m => φ j.succ ((g' j.castSucc : G j.succ.castSucc), g' j.succ)) t ⊗ₜ σ (Fin.succ 0) (g' 0) w) =
            L' (t ⊗ₜ w) := by
        intro g' hg' t w
        obtain ⟨u, rfl⟩ := hs₀ w
        induction u using TensorProduct.induction_on with
        | zero => simp only [map_zero, TensorProduct.tmul_zero]
        | tmul a v =>
          rw [← he₀ 1 (g' 0) a v]
          have k1 := hL' (PiTensorProduct.map (fun j : Fin m => φ j.succ ((g' j.castSucc : G j.succ.castSucc), g' j.succ)) t ⊗ₜ
            (φ 0 (1, g' 0) a ⊗ₜ σ 0 1 v))
          have k2 := hL' (t ⊗ₜ (a ⊗ₜ v))
          rw [LinearMap.lTensor_tmul, hLe] at k1 k2
          have hinv := hl (Fin.cons (1 : G 0) g' : ∀ j, G j)
            (by rw [← Fin.succ_last, Fin.cons_succ]; exact hg') (e (t ⊗ₜ a)) v
          rw [he] at hinv
          exact k1.symm.trans (hinv.trans k2)
        | add u₁ u₂ h₁ h₂ => simp only [map_add (f := _), TensorProduct.tmul_add, h₁, h₂]
      have hx' : π' (LinearMap.lTensor _ π₀ (ψ x)) = 0 := hx
      have h1 := hk' L' hD _ hx'
      rw [← hL', hL, LinearEquiv.symm_apply_apply] at h1
      exact h1

end GlobalTheory.OneFunctional
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContractsTensorProductChainStatement
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contracts_tensorProduct_chain : ∀ (m : ℕ) (G : Fin (m + 1) → Type) [∀ j, Monoid (G j)] (F : Fin m → Type) [∀ j, AddCommGroup (F j)] [∀ j, Module ℂ (F j)] (V : Fin (m + 1) → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (φ : ∀ j : Fin m, Representation ℂ (G j.castSucc × G j.succ) (F j)) (σ : ∀ j, Representation ℂ (G j) (V j)), (∀ j : Fin m, Contracts (φ j) (σ j.castSucc) (σ j.succ)) → ∃ π : ((⨂[ℂ] j, F j) ⊗[ℂ] V 0) →ₗ[ℂ] V (Fin.last m), Function.Surjective π ∧ (∀ (g : ∀ j, G j) (f : ⨂[ℂ] j, F j) (v : V 0), π (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ[ℂ] σ 0 (g 0) v) = σ (Fin.last m) (g (Fin.last m)) (π (f ⊗ₜ[ℂ] v))) ∧ ∀ l : Module.Dual ℂ ((⨂[ℂ] j, F j) ⊗[ℂ] V 0), (∀ g : ∀ j, G j, g (Fin.last m) = 1 → ∀ (f : ⨂[ℂ] j, F j) (v : V 0), l (PiTensorProduct.map (fun j => φ j (g j.castSucc, g j.succ)) f ⊗ₜ[ℂ] σ 0 (g 0) v) = l (f ⊗ₜ[ℂ] v)) → ∀ x, π x = 0 → l x = 0 := by
  first | exact @GlobalTheory.OneFunctional.contracts_chain | exact GlobalTheory.OneFunctional.contracts_chain | (intros; apply GlobalTheory.OneFunctional.contracts_chain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalKill
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta GlobalTheory.PairingTensor Matrix

namespace GlobalTheory.InvPairingTensor

variable {p q : ℕ}

theorem Jm_diag (p q : ℕ) :
    Jm p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  unfold Jm Formalism.UG.Jpq
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply, Matrix.diagonal_apply] <;>
    split_ifs <;> simp

theorem Jm_mul_self (p q : ℕ) : Jm p q * Jm p q = 1 := by
  rw [Jm_diag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  rcases a with a | a <;> simp

theorem exists_real_parts (Z : Mat p q) :
    ∃ X Y : Mat p q, X ∈ upq p q ∧ Y ∈ upq p q ∧ (IsKC Z → IsKC X ∧ IsKC Y) ∧
      Z = X + Complex.I • Y := by
  have hsym : ∀ a b : Ix p q, ¬ sameBlock a b → ¬ sameBlock b a := by
    intro a b h h'
    apply h
    rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]
  refine ⟨(1 / 2 : ℂ) • (Z - Jm p q * Zᴴ * Jm p q), (-Complex.I / 2) • (Z + Jm p q * Zᴴ * Jm p q),
    ?_, ?_, ?_, ?_⟩
  · show _ * _ + _ * _ = 0
    rw [Jm_diag]
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] <;> ring
  · show _ * _ + _ * _ = 0
    rw [Jm_diag]
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] <;> ring
  · intro hZ
    have hZ' : ∀ a b, ¬ sameBlock a b → (Jm p q * Zᴴ * Jm p q) a b = 0 := by
      intro a b hab
      rw [Jm_diag, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
        hZ b a (hsym a b hab)]
      simp
    constructor
    · intro a b hab
      simp [Matrix.sub_apply, hZ a b hab, hZ' a b hab]
    · intro a b hab
      simp [Matrix.add_apply, hZ a b hab, hZ' a b hab]
  · ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring

private theorem inner_pi_apply_pi_apply {T : GrpData p q} (U : URep T) (g : T.G) (x y : U.H) :
    inner ℂ (U.π g x) (U.π g y) = inner ℂ x y := by
  let L : U.H →ₗᵢ[ℂ] U.H := ⟨(U.π g).toLinearMap, U.isom g⟩
  exact L.inner_map_map x y

theorem inner_act_skew {T : GrpData p q} (D : DSRep T) {X : Mat p q} (hX : X ∈ upq p q)
    (v w : D.HK.V) :
    inner ℂ (D.ι v) (D.ι (D.HK.act X w)) + inner ℂ (D.ι (D.HK.act X v)) (D.ι w) = 0 := by
  have hv := D.der X hX v
  have hw := D.der X hX w
  have h := hv.inner ℂ hw
  have hc : (fun t : ℝ => inner ℂ ((D.U.π (T.expt (t • X))) (D.ι v))
      ((D.U.π (T.expt (t • X))) (D.ι w))) = fun _ => inner ℂ (D.ι v) (D.ι w) := by
    funext t
    exact inner_pi_apply_pi_apply D.U _ _ _
  rw [hc] at h
  have h0 := h.unique (hasDerivAt_const (0 : ℝ) (inner ℂ (D.ι v) (D.ι w)))
  simpa [T.expt_zero] using h0

section Frame
variable {A H : Type} [AddCommGroup A] [Module ℂ A] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_frame (i : A →ₗ[ℂ] H) (hi : Function.Injective i) (E : Submodule ℂ A)
    [FiniteDimensional ℂ E] :
    ∃ (n : ℕ) (a : Fin n → A), (∀ j, a j ∈ E) ∧
      ∀ x ∈ E, ∑ j, inner ℂ (i (a j)) (i x) • a j = x := by
  classical
  let F : Submodule ℂ H := E.map i
  let bF := stdOrthonormalBasis ℂ F
  have hb : ∀ j, ∃ a, a ∈ E ∧ i a = (bF j : H) := fun j =>
    Submodule.mem_map.mp (bF j).2
  choose a haE hia using hb
  refine ⟨Module.finrank ℂ F, a, haE, fun x hx => ?_⟩
  apply hi
  have hxF : i x ∈ F := Submodule.mem_map_of_mem hx
  have key := congrArg Subtype.val (bF.sum_repr' (⟨i x, hxF⟩ : F))
  simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at key
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, hia]
  exact key

end Frame

theorem exists_finiteDimensional_kill {r s : ℕ} {T₂ : GrpData r s} (R₂ : DSRep T₂)
    (hA : AdmGK R₂.HK) {N : Type} [AddCommGroup N] [Module ℂ N]
    (B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] N)
    (hB : ∀ Z ∈ upq r s, ∀ P y, B (fockAct2 p q r s Z P) y + B P (R₂.HK.act Z y) = 0)
    (P : Pol p q r s) :
    ∃ E : Submodule ℂ R₂.HK.V, FiniteDimensional ℂ E ∧
      ∀ y, (∀ x ∈ E, inner ℂ (R₂.ι y) (R₂.ι x) = 0) → B P y = 0 := by
  classical
  obtain ⟨⟨W, hWfd, hPW, hWK⟩, -⟩ := (GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).2 P
  have hwt : ∀ v ∈ W, v ∈ ⨆ μ : Ix r s → ℚ, wtSub (fockAct2 p q r s) μ :=
    fun v _ => ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).2 v).2
  have hlie : IsKLieAct (fockAct2 p q r s) := by
    unfold IsKLieAct
    intro Y Z _ _
    exact (GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.2.1 Y Z
  obtain ⟨E, hEfd, hE⟩ :=
    GlobalTheory.T.exists_finiteDimensional_forall_map_mem' r s R₂.HK hA (Pol p q r s) (fockAct2 p q r s) hlie W hWfd hWK hwt
  refine ⟨E, hEfd, fun y hy => ?_⟩
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  obtain ⟨Y, hYfd, hyY, hYK⟩ := R₂.HK.kfin y
  haveI := hYfd
  obtain ⟨n, b, hbY, hfr⟩ := exists_frame R₂.ι R₂.ι_inj Y
  let φ : Pol p q r s →ₗ[ℂ] R₂.HK.V :=
    { toFun := fun Q => ∑ j, l (B Q (b j)) • b j
      map_add' := fun Q Q' => by
        simp only [map_add (f := _), LinearMap.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c Q => by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
          mul_smul] }
  have hφ : ∀ Q, φ Q = ∑ j, l (B Q (b j)) • b j := fun Q => rfl
  have hφY : ∀ Q, φ Q ∈ Y := fun Q => by
    rw [hφ]
    exact Y.sum_mem fun j _ => Y.smul_mem _ (hbY j)
  have hrep : ∀ Q, ∀ z ∈ Y, inner ℂ (R₂.ι z) (R₂.ι (φ Q)) = l (B Q z) := by
    intro Q z hz
    conv_rhs => rw [← hfr z hz]
    rw [hφ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.map_smulₛₗ, inner_sum, inner_smul_right, smul_eq_mul,
      inner_conj_symm]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hsep : ∀ u ∈ Y, ∀ u' ∈ Y,
      (∀ z ∈ Y, inner ℂ (R₂.ι z) (R₂.ι u) = inner ℂ (R₂.ι z) (R₂.ι u')) → u = u' := by
    intro u hu u' hu' h
    have h0 := h (u - u') (Y.sub_mem hu hu')
    rw [← sub_eq_zero, ← inner_sub_right, ← map_sub, inner_self_eq_zero, ← map_zero R₂.ι] at h0
    exact sub_eq_zero.mp (R₂.ι_inj h0)
  have hequ1 : ∀ Z ∈ upq r s, IsKC Z → ∀ Q, φ (fockAct2 p q r s Z Q) = R₂.HK.act Z (φ Q) := by
    intro Z hZ hKZ Q
    refine hsep _ (hφY _) _ (hYK Z hKZ _ (hφY Q)) fun z hz => ?_
    rw [hrep _ z hz, eq_neg_of_add_eq_zero_left (hB Z hZ Q z), map_neg,
      ← hrep Q _ (hYK Z hKZ z hz)]
    exact (eq_neg_of_add_eq_zero_left (inner_act_skew R₂ hZ z (φ Q))).symm
  have hequ : ∀ Z, IsKC Z → ∀ Q, φ (fockAct2 p q r s Z Q) = R₂.HK.act Z (φ Q) := by
    intro Z hKZ Q
    obtain ⟨X1, Y1, hX1, hY1, hK, rfl⟩ := exists_real_parts Z
    obtain ⟨hKX, hKY⟩ := hK hKZ
    simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, hequ1 X1 hX1 hKX,
      hequ1 Y1 hY1 hKY]
  have hφE : φ P ∈ E := hE φ hequ P hPW
  rw [← hrep P y hyY]
  exact hy _ hφE

private theorem contrR_map_id {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] (l : B →ₗ[ℂ] ℂ) (b : Module.End ℂ B) (z : TensorProduct ℂ A B) :
    contrR l (TensorProduct.map LinearMap.id b z) = contrR (l ∘ₗ b) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp
  | add z z' hz hz' => rw [map_add (f := _), map_add (f := _), hz, hz', map_add (f := _)]

private theorem contrR_neg' {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B]
    [Module ℂ B] (l : B →ₗ[ℂ] ℂ) (z : TensorProduct ℂ A B) :
    contrR (-l) z = -contrR l z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [neg_smul]
  | add z z' hz hz' => rw [map_add (f := _), map_add (f := _), hz, hz', neg_add]

theorem exists_tensor_map : ∀ (p q r s : ℕ) (T₂ : GrpData r s) (R₂ : DSRep T₂), AdmGK R₂.HK → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (B : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] N), (∀ Z ∈ upq r s, ∀ P y, B (fockAct2 p q r s Z P) y + B P (R₂.HK.act Z y) = 0) → ∃ f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ N R₂.HK.V, (∀ Y, f ∘ₗ fockAct2 p q r s Y = TensorProduct.map LinearMap.id (R₂.HK.act Y) ∘ₗ f) ∧ (∀ P y, B P y = TensorProduct.rid ℂ N (TensorProduct.map LinearMap.id (innerₛₗ ℂ (R₂.ι y) ∘ₗ R₂.ι) (f P))) ∧ ∀ (c : Module.End ℂ (Pol p q r s)) (a : Module.End ℂ N), (∀ P y, B (c P) y = a (B P y)) → f ∘ₗ c = TensorProduct.map a LinearMap.id ∘ₗ f := by
  intro p q r s T₂ R₂ hA N _ _ B hB
  classical
  let m : R₂.HK.V → R₂.HK.V →ₗ[ℂ] ℂ := fun y => innerₛₗ ℂ (R₂.ι y) ∘ₗ R₂.ι
  have hm : ∀ y x, m y x = inner ℂ (R₂.ι y) (R₂.ι x) := fun _ _ => rfl
  have huniq : ∀ t t' : TensorProduct ℂ N R₂.HK.V,
      (∀ y, contrR (m y) t = contrR (m y) t') → t = t' := by
    intro t t' h
    rw [← sub_eq_zero]
    refine eq_zero_of_contrR m (fun x hx => ?_) _ (fun y => ?_)
    · have h1 := hx x
      rw [hm, inner_self_eq_zero, ← map_zero R₂.ι] at h1
      exact R₂.ι_inj h1
    · rw [map_sub, h y, sub_self]
  have hex : ∀ P, ∃ t : TensorProduct ℂ N R₂.HK.V, ∀ y, B P y = contrR (m y) t := by
    intro P
    obtain ⟨E, hEfd, hE⟩ := exists_finiteDimensional_kill R₂ hA B hB P
    haveI := hEfd
    obtain ⟨n, a, haE, hfr⟩ := exists_frame R₂.ι R₂.ι_inj E
    refine ⟨∑ j, B P (a j) ⊗ₜ[ℂ] a j, fun y => ?_⟩
    have hperp : B P (y - ∑ j, inner ℂ (R₂.ι (a j)) (R₂.ι y) • a j) = 0 := by
      apply hE
      intro x hx
      have e1 : inner ℂ (R₂.ι y) (R₂.ι x) =
          ∑ j, inner ℂ (R₂.ι (a j)) (R₂.ι x) * inner ℂ (R₂.ι y) (R₂.ι (a j)) := by
        conv_lhs => rw [← hfr x hx]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, inner_sum, inner_smul_right]
      rw [map_sub, inner_sub_left, e1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, sum_inner, inner_smul_left, inner_conj_symm]
      rw [sub_eq_zero]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [map_sub, sub_eq_zero] at hperp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hperp, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smulₛₗ, contrR_tmul, hm, inner_conj_symm]
  choose F hF using hex
  have hadd : ∀ P Q, F (P + Q) = F P + F Q := fun P Q => huniq _ _ fun y => by
    rw [map_add (f := _), ← hF, ← hF, ← hF, map_add (f := _), LinearMap.add_apply]
  have hsmul : ∀ (c : ℂ) P, F (c • P) = c • F P := fun c P => huniq _ _ fun y => by
    rw [map_smul, ← hF, ← hF, map_smul, LinearMap.smul_apply]
  let f : Pol p q r s →ₗ[ℂ] TensorProduct ℂ N R₂.HK.V :=
    { toFun := F, map_add' := hadd, map_smul' := fun c P => by simpa using hsmul c P }
  have hf : ∀ P, f P = F P := fun _ => rfl
  have hupq : ∀ Y ∈ upq r s, ∀ P,
      F (fockAct2 p q r s Y P) = TensorProduct.map LinearMap.id (R₂.HK.act Y) (F P) := by
    intro Y hY P
    refine huniq _ _ fun y => ?_
    rw [← hF, contrR_map_id]
    have hl : m y ∘ₗ R₂.HK.act Y = -m (R₂.HK.act Y y) := by
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.comp_apply, LinearMap.neg_apply, hm, hm]
      exact eq_neg_of_add_eq_zero_left (inner_act_skew R₂ hY y x)
    rw [hl, contrR_neg', ← hF]
    exact eq_neg_of_add_eq_zero_left (hB Y hY P y)
  refine ⟨f, fun Y => ?_, fun P y => hF P y, fun c a hca => ?_⟩
  · obtain ⟨X1, Y1, hX1, hY1, -, hY⟩ := exists_real_parts Y
    refine LinearMap.ext fun P => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hf, hf, hY, map_add (f := _), map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, hadd, hsmul, hupq X1 hX1, hupq Y1 hY1, map_add,
      map_smul, TensorProduct.map_add_right, TensorProduct.map_smul_right, LinearMap.add_apply,
      LinearMap.smul_apply]
  · refine LinearMap.ext fun P => huniq _ _ fun y => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hf, hf, ← hF, contrR_map, ← hF, hca]

end GlobalTheory.InvPairingTensor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPiTensorMvPolynomialProdEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPiTensorMvPolynomialProdEquiv
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

noncomputable section

namespace GlobalTheory.PolyTensor

theorem curry_sum_mapDomain {ι β : Type} [Fintype ι] (v : ι → (β →₀ ℕ)) (τ : ι) :
    (∑ σ, Finsupp.mapDomain (fun x => (σ, x)) (v σ)).curry τ = v τ := by
  classical
  ext x
  rw [Finsupp.curry_apply, Finsupp.finsetSum_apply, Finset.sum_eq_single τ]
  · exact Finsupp.mapDomain_apply_of_injective (fun a b h => (Prod.mk.inj h).2) (v τ) x
  · intro σ _ hσ
    apply Finsupp.mapDomain_notin_range
    rintro ⟨y, hy⟩
    exact hσ (congrArg Prod.fst hy)
  · intro h
    exact absurd (Finset.mem_univ τ) h

def expEquiv (ι σ : Type) [Fintype ι] : (ι → (σ →₀ ℕ)) ≃ (ι × σ →₀ ℕ) :=
  Equiv.ofBijective (fun v => ∑ τ, Finsupp.mapDomain (fun x => (τ, x)) (v τ)) <| by
    classical
    refine ⟨fun v w h => funext fun τ => ?_, fun m => ⟨fun τ => m.curry τ, ?_⟩⟩
    · rw [← curry_sum_mapDomain v τ, ← curry_sum_mapDomain w τ]
      exact congrArg (fun m : ι × σ →₀ ℕ => m.curry τ) h
    · ext ⟨τ, x⟩
      have := DFunLike.congr_fun (curry_sum_mapDomain (fun τ => m.curry τ) τ) x
      simpa only [Finsupp.curry_apply] using this

theorem exists_piTensor_equiv : ∀ (ι σ : Type) [Fintype ι],
    ∃ e : (⨂[ℂ] _ : ι, MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ,
      ∀ f : ι → MvPolynomial σ ℂ,
        e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ) := by
  intro ι σ _
  classical
  let bT := Basis.piTensorProduct (fun _ : ι => MvPolynomial.basisMonomials σ ℂ)
  let e : (⨂[ℂ] _ : ι, MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ :=
    bT.equiv (MvPolynomial.basisMonomials (ι × σ) ℂ) (expEquiv ι σ)

  have key : e.toLinearMap.compMultilinearMap (PiTensorProduct.tprod ℂ) =
      (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × σ) ℂ)).compLinearMap
        (fun τ => (rename (Prod.mk τ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (ι × σ) ℂ).toLinearMap) := by
    refine Module.Basis.ext_multilinear (fun _ => MvPolynomial.basisMonomials σ ℂ) fun v => ?_
    rw [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, ← Basis.piTensorProduct_apply]
    change bT.equiv (MvPolynomial.basisMonomials (ι × σ) ℂ) (expEquiv ι σ) (bT v) = _
    rw [Module.Basis.equiv_apply]
    simp only [MvPolynomial.coe_basisMonomials, AlgHom.toLinearMap_apply,
      MvPolynomial.rename_monomial, expEquiv, Equiv.ofBijective_apply]
    exact MvPolynomial.monomial_sum_one _ _
  refine ⟨e, fun f => ?_⟩
  simpa using MultilinearMap.congr_fun key f

end GlobalTheory.PolyTensor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPiTensorMvPolynomialProdEquivStatement
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_piTensor_mvPolynomial_prod_equiv : ∀ (ι σ : Type) [Fintype ι], ∃ e : (⨂[ℂ] _ : ι, MvPolynomial σ ℂ) ≃ₗ[ℂ] MvPolynomial (ι × σ) ℂ, ∀ f : ι → MvPolynomial σ ℂ, e (PiTensorProduct.tprod ℂ f) = ∏ τ, rename (Prod.mk τ) (f τ) := by
  first | exact @GlobalTheory.PolyTensor.exists_piTensor_equiv | exact GlobalTheory.PolyTensor.exists_piTensor_equiv | (intros; apply GlobalTheory.PolyTensor.exists_piTensor_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoUnitaryIrrepConjDual
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoUnitaryIrrepConjDual
noncomputable section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching Formalism.GradedWeylDivisibility Formalism.REAL
open scoped TensorProduct DirectSum Matrix

namespace GlobalTheory.ConjDual

theorem map_rowAct {r n : ℕ} (φ : ℂ →+* ℂ) (A : Matrix (Fin r) (Fin r) ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    map φ (rowAct ℂ A f) = rowAct ℂ (A.map φ) (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp [rowAct]

def bil (σ : Type) : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun f f' => fockF f (map (starRingEnd ℂ) f'))
    (fun _ _ _ => fischerInner_add_left _ _ _)
    (fun c f f' => by rw [smul_eq_C_mul, LFocks_C_mul_left, smul_eq_mul])
    (fun f a b => by rw [map_add (f := _), fischerInner_add_right])
    (fun c f f' => by
      rw [smul_eq_C_mul, map_mul, map_C, LFocks_C_mul_right, smul_eq_mul]
      simp)

theorem bil_apply {σ : Type} (f f' : MvPolynomial σ ℂ) : bil σ f f' = fockF f (map (starRingEnd ℂ) f') := rfl

theorem bil_rowAct {r n : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (f f' : MvPolynomial (Fin r × Fin n) ℂ) :
    bil _ (rowAct ℂ A f) f' = bil _ f (rowAct ℂ Aᵀ f') := by
  rw [bil_apply, bil_apply, fockRowAdj, map_rowAct]
  rfl

theorem bil_conj {σ : Type} (f : MvPolynomial σ ℂ) : bil σ f (map (starRingEnd ℂ) f) = fockF f f := by
  rw [bil_apply, map_map]
  have : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by ext; simp
  rw [this, map_id]

def toDual (n : ℕ) (lam : DomWeight n) : nablaSq ℂ n lam →ₗ[ℂ] Module.Dual ℂ (nablaSq ℂ n lam) :=
  (bil _).compl₁₂ (nablaSq ℂ n lam).subtype (nablaSq ℂ n lam).subtype

theorem toDual_injective (n : ℕ) (lam : DomWeight n) : Function.Injective (toDual n lam) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro f hf
  by_contra h0
  have h1 : f.1 ≠ 0 := fun h => h0 (Subtype.ext h)
  have h2 := LinearMap.congr_fun hf ⟨map (starRingEnd ℂ) f.1, dualWeylMap ℂ ℂ _ n n _ _ f.2⟩
  have h3 : fockF f.1 f.1 = 0 := (bil_conj f.1).symm.trans h2
  have h := fockPos _ f.1 h1
  rw [h3] at h
  simp at h

theorem detPow_conjU (n : ℕ) (g : U n) (c : ℤ) :
    detPow ℂ n (unitaryIncl n (conjU n g)) c = detPow ℂ n (unitaryIncl n g⁻¹) c := by
  unfold detPow
  congr 2
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, unitaryIncl_coe,
    unitaryIncl_coe, conjU_coe, Matrix.det_transpose]
  rfl

theorem iso_conj_dual : ∀ (n : ℕ) (lam : DomWeight n),
    Iso ((irr n lam).comp (conjU n) : Representation ℂ (U n) (nablaSq ℂ n lam)) (irr n lam).dual := by
  intro n lam
  refine ⟨(toDual n lam).linearEquivOfInjective (toDual_injective n lam) Subspace.dual_finrank_eq.symm,
    fun g x => ?_⟩
  ext y
  change bil _ (sqAct ℂ n lam (unitaryIncl n (conjU n g)) x.1) y.1 =
    bil _ x.1 (sqAct ℂ n lam (unitaryIncl n g⁻¹) y.1)
  unfold sqAct
  rw [map_smul, map_smul, LinearMap.smul_apply, detPow_conjU, bil_rowAct, Matrix.transpose_transpose]
  rfl

end GlobalTheory.ConjDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoUnitaryIrrepConjDualStatement
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_unitaryIrrep_conj_dual : ∀ (n : ℕ) (lam : DomWeight n), Iso ((irr n lam).comp (conjU n) : Representation ℂ (U n) (nablaSq ℂ n lam)) (irr n lam).dual := by
  first | exact @GlobalTheory.ConjDual.iso_conj_dual | exact GlobalTheory.ConjDual.iso_conj_dual | (intros; apply GlobalTheory.ConjDual.iso_conj_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoTwistDetIrrShift
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoTwistDetIrrShift
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

private lemma detShift_eq_add_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c)
    (hn : 0 < n) : lam'.detShift = lam.detShift + c := by
  simp only [DomWeight.detShift, dif_pos hn, h]

private lemma natW_eq_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) :
    lam'.natW = lam.natW := by
  funext i
  simp only [DomWeight.natW, detShift_eq_add_of_weight_shift n c lam lam' h (Fin.pos i), h]
  congr 1
  ring

private lemma nablaSq_eq_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) :
    nablaSq ℂ n lam' = nablaSq ℂ n lam := by
  simp only [nablaSq, natW_eq_of_weight_shift n c lam lam' h]

private lemma detPow_detShift_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) (g : U n) :
    detPow ℂ n (unitaryIncl n g) lam'.detShift =
      ((detU n g ^ c : ℂˣ) : ℂ) * detPow ℂ n (unitaryIncl n g) lam.detShift := by
  have hdet : Matrix.GeneralLinearGroup.det (unitaryIncl n g) = detU n g := by
    ext
    simp [detU, unitaryIncl_coe]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h1 : detU 0 g = 1 := by
      ext
      simp [detU]
    simp [h1, DomWeight.detShift, detPow]
  · simp only [detPow, detShift_eq_add_of_weight_shift n c lam lam' h hn, hdet, zpow_add, Units.val_mul]
    ring

theorem iso_twist_det_irr_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) :
    Iso (twist (detU n ^ c) (irr n lam)) (irr n lam') := by
  refine ⟨LinearEquiv.ofEq _ _ (nablaSq_eq_of_weight_shift n c lam lam' h).symm, fun g x => ?_⟩
  apply Subtype.ext
  change ((detU n ^ c) g : ℂ) • (sqRep ℂ n lam (unitaryIncl n g) x : MvPolynomial (Fin n × Fin n) ℂ) =
    (sqRep ℂ n lam' (unitaryIncl n g) (LinearEquiv.ofEq _ _ (nablaSq_eq_of_weight_shift n c lam lam' h).symm x) :
      MvPolynomial (Fin n × Fin n) ℂ)
  have hz : (detU n ^ c) g = detU n g ^ c := rfl
  rw [sqRep_coe, sqRep_coe, hz]
  simp only [sqAct, LinearEquiv.coe_ofEq_apply, detPow_detShift_of_weight_shift n c lam lam' h g, mul_smul]

end GlobalTheory.OneFunctional
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsoTwistDetIrrShiftStatement
open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_twist_detU_pow_irr_of_weight_shift : ∀ (n : ℕ) (c : ℤ) (lam lam' : DomWeight n), (∀ i, lam'.w i = lam.w i + c) → Iso (twist (detU n ^ c) (irr n lam)) (irr n lam') := by
  first | exact @GlobalTheory.OneFunctional.iso_twist_det_irr_shift | exact GlobalTheory.OneFunctional.iso_twist_det_irr_shift | (intros; apply GlobalTheory.OneFunctional.iso_twist_det_irr_shift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexConjParahoric
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition

namespace GlobalTheory.ParahoricConjugateOpen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_conj_inf {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (g : G) :
    IsOpen ((H.map (MulAut.conj g).toMonoidHom ⊓ H : Subgroup G) : Set G) := by
  rw [Subgroup.coe_inf]
  refine IsOpen.inter ?_ hH
  have : ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) = (fun x => g⁻¹ * x * g) ⁻¹' (H : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨_, hx, by simp [mul_assoc]⟩
  rw [this]
  exact hH.preimage (by fun_prop)

theorem isOpen_KO (n : Type) [Fintype n] [DecidableEq n] : IsOpen (KO k n : Set (GL n k)) :=
  Subgroup.isOpen_mono StepData.KOne_le_KO StepData.isOpen_KOne

theorem isOpen_parahoric (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] :
    IsOpen (parahoric k A D : Set (GL (A ⊕ D) k)) := by
  refine Subgroup.isOpen_mono (H₁ := KOne k (A ⊕ D)) (fun g hg => ?_) StepData.isOpen_KOne
  refine mem_parahoric.2 ⟨StepData.KOne_le_KO hg, fun i j => ?_⟩
  simpa using StepData.mem_KOne.1 hg (.inr i) (.inl j)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem torusElt_zero (n : Type) [Fintype n] [DecidableEq n] (ϖ : kˣ) :
    torusElt k n ϖ (fun _ => 0) = 1 := by
  refine Units.ext ?_
  rw [val_torusElt]
  simp

theorem conj_one_inf {G : Type} [Group G] (H : Subgroup G) :
    (H.map (MulAut.conj (1 : G)).toMonoidHom ⊓ H : Subgroup G) = H := by
  have : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
  rw [this, Subgroup.map_id, inf_idem]

theorem vol_conj_inf [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ϖ : kˣ)
    (hϖ : valuation k (ϖ : k) = uniformizer k)
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ) :
    (volM ν (A ⊕ D) (A ⊕ D) (Units.val ''
      (((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom ⊓ parahoric k A D :
        Subgroup (GL (A ⊕ D) k)) : Set (GL (A ⊕ D) k)))).toReal =
      (volM ν A A (Units.val '' (KO k A : Set (GL A k)))).toReal *
        (ν (𝒪[k] : Set k)).toReal ^ (2 * (Fintype.card A * Fintype.card D)) *
        (resCard k : ℝ) ^ (-((Fintype.card A : ℤ) * (Fintype.card D + sumAbs e))) *
        (volM ν D D (Units.val '' (((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom ⊓ KO k D :
          Subgroup (GL D k)) : Set (GL D k)))).toReal := by
  have hq : (0 : ℝ) < resCard k := Nat.cast_pos.2 Nat.card_pos
  have h1 := GlobalTheory.T.matrixEntrywiseProductMeasure_uniformizer_power_box k ν ϖ hϖ A D (fun _ j => max 0 (-e j))
  have h2 := GlobalTheory.T.matrixEntrywiseProductMeasure_uniformizer_power_box k ν ϖ hϖ D A (fun i _ => 1 + max 0 (e i))
  rw [GlobalTheory.T.val_twoBlockParahoric_inf_torusConj_blockwise k ϖ hϖ A D e, GlobalTheory.T.volM_blocks_eq_mul, h1, h2]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (zpow_pos hq _).le]
  have hs : -((Fintype.card A : ℤ) * (Fintype.card D + sumAbs e)) =
      (-∑ _i : A, ∑ j : D, max 0 (-e j)) + (-∑ i : D, ∑ _j : A, (1 + max 0 (e i))) := by
    have : sumAbs e = ∑ j : D, max 0 (-e j) + ∑ j : D, max 0 (e j) := by
      rw [sumAbs, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rcases le_total 0 (e j) with h | h
      · rw [abs_of_nonneg h, max_eq_left (by omega), max_eq_right h]; ring
      · rw [abs_of_nonpos h, max_eq_right (by omega), max_eq_left h]; ring
    rw [this, Finset.sum_comm (s := (Finset.univ : Finset D))]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_add_distrib]
    ring
  rw [hs, zpow_add₀ hq.ne', mul_comm (Fintype.card D) (Fintype.card A)]
  ring

theorem relIndex_conj_parahoric (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k)
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ) :
    ((((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom).relIndex (parahoric k A D) : ℕ) : ℝ) =
      (resCard k : ℝ) ^ ((Fintype.card A : ℤ) * sumAbs e) *
        ((((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom).relIndex (KO k D) : ℕ) : ℝ) := by
  borelize k
  let ν : Measure k := Measure.addHaar
  have hq : (0 : ℝ) < resCard k := Nat.cast_pos.2 Nat.card_pos
  obtain ⟨hp, hJ⟩ := GlobalTheory.T.relIndex_mul_matrixVolume_open_subgroup_integralGL k ν (A ⊕ D) _ (parahoric k A D) inf_le_right
    (fun g hg => (mem_parahoric.1 hg).1) (isOpen_conj_inf _ (isOpen_parahoric A D) (mtor (A := A) ϖ e))
  obtain ⟨-, hK⟩ := GlobalTheory.T.relIndex_mul_matrixVolume_open_subgroup_integralGL k ν D _ (KO k D) inf_le_right le_rfl
    (isOpen_conj_inf _ (isOpen_KO D) (torusElt k D ϖ e))
  rw [Subgroup.inf_relIndex_right] at hJ hK
  have h0 := vol_conj_inf ν ϖ hϖ A D (fun _ => 0)
  have hm : mtor (A := A) ϖ (fun _ : D => 0) = 1 := by
    rw [← torusElt_zero (A ⊕ D) ϖ, mtor]
    congr 1
    funext x
    cases x <;> rfl
  rw [hm, torusElt_zero, conj_one_inf, conj_one_inf] at h0
  refine mul_right_cancel₀ hp.ne' ?_
  rw [hJ, h0, ← hK, vol_conj_inf ν ϖ hϖ A D e]
  have hs : sumAbs (fun _ : D => (0 : ℤ)) = 0 := by simp [sumAbs]
  have hz : (resCard k : ℝ) ^ (-((Fintype.card A : ℤ) * (Fintype.card D + sumAbs (fun _ : D => (0 : ℤ))))) =
      (resCard k : ℝ) ^ ((Fintype.card A : ℤ) * sumAbs e) *
        (resCard k : ℝ) ^ (-((Fintype.card A : ℤ) * (Fintype.card D + sumAbs e))) := by
    rw [← zpow_add₀ hq.ne', hs]
    congr 1
    ring
  rw [hz]
  ring

end GlobalTheory.ParahoricConjugateOpen
end
end
