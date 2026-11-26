module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentInFibreIffOfIsPullback

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquarePresentationOfTower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquarePresentationOfTower
open scoped TensorProduct

namespace GlobalTheory.SquareTower

open MvPolynomial

noncomputable def presOf {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {s : ℕ}
    (φ : MvPolynomial (Fin s) R →ₐ[R] S) (g : Fin s → MvPolynomial (Fin s) R)
    (hs : Function.Surjective φ) (hk : RingHom.ker φ = Ideal.span (Set.range g)) :
    Algebra.Presentation R S (Fin s) (Fin s) :=
  have he : MvPolynomial.aeval (fun i => φ (X i)) = φ := MvPolynomial.algHom_ext (fun i => aeval_X _ _)
  { toGenerators := Algebra.Generators.ofSurjective (fun i => φ (X i)) (by rw [he]; exact hs)
    relation := g
    span_range_relation_eq_ker := by
      rw [Algebra.Generators.ker_eq_ker_aeval_val, ← hk]
      change RingHom.ker φ = RingHom.ker (MvPolynomial.aeval (fun i => φ (X i)))
      rw [he] }

theorem square_of_pres {R T ι σ : Type} [CommRing R] [CommRing T] [Algebra R T] {n : ℕ}
    (P : Algebra.Presentation R T ι σ) (e : Fin n ≃ ι) (f : Fin n ≃ σ) :
    ∃ (s : ℕ) (φ : MvPolynomial (Fin s) R →ₐ[R] T) (g : Fin s → MvPolynomial (Fin s) R),
      Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g) := by
  let E : MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial ι R := renameEquiv R e
  refine ⟨n, (aeval P.val).comp E.toAlgHom, fun i => E.symm (P.relation (f i)), ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := P.toGenerators.algebraMap_surjective y
    refine ⟨E.symm x, ?_⟩
    show aeval P.val (E (E.symm x)) = y
    rw [E.apply_symm_apply, ← hx, Algebra.Generators.algebraMap_eq]
    rfl
  · have h1 : Set.range (fun i => E.symm (P.relation (f i))) = E.symm '' Set.range P.relation := by
      rw [← Set.range_comp]
      exact f.surjective.range_comp (⇑E.symm ∘ P.relation)
    rw [h1, ← Ideal.map_span, P.span_range_relation_eq_ker, Algebra.Generators.ker_eq_ker_aeval_val]
    ext x
    rw [RingHom.mem_ker, Ideal.mem_map_of_equiv]
    constructor
    · intro hx
      refine ⟨E x, ?_, by simp⟩
      rw [RingHom.mem_ker]; simpa using hx
    · rintro ⟨y, hy, rfl⟩
      rw [RingHom.mem_ker] at hy
      simpa using hy

theorem tower : ∀ (k B A : Type) [CommRing k] [CommRing B] [CommRing A] [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A], (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] B) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) B →ₐ[B] A) (g : Fin s → MvPolynomial (Fin s) B), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  intro k B A _ _ _ _ _ _ _
  rintro ⟨t, φ, g, hφ, hg⟩ ⟨d, ψ, h, hψ, hh⟩
  let P := presOf φ g hφ hg
  let Q := presOf ψ h hψ hh
  exact square_of_pres (Q.comp P) finSumFinEquiv.symm finSumFinEquiv.symm

end GlobalTheory.SquareTower
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquarePresentationOfTowerStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_presentation_of_tower : ∀ (k B A : Type) [CommRing k] [CommRing B] [CommRing A] [Algebra k B] [Algebra k A] [Algebra B A] [IsScalarTower k B A], (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] B) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) B →ₐ[B] A) (g : Fin s → MvPolynomial (Fin s) B), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  first | exact @GlobalTheory.SquareTower.tower | exact GlobalTheory.SquareTower.tower | (intros; apply GlobalTheory.SquareTower.tower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusSubalgebraCounitalComul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusSubalgebraCounitalComul
open scoped TensorProduct

namespace GlobalTheory

theorem frobSubalgebra_counit : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] [PerfectRing k p] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∃ B : Subalgebra k A, (∀ a, a ∈ B ↔ ∃ c : A, c ^ p = a) ∧ ∃ Δ' : B →ₐ[k] B ⊗[k] B, ((∀ a : B, TensorProduct.lid k B (LinearMap.rTensor B (ε.comp B.val).toLinearMap (Δ' a)) = a) ∧ (∀ a : B, TensorProduct.rid k B (LinearMap.lTensor B (ε.comp B.val).toLinearMap (Δ' a)) = a)) := by
  intro p _ k A _ _ _ _ _ ε Δ ⟨hl, hr⟩
  have injA : Function.Injective (algebraMap k A) := fun x y h => by
    simpa using congrArg ε h
  haveI : CharP A p := charP_of_injective_algebraMap injA p
  let εε : A ⊗[k] A →ₐ[k] k := Algebra.TensorProduct.lift ε ε (fun _ _ => Commute.all _ _)
  have injAA : Function.Injective (algebraMap k (A ⊗[k] A)) := fun x y h => by
    simpa only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using congrArg εε h
  haveI : CharP (A ⊗[k] A) p := charP_of_injective_algebraMap injAA p
  let B : Subalgebra k A :=
    { carrier := {a | ∃ c : A, c ^ p = a}
      mul_mem' := by rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩; exact ⟨c * d, mul_pow c d p⟩
      add_mem' := by rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩; exact ⟨c + d, add_pow_char c d p⟩
      algebraMap_mem' := by
        intro r
        obtain ⟨s, hs⟩ := surjective_frobenius k p r
        exact ⟨algebraMap k A s, by rw [← map_pow, ← hs, frobenius_def]⟩ }
  refine ⟨B, fun a => Iff.rfl, ?_⟩
  let j : B ⊗[k] B →ₐ[k] A ⊗[k] A := Algebra.TensorProduct.map B.val B.val
  have hj : Function.Injective j :=
    TensorProduct.map_injective_of_flat_flat B.val.toLinearMap B.val.toLinearMap
      Subtype.val_injective Subtype.val_injective
  have hpow : ∀ t : A ⊗[k] A, t ^ p ∈ j.range := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp [zero_pow (Fact.out : p.Prime).ne_zero]⟩
    | tmul a b =>
      exact ⟨(⟨a ^ p, a, rfl⟩ : B) ⊗ₜ (⟨b ^ p, b, rfl⟩ : B), by
        simp [j, Algebra.TensorProduct.tmul_pow]⟩
    | add x y hx hy => rw [add_pow_char]; exact add_mem hx hy
  have hΔ : ∀ b : B, Δ (B.val b) ∈ j.range := by
    rintro ⟨_, c, rfl⟩
    simpa [map_pow] using hpow (Δ c)
  let e := AlgEquiv.ofInjective j hj
  let Δ' : B →ₐ[k] B ⊗[k] B := e.symm.toAlgHom.comp ((Δ.comp B.val).codRestrict j.range hΔ)
  have hjΔ : ∀ b : B, j (Δ' b) = Δ (B.val b) := by
    intro b
    have h1 := e.apply_symm_apply ⟨Δ (B.val b), hΔ b⟩
    exact congrArg Subtype.val h1
  have kl : ∀ x : B ⊗[k] B, ((TensorProduct.lid k B (LinearMap.rTensor B (ε.comp B.val).toLinearMap x) : B) : A)
      = TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (j x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [j]
    | add x y hx hy => simp only [map_add (f := _), Subalgebra.coe_add, hx, hy]
  have kr : ∀ x : B ⊗[k] B, ((TensorProduct.rid k B (LinearMap.lTensor B (ε.comp B.val).toLinearMap x) : B) : A)
      = TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (j x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [j]
    | add x y hx hy => simp only [map_add (f := _), Subalgebra.coe_add, hx, hy]
  refine ⟨Δ', fun b => ?_, fun b => ?_⟩
  · apply Subtype.ext
    rw [kl, hjΔ]; exact hl _
  · apply Subtype.ext
    rw [kr, hjΔ]; exact hr _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusSubalgebraCounitalComulStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusSubalgebra_counital_comul : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] [PerfectRing k p] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∃ B : Subalgebra k A, (∀ a, a ∈ B ↔ ∃ c : A, c ^ p = a) ∧ ∃ Δ' : B →ₐ[k] B ⊗[k] B, ((∀ a : B, TensorProduct.lid k B (LinearMap.rTensor B (ε.comp B.val).toLinearMap (Δ' a)) = a) ∧ (∀ a : B, TensorProduct.rid k B (LinearMap.lTensor B (ε.comp B.val).toLinearMap (Δ' a)) = a)) := by
  first | exact @GlobalTheory.frobSubalgebra_counit | exact GlobalTheory.frobSubalgebra_counit | (intros; apply GlobalTheory.frobSubalgebra_counit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorsDualPointDerivationsAugmented
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorsDualPointDerivationsAugmented
open scoped TensorProduct

namespace GlobalTheory

theorem exists_generators_dual_point_derivations :
    ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k),
      IsNilpotent (RingHom.ker ε) → ∃ (d : ℕ) (x : Fin d → A) (l : Fin d → A →ₗ[k] k),
        (∀ i a b, l i (a * b) = ε a * l i b + ε b * l i a) ∧
        (∀ i j, l i (x j) = if i = j then 1 else 0) ∧ Algebra.adjoin k (Set.range x) = ⊤ := by
  intro k A _ _ _ _ ε hnil
  set I : Ideal A := RingHom.ker ε with hI
  let W : Submodule k A := (I ^ 2).restrictScalars k
  let U : Submodule k (A ⧸ W) := (I.restrictScalars k).map W.mkQ
  let b : Module.Basis (Fin (Module.finrank k U)) k U := Module.finBasis k U
  have hx : ∀ j, ∃ y, y ∈ I ∧ W.mkQ y = (b j : A ⧸ W) := fun j => by
    obtain ⟨y, hy, hy'⟩ := Submodule.mem_map.mp (b j).2
    exact ⟨y, hy, hy'⟩
  choose x hxI hxq using hx
  let P : A →ₗ[k] A := LinearMap.id - (Algebra.linearMap k A) ∘ₗ ε.toLinearMap
  have hPa : ∀ a, P a = a - algebraMap k A (ε a) := fun a => rfl
  have hP : ∀ a, P a ∈ I := fun a => by
    rw [hI, RingHom.mem_ker, hPa, map_sub, AlgHom.commutes]
    simp
  let T : A →ₗ[k] U := LinearMap.codRestrict U (W.mkQ ∘ₗ P)
    (fun a => Submodule.mem_map_of_mem (show P a ∈ I.restrictScalars k from hP a))
  have hT : ∀ a, ((T a : U) : A ⧸ W) = W.mkQ (P a) := fun a => rfl
  let l : Fin (Module.finrank k U) → A →ₗ[k] k := fun i => b.coord i ∘ₗ T
  have hspan : ∀ y ∈ I, ∃ s ∈ Submodule.span k (Set.range x), y - s ∈ I ^ 2 := by
    intro y hy
    let u : U := ⟨W.mkQ y, Submodule.mem_map_of_mem (show y ∈ I.restrictScalars k from hy)⟩
    refine ⟨∑ j, b.repr u j • x j,
      Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)), ?_⟩
    have h1 : W.mkQ (∑ j, b.repr u j • x j) = ∑ j, b.repr u j • (b j : A ⧸ W) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, hxq]
    have h2 := congrArg Subtype.val (b.sum_repr u)
    push_cast at h2
    have hq : W.mkQ (∑ j, b.repr u j • x j) = W.mkQ y := by rw [h1, h2]
    have h0 : W.mkQ (y - ∑ j, b.repr u j • x j) = 0 := by rw [map_sub, hq, sub_self]
    have h3 := LinearMap.mem_ker.mpr h0
    rw [Submodule.ker_mkQ] at h3
    exact h3
  let S := Algebra.adjoin k (Set.range x)
  have spanS : Submodule.span k (Set.range x) ≤ Subalgebra.toSubmodule S :=
    Submodule.span_le.mpr (fun z hz => Algebra.subset_adjoin hz)
  have spanI : Submodule.span k (Set.range x) ≤ I.restrictScalars k :=
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hxI j)
  have hstep : ∀ n : ℕ, ∀ z ∈ I ^ n,
      z ∈ Subalgebra.toSubmodule S ⊔ (I ^ (n + 1)).restrictScalars k := by
    intro n
    induction n with
    | zero =>
      intro z _
      refine Submodule.mem_sup.mpr ⟨_, S.algebraMap_mem (ε z), P z, ?_, ?_⟩
      · show P z ∈ I ^ (0 + 1)
        rw [zero_add, pow_one]; exact hP z
      · rw [hPa]; abel
    | succ n ih =>
      intro z hz
      rw [pow_succ'] at hz
      refine Submodule.mul_induction_on hz ?_ (fun a c ha hc => add_mem ha hc)
      intro y hy w hw
      obtain ⟨s, hs, hys⟩ := hspan y hy
      obtain ⟨t, ht, v, hv, htv⟩ := Submodule.mem_sup.mp (ih w hw)
      have h1 : s * v ∈ I ^ (n + 1 + 1) := by
        rw [pow_succ']; exact Ideal.mul_mem_mul (spanI hs) hv
      have h2 : (y - s) * w ∈ I ^ (n + 1 + 1) := by
        rw [show n + 1 + 1 = 2 + n by omega, pow_add]; exact Ideal.mul_mem_mul hys hw
      refine Submodule.mem_sup.mpr ⟨s * t, S.mul_mem (spanS hs) ht, s * v + (y - s) * w,
        add_mem h1 h2, ?_⟩
      rw [← htv]; ring
  have hall : ∀ n : ℕ, ∀ a : A, a ∈ Subalgebra.toSubmodule S ⊔ (I ^ n).restrictScalars k := by
    intro n
    induction n with
    | zero =>
      intro a
      refine Submodule.mem_sup.mpr ⟨0, zero_mem _, a, ?_, zero_add a⟩
      show a ∈ I ^ 0
      rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    | succ n ih =>
      intro a
      obtain ⟨s, hs, w, hw, hsw⟩ := Submodule.mem_sup.mp (ih a)
      obtain ⟨t, ht, v, hv, htv⟩ := Submodule.mem_sup.mp (hstep n w hw)
      refine Submodule.mem_sup.mpr ⟨s + t, add_mem hs ht, v, hv, ?_⟩
      rw [← hsw, ← htv]; abel
  refine ⟨Module.finrank k U, x, l, ?_, ?_, ?_⟩
  · intro i a c
    have key : P (a * c) - (ε a • P c + ε c • P a) = P a * P c := by
      simp only [hPa, Algebra.smul_def, map_mul]; ring
    have hmem : P (a * c) - (ε a • P c + ε c • P a) ∈ W := by
      rw [key]
      show P a * P c ∈ I ^ 2
      rw [pow_two]; exact Ideal.mul_mem_mul (hP a) (hP c)
    have hTac : T (a * c) = ε a • T c + ε c • T a := by
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, hT, hT, hT]
      have h0 : W.mkQ (P (a * c) - (ε a • P c + ε c • P a)) = 0 := by
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]; exact hmem
      rw [map_sub, map_add (f := _), map_smul, map_smul, sub_eq_zero] at h0
      exact h0
    show b.coord i (T (a * c)) = ε a * b.coord i (T c) + ε c * b.coord i (T a)
    rw [hTac, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  · intro i j
    have hTx : T (x j) = b j := by
      apply Subtype.ext
      rw [hT, hPa]
      have : ε (x j) = 0 := (RingHom.mem_ker).mp (hxI j)
      rw [this, map_zero, sub_zero, hxq]
    show b.coord i (T (x j)) = _
    rw [hTx, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, Ne.symm h]
  · obtain ⟨N, hN⟩ := hnil
    have hv : (I ^ N).restrictScalars k = ⊥ := by
      rw [hI, hN, Submodule.zero_eq_bot, Submodule.restrictScalars_bot]
    refine eq_top_iff.mpr (fun a _ => ?_)
    have := hall N a
    rw [hv, sup_bot_eq] at this
    exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorsDualPointDerivationsAugmentedStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generators_dual_point_derivations_augmented : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k), IsNilpotent (RingHom.ker ε) → ∃ (d : ℕ) (x : Fin d → A) (l : Fin d → A →ₗ[k] k), (∀ i a b, l i (a * b) = ε a * l i b + ε b * l i a) ∧ (∀ i j, l i (x j) = if i = j then 1 else 0) ∧ Algebra.adjoin k (Set.range x) = ⊤ := by
  first | exact @GlobalTheory.exists_generators_dual_point_derivations | exact GlobalTheory.exists_generators_dual_point_derivations | (intros; apply GlobalTheory.exists_generators_dual_point_derivations <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAevalTruncatedPolynomialPresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAevalTruncatedPolynomialPresentation
open scoped TensorProduct

namespace GlobalTheory

theorem ker_aeval_truncated : ∀ (n : ℕ), 0 < n → ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (d : ℕ) (x : Fin d → A) (b : Fin d → B), (∀ i, x i ^ n = algebraMap B A (b i)) → LinearIndependent B (fun a : Fin d → Fin n => ∏ i, x i ^ (a i : ℕ)) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin d) B →ₐ[B] A) = Ideal.span (Set.range fun i : Fin d => (MvPolynomial.X i ^ n - MvPolynomial.C (b i) : MvPolynomial (Fin d) B)) := by
  intro n hn B A _ _ _ d x b hx hli
  set J : Ideal (MvPolynomial (Fin d) B) := Ideal.span (Set.range fun i : Fin d =>
    (MvPolynomial.X i ^ n - MvPolynomial.C (b i) : MvPolynomial (Fin d) B)) with hJ
  have hJker : J ≤ RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin d) B →ₐ[B] A) := by
    rw [hJ, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker, hx]
  refine le_antisymm ?_ hJker
  let q : MvPolynomial (Fin d) B →ₐ[B] (MvPolynomial (Fin d) B ⧸ J) := Ideal.Quotient.mkₐ B J
  have hq : ∀ F G, q F = q G ↔ F - G ∈ J := fun F G => by
    simp only [q, Ideal.Quotient.mkₐ_eq_mk]; exact Ideal.Quotient.eq
  let y : Fin d → (MvPolynomial (Fin d) B ⧸ J) := fun i => q (MvPolynomial.X i)
  let v : (Fin d → Fin n) → (MvPolynomial (Fin d) B ⧸ J) := fun a => ∏ i, y i ^ (a i : ℕ)
  have hqv : ∀ a, q (∏ i, MvPolynomial.X i ^ (a i : ℕ)) = v a := fun a => by
    simp [v, y, map_prod, map_pow]
  have hyn : ∀ i, y i ^ n = algebraMap B _ (b i) := by
    intro i
    have h1 : q (MvPolynomial.X i ^ n) = q (MvPolynomial.C (b i)) :=
      (hq _ _).mpr (Ideal.subset_span ⟨i, rfl⟩)
    simp only [y]
    rw [← map_pow, h1, ← MvPolynomial.algebraMap_eq, q.commutes]
  have hsplit : ∀ (a : Fin d → Fin n) (i : Fin d) (k : Fin n),
      v (Function.update a i k) = y i ^ (k : ℕ) * ∏ j ∈ Finset.univ.erase i, y j ^ (a j : ℕ) := by
    intro a i k
    simp only [v]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · exact Finset.prod_congr rfl fun j hj => by simp [Finset.ne_of_mem_erase hj]
  have hsplit0 : ∀ (a : Fin d → Fin n) (i : Fin d),
      v a = y i ^ (a i : ℕ) * ∏ j ∈ Finset.univ.erase i, y j ^ (a j : ℕ) := by
    intro a i
    have := hsplit a i (a i)
    rwa [Function.update_eq_self] at this
  let S := Submodule.span B (Set.range v)
  have hgen : ∀ (a : Fin d → Fin n) (i : Fin d), v a * y i ∈ S := by
    intro a i
    by_cases h : (a i : ℕ) + 1 < n
    · have : v a * y i = v (Function.update a i ⟨a i + 1, h⟩) := by
        rw [hsplit, hsplit0 a i, pow_succ]; ring
      rw [this]; exact Submodule.subset_span ⟨_, rfl⟩
    · have h' : (a i : ℕ) + 1 = n := by have := (a i).isLt; omega
      have : v a * y i = b i • v (Function.update a i ⟨0, hn⟩) := by
        have hp : y i ^ n = y i ^ ((a i : ℕ) + 1) := by rw [h']
        rw [hsplit, hsplit0 a i, Algebra.smul_def, ← hyn, hp, pow_succ]; simp; ring
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hmulX : ∀ i, ∀ s ∈ S, s * y i ∈ S := by
    intro i s hs
    induction hs using Submodule.span_induction with
    | mem s hs => obtain ⟨a, rfl⟩ := hs; exact hgen a i
    | zero => simp
    | add s t _ _ hs ht => rw [add_mul]; exact add_mem hs ht
    | smul c s _ hs => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hs
  have hall : ∀ F, q F ∈ S := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C c =>
      have : q (MvPolynomial.C c) = c • v (fun _ => ⟨0, hn⟩) := by
        rw [← MvPolynomial.algebraMap_eq, q.commutes, Algebra.algebraMap_eq_smul_one]
        simp [v]
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    | add p r hp hr => rw [map_add]; exact add_mem hp hr
    | mul_X p i hp => rw [map_mul]; exact hmulX i _ hp
  intro F hF
  rw [RingHom.mem_ker] at hF
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp (hall F)
  set G : MvPolynomial (Fin d) B := ∑ a, c a • ∏ i, MvPolynomial.X i ^ (a i : ℕ) with hG
  have hqG : q G = q F := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc, hG, map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, hqv]
  have hFG : F - G ∈ J := (hq F G).mp hqG.symm
  have hevG : MvPolynomial.aeval x G = 0 := by
    have h0 := hJker hFG
    rw [RingHom.mem_ker, map_sub, hF] at h0
    simpa using h0
  have hsum : ∑ a, c a • ∏ i, x i ^ (a i : ℕ) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hevG, hG, map_sum]
    exact Finset.sum_congr rfl fun a _ => by simp [map_prod, map_pow]
  have hc0 := Fintype.linearIndependent_iff.mp hli c hsum
  have hG0 : G = 0 := by rw [hG]; simp [hc0]
  simpa [hG0] using hFG

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAevalTruncatedPolynomialPresentationStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_aeval_truncatedPolynomial_presentation : ∀ (n : ℕ), 0 < n → ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (d : ℕ) (x : Fin d → A) (b : Fin d → B), (∀ i, x i ^ n = algebraMap B A (b i)) → LinearIndependent B (fun a : Fin d → Fin n => ∏ i, x i ^ (a i : ℕ)) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin d) B →ₐ[B] A) = Ideal.span (Set.range fun i : Fin d => (MvPolynomial.X i ^ n - MvPolynomial.C (b i) : MvPolynomial (Fin d) B)) := by
  first | exact @GlobalTheory.ker_aeval_truncated | exact GlobalTheory.ker_aeval_truncated | (intros; apply GlobalTheory.ker_aeval_truncated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedMonomialsLinearIndependentOverConstants
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedMonomialsLinearIndependentOverConstants
open scoped TensorProduct

namespace GlobalTheory

open MvPolynomial

theorem truncMono_deriv_aeval {k A : Type} [Field k] [CommRing A] [Algebra k A] {d : ℕ}
    (x : Fin d → A) (E : Fin d → Derivation k A A)
    (hE : ∀ i j, E i (x j) = if i = j then 1 else 0) (B : Subalgebra k A)
    (hB : ∀ i, ∀ b ∈ B, E i b = 0) (i : Fin d) (F : MvPolynomial (Fin d) B) :
    E i (aeval x F) = aeval x (pderiv i F) := by
  induction F using MvPolynomial.induction_on with
  | C b =>
    rw [aeval_C, pderiv_C, map_zero]
    exact hB i _ b.2
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  | mul_X p j hp =>
    have h1 : E i (aeval x p * x j) = aeval x p * E i (x j) + x j * E i (aeval x p) := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    rw [map_mul, aeval_X, h1, hp, pderiv_mul, pderiv_X, map_add (f := _), map_mul, map_mul, aeval_X, hE]
    by_cases h : i = j
    · subst h; simp; ring
    · simp [h, Pi.single_apply, Ne.symm h]; ring

theorem truncMono_eq_zero {p : ℕ} [Fact p.Prime] {k A : Type} [Field k] [CommRing A]
    [Algebra k A] [CharP k p] {d : ℕ}
    (x : Fin d → A) (E : Fin d → Derivation k A A)
    (hE : ∀ i j, E i (x j) = if i = j then 1 else 0) (B : Subalgebra k A)
    (hB : ∀ i, ∀ b ∈ B, E i b = 0) :
    ∀ n : ℕ, ∀ F : MvPolynomial (Fin d) B,
      (∀ m ∈ F.support, (∀ i, m i < p) ∧ ∑ i, m i ≤ n) → aeval x F = 0 → F = 0 := by
  have hconst : ∀ F : MvPolynomial (Fin d) B, (∀ m, m ≠ 0 → AddMonoidAlgebra.coeff F m = 0) →
      aeval x F = 0 → F = 0 := by
    intro F hc hF
    have hFC : F = C (AddMonoidAlgebra.coeff F 0) := by
      refine MvPolynomial.ext _ _ (fun m => ?_)
      rw [coeff_C]
      by_cases hm : m = 0
      · subst hm; simp
      · rw [if_neg (Ne.symm hm)]; exact hc m hm
    rw [hFC, aeval_C] at hF
    have h0 : AddMonoidAlgebra.coeff F 0 = 0 := Subtype.ext (by simpa using hF)
    rw [hFC, h0, C_0]
  intro n
  induction n with
  | zero =>
    intro F hs hF
    apply hconst F _ hF
    intro m hm
    by_contra hc
    have := (hs m (mem_support_iff.mpr hc)).2
    apply hm
    ext i
    have := (Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp this)) i (Finset.mem_univ _)
    simpa using this
  | succ n ih =>
    intro F hs hF
    have hpd : ∀ i, pderiv i F = 0 := by
      intro i
      apply ih
      · intro m hm
        rw [mem_support_iff, coeff_pderiv] at hm
        have hm' := hs _ (mem_support_iff.mpr (left_ne_zero_of_mul hm))
        refine ⟨fun j => lt_of_le_of_lt ?_ (hm'.1 j), ?_⟩
        · simp
        · have h2 := hm'.2
          simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib] at h2
          have h3 : ∑ j, (Finsupp.single i 1 : Fin d →₀ ℕ) j = 1 := by
            simp [Finsupp.single_apply]
          omega
      · rw [← truncMono_deriv_aeval x E hE B hB, hF, map_zero]
    apply hconst F _ hF
    intro m hm
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hm (Finsupp.ext h)
    by_contra hc
    have hlt := (hs m (mem_support_iff.mpr hc)).1 i
    have hcoef := coeff_pderiv (i := i) F (m - Finsupp.single i 1)
    rw [Finsupp.sub_add_single_one_cancel hi, hpd i] at hcoef
    simp at hcoef
    have hmi : (m - Finsupp.single i 1 : Fin d →₀ ℕ) i + 1 = m i := by
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]; omega
    have hunit : IsUnit (((m - Finsupp.single i 1 : Fin d →₀ ℕ) i : B) + 1) := by
      have e : (((m - Finsupp.single i 1 : Fin d →₀ ℕ) i : B) + 1) = algebraMap k B ((m i : ℕ) : k) := by
        rw [map_natCast, ← hmi]; push_cast; rfl
      rw [e]
      apply IsUnit.map
      apply Ne.isUnit
      rw [Ne, CharP.cast_eq_zero_iff k p]
      intro hdvd
      exact hi (Nat.eq_zero_of_dvd_of_lt hdvd hlt)
    have hcoef' : F.coeff m * (((m - Finsupp.single i 1 : Fin d →₀ ℕ) i : B) + 1) = 0 := by
      have hmi' : m i - 1 = (m - Finsupp.single i 1 : Fin d →₀ ℕ) i := by
        omega
      simpa only [← hmi'] using hcoef.symm
    exact hc ((hunit.mul_left_eq_zero).mp hcoef')

end GlobalTheory

namespace GlobalTheory
open MvPolynomial

theorem truncMono_linearIndependent : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] (d : ℕ) (x : Fin d → A) (E : Fin d → Derivation k A A), (∀ i j, E i (x j) = if i = j then 1 else 0) → ∀ B : Subalgebra k A, (∀ i, ∀ b ∈ B, E i b = 0) → LinearIndependent B (fun a : Fin d → Fin p => ∏ i, x i ^ (a i : ℕ)) := by
  intro p _ k A _ _ _ _ d x E hE B hB
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let toF : (Fin d → Fin p) → (Fin d →₀ ℕ) := fun a => Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))
  have hinj : Function.Injective toF := by
    intro a b hab
    funext i
    apply Fin.ext
    have := congrArg (fun f : Fin d →₀ ℕ => f i) hab
    simpa [toF] using this
  let F : MvPolynomial (Fin d) B := ∑ a, monomial (toF a) (g a)
  have hcoeff : ∀ m, AddMonoidAlgebra.coeff F m = ∑ a, if toF a = m then g a else 0 := by
    intro m
    simp only [F, coeff_sum, coeff_monomial]
  have hF : aeval x F = 0 := by
    rw [← hg]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [F, map_sum, aeval_monomial]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Subalgebra.smul_def]
    rfl
  have hF0 : F = 0 := by
    refine truncMono_eq_zero x E hE B hB (∑ _i : Fin d, p) F ?_ hF
    intro m hm
    rw [mem_support_iff, hcoeff] at hm
    obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    have hm' : toF a = m := by
      by_contra h
      exact ha (if_neg h)
    subst hm'
    refine ⟨fun i => by simp [toF], ?_⟩
    apply Finset.sum_le_sum
    intro i _
    simp [toF, (a i).isLt.le]
  intro a
  have := hcoeff (toF a)
  rw [hF0] at this
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
  simp_rw [hinj.eq_iff] at this
  have hsum : (∑ b : Fin d → Fin p, if b = a then g b else 0) = g a := by
    simp
  rw [hsum] at this
  simpa using this.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedMonomialsLinearIndependentOverConstantsStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncatedMonomials_linearIndependent_over_constants : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] (d : ℕ) (x : Fin d → A) (E : Fin d → Derivation k A A), (∀ i j, E i (x j) = if i = j then 1 else 0) → ∀ B : Subalgebra k A, (∀ i, ∀ b ∈ B, E i b = 0) → LinearIndependent B (fun a : Fin d → Fin p => ∏ i, x i ^ (a i : ℕ)) := by
  first | exact @GlobalTheory.truncMono_linearIndependent | exact GlobalTheory.truncMono_linearIndependent | (intros; apply GlobalTheory.truncMono_linearIndependent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationsDualToFamilyOfNilpotentAug
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationsDualToFamilyOfNilpotentAug
open scoped TensorProduct

theorem GlobalTheory.derivation_normalise_family : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k), IsNilpotent (RingHom.ker ε) → ∀ (d : ℕ) (x : Fin d → A) (D : Fin d → Derivation k A A), (∀ i j, ε (D i (x j)) = if i = j then 1 else 0) → ∃ E : Fin d → Derivation k A A, ∀ i j, E i (x j) = if i = j then 1 else 0 := by
  intro k A _ _ _ ε hnil d x D hD
  let M : Matrix (Fin d) (Fin d) A := Matrix.of fun i j => D i (x j)
  have hε : (ε : A →+* k).mapMatrix M = 1 := by
    ext i j
    simp [M, hD, Matrix.one_apply]
  have hdet : ε M.det = 1 := by
    have h := RingHom.map_det (ε : A →+* k) M
    rw [hε, Matrix.det_one] at h
    simpa using h
  have hunit : IsUnit M.det := by
    obtain ⟨n, hn⟩ := hnil
    have hmem : M.det - 1 ∈ RingHom.ker ε := by simp [RingHom.mem_ker, hdet]
    have hN : IsNilpotent (M.det - 1) := ⟨n, by
      have h : (M.det - 1) ^ n ∈ (RingHom.ker ε) ^ n := Ideal.pow_mem_pow hmem n
      rw [hn] at h
      simpa using h⟩
    have h := hN.isUnit_one_add
    simpa using h
  refine ⟨fun i => ∑ l, (M⁻¹ i l) • D l, fun i j => ?_⟩
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hunit
  have h := congrFun (congrFun hinv i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [← h]
  have hev := map_sum (AddMonoidHom.mk' (fun δ : Derivation k A A => δ (x j)) (fun a b => rfl))
    (fun l => M⁻¹ i l • D l) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hev
  rw [hev]
  simp [M]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationsDualToFamilyOfNilpotentAugStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivations_dual_to_family_of_nilpotent_aug : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k), IsNilpotent (RingHom.ker ε) → ∀ (d : ℕ) (x : Fin d → A) (D : Fin d → Derivation k A A), (∀ i j, ε (D i (x j)) = if i = j then 1 else 0) → ∃ E : Fin d → Derivation k A A, ∀ i j, E i (x j) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.derivation_normalise_family | exact GlobalTheory.derivation_normalise_family | (intros; apply GlobalTheory.derivation_normalise_family <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarePresentationOfCounitalComul
open scoped TensorProduct

namespace GlobalTheory

theorem square_presentation_counital_comul_of_finrank (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (n : ℕ) :
    ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k)
      (Δ : A →ₐ[k] A ⊗[k] A), Module.finrank k A = n →
      ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧
        (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) →
      IsNilpotent (RingHom.ker ε) →
      (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k),
        Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ _ ε Δ hn hΔ hε
  obtain ⟨d, x, l, hl, hlx, hadj⟩ := GlobalTheory.T.exists_generators_dual_point_derivations_augmented k A ε hε
  choose D hD using fun i => GlobalTheory.T.exists_invariant_derivation_of_counital_comul k A ε Δ hΔ (l i) (hl i)
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_derivations_dual_to_family_of_nilpotent_aug k A ε hε d x D (fun i j => by rw [hD, hlx])
  have hnt : Nontrivial A := ε.toRingHom.domain_nontrivial
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨0, MvPolynomial.aeval x, fun _ => 0, ?_, ?_⟩
    · rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, hadj]
    · rw [Set.range_eq_empty, Ideal.span_empty, ← RingHom.injective_iff_ker_eq_bot]
      intro f g h
      rw [MvPolynomial.eq_C_of_isEmpty f, MvPolynomial.eq_C_of_isEmpty g] at h ⊢
      simp only [MvPolynomial.aeval_C] at h
      rw [(algebraMap k A).injective h]
  · obtain ⟨B, hB, Δ', hΔ'⟩ := GlobalTheory.T.frobeniusSubalgebra_counital_comul p k A ε Δ hΔ
    have hp : (p : A) = 0 := by
      rw [← map_natCast (algebraMap k A), CharP.cast_eq_zero, map_zero]
    have hEB : ∀ i, ∀ b ∈ B, E i b = 0 := by
      intro i b hb
      obtain ⟨c, rfl⟩ := (hB b).1 hb
      rw [Derivation.leibniz_pow, nsmul_eq_mul, hp, zero_mul]
    have hBtop : B ≠ ⊤ := by
      intro h
      have h1 := hE ⟨0, hd⟩ ⟨0, hd⟩
      rw [hEB _ _ (h ▸ Algebra.mem_top), if_pos rfl] at h1
      exact zero_ne_one h1
    have hlt : Module.finrank k B < n := by
      rw [← hn]
      have : (Subalgebra.toSubmodule B) ≠ ⊤ := by
        intro h
        apply hBtop
        rw [← Algebra.toSubmodule_eq_top]
        exact h
      exact Submodule.finrank_lt this
    have hfin : Module.Finite k B :=
      Module.Finite.of_injective B.val.toLinearMap Subtype.val_injective
    have hε' : IsNilpotent (RingHom.ker (ε.comp B.val)) := by
      obtain ⟨m, hm⟩ := hε
      refine ⟨m, ?_⟩
      have h1 : (RingHom.ker (ε.comp B.val)) = Ideal.comap B.val (RingHom.ker ε) := by
        ext b; simp [RingHom.mem_ker, Ideal.mem_comap]
      rw [h1, Ideal.zero_eq_bot, eq_bot_iff]
      refine (Ideal.le_comap_pow _ m).trans ?_
      rw [hm, Ideal.zero_eq_bot]
      intro b hb
      rw [Ideal.mem_comap, Ideal.mem_bot] at hb
      rw [Ideal.mem_bot]
      exact Subtype.ext hb
    refine GlobalTheory.T.exists_square_presentation_of_tower k B A (ih _ hlt B (ε.comp B.val) Δ' rfl hΔ' hε') ?_
    refine ⟨d, MvPolynomial.aeval x, _, ?_,
      GlobalTheory.T.ker_aeval_truncatedPolynomial_presentation p (Fact.out : p.Prime).pos B A d x
        (fun i => ⟨x i ^ p, (hB _).2 ⟨x i, rfl⟩⟩) (fun i => rfl)
        (GlobalTheory.T.truncatedMonomials_linearIndependent_over_constants p k A d x E hE B hEB)⟩
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, eq_top_iff]
    intro a _
    have ha : a ∈ Algebra.adjoin k (Set.range x) := hadj ▸ Algebra.mem_top
    have hle : Algebra.adjoin k (Set.range x) ≤
        (Algebra.adjoin B (Set.range x)).restrictScalars k :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact hle ha

theorem square_presentation_of_counital_comul : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] [PerfectRing k p] [Module.Finite k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → IsNilpotent (RingHom.ker ε) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  intro p _ k A _ _ _ _ _ _ ε Δ h hε
  exact square_presentation_counital_comul_of_finrank p k _ A ε Δ rfl h hε

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarePresentationOfCounitalComulStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_presentation_of_counit_isNilpotent_ker : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] [PerfectRing k p] [Module.Finite k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → IsNilpotent (RingHom.ker ε) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  first | exact @GlobalTheory.square_presentation_of_counital_comul | exact GlobalTheory.square_presentation_of_counital_comul | (intros; apply GlobalTheory.square_presentation_of_counital_comul <;> assumption)
end
