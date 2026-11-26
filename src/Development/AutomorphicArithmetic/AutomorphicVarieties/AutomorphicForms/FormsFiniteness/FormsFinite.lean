module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalOfBddCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermSpaceCentreOfBdd
public import Development.AutomorphicArithmetic.DivisorFrames.AlgebraicModSubmoduleQdetBlockOfGlRel

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermSpaceTypesOfBdd
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTermSpace_types_of_bdd :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (S : Submodule ℂ (archSmooth K n)), Bdd S → Types (ctSp r S) := by
  intro K _ _ n r S hS
  obtain ⟨V, hV, hst, hmem⟩ := hS.types
  refine ⟨V, hV, hst, fun ψ hψ g => ?_⟩
  unfold ctSp at hψ
  induction hψ using Submodule.span_induction with
  | mem ψ h =>
    obtain ⟨φ, hφ, he⟩ := h
    have hc : Continuous φ.1 := (UpperTheory.isAutomorphicForm_of_bdd_submodule K n S hS φ hφ).continuous
    rw [he]
    refine @UpperTheory.locallyFinite_of_algMod_criterion _ (archCompact K n) (_) _ V hV
      (fun X k => φ.1 (unipGL X * (g * infEmb K n k.1))) (fun X => ?_)
      (fun k => integrableOn_constantTerm hc _)
    simpa only [mul_assoc] using hmem φ hφ (unipGL X * g)
  | zero => exact V.zero_mem
  | add x y _ _ hx hy => exact V.add_mem hx hy
  | smul c x _ hx => exact V.smul_mem c hx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgebraicModuleOfVanishingBlock
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModQuantumDetLeviBlocksOfParabolic
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

namespace UpperTheory.V.QuantumDetLeviBlocks

private theorem map_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {n : ℕ}
    (φ : A →ₐ[ℂ] B) (E : Fin n → Fin n → A) (u : ℂ) :
    φ (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => φ (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 3
  funext k
  simp only [Function.comp_apply, Formalism.REAL.Tm]
  split_ifs <;> simp

private def pw (ι V : Type) [AddCommGroup V] [Module ℂ V] :
    Module.End ℂ V →ₐ[ℂ] Module.End ℂ (ι → V) where
  toFun f := LinearMap.compLeft f ι
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private theorem algMod_of_ne_zero {M : Type} [AddCommGroup M] [Module ℂ M] (S N : Submodule ℂ M)
    (T : Module.End ℂ M) (P : Polynomial ℂ) (hP : P ≠ 0)
    (h : ∀ x ∈ S, Polynomial.aeval T P x ∈ N) : AlgMod S N T := by
  refine ⟨P * Polynomial.C (P.leadingCoeff)⁻¹, Polynomial.monic_mul_leadingCoeff_inv hP, fun x hx => ?_⟩
  rw [mul_comm, map_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply]
  exact N.smul_mem _ (h x hx)

end UpperTheory.V.QuantumDetLeviBlocks

open UpperTheory.V.QuantumDetLeviBlocks in
theorem UpperTheory.algMod_quantumDet_leviBlocks_of_parabolic :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (r s : ℕ) (X : Fin (r + s) → Fin (r + s) → Module.End ℂ M), Formalism.REAL.GlRel X → ∀ W Z S : Submodule ℂ M, S ≤ W → (∀ p q, ∀ x ∈ W, X p q x ∈ W) → (∀ (p : Fin r) (q : Fin s), ∀ x ∈ W, X (Fin.castAdd s p) (Fin.natAdd r q) x ∈ Z) → (∀ u, AlgMod S ⊥ (Formalism.REAL.qdet X u)) → ∀ u, AlgMod S Z (Formalism.REAL.qdet (fun p q : Fin r => X (Fin.castAdd s p) (Fin.castAdd s q)) u) ∧ AlgMod S Z (Formalism.REAL.qdet (fun p q : Fin s => X (Fin.natAdd r p) (Fin.natAdd r q)) u) := by
  intro M _ _ r s U hU W Z S hs hW hZ hc u
  let φ := pw S M
  let X : Fin (r + s) → Fin (r + s) → Module.End ℂ (S → M) := fun p q => φ (U p q)
  have hX : Formalism.REAL.GlRel X := by
    intro a b c d
    have := congrArg φ (hU a b c d)
    split_ifs at this ⊢ <;> simpa [X] using this
  let W' : Submodule ℂ (S → M) := Submodule.pi Set.univ fun _ => W
  let N' : Submodule ℂ (S → M) := ⊥ ⊔ Submodule.span ℂ {y | ∃ (p : Fin r) (q : Fin s), ∃ x ∈ W',
    y = X (Fin.castAdd s p) (Fin.natAdd r q) x}
  have hle : N' ≤ Submodule.pi Set.univ fun _ => Z := by
    refine sup_le bot_le (Submodule.span_le.2 ?_)
    rintro _ ⟨p, q, x, hx, rfl⟩ i hi
    exact hZ p q _ (hx i hi)
  obtain ⟨-, h1, h2⟩ := UpperTheory.algebraicModSubmodule_qdet_block_of_glRel (S → M) r s X hX W' ⊥ N'
    (fun p q x hx i hi => hW p q _ (hx i hi))
    (fun p q x hx => by rw [(Submodule.mem_bot ℂ).1 hx, map_zero]; exact Submodule.zero_mem _)
    rfl (fun i => i.1) (fun i _ => hs i.2) (fun u => by
      obtain ⟨P, hP, h⟩ := hc u
      refine ⟨P, hP.ne_zero, (Submodule.mem_bot ℂ).2 ?_⟩
      funext i
      rw [← map_qdet φ U u, Polynomial.aeval_algHom_apply]
      exact (Submodule.mem_bot ℂ).1 (h i.1 i.2))
  constructor
  · obtain ⟨P, hP, h⟩ := h1 u
    refine algMod_of_ne_zero _ _ _ P hP fun v hv => ?_
    have h3 := hle h ⟨v, hv⟩ trivial
    simp only [X] at h3
    rw [← map_qdet φ (fun p q : Fin r => U (Fin.castAdd s p) (Fin.castAdd s q)) u,
      Polynomial.aeval_algHom_apply] at h3
    exact h3
  · obtain ⟨P, hP, h⟩ := h2 u
    refine algMod_of_ne_zero _ _ _ P hP fun v hv => ?_
    have h3 := hle h ⟨v, hv⟩ trivial
    simp only [X] at h3
    rw [← map_qdet φ (fun p q : Fin s => U (Fin.natAdd r p) (Fin.natAdd r q)) u,
      Polynomial.aeval_algHom_apply] at h3
    exact h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ArchExpSingleUnipotentEmbedding
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

open GroundTheory.Automorphic.CuspidalSpectrum in
private theorem archExp_single (K : Type) [Field K] [NumberField K] (r s : ℕ) (i : Fin r) (j : Fin s)
    (x : mixedSpace K) :
    ∃ P : UPos (r + s) r → AdeleRing (𝓞 K) K,
      archExp (K := K) (n := r + s) (Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) x) = unipGL P := by
  classical
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let P : UPos (r + s) r → AdeleRing (𝓞 K) K := fun p =>
    if p.1 = (Fin.castAdd s i, Fin.natAdd r j) then ((e.symm x, 0) : AdeleRing (𝓞 K) K) else 0
  refine ⟨P, ?_⟩
  have h0 : ∀ p, (P p).2 = 0 := by
    intro p
    by_cases hp : p.1 = (Fin.castAdd s i, Fin.natAdd r j)
    · simp [P, hp]
    · simp only [P, hp, if_false]
      rfl
  have hc := conj_unipGL_eq_archExp (1 : AdelicGLn.AdelicGL K (r + s)) P h0
  simp only [inv_one, one_mul, mul_one] at hc
  rw [hc]
  congr 1
  refine Matrix.ext fun a b => ?_
  simp [conjArch, archMat, archMatrixEquiv, Matrix.single_apply]
  show _ = e ((blockEntry P a b).1)
  rw [blockEntry_apply]
  by_cases hab : Fin.castAdd s i = a ∧ Fin.natAdd r j = b
  · obtain ⟨rfl, rfl⟩ := hab
    have hh : ((Fin.castAdd s i : Fin (r + s)) : ℕ) < r ∧ r ≤ ((Fin.natAdd r j : Fin (r + s)) : ℕ) :=
      ⟨by simp, by simp⟩
    rw [dite_eq_left hh, if_pos ⟨rfl, rfl⟩]
    simp only [P, if_pos rfl, Prod.fst]
    exact (e.apply_symm_apply x).symm
  · rw [if_neg hab]
    split_ifs with hh
    · have hne : ¬ ((a, b) : Fin (r + s) × Fin (r + s)) = (Fin.castAdd s i, Fin.natAdd r j) := by
        intro heq
        apply hab
        simp only [Prod.mk.injEq] at heq
        exact ⟨heq.1.symm, heq.2.symm⟩
      simp only [P, hne, if_false]
      exact (map_zero e).symm
    · exact (map_zero e).symm

open GroundTheory.Automorphic.CuspidalSpectrum in
theorem UpperTheory.archExp_single_unipotent_embedding :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (i : Fin r) (j : Fin s) (x : mixedSpace K), ∀ ψ ∈ NInv K (r + s) r, lam K (r + s) (Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) x) ψ ∈ Van K r s := by
  intro K _ _ r s i j x ψ hψ
  classical
  have hψ' : ∀ (X : UPos (r + s) r → AdeleRing (𝓞 K) K) (g : AdelicGLn.AdelicGL K (r + s)),
      ψ.1 (unipGL X * g) = ψ.1 g := hψ
  show ∀ (m₁ : GL (Fin r) (AdeleRing (𝓞 K) K)) (m₂ : GL (Fin s) (AdeleRing (𝓞 K) K)),
    (lam K (r + s) (Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) x) ψ).1 (blk m₁ m₂) = 0
  intro m₁ m₂
  let Y : ArchMatrix K (r + s) := Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) x
  let g : AdelicGLn.AdelicGL K (r + s) := blk m₁ m₂
  have hd := CuspidalSpectrum.hasDerivAt_archExp ψ g Y 0
  simp only [zero_smul, CuspidalSpectrum.archExp_zero, mul_one] at hd
  obtain ⟨c, hc⟩ := UpperTheory.blockDiag_conj_unipotent_linear (AdeleRing (𝓞 K) K) r s m₁ m₂
  have hmap : Matrix.GeneralLinearGroup.map (RingHom.id (AdeleRing (𝓞 K) K)) (blk m₁ m₂) = blk m₁ m₂ := by
    ext
    rfl
  have hconst : (fun t : ℝ => ψ.1 (g * CuspidalSpectrum.archExp (t • Y))) = fun _ => ψ.1 g := by
    funext t
    have hsY : t • Y = Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) (t • x) :=
      Matrix.smul_single _ _ _ _
    obtain ⟨P, hP⟩ := archExp_single K r s i j (t • x)
    rw [hsY, hP]
    have h1 := hc (AdeleRing (𝓞 K) K) (RingHom.id _) P
    rw [hmap] at h1
    show ψ.1 (blk m₁ m₂ * unipGL P) = ψ.1 (blk m₁ m₂)
    rw [h1, hψ']
  rw [hconst] at hd
  have h2 := hd.unique (hasDerivAt_const (0 : ℝ) (ψ.1 g))
  exact h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UActionMemUnipotentInvariant
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.uAction_mem_unipotentInvariant :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (u : UEnv K n), ∀ ψ ∈ NInv K n r, uAction u ψ ∈ NInv K n r := by
  intro K _ _ n r u ψ hψ X g
  have h : ∀ y, ψ.1 (unipGL X * y) = ψ.1 y := hψ X
  have e : sliceL (unipGL X * g) ψ = sliceL g ψ :=
    Subtype.ext (funext fun x => by simp only [coe_sliceL, archSlice_apply, mul_assoc, h])
  simp only [coe_uAction, uActFun, e]
end

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private def carry {M : Type} [AddCommGroup M] [Module ℂ M] (W Z : Submodule ℂ M) : Submodule ℂ (Module.End ℂ M) where
  carrier := {T | ∀ x ∈ W, T x ∈ Z}
  add_mem' h1 h2 x hx := Z.add_mem (h1 x hx) (h2 x hx)
  zero_mem' _ _ := Z.zero_mem
  smul_mem' c _ h x hx := Z.smul_mem c (h x hx)

theorem UpperTheory.algebraic_module_of_vanishing_block :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (S : Submodule ℂ (archSmooth K (r + s))), S ≤ NInv K (r + s) r → Centre S → ∀ (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι) (τ : ι) (u : ℂ), AlgMod S (Van K r s) (archCapBlock D (e1 r s) τ u) ∧ AlgMod S (Van K r s) (archCapBlock D (e2 r s) τ u) := by
  intro K _ _ r s S hS hC ι _ D τ u
  have hrel : Formalism.REAL.GlRel (gen D (lam K (r + s)) τ) :=
    (UpperTheory.gen_glRelations_and_commute_of_isLie _ ι (r + s) _ D (lam K (r + s)) (isLie_lam K (r + s))).1 τ
  have hW : ∀ p q, ∀ x ∈ NInv K (r + s) r, gen D (lam K (r + s)) τ p q x ∈ NInv K (r + s) r := fun p q =>
    gen_mem D (lam K (r + s)) τ p q (carry (NInv K (r + s) r) (NInv K (r + s) r))
      fun y x hx => UpperTheory.uAction_mem_unipotentInvariant K (r + s) r _ x hx
  have hZ : ∀ (p : Fin r) (q : Fin s), ∀ x ∈ NInv K (r + s) r,
      gen D (lam K (r + s)) τ (Fin.castAdd s p) (Fin.natAdd r q) x ∈ Van K r s := fun p q =>
    gen_mem D (lam K (r + s)) τ _ _ (carry (NInv K (r + s) r) (Van K r s))
      fun y x hx => UpperTheory.archExp_single_unipotent_embedding K r s p q y x hx
  have hq : ∀ v, AlgMod S ⊥ (Formalism.REAL.qdet (gen D (lam K (r + s)) τ) v) := fun v => by
    refine UpperTheory.algMod_bot_of_mem_adjoin_commuting _ S (uAction '' ((isExpLieAlgebra K (r + s)).centerU : Set (UEnv K (r + s)))) ?_ ?_ _
      (UpperTheory.qdet_generates_universalEnveloping_centre K (r + s) ι D τ v)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact Zc_comm (uAction_mem_Zc hx) (uAction_mem_Zc hy)
    · rintro _ ⟨z, hz, rfl⟩
      exact hC z hz
  exact UpperTheory.algMod_quantumDet_leviBlocks_of_parabolic _ r s (gen D (lam K (r + s)) τ) hrel (NInv K (r + s) r) (Van K r s) S hS hW hZ hq u
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SiegelLeviBlockAevalStable
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalInter
theorem UpperTheory.Reformulated.B.Qe22.aeval_inter :
    ∀ {M N : Type} [inst : AddCommGroup M] [inst_1 : _root_.Module ℂ M]
    [inst_2 : AddCommGroup N] [inst_3 : _root_.Module ℂ N] (f : M →ₗ[ℂ] N) (T : Module.End ℂ M) (T' : Module.End ℂ N),
    (∀ (x : M), (f : M → N) ((T : M → M) x) = (T' : N → N) ((f : M → N) x)) →
      ∀ (p : Polynomial ℂ) (x : M),
        (f : M → N) (((Polynomial.aeval T : Polynomial ℂ → Module.End ℂ M) p : M → M) x) =
          ((Polynomial.aeval T' : Polynomial ℂ → Module.End ℂ N) p : N → N) ((f : M → N) x) := by
  intro M N _ _ _ _ f T T' h p
  have hpow : ∀ (n : ℕ) (x : M), f ((T ^ n) x) = (T' ^ n) (f x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro x
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), hp, hq]
  | monomial n a =>
    intro x
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def,
      ← Algebra.smul_def, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, hpow]
end

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem aeval_inter {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (f : M →ₗ[ℂ] N) (T : Module.End ℂ M) (T' : Module.End ℂ N) (h : ∀ x, f (T x) = T' (f x))
    (p : Polynomial ℂ) (x : M) : f (Polynomial.aeval T p x) = Polynomial.aeval T' p (f x) :=
  _root_.UpperTheory.Reformulated.B.Qe22.aeval_inter f T T' h p x

theorem UpperTheory.siegelLevi_block_aeval_stable :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n)) (S Z : Submodule ℂ (archSmooth K n)) (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι), (∀ ψ ∈ Z, ∀ g ∈ Γ, ∀ m, ψ.1 (g * emb e m) = 0) → (∀ τ u, AlgMod S Z (archCapBlock D e τ u)) → Centre (slSp e Γ S) := by
  intro K _ _ a n e Γ S Z ι _ D hZ hS z hz
  refine UpperTheory.algMod_bot_of_mem_adjoin_commuting _ _ {x | ∃ τ u, x = capOp D a τ u} ?_ ?_ _ (UpperTheory.centerU_action_mem_adjoin_capOp K a ι D z hz)
  · rintro _ ⟨τ, u, rfl⟩ _ ⟨σ, v, rfl⟩
    exact Zc_comm (UpperTheory.qdet_generates_universalEnveloping_centre K a ι D τ u) (UpperTheory.qdet_generates_universalEnveloping_centre K a ι D σ v)
  · rintro _ ⟨τ, u, rfl⟩
    obtain ⟨p, hp, hpS⟩ := hS τ u
    refine ⟨p, hp, fun x hx => ?_⟩
    have hle : slSp e Γ S ≤ LinearMap.ker (Polynomial.aeval (capOp D a τ u) p) := by
      refine Submodule.span_le.2 ?_
      rintro φ ⟨ψ, hψ, g, hg, hφ⟩
      obtain ⟨f, hf, hl⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K a n e g
      have hfφ : φ = f ψ := Subtype.ext (funext fun m => (hφ m).trans (hf ψ m).symm)
      have hgen : ∀ i j y, f (gen D (lam K n) τ (e i) (e j) y) = gen D (lam K a) τ i j (f y) := fun i j y =>
        gen_inter D (lam K n) (lam K a) τ (e i) (e j) i j (f ∘ₗ LinearMap.applyₗ y) (LinearMap.applyₗ (f y))
          fun t => by
            change f (lam K n (Matrix.single (e i) (e j) t) y) = lam K a (Matrix.single i j t) (f y)
            rw [← matrixExtendByZero_single, hl]
      have hq : ∀ y, f (archCapBlock D e τ u y) = capOp D a τ u (f y) :=
        UpperTheory.algMod_of_injective_intertwining _ _ a f _ _ hgen u
      change Polynomial.aeval (capOp D a τ u) p φ = 0
      rw [hfφ, ← aeval_inter f _ _ hq]
      exact Subtype.ext (funext fun m => (hf _ m).trans (hZ _ (hpS ψ hψ) g hg m))
    exact hle hx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAutomorphicSaturationSubmodule
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CenterUActionCommuteRightTranslation
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CapOpCommuteRightTranslation
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem semiconj_gen {R : Type} [CommRing R] [Algebra ℝ R] {ι : Type} [Fintype ι] {n : ℕ}
    {A : Type} [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (D : Idem R ι)
    (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A) (T : A) (P Q : Matrix (Fin n) (Fin n) R)
    (h : ∀ X, T * l X = l (P * X * Q) * T) (τ : ι) (i j : Fin n) :
    T * gen D l τ i j = (∑ k, ∑ m, (D.ch τ (P k i) * D.ch τ (Q j m)) • gen D l τ k m) * T := by
  have ent : ∀ (k m : Fin n) (r : R), (P * Matrix.single i j r * Q) k m = P k i * Q j m * r := by
    intro k m r
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]
    ring
  have key : ∀ x : ℂ ⊗[ℝ] R, T * unitMap l i j x =
      (∑ k, ∑ m, unitMap l k m ((1 ⊗ₜ[ℝ] (P k i * Q j m)) * x)) * T := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c r =>
      rw [unitMap_tmul, mul_smul_comm, h, Matrix.matrix_eq_sum_single (P * Matrix.single i j r * Q)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, Finset.sum_mul, Finset.smul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        unitMap_tmul, ent, smul_mul_assoc]
    | add x y hx hy =>
      simp only [map_add (f := _), mul_add, hx, hy, Finset.sum_add_distrib, add_mul]
  show T * unitMap l i j (D.e τ) = _
  rw [key]
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
  rw [D.mul_e, map_smul, map_mul]
  rfl

private theorem rtInf_lam {K : Type} [Field K] [NumberField K] {n : ℕ} (a : archGroup K n)
    (y : GL (Fin n) (mixedSpace K)) (hy : y = a.1) (X : Matrix (Fin n) (Fin n) (mixedSpace K)) :
    rtInf a * lam K n X = lam K n (y.val * X * (y⁻¹).val) * rtInf a := by
  subst hy
  apply LinearMap.ext
  intro φ
  simp only [Module.End.mul_apply, lam_apply]
  rw [uAction_rtInf, IsExpLieAlgebra.AdU_ι]
  congr 4
  apply Subtype.ext
  simp [IsExpLieAlgebra.AdLie, IsExpLieAlgebra.Ad, toLie, IsExpLieAlgebra.toLie, IsExpLieAlgebra.ofLie,
    mul_assoc]
  show (show ArchMatrix K n from X) = ((↑(↑a : (ArchMatrix K n)ˣ)⁻¹ : ArchMatrix K n)) *
    ((((↑a : (ArchMatrix K n)ˣ) : ArchMatrix K n) * ((show ArchMatrix K n from X) *
      ((↑(↑a : (ArchMatrix K n)ˣ)⁻¹ : ArchMatrix K n)))) * ((↑a : (ArchMatrix K n)ˣ) : ArchMatrix K n))
  simp only [mul_assoc, Units.inv_mul_cancel_left]
  exact (Units.inv_mul_cancel_right (show ArchMatrix K n from X) (a : (ArchMatrix K n)ˣ)).symm

theorem UpperTheory.capOp_commute_rightTranslation :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι) (τ : ι) (u : ℂ) (a : archGroup K n), Commute (capOp D n τ u) (rtInf a) := by
  intro K _ _ n ι _ D τ u a
  let y : GL (Fin n) (mixedSpace K) := a.1
  let P : Matrix (Fin n) (Fin n) ℂ := (D.ch τ).mapMatrix y.val
  let Q : Matrix (Fin n) (Fin n) ℂ := (D.ch τ).mapMatrix (y⁻¹).val
  have hQP : Q * P = 1 := by
    simp only [Q, P]
    rw [← map_mul, Units.inv_mul, map_one]
  have hsemi := semiconj_gen D (lam K n) (rtInf a) y.val (y⁻¹).val
    (fun X => rtInf_lam a y rfl X) τ
  have hq := GlobalTheory.CapAdInv.qdet_semiconj (gen D (lam K n) τ) _ (rtInf a) hsemi u
  have hGl := (UpperTheory.gen_glRelations_and_commute_of_isLie (mixedSpace K) ι n _ D (lam K n) (isLie_lam K n)).1 τ
  have had := GlobalTheory.CapAdInv.qdet_ad (gen D (lam K n) τ) hGl P Q hQP u
  show Formalism.REAL.qdet (gen D (lam K n) τ) u * rtInf a = rtInf a * Formalism.REAL.qdet (gen D (lam K n) τ) u
  rw [hq]
  congr 1
  exact had.symm
end

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.centerU_action_commute_rightTranslation :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∀ z ∈ (isExpLieAlgebra K n).centerU, ∀ g, Commute (uAction z) (rt (K := K) (n := n) g) := by
  intro K _ _ n z hz g
  obtain ⟨ι, hι, ⟨D⟩⟩ := UpperTheory.exists_idempotent_decomposition_mixedSpace K
  have hinf : Commute (uAction z) (rtInf (archPart g)) := by
    have hsub : Algebra.adjoin ℂ {x | ∃ τ u, x = capOp D n τ u} ≤
        Subalgebra.centralizer ℂ {rtInf (archPart g)} := by
      rw [Algebra.adjoin_le_iff]
      rintro x ⟨τ, u, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro y rfl
      exact (UpperTheory.capOp_commute_rightTranslation K n ι D τ u (archPart g)).eq.symm
    have hm := hsub (UpperTheory.centerU_action_mem_adjoin_capOp K n ι D z hz)
    rw [Subalgebra.mem_centralizer_iff] at hm
    exact (hm _ rfl).symm
  have hfin : Commute (uAction z) (rtFin (finPart g)) := by
    refine LinearMap.ext fun φ => ?_
    exact uAction_rtFin z (finPart g) φ
  exact hinf.mul_right hfin
end

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem grp1 {G : Type*} [Group G] (g a b u : G) (h : a * u = u * a) :
    g * u * (a * b) = g * (a * b) * (b⁻¹ * u * b) := by
  rw [mul_assoc g u, ← mul_assoc u, ← h]
  group

private theorem grp2 {G : Type*} [Group G] (g a b u : G) (h : u * a * b = b * (u * a)) :
    g * u * (a * b) = g * b * (u * a) := by
  rw [mul_assoc g b, ← h]
  group

section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem id1 (g k : AdelicGLn.AdelicGL K n) (u : AdelicGLn.FiniteAdelicGL K n) :
    g * finEmb K n u * k = g * k * finEmb K n ((finPart k)⁻¹ * u * finPart k) := by
  have h := grp1 g _ (finEmb K n (finPart k)) _ (infEmb_mul_finEmb_comm (archPart k) u)
  rw [infEmb_archPart_mul_finEmb_finPart] at h
  rw [map_mul, map_mul, map_inv]
  exact h

private theorem id2 (g k : AdelicGLn.AdelicGL K n) (u : archGroup K n) :
    g * infEmb K n u * k = g * finEmb K n (finPart k) * infEmb K n (u * archPart k) := by
  have h0 := infEmb_mul_finEmb_comm (u * archPart k) (finPart k)
  rw [map_mul] at h0
  have h := grp2 g _ _ _ h0
  rw [infEmb_archPart_mul_finEmb_finPart] at h
  rw [map_mul]
  exact h

private theorem hmul (a b : AdelicGLn.AdelicGL K n) (φ : archSmooth K n) : rt a (rt b φ) = rt (a * b) φ :=
  Subtype.ext (funext fun x => by rw [rt_apply, rt_apply, rt_apply, mul_assoc])

private theorem hone (φ : archSmooth K n) : rt (1 : AdelicGLn.AdelicGL K n) φ = φ :=
  Subtype.ext (funext fun x => by rw [rt_apply, mul_one])

private noncomputable def sat (S : Submodule ℂ (archSmooth K n)) : Submodule ℂ (archSmooth K n) :=
  Submodule.span ℂ {ψ | ∃ k ∈ Reduction.maxCompact (K := K) (n := n), ∃ φ ∈ S, ψ = rt k φ}

private theorem ind (S : Submodule ℂ (archSmooth K n)) (P : archSmooth K n → Prop) (h0 : P 0)
    (ha : ∀ x y, P x → P y → P (x + y)) (hs : ∀ (c : ℂ) x, P x → P (c • x))
    (hg : ∀ k ∈ Reduction.maxCompact (K := K) (n := n), ∀ φ ∈ S, P (rt k φ)) : ∀ ψ ∈ sat S, P ψ := by
  intro ψ hψ
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, φ, hφ, rfl⟩ := hx
    exact hg k hk φ hφ
  | zero => exact h0
  | add x y _ _ hx hy => exact ha x y hx hy
  | smul c x _ hx => exact hs c x hx
end

section
variable {K : Type} [Field K] [NumberField K] {n : ℕ} {S : Submodule ℂ (archSmooth K n)}

private theorem sat_left (hS : Bdd S) : ∀ φ ∈ sat S, IsLeftInvariant φ.1 := by
  refine ind S (fun φ => IsLeftInvariant φ.1) isLeftInvariant_zero
      (fun x y hx hy γ g => congrArg₂ (· + ·) (hx γ g) (hy γ g))
      (fun c x hx γ g => congrArg (c • ·) (hx γ g)) ?_
  intro k _ φ hφ γ g
  rw [rt_apply, rt_apply, mul_assoc]
  exact hS.left φ hφ γ _

private theorem sat_growth (hS : Bdd S) : Growth (sat S) := by
  refine ind S (fun φ => HasModerateGrowth φ.1) hasModerateGrowth_zero
      (fun x y hx hy => hx.add hy) (fun c x hx => hx.smul c) ?_
  intro k _ φ hφ
  have h := (hS.growth φ hφ).translate k
  have e : (rt k φ).1 = rightTranslate k φ.1 := funext fun x => rt_apply k φ x
  rw [e]
  exact h

private theorem sat_level (hS : Bdd S) : Level (sat S) := by
  obtain ⟨L, hL, hinv⟩ := hS.level
  obtain ⟨L', hL', hle, hconj, -⟩ := UpperTheory.exists_open_level_normalized_by_integralFiniteGL K n L hL
  refine ⟨L', hL', ?_⟩
  refine ind S (fun φ => ∀ u ∈ L', ∀ g, φ.1 (g * finEmb K n u) = φ.1 g) (fun _ _ _ => rfl)
      (fun x y hx hy u hu g => congrArg₂ (· + ·) (hx u hu g) (hy u hu g))
      (fun c x hx u hu g => congrArg (c • ·) (hx u hu g)) ?_
  intro k hk φ hφ u hu g
  rw [rt_apply, rt_apply, id1]
  exact hinv φ hφ _ (hle (hconj _ (finPart_mem_integralFiniteGL hk) u hu)) (g * k)

private theorem sat_types (hS : Bdd S) : Types (sat S) := by
  obtain ⟨V, hV, hst, hmem⟩ := hS.types
  refine ⟨V, hV, hst, ?_⟩
  refine ind S (fun φ => ∀ g, (fun k : archCompact K n => φ.1 (g * infEmb K n k.1)) ∈ V) (fun _ => V.zero_mem)
      (fun x y hx hy g => V.add_mem (hx g) (hy g))
      (fun c x hx g => V.smul_mem c (hx g)) ?_
  intro k hk φ hφ g
  have h := hst _ (hmem φ hφ (g * finEmb K n (finPart k))) ⟨archPart k, archPart_mem_archCompact hk⟩
  have e : (fun k' : archCompact K n => (rt k φ).1 (g * infEmb K n k'.1)) =
      fun k' : archCompact K n => φ.1 (g * finEmb K n (finPart k) * infEmb K n (k'.1 * archPart k)) :=
    funext fun k' => by rw [rt_apply, id2]
  rw [e]
  exact h

private theorem sat_centre (hS : Bdd S) : Centre (sat S) := by
  intro z hz
  obtain ⟨p, hp, h⟩ := hS.centre z hz
  refine ⟨p, hp, ?_⟩
  refine ind S (fun φ => Polynomial.aeval (uAction z) p φ ∈ (⊥ : Submodule ℂ (archSmooth K n)))
      (by rw [map_zero]; exact Submodule.zero_mem _)
      (fun x y hx hy => by rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy)
      (fun c x hx => by rw [map_smul]; exact Submodule.smul_mem _ c hx) ?_
  intro k _ φ hφ
  have hc : Commute (rt (K := K) (n := n) k) (Polynomial.aeval (uAction z) p) :=
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute (Polynomial.aeval_mem_adjoin_singleton ℂ _)
      (by rintro _ rfl; exact (UpperTheory.centerU_action_commute_rightTranslation K n z hz k).symm)
  have e := LinearMap.congr_fun hc.eq φ
  rw [Module.End.mul_apply, Module.End.mul_apply] at e
  rw [← e, (Submodule.mem_bot ℂ).1 (h φ hφ), map_zero]
  exact Submodule.zero_mem _

private theorem sat_sat : Sat (sat S) := by
  intro k hk
  refine ind S (fun φ => rt k φ ∈ sat S)
      (by rw [map_zero]; exact Submodule.zero_mem _)
      (fun x y hx hy => by rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy)
      (fun c x hx => by rw [map_smul]; exact Submodule.smul_mem _ c hx) ?_
  intro k' hk' φ hφ
  exact Submodule.subset_span ⟨k * k', mul_mem hk hk', φ, hφ, hmul _ _ _⟩
end

theorem UpperTheory.exists_automorphic_saturation_submodule :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Bdd S → ∃ S' : Submodule ℂ (archSmooth K n), S ≤ S' ∧ Bdd S' ∧ Sat S' := by
  intro K _ _ n S hS
  exact ⟨sat S, fun φ hφ => Submodule.subset_span ⟨1, one_mem _, φ, hφ, (hone φ).symm⟩,
    ⟨sat_left hS, sat_growth hS, sat_level hS, sat_types hS, sat_centre hS⟩, sat_sat⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermSpaceAutomorphicProperties
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTermSpace_automorphic_properties :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (S : Submodule ℂ (archSmooth K (r + s))), Bdd S → Sat S → ctSp r S ≤ NInv K (r + s) r ∧ Growth (ctSp r S) ∧ Level (ctSp r S) ∧ Sat (ctSp r S) ∧ ∀ ψ ∈ ctSp r S, ∀ (γ₁ : GL (Fin r) K) (γ₂ : GL (Fin s) K) g, ψ.1 (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * g) = ψ.1 g := by
  intro K _ _ r s S hB hS
  have hrt : ∀ (φ φ' : AdelicGLn.AdelicGL K (r + s) → ℂ) (k : AdelicGLn.AdelicGL K (r + s)),
      (∀ x, φ' x = φ (x * k)) → ∀ g, constantTerm r φ (g * k) = constantTerm r φ' g := by
    intro φ φ' k h g
    unfold constantTerm
    simp only [h, mul_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro ψ ⟨φ, hφ, e⟩ X g
    rw [e]
    exact UpperTheory.constantTerm_unipotent_left_invariant K _ r φ.1 (hB.left φ hφ) X g
  · intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h =>
      obtain ⟨φ, hφ, e⟩ := h
      rw [e]
      exact UpperTheory.hasModerateGrowth_constantTerm K _ r φ.1 (hB.growth φ hφ)
    | zero => exact hasModerateGrowth_zero
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx => exact hx.smul c
  · obtain ⟨L, hL, h⟩ := hB.level
    refine ⟨L, hL, fun ψ hψ u hu g => ?_⟩
    induction hψ using Submodule.span_induction with
    | mem ψ h' =>
      obtain ⟨φ, hφ, e⟩ := h'
      rw [e]
      exact hrt φ.1 φ.1 _ (fun x => (h φ hφ u hu x).symm) g
    | zero => rfl
    | add x y _ _ hx hy => exact congrArg₂ (· + ·) hx hy
    | smul c x _ hx => exact congrArg (c • ·) hx
  · intro k hk ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h' =>
      obtain ⟨φ, hφ, e⟩ := h'
      refine Submodule.subset_span ⟨rt k φ, hS k hk φ hφ, funext fun g => ?_⟩
      rw [rt_apply, e]
      exact hrt φ.1 _ k (rt_apply k φ) g
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  · intro ψ hψ γ₁ γ₂ g
    induction hψ using Submodule.span_induction with
    | mem ψ h' =>
      obtain ⟨φ, hφ, e⟩ := h'
      rw [e]
      exact UpperTheory.constantTerm_levi_rational_left_invariant K r s φ.1 (hB.left φ hφ) γ₁ γ₂ g
    | zero => rfl
    | add x y _ _ hx hy => exact congrArg₂ (· + ·) hx hy
    | smul c x _ hx => exact congrArg (c • ·) hx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalOfFiniteDimensionalLeviSlices
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalMapOfSeparatelyFinite
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.finiteDimensional_map_of_separately_finite :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (X Y : Type) (S : Submodule ℂ M) (Φ : M →ₗ[ℂ] (X × Y → ℂ)) (V₁ : Submodule ℂ (X → ℂ)) (V₂ : Submodule ℂ (Y → ℂ)), FiniteDimensional ℂ V₁ → FiniteDimensional ℂ V₂ → (∀ m ∈ S, ∀ y, (fun x => Φ m (x, y)) ∈ V₁) → (∀ m ∈ S, ∀ x, (fun y => Φ m (x, y)) ∈ V₂) → FiniteDimensional ℂ (S.map Φ) := by
  intro M _ _ X Y S Φ V₁ V₂ h₁ h₂ hrow hcol
  obtain ⟨T, hT⟩ := exists_finset_eval_eq_zero V₁
  have mem : ∀ g ∈ S.map Φ, ∀ x, (fun y => g (x, y)) ∈ V₂ := by
    rintro g ⟨m, hm, rfl⟩ x
    exact hcol m hm x
  have memr : ∀ g ∈ S.map Φ, ∀ y, (fun x => g (x, y)) ∈ V₁ := by
    rintro g ⟨m, hm, rfl⟩ y
    exact hrow m hm y
  let F : S.map Φ →ₗ[ℂ] (T → V₂) :=
    LinearMap.pi fun t => LinearMap.codRestrict V₂
      ((LinearMap.funLeft ℂ ℂ (fun y : Y => ((t : X), y))).comp (S.map Φ).subtype)
      (fun g => mem g.1 g.2 t)
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    apply Subtype.ext
    funext p
    obtain ⟨x, y⟩ := p
    have h0 := hT (fun x => g.1 (x, y)) (memr g.1 g.2 y) (by
      intro t ht
      have := congrArg (fun v : T → V₂ => ((v ⟨t, ht⟩ : V₂) : Y → ℂ) y) hg
      simpa [F, LinearMap.funLeft] using this)
    simpa using congrFun h0 x
  exact Module.Finite.of_injective F hF
end

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.finiteDimensional_of_finiteDimensional_levi_slices :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (S : Submodule ℂ (archSmooth K (r + s))), S ≤ NInv K (r + s) r → Sat S → Level S → Types S → FiniteDimensional ℂ (slSp (e1 r s) (Set.range (emb (e2 r s))) S) → FiniteDimensional ℂ (slSp (e2 r s) (Set.range (emb (e1 r s))) S) → FiniteDimensional ℂ S := by
  intro K _ _ r s S hN hsat hlev htyp h1 h2
  obtain ⟨V, hVfd, hV⟩ := UpperTheory.exists_finiteDimensional_compact_translates_of_level_types K (r + s) S hlev htyp
  let Φ₀ : archSmooth K (r + s) →ₗ[ℂ] (AdelicGLn.AdelicGL K r × AdelicGLn.AdelicGL K s → ℂ) :=
    { toFun := fun m p => (m : AdelicGLn.AdelicGL K (r + s) → ℂ) (emb (e1 r s) p.1 * emb (e2 r s) p.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let Φ : archSmooth K (r + s) →ₗ[ℂ]
      ((AdelicGLn.AdelicGL K r × AdelicGLn.AdelicGL K s) × (Reduction.maxCompact : Subgroup (AdelicGLn.AdelicGL K (r + s))) → ℂ) :=
    { toFun := fun m p => (m : AdelicGLn.AdelicGL K (r + s) → ℂ) (emb (e1 r s) p.1.1 * emb (e2 r s) p.1.2 * (p.2 : AdelicGLn.AdelicGL K (r + s)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hfd0 : FiniteDimensional ℂ (Submodule.map Φ₀ S) := by
    refine UpperTheory.finiteDimensional_map_of_separately_finite _ _ _ S Φ₀ ((slSp (e1 r s) (Set.range (emb (e2 r s))) S).map (archSmooth K r).subtype)
      ((slSp (e2 r s) (Set.range (emb (e1 r s))) S).map (archSmooth K s).subtype) inferInstance inferInstance ?_ ?_
    · intro m hm y
      obtain ⟨f, hf, -⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K r (r + s) (e1 r s) (emb (e2 r s) y)
      refine Submodule.mem_map.mpr ⟨f m, Submodule.subset_span ⟨m, hm, emb (e2 r s) y, ⟨y, rfl⟩, fun x => hf m x⟩, ?_⟩
      funext x
      change (f m : AdelicGLn.AdelicGL K r → ℂ) x = _
      rw [hf, ← emb_comm]
      rfl
    · intro m hm x
      obtain ⟨f, hf, -⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K s (r + s) (e2 r s) (emb (e1 r s) x)
      refine Submodule.mem_map.mpr ⟨f m, Submodule.subset_span ⟨m, hm, emb (e1 r s) x, ⟨x, rfl⟩, fun y => hf m y⟩, ?_⟩
      funext y
      change (f m : AdelicGLn.AdelicGL K s → ℂ) y = _
      rw [hf]
      rfl
  have hfd : FiniteDimensional ℂ (Submodule.map Φ S) := by
    refine UpperTheory.finiteDimensional_map_of_separately_finite _ _ _ S Φ (Submodule.map Φ₀ S) V hfd0 hVfd ?_ ?_
    · intro m hm k
      refine Submodule.mem_map.mpr ⟨rt (k : AdelicGLn.AdelicGL K (r + s)) m, hsat _ k.2 m hm, ?_⟩
      funext x
      change ((rt (k : AdelicGLn.AdelicGL K (r + s)) m : archSmooth K (r + s)) : AdelicGLn.AdelicGL K (r + s) → ℂ) _ = _
      rw [rt_apply]
      rfl
    · intro m hm x
      exact hV m hm (emb (e1 r s) x.1 * emb (e2 r s) x.2)
  refine FiniteDimensional.of_injective (Φ.submoduleMap S) ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have hx' : ∀ p, Φ x p = 0 := fun p => congrFun (congrArg Subtype.val hx) p
  apply Subtype.ext
  apply Subtype.ext
  funext g
  obtain ⟨b, hb, k, hk, rfl⟩ := Reduction.exists_adelicBorel_mul_maxCompact g
  obtain ⟨X, m₁, m₂, rfl⟩ := UpperTheory.upperTriangular_eq_unipotent_mul_levi _ r s b (Reduction.mem_adelicBorel.mp hb)
  have hxN := hN x.2
  change ((x : archSmooth K (r + s)) : AdelicGLn.AdelicGL K (r + s) → ℂ) (unipGL X * blk m₁ m₂ * k) = 0
  rw [mul_assoc]
  change (∀ (X : UPos (r + s) r → AdeleRing (𝓞 K) K) g, ((x : archSmooth K (r + s)) : AdelicGLn.AdelicGL K (r + s) → ℂ) (unipGL X * g) = _) at hxN
  rw [hxN]
  exact hx' ((m₁, m₂), ⟨k, hk⟩)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SlSpPreservesGrowthAndLevel
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.slSp_preserves_growth_and_level :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n)) (S : Submodule ℂ (archSmooth K n)), (Growth S → Growth (slSp e Γ S)) ∧ (Level S → Level (slSp e Γ S)) := by
  intro K _ _ a n e Γ S
  constructor
  · intro hG φ hφ
    induction hφ using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨ψ, hψ, g, -, hfm⟩ := hf
      obtain ⟨C, N, hC⟩ := hG ψ hψ
      have hC0 : 0 ≤ C := by
        have h1 := (norm_nonneg _).trans (hC 1)
        have hp : 0 < height (1 : AdelicGLn.AdelicGL K n) ^ N := pow_pos (height_pos _) N
        exact le_of_mul_le_mul_right (by rw [zero_mul]; exact h1) hp
      have hc : 0 ≤ heightConst K n * height g :=
        mul_nonneg (zero_le_one.trans (one_le_heightConst (K := K) (n := n))) (height_pos g).le
      refine ⟨C * (heightConst K n * height g) ^ N, N, fun m => ?_⟩
      have hh : height (g * emb e m) ≤ heightConst K n * height g * height m :=
        (height_mul_le _ _).trans (mul_le_mul_of_nonneg_left (UpperTheory.height_blockEmbedding_le K a n e m) hc)
      calc ‖(f : AdelicGLn.AdelicGL K a → ℂ) m‖ = ‖(ψ : AdelicGLn.AdelicGL K n → ℂ) (g * emb e m)‖ := by rw [hfm]
        _ ≤ C * height (g * emb e m) ^ N := hC _
        _ ≤ C * (heightConst K n * height g * height m) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le hh N) hC0
        _ = C * (heightConst K n * height g) ^ N * height m ^ N := by rw [mul_pow]; ring
    | zero => simpa using (hasModerateGrowth_zero (K := K) (n := a))
    | add x y _ _ hx hy => simpa using hx.add hy
    | smul c x _ hx => simpa using hx.smul c
  · rintro ⟨L, hL, hinv⟩
    let f : AdelicGLn.FiniteAdelicGL K a →* AdelicGLn.FiniteAdelicGL K n := emb e
    refine ⟨L.comap f, hL.preimage (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K a n e).2.2, fun φ hφ => ?_⟩
    induction hφ using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨ψ, hψ, g, -, hfm⟩ := hh
      intro u hu m
      rw [hfm, hfm, map_mul, (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K a n e).1 u, ← mul_assoc]
      exact hinv ψ hψ (f u) hu _
    | zero => intro u _ m; simp
    | add x y _ _ hx hy => intro u hu m; simp [hx u hu m, hy u hu m]
    | smul c x _ hx => intro u hu m; simp [hx u hu m]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalSlSpReduction
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem aux {G H G' H' : Type} [Monoid G] [Monoid H] [Monoid G'] [Monoid H'] (E : G →* H) (i : G' → G) (i' : H' → H)
    (j : G' → H') (hj : ∀ k k', j (k * k') = j k * j k') (hi : ∀ k, E (i k) = i' (j k)) (V : Submodule ℂ (H' → ℂ))
    (hst : ∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) :
    (∀ f ∈ V.map (LinearMap.funLeft ℂ ℂ j), ∀ k', (fun k => f (k * k')) ∈ V.map (LinearMap.funLeft ℂ ℂ j)) ∧
    ∀ (f : G → ℂ) (ψ : H → ℂ) (g₀ : H), (∀ g, (fun k => ψ (g * i' k)) ∈ V) → (∀ m, f m = ψ (g₀ * E m)) →
      ∀ g, (fun k => f (g * i k)) ∈ V.map (LinearMap.funLeft ℂ ℂ j) := by
  constructor
  · rintro _ ⟨f, hf, rfl⟩ k'
    refine ⟨_, hst f hf (j k'), funext fun k => ?_⟩
    simp only [LinearMap.funLeft_apply, hj]
  · intro f ψ g₀ hψ hf g
    refine ⟨_, hψ (g₀ * E g), funext fun k => ?_⟩
    simp only [LinearMap.funLeft_apply]
    rw [hf, map_mul, hi, mul_assoc]

private theorem aux2 (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (k : archCompact K a) :
    embArch e k.1 ∈ archCompact K n := by
  have h := UpperTheory.blockEmbedding_adelic_norm_compat K a n e _ (Subgroup.mem_comap.1 k.2)
  rw [(UpperTheory.blockEmbedding_comm_infEmb_and_exp K a n e).1] at h
  exact Subgroup.mem_comap.2 h

private theorem aux3 {G X : Type} (A : Submodule ℂ (G → ℂ)) (s : Set A) (p : X → G) (W : Submodule ℂ (X → ℂ))
    (h : ∀ f ∈ s, (fun k => f.1 (p k)) ∈ W) : ∀ f ∈ Submodule.span ℂ s, (fun k => f.1 (p k)) ∈ W := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    convert W.zero_mem using 1
  | add x y _ _ hx hy =>
    convert W.add_mem hx hy using 1
  | smul c x _ hx =>
    convert W.smul_mem c hx using 1

theorem UpperTheory.finiteDimensional_slSp_reduction :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n)) (S : Submodule ℂ (archSmooth K n)), Types S → Types (slSp e Γ S) := by
  intro K _ _ a n e Γ S hS
  obtain ⟨V, hVf, hVst, hV⟩ := hS
  let j : archCompact K a → archCompact K n := fun k => ⟨embArch e k.1, aux2 K a n e k⟩
  have hj : ∀ k k', j (k * k') = j k * j k' := fun k k' => Subtype.ext (map_mul (embArch e) k.1 k'.1)
  have hi : ∀ k : archCompact K a, emb e (infEmb K a k.1) = infEmb K n (j k).1 :=
    fun k => (UpperTheory.blockEmbedding_comm_infEmb_and_exp K a n e).1 k.1
  have key := aux (G := AdelicGLn.AdelicGL K a) (H := AdelicGLn.AdelicGL K n) (emb e)
    (fun k : archCompact K a => infEmb K a k.1)
    (fun k : archCompact K n => infEmb K n k.1) j hj hi V hVst
  refine ⟨V.map (LinearMap.funLeft ℂ ℂ j), ?_, key.1, ?_⟩
  · exact Module.Finite.map V _
  · intro f hf g
    unfold slSp at hf
    refine aux3 (archSmooth K a) _ (fun k : archCompact K a => g * infEmb K a k.1)
      (V.map (LinearMap.funLeft ℂ ℂ j)) ?_ f hf
    rintro f' ⟨ψ, hψ, g₀, -, hf'⟩
    exact key.2 f'.1 ψ.1 g₀ (hV ψ hψ) hf' g
end

noncomputable section

open NumberField NumberField.mixedEmbedding Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.V.Af.Fin

variable {K : Type} [Field K] [NumberField K]

private theorem slLeft {a n : ℕ} (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n))
    (S : Submodule ℂ (archSmooth K n))
    (h : ∀ ψ ∈ S, ∀ g ∈ Γ, ∀ γ m, ψ.1 (g * emb e (AdelicGLn.diagonal K a γ * m)) = ψ.1 (g * emb e m)) :
    ∀ f ∈ slSp e Γ S, IsLeftInvariant f.1 := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ψ, hψ, g, hg, hf⟩ := hf
    intro γ m
    rw [hf, hf, h ψ hψ g hg]
  | zero => exact isLeftInvariant_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

theorem ctFin {r s : ℕ} (h₁ : FinAt K r) (h₂ : FinAt K s) {S : Submodule ℂ (archSmooth K (r + s))} (hS : Bdd S)
    (hK : Sat S) : FiniteDimensional ℂ (ctSp r S) := by
  obtain ⟨ι, _, ⟨D⟩⟩ := UpperTheory.exists_idempotent_decomposition_mixedSpace K
  obtain ⟨hN, hG, hL, hSat, hinv⟩ := UpperTheory.constantTermSpace_automorphic_properties K r s S hS hK
  have hT := UpperTheory.constantTermSpace_types_of_bdd K (r + s) r S hS
  have hC := UpperTheory.constantTermSpace_centre_of_bdd K (r + s) r S hS
  have hcap := UpperTheory.algebraic_module_of_vanishing_block K r s (ctSp r S) hN hC ι D
  have hb1 : ∀ γ : GL (Fin r) K, emb (e1 r s) γ = blk γ (1 : GL (Fin s) K) := by
    intro γ
    simp [blk]
  have hb2 : ∀ γ : GL (Fin s) K, emb (e2 r s) γ = blk (1 : GL (Fin r) K) γ := by
    intro γ
    simp [blk]
  refine UpperTheory.finiteDimensional_of_finiteDimensional_levi_slices K r s (ctSp r S) hN hSat hL hT ?_ ?_
  · refine h₁ _ ⟨?_, (UpperTheory.slSp_preserves_growth_and_level K r (r + s) (e1 r s) _ _).1 hG,
      (UpperTheory.slSp_preserves_growth_and_level K r (r + s) (e1 r s) _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K r (r + s) (e1 r s) _ _ hT, ?_⟩
    · apply slLeft
      rintro ψ hψ _ ⟨m₂, rfl⟩ γ m
      rw [map_mul, ← mul_assoc, ← emb_comm, mul_assoc, (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K r (r + s) (e1 r s)).2.1 γ, hb1,
        hinv ψ hψ]
    · refine UpperTheory.siegelLevi_block_aeval_stable K r (r + s) (e1 r s) _ (ctSp r S) (Van K r s) ι D ?_ (fun τ u => (hcap τ u).1)
      rintro ψ hψ _ ⟨m₂, rfl⟩ m
      rw [← emb_comm]
      exact hψ m m₂
  · refine h₂ _ ⟨?_, (UpperTheory.slSp_preserves_growth_and_level K s (r + s) (e2 r s) _ _).1 hG,
      (UpperTheory.slSp_preserves_growth_and_level K s (r + s) (e2 r s) _ _).2 hL, UpperTheory.finiteDimensional_slSp_reduction K s (r + s) (e2 r s) _ _ hT, ?_⟩
    · apply slLeft
      rintro ψ hψ _ ⟨m₁, rfl⟩ γ m
      rw [map_mul, ← mul_assoc, emb_comm m₁ (AdelicGLn.diagonal K s γ), mul_assoc,
        (UpperTheory.blockEmbedding_finiteAdelicGL_compat_continuous K s (r + s) (e2 r s)).2.1 γ, hb2, hinv ψ hψ]
    · refine UpperTheory.siegelLevi_block_aeval_stable K s (r + s) (e2 r s) _ (ctSp r S) (Van K r s) ι D ?_ (fun τ u => (hcap τ u).2)
      rintro ψ hψ _ ⟨m₁, rfl⟩ m
      exact hψ m₁ m

private theorem fin_of_ker {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (f : M →ₗ[ℂ] N)
    (h1 : FiniteDimensional ℂ (LinearMap.range f)) (h2 : FiniteDimensional ℂ (LinearMap.ker f)) :
    FiniteDimensional ℂ M := by
  apply Module.rank_lt_aleph0_iff.mp
  rw [← LinearMap.rank_range_add_rank_ker f]
  exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 ℂ _) (Module.rank_lt_aleph0 ℂ _)

theorem finAt_of {n : ℕ} (ih : ∀ m < n, FinAt K m) : FinAt K n := by
  intro S hS
  obtain ⟨S', hSS', hB', hSat'⟩ := UpperTheory.exists_automorphic_saturation_submodule K n S hS
  have hct : ∀ r, 0 < r → r < n → FiniteDimensional ℂ (ctSp r S') := by
    intro r hr0 hrn
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hrn.le
    exact ctFin (ih r hrn) (ih s (by omega)) hB' hSat'
  choose F hF1 _ using fun r => UpperTheory.exists_constantTerm_linearMap_equivariant_universalEnveloping K n r
  let ι : S' →ₗ[ℂ] automorphicForms K n :=
    LinearMap.codRestrict _ ((archSmooth K n).subtype ∘ₗ S'.subtype)
      (fun φ => UpperTheory.isAutomorphicForm_of_bdd_submodule K n S' hB' φ.1 φ.2)
  let I := {r : Fin n // 0 < r.val}
  have hmem : ∀ (i : I) (φ : S'), F i.1.val (ι φ) ∈ ctSp i.1.val S' := fun i φ =>
    Submodule.subset_span ⟨φ.1, φ.2, hF1 _ _⟩
  let G : S' →ₗ[ℂ] ((i : I) → ctSp i.1.val S') :=
    LinearMap.pi (fun i => LinearMap.codRestrict _ ((F i.1.val).comp ι) (hmem i))
  haveI : ∀ i : I, FiniteDimensional ℂ (ctSp i.1.val S') := fun i => hct _ i.2 i.1.2
  haveI : FiniteDimensional ℂ S' := by
    refine fin_of_ker G inferInstance ?_
    have hW : FiniteDimensional ℂ ((LinearMap.ker G).map S'.subtype) := by
      refine UpperTheory.finiteDimensional_of_bdd_cuspidal K n _ (hB'.mono (Submodule.map_subtype_le _ _)) ?_
      rintro _ ⟨x, hx, rfl⟩ r hr0 hrn g
      have h0 : F r (ι x) = 0 := by
        have := congrFun (LinearMap.mem_ker.mp hx) ⟨⟨r, hrn⟩, hr0⟩
        exact congrArg Subtype.val this
      have h1 := congrArg (fun ψ : archSmooth K n => (ψ : AdelicGLn.AdelicGL K n → ℂ) g) h0
      simp only [hF1] at h1
      exact h1
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ S'.injective_subtype _).symm
  exact Submodule.finiteDimensional_of_le hSS'

theorem formsFinite : FormsFinite := fun _ _ _ n => Nat.strong_induction_on n fun _ ih => finAt_of ih

end UpperTheory.V.Af.Fin
