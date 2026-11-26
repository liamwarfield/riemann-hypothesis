module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfRel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkInd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilMod

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilPrime
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.til_prime :
    ∀ (O O' B : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [CommRing B] [Algebra O B] [IsNoetherianRing B] (Q : Ideal (O' ⊗[O] B)), Q.IsPrime → (Q.map (Til.C O O' B)).IsPrime ∧ (Q.map (Til.C O O' B)).comap (Til.ι O O' B) = Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) := by
  intro O O' B _ _ _ _ _ _ _ Q hQ
  haveI hN : IsNoetherianRing (O' ⊗[O] B) := by
    letI : Algebra B (O' ⊗[O] B) := Algebra.TensorProduct.rightAlgebra
    haveI : Module.Finite B (O' ⊗[O] B) :=
      Module.Finite.equiv (Algebra.TensorProduct.commRight O B O').toLinearEquiv
    exact Algebra.FiniteType.isNoetherianRing B (O' ⊗[O] B)
  obtain ⟨-, -, h3, h4⟩ := UpperTheory.V.AlgebraTools.powerSeries_ker_map (O' ⊗[O] B) Q (IsNoetherian.noetherian Q)
  refine ⟨h3 hQ, ?_⟩
  have h5 : (Q.map (Til.C O O' B)).comap (Til.C O O' B) = Q := h4
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap]
  conv_rhs => rw [← h5]
  exact Iff.rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.RingBc
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.FreeBc
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem free_quotient_base_change (S T S' : Type) [CommRing S] [CommRing T] [Algebra S T] [CommRing S']
    (τ : T ≃+* S') (I : Ideal S) (rk : ℕ) (M : Type) [AddCommGroup M] [Module S M]
    (e : M ≃ₗ[S] (Fin rk → S ⧸ I)) (I' : Ideal S')
    (hI : I' = I.map ((τ : T →+* S').comp (algebraMap S T))) :
    ∃ e' : T ⊗[S] M ≃+ (Fin rk → S' ⧸ I'), ∀ z m, e' (z • m) = τ z • e' m := by
  let J : Ideal T := I.map (algebraMap S T)
  have hJ : I' = J.map (τ : T →+* S') := by
    rw [hI, Ideal.map_map]
  let q : T ⧸ J ≃+* S' ⧸ I' := Ideal.quotientEquiv J I' τ hJ
  let A1 : T ⊗[S] M ≃ₗ[T] T ⊗[S] (Fin rk → S ⧸ I) := LinearEquiv.baseChange S T M _ e
  let A2 : T ⊗[S] (Fin rk → S ⧸ I) ≃ₗ[T] (Fin rk → T ⊗[S] (S ⧸ I)) :=
    (Algebra.TensorProduct.piRight S T T (fun _ : Fin rk => S ⧸ I)).toLinearEquiv
  let A3 : (Fin rk → T ⊗[S] (S ⧸ I)) ≃ₗ[T] (Fin rk → T ⧸ J) :=
    LinearEquiv.piCongrRight (fun _ => (Algebra.TensorProduct.quotIdealMapEquivTensorQuot T I).symm.toLinearEquiv)
  let A := (A1.trans A2).trans A3
  refine ⟨A.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => q.toAddEquiv), ?_⟩
  intro z m
  funext i
  change q ((A (z • m)) i) = τ z • q ((A m) i)
  rw [A.map_smul, Pi.smul_apply]
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (A m i)
  rw [← hx, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, Ideal.quotientEquiv_mk, Ideal.quotientEquiv_mk, ← map_mul, map_mul]

theorem UpperTheory.V.Pa.BC.free_bc :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] (S R : Type) [CommRing S] [Algebra O S] [IsNoetherianRing S] [CommRing R] [Algebra O R] [IsNoetherianRing R] (s : S →ₐ[O] R) (M : Type) [AddCommGroup M] [Module R M] (I : Ideal S) (rk : ℕ) (e : M ≃+ (Fin rk → S ⧸ I)), (∀ z m, e (s z • m) = z • e m) → ∀ (S' : Type) [CommRing S'] (τ : Til O O' S ≃+* S') (I' : Ideal S'), I' = I.map ((τ : Til O O' S →+* S').comp (Til.ι O O' S)) → ∃ e' : Til O O' R ⊗[R] M ≃+ (Fin rk → S' ⧸ I'), ∀ z m, e' (Til.map O' s z • m) = τ z • e' m := by
  intro O O' _ _ _ _ S R _ _ _ _ _ _ s M _ _ I rk e he S' _ τ I' hI
  letI : Module S M := Module.compHom M s.toRingHom
  let eL : M ≃ₗ[S] (Fin rk → S ⧸ I) := e.toLinearEquiv (fun c x => he c x)
  haveI : Module.Finite S M := Module.Finite.equiv eL.symm
  obtain ⟨ε, -, hε⟩ := BC.til_mod O O' S R s M (fun a m => rfl)
  obtain ⟨f, hf⟩ := free_quotient_base_change S (Til O O' S) S' τ I rk M eL I' (by rw [Til.algebraMap_eq]; exact hI)
  refine ⟨ε.symm.trans f, ?_⟩
  intro z m
  have hsymm : ε.symm (Til.map O' s z • m) = z • ε.symm m := by
    apply ε.injective
    rw [hε, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  rw [AddEquiv.trans_apply, hsymm, hf, AddEquiv.trans_apply]
end

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem lamEmb_X (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (D : ℕ) (k : Fin D) :
    lamEmb O O' D (MvPowerSeries.X (.inr k)) = MvPowerSeries.X (.inr k) := by
  simp [lamEmb]

theorem UpperTheory.V.Pa.BC.ring_bc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O O' : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] [IsScalarTower ℤ_[l] O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] [Module.Free O O'] (r : Resid G0.frame O n) (r' : Resid G0.frame O' n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (u : Pair r B) (u' : Pair r' (Til O O' B)) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (b' : TWBase u' (J.map (Til.ι O O' B)) Unit D) (τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D) (G : Glob l L) (h : G.Hom G0) (q : ℕ) (ut : Fin q → Fin n → O) (N : ℕ) (τS : Til O O' (Sinf O Empty D q n) ≃ₐ[O'] Sinf O' Unit D q n) (A : TWRing b h ut N), RBC r r' → u.Maps (Til.ι O O' B) u'.D u'.ψ → Nonempty (BaseRel b b' τ) → SinfRel l τ τS → ∃ A' : TWRing b' h (fun j i => algebraMap O O' (ut j i)) N, Nonempty (RingRel A A' τS) := by
  intro l _ L G0 n O O' _ _ _ _ _ _ _ _ _ _ _ _ _ r r' B _ _ _ _ u u' J D b b' τ G h q ut N τS A hr _ ⟨hb⟩ hS
  obtain ⟨rN', hN⟩ := (resid_bc l G.frame O O' n A.rN).1
  obtain ⟨hco, hloc, -⟩ := til_co O O' A.R
  obtain ⟨-, p', hp⟩ := pair_bc l G.frame O O' n A.rN rN' hN A.R (Til O O' A.R) (Til.ι O O' A.R)
    (Til.ι_algebraMap O O' A.R) A.p
  obtain ⟨e', he'⟩ := free_bc O O' (Sinf O Empty D q n) A.R A.s A.M _ A.rk A.e A.e_smul
    (Sinf O' Unit D q n) τS.toRingEquiv _ (hS.del A.a)
  have hc : Glob.Compat h rN' r' := by
    refine ⟨fun i => ?_, ?_, ?_⟩
    · rw [hN.1, hr.1, A.compat.1]
      rfl
    · funext v i
      rw [hN.2.1, hr.2.1, A.compat.2.1]
    · funext v i
      rw [hN.2.2, hr.2.2, A.compat.2.2]
      rfl
  refine ⟨{ rN := rN', compat := hc, R := Til O O' A.R, p := p'
            s := (Til.map O' A.s).comp τS.symm.toAlgHom
            s_w := fun k => ?_
            U := fun j i => Til.ι O O' A.R (A.U j i)
            U_res := fun j i => ?_
            M := Til O O' A.R ⊗[A.R] A.M
            a := A.a, le_a := A.le_a, rk := A.rk, e := e'
            e_smul := fun z m => ?_ },
    ⟨{ ρ := AlgEquiv.refl, maps := hp, s := fun z => ?_, U := fun _ _ => rfl, ν := AddEquiv.refl _
       ν_smul := fun _ _ => rfl }⟩⟩
  · rw [← lamEmb_X O O' D k, ← hS.C, hb.wt, ← hp.2]
    change Til.map O' A.s (τS.symm (τS _)) = _
    rw [AlgEquiv.symm_apply_apply, Til.map_ι, A.s_w, map_sub, map_mul, map_one, Til.ι_algebraMap]
    rfl
  · rw [← Til.ι_algebraMap, ← map_sub]
    exact fun hu => A.U_res j i (IsLocalHom.map_nonunit _ hu)
  · have := he' (τS.symm z) m
    rw [show τS.toRingEquiv (τS.symm z) = z from τS.apply_symm_apply z] at this
    exact this
  · change Til.map O' A.s (τS.symm (τS z)) = Til.map O' A.s z
    rw [AlgEquiv.symm_apply_apply]
end
