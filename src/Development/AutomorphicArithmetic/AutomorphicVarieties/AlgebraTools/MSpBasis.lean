module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MSplitDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MSpBasis
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SpBasis
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SpStep
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.splitAlg_succ_equiv :
    ∀ (R : Type) [CommRing R] (n : ℕ) (P : Polynomial R), P.Monic → P.natDegree = n + 1 →
      ∃ (_ : Algebra (AdjoinRoot P) (SplitAlg P (n + 1))) (_ : IsScalarTower R (AdjoinRoot P) (SplitAlg P (n + 1))),
        algebraMap (AdjoinRoot P) (SplitAlg P (n + 1)) (AdjoinRoot.root P) = SplitAlg.root P (n + 1) 0 ∧
        ∃ e : SplitAlg P (n + 1) ≃ₐ[AdjoinRoot P]
            SplitAlg ((P.map (algebraMap R (AdjoinRoot P))) /ₘ (Polynomial.X - Polynomial.C (AdjoinRoot.root P))) n,
          ∀ i : Fin n, e (SplitAlg.root P (n + 1) i.succ) = SplitAlg.root _ n i := by
  intro R _ n P hP hdeg
  have hroot0 : Polynomial.eval₂ (algebraMap R (SplitAlg P (n + 1))) (SplitAlg.root P (n + 1) 0) P = 0 := by
    rw [Polynomial.eval₂_eq_eval_map, ← SplitAlg.prod_root, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 0) (by simp)
  let φ : AdjoinRoot P →+* SplitAlg P (n + 1) :=
    AdjoinRoot.lift (algebraMap R (SplitAlg P (n + 1))) (SplitAlg.root P (n + 1) 0) hroot0
  letI alg : Algebra (AdjoinRoot P) (SplitAlg P (n + 1)) := φ.toAlgebra
  have hφ : ∀ r : R, algebraMap (AdjoinRoot P) (SplitAlg P (n + 1)) (algebraMap R (AdjoinRoot P) r)
      = algebraMap R (SplitAlg P (n + 1)) r := fun r => AdjoinRoot.lift_of hroot0
  haveI tower : IsScalarTower R (AdjoinRoot P) (SplitAlg P (n + 1)) :=
    IsScalarTower.of_algebraMap_eq (fun r => (hφ r).symm)
  have hr0 : algebraMap (AdjoinRoot P) (SplitAlg P (n + 1)) (AdjoinRoot.root P) = SplitAlg.root P (n + 1) 0 :=
    AdjoinRoot.lift_root hroot0
  refine ⟨alg, tower, hr0, ?_⟩
  set Q := (P.map (algebraMap R (AdjoinRoot P))) /ₘ (Polynomial.X - Polynomial.C (AdjoinRoot.root P)) with hQ
  have hfac : P.map (algebraMap R (AdjoinRoot P)) = (Polynomial.X - Polynomial.C (AdjoinRoot.root P)) * Q := by
    rw [hQ, eq_comm, Polynomial.mul_divByMonic_eq_iff_isRoot, AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.isRoot_root P
  have hmapS : P.map (algebraMap R (SplitAlg P (n + 1)))
      = (Polynomial.X - Polynomial.C (SplitAlg.root P (n + 1) 0))
        * Q.map (algebraMap (AdjoinRoot P) (SplitAlg P (n + 1))) := by
    rw [IsScalarTower.algebraMap_eq R (AdjoinRoot P) (SplitAlg P (n + 1)), ← Polynomial.map_map, hfac,
      Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hr0]
  have hg : ∏ i : Fin n, (Polynomial.X - Polynomial.C (SplitAlg.root P (n + 1) i.succ))
      = Q.map (algebraMap (AdjoinRoot P) (SplitAlg P (n + 1))) := by
    have h1 := SplitAlg.prod_root P (n + 1)
    rw [Fin.prod_univ_succ, hmapS] at h1
    exact (Polynomial.monic_X_sub_C _).isRegular.left h1
  let g : SplitAlg Q n →ₐ[AdjoinRoot P] SplitAlg P (n + 1) :=
    SplitAlg.lift Q n (fun i => SplitAlg.root P (n + 1) i.succ) hg
  let a : Fin (n + 1) → SplitAlg Q n :=
    Fin.cons (algebraMap (AdjoinRoot P) (SplitAlg Q n) (AdjoinRoot.root P)) (SplitAlg.root Q n)
  have hf : ∏ i, (Polynomial.X - Polynomial.C (a i)) = P.map (algebraMap R (SplitAlg Q n)) := by
    rw [Fin.prod_univ_succ]
    simp only [a, Fin.cons_zero, Fin.cons_succ]
    rw [SplitAlg.prod_root, IsScalarTower.algebraMap_eq R (AdjoinRoot P) (SplitAlg Q n), ← Polynomial.map_map,
      hfac, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  let f : SplitAlg P (n + 1) →ₐ[R] SplitAlg Q n := SplitAlg.lift P (n + 1) a hf
  have hf0 : f (SplitAlg.root P (n + 1) 0) = algebraMap (AdjoinRoot P) (SplitAlg Q n) (AdjoinRoot.root P) := by
    simp only [f, SplitAlg.lift_root, a, Fin.cons_zero]
  have hfs : ∀ i : Fin n, f (SplitAlg.root P (n + 1) i.succ) = SplitAlg.root Q n i := by
    intro i
    simp only [f, SplitAlg.lift_root, a, Fin.cons_succ]
  have hfK : f.comp (IsScalarTower.toAlgHom R (AdjoinRoot P) (SplitAlg P (n + 1)))
      = IsScalarTower.toAlgHom R (AdjoinRoot P) (SplitAlg Q n) := by
    apply AdjoinRoot.algHom_ext
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', IsScalarTower.coe_toAlgHom', hr0, hf0]
  let fK : SplitAlg P (n + 1) →ₐ[AdjoinRoot P] SplitAlg Q n :=
    { f with commutes' := fun k => DFunLike.congr_fun hfK k }
  have hgs : ∀ i : Fin n, g (SplitAlg.root Q n i) = SplitAlg.root P (n + 1) i.succ := by
    intro i
    exact SplitAlg.lift_root Q n _ hg i
  refine ⟨AlgEquiv.ofAlgHom fK g ?_ ?_, ?_⟩
  · apply SplitAlg.hom_ext
    intro i
    show f (g (SplitAlg.root Q n i)) = SplitAlg.root Q n i
    rw [hgs, hfs]
  · apply AlgHom.restrictScalars_injective R
    apply SplitAlg.hom_ext
    intro i
    show g (f (SplitAlg.root P (n + 1) i)) = SplitAlg.root P (n + 1) i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hf0, AlgHom.commutes, hr0]
    · rw [hfs, hgs]
  · intro i
    exact hfs i
end

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private def UpperTheory.V.AlgebraTools.spIdx (n d : ℕ) (hd : d = n + 1) :
    (Fin d × ∀ i : Fin n, Fin (n - i)) ≃ (∀ i : Fin (n + 1), Fin (n + 1 - i)) where
  toFun p := fun i => Fin.cases (motive := fun i : Fin (n + 1) => Fin (n + 1 - i))
    ⟨p.1, by have := p.1.2; simp; omega⟩
    (fun j => ⟨p.2 j, by have := (p.2 j).2; simp only [Fin.val_succ]; omega⟩) i
  invFun c := (⟨c 0, by have := (c 0).2; simp at this; omega⟩,
    fun j => ⟨c j.succ, by have := (c j.succ).2; simp only [Fin.val_succ] at this; omega⟩)
  left_inv p := by
    ext <;> rfl
  right_inv c := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem UpperTheory.V.AlgebraTools.spCard (n : ℕ) :
    Fintype.card (∀ i : Fin n, Fin (n - i)) = n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Fintype.card_congr (UpperTheory.V.AlgebraTools.spIdx n (n + 1) rfl), Fintype.card_prod,
      Fintype.card_fin, ih, Nat.factorial_succ]

theorem UpperTheory.V.AlgebraTools.splitAlg_basis :
    ∀ (n : ℕ) (R : Type) [CommRing R] (P : Polynomial R), P.Monic → P.natDegree = n →
      (∃ b : Module.Basis (∀ i : Fin n, Fin (n - i)) R (SplitAlg P n), ∀ c, b c = ∏ i, SplitAlg.root P n i ^ (c i : ℕ)) ∧
      Fintype.card (∀ i : Fin n, Fin (n - i)) = n.factorial := by
  intro n
  induction n with
  | zero =>
    intro R _ P hm hd
    refine ⟨?_, UpperTheory.V.AlgebraTools.spCard 0⟩
    have hP : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm hd
    let f : SplitAlg P 0 →ₐ[R] R :=
      SplitAlg.lift P 0 (A := R) (fun i => i.elim0) (by simp [hP])
    have hfg : (Algebra.ofId R (SplitAlg P 0)).comp f = AlgHom.id R _ :=
      SplitAlg.hom_ext P 0 (fun i => i.elim0)
    have hgf : f.comp (Algebra.ofId R (SplitAlg P 0)) = AlgHom.id R R := Algebra.ext_id _ _ _
    let e : R ≃ₐ[R] SplitAlg P 0 := AlgEquiv.ofAlgHom (Algebra.ofId R _) f hfg hgf
    refine ⟨(Module.Basis.singleton (∀ i : Fin 0, Fin (0 - i)) R).map e.toLinearEquiv, fun c => ?_⟩
    simp [Module.Basis.singleton_apply]
  | succ n ih =>
    intro R _ P hm hd
    refine ⟨?_, UpperTheory.V.AlgebraTools.spCard (n + 1)⟩
    obtain ⟨inst1, inst2, h3, e, he⟩ := splitAlg_succ_equiv R n P hm hd
    have hroot : (Polynomial.map (algebraMap R (AdjoinRoot P)) P).IsRoot (AdjoinRoot.root P) := by
      rw [AdjoinRoot.algebraMap_eq]
      exact AdjoinRoot.isRoot_root P
    have hmul := (Polynomial.mul_divByMonic_eq_iff_isRoot).2 hroot
    have hQm : (Polynomial.map (algebraMap R (AdjoinRoot P)) P /ₘ
        (Polynomial.X - Polynomial.C (AdjoinRoot.root P))).Monic := by
      refine Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C (AdjoinRoot.root P)) ?_
      rw [hmul]
      exact hm.map _
    have hQd : (Polynomial.map (algebraMap R (AdjoinRoot P)) P /ₘ
        (Polynomial.X - Polynomial.C (AdjoinRoot.root P))).natDegree = n := by
      rcases subsingleton_or_nontrivial (AdjoinRoot P) with hs | hs
      · exfalso
        have hR : Nontrivial R := by
          rcases subsingleton_or_nontrivial R with hR | hR
          · rw [Subsingleton.elim P 0, Polynomial.natDegree_zero] at hd
            omega
          · exact hR
        have hne := (AdjoinRoot.powerBasis' hm).basis.ne_zero
          ⟨0, by rw [AdjoinRoot.powerBasis'_dim, hd]; omega⟩
        exact hne (Subsingleton.elim _ _)
      · rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C _),
          hm.natDegree_map, hd, Polynomial.natDegree_X_sub_C]
        rfl
    obtain ⟨c, hc⟩ := (ih (AdjoinRoot P) _ hQm hQd).1
    let b := (AdjoinRoot.powerBasis' hm).basis.reindex
      (finCongr (by rw [AdjoinRoot.powerBasis'_dim, hd]))
    let c' := c.map e.symm.toLinearEquiv
    refine ⟨(b.smulTower c').reindex (UpperTheory.V.AlgebraTools.spIdx n (n + 1) rfl), fun k => ?_⟩
    rw [Module.Basis.reindex_apply, Module.Basis.smulTower_apply, Fin.prod_univ_succ]
    have hb : ∀ j, b j = AdjoinRoot.root P ^ (j : ℕ) := by
      intro j
      simp only [b, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, AdjoinRoot.powerBasis'_gen]
      rfl
    have hinv : ∀ i : Fin n, e.symm (SplitAlg.root _ n i) = SplitAlg.root P (n + 1) i.succ := by
      intro i
      rw [AlgEquiv.symm_apply_eq, he]
    simp only [c', Module.Basis.map_apply, hb, hc, Algebra.smul_def, map_pow, h3, map_prod,
      AlgEquiv.toLinearEquiv_apply, hinv]
    rfl
end

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.mSplitAlg_basis :
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (n : ℕ) (R : Type) [CommRing R] (P : κ → Polynomial R), (∀ j, (P j).Monic) → (∀ j, (P j).natDegree = n) →
      ∃ b : Module.Basis (κ → ∀ i : Fin n, Fin (n - i)) R (MSplitAlg P n), ∀ c, b c = ∏ j, ∏ i, MSplitAlg.root P n j i ^ (c j i : ℕ) := by
  intro κ _ _ n R _ P hm hd
  have hb := fun j => (UpperTheory.V.AlgebraTools.splitAlg_basis n R (P j) (hm j) (hd j)).1
  choose bj hbj using hb
  let f : ∀ j, SplitAlg (P j) n →ₐ[R] MSplitAlg P n := fun j =>
    SplitAlg.lift (P j) n (MSplitAlg.root P n j) (MSplitAlg.prod_root P n j)
  let M : (∀ j, SplitAlg (P j) n) →ₘₗ[R] MSplitAlg P n :=
    (MultilinearMap.mkPiAlgebra R κ (MSplitAlg P n)).compLinearMap (fun j => (f j).toLinearMap)
  have hM : ∀ x, M x = ∏ j, f j (x j) := fun x => by
    simp [M, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  let ψ : (⨂[R] j, SplitAlg (P j) n) →ₐ[R] MSplitAlg P n :=
    PiTensorProduct.liftAlgHom M (by rw [hM]; simp)
      (fun x y => by rw [hM, hM, hM]; simp [Finset.prod_mul_distrib])
  have hψt : ∀ x, ψ (PiTensorProduct.tprod R x) = ∏ j, f j (x j) := fun x => by
    simp [ψ, hM]
  have hψs : ∀ j x, ψ (PiTensorProduct.singleAlgHom j x) = f j x := fun j x => by
    rw [PiTensorProduct.singleAlgHom_apply, hψt,
      Fintype.prod_eq_single j (fun k hk => by simp [Pi.mulSingle_eq_of_ne hk])]
    simp
  let φ : MSplitAlg P n →ₐ[R] (⨂[R] j, SplitAlg (P j) n) :=
    MSplitAlg.lift P n (fun j i => PiTensorProduct.singleAlgHom j (SplitAlg.root (P j) n i)) (fun j => by
      have := congrArg (Polynomial.map
        (PiTensorProduct.singleAlgHom (R := R) (A := fun j => SplitAlg (P j) n) j).toRingHom)
        (SplitAlg.prod_root (P j) n)
      simp only [Polynomial.map_prod, Polynomial.map_map, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap,
        Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe] at this
      exact this)
  have h1 : ψ.comp φ = AlgHom.id R (MSplitAlg P n) := MSplitAlg.hom_ext P n (fun j i => by
    simp only [AlgHom.comp_apply, AlgHom.id_apply, φ, MSplitAlg.lift_root, hψs, f, SplitAlg.lift_root])
  have h2 : φ.comp ψ = AlgHom.id R _ := PiTensorProduct.algHom_ext (fun j => SplitAlg.hom_ext (P j) n (fun i => by
    simp only [AlgHom.comp_apply, AlgHom.id_apply, hψs, f, SplitAlg.lift_root, φ, MSplitAlg.lift_root]))
  let e : MSplitAlg P n ≃ₐ[R] (⨂[R] j, SplitAlg (P j) n) := AlgEquiv.ofAlgHom φ ψ h2 h1
  refine ⟨(Basis.piTensorProduct bj).map e.symm.toLinearEquiv, fun c => ?_⟩
  rw [Module.Basis.map_apply, Basis.piTensorProduct_apply]
  show ψ _ = _
  rw [hψt]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [hbj j (c j), map_prod]
  simp only [map_pow, f, SplitAlg.lift_root]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IrredIffSpan
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanMapRingHomEqTop
theorem UpperTheory.Reformulated.B.Qe1.span_map_ringHom_eq_top :
    ∀ {k K G ι : Type} [inst : Field k] [inst_1 : Field K]
    [Fintype ι] [DecidableEq ι] (φ : k →+* K) (f : G → Matrix ι ι k),
    Submodule.span k (Set.range f) = ⊤ → Submodule.span K (Set.range fun (g : G) ↦ (f g).map (⇑φ : k → K)) = ⊤ := by
  intro k K G ι _ _ _ _ φ f h
  have key : ∀ M : Matrix ι ι k, M ∈ Submodule.span k (Set.range f) →
      M.map (⇑φ : k → K) ∈
        Submodule.span K (Set.range fun (g : G) ↦ (f g).map (⇑φ : k → K)) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact Submodule.subset_span ⟨g, rfl⟩
    | zero =>
      have e : (0 : Matrix ι ι k).map (⇑φ : k → K) = 0 := by
        ext i j
        simp
      rw [e]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have e : (x + y).map (⇑φ : k → K) = x.map (⇑φ : k → K) + y.map (⇑φ : k → K) := by
        ext i j
        simp
      rw [e]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have e : (a • x).map (⇑φ : k → K) = φ a • x.map (⇑φ : k → K) := by
        ext i j
        simp
      rw [e]
      exact Submodule.smul_mem _ _ hx
  rw [eq_top_iff]
  intro N _
  rw [Matrix.matrix_eq_sum_single N]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have e : Matrix.single i j (N i j)
      = N i j • (Matrix.single i j (1 : k)).map (⇑φ : k → K) := by
    ext a b
    by_cases hab : i = a ∧ j = b <;> simp [Matrix.single, hab]
  rw [e]
  exact Submodule.smul_mem _ _ (key _ (h ▸ Submodule.mem_top))
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleOfSpanningMatrices
theorem UpperTheory.Reformulated.B.IrreducibleOfSpanningMatrices.irreducible_of_span_eq_top :
    ∀ {K G ι : Type} [inst : Field K] [inst_1 : Fintype ι]
    [DecidableEq ι] (f : G → Matrix ι ι K),
    Submodule.span K (Set.range f) = ⊤ →
      ∀ (N : Submodule K (ι → K)), (∀ (g : G), ∀ v ∈ N, (f g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro K G ι _ _ _ f hf N hN
  have key : ∀ A : Matrix ι ι K, ∀ v ∈ N, A.mulVec v ∈ N := by
    intro A v hv
    have hA : A ∈ Submodule.span K (Set.range f) := by rw [hf]; exact Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact hN g v hv
    | zero => rw [Matrix.zero_mulVec]; exact N.zero_mem
    | add x y _ _ hx hy => rw [Matrix.add_mulVec]; exact N.add_mem hx hy
    | smul a x _ hx => rw [Matrix.smul_mulVec]; exact N.smul_mem a hx
  by_cases h : N = ⊥
  · exact Or.inl h
  · right
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    have hi' : v i ≠ 0 := hi
    rw [eq_top_iff]
    intro w _
    have h1 := key (Matrix.of fun a b => if b = i then w a * (v i)⁻¹ else 0) v hv
    have h2 : (Matrix.of fun a b => if b = i then w a * (v i)⁻¹ else 0).mulVec v = w := by
      funext a
      simp [Matrix.mulVec, dotProduct, hi']
    rwa [h2] at h1
end

open Polynomial Matrix IsLocalRing TensorProduct

private theorem irreducible_of_span_eq_top {K G ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    (f : G → Matrix ι ι K) (h : Submodule.span K (Set.range f) = ⊤) (N : Submodule K (ι → K))
    (hN : ∀ g, ∀ v ∈ N, (f g).mulVec v ∈ N) : N = ⊥ ∨ N = ⊤ :=
  _root_.UpperTheory.Reformulated.B.IrreducibleOfSpanningMatrices.irreducible_of_span_eq_top f h N hN

private theorem span_map_ringHom_eq_top {k K G ι : Type} [Field k] [Field K] [Fintype ι] [DecidableEq ι]
    (φ : k →+* K) (f : G → Matrix ι ι k) (h : Submodule.span k (Set.range f) = ⊤) :
    Submodule.span K (Set.range fun g => (f g).map φ) = ⊤ :=
  _root_.UpperTheory.Reformulated.B.Qe1.span_map_ringHom_eq_top φ f h

theorem UpperTheory.V.AlgebraTools.irred_iff_span :
    ∀ {k K G : Type} [Field k] [IsAlgClosed k] [Field K] [Group G] {ι : Type} [Fintype ι] [DecidableEq ι] (φ : k →+* K) (ρ : G →* Matrix ι ι k), ((∀ N : Submodule k (ι → k), (∀ g, ∀ v ∈ N, (ρ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) ↔ Submodule.span k (Set.range ρ) = ⊤) ∧ (Submodule.span k (Set.range ρ) = ⊤ ↔ Submodule.span K (Set.range fun g => (ρ g).map φ) = ⊤) ∧ (Submodule.span K (Set.range fun g => (ρ g).map φ) = ⊤ → ∀ N : Submodule K (ι → K), (∀ g, ∀ v ∈ N, ((ρ g).map φ).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) := by
  intro k K G _ _ _ _ ι _ _ φ ρ
  refine ⟨⟨KStar.Schema.span_eq_top_of_irreducible ρ, fun h N hN => irreducible_of_span_eq_top ρ h N hN⟩,
    ⟨span_map_ringHom_eq_top φ ρ, fun h => ?_⟩, fun h N hN => irreducible_of_span_eq_top _ h N hN⟩
  refine KStar.Schema.span_eq_top_of_residue φ ?_ _ ?_
  · rw [IsLocalRing.maximalIdeal_eq_bot]
    exact (RingHom.injective_iff_ker_eq_bot φ).mp φ.injective
  · rw [← Set.range_comp]
    exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LocFactor
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := ⟨fun f hf => by
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => f ((e + 1) * k))
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
      rw [pow_mul] at h
      exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m h)
  refine ⟨L, fun n => ?_⟩
  have h1 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hf (m := n) (n := (e + 1) * n) (Nat.le_mul_of_pos_left n (Nat.succ_pos e))
  simpa using (I ^ n).add_mem h2 (Ideal.pow_right_mono hJI n h1)⟩

open IsLocalRing in
private theorem complete_of_finite (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R']
    [IsLocalRing R'] : IsAdicComplete (maximalIdeal R') R' := by
  haveI hN : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  have hcomap : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal R'))
  have hle : (maximalIdeal R).map (algebraMap R R') ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 hcomap.ge
  have hrad : maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨h1, h2⟩ := hP
    have h3 : P.comap (algebraMap R R') = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ h2.ne_top)
        (Ideal.map_le_iff_le_comap.1 h1)).symm
    have h4 : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap R R')
        (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) P
        (h3 ▸ maximalIdeal.isMaximal R)
    exact (eq_maximalIdeal h4).ge
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have h0 : IsAdicComplete (maximalIdeal R) R' := by
    let I := maximalIdeal R
    have hb : Function.Bijective (AdicCompletion.of I R) :=
      AdicCompletion.of_bijective_iff.2 (show IsAdicComplete I R from inferInstance)
    let φ : R ≃ₗ[R] AdicCompletion I R := LinearEquiv.ofBijective (AdicCompletion.of I R) hb
    let e : R' ≃ₗ[R] AdicCompletion I R ⊗[R] R' :=
      (TensorProduct.lid R R').symm.trans (TensorProduct.congr φ (LinearEquiv.refl R R'))
    have h1 : AdicCompletion.of I R 1 = 1 := by
      ext n
      simp
    have hfac : ⇑(AdicCompletion.of I R') =
        ⇑(AdicCompletion.ofTensorProduct I R') ∘ ⇑e := by
      funext x
      have he : e x = (1 : AdicCompletion I R) ⊗ₜ[R] x := by
        simp [e, φ, h1]
      simp [he]
    apply AdicCompletion.of_bijective_iff.1
    rw [hfac]
    exact (AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I R').comp e.bijective
  have hP : IsPrecomplete (maximalIdeal R') R' :=
    prec_cofinal hle he (IsPrecomplete.map_algebraMap_iff.2 h0.toIsPrecomplete)
  exact { toIsHausdorff := inferInstance, toIsPrecomplete := hP }

theorem UpperTheory.V.AlgebraTools.local_factor :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A] (n : Ideal A) [n.IsMaximal],
      Function.Surjective (algebraMap A (Localization.AtPrime n)) ∧ Module.Finite R (Localization.AtPrime n) ∧
      IsLocalHom (algebraMap R (Localization.AtPrime n)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal (Localization.AtPrime n)) (Localization.AtPrime n) ∧
      (Module.Free R A → Module.Free R (Localization.AtPrime n)) ∧
      (∃ e : A, IsIdempotentElem e ∧ (∀ n' : Ideal A, n'.IsMaximal → (e ∉ n' ↔ n' = n)) ∧
        RingHom.ker (algebraMap A (Localization.AtPrime n)) = Ideal.span {1 - e}) ∧
      ∀ (C : Type) [CommRing C] [IsLocalRing C] (f : A →+* C), (IsLocalRing.maximalIdeal C).comap f = n →
        ∃ g : Localization.AtPrime n →+* C, g.comp (algebraMap A _) = f := by
  intro R _ _ _ _ A _ _ _ n hn
  letI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_henselianRing R
  have hfin : Module.Finite R (Localization.AtPrime n) := GlobalTheory.finite_localization_of_henselian R n
  refine ⟨GlobalTheory.surjective_algebraMap_localization_of_henselian R n, hfin, ⟨fun a ha => ?_⟩,
    complete_of_finite R _, fun hF => ?_, ?_, fun C _ _ f hf => ?_⟩
  · by_contra h
    have h1 : a ∈ IsLocalRing.maximalIdeal R := h
    rw [← GlobalTheory.comap_eq_maximalIdeal_of_finite (IsLocalRing.maximalIdeal (Localization.AtPrime n)),
      Ideal.mem_comap] at h1
    exact h1 ha
  · haveI : Module.Flat A (Localization.AtPrime n) := IsLocalization.flat _ n.primeCompl
    haveI : Module.Flat R (Localization.AtPrime n) := Module.Flat.trans R A _
    exact Module.free_of_flat_of_isLocalRing
  · obtain ⟨e, he, H⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian R n
    refine ⟨e, he, H, le_antisymm (fun x hx => ?_) ?_⟩
    · obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff n.primeCompl _ x).1 hx
      have heq : e ∉ n := (H n hn).2 rfl
      have hu : IsUnit (e * s + (1 - e)) := by
        by_contra h
        obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits h
        by_cases hen : e ∈ m
        · rw [Submodule.add_mem_iff_right _ (Ideal.mul_mem_right _ _ hen),
            GlobalTheory.one_sub_mem_iff_notMem_of_isIdempotentElem he] at hmem
          exact hmem hen
        · rw [Submodule.add_mem_iff_left _
              ((GlobalTheory.one_sub_mem_iff_notMem_of_isIdempotentElem he m).2 hen),
            (H m hm).1 hen] at hmem
          exact (hn.isPrime.mem_or_mem hmem).elim heq s.2
      obtain ⟨v, hv⟩ := hu.exists_left_inv
      refine Ideal.mem_span_singleton'.2 ⟨v * x, ?_⟩
      linear_combination x * hv - v * e * hs
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
      exact ((IsIdempotentElem.iff_eq_one_of_isUnit (IsLocalization.map_units _
        (⟨e, (H n hn).2 rfl⟩ : n.primeCompl))).1 (he.map _)).symm
  · have hu : ∀ y : n.primeCompl, IsUnit (f y) := fun y => by
      by_contra h
      have h1 : (y : A) ∈ (IsLocalRing.maximalIdeal C).comap f := h
      rw [hf] at h1
      exact y.2 h1
    exact ⟨IsLocalization.lift hu, IsLocalization.lift_comp hu⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TnAlgMapSmulMem
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem UpperTheory.V.AlgebraTools.tnAlg_smul_mem {R A M : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] (I : Ideal R) (a : A) {y : M}
    (hy : y ∈ (I • ⊤ : Submodule R M)) : a • y ∈ (I • ⊤ : Submodule R M) := by
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro r hr n _
    rw [← algebraMap_smul A r n, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
    exact Submodule.smul_mem_smul hr trivial
  · intro u v hu hv
    rw [smul_add]
    exact Submodule.add_mem _ hu hv

private theorem UpperTheory.V.AlgebraTools.tnAlg_map_smul_mem {R A M : Type} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] (I : Ideal R)
    {a : A} (ha : a ∈ I.map (algebraMap R A)) (y : M) : a • y ∈ (I • ⊤ : Submodule R M) := by
  unfold Ideal.map at ha
  induction ha using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨r, hr, rfl⟩ := hb
    rw [algebraMap_smul]
    exact Submodule.smul_mem_smul hr trivial
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add b c _ _ hb hc => rw [add_smul]; exact Submodule.add_mem _ hb hc
  | smul b c _ hc =>
    rw [smul_eq_mul, mul_smul]
    exact UpperTheory.V.AlgebraTools.tnAlg_smul_mem I b hc

private theorem UpperTheory.V.AlgebraTools.tnAlg_mem_radical {R A : Type} [CommRing R] [IsLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] {a : A}
    (ha : ∀ n : Ideal A, n.IsMaximal → a ∈ n) :
    a ∈ ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).radical := by
  haveI : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hle, hP⟩
  apply ha
  have hle' : IsLocalRing.maximalIdeal R ≤ Ideal.comap (algebraMap R A) P := by
    intro r hr
    rw [Ideal.mem_comap]
    exact hle (Ideal.mem_map_of_mem _ hr)
  have hne : Ideal.comap (algebraMap R A) P ≠ ⊤ := Ideal.comap_ne_top _ hP.ne_top
  have hc : Ideal.comap (algebraMap R A) P = IsLocalRing.maximalIdeal R :=
    ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hne hle').symm
  have hcm : (Ideal.comap (algebraMap R A) P).IsMaximal := by
    rw [hc]
    exact IsLocalRing.maximalIdeal.isMaximal R
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) P hcm

theorem UpperTheory.V.AlgebraTools.topNil_eq_idem :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (A κ : Type) [CommRing A] [Algebra R A] [Module.Finite R A] (t : κ → A),
      ∃ e : A, IsIdempotentElem e ∧ (∀ n : Ideal A, n.IsMaximal → (e ∉ n ↔ ∀ i, t i ∈ n)) ∧
        ∀ (M : Type) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Finite R M] (x : M),
          x ∈ topNil (IsLocalRing.maximalIdeal R) (fun i => (Algebra.lsmul R R M (t i) : Module.End R M)) ↔ e • x = x := by
  intro R _ _ _ _ A κ _ _ _ t
  haveI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_henselianRing R
  obtain ⟨e, he, hT⟩ := GlobalTheory.exists_idempotent_notMem_iff_mem_of_henselian R (S := A)
    {n : MaximalSpectrum A | ∀ i, t i ∈ n.asIdeal}
  have hmax : ∀ n : Ideal A, n.IsMaximal → (e ∉ n ↔ ∀ i, t i ∈ n) := fun n hn => hT ⟨n, hn⟩
  refine ⟨e, he, hmax, ?_⟩
  intro M _ _ _ _ _ x
  have hpow : ∀ (a : A) (r : ℕ) (y : M),
      ((Algebra.lsmul R R M a : Module.End R M) ^ r) y = a ^ r • y := by
    intro a r y
    rw [← map_pow, Algebra.lsmul_coe]
  rw [mem_topNil_iff_exists]
  simp only [hpow]
  set m := IsLocalRing.maximalIdeal R with hm
  have hA : ∀ j : ℕ, ∀ a : A, ∀ y ∈ (m ^ j • ⊤ : Submodule R M), a • y ∈ (m ^ j • ⊤ : Submodule R M) :=
    fun j a y hy => UpperTheory.V.AlgebraTools.tnAlg_smul_mem (m ^ j) a hy
  constructor
  · intro hx
    set y := x - e • x with hy
    have hey : e • y = 0 := by rw [hy, smul_sub, smul_smul, he.eq, sub_self]
    suffices y = 0 by rw [sub_eq_zero] at this; exact this.symm
    have hall : ∀ j : ℕ, y ∈ (m ^ j • ⊤ : Submodule R M) := by
      intro j
      let P : Submodule A M :=
        { carrier := (m ^ j • ⊤ : Submodule R M)
          add_mem' := fun ha hb => Submodule.add_mem _ ha hb
          zero_mem' := Submodule.zero_mem _
          smul_mem' := fun a _ hb => hA j a _ hb }
      let K : Ideal A := P.comap (LinearMap.toSpanSingleton A M y)
      have hKe : e ∈ K := by
        show e • y ∈ P
        rw [hey]
        exact P.zero_mem
      have hKt : ∀ i, t i ∈ K.radical := by
        intro i
        obtain ⟨r, hr⟩ := hx i j
        refine ⟨r, ?_⟩
        show t i ^ r • y ∈ (m ^ j • ⊤ : Submodule R M)
        rw [hy, smul_sub]
        refine Submodule.sub_mem _ hr ?_
        rw [smul_comm (t i ^ r) e x]
        exact hA j e _ hr
      have htop : K.radical = ⊤ := by
        by_contra hne
        obtain ⟨n, hn, hle⟩ := Ideal.exists_le_maximal _ hne
        exact ((hmax n hn).mpr (fun i => hle (hKt i))) (hle (Ideal.le_radical hKe))
      have h1 : (1 : A) ∈ K.radical := htop ▸ Submodule.mem_top
      obtain ⟨r, hr⟩ := h1
      have h2 : (1 : A) ^ r • y ∈ (m ^ j • ⊤ : Submodule R M) := hr
      rw [one_pow, one_smul] at h2
      exact h2
    have hbot := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) m
      (by rw [hm, IsLocalRing.ringJacobson_eq_maximalIdeal])
    have hyi : y ∈ (⨅ i, m ^ i • ⊤ : Submodule R M) := Submodule.mem_iInf _ |>.mpr hall
    rw [hbot] at hyi
    exact hyi
  · intro hx i j
    have hin : ∀ n : Ideal A, n.IsMaximal → t i * e ∈ n := by
      intro n hn
      by_cases h : e ∈ n
      · exact n.mul_mem_left _ h
      · exact n.mul_mem_right _ ((hmax n hn).mp h i)
    obtain ⟨N, hN⟩ := UpperTheory.V.AlgebraTools.tnAlg_mem_radical (R := R) hin
    refine ⟨N * j, ?_⟩
    have hex : ∀ k : ℕ, e ^ k • x = x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, mul_smul, hx, ih]
    have hmem : (t i * e) ^ (N * j) ∈ (m ^ j).map (algebraMap R A) := by
      rw [Ideal.map_pow, pow_mul]
      exact Ideal.pow_mem_pow hN j
    have h3 := UpperTheory.V.AlgebraTools.tnAlg_map_smul_mem (m ^ j) hmem x
    rwa [mul_pow, mul_smul, hex] at h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.FreeProf
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

open ProfiniteGrp ProfiniteGrp.ProfiniteCompletion CategoryTheory in
theorem UpperTheory.V.AlgebraTools.exists_free_profinite :
    ∀ r : ℕ, ∃ (P : Type) (_ : Group P) (_ : TopologicalSpace P) (_ : IsTopologicalGroup P) (_ : CompactSpace P)
      (_ : TotallyDisconnectedSpace P) (x : Fin r → P), TopGen (Set.range x) ∧
        ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (y : Fin r → G), ∃ f : P →* G, Continuous f ∧ ∀ i, f (x i) = y i := by
  intro r
  let F : GrpCat.{0} := GrpCat.of (FreeGroup (Fin r))
  let P : ProfiniteGrp.{0} := completion F
  let η : FreeGroup (Fin r) →* P := (eta F).hom
  refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun i => η (FreeGroup.of i), ?_, ?_⟩
  · unfold TopGen
    have hr : Set.range (fun i => η (FreeGroup.of i)) = η '' Set.range FreeGroup.of := by
      rw [← Set.range_comp]
      rfl
    rw [hr, ← MonoidHom.map_closure, FreeGroup.closure_range_of, ← MonoidHom.range_eq_map,
      MonoidHom.coe_range]
    exact denseRange (G := F)
  · intro G _ _ _ _ _ y
    let Q : ProfiniteGrp.{0} := ProfiniteGrp.of G
    let f0 : F ⟶ GrpCat.of Q := GrpCat.ofHom (FreeGroup.lift y)
    let L : P ⟶ Q := lift f0
    refine ⟨L.hom.toMonoidHom, L.hom.continuous, ?_⟩
    intro i
    have h : ((eta F) ≫ (forget₂ ProfiniteGrp GrpCat).map L).hom (FreeGroup.of i) =
        f0.hom (FreeGroup.of i) := by
      rw [lift_eta]
    exact h.trans FreeGroup.lift_apply_of
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.GenExt
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.exists_surj_over_finite :
    ∀ (P Γ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P] [TotallyDisconnectedSpace P] [Group Γ] (r h : ℕ) (x : Fin (r + h) → P) (γ : Fin r → Γ) (π : P →* Γ), TopGen (Set.range x) →
      (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (y : Fin (r + h) → G), ∃ f : P →* G, Continuous f ∧ ∀ i, f (x i) = y i) →
      Function.Surjective γ → IsOpen (π.ker : Set P) → (∀ i, π (x (Fin.castAdd h i)) = γ i) → (∀ i, π (x (Fin.natAdd r i)) = 1) →
      ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (q : G →* Γ), IsOpen (q.ker : Set G) → ∀ g : Fin r → G, (∀ i, q (g i) = γ i) →
        (∃ z : Fin h → q.ker, TopGen (Set.range z)) →
        ∃ f : P →* G, Continuous f ∧ Function.Surjective f ∧ q.comp f = π ∧ ∀ i, f (x (Fin.castAdd h i)) = g i := by
  intro P Γ _ _ _ _ _ _ r h x γ π hden huniv hγ hπo hπl hπr G _ _ _ _ _ q hqo g hg hz
  obtain ⟨z, hzd⟩ := hz
  obtain ⟨f, hf, hfx⟩ := huniv G (Fin.append g (fun j => (z j : G)))
  have hfl : ∀ i, f (x (Fin.castAdd h i)) = g i := fun i => by
    rw [hfx, Fin.append_left]
  have hfr : ∀ j, f (x (Fin.natAdd r j)) = z j := fun j => by
    rw [hfx, Fin.append_right]
  refine ⟨f, hf, ?_, ?_, hfl⟩
  · haveI : T2Space G := inferInstance
    have hRc : IsClosed (Set.range f) := (isCompact_range hf).isClosed
    have hker : ∀ k : q.ker, (k : G) ∈ Set.range f := by
      let S : Set q.ker := Subtype.val ⁻¹' Set.range f
      have hSc : IsClosed S := hRc.preimage continuous_subtype_val
      have hsub : ((Subgroup.closure (Set.range z) : Subgroup q.ker) : Set q.ker) ⊆ S := by
        have : Subgroup.closure (Set.range z) ≤ f.range.comap q.ker.subtype := by
          rw [Subgroup.closure_le]
          rintro _ ⟨j, rfl⟩
          exact ⟨x (Fin.natAdd r j), hfr j⟩
        intro a ha
        exact this ha
      have hdS : Dense S := hzd.mono hsub
      intro k
      have : k ∈ S := by
        rw [← hSc.closure_eq, hdS.closure_eq]
        trivial
      exact this
    intro a
    obtain ⟨i, hi⟩ := hγ (q a)
    have hmem : (g i)⁻¹ * a ∈ q.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hg i, hi, inv_mul_cancel]
    obtain ⟨p1, hp1⟩ := hker ⟨_, hmem⟩
    refine ⟨x (Fin.castAdd h i) * p1, ?_⟩
    rw [map_mul, hfl, hp1]
    simp
  · set φ := q.comp f with hφ
    have hgen : Set.EqOn φ π (Set.range x) := by
      rintro _ ⟨k, rfl⟩
      induction k using Fin.addCases with
      | left i => simp [hφ, hfl, hg, hπl]
      | right j =>
        simp only [hφ, MonoidHom.comp_apply, hfr, hπr]
        exact (z j).2
    have hcl : Set.EqOn φ π (Subgroup.closure (Set.range x)) := MonoidHom.eqOn_closure hgen
    have hφo : IsOpen (φ.ker : Set P) := by
      have : (φ.ker : Set P) = f ⁻¹' (q.ker : Set G) := by
        ext a
        simp [hφ]
      rw [this]
      exact hqo.preimage hf
    ext p
    let V : Set P := (fun a => p⁻¹ * a) ⁻¹' ((π.ker : Set P) ∩ (φ.ker : Set P))
    have hVo : IsOpen V := (hπo.inter hφo).preimage (continuous_const.mul continuous_id)
    have hpV : p ∈ V := by
      simp [V]
    obtain ⟨d, ⟨hd1, hd2⟩, hdD⟩ := hden.inter_open_nonempty V hVo ⟨p, hpV⟩
    have e1 : π (p⁻¹ * d) = 1 := hd1
    have e2 : φ (p⁻¹ * d) = 1 := hd2
    rw [map_mul, map_inv, inv_mul_eq_one] at e1 e2
    rw [e2, hcl hdD, ← e1]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ResNormal
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem pq_iff (l : ℕ) (G : Type) [Group G] (N : Subgroup G) [N.Normal] :
    IsPGroup l (G ⧸ N) ↔ ∀ g : G, ∃ k : ℕ, g ^ l ^ k ∈ N := by
  refine ⟨fun h g => ?_, fun h x => ?_⟩
  · obtain ⟨k, hk⟩ := h (g : G ⧸ N)
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hk⟩
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h g
    exact ⟨k, by rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]⟩

private theorem res_map (l : ℕ) (G : Type) [Group G] [TopologicalSpace G] (f : G →* G)
    (hf : Continuous f) {x : G} (hx : x ∈ proLRes l G) : f x ∈ proLRes l G := by
  rw [mem_proLRes] at hx ⊢
  intro N hN
  let M : OpenNormalSubgroup G :=
    { toSubgroup := (N.toOpenSubgroup : Subgroup G).comap f
      isOpen' := N.toOpenSubgroup.isOpen.preimage hf
      isNormal' := Subgroup.Normal.comap inferInstance f }
  have hM : IsPGroup l (G ⧸ (M.toOpenSubgroup : Subgroup G)) := by
    rw [pq_iff] at hN ⊢
    intro g
    obtain ⟨k, hk⟩ := hN (f g)
    exact ⟨k, by simpa [M, map_pow] using hk⟩
  have := hx M hM
  simpa [M] using this

private theorem res_pow (l : ℕ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (K : Subgroup G) (hK : IsOpen (K : Set G)) (h : proLRes l G ≤ K) (g : G) :
    ∃ k : ℕ, g ^ l ^ k ∈ K := by
  classical
  let ι := {N : OpenNormalSubgroup G // IsPGroup l (G ⧸ (N.toOpenSubgroup : Subgroup G))}
  let t : ι → Set G := fun i => ((i.1.toOpenSubgroup : Subgroup G) : Set G)
  have ht : ∀ i, IsClosed (t i) := fun i => i.1.toOpenSubgroup.isClosed
  have hs : IsCompact ((K : Set G)ᶜ) := (hK.isClosed_compl).isCompact
  have hdisjoint : Disjoint (K : Set G)ᶜ (⋂ i, t i) := by
    simp only [Set.disjoint_left, Set.mem_compl_iff, Set.mem_iInter]
    intro y hy hall
    apply hy
    apply h
    rw [mem_proLRes]
    intro N hN
    exact hall ⟨N, hN⟩
  obtain ⟨u, hu⟩ := hs.elim_finite_subfamily_closed t ht hdisjoint
  have hk : ∀ i : ι, ∃ k : ℕ, g ^ l ^ k ∈ (i.1.toOpenSubgroup : Subgroup G) := fun i =>
    (pq_iff l G _).mp i.2 g
  choose kf hkf using hk
  refine ⟨∑ i ∈ u, kf i, ?_⟩
  by_contra hg
  apply Set.disjoint_left.mp hu hg
  simp only [Set.mem_iInter]
  intro i hi
  have hle : kf i ≤ ∑ j ∈ u, kf j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  have heq : l ^ (∑ j ∈ u, kf j) = l ^ kf i * l ^ (∑ j ∈ u, kf j - kf i) := by
    rw [← pow_add, Nat.add_sub_cancel' hle]
  show g ^ l ^ (∑ j ∈ u, kf j) ∈ ((i.1.toOpenSubgroup : Subgroup G) : Set G)
  rw [heq, pow_mul]
  exact Subgroup.pow_mem _ (hkf i) _

theorem UpperTheory.V.AlgebraTools.proLResOf_normal :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (H : Subgroup G) [H.Normal], IsClosed (H : Set G) →
      (proLResOf l H).Normal ∧ IsClosed (proLResOf l H : Set G) ∧ proLResOf l H ≤ H ∧
      ∀ (O : OpenNormalSubgroup G), proLResOf l H ≤ O.toSubgroup → ∀ h ∈ H, ∃ k : ℕ, h ^ l ^ k ∈ O.toSubgroup := by
  intro l _ G _ _ _ _ _ H _ hH
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    intro x hx g
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    let c : H →* H := (MulAut.conjNormal g).toMonoidHom
    have hc : Continuous c := by
      apply Continuous.subtype_mk
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const
    have := res_map l H c hc hy
    refine Subgroup.mem_map.mpr ⟨c y, this, ?_⟩
    simp [c, MulAut.conjNormal_apply]
  · unfold proLResOf
    rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact hH.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_proLRes l H)
  · exact Subgroup.map_subtype_le _
  · intro O hO h hh
    have hle : proLRes l H ≤ (O.toOpenSubgroup : Subgroup G).comap H.subtype :=
      Subgroup.map_le_iff_le_comap.mp hO
    have hopen : IsOpen (((O.toOpenSubgroup : Subgroup G).comap H.subtype : Subgroup H) : Set H) :=
      O.toOpenSubgroup.isOpen.preimage continuous_subtype_val
    obtain ⟨k, hk⟩ := res_pow l H _ hopen hle ⟨h, hh⟩
    exact ⟨k, hk⟩
end
