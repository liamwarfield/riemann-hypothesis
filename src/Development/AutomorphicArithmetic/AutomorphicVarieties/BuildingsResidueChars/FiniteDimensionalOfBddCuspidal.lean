module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsAutomorphicFormOfBddSubmodule
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.TypePoly

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsBasisAlgModLaplacianOfTypesCentre
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModBotCompactCasimirOfTypes
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable def slc {K : Type} [Field K] [NumberField K] {n : ℕ} (g : AdelicGLn.AdelicGL K n) :
    archSmooth K n →ₗ[ℂ] (archCompact K n → ℂ) where
  toFun φ k := φ.1 (g * infEmb K n k.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem slc_op {K : Type} [Field K] [NumberField K] {n : ℕ} (X : (isExpLieAlgebra K n).lieSubalgebra)
    (hX : ∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X) ∈ archCompact K n) :
    (∃ D : Module.End ℂ (archCompact K n → ℂ), ∀ g φ,
      D (slc g φ) = slc g (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ)) ∧
    ∀ (V : Submodule ℂ (archCompact K n → ℂ)), FiniteDimensional ℂ V → (∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) →
      ∀ g φ, slc g φ ∈ V → slc g (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ) ∈ V := by
  let γ : ℝ → archCompact K n := fun t =>
    ⟨(isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X), hX t⟩
  have F : ∀ (g : AdelicGLn.AdelicGL K n) (φ : archSmooth K n) (k : archCompact K n),
      HasDerivAt (fun t => slc g φ (k * γ t)) (slc g (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ) k) 0 := by
    intro g φ k
    have d := (isExpLieAlgebra K n).hasDerivAt_rightDeriv
      ((show IsArchSmooth φ.1 from φ.2) (g * infEmb K n k.1)) ((isExpLieAlgebra K n).ofLie X) 1
    show HasDerivAt _ ((uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ).1 (g * infEmb K n k.1)) 0
    rw [uAction_ι_apply]
    have e : (fun t => slc g φ (k * γ t)) = fun t => archSlice φ.1 (g * infEmb K n k.1)
        (1 * (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X)) := by
      funext t
      simp only [slc, LinearMap.coe_mk, AddHom.coe_mk, archSlice_apply, one_mul, Subgroup.coe_mul, map_mul,
        mul_assoc]
      rfl
    rw [e]
    exact d
  let P : Submodule ℂ (archCompact K n → ℂ) :=
    { carrier := {f | ∀ k, DifferentiableAt ℝ (fun t => f (k * γ t)) 0}
      add_mem' := fun ha hb k => (ha k).add (hb k)
      zero_mem' := fun _ => differentiableAt_const _
      smul_mem' := fun c _ hf k => (hf k).const_smul c }
  let D₀ : P →ₗ[ℂ] (archCompact K n → ℂ) :=
    { toFun := fun f k => deriv (fun t => f.1 (k * γ t)) 0
      map_add' := fun f h => by
        funext k
        show deriv (fun t => f.1 (k * γ t) + h.1 (k * γ t)) 0 = _
        exact deriv_add (f.2 k) (h.2 k)
      map_smul' := fun c f => by
        funext k
        show deriv (fun t => c • f.1 (k * γ t)) 0 = _
        exact deriv_const_smul c (f.2 k) }
  obtain ⟨D, hD⟩ := LinearMap.exists_extend D₀
  refine ⟨⟨D, fun g φ => ?_⟩, fun V hV hVs g φ hφ => ?_⟩
  · have hm : slc g φ ∈ P := fun k => (F g φ k).differentiableAt
    have h1 := congrArg (fun L => L ⟨slc g φ, hm⟩) hD
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1]
    funext k
    exact (F g φ k).deriv
  · haveI := hV
    exact mem_of_hasDerivAt V (c := fun t k => slc g φ (k * γ t)) (fun t => hVs _ hφ (γ t)) (fun k => F g φ k)

theorem UpperTheory.algMod_bot_compact_casimir_of_types :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Types S → ∀ (ι : Type) [Fintype ι] (X : ι → (isExpLieAlgebra K n).lieSubalgebra) (c : ι → ℝ), (∀ i, c i = 0 ∨ ∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (X i)) ∈ archCompact K n) → AlgMod S ⊥ (uAction (∑ i, c i • (UniversalEnvelopingAlgebra.ι ℝ (X i) * UniversalEnvelopingAlgebra.ι ℝ (X i)))) := by
  intro K _ _ n S hS ι _ X c hc
  obtain ⟨V, hV, hVs, hSV⟩ := hS
  have hi : ∀ i, ∃ Di : Module.End ℂ (archCompact K n → ℂ), ∀ g φ,
      c i • Di (Di (slc g φ)) = slc g (c i • uAction (UniversalEnvelopingAlgebra.ι ℝ (X i))
        (uAction (UniversalEnvelopingAlgebra.ι ℝ (X i)) φ)) := by
    intro i
    rcases hc i with h0 | hX
    · exact ⟨0, fun g φ => by simp [h0]⟩
    · obtain ⟨D, hD⟩ := (slc_op (X i) hX).1
      exact ⟨D, fun g φ => by rw [hD, hD, LinearMap.map_smul_of_tower]⟩
  choose Di hDi using hi
  have e1 : ∀ φ : archSmooth K n, uAction (∑ i, c i • (UniversalEnvelopingAlgebra.ι ℝ (X i) *
      UniversalEnvelopingAlgebra.ι ℝ (X i))) φ = ∑ i, c i • uAction (UniversalEnvelopingAlgebra.ι ℝ (X i))
        (uAction (UniversalEnvelopingAlgebra.ι ℝ (X i)) φ) := by
    intro φ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_mul, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  have hinter : ∀ g φ, (∑ i, c i • (Di i * Di i)) (slc g φ) = slc g (uAction (∑ i, c i •
      (UniversalEnvelopingAlgebra.ι ℝ (X i) * UniversalEnvelopingAlgebra.ι ℝ (X i))) φ) := by
    intro g φ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    exact Finset.sum_congr rfl fun i _ => hDi i g φ
  have hstab : ∀ φ ∈ (⨅ g, V.comap (slc g)), uAction (∑ i, c i •
      (UniversalEnvelopingAlgebra.ι ℝ (X i) * UniversalEnvelopingAlgebra.ι ℝ (X i))) φ ∈ (⨅ g, V.comap (slc g)) := by
    intro φ hφ
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hφ ⊢
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    refine V.sum_mem fun i _ => ?_
    rw [LinearMap.map_smul_of_tower]
    rcases hc i with h0 | hX
    · rw [h0, zero_smul]
      exact V.zero_mem
    · exact V.smul_of_tower_mem _ ((slc_op (X i) hX).2 V hV hVs g _ ((slc_op (X i) hX).2 V hV hVs g φ (hφ g)))
  have hinV : ∀ g, ∀ φ ∈ (⨅ g, V.comap (slc g)), slc g φ ∈ V := by
    intro g φ hφ
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hφ
    exact hφ g
  obtain ⟨q, hq, -, hq0⟩ := UpperTheory.V.Af.CuspFin.polySlices (archSmooth K n) (archCompact K n → ℂ)
    (AdelicGLn.AdelicGL K n) _ _ (fun g => slc g) hinter V hV _ hstab hinV
  refine ⟨q, hq, fun φ hφ => ?_⟩
  rw [Submodule.mem_bot]
  have hN : φ ∈ (⨅ g, V.comap (slc g)) := by
    simp only [Submodule.mem_iInf, Submodule.mem_comap]
    exact fun g => hSV φ hφ g
  apply Subtype.ext
  funext g
  have h1 := congrFun (hq0 g φ hN) 1
  simpa [slc] using h1
end

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem algMod_add {M : Type} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (A B : Module.End ℂ M)
    (hAB : A * B = B * A) (hA : AlgMod S ⊥ A) (hB : AlgMod S ⊥ B) : AlgMod S ⊥ (A + B) := by
  refine UpperTheory.algMod_bot_of_mem_adjoin_commuting M S {A, B} ?_ ?_ (A + B)
    (Subalgebra.add_mem _ (Algebra.subset_adjoin (by simp)) (Algebra.subset_adjoin (by simp)))
  · intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first | rfl | exact hAB | exact hAB.symm
  · intro T hT
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hT
    rcases hT with rfl | rfl <;> assumption

theorem UpperTheory.exists_basis_algMod_laplacian_of_types_centre :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Types S → Centre S → ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra), AlgMod S ⊥ (uAction (laplacianU K n b)) := by
  intro K _ _ n S hT hC
  obtain ⟨d, b, ε, B, hε, horth, hsymm, hinv, hK⟩ := exists_archCartanData K n
  refine ⟨d, b, ?_⟩
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  have hΩ : casimir b ε ∈ (isExpLieAlgebra K n).centerU := casimir_mem_center hε2 horth hsymm hinv
  rw [laplacianU_eq_casimir_add b ε, map_add (f := _)]
  refine algMod_add S _ _ (Zc_comm_uAction (uAction_mem_Zc hΩ) _).eq (hC _ hΩ) ?_
  refine UpperTheory.algMod_bot_compact_casimir_of_types K n S hT (Fin d) (fun i => b i) (fun i => 1 - ε i) fun i => ?_
  rcases hε i with e | e
  · exact Or.inl (by rw [e, sub_self])
  · exact Or.inr (hK i e)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalInfKerAevalMonic
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem aeval_preserves_invariant_submodule {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M)
    (N : Submodule ℂ M) (hN : ∀ x ∈ N, T x ∈ N) (p : Polynomial ℂ) :
    ∀ x ∈ N, Polynomial.aeval T p x ∈ N := by
  intro x hx
  have hpow : ∀ n : ℕ, ∀ y ∈ N, (T ^ n) y ∈ N := by
    intro n
    induction n with
    | zero =>
      intro y hy
      simpa using hy
    | succ n ih =>
      intro y hy
      rw [pow_succ', Module.End.mul_apply]
      exact hN _ (ih y hy)
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), LinearMap.add_apply]
    exact N.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact N.smul_mem a (hpow n x hx)

theorem UpperTheory.finiteDimensional_inf_ker_aeval_monic :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (N : Submodule ℂ M), (∀ x ∈ N, T x ∈ N) → (∀ c : ℂ, FiniteDimensional ℂ ↥(N ⊓ T.eigenspace c)) → ∀ p : Polynomial ℂ, p.Monic → FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (Polynomial.aeval T p)) := by
  intro M _ _ T N hN hE p hp
  have key : ∀ s : Multiset ℂ, FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker
      (Polynomial.aeval T (s.map (fun a => Polynomial.X - Polynomial.C a)).prod)) := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      rw [Multiset.map_zero, Multiset.prod_zero, map_one]
      have h1 : LinearMap.ker (1 : Module.End ℂ M) = ⊥ := LinearMap.ker_id
      rw [h1, inf_bot_eq]
      infer_instance
    | cons a s ih =>
      set q := (s.map (fun a => Polynomial.X - Polynomial.C a)).prod with hq
      rw [Multiset.map_cons, Multiset.prod_cons]
      rw [← Submodule.fg_iff_finiteDimensional] at ih ⊢
      apply Submodule.fg_of_fg_map_of_fg_inf_ker (f := Polynomial.aeval T q)
      · have hle : (N ⊓ LinearMap.ker (Polynomial.aeval T ((Polynomial.X - Polynomial.C a) * q))).map
            (Polynomial.aeval T q) ≤ N ⊓ T.eigenspace a := by
          rintro _ ⟨x, ⟨hxN, hxk⟩, rfl⟩
          refine ⟨aeval_preserves_invariant_submodule T N hN q x hxN, ?_⟩
          show _ ∈ T.eigenspace a
          rw [Module.End.mem_eigenspace_iff]
          change x ∈ LinearMap.ker _ at hxk
          rw [LinearMap.mem_ker, map_mul, Module.End.mul_apply, map_sub, Polynomial.aeval_X,
            Polynomial.aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at hxk
          exact hxk
        haveI := hE a
        rw [Submodule.fg_iff_finiteDimensional]
        exact Submodule.finiteDimensional_of_le hle
      · apply Submodule.FG.of_le ih
        rintro x ⟨⟨hxN, -⟩, hxq⟩
        exact ⟨hxN, hxq⟩
  have hsplit := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp IsAlgClosed.card_roots_eq_natDegree
  rw [← hsplit]
  exact key p.roots
end

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.finiteDimensional_of_bdd_cuspidal :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Bdd S → (∀ φ ∈ S, IsCuspidal φ.1) → FiniteDimensional ℂ S := by
  intro K _ _ n S hS hcusp
  classical
  have hle : cuspForms K n ≤ archSmooth K n :=
    cuspForms_le_automorphicForms.trans automorphicForms_le_archSmooth
  let j : cuspForms K n →ₗ[ℂ] archSmooth K n := Submodule.inclusion hle
  have hj : Function.Injective j := Submodule.inclusion_injective hle
  have hju : ∀ (u : UEnv K n) (ψ : cuspForms K n), j (uActionCusp K n u ψ) = uAction u (j ψ) :=
    fun u ψ => rfl
  have hjf : ∀ (h : AdelicGLn.FiniteAdelicGL K n) (ψ : cuspForms K n),
      j (finRepCusp K n h ψ) = rtFin h (j ψ) := fun h ψ => rfl
  obtain ⟨d, b, P, hPm, hP⟩ := UpperTheory.exists_basis_algMod_laplacian_of_types_centre K n S hS.types hS.centre
  set Z := UnitaryAdmissible.centralZ K n with hZdef
  have hZc : UniversalEnvelopingAlgebra.ι ℝ Z ∈ (isExpLieAlgebra K n).centerU := by
    apply mem_center_of_forall_ι_commute
    intro x
    have h1 := UnitaryAdmissible.lie_centralZ (K := K) (n := n) x
    have h2 : UniversalEnvelopingAlgebra.ι ℝ ⁅Z, x⁆ = UniversalEnvelopingAlgebra.ι ℝ Z * UniversalEnvelopingAlgebra.ι ℝ x - UniversalEnvelopingAlgebra.ι ℝ x * UniversalEnvelopingAlgebra.ι ℝ Z := by
      rw [LieHom.map_lie, Ring.lie_def]
    rw [h1, map_zero] at h2
    exact (sub_eq_zero.mp h2.symm).symm
  obtain ⟨Q, hQm, hQ⟩ := hS.centre _ hZc
  obtain ⟨L, hLo, hL⟩ := hS.level
  let U : Subgroup (AdelicGLn.integralFiniteGL K n) := L.subgroupOf _
  have hUo : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) := hLo.preimage continuous_subtype_val
  have hP'm : (Polynomial.X * P).Monic := Polynomial.monic_X.mul hPm
  have hP'd : 0 < (Polynomial.X * P).natDegree := by
    rw [Polynomial.Monic.natDegree_mul Polynomial.monic_X hPm, Polynomial.natDegree_X]
    omega
  let N : Submodule ℂ (cuspForms K n) :=
    LinearMap.ker (Polynomial.aeval (uActionCusp K n (laplacianU K n b)) (Polynomial.X * P)) ⊓
      ⨅ u : U, LinearMap.ker (finRepCusp K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) - LinearMap.id)
  have hmemN : ∀ ψ, ψ ∈ N ↔ Polynomial.aeval (uActionCusp K n (laplacianU K n b)) (Polynomial.X * P) ψ = 0 ∧
      ∀ u : U, finRepCusp K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) ψ = ψ := by
    intro ψ
    simp only [N, Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_iInf, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
  have hTA : ∀ m, uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) (uActionCusp K n (laplacianU K n b) m) =
      uActionCusp K n (laplacianU K n b) (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) m) := by
    intro m
    have hc := (Subalgebra.mem_center_iff.mp hZc) (laplacianU K n b)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hc]
  have hTf : ∀ (h : AdelicGLn.FiniteAdelicGL K n) m,
      uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) (finRepCusp K n h m) =
        finRepCusp K n h (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) m) := by
    intro h m
    apply hj
    rw [hju, hjf, hjf, hju, uAction_rtFin]
  have hTN : ∀ x ∈ N, uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z) x ∈ N := by
    intro x hx
    rw [hmemN] at hx ⊢
    refine ⟨?_, fun u => ?_⟩
    · rw [← map_aeval_apply_of_intertwine _ hTA, hx.1, map_zero]
    · rw [← hTf, hx.2 u]
  have hE : ∀ c : ℂ, FiniteDimensional ℂ ↥(N ⊓ (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z)).eigenspace c) := by
    intro c
    refine UnitaryAdmissible.finiteDimensional_of_eigen b _ hP'm hP'd c U hUo _ ?_
    intro φ hφ
    rw [Submodule.mem_inf, hmemN, Module.End.mem_eigenspace_iff] at hφ
    exact ⟨hφ.1.1, hφ.2, fun u hu => hφ.1.2 ⟨u, hu⟩⟩
  have hfin := UpperTheory.finiteDimensional_inf_ker_aeval_monic _ _ N hTN hE Q hQm
  refine Submodule.finiteDimensional_of_le (S₂ := (N ⊓ LinearMap.ker (Polynomial.aeval
    (uActionCusp K n (UniversalEnvelopingAlgebra.ι ℝ Z)) Q)).map j) ?_
  intro φ hφ
  have hφc : (φ : AdelicGLn.AdelicGL K n → ℂ) ∈ cuspForms K n :=
    ⟨UpperTheory.isAutomorphicForm_of_bdd_submodule K n S hS φ hφ, hcusp φ hφ⟩
  have hjψ : j ⟨φ.1, hφc⟩ = φ := rfl
  refine ⟨⟨φ.1, hφc⟩, ?_, hjψ⟩
  refine Submodule.mem_inf.mpr ⟨(hmemN _).mpr ⟨?_, fun u => ?_⟩, ?_⟩
  · apply hj
    rw [map_zero, map_aeval_apply_of_intertwine j (hju _), hjψ, map_mul, Polynomial.aeval_X,
      Module.End.mul_apply, (Submodule.mem_bot ℂ).mp (hP φ hφ), map_zero]
  · apply hj
    rw [hjf, hjψ]
    apply Subtype.ext
    funext g
    exact hL φ hφ _ (Subgroup.mem_subgroupOf.mp u.2) g
  · rw [LinearMap.mem_ker]
    apply hj
    rw [map_zero, map_aeval_apply_of_intertwine j (hju _), hjψ]
    exact (Submodule.mem_bot ℂ).mp (hQ φ hφ)
