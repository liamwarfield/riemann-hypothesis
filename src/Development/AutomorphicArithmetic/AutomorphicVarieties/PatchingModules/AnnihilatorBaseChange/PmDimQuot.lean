module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpRoots
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplModfree
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FlatnessPrecompleteProducts
open IsLocalRing TensorProduct

namespace UpperTheory.Reformulated.B.FlatnessPrecompleteProducts

open UpperTheory.V.AlgebraTools

private lemma mem_smul_top_pi {L : Type} [CommRing L] (I : Ideal L) {n : ℕ} (x : Fin n → L) :
    x ∈ (I • ⊤ : Submodule L (Fin n → L)) ↔ ∀ i, x i ∈ I := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on (p := fun y : Fin n → L => y i ∈ I) hx ?_ ?_
    · intro r hr y _
      exact I.mul_mem_right _ hr
    · intro y z hy hz
      exact I.add_mem hy hz
  · intro h
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

private lemma precomplete_pi {L : Type} [CommRing L] (I : Ideal L) [IsPrecomplete I L] (n : ℕ) :
    IsPrecomplete I (Fin n → L) := by
  refine ⟨fun f hf => ?_⟩
  have h : ∀ i, ∃ x : L, ∀ k, f k i ≡ x [SMOD (I ^ k • ⊤ : Submodule L L)] := by
    intro i
    refine IsPrecomplete.prec' (fun k => f k i) ?_
    intro a b hab
    have := (mem_smul_top_pi _ _).1 (SModEq.sub_mem.1 (hf hab)) i
    rw [SModEq.sub_mem]
    simpa using this
  choose x hx using h
  refine ⟨x, fun k => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  simpa using SModEq.sub_mem.1 (hx i k)

private lemma map_eq_max {R : Type} [CommRing R] {q : Ideal R} {B : Type} [CommRing B]
    [IsLocalRing B] [Algebra R B] (h : IsCplAt R q B) :
    q.map (algebraMap R B) = maximalIdeal B := by
  have := h.noeth
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, h.comap_eq]
  · apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal B)
      (IsNoetherian.noetherian _) (maximalIdeal_le_jacobson _)
    intro x hx
    obtain ⟨a, s, hs, hsa⟩ := h.dense 2 x
    have hu : IsUnit (algebraMap R B s) := by
      by_contra hn
      apply hs
      rw [← h.comap_eq]
      exact hn
    have ha : a ∈ q := by
      rw [← h.comap_eq, Ideal.mem_comap]
      have h1 := Ideal.pow_le_self (two_ne_zero) hsa
      have h2 := (maximalIdeal B).sub_mem (Ideal.mul_mem_left _ (algebraMap R B s) hx) h1
      simpa using h2
    rw [← Ideal.unit_mul_mem_iff_mem _ hu]
    have : algebraMap R B s * x = algebraMap R B a + (algebraMap R B s * x - algebraMap R B a) := by
      ring
    rw [this]
    refine Submodule.add_mem_sup (Ideal.mem_map_of_mem _ ha) ?_
    rwa [smul_eq_mul, ← pow_two]

private lemma flat_of_isCplAt {R : Type} [CommRing R] [IsNoetherianRing R] {q : Ideal R}
    {B : Type} [CommRing B] [IsLocalRing B] [Algebra R B] (h : IsCplAt R q B) :
    Module.Flat R B := by
  have := h.isPrime
  have := h.complete
  have hu : ∀ s : q.primeCompl, IsUnit (algebraMap R B s) := by
    intro s
    by_contra hn
    apply s.2
    have : (s : R) ∈ (maximalIdeal B).comap (algebraMap R B) := hn
    rwa [h.comap_eq] at this
  let S := Localization.AtPrime q
  letI : Algebra S B := (IsLocalization.lift (M := q.primeCompl) hu).toAlgebra
  haveI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.lift_eq (M := q.primeCompl) hu x).symm
  have hm : (maximalIdeal S).map (algebraMap S B) = maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      map_eq_max h]
  have hmem : ∀ (n : ℕ) (b : B),
      b ∈ (maximalIdeal S ^ n • ⊤ : Submodule S B) ↔ b ∈ maximalIdeal B ^ n := by
    intro n b
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow, hm]
  haveI : IsAdicComplete (maximalIdeal S) B :=
    { toIsHausdorff := (IsHausdorff.map_algebraMap_iff (S := B)).1 (by rw [hm]; infer_instance)
      toIsPrecomplete := (IsPrecomplete.map_algebraMap_iff (S := B)).1 (by rw [hm]; infer_instance) }
  have hsurj : Function.Surjective
      (AdicCompletion.map (maximalIdeal S) (Algebra.linearMap S B)) := by
    apply AdicCompletion.map_surjective_of_mkQ_comp_surjective
    intro y
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨a, s, hs, hsa⟩ := h.dense 1 b
    refine ⟨IsLocalization.mk' S a (⟨s, hs⟩ : q.primeCompl), ?_⟩
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, Algebra.linearMap_apply]
    rw [eq_comm, Submodule.Quotient.eq, ← pow_one (maximalIdeal S), hmem,
      ← Ideal.unit_mul_mem_iff_mem _ (hu ⟨s, hs⟩), mul_sub]
    have : algebraMap R B s * algebraMap S B (IsLocalization.mk' S a (⟨s, hs⟩ : q.primeCompl))
        = algebraMap R B a := by
      rw [IsScalarTower.algebraMap_apply R S B s, ← map_mul,
        IsLocalization.mk'_spec' S a (⟨s, hs⟩ : q.primeCompl), ← IsScalarTower.algebraMap_apply]
    rw [this]
    exact hsa
  have hinj : Function.Injective
      (AdicCompletion.map (maximalIdeal S) (Algebra.linearMap S B)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    ext n
    have h1 := AdicCompletion.map_val_apply (maximalIdeal S) (Algebra.linearMap S B) (n := n) x
    rw [hx] at h1
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x.1 n)
    rw [← hy] at h1 ⊢
    have h2 : algebraMap S B y ∈ maximalIdeal B ^ n := by
      rw [← hmem, ← Submodule.Quotient.mk_eq_zero]
      exact h1.symm
    change _ = (0 : S ⧸ (maximalIdeal S ^ n • ⊤ : Submodule S S))
    rw [Submodule.Quotient.mk_eq_zero]
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl y
    have h3 : algebraMap R B a ∈ maximalIdeal B ^ n := by
      rw [IsScalarTower.algebraMap_apply R S B a, ← IsLocalization.mk'_spec' S a t, map_mul]
      exact Ideal.mul_mem_left _ _ h2
    obtain ⟨s, hs, hsa⟩ := h.strict n a h3
    rw [smul_eq_mul, Ideal.mul_top, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    exact (IsLocalization.mk'_mem_map_algebraMap_iff q.primeCompl S _ _ _).2 ⟨s, hs, hsa⟩
  let e : AdicCompletion (maximalIdeal S) S ≃ₗ[S] B :=
    ((LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).restrictScalars S).trans
      (AdicCompletion.ofLinearEquiv (maximalIdeal S) B).symm
  haveI : Module.Flat S B := Module.Flat.of_linearEquiv e.symm
  haveI : Module.Flat R S := IsLocalization.flat S q.primeCompl
  exact Module.Flat.trans R S B

private lemma smul_mem_of_dense {L R B W : Type} [CommRing L] [CommRing R] [CommRing B]
    [IsLocalRing B] [Algebra L B] [Algebra R B] [AddCommGroup W] [Module L W] [Module B W]
    [IsScalarTower L B W] [IsHausdorff (maximalIdeal B) W]
    (hd : ∀ (n : ℕ) (b : B), ∃ a s : R, IsUnit (algebraMap R B s) ∧
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n)
    (V : Submodule L W) [IsArtinian L V] (hV : ∀ (r : R), ∀ v ∈ V, algebraMap R B r • v ∈ V)
    (b : B) (v : W) (hv : v ∈ V) : b • v ∈ V := by
  have h1 : ∀ n : ℕ, ∃ w ∈ V, b • v - w ∈ (maximalIdeal B ^ n • ⊤ : Submodule B W) := by
    intro n
    obtain ⟨a, s, hs, hsa⟩ := hd n b
    let f : V →ₗ[L] V := ((LinearMap.lsmul B W (algebraMap R B s)).restrictScalars L).restrict
      (hV s)
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have : algebraMap R B s • (x : W) = algebraMap R B s • (y : W) := congrArg Subtype.val hxy
      exact (hs.smul_left_cancel).1 this
    obtain ⟨w, hw⟩ := IsArtinian.surjective_of_injective_endomorphism f hf ⟨_, hV a v hv⟩
    have hw' : algebraMap R B s • (w : W) = algebraMap R B a • v := congrArg Subtype.val hw
    refine ⟨w, w.2, ?_⟩
    rw [← Submodule.smul_mem_iff_of_isUnit _ hs, smul_sub, hw', smul_smul, ← sub_smul]
    exact Submodule.smul_mem_smul hsa Submodule.mem_top
  choose w hwV hw using h1
  let g : ℕ →o (Submodule L V)ᵒᵈ :=
    ⟨fun n => ((maximalIdeal B ^ n • ⊤ : Submodule B W).restrictScalars L).comap V.subtype,
      fun m n hmn x hx => Submodule.pow_smul_top_le _ W hmn hx⟩
  obtain ⟨k, hk⟩ := IsArtinian.monotone_stabilizes g
  have h2 : b • v - w k = 0 := by
    apply IsHausdorff.haus' (I := maximalIdeal B)
    intro n
    rw [SModEq.zero]
    apply Submodule.pow_smul_top_le _ W (le_max_left n k)
    have h3 : (⟨w (max n k) - w k, V.sub_mem (hwV _) (hwV _)⟩ : V) ∈ OrderDual.ofDual (g k) := by
      have := Submodule.sub_mem _ (hw k)
        (Submodule.pow_smul_top_le _ W (le_max_right n k) (hw (max n k)))
      rw [sub_sub_sub_cancel_left] at this
      exact this
    rw [hk _ (le_max_right n k)] at h3
    have h4 : w (max n k) - w k ∈ (maximalIdeal B ^ (max n k) • ⊤ : Submodule B W) := h3
    have := Submodule.add_mem _ (hw (max n k)) h4
    rwa [sub_add_sub_cancel] at this
  rw [sub_eq_zero.1 h2]
  exact hwV k

private lemma finite_of_dense {L R B N : Type} [CommRing L] [IsLocalRing L] [CommRing R]
    [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra L B] [Algebra R B]
    [AddCommGroup N] [Module L N] [Module B N] [IsScalarTower L B N] [Module.Finite B N]
    [IsPrecomplete (maximalIdeal L) L]
    (hloc : (maximalIdeal L).map (algebraMap L B) ≤ maximalIdeal B)
    (hd : ∀ (n : ℕ) (b : B), ∃ a s : R, IsUnit (algebraMap R B s) ∧
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n)
    (U : Submodule L N) (hfg : U.FG) (hU : ∀ (r : R), ∀ v ∈ U, algebraMap R B r • v ∈ U)
    (hspan : Submodule.span B (U : Set N) = ⊤) : Module.Finite L N := by
  obtain ⟨n, f, hf⟩ : ∃ (n : ℕ) (f : (Fin n → L) →ₗ[L] N), LinearMap.range f = U :=
    (Submodule.fg_iff_exists_fin_linearMap L N).1 hfg
  haveI := precomplete_pi (maximalIdeal L) n
  haveI : IsHausdorff (maximalIdeal L) N := IsHausdorff.of_map hloc
  refine Module.Finite.of_surjective f (surjective_of_mkQ_comp_surjective (I := maximalIdeal L) ?_)
  let P : Submodule B N := (maximalIdeal L).map (algebraMap L B) • ⊤
  have hP : ∀ x, x ∈ P ↔ x ∈ (maximalIdeal L • ⊤ : Submodule L N) := by
    intro x
    rw [← Submodule.restrictScalars_mem L, Submodule.restrictScalars_map_smul_eq,
      Submodule.restrictScalars_top]
  let π : N →ₗ[L] N ⧸ P := P.mkQ.restrictScalars L
  let F := Fin n → L
  let Q : Submodule L F := maximalIdeal L • ⊤
  have hQ : Q ≤ LinearMap.ker (π ∘ₗ f) := by
    intro x hx
    have : f x ∈ P := by
      rw [hP]
      have := Submodule.mem_map_of_mem (f := f) hx
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    exact (Submodule.Quotient.mk_eq_zero P).2 this
  haveI : IsArtinian L (F ⧸ Q) := by
    letI : Field (L ⧸ maximalIdeal L) := Ideal.Quotient.field _
    haveI : Module.Finite (L ⧸ maximalIdeal L) (F ⧸ Q) :=
      Module.Finite.of_restrictScalars_finite L _ _
    exact isArtinian_of_surjective_algebraMap (R := L ⧸ maximalIdeal L)
      Ideal.Quotient.mk_surjective
  let V : Submodule L (N ⧸ P) := LinearMap.range (Q.liftQ _ hQ)
  have hV : ∀ y, y ∈ V ↔ ∃ u ∈ U, P.mkQ u = y := by
    intro y
    simp only [V, Submodule.range_liftQ, ← hf, LinearMap.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
  have hall : ∀ x : N, P.mkQ x ∈ V := by
    intro x
    have hx : x ∈ Submodule.span B (U : Set N) := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact (hV _).2 ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact V.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact V.add_mem hx hy
    | smul b x _ hx =>
      rw [map_smul]
      refine smul_mem_of_dense hd V ?_ b _ hx
      intro r v hv
      obtain ⟨u, hu, rfl⟩ := (hV _).1 hv
      exact (hV _).2 ⟨_, hU r u hu, map_smul _ _ _⟩
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨u, hu, hux⟩ := (hV _).1 (hall x)
  rw [← hf] at hu
  obtain ⟨z, rfl⟩ := hu
  refine ⟨z, ?_⟩
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hP] at hux
  exact (Submodule.Quotient.eq _).2 hux

private lemma flat_tensor {Λ R B M : Type} [CommRing Λ] [CommRing R] [CommRing B] [Algebra Λ R]
    [Algebra R B] [Algebra Λ B] [IsScalarTower Λ R B] [AddCommGroup M] [Module R M] [Module Λ M]
    [IsScalarTower Λ R M] [Module.Flat Λ M] [Module.Flat R B] : Module.Flat Λ (B ⊗[R] M) := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  have h1 : Function.Injective (AlgebraTensorModule.lTensor R M I.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := M) I.subtype I.injective_subtype
  have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := B) _ h1
  have h3 : ∀ x, AlgebraTensorModule.assoc Λ R B B M Λ (LinearMap.lTensor (B ⊗[R] M) I.subtype x)
      = LinearMap.lTensor B (AlgebraTensorModule.lTensor R M I.subtype)
        (AlgebraTensorModule.assoc Λ R B B M I x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul y i =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [add_tmul, map_add (f := _), hx, hy]
      | tmul b m => simp
  intro x y hxy
  apply (AlgebraTensorModule.assoc Λ R B B M I).injective
  apply h2
  rw [← h3, ← h3, hxy]

private lemma free_of_flat {Λ L N : Type} [CommRing Λ] [CommRing L] [IsLocalRing L]
    [IsNoetherianRing L] [Algebra Λ L] [AddCommGroup N] [Module Λ N] [Module L N]
    [IsScalarTower Λ L N] [Module.Flat Λ N] [Module.Finite L N] (p : Ideal Λ)
    (hp : p.map (algebraMap Λ L) = maximalIdeal L) : Module.Free L N := by
  haveI : Module.FinitePresentation L N := Module.finitePresentation_of_finite L N
  apply Module.free_of_maximalIdeal_rTensor_injective
  have hmem : ∀ x : p, algebraMap Λ L x ∈ maximalIdeal L := fun x =>
    hp ▸ Ideal.mem_map_of_mem _ x.2
  let j : p →ₗ[Λ] maximalIdeal L :=
    LinearMap.codRestrict ((maximalIdeal L).restrictScalars Λ)
      (Algebra.linearMap Λ L ∘ₗ p.subtype) hmem
  let ψ : p ⊗[Λ] N →ₗ[Λ] (maximalIdeal L) ⊗[L] N :=
    mapOfCompatibleSMul L Λ Λ (maximalIdeal L) N ∘ₗ j.rTensor N
  have hψ : ∀ (x : p) (n : N), ψ (x ⊗ₜ n) = (⟨_, hmem x⟩ : maximalIdeal L) ⊗ₜ n := fun _ _ => rfl
  have hsurj : ∀ z, z ∈ LinearMap.range ψ := by
    have key : ∀ (x : L) (hx : x ∈ Submodule.span L (algebraMap Λ L '' p))
        (hx' : x ∈ maximalIdeal L) (n : N),
        (⟨x, hx'⟩ : maximalIdeal L) ⊗ₜ[L] n ∈ LinearMap.range ψ := by
      have hle : ∀ x ∈ Submodule.span L (algebraMap Λ L '' p), x ∈ maximalIdeal L :=
        fun x hx => hp ▸ hx
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        intro _ n
        exact ⟨_, hψ ⟨a, ha⟩ n⟩
      | zero =>
        intro _ n
        have : (⟨0, ‹_›⟩ : maximalIdeal L) = 0 := rfl
        rw [this, zero_tmul]
        exact zero_mem _
      | add x y hx hy ihx ihy =>
        intro _ n
        have : (⟨x + y, ‹_›⟩ : maximalIdeal L) = ⟨x, hle x hx⟩ + ⟨y, hle y hy⟩ := rfl
        rw [this, add_tmul]
        exact add_mem (ihx _ _) (ihy _ _)
      | smul l x hx ih =>
        intro _ n
        have : (⟨l • x, ‹_›⟩ : maximalIdeal L) = l • ⟨x, hle x hx⟩ := rfl
        rw [this, smul_tmul]
        exact ih _ _
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | add x y hx hy => exact add_mem hx hy
    | tmul x n => exact key x.1 (hp.ge x.2) x.2 n
  have hcomp : ∀ y, TensorProduct.lid L N (LinearMap.rTensor N (maximalIdeal L).subtype (ψ y))
      = TensorProduct.lid Λ N (LinearMap.rTensor N p.subtype y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul x n => rw [hψ]; simp
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨y, rfl⟩ := hsurj z
  have h0 := hcomp y
  rw [hz, map_zero, eq_comm, LinearEquiv.map_eq_zero_iff] at h0
  have hy : y = 0 :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := N) p.subtype p.injective_subtype
      (by rw [h0, map_zero])
  rw [hy, map_zero]

end UpperTheory.Reformulated.B.FlatnessPrecompleteProducts

theorem UpperTheory.Reformulated.B.FlatnessPrecompleteProducts.finite_free_baseChange :
    ∀ (Λ R : Type) [inst : CommRing Λ] [IsNoetherianRing Λ] [inst_2 : CommRing R] [IsNoetherianRing R]
      [inst_4 : Algebra Λ R] (p : Ideal Λ) (q : Ideal R) (L B : Type) [inst_5 : CommRing L] [inst_6 : IsLocalRing L]
      [inst_7 : CommRing B] [inst_8 : IsLocalRing B] [inst_9 : Algebra Λ L] [inst_10 : Algebra R B] [inst_11 : Algebra L B]
      [inst_12 : Algebra Λ B] [IsScalarTower Λ R B] [IsScalarTower Λ L B] (M : Type) [inst_15 : AddCommGroup M]
      [inst_16 : _root_.Module R M] [inst_17 : _root_.Module Λ M] [IsScalarTower Λ R M] [Module.Finite Λ M]
      [Module.Flat Λ M],
      UpperTheory.V.AlgebraTools.IsCplAt Λ p L →
        UpperTheory.V.AlgebraTools.IsCplAt R q B →
          Ideal.comap (Algebra.algebraMap Λ R) q = p →
            Module.Finite L (TensorProduct R B M) ∧ Module.Free L (TensorProduct R B M) := by
  intro Λ R _ _ _ _ _ p q L B _ _ _ _ _ _ _ _ _ _ M _ _ _ _ _ _ hL hB hpq
  have := hL.noeth
  have := hB.noeth
  have := hL.complete
  haveI : Module.Finite R M := Module.Finite.of_restrictScalars_finite Λ R M
  haveI : Module.Flat R B := flat_of_isCplAt hB
  haveI : Module.Flat Λ (B ⊗[R] M) := flat_tensor
  have hloc : (maximalIdeal L).map (algebraMap L B) ≤ maximalIdeal B := by
    rw [← map_eq_max hL, Ideal.map_map, ← IsScalarTower.algebraMap_eq, Ideal.map_le_iff_le_comap,
      IsScalarTower.algebraMap_eq Λ R B, ← Ideal.comap_comap, hB.comap_eq, hpq]
  have hd : ∀ (n : ℕ) (b : B), ∃ a s : R, IsUnit (algebraMap R B s) ∧
      algebraMap R B s * b - algebraMap R B a ∈ maximalIdeal B ^ n := by
    intro n b
    obtain ⟨a, s, hs, hsa⟩ := hB.dense n b
    refine ⟨a, s, ?_, hsa⟩
    by_contra hn
    apply hs
    rw [← hB.comap_eq]
    exact hn
  let φ : M →ₗ[Λ] B ⊗[R] M := (TensorProduct.mk R B M 1).restrictScalars Λ
  haveI : Module.Finite L (B ⊗[R] M) := by
    refine finite_of_dense hloc hd (Submodule.span L (Set.range φ)) ?_ ?_ ?_
    · obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Λ) (M := M)
      rw [← LinearMap.coe_range, LinearMap.range_eq_map, ← hs, Submodule.map_span,
        Submodule.span_span_of_tower]
      exact Submodule.fg_span (s.finite_toSet.image _)
    · intro r v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, rfl⟩ := hx
        refine Submodule.subset_span ⟨r • m, ?_⟩
        rw [algebraMap_smul]
        exact map_smul (TensorProduct.mk R B M 1) r m
      | zero => rw [smul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | smul l x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
    · rw [Submodule.span_span_of_tower, eq_top_iff]
      rintro x -
      induction x using TensorProduct.induction_on with
      | zero => exact zero_mem _
      | add x y hx hy => exact add_mem hx hy
      | tmul b m =>
        have : b ⊗ₜ[R] m = b • φ m := by
          change _ = b • ((1 : B) ⊗ₜ[R] m)
          rw [smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  exact ⟨inferInstance, free_of_flat p (map_eq_max hL)⟩
end

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.finite_free_baseChange :
    ∀ (Λ R : Type) [CommRing Λ] [IsNoetherianRing Λ] [CommRing R] [IsNoetherianRing R] [Algebra Λ R]
      (p : Ideal Λ) (q : Ideal R) (L B : Type) [CommRing L] [IsLocalRing L] [CommRing B] [IsLocalRing B]
      [Algebra Λ L] [Algebra R B] [Algebra L B] [Algebra Λ B] [IsScalarTower Λ R B] [IsScalarTower Λ L B]
      (M : Type) [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower Λ R M] [Module.Finite Λ M] [Module.Flat Λ M],
      IsCplAt Λ p L → IsCplAt R q B → q.comap (algebraMap Λ R) = p →
      Module.Finite L (TensorProduct R B M) ∧ Module.Free L (TensorProduct R B M) :=
  _root_.UpperTheory.Reformulated.B.FlatnessPrecompleteProducts.finite_free_baseChange
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCmPatch
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDimFin
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.supportDim_le_of_finite :
    ∀ (L B : Type) [CommRing L] [IsNoetherianRing L] [CommRing B] [Algebra L B] (N : Type) [AddCommGroup N] [Module B N]
      [Module L N] [IsScalarTower L B N] [Module.Finite L N], Module.supportDim B N ≤ ringKrullDim L := by
  intro L B _ _ _ _ N _ _ _ _ _
  have hfin : Module.Finite B N := Module.Finite.of_restrictScalars_finite L B N
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  let f : B →ₐ[L] Module.End L N := Algebra.lsmul L L N
  have hf : ∀ b : B, b ∈ Module.annihilator B N → f b = 0 := by
    intro b hb
    ext n
    exact Module.mem_annihilator.mp hb n
  let g : (B ⧸ Module.annihilator B N) →ₐ[L] Module.End L N :=
    Ideal.Quotient.liftₐ (Module.annihilator B N) f hf
  have hinj : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).mpr ?_
    intro q hq
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine Module.mem_annihilator.mpr (fun n => ?_)
    have h := LinearMap.congr_fun hq n
    exact h
  haveI : Algebra.IsIntegral L (B ⧸ Module.annihilator B N) :=
    ⟨fun q => (isIntegral_algHom_iff g hinj).mp (Algebra.IsIntegral.isIntegral _)⟩
  exact Order.krullDim_le_of_strictMono
    (fun P => (⟨Ideal.comap (algebraMap L (B ⧸ Module.annihilator B N)) P.asIdeal, inferInstance⟩ :
      PrimeSpectrum L))
    (fun P Q h => Ideal.IsIntegral.comap_lt_comap h)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaEquidim
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.dim_minimalPrime_eq :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (M : Type) [AddCommGroup M] [Module B M]
      [Module.Finite B M] (xs : List B), (∀ x ∈ xs, x ∈ maximalIdeal B) → RingTheory.Sequence.IsWeaklyRegular M xs →
      Module.supportDim B M ≤ (xs.length : ℕ) →
      ∀ Z ∈ (Module.annihilator B M).minimalPrimes, ringKrullDim (B ⧸ Z) = (xs.length : ℕ) := by
  intro B _ _ _ M _ _ _ xs hxs hreg hdim Z hZ
  apply le_antisymm
  · calc ringKrullDim (B ⧸ Z) ≤ ringKrullDim (B ⧸ Module.annihilator B M) :=
          ringKrullDim_le_of_surjective (Ideal.Quotient.factor hZ.1.2)
            (Ideal.Quotient.factor_surjective hZ.1.2)
      _ = Module.supportDim B M := (Module.supportDim_eq_ringKrullDim_quotient_annihilator B M).symm
      _ ≤ _ := hdim
  · exact GlobalTheory.length_le_ringKrullDim_quotient_of_isAssociatedPrime hxs hreg
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B M hZ)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDepthCat
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.exists_isRegular_of_free_quotient :
    ∀ (L B : Type) [CommRing L] [IsRegularLocalRing L] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra L B] [IsLocalHom (algebraMap L B)] (M : Type) [AddCommGroup M] [Module B M] [Module L M]
      [IsScalarTower L B M] [Module.Finite B M] [Nontrivial M] (r e : ℕ) (y : Fin r → B),
      ringKrullDim L = e → (∀ i, y i ∈ maximalIdeal B) → GlobalTheory.IsQuasiRegularSeq M y →
      Module.Free L (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) →
      ∃ xs : List B, xs.length = r + e ∧ (∀ x ∈ xs, x ∈ maximalIdeal B) ∧ RingTheory.Sequence.IsRegular M xs := by
  intro L B _ _ _ _ _ _ _ M _ _ _ _ _ _ r e y he hy hq hfree
  obtain ⟨zs, h, hd⟩ := GlobalTheory.exists_ofList_eq_maximalIdeal_length_eq L
  have hreg := (GlobalTheory.isRegular_of_ofList_eq_maximalIdeal h hd.le).toIsWeaklyRegular
  have hlen : zs.length = e := by
    rw [he] at hd
    exact_mod_cast hd
  have hmem : ∀ x ∈ List.ofFn y ++ zs.map (algebraMap L B), x ∈ maximalIdeal B := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hy i
    · refine map_maximalIdeal_le (algebraMap L B) ?_
      rw [← h, Ideal.map_ofList]
      exact Ideal.subset_span hx
  refine ⟨List.ofFn y ++ zs.map (algebraMap L B), by simp [hlen], hmem, ?_⟩
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem,
    RingTheory.Sequence.isWeaklyRegular_append_iff, GlobalTheory.ofList_ofFn_eq_span_range,
    RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff]
  refine ⟨hq.isWeaklyRegular ?_, ?_⟩
  · exact fun i => maximalIdeal_le_jacobson _ (hy i)
  · exact ((TensorProduct.lid L _).isWeaklyRegular_congr zs).mp hreg.isWeaklyRegular_rTensor
end

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.patched_depth_dim :
    ∀ (L B : Type) [CommRing L] [IsRegularLocalRing L] [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
      [Algebra L B] [IsLocalHom (algebraMap L B)] (M : Type) [AddCommGroup M] [Module B M] [Module L M]
      [IsScalarTower L B M] [Module.Finite B M] [Nontrivial M] (r e : ℕ) (y : Fin r → B),
      ringKrullDim L = e → (∀ i, y i ∈ maximalIdeal B) → GlobalTheory.IsQuasiRegularSeq M y →
      Module.Free L (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) →
      Module.Finite L (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) →
      (∃ xs : List B, xs.length = r + e ∧ (∀ x ∈ xs, x ∈ maximalIdeal B) ∧ RingTheory.Sequence.IsRegular M xs) ∧
      ∀ Z ∈ (Module.annihilator B M).minimalPrimes, ringKrullDim (B ⧸ Z) = ((r + e : ℕ) : WithBot ℕ∞) := by
  intro L B _ _ _ _ _ _ _ M _ _ _ _ _ _ r e y hL hy hq hfree hfin
  refine ⟨exists_isRegular_of_free_quotient L B M r e y hL hy hq hfree, ?_⟩
  obtain ⟨xs, hlen, hxs, hreg⟩ := exists_isRegular_of_free_quotient L B M r e y hL hy hq hfree
  have hys : ∀ z ∈ List.ofFn y, z ∈ maximalIdeal B := by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hy i
  have h1 := GlobalTheory.supportDim_le_supportDim_quotient_add_length (M := M) hys
  rw [GlobalTheory.ofList_ofFn_eq_span_range, List.length_ofFn] at h1
  have h2 := supportDim_le_of_finite L B (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M))
  rw [hL] at h2
  have hdim : Module.supportDim B M ≤ ((xs.length : ℕ) : WithBot ℕ∞) := by
    refine h1.trans ?_
    rw [hlen]
    calc Module.supportDim B (M ⧸ Ideal.span (Set.range y) • (⊤ : Submodule B M)) + ((r : ℕ) : WithBot ℕ∞)
        ≤ ((e : ℕ) : WithBot ℕ∞) + ((r : ℕ) : WithBot ℕ∞) := by gcongr
      _ = ((r + e : ℕ) : WithBot ℕ∞) := by
        rw [add_comm]; norm_cast
  intro Z hZ
  have := dim_minimalPrime_eq B M xs hxs hreg.toIsWeaklyRegular hdim Z hZ
  rw [this, hlen]
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem pmDim_quot {A B σ M : Type} [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
    [Module A M] (y : σ → A) :
    Nonempty (((B ⊗[A] M) ⧸ (Ideal.span (Set.range fun i => algebraMap A B (y i)) • ⊤ :
      Submodule B (B ⊗[A] M))) ≃ₗ[B] B ⊗[A] (M ⧸ (Ideal.span (Set.range y) • ⊤ : Submodule A M))) := by
  classical
  set I : Ideal A := Ideal.span (Set.range y) with hIdef
  have hI : Ideal.span (Set.range fun i => algebraMap A B (y i)) = I.map (algebraMap A B) := by
    rw [hIdef, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [hI]
  refine ⟨(TensorProduct.AlgebraTensorModule.tensorQuotientEquiv (R := A) B A B
    (I • ⊤ : Submodule A M) ≪≫ₗ Submodule.quotEquivOfEq _ _ ?_).symm⟩
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      obtain ⟨m, hm⟩ := m
      simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul, LinearMap.coe_restrictScalars,
        Submodule.coe_subtype]
      refine Submodule.smul_induction_on hm ?_ ?_
      · intro a ha m' _
        rw [← TensorProduct.smul_tmul, algebra_compatible_smul B a, ← TensorProduct.smul_tmul']
        exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top
      · intro u v hu hv
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ hu hv
    | add x z hx hz =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hz
  · rw [Submodule.smul_le]
    intro r hr x hx
    clear hx
    induction hr using Submodule.span_induction generalizing x with
    | mem r hr =>
      obtain ⟨a, ha, rfl⟩ := hr
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b m =>
        refine ⟨b ⊗ₜ[A] (⟨a • m, Submodule.smul_mem_smul ha Submodule.mem_top⟩ : (I • ⊤ : Submodule A M)), ?_⟩
        simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul, LinearMap.coe_restrictScalars,
          Submodule.coe_subtype]
        rw [← TensorProduct.smul_tmul, algebra_compatible_smul B a, TensorProduct.smul_tmul']
      | add u v hu hv =>
        rw [smul_add]
        exact Submodule.add_mem _ hu hv
    | zero => simp
    | add r s _ _ hr hs =>
      rw [add_smul]
      exact Submodule.add_mem _ (hr x) (hs x)
    | smul c r _ hr =>
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ c (hr x)

private theorem pmDim_step {L B σ M N : Type} [CommRing L] [IsRegularLocalRing L] [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] [Algebra L B] [IsLocalHom (algebraMap L B)] [Fintype σ]
    [AddCommGroup M] [Module B M] [Module.Finite B M] [AddCommGroup N] [Module B N] [Module L N]
    [IsScalarTower L B N] [Module.Free L N] [Module.Finite L N] (d : ℕ) (y : σ → B)
    (hd : ringKrullDim L = d) (hy : ∀ i, y i ∈ maximalIdeal B) (hq : GlobalTheory.IsQuasiRegularSeq M y)
    (e : (M ⧸ (Ideal.span (Set.range y) • ⊤ : Submodule B M)) ≃ₗ[B] N) :
    ∀ Z ∈ (Module.annihilator B M).minimalPrimes,
      ringKrullDim (B ⧸ Z) = ((d + Fintype.card σ : ℕ) : WithBot ℕ∞) := by
  classical
  intro Z hZ
  rcases subsingleton_or_nontrivial M with hM | hM
  · have htop : Module.annihilator B M = ⊤ := Module.annihilator_eq_top_iff.mpr hM
    rw [htop] at hZ
    exact absurd (top_le_iff.mp hZ.1.2) hZ.1.1.ne_top
  · letI : Module L M := Module.compHom M (algebraMap L B)
    haveI : IsScalarTower L B M := ⟨fun a b m => by
      show (a • b) • m = algebraMap L B a • (b • m)
      rw [Algebra.smul_def, mul_smul]⟩
    let eσ : Fin (Fintype.card σ) ≃ σ := (Fintype.equivFin σ).symm
    have hq' := hq.comp_equiv eσ
    have hspan : Ideal.span (Set.range (y ∘ eσ)) = Ideal.span (Set.range y) := by
      rw [Set.range_comp, EquivLike.range_eq_univ, Set.image_univ]
    let e' : (M ⧸ (Ideal.span (Set.range (y ∘ eσ)) • ⊤ : Submodule B M)) ≃ₗ[L] N :=
      ((Submodule.quotEquivOfEq _ _ (by rw [hspan])) ≪≫ₗ e).restrictScalars L
    have hfree : Module.Free L (M ⧸ (Ideal.span (Set.range (y ∘ eσ)) • ⊤ : Submodule B M)) :=
      Module.Free.of_equiv e'.symm
    have hfin : Module.Finite L (M ⧸ (Ideal.span (Set.range (y ∘ eσ)) • ⊤ : Submodule B M)) :=
      Module.Finite.equiv e'.symm
    have h := (UpperTheory.V.AlgebraTools.patched_depth_dim L B M (Fintype.card σ) d (y ∘ eσ) hd
      (fun i => hy _) hq' hfree hfin).2 Z hZ
    rw [h, Nat.add_comm]

theorem UpperTheory.V.Pa.Core.pmDim :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsNoetherianRing Λ] [CommRing R] [IsNoetherianRing R] [Fintype σ] (c : Λ →+* R) (y : σ → R) (f : R) (ii : Ideal R) (X : Type) [AddCommGroup X] [Module R X] [Module Λ X] [Module.Free Λ X] [Module.Finite Λ X] (P : PMod y f ii X) (q : Ideal R) (d : ℕ) (La B : Type) [CommRing La] [IsLocalRing La] [Algebra Λ La] [CommRing B] [IsLocalRing B] [Algebra P.BB B], (∀ (a : Λ) (x : X), a • x = c a • x) → q.IsPrime → f ∉ q → (∀ a, y a ∈ q) → IsCplAt Λ (q.comap c) La → IsRegularLocalRing La → ringKrullDim La = d → IsCplAt P.BB (q.map (algebraMap R P.BB)) B → ∀ Z ∈ (Module.annihilator B (B ⊗[P.BB] P.MM)).minimalPrimes, ringKrullDim (B ⧸ Z) = ((d + Fintype.card σ : ℕ) : WithBot ℕ∞) := by
  intro Λ R σ _ _ _ _ _ c y f ii X _ _ _ _ _ P q d La B _ _ _ _ _ _ hc hq hf hy hLa hreg hdim hB
  classical
  have hYP := UpperTheory.V.Pa.Core.yPrime R σ y f P.BB P.cpl q hq hf hy
  haveI : IsNoetherianRing P.BB := P.cpl.noeth
  haveI : IsNoetherianRing B := hB.noeth
  haveI : Module.Finite P.BB P.MM := P.fin
  haveI : IsAdicComplete (maximalIdeal B) B := hB.complete
  letI : Algebra R B := ((algebraMap P.BB B).comp (algebraMap R P.BB)).toAlgebra
  haveI : IsScalarTower R P.BB B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hRB : IsCplAt R q B := hYP.2.2.2 B hB
  haveI : Module.Flat P.BB B := UpperTheory.V.AlgebraTools.IsCplAt.flat P.BB _ B hB
  let φ : Λ →+* B := (algebraMap R B).comp c
  have hφ : Ideal.comap φ (maximalIdeal B) = q.comap c := by
    show Ideal.comap ((algebraMap P.BB B).comp ((algebraMap R P.BB).comp c)) (maximalIdeal B) = q.comap c
    rw [← Ideal.comap_comap, ← Ideal.comap_comap, hB.comap_eq, hYP.2.1]
  obtain ⟨ψ, hψ, -⟩ := UpperTheory.V.AlgebraTools.IsCplAt.existsUnique_lift Λ (q.comap c) La hLa B φ hφ
  letI : Algebra La B := ψ.toAlgebra
  haveI : IsLocalHom (algebraMap La B) := by
    show IsLocalHom ψ
    refine ((IsLocalRing.local_hom_tfae ψ).out 1 4).mpr ?_
    have hm : maximalIdeal La = (q.comap c).map (algebraMap Λ La) := by
      simpa using (UpperTheory.V.AlgebraTools.IsCplAt.map_pow_eq Λ (q.comap c) La hLa 1).symm
    rw [hm, Ideal.map_le_iff_le_comap, Ideal.comap_comap, hψ, hφ]
  letI : Algebra Λ R := c.toAlgebra
  letI : Algebra Λ B := φ.toAlgebra
  haveI : IsScalarTower Λ R B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Λ La B :=
    IsScalarTower.of_algebraMap_eq (fun x => (RingHom.congr_fun hψ x).symm)
  haveI : IsScalarTower Λ R X := ⟨fun a r x => by
    show (c a * r) • x = a • (r • x)
    rw [mul_smul, hc]⟩
  obtain ⟨hfin, hfree⟩ :=
    UpperTheory.V.AlgebraTools.IsCplAt.finite_free_baseChange Λ R (q.comap c) q La B X hLa hRB rfl
  haveI := hfin
  haveI := hfree
  let y' : σ → B := fun i => algebraMap P.BB B (algebraMap R P.BB (y i))
  obtain ⟨e1⟩ := pmDim_quot (A := P.BB) (B := B) (M := P.MM) (fun a => algebraMap R P.BB (y a))
  let e : ((B ⊗[P.BB] P.MM) ⧸ (Ideal.span (Set.range y') • ⊤ : Submodule B (B ⊗[P.BB] P.MM))) ≃ₗ[B]
      B ⊗[R] X :=
    e1 ≪≫ₗ TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) P.fib ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange R P.BB B B X
  have hy' : ∀ i, y' i ∈ maximalIdeal B := by
    intro i
    have h : algebraMap R P.BB (y i) ∈ Ideal.comap (algebraMap P.BB B) (maximalIdeal B) := by
      rw [hB.comap_eq]
      exact Ideal.mem_map_of_mem _ (hy i)
    exact h
  have hqr : GlobalTheory.IsQuasiRegularSeq (B ⊗[P.BB] P.MM) y' := P.qr.baseChange B
  exact pmDim_step (L := La) (B := B) (M := B ⊗[P.BB] P.MM) (N := B ⊗[R] X) d y' hdim hy' hqr e
