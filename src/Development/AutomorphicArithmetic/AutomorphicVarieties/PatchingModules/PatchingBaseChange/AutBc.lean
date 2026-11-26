module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilPrime

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.MapsBc
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.XmapsBc
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.xmaps_bc :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] (R P : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] [CommRing P] [Algebra O P] [IsNoetherianRing P] (θ : R →ₐ[O] P) (X X0 : Type) [AddCommGroup X] [Module R X] [AddCommGroup X0] [Module P X0] (f : R) (φ : X0 →+ X) (ψ : X →+ X0), (∃ s : Finset X0, ∀ z, ∃ c : X0 → R, z = ∑ g ∈ s, θ (c g) • g) → (∀ (t : R) z, φ (θ t • z) = t • φ z) → (∀ (t : R) z, ψ (t • z) = θ t • ψ z) → (∀ z, φ (ψ z) = f • z) → (∀ z, ψ (φ z) = θ f • z) → ∃ (φ' : Til O O' P ⊗[P] X0 →+ Til O O' R ⊗[R] X) (ψ' : Til O O' R ⊗[R] X →+ Til O O' P ⊗[P] X0), (∀ t z, φ' (Til.map O' θ t • z) = t • φ' z) ∧ (∀ t z, ψ' (t • z) = Til.map O' θ t • ψ' z) ∧ (∀ z, φ' (ψ' z) = Til.ι O O' R f • z) ∧ ∀ z, ψ' (φ' z) = Til.map O' θ (Til.ι O O' R f) • z := by
  intro O O' _ _ _ _ R P _ _ _ _ _ _ θ X X0 _ _ _ _ f φ ψ hgen hφ hψ hφψ hψφ
  letI : Module R X0 := Module.compHom X0 θ.toRingHom
  haveI : Module.Finite R X0 := by
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hgen
    refine ⟨s, ?_⟩
    rw [eq_top_iff]
    intro z _
    obtain ⟨c, hc⟩ := hs z
    rw [hc]
    refine Submodule.sum_mem _ (fun g hg => ?_)
    exact Submodule.smul_mem _ (c g) (Submodule.subset_span hg)
  obtain ⟨e, he1, he2⟩ := BC.til_mod O O' R P θ X0 (fun a m => rfl)
  let φL : X0 →ₗ[R] X :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun t z => hφ t z }
  let ψL : X →ₗ[R] X0 :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := fun t z => hψ t z }
  let A := Til O O' R
  let Φ := LinearMap.baseChange A φL
  let Ψ := LinearMap.baseChange A ψL
  have hsc : ∀ (M : Type) [AddCommGroup M] [Module R M] (g : M →ₗ[R] M) (r : R), (∀ m, g m = r • m) →
      ∀ w : A ⊗[R] M, LinearMap.baseChange A g w = Til.ι O O' R r • w := by
    intro M _ _ g r hg w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      rw [LinearMap.baseChange_tmul, hg, ← Til.algebraMap_eq, ← TensorProduct.smul_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def]
    | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  have heinv : ∀ (t : A) (z : Til O O' P ⊗[P] X0), e.symm (Til.map O' θ t • z) = t • e.symm z := by
    intro t z
    apply e.injective
    rw [he2, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  refine ⟨Φ.toAddMonoidHom.comp e.symm.toAddMonoidHom, e.toAddMonoidHom.comp Ψ.toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro t z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    rw [heinv, LinearMap.map_smul]
  · intro t z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    rw [LinearMap.map_smul, he2]
  · intro z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe, AddEquiv.symm_apply_apply]
    have := hsc X (φL ∘ₗ ψL) f (fun m => hφψ m) z
    rw [LinearMap.baseChange_comp] at this
    exact this
  · intro z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    have := hsc X0 (ψL ∘ₗ φL) f (fun m => hψφ m) (e.symm z)
    rw [LinearMap.baseChange_comp] at this
    change e (Ψ (Φ (e.symm z))) = _
    rw [show Ψ (Φ (e.symm z)) = Til.ι O O' R f • e.symm z from this, he2, AddEquiv.apply_symm_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilSp
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilQuot
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem mem_map_C_of_forall_coeff_mem_of_fg {A : Type} [CommRing A] (J : Ideal A) (hJ : J.FG) (f : PowerSeries A)
    (h : ∀ n, PowerSeries.coeff n f ∈ J) : f ∈ J.map PowerSeries.C := by
  obtain ⟨s, rfl⟩ := hJ
  have hc : ∀ n, ∃ c : A → A, Function.support c ⊆ ↑s ∧ ∑ a ∈ s, c a • a = PowerSeries.coeff n f :=
    fun n => Submodule.mem_span_finset.mp (h n)
  choose c _ hc using hc
  have hf : f = ∑ a ∈ s, PowerSeries.C a * PowerSeries.mk (fun n => c n a) := by
    ext n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    rw [← hc n]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_eq_mul, mul_comm]
  rw [hf]
  refine Ideal.sum_mem _ fun a ha => Ideal.mul_mem_right _ _ ?_
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ha)

theorem UpperTheory.V.Pa.BC.til_quot :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (R : Type) [CommRing R] [Algebra O R] (I : Ideal R), I.FG → Function.Surjective (Til.map O' (Ideal.Quotient.mkₐ O I)) ∧ RingHom.ker (Til.map O' (Ideal.Quotient.mkₐ O I)) = I.map (Til.ι O O' R) := by
  intro O O' _ _ _ R _ _ I hI
  set φ := Algebra.TensorProduct.map (AlgHom.id O' O') (Ideal.Quotient.mkₐ O I) with hφ
  have hsurj : Function.Surjective φ :=
    Algebra.TensorProduct.map_surjective _ _ (fun x => ⟨x, rfl⟩) (Ideal.Quotient.mkₐ_surjective O I)
  have hker : RingHom.ker φ = I.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) := by
    have e := Algebra.TensorProduct.lTensor_ker (A := O') (Ideal.Quotient.mkₐ O I)
      (Ideal.Quotient.mkₐ_surjective O I)
    have hk : RingHom.ker (Ideal.Quotient.mkₐ O I) = I := by
      ext x
      simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
    rw [hk] at e
    rw [← e]
    rfl
  have hcoeff : ∀ (f : Til O O' R) (n : ℕ),
      PowerSeries.coeff n (Til.map O' (Ideal.Quotient.mkₐ O I) f : PowerSeries (O' ⊗[O] (R ⧸ I)))
        = φ (PowerSeries.coeff n (f : PowerSeries (O' ⊗[O] R))) :=
    fun f n => PowerSeries.coeff_map _ _ _
  refine ⟨?_, ?_⟩
  · intro f
    refine ⟨(PowerSeries.mk fun n =>
      (hsurj (PowerSeries.coeff n (f : PowerSeries (O' ⊗[O] (R ⧸ I))))).choose : PowerSeries (O' ⊗[O] R)), ?_⟩
    apply PowerSeries.ext
    intro n
    refine (hcoeff _ n).trans ?_
    erw [PowerSeries.coeff_mk]
    exact (hsurj _).choose_spec
  · have hι : I.map (Til.ι O O' R) = (RingHom.ker φ).map (Til.C O O' R) := by
      rw [hker]
      exact (Ideal.map_map _ _).symm
    rw [hι]
    ext f
    rw [RingHom.mem_ker]
    constructor
    · intro hf
      have h : ∀ n, PowerSeries.coeff n (f : PowerSeries (O' ⊗[O] R)) ∈ RingHom.ker φ := by
        intro n
        rw [RingHom.mem_ker, ← hcoeff, hf]
        exact map_zero _
      have hJ : (RingHom.ker φ).FG := by
        rw [hker]
        exact hI.map _
      exact mem_map_C_of_forall_coeff_mem_of_fg _ hJ f h
    · intro hf
      refine (Ideal.map_le_iff_le_comap.mpr ?_ : (RingHom.ker φ).map (Til.C O O' R)
        ≤ RingHom.ker (Til.map O' (Ideal.Quotient.mkₐ O I))) hf
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker]
      apply PowerSeries.ext
      intro n
      rw [hcoeff]
      change φ (PowerSeries.coeff n (PowerSeries.C x : PowerSeries (O' ⊗[O] R)))
        = PowerSeries.coeff n (0 : PowerSeries (O' ⊗[O] (R ⧸ I)))
      rw [PowerSeries.coeff_C, map_zero]
      split_ifs
      · exact RingHom.mem_ker.mp hx
      · exact map_zero _
end

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem UpperTheory.V.Pa.BC.equiv_of_ker {K A B C : Type} [CommRing K] [CommRing A] [CommRing B] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K C] (f : A →ₐ[K] B) (g : A →ₐ[K] C) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (h : RingHom.ker f = RingHom.ker g) : ∃ τ : B ≃ₐ[K] C, ∀ a, τ (f a) = g a := by
  refine ⟨((Ideal.quotientKerAlgEquivOfSurjective hf).symm.trans (Ideal.quotientEquivAlgOfEq K h)).trans
    (Ideal.quotientKerAlgEquivOfSurjective hg), fun a => ?_⟩
  have : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f a) = Ideal.Quotient.mk _ a := by
    rw [AlgEquiv.symm_apply_eq]; rfl
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, this]
  rfl

private theorem UpperTheory.V.Pa.BC.spIdeal_fg {R : Type} [CommRing R] {q n : ℕ} (P : Fin q → Polynomial R)
    (ut : Fin q → Fin n → R) : (spIdeal P ut).FG := by
  refine Submodule.fg_span ?_
  have key : ∀ (S : Type) [CommRing S] (Q : Fin q → Polynomial S), {z | ∃ j k, z = (Q j).coeff k}.Finite := by
    intro S _ Q
    refine ((Set.finite_iUnion fun j => (Q j).coeffs.finite_toSet).insert 0).subset ?_
    rintro z ⟨j, k, rfl⟩
    by_cases h : (Q j).coeff k = 0
    · exact Or.inl h
    · exact Or.inr (Set.mem_iUnion.2 ⟨j, Polynomial.coeff_mem_coeffs h⟩)
  exact key _ _

private theorem UpperTheory.V.Pa.BC.spIdeal_map {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {q n : ℕ}
    (P : Fin q → Polynomial R) (ut : Fin q → Fin n → R) :
    (spIdeal P ut).map (MvPowerSeries.map φ) = spIdeal (fun j => (P j).map φ) (fun j i => φ (ut j i)) := by
  have key : ∀ j k, MvPowerSeries.map φ (((∏ i, (Polynomial.X -
      Polynomial.C (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i)))) -
      (P j).map (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R)).coeff k) =
      ((∏ i, (Polynomial.X - Polynomial.C (MvPowerSeries.C (φ (ut j i)) + MvPowerSeries.X (j, i)))) -
      ((P j).map φ).map (MvPowerSeries.C : R' →+* MvPowerSeries (Fin q × Fin n) R')).coeff k := by
    intro j k
    rw [← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, Polynomial.map_map]
    have : (MvPowerSeries.map φ).comp (MvPowerSeries.C : R →+* MvPowerSeries (Fin q × Fin n) R) =
        (MvPowerSeries.C : R' →+* MvPowerSeries (Fin q × Fin n) R').comp φ := by
      ext1 a
      simp
    rw [this]
    simp
  unfold spIdeal
  rw [Ideal.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨j, k, rfl⟩, rfl⟩
    exact ⟨j, k, key j k⟩
  · rintro ⟨j, k, rfl⟩
    exact ⟨_, ⟨j, k, rfl⟩, key j k⟩

theorem UpperTheory.V.Pa.BC.til_sp :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] (B : Type) [CommRing B] [Algebra O B] (q n : ℕ) (P : Fin q → Polynomial B) (ut : Fin q → Fin n → B), ∃ τ : Til O O' (Sp P ut) ≃ₐ[O'] Sp (fun j => (P j).map (Til.ι O O' B)) (fun j i => Til.ι O O' B (ut j i)), (∀ a, τ (Til.map O' (IsScalarTower.toAlgHom O B (Sp P ut)) a) = algebraMap (Til O O' B) _ a) ∧ ∀ j i, τ (Til.ι O O' _ (Sp.u P ut j i)) = Sp.u _ _ j i := by
  intro O O' _ _ _ _ _ B _ _ q n P ut
  obtain ⟨τ0, h1, -, h3, -⟩ := UpperTheory.V.Pa.BC.til_mvps O O' B (Fin q × Fin n)
  obtain ⟨hs, hk⟩ := UpperTheory.V.Pa.BC.til_quot O O' _ (spIdeal P ut) (UpperTheory.V.Pa.BC.spIdeal_fg P ut)
  let f : Til O O' (MvPowerSeries (Fin q × Fin n) B) →ₐ[O'] Til O O' (Sp P ut) :=
    Til.map O' ((Sp.mk P ut).restrictScalars O)
  let g : Til O O' (MvPowerSeries (Fin q × Fin n) B) →ₐ[O']
      Sp (fun j => (P j).map (Til.ι O O' B)) (fun j i => Til.ι O O' B (ut j i)) :=
    ((Sp.mk _ _).restrictScalars O').comp τ0.toAlgHom
  have hf : Function.Surjective f := hs
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp τ0.surjective
  have hfk : RingHom.ker f = (spIdeal P ut).map (Til.ι O O' _) := hk
  have hI : ((spIdeal P ut).map (Til.ι O O' _)).map τ0.toRingEquiv.toRingHom =
      spIdeal (fun j => (P j).map (Til.ι O O' B)) (fun j i => Til.ι O O' B (ut j i)) := by
    rw [Ideal.map_map, ← UpperTheory.V.Pa.BC.spIdeal_map]
    congr 1
    exact RingHom.ext h1
  have hfg : RingHom.ker f = RingHom.ker g := by
    rw [hfk]
    ext a
    have e1 : a ∈ RingHom.ker g ↔
        τ0 a ∈ spIdeal (fun j => (P j).map (Til.ι O O' B)) (fun j i => Til.ι O O' B (ut j i)) :=
      Ideal.Quotient.eq_zero_iff_mem
    rw [e1, ← hI]
    exact (Ideal.apply_mem_of_equiv_iff (f := τ0.toRingEquiv)).symm
  obtain ⟨τ, hτ⟩ := UpperTheory.V.Pa.BC.equiv_of_ker f g hf hg hfg
  refine ⟨τ, fun a => ?_, fun j i => ?_⟩
  · have e : Til.map O' (IsScalarTower.toAlgHom O B (Sp P ut)) a =
        f (Til.map O' (IsScalarTower.toAlgHom O B (MvPowerSeries (Fin q × Fin n) B)) a) := by
      have hc : IsScalarTower.toAlgHom O B (Sp P ut) = ((Sp.mk P ut).restrictScalars O).comp
          (IsScalarTower.toAlgHom O B (MvPowerSeries (Fin q × Fin n) B)) :=
        AlgHom.ext fun b => ((Sp.mk P ut).commutes b).symm
      rw [hc]
      refine PowerSeries.ext fun k => ?_
      show Algebra.TensorProduct.map _ _ (Til.coeff O O' B k a) =
        Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.map _ _ (Til.coeff O O' B k a))
      induction Til.coeff O O' B k a using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [e, hτ]
    show Sp.mk _ _ (τ0 _) = _
    rw [h3]
    exact (Sp.mk _ _).commutes a
  · have e : Til.ι O O' _ (Sp.u P ut j i) =
        f (Til.ι O O' _ (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i))) :=
      (Til.map_ι O' ((Sp.mk P ut).restrictScalars O) (MvPowerSeries.C (ut j i) + MvPowerSeries.X (j, i))).symm
    rw [e, hτ]
    show Sp.mk _ _ (τ0 _) = Sp.mk _ _ _
    rw [h1, map_add (f := _), MvPowerSeries.map_C, MvPowerSeries.map_X]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ExistsFiniteSpanningTaylorWilesTensor
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem tens_fin {Λ B S R M : Type} [CommRing Λ] [CommRing B] [CommRing S] [CommRing R] [Algebra B S]
    [AddCommGroup M] [Module B M] [Module Λ M] [Module.Finite B S] [Module.Finite Λ M]
    (lam : Λ → B) (hl : ∀ (a : Λ) (m : M), a • m = lam a • m) (θ : R →+* S)
    (hθ : ∀ a : Λ, ∃ t : R, θ t = algebraMap B S (lam a)) :
    ∃ s : Finset (S ⊗[B] M), ∀ z, ∃ c : S ⊗[B] M → R, z = ∑ g ∈ s, θ (c g) • g := by
  classical
  obtain ⟨a, ha⟩ := Module.Finite.fg_top (R := B) (M := S)
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := Λ) (M := M)
  let s : Finset (S ⊗[B] M) := Finset.image₂ (fun x y => x ⊗ₜ[B] y) a t
  refine ⟨s, ?_⟩
  have h1 : ∀ x ∈ a, ∀ y : M, x ⊗ₜ[B] y ∈ Submodule.span θ.range (s : Set (S ⊗[B] M)) := by
    intro x hx y
    have hy : y ∈ Submodule.span Λ (t : Set M) := ht ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image₂_of_mem hx hy))
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y y' _ _ h h' => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ h h'
    | smul c y _ h =>
      obtain ⟨w, hw⟩ := hθ c
      rw [hl, TensorProduct.tmul_smul, ← algebraMap_smul S]
      exact Submodule.smul_mem _ (⟨algebraMap B S (lam c), w, hw⟩ : θ.range) h
  have h2 : ∀ x : S, ∀ y : M, x ⊗ₜ[B] y ∈ Submodule.span θ.range (s : Set (S ⊗[B] M)) := by
    intro x
    have hx : x ∈ Submodule.span B (a : Set S) := ha ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact h1 x hx
    | zero => intro y; rw [TensorProduct.zero_tmul]; exact Submodule.zero_mem _
    | add x x' _ _ h h' => intro y; rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ (h y) (h' y)
    | smul c x _ h => intro y; rw [TensorProduct.smul_tmul]; exact h _
  intro z
  have hz : z ∈ Submodule.span θ.range (s : Set (S ⊗[B] M)) := by
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul x y => exact h2 x y
    | add z z' h h' => exact Submodule.add_mem _ h h'
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hz
  choose c hc using fun g => (f g).2
  refine ⟨c, ?_⟩
  rw [← hf]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hc]
  rfl

theorem UpperTheory.V.Pa.BC.exists_finite_spanning_taylorWiles_tensor :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (σ : Type) (D : ℕ) (b : TWBase u J σ D) (G : Glob l L) (h : G.Hom G0) (q : ℕ) (ut : Fin q → Fin n → O) (N : ℕ) (A : TWRing b h ut N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (ex : ℕ) (m : TWMaps Nq ph ta A ex), ∃ s : Finset (SpAt u (fun j => h.p₀ (ph j)) ut ⊗[B] b.M), ∀ z, ∃ c : _ → A.R, z = ∑ g ∈ s, m.θ (c g) • g := by
  intro l _ L G0 n O _ _ _ r B _ _ _ u J σ D b G h q ut N A Nq ph ta ex m
  haveI : Module.Finite B (SpAt u (fun j => h.p₀ (ph j)) ut) := (UpperTheory.V.Pa.BC.sp_fin B q n _ _).1
  haveI := b.fin
  exact tens_fin (Λ := abelian₂ O σ D) (fun a => b.lam a) b.smul_lam m.θ.toRingHom fun a =>
    ⟨A.s (MvPowerSeries.C a), by
      have := m.theta_coefficientMap_eq (MvPowerSeries.C a)
      rw [MvPowerSeries.constantCoeff_C] at this
      exact this⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.QuotBc
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.quot_bc :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M] (I : Ideal R) (I' : Ideal R'), I' = I.map (algebraMap R R') → Nonempty (R' ⊗[R] (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[R'] (R' ⊗[R] M) ⧸ (I' • ⊤ : Submodule R' (R' ⊗[R] M))) := by
  intro R R' _ _ _ M _ _ I I' hI
  subst hI
  have hker : ∀ i ∈ I, ∀ y : R' ⊗[R] (M ⧸ (I • ⊤ : Submodule R M)), i • y = 0 := by
    intro i hi y
    induction y using TensorProduct.induction_on with
    | zero => exact smul_zero _
    | tmul a q =>
      induction q using Submodule.Quotient.induction_on with
      | H m =>
        rw [← TensorProduct.tmul_smul, ← Submodule.Quotient.mk_smul,
          (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul hi Submodule.mem_top),
          TensorProduct.tmul_zero]
    | add y z hy hz => rw [smul_add, hy, hz, add_zero]
  have hann : I.map (algebraMap R R') ≤ Module.annihilator R' (R' ⊗[R] (M ⧸ (I • ⊤ : Submodule R M))) :=
    Ideal.map_le_iff_le_comap.2 fun i hi => Module.mem_annihilator.2 fun y => by
      rw [algebraMap_smul]
      exact hker i hi y
  let ψ : M ⧸ (I • ⊤ : Submodule R M) →ₗ[R]
      (R' ⊗[R] M) ⧸ (I.map (algebraMap R R') • ⊤ : Submodule R' (R' ⊗[R] M)) :=
    (I • ⊤ : Submodule R M).liftQ
      (((I.map (algebraMap R R') • ⊤ : Submodule R' (R' ⊗[R] M)).mkQ.restrictScalars R) ∘ₗ
        TensorProduct.mk R R' M 1) (by
      rw [Submodule.smul_le]
      intro i hi m _
      rw [LinearMap.mem_ker, LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, TensorProduct.tmul_smul,
        ← algebraMap_smul R' i ((1 : R') ⊗ₜ[R] m)]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hi) Submodule.mem_top)
  let φ := ψ.liftBaseChange R'
  let χ := (I.map (algebraMap R R') • ⊤ : Submodule R' (R' ⊗[R] M)).liftQ
    (LinearMap.baseChange R' (I • ⊤ : Submodule R M).mkQ) (by
      rw [Submodule.smul_le]
      intro r hr x _
      rw [LinearMap.mem_ker, map_smul]
      exact Module.mem_annihilator.1 (hann hr) _)
  refine ⟨LinearEquiv.ofLinear φ χ ?_ ?_⟩
  · apply Submodule.linearMap_qext
    apply TensorProduct.AlgebraTensorModule.ext
    intro a m
    simp [φ, χ, ψ]
    rw [← Submodule.Quotient.mk_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  · apply TensorProduct.AlgebraTensorModule.ext
    intro a q
    induction q using Submodule.Quotient.induction_on with
    | H m => simp [φ, χ, ψ, TensorProduct.smul_tmul']
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ExistsSemilinearEquivBaseChangeTensor
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.exists_semilinear_equiv_baseChange_tensor :
    ∀ (B P B' P₁ P' : Type) [CommRing B] [CommRing P] [CommRing B'] [CommRing P₁] [CommRing P'] [Algebra B P] [Algebra B B'] [Algebra P P₁] [Algebra B' P'] (τ : P₁ ≃+* P') (M M' : Type) [AddCommGroup M] [Module B M] [AddCommGroup M'] [Module B' M'] (_μ : B' ⊗[B] M ≃ₗ[B'] M'), (∀ b, τ (algebraMap P P₁ (algebraMap B P b)) = algebraMap B' P' (algebraMap B B' b)) → ∃ e : P₁ ⊗[P] (P ⊗[B] M) ≃+ P' ⊗[B'] M', ∀ z w, e (z • w) = τ z • e w := by
  intro B P B' P₁ P' _ _ _ _ _ _ _ _ _ τ M M' _ _ _ _ μ h
  letI : Algebra P₁ P' := τ.toRingHom.toAlgebra
  letI : Algebra P P' := (τ.toRingHom.comp (algebraMap P P₁)).toAlgebra
  letI : Algebra B P' := ((algebraMap B' P').comp (algebraMap B B')).toAlgebra
  haveI : IsScalarTower P P₁ P' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower B B' P' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower B P P' := IsScalarTower.of_algebraMap_eq (fun b => (h b).symm)
  let t : P₁ ≃ₗ[P₁] P' :=
    { τ.toAddEquiv with
      map_smul' := fun a b => by
        show τ (a * b) = τ a * τ b
        exact map_mul τ a b }
  let e1 : P₁ ⊗[P] (P ⊗[B] M) ≃ₗ[P₁] P' ⊗[P] (P ⊗[B] M) :=
    TensorProduct.AlgebraTensorModule.congr t (LinearEquiv.refl P _)
  let e2 : P' ⊗[P] (P ⊗[B] M) ≃ₗ[P'] P' ⊗[B] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange B P P' P' M
  let e3 : P' ⊗[B'] (B' ⊗[B] M) ≃ₗ[P'] P' ⊗[B] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange B B' P' P' M
  let e4 : P' ⊗[B'] (B' ⊗[B] M) ≃ₗ[P'] P' ⊗[B'] M' :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl P' P') μ
  let f := e2.trans (e3.symm.trans e4)
  refine ⟨e1.toAddEquiv.trans f.toAddEquiv, fun z w => ?_⟩
  show f (e1 (z • w)) = τ z • f (e1 w)
  rw [map_smul, ← map_smul f]
  rfl
end

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem mb_comp {O O' R R' R'' : Type} [CommRing O] [CommRing O'] [Algebra O O'] [CommRing R] [Algebra O R]
    [CommRing R'] [Algebra O R'] [CommRing R''] [Algebra O R''] (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') (a : Til O O' R) :
    Til.map O' (g.comp f) a = Til.map O' g (Til.map O' f a) := by
  refine PowerSeries.ext fun k => ?_
  show Algebra.TensorProduct.map _ _ (Til.coeff O O' R k a) =
    Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.map _ _ (Til.coeff O O' R k a))
  induction Til.coeff O O' R k a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem mb_sp (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O']
    (B : Type) [CommRing B] [Algebra O B] (q n : ℕ) (P : Fin q → Polynomial B) (ut : Fin q → Fin n → B)
    (P' : Fin q → Polynomial (Til O O' B)) (ut' : Fin q → Fin n → Til O O' B)
    (hP : P' = fun j => (P j).map (Til.ι O O' B)) (hu : ut' = fun j i => Til.ι O O' B (ut j i)) :
    ∃ τ : Til O O' (Sp P ut) ≃ₐ[O'] Sp P' ut',
      (∀ a, τ (Til.map O' (IsScalarTower.toAlgHom O B (Sp P ut)) a) = algebraMap (Til O O' B) _ a) ∧
      ∀ j i, τ (Til.ι O O' _ (Sp.u P ut j i)) = Sp.u _ _ j i := by
  subst hP hu
  exact UpperTheory.V.Pa.BC.til_sp O O' B q n P ut

private theorem mb_quot {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R' M'] (ρ : R ≃+* R') (ν : M ≃+ M') (hν : ∀ (t : R) m, ν (t • m) = ρ t • ν m) (I : Ideal R) (I' : Ideal R')
    (hI : I' = I.map (ρ : R →+* R')) :
    ∃ e : (M ⧸ (I • ⊤ : Submodule R M)) ≃+ (M' ⧸ (I' • ⊤ : Submodule R' M')), ∀ (t : R) m, e (t • m) = ρ t • e m := by
  have he : (I • ⊤ : Submodule R M).toAddSubgroup.map (ν : M →+ M') = (I' • ⊤ : Submodule R' M').toAddSubgroup := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      show ν x ∈ (I' • ⊤ : Submodule R' M')
      refine Submodule.smul_induction_on (p := fun x => ν x ∈ (I' • ⊤ : Submodule R' M')) hx (fun a ha m _ => ?_)
        (fun x y hx hy => ?_)
      · rw [hν]
        exact Submodule.smul_mem_smul (hI ▸ Ideal.mem_map_of_mem _ ha) trivial
      · rw [map_add (f := _)]
        exact Submodule.add_mem _ hx hy
    · intro y hy
      refine Submodule.smul_induction_on
        (p := fun y => y ∈ (I • ⊤ : Submodule R M).toAddSubgroup.map (ν : M →+ M')) hy (fun a ha m _ => ?_)
        (fun x y hx hy => AddSubgroup.add_mem _ hx hy)
      rw [hI] at ha
      obtain ⟨c, hc, rfl⟩ := (Ideal.mem_map_iff_of_surjective (ρ : R →+* R') ρ.surjective).1 ha
      refine ⟨c • ν.symm m, Submodule.smul_mem_smul hc trivial, ?_⟩
      show ν _ = ρ c • m
      rw [hν, ν.apply_symm_apply]
  refine ⟨QuotientAddGroup.congr _ _ ν he, fun t m => ?_⟩
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  show (Submodule.Quotient.mk (ν (t • m)) : M' ⧸ (I' • ⊤ : Submodule R' M')) = ρ t • Submodule.Quotient.mk (ν m)
  rw [hν, Submodule.Quotient.mk_smul]

private theorem mb_kill {R T R' M M' : Type} [CommRing R] [CommRing T] [Algebra R T] [CommRing R'] [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R' M'] (ρ : T → R') (ν : T ⊗[R] M ≃+ M')
    (hν : ∀ (t : T) m, ν (t • m) = ρ t • ν m) (x : R) (hx : ∀ m : M, x • m = 0) (m : M') :
    ρ (algebraMap R T x) • m = 0 := by
  obtain ⟨w, rfl⟩ := ν.surjective m
  rw [← hν, algebraMap_smul, map_eq_zero_iff ν ν.injective]
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => rw [← TensorProduct.tmul_smul, hx, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

private theorem mb_fEl {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {q n : ℕ} (Nq : Fin q → ℕ)
    (U : Fin q → Fin n → R) : fEl Nq (fun j i => f (U j i)) = f (fEl Nq U) := by
  simp [fEl, map_prod]

private theorem map_quadratic_element_one {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (f : R →+* R') {n : ℕ} (ph : G)
    (U : Fin n → R) : q1El ph (fun i => f (U i)) = MonoidAlgebra.mapRingHom G f (q1El ph U) := by
  rw [q1El, q1El, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp

private theorem map_quadratic_element_two {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (f : R →+* R') {n : ℕ} (ph ta : G)
    (U : Fin n → R) (i : Fin n) (y : R) :
    q2El ph ta (fun i => f (U i)) i (f y) = MonoidAlgebra.mapRingHom G f (q2El ph ta U i y) := by
  rw [q2El, q2El, map_mul, map_list_prod, List.map_ofFn]
  congr 1
  · congr 2
    funext k
    by_cases h : k = i <;> simp [h]
  · simp

private theorem mb_tr {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (f : R →+* R') {n : ℕ} (D : GDet n R G)
    (g : G) (y : MonoidAlgebra R G) :
    (D.map f).tr (MonoidAlgebra.single g 1 * MonoidAlgebra.mapRingHom G f y) = f (D.tr (MonoidAlgebra.single g 1 * y)) := by
  rw [GDet.tr, GDet.tr, ← ((UpperTheory.V.CA.d_gmap D).2.2.1 f _).2 1, map_mul, MonoidAlgebra.mapRingHom_single, map_one]

private theorem mb_move {T P R' P' X X0 X' X0' : Type} [CommRing T] [CommRing P] [CommRing R'] [CommRing P']
    [AddCommGroup X] [Module T X] [AddCommGroup X0] [Module P X0] [AddCommGroup X'] [Module R' X'] [AddCommGroup X0']
    [Module P' X0'] (ρ : T ≃+* R') (τ : P → P') (θ : T → P) (θ' : R' → P') (hθ : ∀ t, θ' (ρ t) = τ (θ t))
    (e : X ≃+ X') (he : ∀ (t : T) z, e (t • z) = ρ t • e z) (e0 : X0 ≃+ X0') (he0 : ∀ (t : P) z, e0 (t • z) = τ t • e0 z)
    (f : T) (φ : X0 →+ X) (ψ : X →+ X0) (h1 : ∀ t z, φ (θ t • z) = t • φ z) (h2 : ∀ (t : T) z, ψ (t • z) = θ t • ψ z)
    (h3 : ∀ z, φ (ψ z) = f • z) (h4 : ∀ z, ψ (φ z) = θ f • z) :
    ∃ (φ' : X0' →+ X') (ψ' : X' →+ X0'), (∀ t z, φ' (θ' t • z) = t • φ' z) ∧ (∀ (t : R') z, ψ' (t • z) = θ' t • ψ' z) ∧
      (∀ z, φ' (ψ' z) = ρ f • z) ∧ ∀ z, ψ' (φ' z) = θ' (ρ f) • z := by
  refine ⟨e.toAddMonoidHom.comp (φ.comp e0.symm.toAddMonoidHom), e0.toAddMonoidHom.comp (ψ.comp e.symm.toAddMonoidHom),
    fun t z => ?_, fun t z => ?_, fun z => ?_, fun z => ?_⟩
  · obtain ⟨t, rfl⟩ := ρ.surjective t
    obtain ⟨z, rfl⟩ := e0.surjective z
    show e (φ (e0.symm _)) = _ • e (φ (e0.symm _))
    rw [hθ, ← he0, e0.symm_apply_apply, e0.symm_apply_apply, h1, he]
  · obtain ⟨t, rfl⟩ := ρ.surjective t
    obtain ⟨z, rfl⟩ := e.surjective z
    show e0 (ψ (e.symm _)) = _ • e0 (ψ (e.symm _))
    rw [hθ, ← he, e.symm_apply_apply, e.symm_apply_apply, h2, he0]
  · obtain ⟨z, rfl⟩ := e.surjective z
    show e (φ (e0.symm (e0 (ψ (e.symm _))))) = _
    rw [e.symm_apply_apply, e0.symm_apply_apply, h3, he]
  · obtain ⟨z, rfl⟩ := e0.surjective z
    show e0 (ψ (e.symm (e (φ (e0.symm _))))) = _
    rw [e.symm_apply_apply, e0.symm_apply_apply, h4, he0, hθ]

private theorem mb_det {n : ℕ} {R R' P P' B B' G G0 : Type} [CommRing R] [CommRing R'] [CommRing P] [CommRing P']
    [CommRing B] [CommRing B'] [Group G] [Group G0] (p : G →* G0) (D : GDet n R G) (D' : GDet n R' G) (E : GDet n B G0)
    (E' : GDet n B' G0) (κ : R →+* R') (i : B →+* B') (θ : R →+* P) (θ' : R' →+* P') (a : B →+* P) (a' : B' →+* P')
    (lp : P →+* P') (h1 : θ'.comp κ = lp.comp θ) (h2 : lp.comp a = a'.comp i) (hD : D' = D.map κ) (hE : E.map i = E')
    (h : D.map θ = (E.comap p).map a) : D'.map θ' = (E'.comap p).map a' := by
  rw [hD, (UpperTheory.V.CA.d_gmap D).2.1, h1, ← (UpperTheory.V.CA.d_gmap D).2.1, h, (UpperTheory.V.CA.d_gmap _).2.1, h2,
    ← (UpperTheory.V.CA.d_gmap _).2.1, ← hE]
  rfl

theorem UpperTheory.V.Pa.BC.maps_bc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O O' : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] [IsScalarTower ℤ_[l] O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] [Module.Free O O'] (r : Resid G0.frame O n) (r' : Resid G0.frame O' n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (u : Pair r B) (u' : Pair r' (Til O O' B)) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (b' : TWBase u' (J.map (Til.ι O O' B)) Unit D) (τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D) (G : Glob l L) (h : G.Hom G0) (q : ℕ) (ut : Fin q → Fin n → O) (N : ℕ) (τS : Til O O' (Sinf O Empty D q n) ≃ₐ[O'] Sinf O' Unit D q n) (A : TWRing b h ut N) (A' : TWRing b' h (fun j i => algebraMap O O' (ut j i)) N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (ex : ℕ) (_m : TWMaps Nq ph ta A ex), RBC r r' → u.Maps (Til.ι O O' B) u'.D u'.ψ → Nonempty (BaseRel b b' τ) → SinfRel l τ τS → Nonempty (RingRel A A' τS) → Nonempty (TWMaps Nq ph ta A' ex) := by
  intro l _ L G0 n O O' _ _ _ _ _ _ _ _ _ _ _ _ _ r r' B _ _ _ _ u u' J D b b' τ G h q ut N τS A A' Nq ph ta ex m
    _ hu ⟨hb⟩ hS ⟨hA⟩
  obtain ⟨τp, hp1, hp2⟩ := mb_sp O O' B q n (fun j => u.D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1))
    (fun j i => algebraMap O B (ut j i)) (fun j => u'.D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1))
    (fun j i => algebraMap O' (Til O O' B) (algebraMap O O' (ut j i)))
    (funext fun j => by
      rw [← hu.1, ← ((UpperTheory.V.CA.d_gmap u.D).2.2.1 _ _).1, MonoidAlgebra.mapRingHom_single, map_one])
    (funext fun j => funext fun i => (Til.ι_algebraMap O O' B (ut j i)).symm)
  haveI : IsNoetherianRing (SpAt u (fun j => h.p₀ (ph j)) ut) := (UpperTheory.V.Pa.BC.sp_fin B q n _ _).2
  let θ' : A'.R →ₐ[O'] SpAt u' (fun j => h.p₀ (ph j)) (fun j i => algebraMap O O' (ut j i)) :=
    (τp.toAlgHom.comp (Til.map O' m.θ)).comp hA.ρ.symm.toAlgHom
  have hθ : ∀ t, θ' (hA.ρ t) = τp (Til.map O' m.θ t) := fun t =>
    congrArg (fun x => τp (Til.map O' m.θ x)) (hA.ρ.symm_apply_apply t)
  have hB : ∀ x : B, τp (Til.ι O O' _ (algebraMap B (SpAt u (fun j => h.p₀ (ph j)) ut) x)) =
      algebraMap (Til O O' B) _ (Til.ι O O' B x) := fun x => by
    rw [← hp1, Til.map_ι]
    rfl
  let κ : A.R →+* A'.R := (hA.ρ.toRingEquiv : _ →+* A'.R).comp (Til.ι O O' A.R)
  have hκ : ∀ x, κ x = hA.ρ (Til.ι O O' A.R x) := fun _ => rfl
  let lp : SpAt u (fun j => h.p₀ (ph j)) ut →+* SpAt u' (fun j => h.p₀ (ph j)) (fun j i => algebraMap O O' (ut j i)) :=
    (τp.toRingEquiv : _ →+* _).comp (Til.ι O O' _)
  have hc1 : θ'.toRingHom.comp κ = lp.comp m.θ.toRingHom := RingHom.ext fun x => by
    show θ' (hA.ρ (Til.ι O O' A.R x)) = τp (Til.ι O O' _ (m.θ x))
    rw [hθ, Til.map_ι]
  have hc2 : lp.comp (algebraMap B _) = (algebraMap (Til O O' B) _).comp (Til.ι O O' B) := RingHom.ext hB
  have hX : ∀ p, A'.s (MvPowerSeries.X p) = κ (A.s (MvPowerSeries.X p)) := fun p => by
    rw [← hS.X, hA.s, Til.map_ι, hκ]
  have hU : A'.U = fun j i => κ (A.U j i) := funext fun j => funext fun i => hA.U j i
  have hf : fEl Nq A'.U = κ (fEl Nq A.U) := by rw [hU, mb_fEl]
  have hD : A'.p.D = A.p.D.map κ := hA.maps.1.symm
  have hkill : ∀ x : A.R, (∀ z : A.M, x • z = 0) → ∀ z : A'.M, κ x • z = 0 := fun x hx z =>
    mb_kill (fun t => hA.ρ t) hA.ν hA.ν_smul x hx z
  obtain ⟨φ1, ψ1, h1, h2, h3, h4⟩ := UpperTheory.V.Pa.BC.xmaps_bc O O' A.R _ m.θ A.X _ (fEl Nq A.U) m.φ m.ψ
    (UpperTheory.V.Pa.BC.exists_finite_spanning_taylorWiles_tensor l L G0 n O r B u J Empty D b G h q ut N A Nq ph ta ex m) m.φ_smul m.ψ_smul m.φψ m.ψφ
  obtain ⟨e0, he0⟩ := UpperTheory.V.Pa.BC.exists_semilinear_equiv_baseChange_tensor B (SpAt u (fun j => h.p₀ (ph j)) ut) (Til O O' B) (Til O O' _)
    (SpAt u' (fun j => h.p₀ (ph j)) (fun j i => algebraMap O O' (ut j i))) τp.toRingEquiv b.M b'.M hb.μ hB
  obtain ⟨e1⟩ := UpperTheory.V.Pa.BC.quot_bc A.R (Til O O' A.R) A.M
    (Ideal.span (Set.range fun p => A.s (MvPowerSeries.X p))) _ rfl
  obtain ⟨e2, he2⟩ := mb_quot hA.ρ.toRingEquiv hA.ν hA.ν_smul
    ((Ideal.span (Set.range fun p => A.s (MvPowerSeries.X p))).map (algebraMap A.R (Til O O' A.R)))
    (Ideal.span (Set.range fun p => A'.s (MvPowerSeries.X p))) (by
      rw [Ideal.map_map, Ideal.map_span, ← Set.range_comp]
      congr 2
      exact funext hX)
  obtain ⟨φ', ψ', k1, k2, k3, k4⟩ := mb_move hA.ρ.toRingEquiv (fun x => τp x) (fun t => Til.map O' m.θ t)
    (fun t => θ' t) hθ (e1.toAddEquiv.trans e2) (fun t z => by
      show e2 (e1 (t • z)) = _ • e2 (e1 z)
      rw [map_smul, he2]) e0 he0 (Til.ι O O' A.R (fEl Nq A.U)) φ1 ψ1 h1 h2 h3 h4
  refine ⟨⟨θ', ⟨?_, fun v i => ?_⟩, fun z => ?_, fun j i => ?_, φ', ψ', k1, k2, fun z => ?_, fun z => ?_,
    fun j g z => ?_, fun j i g z => ?_⟩⟩
  · exact mb_det h.p₀ A.p.D A'.p.D u.D u'.D κ (Til.ι O O' B) m.θ.toRingHom θ'.toRingHom _ _ lp hc1 hc2 hD hu.1 m.θ_pair.1
  · refine MonoidHom.ext fun g => Units.ext ?_
    have a1 : ((A'.p.ψ v i g : A'.Rˣ) : A'.R) = κ (A.p.ψ v i g) := by rw [← hA.maps.2 v i]; rfl
    have a2 : ((u'.ψ v i g : (Til O O' B)ˣ) : Til O O' B) = Til.ι O O' B (u.ψ v i g) := by rw [← hu.2 v i]; rfl
    have a3 : m.θ (A.p.ψ v i g) = algebraMap B _ ((u.ψ v i g : Bˣ) : B) :=
      congrArg (fun χ => ((χ g : _ˣ) : SpAt u (fun j => h.p₀ (ph j)) ut)) (m.θ_pair.2 v i)
    show θ' (A'.p.ψ v i g) = algebraMap (Til O O' B) _ ((u'.ψ v i g : (Til O O' B)ˣ) : Til O O' B)
    rw [a1, a2, hκ, hθ, Til.map_ι, a3, hB]
  · obtain ⟨z, rfl⟩ := τS.surjective z
    let c : Sinf O Empty D q n →ₐ[O] abelian₂ O Empty D :=
      { (MvPowerSeries.constantCoeff : Sinf O Empty D q n →+* abelian₂ O Empty D) with
        commutes' := fun a => by simp [MvPowerSeries.algebraMap_apply] }
    have hc : m.θ.comp A.s = (IsScalarTower.toAlgHom O B _).comp (b.lam.comp c) := AlgHom.ext m.theta_coefficientMap_eq
    rw [hA.s, hθ, hS.cc c (fun _ => rfl), hb.lam, ← hp1, ← mb_comp, hc, mb_comp, mb_comp]
  · rw [hA.U, hθ, Til.map_ι, m.θ_U, hp2]
  · rw [hf]
    exact k3 z
  · rw [hf]
    exact k4 z
  · rw [hf, hD, hU, map_quadratic_element_one, mb_tr, ← map_mul, ← map_pow]
    exact hkill _ (m.rel1 j g) z
  · rw [hf, hD, hX, hU, map_quadratic_element_two, mb_tr, ← map_mul, ← map_pow]
    exact hkill _ (m.rel2 j i g) z
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.BaseBc
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem free_fin_transfer {S T N N' : Type} [CommRing S] [CommRing T] [AddCommGroup N] [AddCommGroup N']
    [Module S N] [Module T N'] [Module.Free S N] [Module.Finite S N] (τ : S ≃+* T) (e : N ≃+ N')
    (he : ∀ a z, e (a • z) = τ a • e z) : Module.Free T N' ∧ Module.Finite T N' := by
  letI : Module S N' := Module.compHom N' (τ : S →+* T)
  let e' : N ≃ₗ[S] N' := { e with map_smul' := he }
  haveI : Module.Free S N' := Module.Free.of_equiv e'
  haveI : Module.Finite S N' := Module.Finite.equiv e'
  refine ⟨Module.Free.of_basis ((Module.Free.chooseBasis S N').mapCoeffs τ (fun _ _ => rfl)), ?_⟩
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := S) (M := N')
  refine ⟨⟨s, ?_⟩⟩
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span S (s : Set N') := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ (hy trivial) (hz trivial)
  | smul a y _ hy => exact Submodule.smul_mem _ (τ a) (hy trivial)

private theorem fin_of_hom {S R M : Type} [CommRing S] [CommRing R] [AddCommGroup M] [Module S M] [Module R M]
    [Module.Finite S M] (f : S → R) (h : ∀ (a : S) (m : M), a • m = f a • m) : Module.Finite R M :=
  _root_.UpperTheory.Reformulated.B.Qh10.fin_of_hom f h

private theorem lamEmb_X (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (D : ℕ) (k : Fin D) :
    lamEmb O O' D (MvPowerSeries.X (.inr k)) = MvPowerSeries.X (.inr k) := by
  simp [lamEmb]

theorem UpperTheory.V.Pa.BC.base_bc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O O' : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] [IsScalarTower ℤ_[l] O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] [Module.Free O O'] (r : Resid G0.frame O n) (r' : Resid G0.frame O' n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (u : Pair r B) (u' : Pair r' (Til O O' B)) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D), RBC r r' → u.Maps (Til.ι O O' B) u'.D u'.ψ → (∀ a, τ (Til.ι O O' _ a) = lamEmb O O' D a) → ∃ b' : TWBase u' (J.map (Til.ι O O' B)) Unit D, Nonempty (BaseRel b b' τ) := by
  intro l _ L G0 n O O' _ _ _ _ _ _ _ _ _ _ _ _ _ r r' B _ _ _ _ u u' J D b τ hr hu hτ
  haveI := b.free
  haveI := b.fin
  haveI : IsNoetherianRing (abelian₂ O Empty D) := inferInstance
  haveI : Module.Finite B b.M := fin_of_hom b.lam b.smul_lam
  obtain ⟨e, -, he⟩ := UpperTheory.V.Pa.BC.til_mod O O' (abelian₂ O Empty D) B b.lam b.M b.smul_lam
  let lam' : abelian₂ O' Unit D →ₐ[O'] Til O O' B := (Til.map O' b.lam).comp (τ.symm : abelian₂ O' Unit D →ₐ[O'] _)
  have hlam : ∀ a, lam' (τ a) = Til.map O' b.lam a := fun a => by simp [lam']
  letI mL : Module (abelian₂ O' Unit D) (Til O O' B ⊗[B] b.M) := Module.compHom _ (lam' : abelian₂ O' Unit D →+* Til O O' B)
  have hff := free_fin_transfer (T := abelian₂ O' Unit D) (N' := Til O O' B ⊗[B] b.M) τ.toRingEquiv e (fun a z => by
    rw [he, ← hlam]; rfl)
  refine ⟨{ wt := ⟨b.wt.v, b.wt.i, b.wt.γ, fun k => algebraMap O O' (b.wt.c k)⟩
            wt_res := ?_
            lam := lam'
            segmentWeightExponent := ?_
            M := Til O O' B ⊗[B] b.M
            smul_lam := fun _ _ => rfl
            free := hff.1
            fin := hff.2
            supp := ?_ }, ⟨⟨rfl, hlam, LinearEquiv.refl _ _⟩⟩⟩
  · intro k
    have h := congrArg (ResidueField.map (algebraMap O O')) (b.wt_res k)
    rw [map_mul, map_one, ResidueField.map_residue] at h
    dsimp only
    rw [hr.2.1]
    exact h
  · intro k
    dsimp only
    rw [← lamEmb_X O O' D k, ← hτ, hlam, Til.map_ι, b.segmentWeightExponent, map_sub, map_mul, map_one, Til.ι_algebraMap, ← hu.2]
    rfl
  · intro p hp
    have h1 := UpperTheory.V.AlgebraTools.mem_support_baseChange B (Til O O' B) b.M ⟨p, hp⟩
    rw [Module.mem_support_iff_of_finite, Module.mem_support_iff_of_finite] at h1
    rw [Ideal.map_le_iff_le_comap, ← b.supp _ (Ideal.comap_isPrime _ _)]
    exact h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfIso
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem UpperTheory.V.Pa.BC.mvps_congr (K A B σ : Type) [CommRing K] [CommRing A] [CommRing B] [Algebra K A]
    [Algebra K B] (e : A ≃ₐ[K] B) :
    ∃ E : MvPowerSeries σ A ≃ₐ[K] MvPowerSeries σ B, ∀ a, E a = MvPowerSeries.map (e : A →+* B) a := by
  have h1 : ∀ φ : MvPowerSeries σ A,
      MvPowerSeries.map (e.symm : B →+* A) (MvPowerSeries.map (e : A →+* B) φ) = φ := by
    intro φ
    ext n
    simp
  have h2 : ∀ φ : MvPowerSeries σ B,
      MvPowerSeries.map (e : A →+* B) (MvPowerSeries.map (e.symm : B →+* A) φ) = φ := by
    intro φ
    ext n
    simp
  let f : MvPowerSeries σ A ≃+* MvPowerSeries σ B :=
    { toFun := MvPowerSeries.map (e : A →+* B)
      invFun := MvPowerSeries.map (e.symm : B →+* A)
      left_inv := h1
      right_inv := h2
      map_mul' := map_mul _
      map_add' := map_add _ }
  refine ⟨AlgEquiv.ofRingEquiv (f := f) ?_, fun a => ?_⟩
  · intro k
    simp [f, MvPowerSeries.algebraMap_apply]
  · rfl

theorem UpperTheory.V.Pa.BC.sinf_iso :
    ∀ (l : ℕ) (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] (D q n : ℕ) (τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D), (∀ a, τ (Til.ι O O' _ a) = lamEmb O O' D a) → ∃ τS : Til O O' (Sinf O Empty D q n) ≃ₐ[O'] Sinf O' Unit D q n, SinfRel l τ τS := by
  intro l O O' _ _ _ _ _ D q n τ hτ
  obtain ⟨τ0, h0ι, -, -, h0c⟩ :=
    UpperTheory.V.Pa.BC.til_mvps O O' (abelian₂ O Empty D) (Fin q × Fin n)
  obtain ⟨E, hE⟩ :=
    UpperTheory.V.Pa.BC.mvps_congr O' (Til O O' (abelian₂ O Empty D)) (abelian₂ O' Unit D) (Fin q × Fin n) τ
  have key : ∀ x : MvPowerSeries (Fin q × Fin n) (abelian₂ O Empty D),
      (τ0.trans E) (Til.ι O O' _ x) = MvPowerSeries.map ((τ : _ →+* _).comp (Til.ι O O' _)) x := by
    intro x
    rw [AlgEquiv.trans_apply, h0ι, hE, ← RingHom.comp_apply, ← MvPowerSeries.map_comp]
  refine ⟨τ0.trans E, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro p
    rw [key, MvPowerSeries.map_X]
  · intro a
    rw [key, MvPowerSeries.map_C, RingHom.comp_apply]
    simp [hτ]
  · intro c hc z
    rw [AlgEquiv.trans_apply, hE, MvPowerSeries.constantCoeff_map, h0c c hc z]
    rfl
  · intro a
    unfold delIdeal
    rw [Ideal.map_span, ← Set.range_comp]
    congr 1
    congr 1
    funext p
    simp only [Function.comp_apply, RingHom.comp_apply, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_toRingEquiv, key, map_sub, map_pow, map_add, map_one, MvPowerSeries.map_X]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilLam
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private noncomputable def UpperTheory.V.Pa.BC.tlHom (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (σ : Type) :
    O' ⊗[O] MvPowerSeries σ O →ₐ[O'] MvPowerSeries σ O' :=
  Algebra.TensorProduct.lift (Algebra.ofId O' _) (MvPowerSeries.mapAlgHom (Algebra.ofId O O'))
    (fun _ _ => Commute.all _ _)

private theorem UpperTheory.V.Pa.BC.tlHom_tmul (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (σ : Type)
    (o : O') (f : MvPowerSeries σ O) :
    UpperTheory.V.Pa.BC.tlHom O O' σ (o ⊗ₜ f) = MvPowerSeries.C o * MvPowerSeries.map (algebraMap O O') f := by
  rw [UpperTheory.V.Pa.BC.tlHom, Algebra.TensorProduct.lift_tmul]
  rfl

private theorem UpperTheory.V.Pa.BC.tlHom_bij (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O']
    [Module.Finite O O'] [Module.Free O O'] (σ : Type) :
    Function.Bijective (UpperTheory.V.Pa.BC.tlHom O O' σ) := by
  classical
  let b := Module.Free.chooseBasis O O'
  have hsum : ∀ (c : Module.Free.ChooseBasisIndex O O' → MvPowerSeries σ O) (m : σ →₀ ℕ),
      MvPowerSeries.coeff m (UpperTheory.V.Pa.BC.tlHom O O' σ (∑ i, b i ⊗ₜ c i)) =
        ∑ i, MvPowerSeries.coeff m (c i) • b i := by
    intro c m
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, UpperTheory.V.Pa.BC.tlHom_tmul, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_map,
      Algebra.smul_def]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b x
    rw [Finsupp.sum_fintype _ _ (by simp)] at hx ⊢
    have hc : ∀ i, c i = 0 := by
      intro i
      ext m
      have hm := congrArg (MvPowerSeries.coeff m) hx
      rw [hsum, map_zero] at hm
      rw [MvPowerSeries.coeff_zero]
      exact Fintype.linearIndependent_iff.1 b.linearIndependent (fun j => MvPowerSeries.coeff m (c j)) hm i
    simp [hc]
  · intro F
    let c : Module.Free.ChooseBasisIndex O O' → MvPowerSeries σ O :=
      fun i m => b.repr (MvPowerSeries.coeff m F) i
    refine ⟨∑ i, b i ⊗ₜ c i, ?_⟩
    ext m
    rw [hsum]
    exact b.sum_repr _

private theorem UpperTheory.V.Pa.BC.tl_option {σ R : Type} [CommRing R] (p : MvPowerSeries σ R) :
    MvPowerSeries.optionEquivLeft σ R (MvPowerSeries.rename (Function.Embedding.some : σ ↪ Option σ) p) =
      PowerSeries.C p := by
  classical
  ext k x
  rw [MvPowerSeries.coeff_coeff_optionEquivLeft, PowerSeries.coeff_C]
  split_ifs with hk
  · subst hk
    have hx : x.optionElim 0 = Finsupp.embDomain Function.Embedding.some x := by
      ext a
      cases a with
      | none =>
        rw [Finsupp.embDomain_notin_range _ _ _ (by simp)]
        simp
      | some v =>
        rw [show (some v : Option σ) = Function.Embedding.some v from rfl, Finsupp.embDomain_apply_self]
        simp
    rw [hx, MvPowerSeries.coeff_embDomain_rename]
  · rw [MvPowerSeries.coeff_zero]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨y, hy⟩
    apply hk
    have hn := congrArg (fun z : Option σ →₀ ℕ => z none) hy
    simpa [Finsupp.mapDomain_notin_range] using hn.symm

private theorem UpperTheory.V.Pa.BC.tl_map_bij {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) :
    Function.Bijective (PowerSeries.map (e : A →+* B)) := by
  refine ⟨fun p q h => ?_, fun q => ⟨PowerSeries.map (e.symm : B →+* A) q, ?_⟩⟩
  · ext n
    have hn := congrArg (PowerSeries.coeff n) h
    simpa using hn
  · ext n
    simp

theorem UpperTheory.V.Pa.BC.til_lam :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] (D : ℕ), ∃ τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D, (∀ a, τ (Til.ι O O' _ a) = lamEmb O O' D a) ∧ τ (Til.s O O' _) = MvPowerSeries.X (.inl ()) := by
  intro O O' _ _ _ _ _ D
  let ε : Option (Empty ⊕ Fin D) ≃ Unit ⊕ Fin D :=
    { toFun := fun o => Option.elim o (Sum.inl ()) (Sum.map Empty.elim id)
      invFun := fun s => Sum.elim (fun _ => none) (fun i => some (Sum.inr i)) s
      left_inv := by
        rintro (_ | (e | i))
        · rfl
        · exact e.elim
        · rfl
      right_inv := by
        rintro (⟨⟩ | i) <;> rfl }
  have hb := UpperTheory.V.Pa.BC.tl_map_bij
    (RingEquiv.ofBijective (UpperTheory.V.Pa.BC.tlHom O O' (Empty ⊕ Fin D))
      (UpperTheory.V.Pa.BC.tlHom_bij O O' (Empty ⊕ Fin D)))
  let e1 : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] PowerSeries (MvPowerSeries (Empty ⊕ Fin D) O') :=
    AlgEquiv.ofBijective (PowerSeries.mapAlgHom (UpperTheory.V.Pa.BC.tlHom O O' (Empty ⊕ Fin D))) hb
  let φ : O' ⊗[O] abelian₂ O Empty D →+* MvPowerSeries (Empty ⊕ Fin D) O' :=
    (UpperTheory.V.Pa.BC.tlHom O O' (Empty ⊕ Fin D) : O' ⊗[O] abelian₂ O Empty D →+* MvPowerSeries (Empty ⊕ Fin D) O')
  refine ⟨e1.trans ((MvPowerSeries.optionEquivLeft (Empty ⊕ Fin D) O').symm.trans
    (MvPowerSeries.renameEquiv O' ε)), ?_, ?_⟩
  · intro a
    have h1 : e1 (Til.ι O O' _ a) = PowerSeries.C (MvPowerSeries.map (algebraMap O O') a) := by
      show PowerSeries.map φ (PowerSeries.C ((1 : O') ⊗ₜ[O] a)) = _
      rw [PowerSeries.map_C]
      show PowerSeries.C (UpperTheory.V.Pa.BC.tlHom O O' _ ((1 : O') ⊗ₜ[O] a)) = _
      rw [UpperTheory.V.Pa.BC.tlHom_tmul, map_one, one_mul]
    have h2 : (MvPowerSeries.optionEquivLeft (Empty ⊕ Fin D) O').symm
        (PowerSeries.C (MvPowerSeries.map (algebraMap O O') a)) =
        MvPowerSeries.rename (Function.Embedding.some : (Empty ⊕ Fin D) ↪ _)
          (MvPowerSeries.map (algebraMap O O') a) := by
      rw [AlgEquiv.symm_apply_eq, UpperTheory.V.Pa.BC.tl_option]
    rw [AlgEquiv.trans_apply, h1, AlgEquiv.trans_apply, h2]
    show MvPowerSeries.rename (⇑ε) _ = _
    rw [MvPowerSeries.rename_rename]
    rfl
  · have h1 : e1 (Til.s O O' _) = PowerSeries.X := by
      show PowerSeries.map φ PowerSeries.X = _
      exact PowerSeries.map_X _
    have h2 : (MvPowerSeries.optionEquivLeft (Empty ⊕ Fin D) O').symm PowerSeries.X =
        MvPowerSeries.X none := by
      rw [AlgEquiv.symm_apply_eq, MvPowerSeries.optionEquivLeft_X_none]
    rw [AlgEquiv.trans_apply, h1, AlgEquiv.trans_apply, h2]
    show MvPowerSeries.rename (⇑ε) _ = _
    rw [MvPowerSeries.rename_X]
    rfl
end

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.aut_bc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O O' : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] [IsScalarTower ℤ_[l] O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] [Module.Free O O'] (r : Resid G0.frame O n) (r' : Resid G0.frame O' n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (u : Pair r B) (u' : Pair r' (Til O O' B)) (J : Ideal B) (D : ℕ) (T : TWGrp G0) (_A : TWAut u J Empty D T), RBC r r' → u.Maps (Til.ι O O' B) u'.D u'.ψ → ∃ A' : TWAut u' (J.map (Til.ι O O' B)) Unit D T, A'.b.lam (MvPowerSeries.X (.inl ())) = Til.s O O' B := by
  intro l _ L G0 n O O' _ _ _ _ _ _ _ _ _ _ _ _ _ r r' B _ _ _ _ u u' J D T A hr hu
  obtain ⟨τ, hτ, hs⟩ := UpperTheory.V.Pa.BC.til_lam O O' D
  obtain ⟨τS, hS⟩ := UpperTheory.V.Pa.BC.sinf_iso l O O' D T.q n τ hτ
  obtain ⟨b', hb⟩ := UpperTheory.V.Pa.BC.base_bc l L G0 n O O' r r' B u u' J D A.b τ hr hu hτ
  have hA := fun N => UpperTheory.V.Pa.BC.ring_bc l L G0 n O O' r r' B u u' J D A.b b' τ (T.GN N) (T.h N) T.q A.ut N τS
    (A.A N) hr hu hb hS
  choose A' hA' using hA
  have hm := fun N => UpperTheory.V.Pa.BC.maps_bc l L G0 n O O' r r' B u u' J D A.b b' τ (T.GN N) (T.h N) T.q A.ut N τS
    (A.A N) (A' N) (T.Nq N) (T.ph N) (T.ta N) A.ex (A.m N) hr hu hb hS (hA' N)
  refine ⟨⟨b', fun j i => algebraMap O O' (A.ut j i), ?_, A', A.ex, fun N => (hm N).some⟩, ?_⟩
  · intro j i
    rw [hr.1 i, ← ResidueField.map_residue, A.ut_res]
    rfl
  · obtain ⟨hb⟩ := hb
    show b'.lam _ = _
    rw [← hs, hb.lam, Til.map_s]
