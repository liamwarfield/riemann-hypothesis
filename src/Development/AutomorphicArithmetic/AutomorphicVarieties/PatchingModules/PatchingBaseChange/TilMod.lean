module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MSplitDefs

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilMod
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilEv
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

section
variable {R : Type} [CommRing R] {ι : Type} (N : Type) [AddCommGroup N] [Module R N]

private theorem UpperTheory.V.Pa.BC.ev_nat {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (x : M ⊗[R] (ι → N)) (k : ι) :
    TensorProduct.piRightHom R R M' (fun _ : ι => N) (f.rTensor _ x) k =
      f.rTensor N (TensorProduct.piRightHom R R M (fun _ : ι => N) x k) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]

private theorem UpperTheory.V.Pa.BC.ev_free (n : ℕ) :
    Function.Bijective (TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N)) := by
  classical
  let e1 : (Fin n → R) ⊗[R] (ι → N) ≃ₗ[R] (Fin n → ι → N) :=
    TensorProduct.piLeft R (ι → N) (fun _ : Fin n => R) ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ => TensorProduct.lid R (ι → N))
  let e2 : (ι → (Fin n → R) ⊗[R] N) ≃ₗ[R] (ι → Fin n → N) :=
    LinearEquiv.piCongrRight (fun _ => TensorProduct.piLeft R N (fun _ : Fin n => R) ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ => TensorProduct.lid R N))
  have key : ∀ x, TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N) x =
      e2.symm (Equiv.piComm _ (e1 x)) := by
    intro x
    apply e2.injective
    rw [LinearEquiv.apply_symm_apply]
    induction x using TensorProduct.induction_on with
    | zero =>
      ext k i
      simp
      rfl
    | tmul v f =>
      ext k i
      simp [e1, e2, TensorProduct.piRightHom_tmul, Function.swap, LinearEquiv.piCongrRight_apply]
    | add a b ha hb =>
      ext k i
      have h1 := congrFun (congrFun ha k) i
      have h2 := congrFun (congrFun hb k) i
      simp only [map_add (f := _), Pi.add_apply, Equiv.piComm_apply] at h1 h2 ⊢
      rw [h1, h2]
      rfl
  have hfun : ⇑(TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N)) =
      e2.symm ∘ (Equiv.piComm _) ∘ e1 := funext key
  rw [hfun]
  exact e2.symm.bijective.comp ((Equiv.piComm _).bijective.comp e1.bijective)

private theorem UpperTheory.V.Pa.BC.ev_surj (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Surjective (TensorProduct.piRightHom R R M (fun _ : ι => N)) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  intro z
  choose w hw using fun k => LinearMap.rTensor_surjective N hp (z k)
  obtain ⟨y, hy⟩ := (UpperTheory.V.Pa.BC.ev_free (R := R) (ι := ι) N n).2 w
  refine ⟨p.rTensor _ y, ?_⟩
  funext k
  rw [UpperTheory.V.Pa.BC.ev_nat, hy, hw]

private theorem UpperTheory.V.Pa.BC.ev_bij [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Bijective (TensorProduct.piRightHom R R M (fun _ : ι => N)) := by
  haveI := Module.finitePresentation_of_finite R M
  refine ⟨?_, UpperTheory.V.Pa.BC.ev_surj N M⟩
  obtain ⟨n, m, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' R M
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective (ι → N) hf x
  have hex := rTensor_exact N hfg hf
  have hk : ∀ k, TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N) y k ∈
      Set.range (g.rTensor N) := by
    intro k
    have h1 := congrFun hx k
    rw [UpperTheory.V.Pa.BC.ev_nat, Pi.zero_apply] at h1
    exact (hex _).1 h1
  choose z hz using hk
  obtain ⟨w, hw⟩ := (UpperTheory.V.Pa.BC.ev_free N m).2 z
  have hy : y = g.rTensor _ w := by
    apply (UpperTheory.V.Pa.BC.ev_free N n).1
    funext k
    rw [UpperTheory.V.Pa.BC.ev_nat, hw, hz]
  rw [hy, ← LinearMap.rTensor_comp_apply, hfg.linearMap_comp_eq_zero, LinearMap.rTensor_zero,
    LinearMap.zero_apply]

end

theorem UpperTheory.V.Pa.BC.til_ev :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module O M] [IsScalarTower O R M] [Module.Finite R M], ∃ e : Til O O' R ⊗[R] M ≃+ (ℕ → O' ⊗[O] M), ∀ a m k, e (a ⊗ₜ m) k = Til.act O' m (Til.coeff O O' R k a) := by
  intro O O' _ _ _ _ R _ _ _ M _ _ _ _ _
  let N := R ⊗[O] O'
  let tc : O' ⊗[O] R ≃ₗ[O] N := TensorProduct.comm O O' R
  have hadd : ∀ (k : ℕ) (a b : Til O O' R),
      Til.coeff O O' R k (a + b) = Til.coeff O O' R k a + Til.coeff O O' R k b := by
    intro k a b
    unfold Til.coeff
    exact map_add (PowerSeries.coeff k) (show PowerSeries (O' ⊗[O] R) from a)
      (show PowerSeries (O' ⊗[O] R) from b)
  have hmulC : ∀ (k : ℕ) (r : R) (a : Til O O' R),
      Til.coeff O O' R k (algebraMap R (Til O O' R) r * a) = ((1 : O') ⊗ₜ[O] r) * Til.coeff O O' R k a := by
    intro k r a
    unfold Til.coeff
    exact PowerSeries.coeff_C_mul k (show PowerSeries (O' ⊗[O] R) from a) ((1 : O') ⊗ₜ[O] r)
  have hsm : ∀ (r : R) (c : O' ⊗[O] R), tc (((1 : O') ⊗ₜ[O] r) * c) = r • tc c := by
    intro r c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul o s =>
      simp only [tc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [TensorProduct.comm_tmul, TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy => rw [mul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]
  let cf : Til O O' R →ₗ[R] (ℕ → N) :=
    { toFun := fun a k => tc (Til.coeff O O' R k a)
      map_add' := fun a b => by
        funext k
        simp only [hadd, map_add (f := _), Pi.add_apply]
      map_smul' := fun r a => by
        funext k
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [Algebra.smul_def, hmulC, hsm] }
  have hcf : Function.Bijective cf := by
    constructor
    · intro a b hab
      apply PowerSeries.ext
      intro k
      have h1 := congrFun hab k
      exact tc.injective h1
    · intro f
      refine ⟨PowerSeries.mk (fun k => tc.symm (f k)), ?_⟩
      funext k
      change tc (PowerSeries.coeff k (PowerSeries.mk (fun k => tc.symm (f k)))) = f k
      rw [PowerSeries.coeff_mk, LinearEquiv.apply_symm_apply]
  let cfe : Til O O' R ≃ₗ[R] (ℕ → N) := LinearEquiv.ofBijective cf hcf
  have hev := UpperTheory.V.Pa.BC.ev_bij (R := R) (ι := ℕ) N M
  let eve : M ⊗[R] (ℕ → N) ≃ₗ[R] (ℕ → M ⊗[R] N) :=
    LinearEquiv.ofBijective (TensorProduct.piRightHom R R M (fun _ : ℕ => N)) hev
  let cb : M ⊗[R] N ≃+ O' ⊗[O] M :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange O R R M O').toAddEquiv.trans
      (TensorProduct.comm O M O').toAddEquiv
  have hcb : ∀ (m : M) (c : O' ⊗[O] R), cb (m ⊗ₜ[R] tc c) = Til.act O' m c := by
    intro m c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul o s =>
      simp [cb, tc, Til.act, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      rw [TensorProduct.comm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        TensorProduct.comm_tmul]
    | add x y hx hy => rw [map_add (f := _), TensorProduct.tmul_add, map_add (f := _), hx, hy, map_add (f := _)]
  refine ⟨(TensorProduct.comm R (Til O O' R) M).toAddEquiv.trans
    ((cfe.lTensor M).toAddEquiv.trans (eve.toAddEquiv.trans (AddEquiv.piCongrRight (fun _ => cb)))), ?_⟩
  intro a m k
  simp only [AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv, TensorProduct.comm_tmul,
    LinearEquiv.lTensor_tmul, AddEquiv.piCongrRight_apply]
  rw [← hcb]
  rfl
end

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.til_mod :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] (S R : Type) [CommRing S] [Algebra O S] [IsNoetherianRing S] [CommRing R] [Algebra O R] [IsNoetherianRing R] (f : S →ₐ[O] R) (M : Type) [AddCommGroup M] [Module R M] [Module S M] [Module.Finite S M], (∀ (a : S) (m : M), a • m = f a • m) → ∃ e : Til O O' S ⊗[S] M ≃+ Til O O' R ⊗[R] M, (∀ a m, e (a ⊗ₜ m) = Til.map O' f a ⊗ₜ m) ∧ ∀ a z, e (a • z) = Til.map O' f a • e z := by
  intro O O' _ _ _ _ S R _ _ _ _ _ _ f M _ _ _ _ h
  letI : Module O M := Module.compHom M (algebraMap O R)
  haveI : IsScalarTower O R M := ⟨fun o r m => by
    show (o • r) • m = (algebraMap O R o) • (r • m)
    rw [Algebra.smul_def, mul_smul]⟩
  haveI : IsScalarTower O S M := ⟨fun o s m => by
    show (o • s) • m = (algebraMap O R o) • (s • m)
    rw [h (o • s) m, h s m, Algebra.smul_def o s, map_mul, f.commutes, mul_smul]⟩
  have hfin : Module.Finite R M := by
    letI : Algebra S R := f.toRingHom.toAlgebra
    haveI : IsScalarTower S R M := ⟨fun s r m => by
      show (f s * r) • m = s • (r • m)
      rw [mul_smul, h]⟩
    exact Module.Finite.of_restrictScalars_finite S R M
  haveI := hfin
  obtain ⟨e1, he1⟩ := BC.til_ev O O' S M
  obtain ⟨e2, he2⟩ := BC.til_ev O O' R M
  have hact : ∀ (m : M) (x : O' ⊗[O] S), Til.act O' m (Algebra.TensorProduct.map (AlgHom.id O' O') f x) = Til.act O' m x := by
    intro m x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o s => simp [Til.act, h]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hcoeff : ∀ k a, Til.coeff O O' R k (Til.map O' f a) = Algebra.TensorProduct.map (AlgHom.id O' O') f (Til.coeff O O' S k a) := by
    intro k a
    rfl
  have key : ∀ a m, e1 (a ⊗ₜ m) = e2 (Til.map O' f a ⊗ₜ m) := by
    intro a m
    funext k
    rw [he1, he2, hcoeff, hact]
  have hform : ∀ a m, (e1.trans e2.symm) (a ⊗ₜ m) = Til.map O' f a ⊗ₜ m := by
    intro a m
    rw [AddEquiv.trans_apply, key, AddEquiv.symm_apply_apply]
  refine ⟨e1.trans e2.symm, hform, ?_⟩
  intro a z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b m => rw [TensorProduct.smul_tmul', hform, hform, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy, map_add (f := _), smul_add]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ChainLift
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem UpperTheory.V.Pa.BC.chain_lift_down (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B']
    [Module.Flat B B'] (P : Ideal B') (q : Ideal B) (hP : P.IsPrime) (hq : q.IsPrime)
    (hle : q ≤ P.comap (algebraMap B B')) :
    ∃ Q : Ideal B', Q.IsPrime ∧ Q.comap (algebraMap B B') = q ∧ Q ≤ P := by
  haveI : (P.comap (algebraMap B B')).IsPrime := Ideal.comap_isPrime _ _
  haveI : P.LiesOver (P.comap (algebraMap B B')) := ⟨rfl⟩
  obtain ⟨Q, h1, h2, h3⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := q)
    (q := P.comap (algebraMap B B')) P hle
  exact ⟨Q, h2, h3.over.symm, h1⟩

private theorem UpperTheory.V.Pa.BC.prime_chain_lift_extension (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B']
    [Algebra.IsIntegral B B'] [Module.Flat B B'] (h : ℕ) :
    ∀ (p : Fin (h + 1) → Ideal B) (e : Fin h → Ideal B), (∀ i, (p i).IsPrime) →
      (∀ i, (e i).IsPrime ∧ e i ≤ p i.castSucc ∧ e i ≤ p i.succ) →
      ∀ P0 : Ideal B', P0.IsPrime → P0.comap (algebraMap B B') = p 0 →
      ∃ (P : Fin (h + 1) → Ideal B') (E : Fin h → Ideal B'), P 0 = P0 ∧
        (∀ i, (P i).IsPrime ∧ (P i).comap (algebraMap B B') = p i) ∧
        ∀ i, (E i).IsPrime ∧ (E i).comap (algebraMap B B') = e i ∧ E i ≤ P i.castSucc ∧
          E i ≤ P i.succ := by
  induction h with
  | zero =>
    intro p e _ _ P0 hP0 hP0c
    refine ⟨fun _ => P0, Fin.elim0, rfl, ?_, fun i => i.elim0⟩
    intro i
    rw [Fin.fin_one_eq_zero i]
    exact ⟨hP0, hP0c⟩
  | succ h ih =>
    intro p e hp he P0 hP0 hP0c
    obtain ⟨he0, he0l, he0r⟩ := he 0
    obtain ⟨E0, hE0, hE0c, hE0le⟩ :=
      UpperTheory.V.Pa.BC.chain_lift_down B B' P0 (e 0) hP0 he0 (by rw [hP0c]; exact he0l)
    haveI := hp (Fin.succ 0)
    haveI := hE0
    obtain ⟨P1, hP1ge, hP1, hP1c⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime
      (p (Fin.succ 0)) E0 (by
        change E0.comap (algebraMap B B') ≤ p (Fin.succ 0)
        rw [hE0c]
        exact he0r)
    obtain ⟨P', E', hP'0, hP', hE'⟩ := ih (fun i => p i.succ) (fun i => e i.succ)
      (fun i => hp i.succ)
      (fun i => by
        obtain ⟨a, b, c⟩ := he i.succ
        refine ⟨a, ?_, c⟩
        rw [← Fin.succ_castSucc] at b
        exact b)
      P1 hP1 hP1c
    refine ⟨(Fin.cons P0 P' : Fin (h + 1 + 1) → Ideal B'),
      (Fin.cons E0 E' : Fin (h + 1) → Ideal B'), Fin.cons_zero _ _, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => rw [Fin.cons_zero]; exact ⟨hP0, hP0c⟩
      | succ j => rw [Fin.cons_succ]; exact hP' j
    · intro i
      cases i using Fin.cases with
      | zero =>
        rw [Fin.cons_zero, Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hP'0]
        exact ⟨hE0, hE0c, hE0le, hP1ge⟩
      | succ j =>
        rw [Fin.cons_succ, ← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
        exact hE' j

theorem UpperTheory.V.Pa.BC.chain_lift :
    ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B'] [Algebra.IsIntegral B B'] [Module.Flat B B'] [FaithfulSMul B B'] (h : ℕ) (p : Fin (h + 1) → Ideal B) (e : Fin h → Ideal B), (∀ i, (p i).IsPrime) → (∀ i, (e i).IsPrime ∧ e i ≤ p i.castSucc ∧ e i ≤ p i.succ) → (∃ (P : Fin (h + 1) → Ideal B') (E : Fin h → Ideal B'), (∀ i, (P i).IsPrime ∧ (P i).comap (algebraMap B B') = p i) ∧ ∀ i, (E i).IsPrime ∧ (E i).comap (algebraMap B B') = e i ∧ E i ≤ P i.castSucc ∧ E i ≤ P i.succ) ∧ ∀ (P : Ideal B') (q : Ideal B), P.IsPrime → q.IsPrime → q ≤ P.comap (algebraMap B B') → ∃ Q : Ideal B', Q.IsPrime ∧ Q.comap (algebraMap B B') = q ∧ Q ≤ P := by
  intro B B' _ _ _ _ _ _ h p e hp he
  refine ⟨?_, fun P q hP hq hle => UpperTheory.V.Pa.BC.chain_lift_down B B' P q hP hq hle⟩
  haveI := hp 0
  obtain ⟨P0, _, hP0, hP0c⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B') (p 0) ⊥ (by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    rw [(FaithfulSMul.algebraMap_injective B B') (hx.trans (map_zero _).symm)]
    exact Ideal.zero_mem _)
  obtain ⟨P, E, _, hPc, hE⟩ := UpperTheory.V.Pa.BC.prime_chain_lift_extension B B' h p e hp he P0 hP0 hP0c
  exact ⟨P, E, hPc, hE⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PtLift
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PsEv
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

open scoped PowerSeries.WithPiTopology in
theorem UpperTheory.V.Pa.BC.ps_ev :
    ∀ (R K : Type) [CommRing R] [CommRing K] (x : R →+* PowerSeries K), ∃ f : PowerSeries R →+* PowerSeries K, (∀ a, f (PowerSeries.C a) = x a) ∧ f PowerSeries.X = PowerSeries.X := by
  intro R K _ _ x
  letI : UniformSpace R := ⊥
  letI : UniformSpace K := ⊥
  haveI : DiscreteUniformity R := ⟨rfl⟩
  haveI : DiscreteUniformity K := ⟨rfl⟩
  refine ⟨PowerSeries.eval₂Hom (φ := x) (a := PowerSeries.X) continuous_of_discreteTopology
    PowerSeries.HasEval.X, ?_, ?_⟩
  · intro a
    rw [PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C]
  · rw [PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]
end

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem root_const {O K : Type} [CommRing O] [Field K] [Algebra O K] (P : Polynomial O) (hm : P.Monic)
    (hs : (P.map (algebraMap O K)).Splits) (y : PowerSeries K)
    (hy : Polynomial.eval₂ (algebraMap O (PowerSeries K)) y P = 0) : ∃ c : K, y = PowerSeries.C c := by
  have h : algebraMap O (PowerSeries K) = (PowerSeries.C : K →+* PowerSeries K).comp (algebraMap O K) :=
    RingHom.ext fun a => PowerSeries.algebraMap_apply
  rw [h, ← Polynomial.eval₂_map, hs.eq_prod_roots_of_monic (hm.map _), Polynomial.eval₂_multiset_prod,
    Multiset.prod_eq_zero_iff, Multiset.map_map, Multiset.mem_map] at hy
  obtain ⟨c, -, hc⟩ := hy
  simp only [Function.comp_apply, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at hc
  exact ⟨c, sub_eq_zero.1 hc⟩

private theorem surj_of_card {O' K : Type} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Field K]
    [Finite K] (φ : O' →+* K) (hc : Nat.card (ResidueField O') = Nat.card K) : Function.Surjective φ := by
  have hne : RingHom.ker φ ≠ ⊥ := by
    intro h
    have hi : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 h
    haveI : Finite O' := Finite.of_injective φ hi
    exact IsDiscreteValuationRing.not_isField O' (Finite.isField_of_domain O')
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hmax : RingHom.ker φ = maximalIdeal O' :=
    IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne inferInstance)
  let g : ResidueField O' →+* K := Ideal.Quotient.lift (maximalIdeal O') φ (fun a ha => by
    rw [← hmax] at ha; exact ha)
  have hg : Function.Bijective g := by
    haveI : Finite (ResidueField O') := Finite.of_injective g g.injective
    exact (Nat.bijective_iff_injective_and_card g).2 ⟨g.injective, hc⟩
  intro k
  obtain ⟨a, ha⟩ := hg.2 k
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨b, ha⟩

private theorem exists_pt {O O' B K : Type} [CommRing O] [CommRing O'] [Algebra O O'] [CommRing B] [Algebra O B]
    [Field K] [Algebra O K] (α : O') (P : Polynomial O) (f : B →ₐ[O] PowerSeries K) (Q : Ideal (O' ⊗[O] B))
    (hα : Algebra.adjoin O {α} = ⊤) (hm : P.Monic) (h0 : Polynomial.aeval α P = 0)
    (hs : (P.map (algebraMap O K)).Splits) (hQ : Q.IsPrime)
    (hc : Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = RingHom.ker f) :
    ∃ x : O' ⊗[O] B →+* PowerSeries K, (∀ b, x (1 ⊗ₜ b) = f b) ∧ RingHom.ker x = Q := by
  letI : Algebra B (O' ⊗[O] B) := Algebra.TensorProduct.rightAlgebra
  have hB : ∀ b : B, algebraMap B (O' ⊗[O] B) b = 1 ⊗ₜ b := fun b => rfl
  have hcomp : (algebraMap B (O' ⊗[O] B)).comp (algebraMap O B) =
      (Algebra.TensorProduct.includeLeftRingHom : O' →+* O' ⊗[O] B).comp (algebraMap O O') :=
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm
  obtain ⟨x, hx1, hx2⟩ := UpperTheory.V.AlgebraTools.exists_lift_ker_eq B (O' ⊗[O] B) (PowerSeries K) f.toRingHom Unit
    (fun _ => α ⊗ₜ 1) (fun _ => P.map (algebraMap O B)) (by
      have hl : ∀ o : O', o ⊗ₜ[O] (1 : B) ∈ Algebra.adjoin B (Set.range fun _ : Unit => α ⊗ₜ[O] (1 : B)) := by
        intro o
        have ho : o ∈ Algebra.adjoin O {α} := hα ▸ Algebra.mem_top
        induction ho using Algebra.adjoin_induction with
        | mem y hy =>
          rw [Set.mem_singleton_iff.1 hy]
          exact Algebra.subset_adjoin ⟨(), rfl⟩
        | algebraMap r =>
          have := RingHom.congr_fun hcomp r
          change algebraMap B (O' ⊗[O] B) (algebraMap O B r) = algebraMap O O' r ⊗ₜ 1 at this
          rw [← this]
          exact Subalgebra.algebraMap_mem _ _
        | add y z _ _ hy hz => rw [TensorProduct.add_tmul]; exact add_mem hy hz
        | mul y z _ _ hy hz =>
          have := mul_mem hy hz
          rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one] at this
      rw [eq_top_iff]
      rintro s -
      induction s using TensorProduct.induction_on with
      | zero => exact zero_mem _
      | tmul o b =>
        have := mul_mem (hl o) (Subalgebra.algebraMap_mem _ b)
        rwa [hB, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
      | add y z hy hz => exact add_mem hy hz)
    (fun _ => ⟨hm.map _, by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
      have := Polynomial.hom_eval₂ P (algebraMap O O')
        (Algebra.TensorProduct.includeLeftRingHom : O' →+* O' ⊗[O] B) α
      rw [← Polynomial.aeval_def, h0, map_zero] at this
      exact this.symm, by
      have h : f.toRingHom.comp (algebraMap O B) = (PowerSeries.C : K →+* PowerSeries K).comp (algebraMap O K) :=
        RingHom.ext fun a => (f.commutes a).trans PowerSeries.algebraMap_apply
      rw [Polynomial.map_map, h, ← Polynomial.map_map]
      exact hs.map _⟩) Q hQ hc
  exact ⟨x, fun b => RingHom.congr_fun hx1 b, hx2⟩

theorem UpperTheory.V.Pa.BC.pt_lift :
    ∀ (l : ℕ) [Fact l.Prime] (O O' : Type) [CommRing O] [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [IsCoef l O'] [Algebra O O'] (α : O') (P : Polynomial O) (B : Type) [CommRing B] [Algebra O B] (K : Type) [Field K] [Finite K] [Algebra O K] (f : B →ₐ[O] PowerSeries K) (Q : Ideal (O' ⊗[O] B)), Algebra.adjoin O {α} = ⊤ → P.Monic → Polynomial.aeval α P = 0 → (P.map (algebraMap O K)).Splits → Nat.card (ResidueField O') = Nat.card K → Q.IsPrime → Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = RingHom.ker f → ∃ (_ : Algebra O' K) (f' : Til O O' B →ₐ[O'] PowerSeries K), Function.Surjective (algebraMap O' K) ∧ (∀ b, f' (Til.ι O O' B b) = f b) ∧ f' (Til.s O O' B) = PowerSeries.X ∧ (RingHom.ker f').comap (Til.C O O' B) = Q := by
  intro l _ O O' _ _ _ _ _ _ α P B _ _ K _ _ _ f Q hα hm h0 hs hcard hQ hc
  obtain ⟨x, hx1, hx2⟩ := exists_pt α P f Q hα hm h0 hs hQ hc
  let y : O' →+* PowerSeries K := x.comp (Algebra.TensorProduct.includeLeftRingHom : O' →+* O' ⊗[O] B)
  have hyO : y.comp (algebraMap O O') = algebraMap O (PowerSeries K) := by
    refine RingHom.ext fun r => ?_
    have := RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := O) (A := O') (B := B)) r
    change x ((Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap O O')) r) = _
    rw [this]
    exact (hx1 _).trans (f.commutes r)
  have hconst : ∀ o : O', ∃ c : K, y o = PowerSeries.C c := by
    intro o
    have ho : o ∈ Algebra.adjoin O {α} := hα ▸ Algebra.mem_top
    induction ho using Algebra.adjoin_induction with
    | mem z hz =>
      rw [Set.mem_singleton_iff.1 hz]
      refine root_const P hm hs _ ?_
      rw [← hyO, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, h0, map_zero]
    | algebraMap r => exact ⟨algebraMap O K r, (RingHom.congr_fun hyO r).trans PowerSeries.algebraMap_apply⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha⟩ := ha
      obtain ⟨b', hb⟩ := hb
      exact ⟨a' + b', by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨a', ha⟩ := ha
      obtain ⟨b', hb⟩ := hb
      exact ⟨a' * b', by rw [map_mul, map_mul, ha, hb]⟩
  let φ : O' →+* K := (PowerSeries.constantCoeff : PowerSeries K →+* K).comp y
  have hφ : ∀ o, y o = PowerSeries.C (φ o) := by
    intro o
    obtain ⟨c, hc⟩ := hconst o
    change _ = PowerSeries.C (PowerSeries.constantCoeff (y o))
    rw [hc, PowerSeries.constantCoeff_C]
  obtain ⟨g, hg1, hg2⟩ := UpperTheory.V.Pa.BC.ps_ev (O' ⊗[O] B) K x
  letI : Algebra O' K := φ.toAlgebra
  let g' : Til O O' B →+* PowerSeries K := g
  have hg1' : ∀ a, g' (Til.C O O' B a) = x a := hg1
  refine ⟨this, { g' with commutes' := fun o => ?_ }, surj_of_card φ hcard, fun b => ?_, hg2, ?_⟩
  · have h : algebraMap O' (Til O O' B) o = Til.C O O' B (algebraMap O' (O' ⊗[O] B) o) :=
      PowerSeries.algebraMap_apply
    change g' (algebraMap O' (Til O O' B) o) = _
    rw [h, hg1', PowerSeries.algebraMap_apply]
    exact hφ o
  · exact (hg1' _).trans (hx1 b)
  · ext a
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hx2, RingHom.mem_ker, ← hg1']
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilMvps
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

noncomputable section

namespace UpperTheory.V.Pa.BC

section swap
variable (K A σ : Type) [CommRing K] [CommRing A] [Algebra K A]

private def swF (f : PowerSeries (MvPowerSeries σ A)) : MvPowerSeries σ (PowerSeries A) :=
  fun n => PowerSeries.mk fun k => MvPowerSeries.coeff n (PowerSeries.coeff k f)

private theorem coeff_swF (f : PowerSeries (MvPowerSeries σ A)) (n : σ →₀ ℕ) (k : ℕ) :
    PowerSeries.coeff k (MvPowerSeries.coeff n (swF A σ f)) = MvPowerSeries.coeff n (PowerSeries.coeff k f) :=
  PowerSeries.coeff_mk k (fun k => MvPowerSeries.coeff n (PowerSeries.coeff k f))

private def sw : PowerSeries (MvPowerSeries σ A) →ₐ[K] MvPowerSeries σ (PowerSeries A) where
  toFun := swF A σ
  map_one' := by
    classical
    ext n k
    rw [coeff_swF]
    by_cases hn : n = 0 <;> by_cases hk : k = 0 <;>
      simp [PowerSeries.coeff_one, MvPowerSeries.coeff_one, hn, hk]
  map_mul' f g := by
    classical
    ext n k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [coeff_swF, PowerSeries.coeff_mul, MvPowerSeries.coeff_mul, map_sum]
    exact Finset.sum_comm
  map_zero' := by
    ext n k
    simp [coeff_swF]
  map_add' f g := by
    ext n k
    simp [coeff_swF]
  commutes' r := by
    classical
    ext n k
    rw [coeff_swF, PowerSeries.algebraMap_apply, PowerSeries.coeff_C, MvPowerSeries.algebraMap_apply,
      MvPowerSeries.algebraMap_apply (A := PowerSeries A), PowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
    by_cases hn : n = 0 <;> by_cases hk : k = 0 <;>
      simp [PowerSeries.coeff_C, MvPowerSeries.coeff_C, hn, hk]

private theorem sw_bij : Function.Bijective (sw K A σ) := by
  constructor
  · intro f g h
    ext k n
    have := congrArg (fun x => PowerSeries.coeff k (MvPowerSeries.coeff n x)) h
    simpa only [sw, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, coeff_swF] using this
  · intro g
    refine ⟨PowerSeries.mk fun k => (fun n => PowerSeries.coeff k (MvPowerSeries.coeff n g) : MvPowerSeries σ A), ?_⟩
    ext n k
    refine (coeff_swF A σ (PowerSeries.mk fun k =>
      (fun n => PowerSeries.coeff k (MvPowerSeries.coeff n g) : MvPowerSeries σ A)) n k).trans ?_
    exact congrArg (MvPowerSeries.coeff n) (PowerSeries.coeff_mk (R := MvPowerSeries σ A) k
      (fun k => (fun n => PowerSeries.coeff k (MvPowerSeries.coeff n g) : MvPowerSeries σ A)))

end swap

section tens
variable (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (R : Type) [CommRing R] [Algebra O R] (σ : Type)

private def ph : O' ⊗[O] MvPowerSeries σ R →ₐ[O'] MvPowerSeries σ (O' ⊗[O] R) :=
  Algebra.TensorProduct.lift (Algebra.ofId O' _)
    (MvPowerSeries.mapAlgHom (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R)) (fun _ _ => Commute.all _ _)

private def cf (n : σ →₀ ℕ) : O' ⊗[O] MvPowerSeries σ R →ₗ[O] O' ⊗[O] R :=
  LinearMap.lTensor O' ((MvPowerSeries.coeff n : MvPowerSeries σ R →ₗ[R] R).restrictScalars O)

private theorem cf_tmul (n : σ →₀ ℕ) (o : O') (f : MvPowerSeries σ R) :
    cf O O' R σ n (o ⊗ₜ f) = o ⊗ₜ MvPowerSeries.coeff n f := rfl

private theorem coeff_ph (n : σ →₀ ℕ) (x : O' ⊗[O] MvPowerSeries σ R) :
    MvPowerSeries.coeff n (ph O O' R σ x) = cf O O' R σ n x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul o f =>
    rw [cf_tmul]
    simp [ph, Algebra.ofId_apply, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C_mul, MvPowerSeries.mapAlgHom]

private theorem ph_bij [Module.Finite O O'] [Module.Free O O'] : Function.Bijective (ph O O' R σ) := by
  classical
  let b := Module.Free.chooseBasis O O'
  have key : ∀ (n : σ →₀ ℕ) (x : O' ⊗[O] MvPowerSeries σ R) i,
      TensorProduct.equivFinsuppOfBasisLeft b (cf O O' R σ n x) i =
        MvPowerSeries.coeff n (TensorProduct.equivFinsuppOfBasisLeft b x i) := by
    intro n x i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul o f =>
      rw [cf_tmul]
      simp only [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
      rfl
  constructor
  · intro x y h
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext i n
    rw [← key, ← key, ← coeff_ph, ← coeff_ph, h]
  · intro g
    refine ⟨(TensorProduct.equivFinsuppOfBasisLeft b).symm (Finsupp.equivFunOnFinite.symm fun i =>
      (fun n => TensorProduct.equivFinsuppOfBasisLeft b (MvPowerSeries.coeff n g) i : MvPowerSeries σ R)), ?_⟩
    ext n
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext i
    rw [coeff_ph, key, LinearEquiv.apply_symm_apply]
    rfl

private def tau0 : Til O O' (MvPowerSeries σ R) →ₐ[O'] MvPowerSeries σ (Til O O' R) :=
  (sw O' (O' ⊗[O] R) σ).comp (PowerSeries.mapAlgHom (ph O O' R σ))

private theorem coeff_power_series_restriction (a : Til O O' (MvPowerSeries σ R)) (n : σ →₀ ℕ) (k : ℕ) :
    Til.coeff O O' R k (MvPowerSeries.coeff n (tau0 O O' R σ a)) = cf O O' R σ n (Til.coeff O O' _ k a) := by
  rw [← coeff_ph]
  exact coeff_swF (O' ⊗[O] R) σ (PowerSeries.mapAlgHom (ph O O' R σ) a) n k

private theorem til_ext {a b : Til O O' R} (h : ∀ k, Til.coeff O O' R k a = Til.coeff O O' R k b) : a = b :=
  PowerSeries.ext h

private theorem power_series_restriction_bijective [Module.Finite O O'] [Module.Free O O'] : Function.Bijective (tau0 O O' R σ) := by
  refine (sw_bij O' (O' ⊗[O] R) σ).comp (f := PowerSeries.map (ph O O' R σ).toRingHom) ⟨?_, ?_⟩
  · exact PowerSeries.map_injective _ (ph_bij O O' R σ).1
  · exact PowerSeries.map_surjective _ (ph_bij O O' R σ).2

private theorem coeff_ι (a : R) (k : ℕ) :
    Til.coeff O O' R k (Til.ι O O' R a) = if k = 0 then (1 : O') ⊗ₜ[O] a else 0 :=
  PowerSeries.coeff_C _ _

private theorem coeff_alt (k : ℕ) :
    Til.coeff O O' R k (Til.s O O' R) = if k = 1 then 1 else 0 :=
  PowerSeries.coeff_X _

private theorem coeff_zero' (k : ℕ) : Til.coeff O O' R k 0 = 0 :=
  map_zero (PowerSeries.coeff k : PowerSeries (O' ⊗[O] R) →ₗ[O' ⊗[O] R] _)

private theorem coeff_map' {R' : Type} [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') (a : Til O O' R) (k : ℕ) :
    Til.coeff O O' R' k (Til.map O' f a) = Algebra.TensorProduct.map (AlgHom.id O' O') f (Til.coeff O O' R k a) := rfl

end tens

end UpperTheory.V.Pa.BC

open UpperTheory.V.Pa.BC in
theorem UpperTheory.V.Pa.BC.til_mvps :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] (R : Type) [CommRing R] [Algebra O R] (σ : Type) [Finite σ], ∃ τ : Til O O' (MvPowerSeries σ R) ≃ₐ[O'] MvPowerSeries σ (Til O O' R), (∀ a, τ (Til.ι O O' _ a) = MvPowerSeries.map (Til.ι O O' R) a) ∧ τ (Til.s O O' _) = MvPowerSeries.C (Til.s O O' R) ∧ (∀ a, τ (Til.map O' (IsScalarTower.toAlgHom O R (MvPowerSeries σ R)) a) = MvPowerSeries.C a) ∧ ∀ (c : MvPowerSeries σ R →ₐ[O] R), (∀ z, c z = MvPowerSeries.constantCoeff z) → ∀ a, MvPowerSeries.constantCoeff (τ a) = Til.map O' c a := by
  intro O O' _ _ _ _ _ R _ _ σ _
  classical
  refine ⟨AlgEquiv.ofBijective (tau0 O O' R σ) (power_series_restriction_bijective O O' R σ), ?_, ?_, ?_, ?_⟩
  · intro a
    refine MvPowerSeries.ext fun n => til_ext O O' R fun k => ?_
    rw [AlgEquiv.ofBijective_apply, coeff_power_series_restriction, MvPowerSeries.coeff_map, coeff_ι, coeff_ι]
    split_ifs
    · rfl
    · exact map_zero _
  · refine MvPowerSeries.ext fun n => til_ext O O' R fun k => ?_
    rw [AlgEquiv.ofBijective_apply, coeff_power_series_restriction, MvPowerSeries.coeff_C, coeff_alt]
    by_cases hn : n = 0
    · rw [if_pos hn, coeff_alt]
      split_ifs
      · rw [Algebra.TensorProduct.one_def, cf_tmul, hn, MvPowerSeries.coeff_zero_one]; rfl
      · exact map_zero _
    · rw [if_neg hn, coeff_zero']
      split_ifs
      · rw [Algebra.TensorProduct.one_def, cf_tmul, MvPowerSeries.coeff_one, if_neg hn, TensorProduct.tmul_zero]
      · exact map_zero _
  · intro a
    refine MvPowerSeries.ext fun n => til_ext O O' R fun k => ?_
    rw [AlgEquiv.ofBijective_apply, coeff_power_series_restriction, MvPowerSeries.coeff_C, coeff_map']
    have h : ∀ x : O' ⊗[O] R, cf O O' R σ n (Algebra.TensorProduct.map (AlgHom.id O' O')
        (IsScalarTower.toAlgHom O R (MvPowerSeries σ R)) x) = if n = 0 then x else 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]; split_ifs <;> simp
      | tmul o r =>
        rw [Algebra.TensorProduct.map_tmul, cf_tmul]
        split_ifs with hn <;> simp [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, hn]
    rw [h]
    split_ifs
    · rfl
    · exact (coeff_zero' O O' R k).symm
  · intro c hc a
    refine til_ext O O' R fun k => ?_
    rw [AlgEquiv.ofBijective_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_power_series_restriction, coeff_map']
    generalize Til.coeff O O' _ k a = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | tmul o r =>
      rw [Algebra.TensorProduct.map_tmul, cf_tmul, hc]
      rfl
end
end
