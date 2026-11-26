module

public import Development.AutomorphicArithmetic.RealSpanData.RealData

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.LiftBaseChangeRealBijectiveOfLattice
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

theorem UpperTheory.liftBaseChange_real_bijective_of_lattice :
    ∀ (g : ℕ) (V La : Type) [AddCommGroup V] [Module ℚ V] [AddCommGroup La] [Module.Finite ℤ La] [Module.Free ℤ La] (j : La →+ V), Function.Injective j → Submodule.span ℚ (Set.range j) = ⊤ → ∀ P : La →+ (Fin g → ℂ), Function.Injective P → DiscreteTopology P.range → Submodule.span ℝ (Set.range P) = ⊤ → ∀ Pq : V →ₗ[ℚ] (Fin g → ℂ), (∀ z, Pq (j z) = P z) → Function.Bijective (LinearMap.liftBaseChange ℝ Pq) := by
  intro g V La _ _ _ _ _ j hj hspan P hP hdisc hPspan Pq hPq
  classical
  have hsurj : Function.Surjective (LinearMap.liftBaseChange ℝ Pq) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hPspan, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    exact ⟨(1 : ℝ) ⊗ₜ j z, by simp [LinearMap.liftBaseChange_tmul, hPq]⟩
  let L : Submodule ℤ (Fin g → ℂ) := P.range.toIntSubmodule
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨by simpa [L] using hPspan⟩
  have hrank : Module.finrank ℤ La = Module.finrank ℝ (Fin g → ℂ) := by
    rw [← ZLattice.rank ℝ L]
    exact LinearEquiv.finrank_eq (LinearEquiv.ofInjective P.toIntLinearMap hP)
  let b := Module.Free.chooseBasis ℤ La
  have hsub : ∀ z, j z ∈ Submodule.span ℚ (Set.range (j ∘ b)) := by
    intro z
    have htop : ((Submodule.span ℚ (Set.range (j ∘ b))).restrictScalars ℤ).comap j.toIntLinearMap = ⊤ := by
      rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    have : z ∈ ((Submodule.span ℚ (Set.range (j ∘ b))).restrictScalars ℤ).comap j.toIntLinearMap := by
      rw [htop]; trivial
    exact this
  have hVspan : Submodule.span ℚ (Set.range (j ∘ b)) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    exact hsub z
  haveI : Module.Finite ℚ V := ⟨⟨Finset.univ.image (j ∘ b), by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]; exact hVspan⟩⟩
  have hV : Module.finrank ℚ V ≤ Module.finrank ℤ La := by
    rw [Module.finrank_eq_card_chooseBasisIndex ℤ La, ← finrank_top, ← hVspan]
    exact finrank_range_le_card (b := j ∘ b)
  have hdim : Module.finrank ℝ (ℝ ⊗[ℚ] V) = Module.finrank ℝ (Fin g → ℂ) := by
    refine le_antisymm ?_ ?_
    · rw [Module.finrank_baseChange]; omega
    · calc Module.finrank ℝ (Fin g → ℂ)
          = Module.finrank ℝ (⊤ : Submodule ℝ (Fin g → ℂ)) := (finrank_top ℝ _).symm
        _ = Module.finrank ℝ (LinearMap.range (LinearMap.liftBaseChange ℝ Pq)) := by
          rw [LinearMap.range_eq_top.mpr hsurj]
        _ ≤ _ := LinearMap.finrank_range_le _
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.CommutantEqRangeActOnAndInjective
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSumBaseChangeOfCommuteBaseChange
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

theorem UpperTheory.exists_sum_baseChange_of_commute_baseChange :
    ∀ (κ V V' R : Type) [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V'] [FiniteDimensional ℚ V] [FiniteDimensional ℚ V'] [CommRing R] [Algebra ℚ R] (a : κ → Module.End ℚ V) (a' : κ → Module.End ℚ V') (T : (R ⊗[ℚ] V') →ₗ[R] (R ⊗[ℚ] V)), (∀ i, T ∘ₗ (a' i).baseChange R = (a i).baseChange R ∘ₗ T) → ∃ (k : ℕ) (r : Fin k → R) (h : Fin k → V' →ₗ[ℚ] V), (∀ l i, h l ∘ₗ a' i = a i ∘ₗ h l) ∧ T = ∑ l, r l • (h l).baseChange R := by
  intro κ V V' R _ _ _ _ _ _ _ _ a a' T hT
  classical
  set bV' := Module.finBasis ℚ V'
  set bV := Module.finBasis ℚ V
  set B := Algebra.TensorProduct.basis R bV
  let M : Fin (Module.finrank ℚ V') × Fin (Module.finrank ℚ V) → R :=
    fun p => B.repr (T (1 ⊗ₜ bV' p.1)) p.2
  let S : Submodule ℚ R := Submodule.span ℚ (Set.range M)
  haveI : FiniteDimensional ℚ S := FiniteDimensional.span_of_finite ℚ (Set.finite_range M)
  let bS := Module.finBasis ℚ S
  let r : Fin (Module.finrank ℚ S) → R := fun l => (bS l : R)
  have hr : LinearIndependent ℚ r := bS.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  let c : Fin (Module.finrank ℚ S) → Fin (Module.finrank ℚ V') × Fin (Module.finrank ℚ V) → ℚ :=
    fun l p => bS.repr ⟨M p, Submodule.subset_span ⟨p, rfl⟩⟩ l
  have hM : ∀ p, M p = ∑ l, c l p • r l := by
    intro p
    have e := congrArg Subtype.val (bS.sum_repr ⟨M p, Submodule.subset_span ⟨p, rfl⟩⟩)
    rw [Submodule.coe_sum] at e
    exact e.symm
  let h : Fin (Module.finrank ℚ S) → V' →ₗ[ℚ] V :=
    fun l => bV'.constr ℚ (fun j => ∑ i, c l (j, i) • bV i)
  have key : ∀ w : Fin (Module.finrank ℚ S) → V, ∑ l, r l ⊗ₜ[ℚ] w l = 0 → ∀ l, w l = 0 := by
    intro w hw l
    apply bV.ext_elem
    intro i
    have h1 := congrArg (fun x => B.repr x i) hw
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.sum_apply', B,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
    have h2 : ∑ l, bV.repr (w l) i • r l = 0 := by
      rw [← h1]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Algebra.smul_def, mul_comm]
    have h3 := Fintype.linearIndependent_iff.1 hr (fun l => bV.repr (w l) i) h2 l
    simpa using h3
  have hT1 : ∀ x : V', T (1 ⊗ₜ x) = ∑ l, r l ⊗ₜ[ℚ] h l x := by
    have e : (T.restrictScalars ℚ).comp (TensorProduct.mk ℚ R V' 1) =
        ∑ l, (TensorProduct.mk ℚ R V (r l)).comp (h l) := by
      refine bV'.ext fun j => ?_
      have hs : T (1 ⊗ₜ bV' j) = ∑ i, M (j, i) ⊗ₜ[ℚ] bV i := by
        conv_lhs => rw [← B.sum_repr (T (1 ⊗ₜ bV' j))]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Algebra.TensorProduct.basis_repr_symm_apply' bV _ i
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
        LinearMap.sum_apply, h, Module.Basis.constr_basis]
      rw [hs]
      simp only [hM, TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
      exact Finset.sum_comm
    intro x
    have e2 := LinearMap.congr_fun e x
    simpa using e2
  refine ⟨Module.finrank ℚ S, r, h, ?_, ?_⟩
  · intro l i
    have hw : ∀ v : V', ∑ l, r l ⊗ₜ[ℚ] (h l (a' i v) - a i (h l v)) = 0 := by
      intro v
      have e := LinearMap.congr_fun (hT i) (1 ⊗ₜ v)
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul] at e
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hT1, hT1, map_sum] at e
      simp only [LinearMap.baseChange_tmul] at e
      simp only [TensorProduct.tmul_sub, Finset.sum_sub_distrib, e, sub_self]
    ext v
    have h4 := key _ (hw v) l
    simpa [sub_eq_zero] using h4
  · ext m
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.restrictScalars_apply]
    rw [hT1]
    simp [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul,
      TensorProduct.smul_tmul']
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

private theorem actOn_tmul {C V R : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    [CommRing R] [Algebra ℚ R] (rep : C →ₐ[ℚ] Module.End ℚ V) (r s : R) (c : C) (v : V) :
    actOn rep R (r ⊗ₜ c) (s ⊗ₜ v) = (r * s) ⊗ₜ rep c v := by
  have e : actOn rep R (r ⊗ₜ c) = Algebra.ofId R _ r * (Module.End.baseChangeHom ℚ R V) (rep c) :=
    Algebra.TensorProduct.lift_tmul _ _ _ r c
  rw [e]
  change r • ((rep c).baseChange R (s ⊗ₜ v)) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

private theorem actOn_inj {C V R : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V]
    [CommRing R] [Algebra ℚ R] (rep : C →ₐ[ℚ] Module.End ℚ V) (hrep : Function.Injective rep) :
    Function.Injective (actOn rep R) := by
  classical
  have main : ∀ z : R ⊗[ℚ] C, actOn rep R z = 0 → z = 0 := by
    intro z hz
    let bR := Module.Basis.ofVectorSpace ℚ R
    let bC := Module.Basis.ofVectorSpace ℚ C
    let Ψ : (R →ₗ[ℚ] ℚ) → R ⊗[ℚ] C →ₗ[ℚ] C :=
      fun f => (TensorProduct.lid ℚ C).toLinearMap ∘ₗ LinearMap.rTensor C f
    let Φ : (R →ₗ[ℚ] ℚ) → R ⊗[ℚ] V →ₗ[ℚ] V :=
      fun f => (TensorProduct.lid ℚ V).toLinearMap ∘ₗ LinearMap.rTensor V f
    have hΦ : ∀ f (w : R ⊗[ℚ] C) (v : V), Φ f (actOn rep R w (1 ⊗ₜ v)) = rep (Ψ f w) v := by
      intro f w v
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul r c => simp [Φ, Ψ, actOn_tmul]
      | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
    have hΨ : ∀ f, Ψ f z = 0 := by
      intro f
      apply hrep
      rw [map_zero]
      refine LinearMap.ext fun v => ?_
      rw [LinearMap.zero_apply, ← hΦ, hz, LinearMap.zero_apply, map_zero]
    have hrepr : ∀ (w : R ⊗[ℚ] C) i j,
        (bR.tensorProduct bC).repr w (i, j) = bC.repr (Ψ (bR.coord i) w) j := by
      intro w i j
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul r c => simp [Ψ, Module.Basis.tensorProduct_repr_tmul_apply, mul_comm]
      | add a b ha hb => simp only [map_add (f := _), Finsupp.add_apply, ha, hb]
    apply (bR.tensorProduct bC).repr.injective
    ext ⟨i, j⟩
    rw [hrepr, hΨ]
    simp
  intro x y hxy
  rw [← sub_eq_zero]
  apply main
  rw [map_sub, hxy, sub_self]

theorem UpperTheory.commutant_eq_range_actOn_and_injective :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R], (∀ A : Module.End R (R ⊗[ℚ] VQ D), (∀ b : D.O, A ∘ₗ (actQ D b).baseChange R = (actQ D b).baseChange R ∘ₗ A) → ∃ c : R ⊗[ℚ] G.C, actOn L.rep R c = A) ∧ Function.Injective (actOn L.rep R) := by
  intro p _ D G L R _ _
  haveI : Module.Finite ℤ D.La := D.finLa
  refine ⟨fun A hA => ?_, actOn_inj L.rep L.rep_inj⟩
  obtain ⟨k, r, h, hh, hA'⟩ := UpperTheory.exists_sum_baseChange_of_commute_baseChange D.O (VQ D) (VQ D) R (actQ D) (actQ D) A hA
  have hx : ∀ l, ∃ x, L.rep x = h l := fun l => (L.rep_range (h l)).2 (fun b => hh l b)
  choose x hx using hx
  refine ⟨∑ l, r l ⊗ₜ[ℚ] x l, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hA', map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine TensorProduct.AlgebraTensorModule.curry_injective (LinearMap.ext_ring (LinearMap.ext fun v => ?_))
  simp only [TensorProduct.AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_apply,
    TensorProduct.curry_apply, actOn_tmul, LinearMap.smul_apply, LinearMap.baseChange_tmul,
    hx, _root_.mul_one, TensorProduct.smul_tmul', smul_eq_mul]
end
end
