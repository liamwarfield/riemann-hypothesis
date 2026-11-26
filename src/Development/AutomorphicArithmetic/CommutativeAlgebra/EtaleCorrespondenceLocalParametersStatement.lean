module

public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EFam
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsIntegralRBIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.TanConjEt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsUnitMulMemSpanOfReducedIsolatedZero
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 KaehlerDifferential
open scoped TensorProduct

private theorem exists_algHom_complex_ker_eq_maximal (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    (m : Ideal A) [m.IsMaximal] : ∃ e : A →ₐ[ℂ] ℂ, ∀ x, e x = 0 ↔ x ∈ m := by
  letI := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ m)
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ) (K := A ⧸ m)
  let φ := AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ m)) hb
  refine ⟨φ.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ m), fun x => ?_⟩
  show φ.symm (Ideal.Quotient.mkₐ ℂ m x) = 0 ↔ _
  rw [map_eq_zero_iff _ φ.symm.injective, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]

private theorem mem_of_reduced_vanishing_on_zeros (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    (J : Ideal A) (hred : IsReduced (A ⧸ J)) (x : A)
    (hx : ∀ e : A →ₐ[ℂ] ℂ, (∀ y ∈ J, e y = 0) → e x = 0) : x ∈ J := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℂ)
  have hj : x ∈ J.jacobson := by
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro m ⟨hJm, hm⟩
    haveI := hm
    obtain ⟨e, he⟩ := exists_algHom_complex_ker_eq_maximal A m
    exact (he x).1 (hx e fun y hy => (he y).2 (hJm hy))
  rw [← Ideal.radical_eq_jacobson] at hj
  obtain ⟨n, hn⟩ := hj
  haveI := hred
  have hnil : IsNilpotent (Ideal.Quotient.mk J x) :=
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn⟩
  exact Ideal.Quotient.eq_zero_iff_mem.1 hnil.eq_zero

theorem UpperTheory.Cb.exists_unit_mul_mem_span_of_reduced_isolated_zero :
    ∀ (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (d : ℕ) (t : Fin d → A), IsReduced (A ⧸ Ideal.span (Set.range t)) → Finite {e : A →ₐ[ℂ] ℂ // ∀ j, e (t j) = 0} → ∀ e : A →ₐ[ℂ] ℂ, (∀ j, e (t j) = 0) → ∀ b : A, e b = 0 → ∃ (c : A) (g : Fin d → A), e c ≠ 0 ∧ c * b = ∑ l, g l * t l := by
  intro A _ _ _ d t hred hfin e he b hb
  have key : ∀ s : {e' : A →ₐ[ℂ] ℂ // ∀ j, e' (t j) = 0},
      ∃ a : A, e a ≠ 0 ∧ (s.1 ≠ e → s.1 a = 0) := by
    intro s
    by_cases hs : s.1 = e
    · exact ⟨1, by simp, fun h => absurd hs h⟩
    · obtain ⟨y, hy⟩ : ∃ y, e y ≠ s.1 y := by
        by_contra hcon
        push_neg at hcon
        exact hs (AlgHom.ext fun y => (hcon y).symm)
      refine ⟨y - algebraMap ℂ A (s.1 y), ?_, fun _ => ?_⟩
      · rw [map_sub, AlgHom.commutes]
        exact sub_ne_zero.2 hy
      · rw [map_sub, AlgHom.commutes]
        exact sub_self _
  choose f hf using key
  haveI := Fintype.ofFinite {e' : A →ₐ[ℂ] ℂ // ∀ j, e' (t j) = 0}
  refine ⟨∏ s, f s, ?_⟩
  have hmem : (∏ s, f s) * b ∈ Ideal.span (Set.range t) := by
    apply mem_of_reduced_vanishing_on_zeros A _ hred
    intro e' he'
    have ht : ∀ j, e' (t j) = 0 := fun j => he' _ (Ideal.subset_span ⟨j, rfl⟩)
    by_cases hee : e' = e
    · subst hee
      rw [map_mul, hb, mul_zero]
    · rw [map_mul, map_prod, Finset.prod_eq_zero (Finset.mem_univ ⟨e', ht⟩) ((hf ⟨e', ht⟩).2 hee),
        zero_mul]
  obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.1 hmem
  refine ⟨g, ?_, hg.symm⟩
  rw [map_prod]
  exact Finset.prod_ne_zero_iff.2 fun s _ => (hf s).1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteEtaleFunctionFieldGermCompatOfSmooth
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 KaehlerDifferential
open scoped TensorProduct

namespace UpperTheory

private theorem reduced_of_etale_proj (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsReduced R]
    [Algebra.Etale R S] [Module.Projective R S] : IsReduced S := by
  refine ⟨fun s hs => ?_⟩
  by_contra hne
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual R S, φ s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne ((Module.forall_dual_apply_eq_zero_iff R s).1 h)
  have hnil : φ s ∉ nilradical R := by
    rw [nilradical_eq_zero]; simpa using hφ
  rw [nilradical_eq_sInf, Ideal.mem_sInf] at hnil
  push_neg at hnil
  obtain ⟨p, hp, hsp⟩ := hnil
  haveI : p.IsPrime := hp
  let κ := p.ResidueField
  haveI : IsReduced (κ ⊗[R] S) := Algebra.FormallyUnramified.isReduced_of_field κ (κ ⊗[R] S)
  have h0 : (1 : κ) ⊗ₜ[R] s = 0 := by
    have : IsNilpotent ((Algebra.TensorProduct.includeRight : S →ₐ[R] κ ⊗[R] S) s) := hs.map _
    simpa using this.eq_zero
  have h1 := congrArg ((TensorProduct.rid R κ).toLinearMap ∘ₗ LinearMap.lTensor κ φ) h0
  simp at h1
  rw [Algebra.smul_def, mul_one] at h1
  exact hsp (Ideal.algebraMap_residueField_eq_zero.1 h1)

private theorem reduced_quot (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B'] [Algebra.Etale B B']
    [Module.Projective B B'] (I : Ideal B) [IsReduced (B ⧸ I)] : IsReduced (B' ⧸ I.map (algebraMap B B')) := by
  haveI : IsReduced ((B ⧸ I) ⊗[B] B') := reduced_of_etale_proj (B ⧸ I) ((B ⧸ I) ⊗[B] B')
  have e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B' I
  haveI : IsReduced (B' ⊗[B] (B ⧸ I)) := isReduced_of_injective (Algebra.TensorProduct.comm B B' (B ⧸ I)).toRingEquiv (Algebra.TensorProduct.comm B B' (B ⧸ I)).injective
  exact isReduced_of_injective e.toRingEquiv e.injective

private theorem transfer {A A' B B' ι : Type} [CommRing A] [CommRing A'] [CommRing B] [CommRing B'] [Algebra A A']
    [Algebra.Etale A A'] [Module.Projective A A'] (eA : A ≃+* B) (eA' : A' ≃+* B') (t : ι → B) (t' : ι → B')
    (ht : ∀ j, eA' (algebraMap A A' (eA.symm (t j))) = t' j) (hr : IsReduced (B ⧸ Ideal.span (Set.range t))) :
    IsReduced (B' ⧸ Ideal.span (Set.range t')) := by
  let J : Ideal A := Ideal.span (Set.range fun j => eA.symm (t j))
  have hJ : Ideal.span (Set.range t) = J.map (eA : A →+* B) := by
    simp only [J, Ideal.map_span, ← Set.range_comp]
    congr 2
    ext j
    simp
  have eq1 : (A ⧸ J) ≃+* (B ⧸ Ideal.span (Set.range t)) := Ideal.quotientEquiv J _ eA hJ
  haveI : IsReduced (A ⧸ J) := isReduced_of_injective eq1 eq1.injective
  haveI := reduced_quot A A' J
  have hJ' : Ideal.span (Set.range t') = (J.map (algebraMap A A')).map (eA' : A' →+* B') := by
    simp only [J, Ideal.map_span, ← Set.range_comp]
    congr 2
    ext j
    simp [ht]
  have eq2 := Ideal.quotientEquiv (J.map (algebraMap A A')) _ eA' hJ'
  exact isReduced_of_injective eq2.symm eq2.symm.injective

private theorem cover_ring {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    [Algebra k X.functionField] {ι : Type} [DecidableEq ι] {U : ι → X.Opens}
    {B : Finset ι → Subalgebra k X.functionField} (h : IsAffCover p U B) (i : ι) :
    IsAffineOpen (U i) ∧ ∃ hg : genericPoint X ∈ U i, ∀ y, y ∈ B {i} ↔
      ∃ f : Γ(X, U i), (X.presheaf.germ (U i) (genericPoint X) hg).hom f = y := by
  have key : ∀ (V : X.Opens) (_ : V = ({i} : Finset ι).inf U), IsAffineOpen V ∧
      ∃ hg : genericPoint X ∈ V, ∀ y, y ∈ B {i} ↔
        ∃ f : Γ(X, V), (X.presheaf.germ V (genericPoint X) hg).hom f = y := by
    rintro V rfl
    exact ⟨h.affine _ (Finset.singleton_nonempty i), h.ne _, h.ring _ (Finset.singleton_nonempty i)⟩
  exact key (U i) Finset.inf_singleton.symm

private noncomputable def chartEquiv {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [Algebra k X.functionField]
    (V : X.Opens) (hg : genericPoint X ∈ V) (B : Subalgebra k X.functionField)
    (h : ∀ y, y ∈ B ↔ ∃ f : Γ(X, V), (X.presheaf.germ V (genericPoint X) hg).hom f = y) : Γ(X, V) ≃+* B :=
  RingEquiv.ofBijective
    (((X.presheaf.germ V (genericPoint X) hg).hom).codRestrict B fun f => (h _).2 ⟨f, rfl⟩)
    (by
      refine ⟨fun a b e => ?_, fun y => ?_⟩
      · haveI : Nonempty V := ⟨⟨_, hg⟩⟩
        exact germ_injective_of_isIntegral X _ hg (congrArg Subtype.val e)
      · obtain ⟨f, hf⟩ := (h y.1).1 y.2
        exact ⟨f, Subtype.ext hf⟩)

end UpperTheory

theorem UpperTheory.Cb.finite_etale_function_field_germ_compat_of_smooth :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (c1 : Y ⟶ Z), c1 ≫ s = s' → IsFinite c1 → Etale c1 → ∀ [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Y.functionField], inst = ffAlg s → inst' = ffAlg s' → ∀ [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField], (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c1.app V g)) → ∀ (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [IsScalarTower ℂ F Z.functionField] [Algebra F Y.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens), IsFinCover ℂ Z.functionField x → IsAffCover s U (rB ℂ Z.functionField x) → IsAffCover s' (fun i => c1 ⁻¹ᵁ U i) (rB ℂ Y.functionField x) → IsReduced ((rB ℂ Z.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ Z.functionField x j⟩ : rB ℂ Z.functionField x {0})))) → IsReduced ((rB ℂ Y.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ Y.functionField x j⟩ : rB ℂ Y.functionField x {0})))) := by
  intro d Z Y _ _ s s' _ _ c1 hc hfin het inst inst' _ _ _ _ hcomp F _ _ _ _ _ _ _ x U _ hZ hY hred
  obtain ⟨hW, hg, hring⟩ := cover_ring hZ 0
  obtain ⟨-, hg', hring'⟩ := cover_ring hY 0
  letI : Algebra Γ(Z, U 0) Γ(Y, c1 ⁻¹ᵁ U 0) := (c1.app (U 0)).hom.toAlgebra
  haveI : Module.Finite Γ(Z, U 0) Γ(Y, c1 ⁻¹ᵁ U 0) := sec_finite (s := s) (s' := s') (f := c1) hW
  haveI : Algebra.Etale Γ(Z, U 0) Γ(Y, c1 ⁻¹ᵁ U 0) := sec_etale (s := s) (s' := s') (f := c1) hW
  haveI := projective_of_etale Γ(Z, U 0) Γ(Y, c1 ⁻¹ᵁ U 0)
  let eZ := chartEquiv (U 0) hg _ hring
  let eY := chartEquiv (c1 ⁻¹ᵁ U 0) hg' _ hring'
  refine transfer eZ eY _ _ (fun j => ?_) hred
  apply Subtype.ext
  obtain ⟨f, hf⟩ := eZ.surjective ⟨_, tco_mem ℂ Z.functionField x j⟩
  rw [← hf, RingEquiv.symm_apply_apply]
  have h1 : (Z.presheaf.germ (U 0) (genericPoint Z) hg).hom f = algebraMap F Z.functionField (x j.succ / x 0) :=
    congrArg Subtype.val hf
  have h2 := hcomp (U 0) hg hg' f
  rw [h1, ← IsScalarTower.algebraMap_apply] at h2
  exact h2.symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFiniteQCOmega
open CategoryTheory AlgebraicGeometry Module ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HodgeCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeFin

open GlobalTheory.CechDR GlobalTheory.QCoh

variable {k : Type} [Field k] {X : Scheme.{0}} (s : X ⟶ Sp k)

theorem finiteType_sec [LocallyOfFiniteType s] {U : X.Opens} (hU : IsAffineOpen U) :
    Algebra.FiniteType k (Sec s U) := by
  have h1 := LocallyOfFiniteType.finiteType_appLE s (isAffineOpen_top (Sp k)) hU
    (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
  exact h1.comp h2

end GlobalTheory.HodgeFin
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteFiberOfFiniteTypeParameterRing
open GlobalTheory GlobalTheory.PD

set_option autoImplicit false

noncomputable section

namespace UpperTheory

end UpperTheory

theorem UpperTheory.finite_fiber_of_finiteType_parameter_ring :
    ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]
      (d : ℕ) (x : Fin (d + 1) → F), IsPd ℂ x → Algebra.FiniteType ℂ (rB ℂ K x {0}) →
      Finite (fib ℂ K x) := by
  intro F K _ _ _ _ _ _ d x hx hft
  classical
  have hmem : ∀ c : rA ℂ x {0}, algebraMap F K (c : F) ∈ rB ℂ K x {0} := by
    intro c
    show algebraMap F K (c : F) ∈ (integralClosure (rA ℂ x {0}) K).restrictScalars ℂ
    rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
    exact isIntegral_algebraMap (x := c)
  let ι : rA ℂ x {0} →ₐ[ℂ] rB ℂ K x {0} :=
    ((IsScalarTower.toAlgHom ℂ F K).comp (rA ℂ x {0}).val).codRestrict _ hmem
  have key : ∀ e1 e2 : fib ℂ K x, ∀ c : rA ℂ x {0}, e1.1 (ι c) = e2.1 (ι c) := by
    intro e1 e2 c
    obtain ⟨c, hc⟩ := c
    induction hc using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, hi, j, rfl⟩ := hy
      rw [Finset.mem_singleton] at hi
      subst hi
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · have h3 : ∀ (e : fib ℂ K x) (h : x 0 / x 0 ∈ rA ℂ x {0}), e.1 (ι ⟨x 0 / x 0, h⟩) = 1 := by
          intro e h
          have h1 : (⟨x 0 / x 0, h⟩ : rA ℂ x {0}) = 1 := Subtype.ext (div_self (hx.ne 0))
          rw [h1, map_one, map_one]
        exact (h3 e1 _).trans (h3 e2 _).symm
      · exact (e1.2 j').trans (e2.2 j').symm
    | algebraMap r =>
      show e1.1 (ι (algebraMap ℂ (rA ℂ x {0}) r)) = e2.1 (ι (algebraMap ℂ (rA ℂ x {0}) r))
      simp only [AlgHom.commutes]
    | add y z hy hz ihy ihz =>
      show e1.1 (ι (⟨y, hy⟩ + ⟨z, hz⟩)) = e2.1 (ι (⟨y, hy⟩ + ⟨z, hz⟩))
      simp only [map_add (f := _), ihy, ihz]
    | mul y z hy hz ihy ihz =>
      show e1.1 (ι (⟨y, hy⟩ * ⟨z, hz⟩)) = e2.1 (ι (⟨y, hy⟩ * ⟨z, hz⟩))
      simp only [map_mul, ihy, ihz]
  rcases isEmpty_or_nonempty (fib ℂ K x) with hE | hE
  · infer_instance
  obtain ⟨e0⟩ := hE
  obtain ⟨s, hs⟩ := hft.out
  let ψ : rA ℂ x {0} →+* ℂ := (e0.1.comp ι).toRingHom
  have hint : ∀ b : rB ℂ K x {0}, IsIntegral (rA ℂ x {0}) (b : K) := fun b => b.2
  let R : rB ℂ K x {0} → Finset ℂ := fun b => (((hint b).choose).map ψ).roots.toFinset
  have hR : ∀ (e : fib ℂ K x) (b : rB ℂ K x {0}), e.1 b ∈ R b := by
    intro e b
    obtain ⟨hm, hp⟩ := (hint b).choose_spec
    have h0 : Polynomial.eval₂ (ι : rA ℂ x {0} →+* rB ℂ K x {0}) b (hint b).choose = 0 := by
      apply Subtype.ext
      have := Polynomial.hom_eval₂ (hint b).choose (ι : rA ℂ x {0} →+* rB ℂ K x {0})
        (rB ℂ K x {0}).val.toRingHom b
      refine this.trans ?_
      rw [Subalgebra.coe_zero]
      exact hp
    have h1 := Polynomial.hom_eval₂ (hint b).choose (ι : rA ℂ x {0} →+* rB ℂ K x {0}) e.1.toRingHom b
    rw [h0, map_zero] at h1
    have h2 : e.1.toRingHom.comp (ι : rA ℂ x {0} →+* rB ℂ K x {0}) = ψ :=
      RingHom.ext fun c => key e e0 c
    rw [h2] at h1
    have hne : ((hint b).choose.map ψ) ≠ 0 := (hm.map ψ).ne_zero
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot, Polynomial.eval_map]
    exact h1.symm
  let Φ : fib ℂ K x → ((t : s) → (R t : Set ℂ)) := fun e t => ⟨e.1 t, hR e t⟩
  apply Finite.of_injective Φ
  intro e1 e2 h
  apply Subtype.ext
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro t ht
  have := congrFun h ⟨t, ht⟩
  exact congrArg Subtype.val this
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCotangentMapDualBasisOfParameters
open KaehlerDifferential

theorem UpperTheory.exists_cotangent_map_dual_basis_of_parameters :
    ∀ {R : Type} [CommRing R] [Algebra ℂ R] (ev : R →ₐ[ℂ] ℂ) {d : ℕ} (t : Fin d → R) (ψ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ)), (∀ (b : R) (ω : Ω[R⁄ℂ]), ψ (b • ω) = ev b • ψ ω) → Function.Surjective ψ → (∀ l, ev (t l) = 0) → (∀ u : R, ev u = 0 → ∃ (c : R) (g : Fin d → R), ev c ≠ 0 ∧ c * u = ∑ l, g l * t l) → ∃ φ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ), (∀ (b : R) (ω : Ω[R⁄ℂ]), φ (b • ω) = ev b • φ ω) ∧ (∀ l, φ (D ℂ R (t l)) = Pi.single l 1) ∧ (∀ ω, φ ω = 0 → ψ ω = 0) ∧ ∀ (u c : R) (g : Fin d → R), ev u = 0 → ev c ≠ 0 → c * u = ∑ l, g l * t l → ∀ l, ev (g l) = ev c * φ (D ℂ R u) l := by
  intro R _ _ ev d t ψ hψ hsurj ht hloc
  have key : ∀ χ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ), (∀ (b : R) (ω : Ω[R⁄ℂ]), χ (b • ω) = ev b • χ ω) →
      ∀ (u c : R) (g : Fin d → R), ev u = 0 → c * u = ∑ l, g l * t l →
      ev c • χ (D ℂ R u) = ∑ l, ev (g l) • χ (D ℂ R (t l)) := by
    intro χ hχ u c g hu hcu
    have h := congrArg (fun x => χ (D ℂ R x)) hcu
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Derivation.leibniz, map_sum, map_add (f := _), hχ, hu, ht, zero_smul, add_zero] at h
    exact h
  set v : Fin d → (Fin d → ℂ) := fun l => ψ (D ℂ R (t l)) with hvdef
  have hspan : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    intro y hy
    clear hy
    obtain ⟨ω, rfl⟩ := hsurj y
    have hω : ω ∈ Submodule.span R (Set.range (D ℂ R)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      set u' := u - algebraMap ℂ R (ev u) with hu'
      have hDu : D ℂ R u = D ℂ R u' := by
        rw [hu', map_sub, Derivation.map_algebraMap, sub_zero]
      have hev : ev u' = 0 := by
        rw [hu', map_sub, AlgHom.commutes]
        simp
      obtain ⟨c, g, hc, hcu⟩ := hloc u' hev
      have h := key ψ hψ u' c g hev hcu
      rw [hDu]
      have : ψ (D ℂ R u') = (ev c)⁻¹ • ∑ l, ev (g l) • v l := by
        rw [← h, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [this]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      intro l _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [hψ]
      exact Submodule.smul_mem _ _ hx
  have hli : LinearIndependent ℂ v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp)
  set bs := Module.Basis.mk hli hspan with hbs
  have hbv : ∀ l, ψ (D ℂ R (t l)) = bs l := by
    intro l
    rw [hbs, Module.Basis.mk_apply]
  have h2 : ∀ l, (bs.equivFun.toLinearMap ∘ₗ ψ) (D ℂ R (t l)) = Pi.single l 1 := by
    intro l
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, hbv]
    ext j
    rw [Module.Basis.equivFun_self]
    by_cases hlj : l = j
    · subst hlj
      simp
    · simp [hlj, Pi.single_apply, Ne.symm hlj]
  refine ⟨bs.equivFun.toLinearMap ∘ₗ ψ, ?_, h2, ?_, ?_⟩
  · intro b ω
    simp [hψ]
  · intro ω hω
    simpa using hω
  · intro u c g hu hc hcu l
    have h := key (bs.equivFun.toLinearMap ∘ₗ ψ) (by intro b ω; simp [hψ]) u c g hu hcu
    simp only [h2] at h
    have h3 := congrFun h l
    simp [Finset.sum_apply, Pi.single_apply] at h3
    rw [← h3]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsCotangentMapLocalizationAway
open KaehlerDifferential

theorem UpperTheory.exists_cotangent_map_localization_away :
    ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S] [Algebra R S] [IsScalarTower ℂ R S] (f : R) [IsLocalization.Away f S] (ev : S →+* ℂ) {d : ℕ} (ψ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ)), (∀ (b : R) (ω : Ω[R⁄ℂ]), ψ (b • ω) = ev (algebraMap R S b) • ψ ω) → (∀ ω : Ω[R⁄ℂ], ψ ω = 0 → ∃ (m : ℕ) (b : Fin m → R) (ω' : Fin m → Ω[R⁄ℂ]), (∀ i, ev (algebraMap R S (b i)) = 0) ∧ ω = ∑ i, b i • ω' i) → ∃ ψ' : Ω[S⁄ℂ] →ₗ[ℂ] (Fin d → ℂ), (∀ (b : S) (ω : Ω[S⁄ℂ]), ψ' (b • ω) = ev b • ψ' ω) ∧ (∀ ω : Ω[R⁄ℂ], ψ' (KaehlerDifferential.map ℂ ℂ R S ω) = ψ ω) ∧ (∀ ω : Ω[S⁄ℂ], ψ' ω = 0 → ∃ (m : ℕ) (b : Fin m → S) (ω' : Fin m → Ω[S⁄ℂ]), (∀ i, ev (b i) = 0) ∧ ω = ∑ i, b i • ω' i) := by
  intro R S _ _ _ _ _ _ f _ ev d ψ h1 h2
  letI : Module R (Fin d → ℂ) := Module.compHom (Fin d → ℂ) (ev.comp (algebraMap R S))
  have hu : ∀ x : Submonoid.powers f, ev (algebraMap R S x) ≠ 0 := fun x =>
    ((IsLocalization.map_units S x).map ev).ne_zero
  have hunit : ∀ x : Submonoid.powers f,
      IsUnit ((algebraMap R (Module.End R (Fin d → ℂ))) x) := by
    intro x
    rw [Module.End.isUnit_iff]
    refine ⟨fun v w hvw => smul_right_injective (Fin d → ℂ) (hu x) hvw,
      fun v => ⟨(ev (algebraMap R S x))⁻¹ • v, ?_⟩⟩
    show ev (algebraMap R S x) • ((ev (algebraMap R S x))⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (hu x), one_smul]
  let g : Ω[R⁄ℂ] →ₗ[R] (Fin d → ℂ) :=
    { toFun := ψ, map_add' := ψ.map_add, map_smul' := fun b ω => h1 b ω }
  let L := IsLocalizedModule.lift (Submonoid.powers f) (KaehlerDifferential.map ℂ ℂ R S) g hunit
  have hL : ∀ η, L (KaehlerDifferential.map ℂ ℂ R S η) = ψ η := fun η =>
    IsLocalizedModule.lift_apply _ _ _ _ η
  have hLs : ∀ (r : R) (ω : Ω[S⁄ℂ]), L (r • ω) = ev (algebraMap R S r) • L ω :=
    fun r ω => L.map_smul r ω
  have hLS : ∀ (b : S) (ω : Ω[S⁄ℂ]), L (b • ω) = ev b • L ω := by
    intro b ω
    obtain ⟨⟨r, t⟩, ht⟩ := IsLocalization.surj (Submonoid.powers f) b
    have h := hLs (t : R) (b • ω)
    rw [← algebraMap_smul S (t : R) (b • ω), smul_smul, mul_comm, ht, algebraMap_smul, hLs] at h
    apply smul_right_injective (Fin d → ℂ) (hu t)
    show ev (algebraMap R S t) • L (b • ω) = ev (algebraMap R S t) • ev b • L ω
    rw [← h, ← ht, map_mul, mul_comm, mul_smul]
  have hLC : ∀ (c : ℂ) (ω : Ω[S⁄ℂ]), L (c • ω) = c • L ω := by
    intro c ω
    obtain ⟨⟨η, s⟩, hs⟩ :=
      IsLocalizedModule.surj (Submonoid.powers f) (KaehlerDifferential.map ℂ ℂ R S) ω
    have hs' : (s : R) • ω = KaehlerDifferential.map ℂ ℂ R S η := hs
    have e1 : ev (algebraMap R S s) • L ω = ψ η := by rw [← hLs, hs', hL]
    have e2 : ev (algebraMap ℂ S c) • ψ η = c • ψ η := by
      rw [show c • ψ η = ψ (c • η) from (ψ.map_smul c η).symm, ← algebraMap_smul R c η, h1,
        ← IsScalarTower.algebraMap_apply]
    rw [← algebraMap_smul S c ω, hLS]
    apply smul_right_injective (Fin d → ℂ) (hu s)
    show ev (algebraMap R S s) • ev (algebraMap ℂ S c) • L ω = ev (algebraMap R S s) • c • L ω
    rw [smul_comm (ev (algebraMap R S s)) (ev (algebraMap ℂ S c)), e1, e2,
      smul_comm (ev (algebraMap R S s)) c, e1]
  refine ⟨{ toFun := L, map_add' := L.map_add, map_smul' := hLC }, hLS, hL, ?_⟩
  intro ω hω
  change L ω = 0 at hω
  obtain ⟨⟨η, s⟩, hs⟩ :=
    IsLocalizedModule.surj (Submonoid.powers f) (KaehlerDifferential.map ℂ ℂ R S) ω
  have hs' : (s : R) • ω = KaehlerDifferential.map ℂ ℂ R S η := hs
  have hη : ψ η = 0 := by rw [← hL, ← hs', hLs, hω, smul_zero]
  obtain ⟨m, b, ω', hb, hηeq⟩ := h2 η hη
  let u : S := IsLocalization.mk' S (1 : R) s
  have hu1 : u * algebraMap R S s = 1 := by rw [IsLocalization.mk'_spec, map_one]
  refine ⟨m, fun i => algebraMap R S (b i),
    fun i => u • KaehlerDifferential.map ℂ ℂ R S (ω' i), hb, ?_⟩
  calc ω = u • ((s : R) • ω) := by
        rw [← algebraMap_smul S (s : R) ω, smul_smul, hu1, one_smul]
    _ = u • KaehlerDifferential.map ℂ ℂ R S (∑ i, b i • ω' i) := by rw [hs', hηeq]
    _ = ∑ i, algebraMap R S (b i) • u • KaehlerDifferential.map ℂ ℂ R S (ω' i) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, ← algebraMap_smul S (b i), smul_comm]
end

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 KaehlerDifferential
open scoped TensorProduct
set_option autoImplicit false

namespace UpperTheory.EvaluationRestriction

section Pts

variable {Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ} {y : CxPts s' (RingHom.id ℂ)}

private theorem ev_r {V W : Y.Opens} (h : W ≤ V) (hy : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) W) (f : Sec s' V) :
    CxPts.ev s' (RingHom.id ℂ) W (Sec.res s' h f) y = CxPts.ev s' (RingHom.id ℂ) V f y :=
  CxPts.ev_res h hy f

private noncomputable def evA {V : Y.Opens} (hy : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V) : Sec s' V →ₐ[ℂ] ℂ :=
  { (CxPts.evHom hy : Sec s' V →+* ℂ) with
    commutes' := fun a => by
      have h := CxPts.ev_algX (p := s') (σ := RingHom.id ℂ) hy a
      rw [CxPts.ev_eq hy] at h
      exact h }

private theorem evA_apply {V : Y.Opens} (hy : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V) (b : Sec s' V) :
    evA hy b = CxPts.ev s' (RingHom.id ℂ) V b y := (CxPts.ev_eq hy b).symm

private theorem res_self (V : Y.Opens) (b : Sec s' V) : Sec.res s' (le_refl V) b = b := by
  change (Y.presheaf.map (homOfLE (le_refl V)).op).hom b = b
  simp
  rfl

private def Fr (y : CxPts s' (RingHom.id ℂ)) {V0 W : Y.Opens} (h : W ≤ V0) : Prop :=
  ∀ w : Sec s' W, ∃ a p : Sec s' V0, CxPts.ev s' (RingHom.id ℂ) V0 p y ≠ 0 ∧ Sec.res s' h a = Sec.res s' h p * w

private theorem fr_refl (V0 : Y.Opens) (hy : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V0) : Fr y (le_refl V0) := fun w => by
  refine ⟨w, 1, ?_, ?_⟩
  · rw [← evA_apply hy, map_one]; exact one_ne_zero
  · rw [map_one, one_mul, res_self]

private theorem fr_step {V0 V : Y.Opens} (hV : IsAffineOpen V) (h : V ≤ V0) (H : Fr y h) (f : Γ(Y, V))
    (hy : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (Y.basicOpen f)) : Fr y ((Y.basicOpen_le f).trans h) := by
  intro w
  have hyV : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V := CxPts.ptsIn_mono (Y.basicOpen_le f) hy
  have hy0 : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V0 := CxPts.ptsIn_mono h hyV
  have hL := hV.isLocalization_basicOpen f
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f (show Γ(Y, Y.basicOpen f) from w)
  have hf0 : CxPts.ev s' (RingHom.id ℂ) V f y ≠ 0 := (CxPts.mem_ptsIn_basicOpen hyV f).1 hy
  obtain ⟨F, hF⟩ : ∃ F : Sec s' V, F = f := ⟨f, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Sec s' V, A = a := ⟨a, rfl⟩
  have ha' : w * Sec.res s' (Y.basicOpen_le f) F ^ n = Sec.res s' (Y.basicOpen_le f) A := by
    rw [hF, hA]; exact ha
  rw [← hF] at hf0
  obtain ⟨a0, p0, h0, e0⟩ := H A
  obtain ⟨a1, p1, h1, e1⟩ := H F
  have ha1 : evA hy0 a1 ≠ 0 := by
    have := congrArg (evA hyV) e1
    rw [map_mul, evA_apply hyV, evA_apply hyV, evA_apply hyV, ev_r h hyV, ev_r h hyV] at this
    rw [evA_apply hy0, this]
    exact mul_ne_zero h1 hf0
  refine ⟨p1 ^ n * a0, a1 ^ n * p0, ?_, ?_⟩
  · rw [← evA_apply hy0, map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero n ha1) (by rwa [evA_apply hy0])
  · simp only [Sec.res_res s' h (Y.basicOpen_le f), map_mul, map_pow, e0, e1]
    rw [← ha']
    ring

private def Pd (d : ℕ) (y : CxPts s' (RingHom.id ℂ)) (V : Y.Opens) : Prop :=
  ∃ φ : Ω[Sec s' V⁄ℂ] →ₗ[ℂ] (Fin d → ℂ),
    (∀ (b : Sec s' V) (ω : Ω[Sec s' V⁄ℂ]), φ (b • ω) = CxPts.ev s' (RingHom.id ℂ) V b y • φ ω) ∧
    Function.Surjective φ ∧
    ∀ ω : Ω[Sec s' V⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → Sec s' V) (ω' : Fin m → Ω[Sec s' V⁄ℂ]),
        (∀ i, CxPts.ev s' (RingHom.id ℂ) V (b i) y = 0) ∧ ω = ∑ i, b i • ω' i

private theorem pd_step {d : ℕ} {V : Y.Opens} (hV : IsAffineOpen V) (f : Γ(Y, V))
    (hy : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (Y.basicOpen f)) (H : Pd d y V) : Pd d y (Y.basicOpen f) := by
  obtain ⟨φ, h1, h2, h3⟩ := H
  letI : Algebra (Sec s' V) (Sec s' (Y.basicOpen f)) := (Sec.res s' (Y.basicOpen_le f)).toRingHom.toAlgebra
  haveI : IsScalarTower ℂ (Sec s' V) (Sec s' (Y.basicOpen f)) :=
    .of_algebraMap_eq fun r => ((Sec.res s' (Y.basicOpen_le f)).commutes r).symm
  haveI : IsLocalization.Away (show Sec s' V from f) (Sec s' (Y.basicOpen f)) := hV.isLocalization_basicOpen f
  have hal : ∀ b : Sec s' V, CxPts.ev s' (RingHom.id ℂ) V b y =
      (evA hy).toRingHom (algebraMap (Sec s' V) (Sec s' (Y.basicOpen f)) b) := fun b => by
    change _ = evA hy (Sec.res s' (Y.basicOpen_le f) b)
    rw [evA_apply, ev_r _ hy]
  obtain ⟨ψ, g1, g2, g3⟩ := UpperTheory.exists_cotangent_map_localization_away (R := Sec s' V) (S := Sec s' (Y.basicOpen f)) (show Sec s' V from f)
    (evA hy).toRingHom φ (fun b ω => by rw [h1, hal]) (fun ω hω => by
      obtain ⟨m, b, ω', e1, e2⟩ := h3 ω hω
      exact ⟨m, b, ω', fun i => by rw [← hal]; exact e1 i, e2⟩)
  refine ⟨ψ, fun b ω => ?_, fun v => ?_, fun ω hω => ?_⟩
  · rw [g1]; congr 1; exact evA_apply hy b
  · obtain ⟨ω, rfl⟩ := h2 v
    exact ⟨_, g2 ω⟩
  · obtain ⟨m, b, ω', e1, e2⟩ := g3 ω hω
    exact ⟨m, b, ω', fun i => (evA_apply hy _).symm.trans (e1 i), e2⟩

end Pts

end UpperTheory.EvaluationRestriction

namespace UpperTheory.EvaluationRestriction

section Charts

variable {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp ℂ} [Algebra ℂ X.functionField] {ι : Type} {U : ι → X.Opens}
  {B : Finset ι → Subalgebra ℂ X.functionField}

private theorem chart_mem (h : IsAffCover p U B) (i : ι) (hg : genericPoint X ∈ U i) (b : X.functionField) :
    b ∈ B {i} ↔ ∃ f : Γ(X, U i), (X.presheaf.germ (U i) (genericPoint X) hg).hom f = b := by
  have key : ∀ (W : X.Opens) (_ : W = U i) (hn : genericPoint X ∈ W),
      (∃ f : Γ(X, W), (X.presheaf.germ W (genericPoint X) hn).hom f = b) ↔
        ∃ f : Γ(X, U i), (X.presheaf.germ (U i) (genericPoint X) hg).hom f = b := by
    rintro _ rfl _; rfl
  rw [h.ring {i} (by simp)]
  exact key _ (Finset.inf_singleton ..) _

private theorem chart_aff (h : IsAffCover p U B) (i : ι) : IsAffineOpen (U i) := by
  have := h.affine {i} (by simp)
  rwa [Finset.inf_singleton] at this

private theorem chart_gen (h : IsAffCover p U B) (i : ι) : genericPoint X ∈ U i := by
  have := h.ne {i}
  rwa [Finset.inf_singleton] at this

end Charts

section Germ

variable {Y : Scheme.{0}} [IsIntegral Y] (s' : Y ⟶ Sp ℂ)

private noncomputable def gm {V : Y.Opens} (hg : genericPoint Y ∈ V) : Sec s' V →+* Y.functionField :=
  (Y.presheaf.germ V (genericPoint Y) hg).hom

private theorem gm_res {V W : Y.Opens} (h : W ≤ V) (hg : genericPoint Y ∈ V) (hW : genericPoint Y ∈ W) (b : Sec s' V) :
    gm s' hW (Sec.res s' h b) = gm s' hg b :=
  Y.presheaf.germ_res_apply (homOfLE h) _ hW b

private theorem gm_inj {V : Y.Opens} (hg : genericPoint Y ∈ V) : Function.Injective (gm s' hg) :=
  germ_injective_of_isIntegral Y _ hg

private theorem gm_alg [inst : Algebra ℂ Y.functionField]
    (hi : algebraMap ℂ Y.functionField = @algebraMap ℂ Y.functionField _ _ (ffAlg s')) {V : Y.Opens}
    (hg : genericPoint Y ∈ V) (r : ℂ) : gm s' hg (algebraMap ℂ (Sec s' V) r) = algebraMap ℂ Y.functionField r := by
  rw [hi]
  change (Y.presheaf.germ V _ hg).hom ((s'.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r)) =
    (Y.presheaf.germ ⊤ _ trivial).hom (s'.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom r))
  exact Y.presheaf.germ_res_apply (homOfLE le_top) _ hg (s'.appTop.hom _)

end Germ

end UpperTheory.EvaluationRestriction

open UpperTheory.EvaluationRestriction in
theorem UpperTheory.etaleCorrespondence_local_parameters_statement :
    ∀ (d : ℕ) (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (s : Z ⟶ Sp ℂ) (s' : Y ⟶ Sp ℂ) [SmoothOfRelativeDimension d s] [SmoothOfRelativeDimension d s'] (hP : IsProjOver s) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s') [IsFinite c1] [Etale c1] [IsFinite c2] [Etale c2] [instK : Algebra ℂ Z.functionField] [instL : Algebra ℂ Y.functionField] (hK : instK = ffAlg s) (hL : instL = ffAlg s') [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (g1 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c1 ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c1 ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c1.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) (j2 : Z.functionField →ₐ[ℂ] Y.functionField) (g2 : ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c2 ⁻¹ᵁ V) (g : Γ(Z, V)), j2 ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c2 ⁻¹ᵁ V) (genericPoint Y) hV').hom (c2.app V g)) (F : Type) [Field F] [Algebra ℂ F] [Algebra F Z.functionField] [Algebra F Y.functionField] [IsScalarTower ℂ F Z.functionField] [IsScalarTower F Z.functionField Y.functionField] [IsScalarTower ℂ F Y.functionField] (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens) (hx : IsFinCover ℂ Z.functionField x) (hU : IsAffCover s U (rB ℂ Z.functionField x)), IsReduced ((rB ℂ Z.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ Z.functionField x j⟩ : rB ℂ Z.functionField x {0})))) → ∀ (y : CxPts s' (RingHom.id ℂ)), y.1 ≫ c1 = y.1 ≫ c2 → ∀ A : Matrix (Fin d) (Fin d) ℂ, IsTan d c1 c2 h1 h2 y A → ∀ (hg : genericPoint Y ∈ c1 ⁻¹ᵁ U 0) (e : rB ℂ Y.functionField x {0} →ₐ[ℂ] ℂ), UpperTheory.A.Mt s' (c1 ⁻¹ᵁ U 0) hg _ e y → (∀ j : Fin d, e ⟨_, tco_mem ℂ Y.functionField x j⟩ = 0) → ∀ M : Matrix (Fin d) (Fin d) ℂ, (∀ m : Fin d, ∃ (c : Y.functionField) (hc : c ∈ rB ℂ Y.functionField x {0}) (g : Fin d → Y.functionField) (hgl : ∀ l, g l ∈ rB ℂ Y.functionField x {0}), e ⟨c, hc⟩ ≠ 0 ∧ c * j2 (algebraMap F Z.functionField (x m.succ / x 0)) = ∑ l, g l * algebraMap F Y.functionField (x l.succ / x 0) ∧ ∀ l, e ⟨g l, hgl l⟩ = e ⟨c, hc⟩ * M m l) → ∃ P : Matrix (Fin d) (Fin d) ℂ, IsUnit P.det ∧ M = P * A * P⁻¹ := by
  intro d Z Y _ _ s s' _ _ hPr c1 c2 h1 h2 _ _ _ _ inst inst' hinst hinst' _ _ g1 j2 hj2 F _ _ _ _ _ _ _ x U hFC hAC hredZ y hfix A hA hg0 e hMt hz M hM
  have hj1 := fun V hV hV' g => (g1 V hV hV' g).symm
  have hAC' := (UpperTheory.A.isFinCover_pull h1 hinst hinst' g1 hFC hAC).2
  have hred := UpperTheory.Cb.finite_etale_function_field_germ_compat_of_smooth d Z Y s s' c1 h1 inferInstance inferInstance hinst hinst' hj1 F x U hFC hAC hAC' hredZ
  have hy := hMt.1
  have he := fun (_ : genericPoint Y ∈ c1 ⁻¹ᵁ U 0) => hMt.2
  have hgZ : genericPoint Z ∈ U 0 := chart_gen hAC 0
  have hgY : genericPoint Y ∈ c1 ⁻¹ᵁ U 0 := chart_gen hAC' 0
  have hV0 : IsAffineOpen (c1 ⁻¹ᵁ U 0) := chart_aff hAC' 0
  have hU0 : IsAffineOpen (U 0) := chart_aff hAC 0
  choose τ hτ using fun l : Fin d => (chart_mem hAC 0 hgZ _).1 (tco_mem ℂ Z.functionField x l)
  have memB : ∀ f : Sec s' (c1 ⁻¹ᵁ U 0), gm s' hgY f ∈ rB ℂ Y.functionField x {0} := fun f =>
    (chart_mem hAC' 0 hgY _).2 ⟨f, rfl⟩
  have evB : ∀ f : Sec s' (c1 ⁻¹ᵁ U 0), e ⟨gm s' hgY f, memB f⟩ = CxPts.ev s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) f y :=
    fun f => he hgY f (memB f)
  have germT : ∀ l : Fin d, gm s' hgY (appSec s s' c1 (U 0) (τ l)) = algebraMap F Y.functionField (x l.succ / x 0) := fun l => by
    change (Y.presheaf.germ (c1 ⁻¹ᵁ U 0) (genericPoint Y) hgY).hom (c1.app (U 0) (τ l)) = _
    rw [← hj1 (U 0) hgZ hgY (τ l), hτ, ← IsScalarTower.algebraMap_apply]
  have evT : ∀ l : Fin d, CxPts.ev s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) (appSec s s' c1 (U 0) (τ l)) y = 0 := fun l => by
    rw [← evB, ← hz l]
    exact congrArg e (Subtype.ext (germT l))

  have hftB : Algebra.FiniteType ℂ (rB ℂ Y.functionField x {0}) := by
    haveI : Smooth s' := SmoothOfRelativeDimension.smooth d s'
    haveI := GlobalTheory.HodgeFin.finiteType_sec s' hV0
    let gA : Sec s' (c1 ⁻¹ᵁ U 0) →ₐ[ℂ] rB ℂ Y.functionField x {0} :=
      { toFun := fun f => ⟨gm s' hgY f, memB f⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun a b => Subtype.ext (map_mul _ a b)
        map_zero' := Subtype.ext (map_zero _)
        map_add' := fun a b => Subtype.ext (map_add _ a b)
        commutes' := fun r => Subtype.ext (gm_alg s' hAC'.alg hgY r) }
    refine Algebra.FiniteType.of_surjective gA fun b => ?_
    obtain ⟨f, hf⟩ := (chart_mem hAC' 0 hgY _).1 b.2
    exact ⟨f, Subtype.ext hf⟩
  have hQ0 : ∀ u : Sec s' (c1 ⁻¹ᵁ U 0), CxPts.ev s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) u y = 0 →
      ∃ (c : Sec s' (c1 ⁻¹ᵁ U 0)) (g : Fin d → Sec s' (c1 ⁻¹ᵁ U 0)),
        CxPts.ev s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) c y ≠ 0 ∧ c * u = ∑ l, g l * appSec s s' c1 (U 0) (τ l) := by
    intro u hu
    have hfin := UpperTheory.finite_fiber_of_finiteType_parameter_ring F Y.functionField d x hFC.pd hftB
    obtain ⟨c, g, hc, hcg⟩ := UpperTheory.Cb.exists_unit_mul_mem_span_of_reduced_isolated_zero (rB ℂ Y.functionField x {0}) d
      (fun j => ⟨_, tco_mem ℂ Y.functionField x j⟩) hred hfin e hz ⟨gm s' hgY u, memB u⟩ (by rw [evB]; exact hu)
    have onto : ∀ b : rB ℂ Y.functionField x {0}, ∃ f : Sec s' (c1 ⁻¹ᵁ U 0), gm s' hgY f = b := fun b =>
      (chart_mem hAC' 0 hgY _).1 b.2
    obtain ⟨c', hc'⟩ := onto c
    choose g' hg' using fun l => onto (g l)
    refine ⟨c', g', ?_, ?_⟩
    · rw [← evB]
      have : (⟨gm s' hgY c', memB c'⟩ : rB ℂ Y.functionField x {0}) = c := Subtype.ext hc'
      rw [this]; exact hc
    · apply gm_inj s' hgY
      have h := congrArg Subtype.val hcg
      simp only [Subalgebra.coe_mul, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul] at h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_mul, map_sum]
      simp only [map_mul]
      refine Eq.trans ?_ (h.trans ?_)
      · exact congrArg (· * gm s' hgY u) hc'
      · exact Finset.sum_congr rfl fun l _ => by rw [germT]; exact congrArg (· * _) (hg' l).symm

  have hA0 := hA
  obtain ⟨UA, VA, hA1, hA2, tA, hyA, hUA, hVA, φA, hφs, hφ1, hφ2, hφk⟩ := hA
  have pdVA : Pd d y VA := by
    refine ⟨φA, hφs, fun v => ⟨∑ l, v l • D ℂ (Sec s' VA) (Sec.res s' hA1 (appSec s s' c1 UA (tA l))), ?_⟩, hφk⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul, hφ1]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]

  have hpt : ∀ W : Y.Opens, y ∈ CxPts.ptsIn s' (RingHom.id ℂ) W ↔ y.1 (IsLocalRing.closedPoint ℂ) ∈ W := fun W => CxPts.mem_ptsIn
  have hy2 : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (c2 ⁻¹ᵁ U 0) := by
    rw [hpt]
    have h0 := (hpt _).1 hy
    have h3 : c2 (y.1 (IsLocalRing.closedPoint ℂ)) = c1 (y.1 (IsLocalRing.closedPoint ℂ)) := by
      have := congrArg (fun q : Sp ℂ ⟶ Z => q (IsLocalRing.closedPoint ℂ)) hfix
      simpa [Function.comp] using this.symm
    change c2 (y.1 (IsLocalRing.closedPoint ℂ)) ∈ U 0
    rw [h3]
    exact h0

  obtain ⟨hh, hhle, hhy⟩ := hV0.exists_basicOpen_le (V := c2 ⁻¹ᵁ U 0) ⟨_, (hpt _).1 hy2⟩ ((hpt _).1 hy)
  have hV1 : IsAffineOpen (Y.basicOpen hh) := hV0.basicOpen hh
  obtain ⟨f, g, hfg, hfy⟩ := exists_basicOpen_le_affine_inter hVA hV1 (y.1 (IsLocalRing.closedPoint ℂ)) ⟨(hpt _).1 hyA, hhy⟩
  have hW : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) (Y.basicOpen g) := (hpt _).2 (hfg ▸ hfy)
  have pdW : Pd d y (Y.basicOpen g) := hfg ▸ pd_step hVA f ((hpt _).2 hfy) pdVA
  have frV1 : Fr y ((Y.basicOpen_le hh).trans (le_refl (c1 ⁻¹ᵁ U 0))) :=
    fr_step hV0 le_rfl (fr_refl _ hy) hh ((hpt _).2 hhy)
  have hWle : Y.basicOpen g ≤ c1 ⁻¹ᵁ U 0 := (Y.basicOpen_le g).trans ((Y.basicOpen_le hh).trans (le_refl _))
  have frW : Fr y hWle := fr_step hV1 _ frV1 g hW
  have hW2 : Y.basicOpen g ≤ c2 ⁻¹ᵁ U 0 := (Y.basicOpen_le g).trans hhle
  have hVW : IsAffineOpen (Y.basicOpen g) := hV1.basicOpen g
  have hy0W : ∀ b : Sec s' (c1 ⁻¹ᵁ U 0), evA hW (Sec.res s' hWle b) = CxPts.ev s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) b y :=
    fun b => by rw [evA_apply, ev_r hWle hW]
  obtain ⟨t, ht⟩ : ∃ t : Fin d → Sec s' (Y.basicOpen g), t = fun l => Sec.res s' hWle (appSec s s' c1 (U 0) (τ l)) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : Fin d → Sec s' (Y.basicOpen g), u = fun m => Sec.res s' hW2 (appSec s s' c2 (U 0) (τ m)) := ⟨_, rfl⟩
  have evt : ∀ l, evA hW (t l) = 0 := fun l => by rw [ht]; exact (hy0W _).trans (evT l)
  have evu : ∀ m, evA hW (u m) = 0 := fun m => by
    rw [hu]
    refine (evA_apply hW _).trans ((ev_r hW2 hW _).trans ?_)
    refine Eq.trans ?_ (evT m)
    change valR y.1 (c2 ⁻¹ᵁ U 0) (c2.app (U 0) (τ m)) = valR y.1 (c1 ⁻¹ᵁ U 0) (c1.app (U 0) (τ m))
    rw [← GlobalTheory.Points.valR_comp, ← GlobalTheory.Points.valR_comp, hfix]
  have hQW : ∀ w : Sec s' (Y.basicOpen g), evA hW w = 0 → ∃ (c : Sec s' (c1 ⁻¹ᵁ U 0)) (q : Fin d → Sec s' (c1 ⁻¹ᵁ U 0)),
      CxPts.ev s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) c y ≠ 0 ∧
        Sec.res s' hWle c * w = ∑ l, Sec.res s' hWle (q l) * t l := by
    intro w hw
    obtain ⟨a, p, hp, hap⟩ := frW w
    have ha : CxPts.ev s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) a y = 0 := by
      rw [← hy0W, hap, map_mul, hw, mul_zero]
    obtain ⟨c, q, hc, hcq⟩ := hQ0 a ha
    refine ⟨c * p, q, ?_, ?_⟩
    · rw [← hy0W, map_mul, map_mul, hy0W, hy0W]
      exact mul_ne_zero hc hp
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_mul, mul_assoc, ← hap, ← map_mul, hcq, map_sum, ht]
      simp only [map_mul]
  obtain ⟨ψ, p1, p2, p3⟩ := pdW
  obtain ⟨φ, q1, q2, q3, q4⟩ := UpperTheory.exists_cotangent_map_dual_basis_of_parameters (evA hW) t ψ (fun b ω => by rw [p1, evA_apply]) p2 evt
    (fun w hw => by
      obtain ⟨c, q, hc, hcq⟩ := hQW w hw
      exact ⟨Sec.res s' hWle c, fun l => Sec.res s' hWle (q l), by rwa [hy0W], hcq⟩)
  obtain ⟨A', hA'⟩ : ∃ A' : Matrix (Fin d) (Fin d) ℂ, ∀ m, (fun l => A' m l) = φ (D ℂ (Sec s' (Y.basicOpen g)) (u m)) :=
    ⟨Matrix.of fun m l => φ (D ℂ (Sec s' (Y.basicOpen g)) (u m)) l, fun m => rfl⟩
  have hTan : IsTan d c1 c2 h1 h2 y A' := by
    refine ⟨U 0, Y.basicOpen g, hWle, hW2, τ, hW, hU0, hVW, φ, fun b ω => ?_, fun l => ?_, fun j => ?_, fun ω hω => ?_⟩
    · rw [q1, evA_apply]
    · have := q2 l
      rw [ht] at this
      exact this
    · have := hA' j
      rw [hu] at this
      exact this.symm
    · exact p3 ω (q3 ω hω)
  obtain ⟨P, hP, hAP⟩ := UpperTheory.Gal.productCup_of_system.tanConj_etale Z Y s s' d c1 c2 h1 h2 y ‹Etale c1› hfix A A' hA0 hTan
  refine ⟨P, hP, Eq.trans ?_ hAP⟩
  ext m l
  obtain ⟨c0, hc0, g0, hg0', hc, hcq0, hval⟩ := hM m
  obtain ⟨c, hc'⟩ : ∃ f : Sec s' (c1 ⁻¹ᵁ U 0), gm s' hgY f = c0 := (chart_mem hAC' 0 hgY _).1 hc0
  choose q hq using fun l => (show ∃ f : Sec s' (c1 ⁻¹ᵁ U 0), gm s' hgY f = g0 l from (chart_mem hAC' 0 hgY _).1 (hg0' l))
  have hgW : genericPoint Y ∈ Y.basicOpen g :=
    ((genericPoint_spec Y).mem_open_set_iff (Y.basicOpen g).isOpen).2 ⟨_, trivial, (hpt _).1 hW⟩
  have hg2 : genericPoint Y ∈ c2 ⁻¹ᵁ U 0 := hW2 hgW
  have hju : gm s' hgW (u m) = j2 (algebraMap F Z.functionField (x m.succ / x 0)) := by
    rw [hu]
    refine (gm_res s' hW2 hg2 hgW _).trans ?_
    rw [← hτ m]
    exact (hj2 (U 0) hgZ hg2 (τ m)).symm
  have htl : ∀ l, gm s' hgW (t l) = algebraMap F Y.functionField (x l.succ / x 0) := fun l => by
    rw [ht]
    exact (gm_res s' hWle hgY hgW _).trans (germT l)
  have hcq : Sec.res s' hWle c * u m = ∑ l, Sec.res s' hWle (q l) * t l := by
    apply gm_inj s' hgW
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_sum, gm_res s' hWle hgY hgW, hju, hc', hcq0]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, gm_res s' hWle hgY hgW, htl, hq]
  have ec : CxPts.ev s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) c y = e ⟨c0, hc0⟩ := by
    rw [← evB]; exact congrArg e (Subtype.ext hc')
  have eq : CxPts.ev s' (RingHom.id ℂ) (c1 ⁻¹ᵁ U 0) (q l) y = e ⟨g0 l, hg0' l⟩ := by
    rw [← evB]; exact congrArg e (Subtype.ext (hq l))
  have h := q4 (u m) (Sec.res s' hWle c) (fun l => Sec.res s' hWle (q l)) (evu m) (by rw [hy0W, ec]; exact hc) hcq l
  rw [hy0W, hy0W, ec, eq, hval l] at h
  exact (mul_left_cancel₀ hc h).trans (congrFun (hA' m) l).symm
