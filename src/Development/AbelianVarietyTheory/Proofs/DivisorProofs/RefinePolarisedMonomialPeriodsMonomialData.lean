module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricPolarisationFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricDataComparePolarisedUpToFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPointOfSize
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomEvenDefectBimultiplicativePeriods
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeStalkEvalAtOriginOriginStalkConstants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFromBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtLatticeHomFiniteExtensionComplete
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCompleteNormalExtSqrtFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCompleteNormalExtSqrtFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqRoots

open Polynomial

theorem exists_sqrt_one (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (b : R)
    (h : IsCN R) : ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R')
      (ρ : R →+* R') (s : R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧
      s ^ 2 = ρ b := by
  set g : R[X] := X ^ 2 - C b with hg_def
  have hg : g.Monic := monic_X_pow_sub_C b two_ne_zero
  have hdeg : g.natDegree = 2 := natDegree_X_pow_sub_C _
  have hinj : Function.Injective (AdjoinRoot.of g) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hne
    have hdvd : g ∣ C r := by
      rw [AdjoinRoot.of, RingHom.comp_apply, AdjoinRoot.mk_eq_zero] at hr
      exact hr
    refine hg.not_dvd_of_natDegree_lt (C_ne_zero.mpr hne) ?_ hdvd
    rw [natDegree_C, hdeg]; norm_num
  have hfin : (AdjoinRoot.of g).Finite := by
    have := RingHom.finite_algebraMap.mpr hg.finite_adjoinRoot
    rwa [AdjoinRoot.algebraMap_eq] at this
  obtain ⟨R', _, _, _, ρ, σ, hC, hi, hf, hl, hσ⟩ :=
    GlobalTheory.T.exists_complete_normal_local_cover_of_finite_hom R (AdjoinRoot g) (AdjoinRoot.of g) h hinj hfin
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, σ (AdjoinRoot.root g), hC, hi, hf, hl, ?_⟩
  have hroot : AdjoinRoot.root g ^ 2 = AdjoinRoot.of g b := by
    have h0 : AdjoinRoot.mk g g = 0 := AdjoinRoot.mk_self
    rw [hg_def, map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h0
    exact h0
  rw [← map_pow, hroot, ← RingHom.comp_apply, hσ]

theorem exists_sqrt_fin : ∀ (n : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (a : Fin n → R), IsCN R → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R')
      (ρ : R →+* R') (r : Fin n → R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧
      ∀ i, r i ^ 2 = ρ (a i) := by
  intro n
  induction n with
  | zero =>
    intro R _ _ _ a h
    exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, Fin.elim0, h,
      Function.injective_id, RingHom.Finite.id R, inferInstance, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro R _ _ _ a h
    obtain ⟨R₁, _, _, _, ρ₁, r₁, hC₁, hi₁, hf₁, hl₁, hr₁⟩ := ih R (fun i => a i.castSucc) h
    obtain ⟨R₂, _, _, _, ρ₂, s, hC₂, hi₂, hf₂, hl₂, hs⟩ :=
      exists_sqrt_one R₁ (ρ₁ (a (Fin.last n))) hC₁
    refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ₂.comp ρ₁,
      Fin.lastCases s (fun i => ρ₂ (r₁ i)), hC₂, hi₂.comp hi₁, hf₂.comp hf₁, ?_, ?_⟩
    · haveI := hl₁; haveI := hl₂; infer_instance
    · intro i
      induction i using Fin.lastCases with
      | last => beta_reduce; rw [Fin.lastCases_last, hs, RingHom.comp_apply]
      | cast i => beta_reduce; rw [Fin.lastCases_castSucc, ← map_pow, hr₁, RingHom.comp_apply]

end GlobalTheory.SqRoots

theorem GlobalTheory.sqrt_of_finite_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Type) [Finite I] (a : I → R), IsCN R → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : I → R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ ∀ i, r i ^ 2 = ρ (a i) := by
  intro R _ _ _ I _ a h
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  obtain ⟨R', _, _, _, ρ, r, hC, hi, hf, hl, hr⟩ := GlobalTheory.SqRoots.exists_sqrt_fin n R (a ∘ e.symm) h
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, r ∘ e, hC, hi, hf, hl, fun i => ?_⟩
  simpa using hr (e i)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCompleteNormalExtSqrtFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_completeNormal_ext_sqrt_family : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Type) [Finite I] (a : I → R), IsCN R → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : I → R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ ∀ i, r i ^ 2 = ρ (a i) := by
  first | exact @GlobalTheory.sqrt_of_finite_family | exact GlobalTheory.sqrt_of_finite_family | (intros; apply GlobalTheory.sqrt_of_finite_family <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtLatticeHomFiniteExtensionComplete
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RootHom

theorem exists_sqrt_hom : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h : X → (FractionRing R)ˣ) (m : ℕ) (t : Fin m → R), IsCN R → (∀ a b, h (a + b) = h a * h b) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (gam : FractionRing R →+* FractionRing R') (r : Fin m → R') (eta : X → (FractionRing R')ˣ), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ (∀ x, gam (algebraMap R _ x) = algebraMap R' _ (ρ x)) ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ (∀ a b, eta (a + b) = eta a * eta b) ∧ ∀ a, eta a ^ 2 = Units.map gam.toMonoidHom (h a) := by
  intro R _ _ _ X _ _ _ h m t hR hh
  classical
  let b := Module.Free.chooseBasis ℤ X
  have hpq : ∀ k, ∃ p q : R, q ∈ nonZeroDivisors R ∧
      algebraMap R (FractionRing R) p / algebraMap R (FractionRing R) q = (h (b k) : FractionRing R) :=
    fun k => IsFractionRing.div_surjective R _
  choose p q hq hpq using hpq
  obtain ⟨R', _, _, _, ρ, r, hR', hinj, hfin, hloc, hr⟩ :=
    GlobalTheory.T.exists_finite_completeNormal_ext_sqrt_family R (Fin m ⊕ Module.Free.ChooseBasisIndex ℤ X) (Sum.elim t (fun k => p k * q k)) hR
  have hι : Function.Injective (algebraMap R' (FractionRing R')) := IsFractionRing.injective R' (FractionRing R')
  have hinj' : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) := hι.comp hinj
  let gam : FractionRing R →+* FractionRing R' := IsFractionRing.lift hinj'
  have hgam : ∀ x, gam (algebraMap R _ x) = algebraMap R' _ (ρ x) := fun x => IsFractionRing.lift_algebraMap hinj' x
  have hq0 : ∀ k, algebraMap R' (FractionRing R') (ρ (q k)) ≠ 0 := by
    intro k h0
    have : ρ (q k) = 0 := hι (by simpa using h0)
    exact nonZeroDivisors.ne_zero (hq k) (hinj (by simpa using this))
  have hp0 : ∀ k, p k ≠ 0 := by
    intro k h0
    have := hpq k
    rw [h0, map_zero, zero_div] at this
    exact (h (b k)).ne_zero this.symm
  have hs : ∀ k, (r (Sum.inr k)) ^ 2 = ρ (p k * q k) := fun k => by simpa using hr (Sum.inr k)
  have hs0 : ∀ k, algebraMap R' (FractionRing R') (r (Sum.inr k)) ≠ 0 := by
    intro k h0
    have h1 : r (Sum.inr k) = 0 := hι (by simpa using h0)
    have h2 := hs k
    rw [h1, zero_pow two_ne_zero] at h2
    exact mul_ne_zero (hp0 k) (nonZeroDivisors.ne_zero (hq k)) (hinj (by simpa using h2.symm))
  let e : Module.Free.ChooseBasisIndex ℤ X → (FractionRing R')ˣ := fun k =>
    Units.mk0 (algebraMap R' _ (r (Sum.inr k)) / algebraMap R' _ (ρ (q k))) (div_ne_zero (hs0 k) (hq0 k))
  let L : X →ₗ[ℤ] Additive (FractionRing R')ˣ := b.constr ℤ (fun k => Additive.ofMul (e k))
  let H : X →+ Additive (FractionRing R)ˣ := AddMonoidHom.mk' (fun a => Additive.ofMul (h a)) (fun a c => by
    simp [hh a c])
  let G : X →+ Additive (FractionRing R')ˣ := (MonoidHom.toAdditive (Units.map gam.toMonoidHom)).comp H
  have hLG : L + L = G.toIntLinearMap := by
    refine b.ext fun k => ?_
    simp only [LinearMap.add_apply, L, Module.Basis.constr_basis, AddMonoidHom.coe_toIntLinearMap, G, H,
      AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.mk'_apply, MonoidHom.toAdditive_apply_apply]
    rw [← ofMul_mul]
    congr 1
    ext
    simp only [Units.val_mul, e, Units.val_mk0, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, toMul_ofMul]
    rw [← hpq k, map_div₀, hgam, hgam, div_mul_div_comm, div_eq_div_iff (mul_ne_zero (hq0 k) (hq0 k)) (hq0 k)]
    have := congrArg (algebraMap R' (FractionRing R')) (hs k)
    rw [map_pow, map_mul, map_mul] at this
    rw [← sq, this]
    ring
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, gam, fun i => r (Sum.inl i), fun a => Additive.toMul (L a),
    hR', hinj, hfin, hloc, hgam, fun i => by simpa using hr (Sum.inl i), fun a c => by simp [map_add (f := _)], fun a => ?_⟩
  have h2 : Additive.toMul (L a + L a) = Units.map gam.toMonoidHom (h a) := by
    rw [← LinearMap.add_apply, LinearMap.congr_fun hLG a]
    rfl
  rw [sq, ← toMul_add]
  exact h2

end GlobalTheory.RootHom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtLatticeHomFiniteExtensionCompleteStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sqrt_latticeHom_finiteExtension_complete : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h : X → (FractionRing R)ˣ) (m : ℕ) (t : Fin m → R), IsCN R → (∀ a b, h (a + b) = h a * h b) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (gam : FractionRing R →+* FractionRing R') (r : Fin m → R') (eta : X → (FractionRing R')ˣ), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ (∀ x, gam (algebraMap R _ x) = algebraMap R' _ (ρ x)) ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ (∀ a b, eta (a + b) = eta a * eta b) ∧ ∀ a, eta a ^ 2 = Units.map gam.toMonoidHom (h a) := by
  first | exact @GlobalTheory.RootHom.exists_sqrt_hom | exact GlobalTheory.RootHom.exists_sqrt_hom | (intros; apply GlobalTheory.RootHom.exists_sqrt_hom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedPeriodComparisonSymmCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedPeriodComparisonSymmCocycle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.SymCoc

theorem alg {X U : Type} [AddCommGroup X] [CommGroup U] (F t P : X → X → U) (C : X → X → X → U) (ψ : X → U) (r : U)
    (hF : ∀ a b, P a b * F a b = t a b) (hP : ∀ a b, P a b = ψ (a + b) * (ψ a)⁻¹ * (ψ b)⁻¹ * r⁻¹)
    (ht : ∀ a b, t a b = t b a) (hadd : ∀ a a' b, t (a + a') b * C a a' b = t a b * t a' b)
    (hC : ∀ a b c, C a b c = C b c a) :
    (∀ a b, F a b = F b a) ∧ ∀ a b c, F (a + b) c * F a b = F a (b + c) * F b c := by
  constructor
  · intro a b
    have comm : ψ (b + a) = ψ (a + b) := by rw [add_comm]
    have e₁ := congrArg Additive.ofMul (hF a b)
    have e₂ := congrArg Additive.ofMul (hF b a)
    have e₃ := congrArg Additive.ofMul (ht a b)
    have e₄ := congrArg Additive.ofMul (hP a b)
    have e₅ := congrArg Additive.ofMul (hP b a)
    have e₆ := congrArg Additive.ofMul comm
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at e₁ e₂ e₃ e₄ e₅ e₆ ⊢
    linear_combination (norm := abel) e₁ - e₂ + e₃ - e₄ + e₅ + e₆
  · intro a b c
    have p₁ := hP (a + b) c
    rw [add_assoc] at p₁
    have e₁ := congrArg Additive.ofMul (hadd a b c)
    have e₂ := congrArg Additive.ofMul (hadd b c a)
    have s₁ := congrArg Additive.ofMul (ht a (b + c))
    have s₂ := congrArg Additive.ofMul (ht a b)
    have s₃ := congrArg Additive.ofMul (ht a c)
    have c₁ := congrArg Additive.ofMul (hC a b c)
    have f₁ := congrArg Additive.ofMul (hF (a + b) c)
    have f₂ := congrArg Additive.ofMul (hF a b)
    have f₃ := congrArg Additive.ofMul (hF a (b + c))
    have f₄ := congrArg Additive.ofMul (hF b c)
    have q₁ := congrArg Additive.ofMul p₁
    have q₂ := congrArg Additive.ofMul (hP a b)
    have q₃ := congrArg Additive.ofMul (hP a (b + c))
    have q₄ := congrArg Additive.ofMul (hP b c)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv] at e₁ e₂ s₁ s₂ s₃ c₁ f₁ f₂ f₃ f₄ q₁ q₂ q₃ q₄ ⊢
    linear_combination (norm := abel) e₁ - s₁ - e₂ + s₂ + s₃ - c₁ + f₁ + f₂ - f₃ - f₄ - q₁ - q₂ + q₃ + q₄

theorem exists_genPtMap {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ) : ∃ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ := by
  have hu : ∀ y : nonZeroDivisors R, IsUnit ((algebraMap R' (FractionRing R')).comp ρ y) := fun y => by
    refine IsUnit.mk0 _ ?_
    rw [RingHom.comp_apply, ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact (map_ne_zero_iff ρ hρ).2 (nonZeroDivisors.ne_zero y.2)
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) hu)), ?_⟩
  simp only [jK, spMap, ← Spec.map_comp]
  congr 1
  ext x
  simp [IsLocalization.lift_eq]

end GlobalTheory.PolDeg.SymCoc

namespace GlobalTheory.PolDeg


open GlobalTheory.PolDeg.SymCoc in
theorem half_symm_cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (f : D.X → D.X → (FractionRing R')ˣ), Function.Injective ρ → Half Q ρ D e f → (∀ a b, f a b = f b a) ∧ ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c := by
  intro R _ _ R' _ _ Q ρ D e f hρ hH
  obtain ⟨β, β₂, w, h₁, h₂, h₃, h₀, h₄, h₅⟩ := hH
  obtain ⟨κ, hκ⟩ : ∃ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ := exists_genPtMap ρ hρ
  let z : (TK R').left := (default : PrimeSpectrum (FractionRing R'))
  obtain ⟨J, hJ⟩ := GlobalTheory.UU.exists_good_pt Q.M.isLB z
  obtain ⟨J', hJ'⟩ := GlobalTheory.UU.exists_good_pt D.P.isLB z
  let x : D.X → (TK R' ⟶ D.P.A) := fun a => toUnit (TK R') ≫ D.c a
  have hx : ∀ a a', x (a + a') = x a * x a' := fun a a' => by
    show toUnit (TK R') ≫ D.c (a + a') = _
    rw [D.c_add]
    exact MonObj.comp_mul _ _ _
  let ψ : D.X → ((TK R').left.presheaf.stalk z)ˣ := fun χ => val (D.psi χ) (𝟙 _) z J'
  let r : ((TK R').left.presheaf.stalk z)ˣ := val D.rigK (𝟙 _) z J'
  have hP : ∀ a b, val (D.tau a b) (𝟙 _) z J' = ψ (a + b) * (ψ a)⁻¹ * (ψ b)⁻¹ * r⁻¹ := by
    intro a b
    unfold DegPre.tau
    rw [val_mul hJ', val_mul hJ', val_mul hJ', val_inv, val_inv, val_inv]
  let laws := fun a a' b => GlobalTheory.LamRigid.lam_iso_laws (Sp R) (Sp R') Q.B D.P.A Q.M ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ Q.cub D.cub
    (spMap ρ) β β₂ w h₁ D.P.isAb h₂ h₃ h₀ (TK R') (x a) (x a') (x b) z J J' hJ hJ'
  let κo : Over.mk ((TK R').hom ≫ spMap ρ) ⟶ TK R := Over.homMk κ hκ
  let X : D.X → (TK R ⟶ Q.B) := fun a => toUnit (TK R) ≫ Q.c (e a)
  let y : D.X → (Over.mk ((TK R').hom ≫ spMap ρ) ⟶ Q.B) := fun a => κo ≫ X a
  have hy : ∀ a, (y a).left = (x a).left ≫ β := fun a => by
    simp only [y, X, x, κo, Over.comp_left, Over.homMk_left, Rosenlicht.toUnit_left, Over.mk_hom, Category.assoc]
    rw [h₄ a, ← Category.assoc κ, hκ, Category.assoc]
  have hq : ∀ a a' b, val (Q.tau (e (a + a')) (e b)) κ z J *
      @id ((TK R').left.presheaf.stalk z)ˣ (cubV Q.cub (T := Over.mk ((TK R').hom ≫ spMap ρ)) z J (y a) (y a') (y b)) =
      val (Q.tau (e a) (e b)) κ z J * val (Q.tau (e a') (e b)) κ z J := by
    intro a a' b
    have hc : LB.Gen.Corr Q.M.L _ _ _ _
        (LB.mulGen Q.M.L _ _ _ _ (Q.tau (e (a + a')) (e b))
          (LB.pullGen Q.M.L (thφ Q.B (x3 Q.B)) thε Q.cub.t (lift (X a) (lift (X a') (X b))).left))
        (LB.mulGen Q.M.L _ _ _ _ (Q.tau (e a) (e b)) (Q.tau (e a') (e b))) :=
      corr_of_val Q.M.isLB fun y' J₀ hJ₀ => by
        have t₁ := Q.tau_add (e a) (e a') (e b) y' J₀ hJ₀
        rw [← map_add e a a'] at t₁
        refine (val_mul hJ₀ _ _ _).trans (Eq.trans ?_ (t₁.trans (val_mul hJ₀ _ _ _).symm))
        exact congrArg _ ((val_pull hJ₀ _ _ _).trans
          (congrArg (fun p => val (L := Q.M.L) (φ := thφ Q.B (x3 Q.B)) (ε := thε) Q.cub.t p y' J₀) (Category.id_comp _)))
    calc _ = val (LB.mulGen Q.M.L _ _ _ _ (Q.tau (e (a + a')) (e b))
          (LB.pullGen Q.M.L (thφ Q.B (x3 Q.B)) thε Q.cub.t (lift (X a) (lift (X a') (X b))).left)) κ z J := by
          refine Eq.trans ?_ (val_mul hJ _ _ _).symm
          exact congrArg _ (val_cub Q.cub κo hJ (X a) (X a') (X b)).symm
      _ = _ := val_corr hJ hc κ
      _ = _ := val_mul hJ _ _ _
  have hqs : ∀ a b, val (Q.tau (e a) (e b)) κ z J = val (Q.tau (e b) (e a)) κ z J := fun a b =>
    val_corr hJ (corr_of_val Q.M.isLB fun y' J₀ hJ₀ => Q.tau_symm (e a) (e b) y' J₀ hJ₀) κ
  have hcub := isCub_cubV D.cub hJ'
  obtain ⟨hs, hc⟩ := alg (fun a b => gm (𝟙 (TK R').left) z ⊤ (unitOn (f a b)))
    (fun a b => lamVal w (lift (x a) (x b)).left z J J' * val (Q.tau (e a) (e b)) κ z J)
    (fun a b => val (D.tau a b) (𝟙 _) z J') (fun a a' b => cubV D.cub z J' (x a) (x a') (x b)) ψ r
    (fun a b => h₅ κ hκ a b z J J' hJ hJ') hP
    (fun a b => by
      beta_reduce
      rw [(laws a a b).1, hqs a b])
    (fun a a' b => by
      have e₁ := (laws a a' b).2 (y a) (y a') (y b) (hy a) (hy a') (hy b)
      rw [← hx] at e₁
      have e₂ := hq a a' b
      beta_reduce
      apply Additive.ofMul.injective
      have e₁' := congrArg Additive.ofMul e₁
      have e₂' := congrArg Additive.ofMul e₂
      simp only [ofMul_mul, id] at e₁' e₂' ⊢
      linear_combination (norm := abel) e₁' + e₂')
    (fun a b c => (hcub.s01 _ _ _).trans (hcub.s12 _ _ _))
  have inj : ∀ u v : (FractionRing R')ˣ, gm (𝟙 (TK R').left) z ⊤ (unitOn u) = gm (𝟙 (TK R').left) z ⊤ (unitOn v) →
      u = v := fun u v h =>
    ReciprocityTheory.ChartRestriction.G.H1.unitOn_injective (GlobalTheory.ArcData.unit_ext_field (𝟙 (Sp (FractionRing R'))) z fun _ => h)
  have hm : ∀ u v : (FractionRing R')ˣ, unitOn (u * v) = unitOn u * unitOn v := fun u v =>
    map_mul (Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R'))).inv.hom.toMonoidHom) u v
  refine ⟨fun a b => inj _ _ (hs a b), fun a b c => inj _ _ ?_⟩
  rw [hm, hm, map_mul, map_mul]
  exact hc a b c

end GlobalTheory.PolDeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedPeriodComparisonSymmCocycleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedPeriod_comparison_symm_cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (f : D.X → D.X → (FractionRing R')ˣ), Function.Injective ρ → Half Q ρ D e f → (∀ a b, f a b = f b a) ∧ ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c := by
  first | exact @GlobalTheory.PolDeg.half_symm_cocycle | exact GlobalTheory.PolDeg.half_symm_cocycle | (intros; apply GlobalTheory.PolDeg.half_symm_cocycle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauBimultOfRefinesPolarisedData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauBimultOfRefinesPolarisedData
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

theorem exists_fracSpec {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ) : ∃ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ := by
  have hu : ∀ y : nonZeroDivisors R, IsUnit ((algebraMap R' (FractionRing R')).comp ρ y) := fun y => by
    refine IsUnit.mk0 _ ?_
    rw [RingHom.comp_apply, ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact (map_ne_zero_iff ρ hρ).2 (nonZeroDivisors.ne_zero y.2)
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) hu)), ?_⟩
  simp only [jK, spMap, ← Spec.map_comp]
  congr 1
  ext x
  simp [IsLocalization.lift_eq]

theorem toUnit_left {S : Scheme.{0}} (T : Over S) : (toUnit T).left = T.hom := by
  simpa using Over.w (toUnit T)

theorem tauBimult_of_half : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R)
    (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X), Function.Injective ρ → Half Q ρ D e (fun _ _ => 1) →
    D.TauBimult := by
  intro R _ _ R' _ _ Q ρ D e hρ h
  obtain ⟨κ, hκ⟩ := exists_fracSpec ρ hρ
  obtain ⟨β, β₂, w, hpb, hsq, hgen, hnorm, hc, hper⟩ := h
  have per : ∀ a b z J J', Good Q.M.L z J → Good D.P.L z J' → val (D.tau a b) (𝟙 _) z J' =
      lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' * val (Q.tau (e a) (e b)) κ z J := by
    intro a b z J J' hJ hJ'
    have := hper κ hκ a b z J J' hJ hJ'
    rwa [show unitOn (1 : (FractionRing R')ˣ) = 1 from map_one _, map_one, _root_.mul_one] at this
  let k : Over.mk ((TK R').hom ≫ spMap ρ) ⟶ TK R := Over.homMk κ hκ
  have hQ : ∀ a a' b : Q.X, ∀ z J, Good Q.M.L z J →
      val (Q.tau (a + a') b) κ z J * @id ((TK R').left.presheaf.stalk z)ˣ
        (cubV (T := Over.mk ((TK R').hom ≫ spMap ρ)) Q.cub z J
        (k ≫ toUnit (TK R) ≫ Q.c a) (k ≫ toUnit (TK R) ≫ Q.c a') (k ≫ toUnit (TK R) ≫ Q.c b)) =
      val (Q.tau a b) κ z J * val (Q.tau a' b) κ z J := by
    intro a a' b z J hJ
    have hcorr : LB.Gen.Corr Q.M.L _ _ _ _ (LB.mulGen Q.M.L _ _ _ _ (Q.tau (a + a') b)
        (LB.pullGen Q.M.L (thφ Q.B (x3 Q.B)) thε Q.cub.t
          (lift (toUnit (TK R) ≫ Q.c a) (lift (toUnit (TK R) ≫ Q.c a') (toUnit (TK R) ≫ Q.c b))).left))
        (LB.mulGen Q.M.L _ _ _ _ (Q.tau a b) (Q.tau a' b)) := by
      refine corr_of_val Q.M.isLB fun y J hJ => ?_
      refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
      refine (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)).trans ?_
      rw [Category.id_comp]
      exact Q.tau_add a a' b y J hJ
    have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ hcorr κ).trans (val_mul hJ _ _ _))
    refine Eq.trans ?_ this
    exact congrArg₂ (· * ·) rfl (val_cub Q.cub k hJ _ _ _).symm
  intro a a' b
  refine corr_of_val D.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ, -⟩ := exists_good Q.M.L Q.M.isLB y (K := PEmpty) (fun i => i.elim) (fun i => i.elim)
    (fun i => i.elim) (fun i => i.elim)
  refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
  refine (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _)).trans ?_
  rw [Category.id_comp]
  have hx : toUnit (TK R') ≫ D.c (a + a') = (toUnit (TK R') ≫ D.c a) * (toUnit (TK R') ≫ D.c a') := by
    rw [D.c_add, padd, comp_lift_assoc, Hom.mul_def]
  have hu : ∀ χ : D.X, (k ≫ toUnit (TK R) ≫ Q.c (e χ)).left = (toUnit (TK R') ≫ D.c χ).left ≫ β := by
    intro χ
    simp only [Over.comp_left, Over.homMk_left, toUnit_left, Category.assoc, hc, k]
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ Over.Hom.left (Q.c (e χ))) hκ
  obtain ⟨-, hw⟩ := GlobalTheory.T.mumfordBundleIso_normalised_respects_laws _ _ Q.B D.P.A Q.M ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ Q.cub D.cub (spMap ρ) β β₂ w
    hpb D.P.isAb hsq hgen hnorm (TK R') (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c a') (toUnit (TK R') ≫ D.c b)
    y J J' hJ hJ'
  have hw' := hw _ _ _ (hu a) (hu a') (hu b)
  rw [← hx] at hw'
  have hq := hQ (e a) (e a') (e b) y J hJ
  rw [← map_add (f := _)] at hq
  change val (D.tau (a + a') b) (𝟙 _) y J' * cubV D.cub y J' _ _ _ = _
  rw [per _ _ y J J' hJ hJ', per _ _ y J J' hJ hJ', per _ _ y J J' hJ hJ']
  calc _ = (lamVal w (lift (toUnit (TK R') ≫ D.c (a + a')) (toUnit (TK R') ≫ D.c b)).left y J J' *
        cubV D.cub y J' (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c a') (toUnit (TK R') ≫ D.c b)) *
        val (Q.tau (e (a + a')) (e b)) κ y J := by ac_rfl
    _ = _ := by
      rw [hw']
      calc _ = lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left y J J' *
            lamVal w (lift (toUnit (TK R') ≫ D.c a') (toUnit (TK R') ≫ D.c b)).left y J J' *
            (val (Q.tau (e (a + a')) (e b)) κ y J * @id ((TK R').left.presheaf.stalk y)ˣ
              (cubV (T := Over.mk ((TK R').hom ≫ spMap ρ)) Q.cub y J
              (k ≫ toUnit (TK R) ≫ Q.c (e a)) (k ≫ toUnit (TK R) ≫ Q.c (e a')) (k ≫ toUnit (TK R) ≫ Q.c (e b)))) := by
            ac_rfl
        _ = _ := by rw [hq]; ac_rfl

end GlobalTheory.PolDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauBimultOfRefinesPolarisedDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tauBimult_of_refines_polarised_data : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X), Function.Injective ρ → Half Q ρ D e (fun _ _ => 1) → D.TauBimult := by
  first | exact @GlobalTheory.PolDeg.tauBimult_of_half | exact GlobalTheory.PolDeg.tauBimult_of_half | (intros; apply GlobalTheory.PolDeg.tauBimult_of_half <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataOfMonomialEvenBimultiplicative
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataOfMonomialEvenBimultiplicative
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DegFromMonomial

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (m : ℕ) (r : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ D.X), D.PsiEven → D.TauBimult → IsMonomial D r β → (∀ i, r i ∈ maximalIdeal R) → (∀ i y z, β i y z = β i z y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ DD : DegData R (maximalIdeal R), DD.toPre = D := by
  intro R _ _ _ D m r β hE hT hM hr hs hp
  have hmem : ∀ (y : D.X) (u : Rˣ) (n : Fin m → ℕ) (k : ℕ), k ≤ ∑ i, n i →
      (u : R) * ∏ i, r i ^ n i ∈ maximalIdeal R ^ k := by
    intro y u n k hk
    refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hk ?_)
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hr i) _
  let S : LinearMap.BilinForm ℤ D.X := ∑ i, β i
  have hS : ∀ y z, S y z = ∑ i, β i y z := fun y z => by
    simp [S, LinearMap.sum_apply]
  have hSs : ∀ y z, S y z = S z y := fun y z => by
    rw [hS, hS]; exact Finset.sum_congr rfl fun i _ => hs i y z
  have hSp : ∀ y, y ≠ 0 → 0 < S y y := fun y hy => by
    rw [hS]
    obtain ⟨i, hi⟩ := hp y hy
    exact Finset.sum_pos' (fun j _ => hM.nonneg j y) ⟨i, Finset.mem_univ _, hi⟩
  refine ⟨{ toPre := D, psi_even := hE, tau_bimult := hT, psi_pos := ?_, psi_tendsto := ?_ }, rfl⟩
  · intro y hy
    obtain ⟨u, n, hn, hc⟩ := hM y
    refine (GlobalTheory.PeriodFormEdge.psiIn_iff hc _).2 ?_
    have h1 := hmem y u n 1 ?_
    · rwa [pow_one] at h1
    · obtain ⟨i, hi⟩ := hp y hy
      have : 1 ≤ n i := by have := hn i; omega
      exact this.trans (Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i))
  · intro k
    refine (GlobalTheory.ToricData.finite_form_le S hSs hSp (2 * k)).subset fun y hy => ?_
    simp only [Set.mem_setOf_eq] at hy ⊢
    by_contra hlt
    obtain ⟨u, n, hn, hc⟩ := hM y
    refine hy ((GlobalTheory.PeriodFormEdge.psiIn_iff hc _).2 (hmem y u n k ?_))
    have e : S y y = 2 * ((∑ i, n i : ℕ) : ℤ) := by
      rw [hS, Nat.cast_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => hn i
    omega

end GlobalTheory.DegFromMonomial
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataOfMonomialEvenBimultiplicativeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationData_of_monomial_even_bimultiplicative : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (m : ℕ) (r : Fin m → R) (β : Fin m → LinearMap.BilinForm ℤ D.X), D.PsiEven → D.TauBimult → IsMonomial D r β → (∀ i, r i ∈ maximalIdeal R) → (∀ i y z, β i y z = β i z y) → (∀ y, y ≠ 0 → ∃ i, 0 < β i y y) → ∃ DD : DegData R (maximalIdeal R), DD.toPre = D := by
  first | exact @GlobalTheory.DegFromMonomial.main | exact GlobalTheory.DegFromMonomial.main | (intros; apply GlobalTheory.DegFromMonomial.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaleDegDataTrivialisationsPsiEvenOfSqrt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaleDegDataTrivialisationsPsiEvenOfSqrt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PolDeg

theorem rescale_psiEven : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (h eta : D.X → (FractionRing R)ˣ),
    EvenDefect D h → (∀ a b, eta (a + b) = eta a * eta b) → (∀ a, eta a ^ 2 = h a) → (rescale D eta).PsiEven := by
  intro R _ _ D h eta hD hadd hsq
  have h0 : eta 0 = 1 := by
    have e := hadd 0 0
    rw [add_zero] at e
    exact mul_eq_left.1 e.symm
  have key : ∀ χ : D.X, eta (-χ) * h χ = eta χ := fun χ => by
    rw [← hsq, pow_two, ← _root_.mul_assoc, ← hadd, neg_add_cancel, h0, _root_.one_mul]
  have hu : ∀ a b : (FractionRing R)ˣ, unitOn (a * b) = unitOn a * unitOn b := fun a b => map_mul _ a b
  refine fun (χ : D.X) => corr_of_val D.P.isLB fun y J hJ => ?_
  show val (LB.mulGen D.P.L _ _ _ _ (GlobalTheory.UU.scaleGen (unitOn (eta (-χ))) (D.psi (-χ)))
      (LB.pullGen D.P.L _ _ D.sym (D.xK χ))) (𝟙 _) y J = val (GlobalTheory.UU.scaleGen (unitOn (eta χ)) (D.psi χ)) (𝟙 _) y J
  refine (val_mul hJ _ _ _).trans ?_
  refine (congrArg₂ (· * ·) (GlobalTheory.UU.val_scaleGen _ _ _ hJ)
    ((val_pull hJ _ _ _).trans (congrArg (fun r => val D.sym r y J) (Category.id_comp _)))).trans ?_
  refine (_root_.mul_assoc _ _ _).trans ((congrArg (_ * ·) (hD χ y J hJ)).trans ?_)
  refine (_root_.mul_assoc _ _ _).symm.trans ((congrArg (· * _) ((map_mul _ _ _).symm.trans
    (congrArg (gm _ y ⊤) ((hu _ _).symm.trans (congrArg unitOn (key χ)))))).trans (GlobalTheory.UU.val_scaleGen _ _ _ hJ).symm)

end GlobalTheory.PolDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaleDegDataTrivialisationsPsiEvenOfSqrtStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rescaleDegDataTrivialisations_psiEven_of_sqrt : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (h eta : D.X → (FractionRing R)ˣ), EvenDefect D h → (∀ a b, eta (a + b) = eta a * eta b) → (∀ a, eta a ^ 2 = h a) → (rescale D eta).PsiEven := by
  first | exact @GlobalTheory.PolDeg.rescale_psiEven | exact GlobalTheory.PolDeg.rescale_psiEven | (intros; apply GlobalTheory.PolDeg.rescale_psiEven <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRawDegenerationDataInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRawDegenerationDataInjective
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PsiRing GlobalTheory.StrictPull GlobalTheory.ModelData GlobalTheory.DegPull

namespace GlobalTheory.BaseChangeDeg

theorem exists_baseChange : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsNoetherianRing R₂] (σ : R₁ →+* R₂) (D₁ : DegPre R₁) (gam : FractionRing R₁ →+* FractionRing R₂), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) → ∃ (D₂ : DegPre R₂) (β : D₂.P.A.left ⟶ D₁.P.A.left) (v : LB.Iso D₂.P.L (D₁.P.L.pull β)) (xe : D₂.X ≃+ D₁.X), IsGrpPullback D₂.P.A D₁.P.A (spMap σ) β ∧ v.IsGen ∧ (∀ x, (D₂.c x).left ≫ β = spMap σ ≫ (D₁.c (xe x)).left) ∧ GlobalTheory.PsiRing.RigCmp σ D₁ D₂ β v ∧ GlobalTheory.PsiRing.PsiCmp D₁ D₂ β v xe (spMap gam) := by
  intro R₁ _ _ R₂ _ _ _ σ D₁ gam hgam
  let P' : PolAV (Spec (CommRingCat.of R₂)) :=
    { A := (Over.pullback (spMap σ)).obj D₁.P.A
      isAb := TLinPf.isAb_pullback (spMap σ) D₁.P.A D₁.P.isAb
      g := D₁.P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (isGrpPullback_pullback D₁.P.A (spMap σ)).1 D₁.P.smoothDim
      L := D₁.P.L.pull (pullback.fst D₁.P.A.hom (spMap σ))
      isLB := pull_isLB D₁.P.isLB _
      rigid := PolBaseChange.rigidified_pull (isGrpPullback_pullback D₁.P.A (spMap σ)) D₁.P.rigid
      sym := PolBaseChange.sym_pull (isGrpPullback_pullback D₁.P.A (spMap σ)) D₁.P.sym
      ample := by
        haveI := D₁.P.isAb.proper
        exact AmpleBaseChange.relAmple_of_isPullback D₁.P.isLB D₁.P.ample (IsPullback.of_hasPullback D₁.P.A.hom (spMap σ))
      ktriv := by
        obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl (pull_isLB D₁.P.isLB (pullback.fst D₁.P.A.hom (spMap σ)))
        exact kTriv_pull (isGrpPullback_pullback D₁.P.A (spMap σ)) D₁.P.isLB (pull_isLB D₁.P.isLB _) ((isGen_iff w).1 hw) D₁.P.ktriv }
  let F := pullback.fst D₁.P.A.hom (spMap σ)
  have gp : IsGrpPullback P'.A D₁.P.A (spMap σ) F := isGrpPullback_pullback D₁.P.A (spMap σ)
  obtain ⟨w, hw, -⟩ := exists_strict D₁.P.isLB F
  have hF := gp.1
  have hw' := (isGen_iff w).1 hw
  have hE : eSec P'.A ≫ F = spMap σ ≫ eSec D₁.P.A := (cubeMapOf gp).e_comm
  obtain ⟨rig, hrig, Hrig⟩ := exists_pmaps hw' D₁.P.isLB P'.isLB (K := PUnit) (φ' := fun _ => eSec P'.A)
    (φ := fun _ => eSec D₁.P.A) (ε := fun _ => 1) (spMap σ) (fun _ => hE) D₁.rig D₁.rig_gen
  obtain ⟨cub⟩ := nonempty_cubical_pull gp D₁.cub ⟨P'.L, rig, P'.isLB, hrig⟩ hw'
  obtain ⟨sym, hsym, hsr⟩ := exists_sym_pull gp D₁.P.isLB P'.isLB hw' D₁.sym D₁.sym_gen D₁.sym_rig
  obtain ⟨c, hc⟩ : ∃ c : D₁.X → (𝟙_ (Over (Spec (CommRingCat.of R₂))) ⟶ P'.A), ∀ x,
      (c x).left ≫ F = spMap σ ≫ (D₁.c x).left :=
    ⟨fun x => Over.homMk (hF.lift (spMap σ ≫ (D₁.c x).left) (𝟙 _) (by
      rw [Category.assoc, Over.w, Category.id_comp]; exact Category.comp_id _)) (hF.lift_snd _ _ _),
      fun x => hF.lift_fst _ _ _⟩
  have cadd : ∀ a b, c (a + b) = padd P'.A (c a) (c b) := fun a b => by
    refine Over.OverMorphism.ext (hF.hom_ext ?_ (by rw [Over.w, Over.w]))
    have u : (toUnit (Over.mk ((𝟙_ (Over (Spec (CommRingCat.of R₂)))).hom ≫ spMap σ))).left = spMap σ :=
      Category.id_comp _
    have m := gp.2 _ (c a) (c b) (toUnit _ ≫ D₁.c a) (toUnit _ ≫ D₁.c b)
      (by rw [hc, Over.comp_left, u]) (by rw [hc, Over.comp_left, u])
    rw [← MonObj.comp_mul, Over.comp_left, u] at m
    rw [hc, D₁.c_add]
    exact m
  have hK : jK R₂ ≫ spMap σ = spMap gam ≫ jK R₁ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact (hgam r).symm
  have hx : ∀ x, ptK (c x) ≫ F = spMap gam ≫ D₁.xK x := fun x => by
    show (jK R₂ ≫ (c x).left) ≫ F = spMap gam ≫ jK R₁ ≫ (D₁.c x).left
    refine (Category.assoc _ _ _).trans ((congrArg (jK R₂ ≫ ·) (hc x)).trans ?_)
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (D₁.c x).left) hK)).trans (Category.assoc _ _ _)
  choose psi hpsi vpsi using fun x => exists_pmaps hw' D₁.P.isLB P'.isLB (K := PUnit)
    (φ' := fun _ => ptK (c x)) (φ := fun _ => D₁.xK x) (ε := fun _ => -1) (spMap gam) (fun _ => hx x)
    (D₁.psi x) (D₁.psi_gen x)
  let D' : DegPre R₂ :=
    { P := P', rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := D₁.X,
      c := c, c_add := cadd, psi := psi, psi_gen := hpsi }
  exact ⟨D', F, w, AddEquiv.refl _, gp, hw, hc, Hrig, vpsi⟩

end GlobalTheory.BaseChangeDeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRawDegenerationDataInjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseChange_raw_degenerationData_injective : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsNoetherianRing R₂] (σ : R₁ →+* R₂) (D₁ : DegPre R₁) (gam : FractionRing R₁ →+* FractionRing R₂), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) → ∃ (D₂ : DegPre R₂) (β : D₂.P.A.left ⟶ D₁.P.A.left) (v : LB.Iso D₂.P.L (D₁.P.L.pull β)) (xe : D₂.X ≃+ D₁.X), IsGrpPullback D₂.P.A D₁.P.A (spMap σ) β ∧ v.IsGen ∧ (∀ x, (D₂.c x).left ≫ β = spMap σ ≫ (D₁.c (xe x)).left) ∧ GlobalTheory.PsiRing.RigCmp σ D₁ D₂ β v ∧ GlobalTheory.PsiRing.PsiCmp D₁ D₂ β v xe (spMap gam) := by
  first | exact @GlobalTheory.BaseChangeDeg.exists_baseChange | exact GlobalTheory.BaseChangeDeg.exists_baseChange | (intros; apply GlobalTheory.BaseChangeDeg.exists_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PolDeg.refine_monomial_of_polarised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (m : ℕ) (t : Fin m → R) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), IsCN R → Q.IsMonomialTau t δ → (∀ i, t i ∈ maximalIdeal R) → (∀ i, t i ≠ 0) → (∀ i y z, δ i y z = δ i z y) → (∀ i y, 0 ≤ δ i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < δ i y y) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : Fin m → R') (D : DegData R' (maximalIdeal R')) (e : D.toPre.X ≃+ Q.X), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ Refines Q ρ D.toPre e ∧ IsMonomial D.toPre r fun i => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ i) := by
  intro R _ _ _ Q m t δ hCN hmono htm ht0 hsymm hnn hdef
  obtain ⟨R₁, _, _, _, ρ₁, P, β, β₂, hCN₁, hinj₁, hfin₁, hloc₁, hpb, hsq, hiso⟩ := GlobalTheory.T.exists_symmetricPolarisation_finiteExtension R Q hCN
  haveI : IsNoetherianRing R₁ := hCN₁.1
  obtain ⟨D, e, f, hD⟩ := GlobalTheory.T.exists_symmetric_data_compare_polarised_up_to_function R R₁ Q ρ₁ P β β₂ hinj₁ hpb hsq hiso
  obtain ⟨hfs, hfc⟩ := GlobalTheory.T.polarisedPeriod_comparison_symm_cocycle R R₁ Q ρ₁ D e f hinj₁ hD
  obtain ⟨g, hg⟩ := GlobalTheory.T.symmetric_twoCocycle_free_abelian_isCoboundary D.X _ f hfs hfc
  have hD₁ : Half Q ρ₁ (rescale D g) e (fun _ _ => 1) :=
    GlobalTheory.T.refinesPolarisedData_rescale_coboundary R R₁ Q ρ₁ D e f (fun _ _ => 1) g hD (fun a b => by rw [hg a b, _root_.mul_one])
  have hb₁ : (rescale D g).TauBimult := GlobalTheory.T.tauBimult_of_refines_polarised_data R R₁ Q ρ₁ (rescale D g) e hinj₁ hD₁
  obtain ⟨h, hhom, hev⟩ := GlobalTheory.T.exists_hom_evenDefect_bimultiplicative_periods R₁ (rescale D g) hb₁
  obtain ⟨R₂, _, _, _, σ, gam, r, et, hCN₂, hinj₂, hfin₂, hloc₂, hgam, hr, hη, hη2⟩ :=
    GlobalTheory.T.exists_sqrt_latticeHom_finiteExtension_complete R₁ (rescale D g).X h m (fun i => ρ₁ (t i)) hCN₁ hhom
  haveI : IsNoetherianRing R₂ := hCN₂.1
  obtain ⟨D₂, β', v, xe, hpb', hv, hc', hrig, hpsi⟩ := GlobalTheory.T.exists_baseChange_raw_degenerationData_injective R₁ R₂ σ (rescale D g) gam hgam
  have hD₂ := GlobalTheory.T.refinesPolarisedData_baseChange_symmetric R Q R₁ R₂ σ (rescale D g) D₂ β' v xe gam hgam hpb' hv hc' hrig hpsi ρ₁ e hinj₁ hD₁
  have hev₂ := GlobalTheory.T.evenDefect_degenerationData_baseChange R₁ R₂ σ (rescale D g) D₂ β' v xe gam hgam hpb' hv hc' hrig hpsi h hev
  have hinj : Function.Injective (σ.comp ρ₁) := hinj₂.comp hinj₁
  have hηx : ∀ a b : D₂.X, et (xe (a + b)) = et (xe a) * et (xe b) := fun a b => by rw [map_add (f := _), hη]
  have hD₃ : Half Q (σ.comp ρ₁) (rescale D₂ fun χ => et (xe χ)) (xe.trans e) (fun _ _ => 1) :=
    GlobalTheory.T.refinesPolarisedData_rescale_coboundary R R₂ Q (σ.comp ρ₁) D₂ (xe.trans e) (fun _ _ => 1) (fun _ _ => 1) (fun χ => et (xe χ)) hD₂
      (fun a b => by rw [hηx, _root_.mul_one, mul_right_comm (et (xe a)), mul_inv_cancel, _root_.one_mul, mul_inv_cancel])
  have hev₃ : (rescale D₂ fun χ => et (xe χ)).PsiEven :=
    GlobalTheory.T.rescaleDegDataTrivialisations_psiEven_of_sqrt R₂ D₂ _ (fun χ => et (xe χ)) hev₂ hηx (fun a => hη2 (xe a))
  have hb₃ : (rescale D₂ fun χ => et (xe χ)).TauBimult :=
    GlobalTheory.T.tauBimult_of_refines_polarised_data R R₂ Q (σ.comp ρ₁) _ (xe.trans e) hinj hD₃
  have hr' : ∀ i, r i ^ 2 = (σ.comp ρ₁) (t i) := fun i => hr i
  have hmon := GlobalTheory.T.exists_monomial_trivialisation_sqrt_refinedPolarisedData R R₂ Q (σ.comp ρ₁) (rescale D₂ fun χ => et (xe χ)) (xe.trans e) m t r δ hCN₂ hinj hD₃
    hev₃ hb₃ hmono hnn ht0 hr'
  have hrm : ∀ i, r i ∈ maximalIdeal R₂ := by
    intro i
    refine (inferInstance : (maximalIdeal R₂).IsPrime).mem_of_pow_mem 2 ?_
    rw [hr' i, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (mem_maximalIdeal _).1 (htm i) ((isUnit_map_iff (σ.comp ρ₁) _).1 hu)
  have key : ∀ (D₃ : DegPre R₂) (e' : D₃.X ≃+ Q.X), D₃.PsiEven → D₃.TauBimult →
      Half Q (σ.comp ρ₁) D₃ e' (fun _ _ => 1) →
      IsMonomial D₃ r (fun i => (2 : ℤ) • pull e'.toIntLinearEquiv.toLinearMap (δ i)) →
      ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : Fin m → R')
        (D : DegData R' (maximalIdeal R')) (e : D.toPre.X ≃+ Q.X), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧
        IsLocalHom ρ ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ Refines Q ρ D.toPre e ∧
        IsMonomial D.toPre r fun i => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ i) := by
    intro D₃ e' h1 h2 h3 h4
    obtain ⟨DD, rfl⟩ := GlobalTheory.T.degenerationData_of_monomial_even_bimultiplicative R₂ D₃ m r (fun i => (2 : ℤ) • pull e'.toIntLinearEquiv.toLinearMap (δ i))
      h1 h2 h4 hrm (fun i y z => by simp [pull, hsymm i (e' y) (e' z)])
      (fun y hy => by
        obtain ⟨i, hi⟩ := hdef (e' y) (by simpa using hy)
        exact ⟨i, by simpa [pull] using hi⟩)
    exact ⟨R₂, inferInstance, inferInstance, inferInstance, σ.comp ρ₁, r, DD, e', hCN₂, hinj,
      hfin₂.comp hfin₁, inferInstance, hr', h3.refines, h4⟩
  exact key _ _ hev₃ hb₃ hD₃ hmon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinePolarisedMonomialPeriodsMonomialDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refine_polarised_monomial_periods_monomial_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (m : ℕ) (t : Fin m → R) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), IsCN R → Q.IsMonomialTau t δ → (∀ i, t i ∈ maximalIdeal R) → (∀ i, t i ≠ 0) → (∀ i y z, δ i y z = δ i z y) → (∀ i y, 0 ≤ δ i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < δ i y y) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : Fin m → R') (D : DegData R' (maximalIdeal R')) (e : D.toPre.X ≃+ Q.X), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ Refines Q ρ D.toPre e ∧ IsMonomial D.toPre r fun i => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ i) := by
  first | exact @GlobalTheory.PolDeg.refine_monomial_of_polarised | exact GlobalTheory.PolDeg.refine_monomial_of_polarised | (intros; apply GlobalTheory.PolDeg.refine_monomial_of_polarised <;> assumption)
end
