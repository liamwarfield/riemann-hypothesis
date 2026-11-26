module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjSpaceHom

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEquivCohomologyOfQuasiIsomorphism
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEquivCohomologyOfQuasiIsomorphism
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfKerCoh

theorem ker_equiv_cohomology : ∀ (S P₀ P₁ P₂ T B₀ B₁ B₂ : Type) [CommRing S] [AddCommGroup P₀] [Module S P₀] [AddCommGroup P₁] [Module S P₁] [AddCommGroup P₂] [Module S P₂] [AddCommGroup T] [Module S T] [AddCommGroup B₀] [Module S B₀] [AddCommGroup B₁] [Module S B₁] [AddCommGroup B₂] [Module S B₂] (a₀ : P₀ →ₗ[S] P₁) (a₁ : P₁ →ₗ[S] P₂) (π : P₁ →ₗ[S] T) (dT : T →ₗ[S] P₂) (Z : Submodule S B₁) (dB : B₀ →ₗ[S] Z) (b₁ : B₁ →ₗ[S] B₂) (f : P₁ →ₗ[S] B₁) (ψ₀ : P₀ →ₗ[S] B₀), Function.Surjective π → Function.Exact a₀ π → dT ∘ₗ π = a₁ → (∀ z, z ∈ Z ↔ b₁ z = 0) → (∀ x, a₁ x = 0 → b₁ (f x) = 0) → (∀ y, f (a₀ y) = (dB (ψ₀ y) : B₁)) → QIsoAt a₀ a₁ (Z.subtype ∘ₗ dB) b₁ f → Nonempty (LinearMap.ker dT ≃ₗ[S] Z ⧸ LinearMap.range dB) := by
  intro S P₀ P₁ P₂ T B₀ B₁ B₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a₀ a₁ π dT Z dB b₁ f ψ₀ hπ hex hdT hZ hf hψ hq
  have hdTπ : ∀ x, dT (π x) = a₁ x := fun x => LinearMap.congr_fun hdT x
  let H : LinearMap.ker a₁ →ₗ[S] LinearMap.ker dT :=
    (π.comp (LinearMap.ker a₁).subtype).codRestrict (LinearMap.ker dT) fun x => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, hdTπ]
      exact x.2
  let G : LinearMap.ker a₁ →ₗ[S] Z ⧸ LinearMap.range dB :=
    (LinearMap.range dB).mkQ.comp ((f.comp (LinearMap.ker a₁).subtype).codRestrict Z fun x =>
      (hZ _).2 (hf _ x.2))
  have hH : Function.Surjective H := by
    rintro ⟨t, ht⟩
    obtain ⟨x, rfl⟩ := hπ t
    have hx : a₁ x = 0 := by
      rw [← hdTπ]
      exact ht
    exact ⟨⟨x, hx⟩, rfl⟩
  have hG : Function.Surjective G := by
    intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨x, y, hx, hxy⟩ := hq.2 z ((hZ z).1 z.2)
    refine ⟨⟨x, hx⟩, ?_⟩
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    exact ⟨y, Subtype.ext hxy.symm⟩
  have hker : LinearMap.ker H = LinearMap.ker G := by
    ext ⟨x, hx⟩
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    constructor
    · intro h
      have h' : π x = 0 := congrArg Subtype.val h
      obtain ⟨y, rfl⟩ := (hex x).1 h'
      show Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨ψ₀ y, Subtype.ext (hψ y).symm⟩
    · intro h
      have h' : (⟨f x, (hZ _).2 (hf _ hx)⟩ : Z) ∈ LinearMap.range dB :=
        (Submodule.Quotient.mk_eq_zero _).1 h
      obtain ⟨y, hy⟩ := h'
      obtain ⟨y', rfl⟩ := hq.1 x hx ⟨y, congrArg Subtype.val hy⟩
      exact Subtype.ext ((hex _).2 ⟨y', rfl⟩)
  exact ⟨(LinearMap.quotKerEquivOfSurjective H hH).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective G hG))⟩

end GlobalTheory.CompanionTheory.PerfKerCoh
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEquivCohomologyOfQuasiIsomorphismStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
alias GlobalTheory.T.kernel_equiv_cohomology_of_quasi_isomorphism := GlobalTheory.CompanionTheory.PerfKerCoh.ker_equiv_cohomology
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordDimEqRelativeDim
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordDimEqRelativeDim
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.CoordCard

theorem card_eq_of_etale {K L : Type} [Field K] [CommRing L] [Nontrivial L] [Algebra K L] {m n : ℕ}
    [Algebra (MvPolynomial (Fin m) K) L] [IsScalarTower K (MvPolynomial (Fin m) K) L]
    [Algebra.FormallyEtale (MvPolynomial (Fin m) K) L]
    [Algebra.IsStandardSmoothOfRelativeDimension n K L] : m = n := by
  let b := KaehlerDifferential.mvPolynomialBasis K (Fin m)
  let b' := (b.baseChange L).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (MvPolynomial (Fin m) K) L)
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := K) (S := L) n
  have h1 := b'.mk_eq_rank''
  rw [hr] at h1
  simpa using h1

theorem card_eq_of_away {K A L : Type} [Field K] [CommRing A] [CommRing L] [Nontrivial L] [Algebra A L] {m n : ℕ}
    (t : A) [IsLocalization.Away t L] (g : K →+* A) (φ : MvPolynomial (Fin m) K →+* A)
    (hφ : ∀ r, φ (MvPolynomial.C r) = g r) (hE : φ.Etale)
    (hf : RingHom.IsStandardSmoothOfRelativeDimension n ((algebraMap A L).comp g)) : m = n := by
  letI iPA : Algebra (MvPolynomial (Fin m) K) A := φ.toAlgebra
  letI iKL : Algebra K L := ((algebraMap A L).comp g).toAlgebra
  letI iPL : Algebra (MvPolynomial (Fin m) K) L := ((algebraMap A L).comp φ).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin m) K) A L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower K (MvPolynomial (Fin m) K) L :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap A L (g r) = algebraMap A L (φ (MvPolynomial.C r))
      rw [hφ]
  haveI : Algebra.Etale (MvPolynomial (Fin m) K) A := hE
  haveI : Algebra.FormallyEtale A L := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers t)
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin m) K) L := Algebra.FormallyEtale.comp _ A _
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n K L := hf
  exact card_eq_of_etale (K := K) (L := L)

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n q] {V : X.Opens}, (V : Set X).Nonempty → ∀ {m : ℕ} (c : Coord q V m), m = n := by
  intro K _ X q n hn V hV m c
  obtain ⟨x, hx⟩ := hV
  have hnt : Nontrivial Γ(X, V) := (X.presheaf.germ V x hx).hom.domain_nontrivial
  obtain ⟨s, hs, h'⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) q hn
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, c.affine⟩ le_top
  obtain ⟨p, hp⟩ := Ideal.exists_maximal Γ(X, V)
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ p := by
    by_contra hc
    exact hp.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 fun t ht => by_contra fun h => hc ⟨t, ht, h⟩))
  have : Nontrivial (Localization.Away t) := by
    by_contra hc
    obtain ⟨k, hk⟩ := (IsLocalization.subsingleton_iff (M := Submonoid.powers t)).1 (not_nontrivial_iff_subsingleton.1 hc)
    exact htp (hp.isPrime.mem_of_pow_mem k (by rw [show t ^ k = 0 from hk]; exact p.zero_mem))
  have h₁ := h' t ht
  let e : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have hf : RingHom.IsStandardSmoothOfRelativeDimension n
      ((algebraMap Γ(X, V) (Localization.Away t)).comp (strV q V)) :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _ e h₁
  exact card_eq_of_away (L := Localization.Away t) t (strV q V) (MvPolynomial.eval₂Hom (strV q V) c.t)
    (fun r => by simp) c.etale hf

end GlobalTheory.CompanionTheory.CoordCard
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordDimEqRelativeDimStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
alias GlobalTheory.T.coord_dim_eq_relative_dim := GlobalTheory.CompanionTheory.CoordCard.main
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraicOverTorusOfIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraicOverTorusOfIntegral
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoTorus

theorem isAlgebraic_unit_inv {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    (A : Subalgebra K R) (u : Rˣ) (hu : (u : R) ∈ A) : IsAlgebraic A ((u⁻¹ : Rˣ) : R) := by
  refine ⟨Polynomial.C (⟨u, hu⟩ : A) * Polynomial.X - 1, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 0) h
    simp at h1
  · simp [Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_mul]

theorem isAlgebraic_unit_zpow {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    (A : Subalgebra K R) (u : Rˣ) (hu : (u : R) ∈ A) (m : ℤ) : IsAlgebraic A ((u ^ m : Rˣ) : R) := by
  obtain ⟨n, rfl | rfl⟩ := m.eq_nat_or_neg
  · have h : IsAlgebraic A (u : R) := isAlgebraic_algebraMap (⟨u, hu⟩ : A)
    simpa using h.pow n
  · simpa using (isAlgebraic_unit_inv A u hu).pow n

theorem isAlgebraic_tpow {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R] {d : ℕ}
    (t : Fin d → Rˣ) (m : Fin d → ℤ) :
    IsAlgebraic (Algebra.adjoin K (Set.range fun k => (t k : R))) (tpow t m) := by
  set A := Algebra.adjoin K (Set.range fun k => (t k : R))
  have hmem : ∀ k, (t k : R) ∈ A := fun k => Algebra.subset_adjoin ⟨k, rfl⟩
  have key : ∀ s : Finset (Fin d), IsAlgebraic A (((∏ k ∈ s, t k ^ m k : Rˣ)) : R) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (isAlgebraic_one : IsAlgebraic A (1 : R))
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Units.val_mul]
      exact (isAlgebraic_unit_zpow A (t a) (hmem a) (m a)).mul ih
  exact key Finset.univ

theorem isAlgebraic_of_integral_torusS : ∀ {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R] {d : ℕ} (t : Fin d → Rˣ), (∀ r : R, IsIntegral (torusS K t Finset.univ) r) → Algebra.IsAlgebraic (Algebra.adjoin K (Set.range fun k => (t k : R))) R := by
  intro K R _ _ _ _ d t hint
  set A := Algebra.adjoin K (Set.range fun k => (t k : R)) with hA
  let S : Subalgebra A R := Subalgebra.algebraicClosure A R
  have hle : ∀ b : torusS K t Finset.univ, (b : R) ∈ S := by
    rintro ⟨b, hb⟩
    have : torusS K t Finset.univ ≤ S.restrictScalars K := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨m, -, rfl⟩
      exact (Subalgebra.mem_algebraicClosure A R).2 (isAlgebraic_tpow t m)
    exact this hb
  let φ : torusS K t Finset.univ →+* S :=
    { toFun := fun b => ⟨b, hle b⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  refine ⟨fun r => ?_⟩
  obtain ⟨p, hm, hp⟩ := hint r
  have hS : IsIntegral S r := by
    refine ⟨p.map φ, hm.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hp
  set_option synthInstance.maxHeartbeats 200000 in
    exact hS.isAlgebraic.restrictScalars A

end GlobalTheory.CompanionTheory.GeoTorus
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraicOverTorusOfIntegralStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
alias GlobalTheory.T.algebraic_over_torus_of_integral := GlobalTheory.CompanionTheory.GeoTorus.isAlgebraic_of_integral_torusS
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealNeTop
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealNeTop
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GeoNetop

attribute [local instance] MvPolynomial.gradedAlgebra

theorem irrelevant_le_spanX (K : Type) [Field K] (N : ℕ) :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K)) := by
  intro x hx
  have h0 := (HomogeneousIdeal.mem_irrelevant_iff _ _).1 hx
  rw [GradedRing.proj_apply] at h0
  have h1 : MvPolynomial.homogeneousComponent 0 x = 0 := by
    rw [← MvPolynomial.decomposition.decompose'_apply]
    exact h0
  rw [MvPolynomial.homogeneousComponent_zero, MvPolynomial.C_eq_zero] at h1
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (MvPolynomial.mem_support_iff.1 hm) h1
  obtain ⟨a, ha⟩ := Finsupp.ne_iff.1 hm0
  exact ⟨a, Set.mem_univ _, ha⟩

theorem exists_chart {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) (x : X) :
    ∃ j : Fin (N + 1), x ∈ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) := by
  have h := Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) MvPolynomial.X
    (irrelevant_le_spanX K N)
  have hx : i x ∈ ⨆ j, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X j) := by
    rw [h]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨j, hj⟩

theorem mk_C_mul_inv {K : Type} [Field K] {N : ℕ} (j : Fin (N + 1)) (c : K) (hc : c ≠ 0)
    (ha : MvPolynomial.C c ∈ grK K N (0 • 1)) (hb : MvPolynomial.C c⁻¹ ∈ grK K N (0 • 1)) :
    HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) 0 (MvPolynomial.C c) ha *
      HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) 0 (MvPolynomial.C c⁻¹) hb = 1 := by
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.val_mk, Localization.mk_mul, ← map_mul, mul_inv_cancel₀ hc]

theorem constantCoeff_gen {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) (hX : Nonempty X)
    {f : MvPolynomial (Fin (N + 1)) K} (d : ℕ) (hf : f ∈ grK K N (d • 1))
    (h0 : ∀ j : Fin (N + 1), evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf) = 0) :
    MvPolynomial.constantCoeff f = 0 := by
  have hc := MvPolynomial.homogeneousComponent_of_mem (m := 0) hf
  rw [MvPolynomial.homogeneousComponent_zero] at hc
  rw [MvPolynomial.constantCoeff_eq]
  by_cases hd : 0 = d • 1
  · rw [if_pos hd] at hc
    have hd0 : d = 0 := by simpa using hd.symm
    subst hd0
    obtain ⟨c, rfl⟩ : ∃ c, f = MvPolynomial.C c := ⟨_, hc.symm⟩
    rw [MvPolynomial.coeff_zero_C]
    by_contra hne
    obtain ⟨x⟩ := hX
    obtain ⟨j, hj⟩ := exists_chart i x
    haveI : Nonempty (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) := ⟨⟨x, hj⟩⟩
    haveI := Scheme.component_nontrivial X (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j))
    have hb : MvPolynomial.C c⁻¹ ∈ grK K N (0 • 1) := by
      simpa using MvPolynomial.isHomogeneous_C (Fin (N + 1)) c⁻¹
    have e := congrArg (evV i (MvPolynomial.X j) _ le_rfl) (mk_C_mul_inv j c hne hf hb)
    rw [map_mul, map_one, h0 j, zero_mul] at e
    exact zero_ne_one e
  · rw [if_neg hd, MvPolynomial.C_eq_zero] at hc
    exact hc

theorem homIdeal_ne_top : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N),
    Nonempty X → homIdeal i ≠ ⊤ := by
  intro K _ X N i hX htop
  have hle : homIdeal i ≤ RingHom.ker (MvPolynomial.constantCoeff (σ := Fin (N + 1)) (R := K)) := by
    refine Ideal.span_le.2 ?_
    rintro f ⟨d, hf, h0⟩
    exact (RingHom.mem_ker).2 (constantCoeff_gen i hX d hf h0)
  have h1 : (1 : MvPolynomial (Fin (N + 1)) K) ∈ RingHom.ker (MvPolynomial.constantCoeff (σ := Fin (N + 1)) (R := K)) :=
    hle (htop ▸ Submodule.mem_top)
  rw [RingHom.mem_ker, map_one] at h1
  exact one_ne_zero h1
end GlobalTheory.CompanionTheory.GeoNetop
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealNeTopStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
alias GlobalTheory.T.homogeneous_ideal_ne_top := GlobalTheory.CompanionTheory.GeoNetop.homIdeal_ne_top
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasiIsomorphismDegreeOneKernel
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasiIsomorphismDegreeOneKernel
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal

theorem lid_lTensor_apply {R X Y : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (f : X →ₗ[R] Y) (u : R ⊗[R] X) :
    TensorProduct.lid R Y (f.lTensor R u) = f (TensorProduct.lid R X u) := by
  induction u with
  | tmul a b => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem univ_coeff : ∀ (R A₀ A₁ A₂ P₀ P₁ P₂ : Type) [CommRing R] [AddCommGroup A₀] [Module R A₀] [AddCommGroup A₁] [Module R A₁] [AddCommGroup A₂] [Module R A₂] [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] (d₀ : A₀ →ₗ[R] A₁) (d₁ : A₁ →ₗ[R] A₂) (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] A₀) (ψ₁ : P₁ →ₗ[R] A₁) (ψ₂ : P₂ →ₗ[R] A₂) (r : P₂ →ₗ[R] P₁) (Z : Submodule R A₁) (dZ : A₀ →ₗ[R] Z), (∀ z, z ∈ Z ↔ d₁ z = 0) → (∀ y, (dZ y : A₁) = d₀ y) → a₁ ∘ₗ a₀ = 0 → ψ₁ ∘ₗ a₀ = d₀ ∘ₗ ψ₀ → ψ₂ ∘ₗ a₁ = d₁ ∘ₗ ψ₁ → a₁ ∘ₗ r ∘ₗ a₁ = a₁ → (∀ (M : Type) [AddCommGroup M] [Module R M], QIsoAt (a₀.lTensor M) (a₁.lTensor M) (d₀.lTensor M) (d₁.lTensor M) (ψ₁.lTensor M)) → ∀ (M : Type) [AddCommGroup M] [Module R M], (∀ x : M ⊗[R] A₁, d₁.lTensor M x = 0 → ∃ (t : M ⊗[R] Z) (y : M ⊗[R] A₀), Z.subtype.lTensor M t + d₀.lTensor M y = x) ∧ (∀ (t : M ⊗[R] Z) (y : M ⊗[R] A₀), Z.subtype.lTensor M t = d₀.lTensor M y → ∃ y' : M ⊗[R] A₀, dZ.lTensor M y' = t) := by
  intro R A₀ A₁ A₂ P₀ P₁ P₂ _ _ _ _ _ _ _ _ _ _ _ _ _ d₀ d₁ a₀ a₁ ψ₀ ψ₁ ψ₂ r Z dZ hZ hdZ haa hc₀ hc₁ hr hQ M _ _
  have hr' : ∀ p, a₁ (r (a₁ p)) = a₁ p := fun p => LinearMap.congr_fun hr p
  have haa' : ∀ p, a₁ (a₀ p) = 0 := fun p => LinearMap.congr_fun haa p
  have hc₀' : ∀ p, ψ₁ (a₀ p) = d₀ (ψ₀ p) := fun p => LinearMap.congr_fun hc₀ p
  have hc₁' : ∀ p, ψ₂ (a₁ p) = d₁ (ψ₁ p) := fun p => LinearMap.congr_fun hc₁ p
  let ε : P₁ →ₗ[R] LinearMap.ker a₁ := (LinearMap.id - r ∘ₗ a₁).codRestrict (LinearMap.ker a₁) (fun p => by
    simp [LinearMap.mem_ker, hr'])
  let ψZ : LinearMap.ker a₁ →ₗ[R] Z := (ψ₁ ∘ₗ (LinearMap.ker a₁).subtype).codRestrict Z (fun p => (hZ _).2 (by
    have hp : a₁ (p : P₁) = 0 := p.2
    simp [← hc₁', hp]))
  let a₀Z : P₀ →ₗ[R] LinearMap.ker a₁ := a₀.codRestrict (LinearMap.ker a₁) (fun p => haa' p)
  have hεs : (LinearMap.ker a₁).subtype ∘ₗ ε = LinearMap.id - r ∘ₗ a₁ := by
    ext p; rfl
  have hει : ε ∘ₗ (LinearMap.ker a₁).subtype = LinearMap.id := by
    ext p
    have hp : a₁ (p : P₁) = 0 := p.2
    simp [ε, hp]
  have hιψ : Z.subtype ∘ₗ ψZ = ψ₁ ∘ₗ (LinearMap.ker a₁).subtype := by
    ext p; rfl
  have hιd : Z.subtype ∘ₗ dZ = d₀ := by
    ext y; exact hdZ y
  have hεa : ε ∘ₗ a₀ = a₀Z := by
    ext p
    show a₀ p - r (a₁ (a₀ p)) = a₀ p
    rw [haa', map_zero, sub_zero]
  have hψa : ψZ ∘ₗ a₀Z = dZ ∘ₗ ψ₀ := by
    ext p
    show ψ₁ (a₀ p) = (dZ (ψ₀ p) : A₁)
    rw [hc₀', hdZ]
  have ha₁ι : a₁ ∘ₗ (LinearMap.ker a₁).subtype = 0 := by
    ext p; exact p.2
  refine ⟨fun x hx => ?_, fun t y h => ?_⟩
  · obtain ⟨w, y, hw, hy⟩ := (hQ M).2 x hx
    have hwε : (LinearMap.ker a₁).subtype.lTensor M (ε.lTensor M w) = w := by
      rw [← LinearMap.lTensor_comp_apply, hεs, LinearMap.lTensor_sub, LinearMap.sub_apply, LinearMap.lTensor_id,
        LinearMap.id_apply, LinearMap.lTensor_comp_apply, hw, map_zero, sub_zero]
    refine ⟨ψZ.lTensor M (ε.lTensor M w), -y, ?_⟩
    rw [← LinearMap.lTensor_comp_apply, hιψ, LinearMap.lTensor_comp_apply, hwε, map_neg, ← hy]
    abel
  · have hsurj : Function.Surjective (ψZ.coprod dZ) := by
      intro z
      obtain ⟨x, y, hx, hy⟩ := (hQ R).2 ((1 : R) ⊗ₜ (z : A₁)) (by simp [(hZ z).1 z.2])
      have e₁ : a₁ (TensorProduct.lid R P₁ x) = 0 := by
        rw [← lid_lTensor_apply, hx, map_zero]
      have e₂ : ψ₁ (TensorProduct.lid R P₁ x) - z = d₀ (TensorProduct.lid R A₀ y) := by
        have := congrArg (TensorProduct.lid R A₁) hy
        rw [map_sub, lid_lTensor_apply, TensorProduct.lid_tmul, one_smul, lid_lTensor_apply] at this
        exact this
      refine ⟨(⟨TensorProduct.lid R P₁ x, e₁⟩, -TensorProduct.lid R A₀ y), Subtype.ext ?_⟩
      have e₃ : ((ψZ ⟨TensorProduct.lid R P₁ x, e₁⟩ : Z) : A₁) = ψ₁ (TensorProduct.lid R P₁ x) := rfl
      simp only [LinearMap.coprod_apply, Submodule.coe_add, e₃, map_neg, Submodule.coe_neg, hdZ, ← e₂]
      abel
    obtain ⟨u, hu⟩ := LinearMap.lTensor_surjective M hsurj t
    have hcop : ψZ.coprod dZ = ψZ ∘ₗ LinearMap.fst R _ _ + dZ ∘ₗ LinearMap.snd R _ _ := by
      ext <;> simp
    obtain ⟨t₁, y₁, ht⟩ : ∃ (t₁ : M ⊗[R] LinearMap.ker a₁) (y₁ : M ⊗[R] A₀),
        t = ψZ.lTensor M t₁ + dZ.lTensor M y₁ := by
      refine ⟨(LinearMap.fst R _ _).lTensor M u, (LinearMap.snd R _ _).lTensor M u, ?_⟩
      rw [← hu, hcop, LinearMap.lTensor_add, LinearMap.add_apply, LinearMap.lTensor_comp_apply,
        LinearMap.lTensor_comp_apply]
    have h1 : Z.subtype.lTensor M (ψZ.lTensor M t₁) = ψ₁.lTensor M ((LinearMap.ker a₁).subtype.lTensor M t₁) := by
      rw [← LinearMap.lTensor_comp_apply, hιψ, LinearMap.lTensor_comp_apply]
    have h2 : Z.subtype.lTensor M (dZ.lTensor M y₁) = d₀.lTensor M y₁ := by
      rw [← LinearMap.lTensor_comp_apply, hιd]
    have hιP : d₀.lTensor M (y - y₁) = ψ₁.lTensor M ((LinearMap.ker a₁).subtype.lTensor M t₁) := by
      rw [map_sub, ← h, ht, map_add (f := _), h1, h2]
      abel
    obtain ⟨p, hp⟩ := (hQ M).1 ((LinearMap.ker a₁).subtype.lTensor M t₁) (by
      rw [← LinearMap.lTensor_comp_apply, ha₁ι, LinearMap.lTensor_zero, LinearMap.zero_apply]) ⟨_, hιP⟩
    have ht₁ : t₁ = a₀Z.lTensor M p := by
      rw [← hεa, LinearMap.lTensor_comp_apply, hp, ← LinearMap.lTensor_comp_apply, hει, LinearMap.lTensor_id,
        LinearMap.id_apply]
    refine ⟨ψ₀.lTensor M p + y₁, ?_⟩
    have h3 : dZ.lTensor M (ψ₀.lTensor M p) = ψZ.lTensor M t₁ := by
      rw [ht₁, ← LinearMap.lTensor_comp_apply, ← LinearMap.lTensor_comp_apply, hψa]
    rw [map_add (f := _), h3, ← ht]

end GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasiIsomorphismDegreeOneKernelStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
alias GlobalTheory.T.quasi_isomorphism_degree_one_kernel := GlobalTheory.CompanionTheory.PerfectFirstCohomologyUniversal.univ_coeff
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyBaseChangeOfCochainEquivs
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyBaseChangeOfCochainEquivs
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfectFirstCohomologyBaseChange

theorem h1_baseChange (R R' C : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (m : BC F F')
    (E₀ : R' ⊗[R] C0 F ≃ₗ[R'] C0 F') (E₁ : R' ⊗[R] C1 F ≃ₗ[R'] C1 F')
    (E₂ : R' ⊗[R] C2 F ≃ₗ[R'] C2 F')
    (hE₁ : ∀ c, E₁ (1 ⊗ₜ c) = fun T T' φ ↦ m.α T' (c T T' φ))
    (h01 : ∀ x, E₁ ((d0 F).baseChange R' x) = d0 F' (E₀ x))
    (h12 : ∀ x, E₂ ((d1 F).baseChange R' x) = d1 F' (E₁ x))
    (hex : ∀ x : R' ⊗[R] C1 F, (d1 F).lTensor R' x = 0 →
      ∃ (t : R' ⊗[R] Z1 F) (y : R' ⊗[R] C0 F),
        (Z1 F).subtype.lTensor R' t + (d0 F).lTensor R' y = x)
    (hinj : ∀ (t : R' ⊗[R] Z1 F) (y : R' ⊗[R] C0 F),
      (Z1 F).subtype.lTensor R' t = (d0 F).lTensor R' y →
        ∃ y' : R' ⊗[R] C0 F, ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)).lTensor R' y' = t) :
    ∃ e : R' ⊗[R] H1 F ≃ₗ[R'] H1 F', ∀ c, e (1 ⊗ₜ c) = m.coef.pull1 c := by
  letI : Module R (H1 F') := Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' (H1 F') := ⟨fun r s x ↦ by
    change (r • s) • x = algebraMap R R' r • s • x
    rw [Algebra.smul_def, mul_smul]⟩
  let p : H1 F →ₗ[R] H1 F' :=
    { toFun := m.coef.pull1
      map_add' := map_add _
      map_smul' := fun r c ↦ m.coef.pull1.map_smulₛₗ r c }
  let Φ : R' ⊗[R] H1 F →ₗ[R'] H1 F' := p.liftBaseChange R'
  have hΦ : ∀ (r : R') (c : H1 F), Φ (r ⊗ₜ c) = r • m.coef.pull1 c := fun r c ↦
    LinearMap.liftBaseChange_tmul _ _ _ _

  have key : ∀ t : R' ⊗[R] Z1 F, ∃ z' : Z1 F', z'.1 = E₁ ((Z1 F).subtype.lTensor R' t) ∧
      Φ ((H1.mk F).lTensor R' t) = H1.mk F' z' := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul r z =>
      refine ⟨r • m.coef.pullbackOneCocycle z, ?_, ?_⟩
      · have : (r ⊗ₜ[R] z.1 : R' ⊗[R] C1 F) = r • (1 ⊗ₜ[R] z.1) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]
        rw [this, map_smul, hE₁]
        rfl
      · simp only [LinearMap.lTensor_tmul, hΦ, map_smul]
        rfl
    | add a b ha hb =>
      obtain ⟨za, ha1, ha2⟩ := ha
      obtain ⟨zb, hb1, hb2⟩ := hb
      refine ⟨za + zb, ?_, ?_⟩
      · simp only [map_add (f := _), Submodule.coe_add, ha1, hb1]
      · simp only [map_add (f := _), ha2, hb2]
  have bc : ∀ x, (d0 F).lTensor R' x = (d0 F).baseChange R' x := fun x ↦ by
    rw [LinearMap.baseChange_eq_ltensor]
  have hsurj : Function.Surjective Φ := by
    intro c'
    obtain ⟨z', rfl⟩ := H1.mk_surjective F' c'
    have hx : (d1 F).lTensor R' (E₁.symm z'.1) = 0 := by
      rw [← LinearMap.baseChange_eq_ltensor]
      apply E₂.injective
      rw [h12, LinearEquiv.apply_symm_apply, map_zero]
      have hz : z'.1 ∈ LinearMap.ker (d1 F') := by
        rw [← commAlgFunctorCocyclesOne_eq_ker]
        exact z'.2
      exact hz
    obtain ⟨t, y, hty⟩ := hex _ hx
    obtain ⟨z'', h1, h2⟩ := key t
    refine ⟨(H1.mk F).lTensor R' t, ?_⟩
    rw [h2, H1.mk_eq_mk]
    refine ⟨-E₀ y, ?_⟩
    have e := congrArg E₁ hty
    rw [LinearEquiv.apply_symm_apply, map_add (f := _), bc, h01, ← h1] at e
    rw [← e, map_neg]
    abel
  have hinjΦ : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨t, rfl⟩ := LinearMap.lTensor_surjective R' (H1.mk_surjective F) w
    obtain ⟨z'', h1, h2⟩ := key t
    rw [h2, H1.mk_eq_zero] at hw
    obtain ⟨g, hg⟩ := hw
    have e : (Z1 F).subtype.lTensor R' t = (d0 F).lTensor R' (E₀.symm g) := by
      apply E₁.injective
      rw [bc, h01, LinearEquiv.apply_symm_apply, hg, h1]
    obtain ⟨y', rfl⟩ := hinj t _ e
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have : (H1.mk F).comp ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)) = 0 := by
      ext1 g
      exact H1.mk_eq_zero.2 ⟨g, rfl⟩
    rw [this]
    simp
  refine ⟨LinearEquiv.ofBijective Φ ⟨hinjΦ, hsurj⟩, fun c ↦ ?_⟩
  exact (hΦ 1 c).trans (one_smul R' _)

end GlobalTheory.CompanionTheory.PerfectFirstCohomologyBaseChange
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyBaseChangeOfCochainEquivsStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
alias GlobalTheory.T.first_cohomology_base_change_of_cochain_equivs := GlobalTheory.CompanionTheory.PerfectFirstCohomologyBaseChange.h1_baseChange
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedStOfTwoFormCohSt
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.HodgeClosed

section Algebra

variable {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem pairing_map (v : Fin 2 → Module.Dual R N) (g : M →ₗ[R] N) (t : ⋀[R]^2 M) :
    exteriorPower.pairingDual R N 2 (exteriorPower.ιMulti R 2 v) (exteriorPower.map 2 g t) =
      exteriorPower.pairingDual R M 2 (exteriorPower.ιMulti R 2 fun i ↦ v i ∘ₗ g) t := by
  have e : exteriorPower.pairingDual R N 2 (exteriorPower.ιMulti R 2 v) ∘ₗ exteriorPower.map 2 g =
      exteriorPower.pairingDual R M 2 (exteriorPower.ιMulti R 2 fun i ↦ v i ∘ₗ g) := by
    apply exteriorPower.linearMap_ext
    ext x
    simp [exteriorPower.pairingDual_ιMulti_ιMulti]
  exact LinearMap.congr_fun e t

theorem eq_zero_of_pairing [Module.Finite R M] [Module.Projective R M] (t : ⋀[R]^2 M)
    (h : ∀ v : Fin 2 → Module.Dual R M, exteriorPower.pairingDual R M 2 (exteriorPower.ιMulti R 2 v) t = 0) :
    t = 0 := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hu : exteriorPower.map 2 g t = 0 := by
    let b := Pi.basisFun R (Fin n)
    refine (b.exteriorPower 2).repr.injective (Finsupp.ext fun s ↦ ?_)
    rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual, exteriorPower.ιMulti_family]
    simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
    exact (pairing_map _ g t).trans (h _)
  exact exteriorPower.map_injective f hfg (hu.trans (map_zero _).symm)

theorem eq_zero_of_additive [Module.Finite R M] [Module.Projective R M] (A B : M →ₗ[R] N)
    (hb : Function.Bijective fun x : M × M ↦ A x.1 + B x.2) (t : ⋀[R]^2 M)
    (h : exteriorPower.map 2 (A + B) t = exteriorPower.map 2 A t + exteriorPower.map 2 B t) : t = 0 := by
  let e : (M × M) ≃ₗ[R] N := LinearEquiv.ofBijective (A.coprod B) ((funext fun x ↦ LinearMap.coprod_apply A B x : ⇑(A.coprod B) = _) ▸ hb)
  have eA : ∀ x, e.symm (A x) = (x, 0) := fun x ↦ e.symm_apply_eq.2 (by simp [e])
  have eB : ∀ x, e.symm (B x) = (0, x) := fun x ↦ e.symm_apply_eq.2 (by simp [e])
  refine eq_zero_of_pairing t fun v ↦ ?_
  let L : Module.Dual R N := v 0 ∘ₗ LinearMap.fst R M M ∘ₗ e.symm.toLinearMap
  let L' : Module.Dual R N := v 1 ∘ₗ LinearMap.snd R M M ∘ₗ e.symm.toLinearMap
  have key := congrArg (exteriorPower.pairingDual R N 2 (exteriorPower.ιMulti R 2 ![L, L'])) h
  rw [map_add (f := _), pairing_map, pairing_map, pairing_map] at key
  have h0 : (fun i ↦ ![L, L'] i ∘ₗ (A + B)) = v := by
    funext i
    fin_cases i
    · ext x; simp [L, eA, eB]
    · ext x; simp [L', eA, eB]
  have hA : (fun i ↦ ![L, L'] i ∘ₗ A) 1 = 0 := by ext x; simp [L', eA]
  have hB : (fun i ↦ ![L, L'] i ∘ₗ B) 0 = 0 := by ext x; simp [L, eB]
  rw [h0, (exteriorPower.ιMulti R 2).map_coord_zero (m := fun i ↦ ![L, L'] i ∘ₗ A) 1 hA,
    (exteriorPower.ιMulti R 2).map_coord_zero (m := fun i ↦ ![L, L'] i ∘ₗ B) 0 hB] at key
  simpa using key

end Algebra

section Forms

variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}

theorem nu_natural (c : CoefMap (RingHom.id R) F G) (ν : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (ν' : ⋀[R]^2 (Glob1 G) →ₗ[R] W0 G 2)
    (hν : ∀ a b T, ν (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hν' : ∀ a b T, ν' (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (t : ⋀[R]^2 (Glob1 F)) (T : D) :
    qOm c 2 T (ν t (c.G.obj T)) = ν' (exteriorPower.map 2 (pullGlob1 c) t) T := by
  have e : (qOm c 2 T : _ →ₗ[R] _) ∘ₗ LinearMap.proj (c.G.obj T) ∘ₗ ν =
      LinearMap.proj T ∘ₗ ν' ∘ₗ exteriorPower.map 2 (pullGlob1 c) := by
    apply exteriorPower.linearMap_ext
    ext x
    obtain ⟨a, b, rfl⟩ : ∃ a b, x = ![a, b] := ⟨x 0, x 1, by funext i; fin_cases i <;> rfl⟩
    have hy : (pullGlob1 c : Glob1 F →ₗ[R] Glob1 G) ∘ ![a, b] = ![pullGlob1 c a, pullGlob1 c b] := by
      funext i; fin_cases i <;> rfl
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      exteriorPower.map_apply_ιMulti]
    rw [hy, hν, hν']
    exact congrArg Subtype.val (qOm_wedge c (a.1 (c.G.obj T)) (b.1 (c.G.obj T)))
  exact LinearMap.congr_fun e t

end Forms

theorem closedSt_of_twoFormCohSt : TwoFormCohSt → ClosedSt := by
  intro h2 R _ C _ F hF hBi
  obtain ⟨D, _, G, m, p, q, hS, hP, -, hb, -, hm, -⟩ := hBi
  have hG : Framed G := by
    obtain ⟨-, -, h1, h3⟩ := hF
    let e : (Glob1 F × Glob1 F) ≃ₗ[R] Glob1 G := LinearEquiv.ofBijective ((pullGlob1 p).coprod (pullGlob1 q))
      ((funext fun x ↦ LinearMap.coprod_apply (pullGlob1 p) (pullGlob1 q) x :
        ⇑((pullGlob1 p).coprod (pullGlob1 q)) = _) ▸ hb)
    exact ⟨hS, hP, Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  obtain ⟨ν, hν, -, hsurj⟩ := h2 R C F hF
  obtain ⟨ν', hν', hinj, -⟩ := h2 R D G hG
  obtain ⟨-, -, hfin, hproj⟩ := hF
  refine eq_top_iff.2 fun ω₀ _ T ↦ ?_
  obtain ⟨t, ht⟩ := hsurj (fun T ↦ dOne R _ (ω₀.1 T)) fun T T' φ ↦ by
    rw [pOm_dOne, ω₀.2 φ]
  have step : ∀ (c : CoefMap (RingHom.id R) F G),
      ν' (exteriorPower.map 2 (pullGlob1 c) t) = fun T ↦ dOne R _ ((pullGlob1 c ω₀).1 T) := by
    intro c
    funext T
    rw [← nu_natural c ν ν' hν hν' t T, ht]
    exact qOm_dOne c (ω₀.1 (c.G.obj T))
  have hadd : exteriorPower.map 2 (pullGlob1 p + pullGlob1 q) t =
      exteriorPower.map 2 (pullGlob1 p) t + exteriorPower.map 2 (pullGlob1 q) t := by
    have h1 : pullGlob1 p + pullGlob1 q = pullGlob1 m := LinearMap.ext fun ω ↦ (hm ω).symm
    apply hinj
    rw [h1, step m, map_add (f := _), step p, step q]
    funext T'
    change dOne R _ ((pullGlob1 m ω₀).1 T') = dOne R _ ((pullGlob1 p ω₀).1 T') + dOne R _ ((pullGlob1 q ω₀).1 T')
    rw [hm, ← map_add (f := _)]
    rfl
  have ht0 : t = 0 := eq_zero_of_additive _ _ hb t hadd
  have := congrFun ht T
  rw [ht0, map_zero] at this
  exact this.symm

end GlobalTheory.CompanionTheory.HodgeClosed
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpensCoverOfFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpensCoverOfFinite
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoCover

theorem X_mem_of_finite {K : Type} [Field K] {n m : ℕ}
    (I P : Ideal (MvPolynomial (Fin n) K)) [hPp : P.IsPrime] (hIP : I ≤ P)
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) K))
    (y : Fin m → MvPolynomial (Fin n) K) (hy : ∀ k, y k ∈ P)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial (Fin n) K ⧸ I))
    (j : Fin n) : (MvPolynomial.X j : MvPolynomial (Fin n) K) ∈ P := by
  classical
  by_contra hj
  let φ : (MvPolynomial (Fin n) K ⧸ I) →+* (MvPolynomial (Fin n) K ⧸ P) := Ideal.Quotient.factor hIP
  have hφ : ∀ g, φ (Ideal.Quotient.mk I g) = Ideal.Quotient.mk P g := fun g => rfl
  let Q : Ideal (MvPolynomial (Fin n) K ⧸ I) := RingHom.ker φ
  haveI : Q.IsPrime := RingHom.ker_isPrime φ
  haveI : Algebra.IsIntegral (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial (Fin n) K ⧸ I) := Algebra.IsIntegral.of_finite _ _
  have hc0 : ∀ r ∈ Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)),
      ∃ c : K, φ r = Ideal.Quotient.mk P (MvPolynomial.C c) := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact ⟨0, by rw [hφ, map_zero, map_zero]; exact Ideal.Quotient.eq_zero_iff_mem.2 (hy k)⟩
    | algebraMap c => exact ⟨c, rfl⟩
    | add a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := hb
      exact ⟨c + d, by rw [φ.map_add, hc, hd, (MvPolynomial.C : K →+* MvPolynomial (Fin n) K).map_add, (Ideal.Quotient.mk P).map_add]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨c, hc⟩ := ha
      obtain ⟨d, hd⟩ := hb
      exact ⟨c * d, by rw [map_mul, hc, hd, map_mul, map_mul]⟩
  have h1 : (1 : MvPolynomial (Fin n) K ⧸ P) ≠ 0 := by
    intro h
    have : (1 : MvPolynomial (Fin n) K) ∈ P := Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_one]; exact h)
    exact hPp.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hmax : (Q.comap (algebraMap (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial (Fin n) K ⧸ I))).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨fun h => h1 ?_, fun J x hle hx hxJ => ?_⟩
    · have : φ 1 = 0 := by simpa [Q, RingHom.mem_ker, Ideal.mem_comap] using h
      simpa using this
    · obtain ⟨c, hc⟩ := hc0 x.1 x.2
      have hc' : c ≠ 0 := by
        rintro rfl
        apply hx
        rw [Ideal.mem_comap]
        change φ x.1 = 0
        rw [hc, map_zero, map_zero]
      have hm : x * algebraMap K _ c⁻¹ - 1 ∈ J := by
        apply hle
        rw [Ideal.mem_comap]
        change φ (x.1 * algebraMap K _ c⁻¹ - 1) = 0
        rw [φ.map_sub, φ.map_mul, hc, φ.map_one]
        change _ * Ideal.Quotient.mk P (MvPolynomial.C c⁻¹) - 1 = 0
        rw [← map_mul (Ideal.Quotient.mk P), ← map_mul MvPolynomial.C, mul_inv_cancel₀ hc', map_one, map_one, sub_self]
      have := J.sub_mem (J.mul_mem_right (algebraMap K _ c⁻¹) hxJ) hm
      simpa using this
  have hQ : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under
    (R := Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k))) Q hmax
  have hjQ : Ideal.Quotient.mk I (MvPolynomial.X j) ∉ Q := fun h =>
    hj (Ideal.Quotient.eq_zero_iff_mem.1 ((hφ _).symm.trans (RingHom.mem_ker.1 h)))
  obtain ⟨a, b, hb, hab⟩ := hQ.exists_inv hjQ
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h2 : Ideal.Quotient.mk P (g * MvPolynomial.X j - 1) = 0 := by
    have := congrArg φ hab
    rw [φ.map_add, φ.map_mul, hφ, hφ, show φ b = 0 from hb, add_zero, map_one] at this
    rw [(Ideal.Quotient.mk P).map_sub, (Ideal.Quotient.mk P).map_mul, this, (Ideal.Quotient.mk P).map_one, sub_self]
  have h3 : MvPolynomial.homogeneousComponent 0 (g * MvPolynomial.X j - 1) ∈ P := by
    rw [← MvPolynomial.decomposition.decompose'_apply]
    exact hP 0 (Ideal.Quotient.eq_zero_iff_mem.1 h2)
  have h4 : AddMonoidAlgebra.coeff (g * MvPolynomial.X j - 1) 0 = -1 := by
    have : MvPolynomial.constantCoeff (g * MvPolynomial.X j - 1) = -1 := by simp only [(MvPolynomial.constantCoeff : MvPolynomial (Fin n) K →+* K).map_sub, (MvPolynomial.constantCoeff : MvPolynomial (Fin n) K →+* K).map_mul, MvPolynomial.constantCoeff_X, mul_zero, (MvPolynomial.constantCoeff : MvPolynomial (Fin n) K →+* K).map_one, zero_sub]
    rwa [MvPolynomial.constantCoeff_eq] at this
  rw [MvPolynomial.homogeneousComponent_zero, h4, (MvPolynomial.C : K →+* MvPolynomial (Fin n) K).map_neg, (MvPolynomial.C : K →+* MvPolynomial (Fin n) K).map_one] at h3
  exact hPp.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using P.neg_mem h3))

theorem mem_of_evV_eq_zero {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) (p : X)
    (j : Fin (N + 1)) (hj : i p ∈ Proj.basicOpen (grK K N) (MvPolynomial.X j))
    {d : ℕ} {f : MvPolynomial (Fin (N + 1)) K} (hf : f ∈ grK K N (d • 1))
    (h : evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf) = 0) :
    f ∈ (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal := by
  by_contra hfP
  have hf' : f * MvPolynomial.X j ∈ grK K N (d + 1) := by
    have := SetLike.mul_mem_graded hf (xv_mem K N j)
    simpa using this
  have e : HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf =
      HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hf' := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.Away.val_mk]
    exact Localization.mk_eq_mk_iff.2 (Localization.r_of_eq (by
      change MvPolynomial.X j ^ (d + 1) * f = MvPolynomial.X j ^ d * (f * MvPolynomial.X j)
      ring))
  have hb := GroundTheory.Arith.SchemeCoh.ProjHom.basicOpen_awayToSection_isLocalizationElem (grK K N)
    (xv_mem K N j) one_pos hf' (Nat.succ_pos d)
  have hx : i p ∈ (PSpace K N).basicOpen (Proj.awayToSection (grK K N) (MvPolynomial.X j)
      (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hf')) := by
    erw [hb]
    refine ⟨hj, fun hm => ?_⟩
    exact ((i p : ProjectiveSpectrum (grK K N)).isPrime.mem_or_mem hm).elim hfP hj
  have hp : p ∈ i ⁻¹ᵁ (PSpace K N).basicOpen (Proj.awayToSection (grK K N) (MvPolynomial.X j)
      (HomogeneousLocalization.Away.isLocalizationElem (xv_mem K N j) hf')) := hx
  rw [Scheme.preimage_basicOpen, ← e] at hp
  have h0 : i.app _ (Proj.awayToSection (grK K N) (MvPolynomial.X j)
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf)) = 0 := by
    rw [Scheme.Hom.app_eq_appLE]
    exact h
  rw [h0, Scheme.basicOpen_zero] at hp
  exact hp

theorem iSup_preimage_eq_top : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ {m e : ℕ}, 0 < e → ∀ (y : Fin m → MvPolynomial (Fin (N + 1)) K), (∀ k, (y k).IsHomogeneous e) → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk (homIdeal i) (y k))) (MvPolynomial (Fin (N + 1)) K ⧸ homIdeal i) → ⨆ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) = ⊤ := by
  intro K _ X N i m e _ y _ hfin
  rw [_root_.eq_top_iff]
  intro p _
  by_contra hcon
  obtain ⟨j, hj⟩ : ∃ j, i p ∈ Proj.basicOpen (grK K N) (MvPolynomial.X j) := by
    have : i p ∈ (⨆ j : Fin (N + 1), Proj.basicOpen (grK K N) (MvPolynomial.X j)) := by
      erw [GroundTheory.Arith.SchemeCoh.ProjSpace.iSup_basicOpen_X]
      trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  have hy : ∀ k, y k ∈ (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal := by
    intro k
    by_contra hk
    apply hcon
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨k, hk⟩
  have hle : homIdeal i ≤ (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal := by
    rw [homIdeal, Ideal.span_le]
    rintro f ⟨d, hf, hv⟩
    exact mem_of_evV_eq_zero i p j hj hf (hv j)
  haveI : (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).toIdeal.IsPrime :=
    (i p : ProjectiveSpectrum (grK K N)).isPrime
  exact hj (X_mem_of_finite _ _ hle
    (ProjectiveSpectrum.asHomogeneousIdeal (i p : ProjectiveSpectrum (grK K N))).isHomogeneous y hy hfin j)

end GlobalTheory.CompanionTheory.GeoCover
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasicOpensCoverOfFiniteStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
alias GlobalTheory.T.basic_opens_cover_of_finite := GlobalTheory.CompanionTheory.GeoCover.iSup_preimage_eq_top
end
end
