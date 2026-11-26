module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.OElRep

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.KerTest
open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.kerTest :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] {X : Type} (K : X → Type) [∀ x, CommRing (K x)] (f : ∀ x, A →+* K x)
    (ρ : ∀ x, G →* Matrix (Fin n) (Fin n) (K x)) (D : GDet n A G),
    (∀ a, (∀ x, f x a = 0) → a = 0) → (∀ x, D.map (f x) = GDet.ofRep (ρ x)) →
    ∀ y : MonoidAlgebra A G, (∀ x, GDet.repAlg (ρ x) (K x) (MonoidAlgebra.mapRingHom G (f x) y) = 0) → D.Kills y := by
  intro n A G _ _ X K _ f ρ D hf hD y hy
  refine (UpperTheory.V.AlgebraTools.Det.injTest K f hf).2 D y fun x => ?_
  rw [hD x]
  exact (UpperTheory.V.AlgebraTools.Det.repApi (ρ x)).2.2.2.2.1 _ (hy x)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.PolarInj
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

private theorem star_mapRingHom_eq_mapRingHom_star {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (B B' : Type) [CommRing B] [CommRing B'] [Algebra O B] [Algebra O B'] (n : ℕ) (φ : B →+* B') (hφ : φ.comp (algebraMap O B) = algebraMap O B') (y : MonoidAlgebra B F.G₀) :
    F.star O B' n (MonoidAlgebra.mapRingHom F.G₀ φ y) = MonoidAlgebra.mapRingHom F.G₀ φ (F.star O B n y) := by
  have h1 : ∀ (u : Bˣ) (k : ℤ), φ ((u ^ k : Bˣ) : B) = ((Units.map (φ : B →* B') u ^ k : B'ˣ) : B') := by
    intro u k
    rw [← map_zpow]
    rfl
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp [GFrame.star]
  | add a b ha hb =>
    simp only [map_add (f := _), GFrame.star, MulOpposite.unop_add] at *
    rw [ha, hb]
  | single g b =>
    simp only [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, GFrame.eps, MonoidAlgebra.mapRingHom_single]
    simp
    rw [h1]
    congr 3
    ext
    simp [← hφ]

theorem UpperTheory.V.AlgebraTools.Det.polarInj :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (D : GDet n R F.G₀) {X : Type} (K : X → Type) [∀ x, CommRing (K x)] [∀ x, Algebra O (K x)] (f : ∀ x, R →ₐ[O] K x),
    (∀ a, (∀ x, f x a = 0) → a = 0) → (∀ x, F.IsPolar O (D.map (f x : R →+* K x))) → F.IsPolar O D := by
  intro l _ F O _ _ R _ _ n D X K _ _ f hf h
  intro B _ _ _ _ y
  classical
  let u : MonoidAlgebra (MvPolynomial F.G₀ R) F.G₀ := y.coeff.support.sum fun g => MonoidAlgebra.single g (MvPolynomial.X g)
  let ev : MvPolynomial F.G₀ R →ₐ[R] B := MvPolynomial.aeval fun g => y.coeff g
  have hev : MonoidAlgebra.mapRingHom F.G₀ (ev : MvPolynomial F.G₀ R →+* B) u = y := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [u, map_sum, MonoidAlgebra.mapRingHom_single]
    simp only [ev, AlgHom.coe_toRingHom, MvPolynomial.aeval_X]
    exact y.sum_single
  have hevO : (ev : MvPolynomial F.G₀ R →+* B).comp (algebraMap O (MvPolynomial F.G₀ R)) = algebraMap O B := by
    ext o
    simp [ev, MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply O R B]
  have key : D.D _ (F.star O _ n u) = D.D _ u := by
    rw [← sub_eq_zero]
    ext m
    rw [MvPolynomial.coeff_zero]
    apply hf
    intro x
    letI : Algebra R (MvPolynomial F.G₀ (K x)) := ((algebraMap (K x) (MvPolynomial F.G₀ (K x))).comp (f x : R →+* K x)).toAlgebra
    let φ : MvPolynomial F.G₀ R →ₐ[R] MvPolynomial F.G₀ (K x) := MvPolynomial.aeval MvPolynomial.X
    have hφ : (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) = MvPolynomial.map (f x : R →+* K x) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [φ, RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]
      · intro i
        simp [φ]
    have hφO : (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)).comp (algebraMap O (MvPolynomial F.G₀ R)) = algebraMap O (MvPolynomial F.G₀ (K x)) := by
      rw [hφ]
      refine RingHom.ext fun o => ?_
      rw [RingHom.comp_apply, MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_apply, MvPolynomial.map_C]
      congr 1
      exact (f x).commutes o
    have hz : MvPolynomial.map (f x : R →+* K x) (D.D _ (F.star O _ n u) - D.D _ u) = 0 := by
      rw [← hφ, map_sub, sub_eq_zero]
      have hx := h x (MvPolynomial F.G₀ (K x)) (MonoidAlgebra.mapRingHom F.G₀ (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) u)
      rw [star_mapRingHom_eq_mapRingHom_star F O _ _ n _ hφO] at hx
      change D.D _ (MonoidAlgebra.mapRingHom F.G₀ (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) (F.star O _ n u)) = D.D _ (MonoidAlgebra.mapRingHom F.G₀ (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) u) at hx
      rw [D.nat _ _ φ, D.nat _ _ φ] at hx
      exact hx
    have hc := congrArg (AddMonoidAlgebra.coeff · m) hz
    rw [MvPolynomial.coeff_map] at hc
    simpa using hc
  rw [← hev, star_mapRingHom_eq_mapRingHom_star F O _ _ n _ hevO, D.nat _ _ ev, D.nat _ _ ev, key]
end
