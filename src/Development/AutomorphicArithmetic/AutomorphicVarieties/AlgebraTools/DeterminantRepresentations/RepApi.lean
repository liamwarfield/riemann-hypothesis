module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbitt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
open Polynomial UpperTheory.V.W

namespace UpperTheory.V.AlgebraTools.Det

section
variable {n : ℕ} {A G : Type} [CommRing A] [Group G]

private theorem repAlg_single (ρ : G →* Matrix (Fin n) (Fin n) A) (B : Type) [CommRing B] [Algebra A B]
    (g : G) (r : B) : GDet.repAlg ρ B (MonoidAlgebra.single g r) = r • (ρ g).map (algebraMap A B) := by
  unfold GDet.repAlg
  rw [MonoidAlgebra.lift_single]
  rfl

private theorem repAlg_map (ρ : G →* Matrix (Fin n) (Fin n) A) (B : Type) [CommRing B] [Algebra A B]
    (y : MonoidAlgebra A G) :
    GDet.repAlg ρ B (MonoidAlgebra.mapRingHom G (algebraMap A B) y) = (GDet.repAlg ρ A y).map (algebraMap A B) := by
  induction y using MonoidAlgebra.induction_on with
  | of g =>
    simp [MonoidAlgebra.of_apply, repAlg_single]
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
    ext i j
    simp
  | smul r x hx =>
    have hr : r • x = MonoidAlgebra.single 1 r * x := by
      rw [Algebra.smul_def]
      rfl
    have hm : MonoidAlgebra.mapRingHom G (algebraMap A B) (MonoidAlgebra.single 1 r)
        = MonoidAlgebra.single 1 (algebraMap A B r) := by
      ext g
      simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [hr, map_mul, map_mul, map_mul, hx, Matrix.map_mul, hm, repAlg_single, repAlg_single, map_one]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]

private theorem ofRep_D (ρ : G →* Matrix (Fin n) (Fin n) A) (B : Type) [CommRing B] [Algebra A B]
    (x : MonoidAlgebra B G) : (GDet.ofRep ρ).D B x = (GDet.repAlg ρ B x).det := rfl

private theorem chi_eq (ρ : G →* Matrix (Fin n) (Fin n) A) (y : MonoidAlgebra A G) :
    (GDet.ofRep ρ).chi y = (GDet.repAlg ρ A y).charpoly := by
  unfold GDet.chi
  rw [ofRep_D, ← Polynomial.algebraMap_eq, map_sub, repAlg_single, repAlg_map, map_one]
  rw [Matrix.charpoly]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [Matrix.charmatrix_apply, Matrix.one_apply, h]

private theorem chi_single (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  rw [chi_eq, repAlg_single]; simp

end

end UpperTheory.V.AlgebraTools.Det

theorem UpperTheory.V.AlgebraTools.Det.repApi :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A),
    (∀ y, (GDet.ofRep ρ).chi y = (GDet.repAlg ρ A y).charpoly) ∧
    (∀ g, (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly) ∧
    (0 < n → ∀ y, (GDet.ofRep ρ).tr y = (GDet.repAlg ρ A y).trace) ∧
    (∀ g, (GDet.ofRep ρ).lam n (MonoidAlgebra.single g 1) = (ρ g).det) ∧
    (∀ y, GDet.repAlg ρ A y = 0 → (GDet.ofRep ρ).Kills y) ∧
    (∀ {A' : Type} [CommRing A'] (f : A →+* A'), (GDet.ofRep ρ).map f = GDet.ofRep ((RingHom.mapMatrix f).toMonoidHom.comp ρ)) ∧
    (∀ {H : Type} [Group H] (φ : H →* G), (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ)) ∧
    (∀ (ρ' : G →* Matrix (Fin n) (Fin n) A) (P : GL (Fin n) A), (∀ g, (P : Matrix (Fin n) (Fin n) A) * ρ' g = ρ g * P) → GDet.ofRep ρ' = GDet.ofRep ρ) := by
  intro n A G _ _ ρ
  refine ⟨chi_eq ρ, chi_single ρ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hn y
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    unfold GDet.tr GDet.lam
    rw [chi_eq, Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
    ring
  · intro g
    unfold GDet.lam
    rw [chi_single, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, Nat.sub_self]
  · intro y hy
    unfold GDet.Kills
    intro B _ _ h
    rw [ofRep_D, map_add (f := _), map_mul, repAlg_map, hy, Matrix.map_zero _ (map_zero _), mul_zero, add_zero, map_one,
      Matrix.det_one]
  · intro A' _ f
    refine GDet.ext fun B _ _ x => ?_
    unfold GDet.map
    dsimp only
    rw [ofRep_D, ofRep_D]
    congr 2
  · intro H _ φ
    refine GDet.ext fun B _ _ x => ?_
    unfold GDet.comap
    dsimp only
    rw [MonoidHom.comp_apply, ofRep_D, ofRep_D]
    congr 1
    show GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ x) = GDet.repAlg (ρ.comp φ) B x
    induction x using MonoidAlgebra.induction_on with
    | of h =>
      simp [MonoidAlgebra.of_apply, repAlg_single, MonoidAlgebra.mapDomainRingHom]
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
    | smul r x hx =>
      have hr : r • x = MonoidAlgebra.single 1 r * x := by
        rw [Algebra.smul_def]
        rfl
      rw [hr, map_mul, map_mul, map_mul, hx]
      congr 1
      simp [repAlg_single, MonoidAlgebra.mapDomainRingHom]
  · intro ρ' P hP
    refine GDet.ext fun B _ _ x => ?_
    have key : ∀ y : MonoidAlgebra B G,
        (P : Matrix (Fin n) (Fin n) A).map (algebraMap A B) * GDet.repAlg ρ' B y
          = GDet.repAlg ρ B y * (P : Matrix (Fin n) (Fin n) A).map (algebraMap A B) := by
      intro y
      induction y using MonoidAlgebra.induction_on with
      | of g =>
        rw [MonoidAlgebra.of_apply, repAlg_single, repAlg_single, one_smul, one_smul,
          ← Matrix.map_mul, ← Matrix.map_mul, hP]
      | add y z hy hz =>
        rw [map_add (f := _), map_add (f := _), Matrix.mul_add, Matrix.add_mul, hy, hz]
      | smul r y hy =>
        rw [map_smul, map_smul, Matrix.mul_smul, Matrix.smul_mul, hy]
    have hd := congrArg Matrix.det (key x)
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det (GDet.repAlg ρ B x))] at hd
    have hu : IsUnit (Matrix.det ((P : Matrix (Fin n) (Fin n) A).map (algebraMap A B))) := by
      rw [show ((P : Matrix (Fin n) (Fin n) A).map (algebraMap A B)).det
          = algebraMap A B (P : Matrix (Fin n) (Fin n) A).det from (RingHom.map_det _ _).symm]
      exact (Matrix.isUnits_det_units P).map _
    rw [ofRep_D, ofRep_D]
    exact hu.mul_left_cancel hd
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
open Polynomial UpperTheory.V.W

private theorem UpperTheory.V.AlgebraTools.Det.map_D_mapRingHom_eq {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
    {A' : Type} [CommRing A'] (f : A →+* A') (B₀ : Type) [CommRing B₀] [Algebra A B₀]
    (B : Type) [CommRing B] [Algebra A' B] (φ : B₀ →+* B)
    (hφ : ∀ a, φ (algebraMap A B₀ a) = algebraMap A' B (f a)) (x : MonoidAlgebra B₀ G) :
    (D.map f).D B (MonoidAlgebra.mapRingHom G φ x) = φ (D.D B₀ x) := by
  let : Algebra A B := ((algebraMap A' B).comp f).toAlgebra
  exact D.nat B₀ B { φ with commutes' := hφ } x

theorem UpperTheory.V.AlgebraTools.Det.mapApi :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) {A' : Type} [CommRing A'] (f : A →+* A'),
    (∀ y, (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f) ∧
    (∀ i y, (D.map f).lam i (MonoidAlgebra.mapRingHom G f y) = f (D.lam i y)) ∧
    (∀ i g, (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1))) ∧
    (∀ (σ : Type) (x : MonoidAlgebra (MvPolynomial σ A) G), (D.map f).D (MvPolynomial σ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map f) x) =
      MvPolynomial.map f (D.D (MvPolynomial σ A) x)) ∧
    (∀ (m : ℕ) (y : Fin m → MonoidAlgebra A G), (D.map f).D (MvPolynomial (Fin m) A') (GDet.gen fun j => MonoidAlgebra.mapRingHom G f (y j)) =
      MvPolynomial.map f (D.D (MvPolynomial (Fin m) A) (GDet.gen y))) ∧
    (∀ y, D.Kills y → (D.map f).Kills (MonoidAlgebra.mapRingHom G f y)) ∧
    (∀ {A'' : Type} [CommRing A''] (f' : A' →+* A''), (D.map f).map f' = D.map (f'.comp f)) ∧ D.map (RingHom.id A) = D := by
  intro n A G _ _ D A' _ f
  have h1 : ∀ y, (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f := by
    intro y
    have e : MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (MonoidAlgebra.mapRingHom G f y) =
        MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y) := by
      rw [map_sub, MonoidAlgebra.mapRingHom_single, Polynomial.coe_mapRingHom, Polynomial.map_X,
        ← RingHom.comp_apply, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp,
        ← MonoidAlgebra.mapRingHom_comp, Polynomial.mapRingHom_comp_C]
    show (D.map f).D A'[X] _ = _
    rw [e, UpperTheory.V.AlgebraTools.Det.map_D_mapRingHom_eq D f A[X] A'[X] (Polynomial.mapRingHom f) (fun a => by simp)]
    rfl
  have h2 : ∀ i y, (D.map f).lam i (MonoidAlgebra.mapRingHom G f y) = f (D.lam i y) := by
    intro i y
    simp only [GDet.lam, h1, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]
  have h4 : ∀ (σ : Type) (x : MonoidAlgebra (MvPolynomial σ A) G), (D.map f).D (MvPolynomial σ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map f) x) =
      MvPolynomial.map f (D.D (MvPolynomial σ A) x) := fun σ x =>
    UpperTheory.V.AlgebraTools.Det.map_D_mapRingHom_eq D f _ _ (MvPolynomial.map f) (fun a => MvPolynomial.map_C f a) x
  refine ⟨h1, h2, ?_, h4, ?_, ?_, ?_, ?_⟩
  · intro i g
    simpa using h2 i (MonoidAlgebra.single g 1)
  · intro m y
    rw [← h4]
    congr 1
    ext g
    simp [GDet.gen]
  · intro y hy B _ _ h
    let : Algebra A B := ((algebraMap A' B).comp f).toAlgebra
    have := hy B h
    rw [show MonoidAlgebra.mapRingHom G (algebraMap A B) y = MonoidAlgebra.mapRingHom G (algebraMap A' B) (MonoidAlgebra.mapRingHom G f y) from by
      rw [← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp]; rfl] at this
    exact this
  · intro A'' _ f'
    rfl
  · cases D
    simp only [GDet.map]
    congr 1
    funext B _ i
    congr 1
    exact Algebra.algebra_ext _ _ (fun r => rfl)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.BnRepLin
open Polynomial Matrix UpperTheory.V.W

private noncomputable def UpperTheory.V.AlgebraTools.Det.bnRep_lin {n : ℕ} {K G : Type} [Field K] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) K) : Representation K G (Fin n → K) where
  toFun g := Matrix.toLin' (ρ g)
  map_one' := by rw [map_one, Matrix.toLin'_one]; rfl
  map_mul' g h := by rw [map_mul, Matrix.toLin'_mul]; rfl

private theorem UpperTheory.V.AlgebraTools.Det.bnRep_ss {n : ℕ} {K G : Type} [Field K] [Group G]
    (ρ : G →* Matrix (Fin n) (Fin n) K)
    (h : ∀ W : Submodule K (Fin n → K), (∀ g, ∀ v ∈ W, ρ g *ᵥ v ∈ W) →
      ∃ W', (∀ g, ∀ v ∈ W', ρ g *ᵥ v ∈ W') ∧ IsCompl W W') :
    IsSemisimpleModule (MonoidAlgebra K G) (UpperTheory.V.AlgebraTools.Det.bnRep_lin ρ).asModule := by
  rw [← Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  refine ⟨fun W => ?_⟩
  obtain ⟨W', hW', hc⟩ := h W.toSubmodule (fun g v hv => W.apply_mem_toSubmodule g hv)
  refine ⟨⟨W', fun g v hv => hW' g v hv⟩, ?_, ?_⟩
  · rw [disjoint_iff]
    exact Subrepresentation.toSubmodule_injective hc.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subrepresentation.toSubmodule_injective hc.sup_eq_top

theorem UpperTheory.V.AlgebraTools.Det.bnRep :
    ∀ {n : ℕ} {K G : Type} [Field K] [Group G] (ρ ρ' : G →* Matrix (Fin n) (Fin n) K),
    (∀ W : Submodule K (Fin n → K), (∀ g, ∀ v ∈ W, ρ g *ᵥ v ∈ W) → ∃ W', (∀ g, ∀ v ∈ W', ρ g *ᵥ v ∈ W') ∧ IsCompl W W') →
    (∀ W : Submodule K (Fin n → K), (∀ g, ∀ v ∈ W, ρ' g *ᵥ v ∈ W) → ∃ W', (∀ g, ∀ v ∈ W', ρ' g *ᵥ v ∈ W') ∧ IsCompl W W') →
    (∀ g, (ρ g).charpoly = (ρ' g).charpoly) → ∃ P : GL (Fin n) K, ∀ g, (P : Matrix (Fin n) (Fin n) K) * ρ' g = ρ g * P := by
  intro n K G _ _ ρ ρ' h h' hc
  obtain ⟨e, he⟩ := Formalism.IrreducibleCountingLemmas.Z.brauer_nesbitt K G (Fin n → K) (Fin n → K)
    (UpperTheory.V.AlgebraTools.Det.bnRep_lin ρ') (UpperTheory.V.AlgebraTools.Det.bnRep_lin ρ)
    (UpperTheory.V.AlgebraTools.Det.bnRep_ss ρ' h') (UpperTheory.V.AlgebraTools.Det.bnRep_ss ρ h) (fun g => by
      show (Matrix.toLin' (ρ' g)).charpoly = (Matrix.toLin' (ρ g)).charpoly
      rw [Matrix.charpoly_toLin', Matrix.charpoly_toLin']
      exact (hc g).symm)
  have h1 : LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)) *
      LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  have h2 : LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)) *
      LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    simp
  refine ⟨⟨_, _, h2, h1⟩, fun g => ?_⟩
  show LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)) * ρ' g =
    ρ g * LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K))
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  exact he g
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GenEval
open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.genEval :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (B : Type) [CommRing B] [Algebra A B] (m : ℕ) (y : Fin m → MonoidAlgebra A G) (b : Fin m → B),
    D.D B (∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A B) (y j)) =
      MvPolynomial.aeval b (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
  intro n A G _ _ D B _ _ m y b
  rw [← D.nat (MvPolynomial (Fin m) A) B (MvPolynomial.aeval b)]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GDet.gen, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext g
  simp [MonoidAlgebra.mapRingHom]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GenSpan
open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.genSpan :
    ∀ {A G : Type} [CommRing A] [Group G] (B : Type) [CommRing B] [Algebra A B] (x : MonoidAlgebra B G),
    ∃ (m : ℕ) (g : Fin m → G) (b : Fin m → B), x = ∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A B) (MonoidAlgebra.single (g j) 1) := by
  intro A G _ _ B _ _ x
  have hs : ∀ g : G, MonoidAlgebra.mapRingHom G (algebraMap A B) (MonoidAlgebra.single g 1)
      = MonoidAlgebra.single g (1 : B) := by
    intro g
    simp
  simp only [hs]
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    exact ⟨1, fun _ => g, fun _ => 1, by simp [MonoidAlgebra.of_apply]⟩
  | add x y hx hy =>
    obtain ⟨m, g, b, rfl⟩ := hx
    obtain ⟨n, h, c, rfl⟩ := hy
    refine ⟨m + n, Fin.append g h, Fin.append b c, ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  | smul r x hx =>
    obtain ⟨m, g, b, rfl⟩ := hx
    refine ⟨m, g, fun j => r * b j, ?_⟩
    rw [Finset.smul_sum]
    simp [smul_smul]
end
