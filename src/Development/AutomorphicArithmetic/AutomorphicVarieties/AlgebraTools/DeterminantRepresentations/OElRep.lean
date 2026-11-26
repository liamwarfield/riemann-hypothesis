module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepCont

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.OElRep
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.oElRep :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (r : F.G₀ →* GL (Fin n) R) (v : F.Vl) (ψ : Fin n → F.Gv v →* Rˣ), HasFlag (r.comp (F.φ v)) ψ →
    ∀ g, GDet.repAlg (mat r) R (F.oEl v ψ g) = 0 := by
  intro l _ F O _ _ R _ _ n r v ψ h g
  rw [← (UpperTheory.V.AlgebraTools.Det.flagRel _ _ h).2 g, GFrame.oEl, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp [GDet.repAlg, mat, MonoidAlgebra.lift_single]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.InjTest
open Polynomial UpperTheory.V.W

private theorem injTest_mvInj {A : Type} [CommRing A] {X : Type} (K : X → Type) [∀ x, CommRing (K x)]
    (f : ∀ x, A →+* K x) (hf : ∀ a, (∀ x, f x a = 0) → a = 0) {σ : Type} (P Q : MvPolynomial σ A)
    (h : ∀ x, MvPolynomial.map (f x) P = MvPolynomial.map (f x) Q) : P = Q := by
  ext β
  rw [← sub_eq_zero]
  refine hf _ fun x => ?_
  have := congrArg (AddMonoidAlgebra.coeff · β) (h x)
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map] at this
  rw [map_sub, this, sub_self]

private theorem injTest_smul {R S G : Type} [CommRing R] [CommRing S] [Group G] (φ : R →+* S) (r : R)
    (z : MonoidAlgebra R G) :
    MonoidAlgebra.mapRingHom G φ (r • z) = φ r • MonoidAlgebra.mapRingHom G φ z := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [smul_add, map_add (f := _), ha, hb]
  | single g s => simp

private theorem injTest_comp {R S T G : Type} [CommRing R] [CommRing S] [CommRing T] [Group G]
    (φ : R →+* S) (ψ : S →+* T) (z : MonoidAlgebra R G) :
    MonoidAlgebra.mapRingHom G ψ (MonoidAlgebra.mapRingHom G φ z) = MonoidAlgebra.mapRingHom G (ψ.comp φ) z := by
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g s => simp

theorem UpperTheory.V.AlgebraTools.Det.injTest :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] {X : Type} (K : X → Type) [∀ x, CommRing (K x)] (f : ∀ x, A →+* K x),
    (∀ a, (∀ x, f x a = 0) → a = 0) →
    (∀ D D' : GDet n A G, (∀ x, D.map (f x) = D'.map (f x)) → D = D') ∧
    (∀ (D : GDet n A G) (y : MonoidAlgebra A G), (∀ x, (D.map (f x)).Kills (MonoidAlgebra.mapRingHom G (f x) y)) → D.Kills y) := by
  intro n A G _ _ X K _ f hf
  have mapEval (D : GDet n A G) (x : X) {σ : Type} (z : MonoidAlgebra (MvPolynomial σ A) G) :
      (D.map (f x)).D (MvPolynomial σ (K x)) (MonoidAlgebra.mapRingHom G (MvPolynomial.map (f x)) z) =
        MvPolynomial.map (f x) (D.D (MvPolynomial σ A) z) := by
    let : Algebra A (MvPolynomial σ (K x)) := ((algebraMap (K x) (MvPolynomial σ (K x))).comp (f x)).toAlgebra
    exact D.nat _ _ { MvPolynomial.map (f x) with commutes' := fun a => MvPolynomial.map_C (f x) a } z
  have evalGen (B : Type) [CommRing B] [Algebra A B] {m : ℕ} (g : Fin m → G) (b : Fin m → B) :
      MonoidAlgebra.mapRingHom G (MvPolynomial.aeval b : MvPolynomial (Fin m) A →ₐ[A] B)
          (GDet.gen fun j => MonoidAlgebra.single (g j) (1 : A)) =
        ∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A B) (MonoidAlgebra.single (g j) 1) := by
    simp only [GDet.gen, map_sum, injTest_smul, RingHom.coe_coe, MvPolynomial.aeval_X]
    simp
  refine ⟨fun D D' h => ?_, fun D y h => ?_⟩
  · apply GDet.ext
    intro B _ _ w
    obtain ⟨m, g, b, rfl⟩ := UpperTheory.V.AlgebraTools.Det.genSpan (A := A) B w
    let z := GDet.gen fun j => MonoidAlgebra.single (g j) (1 : A)
    have hz : D.D (MvPolynomial (Fin m) A) z = D'.D (MvPolynomial (Fin m) A) z := by
      refine injTest_mvInj K f hf _ _ fun x => ?_
      rw [← mapEval D x z, ← mapEval D' x z, h x]
    rw [← evalGen B g b, D.nat, D'.nat, hz]
  · intro B _ _ w
    obtain ⟨m, g, b, rfl⟩ := UpperTheory.V.AlgebraTools.Det.genSpan (A := A) B w
    set z : MonoidAlgebra (MvPolynomial (Fin m) A) G :=
      1 + GDet.gen (fun j => MonoidAlgebra.single (g j) (1 : A)) * MonoidAlgebra.mapRingHom G MvPolynomial.C y with hz
    have h1 : D.D (MvPolynomial (Fin m) A) z = 1 := by
      refine injTest_mvInj K f hf _ _ fun x => ?_
      rw [← mapEval D x z, map_one, hz, map_add, map_one, map_mul, injTest_comp]
      have e : (MvPolynomial.map (f x) : MvPolynomial (Fin m) A →+* _).comp MvPolynomial.C =
          (algebraMap (K x) (MvPolynomial (Fin m) (K x))).comp (f x) := by
        ext a : 1
        simp
      rw [e, ← injTest_comp]
      exact h x _ _
    have h2 := D.nat _ B (MvPolynomial.aeval b) z
    have e : ((MvPolynomial.aeval b : MvPolynomial (Fin m) A →ₐ[A] B) : MvPolynomial (Fin m) A →+* B).comp
        MvPolynomial.C = algebraMap A B := by
      ext a : 1
      simp
    rw [h1, map_one, hz, map_add, map_one, map_mul, injTest_comp, e, evalGen] at h2
    exact h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.FormRep
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

private theorem repAlg_single {G R : Type} [Group G] [CommRing R] {a : ℕ} (ρ : G →* Matrix (Fin a) (Fin a) R)
    (B : Type) [CommRing B] [Algebra R B] (g : G) (b : B) :
    GDet.repAlg ρ B (MonoidAlgebra.single g b) = b • (ρ g).map (algebraMap R B) := by
  simp [GDet.repAlg]

private theorem UpperTheory.V.AlgebraTools.Det.eps_zpow_algebraMap_eq {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (B : Type) [CommRing B] [Algebra R B]
    [Algebra O B] [IsScalarTower O R B] (g : F.G₀) (k : ℤ) :
    ((F.eps O B g ^ k : Bˣ) : B) = algebraMap R B ((F.eps O R g ^ k : Rˣ) : R) := by
  have e : F.eps O B g = Units.map (algebraMap R B : R →* B) (F.eps O R g) := by
    ext
    simp [GFrame.eps, IsScalarTower.algebraMap_apply O R B]
  rw [e, ← map_zpow]
  rfl

theorem UpperTheory.V.AlgebraTools.Det.formRep :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) {a : ℕ} (r : F.G₀ →* GL (Fin a) R) (P : GL (Fin a) R), F.IsForm O n r P →
    (∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀),
      (GDet.repAlg (mat r) B y)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) =
        (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * GDet.repAlg (mat r) B (F.star O B n y)) ∧
    (∀ y, GDet.repAlg (mat r) R y = 0 → GDet.repAlg (mat r) R (F.star O R n y) = 0) ∧
    ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀),
      (GDet.ofRep (mat r)).D B (F.star O B n y) = (GDet.ofRep (mat r)).D B y := by
  intro l _ F O _ _ R _ _ n a r P hP
  have h1 : ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀),
      (GDet.repAlg (mat r) B y)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) =
        (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * GDet.repAlg (mat r) B (F.star O B n y) := by
    intro B _ _ _ _ y
    let ρ' : F.G₀ →* Matrix (Fin a) (Fin a) B := (algebraMap R B).mapMatrix.toMonoidHom.comp (mat r)
    have hρ : ∀ g, (mat r g).map (algebraMap R B) = ρ' g := fun g => rfl
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp [GFrame.star]
    | add x z hx hz =>
      rw [(UpperTheory.V.AlgebraTools.Det.starApi F O B n).2.2.1, map_add (f := _), map_add (f := _), Matrix.transpose_add, Matrix.add_mul,
        Matrix.mul_add, hx, hz]
    | single g b =>
      have hs : F.star O B n (MonoidAlgebra.single g b) =
          MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O B g ^ (1 - (n:ℤ)) : Bˣ) : B)) := by
        simp [GFrame.star, GFrame.starOp]
      rw [hs, repAlg_single, repAlg_single, hρ, hρ, UpperTheory.V.AlgebraTools.Det.eps_zpow_algebraMap_eq F O R B]
      have hF : (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g) =
          algebraMap R B ((F.eps O R g ^ (1 - (n:ℤ)) : Rˣ) : R) • (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) := by
        have := congrArg (fun M : Matrix (Fin a) (Fin a) R => M.map (algebraMap R B)) (hP g)
        have h' : (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g) =
            ((((F.eps O R g ^ (1 - (n:ℤ)) : Rˣ) : R)) • (P : Matrix (Fin a) (Fin a) R)).map (algebraMap R B) := by
          simpa [Matrix.map_mul, Matrix.transpose_map, ρ'] using this
        rw [h']
        ext i j
        simp
      have hinv : ρ' (F.conj g) * ρ' (F.conj g)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      have key : (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) =
          algebraMap R B ((F.eps O R g ^ (1 - (n:ℤ)) : Rˣ) : R) •
            ((P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g)⁻¹) := by
        calc (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B)
            = (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * (ρ' (F.conj g) * ρ' (F.conj g)⁻¹) := by
              rw [hinv, Matrix.mul_one]
          _ = (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g) * ρ' (F.conj g)⁻¹ := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [hF, Matrix.smul_mul]
      rw [Matrix.transpose_smul, Matrix.smul_mul, key, Matrix.mul_smul, smul_smul]
  have hu : ∀ (B : Type) [CommRing B] [Algebra R B],
      IsUnit ((P : Matrix (Fin a) (Fin a) R).map (algebraMap R B)) := by
    intro B _ _
    exact (P.isUnit.map (algebraMap R B).mapMatrix)
  refine ⟨h1, ?_, ?_⟩
  · intro y hy
    have := h1 R y
    rw [hy, Matrix.transpose_zero, Matrix.zero_mul] at this
    obtain ⟨u, hu'⟩ := hu R
    have h2 := congrArg (fun M => (↑u⁻¹ : Matrix (Fin a) (Fin a) R) * M) this
    simp only [← hu', Matrix.mul_zero, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2
    exact h2.symm
  · intro B _ _ _ _ y
    have := congrArg Matrix.det (h1 B y)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_comm] at this
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (hu B)
    exact (hd.mul_left_cancel this).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.ChiApi
open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.chiApi :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G),
    D.lam 0 y = 1 ∧ D.lam n y = D.D A y ∧ (D.chi y).Monic ∧ (D.chi y).natDegree ≤ n ∧
    D.chi y = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * D.lam i y) * X ^ (n - i) := by
  intro n A G _ _ D y
  have hsum : D.chi y = ∑ i ∈ Finset.range (n + 1), C ((-1) ^ i * D.lam i y) * X ^ (n - i) := by
    have key := UpperTheory.V.AlgebraTools.Det.expand D y (Polynomial A) X (-1)
    have h1 : MonoidAlgebra.single 1 (X : Polynomial A) +
        (-1 : Polynomial A) • (MonoidAlgebra.mapRingHom G (algebraMap A (Polynomial A))) y =
        MonoidAlgebra.single 1 X - (MonoidAlgebra.mapRingHom G C) y := by
      rw [neg_one_smul, ← sub_eq_add_neg, Polynomial.algebraMap_eq]
    rw [h1] at key
    unfold UpperTheory.V.W.GDet.chi
    rw [key]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.algebraMap_eq, C_mul, C_pow, C_neg, C_1]
    ring
  have h0 : D.lam 0 y = 1 := by
    have key := UpperTheory.V.AlgebraTools.Det.expand D y A 1 0
    rw [zero_smul, add_zero, ← MonoidAlgebra.one_def, map_one] at key
    rw [Finset.sum_eq_single 0] at key
    · simpa using key.symm
    · intro b _ hb
      simp [zero_pow hb]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  have hn : D.lam n y = D.D A y := by
    have key := UpperTheory.V.AlgebraTools.Det.expand D y A 0 1
    rw [Finset.sum_eq_single n] at key
    · simp only [MonoidAlgebra.single_zero, zero_add, one_smul, Nat.sub_self, pow_zero, one_pow,
        mul_one, Algebra.algebraMap_self, RingHom.id_apply] at key
      rw [← key]
      congr 1
      ext g
      simp [MonoidAlgebra.mapRingHom]
    · intro b hb hbn
      have : n - b ≠ 0 := by
        have := Finset.mem_range.mp hb
        omega
      simp [zero_pow this]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) h
  have hdeg : (D.chi y).natDegree ≤ n := by
    rw [hsum]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    omega
  have hcoeff : (D.chi y).coeff n = 1 := by
    rw [hsum, Polynomial.finsetSum_coeff, Finset.sum_eq_single 0]
    · simp [h0]
    · intro b hb hb0
      have : n ≠ n - b := by
        have := Finset.mem_range.mp hb
        omega
      rw [Polynomial.coeff_C_mul_X_pow, if_neg this]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h
  exact ⟨h0, hn, Polynomial.monic_of_natDegree_le_of_coeff_eq_one n hdeg hcoeff, hdeg, hsum⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.StarDet
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

private theorem star_mapRingHom_algHom_eq {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (B B' : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] [CommRing B'] [Algebra R B'] [Algebra O B'] [IsScalarTower O R B'] (f : B →ₐ[R] B') (x : MonoidAlgebra B F.G₀) : F.star O B' n (MonoidAlgebra.mapRingHom F.G₀ (f : B →+* B') x) = MonoidAlgebra.mapRingHom F.G₀ (f : B →+* B') (F.star O B n x) := by
  have he : ∀ g : F.G₀, Units.map (f : B →* B') (F.eps O B g) = F.eps O B' g := by
    intro g
    ext
    simp [GFrame.eps, pushCh, IsScalarTower.algebraMap_apply O R B, IsScalarTower.algebraMap_apply O R B']
  have hs : ∀ (C : Type) [CommRing C] [Algebra O C] (g : F.G₀) (b : C), F.star O C n (MonoidAlgebra.single g b) = MonoidAlgebra.single (F.conj g)⁻¹ (b * ↑(F.eps O C g ^ (1 - (n:ℤ)))) := by
    intro C _ _ g b
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, MonoidAlgebra.smul_single']
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [GFrame.star]
  | add x y hx hy => simp only [map_add (f := _)] at hx hy ⊢; simp [GFrame.star, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
  | single g b =>
    rw [MonoidAlgebra.mapRingHom_single, hs, hs, MonoidAlgebra.mapRingHom_single, map_mul, ← he g, ← map_zpow]
    rfl

theorem UpperTheory.V.AlgebraTools.Det.starDet :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (D : GDet n R F.G₀), ∃ D' : GDet n R F.G₀,
    ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀), D'.D B y = D.D B (F.star O B n y) := by
  intro l _ F O _ _ R _ _ n D
  let E : ∀ (B : Type) [CommRing B] [Algebra R B], MonoidAlgebra B F.G₀ →* B := fun B _ _ =>
    letI : Algebra O B := ((algebraMap R B).comp (algebraMap O R)).toAlgebra
    { toFun := fun y => D.D B (F.star O B n y)
      map_one' := by simp [GFrame.star]
      map_mul' := fun x y => by
        have hm : F.star O B n (x * y) = F.star O B n y * F.star O B n x := by simp [GFrame.star, map_mul]
        simp only [hm, map_mul, mul_comm] }
  have hE : ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀), E B y = D.D B (F.star O B n y) := by
    intro B _ _ iO _ y
    have hi : ((algebraMap R B).comp (algebraMap O R)).toAlgebra = iO :=
      Algebra.algebra_ext _ _ (fun r => (IsScalarTower.algebraMap_apply O R B r).symm)
    subst hi
    rfl
  refine ⟨{ D := E, nat := ?_, homog := ?_ }, fun B _ _ _ _ y => hE B y⟩
  · intro B B' _ _ _ _ f x
    letI : Algebra O B := ((algebraMap R B).comp (algebraMap O R)).toAlgebra
    haveI : IsScalarTower O R B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI : Algebra O B' := ((algebraMap R B').comp (algebraMap O R)).toAlgebra
    haveI : IsScalarTower O R B' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    rw [hE B', hE B, star_mapRingHom_algHom_eq F O R n B B' f x, D.nat]
  · intro B _ _ b x
    letI : Algebra O B := ((algebraMap R B).comp (algebraMap O R)).toAlgebra
    haveI : IsScalarTower O R B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hsm : F.star O B n (b • x) = b • F.star O B n x := by simp [GFrame.star, map_smul]
    rw [hE B, hE B, hsm, D.homog]
end
