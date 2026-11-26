module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem gdet_inst {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (B : Type) [CommRing B]
    (i j : Algebra A B) (h : ∀ a, @algebraMap A B _ _ i a = @algebraMap A B _ _ j a) (x : MonoidAlgebra B G) :
    @GDet.D n A G _ _ D B _ i x = @GDet.D n A G _ _ D B _ j x := by
  have : i = j := Algebra.algebra_ext _ _ h
  subst this
  rfl

private theorem gdet_chi {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
    {B : Type} [CommRing B] (f : A →+* B) (y : MonoidAlgebra A G) :
    (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f := by
  letI : Algebra A B[X] := ((algebraMap B B[X]).comp f).toAlgebra
  let φ : A[X] →ₐ[A] B[X] :=
    { Polynomial.mapRingHom f with
      commutes' := fun a => by
        change Polynomial.map f (C a) = C (f a)
        exact Polynomial.map_C f }
  have h := D.nat A[X] B[X] φ (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
  refine Eq.trans ?_ h
  change D.D B[X] _ = D.D B[X] _
  congr 1
  have hφ : (φ : A[X] →+* B[X]) = Polynomial.mapRingHom f := rfl
  rw [hφ]
  ext g : 2
  simp

theorem UpperTheory.V.CA.d_gmap :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G), D.map (RingHom.id A) = D ∧ (∀ {B C : Type} [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C), (D.map f).map g = D.map (g.comp f)) ∧ (∀ {B : Type} [CommRing B] (f : A →+* B) (y : MonoidAlgebra A G), (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f ∧ ∀ i, (D.map f).lam i (MonoidAlgebra.mapRingHom G f y) = f (D.lam i y)) ∧ ∀ {B : Type} [CommRing B] (f : A →+* B) (ρ : G →* Matrix (Fin n) (Fin n) A), (GDet.ofRep ρ).map f = GDet.ofRep (f.mapMatrix.toMonoidHom.comp ρ) := by
  intro n A G _ _ D
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact GDet.ext fun B _ j x =>
      gdet_inst D B ((algebraMap A B).comp (RingHom.id A)).toAlgebra j (fun _ => rfl) x
  · intro B C _ _ f g
    exact GDet.ext fun S _ _ x => gdet_inst D S _ _ (fun _ => rfl) x
  · intro B _ f y
    refine ⟨gdet_chi D f y, fun i => ?_⟩
    simp only [GDet.lam, gdet_chi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]
  · intro B _ f ρ
    refine GDet.ext fun S _ _ x => ?_
    letI : Algebra A S := ((algebraMap B S).comp f).toAlgebra
    change (GDet.repAlg ρ S x).det = (GDet.repAlg (f.mapMatrix.toMonoidHom.comp ρ) S x).det
    congr 2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
noncomputable section

open IsLocalRing TensorProduct Polynomial UpperTheory.V.W UpperTheory.V.Alg

namespace UpperTheory.V.CA

def Z1 {G k : Type} [Group G] [TopologicalSpace G] [Field k] (χ ψ : G →* kˣ) : Submodule k (G → k) where
  carrier := {a | IsLocallyConstant a ∧ ∀ g h, a (g * h) = χ g * a h + a g * ψ h}
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, fun g h => by simp only [Pi.add_apply, ha.2, hb.2]; ring⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun g h => by simp⟩
  smul_mem' c a ha := ⟨ha.1.comp fun x => c * x, fun g h => by simp only [Pi.smul_apply, smul_eq_mul, ha.2]; ring⟩

structure MultFree {n : ℕ} {G k : Type} [Group G] [TopologicalSpace G] [Field k] (χ : Fin n → G →* kˣ) (h : ℕ) :
    Prop where
  isOpen : ∀ i, IsOpen ((χ i).ker : Set G)
  inj : Function.Injective χ
  fin : ∀ i j, i ≠ j → Module.Finite k (Z1 (χ i) (χ j)) ∧ Module.finrank k (Z1 (χ i) (χ j)) ≤ h

def finBound (n h : ℕ) : ℕ := n + ∑ p ∈ Finset.range n, (n ^ 2 * h) ^ p

structure IsGMA {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : Fin n → E) : Prop where
  ch : D.IsCH
  idem : CompleteOrthogonalIdempotents e
  rank : ∀ i, D.D A[X] (1 + X ⊗ₜ e i) = 1 + X

structure IsDef (O : Type) [CommRing O] [IsLocalRing O] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    (Dbar : GDet n (ResidueField O) G) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (D : GDet n R G) : Prop where
  cont : D.IsCont (maximalIdeal R)
  red : D.map (res O R : R →+* ResidueField O) = Dbar

structure IsUnivDet (O : Type) [CommRing O] [IsLocalRing O] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    (Dbar : GDet n (ResidueField O) G) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (D : GDet n R G) : Prop where
  isDef : IsDef O Dbar D
  univ : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (D' : GDet n R' G), IsDef O Dbar D' →
    ∃! f : R →ₐ[O] R', D.map (f : R →+* R') = D'

end UpperTheory.V.CA
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_toDet :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G), D.toDet.chi y = D.chi y ∧ (∀ i, D.toDet.lam i y = D.lam i y) ∧ D.toDet.tr y = D.tr y ∧ (D.toDet.Kills y ↔ D.Kills y) := by
  intro n A G _ _ D y
  have hchi : D.toDet.chi y = D.chi y := by
    change D.D A[X] (ofT A G A[X] (X ⊗ₜ 1 - 1 ⊗ₜ y)) =
      D.D A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
    congr 1
    rw [map_sub, ofT_tmul, ofT_tmul, map_one, one_smul, MonoidAlgebra.one_def, MonoidAlgebra.smul_single,
      smul_eq_mul, mul_one]
    rfl
  have hlam : ∀ i, D.toDet.lam i y = D.lam i y := fun i => by
    unfold Det.lam GDet.lam
    rw [hchi]
  refine ⟨hchi, hlam, hlam 1, ?_⟩
  have key : ∀ (B : Type) [CommRing B] [Algebra A B] (h : B ⊗[A] MonoidAlgebra A G),
      D.toDet.D B (1 + h * (1 ⊗ₜ y)) =
        D.D B (1 + ofT A G B h * MonoidAlgebra.mapRingHom G (algebraMap A B) y) := by
    intro B _ _ h
    change D.D B (ofT A G B (1 + h * (1 ⊗ₜ y))) = _
    rw [map_add (f := _), map_one, map_mul, ofT_tmul, one_smul]
  constructor
  · intro hk B _ _ h
    have := hk B (toT A G B h)
    rwa [key, ofT_toT] at this
  · intro hk B _ _ h
    rw [key]
    exact hk B _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DOfRep
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem chiS_ofRep {n : ℕ} {A E ι : Type} [CommRing A] [Ring E] [Algebra A E] [Fintype ι] [DecidableEq ι]
    (h : Fintype.card ι = n) (r : E →ₐ[A] Matrix ι ι A) (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] E) :
    (Det.ofRep h r).chiS S y = (Det.repS r S y).charpoly := by
  have h1 : Det.repS r (Polynomial S)
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S (Polynomial S)) (AlgHom.id A E) y) =
      (Det.repS r S y).map Polynomial.C := by
    induction y with
    | tmul s z =>
      ext1 a b
      simp [Det.repS_tmul, Polynomial.single_eq_monomial]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), Matrix.map_add _ (map_add _)]
  change (Det.repS r (Polynomial S) _).det = _
  rw [map_sub, h1, Det.repS_tmul, Matrix.charpoly, Matrix.charmatrix]
  congr 2
  ext1 a b
  by_cases hab : a = b <;>
    simp [hab, Matrix.one_apply, Matrix.diagonal_apply, Polynomial.single_eq_monomial]

private theorem chi_ofRep {n : ℕ} {A E ι : Type} [CommRing A] [Ring E] [Algebra A E] [Fintype ι] [DecidableEq ι]
    (h : Fintype.card ι = n) (r : E →ₐ[A] Matrix ι ι A) (x : E) :
    (Det.ofRep h r).chi x = (r x).charpoly := by
  change (Det.repS r (Polynomial A) _).det = _
  rw [map_sub, Det.repS_tmul, Det.repS_tmul, Matrix.charpoly, Matrix.charmatrix]
  congr 2
  · ext1 a b
    by_cases hab : a = b <;> simp [hab, Matrix.one_apply, Matrix.diagonal_apply]
  · ext1 a b
    simp

private theorem coeff_repS {σ A E ι : Type} [CommRing A] [Ring E] [Algebra A E] [Fintype ι] [DecidableEq ι]
    (r : E →ₐ[A] Matrix ι ι A) (α : σ →₀ ℕ) (z : MvPolynomial σ A ⊗[A] E) :
    r (TensorProduct.lid A E ((MvPolynomial.lcoeff A α).rTensor E z)) =
      (Det.repS r (MvPolynomial σ A) z).map (AddMonoidAlgebra.coeff · α) := by
  induction z with
  | tmul s z =>
    ext a b
    simp only [Det.repS_tmul, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, MvPolynomial.algebraMap_eq]
    rw [mul_comm s, MvPolynomial.coeff_C_mul]
    simp [mul_comm]
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), Matrix.map_add _ (MvPolynomial.coeff_add α)]

theorem UpperTheory.V.CA.d_ofRep :
    ∀ {n : ℕ} {A E ι : Type} [CommRing A] [Ring E] [Algebra A E] [Fintype ι] [DecidableEq ι] (h : Fintype.card ι = n) (r : E →ₐ[A] Matrix ι ι A) (x : E), (Det.ofRep h r).chi x = (r x).charpoly ∧ (Det.ofRep h r).val x = (r x).det ∧ (1 ≤ n → (Det.ofRep h r).tr x = (r x).trace) ∧ (x ∈ (Det.ofRep h r).CH → r x = 0) := by
  intro n A E ι _ _ _ _ _ h r x
  refine ⟨chi_ofRep h r x, ?_, fun hn => ?_, fun hx => ?_⟩
  · change (Det.repS r A (1 ⊗ₜ x)).det = _
    rw [Det.repS_tmul]
    simp
  · haveI : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    rw [Det.tr, Det.lam, chi_ofRep, Matrix.trace_eq_neg_charpoly_coeff, h]
    simp
  · have hle : (Det.ofRep h r).CH ≤ TwoSidedIdeal.ker r := by
      rw [Det.CH, TwoSidedIdeal.span_le]
      rintro z ⟨k, y, α, rfl⟩
      change _ ∈ TwoSidedIdeal.ker r
      rw [TwoSidedIdeal.mem_ker, Det.chElt, coeff_repS, chiS_ofRep, ← Polynomial.aeval_algHom_apply,
        Matrix.aeval_self_charpoly]
      ext a b
      simp
    exact (TwoSidedIdeal.mem_ker r).1 (hle hx)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetOfRep
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_toDet_ofRep :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G], (∀ ρ : G →* Matrix (Fin n) (Fin n) A, (GDet.ofRep ρ).toDet = Det.ofRep (Fintype.card_fin n) (GDet.repAlg ρ A)) ∧ ∀ (D : GDet n A G) (H : Type) [Group H] (φ : H →* G), (D.comap φ).toDet = D.toDet.pull (MonoidAlgebra.mapDomainAlgHom A A φ) := by
  intro n A G _ _
  refine ⟨fun ρ => Det.ext' fun S _ _ x => ?_, fun D H _ φ => Det.ext' fun S _ _ x => ?_⟩
  · change (GDet.repAlg ρ S (ofT A G S x)).det = (Det.repS (GDet.repAlg ρ A) S x).det
    congr 1
    induction x with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul s y =>
      rw [ofT_tmul, Det.repS_tmul, map_smul]
      congr 1
      induction y using MonoidAlgebra.induction_linear with
      | zero => ext i j; simp
      | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]; ext i j; simp
      | single g r => ext i j; simp [GDet.repAlg]
  · change D.D S (MonoidAlgebra.mapDomainRingHom S φ (ofT A H S x)) =
      D.D S (ofT A G S (Algebra.TensorProduct.map (AlgHom.id S S) (MonoidAlgebra.mapDomainAlgHom A A φ) x))
    congr 1
    induction x with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul s y =>
      induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
      | single g r => simp [ofT_tmul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetCH
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem D_congr {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (B : Type) [CommRing B]
    (i j : Algebra A B) (h : ∀ a, @algebraMap A B _ _ i a = @algebraMap A B _ _ j a) (x : MonoidAlgebra B G) :
    @GDet.D n A G _ _ D B _ i x = @GDet.D n A G _ _ D B _ j x := by
  have : i = j := Algebra.algebra_ext i j h
  subst this; rfl

private theorem ofT_gen {A G : Type} [CommRing A] [Group G] {m : ℕ} (y : Fin m → MonoidAlgebra A G) :
    ofT A G (MvPolynomial (Fin m) A) (Det.gen (A := A) y) = GDet.gen y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Det.gen, GDet.gen, map_sum, ofT_tmul]
  rfl

private theorem ofT_map {A G : Type} [CommRing A] [Group G] (S : Type) [CommRing S] [Algebra A S]
    (x : S ⊗[A] MonoidAlgebra A G) :
    ofT A G S[X] (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A _) x) =
      MonoidAlgebra.mapRingHom G (C : S →+* S[X]) (ofT A G S x) := by
  induction x with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul s y => ext1; ext1 g; simp [ofT_tmul]

private theorem chiS_eq {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) {m : ℕ}
    (x : MvPolynomial (Fin m) A ⊗[A] MonoidAlgebra A G) :
    D.toDet.chiS (MvPolynomial (Fin m) A) x =
      (D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (ofT A G _ x) := by
  have h : ofT A G (MvPolynomial (Fin m) A)[X] (X ⊗ₜ 1 -
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) A)[X])
        (AlgHom.id A _) x) =
      MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (ofT A G _ x) := by
    rw [map_sub, ofT_map, ofT_tmul, map_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  refine (congrArg (D.D (MvPolynomial (Fin m) A)[X]) h).trans ?_
  exact D_congr D (MvPolynomial (Fin m) A)[X] inferInstance
    ((algebraMap (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) A)[X]).comp MvPolynomial.C).toAlgebra (fun a => rfl) _

private theorem coeff_lid {A G : Type} [CommRing A] [Group G] {m : ℕ} (β : Fin m →₀ ℕ)
    (w : MvPolynomial (Fin m) A ⊗[A] MonoidAlgebra A G) (g : G) :
    (TensorProduct.lid A (MonoidAlgebra A G) ((MvPolynomial.lcoeff A β).rTensor _ w)).coeff g =
      AddMonoidAlgebra.coeff ((ofT A G _ w).coeff g) β := by
  induction w with
  | add a b ha hb => simp only [map_add (f := _), MonoidAlgebra.coeff_add, Finsupp.add_apply, MvPolynomial.coeff_add, ha, hb]
  | tmul s y => simp [ofT_tmul, mul_comm s, MvPolynomial.coeff_C_mul, mul_comm (y.coeff g)]

private theorem chElt_coeff {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) {m : ℕ}
    (y : Fin m → MonoidAlgebra A G) (β : Fin m →₀ ℕ) (g : G) :
    (D.toDet.chElt y β).coeff g = AddMonoidAlgebra.coeff ((Polynomial.aeval (GDet.gen y)
        ((D.map (MvPolynomial.C : A →+* MvPolynomial (Fin m) A)).chi (GDet.gen y))).coeff g)
      β := by
  rw [Det.chElt, coeff_lid, chiS_eq, ← Polynomial.aeval_algHom_apply, ofT_gen]

theorem UpperTheory.V.CA.d_toDet_CH :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G), D.toDet.CH = TwoSidedIdeal.span D.CH := by
  intro n A G _ _ D
  rw [Det.CH]
  congr 1
  ext1 z
  constructor
  · rintro ⟨m, y, β, rfl⟩
    exact ⟨m, y, β, chElt_coeff D y β⟩
  · rintro ⟨m, y, β, h⟩
    refine ⟨m, y, β, ?_⟩
    ext g
    rw [h, chElt_coeff]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapSurj
theorem UpperTheory.Reformulated.B.Qk2.map_surj :
    ∀ {A E : Type} [inst : CommRing A] [inst_1 : Ring E]
    [inst_2 : Algebra A E] {E' : Type} [inst_3 : Ring E'] [inst_4 : Algebra A E'] (f : E' →ₐ[A] E),
    Function.Surjective (⇑f : E' → E) →
      ∀ (S : Type) [inst_5 : CommRing S] [inst_6 : Algebra A S],
        Function.Surjective
          (⇑(Algebra.TensorProduct.map (AlgHom.id S S) f) : TensorProduct A S E' → TensorProduct A S E) := by
  intro A E _ _ _ E' _ _ f hf S _ _ x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul s e =>
    obtain ⟨e', rfl⟩ := hf e
    exact ⟨TensorProduct.tmul A s e', by simp⟩
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩
end

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {E' : Type} [Ring E']
  [Algebra A E'] (f : E' →ₐ[A] E)

private theorem pull_D (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] E') :
    (D.pull f).D S y = D.D S (Algebra.TensorProduct.map (AlgHom.id S S) f y) := rfl

private theorem map_gen {ι : Type} [Fintype ι] (x : ι → E') :
    Algebra.TensorProduct.map (AlgHom.id (MvPolynomial ι A) (MvPolynomial ι A)) f (Det.gen (A := A) x) =
      Det.gen (A := A) (fun a => f (x a)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Det.gen, map_sum]

private theorem pull_chiS (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] E') :
    (D.pull f).chiS S y = D.chiS S (Algebra.TensorProduct.map (AlgHom.id S S) f y) := by
  unfold Det.chiS
  rw [pull_D]
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]

private theorem map_coeff {ι : Type} (α : ι →₀ ℕ) (y : MvPolynomial ι A ⊗[A] E') :
    f (TensorProduct.lid A E' ((MvPolynomial.lcoeff A α).rTensor E' y)) =
      TensorProduct.lid A E ((MvPolynomial.lcoeff A α).rTensor E
        (Algebra.TensorProduct.map (AlgHom.id (MvPolynomial ι A) (MvPolynomial ι A)) f y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

private theorem map_chElt {k : ℕ} (x : Fin k → E') (α : Fin k →₀ ℕ) :
    f ((D.pull f).chElt x α) = D.chElt (fun a => f (x a)) α := by
  unfold Det.chElt
  rw [map_coeff, pull_chiS, ← Polynomial.aeval_algHom_apply, map_gen]

private theorem map_surj (hf : Function.Surjective f) (S : Type) [CommRing S] [Algebra A S] :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id S S) f) :=
  by apply _root_.UpperTheory.Reformulated.B.Qk2.map_surj <;> assumption

end

theorem UpperTheory.V.CA.d_pull :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {E' : Type} [Ring E'] [Algebra A E'] (f : E' →ₐ[A] E), (∀ x, (D.pull f).chi x = D.chi (f x)) ∧ (∀ x, f x ∈ D.ker → x ∈ (D.pull f).ker) ∧ (∀ x ∈ (D.pull f).CH, f x ∈ D.CH) ∧ (Function.Surjective f → (∀ x, x ∈ (D.pull f).ker → f x ∈ D.ker) ∧ ∀ y ∈ D.CH, ∃ x ∈ (D.pull f).CH, f x = y) := by
  intro n A E _ _ _ D E' _ _ f
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_, fun hf => ⟨fun x hx => ?_, fun y hy => ?_⟩⟩
  · unfold Det.chi
    rw [pull_D]
    simp
  · rw [Det.mem_ker] at hx ⊢
    intro S _ _ y u v
    rw [pull_D, pull_D, map_add (f := _), map_mul, map_mul, Algebra.TensorProduct.map_tmul, map_one]
    exact hx S _ _ _
  · unfold Det.CH at hx
    induction hx using TwoSidedIdeal.span_induction with
    | mem x h =>
      obtain ⟨k, z, α, rfl⟩ := h
      exact TwoSidedIdeal.subset_span ⟨k, _, α, map_chElt D f z α⟩
    | zero => rw [map_zero]; exact D.CH.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact D.CH.add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact D.CH.neg_mem hx
    | left_absorb a x _ hx => rw [map_mul]; exact D.CH.mul_mem_left _ _ hx
    | right_absorb b x _ hx => rw [map_mul]; exact D.CH.mul_mem_right _ _ hx
  · rw [Det.mem_ker] at hx ⊢
    intro S _ _ y u v
    obtain ⟨y, rfl⟩ := map_surj f hf S y
    obtain ⟨u, rfl⟩ := map_surj f hf S u
    obtain ⟨v, rfl⟩ := map_surj f hf S v
    have := hx S y u v
    rwa [pull_D, pull_D, map_add, map_mul, map_mul, Algebra.TensorProduct.map_tmul, map_one] at this
  · unfold Det.CH at hy
    induction hy using TwoSidedIdeal.span_induction with
    | mem y h =>
      obtain ⟨k, z, α, rfl⟩ := h
      choose w hw using fun a => hf (z a)
      refine ⟨(D.pull f).chElt w α, TwoSidedIdeal.subset_span ⟨k, w, α, rfl⟩, ?_⟩
      rw [map_chElt]
      simp only [hw]
    | zero => exact ⟨0, (D.pull f).CH.zero_mem, map_zero f⟩
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨x' + y', (D.pull f).CH.add_mem hx' hy', map_add f _ _⟩
    | neg x _ hx =>
      obtain ⟨x', hx', rfl⟩ := hx
      exact ⟨-x', (D.pull f).CH.neg_mem hx', map_neg f _⟩
    | left_absorb a x _ hx =>
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨a, rfl⟩ := hf a
      exact ⟨a * x', (D.pull f).CH.mul_mem_left _ _ hx', map_mul f _ _⟩
    | right_absorb a x _ hx =>
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨a, rfl⟩ := hf a
      exact ⟨x' * a, (D.pull f).CH.mul_mem_right _ _ hx', map_mul f _ _⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.BcChiTmul
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem bc_D {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type)
    [CommRing B] [Algebra A B] (S : Type) [CommRing S] [Algebra B S] [inst : Algebra A S] [h : IsScalarTower A B S]
    (y : S ⊗[B] (B ⊗[A] E)) : (D.baseChange B).D S y = D.D S (Det.cancel A E B S y) := by
  have e : inst = ((algebraMap B S).comp (algebraMap A B)).toAlgebra :=
    Algebra.algebra_ext _ _ fun a => IsScalarTower.algebraMap_apply A B S a
  subst e
  rfl

private theorem cancel_one {A E : Type} [CommRing A] [Ring E] [Algebra A E] (B : Type)
    [CommRing B] [Algebra A B] (S : Type) [CommRing S] [Algebra B S] [Algebra A S] [IsScalarTower A B S]
    (y : B ⊗[A] E) : Det.cancel A E B S (1 ⊗ₜ y) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B S) (AlgHom.id A E) y := by
  induction y with
  | tmul b z => simp [Det.cancel_tmul]
  | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]

private theorem bc_chi {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type)
    [CommRing B] [Algebra A B] (y : B ⊗[A] E) : (D.baseChange B).chi y = D.chiS B y := by
  unfold Det.chi Det.chiS
  rw [bc_D, map_sub, cancel_one, Algebra.TensorProduct.one_def, Det.cancel_tmul, map_one, mul_one]

private theorem bc_chi_tmul {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type)
    [CommRing B] [Algebra A B] (x : E) : (D.baseChange B).chi (1 ⊗ₜ x) = (D.chi x).map (algebraMap A B) := by
  rw [bc_chi]
  have h := D.nat A[X] B[X] (Polynomial.mapAlgHom (Algebra.ofId A B)) (X ⊗ₜ 1 - 1 ⊗ₜ x)
  unfold Det.chi Det.chiS
  refine Eq.trans ?_ (h.trans ?_)
  · congr 1
    simp
  · rfl

theorem UpperTheory.V.CA.d_bc :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type) [CommRing B] [Algebra A B], (∀ (S : Type) [CommRing S] [Algebra B S] [Algebra A S] [IsScalarTower A B S] (y : S ⊗[B] (B ⊗[A] E)), (D.baseChange B).D S y = D.D S (Det.cancel A E B S y)) ∧ (∀ y, (D.baseChange B).val y = D.D B y) ∧ (∀ y, (D.baseChange B).chi y = D.chiS B y) ∧ ∀ x : E, (D.baseChange B).chi (1 ⊗ₜ x) = (D.chi x).map (algebraMap A B) ∧ ∀ i, (D.baseChange B).lam i (1 ⊗ₜ x) = algebraMap A B (D.lam i x) := by
  intro n A E _ _ _ D B _ _
  refine ⟨fun S _ _ _ _ y => bc_D D B S y, fun y => ?_, bc_chi D B, fun x => ⟨bc_chi_tmul D B x, fun i => ?_⟩⟩
  · change (D.baseChange B).D B (1 ⊗ₜ y) = _
    rw [bc_D, cancel_one]
    congr 1
    induction y with
    | tmul b z => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  · unfold Det.lam
    rw [bc_chi_tmul, Polynomial.coeff_map]
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DComm
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_comm :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (S : Type) [CommRing S] [Algebra A S] (x y : S ⊗[A] E), D.D S (1 + x * y) = D.D S (1 + y * x) := by
  intro n A E _ _ _ D S _ _ x y
  let i : S →ₐ[A] S[X] := IsScalarTower.toAlgHom A S S[X]
  let ι := Algebra.TensorProduct.map i (AlgHom.id A E)
  let ev : S → (S[X] →ₐ[A] S) := fun c => (Polynomial.aeval c : S[X] →ₐ[S] S).restrictScalars A
  let π := fun c => Algebra.TensorProduct.map (ev c) (AlgHom.id A E)
  have hπι : ∀ c z, π c (ι z) = z := by
    intro c z
    induction z with
    | tmul s e => simp [π, ι, ev, i]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  let t : S[X] ⊗[A] E := X ⊗ₜ 1
  have ht : ∀ c, π c t = c ⊗ₜ 1 := by
    intro c
    simp [π, t, ev]
  let u : S[X] ⊗[A] E := 1 + t * ι (x - 1)
  have hu0 : π 0 u = 1 := by
    simp only [u, map_add (f := _), map_mul, map_one, hπι, ht]
    simp
  have hu1 : π 1 u = x := by
    simp only [u, map_add (f := _), map_mul, map_one, hπι, ht]
    rw [← Algebra.TensorProduct.one_def]
    simp
  have hc : (D.D S[X] u).coeff 0 = 1 := by
    have h := D.nat S[X] S (ev 0) u
    change D.D S (π 0 u) = _ at h
    rw [hu0, map_one] at h
    rw [h]
    simp [ev, Polynomial.coeff_zero_eq_eval_zero]
  have hnz : D.D S[X] u ∈ nonZeroDivisors S[X] :=
    Polynomial.mem_nonzeroDivisors_of_coeff_mem 0 (by rw [hc]; exact one_mem _)
  have key : D.D S[X] (1 + u * ι y) = D.D S[X] (1 + ι y * u) := by
    have h : (1 + u * ι y) * u = u * (1 + ι y * u) := by noncomm_ring
    have h2 := congrArg (D.D S[X]) h
    rw [map_mul, map_mul, mul_comm (D.D S[X] u)] at h2
    exact (mul_cancel_right_mem_nonZeroDivisors hnz).1 h2
  have h := congrArg (ev 1) key
  rw [← D.nat, ← D.nat] at h
  change D.D S (π 1 _) = D.D S (π 1 _) at h
  simpa only [map_add (f := _), map_mul, map_one, hπι, hu1] using h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPoly
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem aeval_X_mul_C_X_monomial {A ι : Type} [CommRing A] (d : ι →₀ ℕ) (c : A) :
    MvPolynomial.aeval (fun a => (X * C (MvPolynomial.X a) : (MvPolynomial ι A)[X])) (MvPolynomial.monomial d c) =
      X ^ (Finsupp.degree d) * C (MvPolynomial.monomial d c) := by
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul, map_prod,
    map_pow, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  rw [show Finsupp.degree d = ∑ i ∈ d.support, d i from rfl]
  ring

private theorem scale_coeff {A ι : Type} [CommRing A] (P : MvPolynomial ι A) (k : ℕ) :
    (MvPolynomial.aeval (fun a => (X * C (MvPolynomial.X a) : (MvPolynomial ι A)[X])) P).coeff k =
      MvPolynomial.homogeneousComponent k P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [aeval_X_mul_C_X_monomial, Polynomial.coeff_X_pow_mul',
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c rfl), Polynomial.coeff_C]
    split_ifs <;> first | rfl | omega
  | add p q hp hq => rw [map_add (f := _), Polynomial.coeff_add, hp, hq, map_add (f := _)]

theorem UpperTheory.V.CA.d_poly :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {ι : Type} [Fintype ι] (x : ι → E), (D.poly x).IsHomogeneous n ∧ ∀ (S : Type) [CommRing S] [Algebra A S] (s : ι → S), D.D S (∑ a, s a ⊗ₜ x a) = MvPolynomial.aeval s (D.poly x) := by
  intro n A E _ _ _ D ι _ x
  have key : ∀ (S : Type) [CommRing S] [Algebra A S] (f : MvPolynomial ι A →ₐ[A] S),
      D.D S (∑ a, f (MvPolynomial.X a) ⊗ₜ x a) = f (D.poly x) := by
    intro S _ _ f
    rw [Det.poly, ← D.nat]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Det.gen, map_sum]
  refine ⟨?_, fun S _ _ s => by simpa using key S (MvPolynomial.aeval s)⟩
  let g : MvPolynomial ι A →ₐ[A] (MvPolynomial ι A)[X] := MvPolynomial.aeval fun a => X * C (MvPolynomial.X a)
  let t : MvPolynomial ι A →ₐ[A] (MvPolynomial ι A)[X] := IsScalarTower.toAlgHom A (MvPolynomial ι A) (MvPolynomial ι A)[X]
  have h1 := key _ g
  have h3 := key _ t
  have h2 : (∑ a, g (MvPolynomial.X a) ⊗ₜ[A] x a) = (X : (MvPolynomial ι A)[X]) • ∑ a, t (MvPolynomial.X a) ⊗ₜ[A] x a := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp [g, t]
  rw [h2, D.homog, h3] at h1
  have hc := congrArg (fun p : (MvPolynomial ι A)[X] => p.coeff n) h1
  simp only [g, t, scale_coeff, IsScalarTower.coe_toAlgHom', Polynomial.coeff_X_pow_mul', le_refl, if_true,
    Nat.sub_self] at hc
  have hP : MvPolynomial.homogeneousComponent n (D.poly x) = D.poly x := by
    rw [← hc]
    simp
  exact hP ▸ MvPolynomial.homogeneousComponent_isHomogeneous n _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DIdemRank
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem determinant_evaluation_aeval {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E)
    (B : Type) [CommRing B] [Algebra A B] (b : B) :
    D.D B (1 + (b - 1) ⊗ₜ e) = aeval b (D.D A[X] (1 + (X - 1) ⊗ₜ e)) := by
  rw [← D.nat]
  congr 1
  simp

private theorem coeff_aeval_C_mul_X' {A : Type} [CommRing A] (P : A[X]) (a : A[X]) (j : ℕ) :
    (aeval (Polynomial.C a * Polynomial.X : A[X][X]) P).coeff j = Polynomial.C (P.coeff j) * a ^ j := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, map_add (f := _), add_mul]
  | monomial i c =>
    have e1 : aeval (Polynomial.C a * Polynomial.X : A[X][X]) (monomial i c) =
        Polynomial.C (Polynomial.C c * a ^ i) * Polynomial.X ^ i := by
      rw [aeval_monomial, mul_pow, ← Polynomial.C_pow, Polynomial.algebraMap_apply, Polynomial.algebraMap_apply]
      simp [mul_assoc]
    rw [e1, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_monomial]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]

private theorem aeval_C_X_eq_C {A : Type} [CommRing A] (P : A[X]) :
    aeval (Polynomial.C (X : A[X]) : A[X][X]) P = Polynomial.C P := by
  have := Polynomial.aeval_algHom_apply (Polynomial.CAlgHom (R := A) (A := A[X])) (X : A[X]) P
  simpa [Polynomial.aeval_X_left_apply] using this

private theorem pow_aux {n : ℕ} {A E : Type} [CommRing A] [IsLocalRing A] [Ring E] [Algebra A E]
    (D : Det n A E) (e : E) (he : IsIdempotentElem e) :
    ∃ r, D.D A[X] (1 + (X - 1) ⊗ₜ e) = X ^ r := by
  set P := D.D A[X] (1 + (X - 1) ⊗ₜ e) with hP
  have ev : ∀ (B : Type) [CommRing B] [Algebra A B] (b : B), aeval b P = D.D B (1 + (b - 1) ⊗ₜ e) :=
    fun B _ _ b => (determinant_evaluation_aeval D e B b).symm
  have mul : ∀ (B : Type) [CommRing B] [Algebra A B] (s t : B), aeval (s * t) P = aeval s P * aeval t P := by
    intro B _ _ s t
    rw [ev, ev, ev, ← map_mul]
    congr 1
    have key : ∀ u v : B, (1 + u ⊗ₜ[A] e : B ⊗[A] E) * (1 + v ⊗ₜ[A] e) = 1 + (u + v + u * v) ⊗ₜ[A] e := by
      intro u v
      simp only [mul_add, add_mul, one_mul, mul_one, Algebra.TensorProduct.tmul_mul_tmul, he.eq, add_tmul]
      abel
    rw [key]
    congr 2
    ring
  have hcoef : ∀ j, Polynomial.C (P.coeff j) * X ^ j = P * Polynomial.C (P.coeff j) := by
    intro j
    have hm := mul A[X][X] (Polynomial.C X) Polynomial.X
    have h1 : (Polynomial.X : A[X][X]) = Polynomial.C 1 * Polynomial.X := by simp
    have cj := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q j) hm
    rw [coeff_aeval_C_mul_X', aeval_C_X_eq_C, Polynomial.coeff_C_mul, h1, coeff_aeval_C_mul_X', one_pow, mul_one] at cj
    exact cj
  have h1 : P.eval 1 = 1 := by
    have := ev A 1
    rw [sub_self, zero_tmul, add_zero, map_one] at this
    rw [← Polynomial.coe_aeval_eq_eval]
    exact this
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (P.coeff j) := by
    by_contra hcon
    push_neg at hcon
    have hmem : P.eval 1 ∈ maximalIdeal A := by
      rw [Polynomial.eval_eq_sum_range]
      refine Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_right _ _ ?_)
      exact (mem_maximalIdeal _).2 (hcon i)
    rw [h1] at hmem
    exact (mem_maximalIdeal _).1 hmem isUnit_one
  refine ⟨j, ?_⟩
  have hu : IsUnit (Polynomial.C (P.coeff j)) := hj.map Polynomial.C
  apply hu.mul_left_cancel
  rw [hcoef j, mul_comm]

theorem UpperTheory.V.CA.d_idem_rank :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [IsLocalRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E), IsIdempotentElem e → ∃ r ≤ n, D.D A[X] (1 + X ⊗ₜ e) = (1 + X) ^ r := by
  intro n A E _ _ _ _ D e he
  obtain ⟨r, hr⟩ := pow_aux D e he
  obtain ⟨r', hr'⟩ := pow_aux D (1 - e) he.one_sub
  refine ⟨r, ?_, ?_⟩
  · have hz : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
    have step : ∀ a : A[X], (1 + a ⊗ₜ[A] (1 - e) : A[X] ⊗[A] E) * (1 + a ⊗ₜ[A] e) = 1 + a ⊗ₜ[A] (1 : E) := by
      intro a
      rw [mul_add, add_mul, add_mul, one_mul, one_mul, mul_one, Algebra.TensorProduct.tmul_mul_tmul, hz,
        tmul_zero, add_zero, add_assoc, ← tmul_add, sub_add_cancel]
    have key : (1 + (X - 1) ⊗ₜ[A] (1 - e) : A[X] ⊗[A] E) * (1 + (X - 1) ⊗ₜ[A] e) =
        (X : A[X]) • (1 : A[X] ⊗[A] E) := by
      rw [step, Algebra.TensorProduct.one_def, ← add_tmul, add_sub_cancel, TensorProduct.smul_tmul', smul_eq_mul,
        mul_one]
    have h2 := congrArg (D.D A[X]) key
    rw [map_mul, hr, hr', D.homog, map_one, mul_one, ← pow_add] at h2
    have h3 := congrArg Polynomial.natDegree h2
    rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at h3
    omega
  · have h4 := determinant_evaluation_aeval D e A[X] (1 + X)
    have h5 : (1 + X : A[X]) - 1 = X := by ring
    rw [h5, hr, map_pow, aeval_X] at h4
    exact h4
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CplIs
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private lemma mem_pow_iff (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (x : AdicCompletion (maximalIdeal L) L) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n ↔
      AdicCompletion.eval (maximalIdeal L) L n x = 0 := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem L,
    ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal L).fg_of_isNoetherianRing]
  rfl

private lemma strict_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (a : L) (h : algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n) : a ∈ maximalIdeal L ^ n := by
  rw [mem_pow_iff, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h
  have h' : Submodule.Quotient.mk (p := (maximalIdeal L ^ n • ⊤ : Submodule L L)) a = 0 := by
    simpa [AdicCompletion.eval] using h
  rw [Submodule.Quotient.mk_eq_zero] at h'
  simpa using h'

private lemma dense_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (b : AdicCompletion (maximalIdeal L) L) :
    ∃ a : L, b - algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal L) L n b)
  refine ⟨a, ?_⟩
  rw [mem_pow_iff, map_sub, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, sub_eq_zero, ← ha]
  simp [AdicCompletion.eval]

theorem UpperTheory.V.CA.cpl_is :
    ∀ (C : Type) [CommRing C] [IsNoetherianRing C] (x : Ideal C) [x.IsMaximal], ∃ _ : IsLocalRing (Cpl x), IsCplAt x (Cpl x) := by
  intro C _ _ x hx
  refine ⟨inferInstance, ?_⟩
  have hL : ∀ (n : ℕ) (a : Localization.AtPrime x),
      a ∈ maximalIdeal (Localization.AtPrime x) ^ n →
      algebraMap (Localization.AtPrime x) (Cpl x) a ∈ maximalIdeal (Cpl x) ^ n := by
    intro n a ha
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  refine
    { noeth := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
      complete := inferInstance
      comap_pow := fun n => ?_
      dense := fun n r => ?_ }
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [IsScalarTower.algebraMap_eq C (Localization.AtPrime x) (Cpl x), ← Ideal.comap_comap]
    have e : Ideal.comap (algebraMap (Localization.AtPrime x) (Cpl x)) (maximalIdeal (Cpl x) ^ n) =
        maximalIdeal (Localization.AtPrime x) ^ n := by
      ext a
      exact ⟨strict_loc _ n a, hL n a⟩
    rw [e, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    refine IsLocalization.under_map_of_isPrimary_disjoint x.primeCompl (Localization.AtPrime x) ?_ ?_
    · apply Ideal.isPrimary_of_isMaximal_radical
      rw [Ideal.radical_pow _ hn.ne', (inferInstance : x.IsPrime).radical]
      infer_instance
    · exact Set.disjoint_left.mpr fun s hs hs' => hs (Ideal.pow_le_self hn.ne' hs')
  · obtain ⟨a, ha⟩ := dense_loc _ n r
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective x.primeCompl a
    have hsx : Ideal.span {(s : C)} ⊔ x = ⊤ := by
      rw [sup_comm]
      have hm : (s : C) ∈ x ⊔ Ideal.span {(s : C)} :=
        Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
      refine hx.out.2 _ (lt_of_le_of_ne le_sup_left fun e => s.2 ?_)
      rwa [← e] at hm
    have h1 : (1 : C) ∈ Ideal.span {(s : C)} ⊔ x ^ n := by
      rw [Ideal.sup_pow_eq_top hsx]
      trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    refine ⟨c * t, ?_⟩
    have key : IsLocalization.mk' (Localization.AtPrime x) c s - algebraMap C _ (c * t) =
        IsLocalization.mk' (Localization.AtPrime x) c s * algebraMap C _ z := by
      have hs := IsLocalization.mk'_spec (Localization.AtPrime x) c s
      have hz' : z = 1 - t * s := by
        rw [← hyz]
        ring
      rw [hz', map_sub, map_one, map_mul, map_mul, ← hs]
      ring
    have hmem : IsLocalization.mk' (Localization.AtPrime x) c s - algebraMap C _ (c * t) ∈
        maximalIdeal (Localization.AtPrime x) ^ n := by
      rw [key, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hz)
    have hsum := Ideal.add_mem _ ha (hL n _ hmem)
    rw [map_sub, ← IsScalarTower.algebraMap_apply C (Localization.AtPrime x) (Cpl x)] at hsum
    convert hsum using 1
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GDimcpl
open IsLocalRing

theorem UpperTheory.V.CA.g_dimcpl :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
      ringKrullDim (AdicCompletion (maximalIdeal R) R) = ringKrullDim R := by
  intro R _ _ _
  haveI := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion R (maximalIdeal R)
  have hm := AdicCompletion.maximalIdeal_eq_map (R := R)
  haveI : (maximalIdeal (AdicCompletion (maximalIdeal R) R)).LiesOver (maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal.isMaximal R).eq_of_le Ideal.IsPrime.ne_top'
      (Ideal.map_le_iff_le_comap.mp hm.ge)⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R)
    (maximalIdeal (AdicCompletion (maximalIdeal R) R))
  rw [← hm, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at h
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetMap
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_toDet_map :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (B : Type) [CommRing B] [Algebra A B], (D.map (algebraMap A B)).toDet = (D.toDet.baseChange B).pull (toT A G B) := by
  intro n A G _ _ D B _ _
  refine Det.ext' fun S _ _ x => ?_
  letI : Algebra A S := ((algebraMap B S).comp (algebraMap A B)).toAlgebra
  haveI : IsScalarTower A B S := .of_algebraMap_eq fun _ => rfl
  have h : ofT B G S x = ofT A G S (Det.cancel A (MonoidAlgebra A G) B S
      (Algebra.TensorProduct.map (AlgHom.id S S) (toT A G B) x)) := by
    induction x with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul s y =>
      induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
      | single g b =>
        rw [Algebra.TensorProduct.map_tmul, toT_single, Det.cancel_tmul, ofT_tmul, ofT_tmul,
          MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single]
        simp
  exact congrArg (D.D S) h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DKillsPoly
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_kills_poly :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E) (M : Set E), Submodule.span A M = ⊤ → (∀ (k : ℕ) (h : Fin k → E), (∀ a, h a ∈ M) → D.D (MvPolynomial (Fin k) A) (1 + Det.gen h * (1 ⊗ₜ x)) = 1) → D.Kills x := by
  intro n A E _ _ _ D x M hM H B _ _ h
  have key : ∀ e : E, ((1 : B) ⊗ₜ[A] e) ∈ Submodule.span B ((fun m : E => (1 : B) ⊗ₜ[A] m) '' M) := by
    intro e
    have he : e ∈ Submodule.span A M := hM ▸ Submodule.mem_top
    induction he using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [tmul_add]; exact add_mem ha hb
    | smul a y _ hy =>
      rw [tmul_smul, ← algebraMap_smul B]
      exact Submodule.smul_mem _ _ hy
  have hh : h ∈ Submodule.span B ((fun m : E => (1 : B) ⊗ₜ[A] m) '' M) := by
    induction h with
    | add a b ha hb => exact add_mem ha hb
    | tmul b e =>
      have : b ⊗ₜ[A] e = b • ((1 : B) ⊗ₜ[A] e) := by simp [smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (key e)
  obtain ⟨k, f, g, rfl⟩ := Submodule.mem_span_set'.1 hh
  choose m hm hmg using fun i => (g i).2
  have h1 := D.nat _ B (MvPolynomial.aeval f) (1 + Det.gen m * (1 ⊗ₜ x))
  rw [H k m hm, map_one] at h1
  refine Eq.trans (congrArg _ ?_) h1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Det.gen, map_add (f := _), map_mul, map_one, map_sum, Algebra.TensorProduct.map_tmul, MvPolynomial.aeval_X,
    AlgHom.id_apply, ← hmg, smul_tmul', smul_eq_mul, mul_one]
end
