module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.GenAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TraceIntegralSubringExtension

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.ImportsTer
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.Msp
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.msp :
    ∀ (O B κ : Type) [CommRing O] [CommRing B] [Algebra O B] [Fintype κ] (n : ℕ) (x : B →ₐ[O] O) (P : κ → Polynomial B) (α : κ → Fin n → O), (∀ j, (P j).map (x : B →+* O) = ∏ i, (Polynomial.X - Polynomial.C (α j i))) → ∀ a : MvPolynomial (κ × Fin n) B, MvPolynomial.eval₂ (x : B →+* O) (fun p => α p.1 p.2) a = 0 → Ideal.Quotient.mk (mSplitIdeal P n) ((∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) * a) ∈ (RingHom.ker x).map (algebraMap B (MSplitAlg P n)) := by
  intro O B κ _ _ _ _ n x P α hP a ha
  classical
  set J : Ideal (MSplitAlg P n) := (RingHom.ker x).map (algebraMap B (MSplitAlg P n)) with hJ
  let ψ : MvPolynomial (κ × Fin n) B →+* (MSplitAlg P n ⧸ J) :=
    (Ideal.Quotient.mk J).comp (Ideal.Quotient.mk (mSplitIdeal P n))
  let g : B →+* (MSplitAlg P n ⧸ J) := ψ.comp MvPolynomial.C
  let h : O →+* (MSplitAlg P n ⧸ J) := g.comp (algebraMap O B)
  have hg : ∀ b : B, g b = (Ideal.Quotient.mk J) (algebraMap B (MSplitAlg P n) b) := by
    intro b
    show (Ideal.Quotient.mk J) ((Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.C b)) = _
    rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
  have hgx : g = h.comp (x : B →+* O) := by
    ext b
    show g b = g (algebraMap O B (x b))
    rw [← sub_eq_zero, ← map_sub, hg, Ideal.Quotient.eq_zero_iff_mem]
    apply Ideal.mem_map_of_mem
    rw [RingHom.mem_ker]
    simp
  have hg' : (Ideal.Quotient.mk J).comp (algebraMap B (MSplitAlg P n)) = h.comp (x : B →+* O) := by
    rw [← hgx]
    ext b
    exact (hg b).symm
  have hroot : ∀ j i, ∏ k, (ψ (MvPolynomial.X (j, i)) - h (α j k)) = 0 := by
    intro j i
    have e := MSplitAlg.prod_root P n j
    have e2 := congrArg (fun q => Polynomial.eval (ψ (MvPolynomial.X (j, i))) (q.map (Ideal.Quotient.mk J))) e
    rw [Polynomial.map_map, hg', ← Polynomial.map_map, hP j] at e2
    simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at e2
    rw [← e2]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)
  have hh : ∀ c : O, ψ (MvPolynomial.C (algebraMap O B c)) = h c := fun _ => rfl
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change ψ (_ * a) = 0
  rw [map_mul]
  set δ := ψ (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
    (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) with hδ
  have hδX : ∀ p : κ × Fin n, δ * (ψ (MvPolynomial.X p) - h (α p.1 p.2)) = 0 := by
    rintro ⟨j, i⟩
    obtain ⟨q, hq⟩ : (∏ k ∈ Finset.univ.erase i,
        (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k))) : MvPolynomial (κ × Fin n) B) ∣
        ∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k))) :=
      (Finset.dvd_prod_of_mem (fun i => ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) (Finset.mem_univ i)).trans
        (Finset.dvd_prod_of_mem (fun j => ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) (Finset.mem_univ j))
    rw [hδ, hq, map_mul, mul_right_comm]
    simp only [map_prod, map_sub, hh]
    rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i), hroot, zero_mul]
  have key : ∀ b : MvPolynomial (κ × Fin n) B,
      δ * (ψ b - h (MvPolynomial.eval₂ (x : B →+* O) (fun p => α p.1 p.2) b)) = 0 := by
    intro b
    refine MvPolynomial.induction_on
      (motive := fun b => δ * (ψ b - h (MvPolynomial.eval₂ (x : B →+* O) (fun p => α p.1 p.2) b)) = 0)
      b ?_ ?_ ?_
    · intro c
      have hc : ψ (MvPolynomial.C c) = h ((x : B →+* O) c) := by
        show g c = _
        rw [hgx]
        rfl
      rw [MvPolynomial.eval₂_C, hc, sub_self, mul_zero]
    · intro p q hp hq
      rw [map_add (f := _), MvPolynomial.eval₂_add, map_add (f := _)]
      linear_combination hp + hq
    · intro p v hp
      rw [map_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul]
      beta_reduce
      linear_combination (ψ (MvPolynomial.X v)) * hp +
        h (MvPolynomial.eval₂ (x : B →+* O) (fun p => α p.1 p.2) p) * hδX v
  have hk := key a
  rw [ha, map_zero, sub_zero] at hk
  exact hk
end

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.kill :
    ∀ (O R B M V : Type) [CommRing O] [CommRing R] [CommRing B] [Algebra O R] [Algebra O B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →ₐ[O] B) (x : B →ₐ[O] O) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (f : PU R q n) (α : Fin q → Fin n → O) (I : Ideal R) (t₀ : R), Function.Surjective β → TwoMaps (M := M) β.toRingHom P act f → (∀ j, (P j).map (x : B →+* O) = ∏ i, (Polynomial.X - Polynomial.C (α j i))) → (∀ a : B, x a = 0 → ∀ m : M, (β t₀ * a) • m ∈ (I.map β • ⊤ : Submodule B M)) → ∀ a : PU R q n, MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) a = 0 → ∀ v : V, act (MvPolynomial.C t₀ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))) * f * a) v ∈ (I • ⊤ : Submodule R V) := by
  intro O R B M V _ _ _ _ _ _ _ _ _ q n β x P act f α I t₀ hβ hTM hP hker a ha v
  obtain ⟨φ, ψ, h1, h2, h3, h4⟩ := hTM
  have hπC : ∀ b : B, (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.C b) =
      algebraMap B (MSplitAlg P n) b := fun b => rfl
  have key : ∀ i ∈ I, ∀ w : MSplitAlg P n ⊗[B] M, φ ((β i) • w) ∈ (I • ⊤ : Submodule R V) := by
    intro i hi w
    have e1 : (β i) • w = (Ideal.Quotient.mk (mSplitIdeal P n))
        ((MvPolynomial.map β.toRingHom) (MvPolynomial.C i)) • w := by
      rw [MvPolynomial.map_C, hπC, algebraMap_smul]
      rfl
    rw [e1, h1, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply]
    exact Submodule.smul_mem_smul hi trivial
  have claim : ∀ b : B, x b = 0 → ∀ z : MSplitAlg P n ⊗[B] M,
      φ (algebraMap B (MSplitAlg P n) (β t₀ * b) • z) ∈ (I • ⊤ : Submodule R V) := by
    intro b hb z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
      rw [algebraMap_smul, ← TensorProduct.tmul_smul]
      refine Submodule.smul_induction_on (p := fun y => φ (s ⊗ₜ[B] y) ∈ (I • ⊤ : Submodule R V))
        (hker b hb m) ?_ ?_
      · intro r hr m' _
        obtain ⟨i, hi, rfl⟩ := (Ideal.mem_map_iff_of_surjective β hβ).mp hr
        rw [TensorProduct.tmul_smul]
        exact key i hi _
      · intro y1 y2 k1 k2
        rw [TensorProduct.tmul_add, map_add (f := _)]
        exact add_mem k1 k2
    | add z1 z2 k1 k2 =>
      rw [smul_add, map_add (f := _)]
      exact add_mem k1 k2
  have gen : ∀ y ∈ Ideal.map (algebraMap B (MSplitAlg P n)) (RingHom.ker x), ∀ z : MSplitAlg P n ⊗[B] M,
      φ ((algebraMap B (MSplitAlg P n) (β t₀) * y) • z) ∈ (I • ⊤ : Submodule R V) := by
    intro y hy
    unfold Ideal.map at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      intro z
      rw [← map_mul]
      exact claim b (RingHom.mem_ker.mp hb) z
    | zero => intro z; simp
    | add y1 y2 _ _ k1 k2 =>
      intro z
      rw [mul_add, add_smul, map_add (f := _)]
      exact add_mem (k1 z) (k2 z)
    | smul r y _ k =>
      intro z
      rw [smul_eq_mul, mul_left_comm, mul_comm r, mul_smul]
      exact k _
  have hE : MvPolynomial.map β.toRingHom (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
      (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k))) : PU R q n) =
      ∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
      (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k))) := by
    simp [map_prod]
  have hmem := Sp.msp O B (Fin q) n x P α hP (MvPolynomial.map β.toRingHom a)
    (by rw [MvPolynomial.eval₂_map]; exact ha)
  have e3 : act (MvPolynomial.C t₀ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
      (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))) * f * a) v =
      φ (((Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom (MvPolynomial.C t₀ *
        (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))))) *
        (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom a)) • ψ v) := by
    rw [mul_smul, ← h2, h1, h3]
    simp only [map_mul, Module.End.mul_apply]
  rw [e3]
  have e4 : (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom (MvPolynomial.C t₀ *
        (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O R (α j k)))))) *
        (Ideal.Quotient.mk (mSplitIdeal P n)) (MvPolynomial.map β.toRingHom a) =
      algebraMap B (MSplitAlg P n) (β t₀) * (Ideal.Quotient.mk (mSplitIdeal P n))
        ((∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O B (α j k)))) *
          MvPolynomial.map β.toRingHom a) := by
    rw [map_mul (MvPolynomial.map β.toRingHom), hE, MvPolynomial.map_C, ← hπC, ← map_mul, ← map_mul,
      mul_assoc]
    rfl
  rw [e4]
  exact gen _ hmem _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.RepSingle
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.TracePartialCharpolySingle
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem UpperTheory.V.Th.Sp.trace_partial_charpoly_single {T G : Type} [CommRing T] [Group G] (t : MonoidAlgebra T G →ₗ[T] T)
    (g ta : G) (a y : T) :
    t (MonoidAlgebra.single g a * (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 y)) =
      a * (t (MonoidAlgebra.single (g * ta) 1) - t (MonoidAlgebra.single g 1)) -
        y * (a * t (MonoidAlgebra.single g 1)) := by
  have h : ∀ (k : G) (b : T), t (MonoidAlgebra.single k b) = b * t (MonoidAlgebra.single k 1) := fun k b => by
    rw [← smul_eq_mul, ← map_smul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [mul_sub, mul_sub, mul_one, MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one,
    map_sub, map_sub, h (g * ta) a, h g a, h g (a * y)]
  ring

theorem UpperTheory.V.Th.Sp.q2 :
    ∀ (O T G X : Type) [CommRing O] [CommRing T] [Algebra O T] [Group G] [AddCommGroup X] [Module O X] (n : ℕ) (D : GDet n T G) (x : T →ₐ[O] O) (del : T →ₗ[O] X) (ta : G) (y : T) (Q : MonoidAlgebra T G), 1 ≤ n → IsDer x del → x y = 0 → (∀ g, x (D.tr (MonoidAlgebra.single (g * ta) 1)) = x (D.tr (MonoidAlgebra.single g 1))) → x (D.tr (Q * (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 y))) = 0 ∧ del (D.tr (Q * (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 y))) = del (D.tr (MonoidAlgebra.mapRingHom G ((algebraMap O T).comp (x : T →+* O)) Q * (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 0))) - x (D.tr Q) • del y := by
  intro O T G X _ _ _ _ _ _ n D x del ta y Q hn hd hy hta
  obtain ⟨t, ht⟩ := (UpperTheory.V.CA.d_tr D.toDet).1 hn
  have ht' : ∀ z, D.tr z = t z := fun z => by rw [ht, (UpperTheory.V.CA.d_toDet D z).2.2.1]
  simp only [ht'] at hta ⊢
  induction Q using MonoidAlgebra.induction_linear with
  | zero => simp
  | add P Q hP hQ =>
    simp only [map_add (f := _), add_mul, hP.1, hQ.1, hP.2, hQ.2, add_zero, true_and, add_smul]
    abel
  | single g a =>
    have h : t (MonoidAlgebra.single g a) = a * t (MonoidAlgebra.single g 1) := by
      rw [← smul_eq_mul, ← map_smul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [MonoidAlgebra.mapRingHom_single, UpperTheory.V.Th.Sp.trace_partial_charpoly_single, UpperTheory.V.Th.Sp.trace_partial_charpoly_single, h]
    have h0 : x (t (MonoidAlgebra.single (g * ta) 1) - t (MonoidAlgebra.single g 1)) = 0 := by
      rw [map_sub, hta, sub_self]
    refine ⟨by rw [map_sub, map_mul, map_mul, h0, hy, mul_zero, zero_mul, sub_zero], ?_⟩
    rw [map_sub, hd, hd, h0, hy, zero_smul, zero_smul, add_zero, zero_add, zero_mul, sub_zero, RingHom.comp_apply,
      ← Algebra.smul_def, map_smul]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.TrPoly
open IsLocalRing Polynomial

theorem UpperTheory.V.Th.Sp.trp :
    ∀ (O : Type) [CommRing O] [IsDomain O] (n : ℕ) (A : Matrix (Fin n) (Fin n) O) (α : Fin n → O) (p : O[X]), A.charpoly = ∏ i, (X - C (α i)) → (aeval A p).trace = ∑ i, p.eval (α i) := by
  intro O _ _ n A α p h
  let K := AlgebraicClosure (FractionRing O)
  let f : O →+* K := (algebraMap (FractionRing O) K).comp (algebraMap O (FractionRing O))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing O) K).injective.comp (IsFractionRing.injective O (FractionRing O))
  apply hf
  have htr : ∀ M : Matrix (Fin n) (Fin n) O, f M.trace = (M.map f).trace := by
    intro M
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, map_sum]
  have haeval : (aeval A p).map f = aeval (A.map f) (p.map f) := by
    have := Polynomial.map_aeval_eq_aeval_map (φ := f) (ψ := f.mapMatrix) ?_ p A
    · simpa using this
    · ext c i j
      simp [Matrix.algebraMap_matrix_apply]
      split_ifs <;> simp
  have hchar : (A.map f).charpoly = ((Finset.univ.val.map fun i => f (α i)).map fun a => X - C a).prod := by
    rw [Matrix.charpoly_map, h, Polynomial.map_prod]
    simp [Finset.prod_eq_multiset_prod, Multiset.map_map, Function.comp_def]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [htr, haeval, GlobalTheory.CompanionTheory.TraceSpec.trace_aeval_matrix, hchar, Polynomial.roots_multiset_prod_X_sub_C, map_sum]
  simp [Multiset.map_map, Finset.sum_eq_multiset_sum, Function.comp_def]
end

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem tr_map {R S G : Type} [CommRing R] [CommRing S] [Group G] {n : ℕ} (D : GDet n R G)
    (f : R →+* S) (z : MonoidAlgebra R G) :
    (D.map f).tr (MonoidAlgebra.mapRingHom G f z) = f (D.tr z) :=
  ((UpperTheory.V.CA.d_gmap D).2.2.1 f z).2 1

private theorem tr_rep {R G : Type} [CommRing R] [Group G] {n : ℕ} (hn : 1 ≤ n) (ρ : G →* Matrix (Fin n) (Fin n) R)
    (z : MonoidAlgebra R G) : (GDet.ofRep ρ).tr z = (GDet.repAlg ρ R z).trace := by
  have h : (GDet.ofRep ρ).chi z = (GDet.repAlg ρ R z).charpoly := by
    change (GDet.repAlg ρ (Polynomial R) _).det = Matrix.det _
    congr 1
    rw [map_sub, Matrix.charmatrix]
    congr 1
    · ext i j : 2
      simp [GDet.repAlg, Matrix.one_apply, Matrix.diagonal_apply]
    · induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | single g r => ext i j : 2; simp [GDet.repAlg]
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [GDet.tr, GDet.lam, h, Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
  simp

private theorem rep_single {R G : Type} [CommRing R] [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) R) (g : G) (a : R) :
    GDet.repAlg ρ R (MonoidAlgebra.single g a) = a • ρ g := by
  ext i j; simp [GDet.repAlg]

private theorem rep_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (φ : H →* G) :
    (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ) := by
  refine GDet.ext fun B _ _ x => ?_
  change (GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ x)).det = (GDet.repAlg (ρ.comp φ) B x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => simp [GDet.repAlg]

private noncomputable def qq {R G : Type} [CommRing R] [Group G] {n : ℕ} (E : ℕ) (ph : G) (u : Fin n → R) (i : Fin n) :
    MonoidAlgebra R G :=
  (List.ofFn fun k => if k = i then 1 else MonoidAlgebra.single ph (1 : R) - MonoidAlgebra.single 1 (u k)).prod ^ (E + 1)

private theorem qq_map {R S G : Type} [CommRing R] [CommRing S] [Group G] {n : ℕ} (f : R →+* S) (E : ℕ) (ph : G)
    (u : Fin n → R) (i : Fin n) :
    MonoidAlgebra.mapRingHom G f (qq E ph u i) = qq E ph (fun k => f (u k)) i := by
  simp [qq, map_list_prod, List.map_ofFn, Function.comp_def, apply_ite (MonoidAlgebra.mapRingHom G f)]

private theorem qq_tr {O G : Type} [CommRing O] [IsDomain O] [Group G] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) O) (E : ℕ) (ph : G)
    (α : Fin n → O) (i : Fin n) (h : (ρ ph).charpoly = ∏ k, (Polynomial.X - Polynomial.C (α k))) :
    (GDet.ofRep ρ).tr (qq E ph α i) = (∏ k ∈ Finset.univ.erase i, (α i - α k)) ^ (E + 1) := by
  have e : GDet.repAlg ρ O (qq E ph α i) = Polynomial.aeval (ρ ph)
      ((∏ k, if k = i then 1 else (Polynomial.X - Polynomial.C (α k))) ^ (E + 1)) := by
    rw [qq, map_pow, map_pow, ← List.prod_ofFn, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    congr 3
    funext k
    by_cases hk : k = i <;> simp [hk, rep_single, Algebra.algebraMap_eq_smul_one]
  rw [tr_rep (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) i.2)), e, Sp.trp O n _ α _ h,
    Finset.sum_eq_single i]
  · rw [Polynomial.eval_pow, Polynomial.eval_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), if_pos rfl,
      Polynomial.eval_one, mul_one]
    congr 1
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [if_neg (Finset.mem_erase.1 hk).1]
    simp
  · intro a _ ha
    rw [Polynomial.eval_pow, Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha]), zero_pow E.succ_ne_zero]
  · exact fun h => (h (Finset.mem_univ _)).elim

private theorem core {O R T G X : Type} [CommRing O] [IsDomain O] [CommRing R] [CommRing T] [Algebra O R] [Algebra O T] [Group G]
    [AddCommGroup X] [Module O X] {n : ℕ} (D : GDet n R G) (c : R →+* T) (hc : ∀ a, c (algebraMap O R a) = algebraMap O T a)
    (x : T →ₐ[O] O) (del : T →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (hD : D.map ((x : T →+* O).comp c) = GDet.ofRep ρ)
    (ph ta : G) (α : Fin n → O) (E : ℕ) (i : Fin n) (u : Fin n → T) (y : T) (hn : 1 ≤ n) (hta : ρ ta = 1)
    (h : (ρ ph).charpoly = ∏ k, (Polynomial.X - Polynomial.C (α k))) (hu : ∀ k, x (u k) = α k) (hy : x y = 0)
    (hd : IsDer x del) :
    x ((D.map c).tr (twoPowerModulus E ph ta u i y)) = 0 ∧ del ((D.map c).tr (twoPowerModulus E ph ta u i y)) =
      del (c (D.tr (twoPowerModulus E ph ta (fun k => algebraMap O R (α k)) i 0))) -
        (∏ k ∈ Finset.univ.erase i, (α i - α k)) ^ (E + 1) • del y := by
  have hx : ∀ z, x ((D.map c).tr z) = (GDet.ofRep ρ).tr (MonoidAlgebra.mapRingHom G (x : T →+* O) z) := fun z => by
    rw [← hD, ← (UpperTheory.V.CA.d_gmap D).2.1 c (x : T →+* O), tr_map]
    rfl
  obtain ⟨k1, k2⟩ := Sp.q2 O T G X n (D.map c) x del ta y (qq E ph u i) hn hd hy fun g => by
    rw [hx, hx, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single, tr_rep hn, tr_rep hn, rep_single, rep_single,
      map_mul, hta, mul_one]
  refine ⟨k1, k2.trans ?_⟩
  have e1 : (fun k => (x : T →+* O) (u k)) = α := funext hu
  have e2 : MonoidAlgebra.mapRingHom G c (twoPowerModulus E ph ta (fun k => algebraMap O R (α k)) i 0) =
      MonoidAlgebra.mapRingHom G ((algebraMap O T).comp (x : T →+* O)) (qq E ph u i) *
        (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 0) := by
    change MonoidAlgebra.mapRingHom G c (qq E ph _ i * _) = _
    rw [map_mul, qq_map, qq_map]
    congr 1
    · congr 1
      funext k
      rw [hc, ← hu k]
      rfl
    · simp
  rw [← e2, tr_map, hx, qq_map, e1, qq_tr ρ E ph α i h]

theorem UpperTheory.V.Th.Sp.q2op :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 G : Glob l L) (h : G.Hom G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (q N : ℕ) (A : OpMod b h q N) (y : Pt G0.frame O n) (x : B →ₐ[O] O) (ph ta : G.G₀) (α : Fin n → O) (E : ℕ) (j : Fin q) (i : Fin n) (xT : PUY A.R q n →ₐ[O] O) (X : Type) [AddCommGroup X] [Module O X] (del : PUY A.R q n →ₗ[O] X), 1 ≤ n → u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ → h.p₀ ta = 1 → (mat y.ρ (h.p₀ ph)).charpoly = ∏ k, (Polynomial.X - Polynomial.C (α k)) → (∀ s, xT (MvPolynomial.C s) = x (A.β s)) → (∀ k, xT (uV A.R j k) = α k) → xT (yV A.R j i) = 0 → IsDer xT del → xT ((A.p.D.map (MvPolynomial.C : A.R →+* PUY A.R q n)).tr (twoPowerModulus E ph ta (uV A.R j) i (yV A.R j i))) = 0 ∧ del ((A.p.D.map (MvPolynomial.C : A.R →+* PUY A.R q n)).tr (twoPowerModulus E ph ta (uV A.R j) i (yV A.R j i))) = del (MvPolynomial.C (A.p.D.tr (twoPowerModulus E ph ta (fun k => algebraMap O A.R (α k)) i 0))) - (∏ k ∈ Finset.univ.erase i, (α i - α k)) ^ (E + 1) • del (yV A.R j i) := by
  intro l _ L G0 G h n O _ _ _ _ _ r B _ _ _ u J D b q N A y x ph ta α E j i xT X _ _ del hn hmap hta hα hC hu hy hd
  refine core (O := O) (T := PUY A.R q n) A.p.D MvPolynomial.C (fun a => rfl) xT del ((mat y.ρ).comp h.p₀) ?_ ph ta α E i _ _ hn ?_ hα hu hy hd
  · have e : (xT : PUY A.R q n →+* O).comp MvPolynomial.C = x.toRingHom.comp A.β.toRingHom := RingHom.ext hC
    rw [e, ← (UpperTheory.V.CA.d_gmap A.p.D).2.1, A.β_pair.1, ← rep_comap, ← hmap.1]
    rfl
  · rw [MonoidHom.comp_apply, hta, map_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.ImportsFurther
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.trans :
    ∀ (R M W : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup W] [Module R W] (q n : ℕ) (act1 : PUY R q n →ₐ[R] Module.End R M) (actw : PU R q n →ₐ[R] Module.End R W) (tr : M →ₗ[R] W), Function.Surjective tr → LinearMap.ker tr = ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)) → (∀ j i m, tr (act1 (uV R j i) m) = actw (MvPolynomial.X (j, i)) (tr m)) → (∀ τ m, tr (act1 τ m) = actw (MvPolynomial.aeval (Sum.elim MvPolynomial.X 0) τ) (tr m)) ∧ ∀ (I : Ideal R) m, tr m ∈ (I • ⊤ : Submodule R W) → m ∈ (I • ⊤ : Submodule R M) ⊔ ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)) := by
  intro R M W _ _ _ _ _ q n act1 actw tr hsurj hker hu
  have hy : ∀ p : Fin q × Fin n, ∀ m, tr (act1 (yV R p.1 p.2) m) = 0 := by
    intro p m
    rw [← LinearMap.mem_ker, hker]
    exact Submodule.mem_iSup_of_mem p (LinearMap.mem_range_self _ m)
  refine ⟨fun τ => ?_, fun I m hm => ?_⟩
  · induction τ using MvPolynomial.induction_on with
    | C a =>
        intro m
        rw [MvPolynomial.aeval_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes]
        simp
    | add p r hp hr =>
        intro m
        simp [map_add (f := _), hp, hr]
    | mul_X p s hp =>
        intro m
        rcases s with ⟨j, i⟩ | ⟨j, i⟩
        · rw [map_mul, Module.End.mul_apply, hp, map_mul, map_mul, Module.End.mul_apply,
            MvPolynomial.aeval_X, Sum.elim_inl]
          exact congrArg _ (hu j i m)
        · rw [map_mul, Module.End.mul_apply, hp, map_mul, MvPolynomial.aeval_X, Sum.elim_inr,
            show tr (act1 (MvPolynomial.X (Sum.inr (j, i))) m) = 0 from hy (j, i) m]
          simp
  · have htop : (I • ⊤ : Submodule R W) = (I • ⊤ : Submodule R M).map tr := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hsurj]
    rw [htop] at hm
    obtain ⟨m', hm', he⟩ := hm
    have hk : m - m' ∈ ⨆ p : Fin q × Fin n, LinearMap.range (act1 (yV R p.1 p.2)) := by
      rw [← hker, LinearMap.mem_ker, map_sub, he, sub_self]
    have hmm : m = m' + (m - m') := by abel
    rw [hmm]
    exact Submodule.add_mem_sup hm' hk
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.BetaSurj
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem mem_iff {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (y : R) :
    f y ∈ maximalIdeal R' ↔ y ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]

private theorem surj_of_gen {O : Type} [CommRing O] [IsLocalRing O] {R C : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing C] [Algebra O C] [IsCO O C] (f : R →ₐ[O] C) (S : Set C) (hS : GenBy O S)
    (h1 : ∀ b ∈ S, b ∈ f.range) : Function.Surjective f := by
  apply co_surj O R C f
  intro x hx
  obtain ⟨a, ha, hxa⟩ := hS 2 x
  have hrange : Algebra.adjoin O S ≤ f.range := Algebra.adjoin_le (fun b hb => h1 b hb)
  obtain ⟨y, hy⟩ := hrange ha
  have hy' : f y = a := hy
  have hsq : maximalIdeal C ^ 2 ≤ maximalIdeal C := Ideal.pow_le_self (by norm_num)
  have haM : a ∈ maximalIdeal C := by
    have h2 : a = x - (x - a) := by ring
    rw [h2]
    exact sub_mem hx (hsq hxa)
  have hyM : y ∈ maximalIdeal R := by
    rw [← mem_iff f y, hy']
    exact haM
  have hx' : x = f y + (x - a) := by rw [hy']; ring
  rw [hx']
  exact add_mem (Ideal.mem_sup_left (Ideal.mem_map_of_mem f hyM)) (Ideal.mem_sup_right hxa)

private theorem lam_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  simp [GDet.lam, GDet.chi, GDet.comap, Finsupp.mapDomain_sub, MonoidAlgebra.mapDomain,
    Finsupp.mapDomain_single]

private theorem lam_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B)
    (i : ℕ) (g : G) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have h := (CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)
  simpa using h.2 i

private theorem surjective_levelChangeBaseGroupHom {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) :
    Function.Surjective h.p₀ := by
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := h.surj x
  refine ⟨⟨y, ?_⟩, rfl⟩
  rw [MonoidHom.mem_ker, ← h.η y]
  exact hx

theorem UpperTheory.V.Th.Sp.betaSurj :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 G : Glob l L) (h : G.Hom G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (q N : ℕ) (A : OpMod b h q N), GenBy O (pairVals u) → Function.Surjective A.β := by
  intro l _ L G0 G h n O _ _ _ _ _ r B _ _ _ u J D b q N A hgen
  obtain ⟨hD, hψ⟩ := A.β_pair
  refine surj_of_gen A.β _ hgen ?_
  rintro b (⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩)
  · obtain ⟨g, rfl⟩ := surjective_levelChangeBaseGroupHom h g
    refine ⟨A.p.D.lam i (MonoidAlgebra.single g 1), ?_⟩
    have h := lam_map A.p.D A.β.toRingHom i g
    rw [hD, lam_comap] at h
    exact h.symm
  · exact ⟨(A.p.ψ v i g : A.R), congrArg (fun χ => ((χ g : _ˣ) : B)) (hψ v i)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.BetaLam
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.betaLam :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 G : Glob l L) (h : G.Hom G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (q N : ℕ) (A : OpMod b h q N), ∀ a : abelian₂ O Empty D, A.β (algebraMap (abelian₂ O Empty D) A.R a) = b.lam a := by
  intro l _ L G0 G h n O _ _ _ _ _ r B _ _ _ u J D b q N A a
  haveI hOO : IsCO O O :=
    { complete := IsCoef.complete
      isLocalHom := ⟨fun x hx => by simpa using hx⟩
      res_surj := fun x => ⟨x, by simp⟩ }
  haveI hL : IsCO O (abelian₂ O Empty D) := co_mvps O O (Empty ⊕ Fin D)
  have hmax : ∀ s : Empty ⊕ Fin D, b.lam (MvPowerSeries.X s) ∈ maximalIdeal B := by
    intro s
    rw [← res_eq_zero_iff O B, res_map, res_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
    intro hu
    have h0 := hu.map MvPowerSeries.constantCoeff
    simp at h0
  obtain ⟨F, _, huniq⟩ :=
    co_ev O O B (Empty ⊕ Fin D) (Algebra.ofId O B) (fun s => b.lam (MvPowerSeries.X s)) hmax
  let F1 : abelian₂ O Empty D →ₐ[O] B :=
    A.β.comp (IsScalarTower.toAlgHom O (abelian₂ O Empty D) A.R)
  have e1 : F1 = F := by
    apply huniq
    refine ⟨fun x => ?_, fun s => ?_⟩
    · rw [MvPowerSeries.c_eq_algebraMap]
      exact F1.commutes x
    · rcases s with e | k
      · exact e.elim
      · show A.β (algebraMap (abelian₂ O Empty D) A.R (MvPowerSeries.X (Sum.inr k))) = _
        rw [A.segmentWeightExponent k, b.segmentWeightExponent k, map_sub, map_mul, map_one, AlgHom.commutes]
        congr 2
        have hp := congrArg (fun χ => ((χ (b.wt.γ k) : Bˣ) : B)) (A.β_pair.2 (b.wt.v k) (b.wt.i k))
        simpa [pushCh] using hp
  have e2 : b.lam = F := by
    apply huniq
    refine ⟨fun x => ?_, fun s => rfl⟩
    rw [MvPowerSeries.c_eq_algebraMap]
    exact b.lam.commutes x
  have := congrArg (fun φ : abelian₂ O Empty D →ₐ[O] B => φ a) (e1.trans e2.symm)
  simpa [F1] using this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.LamW
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

theorem UpperTheory.V.Th.Sp.lamW :
    ∀ (O R B M V : Type) [CommRing O] [CommRing R] [CommRing B] [Algebra O R] [Algebra O B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →ₐ[O] B) (x : B →ₐ[O] O) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (f : PU R q n) (α : Fin q → Fin n → O) (lam : M →+ O) (m₀ : M), TwoMaps (M := M) β.toRingHom P act f → (∀ j, (P j).map (x : B →+* O) = ∏ i, (Polynomial.X - Polynomial.C (α j i))) → (∀ (a : B) m, lam (a • m) = x a * lam m) → ∃ (lw : V →+ O) (v : V), (∀ τ w, lw (act τ w) = MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) τ * lw w) ∧ lw v = MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) f * lam m₀ := by
  intro O R B M V _ _ _ _ _ _ _ _ _ q n β x P act f α lam m₀ hT hP hlam
  obtain ⟨φ, ψ, h1, h2, h3, h4⟩ := hT
  letI : Algebra B O := (x : B →+* O).toAlgebra
  let ε : MSplitAlg P n →ₐ[B] O := MSplitAlg.lift P n (fun j i => α j i) (fun j => (hP j).symm)
  have hε : ∀ t : PU R q n, ε (Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β.toRingHom t)) =
      MvPolynomial.eval₂ ((x.comp β : R →ₐ[O] O) : R →+* O) (fun p => α p.1 p.2) t := by
    intro t
    show MvPolynomial.aeval (fun p : Fin q × Fin n => α p.1 p.2) (MvPolynomial.map β.toRingHom t) = _
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    rfl
  let lamL : M →ₗ[B] O :=
    { toFun := lam
      map_add' := lam.map_add
      map_smul' := fun a m => hlam a m }
  let Λ : MSplitAlg P n ⊗[B] M →ₗ[B] O :=
    TensorProduct.lift ((LinearMap.mul B O).compl₁₂ ε.toLinearMap lamL)
  have hΛt : ∀ a m, Λ (a ⊗ₜ m) = ε a * lam m := by
    intro a m
    show TensorProduct.lift _ (a ⊗ₜ m) = _
    rw [TensorProduct.lift.tmul]
    rfl
  have hΛs : ∀ (a : MSplitAlg P n) z, Λ (a • z) = ε a * Λ z := by
    intro a z
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, mul_zero]
    | tmul a' m => rw [TensorProduct.smul_tmul', smul_eq_mul, hΛt, hΛt, map_mul, mul_assoc]
    | add z₁ z₂ h₁ h₂ => rw [smul_add, map_add (f := _), map_add (f := _), h₁, h₂, mul_add]
  refine ⟨Λ.toAddMonoidHom.comp ψ, φ (1 ⊗ₜ m₀), ?_, ?_⟩
  · intro τ w
    show Λ (ψ (act τ w)) = _ * Λ (ψ w)
    rw [h2, hΛs, hε]
  · show Λ (ψ (φ (1 ⊗ₜ m₀))) = _
    rw [h4, hΛs, hε, hΛt, map_one, one_mul]
end

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem fEl_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {q n : ℕ} (Nq : Fin q → ℕ) (u : Fin q → Fin n → R) :
    f (fEl Nq u) = fEl Nq fun j i => f (u j i) := by
  simp [fEl]

private theorem chi_rep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]

private theorem g_dvd {O : Type} [CommRing O] {q n : ℕ} (Nq : Fin q → ℕ) (α : Fin q → Fin n → O) :
    (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (α j i - α j k)) ∣ fEl Nq α :=
  Finset.prod_dvd_prod_of_dvd _ _ fun _ _ => Finset.prod_dvd_prod_of_dvd _ _ fun _ _ =>
    Finset.prod_dvd_prod_of_dvd _ _ fun _ _ => dvd_mul_right _ _

private theorem e_dvd {O : Type} [CommRing O] {q n : ℕ} (α : Fin q → Fin n → O) (j : Fin q) (i : Fin n) :
    (∏ k ∈ Finset.univ.erase i, (α j i - α j k)) ∣ ∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (α j i - α j k) :=
  (Finset.dvd_prod_of_mem (fun i => ∏ k ∈ Finset.univ.erase i, (α j i - α j k)) (Finset.mem_univ i)).trans
    (Finset.dvd_prod_of_mem (fun j => ∏ i, ∏ k ∈ Finset.univ.erase i, (α j i - α j k)) (Finset.mem_univ j))

private theorem num_dvd {O : Type} [CommRing O] (a g F e z c : O) (E : ℕ) (h1 : g ∣ F) (h2 : e ∣ F)
    (h : a ^ 2 * z * F ^ (3 * E + 6) ∣ c) : (a * g * F * F ^ E) ^ 2 * (F * z) * e ^ (E + 1) ∣ c := by
  refine Dvd.dvd.trans ?_ h
  obtain ⟨g', hg⟩ := h1
  obtain ⟨e', he⟩ := h2
  refine ⟨g' ^ 2 * e' ^ (E + 1), ?_⟩
  have : F ^ (3 * E + 6) = (g * g') ^ 2 * (F * F ^ E) ^ 2 * F * (e * e') ^ (E + 1) := by
    rw [← hg, ← he]; ring
  rw [this]; ring

theorem UpperTheory.V.Th.Sp.one :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 G : Glob l L) (h : G.Hom G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (q N : ℕ) (A : OpMod b h q N) (y : Pt G0.frame O n) (x : B →ₐ[O] O) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (E : ℕ) (α : Fin q → Fin n → O) (t₀ : B) (lam : b.M →+ O) (m₀ : b.M) (m : ℕ) (c : O), 1 ≤ n → GenBy O (pairVals u) → u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ → (∀ a : B, x a = 0 → ∀ w : b.M, (t₀ * a) • w ∈ wtSub b x) → (∀ (a : B) w, lam (a • w) = x a * lam w) → (∀ j, h.p₀ (ta j) = 1) → (∀ j, (mat y.ρ (h.p₀ (ph j))).charpoly = ∏ k, (Polynomial.X - Polynomial.C (α j k))) → OpRelX A Nq ph ta E → m ≤ N → x t₀ ^ 2 * lam m₀ * fEl Nq α ^ (3 * E + 6) ∣ c → ∀ a : Fin D ⊕ Fin q × Fin n, ∃ δ : A.R →ₗ[O] Om O m, IsDer (x.comp A.β) δ ∧ (∀ k, δ (algebraMap (abelian₂ O Empty D) A.R (MvPowerSeries.X (.inr k))) = if a = .inl k then algebraMap O _ c else 0) ∧ ∀ j i, δ (A.p.D.tr (twoPowerModulus E (ph j) (ta j) (fun k => algebraMap O A.R (α j k)) i 0)) = if a = .inr (j, i) then algebraMap O _ c else 0 := by
  intro l _ L G0 G h n O _ _ _ _ _ r B _ _ _ u J D b q N A y x Nq ph ta E α t₀ lam m₀ m c hn hgen hmap hEt hlam hta hα hA hN hc a
  have hs := Sp.betaSurj l L G0 G h n O r B u J D b q N A hgen
  have hβ := Sp.betaLam l L G0 G h n O r B u J D b q N A
  obtain ⟨t₁, rfl⟩ := hs t₀
  have hP : ∀ j, (u.D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1)).map (x : B →+* O) =
      ∏ i, (Polynomial.X - Polynomial.C (α j i)) := fun j => by
    have h1 := ((UpperTheory.V.CA.d_gmap u.D).2.2.1 x.toRingHom (MonoidAlgebra.single (h.p₀ (ph j)) 1)).1
    rw [MonoidAlgebra.mapRingHom_single, map_one, hmap.1, chi_rep, hα j] at h1
    exact h1.symm
  obtain ⟨lw, v₀, hlw, hv₀⟩ := Sp.lamW O A.R B b.M A.Mw q n A.β x _ A.actw _ α lam m₀ hA.two hP hlam
  obtain ⟨htr, hker⟩ := Sp.trans A.R A.M1 A.Mw q n A.act1 A.actw A.tr A.tr_surj A.tr_ker A.tr_u
  obtain ⟨v, rfl⟩ := A.tr_surj v₀
  let xU : PU A.R q n →+* O := MvPolynomial.eval₂Hom ((x.comp A.β : A.R →ₐ[O] O) : A.R →+* O) fun p => α p.1 p.2
  let π : PUY A.R q n →ₐ[A.R] PU A.R q n := MvPolynomial.aeval (Sum.elim MvPolynomial.X 0)
  let xT : PUY A.R q n →ₐ[O] O :=
    { xU.comp (π : PUY A.R q n →+* PU A.R q n) with
      commutes' := fun o => by
        change xU (π (MvPolynomial.C (algebraMap O A.R o))) = o
        simp [xU, π] }
  have hxT : ∀ τ, xT τ = xU (π τ) := fun _ => rfl
  have hC : ∀ s, xT (MvPolynomial.C s) = x (A.β s) := fun s => by simp [hxT, xU, π]
  have hU : ∀ j k, xT (uV A.R j k) = α j k := fun j k => by simp [hxT, xU, π]
  have hY : ∀ j k, xT (yV A.R j k) = 0 := fun j k => by simp [hxT, xU, π]
  let I : Ideal A.R := (RingHom.ker (x.comp b.lam)).map (algebraMap (abelian₂ O Empty D) A.R)
  have hI : ∀ w, w ∈ wtSub b x → w ∈ (I.map A.β • ⊤ : Submodule B b.M) := fun w hw => by
    refine Submodule.smul_induction_on hw (fun s hs w _ => ?_) fun _ _ => add_mem
    rw [b.smul_lam, ← hβ]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hs)) trivial
  have hkill := Sp.kill O A.R B b.M A.Mw q n A.β x _ A.actw _ α I t₁ hs hA.two hP fun a ha w => hI _ (hEt a ha w)
  let t : PUY A.R q n := MvPolynomial.C t₁ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
    (uV A.R j i - MvPolynomial.C (algebraMap O A.R (α j k)))) * fEl Nq (uV A.R) * fEl Nq (uV A.R) ^ E
  have hF : xT (fEl Nq (uV A.R)) = fEl Nq α := by
    have := fEl_map (xT : PUY A.R q n →+* O) Nq (uV A.R)
    simpa [hU] using this
  have hxt : xT t = x (A.β t₁) * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i, (α j i - α j k)) * fEl Nq α * fEl Nq α ^ E := by
    simp only [t, map_mul, map_pow, map_prod, map_sub, hC, hU, hF, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  have hv : lw (A.tr v) = fEl Nq α * lam m₀ := by
    rw [hv₀]
    congr 1
    have := fEl_map xU Nq fun j i => MvPolynomial.X (j, i)
    simpa [xU] using this
  obtain ⟨del, hd, h1, h2, h3⟩ := Sp.derOp l L G0 G h n O r B u J D b q N A xT (lw.comp A.tr.toAddMonoidHom) t v I m hN hY
    (fun τ w => by
      change lw (A.tr (A.act1 τ w)) = xT τ * lw (A.tr w)
      rw [htr, hlw]; rfl)
    (Ideal.span_le.2 (by
      rintro _ ⟨s, hs, rfl⟩
      exact Ideal.subset_span ⟨s, rfl, by rw [hC, hβ]; exact hs⟩))
    (fun s hs w => hker I _ (by
      have hπ : π (fEl Nq (uV A.R)) = fEl Nq fun j i => MvPolynomial.X (j, i) := by
        have := fEl_map (π : PUY A.R q n →+* PU A.R q n) Nq (uV A.R)
        simpa [π] using this
      have e : π (t * s) = MvPolynomial.C t₁ * (∏ j, ∏ i, ∏ k ∈ Finset.univ.erase i,
          (MvPolynomial.X (j, i) - MvPolynomial.C (algebraMap O A.R (α j k)))) * (fEl Nq fun j i => MvPolynomial.X (j, i)) *
          π (fEl Nq (uV A.R) ^ E * s) := by
        simp only [t, map_mul, map_prod, map_sub, hπ, mul_assoc]
        simp [π]
      rw [htr]
      change A.actw (π (t * s)) _ ∈ _
      rw [e]
      refine hkill _ ?_ _
      change xT _ = 0
      rw [map_mul, hs, mul_zero])) a
  have hv' : (lw.comp A.tr.toAddMonoidHom) v = fEl Nq α * lam m₀ := hv
  rw [hv'] at h1 h2
  have hq : ∀ j i, del (MvPolynomial.C (A.p.D.tr (twoPowerModulus E (ph j) (ta j) (fun k => algebraMap O A.R (α j k)) i 0))) =
      (∏ k ∈ Finset.univ.erase i, (α j i - α j k)) ^ (E + 1) • del (yV A.R j i) := fun j i => by
    obtain ⟨k1, k2⟩ := Sp.q2op l L G0 G h n O r B u J D b q N A y x (ph j) (ta j) (α j) E j i xT _ del hn hmap (hta j) (hα j)
      hC (hU j) (hY j i) hd
    have := h3 _ k1 (by
      simp only [t]
      rw [mul_assoc, map_mul, hA.rel2, mul_zero])
    rw [this] at k2
    exact sub_eq_zero.1 k2.symm
  let δ₀ : A.R →ₗ[O] Om O m := del ∘ₗ (IsScalarTower.toAlgHom O A.R (PUY A.R q n)).toLinearMap
  have hδ : ∀ s, δ₀ s = del (MvPolynomial.C s) := fun _ => rfl
  have hder : ∀ e : O, IsDer (x.comp A.β) (e • δ₀) := fun e s s' => by
    simp only [LinearMap.smul_apply, hδ, map_mul, hd _ _, hC, AlgHom.comp_apply, smul_add, smul_comm e]
  have hnum := fun j i => num_dvd _ _ _ _ _ c E (g_dvd Nq α) ((e_dvd α j i).trans (g_dvd Nq α)) hc
  have hn0 := num_dvd _ _ _ 1 _ c E (g_dvd Nq α) (one_dvd _) hc
  rw [← hxt] at hnum hn0
  rcases a with k | ⟨j, i⟩
  · obtain ⟨e, he⟩ := hn0
    refine ⟨e • δ₀, hder e, fun k' => ?_, fun j i => ?_⟩
    · rw [LinearMap.smul_apply, hδ, h1]
      split_ifs
      · rw [he, Algebra.smul_def, ← map_mul]; congr 1; ring
      · simp
    · rw [LinearMap.smul_apply, hδ, hq, h2]; simp
  · obtain ⟨e, he⟩ := hnum j i
    refine ⟨e • δ₀, hder e, fun k' => ?_, fun j' i' => ?_⟩
    · rw [LinearMap.smul_apply, hδ, h1]; simp
    · rw [LinearMap.smul_apply, hδ, hq, h2]
      split_ifs with hh
      · obtain ⟨rfl, rfl⟩ : j = j' ∧ i = i' := by simpa using hh
        rw [he, Algebra.smul_def, Algebra.smul_def, ← map_mul, ← map_mul]; congr 1; ring
      · simp
