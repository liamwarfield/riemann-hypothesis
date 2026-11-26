module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepCont
open Polynomial UpperTheory.V.W

private theorem UpperTheory.V.AlgebraTools.Det.cont_charpoly_coeff {n : ℕ} {K : Type} [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

theorem UpperTheory.V.AlgebraTools.Det.repCont :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G] (ρ : G →* Matrix (Fin n) (Fin n) A),
    Continuous ρ → ∀ i, Continuous fun g : G => (GDet.ofRep ρ).lam i (MonoidAlgebra.single g 1) := by
  intro n A G _ _ _ _ _ ρ hρ i
  have h : (fun g : G => (GDet.ofRep ρ).lam i (MonoidAlgebra.single g 1))
      = fun g => (-1) ^ i * (ρ g).charpoly.coeff (n - i) := by
    funext g
    rw [GDet.lam, (UpperTheory.V.AlgebraTools.Det.repApi ρ).2.1]
  rw [h]
  exact continuous_const.mul ((UpperTheory.V.AlgebraTools.Det.cont_charpoly_coeff (n - i)).comp hρ)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.StarApi
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

section
variable {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R]
  [Algebra O R] (n : ℕ)

private theorem star_add' (y z : MonoidAlgebra R F.G₀) :
    F.star O R n (y + z) = F.star O R n y + F.star O R n z := by
  simp [GFrame.star]

private theorem star_zero' : F.star O R n 0 = 0 := by
  simp [GFrame.star]

end

private theorem star_single_eq_single_conj_inv_mul_eps_zpow {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (r : R) :
    F.star O R n (MonoidAlgebra.single g r) =
      MonoidAlgebra.single (F.conj g)⁻¹ (r * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]

private theorem conjO_conjO_unimodular_class_representatives {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) : F.conj (F.conj g) = g := by
  have hc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right F.c_sq
  apply Subtype.ext
  simp [GFrame.conj, hc, ← mul_assoc, F.c_sq]
  rw [mul_assoc, F.c_sq, mul_one]

private theorem eps_conj' {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) : F.eps O R (F.conj g) = F.eps O R g := by
  simp [GFrame.eps, GFrame.conj]

private theorem algHom_eps_zpow_eq {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (R' : Type) [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R')
    (g : F.G₀) (k : ℤ) :
    f ((F.eps O R g ^ k : Rˣ) : R) = ((F.eps O R' g ^ k : R'ˣ) : R') := by
  have h : Units.map (f : R →* R') (F.eps O R g) = F.eps O R' g := by
    ext
    simp [GFrame.eps, pushCh]
  rw [← h, ← map_zpow (Units.map (f : R →* R')), Units.coe_map]
  rfl

theorem UpperTheory.V.AlgebraTools.Det.starApi :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ),
    (∀ y z, F.star O R n (y * z) = F.star O R n z * F.star O R n y) ∧ F.star O R n 1 = 1 ∧
    (∀ y z, F.star O R n (y + z) = F.star O R n y + F.star O R n z) ∧ (∀ (a : R) y, F.star O R n (a • y) = a • F.star O R n y) ∧
    (∀ y, F.star O R n (F.star O R n y) = y) ∧
    ∀ (R' : Type) [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') (y : MonoidAlgebra R F.G₀),
      F.star O R' n (MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') y) = MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (F.star O R n y) := by
  intro l _ F O _ _ R _ _ n
  refine ⟨?_, ?_, star_add' F O R n, ?_, ?_, ?_⟩
  · intro y z
    simp only [GFrame.star, map_mul, MulOpposite.unop_mul]
  · simp [GFrame.star, map_one]
  · intro a y
    simp only [GFrame.star, map_smul, MulOpposite.unop_smul]
  · intro y
    induction y using MonoidAlgebra.induction_linear
    next => simp [star_zero']
    next y z hy hz => rw [star_add', star_add', hy, hz]
    next g r =>
      simp only [star_single_eq_single_conj_inv_mul_eps_zpow, map_inv, inv_inv, conjO_conjO_unimodular_class_representatives, eps_conj', _root_.inv_zpow]
      rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  · intro R' _ _ f y
    induction y using MonoidAlgebra.induction_linear
    next => simp [star_zero']
    next y z hy hz => rw [map_add (f := _), star_add', star_add', map_add (f := _), hy, hz]
    next g r =>
      simp only [star_single_eq_single_conj_inv_mul_eps_zpow, MonoidAlgebra.mapRingHom_single, RingHom.coe_coe, map_mul]
      rw [algHom_eps_zpow_eq]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.FlagRel
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.FlagKill
open Polynomial Matrix

private theorem UpperTheory.V.AlgebraTools.Det.flag_product_maps_into {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
    (W : ℕ → Submodule R V) :
    ∀ (n : ℕ) (f : Fin n → Module.End R V),
    (∀ j : Fin n, ∀ v ∈ W (j + 1), f j v ∈ W j) → ∀ v ∈ W n, (List.ofFn f).prod v ∈ W 0 := by
  intro n
  induction n generalizing W with
  | zero =>
    intro f _ v hv
    simpa using hv
  | succ n ih =>
    intro f hf v hv
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    have h0 := hf 0
    simp only [Fin.val_zero, zero_add] at h0
    apply h0
    have ht := ih (fun k => W (k + 1)) (fun i => f i.succ) (fun j w hw => by
      have hj := hf j.succ w (by simpa [Fin.val_succ] using hw)
      simpa [Fin.val_succ] using hj) v hv
    simpa using ht

theorem UpperTheory.V.AlgebraTools.Det.flagKill :
    ∀ {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (n : ℕ) (W : ℕ → Submodule R V) (f : Fin n → Module.End R V),
    W 0 = ⊥ → W n = ⊤ → (∀ j : Fin n, ∀ v ∈ W (j + 1), f j v ∈ W j) → (List.ofFn f).prod = 0 := by
  intro R V _ _ _ n W f h0 hn hf
  ext v
  have h := UpperTheory.V.AlgebraTools.Det.flag_product_maps_into W n f hf v (by rw [hn]; exact Submodule.mem_top)
  rw [h0, Submodule.mem_bot] at h
  simpa using h
end

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.flagRel :
    ∀ {k H : Type} [CommRing k] [Group H] {n : ℕ} (r : H →* GL (Fin n) k) (κ : Fin n → H →* kˣ), HasFlag r κ →
    (∀ s, (mat r s).charpoly = ∏ j, (X - C (κ j s : k))) ∧
    ∀ g : Fin n → H, (List.ofFn fun j => mat r (g j) - (κ j (g j) : k) • (1 : Matrix (Fin n) (Fin n) k)).prod = 0 := by
  intro k H _ _ n r κ ⟨P, hP⟩
  have hm : ∀ s, mat r s = (r s : Matrix (Fin n) (Fin n) k) := fun _ => rfl
  constructor
  · intro s
    have h1 : ((P * r s * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly = (mat r s).charpoly := by
      rw [hm, Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
    have h2 : ((P * r s * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
      fun i j hij => (hP s).1 i j hij
    rw [← h1, Matrix.charpoly_of_upperTriangular _ h2]
    exact Finset.prod_congr rfl fun i _ => by rw [← (hP s).2 i]
  · intro g
    let W : ℕ → Submodule k (Fin n → k) := fun j =>
      { carrier := {v | ∀ i : Fin n, j ≤ i.val → ((P : Matrix (Fin n) (Fin n) k) *ᵥ v) i = 0}
        add_mem' := fun {a b} ha hb i hi => by
          rw [Matrix.mulVec_add, Pi.add_apply, ha i hi, hb i hi, add_zero]
        zero_mem' := fun i _ => by simp
        smul_mem' := fun c a ha i hi => by
          rw [Matrix.mulVec_smul, Pi.smul_apply, ha i hi, smul_zero] }
    have hW : ∀ j v, v ∈ W j ↔ ∀ i : Fin n, j ≤ i.val → ((P : Matrix (Fin n) (Fin n) k) *ᵥ v) i = 0 :=
      fun _ _ => Iff.rfl
    have key := UpperTheory.V.AlgebraTools.Det.flagKill n W
      (fun j => Matrix.toLinAlgEquiv' (mat r (g j) - (κ j (g j) : k) • (1 : Matrix (Fin n) (Fin n) k))) ?_ ?_ ?_
    · apply (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).injective
      rw [map_list_prod, map_zero, List.map_ofFn]
      exact key
    · rw [eq_bot_iff]
      intro v hv
      have h0 : (P : Matrix (Fin n) (Fin n) k) *ᵥ v = 0 := funext fun i => (hW 0 v).1 hv i (Nat.zero_le _)
      have : v = ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ ((P : Matrix (Fin n) (Fin n) k) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [Submodule.mem_bot, this, h0, Matrix.mulVec_zero]
    · rw [eq_top_iff]
      intro v _
      exact (hW n v).2 fun i hi => absurd i.2 (not_lt.2 hi)
    · intro j v hv
      rw [hW] at hv ⊢
      intro i hi
      have e : (P : Matrix (Fin n) (Fin n) k) *ᵥ
          (Matrix.toLinAlgEquiv' (mat r (g j) - (κ j (g j) : k) • (1 : Matrix (Fin n) (Fin n) k)) v) =
          ((P * r (g j) * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ ((P : Matrix (Fin n) (Fin n) k) *ᵥ v)
            - (κ j (g j) : k) • ((P : Matrix (Fin n) (Fin n) k) *ᵥ v) := by
        rw [Matrix.toLinAlgEquiv'_apply, Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
          Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm, Units.val_mul, Units.val_mul,
          Units.inv_mul_cancel_right]
      rw [e, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_zero]
      generalize (P : Matrix (Fin n) (Fin n) k) *ᵥ v = w at hv ⊢
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
      · rcases eq_or_lt_of_le hi with h | h
        · have : j = i := Fin.ext h
          subst this
          rw [← (hP (g j)).2 j]
        · rw [hv i h, mul_zero, mul_zero]
      · intro b _ hb
        rcases lt_or_gt_of_ne hb with h | h
        · have := (hP (g j)).1 i b h
          rw [this, zero_mul]
        · rw [hv b (by have : i.val < b.val := h; omega), mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Expand
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GenHomog
open Polynomial UpperTheory.V.W

private theorem coeff_scale {A : Type} [CommRing A] {m : ℕ} (P : MvPolynomial (Fin m) A) (s : Fin m →₀ ℕ) :
    AddMonoidAlgebra.coeff ((MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X])) P).coeff s.degree)
      s
      = AddMonoidAlgebra.coeff P s := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have h : MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))
        (MvPolynomial.monomial u a) = C (MvPolynomial.monomial u a) * X ^ u.degree := by
      rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, Finsupp.prod, Finsupp.prod,
        show u.degree = ∑ i ∈ u.support, u i from rfl]
      simp only [mul_pow, Finset.prod_mul_distrib, ← C_pow, ← map_prod, Finset.prod_pow_eq_pow_sum,
        Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, map_mul]
      ring
    rw [h, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial_apply, MvPolynomial.coeff_monomial]
    split_ifs with h1 h2 h2
    · rw [MvPolynomial.coeff_monomial, if_pos h2]
    · rw [MvPolynomial.coeff_monomial, if_neg h2]
    · exact absurd (congrArg Finsupp.degree h2) h1
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), Polynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add]

theorem UpperTheory.V.AlgebraTools.Det.genHomog :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (m : ℕ) (y : Fin m → MonoidAlgebra A G),
    (D.D (MvPolynomial (Fin m) A) (GDet.gen y)).IsHomogeneous n := by
  intro n A G _ _ D m y
  have hφ : (MvPolynomial.aeval (fun j => (C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))) =
      (Polynomial.CAlgHom : MvPolynomial (Fin m) A →ₐ[A] (MvPolynomial (Fin m) A)[X]) :=
    MvPolynomial.algHom_ext fun i => by
      change _ = Polynomial.C (MvPolynomial.X i)
      simp
  have hC : MvPolynomial.aeval (fun j => (C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))
      (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) = C (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
    rw [hφ]
    rfl
  have hgen (B : Type) [CommRing B] [Algebra A B] (b : Fin m → B) :
      D.D B (∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A B) (y j)) =
        MvPolynomial.aeval b (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
    rw [← D.nat (MvPolynomial (Fin m) A) B (MvPolynomial.aeval b)]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GDet.gen, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext g
    simp [MonoidAlgebra.mapRingHom]
  have key : MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))
      (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) = X ^ n * C (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
    rw [← hgen _, ← hC, ← hgen _, ← D.homog,
      Finset.smul_sum]
    simp only [mul_smul]
  intro d hd
  have h1 := coeff_scale (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) d
  rw [key, mul_comm, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial] at h1
  have hw : Finsupp.weight 1 d = d.degree := by
    simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rfl
  rw [hw]
  by_contra hne
  simp [hne] at h1
  exact hd h1.symm
end

open Polynomial UpperTheory.V.W

private theorem hom_two {A : Type} [CommRing A] {n : ℕ} (P : MvPolynomial (Fin 2) A) (hP : P.IsHomogeneous n) :
    ∃ c : ℕ → A, ∀ (B : Type) [CommRing B] [Algebra A B] (s t : B),
      MvPolynomial.aeval ![s, t] P = ∑ i ∈ Finset.range (n + 1), algebraMap A B (c i) * s ^ (n - i) * t ^ i := by
  classical
  let e : ℕ → (Fin 2 →₀ ℕ) := fun i => Finsupp.single 0 (n - i) + Finsupp.single 1 i
  refine ⟨fun i => P.coeff (e i), ?_⟩
  intro B _ _ s t
  have hF : ∀ d : Fin 2 →₀ ℕ, MvPolynomial.aeval ![s, t] (MvPolynomial.monomial d (P.coeff d)) =
      algebraMap A B (P.coeff d) * s ^ (d 0) * t ^ (d 1) := by
    intro d
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp [mul_assoc]
  conv_lhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp_rw [hF]
  have hinj : Set.InjOn e (Finset.range (n + 1)) := by
    intro i _ j _ h
    have := congrArg (fun f => f 1) h
    simpa [e] using this
  have hR : ∑ i ∈ Finset.range (n + 1), algebraMap A B (P.coeff (e i)) * s ^ (n - i) * t ^ i =
      ∑ d ∈ (Finset.range (n + 1)).image e, algebraMap A B (P.coeff d) * s ^ (d 0) * t ^ (d 1) := by
    rw [Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [e]
  rw [hR]
  apply Finset.sum_subset
  · intro d hd
    rw [Finset.mem_image]
    have hdeg := hP (MvPolynomial.mem_support_iff.mp hd)
    have h2 : d 0 + d 1 = n := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using hdeg
    refine ⟨d 1, Finset.mem_range.mpr (by omega), ?_⟩
    ext j
    fin_cases j <;> simp [e] <;> omega
  · intro d _ hd
    have h0 : P.coeff d = 0 := by simpa [MvPolynomial.mem_support_iff] using hd
    simp [h0]

theorem UpperTheory.V.AlgebraTools.Det.expand :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G) (B : Type) [CommRing B] [Algebra A B] (s t : B),
    D.D B (MonoidAlgebra.single 1 s + t • MonoidAlgebra.mapRingHom G (algebraMap A B) y) =
    ∑ i ∈ Finset.range (n + 1), algebraMap A B (D.lam i y) * s ^ (n - i) * t ^ i := by
  intro n A G _ _ D y B _ _ s t
  let y2 : Fin 2 → MonoidAlgebra A G := ![1, y]
  have genEval (B : Type) [CommRing B] [Algebra A B] (m : ℕ)
      (y : Fin m → MonoidAlgebra A G) (b : Fin m → B) :
      D.D B (∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A B) (y j)) =
        MvPolynomial.aeval b (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
    rw [← D.nat (MvPolynomial (Fin m) A) B (MvPolynomial.aeval b)]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GDet.gen, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext g
    simp [MonoidAlgebra.mapRingHom]
  have coeff_scale {m : ℕ} (P : MvPolynomial (Fin m) A) (s : Fin m →₀ ℕ) :
      AddMonoidAlgebra.coeff ((MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X])) P).coeff s.degree) s =
        AddMonoidAlgebra.coeff P s := by
    induction P using MvPolynomial.induction_on' with
    | monomial u a =>
      have h : MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))
          (MvPolynomial.monomial u a) = C (MvPolynomial.monomial u a) * X ^ u.degree := by
        rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, Finsupp.prod, Finsupp.prod,
          show u.degree = ∑ i ∈ u.support, u i from rfl]
        simp only [mul_pow, Finset.prod_mul_distrib, ← C_pow, ← map_prod, Finset.prod_pow_eq_pow_sum,
          Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, map_mul]
        ring
      rw [h, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial_apply, MvPolynomial.coeff_monomial]
      split_ifs with h1 h2 h2
      · rw [MvPolynomial.coeff_monomial, if_pos h2]
      · rw [MvPolynomial.coeff_monomial, if_neg h2]
      · exact absurd (congrArg Finsupp.degree h2) h1
      · simp
    | add p q hp hq =>
      rw [map_add (f := _), Polynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add]
  have hP : (D.D (MvPolynomial (Fin 2) A) (GDet.gen y2)).IsHomogeneous n := by
    let m := 2
    let y := y2
    have hφ : (MvPolynomial.aeval (fun j => (C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))) =
        (Polynomial.CAlgHom : MvPolynomial (Fin m) A →ₐ[A] (MvPolynomial (Fin m) A)[X]) :=
      MvPolynomial.algHom_ext fun i => by
        change MvPolynomial.aeval _ (MvPolynomial.X i) = Polynomial.C (MvPolynomial.X i)
        simp
    have hC : MvPolynomial.aeval (fun j => (C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))
        (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) = C (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
      rw [hφ]
      rfl
    have key : MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))
        (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) = X ^ n * C (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
      rw [← genEval _ m y, ← hC, ← genEval _ m y, ← D.homog,
        Finset.smul_sum]
      simp only [mul_smul]
    intro d hd
    have h1 := coeff_scale (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) d
    rw [key, mul_comm, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial] at h1
    have hw : Finsupp.weight 1 d = d.degree := by
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
      rfl
    rw [hw]
    by_contra hne
    simp [Finsupp.single_apply, Ne.symm hne] at h1
    exact hd h1.symm
  obtain ⟨c, hc⟩ := hom_two _ hP
  have hev : ∀ (B : Type) [CommRing B] [Algebra A B] (s t : B),
      D.D B (MonoidAlgebra.single 1 s + t • MonoidAlgebra.mapRingHom G (algebraMap A B) y) =
        ∑ i ∈ Finset.range (n + 1), algebraMap A B (c i) * s ^ (n - i) * t ^ i := by
    intro B _ _ s t
    rw [← hc B s t, ← genEval B 2 y2 ![s, t]]
    congr 1
    rw [Fin.sum_univ_two]
    simp [y2, MonoidAlgebra.one_def, MonoidAlgebra.smul_single']
  have hlam : ∀ i ∈ Finset.range (n + 1), D.lam i y = c i := by
    intro i hi
    have hchi : D.chi y = ∑ j ∈ Finset.range (n + 1), Polynomial.C (c j * (-1) ^ j) * X ^ (n - j) := by
      have h := hev A[X] X (-1)
      rw [neg_one_smul, ← sub_eq_add_neg, Polynomial.algebraMap_eq] at h
      unfold GDet.chi
      rw [h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_pow, map_neg, map_one]
      ring
    unfold GDet.lam
    rw [hchi, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, mul_left_comm, ← mul_pow, neg_one_mul, neg_neg, one_pow, mul_one]
    · intro j hj hji
      rw [if_neg]
      intro h
      apply hji
      have := Finset.mem_range.mp hi
      have := Finset.mem_range.mp hj
      omega
    · intro h
      exact absurd hi h
  rw [hev B s t]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hlam i hi]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.ExtGen
open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.extGen :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D D' : GDet n A G),
    (∀ (m : ℕ) (g : Fin m → G), D.D (MvPolynomial (Fin m) A) (GDet.gen fun j => MonoidAlgebra.single (g j) 1) =
      D'.D (MvPolynomial (Fin m) A) (GDet.gen fun j => MonoidAlgebra.single (g j) 1)) → D = D' := by
  intro n A G _ _ D D' h
  refine GDet.ext fun B _ _ x => ?_
  obtain ⟨m, g, b, rfl⟩ := UpperTheory.V.AlgebraTools.Det.genSpan (A := A) B x
  rw [UpperTheory.V.AlgebraTools.Det.genEval D B m (fun j => MonoidAlgebra.single (g j) 1) b,
    UpperTheory.V.AlgebraTools.Det.genEval D' B m (fun j => MonoidAlgebra.single (g j) 1) b, h]
end
