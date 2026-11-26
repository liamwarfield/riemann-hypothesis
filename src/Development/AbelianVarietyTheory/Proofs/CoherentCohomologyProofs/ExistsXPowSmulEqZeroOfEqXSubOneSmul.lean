module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsXPowSmulEqZeroOfEqXSubOneSmul
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

noncomputable section

namespace GlobalTheory

open GradedHilbert

section

variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι)

private lemma decompose_X_smul_add_one (y : M) (m : ℤ) :
    (decompose ℳ ((X i : MvPolynomial ι R) • y) (m + 1) : M) =
      (X i : MvPolynomial ι R) • (decompose ℳ y m : M) := by
  classical
  have key : ∀ j, (decompose ℳ ((X i : MvPolynomial ι R) • (decompose ℳ y j : M)) (m + 1) : M)
      = if j = m then (X i : MvPolynomial ι R) • (decompose ℳ y m : M) else 0 := by
    intro j
    have hmem := _root_.GlobalTheory.X_smul_mem_gr ℳ i j _ (decompose ℳ y j).2
    split_ifs with hj
    · subst hj; exact decompose_of_mem_same ℳ hmem
    · exact decompose_of_mem_ne ℳ hmem (by omega)
  conv_lhs => rw [← sum_support_decompose ℳ y]
  rw [Finset.smul_sum, decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
  simp only [key]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [DFinsupp.notMem_support_iff.1 h]; simp

private lemma decompose_X_sub_one_smul_add_one (w : M) (m : ℤ) :
    (decompose ℳ ((X i - 1 : MvPolynomial ι R) • w) (m + 1) : M) =
      (X i : MvPolynomial ι R) • (decompose ℳ w m : M) - (decompose ℳ w (m + 1) : M) := by
  rw [sub_smul, one_smul, decompose_sub, DirectSum.sub_apply, Submodule.coe_sub,
    decompose_X_smul_add_one]

private lemma exists_decompose_eq_zero_of_lt (y : M) :
    ∃ N : ℤ, ∀ j < N, (decompose ℳ y j : M) = 0 := by
  classical
  obtain ⟨N, hN⟩ := (decompose ℳ y).support.bddBelow
  refine ⟨N, fun j hj => ?_⟩
  have : j ∉ (decompose ℳ y).support := fun h => by have := hN h; omega
  simp [DFinsupp.notMem_support_iff.1 this]

private lemma exists_decompose_eq_zero_of_gt (y : M) :
    ∃ N : ℤ, ∀ j > N, (decompose ℳ y j : M) = 0 := by
  classical
  obtain ⟨N, hN⟩ := (decompose ℳ y).support.bddAbove
  refine ⟨N, fun j hj => ?_⟩
  have : j ∉ (decompose ℳ y).support := fun h => by have := hN h; omega
  simp [DFinsupp.notMem_support_iff.1 this]

private lemma eq_zero_of_X_smul_recurrence_of_vanish_below {g : ℤ → M} {N c : ℤ} (hN : ∀ j < N, g j = 0)
    (hrec : ∀ m < c, g (m + 1) = (X i : MvPolynomial ι R) • g m) : g c = 0 := by
  have key : ∀ k : ℕ, g c = (X i : MvPolynomial ι R) ^ k • g (c - k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : c - (k : ℤ) = c - ((k + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
      rw [ih, e, hrec _ (by omega), ← mul_smul, ← pow_succ]
  rw [key (c - N + 1).toNat, hN _ (by omega), smul_zero]

private lemma exists_X_pow_smul_eq_zero_of_vanish_above {g : ℤ → M} {N c : ℤ}
    (hN : ∀ j > N, g j = 0) (hrec : ∀ m ≥ c, g (m + 1) = (X i : MvPolynomial ι R) • g m) :
    ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • g c = 0 := by
  have key : ∀ k : ℕ, g (c + k) = (X i : MvPolynomial ι R) ^ k • g c := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ, ← add_assoc, hrec _ (by omega), ih, ← mul_smul, ← pow_succ']
  exact ⟨(N - c + 1).toNat, by rw [← key, hN _ (by omega)]⟩

theorem _root_.GlobalTheory.exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul {n : ℤ} {z w : M} (hz : z ∈ ℳ n)
    (h : z = (X i - 1 : MvPolynomial ι R) • w) :
    ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z = 0 := by
  have hcomp : ∀ m, (decompose ℳ z (m + 1) : M) =
      (X i : MvPolynomial ι R) • (decompose ℳ w m : M) - (decompose ℳ w (m + 1) : M) := by
    intro m; rw [h]; exact decompose_X_sub_one_smul_add_one ℳ i w m
  have hne : ∀ m, m + 1 ≠ n →
      (decompose ℳ w (m + 1) : M) = (X i : MvPolynomial ι R) • (decompose ℳ w m : M) := by
    intro m hm
    have := hcomp m
    rw [decompose_of_mem_ne ℳ hz (Ne.symm hm)] at this
    exact (sub_eq_zero.1 this.symm).symm
  obtain ⟨N₁, hN₁⟩ := exists_decompose_eq_zero_of_lt ℳ w
  obtain ⟨N₂, hN₂⟩ := exists_decompose_eq_zero_of_gt ℳ w
  have h1 : (decompose ℳ w (n - 1) : M) = 0 :=
    eq_zero_of_X_smul_recurrence_of_vanish_below i (g := fun m => (decompose ℳ w m : M)) hN₁
      (fun m hm => hne m (by omega))
  have hzn : z = -(decompose ℳ w n : M) := by
    have := hcomp (n - 1)
    rw [sub_add_cancel, decompose_of_mem_same ℳ hz, h1, smul_zero, zero_sub] at this
    exact this
  obtain ⟨k, hk⟩ := exists_X_pow_smul_eq_zero_of_vanish_above i
    (g := fun m => (decompose ℳ w m : M)) (c := n) hN₂ (fun m hm => hne m (by omega))
  exact ⟨k, by rw [hzn, smul_neg, hk, neg_zero]⟩

private lemma X_pow_smul_mem_add_of_mem {j : ℤ} {v : M} (hv : v ∈ ℳ j) (k : ℕ) :
    (X i : MvPolynomial ι R) ^ k • v ∈ ℳ (j + k) := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    have := _root_.GlobalTheory.X_smul_mem_gr ℳ i (j + k) _ ih
    rw [pow_succ', mul_smul]
    convert this using 2
    push_cast; ring

private lemma exists_mem_add_X_sub_one_smul_of_mem_of_le {j n : ℤ} {v : M} (hv : v ∈ ℳ j) (hn : j ≤ n) :
    ∃ y' ∈ ℳ n, ∃ w : M, v = y' + (X i - 1 : MvPolynomial ι R) • w := by
  have hmem := X_pow_smul_mem_add_of_mem ℳ i hv (n - j).toNat
  have e : j + ((n - j).toNat : ℤ) = n := by omega
  rw [e] at hmem
  refine ⟨_, hmem, -(∑ l ∈ Finset.range (n - j).toNat, (X i : MvPolynomial ι R) ^ l) • v, ?_⟩
  rw [neg_smul, smul_neg, smul_smul, mul_geom_sum, sub_smul, one_smul]
  abel

theorem _root_.GlobalTheory.exists_homogeneous_add_X_sub_one_smul (y : M) :
    ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∃ y' ∈ ℳ n, ∃ w : M, y = y' + (X i - 1 : MvPolynomial ι R) • w := by
  classical
  have hsum : ∀ S : Finset ℤ, ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∃ y' ∈ ℳ n, ∃ w : M,
      ∑ j ∈ S, (decompose ℳ y j : M) = y' + (X i - 1 : MvPolynomial ι R) • w := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨0, fun n _ => ⟨0, zero_mem _, 0, by simp⟩⟩
    | insert a S ha ih =>
      obtain ⟨n₁, hn₁⟩ := ih
      refine ⟨max a n₁, fun n hn => ?_⟩
      obtain ⟨y₁, hy₁, w₁, e₁⟩ :=
        exists_mem_add_X_sub_one_smul_of_mem_of_le ℳ i (decompose ℳ y a).2 (le_of_max_le_left hn)
      obtain ⟨y₂, hy₂, w₂, e₂⟩ := hn₁ n (le_of_max_le_right hn)
      refine ⟨y₁ + y₂, add_mem hy₁ hy₂, w₁ + w₂, ?_⟩
      rw [Finset.sum_insert ha, e₁, e₂, smul_add]
      abel
  obtain ⟨n₀, hn₀⟩ := hsum (decompose ℳ y).support
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨y', hy', w, e⟩ := hn₀ n hn
  exact ⟨y', hy', w, by rw [← e, sum_support_decompose]⟩

end

variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι) in
include ℳ in
private lemma eq_zero_of_X_sub_one_smul_eq_zero {y : M}
    (hy : (X i - 1 : MvPolynomial ι R) • y = 0) : y = 0 := by
  classical
  have hrec : ∀ m, (decompose ℳ y (m + 1) : M) = (X i : MvPolynomial ι R) • (decompose ℳ y m : M) := by
    intro m
    have := decompose_X_sub_one_smul_add_one ℳ i y m
    rw [hy, decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero] at this
    exact (sub_eq_zero.1 this.symm).symm
  obtain ⟨N, hN⟩ := exists_decompose_eq_zero_of_lt ℳ y
  have hall : ∀ c, (decompose ℳ y c : M) = 0 := fun c =>
    eq_zero_of_X_smul_recurrence_of_vanish_below i (g := fun m => (decompose ℳ y m : M)) hN (fun m _ => hrec m)
  rw [← sum_support_decompose ℳ y]
  exact Finset.sum_eq_zero (fun j _ => hall j)

theorem _root_.GlobalTheory.X_sub_one_smul_graded : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ] (i : ι), (∀ y : M, (X i - 1 : MvPolynomial ι R) • y = 0 → y = 0) ∧ (∀ (n : ℤ) (z w : M), z ∈ ℳ n → z = (X i - 1 : MvPolynomial ι R) • w → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z = 0) ∧ (∀ y : M, ∃ n₀ : ℤ, ∀ n, n₀ ≤ n → ∃ y' ∈ ℳ n, ∃ w : M, y = y' + (X i - 1 : MvPolynomial ι R) • w) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ i
  exact ⟨fun y hy => eq_zero_of_X_sub_one_smul_eq_zero ℳ i hy,
    fun n z w hz h => _root_.GlobalTheory.exists_X_pow_smul_eq_zero_of_eq_X_sub_one_smul ℳ i hz h,
    fun y => _root_.GlobalTheory.exists_homogeneous_add_X_sub_one_smul ℳ i y⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFamilySaturating
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem _root_.GlobalTheory.exists_homogeneous_family_saturating : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [_root_.GlobalTheory.PolyGradedSMul ι ℳ] [Decomposition ℳ], (∀ i : ι, ∃ T : Finset M, ∀ y : M, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (T : Set M)) → ∃ (r : ℕ) (d : Fin r → ℤ) (g : Fin r → M), (∀ l, g l ∈ ℳ (d l)) ∧ ∀ (i : ι) (y : M), ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (Set.range g) := by
  intro ι _ _ R _ M _ _ _ _ ℳ _ _ hT
  choose T hT using hT
  choose S hS using fun m : M => _root_.GlobalTheory.exists_sum_grProj ℳ m
  classical
  let G : Finset (ℤ × M) := (Finset.univ.biUnion T).biUnion fun t =>
    (S t).image fun j => (j, _root_.GlobalTheory.GradedHilbert.proj ℳ j t)
  refine ⟨G.card, fun l => (G.equivFin.symm l).1.1, fun l => (G.equivFin.symm l).1.2,
    fun l => ?_, fun i y => ?_⟩
  · have hmem := (G.equivFin.symm l).2
    obtain ⟨t, -, hj⟩ := Finset.mem_biUnion.1 hmem
    obtain ⟨j, -, hjeq⟩ := Finset.mem_image.1 hj
    show (G.equivFin.symm l : ℤ × M).2 ∈ ℳ (G.equivFin.symm l : ℤ × M).1
    rw [← hjeq]
    exact _root_.GlobalTheory.GradedHilbert.proj_mem ℳ j t
  · obtain ⟨k, hk⟩ := hT i y
    refine ⟨k, Submodule.span_le.2 ?_ hk⟩
    intro t ht
    rw [← hS t]
    refine Submodule.sum_mem _ fun j hj => Submodule.subset_span ?_
    have hG : (j, _root_.GlobalTheory.GradedHilbert.proj ℳ j t) ∈ G :=
      Finset.mem_biUnion.2 ⟨t, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ht⟩,
        Finset.mem_image.2 ⟨j, hj, rfl⟩⟩
    exact ⟨G.equivFin ⟨_, hG⟩, by simp⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.BijOnKerAndExactOfQuasiIsoBaseChange
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem bijOn_ker_and_exact_of_quasiIso {R : Type} [CommRing R]
    {K C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : K ⟶ C) (h : QuasiIso φ) :
    Set.BijOn (φ.f 0).hom (LinearMap.ker (K.d 0 1).hom) (LinearMap.ker (C.d 0 1).hom) ∧
      (Function.Exact (C.d 0 1).hom (C.d 1 2).hom → Function.Exact (K.d 0 1).hom (K.d 1 2).hom) := by
  have h0 := (quasiIsoAt_zero_iff φ).1 inferInstance
  have h1 := (quasiIsoAt_succ_iff φ 0).1 inferInstance
  refine ⟨⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩, fun hC x => ⟨fun hx => ?_, ?_⟩⟩
  · have hx' : (K.d 0 1).hom x = 0 := hx
    change (C.d 0 1).hom ((φ.f 0).hom x) = 0
    rw [cochain_comm_apply, hx', map_zero]
  · have hx' : (K.d 0 1).hom x = 0 := hx
    have hy' : (K.d 0 1).hom y = 0 := hy
    exact sub_eq_zero.1 (h0.2 (x - y) (by rw [map_sub, hx', hy', sub_zero])
      (by rw [map_sub, hxy, sub_self]))
  · obtain ⟨x, hx, hx'⟩ := h0.1 y hy
    exact ⟨x, hx, hx'⟩
  · obtain ⟨z, hz⟩ := (hC ((φ.f 1).hom x)).1 (by rw [cochain_comm_apply, hx, map_zero])
    exact h1.2 x z hx hz
  · rintro ⟨w, rfl⟩
    exact cochain_d_d_apply K 0 1 2 w

theorem bijOn_ker_and_exact_of_quasiIso_baseChange (R R' : Type) [CommRing R] [CommRing R']
    [inst : Algebra R R'] (K C : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ C)
    (h : QuasiIso
      (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ)) :
    Set.BijOn ((φ.f 0).hom.baseChange R') (LinearMap.ker ((K.d 0 1).hom.baseChange R'))
        (LinearMap.ker ((C.d 0 1).hom.baseChange R')) ∧
      (Function.Exact ((C.d 0 1).hom.baseChange R') ((C.d 1 2).hom.baseChange R') →
        Function.Exact ((K.d 0 1).hom.baseChange R') ((K.d 1 2).hom.baseChange R')) := by
  have key := bijOn_ker_and_exact_of_quasiIso _ h
  clear h
  generalize hf : algebraMap R R' = f at key
  have e : inst = f.toAlgebra := Algebra.algebra_ext _ _ (fun r => by rw [hf]; rfl)
  subst e
  exact key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexExactAtOfMonomialBasis
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

noncomputable section

namespace GlobalTheory

variable {ι : Type} (R : Type) [CommRing R]

def Cube.above (w : Finset ι) : Cube.{0} ι R :=
  Cube.mk (fun s => ModuleCat.of R (PLift (w ⊆ s) →₀ R))
    (fun h => Finsupp.lmapDomain R R fun x => ⟨x.down.trans h⟩)
    (fun _ _ => Finsupp.mapDomain_id)
    (fun _ _ _ => Finsupp.mapDomain_comp.symm)

theorem cubeComplex_above_exactAt [LinearOrder ι] [Fintype ι] (w : Finset ι) {p : ℕ}
    (hp : p ≠ Fintype.card ι) : (cubeComplex (Cube.above R w)).ExactAt p := by
  by_cases hw : w = Finset.univ
  · subst hw
    have : Subsingleton (Cube.Term (Cube.above R (Finset.univ : Finset ι)) p) := by
      refine ⟨fun x y => funext fun s => ?_⟩
      refine Finsupp.ext fun a => absurd ?_ hp
      rw [← s.2, Finset.univ_subset_iff.1 a.down, Finset.card_univ]
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ShortComplex.isZero_homology_of_isZero_X₂ _
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Cube.Term _ p)))
  · obtain ⟨i, hi⟩ : ∃ i, i ∉ w := by
      by_contra! h
      exact hw (Finset.eq_univ_iff_forall.2 h)
    refine cubeComplex_exactAt_of_bijective _ i (fun s _ => ?_) p
    refine ⟨Finsupp.mapDomain_injective fun _ _ _ => Subsingleton.elim _ _,
      Finsupp.mapDomain_surjective fun x => ⟨⟨?_⟩, Subsingleton.elim _ _⟩⟩
    exact (Finset.subset_insert_iff_of_notMem hi).1 x.down

variable {R}

def monomialCoord {κ : Type} (T : κ → Finset ι) {s : Finset ι} {M : Type} [AddCommGroup M]
    [Module R M] (b : Module.Basis {a : κ // T a ⊆ s} R M) :
    M ≃ₗ[R] ⨁ a, (PLift (T a ⊆ s) →₀ R) :=
  b.repr ≪≫ₗ Finsupp.domLCongr (Equiv.sigmaPLiftEquivSubtype fun a => T a ⊆ s).symm ≪≫ₗ
    sigmaFinsuppLequivDFinsupp R

theorem monomialCoord_basis {κ : Type} [DecidableEq κ] (T : κ → Finset ι) {s : Finset ι} {M : Type}
    [AddCommGroup M] [Module R M] (b : Module.Basis {a : κ // T a ⊆ s} R M)
    (a : {a : κ // T a ⊆ s}) :
    monomialCoord T b (b a) =
      DirectSum.lof R κ (fun a => PLift (T a ⊆ s) →₀ R) a.1 (Finsupp.single ⟨a.2⟩ 1) := by
  simp only [monomialCoord, LinearEquiv.trans_apply, Module.Basis.repr_self, Finsupp.domLCongr_single]
  exact sigmaFinsuppEquivDFinsupp_single _ _

theorem cubeComplex_exactAt_of_monomialBasis (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (κ : Type) (T : κ → Finset ι) (A : Cube.{0} ι R)
    (b : ∀ s : Finset ι, Module.Basis {a : κ // T a ⊆ s} R (A.obj s))
    (hb : ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : κ // T a ⊆ s}),
      Cube.res A h (b s a) = b t ⟨a.1, a.2.trans h⟩)
    (p : ℕ) (hp : p ≠ Fintype.card ι) : (cubeComplex A).ExactAt p := by
  classical
  let e : A ≅ Cube.directSum fun a => Cube.above R (T a) :=
    Cube.isoMk (fun s => monomialCoord T (b s)) fun {s t} h x => by
      have : (monomialCoord T (b t)).toLinearMap ∘ₗ Cube.res A h =
          (DirectSum.lmap fun a => Finsupp.lmapDomain R R
            fun x : PLift (T a ⊆ s) => (⟨x.down.trans h⟩ : PLift (T a ⊆ t))) ∘ₗ
            (monomialCoord T (b s)).toLinearMap := by
        refine (b s).ext fun a => ?_
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hb, monomialCoord_basis,
          DirectSum.lmap_lof, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      exact congr($this x)
  exact (exactAt_iff_of_quasiIsoAt ((cubeFunctor ι R).mapIso e).hom p).2
    ((cubeComplex_directSum_exactAt_iff _ p).2 fun a => cubeComplex_above_exactAt R (T a) hp)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsWitnessesOfFormallySmoothQuotient
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exists_sum_mul_of_mem_span_range_sq {S : Type} [CommRing S] {r : ℕ} (g : Fin r → S)
    (x : S) (hx : x ∈ Ideal.span (Set.range g) * Ideal.span (Set.range g)) :
    ∃ b : Fin r → Fin r → S, x = ∑ k, ∑ l, b k l * (g k * g l) := by

  have hx' : x ∈ Ideal.span (Set.range fun p : Fin r × Fin r => g p.1 * g p.2) := by
    open Pointwise in
    have hset : Set.range g * Set.range g =
        Set.range fun p : Fin r × Fin r => g p.1 * g p.2 := by
      ext y
      simp [Set.mem_mul]
    open Pointwise in
    rwa [Ideal.span_mul_span', hset] at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hx'
  refine ⟨fun k l => c (k, l), ?_⟩
  rw [← hc, Fintype.sum_prod_type]
  simp only [smul_eq_mul]

theorem exists_witnesses_of_formallySmooth_quotient :
    ∀ (ι : Type) [Fintype ι] (R : Type) [CommRing R] (r : ℕ) (g : Fin r → MvPolynomial ι R), Algebra.FormallySmooth R (MvPolynomial ι R ⧸ Ideal.span (Set.range g)) → ∃ (a : ι → Fin r → MvPolynomial ι R) (b : Fin r → Fin r → Fin r → MvPolynomial ι R), ∀ j, aeval (fun i => X i + ∑ k, a i k * g k) (g j) = ∑ k, ∑ l, b j k l * (g k * g l) := by
  intro ι _ R _ r g hs
  set I : Ideal (MvPolynomial ι R) := Ideal.span (Set.range g) with hI
  have hsurj : Function.Surjective (Ideal.Quotient.mkₐ R I) := Ideal.Quotient.mkₐ_surjective R I

  obtain ⟨σ, hσ⟩ := (Algebra.FormallySmooth.iff_split_surjection _ hsurj).1 hs
  have hK : RingHom.ker (Ideal.Quotient.mkₐ R I).toRingHom = I := by
    ext x
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem

  have hlift : ∀ i : ι, ∃ y : MvPolynomial ι R,
      Ideal.Quotient.mk _ y = σ (Ideal.Quotient.mkₐ R I (X i)) :=
    fun i => Ideal.Quotient.mk_surjective _
  choose y hy using hlift

  have hdiff : ∀ i, y i - X i ∈ I := by
    intro i
    have h1 := congrArg (Ideal.Quotient.mkₐ R I).kerSquareLift (hy i)
    rw [AlgHom.kerSquareLift_mk, ← AlgHom.comp_apply, hσ, AlgHom.id_apply] at h1
    exact Ideal.Quotient.eq.1 h1
  choose a ha using fun i => (Submodule.mem_span_range_iff_exists_fun (MvPolynomial ι R)).1 (hdiff i)
  have hy' : ∀ i, X i + ∑ k, a i k * g k = y i := by
    intro i
    have := ha i
    simp only [smul_eq_mul] at this
    rw [this]
    ring

  have hcomp : (Ideal.Quotient.mkₐ R _).comp
      (aeval fun i => X i + ∑ k, a i k * g k : MvPolynomial ι R →ₐ[R] MvPolynomial ι R) =
      σ.comp (Ideal.Quotient.mkₐ R I) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, aeval_X, hy', AlgHom.comp_apply, ← hy i]
    rfl

  have hmem : ∀ j, aeval (fun i => X i + ∑ k, a i k * g k) (g j) ∈ I * I := by
    intro j
    have hgj : Ideal.Quotient.mkₐ R I (g j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
    have h2 := AlgHom.congr_fun hcomp (g j)
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hgj, map_zero, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, hK, pow_two] at h2
    exact h2
  choose b hb using fun j => exists_sum_mul_of_mem_span_range_sq g _ (hmem j)
  exact ⟨a, b, hb⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.TopClassSurjective
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

noncomputable section

namespace GlobalTheory.CubeTop

variable {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type} [CommRing R]

omit [LinearOrder ι] in
theorem univ_subset {n : ℕ} (hn : Fintype.card ι = n) (s : {s : Finset ι // s.card = n}) :
    (Finset.univ : Finset ι) ⊆ s.1 :=
  (Finset.eq_univ_of_card s.1 (s.2.trans hn.symm)).ge

def topTerm (A : Cube.{0} ι R) {n : ℕ} (hn : Fintype.card ι = n) :
    A.obj Finset.univ →ₗ[R] Cube.Term A n :=
  LinearMap.pi fun s => Cube.res A (univ_subset hn s)

omit [LinearOrder ι] in
theorem topTerm_surjective (A : Cube.{0} ι R) {n : ℕ} (hn : Fintype.card ι = n) :
    Function.Surjective (topTerm A hn) := by
  intro x
  refine ⟨x ⟨Finset.univ, hn⟩, funext ?_⟩
  rintro ⟨s, hs⟩
  obtain rfl := Finset.eq_univ_of_card s (hs.trans hn.symm)
  exact Cube.res_self A _ _

theorem topTerm_res_mem (A : Cube.{0} ι R) {p : ℕ} (hn : Fintype.card ι = p + 1) (i : ι)
    (x : A.obj (Finset.univ.erase i)) :
    ∃ y, Cube.d A p y = topTerm A hn (Cube.res A (Finset.erase_subset i _) x) := by
  let y : ∀ s, A.obj s := Pi.single (Finset.univ.erase i) (cubeSign Finset.univ i • x)
  refine ⟨fun s => y s.1, funext ?_⟩
  rintro ⟨s, hs⟩
  obtain rfl := Finset.eq_univ_of_card s (hs.trans hn.symm)
  rw [Cube.d_apply_eq_totalD A _ y (fun _ => rfl), Cube.totalD_apply, Finset.sum_eq_single i]
  · simp only [y, Pi.single_eq_same, map_zsmul, cubeSign_smul_smul]
    exact (Cube.res_self A _ _).symm
  · intro j _ hji
    have : (Finset.univ.erase j : Finset ι) ≠ Finset.univ.erase i := fun h => by
      have : j ∈ (Finset.univ.erase i : Finset ι) := by simp [hji]
      rw [← h] at this
      simp at this
    simp only [y, Pi.single_eq_of_ne this, map_zero, smul_zero]
  · simp

theorem d_top (A : Cube.{0} ι R) :
    (cubeComplex A).d (Fintype.card ι) (Fintype.card ι + 1) = 0 := by
  rw [cubeComplex_d]
  have := Cube.subsingleton_term A (Nat.lt_succ_self (Fintype.card ι))
  exact ModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)

def topClass (A : Cube.{0} ι R) :
    A.obj Finset.univ →ₗ[R] (cubeComplex A).homology (Fintype.card ι) :=
  ((cubeComplex A).pOpcycles (Fintype.card ι) ≫
    ((cubeComplex A).isoHomologyι (Fintype.card ι) (Fintype.card ι + 1) (by simp)
      (d_top A)).inv).hom ∘ₗ topTerm A rfl

theorem topClass_surjective (A : Cube.{0} ι R) : Function.Surjective (topClass A) :=
  ((ModuleCat.epi_iff_surjective ((cubeComplex A).pOpcycles (Fintype.card ι) ≫
    ((cubeComplex A).isoHomologyι (Fintype.card ι) (Fintype.card ι + 1) (by simp)
      (d_top A)).inv)).1 inferInstance).comp (topTerm_surjective A rfl)

theorem topClass_res (A : Cube.{0} ι R) (i : ι) (x : A.obj (Finset.univ.erase i)) :
    topClass A (Cube.res A (Finset.erase_subset i _) x) = 0 := by
  have key : ∀ (n : ℕ) (hn : Fintype.card ι = n), ((cubeComplex A).pOpcycles n).hom
      (topTerm A hn (Cube.res A (Finset.erase_subset i _) x)) = 0 := by
    intro n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 :=
      Nat.exists_eq_succ_of_ne_zero (hn ▸ (Fintype.card_pos_iff.2 ⟨i⟩).ne')
    obtain ⟨y, hy⟩ := topTerm_res_mem A hn i x
    have := (cubeComplex A).d_pOpcycles p (p + 1)
    rw [cubeComplex_d] at this
    rw [← hy]
    exact congr(($this).hom y)
  have := key _ rfl
  let g := ((cubeComplex A).isoHomologyι (Fintype.card ι) (Fintype.card ι + 1) (by simp)
    (d_top A)).inv.hom
  exact (congrArg g this).trans (map_zero g)

theorem span_topClass {κ : Type} (T : κ → Finset ι) (A : Cube.{0} ι R)
    (b : ∀ s : Finset ι, Module.Basis {a : κ // T a ⊆ s} R (A.obj s))
    (hb : ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : κ // T a ⊆ s}),
      Cube.res A h (b s a) = b t ⟨a.1, a.2.trans h⟩) :
    Submodule.span R ((fun a : κ => topClass A (b Finset.univ ⟨a, Finset.subset_univ _⟩)) ''
      {a | T a = Finset.univ}) = ⊤ := by
  rw [eq_top_iff, ← LinearMap.range_eq_top.2 (topClass_surjective A), LinearMap.range_eq_map,
    ← (b Finset.univ).span_eq, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  by_cases h : T a.1 = Finset.univ
  · exact Submodule.subset_span ⟨a.1, h, rfl⟩
  · obtain ⟨i, hi⟩ : ∃ i, i ∉ T a.1 := by
      simpa [Finset.eq_univ_iff_forall] using h
    have := topClass_res A i (b _ ⟨a.1, Finset.subset_erase.2 ⟨Finset.subset_univ _, hi⟩⟩)
    rw [hb] at this
    rw [this]
    exact zero_mem _

theorem main : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (κ : Type) (T : κ → Finset ι) (A : Cube.{0} ι R) (b : ∀ s : Finset ι, Module.Basis {a : κ // T a ⊆ s} R (A.obj s)), (∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : κ // T a ⊆ s}), Cube.res A h (b s a) = b t ⟨a.1, a.2.trans h⟩) → ((∀ a, T a ≠ Finset.univ) → (cubeComplex A).ExactAt (Fintype.card ι)) ∧ ({a | T a = Finset.univ}.Finite → Module.Finite R ((cubeComplex A).homology (Fintype.card ι))) := by
  intro ι _ _ R _ κ T A b hb
  have h := span_topClass T A b hb
  refine ⟨fun hT => ?_, fun hT => ⟨h ▸ Submodule.fg_span (hT.image _)⟩⟩
  · rw [Set.eq_empty_of_forall_notMem (s := {a | T a = Finset.univ}) hT, Set.image_empty,
      Submodule.span_empty] at h
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have := (Submodule.subsingleton_iff R).1 (subsingleton_of_bot_eq_top h)
    exact ModuleCat.isZero_of_subsingleton _

end GlobalTheory.CubeTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsMonomialBasisCechCubePolynomialGrading
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SpanLaurentMonomialEqHomLoc
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem span_laurentMonomial_eq_homLoc :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (s : Finset ι) (n : ℤ)
      (v : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} →
        LocalizedModule.Away (xProd R s) (MvPolynomial ι R)),
      (∀ a (k : ℕ) (m : ι →₀ ℕ), (∀ i, (m i : ℤ) = a.1 i + if i ∈ s then (k : ℤ) else 0) →
        v a = awayFrac (MvPolynomial ι R) (xProd R s) k (monomial m 1)) →
      Submodule.span R (Set.range v) = homLoc (polyGrading ι R) s n := by
  intro ι _ _ R _ s n v hv
  have hsum (k : ℤ) : ∑ i, (if i ∈ s then k else 0) = k * s.card := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hdeg (m : ι →₀ ℕ) : ((m.degree : ℕ) : ℤ) = ∑ i, (m i : ℤ) := by
    rw [Finsupp.degree_eq_sum]; push_cast; rfl
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    let k : ℕ := ∑ i, (a.1 i).natAbs
    have hk (i : ι) : 0 ≤ a.1 i + if i ∈ s then (k : ℤ) else 0 := by
      split_ifs with h
      · have : (a.1 i).natAbs ≤ k :=
          Finset.single_le_sum (f := fun i => (a.1 i).natAbs) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ i)
        omega
      · simpa using a.2.2 i h
    let m : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm
      fun i => (a.1 i + if i ∈ s then (k : ℤ) else 0).toNat
    have hm (i : ι) : (m i : ℤ) = a.1 i + if i ∈ s then (k : ℤ) else 0 :=
      Int.toNat_of_nonneg (hk i)
    rw [hv a k m hm]
    refine awayFrac_mem_homLoc (monomial_mem_polyGrading m 1) ?_
    rw [hdeg, Finset.sum_congr rfl fun i _ => hm i, Finset.sum_add_distrib, a.2.1, hsum]
  · rintro _ ⟨k, p, hp, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [p.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have hd := mem_polyGrading_iff.1 hp m (mem_support_iff.1 hm)
    have e : monomial m (AddMonoidAlgebra.coeff p m) = AddMonoidAlgebra.coeff p m • (monomial m 1 : MvPolynomial ι R) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [e, LinearMap.map_smul_of_tower]
    refine Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨⟨fun i => m i - if i ∈ s then (k : ℤ) else 0, ?_, fun i hi => ?_⟩, hv _ k m fun i => ?_⟩)
    · rw [Finset.sum_sub_distrib, hsum, ← hdeg, hd, add_sub_cancel_right]
    · simp [hi]
    · simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LinearIndependentLaurentMonomial
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem linearIndependent_laurentMonomial :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (s : Finset ι) (n : ℤ) (v : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} → LocalizedModule.Away (xProd R s) (MvPolynomial ι R)), (∀ a (k : ℕ) (m : ι →₀ ℕ), (∀ i, (m i : ℤ) = a.1 i + if i ∈ s then (k : ℤ) else 0) → v a = awayFrac (MvPolynomial ι R) (xProd R s) k (monomial m 1)) → LinearIndependent R v := by
  intro ι _ _ R _ s n v hv
  rw [linearIndependent_iff']
  intro T g hg j hj
  let k : ℕ := T.sup fun a => Finset.univ.sup fun i => (a.1 i).natAbs
  let m : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} → (ι →₀ ℕ) := fun a =>
    Finsupp.equivFunOnFinite.symm fun i => (a.1 i + if i ∈ s then (k : ℤ) else 0).toNat
  have hm : ∀ a ∈ T, ∀ i, (m a i : ℤ) = a.1 i + if i ∈ s then (k : ℤ) else 0 := by
    intro a ha i
    have hk : (a.1 i).natAbs ≤ k :=
      (Finset.le_sup (f := fun i => (a.1 i).natAbs) (Finset.mem_univ i)).trans
        (Finset.le_sup (f := fun a : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} =>
          Finset.univ.sup fun i => (a.1 i).natAbs) ha)
    refine Int.toNat_of_nonneg ?_
    split_ifs with hi
    · omega
    · simpa using a.2.2 i hi
  have hinj : ∀ a ∈ T, m a = m j → a = j := by
    intro a ha e
    refine Subtype.ext (funext fun i => ?_)
    have h1 := hm a ha i
    have h2 := hm j hj i
    rw [e, h2] at h1
    exact (add_right_cancel h1).symm
  have h0 : awayFrac (MvPolynomial ι R) (xProd R s) k
      (∑ a ∈ T, g a • monomial (m a) (1 : R)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hg]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hv a k (m a) (hm a ha), LinearMap.map_smul_of_tower]
  have h1 := congrArg (AddMonoidAlgebra.coeff · (m j))
    ((map_eq_zero_iff _ (awayFrac_injective (xProd_smul_injective s) k)).1 h0)
  rw [coeff_sum, Finset.sum_eq_single j, coeff_smul, coeff_monomial, if_pos rfl] at h1
  · simpa using h1
  · intro a ha hne
    rw [coeff_smul, coeff_monomial, if_neg fun e => hne (hinj a ha e), smul_zero]
  · exact fun h => absurd hj h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsMonomialBasisCechCubePolynomialGrading
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem exists_xProd_pow_smul_monomial {ι : Type} [DecidableEq ι] (R : Type) [CommRing R]
    (s : Finset ι) (j : ℕ) (m : ι →₀ ℕ) :
    ∃ m' : ι →₀ ℕ, (∀ i, m' i = m i + if i ∈ s then j else 0) ∧
      xProd R s ^ j • (monomial m 1 : MvPolynomial ι R) = monomial m' 1 := by
  refine ⟨m + ∑ i ∈ s, Finsupp.single i j, fun i => ?_, ?_⟩
  · simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  · rw [smul_eq_mul, xProd, ← Finset.prod_pow, add_comm]
    simp only [X_pow_eq_monomial]
    rw [← monomial_sum_one, monomial_mul, one_mul]

theorem awayFrac_monomial_congr {ι : Type} [DecidableEq ι] (R : Type) [CommRing R]
    (s : Finset ι) (a : ι → ℤ) {k j : ℕ} {m m' : ι →₀ ℕ}
    (hm : ∀ i, (m i : ℤ) = a i + if i ∈ s then (k : ℤ) else 0)
    (hm' : ∀ i, (m' i : ℤ) = a i + if i ∈ s then (j : ℤ) else 0) :
    awayFrac (MvPolynomial ι R) (xProd R s) k (monomial m 1) =
      awayFrac (MvPolynomial ι R) (xProd R s) j (monomial m' 1) := by
  refine awayFrac_eq_iff.2 ⟨0, ?_⟩
  obtain ⟨u, hu, eu⟩ := exists_xProd_pow_smul_monomial R s (0 + j) m
  obtain ⟨w, hw, ew⟩ := exists_xProd_pow_smul_monomial R s (0 + k) m'
  rw [eu, ew]
  congr 2
  ext i
  have h1 := hu i
  have h2 := hw i
  have h3 := hm i
  have h4 := hm' i
  split_ifs at h1 h2 h3 h4 <;> omega

theorem exists_laurent_numerator {ι : Type} [DecidableEq ι] [Fintype ι] (s : Finset ι)
    (a : ι → ℤ) (ha : ∀ i, i ∉ s → 0 ≤ a i) :
    ∃ (k : ℕ) (m : ι →₀ ℕ), ∀ i, (m i : ℤ) = a i + if i ∈ s then (k : ℤ) else 0 := by
  refine ⟨Finset.univ.sup fun i => (a i).natAbs, Finsupp.equivFunOnFinite.symm fun i =>
    (a i + if i ∈ s then ((Finset.univ.sup fun i => (a i).natAbs : ℕ) : ℤ) else 0).toNat,
    fun i => Int.toNat_of_nonneg ?_⟩
  have hk := Finset.le_sup (f := fun i => (a i).natAbs) (Finset.mem_univ i)
  split_ifs with hi
  · omega
  · simpa using ha i hi

theorem exists_basis_grCube_polyGrading :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (n : ℤ), ∃ b : ∀ s : Finset ι, Module.Basis {a : {a : ι → ℤ // ∑ i, a i = n} // Finset.univ.filter (fun i => a.1 i < 0) ⊆ s} R ((grCube ι (polyGrading ι R) n).obj s), ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : {a : ι → ℤ // ∑ i, a i = n} // Finset.univ.filter (fun i => a.1 i < 0) ⊆ s}), Cube.res (grCube ι (polyGrading ι R) n) h (b s a) = b t ⟨a.1, a.2.trans h⟩ := by
  intro ι _ _ R _ n
  have hiff : ∀ (s : Finset ι) (a : ι → ℤ),
      Finset.univ.filter (fun i => a i < 0) ⊆ s ↔ ∀ i, i ∉ s → 0 ≤ a i := by
    intro s a
    simp only [Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact forall_congr' fun i => by rw [← not_lt]; exact not_imp_not.symm
  have key : ∀ s : Finset ι, ∃ b : Module.Basis {a : {a : ι → ℤ // ∑ i, a i = n} //
      Finset.univ.filter (fun i => a.1 i < 0) ⊆ s} R (homLoc (polyGrading ι R) s n),
      ∀ a (k : ℕ) (m : ι →₀ ℕ), (∀ i, (m i : ℤ) = a.1.1 i + if i ∈ s then (k : ℤ) else 0) →
        (b a).1 = awayFrac (MvPolynomial ι R) (xProd R s) k (monomial m 1) := by
    intro s
    choose k m hm using fun a : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} =>
      exists_laurent_numerator s a.1 a.2.2
    let v := fun a => awayFrac (MvPolynomial ι R) (xProd R s) (k a) (monomial (m a) 1)
    have hv : ∀ a (j : ℕ) (m' : ι →₀ ℕ),
        (∀ i, (m' i : ℤ) = a.1 i + if i ∈ s then (j : ℤ) else 0) →
        v a = awayFrac (MvPolynomial ι R) (xProd R s) j (monomial m' 1) :=
      fun a j m' h => awayFrac_monomial_congr R s a.1 (hm a) h
    let e : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} ≃
        {a : {a : ι → ℤ // ∑ i, a i = n} // Finset.univ.filter (fun i => a.1 i < 0) ⊆ s} :=
      { toFun := fun a => ⟨⟨a.1, a.2.1⟩, (hiff s a.1).2 a.2.2⟩
        invFun := fun a => ⟨a.1.1, a.1.2, (hiff s a.1.1).1 a.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    refine ⟨((Module.Basis.span (linearIndependent_laurentMonomial ι R s n v hv)).map
      (LinearEquiv.ofEq _ _ (span_laurentMonomial_eq_homLoc ι R s n v hv))).reindex e, fun a j m' h => ?_⟩
    rw [Module.Basis.reindex_apply, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
      Module.Basis.span_apply]
    exact hv _ j m' h
  choose b hb using key
  refine ⟨b, fun s t h a => Subtype.ext ?_⟩
  obtain ⟨k, m, hm⟩ := exists_laurent_numerator s a.1.1 ((hiff s _).1 a.2)
  obtain ⟨u, hu, eu⟩ := exists_xProd_pow_smul_monomial R (t \ s) k m
  change locRes X (MvPolynomial ι R) h (b s a).1 = (b t ⟨a.1, a.2.trans h⟩).1
  rw [hb s a k m hm, locRes_awayFrac X h (Finset.prod_sdiff h).symm, eu]
  refine (hb t _ k u fun i => ?_).symm
  have h1 := hu i
  have h2 := hm i
  have h3 := @h i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsMonomialBasisCechCubePolynomialGradingStatement
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
theorem _root_.GlobalTheory.T.exists_monomial_basis_cechCube_polynomialGrading : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (n : ℤ), ∃ b : ∀ s : Finset ι, Module.Basis {a : {a : ι → ℤ // ∑ i, a i = n} // Finset.univ.filter (fun i => a.1 i < 0) ⊆ s} R ((grCube ι (polyGrading ι R) n).obj s), ∀ (s t : Finset ι) (h : s ⊆ t) (a : {a : {a : ι → ℤ // ∑ i, a i = n} // Finset.univ.filter (fun i => a.1 i < 0) ⊆ s}), Cube.res (grCube ι (polyGrading ι R) n) h (b s a) = b t ⟨a.1, a.2.trans h⟩ := by
  first | exact @GlobalTheory.exists_basis_grCube_polyGrading | exact GlobalTheory.exists_basis_grCube_polyGrading | (intros; apply GlobalTheory.exists_basis_grCube_polyGrading <;> assumption)
end
end
