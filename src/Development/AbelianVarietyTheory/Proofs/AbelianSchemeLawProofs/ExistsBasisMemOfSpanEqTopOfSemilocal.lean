module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsBasisMemOfSpanEqTopOfSemilocal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SemilocalBasis

open scoped Pointwise

theorem exists_forall_notMem {A V J : Type*} [CommRing A] [IsLocalRing A]
    [Infinite (IsLocalRing.ResidueField A)] [AddCommGroup V] [Module A V] [Finite J]
    (p : J → Submodule A V) (hp : ∀ i, p i ≠ ⊤)
    (hm : ∀ i, ∀ a ∈ IsLocalRing.maximalIdeal A, ∀ x, a • x ∈ p i) : ∃ x : V, ∀ i, x ∉ p i := by
  classical
  have := Fintype.ofFinite J
  by_contra! h
  have hcov : ⋃ i ∈ (Finset.univ : Finset J),
      (0 : V) +ᵥ ((p i).toAddSubgroup : Set V) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun a => ?_
    obtain ⟨i, hi⟩ := h a
    simp only [zero_vadd, Set.mem_iUnion]
    exact ⟨i, Finset.mem_univ i, hi⟩
  obtain ⟨k, -, hk⟩ := AddSubgroup.exists_finiteIndex_of_leftCoset_cover hcov
  have hfin : Finite (V ⧸ p k) := AddSubgroup.finite_quotient_of_finiteIndex (H := (p k).toAddSubgroup)
  obtain ⟨x, hx⟩ : ∃ x, x ∉ p k := by
    by_contra! h'
    exact hp k (Submodule.eq_top_iff'.mpr h')
  choose s hs using IsLocalRing.residue_surjective (R := A)
  have hinj : Function.Injective
      (fun c : IsLocalRing.ResidueField A => (p k).mkQ (s c • x)) := by
    intro c d hcd
    by_contra hne
    have h1 : (s c - s d) • x ∈ p k := by
      rw [sub_smul]
      exact (Submodule.Quotient.eq _).mp hcd
    have h2 : IsUnit (s c - s d) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, hs, hs]
      exact sub_ne_zero.mpr hne
    exact hx (((p k).smul_mem_iff_of_isUnit h2).mp h1)
  have := Finite.of_injective _ hinj
  exact not_finite (IsLocalRing.ResidueField A)

noncomputable def red {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] {n : ℕ}
    (e : Module.Basis (Fin n) B M) (I : Ideal B) : M →ₗ[B] (Fin n → B ⧸ I) :=
  LinearMap.pi fun j => (Submodule.mkQ I).comp (e.coord j)

theorem red_apply {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] {n : ℕ}
    (e : Module.Basis (Fin n) B M) (I : Ideal B) (x : M) (j : Fin n) :
    red e I x j = Ideal.Quotient.mk I (e.repr x j) := rfl

theorem red_surjective {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] {n : ℕ}
    (e : Module.Basis (Fin n) B M) (I : Ideal B) : Function.Surjective (red e I) := by
  intro y
  choose s hs using Ideal.Quotient.mk_surjective (I := I)
  refine ⟨e.equivFun.symm fun j => s (y j), ?_⟩
  ext j
  rw [red_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hs]

theorem exists_linearIndependent {A B M : Type*} [CommRing A] [IsLocalRing A]
    [Infinite (IsLocalRing.ResidueField A)] [CommRing B] [Algebra A B]
    [Finite (MaximalSpectrum B)] [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    {n : ℕ} (e : Module.Basis (Fin n) B M) (N : Submodule A M)
    (hm : ∀ m : MaximalSpectrum B,
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ m.asIdeal)
    (hN : Submodule.span B (N : Set M) = ⊤) (k : ℕ) (hk : k ≤ n) :
    ∃ v : Fin k → M, (∀ i, v i ∈ N) ∧ ∀ m : MaximalSpectrum B,
      LinearIndependent (B ⧸ m.asIdeal) (fun i => red e m.asIdeal (v i)) := by
  induction k with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0, fun _ => linearIndependent_empty_type⟩
  | succ k ih =>
    obtain ⟨v, hvN, hv⟩ := ih (by omega)
    let W : ∀ m : MaximalSpectrum B, Submodule (B ⧸ m.asIdeal) (Fin n → B ⧸ m.asIdeal) :=
      fun m => Submodule.span _ (Set.range fun i => red e m.asIdeal (v i))
    let q : MaximalSpectrum B → Submodule B M :=
      fun m => ((W m).restrictScalars B).comap (red e m.asIdeal)
    let p : MaximalSpectrum B → Submodule A N :=
      fun m => ((q m).restrictScalars A).comap N.subtype
    obtain ⟨x, hx⟩ := exists_forall_notMem p (fun m h => by
      have := m.isMaximal
      letI := Ideal.Quotient.field m.asIdeal
      have h1 : q m = ⊤ := by
        rw [eq_top_iff, ← hN, Submodule.span_le]
        intro y hy
        have : (⟨y, hy⟩ : N) ∈ p m := h ▸ Submodule.mem_top
        exact this
      have h2 : W m = ⊤ := by
        rw [eq_top_iff]
        intro y _
        obtain ⟨z, rfl⟩ := red_surjective e m.asIdeal y
        have : z ∈ q m := h1 ▸ Submodule.mem_top
        exact this
      have h3 : Module.finrank (B ⧸ m.asIdeal) (W m) = k := by
        have := finrank_span_eq_card (hv m)
        simpa using this
      rw [h2] at h3
      simp at h3
      omega) (fun m a ha y => by
      have h0 : red e m.asIdeal (a • (y : M)) = 0 := by
        ext j
        rw [red_apply, ← algebraMap_smul B, map_smul, Finsupp.smul_apply, smul_eq_mul,
          Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right _ _ (hm m (Ideal.mem_map_of_mem _ ha))
      change red e m.asIdeal (a • (y : M)) ∈ W m
      rw [h0]
      exact zero_mem _)
    refine ⟨Fin.cons (x : M) v, fun i => ?_, fun m => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact x.2
      · exact hvN j
    · have := m.isMaximal
      letI := Ideal.Quotient.field m.asIdeal
      have h1 : (fun i => red e m.asIdeal (Fin.cons (α := fun _ => M) (x : M) v i)) =
          Fin.cons (red e m.asIdeal x) (fun i => red e m.asIdeal (v i)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      rw [h1, linearIndependent_finCons]
      exact ⟨hv m, hx m⟩

end SemilocalBasis

theorem exists_basis_mem_of_span_eq_top_of_semilocal :
    ∀ (A B M : Type) [CommRing A] [IsLocalRing A] [Infinite (IsLocalRing.ResidueField A)] [CommRing B] [Algebra A B] [Finite (MaximalSpectrum B)] [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] (n : ℕ) (_ : Module.Basis (Fin n) B M) (N : Submodule A M), (∀ m : MaximalSpectrum B, (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ m.asIdeal) → Submodule.span B (N : Set M) = ⊤ → ∃ b : Module.Basis (Fin n) B M, ∀ i, b i ∈ N := by
  intro A B M _ _ _ _ _ _ _ _ _ _ n e N hm hN
  obtain ⟨v, hvN, hv⟩ := SemilocalBasis.exists_linearIndependent e N hm hN n le_rfl
  have hu : IsUnit (e.det v) := by
    by_contra hne
    obtain ⟨I, hI, hmem⟩ := exists_max_ideal_of_mem_nonunits hne
    letI := Ideal.Quotient.field I
    have h1 := hv ⟨I, hI⟩
    have h2 : IsUnit ((e.toMatrix v).map (Ideal.Quotient.mk I)) :=
      Matrix.linearIndependent_cols_iff_isUnit.mp h1
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      ← Module.Basis.det_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hmem] at h2
    exact not_isUnit_zero h2
  obtain ⟨hli, hsp⟩ := e.is_basis_iff_det.mpr hu
  exact ⟨Module.Basis.mk hli hsp.ge, fun i => by simpa using hvN i⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankTotalDegreeImageGrowth
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace DegreeGrowth

variable {K B : Type} [Field K] [CommRing B] [Algebra K B]

def boxSpan (K : Type) {B : Type} [Field K] [CommRing B] [Algebra K B] {s n : ℕ}
    (y : Fin s → B) (b : Fin n → B) (D : ℕ) : Submodule K B :=
  Submodule.span K (Set.range fun al : (Fin s → Fin (D + 1)) × Fin n =>
    (∏ i, y i ^ (al.1 i : ℕ)) * b al.2)

theorem mem_boxSpan {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D : ℕ) (a : Fin s → ℕ)
    (ha : ∀ i, a i ≤ D) (l : Fin n) : (∏ i, y i ^ a i) * b l ∈ boxSpan K y b D :=
  Submodule.subset_span ⟨(fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩, l), rfl⟩

theorem finrank_boxSpan_le {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D : ℕ) :
    Module.finrank K (boxSpan K y b D) ≤ (D + 1) ^ s * n := by
  have := finrank_range_le_card (R := K) (fun al : (Fin s → Fin (D + 1)) × Fin n =>
    (∏ i, y i ^ (al.1 i : ℕ)) * b al.2)
  refine le_trans this ?_
  simp

instance finite_boxSpan {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D : ℕ) :
    Module.Finite K (boxSpan K y b D) :=
  Module.Finite.span_of_finite K (Set.finite_range _)

theorem monomial_mul_mem {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D d : ℕ) (a : Fin s → ℕ)
    (ha : ∀ i, a i ≤ d) {x : B} (hx : x ∈ boxSpan K y b D) :
    (∏ i, y i ^ a i) * x ∈ boxSpan K y b (D + d) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨c, l⟩, rfl⟩ := hx
    have h := mem_boxSpan (K := K) y b (D + d) (fun i => (c i : ℕ) + a i)
      (fun i => add_le_add (Nat.le_of_lt_succ (c i).2) (ha i)) l
    simp only [pow_add, Finset.prod_mul_distrib] at h
    convert h using 1
    ring
  | zero => simp
  | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem boxSpan_mono {s n : ℕ} (y : Fin s → B) (b : Fin n → B) {D E : ℕ} (h : D ≤ E) :
    boxSpan K y b D ≤ boxSpan K y b E := by
  intro x hx
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa using monomial_mul_mem y b D d (fun _ => 0) (fun _ => Nat.zero_le _) hx

theorem exists_aeval_mul_mem {s n : ℕ} (y : Fin s → B) (b : Fin n → B)
    (p : MvPolynomial (Fin s) K) {x : B} (hx : ∃ D, x ∈ boxSpan K y b D) :
    ∃ D, MvPolynomial.aeval y p * x ∈ boxSpan K y b D := by
  induction p using MvPolynomial.induction_on'' with
  | C a =>
    obtain ⟨D, hD⟩ := hx
    refine ⟨D, ?_⟩
    rw [MvPolynomial.aeval_C, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hD
  | monomial_add a c f _ _ h1' h2 =>
    obtain ⟨D1, h1⟩ := h2
    obtain ⟨D2, h2⟩ := h1'
    refine ⟨max D1 D2, ?_⟩
    rw [map_add (f := _), add_mul]
    exact add_mem (boxSpan_mono y b (le_max_left _ _) h1) (boxSpan_mono y b (le_max_right _ _) h2)
  | mul_X p i h =>
    obtain ⟨D, hD⟩ := h
    refine ⟨D + 1, ?_⟩
    have := monomial_mul_mem y b D 1 (Pi.single i 1)
      (fun j => by by_cases hj : j = i <;> simp [hj]) hD
    have e : ∏ j, y j ^ (Pi.single i 1 : Fin s → ℕ) j = y i := by
      rw [Finset.prod_eq_single i] <;> simp +contextual
    rw [e] at this
    rw [map_mul, MvPolynomial.aeval_X]
    convert this using 1
    ring

theorem mul_mem_boxSpan {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D d : ℕ) (z : B)
    (hz : ∀ l, z * b l ∈ boxSpan K y b d) {x : B} (hx : x ∈ boxSpan K y b D) :
    z * x ∈ boxSpan K y b (d + D) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨c, l⟩, rfl⟩ := hx
    have h := monomial_mul_mem y b d D (fun i => (c i : ℕ))
      (fun i => Nat.le_of_lt_succ (c i).2) (hz l)
    convert h using 1
    ring
  | zero => simp
  | add x z _ _ hx hz => rw [mul_add]; exact add_mem hx hz
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem pow_mul_mem_boxSpan {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D d : ℕ) (z : B)
    (hz : ∀ l, z * b l ∈ boxSpan K y b d) (k : ℕ) {x : B} (hx : x ∈ boxSpan K y b D) :
    z ^ k * x ∈ boxSpan K y b (k * d + D) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    have := mul_mem_boxSpan y b _ d z hz ih
    rw [show (k + 1) * d + D = d + (k * d + D) by ring, show z ^ (k + 1) * x = z * (z ^ k * x) by ring]
    exact this

theorem prod_mul_mem_boxSpan {s n : ℕ} (y : Fin s → B) (b : Fin n → B) (D d : ℕ) {I : Type}
    (r : I → B) (hr : ∀ i l, r i * b l ∈ boxSpan K y b d) (S : Finset I) (a : I → ℕ) {x : B}
    (hx : x ∈ boxSpan K y b D) :
    (∏ i ∈ S, r i ^ a i) * x ∈ boxSpan K y b ((∑ i ∈ S, a i) * d + D) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hx
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, _root_.mul_assoc, add_mul, add_assoc]
    exact pow_mul_mem_boxSpan y b _ d (r i) (hr i) (a i) ih

theorem upper {s n m : ℕ} (y : Fin s → B) (b : Fin n → B)
    (hall : ∀ x : B, ∃ D, x ∈ boxSpan K y b D) (r : Fin m → B) :
    ∃ C : ℕ, ∀ t : ℕ, 1 ≤ t →
      Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map
        (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) ≤ C * t ^ s := by
  choose f hf using hall
  obtain ⟨d, hd⟩ : ∃ d, ∀ il : Fin m × Fin n, f (r il.1 * b il.2) ≤ d :=
    (Set.finite_range fun il : Fin m × Fin n => f (r il.1 * b il.2)).bddAbove.imp
      fun d hd il => hd ⟨il, rfl⟩
  have hr : ∀ i l, r i * b l ∈ boxSpan K y b d := fun i l =>
    boxSpan_mono y b (hd (i, l)) (hf _)
  refine ⟨n * (d + f 1 + 1) ^ s, fun t ht => ?_⟩
  have hle : (MvPolynomial.restrictTotalDegree (Fin m) K t).map
        (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap ≤
        boxSpan K y b (t * d + f 1) := by
    rintro _ ⟨p, hp, rfl⟩
    have hp' : p.totalDegree ≤ t := (MvPolynomial.mem_restrictTotalDegree _ _ _).1 hp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [p.as_sum, map_sum]
    refine Submodule.sum_mem _ fun a ha => ?_
    have h1 := prod_mul_mem_boxSpan y b (f 1) d r hr a.support a (hf 1)
    have h2 : ∑ i ∈ a.support, a i ≤ t := (MvPolynomial.le_totalDegree ha).trans hp'
    rw [AlgHom.toLinearMap_apply, MvPolynomial.aeval_monomial, ← Algebra.smul_def]
    refine Submodule.smul_mem _ _ ?_
    rw [_root_.mul_one] at h1
    exact boxSpan_mono y b (by gcongr) h1
  refine (Submodule.finrank_mono hle).trans ((finrank_boxSpan_le y b _).trans ?_)
  rw [mul_comm, _root_.mul_assoc, ← mul_pow]
  gcongr
  nlinarith

theorem lower {s m : ℕ} (φ : MvPolynomial (Fin s) K →ₐ[K] B) (hφ : Function.Injective φ)
    (r : Fin m → B)
    (hr : Function.Surjective (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B)) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ t : ℕ,
      t ^ s ≤ c * Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map
        (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) := by
  choose q hq using fun i => hr (φ (MvPolynomial.X i))
  set E : ℕ := (∑ i, (q i).totalDegree) + 1 with hE
  have hE0 : 0 < E := Nat.succ_pos _
  refine ⟨E ^ s, Nat.one_le_pow _ _ hE0, fun t => ?_⟩
  set V := (MvPolynomial.restrictTotalDegree (Fin m) K t).map
        (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap with hV
  let e : (Fin s → Fin (t / E + 1)) → (Fin s →₀ ℕ) := fun a =>
    Finsupp.equivFunOnFinite.symm fun i => (a i : ℕ)
  have he : Function.Injective e := by
    intro a a' h
    funext i
    have := congrArg (fun z : Fin s →₀ ℕ => z i) h
    exact Fin.ext (by simpa [e] using this)
  have hli : LinearIndependent K fun a => φ (MvPolynomial.monomial (e a) (1 : K)) := by
    have h1 := ((MvPolynomial.basisMonomials (Fin s) K).linearIndependent.comp e he).map'
      φ.toLinearMap (LinearMap.ker_eq_bot.2 hφ)
    simpa [Function.comp_def] using h1
  have hmem : ∀ a, φ (MvPolynomial.monomial (e a) (1 : K)) ∈ V := by
    intro a
    refine ⟨∏ i, q i ^ (a i : ℕ), ?_, ?_⟩
    · refine (MvPolynomial.mem_restrictTotalDegree _ _ _).2 ?_
      refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
      calc ∑ i, (q i ^ (a i : ℕ)).totalDegree ≤ ∑ i, (t / E) * (q i).totalDegree :=
            Finset.sum_le_sum fun i _ => (MvPolynomial.totalDegree_pow _ _).trans
              (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (a i).2))
        _ ≤ (t / E) * E := by
            rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left _ (Nat.le_succ _)
        _ ≤ t := Nat.div_mul_le_self _ _
    · rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
      simp [hq, e]
  have hli' : LinearIndependent K fun a => (⟨_, hmem a⟩ : V) :=
    LinearIndependent.of_comp V.subtype hli
  have hc := hli'.fintype_card_le_finrank
  simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ] at hc
  calc t ^ s ≤ (E * (t / E + 1)) ^ s := Nat.pow_le_pow_left (Nat.lt_mul_div_succ t hE0).le _
    _ ≤ _ := by rw [mul_pow]; exact Nat.mul_le_mul_left _ hc

end DegreeGrowth

theorem finrank_totalDegree_image_growth : ∀ (K B : Type) [Field K] [CommRing B] [IsDomain B] [Algebra K B] (m g : ℕ) (r : Fin m → B), Function.Surjective (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B) → Algebra.trdeg K B = g → ∃ c C : ℕ, 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t → t ^ g ≤ c * Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) ∧ Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin m) K t).map (MvPolynomial.aeval r : MvPolynomial (Fin m) K →ₐ[K] B).toLinearMap) ≤ C * t ^ g := by
  intro K B _ _ _ _ m g r hr hg
  haveI : Algebra.FiniteType K B := Algebra.FiniteType.of_surjective _ hr
  obtain ⟨s, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K B
  letI : Algebra (MvPolynomial (Fin s) K) B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin s) K) B :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : Module.Finite (MvPolynomial (Fin s) K) B := hfin
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hs : s = g := by
    have h := trdeg_add_eq K (MvPolynomial (Fin s) K) (A := B)
    rw [MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero, hg] at h
    simpa using h
  subst hs
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := MvPolynomial (Fin s) K) (M := B)
  have hall : ∀ x : B, ∃ D, x ∈ DegreeGrowth.boxSpan K (fun i => φ (MvPolynomial.X i)) b D := by
    intro x
    have hx : x ∈ Submodule.span (MvPolynomial (Fin s) K) (Set.range b) := hb ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact ⟨0, by simpa using DegreeGrowth.mem_boxSpan (K := K) (fun i => φ (MvPolynomial.X i)) b 0 (fun _ => 0) (fun _ => le_rfl) l⟩
    | zero => exact ⟨0, zero_mem _⟩
    | add x z _ _ h1 h2 =>
      obtain ⟨D1, h1⟩ := h1
      obtain ⟨D2, h2⟩ := h2
      exact ⟨max D1 D2, add_mem (DegreeGrowth.boxSpan_mono _ b (le_max_left _ _) h1)
        (DegreeGrowth.boxSpan_mono _ b (le_max_right _ _) h2)⟩
    | smul p x _ hx =>
      have h := DegreeGrowth.exists_aeval_mul_mem _ b p hx
      have e : MvPolynomial.aeval (fun i => φ (MvPolynomial.X i)) = φ :=
        (MvPolynomial.aeval_unique φ).symm
      rw [e] at h
      exact h
  obtain ⟨C, hC⟩ := DegreeGrowth.upper _ b hall r
  obtain ⟨c, hc1, hc⟩ := DegreeGrowth.lower φ hinj r hr
  exact ⟨c, C, hc1, fun t ht => ⟨hc t, hC t ht⟩⟩

end GlobalTheory
end
