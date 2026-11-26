module

public import ReciprocityTheory.DualLattices.ConstantCoeffRowSubst
public import ReciprocityTheory.DualLattices.CotangentSurjective

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.FischerSelfNeZero
section -- merged from ReciprocityTheory.DualLattices.WtGtRowSubstXSub
noncomputable section

open MvPolynomial Matrix Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

def vw (p : Fin ν × ι) : ℕ := 2 ^ (ν - 1 - (p.1 : ℕ))

def wt (A : Fin ν × ι →₀ ℕ) : ℕ := A.sum fun p e => e * vw p

def comp (d : ℕ) (P : MvPolynomial (Fin ν × ι) ℂ) : MvPolynomial (Fin ν × ι) ℂ :=
  ∑ A ∈ P.support.filter (fun A => wt A = d), monomial A (AddMonoidAlgebra.coeff P A)

end ReciprocityTheory.PGsh
end
end

noncomputable section

open MvPolynomial Matrix Finset

open scoped Classical

namespace ReciprocityTheory.PGsh

variable {ν : ℕ} {ι : Type*}

theorem fischer_self_ne_zero (P : MvPolynomial (Fin ν × ι) ℂ) (hP : P ≠ 0) : fischer P P ≠ 0 := by
  intro h0
  have hsum : fischer P P = ((∑ A ∈ P.support,
      ‖AddMonoidAlgebra.coeff P A‖ ^ 2 * ((A.prod fun _ e => e.factorial : ℕ) : ℝ) : ℝ) : ℂ) := by
    unfold fischer
    rw [Finset.union_self]
    push_cast
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [Finsupp.prod]
    push_cast
    ring
  have hne : P.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun h => hP (MvPolynomial.support_eq_empty.mp h))
  have hpos : 0 < ∑ A ∈ P.support, ‖AddMonoidAlgebra.coeff P A‖ ^ 2 * ((A.prod fun _ e => e.factorial : ℕ) : ℝ) := by
    refine Finset.sum_pos (fun A hA => ?_) hne
    have h1 : AddMonoidAlgebra.coeff P A ≠ 0 := MvPolynomial.mem_support_iff.mp hA
    have h2 : 0 < ((A.prod fun _ e => e.factorial : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos fun _ _ => Nat.factorial_pos _
    have h3 : 0 < ‖AddMonoidAlgebra.coeff P A‖ ^ 2 := by positivity
    positivity
  rw [hsum] at h0
  have h4 : (∑ A ∈ P.support, ‖AddMonoidAlgebra.coeff P A‖ ^ 2 * ((A.prod fun _ e => e.factorial : ℕ) : ℝ) : ℝ) = 0 := by
    exact_mod_cast h0
  linarith

theorem rowSubst_mul (g h : Matrix (Fin ν) (Fin ν) ℂ) (P : MvPolynomial (Fin ν × ι) ℂ) :
    rowSubst h (rowSubst g P) = rowSubst (h * g) P := by
  have key : (rowSubst (ι := ι) h).comp (rowSubst g) = rowSubst (h * g) := by
    apply MvPolynomial.algHom_ext
    intro p
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [AlgHom.comp_apply, rowSubst, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, MvPolynomial.C_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  exact congrArg (fun F => F P) key

theorem rowSubst_one (P : MvPolynomial (Fin ν × ι) ℂ) : rowSubst (1 : Matrix (Fin ν) (Fin ν) ℂ) P = P := by
  have h : (fun p : Fin ν × ι => ∑ l, C ((1 : Matrix (Fin ν) (Fin ν) ℂ) l p.1) * X (l, p.2)) = X := by
    funext p
    rw [Finset.sum_eq_single p.1]
    · simp
    · intro l _ hl
      simp [Matrix.one_apply_ne hl]
    · simp
  unfold rowSubst
  rw [h, MvPolynomial.aeval_X_left_apply]

end ReciprocityTheory.PGsh
end
end

section -- merged from ReciprocityTheory.DualLattices.IsLocalOfIntegers
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

lemma det_col_comb {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (i₀ : Fin n)
    (c₀ : R) (β : Fin n → R) :
    (A.updateCol i₀
      (fun k => c₀ * A k i₀ - ∑ i ∈ Finset.univ.erase i₀, β i * A k i)).det = c₀ * A.det := by
  have e : (fun k => c₀ * A k i₀ - ∑ i ∈ Finset.univ.erase i₀, β i * A k i) =
      fun k => ∑ i, (if i = i₀ then c₀ else -β i) • A k i := by
    funext k
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), if_pos rfl, smul_eq_mul, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_neg (Finset.ne_of_mem_erase hi), smul_eq_mul, neg_mul]
  rw [e, Matrix.det_updateCol_sum, if_pos rfl, smul_eq_mul]

theorem det_mem_span_prod {R : Type*} [CommRing R] [IsLocalRing R] :
    ∀ (m : ℕ) (c : Fin m → R) (n : ℕ) (q : Fin n → ((j : Fin m) → R ⧸ Ideal.span {c j})),
      Submodule.span R (Set.range q) = ⊤ →
      ∀ T : Matrix (Fin n) (Fin n) R, (∀ k, ∑ i, T k i • q i = 0) →
      T.det ∈ Ideal.span {∏ j, c j} := by
  intro m
  induction m with
  | zero => intro c n q _ T _; simp
  | succ m ih =>
    intro c n q hq T hT
    let tl : ((j : Fin (m + 1)) → R ⧸ Ideal.span {c j}) →ₗ[R]
        ((j : Fin m) → R ⧸ Ideal.span {c j.succ}) :=
      LinearMap.pi fun j => LinearMap.proj j.succ
    have htl_surj : Function.Surjective tl := fun y =>
      ⟨Fin.cons (0 : R ⧸ Ideal.span {c 0}) y, funext fun j => rfl⟩
    have hprod : ∏ j, c j = c 0 * ∏ j : Fin m, c j.succ := Fin.prod_univ_succ c

    have hfst : ∀ (r : Fin n → R) (a : Fin n → R),
        (∀ i, Ideal.Quotient.mk (Ideal.span {c 0}) (a i) = q i 0) →
        (∑ i, r i • q i) 0 = Ideal.Quotient.mk (Ideal.span {c 0}) (∑ i, r i * a i) := by
      intro r a ha
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, ← ha i, map_mul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    by_cases hc0 : IsUnit (c 0)
    · have hgen : Submodule.span R (Set.range (tl ∘ q)) = ⊤ := by
        rw [Set.range_comp, ← Submodule.map_span, hq, Submodule.map_top,
          LinearMap.range_eq_top.2 htl_surj]
      have h := ih (fun j => c j.succ) n (tl ∘ q) hgen T (fun k => by
        have := congrArg tl (hT k)
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_zero] at this
        simpa only [map_smul, Function.comp_apply] using this)
      rw [hprod, Ideal.span_singleton_mul_left_unit hc0]
      exact h
    · choose a ha using fun i => Ideal.Quotient.mk_surjective (q i 0)
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun R).1
        (hq ▸ Submodule.mem_top : (Pi.single (0 : Fin (m + 1)) (1 : R ⧸ Ideal.span {c 0}) :
          (j : Fin (m + 1)) → R ⧸ Ideal.span {c j}) ∈ Submodule.span R (Set.range q))
      have hc0m : c 0 ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hc0
      have hspan_le : Ideal.span {c 0} ≤ IsLocalRing.maximalIdeal R :=
        (Ideal.span_singleton_le_iff_mem _).2 hc0m
      have h1 : ∑ i, g i * a i - 1 ∈ Ideal.span {c 0} := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hfst g a ha, hg]
        simp
      have hu : IsUnit (∑ i, g i * a i) := by
        by_contra hx
        have hx' : ∑ i, g i * a i ∈ IsLocalRing.maximalIdeal R :=
          (IsLocalRing.mem_maximalIdeal _).2 hx
        have := Ideal.sub_mem _ hx' (hspan_le h1)
        rw [sub_sub_cancel] at this
        exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)
      obtain ⟨i₀, hi₀⟩ : ∃ i₀, IsUnit (a i₀) := by
        by_contra hne
        push Not at hne
        apply (IsLocalRing.mem_maximalIdeal _).1 _ hu
        exact Ideal.sum_mem _ fun i _ =>
          Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hne i))
      set ai : R := ↑hi₀.unit⁻¹ with hai
      have haai : a i₀ * ai = 1 := by rw [hai]; exact hi₀.mul_val_inv
      let β : Fin n → R := fun i => a i * ai
      have hβ0 : β i₀ = 1 := haai
      let q'' : Fin n → ((j : Fin (m + 1)) → R ⧸ Ideal.span {c j}) := fun i =>
        if i = i₀ then c 0 • q i₀ else q i - β i • q i₀

      have hcomb : ∀ (r : Fin n → R) (w : R), c 0 * w = ∑ i, r i * β i →
          ∑ i, (if i = i₀ then w else r i) • q'' i = ∑ i, r i • q i := by
        intro r w hw
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
        have hrest : ∑ i ∈ Finset.univ.erase i₀, (if i = i₀ then w else r i) • q'' i =
            ∑ i ∈ Finset.univ.erase i₀, r i • q i -
              (∑ i ∈ Finset.univ.erase i₀, r i * β i) • q i₀ := by
          rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hne : i ≠ i₀ := Finset.ne_of_mem_erase hi
          simp only [q'', if_neg hne, smul_sub, smul_smul]
        have hw' : c 0 * w = r i₀ + ∑ i ∈ Finset.univ.erase i₀, r i * β i := by
          rw [hw, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), hβ0, mul_one]
        rw [hrest]
        simp only [q'', if_pos rfl, smul_smul, ↓reduceIte]
        rw [mul_comm w, hw', add_smul]
        abel

      have hk0 : ∀ k, ∑ i, T k i * a i ∈ Ideal.span {c 0} := fun k => by
        rw [← Ideal.Quotient.eq_zero_iff_mem, ← hfst (T k) a ha, hT k]; rfl
      choose t' ht' using fun k => Ideal.mem_span_singleton'.1 (hk0 k)
      let t : Fin n → R := fun k => t' k * ai
      have ht : ∀ k, c 0 * t k = ∑ i, T k i * β i := fun k => by
        simp only [t, β, ← mul_assoc, ← Finset.sum_mul, ← ht' k]
        ring
      let T'' : Matrix (Fin n) (Fin n) R := Matrix.of fun k i => if i = i₀ then t k else T k i
      have hrel : ∀ k, ∑ i, T'' k i • (tl ∘ q'') i = 0 := fun k => by
        have := hcomb (T k) (t k) (ht k)
        rw [hT k] at this
        have h2 := congrArg tl this
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_zero] at h2
        simpa only [T'', Matrix.of_apply, map_smul, Function.comp_apply] using h2
      have hgen : Submodule.span R (Set.range (tl ∘ q'')) = ⊤ := by
        rw [eq_top_iff]
        intro y _
        obtain ⟨x, rfl⟩ := htl_surj y
        let x0 : (j : Fin (m + 1)) → R ⧸ Ideal.span {c j} := Fin.cons 0 (tl x)
        obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1
          (hq ▸ Submodule.mem_top : x0 ∈ Submodule.span R (Set.range q))
        have hr0 : ∑ i, r i * a i ∈ Ideal.span {c 0} := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, ← hfst r a ha, hr]; rfl
        obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton'.1 hr0
        have hw : c 0 * (w' * ai) = ∑ i, r i * β i := by
          simp only [β, ← mul_assoc, ← Finset.sum_mul, ← hw']
          ring
        have hx := hcomb r (w' * ai) hw
        rw [hr] at hx
        have htx : tl x = tl x0 := funext fun j => rfl
        set_option synthInstance.maxHeartbeats 100000 in
          rw [htx, ← hx, map_sum]
        exact Submodule.sum_mem _ fun i _ => by
          rw [map_smul]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have hdet'' := ih (fun j => c j.succ) n (tl ∘ q'') hgen T'' hrel
      have hTeq : T = T''.updateCol i₀
          (fun k => c 0 * T'' k i₀ - ∑ i ∈ Finset.univ.erase i₀, β i * T'' k i) := by
        ext k i
        by_cases hi : i = i₀
        · subst hi
          rw [updateCol_self]
          simp only [T'', Matrix.of_apply, ↓reduceIte]
          rw [ht k, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hβ0, mul_one]
          have : ∑ x ∈ Finset.univ.erase i, β x * (if x = i then t k else T k x) =
              ∑ x ∈ Finset.univ.erase i, T k x * β x :=
            Finset.sum_congr rfl fun x hx => by
              rw [if_neg (Finset.ne_of_mem_erase hx), mul_comm]
          rw [this]; ring
        · rw [updateCol_ne hi]
          simp only [T'', Matrix.of_apply, if_neg hi]
      rw [hTeq, det_col_comb]
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hdet''
      rw [hprod, ← hz]
      exact Ideal.mem_span_singleton'.2 ⟨z, by ring⟩

lemma isLocal_of_integers {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) : IsLocalRing R := by
  have hne : Nontrivial R := ⟨⟨0, 1, fun h => by
    have := congrArg (fun x => v (algebraMap R C x)) h
    simp at this⟩⟩
  refine @IsLocalRing.of_nonunits_add R _ hne ?_
  intro a b ha hb
  rw [mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one] at ha hb ⊢
  have ha' : v (algebraMap R C a) < 1 := lt_of_le_of_ne (hv.map_le_one a) ha
  have hb' : v (algebraMap R C b) < 1 := lt_of_le_of_ne (hv.map_le_one b) hb
  rw [map_add (f := _)]
  exact ne_of_lt (lt_of_le_of_lt (v.map_add _ _) (max_lt ha' hb'))

theorem prod_le_of_gen {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {x : NNReal}
    (hx : HasLen v R M x) {n : ℕ} (y : Fin n → M)
    (hy : Submodule.span R (Set.range y) = ⊤) (δ : Fin n → R)
    (hrel : ∀ i, ∃ a : Fin n → R, δ i • y i = ∑ j, (if j < i then a j else 0) • y j) :
    ∏ i, v (algebraMap R C (δ i)) ≤ x := by
  haveI := isLocal_of_integers hv
  obtain ⟨m, c, ⟨e⟩, hxc⟩ := hx
  choose a ha using hrel
  obtain ⟨q, hqdef⟩ : ∃ q : Fin n → ((j : Fin m) → R ⧸ Ideal.span {c j}), q = fun i => e (y i) :=
    ⟨_, rfl⟩
  have hq : Submodule.span R (Set.range q) = ⊤ := by
    have h1 : Set.range q = (e : M →ₗ[R] _) '' Set.range y := by
      ext z
      simp [hqdef]
    rw [h1, Submodule.span_image, hy, Submodule.map_top, LinearEquiv.range]
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin n) (Fin n) R,
      T = fun i j => (if j = i then δ i else 0) - (if j < i then a i j else 0) := ⟨_, rfl⟩
  have hrelT : ∀ k, ∑ i, T k i • q i = 0 := by
    intro k
    have h := congrArg e (ha k)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, ite_smul, zero_smul] at h
    simp only [hT, hqdef, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hdet := det_mem_span_prod m c n q hq T hrelT
  have hdetT : T.det = ∏ i, δ i := by
    rw [Matrix.det_of_lowerTriangular]
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [hT]
    · intro i j hij
      have h' : i < j := OrderDual.toDual_lt_toDual.mp hij
      simp [hT, h'.ne', not_lt.mpr h'.le]
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hdet
  calc ∏ i, v (algebraMap R C (δ i)) = v (algebraMap R C (∏ i, δ i)) := by simp [map_prod]
    _ = v (algebraMap R C r) * ∏ j, v (algebraMap R C (c j)) := by
        rw [← hdetT, ← hr]
        simp [map_prod]
    _ ≤ 1 * ∏ j, v (algebraMap R C (c j)) := by
        gcongr
        exact hv.map_le_one r
    _ = x := by rw [one_mul, hxc]

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.ModuliPointsState
namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

structure DualPair (R : LAlg R₀) where
  D : LAlg R₀
  π : LHom D R
  σ : LHom R D
  η : (D : Type u)
  sect : ∀ r, π.1 (σ.1 r) = r
  η_sq : η * η = 0
  ker_eq : RingHom.ker π.1 = Ideal.span {η}
  free : ∀ r, σ.1 r * η = 0 → r = 0

namespace DualPair

variable {R : LAlg R₀} (Dp : DualPair R)

lemma η_mem : Dp.η ∈ Dp.π.ker := by
  show Dp.η ∈ RingHom.ker Dp.π.1
  rw [Dp.ker_eq]
  exact Ideal.subset_span (Set.mem_singleton _)

lemma sqZero : Dp.π.SqZero := by
  refine ⟨fun r => ⟨Dp.σ.1 r, Dp.sect r⟩, ?_⟩
  rw [Dp.ker_eq, Ideal.span_singleton_pow, pow_two, Dp.η_sq, Ideal.span_singleton_eq_bot]

def ηk : Dp.π.ker := ⟨Dp.η, Dp.η_mem⟩

end DualPair

namespace BX

variable (B : BX R₀)

def IsHeight {R : LAlg R₀} (Dp : DualPair R) (N : ℕ) (y : B.G R) (h : B.gg →ₗ[R₀] R) : Prop :=
  ∀ v : B.gg, ∃ z : (Dp.D : Type u)ˣ,
    B.IsPairing N (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) (B.map Dp.σ y) z ∧ (z : Dp.D) = 1 + Dp.σ.1 (h v) * Dp.η

end BX

def HighestWeightVectorUniformBounds (B : BX R₀) : Prop :=
  ∀ (R : LAlg R₀) (Dp : DualPair R) (N : ℕ), (N : (R : Type u)) = 0 →
    (∀ (y : B.G R) (v : B.gg) (u : B.P Dp.D (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) (B.map Dp.σ y)),
      HEq (B.pmap Dp.π u) (B.zero1 y) →
      HEq (B.nsmul1 u N) (B.zero1 (B.map Dp.σ y))) ∧
    (∀ y : B.G R, N • y = 0 → ∃! h : B.gg →ₗ[R₀] R, B.IsHeight Dp N y h) ∧
    (∀ (y y' : B.G R) (h h' : B.gg →ₗ[R₀] R), B.IsHeight Dp N y h → B.IsHeight Dp N y' h' →
      B.IsHeight Dp N (y + y') (h + h'))

end ReciprocityTheory.PGsh
end

section -- merged from ReciprocityTheory.DualLattices.MemAugIdeal
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.PullbackHopfOrder

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem mem_augIdeal {X : Type} [AddCommGroup X] {M : Submodule R (X → C)} {f : X → C} :
    f ∈ augIdeal M ↔ f ∈ M ∧ f 0 = 0 := by
  exact Iff.rfl

theorem sqIdeal_le {X Y : Type} (F : (X → C) →ₗ[R] (Y → C))
    (hF : ∀ f g, F (f * g) = F f * F g) {I : Submodule R (X → C)} {J : Submodule R (Y → C)}
    (hIJ : ∀ f ∈ I, F f ∈ J) : sqIdeal I ≤ (sqIdeal J).comap F := by
  refine Submodule.span_le.2 ?_
  rintro h ⟨f, hf, f', hf', rfl⟩
  show F (f * f') ∈ sqIdeal J
  rw [hF]
  exact Submodule.subset_span ⟨_, hIJ f hf, _, hIJ f' hf', rfl⟩

theorem smulTop_le (q : ℕ) {a b : ℕ} (G : Matrix (Fin a) (Fin b) R) :
    (Ideal.span {(q : R)} • (⊤ : Submodule R (Fin b → R))) ≤
      (Ideal.span {(q : R)} • (⊤ : Submodule R (Fin a → R))).comap G.mulVecLin := by
  refine Submodule.smul_le.2 fun r hr n _ => ?_
  rw [Submodule.mem_comap, map_smul]
  exact Submodule.smul_mem_smul hr Submodule.mem_top

def mq (q : ℕ) {a b : ℕ} (G : Matrix (Fin a) (Fin b) R) :
    LieDualModP q R b →ₗ[R] LieDualModP q R a :=
  Submodule.mapQ _ _ G.mulVecLin (smulTop_le q G)

theorem mq_mk (q : ℕ) {a b : ℕ} (G : Matrix (Fin a) (Fin b) R) (x : Fin b → R) :
    mq q G (Submodule.Quotient.mk x) = Submodule.Quotient.mk (G *ᵥ x) := rfl

def qPi (q d : ℕ) : LieDualModP q R d ≃ₗ[R] ((i : Fin d) → R ⧸ Ideal.span {(q : R)}) := by
  let πd : (Fin d → R) →ₗ[R] ((i : Fin d) → R ⧸ Ideal.span {(q : R)}) :=
    LinearMap.pi fun i => (Ideal.span {(q : R)}).mkQ ∘ₗ LinearMap.proj i
  have hπ : ∀ x i, πd x i = Submodule.Quotient.mk (x i) := fun _ _ => rfl
  have hsurj : Function.Surjective πd := by
    intro y
    choose x hx using fun i => Submodule.Quotient.mk_surjective _ (y i)
    exact ⟨x, funext fun i => by rw [hπ, hx]⟩
  have hker : Ideal.span {(q : R)} • (⊤ : Submodule R (Fin d → R)) = LinearMap.ker πd := by
    ext x
    rw [LinearMap.mem_ker]
    constructor
    · intro hx
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr n _
        funext i
        rw [hπ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, Pi.smul_apply, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
      · intro x y hx hy
        rw [map_add (f := _), hx, hy, add_zero]
    · intro hx
      have : ∀ i, ∃ s, s * (q : R) = x i := fun i => by
        have := congrFun hx i
        rw [hπ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero] at this
        exact Ideal.mem_span_singleton'.1 this
      choose s hs using this
      have hx' : x = (q : R) • s := funext fun i => by
        rw [Pi.smul_apply, smul_eq_mul, mul_comm, hs]
      rw [hx']
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  exact (Submodule.quotEquivOfEq _ _ hker).trans (πd.quotKerEquivOfSurjective hsurj)

variable {X N : Type} [AddCommGroup X] [AddCommGroup N]

theorem omega_pull (q : ℕ) {g d : ℕ} (ψ : X →+ N) (χ : N →+ X) (hχψ : ∀ x, χ (ψ x) = x)
    (A : Submodule R (N → C)) (hA : ∀ f ∈ A, (fun n => f (ψ (χ n))) ∈ A)
    (φ : augIdeal A →ₗ[R] LieDualModP q R g) (hsurj : Function.Surjective φ)
    (hker : LinearMap.ker φ = (sqIdeal (augIdeal A)).comap (augIdeal A).subtype)
    (F : Matrix (Fin g) (Fin g) R) (P1 : Matrix (Fin g) (Fin d) R) (P2 : Matrix (Fin d) (Fin g) R)
    (hF : P1 * P2 = F) (h21 : P2 * P1 = 1)
    (hlin : ∀ (f f' : augIdeal A) (l : Fin g → R),
      (∀ n, (f' : N → C) n = (f : N → C) (ψ (χ n))) →
      φ f = Submodule.Quotient.mk l → φ f' = Submodule.Quotient.mk (F *ᵥ l)) :
    Nonempty (OmAA (A.map (LinearMap.funLeft R C ψ)) ≃ₗ[R] LieDualModP q R d) := by
  classical
  have hM : P2 * F * P1 = 1 := by
    rw [← hF, ← Matrix.mul_assoc P2 P1 P2, h21, Matrix.one_mul, h21]
  have hψI : ∀ f ∈ augIdeal A,
      LinearMap.funLeft R C ψ f ∈ augIdeal (A.map (LinearMap.funLeft R C ψ)) := by
    intro f hf
    rw [mem_augIdeal] at hf ⊢
    refine ⟨Submodule.mem_map_of_mem hf.1, ?_⟩
    rw [LinearMap.funLeft_apply, map_zero]
    exact hf.2
  have hχI : ∀ g ∈ augIdeal (A.map (LinearMap.funLeft R C ψ)),
      LinearMap.funLeft R C χ g ∈ augIdeal A := by
    intro g hg
    rw [mem_augIdeal] at hg ⊢
    obtain ⟨⟨f, hf, rfl⟩, h0⟩ := hg
    refine ⟨hA f hf, ?_⟩
    rw [LinearMap.funLeft_apply, map_zero]
    exact h0
  let Φ0 : augIdeal (A.map (LinearMap.funLeft R C ψ)) →ₗ[R] augIdeal A :=
    ((LinearMap.funLeft R C χ).comp (augIdeal (A.map (LinearMap.funLeft R C ψ))).subtype).codRestrict
      (augIdeal A) (fun g => hχI g.1 g.2)
  let Φ : augIdeal (A.map (LinearMap.funLeft R C ψ)) →ₗ[R] LieDualModP q R d :=
    mq q P2 ∘ₗ φ ∘ₗ Φ0
  have hΦ : ∀ g, Φ g = mq q P2 (φ (Φ0 g)) := fun _ => rfl
  have hsurjΦ : Function.Surjective Φ := by
    intro y
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨f, hf⟩ := hsurj (Submodule.Quotient.mk (P1 *ᵥ w))
    refine ⟨⟨LinearMap.funLeft R C ψ f, hψI f f.2⟩, ?_⟩
    have h1 := hlin f (Φ0 ⟨LinearMap.funLeft R C ψ f, hψI f f.2⟩) (P1 *ᵥ w) (fun n => rfl) hf
    rw [hΦ, h1, mq_mk, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
  have hkerΦ : LinearMap.ker Φ = (sqIdeal (augIdeal (A.map (LinearMap.funLeft R C ψ)))).comap
      (augIdeal (A.map (LinearMap.funLeft R C ψ))).subtype := by
    ext u
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, hΦ]
    constructor
    · intro h0
      obtain ⟨l, hl⟩ := Submodule.Quotient.mk_surjective _ (φ (Φ0 u))
      have hfix := hlin (Φ0 u) (Φ0 u) l (fun n => by
        show (u : X → C) (χ n) = (u : X → C) (χ (ψ (χ n)))
        rw [hχψ]) hl.symm
      rw [← hl, mq_mk] at h0
      have hφ0 : φ (Φ0 u) = 0 := by
        rw [hfix, ← hF, ← Matrix.mulVec_mulVec,
          show (Submodule.Quotient.mk (P1 *ᵥ (P2 *ᵥ l)) : LieDualModP q R g) =
            mq q P1 (Submodule.Quotient.mk (P2 *ᵥ l)) from rfl, h0, map_zero]
      have hmem : ((Φ0 u : augIdeal A) : N → C) ∈ sqIdeal (augIdeal A) := by
        have := LinearMap.mem_ker.2 hφ0
        rw [hker, Submodule.mem_comap] at this
        exact this
      have := Submodule.mem_comap.1
        (sqIdeal_le (LinearMap.funLeft R C ψ) (fun _ _ => rfl) hψI hmem)
      convert this using 1
      funext x
      show (u : X → C) x = (u : X → C) (χ (ψ x))
      rw [hχψ]
    · intro hu
      have h1 := Submodule.mem_comap.1
        (sqIdeal_le (LinearMap.funLeft R C χ) (fun _ _ => rfl) hχI hu)
      have hφ0 : φ (Φ0 u) = 0 := by
        rw [← LinearMap.mem_ker, hker, Submodule.mem_comap]
        exact h1
      rw [hφ0, map_zero]
  exact ⟨(Submodule.quotEquivOfEq _ _ hkerΦ.symm).trans (Φ.quotKerEquivOfSurjective hsurjΦ)⟩

end ReciprocityTheory.PGsh.Up.PullbackHopfOrder
end
end

section -- merged from ReciprocityTheory.DualLattices.SumValCoord
section -- merged from ReciprocityTheory.DualLattices.MonomialDeterminantStatement
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def MonomialDeterminantStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal) (R : Type)
    [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Λ : Matrix ι ι R) (u : ι → (ι → ZMod p) → C),
    IsUnit Λ.det → (∀ j x, v (u j x) ≤ 1) →
    (∀ j x, v (u j x - algebraMap R C (∑ i, Λ j i * ((x i).val : R))) < 1) →
    v (Matrix.of fun (x α : ι → ZMod p) => ∏ j, u j x ^ (α j).val).det = 1 ∧
    ∀ ε : ι → C,
      v (Matrix.of fun (x α : ι → ZMod p) => ∏ j, (ε j * u j x) ^ (α j).val).det =
        ∏ j, v (ε j) ^ (p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2))

end ReciprocityTheory.PGsh.Up
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.PGsh.Up

theorem sum_val_zmod (p : ℕ) [Fact p.Prime] : ∑ a : ZMod p, a.val = p * (p - 1) / 2 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hinj : Set.InjOn (fun a : ZMod p => a.val) (univ : Finset (ZMod p)) :=
    fun a _ b _ h => ZMod.val_injective p h
  have himg : (univ : Finset (ZMod p)).image (fun a => a.val) = range p := by
    ext i
    simp only [mem_image, mem_univ, true_and, mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      exact ZMod.val_lt a
    · intro hi
      exact ⟨(i : ZMod p), ZMod.val_cast_of_lt hi⟩
  rw [← Finset.sum_range_id, ← himg]
  exact (Finset.sum_image (f := fun i : ℕ => i) hinj).symm

theorem sum_val_coord (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] (j : ι) :
    ∑ α : ι → ZMod p, (α j).val = p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2) := by
  have h := (Equiv.funSplitAt j (ZMod p)).sum_comp (fun q => q.1.val)
  simp only [Equiv.funSplitAt_apply] at h
  rw [h, Fintype.sum_prod_type]
  simp only [sum_const, card_univ, smul_eq_mul]
  rw [← Finset.mul_sum, sum_val_zmod]
  congr 1
  rw [Fintype.card_fun, ZMod.card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

theorem u5 : MonomialDeterminantStatement := by
  intro p _ C _ v R _ _ hR hp ι _ _ Λ u hΛ hu hc
  have hpne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨I, hmem⟩ : ∃ I : Ideal R, ∀ r, r ∈ I ↔ v (algebraMap R C r) < 1 :=
    ⟨{ carrier := {r | v (algebraMap R C r) < 1}
       add_mem' := by
         intro a b ha hb
         show v (algebraMap R C (a + b)) < 1
         rw [map_add (f := _)]
         exact lt_of_le_of_lt (v.map_add _ _) (max_lt ha hb)
       zero_mem' := by
         show v (algebraMap R C 0) < 1
         simp
       smul_mem' := by
         intro c a ha
         show v (algebraMap R C (c * a)) < 1
         rw [map_mul, map_mul]
         exact lt_of_le_of_lt (mul_le_of_le_one_left (by positivity) (hR.map_le_one c)) ha },
     fun r => Iff.rfl⟩
  have hmax : I.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨?_, ?_⟩
    · rw [hmem]
      simp
    · intro J x hIJ hxI hxJ
      have hv1 : v (algebraMap R C x) = 1 :=
        le_antisymm (hR.map_le_one x) (not_lt.mp fun h => hxI ((hmem x).mpr h))
      obtain ⟨y, hy⟩ := (hR.isUnit_of_one' hv1).exists_right_inv
      rw [← hy]
      exact J.mul_mem_right y hxJ
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  have hpk : ((p : ℕ) : R ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem, hmem, map_natCast]
    exact hp
  haveI : CharP (R ⧸ I) p := by
    have hdvd := (ringChar.spec (R ⧸ I) p).mp hpk
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd h1 CharP.ringChar_ne_one
    · exact ringChar.eq_iff.mp h1
  have hC : IsUnit (Λ.map (Ideal.Quotient.mk I)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hΛ.map _
  have hN := det_monF_ne_zero (p := p) (Λ.map (Ideal.Quotient.mk I)) hC
  choose w hw using fun j x => hR.exists_of_le_one (hu j x)
  have hent : ∀ j x, Ideal.Quotient.mk I (w j x) = lam (Λ.map (Ideal.Quotient.mk I)) j x := by
    intro j x
    rw [show Ideal.Quotient.mk I (w j x) = Ideal.Quotient.mk I (∑ i, Λ j i * ((x i).val : R)) from
      Ideal.Quotient.eq.mpr ((hmem _).mpr (by rw [map_sub, hw]; exact hc j x))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_natCast]
    simp only [lam, xc, Matrix.map_apply, ZMod.castHom_apply, ZMod.natCast_val]
  have hWN : Ideal.Quotient.mk I (Matrix.of fun (x α : ι → ZMod p) => ∏ j, w j x ^ (α j).val).det =
      (Matrix.of fun (x α : ι → ZMod p) => monF (Λ.map (Ideal.Quotient.mk I)) α x).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    ext x α
    simp only [Matrix.map_apply, Matrix.of_apply, map_prod, map_pow, monF, hent]
  have hWv : v (algebraMap R C (Matrix.of fun (x α : ι → ZMod p) => ∏ j, w j x ^ (α j).val).det) = 1 := by
    refine le_antisymm (hR.map_le_one _) (not_lt.mp fun h => hN ?_)
    rw [← hWN]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hmem _).mpr h)
  have hdetM : (Matrix.of fun (x α : ι → ZMod p) => ∏ j, u j x ^ (α j).val).det =
      algebraMap R C (Matrix.of fun (x α : ι → ZMod p) => ∏ j, w j x ^ (α j).val).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    ext x α
    simp only [Matrix.map_apply, Matrix.of_apply, map_prod, map_pow, hw]
  have h1 : v (Matrix.of fun (x α : ι → ZMod p) => ∏ j, u j x ^ (α j).val).det = 1 := by
    rw [hdetM]
    exact hWv
  refine ⟨h1, fun ε => ?_⟩
  have hscale : (Matrix.of fun (x α : ι → ZMod p) => ∏ j, (ε j * u j x) ^ (α j).val) =
      Matrix.of fun (x α : ι → ZMod p) =>
        (∏ j, ε j ^ (α j).val) * (Matrix.of fun (x α : ι → ZMod p) => ∏ j, u j x ^ (α j).val) x α := by
    ext x α
    simp only [Matrix.of_apply, mul_pow, Finset.prod_mul_distrib]
  rw [hscale, Matrix.det_mul_row, map_mul, h1, mul_one, Finset.prod_comm, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_pow_eq_pow_sum, map_pow, sum_val_coord p j]

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.PrimeHopfOrderStatement
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def PrimeHopfOrderStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → v (p : C) < 1 →
    ∀ AA : HopfOrder (C := C) R (ZMod p),
    ∃ (x ω : ZMod p → C) (δ : R),
      x ∈ AA.carrier ∧ x 0 = 0 ∧ (∀ a, ω a ^ p = ω a) ∧ (∀ a, v (ω a - (a.val : C)) < 1) ∧
      (∀ a, x a = ω a * x 1) ∧ x ^ p = (fun a => algebraMap R C δ * x a) ∧
      v (algebraMap R C δ) = v (x 1) ^ (p - 1) ∧
      AA.carrier = Submodule.span R (Set.range fun j : Fin p => x ^ (j : ℕ)) ∧
      augIdeal AA.carrier = Submodule.span R {y | ∃ j : ℕ, 1 ≤ j ∧ j < p ∧ y = x ^ j} ∧
      sqIdeal (augIdeal AA.carrier) = Submodule.span R
        ({fun a => algebraMap R C δ * x a} ∪ {y | ∃ j : ℕ, 2 ≤ j ∧ j < p ∧ y = x ^ j}) ∧
      HasColen R v AA.carrier (v (x 1) ^ (p * (p - 1) / 2))

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.ColengthSqBlockVandermonde
section -- merged from ReciprocityTheory.DualLattices.DiscriminantColengthStatement
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def discr {C : Type} [Field C] {n : ℕ} (a : Fin n → C) : C :=
  ∏ τ, ∏ τ' ∈ Finset.univ.erase τ, (a τ - a τ')

def freeMat {C : Type} [Field C] {n : ℕ} (a : Fin n → C) (h : ℕ) :
    Matrix (Fin n × Fin h) (Fin n × Fin h) C :=
  Matrix.of fun x y => if x.2 = y.2 then a x.1 ^ (y.1 : ℕ) else 0

def sumPts {C : Type} [Field C] {v : Valuation C NNReal} {n s : ℕ}
    (Mτ : Fin n → Lat v (Fin s)) : Set (Fin n × Fin s → C) :=
  {w | ∀ τ, (fun i => w (τ, i)) ∈ (Mτ τ).pts}

def projPts {C : Type} [Field C] {n s : ℕ} (M : Set (Fin n × Fin s → C)) (τ : Fin n) :
    Set (Fin s → C) :=
  (fun w i => w (τ, i)) '' M

def IsLaStable {C : Type} [Field C] {v : Valuation C NNReal} {n s : ℕ} (a : Fin n → C)
    (M : Lat v (Fin n × Fin s)) : Prop :=
  ∀ w ∈ M.pts, (fun y : Fin n × Fin s => a y.1 * w y) ∈ M.pts

end ReciprocityTheory.PGsh.Up
end
end

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {v : Valuation C NNReal}

def sumLat {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) : Lat v (Fin n × Fin s) :=
  ⟨Matrix.reindex (Equiv.prodComm (Fin s) (Fin n)) (Equiv.prodComm (Fin s) (Fin n))
      (Matrix.blockDiagonal fun τ => (Mτ τ).B), by
    rw [Matrix.det_reindex_self, Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => (Mτ τ).det_ne⟩

lemma sumLat_apply {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) (x y : Fin n × Fin s) :
    (sumLat Mτ).B x y = if x.1 = y.1 then (Mτ x.1).B x.2 y.2 else 0 := by
  simp only [sumLat, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, Matrix.blockDiagonal_apply]

lemma sumLat_mulVec {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) (c : Fin n × Fin s → C) (τ : Fin n)
    (i : Fin s) : ((sumLat Mτ).B *ᵥ c) (τ, i) = ((Mτ τ).B *ᵥ fun j => c (τ, j)) i := by
  simp only [Matrix.mulVec, dotProduct, sumLat_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_eq_single τ]
  · simp
  · intro b _ hb
    exact Finset.sum_eq_zero fun j _ => if_neg (Ne.symm hb)
  · intro h; exact absurd (Finset.mem_univ τ) h

lemma sumLat_pts {n s : ℕ} (Mτ : Fin n → Lat v (Fin s)) : (sumLat Mτ).pts = sumPts Mτ := by
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩ τ
    refine ⟨fun j => c (τ, j), fun j => hc (τ, j), ?_⟩
    funext i
    exact sumLat_mulVec Mτ c τ i
  · intro hw
    choose c hc hwc using hw
    refine ⟨fun y => c y.1 y.2, fun y => hc y.1 y.2, ?_⟩
    funext ⟨τ, i⟩
    rw [sumLat_mulVec]
    exact congrFun (hwc τ) i

lemma freeMat_eq {n : ℕ} (a : Fin n → C) (s : ℕ) :
    freeMat a s = Matrix.blockDiagonal fun _ : Fin s => Matrix.vandermonde a := by
  ext ⟨i, k⟩ ⟨j, k'⟩
  simp only [freeMat, Matrix.of_apply, Matrix.blockDiagonal_apply, Matrix.vandermonde_apply]

lemma det_freeMat {n : ℕ} (a : Fin n → C) (s : ℕ) :
    (freeMat a s).det = (Matrix.vandermonde a).det ^ s := by
  rw [freeMat_eq, Matrix.det_blockDiagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma v_det_vandermonde_sq {n : ℕ} (a : Fin n → C) :
    v (Matrix.vandermonde a).det ^ 2 = v (discr a) := by
  have hsplit : ∀ τ : Fin n, Finset.univ.erase τ = Finset.Ioi τ ∪ Finset.Iio τ := by
    intro τ
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Ioi,
      Finset.mem_Iio]
    constructor
    · intro h
      rcases lt_or_gt_of_ne h with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rintro (h | h)
      · exact h.ne'
      · exact h.ne
  have hdisj : ∀ τ : Fin n, Disjoint (Finset.Ioi τ) (Finset.Iio τ) := by
    intro τ
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact lt_asymm (Finset.mem_Ioi.1 h1) (Finset.mem_Iio.1 h2)
  rw [Matrix.det_vandermonde, discr]
  simp only [map_prod]
  have h1 : ∏ τ : Fin n, ∏ τ' ∈ Finset.univ.erase τ, v (a τ - a τ') =
      (∏ τ : Fin n, ∏ τ' ∈ Finset.Ioi τ, v (a τ - a τ')) *
        ∏ τ : Fin n, ∏ τ' ∈ Finset.Iio τ, v (a τ - a τ') := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => by rw [hsplit τ, Finset.prod_union (hdisj τ)]
  have h2 : ∏ τ : Fin n, ∏ τ' ∈ Finset.Iio τ, v (a τ - a τ') =
      ∏ τ' : Fin n, ∏ τ ∈ Finset.Ioi τ', v (a τ - a τ') :=
    Finset.prod_comm' (by intro x y; simp [Finset.mem_Iio, Finset.mem_Ioi])
  have h3 : ∏ τ : Fin n, ∏ τ' ∈ Finset.Ioi τ, v (a τ - a τ') =
      ∏ τ : Fin n, ∏ τ' ∈ Finset.Ioi τ, v (a τ' - a τ) :=
    Finset.prod_congr rfl fun _ _ => Finset.prod_congr rfl fun _ _ => Valuation.map_sub_swap v _ _
  rw [h1, h2, h3, sq]

lemma v_det_freeMat_sq {n : ℕ} (a : Fin n → C) (s : ℕ) :
    v (freeMat a s).det ^ 2 = v (discr a) ^ s := by
  rw [det_freeMat, map_pow, pow_right_comm, v_det_vandermonde_sq]

end ReciprocityTheory.PGsh.Up
end
end
