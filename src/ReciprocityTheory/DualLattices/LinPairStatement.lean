module

public import ReciprocityTheory.DualLattices.FischerSelfNeZero
public import ReciprocityTheory.DualLattices.UpSmith
public import ReciprocityTheory.DualLattices.ImportsBis

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.LinPairStatement
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

structure OEnd (B : BX R₀) (O : LAlg R₀) where
  f : ∀ {R : LAlg R₀}, LHom O R → B.G R →+ B.G R
  nat : ∀ {R S : LAlg R₀} (s : LHom O R) (g : LHom R S) (x : B.G R),
    f (g.comp s) (B.map g x) = B.map g (f s x)

structure OAdj (B : BX R₀) (O : LAlg R₀) where
  a : OEnd B O
  ab : OEnd B O
  e : ∀ {R : LAlg R₀} (s : LHom O R) (x z : B.G R), B.P R (a.f s x) z ≃ B.P R x (ab.f s z)
  e_smul : ∀ {R : LAlg R₀} (s : LHom O R) (x z : B.G R) (l : (R : Type u)ˣ) (u : B.P R (a.f s x) z),
    e s x z (B.smul l u) = B.smul l (e s x z u)
  equiv_addFst : ∀ {R : LAlg R₀} (s : LHom O R) (x x' z : B.G R) (u : B.P R (a.f s x) z)
    (u' : B.P R (a.f s x') z),
    e s (x + x') z (B.tr1 (map_add (a.f s) x x').symm (B.add1 u u')) =
      B.add1 (e s x z u) (e s x' z u')
  equiv_addSnd : ∀ {R : LAlg R₀} (s : LHom O R) (x z z' : B.G R) (u : B.P R (a.f s x) z)
    (w : B.P R (a.f s x) z'),
    e s x (z + z') (B.add2 u w) =
      B.tr2 (map_add (ab.f s) z z').symm (B.add2 (e s x z u) (e s x z' w))

namespace DualPair

variable {R : LAlg R₀} (Dp : DualPair R)

lemma ση_mem (r : (R : Type u)) : Dp.σ.1 r * Dp.η ∈ Dp.π.ker := by
  rw [LHom.ker, Submodule.restrictScalars_mem, Dp.ker_eq]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

def ηmap : (R : Type u) →ₗ[R₀] Dp.π.ker where
  toFun r := ⟨Dp.σ.1 r * Dp.η, Dp.ση_mem r⟩
  map_add' r r' := Subtype.ext (by simp [add_mul])
  map_smul' c r := Subtype.ext (by simp [Algebra.smul_def, mul_assoc])

end DualPair

def hext (B : BX R₀) {R : LAlg R₀} (h : B.gg →ₗ[R₀] (R : Type u)) : B.gg ⊗[R₀] (R : Type u) →ₗ[R₀] (R : Type u) :=
  LinearMap.mul' R₀ (R : Type u) ∘ₗ TensorProduct.map h LinearMap.id

def LinHtStatement (B : BX R₀) (O : LAlg R₀) : Prop :=
  ∀ (A : OAdj B O) (R : LAlg R₀) (s : LHom O R) (Dp : DualPair R) (N : ℕ) (y : B.G R)
    (h : B.gg →ₗ[R₀] (R : Type u)) (δ : B.gg →ₗ[R₀] B.gg ⊗[R₀] (R : Type u)),
    N • y = 0 → B.IsHeight Dp N y h →
    (∀ v, A.ab.f (Dp.σ.comp s) (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) =
      B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg Dp.ηmap (δ v))) →
    B.IsHeight Dp N (A.a.f s y) (hext B h ∘ₗ δ)

end ReciprocityTheory.PGsh
end
end

section -- merged from ReciprocityTheory.DualLattices.ProdDvdOfIso
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

private lemma pi_quotient_eq_sum_smul_single {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (I : ι → Ideal R) (y : (i : ι) → R ⧸ I i) (a : ι → R)
    (ha : ∀ i, Ideal.Quotient.mk (I i) (a i) = y i) : y = ∑ i, a i • Pi.single i 1 := by
  funext i'
  rw [Finset.sum_apply, Finset.sum_eq_single i']
  · rw [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one,
      Ideal.Quotient.algebraMap_eq, ha]
  · intro j _ hj
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ i') h

private lemma nonempty_pi_quotient_equiv_maximal_restrict {R : Type} [CommRing R] [IsLocalRing R] {ι : Type} [Fintype ι]
    [DecidableEq ι] (a : ι → R) :
    Nonempty (((i : ι) → R ⧸ Ideal.span {a i}) ≃ₗ[R]
      ((i : {i // a i ∈ IsLocalRing.maximalIdeal R}) → R ⧸ Ideal.span {a i})) := by
  classical
  have hsub : ∀ i, a i ∉ IsLocalRing.maximalIdeal R → ∀ x : R ⧸ Ideal.span {a i}, x = 0 := by
    intro i hi x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hu : IsUnit (a i) := by
      by_contra h
      exact hi ((IsLocalRing.mem_maximalIdeal _).mpr h)
    rw [Ideal.span_singleton_eq_top.mpr hu]
    exact Submodule.mem_top
  let g : ((i : ι) → R ⧸ Ideal.span {a i}) →ₗ[R]
      ((i : {i // a i ∈ IsLocalRing.maximalIdeal R}) → R ⧸ Ideal.span {a i}) :=
    { toFun := fun x i => x i
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl }
  refine ⟨LinearEquiv.ofBijective g ⟨fun x y hxy => ?_, fun z => ?_⟩⟩
  · funext i
    by_cases hi : a i ∈ IsLocalRing.maximalIdeal R
    · exact congrFun hxy ⟨i, hi⟩
    · rw [hsub i hi (x i), hsub i hi (y i)]
  · refine ⟨fun i => if hi : a i ∈ IsLocalRing.maximalIdeal R then z ⟨i, hi⟩ else 0, ?_⟩
    funext i
    exact dif_pos i.2

private lemma prod_mem_span_prod_of_linearEquiv_pi_quotient {R : Type} [CommRing R] [IsLocalRing R] {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (c : ι → R) (d : κ → R)
    (hc : ∀ i, c i ∈ IsLocalRing.maximalIdeal R) (hd : ∀ j, d j ∈ IsLocalRing.maximalIdeal R)
    (f : ((i : ι) → R ⧸ Ideal.span {c i}) ≃ₗ[R] ((j : κ) → R ⧸ Ideal.span {d j})) :
    ∏ i, c i ∈ Ideal.span {∏ j, d j} := by
  classical
  let A : Matrix κ ι R := fun j i =>
    Function.surjInv (f := Ideal.Quotient.mk (Ideal.span {d j})) Ideal.Quotient.mk_surjective
      (f (Pi.single i 1) j)
  let B : Matrix ι κ R := fun i j =>
    Function.surjInv (f := Ideal.Quotient.mk (Ideal.span {c i})) Ideal.Quotient.mk_surjective
      (f.symm (Pi.single j 1) i)
  have hA : ∀ j i, Ideal.Quotient.mk (Ideal.span {d j}) (A j i) = f (Pi.single i 1) j :=
    fun j i => Function.surjInv_eq _ _
  have hB : ∀ i j, Ideal.Quotient.mk (Ideal.span {c i}) (B i j) = f.symm (Pi.single j 1) i :=
    fun i j => Function.surjInv_eq _ _
  have hsing : ∀ i, c i • (Pi.single i 1 : (i : ι) → R ⧸ Ideal.span {c i}) = 0 := by
    intro i
    funext i'
    rw [Pi.smul_apply, Pi.zero_apply]
    by_cases h : i' = i
    · subst h
      rw [Pi.single_eq_same, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    · rw [Pi.single_eq_of_ne h, smul_zero]
  have relA : ∀ j i, c i * A j i ∈ Ideal.span {d j} := by
    intro j i
    have h1 : f (c i • Pi.single i 1) j = 0 := by simp [hsing]
    rw [map_smul, Pi.smul_apply, ← hA, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  have relBA : ∀ i' i, (∑ j, B i' j * A j i) - (if i' = i then 1 else 0) ∈
      Ideal.span {c i'} := by
    intro i' i
    have h1 : (∑ j, Ideal.Quotient.mk (Ideal.span {c i'}) (B i' j * A j i)) =
        (Pi.single i 1 : (i : ι) → R ⧸ Ideal.span {c i}) i' := by
      have h0 := congrArg (fun y => y i') (f.symm_apply_apply (Pi.single i 1))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h0, pi_quotient_eq_sum_smul_single _ (f (Pi.single i 1)) (fun j => A j i) (fun j => hA j i),
        map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, Pi.smul_apply, ← hB, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        ← map_mul, mul_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_sum, h1]
    by_cases h : i' = i
    · subst h
      rw [Pi.single_eq_same, if_pos rfl, map_one]
    · rw [Pi.single_eq_of_ne h, if_neg h, map_zero]
  have relAB : ∀ j j', (∑ i, A j i * B i j') - (if j = j' then 1 else 0) ∈
      Ideal.span {d j} := by
    intro j j'
    have h1 : (∑ i, Ideal.Quotient.mk (Ideal.span {d j}) (A j i * B i j')) =
        (Pi.single j' 1 : (j : κ) → R ⧸ Ideal.span {d j}) j := by
      have h0 := congrArg (fun y => y j) (f.apply_symm_apply (Pi.single j' 1))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h0, pi_quotient_eq_sum_smul_single _ (f.symm (Pi.single j' 1)) (fun i => B i j') (fun i => hB i j'),
        map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, Pi.smul_apply, ← hA, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        ← map_mul, mul_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_sum, h1]
    by_cases h : j = j'
    · subst h
      rw [Pi.single_eq_same, if_pos rfl, map_one]
    · rw [Pi.single_eq_of_ne h, if_neg h, map_zero]
  have hBA : (B * A).map (IsLocalRing.residue R) = 1 := by
    ext i' i
    rw [Matrix.map_apply, Matrix.mul_apply, Matrix.one_apply]
    have h3 : IsLocalRing.residue R ((∑ j, B i' j * A j i) - if i' = i then 1 else 0) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr
        ((Ideal.span_singleton_le_iff_mem _).mpr (hc i') (relBA i' i))
    rw [map_sub, sub_eq_zero] at h3
    rw [h3]
    split_ifs <;> simp
  have hAB : (A * B).map (IsLocalRing.residue R) = 1 := by
    ext j j'
    rw [Matrix.map_apply, Matrix.mul_apply, Matrix.one_apply]
    have h3 : IsLocalRing.residue R ((∑ i, A j i * B i j') - if j = j' then 1 else 0) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr
        ((Ideal.span_singleton_le_iff_mem _).mpr (hd j) (relAB j j'))
    rw [map_sub, sub_eq_zero] at h3
    rw [h3]
    split_ifs <;> simp
  have hcard : Fintype.card ι = Fintype.card κ := by
    apply le_antisymm
    · calc Fintype.card ι = (1 : Matrix ι ι (IsLocalRing.ResidueField R)).rank :=
            Matrix.rank_one.symm
        _ = ((B * A).map (IsLocalRing.residue R)).rank := by rw [hBA]
        _ = (B.map (IsLocalRing.residue R) * A.map (IsLocalRing.residue R)).rank := by
            rw [Matrix.map_mul]
        _ ≤ (A.map (IsLocalRing.residue R)).rank := Matrix.rank_mul_le_right _ _
        _ ≤ Fintype.card κ := Matrix.rank_le_card_height _
    · calc Fintype.card κ = (1 : Matrix κ κ (IsLocalRing.ResidueField R)).rank :=
            Matrix.rank_one.symm
        _ = ((A * B).map (IsLocalRing.residue R)).rank := by rw [hAB]
        _ = (A.map (IsLocalRing.residue R) * B.map (IsLocalRing.residue R)).rank := by
            rw [Matrix.map_mul]
        _ ≤ (B.map (IsLocalRing.residue R)).rank := Matrix.rank_mul_le_right _ _
        _ ≤ Fintype.card ι := Matrix.rank_le_card_height _
  let e : ι ≃ κ := Fintype.equivOfCardEq hcard
  choose X hX using fun j i => Ideal.mem_span_singleton'.mp (relA j i)
  let A' : Matrix κ κ R := fun j j' => A j (e.symm j')
  let B' : Matrix κ κ R := fun j' j => B (e.symm j') j
  let X' : Matrix κ κ R := fun j j' => X j (e.symm j')
  have hmat : A' * Matrix.diagonal (fun j => c (e.symm j)) = Matrix.diagonal d * X' := by
    ext j j'
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    show A j (e.symm j') * c (e.symm j') = d j * X j (e.symm j')
    rw [mul_comm (A _ _), ← hX, mul_comm]
  have hprod : ∏ j, c (e.symm j) = ∏ i, c i := Equiv.prod_comp e.symm c
  have hdet : A'.det * ∏ i, c i = (∏ j, d j) * X'.det := by
    have h := congrArg Matrix.det hmat
    rwa [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hprod] at h
  have hdetBA : IsUnit (B * A).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, hBA,
      Matrix.det_one]
    exact one_ne_zero
  have hBA' : B' * A' = (B * A).submatrix e.symm e.symm := by
    ext j1 j2
    simp only [Matrix.mul_apply, Matrix.submatrix_apply]
    rfl
  have hdetA' : IsUnit A'.det := by
    have h := congrArg Matrix.det hBA'
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul] at h
    rw [← h] at hdetBA
    exact isUnit_of_mul_isUnit_right hdetBA
  obtain ⟨u, hu⟩ := hdetA'
  rw [Ideal.mem_span_singleton']
  refine ⟨↑u⁻¹ * X'.det, ?_⟩
  calc ↑u⁻¹ * X'.det * ∏ j, d j = ↑u⁻¹ * (A'.det * ∏ i, c i) := by rw [hdet]; ring
    _ = ∏ i, c i := by rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]

lemma prod_dvd_of_iso {R : Type} [CommRing R] [IsLocalRing R] {m n : ℕ} (c : Fin m → R)
    (d : Fin n → R)
    (f : ((i : Fin m) → R ⧸ Ideal.span {c i}) ≃ₗ[R] ((j : Fin n) → R ⧸ Ideal.span {d j})) :
    ∏ i, c i ∈ Ideal.span {∏ j, d j} := by
  classical
  obtain ⟨gc⟩ := nonempty_pi_quotient_equiv_maximal_restrict c
  obtain ⟨gd⟩ := nonempty_pi_quotient_equiv_maximal_restrict d
  have core := prod_mem_span_prod_of_linearEquiv_pi_quotient (fun i : {i // c i ∈ IsLocalRing.maximalIdeal R} => c i)
    (fun j : {j // d j ∈ IsLocalRing.maximalIdeal R} => d j) (fun i => i.2) (fun j => j.2)
    ((gc.symm.trans f).trans gd)
  have hunit : ∀ {k : ℕ} (a : Fin k → R),
      IsUnit (∏ i : {i // ¬ a i ∈ IsLocalRing.maximalIdeal R}, a i) := by
    intro k a
    refine Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one fun i _ => ?_
    by_contra h
    exact i.2 ((IsLocalRing.mem_maximalIdeal _).mpr h)
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => c i ∈ IsLocalRing.maximalIdeal R) c,
    ← Fintype.prod_subtype_mul_prod_subtype (fun j => d j ∈ IsLocalRing.maximalIdeal R) d,
    Ideal.span_singleton_mul_right_unit (hunit d)]
  exact Ideal.mul_mem_right _ _ core

theorem hasLen_unique {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {x y : NNReal}
    (hx : HasLen v R M x) (hy : HasLen v R M y) : x = y := by
  obtain ⟨m, c, ⟨φ⟩, rfl⟩ := hx
  obtain ⟨n, d, ⟨ψ⟩, rfl⟩ := hy
  haveI : Nontrivial R := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' := congrArg (algebraMap R C) h
    rw [map_zero, map_one] at h'
    exact zero_ne_one h'
  have hlt : ∀ z : R, ¬ IsUnit z → v (algebraMap R C z) < 1 := fun z hz =>
    lt_of_le_of_ne (hv.map_le_one z) fun h1 => hz (hv.isUnit_iff_valuation_eq_one.mpr h1)
  haveI : IsLocalRing R := by
    refine IsLocalRing.of_nonunits_add fun a b ha hb hab => ?_
    have h1 := hv.isUnit_iff_valuation_eq_one.mp hab
    rw [map_add (f := _)] at h1
    have h2 := (v.map_add _ _).trans_lt (max_lt (hlt a ha) (hlt b hb))
    rw [h1] at h2
    exact lt_irrefl _ h2
  have h1 := prod_dvd_of_iso c d (φ.symm.trans ψ)
  have h2 := prod_dvd_of_iso d c (ψ.symm.trans φ)
  rw [Ideal.mem_span_singleton, hv.dvd_iff_le] at h1 h2
  simp only [map_prod] at h1 h2
  exact le_antisymm h1 h2

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.BlockOneMulMulBlockOne
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up.Smith

section general

variable {R : Type} [CommRing R]

def Vm {N : ℕ} (j0 : Fin (N + 1)) (s : Fin (N + 1) → R) : Matrix (Fin (N + 1)) (Fin (N + 1)) R :=
  Matrix.of fun k l =>
    if l = j0 then (if k = j0 then 1 else 0) else ((if k = l then 1 else 0) - (if k = j0 then s l else 0))

theorem det_Vm {N : ℕ} (j0 : Fin (N + 1)) (s : Fin (N + 1) → R) : (Vm j0 s).det = 1 := by
  rw [Matrix.det_succ_column (Vm j0 s) j0, Finset.sum_eq_single j0]
  · have hsub : (Vm j0 s).submatrix j0.succAbove j0.succAbove = 1 := by
      ext k l
      simp only [Matrix.submatrix_apply, Vm, Matrix.of_apply, Fin.succAbove_ne, ite_false,
        sub_zero, Matrix.one_apply, (Fin.succAbove_right_injective).eq_iff]
    rw [hsub, Matrix.det_one]
    simp [Vm, ← two_mul, pow_mul]
  · intro k _ hk
    simp [Vm, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mul_Vm {m N : ℕ} (X : Matrix (Fin m) (Fin (N + 1)) R) (j0 : Fin (N + 1))
    (s : Fin (N + 1) → R) (i : Fin m) (l : Fin (N + 1)) :
    (X * Vm j0 s) i l = if l = j0 then X i j0 else X i l - s l * X i j0 := by
  classical
  simp only [Matrix.mul_apply, Vm, Matrix.of_apply]
  by_cases hl : l = j0
  · simp [hl]
  · simp only [hl, ite_false, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring

theorem VmT_mul {N n : ℕ} (j0 : Fin (N + 1)) (u : Fin (N + 1) → R) (Y : Matrix (Fin (N + 1)) (Fin n) R)
    (k : Fin (N + 1)) (l : Fin n) :
    ((Vm j0 u)ᵀ * Y) k l = if k = j0 then Y j0 l else Y k l - u k * Y j0 l := by
  classical
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Vm, Matrix.of_apply]
  by_cases hk : k = j0
  · simp [hk]
  · simp only [hk, ite_false, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
    simp [Finset.sum_ite_eq']

def piv {N : ℕ} (i0 : Fin (N + 1)) : Equiv.Perm (Fin (N + 1)) :=
  (finSuccEquiv N).trans (finSuccEquiv' i0).symm

theorem piv_zero {N : ℕ} (i0 : Fin (N + 1)) : piv i0 0 = i0 := by
  simp [piv, finSuccEquiv_zero]

theorem piv_succ {N : ℕ} (i0 : Fin (N + 1)) (l : Fin N) : piv i0 l.succ = i0.succAbove l := by
  simp [piv, finSuccEquiv_succ]

def bd1 {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) : Matrix (Fin (N + 1)) (Fin (M + 1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun l => Fin.cases 0 (fun k => P l k) j) i

@[simp] theorem blockOne_zero_zero_alt {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) : bd1 P 0 0 = 1 := rfl
@[simp] theorem blockOne_zero_succ_alt {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) (k : Fin M) :
    bd1 P 0 k.succ = 0 := rfl
@[simp] theorem blockOne_succ_succ_alt {N M : ℕ} (P : Matrix (Fin N) (Fin M) R) (l : Fin N) (k : Fin M) :
    bd1 P l.succ k.succ = P l k := rfl

theorem det_blockOne_alt {N : ℕ} (P : Matrix (Fin N) (Fin N) R) : (bd1 P).det = P.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [blockOne_zero_zero_alt, blockOne_zero_succ_alt, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, mul_one,
    Fin.val_zero, pow_zero, one_mul]
  congr 1

theorem blockOne_mul_mul_blockOne {d n : ℕ} (P : Matrix (Fin d) (Fin d) R) (Cm : Matrix (Fin (d + 1)) (Fin (n + 1)) R)
    (Q : Matrix (Fin n) (Fin n) R) (h0 : ∀ k : Fin n, Cm 0 k.succ = 0)
    (h1 : ∀ l : Fin d, Cm l.succ 0 = 0) :
    (bd1 P * Cm * bd1 Q) 0 0 = Cm 0 0 ∧ (∀ k : Fin n, (bd1 P * Cm * bd1 Q) 0 k.succ = 0) ∧
      (∀ l : Fin d, (bd1 P * Cm * bd1 Q) l.succ 0 = 0) ∧
      ∀ (l : Fin d) (k : Fin n), (bd1 P * Cm * bd1 Q) l.succ k.succ =
        (P * (Matrix.of fun (l : Fin d) (k : Fin n) => Cm l.succ k.succ) * Q) l k := by
  have bd1_succ_zero {N M : ℕ} (X : Matrix (Fin N) (Fin M) R) (l : Fin N) :
      bd1 X l.succ 0 = 0 := rfl
  have hPC0 : ∀ j : Fin (n + 1), (bd1 P * Cm) 0 j = Cm 0 j := by
    intro j; simp [Matrix.mul_apply, Fin.sum_univ_succ]
  have hPCs : ∀ (l : Fin d) (j : Fin (n + 1)), (bd1 P * Cm) l.succ j = ∑ m, P l m * Cm m.succ j := by
    intro l j; simp [Matrix.mul_apply, Fin.sum_univ_succ, bd1_succ_zero]
  refine ⟨?_, fun k => ?_, fun l => ?_, fun l k => ?_⟩
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, hPC0, h0]
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, hPC0, h0]
  · rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [hPCs, h1, bd1_succ_zero]
  · rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp only [hPCs, blockOne_zero_succ_alt, mul_zero, zero_add, blockOne_succ_succ_alt, Matrix.mul_apply, Matrix.of_apply]

theorem isUnit_det_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    IsUnit (σ.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) R).det := by
  have h := Matrix.det_permutation (R := R) σ
  simp only [Equiv.Perm.permMatrix] at h
  rw [h]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]

end general

variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem smith_mat (hv : v.Integers R) : ∀ (d n : ℕ) (A : Matrix (Fin d) (Fin n) R),
    ∃ (P : Matrix (Fin d) (Fin d) R) (Q : Matrix (Fin n) (Fin n) R) (a : Fin d → R),
      IsUnit P.det ∧ IsUnit Q.det ∧ ∀ j k, (P * A * Q) j k = if (k : ℕ) = (j : ℕ) then a j else 0 := by
  intro d
  induction d with
  | zero =>
    intro n A
    exact ⟨1, 1, Fin.elim0, by simp, by simp, fun j => j.elim0⟩
  | succ d ih =>
    intro n A
    cases n with
    | zero =>
      exact ⟨1, 1, 0, by simp, by simp, fun j k => k.elim0⟩
    | succ n =>
      classical
      set g : Fin (n + 1) → Fin (d + 1) → R := fun j i => A i j with hg
      have hp := exists_pivot (v := v) (b := d) (ι := Fin (n + 1)) hv g
      obtain ⟨i0, a, u, s, hu, -, hs, hz, hnz⟩ := hp
      by_cases ha : a = 0
      · have hA : A = 0 := by
          ext i j
          have := congrFun (hz ha j) i
          simpa [hg] using this
        exact ⟨1, 1, 0, by simp, by simp, fun j k => by simp [hA]⟩
      · obtain ⟨j0, hj0, hs0⟩ := hnz ha
        have hAj0 : ∀ i, A i j0 = a * u i := fun i => by
          have := congrFun hj0 i
          simpa [hg] using this
        have hAi0 : ∀ l, A i0 l = a * s l := fun l => by
          have := hs l
          simpa [hg] using this
        set B := (Vm i0 u)ᵀ * A * Vm j0 s with hBdef
        have hB : ∀ k l, B k l = if k = i0 then (if l = j0 then a else 0) else
            (if l = j0 then 0 else A k l - s l * (a * u k)) := by
          intro k l
          rw [hBdef, Matrix.mul_assoc, VmT_mul, mul_Vm, mul_Vm]
          by_cases hk : k = i0 <;> by_cases hl : l = j0
          · subst hk; subst hl; simp [hAj0, hu]
          · subst hk; simp [hl, hAi0, hs0]; ring
          · subst hl; simp [hk, hAj0, hu]; ring
          · simp [hk, hl, hAj0, hAi0, hu]; ring
        set A'' : Matrix (Fin d) (Fin n) R := Matrix.of fun l k => B (i0.succAbove l) (j0.succAbove k)
        obtain ⟨P'', Q'', a'', hP'', hQ'', hD''⟩ := ih n A''
        set Cm := B.submatrix (piv i0) (piv j0) with hCm
        have hCeq : ((piv i0).toPEquiv.toMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) R) * B * ((piv j0).symm.toPEquiv.toMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) R) = Cm := by
          rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm]
          rfl
        have h0 : ∀ k : Fin n, Cm 0 k.succ = 0 := by
          intro k
          simp only [hCm, Matrix.submatrix_apply, piv_zero, piv_succ, hB, ite_true,
            Fin.succAbove_ne, ite_false]
        have h1 : ∀ l : Fin d, Cm l.succ 0 = 0 := by
          intro l
          simp only [hCm, Matrix.submatrix_apply, piv_zero, piv_succ, hB, Fin.succAbove_ne, ite_false,
            ite_true]
        have hsub : (Matrix.of fun (l : Fin d) (k : Fin n) => Cm l.succ k.succ) = A'' := by
          ext l k
          simp only [hCm, Matrix.of_apply, Matrix.submatrix_apply, piv_succ]
          rfl
        obtain ⟨e00, e0s, es0, ess⟩ := blockOne_mul_mul_blockOne P'' Cm Q'' h0 h1
        refine ⟨bd1 P'' * ((piv i0).toPEquiv.toMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) R) * (Vm i0 u)ᵀ,
          Vm j0 s * ((piv j0).symm.toPEquiv.toMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * bd1 Q'', Fin.cons a a'', ?_, ?_, ?_⟩
        · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne_alt, Matrix.det_transpose, det_Vm, mul_one]
          exact hP''.mul (isUnit_det_perm _)
        · rw [Matrix.det_mul, Matrix.det_mul, det_blockOne_alt, det_Vm, one_mul]
          exact (isUnit_det_perm _).mul hQ''
        · have hfull : bd1 P'' * ((piv i0).toPEquiv.toMatrix : Matrix (Fin (d + 1)) (Fin (d + 1)) R) * (Vm i0 u)ᵀ * A *
              (Vm j0 s * ((piv j0).symm.toPEquiv.toMatrix : Matrix (Fin (n + 1)) (Fin (n + 1)) R) * bd1 Q'') = bd1 P'' * Cm * bd1 Q'' := by
            rw [← hCeq, hBdef]
            simp only [Matrix.mul_assoc]
          intro j k
          rw [hfull]
          refine Fin.cases ?_ (fun l => ?_) j <;> refine Fin.cases ?_ (fun k' => ?_) k
          · rw [e00]
            simp [hCm, piv_zero, hB]
          · rw [e0s]
            simp
          · rw [es0]
            simp
          · rw [ess, hsub, hD'']
            simp [Fin.val_succ]

end ReciprocityTheory.PGsh.Up.Smith
end
end

section -- merged from ReciprocityTheory.DualLattices.PrimeHopfOrderOfAddEquiv
noncomputable section

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Transport

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X Y : Type} [AddCommGroup X] [Fintype X] [DecidableEq X]
  [AddCommGroup Y] [Fintype Y] [DecidableEq Y]

abbrev pbE (e : X ≃+ Y) : (Y → C) ≃ₗ[R] (X → C) := LinearEquiv.funCongrLeft R C e.toEquiv

lemma pbE_apply (e : X ≃+ Y) (f : Y → C) (x : X) : pbE (C := C) (R := R) e f x = f (e x) := rfl

lemma pbE_symm_apply (e : X ≃+ Y) (f : X → C) (y : Y) :
    (pbE (C := C) (R := R) e).symm f y = f (e.symm y) := by
  rfl

lemma det_sub (e : X ≃+ Y) (B : Matrix Y Y C) : (B.submatrix e e).det = B.det :=
  Matrix.det_submatrix_equiv_self e.toEquiv B

lemma map_cols (e : X ≃+ Y) (B : Matrix Y Y C) :
    (Submodule.span R (Set.range fun j y => B y j)).map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) =
      Submodule.span R (Set.range fun j x => (B.submatrix e e) x j) := by
  rw [Submodule.map_span, ← Set.range_comp]
  have h : (fun j x => (B.submatrix e e) x j) =
      ((pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) ∘ fun j y => B y j) ∘ e := by
    funext j x
    rfl
  rw [h, e.surjective.range_comp]

lemma hasColen_map (v : Valuation C NNReal) (e : X ≃+ Y) (M : Submodule R (Y → C)) (c : NNReal)
    (h : HasColen R v M c) : HasColen R v (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) c := by
  obtain ⟨B, hM, hc⟩ := h
  exact ⟨B.submatrix e e, by rw [hM, map_cols], by rw [det_sub, hc]⟩

lemma map_pbE_symm (e : X ≃+ Y) (M : Submodule R (Y → C)) :
    (M.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))).map (pbE (C := C) (R := R) e.symm : (X → C) →ₗ[R] (Y → C)) = M := by
  rw [← Submodule.map_comp]
  have h : ((pbE (C := C) (R := R) e.symm : (X → C) →ₗ[R] (Y → C)).comp
      (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) = LinearMap.id := by
    refine LinearMap.ext fun f => funext fun y => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, pbE_apply, LinearMap.id_apply,
      AddEquiv.apply_symm_apply]
  rw [h, Submodule.map_id]

def hopfPull (e : X ≃+ Y) (A : HopfOrder (C := C) R Y) : HopfOrder (C := C) R X where
  carrier := A.carrier.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))
  lat := by
    obtain ⟨B, hB, hA⟩ := A.lat
    exact ⟨B.submatrix e e, by rwa [det_sub], by rw [hA, map_cols]⟩
  le_int := by
    intro f hf
    rw [Submodule.mem_map_equiv] at hf
    have h := A.le_int hf
    intro x
    obtain ⟨r, hr⟩ := h (e x)
    exact ⟨r, by rw [hr, pbE_symm_apply, AddEquiv.symm_apply_apply]⟩
  one_mem := by
    rw [Submodule.mem_map_equiv]
    convert A.one_mem using 1
    funext y
    simp [pbE_symm_apply]
  mul_mem := fun f g hf hg => by
    rw [Submodule.mem_map_equiv] at hf hg ⊢
    convert A.mul_mem _ _ hf hg using 1
    funext y
    simp only [pbE_symm_apply, Pi.mul_apply]
  comul := by
    intro f hf
    rw [Submodule.mem_map_equiv] at hf
    set g := (pbE (C := C) (R := R) e).symm f with hg
    have hfg : f = pbE (C := C) (R := R) e g := by rw [hg, LinearEquiv.apply_symm_apply]
    let pb2 : (Y × Y → C) →ₗ[R] (X × X → C) :=
      LinearMap.funLeft R C (fun q : X × X => (e q.1, e q.2))
    have h1 : addPull R X f = pb2 (addPull R Y g) := by
      funext q
      rw [hfg]
      simp only [addPull, pb2, LinearMap.funLeft_apply, pbE_apply, map_add (f := _)]
    rw [h1]
    have h2 := A.comul g hf
    have h3 : (tensorSpan R A.carrier).map pb2 ≤ tensorSpan R (A.carrier.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C))) := by
      rw [tensorSpan, Submodule.map_span_le]
      rintro F ⟨g1, hg1, h1', hh1, rfl⟩
      exact Submodule.subset_span ⟨pbE (C := C) (R := R) e g1, Submodule.mem_map_of_mem hg1,
        pbE (C := C) (R := R) e h1', Submodule.mem_map_of_mem hh1, rfl⟩
    exact h3 (Submodule.mem_map_of_mem h2)
  antipode := fun f hf => by
    rw [Submodule.mem_map_equiv] at hf ⊢
    convert A.antipode _ hf using 1
    funext y
    simp only [pbE_symm_apply, map_neg]

private theorem pbE_symm_pow (e : X ≃+ Y) (f : X → C) (n : ℕ) :
    (pbE (C := C) (R := R) e).symm (f ^ n) = ((pbE (C := C) (R := R) e).symm f) ^ n := by
  funext y
  simp only [pbE_symm_apply, Pi.pow_apply]

lemma mem_augIdeal_pull (e : X ≃+ Y) (A : HopfOrder (C := C) R Y) (f : X → C) :
    f ∈ augIdeal (hopfPull e A).carrier ↔ (pbE (C := C) (R := R) e).symm f ∈ augIdeal A.carrier := by
  rw [show (hopfPull e A).carrier =
      A.carrier.map (pbE (C := C) (R := R) e : (Y → C) →ₗ[R] (X → C)) from rfl]
  simp only [ReciprocityTheory.PGsh.L2.augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply,
    Submodule.mem_map_equiv, pbE_symm_apply, map_zero]

end Transport

lemma pow_mem_aug {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {X : Type}
    [AddCommGroup X] [Fintype X] [DecidableEq X] (A : HopfOrder (C := C) R X) {x : X → C}
    (hx : x ∈ augIdeal A.carrier) : ∀ k : ℕ, x ^ (k + 1) ∈ augIdeal A.carrier := by
  intro k
  simp only [ReciprocityTheory.PGsh.L2.augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply] at hx ⊢
  refine ⟨?_, by rw [Pi.pow_apply, hx.2, zero_pow (Nat.succ_ne_zero k)]⟩
  induction k with
  | zero => rw [zero_add, pow_one]; exact hx.1
  | succ k ih => rw [pow_succ]; exact A.mul_mem _ _ ih hx.1

theorem primeHopfOrder_of_addEquiv (hU3 : PrimeHopfOrderStatement) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (hv : v.Integers R) (hp : v (p : C) < 1) {K : Type} [AddCommGroup K] [Fintype K]
    [DecidableEq K] (e : ZMod p ≃+ K) (AK : HopfOrder (C := C) R K) :
    ∃ (xK : K → C) (δ : R) (x1 : C), xK ∈ augIdeal AK.carrier ∧
      xK ^ p = (fun a => algebraMap R C δ * xK a) ∧ v (algebraMap R C δ) = v x1 ^ (p - 1) ∧
      (∀ f ∈ augIdeal AK.carrier, ∃ r : R,
        f - r • xK ∈ augIdeal AK.carrier * augIdeal AK.carrier) ∧
      HasColen R v AK.carrier (v x1 ^ (p * (p - 1) / 2)) := by
  obtain ⟨x, _, δ, hx, hx0, -, -, -, hxp, hδ, -, haug, -, hcol⟩ :=
    hU3 p C v R hv hp (hopfPull e AK)
  have hxa : x ∈ ReciprocityTheory.PGsh.L2.augIdeal (hopfPull e AK).carrier := by
    simp only [ReciprocityTheory.PGsh.L2.augIdeal, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply]
    exact ⟨hx, hx0⟩
  have hxK := (mem_augIdeal_pull e AK x).1 hxa
  refine ⟨(pbE (C := C) (R := R) e).symm x, δ, x 1, hxK, ?_, hδ, ?_, ?_⟩
  · funext k
    have h := congrFun hxp (e.symm k)
    simp only [Pi.pow_apply] at h ⊢
    rw [pbE_symm_apply]
    exact h
  · have key : ∀ F ∈ Submodule.span R {y | ∃ j : ℕ, 1 ≤ j ∧ j < p ∧ y = x ^ j},
        ∃ r : R, (pbE (C := C) (R := R) e).symm F - r • (pbE (C := C) (R := R) e).symm x ∈
          ReciprocityTheory.PGsh.L2.augIdeal AK.carrier * ReciprocityTheory.PGsh.L2.augIdeal AK.carrier := by
      intro F hF
      induction hF using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, hj1, -, rfl⟩ := hy
        rcases Nat.lt_or_ge j 2 with hj | hj
        · obtain rfl : j = 1 := by omega
          refine ⟨1, ?_⟩
          rw [pow_one, one_smul, sub_self]
          exact zero_mem _
        · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
          refine ⟨0, ?_⟩
          rw [zero_smul, sub_zero, pbE_symm_pow, show m + 2 = (m + 1) + 1 from rfl, pow_succ]
          exact Submodule.mul_mem_mul (pow_mem_aug AK hxK m) hxK
      | zero =>
        refine ⟨0, ?_⟩
        rw [map_zero, zero_smul, sub_zero]
        exact zero_mem _
      | add a b _ _ ha hb =>
        obtain ⟨r1, h1⟩ := ha
        obtain ⟨r2, h2⟩ := hb
        refine ⟨r1 + r2, ?_⟩
        convert add_mem h1 h2 using 1
        rw [map_add (f := _), add_smul]
        abel
      | smul c a _ ha =>
        obtain ⟨r1, h1⟩ := ha
        refine ⟨c * r1, ?_⟩
        convert Submodule.smul_mem _ c h1 using 1
        rw [map_smul, smul_sub, mul_smul]
    intro f hf
    have hF : pbE (C := C) (R := R) e f ∈
        ReciprocityTheory.PGsh.L2.augIdeal (hopfPull e AK).carrier := by
      rw [mem_augIdeal_pull, LinearEquiv.symm_apply_apply]
      exact hf
    rw [haug] at hF
    obtain ⟨r, hr⟩ := key _ hF
    rw [LinearEquiv.symm_apply_apply] at hr
    exact ⟨r, hr⟩
  · have hc := hasColen_map v e.symm _ _ hcol
    rwa [show (hopfPull e AK).carrier =
        AK.carrier.map (pbE (C := C) (R := R) e : (K → C) →ₗ[R] (ZMod p → C)) from rfl,
      map_pbE_symm] at hc

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.TangentPairingStatement
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀)

def evK {R' R : LAlg R₀} (π : LHom R' R) (h : B.gg →ₗ[R₀] R') (V : B.gg ⊗[R₀] π.ker) : R' :=
  LinearMap.mul' R₀ R' (TensorProduct.map h π.ker.subtype V)

end BX

def TangentPairingStatement (B : BX R₀) : Prop :=
  ∀ (R' R : LAlg R₀) (π : LHom R' R) (ξ : (R' : Type u)) (Dp : DualPair R) (N : ℕ)
    (hsurj : Function.Surjective π.1) (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0),
    (∀ a, a * ξ = 0 → a ∈ Ideal.span {ξ}) → (N : (R' : Type u)) = 0 →
    ∀ (sh th : B.G R') (Vs Vt : B.gg ⊗[R₀] π.ker) (hs ht : B.gg →ₗ[R₀] R')
      (zh : (R' : Type u)ˣ) (z : (R : Type u)ˣ),
      N • sh = B.tg π (π.sqZero_of_span ξ hsurj hker hsq) Vs → N • th = B.tg π (π.sqZero_of_span ξ hsurj hker hsq) Vt →
      B.IsHeight Dp N (B.map π sh) (π.1.toLinearMap ∘ₗ hs) →
      B.IsHeight Dp N (B.map π th) (π.1.toLinearMap ∘ₗ ht) →
      B.IsPairing N (B.map π sh) (B.map π th) z → Units.map (π.1 : R' →* R) zh = z →
      (zh : (R' : Type u)) ^ N = 1 + (B.evK π ht Vs - B.evK π hs Vt)

end ReciprocityTheory.PGsh
end
end

section -- merged from ReciprocityTheory.DualLattices.LenIdStatement
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

def qE {R : Type} [CommRing R] {g m : ℕ} (εL : Fin m → Matrix (Fin g) (Fin g) R) (i j : Fin m) :
    Submodule R (Fin g ⊕ Fin g → R) :=
  (LinearMap.range (Matrix.mulVecLin (εL j)ᵀ)).comap (LinearMap.funLeft R R Sum.inl) ⊓
    (LinearMap.range (Matrix.mulVecLin (εL i))).comap (LinearMap.funLeft R R Sum.inr)

abbrev xModE {R : Type} [CommRing R] {g m : ℕ} (Ht Bt : Matrix (Fin g) (Ix g) R)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)) (i : Fin m) :=
  qE εL i (π i) ⧸
    ((LinearMap.range (Matrix.mulVecLin (εT i))).map (Matrix.mulVecLin (fromRows Ht Bt))).comap
      (qE εL i (π i)).subtype

def LenIdStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (g m : ℕ) (Ht Bt : Matrix (Fin g) (Ix g) R) (E : Matrix (Ix g) (Ix g) R)
    (cp : R), cp ≠ 0 → IsUnit E.det → Btᵀ * Ht - Htᵀ * Bt = cp • E →
    ∀ (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)), (∀ i, π (π i) = i) →
    (∀ i j, εT i * εT j = if i = j then εT i else 0) → ∑ i, εT i = 1 →
    (∀ i j, εL i * εL j = if i = j then εL i else 0) → ∑ i, εL i = 1 →
    (∀ i, Ht * εT i = (εL (π i))ᵀ * Ht) → (∀ i, Bt * εT i = εL i * Bt) →
    (∀ i, (εT i)ᵀ * E = E * εT (π i)) →
    ∀ (i : Fin m) (d : ℕ), Nonempty (LinearMap.range (Matrix.mulVecLin (εL i)) ≃ₗ[R] (Fin d → R)) →
    ∀ c₁ c₂ : NNReal, HasLen v R (cokE Ht εT εL i (π i)) c₁ →
      HasLen v R (cokE Ht εT εL (π i) i) c₂ →
      ∃ X : NNReal, HasLen v R (xModE Ht Bt εT εL π i) X ∧ X * c₁ = v (algebraMap R C cp) ^ d * c₂

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.ColengthCotangentBoundStatementOfClaim
section -- merged from ReciprocityTheory.DualLattices.ColengthCotangentBoundStatement
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def ColengthCotangentBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → v (p : C) < 1 →
    ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) →
    ∀ (AA : HopfOrder (C := C) R N) (lenN lenOm : NNReal),
      HasColen R v AA.carrier lenN → HasLen v R (OmAA AA.carrier) lenOm →
      lenN ^ 2 ≤ lenOm ^ Fintype.card N

end ReciprocityTheory.PGsh.Up
end
end

noncomputable section

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def ColengthCotangentValuation (p : ℕ) (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] : Prop :=
  ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) →
    ∀ AA : HopfOrder (C := C) R N,
    ∃ (n : ℕ) (g : Fin n → N → C) (δ : Fin n → R),
      (∀ i, g i ∈ augIdeal AA.carrier) ∧
      (∀ f ∈ augIdeal AA.carrier, ∃ r : Fin n → R,
        f - ∑ j, r j • g j ∈ sqIdeal (augIdeal AA.carrier)) ∧
      (∀ i, ∃ a : Fin n → R,
        δ i • g i - ∑ j, (if j < i then a j else 0) • g j ∈ sqIdeal (augIdeal AA.carrier)) ∧
      ∀ c, HasColen R v AA.carrier c →
        c ^ 2 = (∏ i, v (algebraMap R C (δ i))) ^ Fintype.card N

theorem colengthCotangentBound_of_claim (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal)
    (R : Type) [CommRing R] [Algebra R C] (hv : v.Integers R) (hcl : ColengthCotangentValuation p C v R)
    (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (hN : ∀ x : N, p • x = 0)
    (AA : HopfOrder (C := C) R N) (lenN lenOm : NNReal)
    (hlen : HasColen R v AA.carrier lenN) (hom : HasLen v R (OmAA AA.carrier) lenOm) :
    lenN ^ 2 ≤ lenOm ^ Fintype.card N := by
  obtain ⟨n, g, δ, hg, hgen, htri, hcol⟩ := hcl N hN AA
  let q := ((sqIdeal (augIdeal AA.carrier)).comap (augIdeal AA.carrier).subtype).mkQ
  have key : ∀ x z : augIdeal AA.carrier,
      ((x : N → C) - z) ∈ sqIdeal (augIdeal AA.carrier) → q x = q z := by
    intro x z h
    exact (Submodule.Quotient.eq _).mpr (by simpa [Submodule.mem_comap] using h)
  let y : Fin n → OmAA AA.carrier := fun i => q ⟨g i, hg i⟩
  have hy : Submodule.span R (Set.range y) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨r, hr⟩ := hgen f hf
    have e : q ⟨f, hf⟩ = ∑ j, r j • y j := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [y, ← map_smul, ← map_sum]
      apply key
      simpa using hr
    show q ⟨f, hf⟩ ∈ _
    rw [e]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have hrel : ∀ i, ∃ a : Fin n → R, δ i • y i = ∑ j, (if j < i then a j else 0) • y j := by
    intro i
    obtain ⟨a, ha⟩ := htri i
    refine ⟨a, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, ← map_smul, ← map_sum]
    apply key
    have e2 : (((∑ j, (if j < i then a j else 0) • (⟨g j, hg j⟩ : augIdeal AA.carrier) :
        augIdeal AA.carrier)) : N → C) = ∑ j, (if j < i then a j else 0) • g j := by
      rw [Submodule.coe_sum]
      rfl
    rw [e2]
    exact ha
  have hle := prod_le_of_gen hv hom y hy δ hrel
  rw [hcol lenN hlen]
  first
    | exact pow_le_pow_left₀ zero_le hle _
    | exact pow_le_pow_left zero_le hle _
    | gcongr

theorem colengthCotangentBoundStatement_of_claim (hcl : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → v (p : C) < 1 → ColengthCotangentValuation p C v R) : ColengthCotangentBoundStatement := by
  intro p _ C _ _ _ v R _ _ hv hp N _ _ _ hN AA lenN lenOm hlen hom
  exact colengthCotangentBound_of_claim p C v R hv (hcl p C v R hv hp) N hN AA lenN lenOm hlen hom

end ReciprocityTheory.PGsh.Up
end
end
