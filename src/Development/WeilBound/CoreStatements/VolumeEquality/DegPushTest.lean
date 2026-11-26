module

public import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.DegPushTestA
noncomputable section

namespace SheetDecomposition

open MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

section Relabel

variable {Ψ Ψ' : Type} [Fintype Ψ] [DecidableEq Ψ] [Fintype Ψ'] [DecidableEq Ψ'] {N : ℕ} (e : Ψ ≃ Ψ')

theorem degFl_rename (F : RP Ψ N) : degFl (rename (e.prodCongr (Equiv.refl (Fin N))) F : RP Ψ' N) = degFl F := by
  unfold degFl
  have hd : dimFl Ψ' N = dimFl Ψ N := by
    unfold dimFl
    rw [Fintype.card_congr e]
  rw [hd, ← (Equiv.arrowCongr e (Equiv.refl (Equiv.Perm (Fin N)))).sum_comp]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hp : permExp ((Equiv.arrowCongr e (Equiv.refl (Equiv.Perm (Fin N)))) σ) =
      Finsupp.mapDomain (e.prodCongr (Equiv.refl (Fin N))) (permExp σ) := by
    ext ⟨τ', i⟩
    rw [Finsupp.mapDomain_equiv_apply]
    simp [permExp]
  rw [hp, coeff_rename_mapDomain _ (e.prodCongr (Equiv.refl (Fin N))).injective]
  congr 1
  exact Equiv.prod_comp e.symm (fun τ => ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ))

theorem rename_muSmall (j : ℕ) : (rename (e.prodCongr (Equiv.refl (Fin N))) (muSmall j : RP Ψ N) : RP Ψ' N) = muSmall j := by
  unfold muSmall
  split_ifs
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, rename_X, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [pkLow, map_neg, map_sum, map_pow, rename_X, Equiv.prodCongr_apply, Prod.map_apply,
      Equiv.refl_apply]
      congr 1
      exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem rename_fibClass (j : ℕ) : (rename (e.prodCongr (Equiv.refl (Fin N))) (fibClass j : RP Ψ N) : RP Ψ' N) = fibClass j := by
  unfold fibClass
  simp only [map_prod, map_sub, rename_X, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

end Relabel

theorem testRelabel : TestRelabel := by
  intro Ψ _ _ N j
  unfold testDeg
  rw [← degFl_rename (Fintype.equivFin Ψ), map_mul, map_pow, rename_muSmall, rename_fibClass]
  simp [dimX]

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {p q : ℕ}

theorem count_pairs : Fintype.card Ψ * p * q + Fintype.card (PairIx Ψ p q) = dimFl Ψ (p + q) := by
  classical
  have hL : (Finset.univ.filter fun ab : Fin (p + q) × Fin (p + q) => ab.1 < ab.2).card =
      (p + q) * (p + q - 1) / 2 := by
    rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm, ← Finset.sum_range_id,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.card_filter, Finset.filter_gt_eq_Iio, Fin.card_Iio]
  have hC : ((Finset.univ.filter fun ab : Fin (p + q) × Fin (p + q) => ab.1 < ab.2).filter
      fun ab => ¬ ((ab.1 : ℕ) < p ↔ (ab.2 : ℕ) < p)).card = p * q := by
    have e : ((Finset.univ.filter fun ab : Fin (p + q) × Fin (p + q) => ab.1 < ab.2).filter
        fun ab => ¬ ((ab.1 : ℕ) < p ↔ (ab.2 : ℕ) < p)) =
        (Finset.univ.filter fun a : Fin (p + q) => (a : ℕ) < p) ×ˢ
          (Finset.univ.filter fun b : Fin (p + q) => ¬ (b : ℕ) < p) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product, Fin.lt_iff_val_lt_val]
      omega
    have h1 : (Finset.univ.filter fun a : Fin (p + q) => (a : ℕ) < p).card = p := by
      rw [Fin.card_filter_val_lt]
      omega
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (p + q))))
      (fun a : Fin (p + q) => (a : ℕ) < p)
    rw [h1, Finset.card_univ, Fintype.card_fin] at h2
    rw [e, Finset.card_product, h1]
    congr 1
    omega
  have hS : Fintype.card {ab : Fin (p + q) × Fin (p + q) // ab.1 < ab.2 ∧ ((ab.1 : ℕ) < p ↔ (ab.2 : ℕ) < p)} +
      p * q = (p + q) * (p + q - 1) / 2 := by
    rw [Fintype.card_subtype, ← hL, ← hC, ← Finset.filter_filter]
    exact Finset.card_filter_add_card_filter_not _
  rw [Fintype.card_prod]
  unfold dimFl
  rw [← hS]
  ring

def muCoef (Ψ : Type) (p q : ℕ) : Ψ × Fin (p + q) → ℤ := fun x => if p ≤ (x.2 : ℕ) then 1 else 0

def fibCoef (t : PairIx Ψ p q) : Ψ × Fin (p + q) → ℤ := fun x =>
  (if x = (t.1, t.2.1.2) then 1 else 0) - if x = (t.1, t.2.1.1) then 1 else 0

theorem sum_muCoef {A : Type} [AddCommGroup A] (x : Ψ × Fin (p + q) → A) :
    ∑ r, muCoef Ψ p q r • x r = ∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (p + q) => p ≤ (i : ℕ)), x (τ, i) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [muCoef]
  split_ifs <;> simp

theorem sum_fibCoef {A : Type} [AddCommGroup A] (x : Ψ × Fin (p + q) → A) (t : PairIx Ψ p q) :
    ∑ r, fibCoef t r • x r = x (t.1, t.2.1.2) - x (t.1, t.2.1.1) := by
  simp [fibCoef, sub_smul, Finset.sum_sub_distrib, ite_smul]

theorem test_factor {n r : ℕ} (e : Fin r ≃ PairIx Ψ p q) (hq : q ≤ p) (hn : n = Fintype.card Ψ * p * q) :
    (muSmall p ^ dimX Ψ (p + q) p * fibClass p : RP Ψ (p + q)) =
      ∏ j : Fin (n + r), ∑ x, Fin.append (fun _ : Fin n => muCoef Ψ p q) (fun j => fibCoef (e j)) j x • X x := by
  have hN : p + q - p ≤ p := by omega
  have hmu : (muSmall p : RP Ψ (p + q)) = ∑ x, muCoef Ψ p q x • (X x : RP Ψ (p + q)) := by
    rw [sum_muCoef (X : Ψ × Fin (p + q) → RP Ψ (p + q))]
    unfold muSmall
    rw [if_pos hN]
  have hdim : dimX Ψ (p + q) p = n := by
    unfold dimX
    rw [hn, Nat.add_sub_cancel_left]
    ring
  have hfib : (fibClass p : RP Ψ (p + q)) = ∏ i : Fin r, ∑ x, fibCoef (e i) x • (X x : RP Ψ (p + q)) := by
    simp only [sum_fibCoef]
    rw [Fintype.prod_equiv e _ (fun t : PairIx Ψ p q => (X (t.1, t.2.1.2) - X (t.1, t.2.1.1) : RP Ψ (p + q)))
      (fun _ => rfl)]
    unfold fibClass
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← Finset.prod_subtype_eq_prod_filter, Finset.subtype_univ]
    try rfl
  rw [Fin.prod_univ_add, hmu, hdim, hfib]
  simp only [Fin.append_left, Fin.append_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end SheetDecomposition
end
end

section -- merged from Development.WeilBound.CoreStatements.VolumeEquality.DegPushTestB
namespace SheetDecomposition

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel

theorem exists_multilinear_gen {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P (d + 1)) :
    ∃ F : MultilinearMap (RingHom.id ℤ) (fun _ : Fin d => K → ℤ) ℤ,
      ∀ bs, F bs = NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) bs := by
  have hX : IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) d := isProjVarF_map_of_isArithVar hP
  have hXN : NumbersDVR.IsMultiProjPrime (P.map (MvPolynomial.map (Int.castRingHom ℚ))) :=
    (Bridge.isMultiProjPrime_iff _).mpr hX.1
  have hd : FieldNumbers.relDim (P.map (MvPolynomial.map (Int.castRingHom ℚ))) = d := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq _ _ hX.2]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  let I := P.map (MvPolynomial.map (Int.castRingHom ℚ))
  have hadd (bs : Fin d → K → ℤ) (i : Fin d) (x y : K → ℤ) :
      NumbersDVR.intNum ℚ I (Function.update bs i (x + y)) =
        NumbersDVR.intNum ℚ I (Function.update bs i x) +
          NumbersDVR.intNum ℚ I (Function.update bs i y) :=
    FieldNumbers.IntNumAdd.full ℚ K ι I hXN.multiHomog hXN.relevant d hd bs i x y
  refine ⟨{ toFun := NumbersDVR.intNum ℚ I
            map_update_add' := ?_
            map_update_smul' := ?_ }, fun _ => rfl⟩
  · intro inst bs i x y
    obtain rfl : inst = instDecidableEqFin d := Subsingleton.elim _ _
    exact hadd bs i x y
  · intro inst bs i c x
    obtain rfl : inst = instDecidableEqFin d := Subsingleton.elim _ _
    let g : (K → ℤ) →+ ℤ := AddMonoidHom.mk'
      (fun y => NumbersDVR.intNum ℚ I (Function.update bs i y)) (hadd bs i)
    exact map_zsmul g c x

end SheetDecomposition
end

noncomputable section

namespace SheetDecomposition

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal intNum mixedDiff diffStep)

theorem intNum_perm {K : Type} [DecidableEq K] {ι : K → Type} {F : Type} [Field F] (I : Ideal (MvPolynomial (Σ k, ι k) F))
    {n m : ℕ} (a : Fin n → K → ℤ) (b : Fin m → K → ℤ) (h : (List.ofFn a).Perm (List.ofFn b)) : intNum F I a = intNum F I b := by
  have : LeftCommutative (diffStep (K := K)) := ⟨fun x y g => by
    funext z
    simp only [diffStep, sub_right_comm z x y]
    ring⟩
  unfold intNum mixedDiff
  rw [h.foldr_eq]

theorem monoLines_perm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} (l : J → HermLine ι) {d : ℕ}
    (w : Fin d → J) :
    (List.ofFn fun k => (monoLines l (∑ j, Finsupp.single (w j) 1) d k).a).Perm (List.ofFn fun j => (l (w j)).a) := by
  have h1 : Finsupp.toMultiset (∑ j, Finsupp.single (w j) 1 : J →₀ ℕ) = (List.ofFn w : Multiset J) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Fin.univ_val_map, Finset.sum_eq_multiset_sum]
    simp only [Finsupp.toMultiset_single, one_smul]
    conv_rhs => rw [← Multiset.sum_map_singleton (Multiset.map w Finset.univ.val), Multiset.map_map]
    rfl
  have h2 : (Finsupp.toMultiset (∑ j, Finsupp.single (w j) 1 : J →₀ ℕ)).toList.Perm (List.ofFn w) := by
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, h1]
  have h4 : (List.ofFn fun k => (monoLines l (∑ j, Finsupp.single (w j) 1) d k).a) =
      ((Finsupp.toMultiset (∑ j, Finsupp.single (w j) 1 : J →₀ ℕ)).toList).map fun x => (l x).a := by
    refine List.ext_getElem (by simp) fun i h h' => ?_
    have hi : i < (Finsupp.toMultiset (∑ j, Finsupp.single (w j) 1 : J →₀ ℕ)).toList.length := by simpa using h'
    simp only [List.getElem_ofFn, List.getElem_map, monoLines, dif_pos hi, List.get_eq_getElem]
  rw [h4]
  have h5 := h2.map fun x => (l x).a
  rwa [List.map_ofFn] at h5

theorem monoLines_smooth {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {J : Type} (l : J → HermLine ι)
    (hl : ∀ j, IsSmoothHerm (l j)) (m : J →₀ ℕ) (d : ℕ) (k : Fin d) : IsSmoothHerm (monoLines l m d k) := by
  unfold monoLines
  split_ifs
  · exact hl _
  · exact contDiffOn_const

variable {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N)

open Classical in
theorem geoFun_word (hI : PB.Inputs) (w : Fin (dimFl Ψ N) → Ψ × Fin N) :
    M.geoFun (toA (∏ j, X (w j))) * M.δ =
      (intNum ℚ (M.P.map (MvPolynomial.map (Int.castRingHom ℚ))) fun j => M.xdeg (w j) : ℤ) := by
  have h1 : toA (∏ j, X (w j) : RP Ψ N) = basisMonomials (Option (Ψ × Fin N)) ℝ (∑ j, Finsupp.single (some (w j)) 1) := by
    simp only [toA, map_prod, rename_X, coe_basisMonomials]
    rw [monomial_sum_one]
    rfl
  have h2 : (∑ j, Finsupp.single (some (w j)) 1 : Option (Ψ × Fin N) →₀ ℕ).degree = dimFl Ψ N := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  have h3 : (∑ j, Finsupp.single (some (w j)) 1 : Option (Ψ × Fin N) →₀ ℕ) none = 0 := by
    simp [Finsupp.finsetSum_apply]
  have hs : ∀ j, IsSmoothHerm (M.line 1 j) := fun j => by
    cases j
    · exact M.A_smooth
    · exact M.x_smooth _ _
  have h4 := GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree hI.degree M.K M.ι M.P (dimFl Ψ N)
    (monoLines (M.line 1) (∑ j, Finsupp.single (some (w j)) 1) (dimFl Ψ N)) M.arith (monoLines_smooth _ hs _ _)
  have hδ : (M.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 M.δ_pos.ne'
  rw [h1, RootModel.geoFun, Module.Basis.constr_basis, RootModel.geoMono, if_pos h2, h3, pow_zero, mul_one, div_mul_cancel₀ _ hδ]
  refine h4.trans (congrArg _ ?_)
  refine (intNum_perm _ _ _ (monoLines_perm (M.line 1) fun j => some (w j))).trans ?_
  simp only [RootModel.line, M.x_deg]

open Classical in
theorem geoFun_prod (hI : PB.Inputs) (c : Fin (dimFl Ψ N) → Ψ × Fin N → ℤ) :
    M.geoFun (toA (∏ j, ∑ x, c j x • X x)) * M.δ =
      (intNum ℚ (M.P.map (MvPolynomial.map (Int.castRingHom ℚ))) fun j => ∑ x, c j x • M.xdeg x : ℤ) := by
  obtain ⟨F, hF⟩ := exists_multilinear_gen (P := M.P) M.arith
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hF, F.map_sum, Fintype.prod_sum]
  have h1 : ∀ w : Fin (dimFl Ψ N) → Ψ × Fin N, toA (∏ j, c j (w j) • X (w j) : RP Ψ N) =
      ((∏ j, c j (w j) : ℤ) : ℝ) • toA (∏ j, X (w j)) := fun w => by
    rw [Finset.prod_smul, Int.cast_smul_eq_zsmul, toA, toA, map_zsmul]
  have h2 : toA (∑ w : Fin (dimFl Ψ N) → Ψ × Fin N, ∏ j, c j (w j) • X (w j) : RP Ψ N) =
      ∑ w : Fin (dimFl Ψ N) → Ψ × Fin N, toA (∏ j, c j (w j) • X (w j)) := map_sum (rename some) _ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, map_sum, Finset.sum_mul, Int.cast_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [h1, map_smul, F.map_smul_univ, smul_eq_mul, smul_eq_mul, mul_assoc, geoFun_word M hI, hF, Int.cast_mul]
  rfl

theorem test_pointIdeal_rat {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [h : Algebra ℚ Ω]
    (y : (Σ k, ι k) → Ω) : pointIdeal ℚ y = (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) := by
  have : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : h = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  exact (GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalNef.genIdeal_eq y).symm

theorem geoTest : GeoTest := by
  intro hI Ψ _ _ p q M _ n r e hq hn
  have hc : n + r = dimFl Ψ (p + q) := by
    rw [hn, ← count_pairs, ← Fintype.card_congr e, Fintype.card_fin]
  refine ⟨hc, ?_⟩
  have key : ∀ (d : ℕ) (_ : d = dimFl Ψ (p + q)) (c : Fin d → Ψ × Fin (p + q) → ℤ),
      M.geoFun (toA (∏ j, ∑ x, c j x • X x)) * M.δ = inum ℚ M.y fun j => ∑ x, c j x • M.xdeg x := by
    rintro _ rfl c
    rw [inum, test_pointIdeal_rat]
    convert geoFun_prod M hI c
    rfl
  rw [test_factor e hq hn, key _ hc]
  congr 2
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [Fin.append_left, sum_muCoef, muDeg]
  · simp only [Fin.append_right, sum_fibCoef, fibDeg]

end SheetDecomposition
