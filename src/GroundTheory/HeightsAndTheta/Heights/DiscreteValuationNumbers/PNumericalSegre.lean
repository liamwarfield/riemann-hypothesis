module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsExamples
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.JoinCoordMidVar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PNumericalSegre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace NumericalSegreProof

section Combinatorics

theorem sum_antidiagonalTuple_succ {A : Type*} [AddCommMonoid A] (i c : ℕ)
    (f : (Fin (i + 1) → ℕ) → A) :
    ∑ α ∈ Finset.Nat.antidiagonalTuple (i + 1) (c + 1), f α =
      ∑ α ∈ Finset.Nat.antidiagonalTuple i (c + 1), f (Fin.snoc α 0) +
        ∑ β ∈ Finset.Nat.antidiagonalTuple (i + 1) c,
          f (Function.update β (Fin.last i) (β (Fin.last i) + 1)) := by
  have hsum : ∀ (α : Fin (i + 1) → ℕ) (v : ℕ),
      ∑ j, Function.update α (Fin.last i) v j = ∑ j : Fin i, α (Fin.castSucc j) + v := by
    intro α v
    rw [Fin.sum_univ_castSucc]
    simp
  have hsum' : ∀ α : Fin (i + 1) → ℕ,
      ∑ j, α j = ∑ j : Fin i, α (Fin.castSucc j) + α (Fin.last i) := fun α =>
    Fin.sum_univ_castSucc α
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun α : Fin (i + 1) → ℕ => α (Fin.last i) = 0)]
  congr 1
  · refine Finset.sum_nbij' Fin.init (fun α => Fin.snoc α 0) ?_ ?_ ?_ ?_ ?_
    · intro α hα
      simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hα ⊢
      rw [hsum'] at hα
      simpa [Fin.init, hα.2] using hα.1
    · intro α hα
      simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hα ⊢
      refine ⟨?_, by simp⟩
      rw [hsum']
      simpa using hα
    · intro α hα
      simp only [Finset.mem_filter] at hα
      rw [← hα.2, Fin.snoc_init_self]
    · intro α _
      exact Fin.init_snoc _ _
    · intro α hα
      simp only [Finset.mem_filter] at hα
      rw [← hα.2, Fin.snoc_init_self]
  · have linv : ∀ α : Fin (i + 1) → ℕ, α (Fin.last i) ≠ 0 →
        Function.update (Function.update α (Fin.last i) (α (Fin.last i) - 1)) (Fin.last i)
          (Function.update α (Fin.last i) (α (Fin.last i) - 1) (Fin.last i) + 1) = α := by
      intro α hα
      rw [Function.update_self, Function.update_idem, Nat.sub_add_cancel (Nat.pos_of_ne_zero hα),
        Function.update_eq_self]
    refine Finset.sum_nbij' (fun α => Function.update α (Fin.last i) (α (Fin.last i) - 1))
      (fun β => Function.update β (Fin.last i) (β (Fin.last i) + 1)) ?_ ?_ ?_ ?_ ?_
    · intro α hα
      simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hα ⊢
      rw [hsum]
      rw [hsum'] at hα
      omega
    · intro β hβ
      simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hβ ⊢
      rw [hsum, Function.update_self]
      rw [hsum'] at hβ
      refine ⟨by omega, by omega⟩
    · intro α hα
      simp only [Finset.mem_filter] at hα
      exact linv α hα.2
    · intro β _
      simp
    · intro α hα
      simp only [Finset.mem_filter] at hα
      rw [linv α hα.2]

end Combinatorics

section Lists

variable {K : Type*} [DecidableEq K]


omit [DecidableEq K] in
theorem rootList_succ {i : ℕ} (x : Fin (i + 1) → K → ℤ) (α : Fin (i + 1) → ℕ) :
    rootList x α = rootList (fun j => x (Fin.castSucc j)) (Fin.init α) ++
      List.replicate (α (Fin.last i)) (x (Fin.last i)) := by
  unfold rootList
  rw [List.finRange_succ_last]
  simp [List.flatMap_append, Fin.init, List.flatMap_map]

omit [DecidableEq K] in
theorem rootList_snoc_zero {i : ℕ} (x : Fin (i + 1) → K → ℤ) (α : Fin i → ℕ) :
    rootList x (Fin.snoc α 0) = rootList (fun j => x (Fin.castSucc j)) α := by
  rw [rootList_succ, Fin.init_snoc, Fin.snoc_last]
  simp

omit [DecidableEq K] in
theorem rootList_update_last {i : ℕ} (x : Fin (i + 1) → K → ℤ) (β : Fin (i + 1) → ℕ) :
    rootList x (Function.update β (Fin.last i) (β (Fin.last i) + 1)) =
      rootList x β ++ [x (Fin.last i)] := by
  have hinit : Fin.init (Function.update β (Fin.last i) (β (Fin.last i) + 1)) = Fin.init β := by
    funext j
    simp [Fin.init]
  rw [rootList_succ, rootList_succ x β, hinit, Function.update_self, List.replicate_succ',
    List.append_assoc]

omit [DecidableEq K] in
theorem rootList_zero {n : ℕ} (x : Fin n → K → ℤ) : rootList x 0 = [] := by
  simp [rootList]

theorem intNumL_eq {ι : K → Type*} (F : Type*) [Field F] (P : Ideal (MRing ι F))
    (l : List (K → ℤ)) : intNumL F P l = eventualValue (l.foldr diffStep (hilbFn P)) := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get]

theorem intNumL_perm {ι : K → Type*} (F : Type*) [Field F] (P : Ideal (MRing ι F))
    {l l' : List (K → ℤ)} (h : l.Perm l') : intNumL F P l = intNumL F P l' := by
  rw [intNumL_eq, intNumL_eq, h.foldr_eq]

end Lists

def segreSide {K : Type*} [DecidableEq K] {ι : K → Type*} (F : Type*) [Field F]
    (P : Ideal (MRing ι F)) {i : ℕ} (x : Fin i → K → ℤ) (n : ℕ) (Y : List (K → ℤ)) : ℤ :=
  if i - 1 ≤ n then
    ∑ α ∈ Finset.Nat.antidiagonalTuple i (n - (i - 1)), intNumL F P (rootList x α ++ Y)
  else 0

theorem segreSide_succ {K : Type*} [DecidableEq K] {ι : K → Type*} (F : Type*) [Field F]
    (P : Ideal (MRing ι F)) {i : ℕ} (hi : 1 ≤ i) (x : Fin (i + 1) → K → ℤ) (m : ℕ)
    (Y : List (K → ℤ)) :
    segreSide F P x (m + 1) Y =
      segreSide F P (fun j => x (Fin.castSucc j)) m Y +
        segreSide F P x m (x (Fin.last i) :: Y) := by
  unfold segreSide
  simp only [Nat.add_sub_cancel]
  by_cases h : i ≤ m + 1
  · obtain ⟨c, hc⟩ : ∃ c, m + 1 = i + c := ⟨m + 1 - i, by omega⟩
    rw [ite_eq_left h, ite_eq_left (by omega), show m + 1 - i = c by omega,
      show m - (i - 1) = c by omega]
    rcases c with _ | c
    · rw [ite_eq_right (by omega), add_zero, Finset.Nat.antidiagonalTuple_zero_right,
        Finset.Nat.antidiagonalTuple_zero_right, Finset.sum_singleton, Finset.sum_singleton,
        rootList_zero, rootList_zero]
    · rw [ite_eq_left (by omega), show m - i = c by omega, sum_antidiagonalTuple_succ]
      congr 1
      · refine Finset.sum_congr rfl fun α _ => ?_
        rw [rootList_snoc_zero]
      · refine Finset.sum_congr rfl fun β _ => ?_
        rw [rootList_update_last, List.append_assoc, List.singleton_append]
  · rw [ite_eq_right h, ite_eq_right (by omega), ite_eq_right (by omega), add_zero]

theorem zetaDeg_split {K : Type*} (a c : K → ℤ) :
    ((zetaDeg + liftDeg (c - a)) + liftDeg (a - c) : Option K → ℤ) = zetaDeg := by
  funext o
  cases o <;> simp [zetaDeg, liftDeg]

theorem truncCoord_of_le {N : ℕ} {Φ : Type*} [Zero Φ] (t : Fin N → Φ) {i : ℕ} (h : N ≤ i) :
    truncCoord t i = t := by
  funext j
  simp [truncCoord, lt_of_lt_of_le j.isLt h]

theorem intNumL_cons_add (hadd : FieldNumbers.IntNumAdd.Statement.{0}) (F : Type) [Field F]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P) (l : List (K → ℤ))
    (hd : FieldNumbers.relDim P = ((l.length + 1 : ℕ) : WithBot (WithTop ℤ))) (c c' : K → ℤ) :
    intNumL F P ((c + c') :: l) = intNumL F P (c :: l) + intNumL F P (c' :: l) := by
  have key : ∀ d, Function.update (c :: l).get (0 : Fin (l.length + 1)) d = (d :: l).get := by
    intro d
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · rw [Function.update_of_ne (Fin.succ_ne_zero j)]
      rfl
  have h := hadd F K ι P hP.multiHomog hP.relevant (l.length + 1) hd ((c :: l).get) 0 c c'
  rw [key, key, key] at h
  exact h

end NumericalSegreProof


open NumericalSegreProof in
theorem NumericalSegre.proof (hadd : FieldNumbers.IntNumAdd.Statement.{0})
    (hdim : FlagBundleDim.Statement) (hcut : FlagBundleCut.Statement)
    (hvan : FlagBundlePullbackVanish.Statement) (hbase : FlagBundleLineBase.Statement) :
    NumericalSegre.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hP hdimV N hN E _ _ B w b hflag M a φ hφ Φ _ _ t ht n Y hnY
  have claim : ∀ i : ℕ, 1 ≤ i → ∀ hi : i ≤ N, ∀ (n : ℕ) (Y : List (K → ℤ)),
      n + Y.length + 1 = e + i →
      intNumL F (projIdeal F y w φ (truncCoord t i)) (List.replicate n zetaDeg ++ Y.map liftDeg) =
        segreSide F (pointIdeal F y) (fun j : Fin i => a - b (Fin.castLE hi j)) n Y := by
    intro i hi1
    induction i, hi1 using Nat.le_induction with
    | base =>
      intro hi n Y hnY
      rw [hbase F Ω K ι y e hP hdimV N E B w b hflag M a φ hφ Φ t ht hi n Y (by omega)]
      simp [segreSide, Finset.Nat.antidiagonalTuple_one, rootList, List.finRange_succ]
      rfl
    | succ i hi1 ih =>
      intro hi n
      induction n with
      | zero =>
        intro Y hY
        rw [List.replicate_zero, List.nil_append,
          hvan F Ω K ι y e hP hdimV N E B w b hflag M a φ hφ Φ t ht (i + 1) (by omega) hi Y
            (by omega)]
        unfold segreSide
        rw [ite_eq_right (by omega)]
      | succ m ihm =>
        intro Y hY
        set l := List.replicate m (zetaDeg : Option K → ℤ) ++ Y.map liftDeg with hl
        have hlen : l.length + 1 = e + i := by
          simp [hl]
          omega
        obtain ⟨hPi, hdi⟩ := hdim F Ω K ι y e hP hdimV N E B w b hflag M a φ hφ Φ t ht (i + 1)
          (by omega) hi
        rw [show e + (i + 1) - 1 = l.length + 1 by omega] at hdi
        rw [List.replicate_succ, List.cons_append, ← hl,
          ← zetaDeg_split a (b ⟨i, hi⟩), intNumL_cons_add hadd F _ hPi l hdi]
        have hc := hcut F Ω K ι y e hP hdimV N E B w b hflag M a φ hφ Φ t ht ⟨i, hi⟩ hi1 l hlen
        simp only at hc
        rw [hc, ih (by omega) m Y (by omega)]
        have hperm : (liftDeg (a - b ⟨i, hi⟩) :: l).Perm
            (List.replicate m zetaDeg ++ ((a - b ⟨i, hi⟩) :: Y).map liftDeg) := by
          rw [hl, List.map_cons]
          exact List.perm_middle.symm
        rw [intNumL_perm F _ hperm, ihm _ (by simp; omega), segreSide_succ F _ hi1]
        rfl
  rw [← truncCoord_of_le t (le_refl N), claim N hN (le_refl N) n Y (by omega)]
  rfl

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSymmetricSpanHsymm
section -- merged from GroundTheory.HeightsAndTheta.Theta.Capelli.CompleteHomogeneous
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

namespace SymmFun

open MvPolynomial Finset

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem eval_hsymm (x : σ → ℂ) (b : ℕ) :
    eval x (hsymm σ ℂ b) = ∑ l ∈ finsuppAntidiag (univ : Finset σ) b, ∏ i, x i ^ l i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsymm, map_sum]
  refine Finset.sum_bij' (fun s _ => Multiset.toFinsupp s.1)
    (fun l hl => ⟨Finsupp.toMultiset l, by
      rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (by simp)]
      exact (mem_finsuppAntidiag.mp hl).1⟩) ?_ ?_ ?_ ?_ ?_
  · intro s _
    rw [mem_finsuppAntidiag]
    refine ⟨?_, by simp⟩
    have := Multiset.toFinsupp_sum_eq s.1
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    exact this.trans s.2
  · intro l _
    exact Finset.mem_univ _
  · intro s _
    ext1
    simp
  · intro l _
    simp
  · intro s _
    rw [map_multiset_prod, Multiset.map_map, Finset.prod_multiset_map_count]
    rw [Finset.prod_subset (Finset.subset_univ _)]
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp [Multiset.toFinsupp_apply]
    · intro i _ hi
      rw [Multiset.mem_toFinset] at hi
      rw [Multiset.count_eq_zero.mpr hi, pow_zero]

noncomputable def hSeries (x : σ → ℂ) : PowerSeries ℂ := PowerSeries.mk fun b => eval x (hsymm σ ℂ b)

theorem hSeries_eq_prod (x : σ → ℂ) :
    hSeries x = ∏ i, PowerSeries.mk fun k => x i ^ k := by
  ext b
  rw [hSeries, PowerSeries.coeff_mk, eval_hsymm, PowerSeries.coeff_prod]
  simp [PowerSeries.coeff_mk]

theorem one_sub_mul_geom (a : ℂ) :
    (1 - PowerSeries.C a * PowerSeries.X) * PowerSeries.mk (fun k => a ^ k) = 1 := by
  ext k
  rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul]
  rcases k with _ | k
  · simp
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_one,
      if_neg (Nat.succ_ne_zero k), pow_succ, mul_comm, sub_self]

theorem prod_one_sub_mul_hSeries (x : σ → ℂ) :
    (∏ i, (1 - PowerSeries.C (x i) * PowerSeries.X)) * hSeries x = 1 := by
  rw [hSeries_eq_prod, ← Finset.prod_mul_distrib]
  simp [one_sub_mul_geom]

theorem coeff_prod_one_sub (x : σ → ℂ) (s : ℕ) :
    PowerSeries.coeff s (∏ i, (1 - PowerSeries.C (x i) * PowerSeries.X)) =
      (-1) ^ s * eval x (esymm σ ℂ s) := by
  have h : ∏ i, (1 - PowerSeries.C (x i) * PowerSeries.X) =
      ∏ i, (PowerSeries.C (-x i) * PowerSeries.X + 1) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_neg, neg_mul, ← sub_eq_neg_add]
  rw [h, Finset.prod_add]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, ← map_prod, Finset.prod_const,
    map_sum, PowerSeries.coeff_C_mul_X_pow]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [esymm, map_sum, Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [Finset.powersetCard_eq_filter]
  refine Finset.sum_congr (by ext t; simp [eq_comm]) fun t ht => ?_
  simp only [Finset.mem_filter] at ht
  rw [map_prod]
  simp only [eval_X]
  have hneg : ∀ i, -x i = (-1) * x i := fun i => by ring
  simp_rw [hneg, Finset.prod_mul_distrib, Finset.prod_const, ht.2]

end SymmFun

end GroundTheory.Heights₂.Theta

namespace GroundTheory.Heights₂.Theta

namespace SymmFun

open MvPolynomial Finset

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem sum_esymm_mul_hsymm (x : σ → ℂ) (m : ℕ) :
    ∑ s ∈ Finset.range (m + 1), (-1) ^ s * eval x (esymm σ ℂ s) * eval x (hsymm σ ℂ (m - s)) =
      if m = 0 then 1 else 0 := by
  have h := congrArg (PowerSeries.coeff m) (prod_one_sub_mul_hSeries x)
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (∏ i, (1 - PowerSeries.C (x i) * PowerSeries.X)) *
      PowerSeries.coeff b (hSeries x))] at h
  rw [← h]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [coeff_prod_one_sub, hSeries, PowerSeries.coeff_mk]

end SymmFun

end GroundTheory.Heights₂.Theta
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial Finset

namespace SymmetricSpanHsymm

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem sum_esymm_mul_hsymm_int {k : ℕ} (hk : k ≠ 0) :
    ∑ s ∈ range (k + 1), (-1) ^ s * esymm σ ℤ s * hsymm σ ℤ (k - s) = 0 := by
  apply map_injective (Int.castRingHom ℂ) Int.cast_injective
  apply MvPolynomial.funext
  intro x
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_esymm, map_hsymm, map_zero]
  simp [GroundTheory.Heights₂.Theta.SymmFun.sum_esymm_mul_hsymm x k, hk]

theorem esymm_mem_adjoin (k : ℕ) :
    esymm σ ℤ k ∈ Algebra.adjoin ℤ (Set.range (hsymm σ ℤ)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  set A := Algebra.adjoin ℤ (Set.range (hsymm σ ℤ))
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [esymm_zero]; exact one_mem A
  have h := sum_esymm_mul_hsymm_int (σ := σ) hk.ne'
  rw [sum_range_succ, Nat.sub_self, hsymm_zero, mul_one] at h
  have h2 : ((-1 : MvPolynomial σ ℤ) ^ k) * (-1) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  have he : esymm σ ℤ k =
      -((-1) ^ k * ∑ s ∈ range k, (-1) ^ s * esymm σ ℤ s * hsymm σ ℤ (k - s)) := by
    linear_combination (-1 : MvPolynomial σ ℤ) ^ k * h - esymm σ ℤ k * h2
  have hm1 : ∀ j : ℕ, (-1 : MvPolynomial σ ℤ) ^ j ∈ A := fun j => pow_mem (neg_mem (one_mem A)) j
  rw [he]
  refine neg_mem (mul_mem (hm1 k) (sum_mem fun s hs => mul_mem (mul_mem (hm1 s)
    (ih s (mem_range.mp hs))) (Algebra.subset_adjoin ⟨k - s, rfl⟩)))


omit [Fintype σ] [DecidableEq σ] in
theorem isHomogeneous_prod_map_X (t : Multiset σ) :
    ((t.map (X : σ → MvPolynomial σ ℤ)).prod).IsHomogeneous (Multiset.card t) := by
  induction t using Multiset.induction_on with
  | empty => simpa using isHomogeneous_one σ ℤ
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, add_comm]
    exact (isHomogeneous_X ℤ a).mul ih

theorem isHomogeneous_hsymm_int (a : ℕ) : (hsymm σ ℤ a).IsHomogeneous a := by
  unfold hsymm
  refine IsHomogeneous.sum _ _ _ fun s _ => ?_
  have := isHomogeneous_prod_map_X (σ := σ) s.1
  rwa [s.2] at this

theorem isHomogeneous_prod_map_hsymm (t : Multiset ℕ) :
    ((t.map (hsymm σ ℤ)).prod).IsHomogeneous t.sum := by
  induction t using Multiset.induction_on with
  | empty => simpa using isHomogeneous_one σ ℤ
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    exact (isHomogeneous_hsymm_int a).mul ih

theorem isHomogeneous_hsymmPart {n : ℕ} (μ : n.Partition) : (hsymmPart σ ℤ μ).IsHomogeneous n := by
  have := isHomogeneous_prod_map_hsymm (σ := σ) μ.parts
  rwa [μ.parts_sum] at this

theorem exists_hsymmPart_of_mem_closure {x : MvPolynomial σ ℤ}
    (hx : x ∈ Submonoid.closure (Set.range (hsymm σ ℤ))) :
    ∃ (n : ℕ) (μ : n.Partition), x = hsymmPart σ ℤ μ := by
  induction hx using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact ⟨a, .indiscrete a, (hsymmPart_indiscrete σ ℤ a).symm⟩
  | one => exact ⟨0, .indiscrete 0, (hsymmPart_zero σ ℤ).symm⟩
  | mul y z _ _ hy hz =>
    obtain ⟨n, μ, rfl⟩ := hy
    obtain ⟨n', ν, rfl⟩ := hz
    refine ⟨n + n', ⟨μ.parts + ν.parts, fun {i} hi => ?_, ?_⟩, ?_⟩
    · rcases Multiset.mem_add.mp hi with h | h
      exacts [μ.parts_pos h, ν.parts_pos h]
    · rw [Multiset.sum_add, μ.parts_sum, ν.parts_sum]
    · simp only [hsymmPart, Multiset.map_add (f := _), Multiset.prod_add]

theorem proof : SymmetricSpanHsymm.Statement := by
  intro N m G hG hsym
  set S := Submodule.span ℤ (Set.range fun μ : m.Partition => hsymmPart (Fin N) ℤ μ)
  have hA : G ∈ Algebra.adjoin ℤ (Set.range (hsymm (Fin N) ℤ)) := by
    obtain ⟨p, hp⟩ := esymmAlgHom_fin_surjective ℤ (le_refl N) ⟨G, hsym⟩
    have hG' : G = aeval (fun i : Fin N => esymm (Fin N) ℤ (i + 1)) p := by
      rw [← esymmAlgHom_apply, hp]
    rw [hG']
    clear hp hG'
    induction p using MvPolynomial.induction_on with
    | C r => rw [aeval_C]; exact Subalgebra.algebraMap_mem _ r
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp => rw [map_mul, aeval_X]; exact mul_mem hp (esymm_mem_adjoin _)
  have hspan : G ∈ Submodule.span ℤ
      (Submonoid.closure (Set.range (hsymm (Fin N) ℤ)) : Set (MvPolynomial (Fin N) ℤ)) := by
    rw [← Algebra.adjoin_eq_span, Subalgebra.mem_toSubmodule]
    exact hA
  have hle : Submodule.span ℤ
      (Submonoid.closure (Set.range (hsymm (Fin N) ℤ)) : Set (MvPolynomial (Fin N) ℤ)) ≤
      S.comap (homogeneousComponent m) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨n, μ, rfl⟩ := exists_hsymmPart_of_mem_closure hx
    show homogeneousComponent m (hsymmPart (Fin N) ℤ μ) ∈ S
    rw [homogeneousComponent_of_mem (isHomogeneous_hsymmPart μ)]
    split_ifs with h
    · subst h; exact Submodule.subset_span ⟨μ, rfl⟩
    · exact zero_mem S
  have := hle hspan
  rwa [Submodule.mem_comap, homogeneousComponent_eq_self hG] at this

end SymmetricSpanHsymm

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord IsPull SameGeneric)

def JoinPullbackAlt.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' →
    ∃ EB E'B : ChartBundle O (mseg (joinCoord x z)) N V,
      IsPull O x z E EB ∧ IsPull O x z E' E'B ∧ SameGeneric O (joinCoord x z) EB E'B

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord assocDeg assocVar)

def JoinVerticalDivisorLeft.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (b : K ⊕ K' → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')),
    IsVertDiv O (mcIdeal O (joinCoord x z)) b f g →
    IsVertDiv O (mcIdeal O (joinCoord x (joinCoord z w))) (assocDeg (K₂ := K₂) b)
      (rename (assocVar ι₂) f) (rename (assocVar ι₂) g)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal joinCoord midDeg midVar)

def JoinVerticalDivisorRight.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (b : K ⊕ K' → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')),
    IsVertDiv O (mcIdeal O (joinCoord x z)) b f g →
    IsVertDiv O (mcIdeal O (joinCoord x (joinCoord w z))) (midDeg (K₂ := K₂) b)
      (rename (midVar ι₂) f) (rename (midVar ι₂) g)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

def JoinPointVerticalDivisor.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (b : K → ℤ) (f g : ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O y) b f g →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω))))
      (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) b)
      (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) f)
      (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) g)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

def JoinPointFlagModel.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
      [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle O (segreVec y) N E),
      SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∃ (EB E'B : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))) N E)
      (φ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))
          EB E'B),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω)))) d ∧
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω))) =
          IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O y ∧
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsPull O y (ptCoord (Ω := Ω)) B EB ∧
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsPull O y (ptCoord (Ω := Ω)) B' E'B ∧
        φ.deg = (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x i)) ∧
        φ.deg' = (fun i => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (x' i)) ∧
        φ.f = (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (f i)) ∧
        φ.g = (fun i => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) (g i))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundleForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def FlagBundleSectionForms.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ i : Fin N,
      ∃ (bf bg : Option K → ℕ) (f g : MRing (bundleIdx ι M) F),
        IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
        (fun o => (bf o : ℤ) - bg o) = zetaDeg + liftDeg (b i - a) ∧
        f ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ∧
        g ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ∧
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) f =
          t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
            (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) g

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPointIdealMultiProj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace PointIdealMultiProj

variable {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L]
  {K : Type*} [DecidableEq K] {ι : K → Type*}

def coneWeight (K : Type*) [DecidableEq K] : K → K → ℕ := fun k => Pi.single k 1

theorem coneMap_monomial_isWeightedHomogeneous (z : (Σ k, ι k) → L) (d : (Σ k, ι k) →₀ ℕ) (a : F) :
    IsWeightedHomogeneous (coneWeight K) (pointConeMap F z (monomial d a))
      (Finsupp.weight (blockWeight ι) d) := by
  rw [pointConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, Finsupp.weight_apply, Finsupp.prod,
    Finsupp.sum]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_
  exact ((isWeightedHomogeneous_X (R := L) (coneWeight K) p.1).C_mul (z p)).pow (d p)

theorem coneMap_component (z : (Σ k, ι k) → L) (b : K → ℕ) (f : MRing ι F) :
    weightedHomogeneousComponent (coneWeight K) b (pointConeMap F z f) =
      pointConeMap F z (weightedHomogeneousComponent (blockWeight ι) b f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial d a =>
    have h1 := coneMap_monomial_isWeightedHomogeneous (K := K) (F := F) z d a
    have h2 : IsWeightedHomogeneous (blockWeight ι) (monomial d a : MRing ι F)
        (Finsupp.weight (blockWeight ι) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases h : b = Finsupp.weight (blockWeight ι) d
    · subst h
      rw [h1.weightedHomogeneousComponent_same, h2.weightedHomogeneousComponent_same]
    · rw [h1.weightedHomogeneousComponent_ne _ h, h2.weightedHomogeneousComponent_ne _ h, map_zero]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]

theorem proof : PointIdealMultiProj.Statement := by
  intro F _ L _ _ K _ ι z hz
  refine ⟨?_, ?_, ?_⟩
  · exact RingHom.ker_isPrime _
  · intro f hf b
    rw [pointIdeal, RingHom.mem_ker] at hf ⊢
    have := coneMap_component (F := F) z b f
    rw [show (pointConeMap F z) f = 0 from hf, map_zero] at this
    exact this.symm
  · intro k
    obtain ⟨i, hi⟩ := hz k
    refine ⟨i, ?_⟩
    rw [pointIdeal, RingHom.mem_ker]
    change pointConeMap F z (X ⟨k, i⟩) ≠ 0
    rw [pointConeMap, aeval_X]
    exact mul_ne_zero (by simpa using hi) (X_ne_zero _)

end PointIdealMultiProj

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreClosureModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Objects

variable {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M M' : ℕ} {E : Type*} [AddCommGroup E]
  [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]

def pairProjCoord (y : (Σ k, ι k) → Ω) (e : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) :
    (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ
  | ⟨none, l⟩ => ∑ i, t i * algebraMap Ω Φ (φ' l (e i))
  | ⟨some o, j⟩ => projCoord y e φ t ⟨o, j⟩

def zetaFirst (a : K → ℤ) : Option (Option K) → ℤ
  | none => 0
  | some none => 1
  | some (some k) => -a k

def zetaSecond (a : K → ℤ) : Option (Option K) → ℤ
  | none => 1
  | some none => 0
  | some (some k) => -a k

def liftPairDeg (L : K → ℤ) : Option (Option K) → ℤ
  | some (some k) => L k
  | _ => 0

def liftPairForm {R : Type*} [CommRing R] (M M' : ℕ) (f : MRing ι R) :
    MRing (bundleIdx (bundleIdx ι M) M') R :=
  rename (fun p : Σ k, ι k => (⟨some (some p.1), p.2⟩ : Σ o, bundleIdx (bundleIdx ι M) M' o)) f

end Objects

def zetaPowTimes (n m : ℕ) (R : MvPolynomial (Fin n) ℤ) : MvPolynomial (Fin (1 + n)) ℤ :=
  X (Fin.castAdd n 0) ^ m * rename (Fin.natAdd 1) R

def GenericProjClosureModel.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∃ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ ∧ IsTwistedDualGens y B' a₀' φ' ∧
      IsModelOver (pointIdeal O (pairProjCoord y e φ φ' t)) (d + (N - 1)) ∧
      ∃ f₀ g₀ : MRing (bundleIdx (bundleIdx ι M) M') O,
        IsVerticalDivisor (pointIdeal O (pairProjCoord y e φ φ' t)) ϖ
          (zetaFirst a₀ - zetaSecond a₀') f₀ g₀ ∧
        aeval (pairProjCoord y e φ φ' t) f₀ = aeval (pairProjCoord y e φ φ' t) g₀

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVerticalComponentFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem VerticalComponentFibre.proof (h : FibreVarieties.Statement.{0}) :
    VerticalComponentFibre.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP f b hf hfP W hW hrel hϖW
  have hWp : W.IsPrime := hW.1.1
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hPW : P ≤ W := le_sup_left.trans hW.1.2
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro hmem
    have : ϖ ∈ P.comap (C : O →+* MRing ι O) := hmem
    rw [hP.noTorsion, Ideal.mem_bot] at this
    exact hϖ.ne_zero this

  have hmin : W ∈ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}).minimalPrimes := by
    refine ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hϖW)⟩, ?_⟩
    rintro Q ⟨hQ, hQle⟩ hQW
    by_contra hWQ
    have hlt : Q < W := lt_of_le_of_ne hQW (fun e => hWQ (e ▸ le_rfl))
    have hPQ : P ≤ Q := le_sup_left.trans hQle
    have hϖQ : (C ϖ : MRing ι O) ∈ Q := hQle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    let π := Ideal.Quotient.mk P
    have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
    have : (W.map π).IsPrime :=
      Ideal.map_isPrime_of_surjective hsurj (by rw [Ideal.mk_ker]; exact hPW)
    have : (Q.map π).IsPrime :=
      Ideal.map_isPrime_of_surjective hsurj (by rw [Ideal.mk_ker]; exact hPQ)
    have hle1 : (W.map π).height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
    have hlt' : Q.map π < W.map π := by
      refine (Ideal.map_mono hlt.le).lt_of_not_ge fun e => hlt.not_ge ?_
      have := Ideal.comap_mono (f := π) e
      rwa [Ideal.comap_map_of_surjective' π hsurj, Ideal.comap_map_of_surjective' π hsurj,
        Ideal.mk_ker, sup_eq_left.mpr hPW, sup_eq_left.mpr hPQ] at this
    have : (W.map π).FiniteHeight := ⟨Or.inr (hle1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
    have h0 := (Ideal.height_strict_mono_of_isPrime_of_isPrime hlt').trans_le hle1
    rw [Order.lt_one_iff, Ideal.height_eq_zero_iff] at h0
    have hbot : Q.map π ≤ ⊥ := h0.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le
    have : π (C ϖ) ∈ (⊥ : Ideal (MRing ι O ⧸ P)) := hbot (Ideal.mem_map_of_mem π hϖQ)
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hϖP this

  have hdiv : divCycle P (C ϖ) W ≠ 0 := by
    unfold divCycle
    rw [dite_eq_left ⟨hmin, hrel⟩]
    have hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
        ((P ⊔ Ideal.span {(C ϖ : MRing ι O)}).map
          (algebraMap (MRing ι O) (Localization.AtPrime W))).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W),
        Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
      exact hmin
    have hne := ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.length_quot_ne_top_of_mem_minimalPrimes _ hm
    have : Nontrivial (Localization.AtPrime W ⧸
        (P ⊔ Ideal.span {(C ϖ : MRing ι O)}).map
          (algebraMap (MRing ι O) (Localization.AtPrime W))) :=
      Ideal.Quotient.nontrivial_iff.mpr
        (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm.1.2)
    have hpos := Module.length_pos (R := Localization.AtPrime W)
      (M := Localization.AtPrime W ⧸
        (P ⊔ Ideal.span {(C ϖ : MRing ι O)}).map (algebraMap (MRing ι O) (Localization.AtPrime W)))
    rw [multAt, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_length_locQuot]
    exact_mod_cast (ENat.toNat_pos hpos.ne' hne).ne'
  exact (h O ϖ hϖ K ι P d hP).2 W hdiv

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsJoinPointIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

def JoinPointIdeal.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (Ω : Type) [Field Ω] [Algebra R Ω] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal R (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω))) =
      (pointIdeal R y).map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx))

end GroundTheory.Heights₂.Heights.NumbersDVR
end
