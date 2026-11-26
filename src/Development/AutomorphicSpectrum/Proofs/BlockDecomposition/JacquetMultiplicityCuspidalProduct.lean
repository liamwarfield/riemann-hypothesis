module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubquotientCuspidalPermutation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductJacquetShuffleCount
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBlockMatrixTwoByTwoFinEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteVectorsDense
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWittIsotropicToE0

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityOfSizeMatrix
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityOfSizeMatrix
noncomputable section

namespace GlobalTheory.CompanionTheory.CuspCell

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead GlobalTheory.DiagCell

set_option synthInstance.maxHeartbeats 400000

theorem exists_eq_singleton_of_sum {ι A : Type*} [Fintype ι] [DecidableEq ι] {a : A} {t : ι → Multiset A}
    (h : ({a} : Multiset A) = ∑ j, t j) : ∃ j₀, t j₀ = {a} ∧ ∀ j, j ≠ j₀ → t j = 0 := by
  have hc : ∑ j, Multiset.card (t j) = 1 := by
    have := congrArg Multiset.card h
    rw [Multiset.card_sum] at this
    simpa using this.symm
  obtain ⟨j₀, -, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hc.symm ▸ one_ne_zero)
  have hz : ∀ j, j ≠ j₀ → t j = 0 := fun j hj => by
    have h2 := Finset.add_le_sum (s := Finset.univ) (f := fun j => Multiset.card (t j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j₀) (Finset.mem_univ j) (Ne.symm hj)
    simp only [hc] at h2
    exact Multiset.card_eq_zero.1 (by omega)
  refine ⟨j₀, ?_, hz⟩
  rw [h, Finset.sum_eq_single j₀ (fun j _ hj => hz j hj) (by simp)]

theorem exists_equiv_of_sums {l c : ℕ} {A : Type*} {x : Fin l → A} {y : Fin c → A} {t : Fin l → Fin c → Multiset A}
    (hr : ∀ i, ({x i} : Multiset A) = ∑ j, t i j) (hc : ∀ j, ({y j} : Multiset A) = ∑ i, t i j) :
    ∃ e : Fin c ≃ Fin l, (∀ a, y a = x (e a)) ∧ ∀ i j, t i j = if e j = i then {x i} else 0 := by
  choose r hr1 hr0 using fun i => exists_eq_singleton_of_sum (hr i)
  choose e he1 he0 using fun j => exists_eq_singleton_of_sum (hc j)
  have hne : ∀ {a : A}, ({a} : Multiset A) ≠ 0 := Multiset.singleton_ne_zero _
  have h1 : ∀ i, e (r i) = i := fun i => by
    by_contra hi
    exact hne ((hr1 i).symm.trans (he0 (r i) i (Ne.symm hi)))
  have h2 : ∀ j, r (e j) = j := fun j => by
    by_contra hj
    exact hne ((he1 j).symm.trans (hr0 (e j) j (Ne.symm hj)))
  refine ⟨⟨e, r, h2, h1⟩, fun a => ?_, fun i j => ?_⟩
  · have h3 := hr1 (e a)
    rw [h2 a, he1 a] at h3
    exact Multiset.singleton_inj.1 h3
  · by_cases h : e j = i
    · subst h
      have h3 := hr1 (e j)
      rw [h2 j] at h3
      simpa using h3
    · simpa [h] using he0 j i (Ne.symm h)

theorem exists_equiv_of_jhMult_cell_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {l c : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k))
    (hxc : ∀ a, (x a).IsCusp) (hyc : ∀ a, (y a).IsCusp)
    (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1)
    (h0 : jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) ≠ 0) :
    ∃ e : Fin c ≃ Fin l, (∀ a, y a = x (e a)) ∧ ∀ i j, b.1 i j = if e j = i then (x i).1 else 0 := by
  have hG := GlobalTheory.CompanionTheory.GeoLink.geometricLemma
  have hBZ := GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
  have hτ : (piTensor fun j => (y j).rep).IsIrreducible := GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => (y j).2.rep
  have hτs : IsSmooth (piTensor fun j => (y j).rep) := isSmooth_piTensor fun j => (y j).2.rep.smooth
  obtain ⟨s, hrow, hcol⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_of_cell (hG k).2 f g (fun i => (x i).2.rep.smooth)
    (fun i => (x i).2.rep.hasFiniteLength) hτ hτs h0
  have hR : ∀ i, ∃ t : Fin c → Multiset (IrrGL (k := k)), (∀ j, HasSupport (s i j).ρ (t j)) ∧ {x i} = ∑ j, t j :=
    fun i => GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_sum_of_jac hG hBZ (hasSupport_self (hxc i)) (f i)
      (GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => s i j) (hrow i)
      (fun j => s i j) (fun j => GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle _ (fun j => (s i j).irr) j)
  choose t ht hAt using hR
  have hC : ∀ j, HasSupport (y j).rep (∑ i, t i j) := by
    intro j
    have hd : ∑ i, b.1 i j = (y j).1 := by simpa using Fintype.card_congr (g j)
    have hy := GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (y j).rep) (fun j => (y j).2.rep.irr) j
    have h1 := isSubquotient_factor (fun j => multiProd (g j) fun i => (s i j).ρ) j (y j).2.rep.irr
      (hy.trans (isSubquotient_comp hcol _))
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (g j) (stdBlocks (fun i => b.1 i j) hd) _).1
      (piTensor fun i => (s i j).ρ)
    let ψ := φ.trans (prodIrrEquiv hd (fun i => (s i j).ρ) (fun i => (s i j).smooth) fun i => (s i j).irr)
    exact GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr
      (y := fun i => IrrGL.of (s i j).ρ (s i j).smooth (s i j).irr)
      (fun i => (ht i j).of_equiv (IrrGL.equivOf _ _ _)) (y j).2.rep.irr
      (h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
  have hU : ∀ j, ({y j} : Multiset (IrrGL (k := k))) = ∑ i, t i j :=
    fun j => GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ (hasSupport_self (hyc j)) (hC j)
  obtain ⟨e, he, het⟩ := exists_equiv_of_sums hAt hU
  refine ⟨e, he, fun i j => ?_⟩
  have hd := (ht i j).sum_fst
  rw [het i j] at hd
  split_ifs at hd ⊢ <;> simpa using hd.symm

end GlobalTheory.CompanionTheory.CuspCell
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityOfSizeMatrixStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_cell_multiplicity_of_size_matrix : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {l c : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k)), (∀ a, (x a).IsCusp) → (∀ a, (y a).IsCusp) → ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1), jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) ≠ 0 → ∃ e : Fin c ≃ Fin l, (∀ a, y a = x (e a)) ∧ ∀ i j, b.1 i j = if e j = i then (x i).1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.CuspCell.exists_equiv_of_jhMult_cell_ne_zero | exact GlobalTheory.CompanionTheory.CuspCell.exists_equiv_of_jhMult_cell_ne_zero | (intros; apply GlobalTheory.CompanionTheory.CuspCell.exists_equiv_of_jhMult_cell_ne_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProduct
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspJm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsPermCell {l c : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k))
    (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) : Prop :=
  ∃ e : Fin c ≃ Fin l, (∀ a, y a = x (e a)) ∧ ∀ i j, b.1 i j = if e j = i then (x i).1 else 0

def permMatrix {l c : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k)) (e : Fin c ≃ Fin l)
    (h : ∀ a, y a = x (e a)) : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1) :=
  ⟨fun i j => if e j = i then (x i).1 else 0, fun i => by
    rw [Finset.sum_eq_single (e.symm i) (fun j _ hj => if_neg fun h' => hj (by rw [← h', e.symm_apply_apply]))
      (by simp)]
    simp, fun j => by
    rw [Finset.sum_ite_eq]
    simp [h j]⟩


set_option maxHeartbeats 2000000 in
theorem exists_choice (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l c : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k)) :
    ∃ (f : ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1)
      (g : ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1),
      ∀ b, IsPermCell x y b →
        jhMult (piTensor fun j => (y j).rep) (cellFunctor (f b) (g b) (piTensor fun i => (x i).rep)) = 1 := by
  classical
  have key : ∀ b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1), IsPermCell x y b → ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1)
      (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1),
      jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) = 1 := by
    rintro b ⟨e, he, hb⟩
    exact GlobalTheory.T.size_matrix_permutation_equivs_exist hA x y e he b hb
  have key' : ∀ b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1), ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1),
      IsPermCell x y b → jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) = 1 := by
    intro b
    by_cases h : IsPermCell x y b
    · obtain ⟨f, g, hfg⟩ := key b h
      exact ⟨f, g, fun _ => hfg⟩
    · exact ⟨b.nonempty_rows.some, b.nonempty_cols.some, fun h' => absurd h' h⟩
  choose f g hfg using key'
  exact ⟨f, g, hfg⟩

theorem card_permCell {l c : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k)) (hxc : ∀ a, (x a).IsCusp)
    [Fintype (SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1))] [DecidablePred (IsPermCell x y)] :
    (Finset.univ.filter (IsPermCell x y)).card = Set.ncard {e : Fin c ≃ Fin l | ∀ a, y a = x (e a)} := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  symm
  refine Finset.card_bij (fun e he => permMatrix x y e (Set.mem_toFinset.1 he)) ?_ ?_ ?_
  · intro e he
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, e, Set.mem_toFinset.1 he, fun i j => rfl⟩
  · intro e he e' he' H
    refine Equiv.ext fun j => ?_
    have h2 := congrArg (fun b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1) => b.1 (e j) j) H
    simp only [permMatrix, if_true] at h2
    by_contra hne
    rw [if_neg (Ne.symm hne)] at h2
    exact (hxc (e j)).1.ne' h2
  · intro b hb
    obtain ⟨e, he, hb⟩ := (Finset.mem_filter.1 hb).2
    exact ⟨e, Set.mem_toFinset.2 he, Subtype.ext (funext fun i => funext fun j => (hb i j).symm)⟩


set_option maxHeartbeats 1000000 in
theorem main (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l c N : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k))
    (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N) (hxc : ∀ a, (x a).IsCusp) (hyc : ∀ a, (y a).IsCusp) :
    jm y hy (prodIrr x hx) = (Set.ncard {e : Fin c ≃ Fin l | ∀ a, y a = x (e a)} : ℕ∞) := by
  classical
  haveI : Fintype (SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) := Fintype.ofFinite _
  obtain ⟨f, g, hfg⟩ := exists_choice hA x y
  have hτ : (piTensor fun j => (y j).rep).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k _ _ fun j => (y j).2.rep
  have h1 := (GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).1.jhMult_eq (stdBlocks (fun a => (x a).1) hx)
    (stdBlocks (fun a => (y a).1) hy) (isSmooth_piTensor fun i => (x i).2.rep.smooth) f g hτ
  have hterm : ∀ b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1), jhMult (piTensor fun j => (y j).rep) (cellFunctor (f b) (g b) (piTensor fun i => (x i).rep)) =
      if IsPermCell x y b then 1 else 0 := by
    intro b
    split_ifs with h
    · exact hfg b h
    · by_contra hne
      exact h (GlobalTheory.T.cuspidal_cell_multiplicity_of_size_matrix x y hxc hyc b (f b) (g b) hne)
  have h2 : jm y hy (prodIrr x hx) = jhMult (piTensor fun j => (y j).rep)
      (GlobalTheory.SmGL.jac (stdBlocks (fun a => (y a).1) hy) (parInd (stdBlocks (fun a => (x a).1) hx)
        (piTensor fun i => (x i).rep))) := rfl
  rw [h2, h1, Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_boole, card_permCell x y hxc]

end GlobalTheory.CompanionTheory.CuspJm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityCuspidalProductStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_cuspidal_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l c N : ℕ} (x : Fin l → IrrGL (k := k)) (y : Fin c → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N) (hxc : ∀ a, (x a).IsCusp) (hyc : ∀ a, (y a).IsCusp), jm y hy (prodIrr x hx) = (Set.ncard {e : Fin c ≃ Fin l | ∀ a, y a = x (e a)} : ℕ∞) := by
  first | exact @GlobalTheory.CompanionTheory.CuspJm.main | exact GlobalTheory.CompanionTheory.CuspJm.main | (intros; apply GlobalTheory.CompanionTheory.CuspJm.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffle
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffle
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspShuffle

open Zc.Comb

variable {α β : Type*}

theorem interleave_filter (f : β → α) (q : β → Bool) (P : List β) :
    Interleave ((P.filter q).map f) ((P.filter fun p => !q p).map f) (P.map f) := by
  induction P with
  | nil => exact Zc.Comb.Interleave.nil
  | cons p P ih =>
    cases hq : q p with
    | true =>
      simp only [List.filter_cons, hq, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        List.map_cons]
      exact Zc.Comb.Interleave.left ih
    | false =>
      simp only [List.filter_cons, hq, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
        List.map_cons]
      exact Zc.Comb.Interleave.right ih

theorem shuffle_range (f : β → α) (c : β → ℕ) (n : ℕ) : ∀ (s : ℕ) (P : List β),
    (∀ p ∈ P, s ≤ c p ∧ c p < s + n) →
      Shuffle ((List.range' s n).map fun i => (P.filter fun p => c p = i).map f) (P.map f) := by
  induction n with
  | zero =>
    intro s P hP
    have hnil : P = [] := List.eq_nil_iff_forall_not_mem.mpr fun p hp => by
      have := hP p hp
      omega
    subst hnil
    exact Zc.Comb.Shuffle.nil
  | succ n ih =>
    intro s P hP
    simp only [List.range'_succ, List.map_cons]
    refine Zc.Comb.Shuffle.cons (v := (P.filter fun p => !decide (c p = s)).map f) ?_
      (GlobalTheory.CompanionTheory.CuspShuffle.interleave_filter f (fun p => decide (c p = s)) P)
    have h := ih (s + 1) (P.filter fun p => !decide (c p = s)) (by
      intro p hp
      rw [List.mem_filter] at hp
      have h1 := hP p hp.1
      have hne : c p ≠ s := by simpa using hp.2
      omega)
    convert h using 1
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range'_1] at hi
    rw [List.filter_filter]
    congr 1
    apply List.filter_congr
    intro p _
    by_cases hc : c p = i
    · have his : i ≠ s := by omega
      simp [hc, his]
    · simp [hc]

theorem shuffle_of_colouring {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (D : Fin h → List α)
    (hD : ∀ i, Zc.Cos.sub W c i = D i) : Shuffle (List.ofFn D) W := by
  have key := GlobalTheory.CompanionTheory.CuspShuffle.shuffle_range W.get (fun p => (c p : ℕ)) h 0 (List.finRange W.length)
    (fun p _ => ⟨Nat.zero_le _, by simpa using (c p).isLt⟩)
  convert key using 1
  · apply List.ext_getElem
    · simp
    · intro i h1 h2
      rw [List.getElem_ofFn, List.getElem_map, List.getElem_range', ← hD]
      unfold Zc.Cos.sub
      congr 1
      apply List.filter_congr
      intro p _
      simp [Fin.ext_iff]
  · apply List.ext_getElem <;> simp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem decWord_eq_decW (Δ : Segment k) : Zc.Cos.decWord Δ = decW Δ := by
  unfold Zc.Cos.decWord Zc.M.decW
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_reverse, List.getElem_ofFn, List.getElem_ofFn]
    congr 1
    ext
    simp only [Fin.val_rev, List.length_ofFn]
    omega

theorem inShW_of_wd {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hL : LSegJacquet k) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hd : ∑ a, (x a).1 = N) (Δ : Fin h → Segment k) (hΔ : ∀ i, IsLSeg (Δ i) (x i).rep) (w : List (IrrGL (k := k)))
    (hc : ∀ c ∈ w, c.IsCusp) (hw : Wd (prodIrr x hd) w) : InShW (Finset.univ.val.map Δ) w := by
  obtain ⟨hsum, hne⟩ := hw
  have hmult := GlobalTheory.T.segment_product_jacquet_shuffle_count hA hL Δ x hd hΔ w hc
  have hpos : Zc.Cos.jmL w (GlobalTheory.LocGL.prodIrr x hd) ≠ 0 := by
    unfold Zc.Cos.jmL
    rw [dite_eq_left hsum]
    exact hne
  rw [hmult] at hpos
  have hcard : Zc.Cos.shuffleCount w (fun i => Zc.Cos.decWord (Δ i)) ≠ 0 := by exact_mod_cast hpos
  unfold Zc.Cos.shuffleCount at hcard
  obtain ⟨col, hcol⟩ := Finset.card_ne_zero.mp hcard
  have hcol' : ∀ i, Zc.Cos.sub w col i = Zc.Cos.decWord (Δ i) := by simpa using hcol
  unfold Zc.M.InShW
  refine ⟨List.ofFn Δ, ?_, ?_⟩
  · rw [Fin.univ_val_map]
  · rw [List.map_ofFn]
    have e : (Zc.M.decW ∘ Δ) = fun i => Zc.Cos.decWord (Δ i) :=
      funext fun i => (GlobalTheory.CompanionTheory.CuspShuffle.decWord_eq_decW (Δ i)).symm
    rw [e]
    exact GlobalTheory.CompanionTheory.CuspShuffle.shuffle_of_colouring w col _ hcol'

end GlobalTheory.CompanionTheory.CuspShuffle

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffleStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_product_word_in_shuffle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSegJacquet k → ∀ {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (Δ : Fin h → Segment k), (∀ i, IsLSeg (Δ i) (x i).rep) → ∀ w : List (IrrGL (k := k)), (∀ c ∈ w, c.IsCusp) → Wd (prodIrr x hd) w → InShW (Finset.univ.val.map Δ) w := by
  first | exact @GlobalTheory.CompanionTheory.CuspShuffle.inShW_of_wd | exact GlobalTheory.CompanionTheory.CuspShuffle.inShW_of_wd | (intros; apply GlobalTheory.CompanionTheory.CuspShuffle.inShW_of_wd <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanTransport
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

variable {D : D7} {n ρ p : ℕ}

theorem adj_bl (hn : ρ + p = n) (a : Mx D ρ ρ) (b : Mx D ρ p) (c : Mx D p ρ) (d : Mx D p p) :
    adj (bl hn a b c d : Mx D n n) = bl hn (adj a) (adj c) (adj b) (adj d) := by
  ext i j
  simp only [adj, bl, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases h1 : (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
    rcases h2 : (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;> rfl

def bT (hn : ρ + p = n) (z : hermA D ρ) (x : Mx D ρ p) (y : hermA D p) : hermA D n :=
  ⟨bl hn z.1 x (adj x) y.1, by
    show adj (bl hn z.1 x (adj x) y.1 : Mx D n n) = _
    rw [adj_bl, adj_adj]
    have hz : adj z.1 = z.1 := z.2
    have hy : adj y.1 = y.1 := y.2
    rw [hz, hy]⟩

def dsum (hn : ρ + p = n) (b₀ : HermE D ρ) (β' : HermE D p) : HermE D n :=
  ⟨bl hn b₀.1 0 0 β'.1, by
    have h1 := b₀.2
    have h2 := β'.2
    refine Matrix.ext fun i j => ?_
    simp only [bl, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
    rcases h1' : (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
      rcases h2' : (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, map_zero]
    · exact congrFun (congrFun h1 i') j'
    · exact congrFun (congrFun h2 i') j'⟩

def cg (a : GL (Fin n) D.host.E) (β : HermE D n) : HermE D n :=
  ⟨(a.1.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose * β.1 * a.1, by
    have h : ∀ M : Matrix (Fin n) (Fin n) D.host.E, (M.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = Mᴴ := fun _ => rfl
    have hb : β.1ᴴ = β.1 := β.2
    rw [h, h, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hb, Matrix.mul_assoc]⟩

def IsPer (Φ : hermA D n → ℂ) : Prop := ∀ γ ∈ ratHerm D n, ∀ x, Φ (γ + x) = Φ x

def chn (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b : hermA D n) : ℂ :=
  ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n)))

def pm (hn : ρ + p = n) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (Φ : hermA D n → ℂ) (y : hermA D p) : ℂ :=
  ∫ x in m.𝓕, ∫ z in m.𝓖, Φ (bT hn z x y) * conj (chz ψ b₀ z) ∂m.lz ∂m.μ

end GlobalTheory.CompanionTheory.PcFc

namespace GlobalTheory.CompanionTheory.PcFc

section Transport
variable {A B : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [T2Space A] [LocallyCompactSpace A]
  [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [T2Space B] [LocallyCompactSpace B]
  [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

theorem mean_transport (Γ : AddSubgroup A) (Δ : AddSubgroup B) [Countable Γ] [Countable Δ] (T : A ≃ₜ+ B)
    (hT : ∀ a, T a ∈ Δ ↔ a ∈ Γ) (μ : Measure A) (ν : Measure B) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    {s : Set A} {t : Set B} (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) (hs1 : μ s = 1) (ht1 : ν t = 1)
    (f : B → ℂ) (hf : ∀ γ ∈ Δ, ∀ x, f (γ + x) = f x) :
    ∫ a in s, f (T a) ∂μ = ∫ b in t, f b ∂ν := by
  have hm : Measurable T := T.continuous.measurable
  have hAC : (μ.map T).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map μ T
  have hAC2 : (ν.map T.symm).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν T.symm
  have hsm : Measure.QuasiMeasurePreserving (T.symm.toAddEquiv.toEquiv) ν μ :=
    ⟨T.symm.continuous.measurable.aemeasurable, Measure.absolutelyContinuous_isAddHaarMeasure _ _⟩
  let eΓ : Δ ≃ Γ :=
    { toFun := fun d => ⟨T.symm d.1, (hT _).1 (by simpa using d.2)⟩
      invFun := fun c => ⟨T c.1, (hT _).2 c.2⟩
      left_inv := fun d => Subtype.ext (by simp)
      right_inv := fun c => Subtype.ext (by simp) }
  have hFD : IsAddFundamentalDomain Δ (T.toAddEquiv.toEquiv '' s) ν :=
    hs.image_of_equiv T.toAddEquiv.toEquiv hsm eΓ (fun g x => by
      show T (T.symm g.1 + x) = g.1 + T x
      simp)
  have h1 : ν (T.toAddEquiv.toEquiv '' s) = 1 := by rw [hFD.measure_eq ht, ht1]
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have h2 : μ.map T (T.toAddEquiv.toEquiv '' s) = 1 := by
    rw [hemb.map_apply, show T ⁻¹' (T.toAddEquiv.toEquiv '' s) = s from Set.preimage_image_eq _ T.injective, hs1]
  have h3 : μ.map T = ν := by
    have h4 := Measure.isAddLeftInvariant_eq_smul (μ.map T) ν
    rw [h4] at h2
    have hc : Measure.addHaarScalarFactor (μ.map T) ν = 1 := by
      rw [Measure.smul_apply, h1, ENNReal.smul_def, smul_eq_mul, mul_one] at h2
      exact_mod_cast h2
    rw [h4, hc, one_smul]
  have h5 : ∫ a in s, f (T a) ∂μ = ∫ b in T.toAddEquiv.toEquiv '' s, f b ∂ν := by
    rw [← h3, hemb.setIntegral_map, show T ⁻¹' (T.toAddEquiv.toEquiv '' s) = s from Set.preimage_image_eq _ T.injective]
  rw [h5]
  exact hFD.setIntegral_eq ht (fun g x => hf g.1 g.2 x)
end Transport
end GlobalTheory.CompanionTheory.PcFc
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompact
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp

def GoodPsi (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D) : Prop :=
  (∀ a ∈ v.adicCompletionIntegers D.host.F, psiV D.host.F ψ v a = 1) ∧
    ∀ ϖ : v.adicCompletionIntegers D.host.F, Irreducible ϖ →
      ∃ b : v.adicCompletionIntegers D.host.F,
        psiV D.host.F ψ v ((b : Fv D.host.F v) / (ϖ : Fv D.host.F v)) ≠ 1

def GoodChi (D : D7) (χ : (AE D)ˣ →* Circle) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : Prop :=
  ∀ a : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ,
    ‖splitProj τ (a : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ =
      ‖splitProj (τ.comp D.sp.cm.sig) (a : Fv D.host.F v ⊗[D.host.F] D.host.E)‖ →
    χ (ideleAt D.host.F D.host.E v a) = 1

abbrev sphV (D : D7) (n : ℕ) (v : Pl D) (z : ℂ) : GLoc D.sp.cm.sig (Jst D n) v → ℂ :=
  GlobalTheory.LocIntw.sphUp (Fv D.host.F v) D.sp.cm.sig (Jst D n) (absEv D.host.F D.host.E v)
    (GlobalTheory.LocIntw.KUpFin D.sp.cm.sig (Jst D n) v) z

def GoodPlacesOutsideFiniteSet : Prop :=
  ∀ (D : D7) (r : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ →
    ResEta D χ r → ∀ S : Finset (Pl D), ∃ v ∉ S, GoodPsi D ψ v ∧ ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v, GoodChi D χ v τ

def SplitPlaceRankCutEigenvalue : Prop :=
  ∀ (D : D7) (n r t : ℕ), r + t = n → 1 ≤ r → ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ →
    ∀ nb : hermA D n → G D n, IsNMap nb → ∀ v : Pl D, GoodPsi D ψ v → ∀ _ : D.host.E →ₐ[D.host.F] Fv D.host.F v,
    ∃ (C : Cut D n v) (c : ℂ → ℂ), C.Kills ψ r ∧ Differentiable ℂ c ∧ c ((t : ℂ) / 2) ≠ 0 ∧
      ∀ νv : Measure (KAt D n v), νv.IsHaarMeasure → IsProbabilityMeasure νv → ∀ z : ℂ,
        ∫ k : KAt D n v, ∑ x ∈ C.s, C.co x * sphV D n v z (proj D.sp.cm.sig (Jst D n) v ((k : G D n) * nb x)) ∂νv = c z

def SectionEigenfunctionMaximalCompact : Prop :=
  ∀ (D : D7) (n : ℕ) (χ : (AE D)ˣ →* Circle) (nb : hermA D n → G D n), IsNMap nb → ∀ (v : Pl D)
    (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), GoodChi D χ v τ → ∀ (C : Cut D n v) (νv : Measure (KAt D n v)),
    νv.IsHaarMeasure → ∀ z c : ℂ,
    (∫ k : KAt D n v, ∑ x ∈ C.s, C.co x * sphV D n v z (proj D.sp.cm.sig (Jst D n) v ((k : G D n) * nb x)) ∂νv = c) →
    ∀ f : G D n → ℂ, IsLaw χ z f → (∀ k ∈ KAt D n v, ∀ g, f (g * k) = f g) → ∀ g : G D n,
      ∫ k : KAt D n v, cutR nb C f (g * k) ∂νv = c * f g

end GlobalTheory.CompanionTheory.Jp

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemL2OfBoundedContinuousInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalKerSubId
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CompactFix

theorem finiteDimensional_ker_sub_id {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : X →L[ℂ] X) (hT : IsCompactOperator T) :
    FiniteDimensional ℂ (LinearMap.ker ((T : X →ₗ[ℂ] X) - LinearMap.id)) := by
  set K : Submodule ℂ X := LinearMap.ker ((T : X →ₗ[ℂ] X) - LinearMap.id) with hK
  have hfix : ∀ x ∈ K, T x = x := by
    intro x hx
    have : (T : X →ₗ[ℂ] X) x - x = 0 := by simpa [hK] using hx
    simpa [sub_eq_zero] using this
  have hclosed : IsClosed (K : Set X) := by
    have : (K : Set X) = {x | T x = x} := by
      ext x
      constructor
      · exact hfix x
      · intro h
        have h' : T x = x := h
        simp [hK, h']
    rw [this]
    exact isClosed_eq T.continuous continuous_id
  obtain ⟨C, hC, hCsub⟩ := hT
  have hpre : (T ⁻¹' C) ∈ nhds (0 : X) := hCsub
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hpre
  have hcomp : IsCompact (Metric.closedBall (0 : K) r) := by
    have hemb : Topology.IsClosedEmbedding (Subtype.val : K → X) := hclosed.isClosedEmbedding_subtypeVal
    rw [hemb.isCompact_iff]
    refine hC.of_isClosed_subset ?_ ?_
    · have : (Subtype.val '' Metric.closedBall (0 : K) r) = (K : Set X) ∩ Metric.closedBall 0 r := by
        ext x
        simp [Metric.mem_closedBall, dist_eq_norm, and_comm]
      rw [this]
      exact hclosed.inter Metric.isClosed_closedBall
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : (x : X) ∈ Metric.closedBall (0 : X) r := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      have := hball hx'
      simpa [hfix x x.2] using this
  exact FiniteDimensional.of_isCompact_closedBall ℂ hr hcomp

end GlobalTheory.CompanionTheory.CompactFix
end

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC PositivityTheory.Affgl

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspInvariant

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem memL2_of_bounded_continuous_invariant (μ : Measure (GA E a)) [μ.IsHaarMeasure] {φ : GA E a → ℂ} (hc : Continuous φ)
    (hl : LeftInv (latticeGL E a) φ) {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) : MemL2Quotient (latticeGL E a) μ φ := by
  have hfin := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  refine ⟨hl, MemLp.of_bound ?_ C (.of_forall fun q => hC _)⟩
  refine aestronglyMeasurable_quotMeasure_iff_lift.2 ?_
  rw [hl.lift_descend]
  exact hc.aestronglyMeasurable

theorem repOp_toL2cusp (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {f φ : GA E a → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) (h : MemL2Quotient (latticeGL E a) μ φ) (hm : φ ∈ cuspCont E a)
    (hφ : ∀ x, convR μ f φ x = φ x) :
    repOp (Rcusp μ) μ f ⟨h.toL2, toL2_mem_cuspidal h hm⟩ = ⟨h.toL2, toL2_mem_cuspidal h hm⟩ := by
  have hi : Integrable f μ := hf.integrable_of_hasCompactSupport hs
  have hT : IsRepOp (R (latticeGL E a) μ) μ f (Rop (latticeGL E a) μ f) := isRepOp_Rop hi
  refine Subtype.ext (((isSubrep_L2cusp μ).coe_repOp_rep hT).2 _ |>.trans ?_)
  refine l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ?_
  have e := h.lift_toL2_ae_eq
  refine (GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR _ _ μ f hi h.toL2).2.trans
    (Filter.EventuallyEq.trans (.of_forall fun x => ?_) e.symm)
  rw [← hφ x]
  refine integral_congr_ae ?_
  filter_upwards [(measurePreserving_mul_left μ x).quasiMeasurePreserving.ae e] with y hy
  rw [hy]

theorem finiteDimensional_span (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {f : GA E a → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) (S : Set (GA E a → ℂ))
    (hS : ∀ φ ∈ S, φ ∈ cuspCont E a ∧ (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) ∧ ∀ x, convR μ f φ x = φ x) :
    FiniteDimensional ℂ (Submodule.span ℂ S) := by
  have hA := GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp E a μ f hf hs
  have hK := GlobalTheory.CompanionTheory.CompactFix.finiteDimensional_ker_sub_id _ hA
  set K := LinearMap.ker (((repOp (Rcusp μ) μ f : L2cusp μ →L[ℂ] L2cusp μ) : L2cusp μ →ₗ[ℂ] L2cusp μ) - LinearMap.id)
  let t := GlobalTheory.CompanionTheory.CuspTransfer.toL2cusp μ
  have ht : Function.Injective t := (injective_iff_map_eq_zero _).2 fun φ e => Subtype.ext (by
    by_contra h0
    exact toL2_ne_zero φ.2.2 φ.2.1.1 h0 (congrArg Subtype.val e))
  let Q := K.comap t
  have hQ : FiniteDimensional ℂ Q := FiniteDimensional.of_injective (t.restrict (q := K) fun x hx => hx)
    fun x y e => Subtype.ext (ht (congrArg Subtype.val e))
  have hle : Submodule.span ℂ S ≤ Q.map (GlobalTheory.CompanionTheory.CuspTransfer.cuspidalL2Functions μ).subtype := Submodule.span_le.2 fun φ hφ => by
    obtain ⟨h1, ⟨C, hC⟩, h3⟩ := hS φ hφ
    have hm := memL2_of_bounded_continuous_invariant μ h1.1 (leftInv_of_mem_cuspCont h1) hC
    refine ⟨⟨φ, h1, hm⟩, ?_, rfl⟩
    change _ ∈ K
    simp only [K, LinearMap.mem_ker, LinearMap.sub_apply, ContinuousLinearMap.coe_coe, LinearMap.id_apply]
    exact sub_eq_zero.2 (repOp_toL2cusp μ hf hs hm h1 h3)
  exact Submodule.finiteDimensional_of_le hle

theorem exists_compact_open {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) :
    ∃ U : Subgroup (GL (Fin a) (Af E)), U ≤ L ∧ IsOpen (U : Set (GL (Fin a) (Af E))) ∧
      IsCompact (U : Set (GL (Fin a) (Af E))) := by
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : GA E a)
  have hc := ContAut.continuous_map_pFin E a
  have hW : (GeneralLinearGroup.map (pFin E) '' C : Set (GL (Fin a) (Af E))) ∈ 𝓝 (1 : GL (Fin a) (Af E)) := by
    set_option synthInstance.maxHeartbeats 200000 in
      have h1 : finGL E a ⁻¹' C ∈ 𝓝 (1 : GL (Fin a) (Af E)) :=
        (GlobalTheory.CompanionTheory.DenseKFin.continuous_finGL (E := E) (a := a)).continuousAt.preimage_mem_nhds (by simpa using hC1)
    exact Filter.mem_of_superset h1 fun k hk => ⟨_, hk, pFin_finGL k⟩
  obtain ⟨U, hU, hUW⟩ := GlobalTheory.CompanionTheory.DenseKFin.exists_openSubgroup_GLAf (Filter.inter_mem hW (hL.mem_nhds (one_mem L)))
  exact ⟨U, fun k hk => (hUW hk).2, hU, (hC.image hc).of_isClosed_subset (Subgroup.isClosed_of_isOpen U hU)
    fun k hk => (hUW hk).1⟩

abbrev pI (g : GA E a) : GL (Fin a) (Cinf E) := GeneralLinearGroup.map (pInf E) g

def levelSet (U : Subgroup (GL (Fin a) (Af E))) : Set (GA E a) := {g | GeneralLinearGroup.map (pFin E) g ∈ U}

theorem isClopen_levelSet {U : Subgroup (GL (Fin a) (Af E))} (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) :
    IsClopen (levelSet U : Set (GA E a)) :=
  ⟨(Subgroup.isClosed_of_isOpen U hU).preimage (ContAut.continuous_map_pFin E a),
    hU.preimage (ContAut.continuous_map_pFin E a)⟩

theorem isCompact_levelSet_inter {U : Subgroup (GL (Fin a) (Af E))} (hU : IsCompact (U : Set (GL (Fin a) (Af E))))
    {K : Set (GL (Fin a) (Cinf E))} (hK : IsCompact K) : IsCompact ((levelSet U : Set (GA E a)) ∩ pI ⁻¹' K) := by
  have e : (levelSet U : Set (GA E a)) ∩ pI ⁻¹' K =
      (GASplit.splitEquiv E a).toHomeomorph ⁻¹' (K ×ˢ (U : Set (GL (Fin a) (Af E)))) := by
    ext g
    exact and_comm
  rw [e]
  exact (Homeomorph.isCompact_preimage _).2 (hK.prod hU)

section Measure

variable [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))]

def levelMeasure (μ : Measure (GA E a)) (U : Subgroup (GL (Fin a) (Af E))) : Measure (GL (Fin a) (Cinf E)) :=
  (μ.restrict (levelSet U)).map pI

theorem measurable_pI : Measurable (pI : GA E a → GL (Fin a) (Cinf E)) :=
  (ContAut.continuous_map_pInf E a).measurable

theorem isHaarMeasure_levelMeasure (μ : Measure (GA E a)) [μ.IsHaarMeasure] {U : Subgroup (GL (Fin a) (Af E))}
    (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) :
    (levelMeasure μ U).IsHaarMeasure := by
  haveI : T2Space (GL (Fin a) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
  have hH := (isClopen_levelSet hU).isOpen.measurableSet
  have hp := measurable_pI (E := E) (a := a)
  have hmeas : ∀ {K : Set (GL (Fin a) (Cinf E))}, MeasurableSet K →
      levelMeasure μ U K = μ (pI ⁻¹' K ∩ levelSet U) := fun hK => by
    rw [levelMeasure, Measure.map_apply hp hK, Measure.restrict_apply (hp hK)]
  refine { lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }
  · intro K hK
    rw [hmeas hK.measurableSet, Set.inter_comm]
    exact (isCompact_levelSet_inter hUc hK).measure_lt_top
  · intro y
    have hpre : (fun g : GA E a => infGL E a y * g) ⁻¹' levelSet U = levelSet U := by
      ext g
      simp [levelSet]
    have hmp := (measurePreserving_mul_left μ (infGL E a y)).restrict_preimage hH
    rw [hpre] at hmp
    rw [levelMeasure, Measure.map_map (measurable_const_mul y) hp]
    have e : ((fun x => y * x) ∘ pI : GA E a → _) = pI ∘ fun g => infGL E a y * g := by
      funext g
      simp
    rw [e, ← Measure.map_map hp (measurable_const_mul _), hmp.map_eq]
  · intro V hV hne
    obtain ⟨y, hy⟩ := hne
    rw [hmeas hV.measurableSet]
    refine ((hV.preimage (ContAut.continuous_map_pInf E a)).inter (isClopen_levelSet hU).isOpen).measure_ne_zero μ
      ⟨infGL E a y, by simpa using hy, ?_⟩
    simp [levelSet, one_mem]

theorem integral_levelMeasure (μ : Measure (GA E a)) {U : Subgroup (GL (Fin a) (Af E))}
    (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) {α : GL (Fin a) (Cinf E) → ℂ} (hα : Continuous α) {φ : GA E a → ℂ}
    (hφ : Continuous φ) (hfix : ∀ k ∈ U, ∀ x, φ (x * finGL E a k) = φ x) (g : GA E a) :
    ∫ y, φ (g * infGL E a y) * α y ∂levelMeasure μ U = convR μ ((levelSet U).indicator (α ∘ pI)) φ g := by
  have hH := (isClopen_levelSet (E := E) hU).isOpen.measurableSet
  have hc : Continuous fun y => φ (g * infGL E a y) * α y :=
    (hφ.comp (continuous_const.mul GlobalTheory.CompanionTheory.DenseKFin.continuous_infGL)).mul hα
  rw [levelMeasure, integral_map measurable_pI.aemeasurable hc.aestronglyMeasurable]
  have e : (fun y => (levelSet U).indicator (α ∘ pI) y * φ (g * y)) =
      (levelSet U).indicator fun y => α (pI y) * φ (g * y) := by
    funext y
    by_cases h : y ∈ levelSet U <;> simp [h]
  rw [convR, e, integral_indicator hH]
  refine setIntegral_congr_fun hH fun y hy => ?_
  have h := hfix _ hy (g * infGL E a (pI y))
  rw [mul_assoc, infGL_mul_finGL] at h
  simp only [h, mul_comm]

end Measure

theorem continuous_test {U : Subgroup (GL (Fin a) (Af E))} (hU : IsOpen (U : Set (GL (Fin a) (Af E))))
    {α : GL (Fin a) (Cinf E) → ℂ} (hα : Continuous α) :
    Continuous ((levelSet U : Set (GA E a)).indicator (α ∘ pI)) :=
  (hα.comp (ContAut.continuous_map_pInf E a)).indicator fun x hx => by
    rw [(isClopen_levelSet hU).frontier_eq] at hx
    exact absurd hx (Set.notMem_empty x)

theorem hasCompactSupport_test {U : Subgroup (GL (Fin a) (Af E))} (hU : IsCompact (U : Set (GL (Fin a) (Af E))))
    {α : GL (Fin a) (Cinf E) → ℂ} (hα : HasCompactSupport α) :
    HasCompactSupport ((levelSet U : Set (GA E a)).indicator (α ∘ pI)) := by
  set_option synthInstance.maxHeartbeats 200000 in
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_levelSet_inter hU hα) fun g hg => ?_
  rw [Function.mem_support] at hg
  have h1 : g ∈ levelSet U := by
    by_contra h
    exact hg (Set.indicator_of_notMem h _)
  refine ⟨h1, subset_tsupport _ ?_⟩
  rw [Function.mem_support]
  rwa [Set.indicator_of_mem h1] at hg

theorem cuspInvFin (hb : GlobalTheory.Published.CuspFormsBoundedGL)
    (hu : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), UnifAlpha E a) :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), CuspInvFin E a := by
  intro E _ _ _ a L hL W _ _ _ ρ hρ J hJ
  obtain ⟨U, hUL, hUo, hUc⟩ := exists_compact_open hL
  letI : MeasurableSpace (GL (Fin a) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin a) (Cinf E)) := ⟨rfl⟩
  let μ : Measure (GA E a) := Measure.haar
  haveI := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨α, hαc, hαs, hα⟩ := hu E a W ρ hρ J hJ (levelMeasure μ U) (isHaarMeasure_levelMeasure μ hUo hUc)
  set S : Set (Sm E a) := {φ | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1 ∧
    ∀ t g, φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = φ.1 g} with hSdef
  have key := finiteDimensional_span μ (continuous_test hUo hαc) (hasCompactSupport_test hUc hαs)
    ((Sm E a).subtype '' S) (by
      rintro _ ⟨φ, ⟨hφ, hcusp, hz⟩, rfl⟩
      have hcf : IsCuspForm φ := ⟨hφ.1, hcusp⟩
      have hm := mem_cuspCont_of_isCuspForm hcf hz
      refine ⟨hm, hb.of_invariant hcf hz, fun x => ?_⟩
      refine (integral_levelMeasure μ hUo hαc hm.1 (fun k hk y => ?_) x).symm.trans (hα L φ hφ x).symm
      exact congrFun (congrArg Subtype.val (hφ.2.1 k (hUL hk))) y)
  rw [← Submodule.map_span] at key
  exact (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).symm.finiteDimensional

end GlobalTheory.CompanionTheory.CuspInvariant

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedHermSVal
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
namespace GlobalTheory.CompanionTheory.MuC

theorem isClosed_hermS_val (D : D7) (p : ℕ) (e : AE D) :
    IsClosed ((hermS D p e : AddSubgroup (hermA D p)) : Set (hermA D p)) := by
  obtain ⟨_, _, _, _, _⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hc : Continuous fun x : hermA D p => e • (x : Formalism.IndefR.Datum.Mx D p p) :=
    (continuous_const_smul e).comp continuous_subtype_val
  exact isClosed_eq hc continuous_subtype_val


set_option synthInstance.maxHeartbeats 400000 in
theorem hermS_facts : ∀ (D : D7) (p : ℕ) (e : AE D), LocallyCompactSpace (hermS D p e) ∧ T2Space (hermS D p e) ∧
    SecondCountableTopology (hermS D p e) ∧ BorelSpace (hermS D p e) ∧ IsTopologicalAddGroup (hermS D p e) := by
  intro D p e
  obtain ⟨_, _, _, _, _⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hS := isClosed_hermS_val D p e
  have hA : IsClosed ((hermA D p : AddSubgroup (Formalism.IndefR.Datum.Mx D p p)) : Set (Formalism.IndefR.Datum.Mx D p p)) :=
    GlobalTheory.CompanionTheory.HermVol.isClosed_hermA
  haveI : LocallyCompactSpace (Formalism.IndefR.Datum.Mx D p p) :=
    show LocallyCompactSpace (Fin p → Fin p → AE D) from inferInstance
  haveI : SecondCountableTopology (Formalism.IndefR.Datum.Mx D p p) :=
    show SecondCountableTopology (Fin p → Fin p → AE D) from inferInstance
  haveI : BorelSpace (Formalism.IndefR.Datum.Mx D p p) := by
    first
    | exact show BorelSpace (Fin p → Fin p → AE D) from inferInstance
    | exact ⟨rfl⟩
    | exact Matrix.borelSpace
  haveI : SecondCountableTopology (hermA D p) := by
    first
    | exact Topology.IsInducing.subtypeVal.secondCountableTopology
    | exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
    | exact show SecondCountableTopology ((hermA D p : Set (Formalism.IndefR.Datum.Mx D p p))) from inferInstance
  haveI : SecondCountableTopology (hermS D p e) := by
    first
    | exact Topology.IsInducing.subtypeVal.secondCountableTopology
    | exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
    | exact show SecondCountableTopology ((hermS D p e : Set (hermA D p))) from inferInstance
  haveI : LocallyCompactSpace (hermA D p) := hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact ⟨hS.isClosedEmbedding_subtypeVal.locallyCompactSpace, inferInstance, inferInstance, inferInstance,
    inferInstance⟩

end GlobalTheory.CompanionTheory.MuC
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalIsotropicOrbitOfE0
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalIsotropicOrbitOfE0
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypOrbit

theorem exists_actW_e0_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E), LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ (hypOne J) y = 0 → ∃ g : HA (Fv F v) σ (hypOne J), actW (Fv F v) σ (hypOne J) g (e0 _ M) = y := by
  intro F E _ _ _ _ _ σ hσ M J hJ v y hy gy
  exact GlobalTheory.CompanionTheory.WeilSiegel.HypWitt.witt_e0 F E σ hσ M J hJ (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) y hy gy

end GlobalTheory.CompanionTheory.WeilSiegel.HypOrbit
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalIsotropicOrbitOfE0Statement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_isotropic_orbit_of_e0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E), LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ (hypOne J) y = 0 → ∃ g : HA (Fv F v) σ (hypOne J), actW (Fv F v) σ (hypOne J) g (e0 _ M) = y := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypOrbit.exists_actW_e0_eq | exact GlobalTheory.CompanionTheory.WeilSiegel.HypOrbit.exists_actW_e0_eq | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypOrbit.exists_actW_e0_eq <;> assumption)
end
end
