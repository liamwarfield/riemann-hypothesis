module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFinCombOfIsThetaAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionByZeroMapsCompletedHomLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionByZeroMapsCompletedHomLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ExtZeroLat

variable {D : D7}

theorem mxAt_mul_left {P : Pl D → Prop} {a b c : ℕ} (y : Mx D a b) {x : Mx D b c} (hx : MxAt P x) : MxAt P (y ⬝ x) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

theorem symplO_resT_symm_left {S A L T : HSp D} (o : OrthDec S A L) (a : WO T A) (t : WO T S) :
    symplO T S ((o.resT T).symm (a, 0)) t = symplO T A a (o.pA ⬝ t) := by
  rw [o.symplO_resT, AddEquiv.apply_symm_apply]
  have h0 : symplO T L 0 ((o.resT T) t).2 = 0 := by simp [symplO, hO]
  rw [h0, add_zero]; rfl

end GlobalTheory.FinPl.ExtZeroLat


open GlobalTheory.FinPl.ExtZeroLat in
theorem GlobalTheory.FinPl.ExtZero.extZero_mem_latO_target : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), (∀ u : WO T A, MxAt (· = p.v) u → (u ∈ latO T A (LT : Set _) (LA : Set _) (· = p.v) ↔ ∀ u' ∈ latO T A (LT : Set _) (LA : Set _) (· = p.v), ψ (symplO T A u u') = 1)) → (∀ u : WO T S, MxAt (· = p.v) u → (u ∈ latO T S (LT : Set _) (LS : Set _) (· = p.v) ↔ ∀ u' ∈ latO T S (LT : Set _) (LS : Set _) (· = p.v), ψ (symplO T S u u') = 1)) → halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) = o.boxT T (halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT)) → ∀ u ∈ latO T A (LT : Set _) (LA : Set _) (· = p.v), (o.resT T).symm (u, 0) ∈ latO T S (LT : Set _) (LS : Set _) (· = p.v) := by
  intro D k _ _ _ _ p n _ _ ψ S A L T o ζ β LA LS LT ΛT hA hS hfac u hu
  classical
  set ΛA := latO T A (LT : Set _) (LA : Set _) (· = p.v) with hΛA
  set ΛS := latO T S (LT : Set _) (LS : Set _) (· = p.v) with hΛS
  have he := p.split
  have hce := GlobalTheory.SplitScalar.isSplitIdem_conj he
  obtain ⟨ε, hε, hsum⟩ := p.above
  have hact := (GlobalTheory.FinPl.placeIdem_acts D p.v ε hε).1

  have hsplit : ∀ {m n : ℕ} (x : Mx D m n), MxAt (· = p.v) x → p.e • x + cA D p.e • x = x := by
    intro m n x hx
    rw [← add_smul, hsum]
    ext i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (hact _).1 (hx i j)

  have hrow0 : GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT) 0 = 1 := by
    have hz : GlobalTheory.FinPl.ExtZero.zrow β ζ (0 : WO T L) = 0 := by
      simp only [GlobalTheory.FinPl.ExtZero.zrow, Matrix.vecMul_zero, Pi.zero_apply, map_zero]
      have : ((fun _ => 0 : Fin T.rank → k) ᵥ* β.b) = 0 := Matrix.zero_vecMul _
      rw [this, smul_zero]
    have h0 : IsHalf p.e (0 : WO T L) := fun i j => by simp
    have hd : InDual ΛT (0 : n → k) := fun y _ => by
      rw [zero_dotProduct]; exact zero_mem _
    simp [GlobalTheory.FinPl.ExtZero.rowFun, hz, dualInd, h0, hd]

  have hext : ∀ a ∈ ΛA, IsHalf p.e a → (o.resT T).symm (a, 0) ∈ ΛS := by
    intro a ha hah
    have h1 := congrFun hfac ((o.resT T).symm (a, 0))
    rw [OrthDec.boxT, AddEquiv.apply_symm_apply, hrow0, mul_one] at h1
    have h2 : halfInd p.e ΛA a = 1 := by simp [halfInd, ha, hah]
    rw [h2] at h1
    unfold halfInd at h1
    by_contra hn
    rw [if_neg fun h => hn h.1] at h1
    exact zero_ne_one h1

  have hres : ∀ t ∈ ΛS, IsHalf p.e t → o.pA ⬝ t ∈ ΛA := by
    intro t ht hth
    have h1 := congrFun hfac t
    have h2 : halfInd p.e ΛS t = 1 := by simp [halfInd, ht, hth]
    rw [h2, OrthDec.boxT] at h1
    by_contra hn
    have : halfInd p.e ΛA ((o.resT T) t).1 = 0 := by
      unfold halfInd; rw [if_neg fun h => hn h.1]
    rw [this, zero_mul] at h1
    exact one_ne_zero h1
  have huM : MxAt (· = p.v) u := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  have heu : p.e • u ∈ ΛA := GlobalTheory.LatticeStable.smul_mem_latO D T A _ _ _ _ (finPart_idem_mem he.1) u hu
  have hι : (o.resT T).symm (p.e • u, 0) ∈ ΛS := hext _ heu (smul_isHalf he.1 u)
  have hιM : MxAt (· = p.v) ((o.resT T).symm (u, 0)) := by
    rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero]
    exact mxAt_mul_left _ huM
  refine (hS _ hιM).2 fun u' hu' => ?_
  have hu'M : MxAt (· = p.v) u' := GlobalTheory.FinPl.LatMem.latO_mxAt hu'
  have heu' : p.e • u' ∈ ΛS := GlobalTheory.LatticeStable.smul_mem_latO D T S _ _ _ _ (finPart_idem_mem he.1) u' hu'
  have hceu' : cA D p.e • u' ∈ ΛS := GlobalTheory.LatticeStable.smul_mem_latO D T S _ _ _ _ (finPart_idem_mem hce.1) u' hu'
  rw [symplO_resT_symm_left, ← hsplit u' hu'M, Matrix.mul_add, symplO_add_right, AddChar.map_add_eq_mul]
  have part1 : ψ (symplO T A u (o.pA ⬝ (p.e • u'))) = 1 :=
    (hA u huM).1 hu _ (hres _ heu' (smul_isHalf he.1 u'))
  have part2 : ψ (symplO T A u (o.pA ⬝ (cA D p.e • u'))) = 1 := by
    rw [← hsplit u huM, symplO_add_left, AddChar.map_add_eq_mul]
    have hz : symplO T A (cA D p.e • u) (o.pA ⬝ (cA D p.e • u')) = 0 := by
      refine symplO_conjHalf he (smul_isHalf hce.1 u) ?_
      intro i j
      rw [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_left_comm, (smul_isHalf hce.1 u') l j]
    rw [hz, AddChar.map_zero_eq_one, mul_one, ← symplO_resT_symm_left]
    exact (hS _ (GlobalTheory.FinPl.LatMem.latO_mxAt hι)).1 hι _ hceu'
  rw [part1, part2, one_mul]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionByZeroMapsCompletedHomLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_by_zero_maps_completed_hom_lattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), (∀ u : WO T A, MxAt (· = p.v) u → (u ∈ latO T A (LT : Set _) (LA : Set _) (· = p.v) ↔ ∀ u' ∈ latO T A (LT : Set _) (LA : Set _) (· = p.v), ψ (symplO T A u u') = 1)) → (∀ u : WO T S, MxAt (· = p.v) u → (u ∈ latO T S (LT : Set _) (LS : Set _) (· = p.v) ↔ ∀ u' ∈ latO T S (LT : Set _) (LS : Set _) (· = p.v), ψ (symplO T S u u') = 1)) → halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) = o.boxT T (halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT)) → ∀ u ∈ latO T A (LT : Set _) (LA : Set _) (· = p.v), (o.resT T).symm (u, 0) ∈ latO T S (LT : Set _) (LS : Set _) (· = p.v) := by
  first | exact @GlobalTheory.FinPl.ExtZero.extZero_mem_latO_target | exact GlobalTheory.FinPl.ExtZero.extZero_mem_latO_target | (intros; apply GlobalTheory.FinPl.ExtZero.extZero_mem_latO_target <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfTargetBoxDualIndicator
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfTargetBoxDualIndicator
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

namespace RowSB

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n]

theorem isHalf_add_of {e : AE D} {a b : ℕ} {x y : Mx D a b} (hx : IsHalf e x) (hy : IsHalf e y) :
    IsHalf e (x + y) := by
  intro i j
  simp only [Matrix.add_apply, mul_add, hx i j, hy i j]

theorem isHalf_nsmul_of {e : AE D} {a b : ℕ} {x : Mx D a b} (hx : IsHalf e x) (m : ℕ) : IsHalf e (m • x) := by
  intro i j
  rw [show (m • x) i j = m • x i j from rfl, nsmul_eq_mul, mul_left_comm, hx i j]

theorem isHalf_of_add {e : AE D} {a b : ℕ} {x y : Mx D a b} (hxy : IsHalf e (x + y)) (hy : IsHalf e y) :
    IsHalf e x := by
  intro i j
  have h := hxy i j
  rw [Matrix.add_apply, mul_add, hy i j] at h
  exact add_right_cancel h

theorem isHalf_resT_symm_pair {S A L : HSp D} (o : OrthDec S A L) (T : HSp D) {e : AE D} {a : WO T A} {b : WO T L}
    (ha : IsHalf e a) (hb : IsHalf e b) : IsHalf e ((o.resT T).symm (a, b)) := by
  intro i j
  rw [OrthDec.resT_symm_apply]
  simp only [Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun x _ => by rw [mul_left_comm, ha]
  · exact Finset.sum_congr rfl fun x _ => by rw [mul_left_comm, hb]

theorem zrow_add' {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (x y : WO T L) :
    zrow β ζ (x + y) = zrow β ζ x + zrow β ζ y := by
  simp only [zrow, Matrix.vecMul_add, Pi.add_apply, map_add (f := _)]
  rw [← smul_add, ← Matrix.add_vecMul]
  rfl

def zrowHom {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E) : WO T L →+ (n → k) :=
  AddMonoidHom.mk' (zrow β ζ) (zrow_add' β ζ)

theorem zrow_nsmul' {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (m : ℕ) (x : WO T L) :
    zrow β ζ (m • x) = m • zrow β ζ x :=
  map_nsmul (zrowHom β ζ) m x

theorem inDual_add' {Λ : Submodule 𝒪[k] (n → k)} {η ξ : n → k} (h : InDual Λ η) (h' : InDual Λ ξ) :
    InDual Λ (η + ξ) := fun y hy => by
  rw [add_dotProduct]; exact add_mem (h y hy) (h' y hy)

theorem inDual_sub' {Λ : Submodule 𝒪[k] (n → k)} {η ξ : n → k} (h : InDual Λ η) (h' : InDual Λ ξ) :
    InDual Λ (η - ξ) := fun y hy => by
  rw [sub_dotProduct]; exact sub_mem (h y hy) (h' y hy)

theorem inDual_nsmul' {Λ : Submodule 𝒪[k] (n → k)} {η : n → k} (h : InDual Λ η) (m : ℕ) :
    InDual Λ (m • η) := fun y hy => by
  rw [smul_dotProduct]; exact nsmul_mem (h y hy) m

theorem rowFun_dualInd_ne_zero {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E)
    (ΛT : Submodule 𝒪[k] (n → k)) {y : WO T L} (h : rowFun β ζ (dualInd ΛT) y ≠ 0) :
    IsHalf p.e y ∧ InDual ΛT (zrow β ζ y) := by
  unfold rowFun dualInd at h
  by_cases hy : IsHalf p.e y
  · rw [if_pos hy] at h
    by_cases hd : InDual ΛT (zrow β ζ y)
    · exact ⟨hy, hd⟩
    · rw [if_neg hd] at h; exact absurd rfl h
  · rw [if_neg hy] at h; exact absurd rfl h

theorem rowFun_dualInd_eq_one {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E)
    (ΛT : Submodule 𝒪[k] (n → k)) {y : WO T L} (hy : IsHalf p.e y) (hd : InDual ΛT (zrow β ζ y)) :
    rowFun β ζ (dualInd ΛT) y = 1 := by
  unfold rowFun dualInd
  rw [if_pos hy, if_pos hd]

theorem rowFun_dualInd_add_nsmul {T L : HSp D} (β : Frame p T n) (ζ : Fin L.rank → D.host.E)
    (ΛT : Submodule 𝒪[k] (n → k)) {y : WO T L} (hy : IsHalf p.e y) (hd : InDual ΛT (zrow β ζ y)) (m : ℕ)
    (x : WO T L) : rowFun β ζ (dualInd ΛT) (x + m • y) = rowFun β ζ (dualInd ΛT) x := by
  have hz : zrow β ζ (x + m • y) = zrow β ζ x + m • zrow β ζ y := by
    rw [zrow_add', zrow_nsmul']
  have hm := inDual_nsmul' hd m
  unfold rowFun dualInd
  by_cases hx : IsHalf p.e x
  · rw [if_pos (isHalf_add_of hx (isHalf_nsmul_of hy m)), if_pos hx, hz]
    have hiff : InDual ΛT (zrow β ζ x + m • zrow β ζ y) ↔ InDual ΛT (zrow β ζ x) :=
      ⟨fun h => by simpa using inDual_sub' h hm, fun h => inDual_add' h hm⟩
    by_cases hd' : InDual ΛT (zrow β ζ x)
    · rw [if_pos hd', if_pos (hiff.2 hd')]
    · rw [if_neg hd', if_neg (fun h => hd' (hiff.1 h))]
  · rw [if_neg hx, if_neg (fun h => hx (isHalf_of_add h (isHalf_nsmul_of hy m)))]

theorem halfInd_eq_one_iff' {e : AE D} {a b : ℕ} (Λ : AddSubgroup (Mx D a b)) (t : Mx D a b) :
    halfInd e Λ t = 1 ↔ t ∈ Λ ∧ IsHalf e t := by
  unfold halfInd
  split_ifs with h <;> simp [h]

theorem halfInd_ne_zero_iff' {e : AE D} {a b : ℕ} (Λ : AddSubgroup (Mx D a b)) (t : Mx D a b) :
    halfInd e Λ t ≠ 0 ↔ t ∈ Λ ∧ IsHalf e t := by
  unfold halfInd
  split_ifs with h <;> simp [h]

end RowSB

open RowSB

theorem isSBHalf_boxT_rowFun_dualInd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) = o.boxT T (halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT)) → ∀ Φ, IsSBHalf p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v)) Φ → IsSBHalf p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) (o.boxT T Φ (GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT))) := by
  intro D k _ _ _ _ p n _ _ S A L T o ζ β LA LS LT ΛT H Φ hΦ
  obtain ⟨hsupp, m, hm, hinv, hlat⟩ := hΦ
  have hH : ∀ w, halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) w =
      halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v)) (o.resT T w).1 *
        rowFun β ζ (dualInd ΛT) (o.resT T w).2 := fun w => congrFun H w
  have hbox : ∀ w, o.boxT T Φ (rowFun β ζ (dualInd ΛT)) w =
      Φ (o.resT T w).1 * rowFun β ζ (dualInd ΛT) (o.resT T w).2 := fun w => rfl
  refine ⟨fun t ht => ?_, m, hm, fun u hu hhu t => ?_, fun t ht => ?_⟩
  · rw [hbox] at ht
    have h1 := hsupp _ (left_ne_zero_of_mul ht)
    have h2 := (rowFun_dualInd_ne_zero β ζ ΛT (right_ne_zero_of_mul ht)).1
    have := isHalf_resT_symm_pair o T h1 h2
    rwa [Prod.mk.eta, AddEquiv.symm_apply_apply] at this
  · have hu1 : halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) u = 1 :=
      (halfInd_eq_one_iff' _ _).2 ⟨hu, hhu⟩
    rw [hH] at hu1
    have hA := (halfInd_ne_zero_iff' _ _).1 (left_ne_zero_of_mul_eq_one hu1)
    have hR := rowFun_dualInd_ne_zero β ζ ΛT (right_ne_zero_of_mul_eq_one hu1)
    rw [hbox, hbox, map_add (f := _), map_nsmul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      hinv _ hA.1 hA.2, rowFun_dualInd_add_nsmul β ζ ΛT hR.1 hR.2]
  · rw [hbox] at ht
    have hΦt := left_ne_zero_of_mul ht
    have h1 := hsupp _ hΦt
    have hR := rowFun_dualInd_ne_zero β ζ ΛT (right_ne_zero_of_mul ht)
    have hmt : halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) (m • t) = 1 := by
      rw [hH, map_nsmul, Prod.smul_fst, Prod.smul_snd,
        (halfInd_eq_one_iff' _ _).2 ⟨hlat _ hΦt, isHalf_nsmul_of h1 m⟩,
        rowFun_dualInd_eq_one β ζ ΛT (isHalf_nsmul_of hR.1 m) (by rw [zrow_nsmul']; exact inDual_nsmul' hR.2 m),
        one_mul]
    exact ((halfInd_eq_one_iff' _ _).1 hmt).1

end GlobalTheory.FinPl.ExtZero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfTargetBoxDualIndicatorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchwartzBruhatHalf_target_box_dualIndicator : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) = o.boxT T (halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT)) → ∀ Φ, IsSBHalf p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v)) Φ → IsSBHalf p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) (o.boxT T Φ (GlobalTheory.FinPl.ExtZero.rowFun β ζ (dualInd ΛT))) := by
  first | exact @GlobalTheory.FinPl.ExtZero.isSBHalf_boxT_rowFun_dualInd | exact GlobalTheory.FinPl.ExtZero.isSBHalf_boxT_rowFun_dualInd | (intros; apply GlobalTheory.FinPl.ExtZero.isSBHalf_boxT_rowFun_dualInd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfSourceBoxLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfSourceBoxLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.ExtZero.SBBox

variable {D : D7}

theorem half_add {m n : ℕ} {e : AE D} {u t : Mx D m n} (hu : IsHalf e u) (ht : IsHalf e t) : IsHalf e (u + t) := by
  intro i j
  rw [Matrix.add_apply, mul_add, hu, ht]

theorem half_sub {m n : ℕ} {e : AE D} {u t : Mx D m n} (hu : IsHalf e u) (ht : IsHalf e t) : IsHalf e (u - t) := by
  intro i j
  rw [Matrix.sub_apply, mul_sub, hu, ht]

theorem half_nsmul {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) (N : ℕ) : IsHalf e (N • u) := by
  induction N with
  | zero => intro i j; rw [zero_smul, Matrix.zero_apply, mul_zero]
  | succ N ih => rw [succ_nsmul]; exact half_add ih hu

theorem half_mul {m n l : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) (x : Mx D n l) :
    IsHalf e (u * x : Mx D m l) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by rw [← mul_assoc, hu]

theorem half_of_res {S A L T : HSp D} (o : OrthDec S A L) {e : AE D} {t : WO S T}
    (h1 : IsHalf e (o.resS T t).1) (h2 : IsHalf e (o.resS T t).2) : IsHalf e t := by
  rw [← (o.resS T).symm_apply_apply t]
  exact half_add (half_mul h1 _) (half_mul h2 _)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {T L : HSp D} {n : Type} [Fintype n] [DecidableEq n]

theorem zcol_add (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (y y' : WO L T) :
    zcol β ζ (y + y') = zcol β ζ y + zcol β ζ y' := by
  unfold zcol
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  rw [Matrix.add_mulVec, Pi.add_apply, map_add (f := _)]; rfl

theorem zcol_zero (β : Frame p T n) (ζ : Fin L.rank → D.host.E) : zcol β ζ 0 = 0 := by
  have := zcol_add β ζ 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem zcol_nsmul (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (y : WO L T) (N : ℕ) :
    zcol β ζ (N • y) = N • zcol β ζ y := by
  induction N with
  | zero => rw [zero_smul, zero_smul, zcol_zero]
  | succ N ih => rw [succ_nsmul, succ_nsmul, zcol_add, ih]

theorem colFun_ne_zero (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (Λ : Submodule 𝒪[k] (n → k)) (y : WO L T) :
    colFun β ζ (vecInd Λ) y ≠ 0 ↔ IsHalf p.e y ∧ zcol β ζ y ∈ Λ := by
  unfold colFun vecInd
  by_cases h : IsHalf p.e y <;> by_cases h' : zcol β ζ y ∈ Λ <;> simp [h, h']

theorem colFun_add (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (Λ : Submodule 𝒪[k] (n → k)) (y u : WO L T)
    (hu : IsHalf p.e u) (hu' : zcol β ζ u ∈ Λ) :
    colFun β ζ (vecInd Λ) (y + u) = colFun β ζ (vecInd Λ) y := by
  have h1 : IsHalf p.e (y + u) ↔ IsHalf p.e y :=
    ⟨fun h => by simpa using half_sub h hu, fun h => half_add h hu⟩
  have h2 : zcol β ζ (y + u) ∈ Λ ↔ zcol β ζ y ∈ Λ := by
    rw [zcol_add]; exact Λ.add_mem_iff_left hu'
  unfold colFun vecInd
  rw [propext h1, propext h2]

theorem halfInd_ne_zero {m l : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m l)) (t : Mx D m l) :
    halfInd e Λ t ≠ 0 ↔ t ∈ Λ ∧ IsHalf e t := by
  unfold halfInd
  by_cases h : t ∈ Λ ∧ IsHalf e t <;> simp [h]

theorem isSBHalf_boxS_gen {S A : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n)
    (ΛA : AddSubgroup (WO A T)) (ΛS : AddSubgroup (WO S T)) (ΛT : Submodule 𝒪[k] (n → k))
    (hf : halfInd p.e ΛS = o.boxS T (halfInd p.e ΛA) (colFun β ζ (vecInd ΛT)))
    (Φ : WO A T → ℂ) (hΦ : IsSBHalf p.e ΛA Φ) :
    IsSBHalf p.e ΛS (o.boxS T Φ (colFun β ζ (vecInd ΛT))) := by
  have key : ∀ u : WO S T, (u ∈ ΛS ∧ IsHalf p.e u) ↔
      (((o.resS T u).1 ∈ ΛA ∧ IsHalf p.e (o.resS T u).1) ∧
        (IsHalf p.e (o.resS T u).2 ∧ zcol β ζ (o.resS T u).2 ∈ ΛT)) := by
    intro u
    rw [← halfInd_ne_zero, ← halfInd_ne_zero, ← colFun_ne_zero, hf, ← mul_ne_zero_iff]
    rfl
  obtain ⟨hs, N, hN, hinv, hsup⟩ := hΦ
  have hne : ∀ t, o.boxS T Φ (colFun β ζ (vecInd ΛT)) t ≠ 0 →
      Φ (o.resS T t).1 ≠ 0 ∧ IsHalf p.e (o.resS T t).2 ∧ zcol β ζ (o.resS T t).2 ∈ ΛT := by
    intro t ht
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 ht
    exact ⟨h1, (colFun_ne_zero β ζ ΛT _).1 h2⟩
  refine ⟨fun t ht => half_of_res o (hs _ (hne t ht).1) (hne t ht).2.1, N, hN, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (key u).1 ⟨hu, hu'⟩
    unfold OrthDec.boxS
    rw [map_add (f := _), map_nsmul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, hinv _ h1 h2,
      colFun_add β ζ ΛT _ _ (half_nsmul h3 N) (by rw [zcol_nsmul]; exact nsmul_mem h4 N)]
  · obtain ⟨h1, h2, h3⟩ := hne t ht
    refine ((key (N • t)).2 ?_).1
    rw [map_nsmul, Prod.smul_fst, Prod.smul_snd]
    exact ⟨⟨hsup _ h1, half_nsmul (hs _ h1) N⟩, half_nsmul h2 N, by rw [zcol_nsmul]; exact nsmul_mem h3 N⟩

theorem isSBHalf_boxS : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) = o.boxS T (halfInd p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT)) → ∀ Φ, IsSBHalf p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v)) Φ → IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) (o.boxS T Φ (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT))) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ o ζ β _ _ _ ΛT hf Φ hΦ => isSBHalf_boxS_gen o ζ β _ _ ΛT hf Φ hΦ

end GlobalTheory.FinPl.ExtZero.SBBox

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfSourceBoxLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSchwartzBruhatHalf_source_box_lattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) = o.boxS T (halfInd p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT)) → ∀ Φ, IsSBHalf p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v)) Φ → IsSBHalf p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) (o.boxS T Φ (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT))) := by
  first | exact @GlobalTheory.FinPl.ExtZero.SBBox.isSBHalf_boxS | exact GlobalTheory.FinPl.ExtZero.SBBox.isSBHalf_boxS | (intros; apply GlobalTheory.FinPl.ExtZero.SBBox.isSBHalf_boxS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationExtendByZeroTargetSlice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationExtendByZeroTargetSlice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem comb_extT_resT_symm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (c : WO T A →₀ ℂ) (f : WO T S → ℂ) (y : WO T L) (w : WO T A), comb ψ T A c (fun w' => f ((o.resT T).symm (w', y))) w = comb ψ T S (extT o T c) f ((o.resT T).symm (w, y)) := by
  intro D ψ S A L T o c f y w
  have h1 : ∀ (X Y : HSp D) (d : WO X Y →₀ ℂ) (g : WO X Y → ℂ) (x : WO X Y),
      comb ψ X Y d g x = d.sum fun u a => a * heisO ψ X Y u g x := by
    intro X Y d g x
    simp only [comb, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h1, extT, Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  exact Finsupp.sum_congr fun u _ => by rw [heisO_resT_symm]

end GlobalTheory.FinPl.ExtZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationExtendByZeroTargetSliceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCombination_extendByZero_target_slice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (c : WO T A →₀ ℂ) (f : WO T S → ℂ) (y : WO T L) (w : WO T A), comb ψ T A c (fun w' => f ((o.resT T).symm (w', y))) w = comb ψ T S (extT o T c) f ((o.resT T).symm (w, y)) := by
  first | exact @GlobalTheory.FinPl.ExtZero.comb_extT_resT_symm | exact GlobalTheory.FinPl.ExtZero.comb_extT_resT_symm | (intros; apply GlobalTheory.FinPl.ExtZero.comb_extT_resT_symm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerIntertwinerSliceRestrictionPlaceMode
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerIntertwinerSliceRestrictionPlaceMode
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem restrModel_isPlaceModel : ∀ (D : D7) {m n m' n' m'' n'' : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (BS : Mx D m n → Mx D m n → AF D.host.F) (hsS : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (BA : Mx D m' n' → Mx D m' n' → AF D.host.F) (hsA : Mx D m' n' → (Mx D m' n' → ℂ) → (Mx D m' n' → ℂ)) (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (e : AE D) (ΛS : AddSubgroup (Mx D m n)) (ΛA : AddSubgroup (Mx D m' n')) (h : Mx D m'' n'' → ℂ) (f₀ : Mx D m n → ℂ) (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)), IsPlaceModel ψ BS hsS e ΛS 1 f₀ T' → (∀ a F w y, hsS (r.symm (a, 0)) F (r.symm (w, y)) = hsA a (fun w' => F (r.symm (w', y))) w) → (∀ t a, BS t (r.symm (a, 0)) = BA (r t).1 a) → (∀ a, IsHalf e a → IsHalf e (r.symm (a, 0))) → (∀ a, IsHalf (cA D e) a → IsHalf (cA D e) (r.symm (a, 0))) → (∀ Φ, IsSBHalf e ΛA Φ → IsSBHalf e ΛS (fun t => Φ (r t).1 * h (r t).2)) → halfInd e ΛS = (fun t => halfInd e ΛA (r t).1 * h (r t).2) → ∀ y, IsPlaceModel ψ BA hsA e ΛA 1 (fun w => f₀ (r.symm (w, y))) (GlobalTheory.FinPl.ExtZero.restrModel r h T' y) := by
  intro D m n m' n' m'' n'' ψ BS hsS BA hsA r e ΛS ΛA h f₀ T' hT hcomp hB hhalf hhalfc hSB hInd y
  refine ⟨?_, ?_, ?_⟩
  · intro Φ hΦ x hx
    funext w
    rw [restrModel_apply]
    have hfun : (fun t => (fun t => Φ (t + x)) (r t).1 * h (r t).2) =
        fun t => (fun t => Φ (r t).1 * h (r t).2) (t + r.symm (x, 0)) := by
      funext t
      simp only [map_add (f := _), AddEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add, add_zero]
    rw [hfun, hT.trans _ (hSB Φ hΦ) _ (hhalf x hx), hcomp]
    rfl
  · intro Φ hΦ y' hy'
    funext w
    rw [restrModel_apply]
    have hfun : (fun t => (fun t => ψ (BA t y') * Φ t) (r t).1 * h (r t).2) =
        fun t => ψ (BS t (r.symm (y', 0))) * (fun t => Φ (r t).1 * h (r t).2) t := by
      funext t
      simp only [hB, mul_assoc]
    rw [hfun, hT.modul _ (hSB Φ hΦ) _ (hhalfc y' hy'), hcomp]
    rfl
  · funext w
    rw [restrModel_apply]
    have hfun : (fun t => ((1 : ℂ) • halfInd e ΛA) (r t).1 * h (r t).2) = (1 : ℂ) • halfInd e ΛS := by
      rw [hInd]; funext t; simp
    rw [hfun, hT.vac]

end GlobalTheory.FinPl.ExtZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerIntertwinerSliceRestrictionPlaceModeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schroedinger_intertwiner_slice_restriction_placeModel : ∀ (D : D7) {m n m' n' m'' n'' : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (BS : Mx D m n → Mx D m n → AF D.host.F) (hsS : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (BA : Mx D m' n' → Mx D m' n' → AF D.host.F) (hsA : Mx D m' n' → (Mx D m' n' → ℂ) → (Mx D m' n' → ℂ)) (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (e : AE D) (ΛS : AddSubgroup (Mx D m n)) (ΛA : AddSubgroup (Mx D m' n')) (h : Mx D m'' n'' → ℂ) (f₀ : Mx D m n → ℂ) (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)), IsPlaceModel ψ BS hsS e ΛS 1 f₀ T' → (∀ a F w y, hsS (r.symm (a, 0)) F (r.symm (w, y)) = hsA a (fun w' => F (r.symm (w', y))) w) → (∀ t a, BS t (r.symm (a, 0)) = BA (r t).1 a) → (∀ a, IsHalf e a → IsHalf e (r.symm (a, 0))) → (∀ a, IsHalf (cA D e) a → IsHalf (cA D e) (r.symm (a, 0))) → (∀ Φ, IsSBHalf e ΛA Φ → IsSBHalf e ΛS (fun t => Φ (r t).1 * h (r t).2)) → halfInd e ΛS = (fun t => halfInd e ΛA (r t).1 * h (r t).2) → ∀ y, IsPlaceModel ψ BA hsA e ΛA 1 (fun w => f₀ (r.symm (w, y))) (GlobalTheory.FinPl.ExtZero.restrModel r h T' y) := by
  first | exact @GlobalTheory.FinPl.ExtZero.restrModel_isPlaceModel | exact GlobalTheory.FinPl.ExtZero.restrModel_isPlaceModel | (intros; apply GlobalTheory.FinPl.ExtZero.restrModel_isPlaceModel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationExtendByZeroSourceSlice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationExtendByZeroSourceSlice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem comb_extS_slice :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (c : WO A T →₀ ℂ) (f : WO S T → ℂ) (y : WO L T) (w : WO A T), comb ψ A T c (fun w' => f ((o.resS T).symm (w', y))) w = comb ψ S T (extS o T c) f ((o.resS T).symm (w, y)) := by
  intro D ψ S A L T o c f y w
  classical
  have hinj : Function.Injective (fun a : WO A T => (o.resS T).symm (a, 0)) := fun a b h => by
    simpa using h
  unfold comb extS
  rw [Finsupp.mapDomain_support_of_injective hinj, Finset.sum_image (fun a _ b _ h => hinj h),
    Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finsupp.mapDomain_apply_of_injective hinj, Pi.smul_apply, Pi.smul_apply, heisO_resS_symm]

end GlobalTheory.FinPl.ExtZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationExtendByZeroSourceSliceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCombination_extendByZero_source_slice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (c : WO A T →₀ ℂ) (f : WO S T → ℂ) (y : WO L T) (w : WO A T), comb ψ A T c (fun w' => f ((o.resS T).symm (w', y))) w = comb ψ S T (extS o T c) f ((o.resS T).symm (w, y)) := by
  first | exact @GlobalTheory.FinPl.ExtZero.comb_extS_slice | exact GlobalTheory.FinPl.ExtZero.comb_extS_slice | (intros; apply GlobalTheory.FinPl.ExtZero.comb_extS_slice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCombinationExtendByZeroOrthSumLine
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem ext_zero : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∀ (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛA : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC T LT → α.IsLat LA ΛA → α₀.IsLat LS (lastKer ΛA) → β.IsLat LT ΛT → (∀ (Ψ : Matrix n n' k → ℂ) (c : WO A T →₀ ℂ), CombAt (· = p.v) c → (∀ f₀, Vac ψ A T LA LT (· = p.v) f₀ → Over ψ α β LA LT f₀ Ψ (comb ψ A T c f₀)) → ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → Over ψ α₀ β LS LT f₀ (tensCol Ψ (vecInd ΛT)) (comb ψ S T (extS o T c) f₀)) ∧ ∀ (Ψ : Matrix n' n k → ℂ) (c : WO T A →₀ ℂ), CombAt (· = p.v) c → (∀ f₀, Vac ψ T A LT LA (· = p.v) f₀ → Over ψ β α LT LA f₀ Ψ (comb ψ T A c f₀)) → ∀ f₀, Vac ψ T S LT LS (· = p.v) f₀ → Over ψ β α₀ LT LS f₀ (tensRow Ψ (dualInd ΛT)) (comb ψ T S (extT o T c) f₀) := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ hU S A L T o ζ hζ α α₀ β hsum LA LS LT ΛA ΛT hA hS hT hαA hα₀ hβ
  have : ΛT.IsFullLattice k := GlobalTheory.FinPl.isLattice_of_isLat_selfDual β LT hT ΛT hβ
  have sdA := GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ A T LA LT hA hT (· = p.v)
  have sdS := GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ S T LS LT hS hT (· = p.v)
  have sdA' := GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ T A LT LA hT hA (· = p.v)
  have sdS' := GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ T S LT LS hT hS (· = p.v)
  have facS : halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) =
      o.boxS T (halfInd p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v))) (colFun β ζ (vecInd ΛT)) := by
    rw [← GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator D k p n (n' ⊕ Fin 1) S T α₀ β LS LT hS hT hU _ _ hα₀ hβ,
      ← GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator D k p n n' A T α β LA LT hA hT hU _ _ hαA hβ, latInd_lastKer,
      GlobalTheory.T.extendByZero_source_tensor_column_product D k p n n' S A L T o ζ α α₀ β hsum]
  have facT : halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) =
      o.boxT T (halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v))) (rowFun β ζ (dualInd ΛT)) := by
    rw [← GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator D k p (n' ⊕ Fin 1) n T S β α₀ LT LS hT hS hU _ _ hβ hα₀,
      ← GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator D k p n' n T A β α LT LA hT hA hU _ _ hβ hαA, latInd_lastKer_row,
      GlobalTheory.T.extendByZero_target_tensor_row_product D k p n n' S A L T o ζ hζ α α₀ β hsum]
  have latS := GlobalTheory.T.extendByZero_mem_completed_lattice_source D k p n ψ S A L T o ζ β LA LS LT ΛT sdA sdS facS
  have latT := GlobalTheory.T.extension_by_zero_maps_completed_hom_lattice D k p n ψ S A L T o ζ β LA LS LT ΛT sdA' sdS' facT
  have vacS : ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → ∀ y,
      Vac ψ A T LA LT (· = p.v) (fun w => f₀ ((o.resS T).symm (w, y))) := by
    intro f₀ hf y
    refine ⟨GlobalTheory.T.isThetaFunO_source_slice D ψ S A L T o f₀ y hf.1, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
    · funext w
      rw [← heisO_resS_symm ψ o (2 • u) f₀ w y]
      have h2 : (o.resS T).symm (2 • u, 0) = 2 • (o.resS T).symm (u, 0) := by
        rw [← map_nsmul]; simp
      rw [h2, hf.2.1 _ (latS u hu)]
    · funext w
      rw [← heisO_resS_symm ψ o u f₀ w y, hf.2.2 e' he' _ (latS u hu) (half_resS_symm o hh)]
  have vacT : ∀ f₀, Vac ψ T S LT LS (· = p.v) f₀ → ∀ y,
      Vac ψ T A LT LA (· = p.v) (fun w => f₀ ((o.resT T).symm (w, y))) := by
    intro f₀ hf y
    refine ⟨GlobalTheory.T.isThetaFunO_target_slice_orthogonal_sum D ψ S A L T o f₀ y hf.1, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
    · funext w
      rw [← heisO_resT_symm ψ o (2 • u) f₀ w y]
      have h2 : (o.resT T).symm (2 • u, 0) = 2 • (o.resT T).symm (u, 0) := by
        rw [← map_nsmul]; simp
      rw [h2, hf.2.1 _ (latT u hu)]
    · funext w
      rw [← heisO_resT_symm ψ o u f₀ w y, hf.2.2 e' he' _ (latT u hu) (half_resT_symm o hh)]
  refine ⟨fun Ψ c _ hyp f₀ hf₀ => ?_, fun Ψ c _ hyp f₀ hf₀ => ?_⟩
  · have hΨ : Ψ ∈ SB (Matrix n n' k) := (hyp _ (vacS f₀ hf₀ 0)).2.2.2.1
    have hΨ' : tensCol Ψ (vecInd ΛT) ∈ SB (Matrix n (n' ⊕ Fin 1) k) :=
      GlobalTheory.FinPl.Comm.tensCol_mem hΨ (GlobalTheory.FinPl.Comm.vecInd_mem ΛT)
    obtain ⟨f, hf, -⟩ := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hψ S T α₀ β LS LT hS hT f₀ hf₀).1 _ hΨ'
    refine ⟨hS, hT, hf₀, hΨ', hf.2.2.2.2.1, fun T' hT' => ?_⟩
    funext t
    obtain ⟨⟨w, y⟩, rfl⟩ : ∃ q, (o.resS T).symm q = t := ⟨_, (o.resS T).symm_apply_apply t⟩
    have hmod := GlobalTheory.T.schroedinger_intertwiner_slice_restriction_placeModel D ψ (symplO S T) (heisO ψ S T) (symplO A T) (heisO ψ A T) (o.resS T) p.e _ _
      (colFun β ζ (vecInd ΛT)) f₀ T' hT' (fun a F w y => heisO_resS_symm ψ o a F w y)
      (fun t a => symplO_resS_symm o t a) (fun a ha => half_resS_symm o ha) (fun a ha => half_resS_symm o ha)
      (GlobalTheory.T.isSchwartzBruhatHalf_source_box_lattice D k p n S A L T o ζ β LA LS LT ΛT facS) facS y
    have key := congrFun ((hyp _ (vacS f₀ hf₀ y)).2.2.2.2.2 _ hmod) w
    rw [GlobalTheory.T.heisenbergCombination_extendByZero_source_slice] at key
    rw [key, restrModel_apply, GlobalTheory.T.extendByZero_source_tensor_column_product D k p n n' S A L T o ζ α α₀ β hsum]
    rfl
  · have hΨ : Ψ ∈ SB (Matrix n' n k) := (hyp _ (vacT f₀ hf₀ 0)).2.2.2.1
    have hΨ' : tensRow Ψ (dualInd ΛT) ∈ SB (Matrix (n' ⊕ Fin 1) n k) :=
      GlobalTheory.FinPl.Comm.tensRow_mem hΨ (GlobalTheory.FinPl.Comm.dualInd_mem ΛT)
    obtain ⟨f, hf, -⟩ := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p (n' ⊕ Fin 1) n ψ hψ T S β α₀ LT LS hT hS f₀ hf₀).1 _ hΨ'
    refine ⟨hT, hS, hf₀, hΨ', hf.2.2.2.2.1, fun T' hT' => ?_⟩
    funext t
    obtain ⟨⟨w, y⟩, rfl⟩ : ∃ q, (o.resT T).symm q = t := ⟨_, (o.resT T).symm_apply_apply t⟩
    have hmod := GlobalTheory.T.schroedinger_intertwiner_slice_restriction_placeModel D ψ (symplO T S) (heisO ψ T S) (symplO T A) (heisO ψ T A) (o.resT T) p.e _ _
      (rowFun β ζ (dualInd ΛT)) f₀ T' hT' (fun a F w y => heisO_resT_symm ψ o a F w y)
      (fun t a => symplO_resT_symm o t a) (fun a ha => half_resT_symm o ha) (fun a ha => half_resT_symm o ha)
      (GlobalTheory.T.isSchwartzBruhatHalf_target_box_dualIndicator D k p n S A L T o ζ β LA LS LT ΛT facT) facT y
    have key := congrFun ((hyp _ (vacT f₀ hf₀ y)).2.2.2.2.2 _ hmod) w
    rw [GlobalTheory.T.heisenbergCombination_extendByZero_target_slice] at key
    rw [key, restrModel_apply, GlobalTheory.T.extendByZero_target_tensor_row_product D k p n n' S A L T o ζ hζ α α₀ β hsum]
    rfl

end GlobalTheory.FinPl.ExtZero

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCombinationExtendByZeroOrthSumLineStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_combination_extendByZero_orthSum_line : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∀ (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛA : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC T LT → α.IsLat LA ΛA → α₀.IsLat LS (lastKer ΛA) → β.IsLat LT ΛT → (∀ (Ψ : Matrix n n' k → ℂ) (c : WO A T →₀ ℂ), CombAt (· = p.v) c → (∀ f₀, Vac ψ A T LA LT (· = p.v) f₀ → Over ψ α β LA LT f₀ Ψ (comb ψ A T c f₀)) → ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → Over ψ α₀ β LS LT f₀ (tensCol Ψ (vecInd ΛT)) (comb ψ S T (extS o T c) f₀)) ∧ ∀ (Ψ : Matrix n' n k → ℂ) (c : WO T A →₀ ℂ), CombAt (· = p.v) c → (∀ f₀, Vac ψ T A LT LA (· = p.v) f₀ → Over ψ β α LT LA f₀ Ψ (comb ψ T A c f₀)) → ∀ f₀, Vac ψ T S LT LS (· = p.v) f₀ → Over ψ β α₀ LT LS f₀ (tensRow Ψ (dualInd ΛT)) (comb ψ T S (extT o T c) f₀) := by
  first | exact @GlobalTheory.FinPl.ExtZero.ext_zero | exact GlobalTheory.FinPl.ExtZero.ext_zero | (intros; apply GlobalTheory.FinPl.ExtZero.ext_zero <;> assumption)
end
