module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HerbrandQuotientEigenDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLinearEquivOfPiFinPowFinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenSublatticeFreeLatticeIffEval
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenSublatticeFreeLatticeIffEval
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.EigenSubEval

variable {C : Type} [Field C] {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
  {S : Type} [Fintype S] [DecidableEq S]

theorem evalVec_rsmul (b : S → Int0 v) (N : ℕ) (r : RS b) (z : Fin N → RS b) (s : S) (i : Fin N) :
    evalVec b N (r • z) s i = ((ev b s r : Int0 v) : C) * evalVec b N z s i := by
  simp only [evalVec, Pi.smul_apply, smul_eq_mul, map_mul, Subring.coe_mul]

theorem mem_eigSub_iff (b : S → Int0 v) (N : ℕ) (τ : S) (z : Fin N → RS b) :
    z ∈ eigSub b τ (Fin N → RS b) ↔ lin b τ • z = 0 := Iff.rfl

theorem eigenSub_iff_eval (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (τ : S) (ha : Function.Injective a)
    (hinj : Function.Injective (evalVec (liftA hv a) N))
    (hrange : ∀ y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y)
    (y : Fin N → C) :
    y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin N → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) τ ↔
      ∃ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.eigSub (liftA hv a) τ (Fin N → RS (liftA hv a)),
        (fun i => ((GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.comp (liftA hv a) N τ z i : Int0 v) : C)) = y := by
  have hev : ∀ s t, ((ev (liftA hv a) s (lin (liftA hv a) t) : Int0 v) : C) = (a s : C) - a t := by
    intro s t
    rw [ev_lin]; rfl
  have hne : ∀ s, s ≠ τ → (a s : C) - a τ ≠ 0 := by
    intro s hs h
    exact hs (ha (Subtype.ext (sub_eq_zero.1 h)))
  have hmem : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin N → C)
      (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) τ ↔
      (Pi.single τ y : S → Fin N → C) ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N := Iff.rfl
  rw [hmem]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := (hrange _).1 h
    refine ⟨x, ?_, ?_⟩
    · rw [mem_eigSub_iff]
      apply hinj
      funext s i
      rw [evalVec_rsmul, hev, hx]
      have h0 : evalVec (liftA hv a) N (0 : Fin N → RS (liftA hv a)) s i = 0 := by
        simp [evalVec]
      rw [h0]
      by_cases e : s = τ
      · subst e; simp
      · simp [e]
    · rw [comp_coe, hx]; simp
  · rintro ⟨z, hz, rfl⟩
    rw [mem_eigSub_iff] at hz
    have key : evalVec (liftA hv a) N z = Pi.single τ (evalVec (liftA hv a) N z τ) := by
      funext s i
      by_cases e : s = τ
      · subst e; simp
      · have h1 := congrFun (congrFun (congrArg (evalVec (liftA hv a) N) hz) s) i
        rw [evalVec_rsmul, hev] at h1
        have h0 : evalVec (liftA hv a) N (0 : Fin N → RS (liftA hv a)) s i = 0 := by
          simp [evalVec]
        rw [h0] at h1
        rw [Pi.single_eq_of_ne e]
        exact (mul_eq_zero.1 h1).resolve_left (hne s e)
    rw [comp_coe, ← key]
    exact (hrange _).2 ⟨z, rfl⟩

end GlobalTheory.EigenSubEval
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenSublatticeFreeLatticeIffEvalStatement
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenSublattice_freeLattice_iff_eval : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (τ : S), Function.Injective a → Function.Injective (evalVec (liftA hv a) N) → (∀ y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y) → ∀ y : Fin N → C, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin N → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) τ ↔ ∃ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.eigSub (liftA hv a) τ (Fin N → RS (liftA hv a)), (fun i => ((GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.comp (liftA hv a) N τ z i : Int0 v) : C)) = y := by
  first | exact @GlobalTheory.EigenSubEval.eigenSub_iff_eval | exact GlobalTheory.EigenSubEval.eigenSub_iff_eval | (intros; apply GlobalTheory.EigenSubEval.eigenSub_iff_eval <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPolynomialEvalFreeLatticeIffExistsEval
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPolynomialEvalFreeLatticeIffExistsEval
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.EvalVecRange

def toW {C : Type} [Field C] {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) : Int0 v →+* w.valuationSubring where
  toFun x := ⟨x, (hv x).1 x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def toV {C : Type} [Field C] {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) : w.valuationSubring →+* Int0 v where
  toFun x := ⟨x, (hv x).2 x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem ev_mk {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {S : Type} [Fintype S]
    [DecidableEq S] (b : S → Int0 v) (s : S) (g : Polynomial (Int0 v)) :
    ev b s (AdjoinRoot.mk _ g) = g.eval (b s) := by
  unfold ev
  rw [AdjoinRoot.liftAlgHom_mk]
  rfl

theorem evalVec_range : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (y : S → Fin N → C),
    y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y := by
  intro C _ w v hv S _ _ a N y
  constructor
  · intro hy
    choose f hf using hy
    refine ⟨fun i => AdjoinRoot.mk _ ((f i).map (toV hv)), ?_⟩
    funext s i
    simp only [evalVec]
    rw [ev_mk, Polynomial.eval_map, hf i s]
    have : liftA hv a s = toV hv (a s) := rfl
    rw [this, Polynomial.eval₂_hom]
    rfl
  · rintro ⟨x, rfl⟩ i
    obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective (x i)
    refine ⟨g.map (toW hv), fun s => ?_⟩
    simp only [evalVec]
    rw [← hg, ev_mk, Polynomial.eval_map]
    have : a s = toW hv (liftA hv a s) := rfl
    rw [this, Polynomial.eval₂_hom]
    rfl

end GlobalTheory.EvalVecRange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPolynomialEvalFreeLatticeIffExistsEvalStatement
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_polynomialEvalFreeLattice_iff_exists_eval : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (y : S → Fin N → C), y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y := by
  first | exact @GlobalTheory.EvalVecRange.evalVec_range | exact GlobalTheory.EvalVecRange.evalVec_range | (intros; apply GlobalTheory.EvalVecRange.evalVec_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiltrationPreimageIffEvalMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiltrationPreimageIffEvalMem
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.FilPreMem

theorem poly_mem (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C))
    (hF : ∀ x ∈ F, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.unif a x ∈ F) (f : Polynomial (Int0 v)) :
    ∀ y ∈ F, (fun s i => ((f.eval (liftA hv a s) : Int0 v) : C) * y s i) ∈ F := by
  induction f using Polynomial.induction_on with
  | C c =>
    intro y hy
    have := F.smul_mem (⟨(c : C), (hv _).1 c.2⟩ : w.valuationSubring) hy
    convert this using 1
    funext s i
    simp only [Polynomial.eval_C]
    rfl
  | add p q hp hq =>
    intro y hy
    have := F.add_mem (hp y hy) (hq y hy)
    convert this using 1
    funext s i
    simp only [Polynomial.eval_add, Subring.coe_add, Pi.add_apply, add_mul]
  | monomial n c h =>
    intro y hy
    have := hF _ (h y hy)
    convert this using 1
    funext s i
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.unif, Pi.smul_apply, smul_eq_mul, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Subring.coe_mul,
      Subring.coe_pow, pow_succ, liftA]
    ring

theorem filPre_mem_iff : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C)), (∀ x ∈ F, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.unif a x ∈ F) → ∀ x, x ∈ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F}) ↔ evalVec (liftA hv a) N x ∈ F := by
  intro C _ w v hv S _ _ a N F hF x
  let T : Submodule (RS (liftA hv a)) (Fin N → RS (liftA hv a)) :=
    { carrier := {x | evalVec (liftA hv a) N x ∈ F}
      zero_mem' := by
        show evalVec (liftA hv a) N 0 ∈ F
        have : evalVec (liftA hv a) N 0 = 0 := by
          funext s i; simp [evalVec]
        rw [this]; exact F.zero_mem
      add_mem' := by
        intro x y hx hy
        show evalVec (liftA hv a) N (x + y) ∈ F
        rw [evalVec_add]; exact F.add_mem hx hy
      smul_mem' := by
        intro r x hx
        show evalVec (liftA hv a) N (r • x) ∈ F
        induction r using AdjoinRoot.induction_on with
        | ih f =>
          have := poly_mem C w v hv S a N F hF f _ hx
          convert this using 1
          funext s i
          simp [evalVec, ev] }
  constructor
  · intro hx
    have : (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F}) ≤ T := Submodule.span_le.2 (fun y hy => hy)
    exact this hx
  · intro hx
    exact Submodule.subset_span hx

end GlobalTheory.FilPreMem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiltrationPreimageIffEvalMemStatement
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_filtrationPreimage_iff_eval_mem : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C)), (∀ x ∈ F, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.unif a x ∈ F) → ∀ x, x ∈ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F}) ↔ evalVec (liftA hv a) N x ∈ F := by
  first | exact @GlobalTheory.FilPreMem.filPre_mem_iff | exact GlobalTheory.FilPreMem.filPre_mem_iff | (intros; apply GlobalTheory.FilPreMem.filPre_mem_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalQuotientRingVectorAtPointsInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalQuotientRingVectorAtPointsInjective
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.HerbrandBridge

open Polynomial

theorem prod_X_sub_C_dvd_of_eval_zero {O S : Type} [CommRing O] [IsDomain O] [Fintype S]
    (b : S → O) (hb : Function.Injective b) (g : O[X]) (hg : ∀ s, g.eval (b s) = 0) :
    (∏ s, (X - C (b s))) ∣ g := by
  by_cases h0 : g = 0
  · simp [h0]
  have hprod : (∏ s, (X - C (b s))) = ((Finset.univ.val.map b).map (fun t => X - C t)).prod := by
    rw [Multiset.map_map]; rfl
  rw [hprod, Multiset.prod_X_sub_C_dvd_iff_le_roots h0]
  rw [Multiset.le_iff_subset (Multiset.Nodup.map hb Finset.univ.nodup)]
  intro t ht
  obtain ⟨s, -, rfl⟩ := Multiset.mem_map.1 ht
  exact (mem_roots h0).2 (hg s)

theorem evalVec_injective_of_injective (C : Type) [Field C] (w : Valuation C ℝ≥0)
    (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring)
    (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) :
    Function.Injective a → Function.Injective (evalVec (liftA hv a) N) := by
  intro ha
  have hinj : Function.Injective (liftA hv a) := by
    intro s t hst
    apply ha
    apply Subtype.ext
    have := congrArg (fun u : Int0 v => (u : C)) hst
    exact this
  have key : ∀ x : Fin N → RS (liftA hv a), evalVec (liftA hv a) N x = 0 → x = 0 := by
    intro x hx
    funext i
    obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective (x i)
    rw [Pi.zero_apply, ← hg, AdjoinRoot.mk_eq_zero]
    apply prod_X_sub_C_dvd_of_eval_zero _ hinj
    intro s
    have h1 := congrFun (congrFun hx s) i
    simp only [evalVec, Pi.zero_apply, ← hg] at h1
    apply Subtype.ext
    rw [show ((0 : Int0 v) : C) = 0 from rfl, ← h1]
    congr 1
  intro x y hxy
  have := key (x - y) (by rw [evalVec_sub, hxy, sub_self])
  exact sub_eq_zero.1 this

end GlobalTheory.HerbrandBridge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalQuotientRingVectorAtPointsInjectiveStatement
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalQuotientRingVectorAtPoints_injective : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ), Function.Injective a → Function.Injective (evalVec (liftA hv a) N) := by
  first | exact @GlobalTheory.HerbrandBridge.evalVec_injective_of_injective | exact GlobalTheory.HerbrandBridge.evalVec_injective_of_injective | (intros; apply GlobalTheory.HerbrandBridge.evalVec_injective_of_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieEigenSublatticeIffEvalFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieEigenSublatticeIffEvalFlat
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory

theorem lie_eigenSub_iff_flat : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a F → Function.Injective (evalVec (liftA hv a) N) → (∀ y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y) → (∀ x, x ∈ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F}) ↔ evalVec (liftA hv a) N x ∈ F) → (∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N, (∀ s, x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s) → x ∈ F) → ∀ z : (Fin N → C) ⧸ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F τ, z ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) F) τ ↔ ∃ x : Fin N → RS (liftA hv a), proj (liftA hv a) ((Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.eigSub (liftA hv a) τ ((Fin N → RS (liftA hv a)) ⧸ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) ∧ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.quotMap (w := w) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F τ) (fun i => ((GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.comp (liftA hv a) N τ x i : Int0 v) : C)) = z := by
  intro C _ w v hv S _ _ a N F τ hinj _hfilt _hevinj hrange hmem hlast z
  have hev : ∀ x : Fin N → RS (liftA hv a), ∀ s i,
      evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s i
        = ((a s : C) - a τ) * evalVec (liftA hv a) N x s i := by
    intro x s i
    simp only [evalVec, Pi.smul_apply, smul_eq_mul, map_mul, ev_lin]
    rfl
  have hevs : ∀ x : Fin N → RS (liftA hv a), ∀ s,
      evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s
        = ((a s : C) - a τ) • evalVec (liftA hv a) N x s := by
    intro x s; funext i; rw [hev]; rfl
  have heig : ∀ x : Fin N → RS (liftA hv a),
      proj (liftA hv a) ((Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) x ∈
          GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.eigSub (liftA hv a) τ ((Fin N → RS (liftA hv a)) ⧸ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) ↔
        evalVec (liftA hv a) N (lin (liftA hv a) τ • x) ∈ F := by
    intro x
    rw [← hmem]
    show lin (liftA hv a) τ • ((Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})).mkQ x = 0 ↔ _
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hlie : z ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub
        (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) F) τ ↔
      ∃ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N, ∀ s,
        (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s).mkQ (h s) =
          (Pi.single τ z : ∀ s, (Fin N → C) ⧸ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s) s := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie, Submodule.mem_comap,
      Submodule.mem_map]
    constructor
    · rintro ⟨h, hh, he⟩
      exact ⟨h, hh, fun s => congrFun he s⟩
    · rintro ⟨h, hh, he⟩
      exact ⟨h, hh, funext he⟩
  rw [hlie]
  constructor
  · rintro ⟨h, hh, he⟩
    obtain ⟨x, rfl⟩ := (hrange h).1 hh
    refine ⟨x, (heig x).2 ?_, ?_⟩
    · apply hlast _ ((hrange _).2 ⟨_, rfl⟩)
      intro s
      rw [hevs]
      by_cases hs : s = τ
      · rw [hs, sub_self, zero_smul]; exact zero_mem _
      · have h1 : evalVec (liftA hv a) N x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s := by
          have := he s
          rw [Pi.single_eq_of_ne hs, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
          exact this
        exact Submodule.smul_mem _ _ h1
    · have := he τ
      rw [Pi.single_eq_same] at this
      exact this
  · rintro ⟨x, hx, rfl⟩
    refine ⟨evalVec (liftA hv a) N x, (hrange _).2 ⟨x, rfl⟩, fun s => ?_⟩
    by_cases hs : s = τ
    · subst hs
      rw [Pi.single_eq_same]
      rfl
    · rw [Pi.single_eq_of_ne hs, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      have hy := (heig x).1 hx
      have hys : evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s ∈
          GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s :=
        Submodule.subset_span ⟨_, hy, rfl⟩
      have hne : (a s : C) - a τ ≠ 0 := sub_ne_zero.2 fun e => hs (hinj (Subtype.ext e))
      have : evalVec (liftA hv a) N x s =
          ((a s : C) - a τ)⁻¹ • evalVec (liftA hv a) N (lin (liftA hv a) τ • x) s := by
        rw [hevs, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ hys

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieEigenSublatticeIffEvalFlatStatement
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieEigenSublattice_iff_eval_flat : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a F → Function.Injective (evalVec (liftA hv a) N) → (∀ y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y) → (∀ x, x ∈ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F}) ↔ evalVec (liftA hv a) N x ∈ F) → (∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N, (∀ s, x s ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F s) → x ∈ F) → ∀ z : (Fin N → C) ⧸ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F τ, z ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) F) τ ↔ ∃ x : Fin N → RS (liftA hv a), proj (liftA hv a) ((Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.eigSub (liftA hv a) τ ((Fin N → RS (liftA hv a)) ⧸ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) ∧ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.quotMap (w := w) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace F τ) (fun i => ((GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.comp (liftA hv a) N τ x i : Int0 v) : C)) = z := by
  first | exact @GlobalTheory.lie_eigenSub_iff_flat | exact GlobalTheory.lie_eigenSub_iff_flat | (intros; apply GlobalTheory.lie_eigenSub_iff_flat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationHerbrandEigenspace
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity

namespace GlobalTheory.HerbrandBridge
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference (freeLattice unif IsFiltration filSpace eigenSub eigenQuot lie quotMap addVal)

theorem filPre_mem : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C)),
    (∀ x ∈ F, unif a x ∈ F) →
    ∀ x, x ∈ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F}) ↔ evalVec (liftA hv a) N x ∈ F :=
  GlobalTheory.T.mem_filtrationPreimage_iff_eval_mem

theorem evalVec_range : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (y : S → Fin N → C),
    y ∈ freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y :=
  GlobalTheory.T.mem_polynomialEvalFreeLattice_iff_exists_eval

theorem evalVec_injective : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ), Function.Injective a →
    Function.Injective (evalVec (liftA hv a) N) :=
  GlobalTheory.T.evalQuotientRingVectorAtPoints_injective

theorem eigenSub_iff : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (τ : S), Function.Injective a →
    Function.Injective (evalVec (liftA hv a) N) →
    (∀ y, y ∈ freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y) →
    ∀ y : Fin N → C, y ∈ eigenSub (W := fun _ => Fin N → C) (freeLattice a N) τ ↔
      ∃ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.eigSub (liftA hv a) τ (Fin N → RS (liftA hv a)),
        (fun i => ((GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.comp (liftA hv a) N τ z i : Int0 v) : C)) = y :=
  GlobalTheory.T.eigenSublattice_freeLattice_iff_eval

theorem mem_of_components : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (S : Type) [Fintype S]
    [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ)
    (F : Submodule w.valuationSubring (S → Fin N → C)), Function.Injective a → IsFiltration a F →
    ∀ x ∈ freeLattice a N, (∀ s, x s ∈ filSpace F s) → x ∈ F :=
  GlobalTheory.T.mem_filtration_of_components_mem_eigenSpan

theorem lie_iff : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C))
    (τ : S), Function.Injective a → IsFiltration a F →
    Function.Injective (evalVec (liftA hv a) N) →
    (∀ y, y ∈ freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y) →
    (∀ x, x ∈ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F}) ↔ evalVec (liftA hv a) N x ∈ F) →
    (∀ x ∈ freeLattice a N, (∀ s, x s ∈ filSpace F s) → x ∈ F) →
    ∀ z : (Fin N → C) ⧸ filSpace F τ, z ∈ eigenSub (lie (freeLattice a N) F) τ ↔
      ∃ x : Fin N → RS (liftA hv a),
        proj (liftA hv a) ((Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) x ∈
          GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.eigSub (liftA hv a) τ ((Fin N → RS (liftA hv a)) ⧸ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) ∧
        quotMap (w := w) (filSpace F τ) (fun i => ((GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.comp (liftA hv a) N τ x i : Int0 v) : C)) = z :=
  GlobalTheory.T.lieEigenSublattice_iff_eval_flat

end GlobalTheory.HerbrandBridge

namespace GlobalTheory.HerbrandBridge
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference (freeLattice unif IsFiltration filSpace eigenSub eigenQuot lie quotMap addVal
  DetRel IsLatticeBasis HasVal)

variable {C : Type} [Field C]

theorem span_eq_of_basis {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) {E E' W : Type} [AddCommGroup E]
    [Module (Int0 v) E] [AddCommGroup E'] [Module (Int0 v) E'] [AddCommGroup W] [Module C W]
    [Module w.valuationSubring W] [IsScalarTower w.valuationSubring C W] {ι : Type} [Fintype ι]
    (M : Submodule (Int0 v) E) (b : Module.Basis ι (Int0 v) M) (π : E' →ₗ[Int0 v] E) (g : E' → W)
    (hadd : ∀ x y, g (x + y) = g x + g y) (hsmul : ∀ (c : Int0 v) x, g (c • x) = (c : C) • g x)
    (hwd : ∀ x x', π x = π x' → g x = g x') (xs : ι → E') (hxs : ∀ i, π (xs i) = b i)
    (X : Submodule w.valuationSubring W) (hX : ∀ y, y ∈ X ↔ ∃ x, π x ∈ M ∧ g x = y) :
    Submodule.span w.valuationSubring (Set.range fun i => g (xs i)) = X := by
  let gh : E' →+ W := AddMonoidHom.mk' g hadd
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact (hX _).2 ⟨xs i, by rw [hxs i]; exact (b i).2, rfl⟩
  · intro y hy
    obtain ⟨x, hxM, rfl⟩ := (hX y).1 hy
    have hrep := b.sum_repr ⟨π x, hxM⟩
    have hπ : π x = π (∑ i, b.repr ⟨π x, hxM⟩ i • xs i) := by
      have h2 : π x = ∑ i, b.repr ⟨π x, hxM⟩ i • (b i : E) := by
        have := congrArg Subtype.val hrep
        simp only [Submodule.coe_sum, Submodule.coe_smul] at this
        exact this.symm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      conv_lhs => rw [h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hxs i]
    rw [hwd _ _ hπ]
    have : g (∑ i, b.repr ⟨π x, hxM⟩ i • xs i) = ∑ i, ((b.repr ⟨π x, hxM⟩ i : Int0 v) : C) • g (xs i) := by
      change gh _ = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => hsmul _ _
    rw [this]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hc : ((b.repr ⟨π x, hxM⟩ i : Int0 v) : C) ∈ w.valuationSubring := (hv _).1 (Subtype.prop _)
    have : ((b.repr ⟨π x, hxM⟩ i : Int0 v) : C) • g (xs i) =
        (⟨_, hc⟩ : w.valuationSubring) • g (xs i) := by
      rw [algebra_compatible_smul C (⟨_, hc⟩ : w.valuationSubring) (g (xs i))]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem linearIndependent_mkQ {p q : ℕ} (F : Submodule C (Fin (p + q) → C))
    (hF : Module.finrank C F = q) (u : Fin p → Fin (p + q) → C) (m : Fin q → Fin (p + q) → C)
    (hm : ∀ i, m i ∈ F) (hdet : (Matrix.of (Fin.append u m)).det ≠ 0) :
    LinearIndependent C (fun i => F.mkQ (u i)) := by
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have hli' : LinearIndependent C (Fin.append u m) := hli
  have hmli : LinearIndependent C m := by
    have := hli'.comp (Fin.natAdd p) (Fin.natAdd_injective q p)
    convert this using 1
    funext i; simp
  have hspan : Submodule.span C (Set.range m) = F := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hm i)
    · rw [finrank_span_eq_card hmli, Fintype.card_fin, hF]
  rw [linearIndependent_iff']
  intro s c hs i hi
  have h1 : ∑ j ∈ s, c j • u j ∈ F := by
    have : F.mkQ (∑ j ∈ s, c j • u j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; simp only [map_smul]; exact hs
    exact (Submodule.Quotient.mk_eq_zero F).1 this
  rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at h1
  obtain ⟨d, hd⟩ := h1
  let c' : Fin (p + q) → C := Fin.append (fun j => if j ∈ s then c j else 0) (fun k => - d k)
  have hsum : ∑ k, c' k • Fin.append u m k = 0 := by
    rw [Fin.sum_univ_add]
    simp only [c', Fin.append_left, Fin.append_right, neg_smul, Finset.sum_neg_distrib]
    rw [hd]
    simp only [ite_smul, zero_smul]
    rw [Finset.sum_ite_mem, Finset.univ_inter, add_neg_cancel]
  have := (Fintype.linearIndependent_iff.1 hli') c' hsum (Fin.castAdd q i)
  simpa [c', hi] using this

end GlobalTheory.HerbrandBridge

namespace GlobalTheory.HerbrandBridge
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference (freeLattice unif IsFiltration filSpace eigenSub eigenQuot lie quotMap addVal
  DetRel IsLatticeBasis HasVal)

variable {C : Type} [Field C] {S : Type} [Fintype S] [DecidableEq S]

theorem eigenQuot_iff {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (a : S → w.valuationSubring) (N : ℕ)
    (F : Submodule w.valuationSubring (S → Fin N → C)) (hle : F ≤ freeLattice a N)
    (hrange : ∀ y, y ∈ freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y)
    (hmem : ∀ x, x ∈ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F}) ↔ evalVec (liftA hv a) N x ∈ F) (s : S)
    (y : Fin N → C) :
    y ∈ eigenQuot (W := fun _ => Fin N → C) F s ↔
      ∃ z ∈ eigQuot (liftA hv a) ((Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) s, (fun i => (z i : C)) = y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨z, hz⟩ := (hrange x).1 (hle hx)
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.comp (liftA hv a) N s z, ⟨z, (hmem z).2 (hz ▸ hx), rfl⟩, ?_⟩
    rw [comp_coe, hz]; rfl
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, (hmem z).1 hz, rfl⟩

theorem eigRank_eq {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (a : S → w.valuationSubring) (N : ℕ)
    (F : Submodule w.valuationSubring (S → Fin N → C)) (hle : F ≤ freeLattice a N)
    (hrange : ∀ y, y ∈ freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y)
    (hmem : ∀ x, x ∈ (Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F}) ↔ evalVec (liftA hv a) N x ∈ F) (s : S) :
    eigRank v (liftA hv a) ((Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) s = Module.finrank C (filSpace F s) := by
  have : ((fun (x : Fin N → Int0 v) (i : Fin N) => (x i : C)) ''
      (eigQuot (liftA hv a) ((Submodule.span (RS (liftA hv a)) {x : Fin _ → RS (liftA hv a) | (fun s i => ↑(ev (liftA hv a) s (x i))) ∈ F})) s : Set (Fin N → Int0 v))) =
      (eigenQuot (W := fun _ => Fin N → C) F s : Set (Fin N → C)) := by
    ext y
    simp only [Set.mem_image, SetLike.mem_coe]
    rw [eigenQuot_iff hv a N F hle hrange hmem s y]
  unfold eigRank filSpace
  rw [this]

end GlobalTheory.HerbrandBridge

namespace GlobalTheory.HerbrandBridge
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference (freeLattice unif IsFiltration filSpace eigenSub eigenQuot lie quotMap addVal
  DetRel IsLatticeBasis HasVal)

variable {C : Type} [Field C] {S : Type} [Fintype S] [DecidableEq S]

theorem yExp_eq (w : Valuation C ℝ≥0) (ℓ : C) (h0 : 0 < w ℓ) (h1 : w ℓ < 1)
    (hv : ∀ x, x ∈ Int0 (toAddVal w ℓ h0 h1) ↔ x ∈ w.valuationSubring)
    (a : S → w.valuationSubring) (ha : Function.Injective a) {N : ℕ}
    (F : Submodule (RS (liftA hv a)) (Fin N → RS (liftA hv a))) (G : S → Submodule C (Fin N → C))
    (hrk : ∀ s, eigRank (toAddVal w ℓ h0 h1) (liftA hv a) F s = Module.finrank C (G s)) (τ : S) :
    yExp (toAddVal w ℓ h0 h1) (liftA hv a) F τ =
      ((∑ s ∈ Finset.univ.erase τ, (Module.finrank C (G s) : ℝ) *
        addVal w ℓ ((a τ : C) - (a s : C)) : ℝ) : WithTop ℝ) := by
  unfold yExp
  rw [WithTop.coe_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [hrk s]
  have hne : (a s : C) - (a τ : C) ≠ 0 := by
    intro h
    exact (Finset.ne_of_mem_erase hs) (ha (Subtype.ext (sub_eq_zero.1 h)))
  change _ • toAddVal w ℓ h0 h1 ((a s : C) - (a τ : C)) = _
  rw [toAddVal_of_ne _ _ _ _ hne, ← WithTop.coe_nsmul, nsmul_eq_mul]
  congr 2
  unfold addVal
  rw [w.map_sub_swap]

end GlobalTheory.HerbrandBridge

namespace GlobalTheory.HerbrandBridge
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference (freeLattice unif IsFiltration filSpace eigenSub eigenQuot lie quotMap addVal
  DetRel IsLatticeBasis HasVal)

theorem exForm : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 →
    ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ)
    (Fil : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S), Function.Injective a →
    GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a Fil →
    Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ) = q →
    GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ)
      (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin (p + q) → C)
        (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) τ)
      (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub
        (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) Fil) τ)
      (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ)
      (∑ s ∈ Finset.univ.erase τ, (Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) : ℝ) *
        GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal w ℓ ((a τ : C) - (a s : C))) := by
  intro C _ w ℓ h0 h1 S _ _ a p q Fil τ ha hF hq
  have hv := mem_addValuationIntegerRing_normalized_iff w ℓ h0 h1
  have ha' : Function.Injective (liftA hv a) := fun s t h =>
    ha (Subtype.ext (congrArg (fun z : Int0 (toAddVal w ℓ h0 h1) => (z : C)) h))
  let P := filPre (liftA hv a) (N := p + q) Fil
  have hmem (x : Fin (p + q) → RS (liftA hv a)) : x ∈ P ↔ evalVec (liftA hv a) (p + q) x ∈ Fil :=
    filPre_mem C w _ hv S a (p + q) Fil hF.stable x
  have hrange := evalVec_range C w _ hv S a (p + q)
  have hinj := evalVec_injective C w _ hv S a (p + q) ha
  have hcomp := mem_of_components C w S a (p + q) Fil ha hF
  have hsat : ∀ (c : Int0 (toAddVal w ℓ h0 h1)) (x : Fin (p + q) → RS (liftA hv a)), c ≠ 0 →
      c • x ∈ P → x ∈ P := by
    intro c x hc hcx
    rw [hmem] at hcx ⊢
    have hc' : (c : C) ∈ w.valuationSubring := (hv _).1 c.2
    refine hF.saturated _ ((hrange _).2 ⟨x, rfl⟩) ⟨(c : C), hc'⟩ ?_ ?_
    · intro h
      apply hc
      exact Subtype.ext (congrArg (fun z : w.valuationSubring => (z : C)) h)
    · convert hcx using 1
      rw [evalVec_smul]
      rfl
  have hrk (s : S) : eigRank (toAddVal w ℓ h0 h1) (liftA hv a) P s =
      Module.finrank C (filSpace Fil s) :=
    eigRank_eq hv a (p + q) Fil hF.le hrange hmem s
  have hy := yExp_eq w ℓ h0 h1 hv a ha (N := p + q) P (filSpace Fil) hrk τ
  obtain ⟨⟨p', hp', ⟨h⟩, ⟨l⟩, ⟨f⟩, hDet⟩, -, -⟩ :=
    GlobalTheory.T.herbrandQuotient_eigen_det C (toAddVal w ℓ h0 h1) S (liftA hv a) ha' (p + q) P hsat τ
  have hq' : eigRank (toAddVal w ℓ h0 h1) (liftA hv a) P τ = q :=
    (hrk τ).trans hq
  have hpp : p = p' := by omega
  subst p'

  choose x hx using fun i : Fin p => Submodule.Quotient.mk_surjective P
    (l i : (Fin (p + q) → RS (liftA hv a)) ⧸ P)
  let e : Fin (p + q) ≃ Fin p ⊕ Fin (eigRank (toAddVal w ℓ h0 h1) (liftA hv a) P τ) :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) (finCongr hq'.symm))
  obtain ⟨c, hc, hne, hdet⟩ := hDet h l x hx f e
  let X : Fin (p + q) → Fin (p + q) → C := fun k i =>
    ((GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.comp (liftA hv a) (p + q) τ (h k : Fin (p + q) → RS (liftA hv a)) i : Int0 (toAddVal w ℓ h0 h1)) : C)
  let U : Fin p → Fin (p + q) → C := fun k i => ((GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.comp (liftA hv a) (p + q) τ (x k) i : Int0 (toAddVal w ℓ h0 h1)) : C)
  let fb := f.reindex (finCongr hq')
  let M : Fin q → Fin (p + q) → C := fun k i => ((fb k : Fin (p + q) → Int0 (toAddVal w ℓ h0 h1)) i : C)
  have hXmat : Matrix.of X = (Matrix.of fun k => GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.comp (liftA hv a) (p + q) τ
      (h k : Fin (p + q) → RS (liftA hv a))).map (Int0 (toAddVal w ℓ h0 h1)).subtype := rfl
  have hAmat : Matrix.of (Fin.append U M) = (Matrix.of fun k => Sum.elim
      (fun i => GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.comp (liftA hv a) (p + q) τ (x i)) (fun i => (f i : Fin (p + q) → Int0 (toAddVal w ℓ h0 h1))) (e k)).map
      (Int0 (toAddVal w ℓ h0 h1)).subtype := by
    ext k j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simp [e, U]
    · simp [e, M, fb, Module.Basis.reindex_apply]
  have hdet' : (Matrix.of X).det = c * (Matrix.of (Fin.append U M)).det := by
    rw [hXmat, hAmat, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      ← RingHom.map_det]
    exact hdet
  have hc0 : c ≠ 0 := by
    intro h0'
    rw [h0', AddValuation.map_zero, hy] at hc
    exact WithTop.top_ne_coe hc
  have hAne : (Matrix.of (Fin.append U M)).det ≠ 0 := by
    rw [hAmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    intro h'
    exact hne (Subtype.ext h')
  have hXne : (Matrix.of X).det ≠ 0 := by
    rw [hdet']
    exact mul_ne_zero hc0 hAne
  have hli : LinearIndependent C (Fin.append U M) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hAne
  have hMli : LinearIndependent C M := by
    have := hli.comp (Fin.natAdd p) (Fin.natAdd_injective q p)
    convert this using 1
    funext i; simp
  have hMq : ∀ k, M k ∈ eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ := fun k =>
    (eigenQuot_iff hv a (p + q) Fil hF.le hrange hmem τ (M k)).2 ⟨_, (fb k).2, rfl⟩
  have hMF : ∀ k, M k ∈ filSpace Fil τ := fun k => Submodule.subset_span (hMq k)

  refine ⟨X, U, M, c, ⟨Matrix.linearIndependent_rows_of_det_ne_zero hXne, ?_⟩,
    ⟨linearIndependent_mkQ (filSpace Fil τ) hq U M hMF hAne, ?_⟩, ⟨hMli, ?_⟩, hMF,
    ⟨hc0, ?_⟩, hdet'⟩
  · refine span_eq_of_basis hv (GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.eigSub (liftA hv a) τ (Fin (p + q) → RS (liftA hv a))) h
      LinearMap.id (fun z i => ((GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.comp (liftA hv a) (p + q) τ z i : Int0 (toAddVal w ℓ h0 h1)) : C))
      (fun z z' => by funext i; simp only [map_add (f := _), Pi.add_apply]; rfl)
      (fun c z => by funext i; simp only [map_smul, Pi.smul_apply, smul_eq_mul]; rfl)
      (fun z z' hz => by rw [show z = z' from hz])
      (fun k => (h k : Fin (p + q) → RS (liftA hv a))) (fun k => rfl) _ (fun y => ?_)
    rw [eigenSub_iff C w _ hv S a (p + q) τ ha hinj hrange y]
    simp only [LinearMap.id_apply]
  · refine span_eq_of_basis hv (GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.eigSub (liftA hv a) τ ((Fin (p + q) → RS (liftA hv a)) ⧸ P)) l (proj (liftA hv a) P)
      (fun z => quotMap (w := w) (filSpace Fil τ)
        (fun i => ((GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.comp (liftA hv a) (p + q) τ z i : Int0 (toAddVal w ℓ h0 h1)) : C)))
      (fun z z' => by
        rw [← map_add (f := _)]; congr 1; funext i; simp only [map_add (f := _), Pi.add_apply]; rfl)
      (fun c z => by
        show (filSpace Fil τ).mkQ _ = (c : C) • (filSpace Fil τ).mkQ _
        rw [← map_smul]; congr 1; funext i; simp only [map_smul, Pi.smul_apply, smul_eq_mul]; rfl)
      (fun z z' hz => ?_) x hx _ (fun y => ?_)
    · show (filSpace Fil τ).mkQ _ = (filSpace Fil τ).mkQ _
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      have h2 : z - z' ∈ P :=
        (Submodule.Quotient.eq P).1 hz
      rw [hmem, evalVec_sub] at h2
      refine Submodule.subset_span ⟨_, h2, ?_⟩
      funext i
      rfl
    · exact lie_iff C w _ hv S a (p + q) Fil τ ha hF hinj hrange hmem hcomp y
  · exact span_eq_of_basis hv (eigQuot (liftA hv a) P τ) fb
      LinearMap.id (fun z i => ((z i : Int0 (toAddVal w ℓ h0 h1)) : C))
      (fun z z' => by funext i; rfl) (fun c z => by funext i; rfl)
      (fun z z' hz => congrArg (fun z i => (z i : C)) hz)
      (fun k => (fb k : Fin (p + q) → Int0 (toAddVal w ℓ h0 h1))) (fun _ => rfl)
      (eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ)
      (eigenQuot_iff hv a (p + q) Fil hF.le hrange hmem τ)
  · rw [hy, toAddVal_of_ne _ _ _ _ hc0] at hc
    exact WithTop.coe_injective hc

end GlobalTheory.HerbrandBridge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationHerbrandEigenspaceStatement
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeDetRelation_herbrand_eigenspace : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ) (Fil : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a Fil → Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ) = q → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.DetRel w ℓ (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin (p + q) → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) τ) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) Fil) τ) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ) (∑ s ∈ Finset.univ.erase τ, (Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal w ℓ ((a τ : C) - (a s : C))) := by
  first | exact @GlobalTheory.HerbrandBridge.exForm | exact GlobalTheory.HerbrandBridge.exForm | (intros; apply GlobalTheory.HerbrandBridge.exForm <;> assumption)
end
