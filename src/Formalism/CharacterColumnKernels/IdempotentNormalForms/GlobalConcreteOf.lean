module

public import Formalism.CharacterColumnKernels.IdempotentNormalForms.GenFin
public import Formalism.CharacterColumnKernels.StatOntoLattice

@[expose] public section

section -- merged from Formalism.CharacterColumnKernels.IdempotentNormalForms.GlobalConcreteOf
section -- merged from Formalism.CharacterColumnKernels.IdempotentNormalForms.VccSpan
open Finset

namespace Formalism.NG

theorem descent : StatDescent := by
  intro O _ X X' T T' Z p q b hexp hind f' hf' hvan π'
  obtain ⟨a, haT, rfl⟩ := hexp f' hf'
  have hker : ∀ k, (⟨a k, haT k⟩ : T) ∈ ccIdeal T Z := by
    intro k
    rw [ccIdeal, RingHom.mem_ker]
    funext x
    have hx : x.1 ∉ Z := x.2
    have h0 := hind x.1 hx (fun k => a k x.1) (fun x' hx' => by
      have e := hvan x' (by rw [hx']; exact hx)
      simpa [hx', Finset.sum_apply, Pi.mul_apply, Function.comp] using e)
    have e2 := congrFun h0 k
    simpa [resOff] using e2
  rw [Finset.sum_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  simp only [Pi.mul_apply, Function.comp_apply]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, hker k, rfl⟩)

theorem vccSpan : StatVccSpan := by
  intro O _ _ _ X T Z x y hy
  induction hy using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨c, hc, rfl⟩ := hs
    exact iInf₂_le c hc
  | zero => simp
  | add a b _ _ ha hb =>
    exact le_trans (le_min ha hb) IsDiscreteValuationRing.addVal_add
  | smul r a _ ha =>
    rw [smul_eq_mul, IsDiscreteValuationRing.addVal_mul]
    exact le_trans ha le_add_self

end Formalism.NG
end

open Finset

noncomputable section

namespace Formalism.NG

namespace GlobalDeterminantRelations

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type*}
  {d : Type} [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
  (x' : X')

lemma evalSp_smul (r : R') (v : EvalSp O d R' x') (a : d) :
    (r • v : d → FractionRing O) a =
      ∑ b, (r : X' → Matrix d d (FractionRing O)) x' a b * (v : d → FractionRing O) b := rfl

instance : SMulCommClass R' (FractionRing O) (EvalSp O d R' x') where
  smul_comm r c v := by
    funext a
    change (∑ b, (r : X' → Matrix d d (FractionRing O)) x' a b * (c * (v : d → FractionRing O) b)) =
      c * ∑ b, (r : X' → Matrix d d (FractionRing O)) x' a b * (v : d → FractionRing O) b
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

instance : FiniteDimensional (FractionRing O) (EvalSp O d R' x') :=
  inferInstanceAs (FiniteDimensional (FractionRing O) (d → FractionRing O))

def curryE (g : Type) : (g × d → FractionRing O) ≃ₗ[FractionRing O] (g → EvalSp O d R' x') where
  toFun v i a := v (i, a)
  invFun w q := (w q.1 : d → FractionRing O) q.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

lemma det_relMap_eq (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R') :
    LinearMap.det (relMap (FractionRing O) (EvalSp O d R' x') Θ) =
      (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det := by
  have hconj := LinearMap.det_conj (relMap (FractionRing O) (EvalSp O d R' x') Θ) (curryE R' x' g).symm
  rw [← hconj, ← LinearMap.det_toLin']
  congr 1
  apply LinearMap.ext
  intro v
  funext p
  obtain ⟨i, a⟩ := p
  let ev : EvalSp O d R' x' →+ FractionRing O :=
    { toFun := fun w => (w : d → FractionRing O) a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  show ev (∑ j, Θ i j • (curryE R' x' g v) j) =
    Matrix.mulVec (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ) v (i, a)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have hev : ∀ j, ev (Θ i j • (curryE R' x' g v) j) =
      ∑ b, (Θ i j : X' → Matrix d d (FractionRing O)) x' a b * v (j, b) := fun j =>
    evalSp_smul R' x' (Θ i j) ((curryE R' x' g v) j) a
  rw [Finset.sum_congr rfl (fun j _ => hev j), Matrix.mulVec]
  first
    | (rw [dotProduct, Fintype.sum_prod_type]; rfl)
    | (rw [Matrix.dotProduct, Fintype.sum_prod_type]; rfl)
    | (simp only [dotProduct, Fintype.sum_prod_type]; rfl)

end GlobalDeterminantRelations

universe u v w

open GlobalDeterminantRelations in
theorem globalConcrete_of (hD : StatDescent.{u, v, w}) (hV : StatVccSpan.{u, v}) :
    CharacterColumnGlobal.{u, v, w} := by
  intro O _ _ _ X X' T T' Z p q b hT hZ d _ _ R' m g _ _ _ P hdet hφ π' ρπ hρπ α _ _ bl hbl ρk
    hsurj hblk hcard
  classical
  obtain ⟨C, hC⟩ := genericFin R' O m g α (fun k => {a // bl a = k}) hcard ρk hsurj P
  obtain ⟨f, hfT, hf⟩ := hdet (C * P)
  have hcomp : ∀ (x' : X') (v : g → EvalSp O d R' x'),
      relMap (FractionRing O) (EvalSp O d R' x') (C * P) v =
        relMap (FractionRing O) (EvalSp O d R' x') C (relMap (FractionRing O) (EvalSp O d R' x') P v) := by
    intro x' v
    funext i
    show ∑ j, (C * P) i j • v j = ∑ l, C i l • ∑ j, P l j • v j
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  have hvanish : ∀ x', p x' ∉ Z → f x' = 0 := by
    intro x' hx
    obtain ⟨φ, hφ0⟩ := hφ x' hx
    let e := (homEquiv P : (Coker P →ₗ[R'] EvalSp O d R' x') ≃ₗ[FractionRing O]
      LinearMap.ker (relMap (FractionRing O) (EvalSp O d R' x') P))
    have hne : e φ ≠ 0 := fun h => hφ0 (e.injective (h.trans (map_zero e).symm))
    have hv0 : ((e φ : LinearMap.ker _) : g → EvalSp O d R' x') ≠ 0 := fun h => hne (Subtype.ext h)
    have hvk := LinearMap.mem_ker.mp (e φ).2
    have hnot : ¬ Function.Injective (relMap (FractionRing O) (EvalSp O d R' x') (C * P)) := by
      intro hinj
      apply hv0
      apply hinj
      rw [hcomp, hvk, map_zero, map_zero]
    have hdet0 : LinearMap.det (relMap (FractionRing O) (EvalSp O d R' x') (C * P)) = 0 := by
      by_contra hne'
      apply hnot
      have hu : IsUnit (relMap (FractionRing O) (EvalSp O d R' x') (C * P)) :=
        (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne')
      exact ((Module.End.isUnit_iff _).mp hu).injective
    rw [GlobalDeterminantRelations.det_relMap_eq] at hdet0
    apply IsFractionRing.injective O (FractionRing O)
    rw [hf x', hdet0, map_zero]
  have hspan := hD O X X' T T' Z p q b hT hZ f hfT hvanish π'
  refine (hV O X T Z (p π') (f π') hspan).trans (le_of_eq ?_)
  have hfπ : f π' = (bigMat (fun r : R' => ρπ r) (C * P)).det := by
    apply IsFractionRing.injective O (FractionRing O)
    rw [hf π', RingHom.map_det]
    congr 1
    refine Matrix.ext fun x y => ?_
    simp [bigMat, RingHom.mapMatrix_apply, ← hρπ]
  rcases isEmpty_or_nonempty g with hg | hg
  · have h1 : f π' = 1 := by
      rw [hfπ]
      exact Matrix.det_isEmpty
    rw [h1, IsDiscreteValuationRing.addVal_one]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Module.length_eq_zero_iff]
    exact ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  have hBT : (bigMat (fun r : R' => ρπ r) (C * P)).BlockTriangular (fun x : g × d => bl x.2) := by
    intro x y hxy
    exact hbl _ hxy
  have himage : (Finset.univ.image fun x : g × d => bl x.2) = Finset.univ.image bl := by
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨a, ha⟩
      exact ⟨(Classical.arbitrary g, a), ha⟩
  have hprod : ∀ (s : Finset α) (F : α → O), IsDiscreteValuationRing.addVal O (∏ k ∈ s, F k) =
      ∑ k ∈ s, IsDiscreteValuationRing.addVal O (F k) := by
    intro s F
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.prod_empty, Finset.sum_empty, IsDiscreteValuationRing.addVal_one]
    · intro a s ha ih
      rw [Finset.prod_insert ha, Finset.sum_insert ha, IsDiscreteValuationRing.addVal_mul, ih]
  have hblock : ∀ k, ((bigMat (fun r : R' => ρπ r) (C * P)).toSquareBlock
      (fun x : g × d => bl x.2) k).det = (bigMat (fun r : R' => ρk k r) (C * P)).det := by
    intro k
    let eK : g × {a // bl a = k} ≃ {x : g × d // bl x.2 = k} :=
      { toFun := fun y => ⟨(y.1, y.2.1), y.2.2⟩
        invFun := fun x => (x.1.1, ⟨x.1.2, x.2⟩)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← Matrix.det_reindex_self eK.symm]
    congr 1
    refine Matrix.ext fun x y => ?_
    obtain ⟨pp, i⟩ := x
    obtain ⟨qq, j⟩ := y
    show _ = (ρk k) ((C * P) pp qq) i j
    rw [← hblk]
    rfl
  rw [hfπ, hBT.det, hprod, himage]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hblock k, ← (lenKer : StatLenKer) O _ (bigMat (fun r : R' => ρk k r) (C * P))]
  exact hC k

theorem globalConcrete : CharacterColumnGlobal := globalConcrete_of descent vccSpan

end Formalism.NG
end
end

section -- merged from Formalism.CharacterColumnKernels.IdempotentNormalForms.IdemNormalForm
open Module

noncomputable section

namespace Formalism.NG

theorem burnside : StatBurnside := by
  intro k A V _ _ _ _ _ _ _ _ hS hsc f
  classical
  have := hS
  let F : Module.End (Module.End A V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => by
        obtain ⟨c, hc⟩ := hsc φ
        simp only [Module.End.smul_def, hc, RingHom.id_apply, f.map_smul] }
  obtain ⟨a, ha⟩ := jacobson_density F (Finset.univ.image (Module.finBasis k V))
  refine ⟨a, (Module.finBasis k V).ext fun i => ?_⟩
  have := ha (Module.finBasis k V i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  simpa [F] using this.symm

section RankMod

variable {O : Type*} [CommRing O] {r : Type} [Fintype r] [DecidableEq r]

end RankMod

end Formalism.NG
end
end

section -- merged from Formalism.CharacterColumnKernels.IdempotentNormalForms.MemCcIdealIffForall
open Finset

noncomputable section

namespace Formalism.NG

theorem mem_ccIdeal_iff_forall {O : Type*} [CommRing O] {X : Type*} (T : Subalgebra O (X → O))
    (Z : Set X) (c : T) : c ∈ ccIdeal T Z ↔ ∀ x ∉ Z, (c : X → O) x = 0 := by
  unfold ccIdeal
  rw [RingHom.mem_ker]
  constructor
  · intro h x hx
    have := congrFun h ⟨x, hx⟩
    simpa [resOff] using this
  · intro h
    funext x
    simp [resOff, h x.1 x.2]

theorem vccBaseChange : StatVccBaseChange := by
  intro O O' _ _ _ _ _ _ _ _ _ e he X T T' hT' Z x
  classical
  set b := Module.Free.chooseBasis O O' with hb
  set φ : (X → O) → (X → O') := fun f => algebraMap O O' ∘ f with hφ
  have hdec : ∀ f ∈ Submodule.span O' (φ '' (T : Set (X → O))),
      ∃ g : Module.Free.ChooseBasisIndex O O' → (X → O), (∀ j, g j ∈ T) ∧ f = ∑ j, b j • φ (g j) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨t, ht, rfl⟩ := hf
      refine ⟨fun j => b.repr 1 j • t, fun j => T.smul_mem ht _, ?_⟩
      funext x'
      simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
      calc algebraMap O O' (t x') = algebraMap O O' (t x') * ∑ j, b.repr 1 j • b j := by
            rw [b.sum_repr, mul_one]
        _ = ∑ j, b j * algebraMap O O' (b.repr 1 j * t x') := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Algebra.smul_def, map_mul]
            ring
    | zero =>
      refine ⟨0, fun j => T.zero_mem, ?_⟩
      funext x'
      simp [hφ]
    | add f f' _ _ hf hf' =>
      obtain ⟨g, hg, rfl⟩ := hf
      obtain ⟨g', hg', rfl⟩ := hf'
      refine ⟨g + g', fun j => T.add_mem (hg j) (hg' j), ?_⟩
      funext x'
      simp only [hφ, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
        map_add, mul_add, Finset.sum_add_distrib]
    | smul o f _ hf =>
      obtain ⟨g, hg, rfl⟩ := hf
      refine ⟨fun k => ∑ j, b.repr (o * b j) k • g j, fun k => T.sum_mem fun j _ => T.smul_mem (hg j) _, ?_⟩
      funext x'
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, map_sum, map_mul]
      calc o * ∑ j, b j * algebraMap O O' (g j x') = ∑ j, (o * b j) * algebraMap O O' (g j x') := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ = ∑ j, (∑ k, b.repr (o * b j) k • b k) * algebraMap O O' (g j x') := by
            simp_rw [b.sum_repr]
        _ = ∑ k, b k * ∑ j, algebraMap O O' (b.repr (o * b j) k) * algebraMap O O' (g j x') := by
            simp only [Finset.sum_mul, Finset.mul_sum, Algebra.smul_def]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  have hvan : ∀ (g : Module.Free.ChooseBasisIndex O O' → X → O) (x' : X),
      ∑ j, b j * algebraMap O O' (g j x') = 0 → ∀ j, g j x' = 0 := by
    intro g x' h
    have h2 : ∑ j, g j x' • b j = 0 := by
      rw [← h]
      exact Finset.sum_congr rfl fun j _ => by rw [Algebra.smul_def, mul_comm]
    exact Fintype.linearIndependent_iff.mp b.linearIndependent _ h2
  apply le_antisymm
  · have hne : ((fun c : T => IsDiscreteValuationRing.addVal O ((c : X → O) x)) ''
        (ccIdeal T Z : Set T)).Nonempty := ⟨_, 0, (ccIdeal T Z).zero_mem, rfl⟩
    obtain ⟨c0, hc0, hc0eq⟩ := csInf_mem hne
    have hvcc : vcc T Z x = IsDiscreteValuationRing.addVal O ((c0 : X → O) x) := by
      rw [show IsDiscreteValuationRing.addVal O ((c0 : X → O) x) = _ from hc0eq, sInf_image]
      rfl
    rw [hvcc, ← he]
    have hmem : φ (c0 : X → O) ∈ T' := by
      have h1 : φ (c0 : X → O) ∈ (T' : Set (X → O')) := by
        rw [hT']
        exact Submodule.subset_span ⟨c0, c0.2, rfl⟩
      exact h1
    have hc0' : (⟨φ (c0 : X → O), hmem⟩ : T') ∈ ccIdeal T' Z := by
      rw [mem_ccIdeal_iff_forall]
      intro x' hx'
      have h0 := (mem_ccIdeal_iff_forall T Z c0).mp hc0 x' hx'
      simp [hφ, h0]
    exact iInf₂_le _ hc0'
  · unfold vcc
    refine le_iInf₂ fun c' hc' => ?_
    have hc'span : (c' : X → O') ∈ Submodule.span O' (φ '' (T : Set (X → O))) := by
      have h1 : (c' : X → O') ∈ (T' : Set (X → O')) := c'.2
      rw [hT'] at h1
      exact h1
    obtain ⟨g, hg, hgeq⟩ := hdec _ hc'span
    have hgZ : ∀ j, (⟨g j, hg j⟩ : T) ∈ ccIdeal T Z := by
      intro j
      rw [mem_ccIdeal_iff_forall]
      intro x' hx'
      have h0 := (mem_ccIdeal_iff_forall T' Z c').mp hc' x' hx'
      rw [hgeq] at h0
      simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at h0
      exact hvan g x' h0 j
    rw [hgeq]
    simp only [hφ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    refine AddValuation.map_le_sum _ fun j _ => ?_
    rw [AddValuation.map_mul, he]
    refine le_trans ?_ le_add_self
    exact mul_le_mul_of_nonneg_left (iInf₂_le (⟨g j, hg j⟩ : T) (hgZ j)) (zero_le)

end Formalism.NG
end
end
