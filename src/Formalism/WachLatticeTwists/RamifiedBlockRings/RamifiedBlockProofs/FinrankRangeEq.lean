module

public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaDetPoly
public import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.Normal
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsBasisOfPid
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.BridgeDet
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.IsUnitDetOfConst

@[expose] public section

section -- merged from Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.RankDiagIte
section -- merged from Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.CMemPolyT
section -- merged from Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.RingDataObjects
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

section Span
variable {O K : Type} [CommRing O] [CommRing K] [Algebra O K] {X : Type} (T : Subalgebra O (X → O))
  {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Monoid G] (r : G →* (X → Matrix d d K))

def term (c : X → O) (g : G) : X → Matrix d d K := fun x => algebraMap O K (c x) • r g x

theorem term_add (c c' : X → O) (g : G) : term r (c + c') g = term r c g + term r c' g := by
  funext x
  simp [term, add_smul]

theorem term_zero (g : G) : term r (0 : X → O) g = 0 := by
  funext x
  simp [term]

theorem term_mul (c c' : X → O) (g g' : G) : term r c g * term r c' g' = term r (c * c') (g * g') := by
  funext x
  simp only [term, Pi.mul_apply, map_mul]
  first
  | exact smul_mul_smul_comm _ _ _ _
  | exact smul_mul_smul _ _ _ _
  | simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]

theorem mem_tSpan_iff (F : X → Matrix d d K) :
    F ∈ tSpan T r ↔ ∃ (s : Finset G) (c : G → X → O), (∀ g, c g ∈ T) ∧ F = ∑ g ∈ s, term r (c g) g := Iff.rfl

theorem term_mem {c : X → O} (hc : c ∈ T) (g : G) : term r c g ∈ tSpan T r := (mem_tSpan_iff T r _).2 ⟨{g}, fun _ => c, fun _ => hc, by simp⟩

theorem zero_mem_tSpan : (0 : X → Matrix d d K) ∈ tSpan T r := (mem_tSpan_iff T r 0).2 ⟨∅, fun _ => 0, fun _ => T.zero_mem, by simp⟩

theorem add_mem_tSpan {F F' : X → Matrix d d K} (h : F ∈ tSpan T r) (h' : F' ∈ tSpan T r) :
    F + F' ∈ tSpan T r := by
  classical
  obtain ⟨s, c, hc, rfl⟩ := (mem_tSpan_iff T r _).1 h
  obtain ⟨s', c', hc', rfl⟩ := (mem_tSpan_iff T r _).1 h'
  refine (mem_tSpan_iff T r _).2 ⟨s ∪ s', fun g => (if g ∈ s then c g else 0) + (if g ∈ s' then c' g else 0),
    fun g => T.add_mem (by split_ifs; exacts [hc g, T.zero_mem]) (by split_ifs; exacts [hc' g, T.zero_mem]), ?_⟩
  simp only [term_add, Finset.sum_add_distrib]
  congr 1
  · refine (Finset.sum_congr rfl fun g hg => ?_).trans (Finset.sum_subset Finset.subset_union_left fun g _ hg => ?_)
    · rw [if_pos hg]
    · rw [if_neg hg, term_zero]
  · refine (Finset.sum_congr rfl fun g hg => ?_).trans (Finset.sum_subset Finset.subset_union_right fun g _ hg => ?_)
    · rw [if_pos hg]
    · rw [if_neg hg, term_zero]

theorem sum_mem_tSpan {ι : Type*} (s : Finset ι) (F : ι → X → Matrix d d K)
    (h : ∀ i ∈ s, F i ∈ tSpan T r) : ∑ i ∈ s, F i ∈ tSpan T r := Finset.sum_induction _ (· ∈ tSpan T r) (fun _ _ ha hb => add_mem_tSpan T r ha hb)
  (zero_mem_tSpan T r) h

theorem mul_mem_tSpan {F F' : X → Matrix d d K} (h : F ∈ tSpan T r) (h' : F' ∈ tSpan T r) :
    F * F' ∈ tSpan T r := by
  obtain ⟨s, c, hc, rfl⟩ := (mem_tSpan_iff T r _).1 h
  obtain ⟨s', c', hc', rfl⟩ := (mem_tSpan_iff T r _).1 h'
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact sum_mem_tSpan T r _ _ fun g _ => sum_mem_tSpan T r _ _ fun g' _ => by
    rw [term_mul]
    exact term_mem T r (T.mul_mem (hc _) (hc' _)) _

theorem smul_mem_tSpan {f : X → O} (hf : f ∈ T) {F : X → Matrix d d K} (h : F ∈ tSpan T r) :
    (fun x => algebraMap O K (f x) • F x) ∈ tSpan T r := by
  obtain ⟨s, c, hc, rfl⟩ := (mem_tSpan_iff T r _).1 h
  refine (mem_tSpan_iff T r _).2 ⟨s, fun g => f * c g, fun g => T.mul_mem hf (hc g), ?_⟩
  funext x
  simp [term, Finset.sum_apply, Finset.smul_sum, smul_smul, map_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← map_mul, algebraMap_smul]

def spanSub : Subalgebra O (X → Matrix d d K) where
  carrier := tSpan T r
  mul_mem' := mul_mem_tSpan T r
  add_mem' := add_mem_tSpan T r
  algebraMap_mem' c := by
    have h1 : algebraMap O (X → Matrix d d K) c = term r (algebraMap O (X → O) c) 1 := by
      funext x
      simp [term, Algebra.algebraMap_eq_smul_one]
    rw [h1]
    exact term_mem T r (T.algebraMap_mem c) 1

end Span

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

open Finset Classical Polynomial

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

section
variable {O : Type} [CommRing O] {Xs : Type} (T : Subalgebra O (Xs → O))
  {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Group G] (r : G →* (Xs → Matrix d d O))

def polyT : Subalgebra O[X] (Xs → O[X]) where
  carrier := {f | ∀ k, (fun x => (f x).coeff k) ∈ T}
  mul_mem' := by
    intro f g hf hg k
    have h : (fun x => ((f * g) x).coeff k) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, (fun x => (f x).coeff p.1) * (fun x => (g x).coeff p.2) := by
      funext x; simp [Polynomial.coeff_mul, Finset.sum_apply]
    rw [h]
    exact T.sum_mem fun p _ => T.mul_mem (hf _) (hg _)
  add_mem' := by
    intro f g hf hg k
    have h : (fun x => ((f + g) x).coeff k) = (fun x => (f x).coeff k) + fun x => (g x).coeff k := by
      funext x; simp
    rw [h]
    exact T.add_mem (hf k) (hg k)
  algebraMap_mem' p := by
    intro k
    have h : (fun x => ((algebraMap O[X] (Xs → O[X]) p) x).coeff k) =
        algebraMap O (Xs → O) (p.coeff k) := by
      funext x; simp
    rw [h]
    exact T.algebraMap_mem _

theorem C_mem_polyT {c : Xs → O} (hc : c ∈ T) : (fun x => C (c x)) ∈ polyT T := by
  show ∀ k, (fun x => (C (c x)).coeff k) ∈ T
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hc
  · have h0 : (fun x => (C (c x)).coeff k) = 0 := by
      funext x
      simp [Polynomial.coeff_C, hk.ne']
    rw [h0]
    exact T.zero_mem

def rPoly : G →* (Xs → Matrix d d O[X]) where
  toFun g x := (r g x).map C
  map_one' := by funext x; simp
  map_mul' g h := by funext x; simp [Matrix.map_mul]

theorem lift_mem {a : Xs → Matrix d d O} (ha : a ∈ tSpan T r) :
    (fun x => (a x).map C) ∈ tSpan (polyT T) (rPoly r) := by
  obtain ⟨s, c, hc, rfl⟩ := ha
  refine ⟨s, fun g x => C (c g x), fun g => C_mem_polyT T (hc g), ?_⟩
  funext x
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [rPoly, Finset.sum_apply, Matrix.sum_apply, map_sum]

private theorem matrix_charpolyRev_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Matrix d d R) : (M.map f).charpolyRev = M.charpolyRev.map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply]
  · simp [Matrix.one_apply, h]

theorem detT (hG1 : ∀ (g : G) (k : ℕ), (fun x => (Matrix.charpolyRev (r g x)).coeff k) ∈ T)
    (M : Xs → Matrix d d O[X]) (hM : M ∈ tSpan (polyT T) (rPoly r)) (k : ℕ) :
    (fun x => (M x).det.coeff k) ∈ T := by
  have h1 : ∀ (g : G) (k : ℕ), FromT (polyT T) (fun x => (Matrix.charpolyRev (rPoly r g x)).coeff k) := by
    intro g k
    refine ⟨fun x => C ((Matrix.charpolyRev (r g x)).coeff k), C_mem_polyT T (hG1 g k), fun x => ?_⟩
    have hx : rPoly r g x = (r g x).map C := rfl
    dsimp only
    rw [hx, matrix_charpolyRev_map, Polynomial.coeff_map]
    rfl
  obtain ⟨u, hu, hux⟩ := det_poly_statement O[X] O[X] Xs G d (polyT T) (rPoly r) h1 1 (fun _ => M)
    (fun _ => hM) (Finsupp.single 0 (Fintype.card d))
  have key : ∀ x, u x = (M x).det := by
    intro x
    have hx := hux x
    dsimp only at hx
    rw [Fin.sum_univ_one, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, mul_comm,
      MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow] at hx
    simpa using hx
  have hfun : (fun x => (M x).det.coeff k) = fun x => (u x).coeff k := by
    funext x
    rw [key x]
  rw [hfun]
  exact hu k

end

theorem blockPolyT : StatBlockPolyT := by
  intro O _ X T d _ _ G _ r hG1 e he a ha k
  have hE : (fun x => (e x).map C) ∈ spanSub (polyT T) (rPoly r) := lift_mem T r he
  have hA : (fun x => (a x).map C) ∈ spanSub (polyT T) (rPoly r) := lift_mem T r ha
  have hM : (fun x => (Polynomial.X : O[X]) • (e x).map C - (a x).map C + (1 - e x).map C) ∈
      spanSub (polyT T) (rPoly r) := by
    have hq : (fun x => (Polynomial.X : O[X]) • (e x).map C - (a x).map C + (1 - e x).map C) =
        algebraMap O[X] (X → Matrix d d O[X]) Polynomial.X * (fun x => (e x).map C) -
          (fun x => (a x).map C) + (1 - fun x => (e x).map C) := by
      funext x
      ext i j
      by_cases h : i = j
      · subst h
        simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_apply]
      · simp [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_apply, h]
    rw [hq]
    exact Subalgebra.add_mem _ (Subalgebra.sub_mem _
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hE) hA)
      (Subalgebra.sub_mem _ (Subalgebra.one_mem _) hE)
  exact detT T r hG1 _ hM k

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section -- merged from Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.BurnsideMat
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem burnsideMat : StatBurnsideMat := by
  intro k _ n _ _ _ G _ ρ hρ
  obtain ⟨hirr, hcom⟩ := hρ
  let A := MonoidAlgebra k G
  let V := n → k
  let L : A →ₐ[k] Matrix n n k := MonoidAlgebra.lift k (Matrix n n k) G ρ
  let φ : A →ₐ[k] Module.End k V := (Matrix.toLinAlgEquiv' : Matrix n n k ≃ₐ[k] _).toAlgHom.comp L
  letI : Module A V := Module.compHom V φ.toRingHom
  have hact : ∀ (a : A) (v : V), a • v = (L a).mulVec v := fun a v => rfl
  haveI : IsScalarTower k A V := ⟨fun c a v => by
    rw [hact, hact, map_smul, Matrix.smul_mulVec]⟩
  have hof : ∀ g, L (MonoidAlgebra.of k G g) = ρ g := fun g => MonoidAlgebra.lift_of ρ g
  have hS : IsSimpleModule A V := by
    haveI : Nontrivial (Submodule A V) := by
      refine ⟨⊥, ⊤, fun h => ?_⟩
      have : (⊤ : Submodule A V) = ⊥ := h.symm
      have h2 : (fun _ : n => (1 : k)) ∈ (⊤ : Submodule A V) := Submodule.mem_top
      rw [this, Submodule.mem_bot] at h2
      exact one_ne_zero (congrFun h2 (Classical.arbitrary n))
    suffices hso : IsSimpleOrder (Submodule A V) from @IsSimpleModule.mk _ _ _ _ _ hso
    refine ⟨fun W => ?_⟩
    rcases hirr (W.restrictScalars k) (fun g v hv => by
      have := W.smul_mem (MonoidAlgebra.of k G g) hv
      rw [hact, hof] at this
      exact this) with h | h
    · left; exact (Submodule.restrictScalars_eq_bot_iff k A V).mp h
    · right; exact (Submodule.restrictScalars_eq_top_iff k A V).mp h
  have hsc : ∀ ψ : V →ₗ[A] V, ∃ c : k, ∀ v, ψ v = c • v := by
    intro ψ
    let M : Matrix n n k := LinearMap.toMatrix' (ψ.restrictScalars k)
    have hM : ∀ v, M.mulVec v = ψ v := fun v => by
      have := LinearMap.toMatrix'_mulVec (ψ.restrictScalars k) v
      simpa [M] using this
    obtain ⟨c, hc⟩ := hcom M (fun g => by
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
      rw [hM, hM, ← hof, ← hact, ← hact, map_smul])
    refine ⟨c, fun v => ?_⟩
    rw [← hM, hc, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hsurj := burnside k A V hS hsc
  refine eq_top_iff.mpr fun B _ => ?_
  obtain ⟨a, ha⟩ := hsurj (Matrix.toLin' B)
  have hB : B = L a := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun ha v
    simp only [Matrix.toLin'_apply]
    rw [← hact]
    exact this.symm
  rw [hB]
  exact MonoidAlgebra.induction_on (motive := fun a => L a ∈ Submodule.span k (Set.range ρ)) a
    (fun g => by rw [hof]; exact Submodule.subset_span ⟨g, rfl⟩)
    (fun f g hf hg => by rw [map_add (f := _)]; exact Submodule.add_mem _ hf hg)
    (fun c f hf => by rw [map_smul]; exact Submodule.smul_mem _ _ hf)

theorem ontoSpan : StatOntoSpan := by
  first | exact UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan .. | (apply UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> assumption) | (intros; apply UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> assumption) | (apply @UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> assumption) | (apply @UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan <;> first | assumption | infer_instance)

theorem noeth : StatNoeth := by
  intro O _ _ _ X' _ d _ _ R' hint
  let L : (X' → d → d → O) →ₗ[O] (X' → Matrix d d (FractionRing O)) :=
    { toFun := fun F x' => Matrix.of fun i j => algebraMap O (FractionRing O) (F x' i j)
      map_add' := fun F F' => by funext x'; ext i j; simp
      map_smul' := fun c F => by funext x'; ext i j; simp [Algebra.smul_def] }
  have hle : Subalgebra.toSubmodule R' ≤ LinearMap.range L := by
    intro a ha
    choose F hF using hint a ha
    exact ⟨F, by funext x'; ext i j; exact hF x' i j⟩
  haveI : IsNoetherian O (LinearMap.range L) := inferInstance
  haveI h1 : IsNoetherian O (Subalgebra.toSubmodule R') := isNoetherian_of_le hle
  haveI h2 : IsNoetherian O R' := h1
  exact isNoetherian_of_tower O h2

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

section Blocks
variable {A : Type*} [CommRing A] {d : Type} [Fintype d] [DecidableEq d] {α : Type} [DecidableEq α]
  (bl : d → α)

theorem blk_mul {M N : Matrix d d A} (hM : ∀ i j, bl i ≠ bl j → M i j = 0) (c : α) :
    (M * N).toSquareBlock bl c = M.toSquareBlock bl c * N.toSquareBlock bl c := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Matrix.toSquareBlock_def, Matrix.of_apply, Matrix.mul_apply]
  have h0 : ∑ k : {k // ¬ bl k = c}, M i (k : d) * N (k : d) j = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [hM i k (by rw [hi]; exact Ne.symm k.2), zero_mul]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => bl k = c) (fun k => M i k * N k j), h0,
    add_zero]

end Blocks

theorem r_mem {O : Type} [CommRing O] {X : Type} (T : Subalgebra O (X → O)) {d : Type} [Fintype d]
    [DecidableEq d] {G : Type} [Monoid G] (r : G →* (X → Matrix d d O)) (g : G) : r g ∈ tSpan T r := by
  refine ⟨{g}, fun _ => 1, fun _ => T.one_mem, ?_⟩
  funext x
  simp


end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem blockPoly_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {d : Type*} [Fintype d]
    [DecidableEq d] (e a : Matrix d d A) :
    (blockPoly e a).map f = blockPoly (e.map f) (a.map f) := by
  unfold blockPoly
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply]
  · simp [Matrix.one_apply, h]

theorem r_mem' {O K : Type} [CommRing O] [CommRing K] [Algebra O K] {X : Type} (T : Subalgebra O (X → O))
    {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Monoid G] (r : G →* (X → Matrix d d K)) (g : G) :
    r g ∈ tSpan T r := by
  refine ⟨{g}, fun _ => 1, fun _ => T.one_mem, ?_⟩
  funext x
  simp

section Build
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type}
  (T' : Subalgebra O (X' → O)) {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Group G]
  (rK : G →* (X' → Matrix d d (FractionRing O)))

def scal : T' →+* spanSub T' rK where
  toFun f := ⟨term rK f.1 1, term_mem T' rK f.2 1⟩
  map_one' := Subtype.ext (by funext y; simp [term])
  map_mul' f g := Subtype.ext (by
    show term rK (f.1 * g.1) 1 = term rK f.1 1 * term rK g.1 1
    rw [term_mul, mul_one])
  map_zero' := Subtype.ext (term_zero rK 1)
  map_add' f g := Subtype.ext (term_add rK f.1 g.1 1)

theorem scal_apply (f : T') (y : X') :
    (scal T' rK f).1 y = algebraMap O (FractionRing O) (f.1 y) • (1 : Matrix d d (FractionRing O)) := by
  simp [scal, term]

@[instance_reducible] def algRp : Algebra T' (spanSub T' rK) :=
  RingHom.toAlgebra' (scal T' rK) (fun f a => Subtype.ext (by
    funext y
    show (scal T' rK f).1 y * a.1 y = a.1 y * (scal T' rK f).1 y
    rw [scal_apply]; simp))

@[instance_reducible] def modEvRp (x' : X') : Module T' (EvalSp O d (spanSub T' rK) x') :=
  Module.compHom _ ((algebraMap O (FractionRing O)).comp
    ((Pi.evalRingHom (fun _ : X' => O) x').comp T'.val.toRingHom))

theorem smul_val (f : T') (a : spanSub T' rK) (y : X') :
    (letI := algRp T' rK; (f • a : spanSub T' rK)).1 y =
      algebraMap O (FractionRing O) (f.1 y) • a.1 y := by
  letI := algRp T' rK
  show ((scal T' rK f) * a).1 y = _
  rw [Subalgebra.coe_mul, Pi.mul_apply, scal_apply, smul_mul_assoc, one_mul]

theorem finrank_range_eq (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) (x' : X') (a : R') :
    Module.finrank (FractionRing O)
      (LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') a)) =
      (a.1 x').rank := by
  show Module.finrank (FractionRing O) (LinearMap.range (a.1 x').mulVecLin) = _
  rfl

end Build

theorem inj_of_prod_eq {K : Type*} [Field K] {t : ℕ} (a b : Fin t → K) (hb : Function.Injective b)
    (h : ∏ i, (Polynomial.X - Polynomial.C (a i)) = ∏ i, (Polynomial.X - Polynomial.C (b i))) :
    Function.Injective a := by
  have key : ∀ c : Fin t → K, ∏ i, (Polynomial.X - Polynomial.C (c i)) =
      ((Finset.univ.val.map c).map fun x => Polynomial.X - Polynomial.C x).prod := by
    intro c
    rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  have hm : Finset.univ.val.map a = Finset.univ.val.map b := by
    have h2 := congrArg Polynomial.roots h
    rwa [key a, key b, Polynomial.roots_multiset_prod_X_sub_C,
      Polynomial.roots_multiset_prod_X_sub_C] at h2
  have hnd : (Finset.univ.val.map a).Nodup := by
    rw [hm]
    exact Multiset.Nodup.map hb Finset.univ.nodup
  intro x y hxy
  exact Multiset.inj_on_of_nodup_map hnd x (by simp) y (by simp) hxy

end Formalism.RepresentationBoundsCohomology.ringDataObjects
