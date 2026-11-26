module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.IsoOfTrace
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Alg

open PositivityTheory.RgUd.T

variable (k : Type) [Field k] [CharZero k]

def JC : Prop :=
  ∀ (n : ℕ) (x : Matrix (Fin n) (Fin n) k), ∃ s ∈ Algebra.adjoin k {x},
    Module.End.IsSemisimple (Matrix.toLin' s) ∧ IsNilpotent (x - s)

def TrNil : Prop :=
  ∀ (n : ℕ) (x s z : Matrix (Fin n) (Fin n) k), s ∈ Algebra.adjoin k {x} → IsNilpotent (x - s) → Commute z x →
    ∀ j : ℕ, trace (z * x ^ j) = trace (z * s ^ j)

def TrAll : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x x' : Matrix (Fin n) (Fin n) k), pZ Z x = pZ Z x' →
    ∀ z ∈ Z, ∀ j : ℕ, trace (z * x ^ j) = trace (z * x' ^ j)

def IsoOfTrace : Prop :=
  ∀ (n : ℕ) (R : Type) [CommRing R] [Algebra k R] [FiniteDimensional k R] [IsReduced R]
    (ρ ρ' : R →ₐ[k] Module.End k (Fin n → k)), (∀ r, LinearMap.trace k _ (ρ r) = LinearMap.trace k _ (ρ' r)) →
    ∃ φ : (Fin n → k) ≃ₗ[k] (Fin n → k), ∀ r v, φ (ρ r v) = ρ' r (φ v)

def Conj : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → ∀ s s' : Matrix (Fin n) (Fin n) k, s ∈ Bz Z → s' ∈ Bz Z →
    Module.End.IsSemisimple (Matrix.toLin' s) → Module.End.IsSemisimple (Matrix.toLin' s') →
    (∀ z ∈ Z, ∀ j : ℕ, trace (z * s ^ j) = trace (z * s' ^ j)) →
    ∃ g ∈ Gz Z, g.val * s * g⁻¹.val = s'

end PositivityTheory.RgUd.T.Alg
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.LinearConjugation.ToLinAlgEquivEq
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.T.Alg.Conj2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Alg

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

def SS (a : Matrix (Fin n) (Fin n) k) : Prop := Module.End.IsSemisimple (Matrix.toLin' a)

theorem toLinAlgEquiv'_eq (a : Matrix (Fin n) (Fin n) k) : Matrix.toLinAlgEquiv' a = Matrix.toLin' a := rfl

theorem ss_add {a b : Matrix (Fin n) (Fin n) k} (h : Commute a b) (ha : SS a) (hb : SS b) : SS (a + b) := by
  unfold SS
  rw [← toLinAlgEquiv'_eq, map_add (f := _)]
  exact Module.End.IsSemisimple.add_of_commute (h.map Matrix.toLinAlgEquiv') ha hb

theorem ss_mul {a b : Matrix (Fin n) (Fin n) k} (h : Commute a b) (ha : SS a) (hb : SS b) : SS (a * b) := by
  unfold SS
  rw [← toLinAlgEquiv'_eq, map_mul]
  exact Module.End.IsSemisimple.mul_of_commute (h.map Matrix.toLinAlgEquiv') ha hb

theorem ss_algebraMap (c : k) : SS (algebraMap k (Matrix (Fin n) (Fin n) k) c) := by
  unfold SS
  rw [← toLinAlgEquiv'_eq, AlgEquiv.commutes]
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := X - C c)
    (Polynomial.irreducible_X_sub_C c).squarefree ?_
  simp

theorem ss_of_mem {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) {z : Matrix (Fin n) (Fin n) k}
    (hz : z ∈ Z) : SS z := by
  obtain ⟨nn, hnn, ss, -, hnil, hsss, hsum⟩ := Module.End.exists_isNilpotent_isSemisimple (K := k) (f := Matrix.toLin' z)
  have hmap : Algebra.adjoin k {Matrix.toLin' z} =
      (Algebra.adjoin k {z}).map (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom := by
    rw [← Algebra.adjoin_image, Set.image_singleton]
    rfl
  rw [hmap] at hnn
  obtain ⟨m, hm, hmn⟩ := Subalgebra.mem_map.1 hnn
  have hmZ : m ∈ Z := Algebra.adjoin_le (Set.singleton_subset_iff.2 hz) hm
  have hmnil : IsNilpotent m := by
    have : IsNilpotent ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).symm nn) := hnil.map _
    rw [← hmn] at this
    simpa using this
  have hm0 : m = 0 := by
    have h1 : IsNilpotent (⟨m, hmZ⟩ : Z) := by
      obtain ⟨e, he⟩ := hmnil
      exact ⟨e, Subtype.ext (by simpa using he)⟩
    have := hZ.2.eq_zero _ h1
    simpa using congrArg Subtype.val this
  have hnn0 : nn = 0 := by rw [← hmn, hm0]; simp
  unfold SS
  rw [hsum, hnn0, zero_add]
  exact hsss

theorem conj_of (hiso : IsoOfTrace k) : Conj k := by
  intro n Z hZ s s' hs hs' hss hss' htr
  classical
  set S : Set (Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k) :=
    (fun z => (z, z)) '' (Z : Set (Matrix (Fin n) (Fin n) k)) ∪ {(s, s')} with hSdef
  have hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro a (⟨z, hz, rfl⟩ | ha) b (⟨w, hw, rfl⟩ | hb)
    · simp [hZ.1 z hz w hw]
    · rw [Set.mem_singleton_iff] at hb; subst hb
      simp [hs z hz, hs' z hz]
    · rw [Set.mem_singleton_iff] at ha; subst ha
      simp [hs w hw, hs' w hw]
    · rw [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
  set R := Algebra.adjoin k S with hRdef

  have hRc : ∀ x ∈ R, ∀ y ∈ R, Commute x y := fun x hx y hy =>
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun b hb =>
      (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun a ha => hcomm b hb a ha).symm

  letI : CommRing R := { (inferInstance : Ring R) with
    mul_comm := fun x y => Subtype.ext (hRc x x.2 y y.2).eq }

  have hRss : ∀ x ∈ R, SS x.1 ∧ SS x.2 := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨z, hz, rfl⟩ | hx
      · exact ⟨ss_of_mem hZ hz, ss_of_mem hZ hz⟩
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact ⟨hss, hss'⟩
    | algebraMap c => exact ⟨ss_algebraMap c, ss_algebraMap c⟩
    | add x y hx hy ihx ihy =>
      have h := hRc x hx y hy
      exact ⟨ss_add (h.map (RingHom.fst _ _)) ihx.1 ihy.1, ss_add (h.map (RingHom.snd _ _)) ihx.2 ihy.2⟩
    | mul x y hx hy ihx ihy =>
      have h := hRc x hx y hy
      exact ⟨ss_mul (h.map (RingHom.fst _ _)) ihx.1 ihy.1, ss_mul (h.map (RingHom.snd _ _)) ihx.2 ihy.2⟩

  let f : Z →+* Matrix (Fin n) (Fin n) k := Z.val.toRingHom
  have hform : ∀ x ∈ R, ∃ P : Z[X], x = (P.eval₂ f s, P.eval₂ f s') := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨z, hz, rfl⟩ | hx
      · exact ⟨C ⟨z, hz⟩, by simp [f]⟩
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact ⟨X, by simp⟩
    | algebraMap c =>
      refine ⟨C (algebraMap k Z c), ?_⟩
      simp [f, Prod.algebraMap_apply]
    | add x y hx hy ihx ihy =>
      obtain ⟨P, rfl⟩ := ihx
      obtain ⟨Q, rfl⟩ := ihy
      exact ⟨P + Q, by simp [eval₂_add]⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨P, rfl⟩ := ihx
      obtain ⟨Q, rfl⟩ := ihy
      refine ⟨P * Q, ?_⟩
      rw [eval₂_mul_noncomm _ _ fun j => ?_, eval₂_mul_noncomm _ _ fun j => ?_]
      · rfl
      · exact hs' (f (Q.coeff j)) (Q.coeff j).2
      · exact hs (f (Q.coeff j)) (Q.coeff j).2
  have htrP : ∀ P : Z[X], trace (P.eval₂ f s) = trace (P.eval₂ f s') := by
    intro P
    rw [eval₂_eq_sum, eval₂_eq_sum, Polynomial.sum_def, Polynomial.sum_def, trace_sum, trace_sum]
    exact Finset.sum_congr rfl fun e _ => htr _ (P.coeff e).2 e

  haveI : IsReduced R := ⟨fun x hx => by
    have h1 : IsNilpotent (x : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k) := hx.map R.val
    have hs1 := hRss x x.2
    have e1 : (x : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k).1 = 0 := by
      have hn1 := (h1.map (RingHom.fst (Matrix (Fin n) (Fin n) k) (Matrix (Fin n) (Fin n) k))).map
        (Matrix.toLinAlgEquiv' (R := k) (n := Fin n))
      have := Module.End.eq_zero_of_isNilpotent_isSemisimple hn1 (by exact hs1.1)
      exact (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).injective (this.trans (map_zero _).symm)
    have e2 : (x : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k).2 = 0 := by
      have hn2 := (h1.map (RingHom.snd (Matrix (Fin n) (Fin n) k) (Matrix (Fin n) (Fin n) k))).map
        (Matrix.toLinAlgEquiv' (R := k) (n := Fin n))
      have := Module.End.eq_zero_of_isNilpotent_isSemisimple hn2 (by exact hs1.2)
      exact (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).injective (this.trans (map_zero _).symm)
    exact Subtype.ext (Prod.ext e1 e2)⟩
  let ρ : R →ₐ[k] Module.End k (Fin n → k) :=
    (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp ((AlgHom.fst k _ _).comp R.val)
  let ρ' : R →ₐ[k] Module.End k (Fin n → k) :=
    (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp ((AlgHom.snd k _ _).comp R.val)
  have hρ : ∀ r : R, ρ r = Matrix.toLin' (r : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k).1 :=
    fun r => rfl
  have hρ' : ∀ r : R, ρ' r = Matrix.toLin' (r : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k).2 :=
    fun r => rfl
  have htrace : ∀ r, LinearMap.trace k _ (ρ r) = LinearMap.trace k _ (ρ' r) := by
    intro r
    rw [hρ, hρ', Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq]
    obtain ⟨P, hP⟩ := hform r r.2
    rw [hP]
    exact htrP P
  obtain ⟨φ, hφ⟩ := hiso n R ρ ρ' htrace

  let A : Matrix (Fin n) (Fin n) k := LinearMap.toMatrix' (φ : (Fin n → k) →ₗ[k] (Fin n → k))
  let B : Matrix (Fin n) (Fin n) k := LinearMap.toMatrix' (φ.symm : (Fin n → k) →ₗ[k] (Fin n → k))
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext v : 1
    simp
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext v : 1
    simp
  let g : GL (Fin n) k := ⟨A, B, hAB, hBA⟩

  have hint : ∀ x ∈ R, A * x.1 = x.2 * A := by
    intro x hx
    have hc : (φ : (Fin n → k) →ₗ[k] (Fin n → k)).comp (Matrix.toLin' x.1) =
        (Matrix.toLin' x.2).comp (φ : (Fin n → k) →ₗ[k] (Fin n → k)) := by
      refine LinearMap.ext fun v => ?_
      have := hφ ⟨x, hx⟩ v
      rw [hρ, hρ'] at this
      simpa using this
    have := congrArg LinearMap.toMatrix' hc
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_toLin'] at this
    exact this
  refine ⟨g, fun a ha => ?_, ?_⟩
  · have := hint (a, a) (Algebra.subset_adjoin (Or.inl ⟨a, ha, rfl⟩))
    exact this.symm
  · have h1 := hint (s, s') (Algebra.subset_adjoin (Or.inr rfl))
    show A * s * B = s'
    rw [h1, Matrix.mul_assoc, hAB, Matrix.mul_one]

end PositivityTheory.RgUd.T.Alg.Conj2
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.NilpotentTraces.TrNil
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Alg.Jcnil

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Alg

variable (k : Type) [Field k] [CharZero k]

theorem jc : JC k := by
  intro n x
  obtain ⟨N, -, S, hS, hN, hSs, hx⟩ := Module.End.exists_isNilpotent_isSemisimple (K := k) (f := Matrix.toLin' x)
  have hsx : Matrix.toLinAlgEquiv' (Matrix.toLinAlgEquiv'.symm S) = S := AlgEquiv.apply_symm_apply _ _
  refine ⟨Matrix.toLinAlgEquiv'.symm S, ?_, ?_, ?_⟩
  · have hmap := AlgHom.map_adjoin (Matrix.toLinAlgEquiv'.symm : _ ≃ₐ[k] Matrix (Fin n) (Fin n) k).toAlgHom {Matrix.toLin' x}
    rw [Set.image_singleton] at hmap
    have hx' : (Matrix.toLinAlgEquiv'.symm : _ ≃ₐ[k] Matrix (Fin n) (Fin n) k).toAlgHom (Matrix.toLin' x) = x :=
      Matrix.toLinAlgEquiv'.symm_apply_apply x
    rw [hx'] at hmap
    rw [← hmap]
    exact Subalgebra.mem_map.mpr ⟨S, hS, rfl⟩
  · have : Matrix.toLin' (Matrix.toLinAlgEquiv'.symm S) = S := hsx
    rw [this]
    exact hSs
  · have hdiff : x - Matrix.toLinAlgEquiv'.symm S = Matrix.toLinAlgEquiv'.symm N := by
      apply Matrix.toLinAlgEquiv'.injective
      rw [map_sub, hsx, AlgEquiv.apply_symm_apply]
      have : Matrix.toLinAlgEquiv' x = Matrix.toLin' x := rfl
      rw [this, hx]
      abel
    rw [hdiff]
    exact hN.map _

theorem trNil : TrNil k := by
  intro n x s z hs hn hz j
  have hxs : Commute x s := Algebra.commute_of_mem_adjoin_self hs
  have hzs : Commute z s := Algebra.commute_of_mem_adjoin_singleton_of_commute hs hz
  have hdx : Commute (x - s) x := (Commute.refl x).sub_left hxs.symm
  have hds : Commute (x - s) s := hxs.sub_left (Commute.refl s)
  have hg := hxs.mul_geom_sum₂ j
  have hc : Commute (x - s) (∑ i ∈ Finset.range j, x ^ i * s ^ (j - 1 - i)) :=
    Commute.sum_right _ _ _ fun i _ => (hdx.pow_right i).mul_right (hds.pow_right _)
  have hzd : Commute z (x - s) := hz.sub_right hzs
  have hnil : IsNilpotent (z * x ^ j - z * s ^ j) := by
    rw [← mul_sub, ← hg, ← mul_assoc, hzd.eq, mul_assoc]
    exact Commute.isNilpotent_mul_right (hzd.symm.mul_right hc) hn
  have ht := Matrix.isNilpotent_trace_of_isNilpotent hnil
  rw [Matrix.trace_sub] at ht
  exact sub_eq_zero.mp ht.eq_zero

end PositivityTheory.RgUd.T.Alg.Jcnil
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.CoefficientTraces.TraceAllHolds
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.T.Alg.Trall

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Alg

variable (k : Type) [Field k] [CharZero k]

theorem sum_coeff_trace {n : ℕ} (x z : Matrix (Fin n) (Fin n) k) (p : k[X]) (hp : aeval x p = 0) (m : ℕ) :
    ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * trace (z * x ^ (m + i)) = 0 := by
  have h : trace (z * x ^ m * aeval x p) = 0 := by rw [hp, mul_zero, trace_zero]
  rw [aeval_eq_sum_range, Finset.mul_sum, trace_sum] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, trace_smul, smul_eq_mul, mul_assoc, ← pow_add]

theorem trace_all_holds : TrAll k := by
  intro n Z x x' h z hz j
  have key : ∀ w : Z, ∀ j, j < 2 * n + 1 → trace ((w : Matrix (Fin n) (Fin n) k) * x ^ j) = trace ((w : Matrix (Fin n) (Fin n) k) * x' ^ j) := by
    intro w j hj
    have hw : (w : Matrix (Fin n) (Fin n) k) = ∑ i, (Module.finBasis k Z).repr w i • ((Module.finBasis k Z) i : Matrix (Fin n) (Fin n) k) := by
      nth_rewrite 1 [← (Module.finBasis k Z).sum_repr w]
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    rw [hw, Finset.sum_mul, Finset.sum_mul, trace_sum, trace_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, trace_smul, trace_smul]
    congr 1
    exact congrFun h (⟨j, hj⟩, i)
  set q := x.charpoly * x'.charpoly with hqdef
  have hqm : q.Monic := x.charpoly_monic.mul x'.charpoly_monic
  have hdeg : q.natDegree = 2 * n := by
    rw [hqdef, x.charpoly_monic.natDegree_mul x'.charpoly_monic, charpoly_natDegree_eq_dim, charpoly_natDegree_eq_dim, Fintype.card_fin]
    ring
  have hx0 : aeval x q = 0 := by rw [hqdef, map_mul, aeval_self_charpoly, zero_mul]
  have hx'0 : aeval x' q = 0 := by rw [hqdef, map_mul, aeval_self_charpoly, mul_zero]
  have hrec : ∀ m, ∑ i ∈ Finset.range (2 * n + 1), q.coeff i * (trace (z * x ^ (m + i)) - trace (z * x' ^ (m + i))) = 0 := by
    intro m
    have h1 := sum_coeff_trace k x z q hx0 m
    have h2 := sum_coeff_trace k x' z q hx'0 m
    rw [hdeg] at h1 h2
    simp only [mul_sub, Finset.sum_sub_distrib, h1, h2, sub_zero]
  have hlead : q.coeff (2 * n) = 1 := by
    rw [← hdeg]
    exact hqm
  suffices hall : ∀ j, trace (z * x ^ j) - trace (z * x' ^ j) = 0 from sub_eq_zero.mp (hall j)
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j < 2 * n + 1
    · exact sub_eq_zero.mpr (key ⟨z, hz⟩ j hj)
    · obtain ⟨m, rfl⟩ : ∃ m, j = m + 2 * n := ⟨j - 2 * n, by omega⟩
      have hm := hrec m
      rw [Finset.sum_range_succ, hlead, one_mul] at hm
      have hs : ∑ i ∈ Finset.range (2 * n), q.coeff i * (trace (z * x ^ (m + i)) - trace (z * x' ^ (m + i))) = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [Finset.mem_range] at hi
          rw [ih (m + i) (by omega), mul_zero]
      rw [hs, zero_add] at hm
      exact hm

end PositivityTheory.RgUd.T.Alg.Trall
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.RestrictionHomomorphisms.ResHomApply
noncomputable section

open Module

namespace PositivityTheory.RgUd.T.Alg.Iso2

variable {k : Type} [Field k] [CharZero k]

theorem iso_of_field {K W W' : Type} [Field K] [Algebra k K] [FiniteDimensional k K]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] [AddCommGroup W'] [Module k W'] [FiniteDimensional k W']
    (σ : K →ₐ[k] Module.End k W) (σ' : K →ₐ[k] Module.End k W') (h : finrank k W = finrank k W') :
    ∃ φ : W ≃ₗ[k] W', ∀ c w, φ (σ c w) = σ' c (φ w) := by
  classical
  letI : Module K W := Module.compHom W σ.toRingHom
  letI : Module K W' := Module.compHom W' σ'.toRingHom
  haveI : IsScalarTower k K W := ⟨fun a c w => by
    show σ (a • c) w = a • σ c w
    rw [map_smul]
    rfl⟩
  haveI : IsScalarTower k K W' := ⟨fun a c w => by
    show σ' (a • c) w = a • σ' c w
    rw [map_smul]
    rfl⟩
  haveI : FiniteDimensional K W := Module.Finite.of_restrictScalars_finite k K W
  haveI : FiniteDimensional K W' := Module.Finite.of_restrictScalars_finite k K W'
  have hK : 0 < finrank k K := Module.finrank_pos
  have h2 : finrank K W = finrank K W' := by
    apply Nat.eq_of_mul_eq_mul_left hK
    rw [Module.finrank_mul_finrank, Module.finrank_mul_finrank, h]
  let ψ : W ≃ₗ[K] W' := LinearEquiv.ofFinrankEq W W' h2
  refine ⟨ψ.restrictScalars k, fun c w => ?_⟩
  exact ψ.map_smul c w

variable {n : ℕ} {R : Type} [CommRing R] [Algebra k R]

def resHom (ρ : R →ₐ[k] Module.End k (Fin n → k)) (e : R) :
    R →ₐ[k] Module.End k (LinearMap.range (ρ e)) where
  toFun r := (ρ r).restrict (p := LinearMap.range (ρ e)) (q := LinearMap.range (ρ e)) (fun x hx => by
    obtain ⟨y, rfl⟩ := hx
    refine ⟨ρ r y, ?_⟩
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm])
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp
  map_zero' := by ext x; simp
  map_add' a b := by ext x; simp
  commutes' c := by ext x; simp [Algebra.algebraMap_eq_smul_one]

theorem resHom_apply (ρ : R →ₐ[k] Module.End k (Fin n → k)) (e r : R) (x : LinearMap.range (ρ e)) :
    ((resHom ρ e r x : LinearMap.range (ρ e)) : Fin n → k) = ρ r x := rfl

end PositivityTheory.RgUd.T.Alg.Iso2

namespace PositivityTheory.RgUd.T.Alg.Iso2

open Module

variable {k : Type} [Field k] [CharZero k]

theorem proj_of_mem {n : ℕ} {R : Type} [CommRing R] [Algebra k R] (ρ : R →ₐ[k] Module.End k (Fin n → k))
    {ι : Type} [DecidableEq ι] (e : ι → R) (he : ∀ I J, e I * e J = if I = J then e I else 0) (I J : ι)
    (x : Fin n → k) (hx : x ∈ LinearMap.range (ρ (e I))) : ρ (e J) x = if I = J then x else 0 := by
  obtain ⟨y, rfl⟩ := hx
  rw [← Module.End.mul_apply, ← map_mul, he J I]
  by_cases h : I = J
  · subst h
    simp
  · simp [h, Ne.symm h]

private theorem comp_lemma {n : ℕ} {R : Type} [CommRing R] [Algebra k R] [FiniteDimensional k R]
    (ρ ρ' : R →ₐ[k] Module.End k (Fin n → k)) (e : R) (he : e * e = e)
    (m : Ideal R) [m.IsMaximal] (hm : ∀ a ∈ m, a * e = 0)
    (htr : LinearMap.trace k (Fin n → k) (ρ e) = LinearMap.trace k (Fin n → k) (ρ' e)) :
    ∃ φ : LinearMap.range (ρ e) ≃ₗ[k] LinearMap.range (ρ' e),
      ∀ r x, φ (resHom ρ e r x) = resHom ρ' e r (φ x) := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : FiniteDimensional k (R ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m).toLinearMap (Ideal.Quotient.mkₐ_surjective k m)
  have h0 : ∀ (σ : R →ₐ[k] Module.End k (Fin n → k)), ∀ a ∈ m, resHom σ e a = 0 := by
    intro σ a ha
    refine LinearMap.ext fun x => Subtype.ext ?_
    obtain ⟨y, hy⟩ := x.2
    rw [resHom_apply, ← hy, ← Module.End.mul_apply, ← map_mul, hm a ha]
    simp
  have hI : ∀ σ : R →ₐ[k] Module.End k (Fin n → k), IsIdempotentElem (σ e) := fun σ => by
    show σ e * σ e = σ e
    rw [← map_mul, he]
  have hdim : finrank k (LinearMap.range (ρ e)) = finrank k (LinearMap.range (ρ' e)) := by
    have h1 := htr
    rw [(LinearMap.IsIdempotentElem.isProj_range _ (hI ρ)).trace,
      (LinearMap.IsIdempotentElem.isProj_range _ (hI ρ')).trace] at h1
    exact_mod_cast h1
  obtain ⟨φ, hφ⟩ := iso_of_field (Ideal.Quotient.liftₐ m (resHom ρ e) (h0 ρ))
    (Ideal.Quotient.liftₐ m (resHom ρ' e) (h0 ρ')) hdim
  refine ⟨φ, fun r x => ?_⟩
  exact hφ (Ideal.Quotient.mk m r) x

private theorem mul_eq_mul_of_ratio_eq_one {n : ℕ} {R : Type} [CommRing R] [Algebra k R]
    (ρ ρ' : R →ₐ[k] Module.End k (Fin n → k)) {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → R)
    (he : ∀ I J, e I * e J = if I = J then e I else 0) (hs : ∑ i, e i = 1)
    (φ : ∀ i, LinearMap.range (ρ (e i)) ≃ₗ[k] LinearMap.range (ρ' (e i))) (v : Fin n → k) :
    (∑ i, (LinearMap.range (ρ (e i))).subtype ∘ₗ (φ i).symm.toLinearMap ∘ₗ (ρ' (e i)).rangeRestrict)
      ((∑ i, (LinearMap.range (ρ' (e i))).subtype ∘ₗ (φ i).toLinearMap ∘ₗ (ρ (e i)).rangeRestrict) v) = v := by
  have inner : ∀ i j, (((φ j).symm ((ρ' (e j)).rangeRestrict
      ((φ i ((ρ (e i)).rangeRestrict v) : LinearMap.range (ρ' (e i))) : Fin n → k)) :
        LinearMap.range (ρ (e j))) : Fin n → k) = if i = j then ρ (e i) v else 0 := by
    intro i j
    by_cases h : i = j
    · subst h
      have h1 : (ρ' (e i)).rangeRestrict ((φ i ((ρ (e i)).rangeRestrict v) : LinearMap.range (ρ' (e i))) : Fin n → k)
          = φ i ((ρ (e i)).rangeRestrict v) := by
        apply Subtype.ext
        have := proj_of_mem ρ' e he i i _ (φ i ((ρ (e i)).rangeRestrict v)).2
        simpa using this
      rw [h1, LinearEquiv.symm_apply_apply, if_pos rfl]
      rfl
    · have h1 : (ρ' (e j)).rangeRestrict ((φ i ((ρ (e i)).rangeRestrict v) : LinearMap.range (ρ' (e i))) : Fin n → k)
          = 0 := by
        apply Subtype.ext
        have := proj_of_mem ρ' e he i j _ (φ i ((ρ (e i)).rangeRestrict v)).2
        simpa [h] using this
      rw [h1, (φ j).symm.map_zero, if_neg h]
      rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, Submodule.coe_subtype,
    LinearEquiv.coe_coe]
  simp only [Submodule.coe_sum, inner]
  simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← LinearMap.sum_apply, ← map_sum, hs, map_one]
  rfl

theorem isoOfTrace : IsoOfTrace k := by
  unfold IsoOfTrace
  intro n R _ _ _ _ ρ ρ' htr
  classical
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  let E := IsArtinianRing.equivPi R
  let e : MaximalSpectrum R → R := fun m => E.symm (Pi.single m 1)
  have hE : ∀ m, E (e m) = Pi.single m 1 := fun m => E.apply_symm_apply _
  have he : ∀ I J, e I * e J = if I = J then e I else 0 := by
    intro I J
    apply E.injective
    rw [map_mul, hE, hE]
    by_cases h : I = J
    · subst h
      rw [if_pos rfl, hE, ← Pi.single_mul, mul_one]
    · rw [if_neg h, map_zero]
      funext x
      rw [Pi.mul_apply, Pi.zero_apply]
      by_cases hx : x = I
      · subst hx
        rw [Pi.single_eq_of_ne h, mul_zero]
      · rw [Pi.single_eq_of_ne hx, zero_mul]
  have hs : ∑ m, e m = 1 := by
    apply E.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    funext x
    simp [hE, Finset.sum_apply, Pi.single_apply]
  have hm : ∀ m : MaximalSpectrum R, ∀ a ∈ m.asIdeal, a * e m = 0 := by
    intro m a ha
    apply E.injective
    rw [map_mul, hE, map_zero]
    funext x
    rw [Pi.mul_apply, Pi.zero_apply]
    by_cases h : x = m
    · subst h
      have h0 : E a x = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ha
      rw [h0, zero_mul]
    · rw [Pi.single_eq_of_ne h, mul_zero]
  have hc : ∀ m : MaximalSpectrum R, ∃ φ : LinearMap.range (ρ (e m)) ≃ₗ[k] LinearMap.range (ρ' (e m)),
      ∀ r x, φ (resHom ρ (e m) r x) = resHom ρ' (e m) r (φ x) := fun m => by
    haveI := m.isMaximal
    exact comp_lemma ρ ρ' (e m) (by simpa using he m m) m.asIdeal (hm m) (htr _)
  choose φ hφ using hc
  let Φ : (Fin n → k) →ₗ[k] (Fin n → k) :=
    ∑ i, (LinearMap.range (ρ' (e i))).subtype ∘ₗ (φ i).toLinearMap ∘ₗ (ρ (e i)).rangeRestrict
  let Ψ : (Fin n → k) →ₗ[k] (Fin n → k) :=
    ∑ i, (LinearMap.range (ρ (e i))).subtype ∘ₗ (φ i).symm.toLinearMap ∘ₗ (ρ' (e i)).rangeRestrict
  have h1 : Ψ ∘ₗ Φ = LinearMap.id := LinearMap.ext fun v => mul_eq_mul_of_ratio_eq_one ρ ρ' e he hs φ v
  have h2 : Φ ∘ₗ Ψ = LinearMap.id :=
    LinearMap.ext fun v => mul_eq_mul_of_ratio_eq_one ρ' ρ e he hs (fun i => (φ i).symm) v
  refine ⟨LinearEquiv.ofLinear Φ Ψ h2 h1, fun r v => ?_⟩
  show Φ (ρ r v) = ρ' r (Φ v)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, map_sum, Submodule.coe_subtype,
    LinearEquiv.coe_coe]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h3 : (ρ (e i)).rangeRestrict (ρ r v) = resHom ρ (e i) r ((ρ (e i)).rangeRestrict v) := by
    apply Subtype.ext
    rw [resHom_apply]
    show ρ (e i) (ρ r v) = ρ r (ρ (e i) v)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  rw [h3, hφ, resHom_apply]

end PositivityTheory.RgUd.T.Alg.Iso2
end
end

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Alg

open PositivityTheory.RgUd.T

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]

theorem mem_Bz_of_adjoin' {n : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {x s : Matrix (Fin n) (Fin n) k}
    (hx : x ∈ Bz Z) (hs : s ∈ Algebra.adjoin k {x}) : s ∈ Bz Z := by
  intro a ha
  exact (Algebra.commute_of_mem_adjoin_singleton_of_commute hs (hx a ha)).eq

theorem dich : Dich (k := k) := by
  classical
  intro n Z hZ y
  by_cases hne : ∃ x₀ ∈ Bz Z, pZ Z x₀ = y
  · obtain ⟨x₀, hx₀, hy₀⟩ := hne
    obtain ⟨s₀, hs₀, hss₀, hn₀⟩ := Jcnil.jc k n x₀
    have hs₀B : s₀ ∈ Bz Z := mem_Bz_of_adjoin' k hx₀ hs₀

    have key : ∀ x ∈ Bz Z, pZ Z x = y → ∃ g ∈ Gz Z, ∃ s, s ∈ Algebra.adjoin k {x} ∧ IsNilpotent (x - s) ∧
        g.val * s * g⁻¹.val = s₀ := by
      intro x hx hy
      obtain ⟨s, hs, hss, hn⟩ := Jcnil.jc k n x
      have hsB : s ∈ Bz Z := mem_Bz_of_adjoin' k hx hs
      have htr : ∀ z ∈ Z, ∀ j : ℕ, trace (z * s ^ j) = trace (z * s₀ ^ j) := by
        intro z hz j
        rw [← Jcnil.trNil k n x s z hs hn (hx z hz) j, ← Jcnil.trNil k n x₀ s₀ z hs₀ hn₀ (hx₀ z hz) j]
        exact Trall.trace_all_holds k n Z x x₀ (hy.trans hy₀.symm) z hz j
      obtain ⟨g, hg, hgs⟩ := Conj2.conj_of Iso2.isoOfTrace n Z hZ s s₀ hsB hs₀B hss hss₀ htr
      exact ⟨g, hg, s, hs, hn, hgs⟩
    by_cases hZs : s₀ ∈ Z
    · refine Or.inl ⟨s₀, hZs, fun x hx hy => ?_⟩
      obtain ⟨g, hg, s, hs, hn, hgs⟩ := key x hx hy
      have hgc : g.val * s₀ = s₀ * g.val := (hg s₀ hZs).symm
      have : s = s₀ := by
        have h1 : g.val * s = s₀ * g.val := by
          rw [← hgs, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.mul_one]
        have h2 : g.val * s = g.val * s₀ := h1.trans hgc.symm
        have := congrArg (fun m => g⁻¹.val * m) h2
        simpa [← Matrix.mul_assoc, ← Units.val_mul] using this
      rw [← this]
      exact hn
    · refine Or.inr ⟨s₀, hs₀B, hZs, hss₀, fun x hx hy => ?_⟩
      obtain ⟨g, hg, s, hs, hn, hgs⟩ := key x hx hy
      refine ⟨g, hg, ?_, ?_⟩
      · have e : g.val * x * g⁻¹.val - s₀ = g.val * (x - s) * g⁻¹.val := by
          rw [← hgs, Matrix.mul_sub, Matrix.sub_mul]
        rw [e]
        obtain ⟨m, hm⟩ := hn
        refine ⟨m, ?_⟩
        have hconj : ∀ j : ℕ, (g.val * (x - s) * g⁻¹.val) ^ j = g.val * (x - s) ^ j * g⁻¹.val := by
          intro j
          induction j with
          | zero => simp [← Units.val_mul]
          | succ j ih =>
            rw [pow_succ, ih, pow_succ]
            simp only [Matrix.mul_assoc]
            congr 2
            rw [← Matrix.mul_assoc g⁻¹.val, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        rw [hconj, hm]
        simp
      · have hcs : Commute x s := (Algebra.commute_of_mem_adjoin_singleton_of_commute hs (Commute.refl x)).symm.symm
        rw [← hgs]
        have e1 : g.val * x * g⁻¹.val * (g.val * s * g⁻¹.val) = g.val * (x * s) * g⁻¹.val := by
          simp only [Matrix.mul_assoc]
          congr 2
          rw [← Matrix.mul_assoc g⁻¹.val, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        have e2 : g.val * s * g⁻¹.val * (g.val * x * g⁻¹.val) = g.val * (s * x) * g⁻¹.val := by
          simp only [Matrix.mul_assoc]
          congr 2
          rw [← Matrix.mul_assoc g⁻¹.val, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        show _ * _ = _ * _
        rw [e1, e2, hcs.eq]
  · refine Or.inl ⟨0, Z.zero_mem, fun x hx hy => absurd ⟨x, hx, hy⟩ hne⟩

end PositivityTheory.RgUd.T.Alg
