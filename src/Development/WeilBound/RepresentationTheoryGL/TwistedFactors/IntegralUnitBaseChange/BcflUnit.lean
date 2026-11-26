module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedDictionaryPartB
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedDualFamilyHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinScalingLaw
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapSecondProperty
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapThirdProperty
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapIntegralProperty
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeThirdProperty
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitFundamentalLemmaFirstHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIwahoriContractionHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothConjugateInverseMem

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCommutesSeparableHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCommutesSeparableHolds
open Polynomial PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.TfLoc

theorem sigmaGL_incl_fixed {k E : Type*} [Field k] [Field E] [Algebra k E] {n : ℕ}
    (σ : E ≃ₐ[k] E) (γ : GL (Fin n) k) :
    sigmaGL σ (incl γ : GL (Fin n) E) = incl γ := by
  apply Units.ext
  ext i j
  show σ (algebraMap k E ((γ : Matrix (Fin n) (Fin n) k) i j)) =
    algebraMap k E ((γ : Matrix (Fin n) (Fin n) k) i j)
  exact σ.commutes _

theorem commute_of_normGL_eq {k E : Type*} [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E] {n : ℕ} (σ : E ≃ₐ[k] E)
    (δ : GL (Fin n) E) (γ : GL (Fin n) k) (hN : normGL σ δ = incl γ) :
    Commute (δ : Matrix (Fin n) (Fin n) E) (incl γ : GL (Fin n) E) := by
  have hℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank k E = 1 := by
    rw [← sigmaGL_pow, hℓ, sigmaGL_one]
  have h := map_twNorm_of_pow_eq_one (sigmaGL σ) hθ δ
  have h' : sigmaGL σ (normGL σ δ) = δ⁻¹ * normGL σ δ * δ := h
  rw [hN, sigmaGL_incl_fixed] at h'
  have hc : δ * (incl γ : GL (Fin n) E) = incl γ * δ := by
    calc δ * (incl γ : GL (Fin n) E) = δ * (δ⁻¹ * incl γ * δ) := by rw [← h']
      _ = incl γ * δ := by group
  have := congrArg (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E)) hc
  simpa [Commute, SemiconjBy] using this

theorem norm_commutes_of_separable : PositivityTheory.Rg.Tf.Loc.A1 → PositivityTheory.Rg.Tf.Loc.A2 := by
  intro hA1 k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ _ n δ γ hN hsep
  have hc := commute_of_normGL_eq σ δ γ hN
  exact ⟨hc, hA1 E n _ hsep _ hc⟩

end GlobalTheory.CompanionTheory.TfLoc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCommutesSeparableHoldsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_commutes_separable_holds : PositivityTheory.Rg.Tf.Loc.A1 → PositivityTheory.Rg.Tf.Loc.A2 := by
  first | exact @GlobalTheory.CompanionTheory.TfLoc.norm_commutes_of_separable | exact GlobalTheory.CompanionTheory.TfLoc.norm_commutes_of_separable | (intros; apply GlobalTheory.CompanionTheory.TfLoc.norm_commutes_of_separable <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFirstProperty
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFirstProperty
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.LatticeCoset

variable {F : Type} [Field F] [ValuativeRel F] {n : ℕ}

theorem mem_unitGL_iff (h : GL (Fin n) F) :
    h ∈ unitGL (n := Fin n) F ↔
      (∀ i j, (h : Matrix (Fin n) (Fin n) F) i j ∈ intO F) ∧
      (∀ i j, ((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ intO F) := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨fun i j => (k.1 i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((k⁻¹).1 i j).2
  · rintro ⟨h1, h2⟩
    let O := (ValuativeRel.valuation F).integer
    let A : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨(h : Matrix (Fin n) (Fin n) F) i j, h1 i j⟩
    let B : Matrix (Fin n) (Fin n) O :=
      Matrix.of fun i j => ⟨((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j, h2 i j⟩
    have hA : A.map O.subtype = (h : Matrix (Fin n) (Fin n) F) := by ext i j; rfl
    have hB : B.map O.subtype = ((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by ext i j; rfl
    have inj : Function.Injective (fun M : Matrix (Fin n) (Fin n) O => M.map O.subtype) :=
      Matrix.map_injective Subtype.val_injective
    have hAB : A * B = 1 := by
      apply inj
      show (A * B).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
      rw [Matrix.map_mul, hA, hB, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    have hBA : B * A = 1 := by
      apply inj
      show (B * A).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
      rw [Matrix.map_mul, hA, hB, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
    ext i j
    rfl

theorem latticeOf_subset_of_integral (g g' : GL (Fin n) F)
    (h : ∀ i j, ((g⁻¹ * g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ intO F) :
    latticeOf g' ⊆ latticeOf g := by
  rintro v ⟨w, hw, rfl⟩
  refine ⟨((g⁻¹ * g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec w, fun i => ?_, ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (h i j) (hw j)
  · rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left]

theorem integral_of_latticeOf_subset (g g' : GL (Fin n) F)
    (h : latticeOf g' ⊆ latticeOf g) (i j : Fin n) :
    ((g⁻¹ * g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ intO F := by
  have hs : ∀ k, (Pi.single j (1 : F) : Fin n → F) k ∈ intO F := by
    intro k
    rcases eq_or_ne k j with rfl | hk
    · rw [Pi.single_eq_same]; exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne hk]; exact Subring.zero_mem _
  obtain ⟨w', hw', he⟩ := h ⟨Pi.single j 1, hs, rfl⟩
  have key : ((g⁻¹ * g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).mulVec (Pi.single j 1) = w' := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, he, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mulVec]
  have hi := congrFun key i
  rw [Matrix.mulVec_single_one] at hi
  change ((g⁻¹ * g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = w' i at hi
  rw [hi]
  exact hw' i

theorem latticeOf_eq_iff : PositivityTheory.Rg.Tf.Loc.L1 := by
  intro F _ _ _ _ n g g'
  constructor
  · intro h
    rw [mem_unitGL_iff]
    refine ⟨integral_of_latticeOf_subset g g' h.symm.subset, ?_⟩
    rw [mul_inv_rev, inv_inv]
    exact integral_of_latticeOf_subset g' g h.subset
  · intro hm
    rw [mem_unitGL_iff] at hm
    obtain ⟨h1, h2⟩ := hm
    rw [mul_inv_rev, inv_inv] at h2
    exact Set.Subset.antisymm (latticeOf_subset_of_integral g' g h2) (latticeOf_subset_of_integral g g' h1)

end GlobalTheory.CompanionTheory.LatticeCoset
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeFirstPropertyStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_first_property : PositivityTheory.Rg.Tf.Loc.L1 := by
  first | exact @GlobalTheory.CompanionTheory.LatticeCoset.latticeOf_eq_iff | exact GlobalTheory.CompanionTheory.LatticeCoset.latticeOf_eq_iff | (intros; apply GlobalTheory.CompanionTheory.LatticeCoset.latticeOf_eq_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapFirstProperty
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapFirstProperty
open scoped TensorProduct
open Finset

namespace GlobalTheory.CompanionTheory.NormOnto

theorem field_norm_onto {L : Type*} [Field L] [Finite L] (ρ : RingAut L) (e : ℕ) (he : 0 < e)
    (h1 : ρ ^ e = 1) (hne : ∀ j, 0 < j → j < e → ρ ^ j ≠ 1) (a : L) (ha0 : a ≠ 0) (hfix : ρ a = a) :
    ∃ w : L, w ≠ 0 ∧ ∏ j ∈ range e, (ρ ^ j) w = a := by
  have hord : orderOf ρ = e := by
    rw [orderOf_eq_iff he]
    exact ⟨h1, fun m hm hm0 => hne m hm0 hm⟩
  have hfin : IsOfFinOrder ρ := isOfFinOrder_iff_pow_eq_one.2 ⟨e, he, h1⟩
  let G := Subgroup.zpowers ρ
  haveI : Finite G := Finite.of_equiv _ (finEquivZPowers hfin)
  haveI := Fintype.ofFinite G
  let K := FixedPoints.subfield G L
  have haK : a ∈ K := by
    intro g
    have hle : G ≤ MulAction.stabilizer (RingAut L) a := by
      rw [Subgroup.zpowers_le]
      exact hfix
    exact hle g.2
  let aK : K := ⟨a, haK⟩
  have haK0 : aK ≠ 0 := fun h => ha0 (congrArg Subtype.val h)
  obtain ⟨v, hv⟩ := FiniteField.unitsMap_norm_surjective K L (Units.mk0 aK haK0)
  have hv' : Algebra.norm K (v : L) = aK := by
    have := congrArg Units.val hv
    simpa using this
  refine ⟨v, v.ne_zero, ?_⟩
  have h2 := Algebra.norm_eq_prod_automorphisms K (v : L)
  rw [hv'] at h2
  have h3 : (∏ σ : L ≃ₐ[K] L, σ (v : L)) = ∏ g : G, (g : RingAut L) (v : L) := by
    symm
    exact Fintype.prod_equiv (FixedPoints.toAlgAutMulEquiv G L) _ _ (fun g => rfl)
  have h4 : (∏ g : G, (g : RingAut L) (v : L)) = ∏ i : Fin (orderOf ρ), (ρ ^ (i : ℕ)) (v : L) := by
    symm
    exact Fintype.prod_equiv (finEquivZPowers hfin) _ _ (fun i => by simp [finEquivZPowers_apply])
  rw [h3, h4, Fin.prod_univ_eq_prod_range (fun i => (ρ ^ i) (v : L)), hord] at h2
  exact h2.symm

theorem prod_range_stride {M : Type*} [CommMonoid M] (f : ℕ → M) (d e : ℕ) (hd : 0 < d)
    (h : ∀ i, ¬ d ∣ i → f i = 1) :
    ∏ i ∈ range (d * e), f i = ∏ j ∈ range e, f (d * j) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Nat.mul_succ, prod_range_add, ih, prod_range_succ]
    congr 1
    rw [prod_eq_single 0]
    · simp
    · intro b hb hb0
      apply h
      have hlt := mem_range.1 hb
      intro hdvd
      have : d ∣ b := (Nat.dvd_add_right (Dvd.intro _ rfl)).1 hdvd
      exact hb0 (Nat.eq_zero_of_dvd_of_lt this hlt)
    · intro h0
      exact absurd (mem_range.2 hd) h0

end GlobalTheory.CompanionTheory.NormOnto

namespace GlobalTheory.CompanionTheory.NormOnto

section Core

variable {B : Type*} [CommRing B]

def pull (T : RingAut B) (I : Ideal B) : Ideal B := I.comap (T : B →+* B)

theorem mem_pull_iter (T : RingAut B) (i : ℕ) (I : Ideal B) (b : B) :
    b ∈ (pull T)^[i] I ↔ (T ^ i) b ∈ I := by
  induction i generalizing I with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [pull, Ideal.mem_comap, pow_succ']
    rfl

theorem pull_iter_period (T : RingAut B) (ℓ : ℕ) (hT : T ^ ℓ = 1) (I : Ideal B) :
    (pull T)^[ℓ] I = I := by
  ext b
  rw [mem_pull_iter, hT]
  rfl

theorem pull_iter_max (T : RingAut B) (i : ℕ) (I : Ideal B) (hI : I.IsMaximal) :
    ((pull T)^[i] I).IsMaximal := by
  induction i generalizing I with
  | zero => simpa
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    apply ih
    exact Ideal.comap_isMaximal_of_surjective (T : B →+* B) (RingEquiv.surjective T)

theorem norm_fixed (T : RingAut B) (ℓ : ℕ) (hℓ : 0 < ℓ) (hT : T ^ ℓ = 1) (c : B) :
    T (∏ i ∈ range ℓ, (T ^ i) c) = ∏ i ∈ range ℓ, (T ^ i) c := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  have hs : ∀ i, T ((T ^ i) c) = (T ^ (i + 1)) c := fun i => by
    rw [pow_succ']; rfl
  rw [map_prod]
  simp only [hs]
  rw [prod_range_succ, prod_range_succ' (fun i => (T ^ i) c), hT]
  simp

theorem local_step [Finite B] (T : RingAut B) (ℓ : ℕ) (hℓ : 0 < ℓ) (hT : T ^ ℓ = 1)
    (n : ℕ) (x y : Fin n → B)
    (hxy : ∀ j < ℓ, ∑ i, x i * (T ^ j) (y i) = if j = 0 then 1 else 0)
    (a : B) (ha : IsUnit a) (hfix : T a = a) (m : Ideal B) (hm : m.IsMaximal) :
    ∃ w : B, w ∉ m ∧ ∀ c : B, c - w ∈ m →
      (∀ i, ¬ Function.minimalPeriod (pull T) m ∣ i → c - 1 ∈ (pull T)^[i] m) →
      ∏ i ∈ range ℓ, (T ^ i) c - a ∈ m := by
  classical
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  haveI : Finite (B ⧸ m) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := m))
  set d := Function.minimalPeriod (pull T) m with hd
  have hper : Function.IsPeriodicPt (pull T) ℓ m := pull_iter_period T ℓ hT m
  have hdpos : 0 < d := Function.minimalPeriod_pos_of_mem_periodicPts ⟨ℓ, hℓ, hper⟩
  obtain ⟨e, he⟩ : d ∣ ℓ := hper.minimalPeriod_dvd
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; omega
    · exact h
  have hdm : ∀ b, (T ^ d) b ∈ m ↔ b ∈ m := fun b => by
    rw [← mem_pull_iter, Function.iterate_minimalPeriod]
  have hmap : m = Ideal.map ((T ^ d : RingAut B) : B ≃+* B) m := by
    ext b
    rw [Ideal.mem_map_of_equiv]
    constructor
    · intro hb
      refine ⟨((T ^ d : RingAut B) : B ≃+* B).symm b, ?_, by simp⟩
      rw [← hdm]
      simpa using hb
    · rintro ⟨z, hz, rfl⟩
      exact (hdm z).2 hz
  let ρ : RingAut (B ⧸ m) := Ideal.quotientEquiv m m ((T ^ d : RingAut B) : B ≃+* B) hmap
  have hρ : ∀ (j : ℕ) (b : B), (ρ ^ j) (Ideal.Quotient.mk m b) =
      Ideal.Quotient.mk m ((T ^ (d * j)) b) := by
    intro j
    induction j with
    | zero => intro b; simp
    | succ j ih =>
      intro b
      rw [pow_succ', Nat.mul_succ, Nat.add_comm, pow_add]
      show ρ ((ρ ^ j) _) = _
      rw [ih]
      rfl
  have hρ1 : ρ ^ e = 1 := by
    ext z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hρ, ← he, hT]
    rfl
  have hne : ∀ j, 0 < j → j < e → ρ ^ j ≠ 1 := by
    intro j hj0 hje h1
    have hlt : d * j < ℓ := by rw [he]; exact Nat.mul_lt_mul_of_pos_left hje hdpos
    have h0 := hxy (d * j) hlt
    rw [if_neg (Nat.mul_ne_zero hdpos.ne' hj0.ne')] at h0
    have h1' := hxy 0 hℓ
    rw [if_pos rfl] at h1'
    have hy : ∀ b, Ideal.Quotient.mk m ((T ^ (d * j)) b) = Ideal.Quotient.mk m b := by
      intro b
      rw [← hρ, h1]
      rfl
    have := congrArg (Ideal.Quotient.mk m) h0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hy, map_zero] at this
    have h2 := congrArg (Ideal.Quotient.mk m) h1'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, pow_zero, map_one] at h2
    have h3 : ∀ i, Ideal.Quotient.mk m (((1 : RingAut B)) (y i)) = Ideal.Quotient.mk m (y i) :=
      fun i => rfl
    simp only [h3] at h2
    rw [this] at h2
    exact zero_ne_one h2
  have ha0 : Ideal.Quotient.mk m a ≠ 0 := by
    intro h
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.Quotient.eq_zero_iff_mem.1 h) ha)
  have hafix : ρ (Ideal.Quotient.mk m a) = Ideal.Quotient.mk m a := by
    have : (T ^ d) a = a := by
      have : ∀ k : ℕ, (T ^ k) a = a := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          rw [pow_succ']
          show T ((T ^ k) a) = a
          rw [ih, hfix]
      exact this d
    show Ideal.Quotient.mk m ((T ^ d) a) = _
    rw [this]
  obtain ⟨wb, hw0, hw⟩ := field_norm_onto ρ e hepos hρ1 hne _ ha0 hafix
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective wb
  refine ⟨w, fun h => hw0 (Ideal.Quotient.eq_zero_iff_mem.2 h), ?_⟩
  intro c hcw hc1
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_prod, he,
    prod_range_stride (fun i => Ideal.Quotient.mk m ((T ^ i) c)) d e hdpos, ← hw]
  · apply prod_congr rfl
    intro j _
    rw [← hρ, Ideal.Quotient.eq.2 hcw]
  · intro i hi
    have := (mem_pull_iter T i m (c - 1)).1 (hc1 i hi)
    rw [map_sub, map_one] at this
    have h := Ideal.Quotient.eq.2 this
    simpa using h

end Core

end GlobalTheory.CompanionTheory.NormOnto

namespace GlobalTheory.CompanionTheory.NormOnto

section Core2

variable {B : Type*} [CommRing B]

theorem norm_mod_max [Finite B] (T : RingAut B) (ℓ : ℕ) (hℓ : 0 < ℓ) (hT : T ^ ℓ = 1)
    (n : ℕ) (x y : Fin n → B)
    (hxy : ∀ j < ℓ, ∑ i, x i * (T ^ j) (y i) = if j = 0 then 1 else 0)
    (a : B) (ha : IsUnit a) (hfix : T a = a) :
    ∃ c : Bˣ, ∀ m : Ideal B, m.IsMaximal → ∏ i ∈ range ℓ, (T ^ i) (c : B) - a ∈ m := by
  classical
  have hmul : ∀ (k i : ℕ) (I : Ideal B), (pull T)^[i * k] ((pull T)^[k] I) = (pull T)^[(i + 1) * k] I := by
    intro k i I
    rw [← Function.iterate_add_apply]
    congr 1
    ring
  let s : Setoid (Ideal B) :=
    { r := fun I J => ∃ i, (pull T)^[i] I = J
      iseqv :=
        { refl := fun I => ⟨0, rfl⟩
          symm := by
            rintro I J ⟨i, rfl⟩
            refine ⟨(ℓ - 1) * i, ?_⟩
            rw [hmul, Nat.sub_add_cancel hℓ]
            rw [Nat.mul_comm]
            exact Function.IsPeriodicPt.const_mul (pull_iter_period T ℓ hT I) i
          trans := by
            rintro I J K ⟨i, rfl⟩ ⟨j, rfl⟩
            exact ⟨j + i, Function.iterate_add_apply _ _ _ _⟩ } }
  let rep : Ideal B → Ideal B := fun I => (Quotient.mk s I).out
  have hrep : ∀ I, ∃ i, (pull T)^[i] (rep I) = I := fun I => Quotient.mk_out (s := s) I
  have hrep_eq : ∀ I J, (∃ i, (pull T)^[i] I = J) → rep I = rep J := by
    intro I J h
    have : Quotient.mk s I = Quotient.mk s J := Quotient.sound h
    simp only [rep, this]
  have hrr : ∀ I, rep (rep I) = rep I := by
    intro I
    obtain ⟨i, hi⟩ := hrep I
    exact hrep_eq _ _ ⟨i, hi⟩
  have hloc := fun (m : {I : Ideal B // I.IsMaximal}) =>
    local_step T ℓ hℓ hT n x y hxy a ha hfix m.1 m.2
  choose w hw hwc using hloc
  let W : {I : Ideal B // I.IsMaximal} → B := fun I => if rep I.1 = I.1 then w I else 1
  haveI : Finite (Ideal B) :=
    Finite.of_injective (fun I : Ideal B => (I : Set B)) SetLike.coe_injective
  have hco : Pairwise (Function.onFun IsCoprime fun I : {I : Ideal B // I.IsMaximal} => I.1) := by
    intro I J hIJ
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne I.2 J.2 (fun h => hIJ (Subtype.ext h))
  obtain ⟨c, hc⟩ := Ideal.exists_forall_sub_mem_ideal hco W
  have hcu : IsUnit c := by
    by_contra hnu
    obtain ⟨M, hM, hcM⟩ := exists_max_ideal_of_mem_nonunits hnu
    have h1 := hc ⟨M, hM⟩
    by_cases hr : rep M = M
    · have h2 : c - w ⟨M, hM⟩ ∈ M := by simpa [W, hr] using h1
      have h3 := M.sub_mem hcM h2
      rw [sub_sub_cancel] at h3
      exact hw ⟨M, hM⟩ h3
    · have h2 : c - 1 ∈ M := by simpa [W, hr] using h1
      have h3 := M.sub_mem hcM h2
      rw [sub_sub_cancel] at h3
      exact hM.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  obtain ⟨cu, rfl⟩ := hcu
  refine ⟨cu, fun J hJ => ?_⟩
  obtain ⟨i0, hi0⟩ := hrep J
  set I := rep J with hI
  obtain ⟨i1, hi1⟩ : ∃ i, (pull T)^[i] J = I := s.symm ⟨i0, hi0⟩
  have hImax : I.IsMaximal := hi1 ▸ pull_iter_max T i1 J hJ
  have hII : rep I = I := hrr J
  have hmemI : ∏ i ∈ range ℓ, (T ^ i) (cu : B) - a ∈ I := by
    apply hwc ⟨I, hImax⟩
    · have h1 := hc ⟨I, hImax⟩
      simpa [W, hII] using h1
    · intro i hi
      have hmax' := pull_iter_max T i I hImax
      have hne : (pull T)^[i] I ≠ I := fun h =>
        hi (Function.IsPeriodicPt.minimalPeriod_dvd h)
      have hr : rep ((pull T)^[i] I) ≠ (pull T)^[i] I := by
        rw [← hrep_eq I _ ⟨i, rfl⟩, hII]
        exact hne.symm
      have h1 := hc ⟨_, hmax'⟩
      simpa [W, hr] using h1
  have hzfix : T (∏ i ∈ range ℓ, (T ^ i) (cu : B) - a) = ∏ i ∈ range ℓ, (T ^ i) (cu : B) - a := by
    rw [map_sub, norm_fixed T ℓ hℓ hT, hfix]
  have hz : ∀ k : ℕ, (T ^ k) (∏ i ∈ range ℓ, (T ^ i) (cu : B) - a) =
      ∏ i ∈ range ℓ, (T ^ i) (cu : B) - a := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ']
      show T ((T ^ k) _) = _
      rw [ih, hzfix]
  rw [← hi0, mem_pull_iter, hz]
  exact hmemI

end Core2

theorem fixed_tensor {κ κ' A : Type*} [Field κ] [CommRing κ'] [Algebra κ κ'] [CommRing A] [Algebra κ A]
    (τ : κ' ≃ₐ[κ] κ') (hfix : ∀ z : κ', τ z = z → z ∈ Set.range (algebraMap κ κ'))
    (s : κ' ⊗[κ] A) (hs : Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id κ A) s = s) :
    ∃ t : A, s = 1 ⊗ₜ[κ] t := by
  classical
  let C := Module.Basis.ofVectorSpace κ A
  obtain ⟨b, rfl⟩ := TensorProduct.eq_repr_basis_right C s
  have hinj := TensorProduct.sum_tmul_basis_right_injective (M := κ') C
  have hbb : b.mapRange τ (map_zero τ) = b := by
    apply hinj
    simp only [Finsupp.coe_lsum]
    change (Finsupp.mapRange τ (map_zero τ) b).sum (fun i m => m ⊗ₜ[κ] C i) =
      b.sum (fun i m => m ⊗ₜ[κ] C i)
    rw [Finsupp.sum_mapRange_index (by simp)]
    conv_rhs => rw [← hs]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Finsupp.sum, map_sum]
  have hb : ∀ i, τ (b i) = b i := fun i => by
    have := DFunLike.congr_fun hbb i
    simpa using this
  choose t ht using fun i => hfix (b i) (hb i)
  refine ⟨∑ i ∈ b.support, t i • C i, ?_⟩
  rw [Finsupp.sum, TensorProduct.tmul_sum]
  apply sum_congr rfl
  intro i _
  rw [← ht i, TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul']

end GlobalTheory.CompanionTheory.NormOnto

namespace GlobalTheory.CompanionTheory.NormOnto

theorem norm_onto : PositivityTheory.Rg.Tf.Loc.N1 := by
  intro κ κ' A _ _ _ _ _ _ _ _ _ ℓ τ hℓ hτ hfix hdual a
  obtain ⟨x, y, hxy⟩ := hdual
  classical
  by_cases hκ' : Subsingleton κ'
  · haveI : Subsingleton (κ' ⊗[κ] A) := by
      refine ⟨fun p q => ?_⟩
      have hz : ∀ s : κ' ⊗[κ] A, s = 0 := by
        intro s
        induction s with
        | tmul z b => rw [Subsingleton.elim z 0, TensorProduct.zero_tmul]
        | add u v hu hv => rw [hu, hv, add_zero]
      rw [hz p, hz q]
    exact ⟨1, Subsingleton.elim _ _⟩
  haveI : Nontrivial κ' := not_subsingleton_iff_nontrivial.1 hκ'
  haveI : Finite κ' := Module.finite_of_finite κ
  haveI : Finite (κ' ⊗[κ] A) := Module.finite_of_finite κ
  let T : RingAut (κ' ⊗[κ] A) :=
    (Algebra.TensorProduct.congr τ (AlgEquiv.refl : A ≃ₐ[κ] A)).toRingEquiv
  have hT1 : ∀ (z : κ') (b : A), T (z ⊗ₜ[κ] b) = τ z ⊗ₜ[κ] b := fun z b => rfl
  have hTm : ∀ (i : ℕ) (z : κ') (b : A), (T ^ i) (z ⊗ₜ[κ] b) = (τ ^ i) z ⊗ₜ[κ] b := by
    intro i
    induction i with
    | zero => intro z b; rfl
    | succ i ih =>
      intro z b
      rw [pow_succ', pow_succ']
      show T ((T ^ i) _) = τ ((τ ^ i) z) ⊗ₜ[κ] b
      rw [ih, hT1]
  have hTi : ∀ (i : ℕ) (s : κ' ⊗[κ] A),
      Algebra.TensorProduct.map ((τ ^ i : κ' ≃ₐ[κ] κ').toAlgHom) (AlgHom.id κ A) s = (T ^ i) s := by
    intro i s
    induction s with
    | tmul z b => rw [hTm]; rfl
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), hu, hv]
  have hT : T ^ ℓ = 1 := by
    ext s
    rw [← hTi, hτ]
    induction s with
    | tmul z b => rfl
    | add u v hu hv => rw [map_add (f := _), hu, hv]; rfl
  have hXY : ∀ j < ℓ, ∑ i, (x i ⊗ₜ[κ] (1 : A)) * (T ^ j) (y i ⊗ₜ[κ] (1 : A)) =
      if j = 0 then 1 else 0 := by
    intro j hj
    have h := congrArg (fun z : κ' => z ⊗ₜ[κ] (1 : A)) (hxy j hj)
    simp only [TensorProduct.sum_tmul] at h
    simp only [hTm, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [h]
    split_ifs
    · rfl
    · exact TensorProduct.zero_tmul _ _
  have haU : IsUnit ((1 : κ') ⊗ₜ[κ] (a : A)) :=
    a.isUnit.map (Algebra.TensorProduct.includeRight : A →ₐ[κ] κ' ⊗[κ] A)
  obtain ⟨c, hc⟩ := norm_mod_max T ℓ hℓ hT ℓ (fun i => x i ⊗ₜ[κ] (1 : A))
    (fun i => y i ⊗ₜ[κ] (1 : A)) hXY _ haU (by rw [hT1, map_one])
  refine ⟨c, ?_⟩
  simp only [hTi]
  rw [Algebra.TensorProduct.includeRight_apply, ← sub_eq_zero]
  set z := ∏ i ∈ range ℓ, (T ^ i) (c : κ' ⊗[κ] A) - (1 : κ') ⊗ₜ[κ] (a : A) with hz
  have hzfix : T z = z := by
    rw [hz, map_sub, norm_fixed T ℓ hℓ hT, hT1, map_one]
  obtain ⟨t, ht⟩ := fixed_tensor τ hfix z (by
    have := hTi 1 z
    rw [pow_one, pow_one] at this
    exact this.trans hzfix)
  have hznil : IsNilpotent z := by
    have hj : z ∈ (⊥ : Ideal (κ' ⊗[κ] A)).jacobson := by
      rw [Ideal.jacobson, Ideal.mem_sInf]
      rintro M ⟨-, hM⟩
      exact hc M hM
    rw [IsArtinianRing.jacobson_eq_radical] at hj
    obtain ⟨k, hk⟩ := hj
    exact ⟨k, by simpa using hk⟩
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeRight : A →ₐ[κ] κ' ⊗[κ] A) :=
    Algebra.TensorProduct.includeRight_injective (FaithfulSMul.algebraMap_injective κ κ')
  have htn : IsNilpotent t := by
    obtain ⟨k, hk⟩ := hznil
    refine ⟨k, hinj ?_⟩
    rw [map_pow, map_zero, Algebra.TensorProduct.includeRight_apply, ← ht, hk]
  have ht0 : t = 0 := htn.eq_zero
  rw [ht, ht0, TensorProduct.tmul_zero]

end GlobalTheory.CompanionTheory.NormOnto
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapFirstPropertyStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_map_first_property : PositivityTheory.Rg.Tf.Loc.N1 := by
  first | exact @GlobalTheory.CompanionTheory.NormOnto.norm_onto | exact GlobalTheory.CompanionTheory.NormOnto.norm_onto | (intros; apply GlobalTheory.CompanionTheory.NormOnto.norm_onto <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCentralizerIdentification
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCentralizerIdentification
open Polynomial
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.CyclicCocycle

theorem infinite_of_localField (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Infinite K := by
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation K)
  by_contra h
  rw [not_infinite_iff_finite] at h
  have hr : r ≠ 0 := fun h0 => hr0 (by simp [h0])
  obtain ⟨m, hm, hmm⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite (Units.mk0 r hr))
  have h1 : r ^ m = 1 := by simpa using congrArg Units.val hmm
  have h2 : (ValuativeRel.valuation K r) ^ m = 1 := by rw [← map_pow, h1, map_one]
  exact absurd h2 (pow_lt_one₀ zero_le' hr1 hm.ne').ne

theorem exists_det_ne_zero {k E : Type*} [Field k] [Field E] [Algebra k E] [Infinite k]
    {m n : ℕ} (y : Fin m → Matrix (Fin n) (Fin n) E) (a : Fin m → E)
    (h : (∑ j, a j • y j).det ≠ 0) :
    ∃ t : Fin m → k, (∑ j, algebraMap k E (t j) • y j).det ≠ 0 := by
  classical
  let A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) E) :=
    ∑ j, (MvPolynomial.X j : MvPolynomial (Fin m) E) • (y j).map MvPolynomial.C
  have hev : ∀ v : Fin m → E, MvPolynomial.eval v A.det = (∑ j, v j • y j).det := by
    intro v
    rw [RingHom.map_det]
    congr 1
    ext p q
    simp [A, Matrix.sum_apply]
  by_contra hcon
  push Not at hcon
  have hzero : A.det = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (algebraMap k E)) (fun _ => ?_)
      (fun v hv => ?_)
    · exact Set.infinite_range_of_injective (algebraMap k E).injective
    · have hv' : ∀ i, ∃ t : k, algebraMap k E t = v i := fun i => hv i (Set.mem_univ i)
      choose t ht using hv'
      rw [hev, map_zero]
      have := hcon t
      simpa [ht] using this
  exact h (by rw [← hev, hzero, map_zero])

theorem exists_dual {k E : Type*} [Field k] [Field E] [Algebra k E] {ℓ : ℕ} (σ : E ≃ₐ[k] E)
    (hinj : Set.InjOn (fun i : ℕ => σ ^ i) (Set.Iio ℓ)) (b : Module.Basis (Fin ℓ) k E) :
    ∃ a : Fin ℓ → E, ∀ i : Fin ℓ,
      ∑ j, a j * (σ ^ (i : ℕ)) (b j) = if (i : ℕ) = 0 then 1 else 0 := by
  classical
  let M : Matrix (Fin ℓ) (Fin ℓ) E := Matrix.of fun i j => (σ ^ (i : ℕ)) (b j)
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    have hvj : ∀ j, ∑ i, v i * (σ ^ (i : ℕ)) (b j) = 0 := by
      intro j
      have := congrFun hv j
      simpa [Matrix.vecMul, dotProduct, M] using this
    have hall : ∀ z : E, ∑ i, v i * (σ ^ (i : ℕ)) z = 0 := by
      intro z
      rw [← b.sum_repr z]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := congrArg (fun w => b.repr z j • w) (hvj j)
      simp only [smul_zero, Finset.smul_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul_comm]
    let f : Fin ℓ → (E →* E) := fun i => ((σ ^ (i : ℕ) : E ≃ₐ[k] E) : E →* E)
    have hf : Function.Injective f := by
      intro i j hij
      have h1 : (σ ^ (i : ℕ) : E ≃ₐ[k] E) = σ ^ (j : ℕ) := by
        ext z
        exact DFunLike.congr_fun hij z
      exact Fin.ext (hinj i.2 j.2 h1)
    have li := (linearIndependent_monoidHom E E).comp f hf
    have hz := Fintype.linearIndependent_iff.mp li v (by
      funext z
      simpa [f] using hall z)
    exact hv0 (funext hz)
  let e : Fin ℓ → E := fun i => if (i : ℕ) = 0 then 1 else 0
  refine ⟨M⁻¹.mulVec e, fun i => ?_⟩
  have h1 : M.mulVec (M⁻¹.mulVec e) = e := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have h2 := congrFun h1 i
  simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply] at h2
  simp only [e] at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem inv_mem_range {E : Type*} [Field E] {n : ℕ} (Γ X : Matrix (Fin n) (Fin n) E)
    (hX : ∃ p : E[X], X = aeval Γ p) (hd : X.det ≠ 0) : ∃ q : E[X], X⁻¹ = aeval Γ q := by
  obtain ⟨p, hp⟩ := hX
  have hc : X.charpoly.coeff 0 ≠ 0 := by
    intro h0
    apply hd
    rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
  set c := X.charpoly.coeff 0 with hcdef
  have h1 : aeval X (divX X.charpoly) * X + algebraMap E _ c = 0 := by
    have h := Matrix.aeval_self_charpoly X
    rw [← divX_mul_X_add X.charpoly] at h
    simpa [map_add (f := _), map_mul, aeval_X, aeval_C, ← hcdef] using h
  have h2 : (-(c⁻¹) • aeval X (divX X.charpoly)) * X = 1 := by
    rw [Matrix.smul_mul, eq_neg_of_add_eq_zero_left h1, smul_neg, neg_smul, neg_neg,
      Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hc, one_smul]
  refine ⟨C (-(c⁻¹)) * (divX X.charpoly).comp p, ?_⟩
  rw [Matrix.inv_eq_left_inv h2, map_mul, aeval_C, aeval_comp, ← hp,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

variable {k E : Type*} [Field k] [Field E] [Algebra k E] {n : ℕ}

theorem map_aeval_incl (σ : E ≃ₐ[k] E) (γ : GL (Fin n) k) (p : E[X]) :
    (aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p).map σ =
      aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
        (p.map (σ.toAlgHom.toRingHom)) := by
  set Γ := ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hΓ
  have hfix : (σ.toAlgHom.toRingHom).mapMatrix Γ = Γ := by
    ext i j
    have : Γ i j = algebraMap k E ((γ : Matrix (Fin n) (Fin n) k) i j) := rfl
    simp [this]
  have h1 : (aeval Γ p).map σ = (σ.toAlgHom.toRingHom).mapMatrix (aeval Γ p) := rfl
  rw [h1, aeval_def, aeval_def, hom_eval₂, hfix, eval₂_map]
  congr 1
  ext a i j
  by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]

def cMat (σ : E ≃ₐ[k] E) (u : GL (Fin n) E) (i : ℕ) : Matrix (Fin n) (Fin n) E :=
  ((twNorm (sigmaGL σ) i u : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)

def res (σ : E ≃ₐ[k] E) (ℓ : ℕ) (u : GL (Fin n) E) (s : E) : Matrix (Fin n) (Fin n) E :=
  ∑ i ∈ Finset.range ℓ, ((σ ^ i) s) • cMat σ u i

theorem cMat_succ (σ : E ≃ₐ[k] E) (u : GL (Fin n) E) (i : ℕ) :
    (u : Matrix (Fin n) (Fin n) E) * (cMat σ u i).map σ = cMat σ u (i + 1) := by
  have h : u * sigmaGL σ (twNorm (sigmaGL σ) i u) = twNorm (sigmaGL σ) (i + 1) u := by
    rw [map_twNorm, twNorm_succ]
    group
  exact congrArg Units.val h

theorem mul_map_res (σ : E ≃ₐ[k] E) {ℓ : ℕ} (hℓ : σ ^ ℓ = 1) (u : GL (Fin n) E)
    (hN : twNorm (sigmaGL σ) ℓ u = 1) (s : E) :
    (u : Matrix (Fin n) (Fin n) E) * (res σ ℓ u s).map σ = res σ ℓ u s := by
  set f : ℕ → Matrix (Fin n) (Fin n) E := fun i => ((σ ^ i) s) • cMat σ u i with hf
  have h1 : (res σ ℓ u s).map σ = ∑ i ∈ Finset.range ℓ, ((σ ^ (i + 1)) s) • (cMat σ u i).map σ := by
    ext p q
    simp [res, Matrix.sum_apply, pow_succ']
  have h2 : (u : Matrix (Fin n) (Fin n) E) * (res σ ℓ u s).map σ =
      ∑ i ∈ Finset.range ℓ, f (i + 1) := by
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_smul, cMat_succ]
  have h3 : f ℓ = f 0 := by
    have hs : (σ ^ ℓ) s = s := by rw [hℓ]; rfl
    change ((σ ^ ℓ) s) • cMat σ u ℓ = ((σ ^ 0) s) • cMat σ u 0
    rw [hs]
    simp [cMat, hN]
  have h4 := Finset.sum_range_succ f ℓ
  rw [Finset.sum_range_succ' f ℓ, h3] at h4
  rw [h2]
  exact add_right_cancel h4

theorem exists_res_det_ne_zero [FiniteDimensional k E] [IsGalois k E] [Infinite k]
    (σ : E ≃ₐ[k] E) (hgen : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) (u : GL (Fin n) E) :
    ∃ s : E, (res σ (Module.finrank k E) u s).det ≠ 0 := by
  classical
  have hord : orderOf σ = Module.finrank k E := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]
  have hinj : Set.InjOn (fun i : ℕ => σ ^ i) (Set.Iio (Module.finrank k E)) := by
    rw [← hord]
    exact pow_injOn_Iio_orderOf
  have hpos : 0 < Module.finrank k E := Module.finrank_pos
  let b := Module.finBasis k E
  obtain ⟨a, ha⟩ := exists_dual σ hinj b
  let y : Fin (Module.finrank k E) → Matrix (Fin n) (Fin n) E :=
    fun j => res σ (Module.finrank k E) u (b j)
  have hone : ∑ j, a j • y j = 1 := by
    have h1 : ∀ j, a j • y j = ∑ i : Fin (Module.finrank k E),
        (a j * (σ ^ (i : ℕ)) (b j)) • cMat σ u i := by
      intro j
      simp only [y, res]
      rw [Finset.sum_range, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
    simp only [h1]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ha]
    rw [Finset.sum_eq_single (⟨0, hpos⟩ : Fin (Module.finrank k E))]
    · simp [cMat]
    · intro i _ hi
      have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
      simp [this]
    · simp
  obtain ⟨t, ht⟩ := exists_det_ne_zero (k := k) y a (by rw [hone]; simp)
  refine ⟨∑ j, t j • b j, ?_⟩
  have : res σ (Module.finrank k E) u (∑ j, t j • b j) = ∑ j, algebraMap k E (t j) • y j := by
    simp only [y, res, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_smul, Algebra.smul_def (t j)]
  rwa [this]

theorem cocycle [FiniteDimensional k E] [IsGalois k E] [Infinite k]
    (σ : E ≃ₐ[k] E) (hgen : ∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ)
    (γ : GL (Fin n) k) (u : GL (Fin n) E)
    (hu : ∃ p : E[X], (u : Matrix (Fin n) (Fin n) E) =
      aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) p)
    (hN : normGL σ u = 1) :
    ∃ x : GL (Fin n) E,
      (∃ q : E[X], (x : Matrix (Fin n) (Fin n) E) =
        aeval ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) q) ∧
      u = x⁻¹ * sigmaGL σ x := by
  classical
  have hℓ : σ ^ Module.finrank k E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact pow_card_eq_one'
  set Γ := ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) with hΓ
  let S := (aeval Γ : E[X] →ₐ[E] Matrix (Fin n) (Fin n) E).range
  have hmemS : ∀ {M : Matrix (Fin n) (Fin n) E}, M ∈ S ↔ ∃ p : E[X], M = aeval Γ p := by
    intro M
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p, rfl⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p, rfl⟩
  have hmap : ∀ {M : Matrix (Fin n) (Fin n) E}, M ∈ S → M.map σ ∈ S := by
    intro M hM
    obtain ⟨p, rfl⟩ := hmemS.mp hM
    exact hmemS.mpr ⟨_, map_aeval_incl σ γ p⟩
  have hc : ∀ i, cMat σ u i ∈ S := by
    intro i
    induction i with
    | zero =>
      have : cMat σ u 0 = 1 := by simp [cMat]
      rw [this]
      exact S.one_mem
    | succ i ih =>
      rw [← cMat_succ]
      exact S.mul_mem (hmemS.mpr hu) (hmap ih)
  obtain ⟨s, hs⟩ := exists_res_det_ne_zero σ hgen u
  set X := res σ (Module.finrank k E) u s with hX
  have hXS : X ∈ S := S.sum_mem fun i _ => S.smul_mem (hc i) _
  let Xu : GL (Fin n) E := Matrix.GeneralLinearGroup.mkOfDetNeZero X hs
  have hXu : (Xu : Matrix (Fin n) (Fin n) E) = X := rfl
  have hfun : u * sigmaGL σ Xu = Xu := Units.ext (mul_map_res σ hℓ u hN s)
  refine ⟨Xu⁻¹, ?_, ?_⟩
  · rw [Matrix.coe_units_inv, hXu]
    exact inv_mem_range Γ X (hmemS.mp hXS) hs
  · rw [inv_inv, map_inv]
    exact eq_mul_inv_of_mul_eq hfun

theorem cyclicCocycleLemma : PositivityTheory.Rg.Tf.Loc.A2 → PositivityTheory.Rg.Tf.Loc.A3 := by
  intro _ k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n γ _ u hu hN
  haveI := infinite_of_localField k
  exact cocycle σ hgen γ u hu hN

end GlobalTheory.CompanionTheory.CyclicCocycle
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCentralizerIdentificationStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_centralizer_identification : PositivityTheory.Rg.Tf.Loc.A2 → PositivityTheory.Rg.Tf.Loc.A3 := by
  first | exact @GlobalTheory.CompanionTheory.CyclicCocycle.cyclicCocycleLemma | exact GlobalTheory.CompanionTheory.CyclicCocycle.cyclicCocycleLemma | (intros; apply GlobalTheory.CompanionTheory.CyclicCocycle.cyclicCocycleLemma <;> assumption)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.QuotientIntegralOfCompactOpen
open MeasureTheory
open scoped ENNReal

namespace PositivityTheory.Rg.Tf.Loc

theorem quotient_integral_of_compact_open (hT : T0) (h : QuotientIntegralCompactOpen) : H2 := by
  intro F _ _ _ _ n _ _ μG H μH h1 h2 h3 h4 Fn _ h5 h6 Rp h7 h8
  obtain ⟨-, -, ho, hc⟩ := hT.1 F n
  exact h F n μG H μH (unitGL F) ho hc h1 h2 h3 h4 Fn h5 h6 Rp h7 h8

theorem measure_transport_of_open_set (hT : T0) (hD : D0a) (h : MeasureTransportOpenSet) : H4 := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ hun σ hgen n _ _ _ _ δ γ hh μδ μγ h1 h2 h3 y z hz
  exact h k E hun σ hgen n (unitGL E : Subgroup (GL (Fin n) E)) (unitGL k : Subgroup (GL (Fin n) k))
    (hT.1 E n).2.2.1 (fun g => (hD k E hun σ hgen).2.2.1 n g) δ γ hh μδ μγ h1 h2 h3 y z hz

theorem bcflUnit_of_leaves (hD0a : D0a) (hD0b : D0a → IntegralBasisUnramified) (hD0c : IntegralBasisUnramified → TraceOneIntegralElement) (hT0 : T0) (hA1 : A1)
    (hA2 : A1 → A2) (hA3 : A2 → A3) (hN1 : N1) (hN2 : N2) (hN3 : N1 → N2 → N3)
    (hN4 : D0a → IntegralBasisUnramified → TraceOneIntegralElement → N3 → N4) (hL1 : L1) (hL2 : D0a → L2) (hL3 : TraceOneIntegralElement → L1 → L3)
    (hL4 : D0a → A1 → L4) (hH2U : QuotientIntegralCompactOpen) (hH3 : H3) (hH4U : D0a → T0 → A1 → MeasureTransportOpenSet)
    (hZ1 : D0a → T0 → A1 → A2 → A3 → N4 → L2 → L3 → L4 → H2 → H3 → H4 → Z1)
    (hZ2 : L2 → N4 → Z2) : BCFLUnit := by
  have b := hD0b hD0a
  have c := hD0c b
  have a2 := hA2 hA1
  have n4 := hN4 hD0a b c (hN3 hN1 hN2)
  have l2 := hL2 hD0a
  have z1 := hZ1 hD0a hT0 hA1 a2 (hA3 a2) n4 l2 (hL3 c hL1) (hL4 hD0a hA1) (quotient_integral_of_compact_open hT0 hH2U) hH3
    (measure_transport_of_open_set hT0 hD0a (hH4U hD0a hT0 hA1))
  have z2 := hZ2 l2 n4
  intro k E
  intros
  exact ⟨by apply z1 <;> assumption, by apply z2 <;> assumption⟩

end PositivityTheory.Rg.Tf.Loc
end

namespace PositivityTheory.Rg.Tf.Loc

theorem bcflUnit : BCFLUnit :=
  bcflUnit_of_leaves GlobalTheory.T.unramified_extension_integral_basis GlobalTheory.T.integralBasisUnramified_of_d0a GlobalTheory.T.unramified_dual_family_holds GlobalTheory.T.norm_map_torus_surjective GlobalTheory.T.separable_norm_commuting GlobalTheory.T.norm_commutes_separable_holds GlobalTheory.T.norm_centralizer_identification GlobalTheory.T.norm_map_first_property GlobalTheory.T.norm_map_second_property GlobalTheory.T.norm_map_third_property GlobalTheory.T.norm_map_integral_property GlobalTheory.T.lattice_first_property GlobalTheory.T.lattice_second_property GlobalTheory.T.lattice_third_property GlobalTheory.T.lattice_fourth_property GlobalTheory.T.unipotent_hecke_support GlobalTheory.T.hecke_third_property GlobalTheory.T.unipotent_hecke_fourth_property GlobalTheory.T.unit_fundamental_lemma_first_holds GlobalTheory.T.unit_fundamental_lemma_second_holds

end PositivityTheory.Rg.Tf.Loc
