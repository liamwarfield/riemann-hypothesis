module

public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealOrder
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealEtaleBaseChange
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates

private def derivationCompAlgebraMap (k : Type*) [CommRing k] (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T] (D : Derivation k T T) :
    Derivation k S T :=
  Derivation.mk' (D.toLinearMap.comp (IsScalarTower.toAlgHom k S T).toLinearMap) (by
    intro a b
    show D (algebraMap S T (a * b)) = a • D (algebraMap S T b) + b • D (algebraMap S T a)
    rw [map_mul, D.leibniz, smul_eq_mul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def])

private theorem derivation_comp_algebraMap_apply (k : Type*) [CommRing k] (S : Type*) [CommRing S]
    (T : Type*) [CommRing T] [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (D : Derivation k T T) (s : S) :
    derivationCompAlgebraMap k S T D s = D (algebraMap S T s) := rfl

private def algebraMapCompDerivation (k : Type*) [CommRing k] (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T] (D : Derivation k S S) :
    Derivation k S T :=
  Derivation.mk' ((IsScalarTower.toAlgHom k S T).toLinearMap.comp D.toLinearMap) (by
    intro a b
    show algebraMap S T (D (a * b)) = a • algebraMap S T (D b) + b • algebraMap S T (D a)
    rw [D.leibniz, map_add (f := _), smul_eq_mul, smul_eq_mul, map_mul, map_mul, Algebra.smul_def,
      Algebra.smul_def])

private theorem algebraMap_comp_derivation_apply (k : Type*) [CommRing k] (S : Type*) [CommRing S]
    (T : Type*) [CommRing T] [Algebra k S] [Algebra k T] [Algebra S T] [IsScalarTower k S T]
    (D : Derivation k S S) (s : S) :
    algebraMapCompDerivation k S T D s = algebraMap S T (D s) := rfl

theorem derivation_ext_of_coord (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
    [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    (M : Type*) [AddCommGroup M] [Module k M] [Module S M] [IsScalarTower k S M]
    (D₁ D₂ : Derivation k S M)
    (h : ∀ i : ι, D₁ (coord k ι S i) = D₂ (coord k ι S i)) : D₁ = D₂ := by
  have key : D₁.liftKaehlerDifferential = D₂.liftKaehlerDifferential := by
    refine (basisKaehler k ι S).ext ?_
    intro i
    rw [basisKaehler_apply, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    exact h i
  refine Derivation.ext fun x => ?_
  rw [← Derivation.liftKaehlerDifferential_comp_D D₁ x,
    ← Derivation.liftKaehlerDifferential_comp_D D₂ x, key]

theorem partialDeriv_inr_algebraMap (k : Type*) [CommRing k] (ι : Type*) (κ : Type*)
    (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (j : κ) (s : S) :
    partialDeriv k (ι ⊕ κ) T (Sum.inr j) (algebraMap S T s) = 0 := by
  have key : derivationCompAlgebraMap k S T (partialDeriv k (ι ⊕ κ) T (Sum.inr j)) = 0 := by
    refine derivation_ext_of_coord k ι S T _ _ ?_
    intro i
    rw [derivation_comp_algebraMap_apply, hcoord i,
      partialDeriv_coord_of_ne k (ι ⊕ κ) T (Sum.inr j) (Sum.inl i) (by simp)]
    have h0 : ((0 : Derivation k S T)) (coord k ι S i) = 0 := rfl
    rw [h0]
  have h2 := DFunLike.congr_fun key s
  rw [derivation_comp_algebraMap_apply] at h2
  have h0 : ((0 : Derivation k S T)) s = 0 := rfl
  rw [h0] at h2
  exact h2

theorem partialDeriv_inl_algebraMap (k : Type*) [CommRing k] (ι : Type*) (κ : Type*)
    [DecidableEq ι] [DecidableEq κ]
    (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (i : ι) (s : S) :
    partialDeriv k (ι ⊕ κ) T (Sum.inl i) (algebraMap S T s)
      = algebraMap S T (partialDeriv k ι S i s) := by
  have key : derivationCompAlgebraMap k S T (partialDeriv k (ι ⊕ κ) T (Sum.inl i))
      = algebraMapCompDerivation k S T (partialDeriv k ι S i) := by
    refine derivation_ext_of_coord k ι S T _ _ ?_
    intro j
    rw [derivation_comp_algebraMap_apply, algebraMap_comp_derivation_apply, hcoord j]
    by_cases hij : i = j
    · subst hij
      rw [partialDeriv_coord_self, partialDeriv_coord_self, map_one]
    · rw [partialDeriv_coord_of_ne k (ι ⊕ κ) T (Sum.inl i) (Sum.inl j) (by simpa using hij),
        partialDeriv_coord_of_ne k ι S i j hij, map_zero]
  have h2 := DFunLike.congr_fun key s
  rw [derivation_comp_algebraMap_apply, algebraMap_comp_derivation_apply] at h2
  exact h2

theorem map_derivIdeal_sum (k : Type*) [CommRing k] (ι : Type*) (κ : Type*)
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (S : Type*) [CommRing S] (T : Type*) [CommRing T]
    [Algebra k S] [Algebra (MvPolynomial ι k) S] [IsScalarTower k (MvPolynomial ι k) S]
    [Algebra.FormallyEtale (MvPolynomial ι k) S]
    [Algebra k T] [Algebra (MvPolynomial (ι ⊕ κ) k) T]
    [IsScalarTower k (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra.FormallyEtale (MvPolynomial (ι ⊕ κ) k) T]
    [Algebra S T] [IsScalarTower k S T]
    (hcoord : ∀ i : ι, algebraMap S T (coord k ι S i) = coord k (ι ⊕ κ) T (Sum.inl i))
    (J : Ideal S) :
    Ideal.map (algebraMap S T) (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S T) J) := by
  have key1 : ∀ (D : Derivation k S S) (y : S), y ∈ J →
      algebraMap S T (D y) ∈ derivIdeal k (Ideal.map (algebraMap S T) J) := by
    intro D y hy
    have hsp : D ∈ Submodule.span S (Set.range (partialDeriv k ι S)) := by
      rw [span_range_partialDeriv]
      exact Submodule.mem_top
    induction hsp using Submodule.span_induction with
    | mem D hD =>
        obtain ⟨i, rfl⟩ := hD
        rw [← partialDeriv_inl_algebraMap k ι κ S T hcoord i y]
        exact derivation_apply_mem_derivIdeal k _ _ (Ideal.mem_map_of_mem _ hy)
    | zero =>
        have h0 : ((0 : Derivation k S S)) y = 0 := rfl
        rw [h0, map_zero]
        exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
        have h0 : (a + b) y = a y + b y := rfl
        rw [h0, map_add (f := _)]
        exact Ideal.add_mem _ ha hb
    | smul c a _ ha =>
        have h0 : (c • a) y = c * a y := rfl
        rw [h0, map_mul]
        exact Ideal.mul_mem_left _ _ ha
  have key2 : ∀ (D' : Derivation k T T) (y : S), y ∈ J →
      D' (algebraMap S T y) ∈ Ideal.map (algebraMap S T) (derivIdeal k J) := by
    intro D' y hy
    have hsp : D' ∈ Submodule.span T (Set.range (partialDeriv k (ι ⊕ κ) T)) := by
      rw [span_range_partialDeriv]
      exact Submodule.mem_top
    induction hsp using Submodule.span_induction with
    | mem D hD =>
        obtain ⟨x, rfl⟩ := hD
        cases x with
        | inl i =>
            rw [partialDeriv_inl_algebraMap k ι κ S T hcoord i y]
            exact Ideal.mem_map_of_mem _
              (derivation_apply_mem_derivIdeal k J (partialDeriv k ι S i) hy)
        | inr j =>
            rw [partialDeriv_inr_algebraMap k ι κ S T hcoord j y]
            exact Submodule.zero_mem _
    | zero =>
        have h0 : ((0 : Derivation k T T)) (algebraMap S T y) = 0 := rfl
        rw [h0]
        exact Submodule.zero_mem _
    | add a b _ _ ha hb =>
        have h0 : (a + b) (algebraMap S T y)
            = a (algebraMap S T y) + b (algebraMap S T y) := rfl
        rw [h0]
        exact Ideal.add_mem _ ha hb
    | smul c a _ ha =>
        have h0 : (c • a) (algebraMap S T y) = c * a (algebraMap S T y) := rfl
        rw [h0]
        exact Ideal.mul_mem_left _ _ ha
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap, derivIdeal_le_iff]
    refine ⟨fun y hy => Ideal.mem_comap.mpr (le_derivIdeal k _ (Ideal.mem_map_of_mem _ hy)), ?_⟩
    intro D y hy
    exact Ideal.mem_comap.mpr (key1 D y hy)
  · rw [derivIdeal_le_iff]
    refine ⟨Ideal.map_mono (le_derivIdeal k J), ?_⟩
    intro D' z hz
    have hspan : Ideal.map (algebraMap S T) J
        = Ideal.span ((algebraMap S T) '' (J : Set S)) := by
      rw [← Ideal.map_span, Ideal.span_eq]
    rw [hspan] at hz
    refine derivation_apply_mem_of_mem_span D' ?_ ?_ hz
    · rw [← hspan]
      exact Ideal.map_mono (le_derivIdeal k J)
    · rintro g ⟨y, hy, rfl⟩
      exact key2 D' y hy

end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdeal
namespace FunctorialResolution.EmbeddedResolution

variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]

def tangentDerivations (P : Ideal S) : Submodule S (Derivation k S S) where
  carrier := {D : Derivation k S S | ∀ x ∈ P, D x ∈ P}
  add_mem' := by
    intro D D' hD hD' x hx
    have h := P.add_mem (hD x hx) (hD' x hx)
    simpa using h
  zero_mem' := by
    intro x _
    simp
  smul_mem' := by
    intro a D hD x hx
    have h := Ideal.mul_mem_left P a (hD x hx)
    simpa [smul_eq_mul] using h

theorem mem_tangentDerivations (P : Ideal S) (D : Derivation k S S) :
    D ∈ tangentDerivations k P ↔ ∀ x ∈ P, D x ∈ P := Iff.rfl

theorem smul_mem_tangentDerivations (P : Ideal S) {p : S} (hp : p ∈ P)
    (D : Derivation k S S) : p • D ∈ tangentDerivations k P := by
  rw [mem_tangentDerivations]
  intro x _
  have h := Ideal.mul_mem_right (D x) P hp
  simpa [smul_eq_mul] using h

theorem mem_tangentDerivations_span_singleton (x : S) (D : Derivation k S S) :
    D ∈ tangentDerivations k (Ideal.span ({x} : Set S)) ↔
      D x ∈ Ideal.span ({x} : Set S) := by
  rw [mem_tangentDerivations]
  constructor
  · intro hD
    exact hD x (Ideal.subset_span (Set.mem_singleton x))
  · intro hD y hy
    refine derivation_apply_mem_of_mem_span D le_rfl ?_ hy
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hD

def logDerivIdeal (P J : Ideal S) : Ideal S :=
  J ⊔ Ideal.span {x : S | ∃ D ∈ tangentDerivations k P, ∃ y ∈ J, D y = x}

private theorem logDerivIdeal_eq_sup_span (P J : Ideal S) :
    logDerivIdeal k P J =
      J ⊔ Ideal.span {x : S | ∃ D ∈ tangentDerivations k P, ∃ y ∈ J, D y = x} := rfl

theorem le_logDerivIdeal (P J : Ideal S) : J ≤ logDerivIdeal k P J := by
  rw [logDerivIdeal_eq_sup_span]
  exact le_sup_left

theorem derivation_apply_mem_logDerivIdeal (P J : Ideal S) (D : Derivation k S S)
    (hD : D ∈ tangentDerivations k P) {x : S} (hx : x ∈ J) :
    D x ∈ logDerivIdeal k P J := by
  rw [logDerivIdeal_eq_sup_span]
  exact Submodule.mem_sup_right (Ideal.subset_span ⟨D, hD, x, hx, rfl⟩)

theorem logDerivIdeal_le_iff (P J K : Ideal S) :
    logDerivIdeal k P J ≤ K ↔
      J ≤ K ∧ ∀ D ∈ tangentDerivations k P, ∀ x ∈ J, D x ∈ K := by
  rw [logDerivIdeal_eq_sup_span, sup_le_iff, Ideal.span_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun D hD x hx => h2 ⟨D, hD, x, hx, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro x ⟨D, hD, y, hy, rfl⟩
    exact h2 D hD y hy

theorem logDerivIdeal_mono (P : Ideal S) : Monotone (logDerivIdeal k P : Ideal S → Ideal S) := by
  intro I J h
  rw [logDerivIdeal_le_iff]
  refine ⟨h.trans (le_logDerivIdeal k P J), fun D hD x hx => ?_⟩
  exact derivation_apply_mem_logDerivIdeal k P J D hD (h hx)

theorem logDerivIdeal_le_logDerivIdeal (P : Ideal S) {I J : Ideal S} (h : I ≤ J) :
    logDerivIdeal k P I ≤ logDerivIdeal k P J :=
  logDerivIdeal_mono k P h

theorem logDerivIdeal_le_derivIdeal (P J : Ideal S) :
    logDerivIdeal k P J ≤ derivIdeal k J := by
  rw [logDerivIdeal_le_iff]
  refine ⟨le_derivIdeal k J, fun D _ x hx => ?_⟩
  exact derivation_apply_mem_derivIdeal k J D hx

theorem logDerivIdeal_top_eq_derivIdeal (J : Ideal S) :
    logDerivIdeal k (⊤ : Ideal S) J = derivIdeal k J := by
  refine le_antisymm (logDerivIdeal_le_derivIdeal k ⊤ J) ?_
  rw [derivIdeal_le_iff]
  refine ⟨le_logDerivIdeal k ⊤ J, fun D x hx => ?_⟩
  refine derivation_apply_mem_logDerivIdeal k ⊤ J D ?_ hx
  rw [mem_tangentDerivations]
  intro y _
  exact Submodule.mem_top

theorem logDerivIdeal_iSup_le {ι : Sort*} (P : Ideal S) (J : ι → Ideal S) :
    logDerivIdeal k P (⨆ i, J i) ≤ ⨆ i, logDerivIdeal k P (J i) := by
  rw [logDerivIdeal_le_iff]
  refine ⟨iSup_mono fun i => le_logDerivIdeal k P (J i), ?_⟩
  intro D hD x hx
  refine Submodule.iSup_induction
    (motive := fun z : S => D z ∈ ⨆ i, logDerivIdeal k P (J i)) J hx ?_ ?_ ?_
  · intro i y hy
    exact le_iSup (fun i => logDerivIdeal k P (J i)) i
      (derivation_apply_mem_logDerivIdeal k P (J i) D hD hy)
  · simpa only [map_zero] using Submodule.zero_mem (⨆ i, logDerivIdeal k P (J i))
  · intro a b ha hb
    simpa only [map_add (f := _)] using Submodule.add_mem (⨆ i, logDerivIdeal k P (J i)) ha hb

def logDerivIdealIterate (P : Ideal S) : ℕ → Ideal S → Ideal S
  | 0, J => J
  | r + 1, J => logDerivIdeal k P (logDerivIdealIterate P r J)

theorem logDerivIdealIterate_zero (P J : Ideal S) : logDerivIdealIterate k P 0 J = J := rfl

theorem logDerivIdealIterate_succ (P : Ideal S) (r : ℕ) (J : Ideal S) :
    logDerivIdealIterate k P (r + 1) J = logDerivIdeal k P (logDerivIdealIterate k P r J) := rfl

theorem logDerivIdealIterate_add (P : Ideal S) (r s : ℕ) (J : Ideal S) :
    logDerivIdealIterate k P (r + s) J =
      logDerivIdealIterate k P r (logDerivIdealIterate k P s J) := by
  induction r with
  | zero => rw [Nat.zero_add, logDerivIdealIterate_zero]
  | succ r ih => rw [Nat.succ_add, logDerivIdealIterate_succ, logDerivIdealIterate_succ, ih]

theorem le_logDerivIdealIterate (P : Ideal S) (r : ℕ) (J : Ideal S) :
    J ≤ logDerivIdealIterate k P r J := by
  induction r with
  | zero => exact (logDerivIdealIterate_zero k P J).ge
  | succ r ih =>
      rw [logDerivIdealIterate_succ]
      exact ih.trans (le_logDerivIdeal k P _)

theorem logDerivIdealIterate_mono (P : Ideal S) (r : ℕ) :
    Monotone (logDerivIdealIterate k P r : Ideal S → Ideal S) := by
  induction r with
  | zero =>
      intro I J h
      rw [logDerivIdealIterate_zero, logDerivIdealIterate_zero]
      exact h
  | succ r ih =>
      intro I J h
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ]
      exact logDerivIdeal_mono k P (ih h)

theorem logDerivIdealIterate_le_of_le (P : Ideal S) {r r' : ℕ} (h : r ≤ r') (J : Ideal S) :
    logDerivIdealIterate k P r J ≤ logDerivIdealIterate k P r' J := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm r d, logDerivIdealIterate_add]
  exact le_logDerivIdealIterate k P d _

theorem logDerivIdealIterate_top_eq_derivIdealIterate (r : ℕ) (J : Ideal S) :
    logDerivIdealIterate k (⊤ : Ideal S) r J = derivIdealIterate k r J := by
  induction r with
  | zero => rw [logDerivIdealIterate_zero, derivIdealIterate_zero]
  | succ r ih =>
      rw [logDerivIdealIterate_succ, derivIdealIterate_succ, ih, logDerivIdeal_top_eq_derivIdeal]

theorem logDerivIdealIterate_iSup_le {ι : Sort*} (P : Ideal S) (r : ℕ) (J : ι → Ideal S) :
    logDerivIdealIterate k P r (⨆ i, J i) ≤ ⨆ i, logDerivIdealIterate k P r (J i) := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
      rw [logDerivIdealIterate_succ]
      refine le_trans (logDerivIdeal_mono k P ih) ?_
      refine le_trans (logDerivIdeal_iSup_le k P fun i => logDerivIdealIterate k P r (J i)) ?_
      exact iSup_mono fun i => le_of_eq (logDerivIdealIterate_succ k P r (J i)).symm

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealOrderDecrease
namespace FunctorialResolution.EmbeddedResolution

open IsLocalRing

noncomputable def eulerDerivation (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R]
    {ι : Type*} [Fintype ι] (x : ι → R) (D : ι → Derivation k R R) : Derivation k R R :=
  ∑ i, x i • D i

private theorem sum_smul_derivation_apply (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [Algebra k R] {ι : Type*} (s : Finset ι) (x : ι → R) (D : ι → Derivation k R R) (a : R) :
    (∑ i ∈ s, x i • D i) a = ∑ i ∈ s, x i * D i a := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply,
        Derivation.smul_apply, smul_eq_mul, ih]

theorem eulerDerivation_apply (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R]
    {ι : Type*} [Fintype ι] (x : ι → R) (D : ι → Derivation k R R) (a : R) :
    eulerDerivation k x D a = ∑ i, x i * D i a := by
  show (∑ i, x i • D i) a = ∑ i, x i * D i a
  exact sum_smul_derivation_apply k Finset.univ x D a

theorem eulerDerivation_apply_mem_span (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R]
    {ι : Type*} [Fintype ι] (x : ι → R) (D : ι → Derivation k R R) (a : R) :
    eulerDerivation k x D a ∈ Ideal.span (Set.range x) := by
  rw [eulerDerivation_apply]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem eulerDerivation_apply_generator (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) (j : ι) :
    eulerDerivation k x D (x j) = x j := by
  rw [eulerDerivation_apply]
  simp [hD]

private theorem eulerDerivation_sub_self_mem_sq (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) {f : R}
    (hf : f ∈ Ideal.span (Set.range x)) :
    eulerDerivation k x D f - f ∈ Ideal.span (Set.range x) ^ 2 := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨j, rfl⟩ := hg
      rw [eulerDerivation_apply_generator k x D hD j, sub_self]
      exact Submodule.zero_mem _
  | zero =>
      rw [map_zero, sub_zero]
      exact Submodule.zero_mem _
  | add a b _ _ iha ihb =>
      have key : eulerDerivation k x D (a + b) - (a + b)
          = (eulerDerivation k x D a - a) + (eulerDerivation k x D b - b) := by
        rw [map_add (f := _)]; ring
      rw [key]
      exact Submodule.add_mem _ iha ihb
  | smul c a ha iha =>
      have key : eulerDerivation k x D (c • a) - c • a
          = c * (eulerDerivation k x D a - a) + a * eulerDerivation k x D c := by
        rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
      rw [key]
      refine Submodule.add_mem _ (Ideal.mul_mem_left _ _ iha) ?_
      have h2 := Ideal.mul_mem_mul ha (eulerDerivation_apply_mem_span k x D c)
      rwa [← pow_two] at h2

private theorem forall_eulerDerivation_sub_natCast_mul_mem (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) (r : ℕ) :
    ∀ f : R, f ∈ Ideal.span (Set.range x) ^ r →
      eulerDerivation k x D f - (r : R) * f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
  induction r with
  | zero =>
      intro f _
      have h := eulerDerivation_apply_mem_span k x D f
      simpa using h
  | succ r ih =>
      intro f hf
      rw [pow_succ] at hf
      refine Submodule.mul_induction_on hf ?_ ?_
      · intro a ha b hb
        have hEb := eulerDerivation_sub_self_mem_sq k x D hD hb
        have hEa := ih a ha
        have h1 : a * (eulerDerivation k x D b - b) ∈ Ideal.span (Set.range x) ^ (r + 2) := by
          have h := Ideal.mul_mem_mul ha hEb
          rwa [← pow_add] at h
        have h2 : (eulerDerivation k x D a - (r : R) * a) * b
            ∈ Ideal.span (Set.range x) ^ (r + 2) := by
          have hb1 : b ∈ Ideal.span (Set.range x) ^ 1 := by rwa [pow_one]
          have h := Ideal.mul_mem_mul hEa hb1
          have e : r + 1 + 1 = r + 2 := by omega
          rw [← pow_add, e] at h
          exact h
        have key : eulerDerivation k x D (a * b) - ((r + 1 : ℕ) : R) * (a * b)
            = a * (eulerDerivation k x D b - b) + (eulerDerivation k x D a - (r : R) * a) * b := by
          rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
          push_cast
          ring
        have hres : eulerDerivation k x D (a * b) - ((r + 1 : ℕ) : R) * (a * b)
            ∈ Ideal.span (Set.range x) ^ (r + 2) := by
          rw [key]
          exact Submodule.add_mem _ h1 h2
        exact hres
      · intro y z hy hz
        have key : eulerDerivation k x D (y + z) - ((r + 1 : ℕ) : R) * (y + z)
            = (eulerDerivation k x D y - ((r + 1 : ℕ) : R) * y)
              + (eulerDerivation k x D z - ((r + 1 : ℕ) : R) * z) := by
          rw [map_add (f := _)]; ring
        have hres : eulerDerivation k x D (y + z) - ((r + 1 : ℕ) : R) * (y + z)
            ∈ Ideal.span (Set.range x) ^ (r + 1 + 1) := by
          rw [key]
          exact Submodule.add_mem _ hy hz
        exact hres

theorem eulerDerivation_sub_natCast_mul_mem_pow_succ (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) (r : ℕ) {f : R}
    (hf : f ∈ Ideal.span (Set.range x) ^ r) :
    eulerDerivation k x D f - (r : R) * f ∈ Ideal.span (Set.range x) ^ (r + 1) :=
  forall_eulerDerivation_sub_natCast_mul_mem k x D hD r f hf

theorem mem_pow_succ_of_deriv_mem_pow (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) {r : ℕ} (hr : IsUnit ((r : ℕ) : R))
    {f : R} (hf : f ∈ Ideal.span (Set.range x) ^ r)
    (hdf : ∀ i, D i f ∈ Ideal.span (Set.range x) ^ r) :
    f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
  have hgen : ∀ i, x i * D i f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
    intro i
    have hx1 : x i ∈ Ideal.span (Set.range x) ^ 1 := by
      rw [pow_one]
      exact Ideal.subset_span ⟨i, rfl⟩
    have h := Ideal.mul_mem_mul hx1 (hdf i)
    rw [← pow_add, Nat.add_comm 1 r] at h
    exact h
  have h1 : eulerDerivation k x D f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
    rw [eulerDerivation_apply]
    exact Ideal.sum_mem _ fun i _ => hgen i
  have h2 := eulerDerivation_sub_natCast_mul_mem_pow_succ k x D hD r hf
  have h3 : (r : R) * f ∈ Ideal.span (Set.range x) ^ (r + 1) := by
    have h := Submodule.sub_mem _ h1 h2
    simpa using h
  obtain ⟨u, hu⟩ := hr
  have key : (↑u⁻¹ : R) * ((r : R) * f) = f := by
    rw [← hu, ← mul_assoc, u.inv_mul, one_mul]
  rw [← key]
  exact Ideal.mul_mem_left _ _ h3

theorem not_derivIdeal_le_pow (k : Type*) [CommRing k] {R : Type*} [CommRing R] [Algebra k R]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0) {r : ℕ} (hr : IsUnit ((r : ℕ) : R))
    {I : Ideal R} (h1 : I ≤ Ideal.span (Set.range x) ^ r)
    (h2 : ¬ I ≤ Ideal.span (Set.range x) ^ (r + 1)) :
    ¬ derivIdeal k I ≤ Ideal.span (Set.range x) ^ r := by
  intro h
  apply h2
  intro f hf
  exact mem_pow_succ_of_deriv_mem_pow k x D hD hr (h1 hf)
    (fun i => h (derivation_apply_mem_derivIdeal k I (D i) hf))

private theorem eq_natCast_of_le_of_not_succ_le (n : ℕ) (a : ℕ∞) (h1 : (n : ℕ∞) ≤ a)
    (h2 : ¬ ((n + 1 : ℕ) : ℕ∞) ≤ a) : a = (n : ℕ∞) := by
  rcases eq_top_or_lt_top a with rfl | hlt
  · exact absurd le_top h2
  · lift a to ℕ using hlt.ne
    have hn : n ≤ a := by exact_mod_cast h1
    have hn2 : ¬ (n + 1 ≤ a) := by
      intro hc
      exact h2 (by exact_mod_cast hc)
    have ha : a = n := by omega
    exact_mod_cast ha

theorem idealOrder_derivIdeal_of_isUnit_natCast (k : Type*) [CommRing k] {R : Type*} [CommRing R] [IsLocalRing R]
    [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R))
    {I : Ideal R} {r : ℕ} (hr : 1 ≤ r) (hI : idealOrder I = (r : ℕ∞)) :
    idealOrder (derivIdeal k I) = ((r - 1 : ℕ) : ℕ∞) := by
  have hIr : I ≤ IsLocalRing.maximalIdeal R ^ r := (le_idealOrder_iff I r).mp hI.ge
  have hIr1 : ¬ I ≤ IsLocalRing.maximalIdeal R ^ (r + 1) := by
    intro hc
    have h := (le_idealOrder_iff I (r + 1)).mpr hc
    rw [hI] at h
    have h' : r + 1 ≤ r := by exact_mod_cast h
    omega
  have hunitr : IsUnit ((r : ℕ) : R) := hunit r hr
  have hnot : ¬ derivIdeal k I ≤ Ideal.span (Set.range x) ^ r :=
    not_derivIdeal_le_pow k x D hD hunitr (by rw [hx]; exact hIr) (by rw [hx]; exact hIr1)
  have hle : derivIdeal k I ≤ IsLocalRing.maximalIdeal R ^ (r - 1) :=
    derivIdeal_le_pow_of_le_pow k hIr
  have h1 : ((r - 1 : ℕ) : ℕ∞) ≤ idealOrder (derivIdeal k I) :=
    (le_idealOrder_iff _ (r - 1)).mpr hle
  have h2 : ¬ (((r - 1) + 1 : ℕ) : ℕ∞) ≤ idealOrder (derivIdeal k I) := by
    intro hc
    have h := (le_idealOrder_iff _ ((r - 1) + 1)).mp hc
    apply hnot
    rw [hx]
    have hrr : (r - 1) + 1 = r := by omega
    rwa [hrr] at h
  exact eq_natCast_of_le_of_not_succ_le (r - 1) _ h1 h2

theorem idealOrder_derivIdealIterate_of_isUnit_natCast (k : Type*) [CommRing k] {R : Type*} [CommRing R]
    [IsLocalRing R] [Algebra k R] {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → R)
    (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (x j) = if i = j then 1 else 0)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (hunit : ∀ n : ℕ, 1 ≤ n → IsUnit ((n : ℕ) : R))
    {I : Ideal R} {r : ℕ} (hI : idealOrder I = (r : ℕ∞)) {j : ℕ} (hj : j ≤ r) :
    idealOrder (derivIdealIterate k j I) = ((r - j : ℕ) : ℕ∞) := by
  revert hj
  induction j with
  | zero =>
      intro _
      rw [derivIdealIterate_zero, Nat.sub_zero]
      exact hI
  | succ j ih =>
      intro hj
      have hj' : j ≤ r := by omega
      have hprev := ih hj'
      have h1 : 1 ≤ r - j := by omega
      have h := idealOrder_derivIdeal_of_isUnit_natCast k x D hD hx hunit h1 hprev
      rw [derivIdealIterate_succ]
      have heq : r - j - 1 = r - (j + 1) := by omega
      rwa [heq] at h

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealLocalization
universe u v w

namespace FunctorialResolution.EmbeddedResolution

variable {k : Type u} {S : Type v} {S' : Type w}

theorem map_derivIdeal_le [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S']
    [Algebra k S'] [IsScalarTower k S S'] (M : Submonoid S) [IsLocalization M S']
    (J : Ideal S) :
    Ideal.map (algebraMap S S') (derivIdeal k J) ≤
      derivIdeal k (Ideal.map (algebraMap S S') J) := by
  rw [Ideal.map_le_iff_le_comap, derivIdeal_le_iff]
  constructor
  · intro x hx
    refine Ideal.mem_comap.mpr ?_
    exact le_derivIdeal k _ (Ideal.mem_map_of_mem (algebraMap S S') hx)
  · intro D x hx
    refine Ideal.mem_comap.mpr ?_
    have h := derivation_apply_mem_derivIdeal k (Ideal.map (algebraMap S S') J)
      (D.mapToLocalization (S' := S') M) (Ideal.mem_map_of_mem (algebraMap S S') hx)
    rwa [Derivation.mapToLocalization_algebraMap] at h

private theorem derivation_algebraMap_mem_map_derivIdeal [CommRing k] [CommRing S] [CommRing S'] [Algebra k S]
    [Algebra S S'] [Algebra k S'] [IsScalarTower k S S'] (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S)
    (D : Derivation k S' S') {a : S} (ha : a ∈ J) :
    D (algebraMap S S' a) ∈ Ideal.map (algebraMap S S') (derivIdeal k J) := by
  obtain ⟨m, D₀, hm⟩ := Derivation.exists_derivation_mul_eq_of_isLocalization (R := k) M D
  refine (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S' m)).mp ?_
  rw [hm a]
  exact Ideal.mem_map_of_mem _ (derivation_apply_mem_derivIdeal k J D₀ ha)

theorem derivIdeal_map_le [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S']
    [Algebra k S'] [IsScalarTower k S S'] (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S) :
    derivIdeal k (Ideal.map (algebraMap S S') J) ≤
      Ideal.map (algebraMap S S') (derivIdeal k J) := by
  rw [derivIdeal_le_iff]
  refine ⟨Ideal.map_mono (le_derivIdeal k J), ?_⟩
  intro D x hx
  rw [IsLocalization.mem_map_algebraMap_iff M S'] at hx
  obtain ⟨⟨a, m⟩, hax⟩ := hx
  have h1 : D (x * algebraMap S S' (m : S)) = D (algebraMap S S' (a : S)) := by rw [hax]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1
  have hA : D (algebraMap S S' (a : S)) ∈ Ideal.map (algebraMap S S') (derivIdeal k J) :=
    derivation_algebraMap_mem_map_derivIdeal M J D a.2
  have hmem1 : algebraMap S S' (m : S) * D (algebraMap S S' (a : S)) ∈
      Ideal.map (algebraMap S S') (derivIdeal k J) := Ideal.mul_mem_left _ _ hA
  have hmem2 : algebraMap S S' (a : S) * D (algebraMap S S' (m : S)) ∈
      Ideal.map (algebraMap S S') (derivIdeal k J) :=
    Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (le_derivIdeal k J a.2))
  have h3 : algebraMap S S' (m : S) * (algebraMap S S' (m : S) * D x) ∈
      Ideal.map (algebraMap S S') (derivIdeal k J) := by
    have h2 : algebraMap S S' (m : S) * (algebraMap S S' (m : S) * D x) =
        algebraMap S S' (m : S) * D (algebraMap S S' (a : S)) -
          algebraMap S S' (a : S) * D (algebraMap S S' (m : S)) := by
      linear_combination (algebraMap S S' (m : S)) * h1 - (D (algebraMap S S' (m : S))) * hax
    rw [h2]
    exact sub_mem hmem1 hmem2
  exact (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S' m)).mp
    ((Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S' m)).mp h3)

theorem map_derivIdeal [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S']
    [Algebra k S'] [IsScalarTower k S S'] (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S) :
    Ideal.map (algebraMap S S') (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S S') J) :=
  le_antisymm (map_derivIdeal_le M J) (derivIdeal_map_le M J)

theorem map_derivIdeal_away [CommRing k] [CommRing S] [CommRing S'] [Algebra k S] [Algebra S S']
    [Algebra k S'] [IsScalarTower k S S'] (g : S) [IsLocalization.Away g S']
    [Module.FinitePresentation S (KaehlerDifferential k S)] (J : Ideal S) :
    Ideal.map (algebraMap S S') (derivIdeal k J) = derivIdeal k (Ideal.map (algebraMap S S') J) :=
  map_derivIdeal (Submonoid.powers g) J

end FunctorialResolution.EmbeddedResolution
end
