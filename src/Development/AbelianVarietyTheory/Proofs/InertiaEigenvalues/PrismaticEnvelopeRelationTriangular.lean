module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MvPolynomialDeltaSupportedLinearModPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MvPolynomialDeltaSupportedLinearModPrime
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem polyDelta_supported_linear_mod (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (i : ℕ) :
    ∀ s ∈ MvPolynomial.supported A (Set.Iic i), (polyDelta D).δ s ∈ MvPolynomial.supported A (Set.Iic (i + 1)) ∧
      ∃ a ∈ MvPolynomial.supported A (Set.Iic i), ∃ b ∈ MvPolynomial.supported A (Set.Iic i),
        (polyDelta D).δ s - (a * MvPolynomial.X (i + 1) + b) ∈ Ideal.span {(l : MvPolynomial ℕ A)} := by
  intro s hs
  have hX : ∀ (U : Set ℕ) (j : ℕ), j ∈ U → (MvPolynomial.X j : MvPolynomial ℕ A) ∈ MvPolynomial.supported A U :=
    fun U j hj => by
      rw [MvPolynomial.supported_eq_adjoin_X]; exact Algebra.subset_adjoin ⟨j, hj, rfl⟩
  have hC : ∀ (U : Subalgebra A (MvPolynomial ℕ A)) (a : A), MvPolynomial.C a ∈ U :=
    fun U a => U.algebraMap_mem a
  set S := MvPolynomial.supported A (Set.Iic i) with hS
  set T := MvPolynomial.supported A (Set.Iic (i + 1)) with hT
  have hST : S ≤ T := MvPolynomial.supported_mono (Set.Iic_subset_Iic.2 (Nat.le_succ i))
  have hcc : ∀ x y, x ∈ S → y ∈ S → cc l x y ∈ S := by
    intro x y hx hy
    unfold cc
    refine Subalgebra.sum_mem _ fun k _ => ?_
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (Subalgebra.pow_mem _ hx _))
      (Subalgebra.pow_mem _ hy _)
  have hS' : S = Algebra.adjoin A (MvPolynomial.X '' Set.Iic i) := MvPolynomial.supported_eq_adjoin_X _
  rw [hS'] at hs
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    have hj' : j ≤ i := Set.mem_Iic.1 hj
    rw [polyDelta_X]
    refine ⟨hX _ _ (Set.mem_Iic.2 (by omega)), ?_⟩
    rcases Nat.lt_or_ge j i with h | h
    · refine ⟨0, Subalgebra.zero_mem _, MvPolynomial.X (j + 1), hX _ _ (Set.mem_Iic.2 (by omega)), ?_⟩
      simp
    · have : j = i := le_antisymm hj' h
      subst this
      refine ⟨1, Subalgebra.one_mem _, 0, Subalgebra.zero_mem _, ?_⟩
      simp
  | algebraMap a =>
    rw [MvPolynomial.algebraMap_eq, polyDelta_C]
    refine ⟨hC _ _, 0, Subalgebra.zero_mem _, MvPolynomial.C (D.δ a), hC _ _, ?_⟩
    simp
  | add x y hx hy ihx ihy =>
    rw [← hS'] at hx hy
    obtain ⟨hx1, a1, ha1, b1, hb1, hx2⟩ := ihx
    obtain ⟨hy1, a2, ha2, b2, hb2, hy2⟩ := ihy
    have hd : (polyDelta D).δ (x + y) = (polyDelta D).δ x + (polyDelta D).δ y - cc l x y := (polyDelta D).δ_add x y
    rw [hd]
    refine ⟨T.sub_mem (T.add_mem hx1 hy1) (hST (hcc x y hx hy)), a1 + a2, S.add_mem ha1 ha2,
      b1 + b2 - cc l x y, S.sub_mem (S.add_mem hb1 hb2) (hcc x y hx hy), ?_⟩
    have := Ideal.add_mem _ hx2 hy2
    convert this using 1
    ring
  | mul x y hx hy ihx ihy =>
    rw [← hS'] at hx hy
    obtain ⟨hx1, a1, ha1, b1, hb1, hx2⟩ := ihx
    obtain ⟨hy1, a2, ha2, b2, hb2, hy2⟩ := ihy
    have hd : (polyDelta D).δ (x * y) = x ^ l * (polyDelta D).δ y + y ^ l * (polyDelta D).δ x +
        (l : MvPolynomial ℕ A) * (polyDelta D).δ x * (polyDelta D).δ y := (polyDelta D).δ_mul x y
    rw [hd]
    refine ⟨T.add_mem (T.add_mem (T.mul_mem (T.pow_mem (hST hx) _) hy1) (T.mul_mem (T.pow_mem (hST hy) _) hx1))
        (T.mul_mem (T.mul_mem (T.natCast_mem _) hx1) hy1),
      x ^ l * a2 + y ^ l * a1, S.add_mem (S.mul_mem (S.pow_mem hx _) ha2) (S.mul_mem (S.pow_mem hy _) ha1),
      x ^ l * b2 + y ^ l * b1, S.add_mem (S.mul_mem (S.pow_mem hx _) hb2) (S.mul_mem (S.pow_mem hy _) hb1), ?_⟩
    have h3 : (l : MvPolynomial ℕ A) * (polyDelta D).δ x * (polyDelta D).δ y ∈
        Ideal.span {(l : MvPolynomial ℕ A)} :=
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
    have := Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ (x ^ l) hy2) (Ideal.mul_mem_left _ (y ^ l) hx2)) h3
    convert this using 1
    ring

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MvPolynomialDeltaSupportedLinearModPrimeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPolynomialDelta_supported_linear_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (i : ℕ), ∀ s ∈ MvPolynomial.supported A (Set.Iic i), (polyDelta D).δ s ∈ MvPolynomial.supported A (Set.Iic (i + 1)) ∧ ∃ a ∈ MvPolynomial.supported A (Set.Iic i), ∃ b ∈ MvPolynomial.supported A (Set.Iic i), (polyDelta D).δ s - (a * MvPolynomial.X (i + 1) + b) ∈ Ideal.span {(l : MvPolynomial ℕ A)} := by
  first | exact @GlobalTheory.BSP.polyDelta_supported_linear_mod | exact GlobalTheory.BSP.polyDelta_supported_linear_mod | (intros; apply GlobalTheory.BSP.polyDelta_supported_linear_mod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaRingStructureDeltaFrobeniusComm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaRingStructureDeltaFrobeniusComm
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem int_frob_lift (l : ℕ) [hl : Fact l.Prime] (a : ℤ) :
    ∃ b : ℤ, (RingHom.id ℤ) a = a ^ l + (l : ℤ) * b := by
  have h : ((a ^ l : ℤ) : ZMod l) = ((a : ℤ) : ZMod l) := by
    push_cast; exact ZMod.pow_card _
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨b, hb⟩ := h
  exact ⟨b, by simp only [RingHom.id_apply]; linear_combination hb⟩

def intDelta (l : ℕ) [hl : Fact l.Prime] : Delta l ℤ :=
  Delta.ofLift l (RingHom.id ℤ)
    (fun x hx => (mul_eq_zero.1 hx).resolve_left (by exact_mod_cast hl.out.ne_zero))
    (int_frob_lift l)

theorem poly_δ_φ (l : ℕ) [hl : Fact l.Prime] (x : MvPolynomial ℕ ℤ) :
    (polyDelta (intDelta l)).δ ((polyDelta (intDelta l)).φ x) =
      (polyDelta (intDelta l)).φ ((polyDelta (intDelta l)).δ x) := by
  set D := polyDelta (intDelta l)
  have hl0 : (l : MvPolynomial ℕ ℤ) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  refine mul_left_cancel₀ hl0 ?_
  have h1 := D.φ_eq (D.φ x)
  have h2 := D.φ_eq x
  have h3 : D.φ ((l : MvPolynomial ℕ ℤ) * D.δ x) = (l : MvPolynomial ℕ ℤ) * D.φ (D.δ x) := by
    rw [map_mul, map_natCast]
  have h4 : D.φ (D.φ x) = D.φ (x ^ l) + D.φ ((l : MvPolynomial ℕ ℤ) * D.δ x) := by
    rw [← map_add (f := _), ← h2]
  rw [map_pow] at h4
  linear_combination -h1 + h4 + h3

theorem Delta.δ_φ_comm : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (a : A),
    D.δ (D.φ a) = D.φ (D.δ a) := by
  intro l hl A _ D a
  set D₀ := polyDelta (intDelta l)
  let g : MvPolynomial ℕ ℤ →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) (fun i => D.δ^[i] a)
  have hg : ∀ p, p ∈ δLocus D₀ D g := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C n =>
      have : MvPolynomial.C n = ((n : ℤ) : MvPolynomial ℕ ℤ) := by simp
      rw [this]; exact intCast_mem _ n
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp =>
      refine mul_mem hp (mem_δLocus.2 ?_)
      rw [polyDelta_X]
      simp only [g, MvPolynomial.eval₂Hom_X']
      rw [Function.iterate_succ_apply']
  have hgδ : ∀ p, g (D₀.δ p) = D.δ (g p) := fun p => mem_δLocus.1 (hg p)
  have hgφ : ∀ p, g (D₀.φ p) = D.φ (g p) := Delta.map_φ_of_map_δ D₀ D g hgδ
  have hX : g (MvPolynomial.X 0) = a := by simp [g]
  have := congrArg g (poly_δ_φ l (MvPolynomial.X 0))
  rw [hgδ, hgφ, hgφ, hgδ, hX] at this
  exact this

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaRingStructureDeltaFrobeniusCommStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deltaRingStructure_delta_frobenius_comm : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (a : A), D.δ (D.φ a) = D.φ (D.δ a) := by
  first | exact @GlobalTheory.BSP.Delta.δ_φ_comm | exact GlobalTheory.BSP.Delta.δ_φ_comm | (intros; apply GlobalTheory.BSP.Delta.δ_φ_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticEnvelopeRelationTriangular
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.EnvShape

variable {l : ℕ} [hl : Fact l.Prime] {A : Type} [CommRing A]

theorem C_mem_supp (S : Set ℕ) (c : A) : MvPolynomial.C c ∈ MvPolynomial.supported A S := by
  rw [← MvPolynomial.algebraMap_eq]; exact Subalgebra.algebraMap_mem _ c


omit hl in
theorem cc_mem_ideal {R : Type} [CommRing R] (I : Ideal R) {x : R} (y : R) (hx : x ∈ I) : cc l x y ∈ I := by
  unfold cc
  exact Ideal.sum_mem _ fun k hk =>
    Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hx k (Finset.mem_Ioo.1 hk).1))


omit hl in
theorem cc_mem_sub {R : Type} [CommRing R] [Algebra A R] (S : Subalgebra A R) {x y : R} (hx : x ∈ S)
    (hy : y ∈ S) : cc l x y ∈ S := by
  unfold cc
  exact Subalgebra.sum_mem _ fun k _ => S.mul_mem (S.mul_mem (natCast_mem S _) (S.pow_mem hx _)) (S.pow_mem hy _)

theorem phi_mem (D : Delta l A) (J : Ideal A) (hlJ : (l : A) ∈ J) {e : A} (he : e ∈ J) : D.φ e ∈ J := by
  rw [D.φ_eq]; exact J.add_mem (J.pow_mem_of_mem he _ hl.out.pos) (J.mul_mem_right _ hlJ)

theorem delta_Iio (D : Delta l A) (J : Ideal A) (hlJ : (l : A) ∈ J) (i : ℕ) (s : MvPolynomial ℕ A)
    (hs : s ∈ MvPolynomial.supported A (Set.Iio i)) :
    (polyDelta D).δ s ∈ MvPolynomial.supported A (Set.Iic i) ∧
    ∃ a ∈ MvPolynomial.supported A (Set.Iio i), ∃ b ∈ MvPolynomial.supported A (Set.Iio i),
      (polyDelta D).δ s - (a * MvPolynomial.X i + b) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
  cases i with
  | zero =>
    have h0 : Set.Iio (0:ℕ) = ∅ := by ext; simp
    rw [h0, MvPolynomial.supported_empty, Algebra.mem_bot] at hs
    obtain ⟨c, rfl⟩ := hs
    rw [MvPolynomial.algebraMap_eq, polyDelta_C]
    refine ⟨C_mem_supp _ _, 0, Subalgebra.zero_mem _, MvPolynomial.C (D.δ c), C_mem_supp _ _, ?_⟩
    simp
  | succ i =>
    have h1 : Set.Iio (i+1) = Set.Iic i := by ext; simp [Nat.lt_succ_iff]
    rw [h1] at hs ⊢
    obtain ⟨h2, a, ha, b, hb, h3⟩ := GlobalTheory.T.mvPolynomialDelta_supported_linear_mod_prime l A D i s hs
    have hl' : (l : MvPolynomial ℕ A) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
      have := Ideal.mem_map_of_mem (MvPolynomial.C : A →+* MvPolynomial ℕ A) hlJ
      rwa [map_natCast] at this
    exact ⟨h2, a, ha, b, hb, Ideal.span_le.2 (Set.singleton_subset_iff.2 hl') h3⟩

theorem step_eq (D : Delta l A) (e : A) (k : ℕ) (s : MvPolynomial ℕ A) :
    (polyDelta D).δ (MvPolynomial.C e * MvPolynomial.X k + s) =
      MvPolynomial.C (D.φ e) * MvPolynomial.X (k + 1) +
        (MvPolynomial.X k ^ l * MvPolynomial.C (D.δ e) + (polyDelta D).δ s -
          cc l (MvPolynomial.C e * MvPolynomial.X k) s) := by
  rw [(polyDelta D).δ_add, (polyDelta D).δ_mul, polyDelta_C, polyDelta_X, D.φ_eq]
  simp only [map_add (f := _), map_pow, map_mul, map_natCast]
  unfold cc; ring

theorem shape (D : Delta l A) (J : Ideal A) (d p : A) (hlJ : (l : A) ∈ J) (hd : d ∈ J)
    (hu : IsUnit (D.δ d)) (k : ℕ) :
    ∃ e ∈ J, IsUnit (D.δ e) ∧ ∃ s ∈ MvPolynomial.supported A (Set.Iio k),
      (polyDelta D).δ^[k] (MvPolynomial.C p + MvPolynomial.C d * MvPolynomial.X 0) =
        MvPolynomial.C e * MvPolynomial.X k + s := by
  induction k with
  | zero => exact ⟨d, hd, hu, MvPolynomial.C p, C_mem_supp _ _, by simp [add_comm]⟩
  | succ k ih =>
    obtain ⟨e, he, heu, s, hs, hk⟩ := ih
    have hIic : Set.Iic k = Set.Iio (k+1) := by ext; simp [Nat.lt_succ_iff]
    have hX : MvPolynomial.X k ∈ MvPolynomial.supported A (Set.Iio (k+1)) :=
      by rw [MvPolynomial.supported_eq_adjoin_X]; exact Algebra.subset_adjoin ⟨k, by simp, rfl⟩
    have hδ := (delta_Iio D J hlJ k s hs).1
    rw [hIic] at hδ
    have hs' : s ∈ MvPolynomial.supported A (Set.Iio (k+1)) :=
      MvPolynomial.supported_mono (Set.Iio_subset_Iio (Nat.le_succ k)) hs
    refine ⟨D.φ e, phi_mem D J hlJ he, ?_, MvPolynomial.X k ^ l * MvPolynomial.C (D.δ e) + (polyDelta D).δ s -
      cc l (MvPolynomial.C e * MvPolynomial.X k) s, ?_, ?_⟩
    · rw [GlobalTheory.T.deltaRingStructure_delta_frobenius_comm]; exact heu.map D.φ
    · exact Subalgebra.sub_mem _ (Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hX _)
        (C_mem_supp _ _)) hδ) (cc_mem_sub _ (Subalgebra.mul_mem _ (C_mem_supp _ _) hX) hs')
    · rw [Function.iterate_succ_apply', hk, step_eq]

theorem envRel_triangular : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A)
    (d p : A), (l : A) ∈ J → d ∈ J → IsUnit (D.δ d) → ∀ i, ∃ (v : Aˣ) (a b : MvPolynomial ℕ A),
    a ∈ MvPolynomial.supported A (Set.Iio i) ∧ b ∈ MvPolynomial.supported A (Set.Iio i) ∧
    envRel D d p i - (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) ∈
      J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
  intro l _ A _ D J d p hlJ hd hu i
  obtain ⟨e, he, heu, s, hs, hi⟩ := shape D J d p hlJ hd hu i
  obtain ⟨-, a, ha, b, hb, hab⟩ := delta_Iio D J hlJ i s hs
  refine ⟨heu.unit, a, b, ha, hb, ?_⟩
  have hrel : envRel D d p i = MvPolynomial.C (D.φ e) * MvPolynomial.X (i + 1) +
      (MvPolynomial.X i ^ l * MvPolynomial.C (D.δ e) + (polyDelta D).δ s -
        cc l (MvPolynomial.C e * MvPolynomial.X i) s) := by
    rw [envRel, Function.iterate_succ_apply', hi, step_eq]
  have hdiff : envRel D d p i - (MvPolynomial.C (heu.unit : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b)
      = MvPolynomial.C (D.φ e) * MvPolynomial.X (i + 1) + ((polyDelta D).δ s - (a * MvPolynomial.X i + b)) -
        cc l (MvPolynomial.C e * MvPolynomial.X i) s := by
    rw [hrel, IsUnit.unit_spec]; ring
  rw [hdiff]
  exact Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _
    (Ideal.mem_map_of_mem _ (phi_mem D J hlJ he))) hab)
    (cc_mem_ideal _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ he)))

end GlobalTheory.EnvShape
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticEnvelopeRelationTriangularStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismaticEnvelopeRelation_triangular : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A) (d p : A), (l : A) ∈ J → d ∈ J → IsUnit (D.δ d) → ∀ i, ∃ (v : Aˣ) (a b : MvPolynomial ℕ A), a ∈ MvPolynomial.supported A (Set.Iio i) ∧ b ∈ MvPolynomial.supported A (Set.Iio i) ∧ envRel D d p i - (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
  first | exact @GlobalTheory.EnvShape.envRel_triangular | exact GlobalTheory.EnvShape.envRel_triangular | (intros; apply GlobalTheory.EnvShape.envRel_triangular <;> assumption)
end
