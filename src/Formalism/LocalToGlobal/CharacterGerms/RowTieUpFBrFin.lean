module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrSfI
public import Lemmata.MiscLemmasH.Imports

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrPlP
section -- merged from Formalism.LocalToGlobal.CharacterGerms.NatCastMulTmul
section -- merged from Formalism.LocalToGlobal.CharacterGerms.CompleteOfBasis
set_option autoImplicit false

noncomputable section

open TensorProduct IsLocalRing Polynomial

namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl

section Complete

variable {Z : Type} [CommRing Z] (π : Z) {A : Type} [CommRing A] [Algebra Z A] {N : ℕ}
  (β : Module.Basis (Fin N) Z A)


end Complete

section Lift

variable {A : Type} [CommRing A] (I : Ideal A)

theorem lift_idem [IsAdicComplete I A] (ε : A) (h : ε * ε - ε ∈ I) : ∃ e : A, e * e = e ∧ e - ε ∈ I := by
  first | exact Bl.SecondBlockLemmaI.goal1 .. | (apply Bl.SecondBlockLemmaI.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaI.goal1 <;> assumption)

theorem idem_zero [IsHausdorff I A] {f : A} (h : f * f = f) (hf : f ∈ I) : f = 0 := by
  refine IsHausdorff.haus (I := I) ‹_› f fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  rcases n with _ | n
  · simp
  · have he : IsIdempotentElem f := h
    rw [← he.pow_succ_eq n]
    exact Ideal.pow_mem_pow hf _

end Lift

end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
end
end

section -- merged from Formalism.LocalToGlobal.CharacterGerms.DetNeZeroOfChars
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl

section Chars

variable {F A L : Type} [CommRing F] [CommRing A] [Algebra F A] [Field L] {ι' ι : Type} [Fintype ι'] [Fintype ι]

theorem char_indep (χ : ι' → A →+* L) (hχ : Function.Injective χ) (φ : F →+* L)
    (hφ : ∀ j r, χ j (algebraMap F A r) = φ r) (e : A) (he : ∀ j, χ j e = 1) (b : ι → A)
    (hb : ∀ x : A, ∃ r : ι → F, e * x = ∑ i, r i • b i) (c : ι' → L) (hc : ∀ i, ∑ j, c j * χ j (b i) = 0) :
    c = 0 := by
  have key : ∀ x : A, ∑ j, c j * χ j x = 0 := by
    intro x
    obtain ⟨r, hr⟩ := hb x
    have hx : ∀ j, χ j x = ∑ i, φ (r i) * χ j (b i) := by
      intro j
      have h1 : χ j (e * x) = χ j x := by rw [map_mul, he, one_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← h1, hr, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, hφ]
    calc ∑ j, c j * χ j x = ∑ j, ∑ i, c j * (φ (r i) * χ j (b i)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hx j, Finset.mul_sum]
      _ = ∑ i, φ (r i) * ∑ j, c j * χ j (b i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = 0 := by simp [hc]
  have hli : LinearIndependent L (fun j => ((χ j).toMonoidHom : A → L)) := by
    have h := (linearIndependent_monoidHom A L).comp (fun j => (χ j).toMonoidHom) (by
      intro j k hjk
      apply hχ
      ext x
      exact DFunLike.congr_fun hjk x)
    exact h
  funext j
  have h2 := Fintype.linearIndependent_iff.mp hli c (by
    funext x
    rw [Finset.sum_apply]
    exact key x)
  exact h2 j

theorem card_le_of_chars (χ : ι' → A →+* L) (hχ : Function.Injective χ) (φ : F →+* L)
    (hφ : ∀ j r, χ j (algebraMap F A r) = φ r) (e : A) (he : ∀ j, χ j e = 1) (b : ι → A)
    (hb : ∀ x : A, ∃ r : ι → F, e * x = ∑ i, r i • b i) : Fintype.card ι' ≤ Fintype.card ι := by
  have hli : LinearIndependent L (fun j : ι' => fun i : ι => χ j (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 := char_indep χ hχ φ hφ e he b hb g (fun i => by
      have h3 := congrFun hg i
      rw [Finset.sum_apply] at h3
      exact h3)
    intro j
    simp [h0]
  simpa using hli.fintype_card_le_finrank

theorem det_ne_zero_of_chars [DecidableEq ι] (χ : ι → A →+* L) (hχ : Function.Injective χ) (φ : F →+* L)
    (hφ : ∀ j r, χ j (algebraMap F A r) = φ r) (e : A) (he : ∀ j, χ j e = 1) (b : ι → A)
    (hb : ∀ x : A, ∃ r : ι → F, e * x = ∑ i, r i • b i) : (Matrix.of fun i j => χ j (b i)).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv0
  apply char_indep χ hχ φ hφ e he b hb v
  intro i
  have h := congrFun hv i
  calc ∑ j, v j * χ j (b i) = ∑ j, χ j (b i) * v j :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = 0 := by
        first
        | exact h
        | simpa [Matrix.mulVec, dotProduct] using h

end Chars

section Label

end Label

end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
end
end

set_option autoImplicit false

noncomputable section

open TensorProduct IsLocalRing

namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl

section T

variable {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE]

theorem tauX_tmul {R : Type} [CommRing R] [Algebra ℤ_[l] R] (τ : OE →+* R) (z : ℤ_[l]) (x : OE) :
    tauX τ (z ⊗ₜ x) = algebraMap ℤ_[l] R z * τ x := by
  simp [tauX]

theorem natCast_eq_tmul (k : ℕ) : ((k : ℕ) : ℤ_[l] ⊗[ℤ] OE) = (k : ℤ_[l]) ⊗ₜ (1 : OE) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, ih, Nat.cast_succ, TensorProduct.add_tmul, Algebra.TensorProduct.one_def]

theorem natCast_tmul (k : ℕ) (y : OE) : (k : ℤ_[l]) ⊗ₜ[ℤ] y = (1 : ℤ_[l]) ⊗ₜ[ℤ] ((k : OE) * y) := by
  have h1 : (k : ℤ_[l]) = (k : ℤ) • (1 : ℤ_[l]) := by simp
  have h2 : ((k : OE) * y) = (k : ℤ) • y := by simp
  rw [h1, h2, TensorProduct.smul_tmul]

theorem natCast_mul_tmul (k : ℕ) (z : ℤ_[l]) (y : OE) :
    ((k : ℕ) : ℤ_[l] ⊗[ℤ] OE) * (z ⊗ₜ y) = ((k : ℤ_[l]) * z) ⊗ₜ y := by
  rw [natCast_eq_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem decomp (s : ℤ_[l] ⊗[ℤ] OE) :
    ∃ (x : OE) (s' : ℤ_[l] ⊗[ℤ] OE), s = 1 ⊗ₜ x + ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * s' := by
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul z y =>
    obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range (x := z)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hn
    obtain ⟨z', hz'⟩ := hn
    refine ⟨(n : OE) * y, z' ⊗ₜ y, ?_⟩
    rw [natCast_mul_tmul, ← natCast_tmul, ← TensorProduct.add_tmul, mul_comm (l : ℤ_[l]) z', hz']
    congr 1
    ring
  | add a b ha hb =>
    obtain ⟨x, s', hs⟩ := ha
    obtain ⟨x', t', ht⟩ := hb
    refine ⟨x + x', s' + t', ?_⟩
    rw [hs, ht, TensorProduct.tmul_add]
    ring

theorem completeA [Module.Free ℤ OE] [Module.Finite ℤ OE] :
    IsAdicComplete (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)}) (ℤ_[l] ⊗[ℤ] OE) := by
  classical
  have key : ∀ (A : Type) [CommRing A] (a x : A) (n : ℕ),
      x ∈ (Ideal.span {a} ^ n • ⊤ : Submodule A A) ↔ ∃ s, x = a ^ n * s := by
    intro A _ a x n
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, -, hs⟩
      exact ⟨s, by rw [← hs, smul_eq_mul]⟩
    · rintro ⟨s, hs⟩
      exact ⟨s, Submodule.mem_top, by rw [hs, smul_eq_mul]⟩
  let bR := Algebra.TensorProduct.basis ℤ_[l] (Module.Free.chooseBasis ℤ OE)
  have hl : ∀ (n : ℕ) (s : ℤ_[l] ⊗[ℤ] OE),
      ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) ^ n * s = ((l : ℤ_[l]) ^ n) • s := by
    intro n s
    rw [Algebra.smul_def, map_pow, map_natCast]
  have hcoord : ∀ (n : ℕ) (x : ℤ_[l] ⊗[ℤ] OE),
      (∃ s, x = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) ^ n * s) ↔ ∀ i, ∃ c, bR.repr x i = (l : ℤ_[l]) ^ n * c := by
    intro n x
    constructor
    · rintro ⟨s, rfl⟩ i
      refine ⟨bR.repr s i, ?_⟩
      rw [hl, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
    · intro h
      choose c hc using h
      refine ⟨∑ i, c i • bR i, ?_⟩
      rw [hl]
      apply bR.repr.injective
      ext i
      rw [hc i, LinearEquiv.map_smul, Finsupp.smul_apply, bR.repr_sum_self, smul_eq_mul]
  have hZ : IsAdicComplete (Ideal.span {((l : ℕ) : ℤ_[l])}) ℤ_[l] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  have haus : ∀ x : ℤ_[l] ⊗[ℤ] OE, (∀ n : ℕ, x ≡ 0 [SMOD (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)} ^ n • ⊤ :
      Submodule (ℤ_[l] ⊗[ℤ] OE) (ℤ_[l] ⊗[ℤ] OE))]) → x = 0 := by
    intro x hx
    apply bR.repr.injective
    apply Finsupp.ext
    intro i
    rw [map_zero, Finsupp.zero_apply]
    apply hZ.toIsHausdorff.haus
    intro n
    rw [SModEq.sub_mem, sub_zero, key]
    have h := hx n
    rw [SModEq.sub_mem, sub_zero, key, hcoord] at h
    exact h i
  have prec : ∀ f : ℕ → ℤ_[l] ⊗[ℤ] OE, (∀ {m n : ℕ}, m ≤ n → f m ≡ f n
      [SMOD (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)} ^ m • ⊤ : Submodule (ℤ_[l] ⊗[ℤ] OE) (ℤ_[l] ⊗[ℤ] OE))]) →
      ∃ L, ∀ n, f n ≡ L [SMOD (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)} ^ n • ⊤ :
        Submodule (ℤ_[l] ⊗[ℤ] OE) (ℤ_[l] ⊗[ℤ] OE))] := by
    intro f hf
    have hci : ∀ i, ∃ Li : ℤ_[l], ∀ n, bR.repr (f n) i ≡ Li
        [SMOD (Ideal.span {((l : ℕ) : ℤ_[l])} ^ n • ⊤ : Submodule ℤ_[l] ℤ_[l])] := by
      intro i
      apply hZ.toIsPrecomplete.prec
      intro m n hmn
      have h := hf hmn
      rw [SModEq.sub_mem, key, hcoord] at h
      rw [SModEq.sub_mem, key]
      obtain ⟨c, hc⟩ := h i
      exact ⟨c, by rw [← hc, map_sub, Finsupp.sub_apply]⟩
    choose L hL using hci
    refine ⟨∑ i, L i • bR i, fun n => ?_⟩
    rw [SModEq.sub_mem, key, hcoord]
    intro i
    have h := hL i n
    rw [SModEq.sub_mem, key] at h
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [map_sub, Finsupp.sub_apply, bR.repr_sum_self, hc]⟩
  haveI : IsHausdorff (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)}) (ℤ_[l] ⊗[ℤ] OE) := ⟨haus⟩
  haveI : IsPrecomplete (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)}) (ℤ_[l] ⊗[ℤ] OE) := ⟨fun f hf => prec f hf⟩
  exact IsAdicComplete.mk

variable {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[l] R]

def chi (τ : OE →+* R) : (ℤ_[l] ⊗[ℤ] OE) →+* ResidueField R := (residue R).comp (tauX τ).toRingHom

theorem chi_apply (τ : OE →+* R) (s : ℤ_[l] ⊗[ℤ] OE) : chi τ s = residue R (tauX τ s) := rfl

theorem chi_one_tmul (τ : OE →+* R) (x : OE) : chi τ ((1 : ℤ_[l]) ⊗ₜ[ℤ] x) = residue R (τ x) := by
  rw [chi_apply, tauX_tmul, map_one, one_mul]

theorem chi_l (hl : ((l : ℕ) : R) ∈ maximalIdeal R) (τ : OE →+* R) (s : ℤ_[l] ⊗[ℤ] OE) :
    chi τ (((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * s) = 0 := by
  have hl0 : ((l : ℕ) : ResidueField R) = 0 := by
    rw [← map_natCast (residue R), residue_eq_zero_iff]
    exact hl
  rw [map_mul, map_natCast, hl0, zero_mul]

theorem chi_alg (τ : OE →+* R) (r : ℤ_[l]) :
    chi τ (algebraMap ℤ_[l] (ℤ_[l] ⊗[ℤ] OE) r) = ((residue R).comp (algebraMap ℤ_[l] R)) r := by
  rw [chi_apply, AlgHom.commutes]
  rfl

variable {d : ℕ} [NeZero d] (em : ZMod d → OE →+* R)

theorem res_frob (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) (a : ZMod d) (x : OE) :
    residue R (em (a + 1) x) = residue R (em a x) ^ l := by
  have h := (residue_eq_zero_iff _).mpr (hfrob a x)
  rw [map_sub, map_pow, sub_eq_zero] at h
  exact h

theorem res_frob_pow (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) (a : ZMod d) (x : OE) :
    ∀ k : ℕ, residue R (em (a + (k : ZMod d)) x) = residue R (em a x) ^ (l ^ k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, res_frob em hfrob, ih, ← pow_mul, Nat.pow_succ l k]

theorem mem_all (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) {x : OE}
    (h : em 0 x ∈ maximalIdeal R) (a : ZMod d) : em a x ∈ maximalIdeal R := by
  have hk := res_frob_pow em hfrob 0 x a.val
  rw [zero_add, ZMod.natCast_zmod_val] at hk
  rw [← residue_eq_zero_iff, hk, (residue_eq_zero_iff _).mpr h,
    zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]

theorem key (hl : ((l : ℕ) : R) ∈ maximalIdeal R)
    (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) {ε : OE}
    (hε : ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y)
    {e z : ℤ_[l] ⊗[ℤ] OE} (he : e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z) {s : ℤ_[l] ⊗[ℤ] OE}
    (hs : e * s = s) (h0 : chi (em 0) s = 0) : ∃ w, s = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * w := by
  obtain ⟨x, s', hs'⟩ := decomp s
  have hx0 : em 0 x ∈ maximalIdeal R := by
    rw [hs', map_add (f := _), chi_one_tmul, chi_l hl, add_zero, residue_eq_zero_iff] at h0
    exact h0
  obtain ⟨y, hy⟩ := hε x (mem_all em hfrob hx0)
  have hkey : (1 : ℤ_[l]) ⊗ₜ[ℤ] ε * (1 ⊗ₜ x) = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * (1 ⊗ₜ y) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hy, natCast_mul_tmul, mul_one, natCast_tmul]
  refine ⟨1 ⊗ₜ y + z * (1 ⊗ₜ x) + e * s', ?_⟩
  linear_combination (-1 : ℤ_[l] ⊗[ℤ] OE) * hs + e * hs' + (1 ⊗ₜ x) * he + hkey

end T

end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
end
end

set_option autoImplicit false

noncomputable section

open TensorProduct IsLocalRing Polynomial

namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl

section Main

variable {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE]

theorem exists_e [Module.Free ℤ OE] [Module.Finite ℤ OE] (ε : OE) (hε1 : ∃ y, ε * ε - ε = (l : OE) * y) :
    ∃ e z : ℤ_[l] ⊗[ℤ] OE, e * e = e ∧ e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z := by
  have := completeA (l := l) (OE := OE)
  obtain ⟨y, hy⟩ := hε1
  have h : ((1 : ℤ_[l]) ⊗ₜ[ℤ] ε) * ((1 : ℤ_[l]) ⊗ₜ[ℤ] ε) - (1 : ℤ_[l]) ⊗ₜ[ℤ] ε ∈
      Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)} := by
    rw [Ideal.mem_span_singleton']
    refine ⟨(1 : ℤ_[l]) ⊗ₜ[ℤ] y, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_sub, hy, mul_comm, natCast_mul_tmul,
      mul_one, natCast_tmul]
  obtain ⟨e, he, he'⟩ := lift_idem _ _ h
  rw [Ideal.mem_span_singleton'] at he'
  obtain ⟨z, hz⟩ := he'
  exact ⟨e, z, he, by rw [← hz, mul_comm]⟩

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra ℤ_[l] R] {d : ℕ} [NeZero d]
  (em : ZMod d → OE →+* R)

theorem chi_e (hl : ((l : ℕ) : R) ∈ maximalIdeal R) {ε : OE} (hε2 : ∀ a, em a ε - 1 ∈ maximalIdeal R)
    {e z : ℤ_[l] ⊗[ℤ] OE} (he : e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z) (a : ZMod d) : chi (em a) e = 1 := by
  have ht : tauX (l := l) (em a) (1 ⊗ₜ ε) = em a ε := by
    simp [tauX, Algebra.TensorProduct.lift_tmul]
  have he' : e = 1 ⊗ₜ ε + ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z := sub_eq_iff_eq_add'.1 he
  change residue R (tauX (l := l) (em a) e) = 1
  have h1 : residue R ((l : ℕ) : R) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hl
  have h2 : residue R (em a ε) = 1 := by
    rw [← sub_eq_zero, ← map_one (residue R), ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hε2 a
  rw [he', map_add (f := _), map_mul, map_natCast, ht, map_add (f := _), map_mul, h1, h2, zero_mul, add_zero]

theorem tau_e (hl : ((l : ℕ) : R) ∈ maximalIdeal R) {ε : OE} (hε2 : ∀ a, em a ε - 1 ∈ maximalIdeal R)
    {e z : ℤ_[l] ⊗[ℤ] OE} (hee : e * e = e) (he : e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z) (a : ZMod d) :
    tauX (em a) e = 1 := by
  have hc := chi_e em hl hε2 he a
  have hid : tauX (l := l) (em a) e * tauX (l := l) (em a) e = tauX (l := l) (em a) e := by
    rw [← map_mul, hee]
  have h2 : tauX (l := l) (em a) e * (tauX (l := l) (em a) e - 1) = 0 := by
    rw [mul_sub, hid, mul_one, sub_self]
  rcases mul_eq_zero.1 h2 with h0 | h1
  · exfalso
    have h3 : chi (l := l) (em a) e = 0 := by
      change residue R (tauX (l := l) (em a) e) = 0
      rw [h0, map_zero]
    rw [hc] at h3
    exact one_ne_zero h3
  · exact sub_eq_zero.1 h1

theorem prim_e [Module.Free ℤ OE] [Module.Finite ℤ OE] (hl : ((l : ℕ) : R) ∈ maximalIdeal R)
    (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) {ε : OE}
    (hε2 : ∀ a, em a ε - 1 ∈ maximalIdeal R)
    (hε3 : ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y)
    {e z : ℤ_[l] ⊗[ℤ] OE} (hee : e * e = e) (he : e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z)
    (f : ℤ_[l] ⊗[ℤ] OE) (hf : f * f = f) (hfe : f * e = f) : f = 0 ∨ f = e := by
  have := completeA (l := l) (OE := OE)
  have hz : ∀ g : ℤ_[l] ⊗[ℤ] OE, g * g = g → e * g = g → chi (em 0) g = 0 → g = 0 := by
    intro g hg heg h0
    obtain ⟨w, hw⟩ := key em hl hfrob hε3 he heg h0
    exact idem_zero (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)}) hg
      (by rw [hw]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hu : chi (em 0) f * chi (em 0) f = chi (em 0) f := by rw [← map_mul, hf]
  have hu' : chi (em 0) f * (chi (em 0) f - 1) = 0 := by linear_combination hu
  rcases mul_eq_zero.1 hu' with h | h
  · left
    exact hz f hf (by rw [mul_comm]; exact hfe) h
  · right
    have := hz (e - f) (by linear_combination hee - 2 * hfe + hf) (by linear_combination hee - hfe)
      (by rw [map_sub, chi_e em hl hε2 he 0, sub_eq_zero.1 h, sub_self])
    exact (sub_eq_zero.1 this).symm

theorem hb_of {ι : Type} [Fintype ι] (e : ℤ_[l] ⊗[ℤ] OE)
    (b : Module.Basis ι ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))) (x : ℤ_[l] ⊗[ℤ] OE) :
    ∃ r : ι → ℤ_[l], e * x = ∑ i, r i • (b i : ℤ_[l] ⊗[ℤ] OE) := by
  have hy : e * x ∈ LinearMap.range (LinearMap.mulLeft ℤ_[l] e) := ⟨x, by simp⟩
  refine ⟨b.repr ⟨e * x, hy⟩, ?_⟩
  have h := congrArg Subtype.val (b.sum_repr ⟨e * x, hy⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  exact h.symm

theorem chi_inj (hsep : ∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) :
    Function.Injective fun a => chi (l := l) (em a) := by
  have ht : ∀ τ : OE →+* R, ∀ x : OE, tauX (l := l) τ (1 ⊗ₜ x) = τ x := by
    intro τ x
    simp [tauX, Algebra.TensorProduct.lift_tmul]
  intro a a' hchi
  by_contra hne
  obtain ⟨x, hx⟩ := hsep a a' hne
  apply hx
  have h1 : chi (l := l) (em a) (1 ⊗ₜ x) = chi (l := l) (em a') (1 ⊗ₜ x) := by
    rw [show chi (l := l) (em a) = chi (l := l) (em a') from hchi]
  change residue R (tauX (l := l) (em a) (1 ⊗ₜ x)) = residue R (tauX (l := l) (em a') (1 ⊗ₜ x)) at h1
  rw [ht, ht, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at h1
  exact h1

theorem le_rank (hl : ((l : ℕ) : R) ∈ maximalIdeal R)
    (hsep : ∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) {ε : OE}
    (hε2 : ∀ a, em a ε - 1 ∈ maximalIdeal R)
    {e z : ℤ_[l] ⊗[ℤ] OE} (he : e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z) {n : ℕ}
    (b : Module.Basis (Fin n) ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))) : d ≤ n := by
  have := card_le_of_chars (F := ℤ_[l]) (fun a => chi (l := l) (em a)) (chi_inj em hsep)
    ((residue R).comp (algebraMap ℤ_[l] R)) (fun a r => chi_alg (em a) r) e (chi_e em hl hε2 he)
    (fun i => (b i : ℤ_[l] ⊗[ℤ] OE)) (hb_of e b)
  simpa [ZMod.card] using this

theorem chi_pow (hl : ((l : ℕ) : R) ∈ maximalIdeal R)
    (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) (s : ℤ_[l] ⊗[ℤ] OE) :
    chi (em 0) s ^ (l ^ d) = chi (em 0) s := by
  have hl0 : residue R ((l : ℕ) : R) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hl
  have hlk : ((l : ℕ) : IsLocalRing.ResidueField R) = 0 := by
    have h := map_natCast (residue R) l
    rw [← h]
    exact hl0
  haveI : CharP (IsLocalRing.ResidueField R) l := by
    exact (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 hlk
  have hstep : ∀ (a : ZMod d) (x : OE), residue R (em (a + 1) x) = residue R (em a x) ^ l := by
    intro a x
    rw [← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hfrob a x
  have hiter : ∀ (n : ℕ) (x : OE), residue R (em (n : ZMod d) x) = residue R (em 0 x) ^ (l ^ n) := by
    intro n x
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, hstep, ih, ← pow_mul, pow_succ]
  have htx : ∀ x : OE, tauX (l := l) (em 0) (1 ⊗ₜ x) = em 0 x := by
    intro x
    simp [tauX, Algebra.TensorProduct.lift_tmul]
  have hx : ∀ x : OE, chi (l := l) (em 0) (1 ⊗ₜ x) ^ (l ^ d) = chi (l := l) (em 0) (1 ⊗ₜ x) := by
    intro x
    change residue R (tauX (l := l) (em 0) (1 ⊗ₜ x)) ^ (l ^ d) = residue R (tauX (l := l) (em 0) (1 ⊗ₜ x))
    rw [htx, ← hiter d x, ZMod.natCast_self]
  have hnat : ∀ a : ℕ, ((a : IsLocalRing.ResidueField R)) ^ (l ^ d) = (a : IsLocalRing.ResidueField R) := by
    intro a
    have h0 : ((a : ZMod l)) ^ (l ^ d) = (a : ZMod l) := ZMod.pow_card_pow _
    have h := congrArg (ZMod.castHom (dvd_refl l) (IsLocalRing.ResidueField R)) h0
    rwa [map_pow, map_natCast] at h
  have hc : ∀ c : ℤ_[l], chi (l := l) (em 0) (c ⊗ₜ (1 : OE)) ^ (l ^ d) = chi (l := l) (em 0) (c ⊗ₜ (1 : OE)) := by
    intro c
    have htc : tauX (l := l) (em 0) (c ⊗ₜ (1 : OE)) = algebraMap ℤ_[l] R c := by
      simp [tauX, Algebra.TensorProduct.lift_tmul]
    change residue R (tauX (l := l) (em 0) (c ⊗ₜ (1 : OE))) ^ (l ^ d) =
      residue R (tauX (l := l) (em 0) (c ⊗ₜ (1 : OE)))
    rw [htc]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec 1 c)
    obtain ⟨a, ha⟩ : ∃ a, a = c.appr 1 := ⟨_, rfl⟩
    rw [← ha, pow_one] at hy
    have hc' : c = ((a : ℕ) : ℤ_[l]) + y * ((l : ℕ) : ℤ_[l]) := by
      rw [hy]
      ring
    have hr : residue R (algebraMap ℤ_[l] R c) = (a : IsLocalRing.ResidueField R) := by
      rw [hc', map_add (f := _), map_mul, map_natCast, map_natCast, map_add (f := _), map_mul, hl0, mul_zero, add_zero,
        map_natCast]
    rw [hr, hnat]
  induction s using TensorProduct.induction_on with
  | zero => rw [map_zero, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]
  | tmul c x =>
    have hsplit : c ⊗ₜ[ℤ] x = (c ⊗ₜ[ℤ] (1 : OE)) * ((1 : ℤ_[l]) ⊗ₜ[ℤ] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hsplit, map_mul, mul_pow, hc c, hx x]
  | add s t hs ht => rw [map_add (f := _), add_pow_char_pow, hs, ht]

theorem rank_le (hl : ((l : ℕ) : R) ∈ maximalIdeal R)
    (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) {ε : OE}
    (hε3 : ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y)
    {e z : ℤ_[l] ⊗[ℤ] OE} (hee : e * e = e) (he : e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z) {n : ℕ}
    (b : Module.Basis (Fin n) ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))) : n ≤ d := by
  classical
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hq : 1 < l ^ d := Nat.one_lt_pow (NeZero.ne d) hl1
  have hP0 : (X ^ (l ^ d) - X : (ResidueField R)[X]) ≠ 0 := Polynomial.X_pow_sub_X_ne_zero hq
  have hroot : ∀ s : ℤ_[l] ⊗[ℤ] OE, chi (em 0) s ∈ (X ^ (l ^ d) - X : (ResidueField R)[X]).roots.toFinset := by
    intro s
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def, eval_sub, eval_pow, eval_X, chi_pow em hl hfrob, sub_self]
  have heb : ∀ i, e * (b i : ℤ_[l] ⊗[ℤ] OE) = b i := by
    intro i
    obtain ⟨x, hx⟩ := (b i).2
    rw [← hx]
    show e * (e * x) = e * x
    rw [← mul_assoc, hee]
  let S : (Fin n → Fin l) → ℤ_[l] ⊗[ℤ] OE := fun r => ∑ i, (((r i : ℕ) : ℤ_[l])) • (b i : ℤ_[l] ⊗[ℤ] OE)
  have heS : ∀ r, e * S r = S r := by
    intro r
    simp only [S, Finset.mul_sum, mul_smul_comm, heb]
  let Ψ : (Fin n → Fin l) → ResidueField R := fun r => chi (em 0) (S r)
  have hinj : Function.Injective Ψ := by
    intro r r' h
    have h0 : chi (em 0) (S r - S r') = 0 := by
      rw [map_sub, sub_eq_zero]
      exact h
    obtain ⟨w, hw⟩ := key em hl hfrob hε3 he (s := S r - S r') (by rw [mul_sub, heS, heS]) h0
    obtain ⟨c, hc⟩ := hb_of e b w
    have h1 : S r - S r' = ∑ i, (((l : ℕ) : ℤ_[l]) * c i) • (b i : ℤ_[l] ⊗[ℤ] OE) := by
      have h2 : S r - S r' = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * (e * w) := by
        have h3 : e * (S r - S r') = S r - S r' := by rw [mul_sub, heS, heS]
        rw [← h3, hw]
        ring
      rw [h2, hc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul, ← map_natCast (algebraMap ℤ_[l] (ℤ_[l] ⊗[ℤ] OE)), ← Algebra.smul_def]
    have h4 : ∑ i, ((((r i : ℕ) : ℤ_[l])) - (((r' i : ℕ) : ℤ_[l])) - ((l : ℕ) : ℤ_[l]) * c i) • b i = 0 := by
      apply Subtype.ext
      have : ∑ i, ((((r i : ℕ) : ℤ_[l])) - (((r' i : ℕ) : ℤ_[l])) - ((l : ℕ) : ℤ_[l]) * c i) •
          (b i : ℤ_[l] ⊗[ℤ] OE) = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← h1]
        simp only [S]
        ring
      simpa using this
    have h5 := Fintype.linearIndependent_iff.1 b.linearIndependent _ h4
    funext i
    have h6 := congrArg (PadicInt.toZMod (p := l)) (h5 i)
    simp only [map_sub, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, sub_zero, map_zero] at h6
    have h7 : ((r i : ℕ) : ZMod l) = ((r' i : ℕ) : ZMod l) := sub_eq_zero.1 h6
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (r i).2, Nat.mod_eq_of_lt (r' i).2] at h7
    exact Fin.ext h7
  have h8 : (Finset.univ : Finset (Fin n → Fin l)).card ≤
      (X ^ (l ^ d) - X : (ResidueField R)[X]).roots.toFinset.card :=
    Finset.card_le_card_of_injOn Ψ (fun r _ => hroot _) (fun r _ r' _ h => hinj h)
  have h9 : (X ^ (l ^ d) - X : (ResidueField R)[X]).roots.toFinset.card ≤ l ^ d := by
    refine le_trans (Multiset.toFinset_card_le _) (le_trans (card_roots' _) ?_)
    rw [Polynomial.natDegree_X_pow_sub_X hq]
  have h10 : l ^ n ≤ l ^ d := by
    have : (Finset.univ : Finset (Fin n → Fin l)).card = l ^ n := by simp
    rw [← this]
    exact le_trans h8 h9
  exact (Nat.pow_le_pow_iff_right hl1).1 h10

theorem tauX_inj {τ τ' : OE →+* R} (h : ∀ s, tauX (l := l) τ s = tauX τ' s) : τ = τ' := by
  ext x
  have hx := h (1 ⊗ₜ x)
  simpa [tauX, Algebra.TensorProduct.lift_tmul] using hx

theorem em_inj (hsep : ∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) : Function.Injective em := by
  intro a a' h
  by_contra hne
  obtain ⟨x, hx⟩ := hsep a a' hne
  apply hx
  rw [h, sub_self]
  exact Ideal.zero_mem _

theorem emb_eq (hsep : ∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R)
    {e : ℤ_[l] ⊗[ℤ] OE} (hte : ∀ a, tauX (em a) e = 1)
    (b : Module.Basis (Fin d) ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)))
    (τ : OE →+* R) (hτ : tauX τ e = 1) : ∃ a, τ = em a := by
  by_contra hne
  push Not at hne
  let ff : Option (ZMod d) → OE →+* R := fun o => o.elim τ em
  have hff : Function.Injective ff := by
    intro o o' h
    cases o with
    | none =>
      cases o' with
      | none => rfl
      | some a' => exact absurd h (hne a')
    | some a =>
      cases o' with
      | none => exact absurd h.symm (hne a)
      | some a' => exact congrArg some (em_inj em hsep h)
  let χ : Option (ZMod d) → (ℤ_[l] ⊗[ℤ] OE) →+* FractionRing R :=
    fun o => (algebraMap R (FractionRing R)).comp (tauX (ff o)).toRingHom
  have hχ : Function.Injective χ := by
    intro o o' h
    apply hff
    apply tauX_inj (l := l)
    intro s
    exact IsFractionRing.injective R (FractionRing R) (DFunLike.congr_fun h s)
  have := card_le_of_chars (F := ℤ_[l]) χ hχ ((algebraMap R (FractionRing R)).comp (algebraMap ℤ_[l] R))
    (fun o r => by
      show algebraMap R (FractionRing R) (tauX (ff o) (algebraMap ℤ_[l] _ r)) = _
      rw [AlgHom.commutes]
      rfl) e
    (fun o => by
      show algebraMap R (FractionRing R) (tauX (ff o) e) = 1
      cases o with
      | none => show algebraMap R (FractionRing R) (tauX τ e) = 1; rw [hτ, map_one]
      | some a => show algebraMap R (FractionRing R) (tauX (em a) e) = 1; rw [hte, map_one])
    (fun i => (b i : ℤ_[l] ⊗[ℤ] OE)) (hb_of e b)
  simp [ZMod.card] at this

theorem unit_det (hsep : ∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R)
    {e : ℤ_[l] ⊗[ℤ] OE} {n : ℕ} (b : Module.Basis (Fin n) ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)))
    (t : Fin n ≃ EmbX (R := R) e) (jj : ZMod d ≃ Fin n)
    (ht : ∀ a, ((t (jj a) : EmbX (R := R) e) : OE →+* R) = em a) :
    IsUnit (Matrix.det (Matrix.of fun i j =>
      tauX ((t j : EmbX (R := R) e) : OE →+* R) (b i : ℤ_[l] ⊗[ℤ] OE))) := by
  have hdet := det_ne_zero_of_chars (F := ℤ_[l]) (fun j => chi (l := l) ((t j : EmbX (R := R) e) : OE →+* R))
    (by
      intro j j' h
      obtain ⟨a, rfl⟩ := jj.surjective j
      obtain ⟨a', rfl⟩ := jj.surjective j'
      simp only [ht] at h
      rw [chi_inj em hsep h])
    ((residue R).comp (algebraMap ℤ_[l] R)) (fun j r => chi_alg _ r) e
    (fun j => by rw [chi_apply, (t j).2, map_one])
    (fun i => (b i : ℤ_[l] ⊗[ℤ] OE)) (hb_of e b)
  by_contra hu
  apply hdet
  have h1 := (residue_eq_zero_iff _).2 ((mem_maximalIdeal _).2 hu)
  rw [RingHom.map_det] at h1
  exact h1

theorem placeX_of [Module.Free ℤ OE] [Module.Finite ℤ OE] (hl : ((l : ℕ) : R) ∈ maximalIdeal R)
    (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R)
    (hsep : ∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) (ε : OE)
    (hε1 : ∃ y, ε * ε - ε = (l : OE) * y) (hε2 : ∀ a, em a ε - 1 ∈ maximalIdeal R)
    (hε3 : ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y) : PlaceX l OE R d em := by
  classical
  obtain ⟨e, z, hee, he⟩ := exists_e ε hε1
  have hte : ∀ a, tauX (em a) e = 1 := tau_e em hl hε2 hee he
  have he0 : e ≠ 0 := by
    intro h0
    have h1 := hte 0
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  have hprim := prim_e em hl hfrob hε2 hε3 hee he
  haveI : Module.Free ℤ_[l] (ℤ_[l] ⊗[ℤ] OE) := inferInstance
  haveI : Module.Finite ℤ_[l] (ℤ_[l] ⊗[ℤ] OE) := inferInstance
  haveI : Module.Finite ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)) := inferInstance
  haveI : Module.Free ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)) := by
    first
    | infer_instance
    | exact Module.free_of_finite_type_torsion_free'
  set n := Module.finrank ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e)) with hn
  let b := Module.finBasis ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))

  have hdn : d = n := le_antisymm (le_rank em hl hsep hε2 he b) (rank_le em hl hfrob hε3 hee he b)
  haveI : NeZero n := ⟨by rw [← hdn]; exact NeZero.ne d⟩

  have hinj : Function.Injective (fun a : ZMod d => (⟨em a, hte a⟩ : EmbX (R := R) e)) :=
    fun a a' h => em_inj em hsep (congrArg Subtype.val h)
  have hsurj : Function.Surjective (fun a : ZMod d => (⟨em a, hte a⟩ : EmbX (R := R) e)) := by
    intro τ
    obtain ⟨a, ha⟩ := emb_eq em hsep hte (b.reindex (finCongr hdn.symm)) τ.1 τ.2
    exact ⟨a, Subtype.ext ha.symm⟩
  let jjr : ZMod d ≃+* Fin n := (ZMod.ringEquivCongr hdn).trans (ZMod.finEquiv n).symm
  let jj : ZMod d ≃ Fin n := jjr.toEquiv
  have hjj : ∀ a, jj (a + 1) = jj a + 1 := by
    intro a
    show jjr (a + 1) = jjr a + 1
    rw [map_add (f := _), map_one]
  let t : Fin n ≃ EmbX (R := R) e := jj.symm.trans (Equiv.ofBijective _ ⟨hinj, hsurj⟩)
  have ht : ∀ a, ((t (jj a) : EmbX (R := R) e) : OE →+* R) = em a := by
    intro a
    show (((Equiv.ofBijective _ ⟨hinj, hsurj⟩) (jj.symm (jj a)) : EmbX (R := R) e) : OE →+* R) = em a
    rw [Equiv.symm_apply_apply]
    rfl
  exact ⟨e, hee, he0, hprim, inferInstance, t, jj, hjj, ht, b, unit_det em hsep b t jj ht⟩

end Main

theorem place_doubling_condition : PlaceCriterionOfIdempotent := by
  unfold PlaceCriterionOfIdempotent
  intro l _ OE _ _ _ _ _ R _ _ _ _ _ hl _ d _ em hfrob hsep hε
  obtain ⟨ε, hε1, hε2, hε3⟩ := hε
  exact placeX_of em hl hfrob hsep ε hε1 hε2 hε3

end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
end
end

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {C3 : IntChart T io y}
variable {C : Type} [Field C] [CharZero C] {V : VF C} {ie : T.Fr →+* C}

theorem upCharS_chartL (hL : UpFLaw V.l T.V (𝓞 E) (chD C3.ch) C3.FT C3.actT)
    (hie : EmbOK T V ie) (hd : ¬ ((V.l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ (𝓞 E))))
    {k : ℕ} {Y : FBChart C V (𝓞 E) (chD C3.ch)} (hY : IsBC C3 ie k Y)
    {Orb : Type} {d : ℕ} [NeZero d] {lab : LabS E C Orb d} (ha : LabSArith V io ie lab) (hg : LabSGeo C3 ie Y lab)
    (hr : lab.RankOK Dw) (o : Orb) (Hc : ∀ g, (Y.rawSelf (selfOfLab ha hg o)).CartHyp V g) :
    UPCharSelfSt Y (selfOfLab ha hg o) Hc :=
  upCharS_at_chartL Pl.place_doubling_condition hL hie hd hY ha hg hr o Hc

variable (Xo c)

end UpFBr

end Formalism.L2.FormalSeriesBounds
