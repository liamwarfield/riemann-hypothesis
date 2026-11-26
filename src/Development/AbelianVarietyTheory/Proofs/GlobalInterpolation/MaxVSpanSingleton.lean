module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIrreducibleSmallRepUnitary
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimePowSmulMemValueLatticeErase
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.CharVal

open Formalism.HermitianLatticesTheory Formalism.L2.Col

variable {E : Type} [Field E] [NumberField E]

def detLat [StarRing E] {n : ℕ} (N : Submodule (𝓞 E) (Sp E n)) : Submodule (𝓞 E) E :=
  Submodule.span (𝓞 E) {x | ∃ A : Matrix (Fin n) (Fin n) E, (∀ v ∈ stdLat E n, A.mulVec v ∈ N) ∧ x = A.det}

def MaxV (P : HeightOneSpectrum (𝓞 E)) (I : Submodule (𝓞 E) E) (γ : WithZero (Multiplicative ℤ)) : Prop :=
  (∀ a ∈ I, P.valuation E a ≤ γ) ∧ ∃ a ∈ I, P.valuation E a = γ

variable {P : HeightOneSpectrum (𝓞 E)} {I J : Submodule (𝓞 E) E} {γ δ : WithZero (Multiplicative ℤ)}

open scoped Pointwise in
theorem _root_.GlobalTheory.CharVal.MaxV.unique (h : _root_.GlobalTheory.CharVal.MaxV P I γ)
    (h' : _root_.GlobalTheory.CharVal.MaxV P I δ) : γ = δ := by
  obtain ⟨a, ha, hγ⟩ := h.2
  obtain ⟨b, hb, hδ⟩ := h'.2
  exact le_antisymm (hγ ▸ h'.1 a ha) (hδ ▸ h.1 b hb)

open scoped Pointwise in
theorem _root_.GlobalTheory.CharVal.val_le_of_span {S : Set E} (h : ∀ a ∈ S, P.valuation E a ≤ γ) :
    ∀ a ∈ Submodule.span (𝓞 E) S, P.valuation E a ≤ γ := by
  intro a ha
  induction ha using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [map_zero]; exact zero_le'
  | add x y _ _ hx hy => exact (Valuation.map_add _ x y).trans (max_le hx hy)
  | smul r x _ hx =>
    rw [Algebra.smul_def, map_mul]
    exact (mul_le_of_le_one_left' (P.valuation_le_one r)).trans hx

open scoped Pointwise in
theorem _root_.GlobalTheory.CharVal.maxV_span_singleton (y : E) :
    _root_.GlobalTheory.CharVal.MaxV P (Submodule.span (𝓞 E) {y}) (P.valuation E y) :=
  ⟨_root_.GlobalTheory.CharVal.val_le_of_span fun a ha => by rw [Set.mem_singleton_iff.1 ha],
    y, Submodule.mem_span_singleton_self y, rfl⟩

open scoped Pointwise in
theorem _root_.GlobalTheory.CharVal.maxV_one : _root_.GlobalTheory.CharVal.MaxV P (1 : Submodule (𝓞 E) E) 1 := by
  refine ⟨fun a ha => ?_, 1, Submodule.mem_one.2 ⟨1, map_one _⟩, map_one _⟩
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 ha
  exact P.valuation_le_one r

open scoped Pointwise in
theorem _root_.GlobalTheory.CharVal.MaxV.mul (h : _root_.GlobalTheory.CharVal.MaxV P I γ)
    (h' : _root_.GlobalTheory.CharVal.MaxV P J δ) : _root_.GlobalTheory.CharVal.MaxV P (I * J) (γ * δ) := by
  obtain ⟨a, ha, hγ⟩ := h.2
  obtain ⟨b, hb, hδ⟩ := h'.2
  refine ⟨fun x hx => ?_, a * b, Submodule.mul_mem_mul ha hb, by rw [map_mul, hγ, hδ]⟩
  rw [Submodule.mul_eq_span_mul_set] at hx
  refine _root_.GlobalTheory.CharVal.val_le_of_span (fun z hz => ?_) x hx
  obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.1 hz
  rw [map_mul]
  exact mul_le_mul' (h.1 u hu) (h'.1 w hw)

open scoped Pointwise in
theorem _root_.GlobalTheory.CharVal.MaxV.pow (h : _root_.GlobalTheory.CharVal.MaxV P I γ) (n : ℕ) :
    _root_.GlobalTheory.CharVal.MaxV P (I ^ n) (γ ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact _root_.GlobalTheory.CharVal.maxV_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

open scoped Pointwise in
private lemma valuation_lt_one_of_mem_span {S : Set E} (h : ∀ a ∈ S, P.valuation E a < 1) :
    ∀ a ∈ Submodule.span (𝓞 E) S, P.valuation E a < 1 := by
  intro a ha
  induction ha using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [map_zero]; exact zero_lt_one
  | add x y _ _ hx hy => exact (Valuation.map_add _ x y).trans_lt (max_lt hx hy)
  | smul r x _ hx =>
    rw [Algebra.smul_def, map_mul]
    exact (mul_le_of_le_one_left' (P.valuation_le_one r)).trans_lt hx

open scoped Pointwise in
theorem _root_.GlobalTheory.CharVal.MaxV.inv (h : _root_.GlobalTheory.CharVal.MaxV P I γ) (h0 : γ ≠ 0)
    (hIJ : I * J = 1) : _root_.GlobalTheory.CharVal.MaxV P J γ⁻¹ := by
  obtain ⟨a, ha, hγ⟩ := h.2
  have hle : ∀ b ∈ J, P.valuation E b ≤ γ⁻¹ := by
    intro b hb
    have hab : a * b ∈ (1 : Submodule (𝓞 E) E) := hIJ ▸ Submodule.mul_mem_mul ha hb
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 hab
    have h1 : γ * P.valuation E b ≤ 1 := by
      rw [← hγ, ← map_mul, ← hr]
      exact P.valuation_le_one r
    rwa [← mul_le_mul_iff_of_pos_left (zero_lt_iff.2 h0), mul_inv_cancel₀ h0]
  refine ⟨hle, ?_⟩
  by_contra hne
  push_neg at hne
  have hlt : ∀ b ∈ J, P.valuation E b < γ⁻¹ := fun b hb => lt_of_le_of_ne (hle b hb) (hne b hb)
  have hS : ∀ z ∈ (I : Set E) * (J : Set E), P.valuation E z < 1 := by
    intro z hz
    obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.1 hz
    rw [map_mul]
    calc P.valuation E u * P.valuation E w ≤ γ * P.valuation E w :=
          mul_le_mul' (h.1 u hu) le_rfl
      _ < γ * γ⁻¹ := mul_lt_mul_of_pos_left (hlt w hw) (zero_lt_iff.2 h0)
      _ = 1 := mul_inv_cancel₀ h0
  have h1 : (1 : E) ∈ I * J := by
    rw [hIJ]
    exact Submodule.mem_one.2 ⟨1, map_one _⟩
  rw [Submodule.mul_eq_span_mul_set] at h1
  have := valuation_lt_one_of_mem_span hS 1 h1
  rw [map_one] at this
  exact lt_irrefl _ this

open scoped Pointwise in
private lemma valuation_algebraMap_eq_one_of_notMem' {s : 𝓞 E} (hs : s ∉ P.asIdeal) :
    P.valuation E (algebraMap (𝓞 E) E s) = 1 :=
  le_antisymm (P.valuation_le_one s) (not_lt.1 fun h => hs ((P.valuation_lt_one_iff_mem s).1 h))

open scoped Pointwise in
theorem _root_.GlobalTheory.CharVal.intAt_iff (x : E) :
    _root_.Formalism.L2.Col.IntAt P x ↔ P.valuation E x ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, hsr⟩
    have h := congrArg (P.valuation E) hsr
    rw [map_mul, valuation_algebraMap_eq_one_of_notMem' hs, one_mul] at h
    rw [h]
    exact P.valuation_le_one r
  · intro hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hb' : algebraMap (𝓞 E) E b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    set k := (Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {b})).factors with hk
    have hbv := P.intValuation_if_neg hb0
    rw [← hk] at hbv
    have hbk : b ∈ P.asIdeal ^ k := (P.intValuation_le_pow_iff_mem b k).1 hbv.le
    have hbk1 : b ∉ P.asIdeal ^ (k + 1) := by
      rw [← P.intValuation_le_pow_iff_mem, hbv, WithZero.exp_le_exp]
      push_cast
      omega
    have hak : a ∈ P.asIdeal ^ k := by
      rw [← P.intValuation_le_pow_iff_mem, ← hbv, ← P.valuation_of_algebraMap (K := E),
        ← P.valuation_of_algebraMap (K := E)]
      rw [map_div₀] at hx
      exact (div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb'))).1 hx
    obtain ⟨Q, hQ⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hbk)
    have hQP : ¬ Q ≤ P.asIdeal := by
      intro hle
      apply hbk1
      rw [pow_succ, ← Ideal.span_singleton_le_iff_mem, hQ]
      exact Ideal.mul_mono_right hle
    obtain ⟨s, hsQ, hsP⟩ := Set.not_subset.1 hQP
    have hsa : a * s ∈ Ideal.span {b} := by
      rw [hQ]
      exact Ideal.mul_mem_mul hak hsQ
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hsa
    refine ⟨c, s, hsP, ?_⟩
    rw [mul_div_assoc', div_eq_iff hb', ← map_mul, ← map_mul, hc, mul_comm s a]

open scoped Pointwise in
theorem _root_.GlobalTheory.CharVal.mem_locP' (I : Submodule (𝓞 E) E) (x : E) :
    x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal I ↔ ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ I :=
  Iff.rfl

open scoped Pointwise in
theorem _root_.GlobalTheory.CharVal.MaxV.mem_locP (h : _root_.GlobalTheory.CharVal.MaxV P I γ) (h0 : γ ≠ 0) (x : E) :
    x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal I ↔ P.valuation E x ≤ γ := by
  rw [_root_.GlobalTheory.CharVal.mem_locP']
  constructor
  · rintro ⟨s, hs, hsx⟩
    have := h.1 _ hsx
    rwa [Algebra.smul_def, map_mul, valuation_algebraMap_eq_one_of_notMem' hs, one_mul] at this
  · intro hx
    obtain ⟨a, ha, hγ⟩ := h.2
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact h0 (by rw [← hγ, map_zero])
    have hint : _root_.Formalism.L2.Col.IntAt P (x / a) := by
      rw [_root_.GlobalTheory.CharVal.intAt_iff, map_div₀, hγ]
      exact (div_le_one₀ (zero_lt_iff.2 h0)).2 hx
    obtain ⟨r, s, hs, hsr⟩ := hint
    refine ⟨s, hs, ?_⟩
    have hsx : s • x = r • a := by
      rw [Algebra.smul_def, Algebra.smul_def, ← hsr, mul_assoc, div_mul_cancel₀ x ha0]
    rw [hsx]
    exact I.smul_mem r ha

open scoped Pointwise in
theorem _root_.GlobalTheory.CharVal.maxV_of_localization_eq
    (h : _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal I = _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 E) E)) :
    _root_.GlobalTheory.CharVal.MaxV P I 1 := by
  have h1P : (1 : 𝓞 E) ∉ P.asIdeal := P.asIdeal.ne_top_iff_one.1 P.isPrime.ne_top
  constructor
  · intro a ha
    have hmem : a ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 E) E) := by
      rw [← h]
      exact (_root_.GlobalTheory.CharVal.mem_locP' I a).2 ⟨1, h1P, by rwa [one_smul]⟩
    obtain ⟨s, hs, hsa⟩ := (_root_.GlobalTheory.CharVal.mem_locP' _ a).1 hmem
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 hsa
    have hv := congrArg (P.valuation E) hr
    rw [Algebra.smul_def, map_mul, valuation_algebraMap_eq_one_of_notMem' hs, one_mul] at hv
    rw [← hv]
    exact P.valuation_le_one r
  · have hmem : (1 : E) ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal I := by
      rw [h]
      exact (_root_.GlobalTheory.CharVal.mem_locP' _ 1).2
        ⟨1, h1P, by rw [one_smul]; exact Submodule.mem_one.2 ⟨1, map_one _⟩⟩
    obtain ⟨s, hs, hs1⟩ := (_root_.GlobalTheory.CharVal.mem_locP' I 1).1 hmem
    refine ⟨s • 1, hs1, ?_⟩
    rw [Algebra.smul_def, mul_one, valuation_algebraMap_eq_one_of_notMem' hs]

end GlobalTheory.CharVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualWeylHighestWeightSpaceLineField
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualWeylHighestWeightSpaceLineField
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

theorem rowDiv_raise_eq_zero (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) k) (hf : f ∈ dualWeyl k N N ν)
    (hwt : IsWeightedHomogeneous (rowW N N) f ν) (a b : Fin N) (hab : a < b) (j : ℕ) (hj : 1 ≤ j) :
    rowDiv k a b j f = 0 := by
  classical
  by_contra hne
  have hg : rowDiv k a b j f ∈ dualWeyl k N N ν := rowDivStable k N N ν a b j f hf
  have hZ : IsWeightedHomogeneous (GlobalTheory.LvT.KerLat.rowZ N N) f (fun i => (ν i : ℤ)) := by
    intro d hd
    funext i
    rw [GlobalTheory.LvT.KerLat.weight_rowZ, hwt hd]
  have hsh := GlobalTheory.LvT.KerLat.rowDiv_shift k (fun i => (ν i : ℤ)) a b j f hZ
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hne
  have e := hsh hm
  have dom := (GlobalTheory.DualWeyl.rowDeg_dominated_of_mem_nabla ν _ hg m (mem_support_iff.mpr hm)).1 (a.val + 1)
  have hrow : ∀ i, ((rowDeg m i : ℕ) : ℤ) = (ν i : ℤ) + (j : ℤ) * ((Pi.single a (1:ℤ) : Fin N → ℤ) i - (Pi.single b (1:ℤ) : Fin N → ℤ) i) := by
    intro i
    have := congrFun e i
    rw [GlobalTheory.LvT.KerLat.weight_rowZ, GlobalTheory.LvT.KerLat.weight_rowW] at this
    rw [this]
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hcast : ((∑ i : Fin N with i.val < a.val + 1, rowDeg m i : ℕ) : ℤ) =
      ((∑ i : Fin N with i.val < a.val + 1, ν i : ℕ) : ℤ) + j := by
    push_cast
    simp only [hrow]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    have ha : (∑ i : Fin N with i.val < a.val + 1, (Pi.single a (1:ℤ) : Fin N → ℤ) i) = 1 := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro i _ hi; simp [Pi.single_apply, hi]
      · intro h; simp at h
    have hb : (∑ i : Fin N with i.val < a.val + 1, (Pi.single b (1:ℤ) : Fin N → ℤ) i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have : i ≠ b := by
        intro h; subst h
        simp at hi
        have : a.val < i.val := hab
        omega
      simp [Pi.single_apply, this]
    rw [ha, hb]; ring
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  have : ((∑ i : Fin N with i.val < a.val + 1, rowDeg m i : ℕ) : ℤ) ≤
      ((∑ i : Fin N with i.val < a.val + 1, ν i : ℕ) : ℤ) := by exact_mod_cast dom
  omega

theorem hw_line_field : ∀ (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ f ∈ dualWeyl k N N ν,
    IsWeightedHomogeneous (rowW N N) f ν → ∃ c : k, f = c • hw k le_rfl ν := by
  intro k _ N ν hν f hf hwt
  classical
  let K := AlgebraicClosure k
  let φ : k →+* K := algebraMap k K
  have hgK : map φ f ∈ dualWeyl K N N ν := dualWeylMap k K φ N N ν f hf
  have hrK : ∀ a b : Fin N, a < b → ∀ j : ℕ, 1 ≤ j → rowDiv K a b j (map φ f) = 0 := by
    intro a b hab j hj
    rw [lclosedeq_rowDiv_map, rowDiv_raise_eq_zero k N ν f hf hwt a b hab j hj, map_zero]
  obtain ⟨c, hc⟩ := hwLine K N N le_rfl ν hν (map φ f) hgK hrK
  obtain ⟨m, hm⟩ := ne_zero_iff.mp (hwNe k N N le_rfl ν)
  refine ⟨AddMonoidAlgebra.coeff f m / AddMonoidAlgebra.coeff (hw k le_rfl ν) m, ?_⟩
  have hcm := congrArg (AddMonoidAlgebra.coeff · m) hc
  rw [coeff_map, coeff_smul, ← lclosedeq_hw_map φ, coeff_map, smul_eq_mul] at hcm
  have hφ : φ (AddMonoidAlgebra.coeff (hw k le_rfl ν) m) ≠ 0 := (map_ne_zero φ).mpr hm
  have hcv : c = φ (AddMonoidAlgebra.coeff f m / AddMonoidAlgebra.coeff (hw k le_rfl ν) m) := by
    rw [map_div₀, hcm, mul_div_cancel_right₀ _ hφ]
  apply map_injective φ φ.injective
  rw [hc, hcv, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, lclosedeq_hw_map]

end GlobalTheory.Alc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualWeylHighestWeightSpaceLineFieldStatement
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_highestWeight_space_line_field : ∀ (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∀ f ∈ dualWeyl k N N ν, IsWeightedHomogeneous (rowW N N) f ν → ∃ c : k, f = c • hw k le_rfl ν := by
  first | exact @GlobalTheory.Alc.hw_line_field | exact GlobalTheory.Alc.hw_line_field | (intros; apply GlobalTheory.Alc.hw_line_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistPrimeDatumIntegralSupportAndInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistPrimeDatumIntegralSupportAndInvariant
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant

variable {E : Type} [Field E] [NumberField E]

theorem entB_zero (q : ℕ) {N' N : ℕ} (k₀ c' n' c n : ℕ) (x : (Fin N' → E) →ₗ[E] (Fin N → E)) (p p' : ℕ) :
    LocE.entB q k₀ c' n' c n 0 0 x p p' =
      Loc.atN (x (Loc.eN E N' (LocE.fIdx k₀ c' n' p'))) (LocE.fIdx k₀ c n p) := by
  simp [LocE.entB, LocE.scE]

theorem intAt_entB {P : HeightOneSpectrum (𝓞 E)} (q : ℕ) {N' N : ℕ} (k₀ c' n' c n : ℕ)
    {y : (Fin N' → E) →ₗ[E] (Fin N → E)} (hy : IntHom P y) (p p' : ℕ) :
    IntAt P (LocE.entB q k₀ c' n' c n 0 0 y p p') := by
  rw [entB_zero]
  have h : IntV P (Loc.eN E N' (LocE.fIdx k₀ c' n' p')) := fun l => by
    unfold Loc.eN
    split_ifs
    · exact intAt_one P
    · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P
  unfold Loc.atN
  split_ifs
  · exact hy _ h _
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem entB_add (q : ℕ) {N' N : ℕ} (k₀ c' n' c n : ℕ) (x y : (Fin N' → E) →ₗ[E] (Fin N → E)) (a : E) (p p' : ℕ) :
    LocE.entB q k₀ c' n' c n 0 0 (x + a • y) p p' =
      LocE.entB q k₀ c' n' c n 0 0 x p p' + a * LocE.entB q k₀ c' n' c n 0 0 y p p' := by
  rw [entB_zero, entB_zero, entB_zero, LinearMap.add_apply, LinearMap.smul_apply, atN_add, atN_smul]

theorem fIdx_fPos {k₀ c n l : ℕ} (hk : k₀ ≤ n) (hl : l < n + c) :
    LocE.fIdx k₀ c n (LocE.fPos k₀ c n l) = l ∧ LocE.fPos k₀ c n l < n + c := by
  unfold LocE.fIdx LocE.fPos
  split_ifs <;> omega

theorem unitV_congr {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)} (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b : E}
    (h : redP P a = redP P b) : LocE.unitV ξ a = LocE.unitV ξ b := by
  unfold LocE.unitV
  have key : ∀ u v : 𝓞 E ⧸ P.asIdeal, u = v →
      (open Classical in if h : IsUnit u then ((ξ h.unit : Kˣ) : K) else 0) =
        (open Classical in if h : IsUnit v then ((ξ h.unit : Kˣ) : K) else 0) := by
    rintro u v rfl
    rfl
  exact key _ _ h

theorem intAt_add_iff {P : HeightOneSpectrum (𝓞 E)} {a b : E} (hb : IntAt P b) : IntAt P (a + b) ↔ IntAt P a :=
  ⟨fun h => by simpa using h.add (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg hb), fun h => h.add hb⟩

theorem phiQ_bdd : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ), k₀ ≤ n' → k₀ ≤ n → r ≤ n' + c' → r ≤ n + c → (∀ x, LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x ≠ 0 → IntHom P x) ∧ ∀ x y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E), IntHom P y → LocE.PhiQ (qOf P) ξ k₀ r c' n' c n (x + (qOf P : E) • y) = LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x := by
  intro E _ _ K _ P ξ k₀ r c' n' c n hk' hk hr' hr
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · unfold LocE.PhiQ at hx
    split_ifs at hx with h
    · rw [intHom_iff]
      intro s l
      obtain ⟨a1, a2⟩ := fIdx_fPos hk l.2
      obtain ⟨b1, b2⟩ := fIdx_fPos hk' s.2
      have := h.1 _ _ a2 b2
      rw [entB_zero, a1, b1] at this
      have e : Loc.eN E (n' + c') s.1 = Pi.single s 1 := by
        funext i
        simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
      rw [e] at this
      simpa [Loc.atN] using this
    · exact absurd rfl hx
  · have hq : (qOf P : E) ≠ 0 := NormalFormAtPrime.qOf_ne_zero P
    have hI := intAt_entB (qOf P) k₀ c' n' c n hy
    have e1 : ∀ p p', IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 (x + (qOf P : E) • y) p p') ↔
        IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x p p') := fun p p' => by
      rw [entB_add, intAt_add_iff ((TopStep.intAt_nat (qOf P)).mul (hI p p'))]
    have e2 : ∀ p p', IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 (x + (qOf P : E) • y) p p' / (qOf P : E)) ↔
        IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x p p' / (qOf P : E)) := fun p p' => by
      rw [entB_add, add_div, mul_div_cancel_left₀ _ hq, intAt_add_iff (hI p p')]
    unfold LocE.PhiQ
    split_ifs with h' h h
    rotate_left
    · exact absurd ⟨fun p p' a b => (e1 p p').1 (h'.1 p p' a b), fun p p' a b d => (e2 p p').1 (h'.2 p p' a b d)⟩ h
    · exact absurd ⟨fun p p' a b => (e1 p p').2 (h.1 p p' a b), fun p p' a b d => (e2 p p').2 (h.2 p p' a b d)⟩ h'
    · rfl
    · apply unitV_congr
      have hx : ∀ s t : Fin r, IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x s.1 t.1) :=
        fun s t => h.1 _ _ (by have := s.2; omega) (by have := t.2; omega)
      refine (TopStep.det_int ?_).2.trans (Eq.trans ?_ (TopStep.det_int ?_).2.symm)
      · exact fun s t => (e1 _ _).2 (hx s t)
      swap
      · exact hx
      refine congrArg Matrix.det (Matrix.ext fun s t => ?_)
      change redP P (LocE.entB (qOf P) k₀ c' n' c n 0 0 (x + (qOf P : E) • y) s.1 t.1) =
        redP P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x s.1 t.1)
      rw [entB_add, reduction_add (hx s t) ((TopStep.intAt_nat (qOf P)).mul (hI _ _)), reduction_mul (TopStep.intAt_nat (qOf P)) (hI _ _), TopStep.reduction_absNorm_eq_zero, zero_mul, add_zero]

end GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistPrimeDatumIntegralSupportAndInvariantStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPrimeDatum_integral_support_and_invariant : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ), k₀ ≤ n' → k₀ ≤ n → r ≤ n' + c' → r ≤ n + c → (∀ x, LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x ≠ 0 → IntHom P x) ∧ ∀ x y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E), IntHom P y → LocE.PhiQ (qOf P) ξ k₀ r c' n' c n (x + (qOf P : E) • y) = LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x := by
  first | exact @GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant.phiQ_bdd | exact GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant.phiQ_bdd | (intros; apply GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant.phiQ_bdd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowEtaBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowEtaBounds
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_eta_bounds : SzRow (fun C D L => (L.etaSz ≤ L.sc.b / ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3)) ∧ (Real.log L.etaSz ≤ L.sc.x ^ (L.sc.eps / 4)) ∧ ((D.R.t : ℝ) ≤ L.etaSz) ∧ ((D.R.t : ℝ) * L.etaSz ≤ L.sc.w'' D.R.n / L.sc.x) ∧ ((D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n)) := by
  intro eps he0 he1 C _
  refine ⟨0, fun cD _ => ⟨401, fun ch hch => ?_⟩⟩
  obtain ⟨x1, h1⟩ := GlobalTheory.T.scale_polynomial_quantities_comparison eps (ch + (1224 : ℕ)) (1 / 2) he0 (by norm_num)
  obtain ⟨x2, h2⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  obtain ⟨x3, h3⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (eps / 4) (ch + (3 : ℕ)) 0 1 0 le_rfl
    (by positivity) one_pos
  refine ⟨max (max x1 x2) (max x3 2), fun D L hE hx V => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  obtain ⟨-, -, s3, -, -, s6, -⟩ := h1 L.sc hE hx1
  obtain ⟨rf, rm, rr, rk, -, -, -, -, -, -, -, -, -, rt, -⟩ := h2 L.sc D.R hE hx2 V.ranks
  have h3' := h3 L.sc.x hx3
  have heta := V.eta_eq
  have hpos := L.etaSz_pos
  unfold h0v at heta
  push_cast at heta
  have hb1 : 1 ≤ L.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hX1 : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
  have hn1 : 1 ≤ D.R.n := D.R.ord_pos
  have hfn : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
  have hn1' : (1 : ℝ) ≤ D.R.n := by exact_mod_cast hn1
  obtain ⟨s7, -⟩ := s6 D.R.n hn1 (by linarith)
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have ht1 : (1 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t
    exact_mod_cast (by omega : 1 ≤ D.R.t)
  have rk' : (D.R.k : ℝ) ≤ L.sc.x ^ (5 : ℝ) := le_trans (by exact_mod_cast rk) rr
  rw [hE]
  generalize L.sc.x = x at *
  generalize L.sc.b = b at *
  generalize L.sc.X' = X at *
  generalize L.sc.w'' D.R.n = w at *
  generalize L.etaSz = η at *
  generalize (D.R.t : ℝ) = t at *
  generalize (D.R.m : ℝ) = m at *
  generalize (D.R.f : ℝ) = f at *
  generalize (D.R.k : ℝ) = k at *
  have hx0 : 0 < x := by linarith
  have hx1' : 1 ≤ x := by linarith
  have hty : t ≤ x ^ ch := rt.trans (Real.rpow_le_rpow_of_exponent_le hx1' hch)
  have e3 : x ^ (ch + (3 : ℕ)) = x ^ ch * x ^ 3 := by rw [Real.rpow_add hx0, Real.rpow_natCast]
  have eB : x ^ (ch + (1224 : ℕ)) = x ^ ch * x ^ 1224 := by rw [Real.rpow_add hx0, Real.rpow_natCast]
  have rf' : f ≤ x ^ 3 := by rw [← Real.rpow_natCast]; exact_mod_cast rf
  have rk'' : k ≤ x ^ 5 := by rw [← Real.rpow_natCast]; exact_mod_cast rk'
  have rt' : t ≤ x ^ 401 := by rw [← Real.rpow_natCast]; exact_mod_cast rt
  have hy1 : 1 ≤ x ^ ch := ht1.trans hty
  have hc1 : x ^ ch ≤ (⌈x ^ ch⌉₊ : ℝ) := Nat.le_ceil _
  have hc2 : (⌈x ^ ch⌉₊ : ℝ) ≤ x ^ ch + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hup : η ≤ x ^ ch * x ^ 3 := by
    rw [heta]
    have a1 : 2 * (⌈x ^ ch⌉₊ : ℝ) ≤ x ^ ch * x ^ 2 := by
      have : 4 ≤ x ^ 2 := by nlinarith
      nlinarith
    calc m * (2 * (⌈x ^ ch⌉₊ : ℝ)) ≤ x * (x ^ ch * x ^ 2) := by gcongr
      _ = _ := by ring
  have hlo : t ≤ η := by rw [heta]; nlinarith
  have hlog : Real.log η ≤ x ^ (eps / 4) := by
    have a1 : Real.log η ≤ (ch + (3 : ℕ)) * Real.log x := by
      rw [← Real.log_rpow hx0, e3]; exact Real.log_le_log hpos hup
    simp only [zero_mul, add_zero, one_mul] at h3'
    exact a1.trans h3'
  rw [eB] at s3 s7
  generalize x ^ ch = y at *
  have hB0 : 0 ≤ y * x ^ 1224 := by positivity
  have hBb : y * x ^ 1224 ≤ b := by
    have a1 : b ^ (1 / 2 : ℝ) ≤ b ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
    rw [Real.rpow_one] at a1
    exact (le_mul_of_one_le_right hB0 hX1).trans (s3.trans a1)
  have hBw : y * x ^ 1224 ≤ w :=
    (le_mul_of_one_le_left hB0 (Real.one_le_rpow hb1 (by norm_num))).trans s7
  have hf0 : 0 < f := by linarith
  refine ⟨?_, hlog, hlo, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    calc η * (t ^ 3 * f * k ^ 3) ≤ (y * x ^ 3) * ((x ^ 401) ^ 3 * x ^ 3 * (x ^ 5) ^ 3) := by gcongr
      _ = y * x ^ 1224 := by ring
      _ ≤ b := hBb
  · rw [le_div_iff₀ hx0]
    calc t * η * x ≤ x ^ 401 * (y * x ^ 3) * x := by gcongr
      _ = y * x ^ 405 := by ring
      _ ≤ y * x ^ 1224 := by gcongr <;> first | assumption | norm_num
      _ ≤ w := hBw
  · have a1 : t + 1 ≤ x * x ^ 401 :=
      calc t + 1 ≤ t + t := by gcongr
        _ = 2 * t := by ring
        _ ≤ x * x ^ 401 := by gcongr
    calc m * (t + 1) * η ≤ x * (x * x ^ 401) * (y * x ^ 3) := by gcongr
      _ = y * x ^ 406 := by ring
      _ ≤ y * x ^ 1224 := by gcongr <;> first | assumption | norm_num
      _ ≤ w := hBw

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowEtaBoundsStatement
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_etaSz_le_b_div_and_log_etaSz_le_and_t_le : SzRow (fun C D L => (L.etaSz ≤ L.sc.b / ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3)) ∧ (Real.log L.etaSz ≤ L.sc.x ^ (L.sc.eps / 4)) ∧ ((D.R.t : ℝ) ≤ L.etaSz) ∧ ((D.R.t : ℝ) * L.etaSz ≤ L.sc.w'' D.R.n / L.sc.x) ∧ ((D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n)) := by
  first | exact @GlobalTheory.EX.szRow_eta_bounds | exact GlobalTheory.EX.szRow_eta_bounds | (intros; apply GlobalTheory.EX.szRow_eta_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowEtaLeW
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowEtaLeW
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem eta_rows_of_pow_bounds {M k m r N L S η d W : ℝ} (hM : 8 ≤ M) (hk : k ≤ M) (hm1 : 1 ≤ m) (hm : m ≤ M)
    (hr0 : 0 ≤ r) (hr : r ≤ M) (hN : N ≤ M) (hL1 : 1 ≤ L) (hL : L ≤ M) (hS0 : 0 ≤ S) (hS : S ≤ M ^ 3)
    (he0 : 0 ≤ η) (he : η ≤ M ^ 3) (hd0 : 0 ≤ d) (hd : 1 ≤ d * M) (hW : M ^ 10 ≤ W) :
    m * (S + η) ≤ W * L ∧ N * η ≤ d * m * W ∧ η ^ 2 * r * L ≤ d * m * W ^ 2 ∧ k * S ≤ W := by
  have hM1 : 1 ≤ M := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hW1 : 1 ≤ W := le_trans (one_le_pow₀ hM1) hW
  have h9 : M ^ 9 ≤ d * m * W := by
    calc M ^ 9 = 1 * M ^ 9 := by ring
      _ ≤ (d * M) * M ^ 9 := by gcongr
      _ = d * 1 * M ^ 10 := by ring
      _ ≤ d * m * W := by gcongr
  have h45 : 2 * M ^ 4 ≤ M ^ 10 := by
    calc 2 * M ^ 4 ≤ M * M ^ 4 := by gcongr; linarith
      _ = M ^ 5 := by ring
      _ ≤ M ^ 10 := pow_le_pow_right₀ hM1 (by norm_num)
  have h4 : 0 ≤ M ^ 4 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc m * (S + η) ≤ M * (M ^ 3 + M ^ 3) := by gcongr
      _ = 2 * M ^ 4 := by ring
      _ ≤ W * 1 := by linarith
      _ ≤ W * L := by gcongr
  · calc N * η ≤ M * M ^ 3 := by gcongr
      _ = M ^ 4 := by ring
      _ ≤ M ^ 9 := pow_le_pow_right₀ hM1 (by norm_num)
      _ ≤ _ := h9
  · calc η ^ 2 * r * L ≤ (M ^ 3) ^ 2 * M * M := by gcongr
      _ = M ^ 8 := by ring
      _ ≤ M ^ 9 := pow_le_pow_right₀ hM1 (by norm_num)
      _ ≤ d * m * W * 1 := by linarith
      _ ≤ d * m * W * W := by gcongr
      _ = _ := by ring
  · calc k * S ≤ M * M ^ 3 := by gcongr
      _ = M ^ 4 := by ring
      _ ≤ W := by linarith

theorem szRow_eta_le_w : SzRow (fun C D L => ((D.R.m : ℝ) * (L.Sc + L.etaSz) ≤ L.sc.w'' D.R.n * L.sc.L) ∧ ((D.R.N D.R.m : ℝ) * L.etaSz ≤ L.de2 * D.R.m * L.sc.w'' D.R.n) ∧ (L.etaSz ^ 2 * D.R.r * L.sc.L ≤ L.de2 * D.R.m * L.sc.w'' D.R.n ^ 2) ∧ ((D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n)) := by
  intro eps h0 h1 C _
  refine ⟨0, fun cD hcD => ⟨0, fun ch hch => ?_⟩⟩
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.scale_polynomial_quantities_comparison eps ((cD + ch + 402) * (10 : ℕ)) 1 h0 one_pos
  obtain ⟨x2, hx2⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps h0 h1
  refine ⟨max 8 (max x1 x2), fun D L he hx hV => ?_⟩
  have h8 : 8 ≤ L.sc.x := le_trans (le_max_left _ _) hx
  have hxa : x1 ≤ L.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxb : x2 ≤ L.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨hf, hm, hr, hkr, -, hL, hL1, -, -, -, -, -, -, -, hN, -, -⟩ := hx2 L.sc D.R he hxb hV.ranks
  have hx1' : 1 ≤ L.sc.x := by linarith
  have hx0 : 0 < L.sc.x := by linarith
  have hn1 : 1 ≤ D.R.n := D.R.ord_pos
  have hn0 : (0 : ℝ) < D.R.n := by exact_mod_cast hn1
  have hn3 : (D.R.n : ℝ) ≤ L.sc.x ^ (3 : ℝ) := by
    refine le_trans ?_ hf
    simp only [Ranks.f]; push_cast; linarith
  have hW := ((hx1 L.sc he hxa).2.2.2.2.2.1 D.R.n hn1 hn3).1
  rw [sub_self, Real.rpow_zero, one_mul, Real.rpow_mul_natCast hx0.le] at hW
  set M := L.sc.x ^ (cD + ch + 402) with hM
  have key : ∀ a : ℝ, a ≤ cD + ch + 402 → L.sc.x ^ a ≤ M := fun a ha =>
    Real.rpow_le_rpow_of_exponent_le hx1' ha
  have hxM : L.sc.x ≤ M := by simpa using key 1 (by linarith)
  have hM8 : 8 ≤ M := h8.trans hxM
  have hrM : (D.R.r : ℝ) ≤ M := hr.trans (key _ (by linarith))
  have hkM : (D.R.k : ℝ) ≤ M := le_trans (by exact_mod_cast hkr) hrM
  have hceil : ∀ a : ℝ, 0 ≤ a → a ≤ cD + ch + 402 → (⌈L.sc.x ^ a⌉₊ : ℝ) ≤ 2 * M := by
    intro a ha ha'
    have := Nat.ceil_lt_add_one (Real.rpow_nonneg hx0.le a)
    have := key a ha'
    linarith
  have hSc : L.Sc = (D.R.k : ℝ) * (4 * (⌈L.sc.x ^ cD⌉₊ : ℝ)) := by
    rw [L.Sc_eq, hV.Del_eq]; simp [Delv]
  have hEta : L.etaSz = (D.R.m : ℝ) * (2 * (⌈L.sc.x ^ ch⌉₊ : ℝ)) := by
    rw [hV.eta_eq]; simp [h0v]
  have hd : L.sc.x ^ (-L.sc.eps) ≤ L.de2 := by
    rw [L.typeDensity_eq_card_div, le_div_iff₀ hn0]; exact hV.host.2.2.1
  have hdp : 0 < L.sc.x ^ (-L.sc.eps) := Real.rpow_pos_of_pos hx0 _
  refine eta_rows_of_pow_bounds hM8 hkM ?_ (hm.trans hxM) (Nat.cast_nonneg _) hrM
    (hN.trans (key _ (by linarith))) hL1 (hL.trans hxM) ?_ ?_ ?_ ?_ (hdp.le.trans hd) ?_ hW
  · have := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.m)
  · rw [hSc]; positivity
  · rw [hSc]
    have := hceil cD hcD (by linarith)
    calc (D.R.k : ℝ) * (4 * (⌈L.sc.x ^ cD⌉₊ : ℝ)) ≤ M * (4 * (2 * M)) := by gcongr
      _ = 8 * M ^ 2 := by ring
      _ ≤ M * M ^ 2 := by gcongr
      _ = M ^ 3 := by ring
  · rw [hEta]; positivity
  · rw [hEta]
    have := hceil ch hch (by linarith)
    have hmM := hm.trans hxM
    calc (D.R.m : ℝ) * (2 * (⌈L.sc.x ^ ch⌉₊ : ℝ)) ≤ M * (2 * (2 * M)) := by gcongr
      _ = 4 * M ^ 2 := by ring
      _ ≤ M * M ^ 2 := by gcongr; linarith
      _ = M ^ 3 := by ring
  · have hLM : L.sc.x ^ L.sc.eps ≤ M := hL.trans hxM
    calc (1 : ℝ) = L.sc.x ^ (-L.sc.eps) * L.sc.x ^ L.sc.eps := by
          rw [← Real.rpow_add hx0]; simp
      _ ≤ L.de2 * M := by gcongr; exact hdp.le.trans hd

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowEtaLeWStatement
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_m_mul_Sc_add_etaSz_le_w_mul_L_and_bounds : SzRow (fun C D L => ((D.R.m : ℝ) * (L.Sc + L.etaSz) ≤ L.sc.w'' D.R.n * L.sc.L) ∧ ((D.R.N D.R.m : ℝ) * L.etaSz ≤ L.de2 * D.R.m * L.sc.w'' D.R.n) ∧ (L.etaSz ^ 2 * D.R.r * L.sc.L ≤ L.de2 * D.R.m * L.sc.w'' D.R.n ^ 2) ∧ ((D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n)) := by
  first | exact @GlobalTheory.EX.szRow_eta_le_w | exact GlobalTheory.EX.szRow_eta_le_w | (intros; apply GlobalTheory.EX.szRow_eta_le_w <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowLStar
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowLStar
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem lstar_ineqs_of_le (m b b' Λ S η t P : ℝ) (hm : 1 ≤ m) (hΛ0 : 0 < Λ) (hΛ : Λ ≤ P) (hS : S ≤ P)
    (hη : η ≤ P) (ht : t ≤ P) (hP : 100 ≤ P) (h1 : P ^ 2 ≤ b') (h2 : b' * P ^ 2 ≤ b) :
    b' + S + η + b / (m * b / Λ) < m * b / Λ ∧ 2 * η + t + 8 * b / (m * b / Λ) + 7 < m * b / Λ := by
  have hPb : P ≤ b' := by nlinarith
  have hb'0 : 0 < b' := by linarith
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) h2
  have hm0 : 0 < m := by linarith
  have e1 : b / (m * b / Λ) = Λ / m := by field_simp
  have e2 : 8 * b / (m * b / Λ) = 8 * (Λ / m) := by field_simp
  have h3 : Λ / m ≤ P := (div_le_self hΛ0.le hm).trans hΛ
  have h4 : 100 * b' ≤ m * b / Λ := by
    rw [le_div_iff₀ hΛ0]
    have a1 : 100 * Λ ≤ P ^ 2 := by nlinarith
    have a2 : b' * (100 * Λ) ≤ b' * P ^ 2 := mul_le_mul_of_nonneg_left a1 hb'0.le
    have a3 : b ≤ m * b := le_mul_of_one_le_left hb0.le hm
    nlinarith
  rw [e1, e2]
  constructor <;> linarith

theorem lstar_den_le (n t N l k m Δ h Q : ℝ) (hQ : 100 ≤ Q) (n0 : 0 ≤ n) (t0 : 0 ≤ t) (N0 : 0 ≤ N) (l0 : 0 ≤ l)
    (k0 : 0 ≤ k) (m0 : 0 ≤ m) (Δ0 : 0 ≤ Δ) (h0 : 0 ≤ h) (hn : n ≤ Q) (ht : t ≤ Q) (hN : N ≤ Q) (hl : l ≤ Q)
    (hk : k ≤ Q) (hm : m ≤ Q) (hΔ : Δ ≤ 2 * Q) (hh : h ≤ 4 * Q) :
    n * t ^ 2 * (N + t) * l ^ 2 + k * n ^ 2 * (k * (4 * Δ) + t + l) ≤ Q ^ 7 ∧ k * (4 * Δ) ≤ Q ^ 7 ∧
      m * h ≤ Q ^ 7 ∧ t ≤ Q ^ 7 ∧ 100 ≤ Q ^ 7 := by
  have Q1 : 1 ≤ Q := by linarith
  have Q0 : 0 ≤ Q := by linarith
  have p1 : Q ≤ Q ^ 6 := le_self_pow₀ Q1 (by norm_num)
  have p2 : Q ^ 2 ≤ Q ^ 6 := pow_le_pow_right₀ Q1 (by norm_num)
  have p4 : Q ^ 4 ≤ Q ^ 6 := pow_le_pow_right₀ Q1 (by norm_num)
  have p5 : Q ^ 5 ≤ Q ^ 6 := pow_le_pow_right₀ Q1 (by norm_num)
  have p7 : 100 * Q ^ 6 ≤ Q ^ 7 := by
    rw [show Q ^ 7 = Q * Q ^ 6 by ring]; gcongr
  have a1 : n * t ^ 2 * (N + t) * l ^ 2 ≤ Q * Q ^ 2 * (Q + Q) * Q ^ 2 := by gcongr
  have a2 : k * n ^ 2 * (k * (4 * Δ) + t + l) ≤ Q * Q ^ 2 * (Q * (4 * (2 * Q)) + Q + Q) := by gcongr
  have a3 : k * (4 * Δ) ≤ Q * (4 * (2 * Q)) := by gcongr
  have a4 : m * h ≤ Q * (4 * Q) := by gcongr
  have e1 : Q * Q ^ 2 * (Q + Q) * Q ^ 2 = 2 * Q ^ 6 := by ring
  have e2 : Q * Q ^ 2 * (Q * (4 * (2 * Q)) + Q + Q) = 8 * Q ^ 5 + 2 * Q ^ 4 := by ring
  have e3 : Q * (4 * (2 * Q)) = 8 * Q ^ 2 := by ring
  have e4 : Q * (4 * Q) = 4 * Q ^ 2 := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem szRow_lStar : SzRow (fun _ D L => (L.sc.b' + L.Sc + L.etaSz + L.sc.b / lStar L < lStar L) ∧
    (2 * L.etaSz + D.R.t + 8 * L.sc.b / lStar L + 7 < lStar L)) := by
  intro eps he0 he1 C _
  refine ⟨0, fun cD hcD => ⟨0, fun ch hch => ?_⟩⟩
  have hcD' : 0 ≤ cD := hcD
  have hch' : 0 ≤ ch := hch
  obtain ⟨x1, h1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  obtain ⟨x2, h2⟩ := GlobalTheory.T.scale_polynomial_quantities_comparison eps ((cD + ch + 402) * 14) 1 he0 one_pos
  refine ⟨max 100 (max x1 x2), fun D L hL hx hV => ?_⟩
  have hx0 : 100 ≤ L.sc.x := (le_max_left _ _).trans hx
  have hx1 : x1 ≤ L.sc.x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx2 : x2 ≤ L.sc.x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  obtain ⟨hf, hm, hr, hkr, -, hl, hl1, -, -, -, -, -, -, ht, hN, -, -⟩ := h1 L.sc D.R hL hx1 hV.ranks
  obtain ⟨-, -, -, hb1, hb2, -, -⟩ := h2 L.sc hL hx2
  have x1le : 1 ≤ L.sc.x := by linarith
  set Q : ℝ := L.sc.x ^ (cD + ch + 402) with hQ
  have hpow : ∀ c : ℝ, c ≤ cD + ch + 402 → L.sc.x ^ c ≤ Q := fun c hc =>
    Real.rpow_le_rpow_of_exponent_le x1le hc
  have hxQ : L.sc.x ≤ Q := by
    have := hpow 1 (by linarith); rwa [Real.rpow_one] at this
  have hQ14 : L.sc.x ^ ((cD + ch + 402) * 14) = (Q ^ 7) ^ 2 := by
    rw [Real.rpow_mul (by linarith), ← pow_mul, ← hQ]
    exact_mod_cast Real.rpow_natCast Q 14
  rw [hQ14] at hb1 hb2
  rw [sub_self, Real.rpow_zero, one_mul] at hb2
  have hQ100 : 100 ≤ Q := hx0.trans hxQ
  have hnQ : (D.R.n : ℝ) ≤ Q := by
    have a : (D.R.n : ℝ) ≤ D.R.f := by
      have : D.R.n ≤ D.R.f := by unfold Ranks.f; omega
      exact_mod_cast this
    exact a.trans (hf.trans (hpow 3 (by linarith)))
  have hkQ : (D.R.k : ℝ) ≤ Q := by
    have a : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    exact a.trans (hr.trans (hpow 5 (by linarith)))
  have htQ : (D.R.t : ℝ) ≤ Q := ht.trans (hpow 401 (by linarith))
  have hNQ : (D.R.N D.R.m : ℝ) ≤ Q := hN.trans (hpow 402 (by linarith))
  have hΔ : (Delv L.sc cD : ℝ) ≤ 2 * Q := by
    have a := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by positivity)
    have b := hpow cD (by linarith)
    unfold Delv; linarith
  have hh : (h0v L.sc ch : ℝ) ≤ 4 * Q := by
    have a := Nat.ceil_lt_add_one (a := L.sc.x ^ ch) (by positivity)
    have b := hpow ch (by linarith)
    unfold h0v; push_cast; linarith
  have hSc : L.Sc = (D.R.k : ℝ) * (4 * (Delv L.sc cD : ℝ)) := by
    rw [L.Sc_eq, hV.Del_eq]; push_cast; rfl
  obtain ⟨c1, c2, c3, c4, c5⟩ := lstar_den_le (D.R.n : ℝ) D.R.t (D.R.N D.R.m) L.sc.L D.R.k D.R.m
    (Delv L.sc cD) (h0v L.sc ch) Q hQ100 (by positivity) (by positivity) (by positivity) (by linarith)
    (by positivity) (by positivity) (by positivity) (by positivity) hnQ htQ hNQ (hl.trans hxQ) hkQ
    (hm.trans hxQ) hΔ hh
  rw [← hSc] at c1 c2
  rw [← hV.eta_eq] at c3
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hn0 : (0 : ℝ) < D.R.n := by
    have hm := D.R.two_le_m
    have hf := D.R.m_le_f
    have hn : 0 < D.R.n := by unfold Ranks.n; omega
    exact_mod_cast hn
  have ht0 : (0 : ℝ) < D.R.t := by
    have := D.R.three_m_lt_t
    exact_mod_cast (by omega : 0 < D.R.t)
  have hl0 : 0 < L.sc.L := by linarith
  have hSc0 : 0 ≤ L.Sc := by rw [hSc]; positivity
  unfold lStar
  exact lstar_ineqs_of_le _ _ _ _ _ _ _ (Q ^ 7) hm1 (by positivity) c1 c2 c3 c4 c5 hb2 hb1

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowLStarStatement
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_b_add_Sc_add_etaSz_add_div_lt_lStar : SzRow (fun C D L => (L.sc.b' + L.Sc + L.etaSz + L.sc.b / lStar L < lStar L) ∧ (2 * L.etaSz + D.R.t + 8 * L.sc.b / lStar L + 7 < lStar L)) := by
  first | exact @GlobalTheory.EX.szRow_lStar | exact GlobalTheory.EX.szRow_lStar | (intros; apply GlobalTheory.EX.szRow_lStar <;> assumption)
end
end
