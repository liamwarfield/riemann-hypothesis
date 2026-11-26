module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTaylorShiftFrobeniusTwoVariableCompatible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobMemPPSetCongr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowEqOfRoot

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomExtDense
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysEval

section Abstract

variable {B P R : Type} [CommRing B] [CommRing P] [CommRing R] (l : ℕ) (ι : B →+* P) (f : B →+* R)

def Approx (F : P) (r : ℕ) (y : R) : Prop :=
  ∃ (n : ℕ) (b : B) (p h : P), n ≠ 0 ∧ (n : P) * p = ι b ∧ F = p + (l : P) ^ r * h ∧ (n : R) * y = f b

variable {l ι f}

theorem approx_add {F G : P} {r : ℕ} {y z : R} (hF : Approx l ι f F r y) (hG : Approx l ι f G r z) :
    Approx l ι f (F + G) r (y + z) := by
  obtain ⟨n, b, p, h, hn, hp, hF, hy⟩ := hF
  obtain ⟨m, c, q, k, hm, hq, hG, hz⟩ := hG
  refine ⟨n * m, (m : B) * b + (n : B) * c, p + q, h + k, mul_ne_zero hn hm, ?_, ?_, ?_⟩
  · rw [map_add (f := _), map_mul, map_mul, map_natCast, map_natCast, ← hp, ← hq]; push_cast; ring
  · rw [hF, hG]; ring
  · rw [map_add (f := _), map_mul, map_mul, map_natCast, map_natCast, ← hy, ← hz]; push_cast; ring

theorem approx_mul {F G : P} {r : ℕ} {y z : R} (hF : Approx l ι f F r y) (hG : Approx l ι f G r z) :
    Approx l ι f (F * G) r (y * z) := by
  obtain ⟨n, b, p, h, hn, hp, hF, hy⟩ := hF
  obtain ⟨m, c, q, k, hm, hq, hG, hz⟩ := hG
  refine ⟨n * m, b * c, p * q, p * k + h * q + (l : P) ^ r * h * k, mul_ne_zero hn hm, ?_, ?_, ?_⟩
  · rw [map_mul, ← hp, ← hq]; push_cast; ring
  · rw [hF, hG]; ring
  · rw [map_mul, ← hy, ← hz]; push_cast; ring

theorem approx_ι (b : B) (r : ℕ) : Approx l ι f (ι b) r (f b) :=
  ⟨1, b, ι b, 0, one_ne_zero, by simp, by simp, by simp⟩

theorem approx_one (r : ℕ) : Approx l ι f 1 r 1 := by
  simpa using approx_ι (l := l) (ι := ι) (f := f) 1 r

theorem approx_zero (r : ℕ) : Approx l ι f 0 r 0 := by
  simpa using approx_ι (l := l) (ι := ι) (f := f) 0 r

variable (htf : ∀ (n : ℕ) (x : R), n ≠ 0 → (n : R) * x = 0 → x = 0)
  (hK : ∀ (n : ℕ) (b : B) (p : P), n ≠ 0 → (n : P) * p = ι b → ∃ y : R, (n : R) * y = f b) (hl0 : l ≠ 0)
include htf hK hl0

theorem approx_dvd {F : P} {r s : ℕ} (hrs : r ≤ s) {y z : R} (hy : Approx l ι f F r y)
    (hz : Approx l ι f F s z) : (l : R) ^ r ∣ y - z := by
  obtain ⟨n, b, p, h, hn, hp, hF, hy⟩ := hy
  obtain ⟨m, c, q, k, hm, hq, hF', hz⟩ := hz
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrs
  have h0 : p - q = (l : P) ^ r * ((l : P) ^ d * k - h) := by linear_combination hF' - hF
  have h1 : ((n * m * l ^ r : ℕ) : P) * ((l : P) ^ d * k - h) = ι ((m : B) * b - (n : B) * c) := by
    rw [map_sub, map_mul, map_mul, map_natCast, map_natCast, ← hp, ← hq]
    push_cast
    linear_combination ((n : P) * m) * h0.symm
  obtain ⟨w, hw⟩ := hK _ _ _ (mul_ne_zero (mul_ne_zero hn hm) (pow_ne_zero _ hl0)) h1
  refine ⟨w, (sub_eq_zero.1 (htf (n * m) _ (mul_ne_zero hn hm) ?_)).symm⟩
  rw [map_sub, map_mul, map_mul, map_natCast, map_natCast, ← hy, ← hz] at hw
  push_cast at hw ⊢
  linear_combination hw

variable [IsAdicComplete (Ideal.span {(l : R)}) R]
  (hD : ∀ (F : P) (r : ℕ), ∃ (n : ℕ) (b : B) (p h : P), n ≠ 0 ∧ (n : P) * p = ι b ∧ F = p + (l : P) ^ r * h)

omit htf hl0 in
include hD in
theorem exists_approx (F : P) (r : ℕ) : ∃ y, Approx l ι f F r y := by
  obtain ⟨n, b, p, h, hn, hp, hF⟩ := hD F r
  obtain ⟨y, hy⟩ := hK n b p hn hp
  exact ⟨y, n, b, p, h, hn, hp, hF, hy⟩


omit htf hK hl0 in
variable (l) in
theorem sep_l (x : R) (h : ∀ r : ℕ, (l : R) ^ r ∣ x) : x = 0 :=
  IsHausdorff.haus' (I := Ideal.span {(l : R)}) x fun n => by
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h n

include hD in
theorem exists_lim (F : P) : ∃ L : R, ∀ r y, Approx l ι f F r y → (l : R) ^ r ∣ L - y := by
  choose y hy using exists_approx hK hD F
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(l : R)}) y (fun {m n} hmn => by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact approx_dvd htf hK hl0 hmn (hy m) (hy n))
  refine ⟨L, fun r z hz => ?_⟩
  have h1 := hL r
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  have h2 := approx_dvd htf hK hl0 le_rfl (hy r) hz
  have e : L - z = (y r - z) - (y r - L) := by ring
  rw [e]
  exact dvd_sub h2 h1


include hD in
theorem exists_ringHom : ∃ E : P →+* R, ∀ F r y, Approx l ι f F r y → (l : R) ^ r ∣ E F - y := by
  choose L hL using exists_lim htf hK hl0 hD
  have key : ∀ F z, (∀ r, ∃ y, Approx l ι f F r y ∧ (l : R) ^ r ∣ z - y) → L F = z := fun F z hz =>
    sub_eq_zero.1 (sep_l l _ fun r => by
      obtain ⟨y, hy, hzy⟩ := hz r
      have e : L F - z = (L F - y) - (z - y) := by ring
      rw [e]
      exact dvd_sub (hL F r y hy) hzy)
  have h1 : L 1 = 1 := key 1 1 fun r => ⟨1, approx_one r, by simp⟩
  have h0 : L 0 = 0 := key 0 0 fun r => ⟨0, approx_zero r, by simp⟩
  have hm : ∀ F G, L (F * G) = L F * L G := by
    intro F G
    refine key _ _ fun r => ?_
    obtain ⟨y, hy⟩ := exists_approx hK hD F r
    obtain ⟨z, hz⟩ := exists_approx hK hD G r
    obtain ⟨c, hc⟩ := hL F r y hy
    obtain ⟨d, hd⟩ := hL G r z hz
    exact ⟨y * z, approx_mul hy hz, c * z + y * d + (l : R) ^ r * c * d, by
      linear_combination (L G) * hc + (y + (l : R) ^ r * c) * hd⟩
  have ha : ∀ F G, L (F + G) = L F + L G := by
    intro F G
    refine key _ _ fun r => ?_
    obtain ⟨y, hy⟩ := exists_approx hK hD F r
    obtain ⟨z, hz⟩ := exists_approx hK hD G r
    obtain ⟨c, hc⟩ := hL F r y hy
    obtain ⟨d, hd⟩ := hL G r z hz
    exact ⟨y + z, approx_add hy hz, c + d, by linear_combination hc + hd⟩
  exact ⟨{ toFun := L, map_one' := h1, map_zero' := h0, map_mul' := hm, map_add' := ha }, hL⟩


omit hK in
include hD in
theorem ringHom_ext_dense (G₁ G₂ : P →+* R) (h : ∀ b, G₁ (ι b) = G₂ (ι b)) : G₁ = G₂ := by
  ext F
  refine sub_eq_zero.1 (sep_l l _ fun r => ?_)
  obtain ⟨n, b, p, k, hn, hp, hF⟩ := hD F r
  have e1 : (n : R) * (G₁ p - G₂ p) = G₁ ((n : P) * p) - G₂ ((n : P) * p) := by
    rw [map_mul, map_mul, map_natCast, map_natCast]; ring
  have h1 : G₁ p = G₂ p := sub_eq_zero.1 (htf n _ hn (by rw [e1, hp, h, sub_self]))
  exact ⟨G₁ k - G₂ k, by rw [hF, map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, h1]; ring⟩

end Abstract

section Concrete

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [Algebra O K] (t : Wq l a →ₐ[ℤ_[l]] O)


variable (K) in
def embK (τ : ZMod a) : Wq l a →+* K := (algebraMap O K).comp (emb t τ).toRingHom


variable (l a) in
abbrev Bp : Type := Polynomial (Polynomial (Wq l a))


variable (K) in
def rhoK (τ : ZMod a) : Polynomial (Wq l a) →+* K⟦X⟧ :=
  (PowerSeries.map (embK K t τ)).comp Polynomial.coeToPowerSeries.ringHom


variable (K) in
def iotaP : Bp l a →+* (ZMod a → K⟦X⟧⟦X⟧) :=
  Pi.ringHom fun τ => (PowerSeries.map (rhoK K t τ)).comp Polynomial.coeToPowerSeries.ringHom

theorem coeff_iotaP (b : Bp l a) (τ : ZMod a) (i n : ℕ) :
    coeff n (coeff i (iotaP K t b τ)) = embK K t τ ((b.coeff i).coeff n) := by
  rw [show iotaP K t b τ = PowerSeries.map (rhoK K t τ) (b : (Polynomial (Wq l a))⟦X⟧) from rfl, coeff_map,
    Polynomial.coeff_coe, rhoK, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, coeff_map,
    Polynomial.coeff_coe]

theorem rhoK_eq_toAc [IsUltrametricDist K] [IsUnitBall O K] (q : Polynomial (Wq l a)) (τ : ZMod a) :
    rhoK K t τ q = (toAc t K (q : (Wq l a)⟦X⟧) τ : K⟦X⟧) := by
  ext n
  rw [coeff_toAc]
  simp [rhoK, embK, coeff_map, Polynomial.coeff_coe]

theorem charZero_K [NormedAlgebra ℚ_[l] K] : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective

theorem embK_injective [NormedAlgebra ℚ_[l] K] (τ : ZMod a) : Function.Injective (embK K t τ) := by
  have := charZero_K (l := l) (K := K)
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  by_contra h0
  obtain ⟨m, v, hv, rfl⟩ := WittVector.exists_eq_pow_p_mul w h0
  have hu : IsUnit v := WittVector.isUnit_of_coeff_zero_ne_zero v hv
  rw [map_mul, map_pow, map_natCast] at hw
  exact mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)) (hu.map _).ne_zero hw


include t in
theorem wq_nat_cancel [NormedAlgebra ℚ_[l] K] {n : ℕ} (hn : n ≠ 0) {x : Wq l a}
    (h : (n : Wq l a) * x = 0) : x = 0 := by
  have := charZero_K (l := l) (K := K)
  refine embK_injective (K := K) t 0 ?_
  have h1 := congrArg (embK K t 0) h
  rw [map_mul, map_natCast, map_zero] at h1
  rw [map_zero]
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 hn)

variable {e : ℕ} (ϖ : PiSys l e)

theorem ev_coe (q : Polynomial (Wq l a)) :
    ϖ.ev a (q : (Wq l a)⟦X⟧) = q.eval₂ (wA l a).toRingHom ϖ.teich := by
  have h := Polynomial.ringHom_ext (f := (ϖ.ev a).comp Polynomial.coeToPowerSeries.ringHom)
    (g := Polynomial.eval₂RingHom (wA l a).toRingHom ϖ.teich) (fun w => by simp) (by simp)
  exact RingHom.congr_fun h q


variable (a) in
def evC : Polynomial (Wq l a) →+* Per.Acris l :=
  ((ainfToAcris l).toRingHom.comp (ϖ.ev a)).comp Polynomial.coeToPowerSeries.ringHom


variable (a) in
def fP (g : GQ l) : Bp l a →+* Per.Acris l :=
  Polynomial.eval₂RingHom (evC a ϖ) (ainfToAcris l (ϖ.mu g * ϖ.teich))

end Concrete

end GlobalTheory.CrysEval
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPolynomialApproxDividedTwoVariableSet
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPolynomialApproxDividedTwoVariableSet
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism GlobalTheory.CrysEval
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysEval

theorem coeff_coeff_natCast_mul {K : Type} [CommRing K] (m : ℕ) (q : K⟦X⟧⟦X⟧) (i n : ℕ) :
    coeff n (coeff i ((m : K⟦X⟧⟦X⟧) * q)) = (m : K) * coeff n (coeff i q) := by
  rw [← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), coeff_C_mul, ← map_natCast (C : K →+* K⟦X⟧), coeff_C_mul]

theorem exists_poly_approx_PPSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ PPSet t K e, ∀ r : ℕ, ∃ (n : ℕ) (b : Bp l a) (p h : ZMod a → K⟦X⟧⟦X⟧), n ≠ 0 ∧ p ∈ PPSet t K e ∧ h ∈ PPSet t K e ∧ (n : ZMod a → K⟦X⟧⟦X⟧) * p = iotaP K t b ∧ F = p + (l : ZMod a → K⟦X⟧⟦X⟧) ^ r * h := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t F hF r
  classical
  have hK0 := charZero_K (l := l) (K := K)
  obtain ⟨w, hw, hFw⟩ := hF
  let N : ℕ × ℕ → ℕ := fun x => x.1.factorial * (x.2 / e).factorial
  have hNpos : ∀ x, N x ≠ 0 := fun x => Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
  have hN0 : ∀ x, (N x : K) ≠ 0 := fun x => Nat.cast_ne_zero.2 (hNpos x)
  let ser : (ℕ × ℕ → Wq l a) → ZMod a → K⟦X⟧⟦X⟧ := fun v τ =>
    PowerSeries.mk fun i => PowerSeries.mk fun n => embK K t τ (v (i, n)) / (N (i, n) : K)
  have coeff_ser : ∀ v τ i n, coeff n (coeff i (ser v τ)) = embK K t τ (v (i, n)) / (N (i, n) : K) := by
    intro v τ i n; simp [ser]
  have ser_mem : ∀ v, LTo0 l v → ser v ∈ PPSet t K e := by
    intro v hv
    refine ⟨v, hv, fun τ i n => ?_⟩
    rw [coeff_ser, mul_div_cancel₀ _ (hN0 (i, n))]
    rfl
  have coeff_F : ∀ τ i n, coeff n (coeff i (F τ)) = embK K t τ (w (i, n)) / (N (i, n) : K) := by
    intro τ i n
    rw [eq_div_iff (hN0 _), mul_comm]
    exact hFw τ i n
  have hfin : {x | ¬ (l : Wq l a) ^ r ∣ w x}.Finite := Filter.eventually_cofinite.1 (hw r)
  let s := hfin.toFinset
  have mem_s : ∀ x, x ∈ s ↔ ¬ (l : Wq l a) ^ r ∣ w x := fun x => by simp [s]
  let c : ℕ × ℕ → Wq l a := fun x => if h : (l : Wq l a) ^ r ∣ w x then h.choose else 0
  let w₁ : ℕ × ℕ → Wq l a := fun x => if x ∈ s then w x else 0
  have hsplit : ∀ x, w x = w₁ x + (l : Wq l a) ^ r * c x := by
    intro x
    by_cases h : (l : Wq l a) ^ r ∣ w x
    · have hx : x ∉ s := fun hx => (mem_s x).1 hx h
      simp only [w₁, c, hx, if_false, dif_pos h, zero_add]
      exact h.choose_spec
    · have hx : x ∈ s := (mem_s x).2 h
      simp [w₁, c, hx, h]
  have hw₁ : LTo0 l w₁ := by
    intro m
    refine Filter.eventually_cofinite.2 (hfin.subset fun x hx => ?_)
    simp only [Set.mem_setOf_eq] at hx ⊢
    intro hd
    apply hx
    have : x ∉ s := fun hx' => (mem_s x).1 hx' hd
    simp [w₁, this]
  have hc : LTo0 l c := by
    intro m
    filter_upwards [hw (m + r)] with x hx
    have h : (l : Wq l a) ^ r ∣ w x := dvd_trans (pow_dvd_pow _ (Nat.le_add_left r m)) hx
    obtain ⟨d, hd⟩ := hx
    have hcx : c x = h.choose := dif_pos h
    have hspec := h.choose_spec
    refine ⟨d, ?_⟩
    rw [hcx]
    have hl0 : l ^ r ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    have := wq_nat_cancel (K := K) t hl0 (x := h.choose - (l : Wq l a) ^ m * d) (by
      push_cast
      linear_combination hd - hspec)
    exact sub_eq_zero.1 this
  let nn : ℕ := ∏ x ∈ s, N x
  let b : Bp l a := ∑ x ∈ s, Polynomial.monomial x.1 (Polynomial.monomial x.2 ((nn / N x) • w x))
  have coeff_b : ∀ i n, (b.coeff i).coeff n = if (i, n) ∈ s then (nn / N (i, n)) • w (i, n) else 0 := by
    intro i n
    simp only [b, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_congr rfl (g := fun x => if x = (i, n) then (nn / N x) • w x else 0)]
    · exact Finset.sum_ite_eq' _ _ _
    · intro x _
      obtain ⟨x1, x2⟩ := x
      by_cases h1 : x1 = i <;> by_cases h2 : x2 = n <;> simp [h1, h2, Polynomial.coeff_monomial, Prod.ext_iff] <;> first | done | (subst h1; simp_all) | (split_ifs <;> simp_all)
  refine ⟨nn, b, ser w₁, ser c, Finset.prod_ne_zero_iff.2 fun x _ => hNpos x, ser_mem _ hw₁, ser_mem _ hc, ?_, ?_⟩
  · funext τ
    refine PowerSeries.ext fun i => PowerSeries.ext fun n => ?_
    rw [Pi.mul_apply, Pi.natCast_apply, coeff_coeff_natCast_mul, coeff_ser, coeff_iotaP, coeff_b]
    split_ifs with hx
    · have hdvd : N (i, n) ∣ nn := Finset.dvd_prod_of_mem N hx
      simp only [w₁, hx, if_true]
      rw [map_nsmul, nsmul_eq_mul, Nat.cast_div hdvd (hN0 _)]
      field_simp
    · simp [w₁, hx]
  · funext τ
    refine PowerSeries.ext fun i => PowerSeries.ext fun n => ?_
    rw [← Nat.cast_pow, Pi.add_apply, Pi.mul_apply, Pi.natCast_apply, map_add (f := _), map_add (f := _), coeff_coeff_natCast_mul,
      coeff_F, coeff_ser, coeff_ser, hsplit (i, n), map_add, map_mul, map_pow, map_natCast]
    push_cast
    ring

end GlobalTheory.CrysEval
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPolynomialApproxDividedTwoVariableSetStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism GlobalTheory.CrysEval
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_approx_dividedTwoVariableSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ PPSet t K e, ∀ r : ℕ, ∃ (n : ℕ) (b : Bp l a) (p h : ZMod a → K⟦X⟧⟦X⟧), n ≠ 0 ∧ p ∈ PPSet t K e ∧ h ∈ PPSet t K e ∧ (n : ZMod a → K⟦X⟧⟦X⟧) * p = iotaP K t b ∧ F = p + (l : ZMod a → K⟦X⟧⟦X⟧) ^ r * h := by
  first | exact @GlobalTheory.CrysEval.exists_poly_approx_PPSet | exact GlobalTheory.CrysEval.exists_poly_approx_PPSet | (intros; apply GlobalTheory.CrysEval.exists_poly_approx_PPSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdPolyEvaluationOfMemDividedTwoVariableSet
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdPolyEvaluationOfMemDividedTwoVariableSet
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism GlobalTheory.CrysEval
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.CrysEval

theorem coeff_natCast_mul_ps {R : Type} [CommRing R] (n i : ℕ) (f : R⟦X⟧) :
    coeff i ((n : R⟦X⟧) * f) = n * coeff i f := by
  rw [← map_natCast (C : R →+* R⟦X⟧) n, coeff_C_mul]

theorem dvd_fP_of_mem_PPSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (b : Bp l a) (F : ZMod a → K⟦X⟧⟦X⟧), F ∈ PPSet t K e → ∀ n : ℕ, n ≠ 0 → (n : ZMod a → K⟦X⟧⟦X⟧) * F = iotaP K t b → ∃ y : Per.Acris l, (n : Per.Acris l) * y = fP a ϖ (g : GQ l) b := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ g b F hF n hn hnF
  obtain ⟨w, -, hw⟩ := hF
  have := charZero_K (l := l) (K := K)
  have key : ∀ i k, ((i.factorial * (k / e).factorial : ℕ) : Wq l a) * (b.coeff i).coeff k = n * w (i, k) := by
    intro i k
    apply embK_injective (K := K) t 0
    have h1 := congrArg (fun G => coeff k (coeff i (G 0))) hnF
    simp only [Pi.mul_apply, Pi.natCast_apply] at h1
    rw [coeff_natCast_mul_ps, coeff_natCast_mul_ps, coeff_iotaP] at h1
    have h2 := hw 0 i k
    change _ = embK K t 0 (w (i, k)) at h2
    rw [map_mul, map_mul, map_natCast, map_natCast]
    push_cast at h2 ⊢
    linear_combination (-((i.factorial : K) * ((k / e).factorial : K))) * h1 + (n : K) * h2
  have hμ := ϖ.theta_mu (ϖ.gal_pi a g)
  set T := ainfToAcris l ϖ.teich with hTdef
  have term : ∀ i k, ainfToAcris l (wA l a ((b.coeff i).coeff k)) * T ^ k *
      ainfToAcris l (ϖ.mu (g : GQ l) * ϖ.teich) ^ i ∈ Ideal.span {(n : Per.Acris l)} := by
    intro i k
    obtain ⟨D, hD⟩ := ϖ.exists_dpow_teich (k / e)
    have hm := factorial_mul_dpow (ϖ.mu (g : GQ l)) hμ i
    have hk := congrArg (fun x => ainfToAcris l (wA l a x)) (key i k)
    simp only [map_mul, map_natCast] at hk
    push_cast at hk
    rw [Ideal.mem_span_singleton']
    refine ⟨ainfToAcris l (wA l a (w (i, k))) * D * dpow (ϖ.mu (g : GQ l)) hμ i * T ^ (k % e) * T ^ i, ?_⟩
    have hT : T ^ k = T ^ (k % e) * T ^ (e * (k / e)) := by rw [← pow_add, Nat.mod_add_div]
    rw [hT, ← hD, map_mul, mul_pow, ← hm]
    linear_combination (-(D * dpow (ϖ.mu (g : GQ l)) hμ i * T ^ (k % e) * T ^ i)) * hk
  have hmem : fP a ϖ (g : GQ l) b ∈ Ideal.span {(n : Per.Acris l)} := by
    rw [fP, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    refine Ideal.sum_mem _ fun i _ => ?_
    have hev : evC a ϖ (b.coeff i) = (b.coeff i).sum fun k c => ainfToAcris l (wA l a c) * T ^ k := by
      rw [evC, RingHom.comp_apply, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, ev_coe,
        Polynomial.eval₂_eq_sum, Polynomial.sum_def, Polynomial.sum_def]
      change ainfToAcris l _ = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, map_pow]
      rfl
    rw [hev, Polynomial.sum_def, Finset.sum_mul]
    exact Ideal.sum_mem _ fun k _ => term i k
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨y, by rw [mul_comm]; exact hy⟩

end GlobalTheory.CrysEval
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdPolyEvaluationOfMemDividedTwoVariableSetStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism GlobalTheory.CrysEval
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_polyEvaluation_of_mem_dividedTwoVariableSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (b : Bp l a) (F : ZMod a → K⟦X⟧⟦X⟧), F ∈ PPSet t K e → ∀ n : ℕ, n ≠ 0 → (n : ZMod a → K⟦X⟧⟦X⟧) * F = iotaP K t b → ∃ y : Per.Acris l, (n : Per.Acris l) * y = fP a ϖ (g : GQ l) b := by
  first | exact @GlobalTheory.CrysEval.dvd_fP_of_mem_PPSet | exact GlobalTheory.CrysEval.dvd_fP_of_mem_PPSet | (intros; apply GlobalTheory.CrysEval.dvd_fP_of_mem_PPSet <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineEvalRingHomFrobeniusTaylor
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysEval

section Main

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O)


omit [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] in
theorem iotaP_mem (b : Bp l a) : iotaP K t b ∈ PPSet t K e := by
  refine ⟨fun x => ((x.1.factorial * (x.2 / e).factorial : ℕ) : Wq l a) * (b.coeff x.1).coeff x.2,
    fun r => ?_, fun τ i n => ?_⟩
  · refine Filter.eventually_cofinite.2 (((Set.finite_Iic b.natDegree).prod (Set.finite_Iic
      ((Finset.range (b.natDegree + 1)).sup fun i => (b.coeff i).natDegree))).subset fun x hx => ?_)
    have h0 : (b.coeff x.1).coeff x.2 ≠ 0 := fun h0 => hx (by simp [h0])
    have h1 : b.coeff x.1 ≠ 0 := fun h1 => h0 (by simp [h1])
    have h2 := Polynomial.le_natDegree_of_ne_zero h1
    have h3 := Polynomial.le_natDegree_of_ne_zero h0
    exact ⟨h2, h3.trans (Finset.le_sup (f := fun i => (b.coeff i).natDegree)
      (Finset.mem_range.2 (Nat.lt_succ_of_le h2)))⟩
  · rw [coeff_iotaP]
    simp [embK, map_mul, map_natCast]


variable (K) in
def iotaD : Bp l a →+* PPd t K e :=
  (iotaP K t).codRestrict (PPd t K e) fun b => Subring.subset_closure (iotaP_mem t b)

omit [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedAlgebra ℚ_[l] K] in
@[simp] theorem coe_iotaD (b : Bp l a) : (iotaD K (e := e) t b : ZMod a → K⟦X⟧⟦X⟧) = iotaP K t b := rfl

theorem iotaP_C (q : Polynomial (Wq l a)) (τ : ZMod a) :
    iotaP K t (Polynomial.C q) τ = C (rhoK K t τ q) := by
  change PowerSeries.map (rhoK K t τ) ((Polynomial.C q : Bp l a) : (Polynomial (Wq l a))⟦X⟧) = _
  rw [Polynomial.coe_C, map_C]

theorem iotaP_X (τ : ZMod a) : iotaP K t (Polynomial.X : Bp l a) τ = X := by
  change PowerSeries.map (rhoK K t τ) ((Polynomial.X : Bp l a) : (Polynomial (Wq l a))⟦X⟧) = _
  rw [Polynomial.coe_X, map_X]

theorem rhoK_C (w : Wq l a) (τ : ZMod a) : rhoK K t τ (Polynomial.C w) = C (embK K t τ w) := by
  change PowerSeries.map (embK K t τ) ((Polynomial.C w : Polynomial (Wq l a)) : (Wq l a)⟦X⟧) = _
  rw [Polynomial.coe_C, map_C]

theorem rhoK_X (τ : ZMod a) : rhoK K t τ Polynomial.X = X := by
  change PowerSeries.map (embK K t τ) ((Polynomial.X : Polynomial (Wq l a)) : (Wq l a)⟦X⟧) = _
  rw [Polynomial.coe_X, map_X]

theorem coeff_iotaP_X (b : Bp l a) (τ : ZMod a) (i : ℕ) : coeff i (iotaP K t b τ) = rhoK K t τ (b.coeff i) := by
  change coeff i (PowerSeries.map (rhoK K t τ) (b : (Polynomial (Wq l a))⟦X⟧)) = _
  rw [coeff_map, Polynomial.coeff_coe]


omit [NeZero e] in
theorem constP_inclS_coe (q : Polynomial (Wq l a)) :
    constP a K (inclS t K (q : (Wq l a)⟦X⟧)) = iotaP K t (Polynomial.C q) := funext fun τ => by
  rw [iotaP_C, rhoK_eq_toAc]
  rfl


omit [NeZero e] in
theorem acris_complete : IsAdicComplete (Ideal.span {(l : Per.Acris l)}) (Per.Acris l) :=
  (GlobalTheory.MemLoc.acris_torsionFree_complete l).2

theorem denseD (F : PPd t K e) (r : ℕ) : ∃ (n : ℕ) (b : Bp l a) (p h : PPd t K e),
    n ≠ 0 ∧ (n : PPd t K e) * p = iotaD K t b ∧ F = p + (l : PPd t K e) ^ r * h := by
  obtain ⟨n, b, p, h, hn, hp, hh, hpb, hF⟩ := GlobalTheory.T.exists_polynomial_approx_dividedTwoVariableSet l a e O K t F (GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t _ F.2) r
  exact ⟨n, b, ⟨p, Subring.subset_closure hp⟩, ⟨h, Subring.subset_closure hh⟩, hn,
    Subtype.ext (by simpa [coe_iotaD] using hpb), Subtype.ext (by simpa using hF)⟩

variable (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a)))

theorem exists_E : ∃ E : PPd t K e →+* Per.Acris l,
    ∀ F r y, Approx l (iotaD K t) (fP a ϖ (g : GQ l)) F r y → (l : Per.Acris l) ^ r ∣ E F - y := by
  have := acris_complete (l := l)
  refine exists_ringHom (fun n x hn h => acris_nat_cancel hn h) (fun n b p hn hp => ?_) hl.out.ne_zero
    (fun F r => ?_)
  · exact GlobalTheory.T.dvd_polyEvaluation_of_mem_dividedTwoVariableSet l a e O K t ϖ g b p (GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t _ p.2) n hn
      (by simpa [coe_iotaD] using congrArg Subtype.val hp)
  · exact denseD t F r

def evE : PPd t K e →+* Per.Acris l := (exists_E t ϖ g).choose

theorem evE_approx (F : PPd t K e) (r : ℕ) (y : Per.Acris l)
    (h : Approx l (iotaD K t) (fP a ϖ (g : GQ l)) F r y) : (l : Per.Acris l) ^ r ∣ evE t ϖ g F - y :=
  (exists_E t ϖ g).choose_spec F r y h

theorem evE_iotaD (b : Bp l a) : evE t ϖ g (iotaD K t b) = fP a ϖ (g : GQ l) b := by
  have := acris_complete (l := l)
  exact sub_eq_zero.1 (sep_l l _ fun r => evE_approx t ϖ g _ r _ (approx_ι b r))

theorem evE_of_eq {F : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPd t K e) (b : Bp l a) (h : F = iotaP K t b) :
    evE t ϖ g ⟨F, hF⟩ = fP a ϖ (g : GQ l) b := by
  subst h
  exact evE_iotaD t ϖ g b

omit [NeZero e] in
theorem fP_C (q : Polynomial (Wq l a)) (g' : GQ l) : fP a ϖ g' (Polynomial.C q) = ainfToAcris l (ϖ.ev a q) := by
  simp [fP, evC]

omit [NeZero e] in
theorem fP_X (g' : GQ l) : fP a ϖ g' Polynomial.X = ainfToAcris l (ϖ.mu g' * ϖ.teich) := by
  simp [fP]


omit [NeZero a] [NeZero e] in
theorem sep_teich_acris (x : Per.Acris l) (h : ∀ n, ainfToAcris l ϖ.teich ^ n ∣ x) : x = 0 := by
  have := acris_complete (l := l)
  refine sep_l l x fun r => ?_
  obtain ⟨d, hd⟩ := ϖ.exists_dpow_teich (l ^ r)
  obtain ⟨k, hk⟩ := Nat.dvd_factorial (pow_pos hl.out.pos r) (le_refl (l ^ r))
  refine Dvd.dvd.trans ⟨k * d, ?_⟩ (h (e * l ^ r))
  rw [← hd, hk]
  push_cast
  ring

theorem constP_inclS_mem (x : (Wq l a)⟦X⟧) : constP a K (inclS t K x) ∈ PPd t K e :=
  Subring.subset_closure (constP_mem t e (GlobalTheory.T.unramifiedWittPowerSeries_mem_dividedPowerSeriesGeneratorSet l a e O K t x))

theorem evE_constP_coe (q : Polynomial (Wq l a)) (h : constP a K (inclS t K (q : (Wq l a)⟦X⟧)) ∈ PPd t K e) :
    evE t ϖ g ⟨_, h⟩ = ainfToAcris l (ϖ.ev a q) :=
  (evE_of_eq t ϖ g h _ (constP_inclS_coe t q)).trans (fP_C ϖ q _)

theorem evE_constP (x : (Wq l a)⟦X⟧) (hx : constP a K (inclS t K x) ∈ PPd t K e) :
    evE t ϖ g ⟨_, hx⟩ = ainfToAcris l (ϖ.ev a x) := by
  let φ : (Wq l a)⟦X⟧ →+* Per.Acris l :=
    (evE t ϖ g).comp (((constP a K).comp (inclS t K)).codRestrict _ (constP_inclS_mem t))
  have hφ : ∀ q : Polynomial (Wq l a), φ q = ainfToAcris l (ϖ.ev a q) := fun q =>
    evE_constP_coe t ϖ g q _
  have hφX : φ X = ainfToAcris l ϖ.teich := by
    have := hφ Polynomial.X
    rwa [Polynomial.coe_X, PiSys.ev_X] at this
  have h := ringHom_ext_of_sep φ ((ainfToAcris l).toRingHom.comp (ϖ.ev a)) (fun w => ?_) ?_
    (fun y hy => sep_teich_acris ϖ y fun n => hφX ▸ hy n)
  · exact RingHom.congr_fun h x
  · have := hφ (Polynomial.C w)
    rwa [Polynomial.coe_C] at this
  · have := hφ Polynomial.X
    rwa [Polynomial.coe_X] at this

omit [NeZero a] [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] in
theorem frobenius_teich_mul (g' : GQ l) :
    WittVector.frobenius ((1 + ϖ.mu g') * ϖ.teich) = ((1 + ϖ.mu g') * ϖ.teich) ^ l := by
  rw [PiSys.mu, add_sub_cancel, PiSys.teich, ← map_mul, WittVector.frobenius_eq_map_frobenius,
    WittVector.map_teichmuller, frobenius_def, map_pow]

section Sh

variable (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
  (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f)
include hsh


omit [NeZero a] [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] in
theorem sh_C [CharZero K] (c : K) : sh (C c) = C (C c) := by
  ext i : 1
  rcases i with _ | i
  · simpa [coeff_C] using hsh (C c) 0
  · have h := hsh (C c) (i + 1)
    have h4 : (PowerSeries.derivative (R := K))^[i + 1] (C c) = 0 := by
      rw [Function.iterate_succ_apply, PowerSeries.derivative_C]
      exact Function.iterate_fixed (map_zero _) i
    rw [h4] at h
    rw [(mul_eq_zero.1 h).resolve_left (natCast_ne_zero_ps (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))),
      coeff_C, if_neg (Nat.succ_ne_zero i)]

theorem shP_mem (x : (Wq l a)⟦X⟧) : shP a sh (inclS t K (frobS l a x)) ∈ PPd t K e :=
  Subring.subset_closure (GlobalTheory.T.taylorShift_frobenius_mem_dividedTwoVariableGeneratorSet l a e O K t sh hsh x).1

omit [NeZero e] in
theorem shP_frobS_C (w : Wq l a) :
    shP a sh (inclS t K (frobS l a (C w))) = iotaP K t (Polynomial.C (Polynomial.C (sigma l a w))) := by
  have := charZero_K (l := l) (K := K)
  funext τ
  rw [iotaP_C, rhoK_C, frobS_C]
  change sh (toAc t K (C (sigma l a w)) τ : K⟦X⟧) = _
  rw [show (toAc t K (C (sigma l a w)) τ : K⟦X⟧) = C (embK K t τ (sigma l a w)) from
    PowerSeries.ext fun n => by rw [coeff_toAc, coeff_C, coeff_C]; split_ifs <;> simp [embK]]
  exact sh_C sh hsh _

omit [NeZero e] in
theorem shP_frobS_X :
    shP a sh (inclS t K (frobS l a X)) = iotaP K t ((Polynomial.C Polynomial.X + Polynomial.X) ^ l) := by
  have := charZero_K (l := l) (K := K)
  funext τ
  rw [map_pow, map_add (f := _), Pi.pow_apply, Pi.add_apply, iotaP_C, rhoK_X, iotaP_X, frobS_X, map_pow, map_pow,
    Pi.pow_apply]
  change sh (toAc t K X τ : K⟦X⟧) ^ l = _
  rw [show (toAc t K X τ : K⟦X⟧) = X from PowerSeries.ext fun n => by
    rw [coeff_toAc, coeff_X, coeff_X]; split_ifs <;> simp]
  rw [sh_X sh hsh]

theorem evE_shP (x : (Wq l a)⟦X⟧) (hx : shP a sh (inclS t K (frobS l a x)) ∈ PPd t K e) :
    evE t ϖ g ⟨_, hx⟩ = ainfToAcris l (WittVector.frobenius (Per.σA (g : GQ l) (ϖ.ev a x))) := by
  let φ : (Wq l a)⟦X⟧ →+* Per.Acris l := (evE t ϖ g).comp
    (((shP a sh).comp ((inclS t K).comp (frobS l a))).codRestrict _ (shP_mem t sh hsh))
  let ψ : (Wq l a)⟦X⟧ →+* Per.Acris l := (ainfToAcris l).toRingHom.comp
    (WittVector.frobenius.comp ((Per.σA (g : GQ l)).comp (ϖ.ev a)))
  have hψX : ψ X = (ainfToAcris l ((1 + ϖ.mu g) * ϖ.teich)) ^ l := by
    change ainfToAcris l (WittVector.frobenius (Per.σA (g : GQ l) (ϖ.ev a X))) = _
    rw [PiSys.ev_X, PiSys.gal_teich, frobenius_teich_mul, map_pow]
  have hπ : ainfToAcris l ϖ.teich ∣ ψ X := by
    rw [hψX, map_mul]
    exact (dvd_mul_left _ _).trans (dvd_pow_self _ hl.out.ne_zero)
  have hg : ∀ y ∈ Kunr l a, (g : GQ l) y = y := fun y hy =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 y (ϖ.Kunr_le_field a hy)
  have hφC : ∀ w, φ (C w) = ψ (C w) := fun w => by
    change evE t ϖ g ⟨shP a sh (inclS t K (frobS l a (C w))), shP_mem t sh hsh _⟩ =
      ainfToAcris l (WittVector.frobenius (Per.σA (g : GQ l) (ϖ.ev a (C w))))
    rw [evE_of_eq t ϖ g _ _ (shP_frobS_C t sh hsh w), fP_C, Polynomial.coe_C, PiSys.ev_C, PiSys.ev_C,
      gal_wA l a hg, wA_sigma]
  have hφX : φ X = ψ X := by
    change evE t ϖ g ⟨shP a sh (inclS t K (frobS l a X)), shP_mem t sh hsh _⟩ =
      ainfToAcris l (WittVector.frobenius (Per.σA (g : GQ l) (ϖ.ev a X)))
    rw [evE_of_eq t ϖ g _ _ (shP_frobS_X t sh hsh), map_pow, map_add (f := _), fP_C, fP_X, Polynomial.coe_X, PiSys.ev_X,
      PiSys.gal_teich, frobenius_teich_mul, map_pow, map_mul, map_mul, map_add, map_one]
    ring
  have h := ringHom_ext_of_sep ψ φ (fun w => (hφC w).symm) hφX.symm (fun y hy => sep_teich_acris ϖ y fun n =>
    (pow_dvd_pow_of_dvd hπ n).trans (hy n))
  exact (RingHom.congr_fun h x).symm

end Sh

omit [NeZero a] [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] in
theorem frobenius_teich : WittVector.frobenius ϖ.teich = ϖ.teich ^ l := by
  rw [WittVector.frobenius_eq_map_frobenius, PiSys.teich, WittVector.map_teichmuller, frobenius_def, map_pow]

theorem evE_ext (G₁ G₂ : PPd t K e →+* Per.Acris l) (h : ∀ b, G₁ (iotaD K t b) = G₂ (iotaD K t b)) : G₁ = G₂ := by
  have := acris_complete (l := l)
  exact ringHom_ext_dense (ι := iotaD K t) (fun n x hn h => acris_nat_cancel hn h) hl.out.ne_zero
    (denseD (e := e) t) G₁ G₂ h

section Frob

variable (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
  (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f)
  (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧) (hφC : ∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f))
  (hφsh : ∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f))
include hsh hφC hφsh

theorem bivariateFrobenius_mem_dividedSubring {F : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPd t K e) : frob2 φ₂ F ∈ PPd t K e :=
  Subring.subset_closure (GlobalTheory.T.frob2_mem_PPSet_and_eq_pow_add_mul l a e O K t sh hsh φ₂ hφC hφsh F (GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t F hF)).1

omit [NeZero a] [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in
theorem φ₂_X : φ₂ X = (C X + X) ^ l - C (X ^ l) := by
  have := charZero_K (l := l) (K := K)
  have h : (X : K⟦X⟧⟦X⟧) = sh X - C X := by rw [sh_X sh hsh]; ring
  conv_lhs => rw [h]
  rw [map_sub, hφsh, hφC, frob_X, map_pow]
  rw [sh_X sh hsh]

omit [NeZero e] in
theorem bivariateFrobenius_bivariateEmbedding_CC (w : Wq l a) :
    frob2 φ₂ (iotaP K t (Polynomial.C (Polynomial.C w))) = iotaP K t (Polynomial.C (Polynomial.C (sigma l a w))) := by
  funext τ
  change φ₂ (iotaP K t (Polynomial.C (Polynomial.C w)) (τ - 1)) = _
  rw [iotaP_C, iotaP_C, rhoK_C, rhoK_C, hφC, frob_C]
  congr 2
  simp only [embK, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, emb_sigma]

omit [NeZero e] in
theorem bivariateFrobenius_bivariateEmbedding_CX :
    frob2 φ₂ (iotaP K t (Polynomial.C Polynomial.X)) = iotaP K t (Polynomial.C (Polynomial.X ^ l)) := by
  funext τ
  change φ₂ (iotaP K t (Polynomial.C Polynomial.X) (τ - 1)) = _
  rw [iotaP_C, iotaP_C, rhoK_X, map_pow, rhoK_X, hφC, frob_X]

omit [NeZero e] in
theorem bivariateFrobenius_bivariateEmbedding_X : frob2 φ₂ (iotaP K t Polynomial.X) =
    iotaP K t ((Polynomial.C Polynomial.X + Polynomial.X) ^ l - (Polynomial.C Polynomial.X) ^ l) := by
  funext τ
  change φ₂ (iotaP K t Polynomial.X (τ - 1)) = _
  rw [iotaP_X, φ₂_X sh hsh φ₂ hφC hφsh]
  simp only [map_sub, map_pow, map_add (f := _), Pi.sub_apply, Pi.pow_apply, Pi.add_apply, iotaP_C, iotaP_X, rhoK_X]

theorem evE_frob2 : (evE t ϖ g).comp ((frob2 φ₂).restrict (PPd t K e) (PPd t K e)
    fun _ hF => bivariateFrobenius_mem_dividedSubring t sh hsh φ₂ hφC hφsh hF) = (frobC l).toRingHom.comp (evE t ϖ g) := by
  refine evE_ext t _ _ fun b => ?_
  have key : ∀ b b' : Bp l a, frob2 φ₂ (iotaP K t b) = iotaP K t b' →
      fP a ϖ (g : GQ l) b' = frobC l (fP a ϖ (g : GQ l) b) →
      ((evE t ϖ g).comp ((frob2 φ₂).restrict (PPd t K e) (PPd t K e)
        fun _ hF => bivariateFrobenius_mem_dividedSubring t sh hsh φ₂ hφC hφsh hF)) (iotaD K t b) =
      ((frobC l).toRingHom.comp (evE t ϖ g)) (iotaD K t b) := fun b b' h1 h2 => by
    have hm : frob2 φ₂ (iotaP K t b) ∈ PPd t K e :=
      bivariateFrobenius_mem_dividedSubring t sh hsh φ₂ hφC hφsh (Subring.subset_closure (iotaP_mem t b))
    change evE t ϖ g ⟨frob2 φ₂ (iotaP K t b), hm⟩ = frobC l (evE t ϖ g (iotaD K t b))
    rw [evE_of_eq t ϖ g hm b' h1, evE_iotaD, h2]
  let H₁ := ((evE t ϖ g).comp ((frob2 φ₂).restrict (PPd t K e) (PPd t K e)
    fun _ hF => bivariateFrobenius_mem_dividedSubring t sh hsh φ₂ hφC hφsh hF)).comp (iotaD K t)
  let H₂ := ((frobC l).toRingHom.comp (evE t ϖ g)).comp (iotaD K t)
  have hC : H₁.comp Polynomial.C = H₂.comp Polynomial.C := by
    refine Polynomial.ringHom_ext (fun w => ?_) ?_
    · refine key _ _ (bivariateFrobenius_bivariateEmbedding_CC t sh hsh φ₂ hφC hφsh w) ?_
      rw [fP_C, fP_C, Polynomial.coe_C, Polynomial.coe_C, PiSys.ev_C, PiSys.ev_C, wA_sigma,
        GlobalTheory.AcrisPrism.frobC_ainfToAcris]
    · refine key _ _ (bivariateFrobenius_bivariateEmbedding_CX t sh hsh φ₂ hφC hφsh) ?_
      rw [fP_C, fP_C, Polynomial.coe_pow, Polynomial.coe_X, map_pow, PiSys.ev_X,
        GlobalTheory.AcrisPrism.frobC_ainfToAcris, frobenius_teich, map_pow]
  have h := Polynomial.ringHom_ext (f := H₁) (g := H₂) (fun q => RingHom.congr_fun hC q) (by
    refine key _ _ (bivariateFrobenius_bivariateEmbedding_X t sh hsh φ₂ hφC hφsh) ?_
    rw [map_sub, map_pow, map_pow, map_add (f := _), fP_C, fP_X, Polynomial.coe_X, PiSys.ev_X,
      GlobalTheory.AcrisPrism.frobC_ainfToAcris]
    have e1 : WittVector.frobenius (ϖ.mu (g : GQ l) * ϖ.teich) =
        ((1 + ϖ.mu (g : GQ l)) * ϖ.teich) ^ l - ϖ.teich ^ l := by
      rw [show ϖ.mu (g : GQ l) * ϖ.teich = (1 + ϖ.mu (g : GQ l)) * ϖ.teich - ϖ.teich by ring, map_sub,
        frobenius_teich_mul, frobenius_teich]
    rw [e1, map_sub, map_pow, map_pow, map_mul, map_mul, map_add (f := _), map_one]
    ring)
  exact RingHom.congr_fun h b

end Frob

theorem iC_rhoK (q : Polynomial (Wq l a)) (hq : ∀ τ, rhoK K t τ q ∈ S O K e) :
    ϖ.iC t K (fun τ => ⟨rhoK K t τ q, hq τ⟩) = 1 ⊗ₜ ainfToAcris l (ϖ.ev a q) := by
  have h : (fun τ => (⟨rhoK K t τ q, hq τ⟩ : S O K e)) =
      fun τ => ⟨(toAc t K (q : (Wq l a)⟦X⟧) τ : K⟦X⟧), A_le_S l e (toAc t K (q : (Wq l a)⟦X⟧) τ).2⟩ :=
    funext fun τ => Subtype.ext (rhoK_eq_toAc t q τ)
  rw [h, PiSys.iC_of_mem, PiSys.iTot_toAc, toOCr_tmul]

theorem iC_u : ϖ.iC t K (fun _ => uIn (S O K e)) = 1 ⊗ₜ ainfToAcris l ϖ.teich := by
  have hX : ∀ τ, rhoK K t τ Polynomial.X ∈ S O K e := fun τ => by rw [rhoK_X]; exact HasU.X_mem
  have e1 : (fun _ => uIn (S O K e) : ZMod a → S O K e) = fun τ => ⟨rhoK K t τ Polynomial.X, hX τ⟩ :=
    funext fun τ => Subtype.ext (rhoK_X t τ).symm
  rw [e1, iC_rhoK, Polynomial.coe_X, PiSys.ev_X]

theorem taylor_term (b : Bp l a) (p : ZMod a → K⟦X⟧⟦X⟧) (N : ℕ) (hpb : (N : ZMod a → K⟦X⟧⟦X⟧) * p = iotaP K t b)
    (i : ℕ) (hSp : ∀ τ, (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (p τ)) ∈ S O K e) :
    (N : OCr l O) * (ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hSp τ⟩)) =
      1 ⊗ₜ (ainfToAcris l (ϖ.ev a (b.coeff i)) * ainfToAcris l (ϖ.mu g * ϖ.teich) ^ i) := by
  let j : Per.Acris l →ₐ[ℤ_[l]] OCr l O := Algebra.TensorProduct.includeRight
  have hq : ∀ τ, rhoK K t τ (b.coeff i) ∈ S O K e := fun τ => by
    rw [rhoK_eq_toAc]; exact A_le_S l e (toAc t K _ τ).2
  have e1 : (N : ZMod a → S O K e) * (fun τ => ⟨_, hSp τ⟩) =
      (fun _ => uIn (S O K e)) ^ i * (i.factorial : ZMod a → S O K e) *
        fun τ => ⟨rhoK K t τ (b.coeff i), hq τ⟩ := funext fun τ => Subtype.ext (by
    have h2 := congrArg (fun G => coeff i (G τ)) hpb
    simp only [Pi.mul_apply, Pi.natCast_apply] at h2
    rw [← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), coeff_C_mul, coeff_iotaP_X] at h2
    simp only [Pi.mul_apply, Pi.natCast_apply, Pi.pow_apply, Subalgebra.coe_mul, Subalgebra.coe_pow,
      SubringClass.coe_natCast, coe_uIn]
    rw [← h2]; ring)
  have hA : (N : OCr l O) * ϖ.iC t K (fun τ => ⟨_, hSp τ⟩) =
      j (ainfToAcris l ϖ.teich) ^ i * (i.factorial : OCr l O) * j (ainfToAcris l (ϖ.ev a (b.coeff i))) := by
    rw [← map_natCast (ϖ.iC t K), ← map_mul, e1, map_mul, map_mul, map_pow, map_natCast, iC_u, iC_rhoK]
    rfl
  have h3 : (i.factorial : OCr l O) * ϖ.muDiv a O g i = j (ainfToAcris l (ϖ.mu g)) ^ i := by
    have h4 := congrArg j (factorial_mul_dpow (ϖ.mu g) (ϖ.theta_mu (ϖ.gal_pi a g)) i)
    rw [map_mul, map_natCast, map_pow] at h4
    exact h4
  rw [mul_left_comm, hA]
  change _ = j _
  rw [map_mul, map_pow, map_mul, map_mul]
  linear_combination (j (ainfToAcris l ϖ.teich) ^ i * j (ainfToAcris l (ϖ.ev a (b.coeff i)))) * h3

theorem taylor_poly (b : Bp l a) (p : ZMod a → K⟦X⟧⟦X⟧) (hp : p ∈ PPd t K e) (N : ℕ) (hN : N ≠ 0)
    (hpb : (N : ZMod a → K⟦X⟧⟦X⟧) * p = iotaP K t b)
    (hSp : ∀ τ i, (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (p τ)) ∈ S O K e) (n : ℕ) (hn : b.natDegree < n) :
    (1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨p, hp⟩ -
      ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hSp τ i⟩) = 0 := by
  let j : Per.Acris l →ₐ[ℤ_[l]] OCr l O := Algebra.TensorProduct.includeRight
  refine nat_cancel_OCr hN ?_
  have e1 : (N : PPd t K e) * ⟨p, hp⟩ = iotaD K t b := Subtype.ext (by simpa [coe_iotaD] using hpb)
  have e2 : (N : Per.Acris l) * evE t ϖ g ⟨p, hp⟩ = fP a ϖ (g : GQ l) b := by
    rw [← map_natCast (evE (K := K) (e := e) t ϖ g), ← map_mul, e1, evE_iotaD]
  have e3 : fP a ϖ (g : GQ l) b = ∑ i ∈ Finset.range n,
      ainfToAcris l (ϖ.ev a (b.coeff i)) * ainfToAcris l (ϖ.mu g * ϖ.teich) ^ i := by
    rw [fP, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range' _ hn]
    rfl
  have e4 : (N : OCr l O) * (1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨p, hp⟩ = j (fP a ϖ (g : GQ l) b) := by
    rw [← e2, map_mul, map_natCast]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [mul_sub, Finset.mul_sum, e4, Finset.sum_congr rfl fun i _ => taylor_term t ϖ g b p N hpb i (fun τ => hSp τ i),
    e3, map_sum]
  exact sub_eq_zero.2 (Finset.sum_congr rfl fun i _ => rfl)

theorem evE_taylor (F : ZMod a → K⟦X⟧⟦X⟧) (hF : F ∈ PPd t K e)
    (hS : ∀ (τ : ZMod a) (i : ℕ), (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (F τ)) ∈ S O K e) (r : ℕ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ (1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨F, hF⟩ -
      ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hS τ i⟩) := by
  let j : Per.Acris l →ₐ[ℤ_[l]] OCr l O := Algebra.TensorProduct.includeRight
  obtain ⟨N, b, p, h, hN, hp, hh, hpb, hFeq⟩ :=
    GlobalTheory.T.exists_polynomial_approx_dividedTwoVariableSet l a e O K t F (GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet l a e O K t F hF) r
  have hcoef : ∀ τ i, coeff i (F τ) = coeff i (p τ) + (l : K⟦X⟧) ^ r * coeff i (h τ) := fun τ i => by
    have h1 := congrFun hFeq τ
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply] at h1
    rw [h1, map_add (f := _), ← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), ← map_pow, coeff_C_mul]
  have hSh : ∀ τ i, (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (h τ)) ∈ S O K e := fun τ i =>
    mul_mem (pow_mem HasU.X_mem i) (GlobalTheory.T.factorial_mul_coeff_mem_dividedPowerSeriesSubring l a e O K t h hh τ i)
  have hSp : ∀ τ i, (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (p τ)) ∈ S O K e := fun τ i => by
    have e1 : (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (p τ)) =
        (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (F τ)) -
          (l : K⟦X⟧) ^ r * ((X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (h τ))) := by
      rw [hcoef]; ring
    rw [e1]
    exact sub_mem (hS τ i) (mul_mem (pow_mem (natCast_mem _ l) r) (hSh τ i))
  have hp' : p ∈ PPd t K e := Subring.subset_closure hp
  have hh' : h ∈ PPd t K e := Subring.subset_closure hh
  have hsplit : ∀ i, ϖ.iC t K (fun τ => ⟨_, hS τ i⟩) =
      ϖ.iC t K (fun τ => ⟨_, hSp τ i⟩) + (l : OCr l O) ^ r * ϖ.iC t K (fun τ => ⟨_, hSh τ i⟩) := fun i => by
    have e1 : (fun τ => (⟨_, hS τ i⟩ : S O K e)) =
        (fun τ => (⟨_, hSp τ i⟩ : S O K e)) + (l : ZMod a → S O K e) ^ r * fun τ => ⟨_, hSh τ i⟩ :=
      funext fun τ => Subtype.ext (by
        simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, Subalgebra.coe_add,
          Subalgebra.coe_mul, Subalgebra.coe_pow, SubringClass.coe_natCast]
        rw [hcoef]; ring)
    rw [e1, map_add (f := _), map_mul, map_pow, map_natCast]
  have hEsplit : (1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨F, hF⟩ = (1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨p, hp'⟩ +
      (l : OCr l O) ^ r * (1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨h, hh'⟩ := by
    have e1 : (⟨F, hF⟩ : PPd t K e) = ⟨p, hp'⟩ + (l : PPd t K e) ^ r * ⟨h, hh'⟩ := Subtype.ext (by simpa using hFeq)
    rw [e1, map_add (f := _), map_mul, map_pow, map_natCast]
    change j _ = j _ + _ * j _
    rw [map_add (f := _), map_mul, map_pow, map_natCast]
  refine ⟨b.natDegree + 1, fun n hn => ⟨(1 : O) ⊗ₜ[ℤ_[l]] evE t ϖ g ⟨h, hh'⟩ -
    ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hSh τ i⟩), ?_⟩⟩
  have hz := taylor_poly t ϖ g b p hp' N hN hpb hSp n (by omega)
  have e4 : ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hS τ i⟩) =
      ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hSp τ i⟩) +
        (l : OCr l O) ^ r * ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hSh τ i⟩) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hsplit]; ring
  rw [hEsplit, e4]
  linear_combination hz

end Main

theorem evalPP : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ g : ↥(GK (ϖ.field a)), ∃ E : ↥(PPd t K e) →+* Per.Acris l, (∀ (x : (Wq l a)⟦X⟧) (hx : constP a K (inclS t K (frobS l a x)) ∈ PPd t K e), E ⟨_, hx⟩ = ainfToAcris l (WittVector.frobenius (ϖ.ev a x))) ∧ (∀ (x : (Wq l a)⟦X⟧) (hx : shP a sh (inclS t K (frobS l a x)) ∈ PPd t K e), E ⟨_, hx⟩ = ainfToAcris l (WittVector.frobenius (Per.σA (g : GQ l) (ϖ.ev a x)))) ∧ (∀ (F : ZMod a → K⟦X⟧⟦X⟧) (hF : F ∈ PPd t K e) (hF' : frob2 φ₂ F ∈ PPd t K e), E ⟨_, hF'⟩ = frobC l (E ⟨F, hF⟩)) ∧ ∀ (F : ZMod a → K⟦X⟧⟦X⟧) (hF : F ∈ PPd t K e) (hS : ∀ (τ : ZMod a) (i : ℕ), (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (F τ)) ∈ S O K e) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ (1 : O) ⊗ₜ[ℤ_[l]] E ⟨F, hF⟩ - ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hS τ i⟩) :=
  fun l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ sh hsh φ₂ hφC hφsh g =>
    ⟨evE t ϖ g, fun x hx => by rw [evE_constP, PiSys.ev_frobS], fun x hx => evE_shP t ϖ g sh hsh x hx,
      fun F hF hF' => RingHom.congr_fun (evE_frob2 t ϖ g sh hsh φ₂ hφC hφsh) ⟨F, hF⟩,
      fun F hF hS r => evE_taylor t ϖ g F hF hS r⟩

end GlobalTheory.CrysEval
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineEvalRingHomFrobeniusTaylorStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineEval_ringHom_frobenius_taylor : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) → ∀ g : ↥(GK (ϖ.field a)), ∃ E : ↥(PPd t K e) →+* Per.Acris l, (∀ (x : (Wq l a)⟦X⟧) (hx : constP a K (inclS t K (frobS l a x)) ∈ PPd t K e), E ⟨_, hx⟩ = ainfToAcris l (WittVector.frobenius (ϖ.ev a x))) ∧ (∀ (x : (Wq l a)⟦X⟧) (hx : shP a sh (inclS t K (frobS l a x)) ∈ PPd t K e), E ⟨_, hx⟩ = ainfToAcris l (WittVector.frobenius (Per.σA (g : GQ l) (ϖ.ev a x)))) ∧ (∀ (F : ZMod a → K⟦X⟧⟦X⟧) (hF : F ∈ PPd t K e) (hF' : frob2 φ₂ F ∈ PPd t K e), E ⟨_, hF'⟩ = frobC l (E ⟨F, hF⟩)) ∧ ∀ (F : ZMod a → K⟦X⟧⟦X⟧) (hF : F ∈ PPd t K e) (hS : ∀ (τ : ZMod a) (i : ℕ), (X : K⟦X⟧) ^ i * ((i.factorial : K⟦X⟧) * coeff i (F τ)) ∈ S O K e) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣ (1 : O) ⊗ₜ[ℤ_[l]] E ⟨F, hF⟩ - ∑ i ∈ Finset.range n, ϖ.muDiv a O g i * ϖ.iC t K (fun τ => ⟨_, hS τ i⟩) := by
  first | exact @GlobalTheory.CrysEval.evalPP | exact GlobalTheory.CrysEval.evalPP | (intros; apply GlobalTheory.CrysEval.evalPP <;> assumption)
end
