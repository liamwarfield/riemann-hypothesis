module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentDataHodgeBound
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestOrderSections
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.KernelMem
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ReducesAtOfWithE
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsDualFamily
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ValCastSub

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsUnitOfVal
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Num.FamEx PositivityTheory.HtPt.Sgp
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

theorem bcLin_apply {Ω C : Type} [Field Ω] [Field C] [Algebra Ω C] {m n : ℕ} (f : (Fin m → Ω) →ₗ[Ω] (Fin n → Ω))
    (x : Fin m → C) (k : Fin n) : TestPt.bcLin C f x k = ∑ i, algebraMap Ω C (f (Pi.single i 1) k) * x i := by
  simp only [TestPt.bcLin, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, LinearMap.toMatrix'_apply]
  try (refine Finset.sum_congr rfl fun i _ => ?_; congr 4; funext j; simp [Pi.single_apply])

theorem bcLin_bc {Ω C : Type} [Field Ω] [Field C] [Algebra Ω C] {m n : ℕ} (f : (Fin m → Ω) →ₗ[Ω] (Fin n → Ω))
    (x : Fin m → Ω) (k : Fin n) : TestPt.bcLin C f (fun i => algebraMap Ω C (x i)) k = algebraMap Ω C (f x k) := by
  rw [bcLin_apply]
  have h := congrFun (LinearMap.toMatrix'_mulVec f x) k
  rw [← h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, LinearMap.toMatrix'_apply, map_sum, map_mul]

theorem isUnit_of_val {O C : Type} [CommRing O] [Field C] [Algebra O C] {RC : Subalgebra O C} {v : Valuation C NNReal}
    (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) (a : RC) (ha : v (a : C) = 1) : IsUnit a := by
  have h0 : (a : C) ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact zero_ne_one ha
  have hi : (a : C)⁻¹ ∈ RC := (hv _).2 (by rw [map_inv₀, ha, inv_one])
  refine ⟨⟨a, ⟨_, hi⟩, ?_, ?_⟩, rfl⟩
  · ext
    simp [h0]
  · ext
    simp [h0]

theorem chi_cong {E : Type} [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {C : Type} [Field C] [Algebra O C] (RC : Subalgebra O C) (v : Valuation C NNReal) (hv : ∀ c, c ∈ RC ↔ v c ≤ 1)
    {F : Type} [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F)
    (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (hsec : IsSec pq sc)
    (σF : F →+* IsLocalRing.ResidueField O) (χ : F →*₀ C)
    (hχ : ∀ a (o : O), IsLocalRing.residue O o = σF a →
      χ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ a - algebraMap O C o) ≠ 1)
    (σ : 𝓞 E →+* RC)
    (hσ : ∀ a, ∃ o : O, algebraMap O C o = σ a ∧ IsLocalRing.residue O o = σF (pq (Ideal.Quotient.mk _ a))) :
    ∃ χ' : F → RC, (∀ a, χ a = χ' a) ∧ ∀ a, χ' (pq (Ideal.Quotient.mk _ a)) - σ a ∈ Ideal.span {(p : RC)} := by
  have hmem : ∀ a, χ a ∈ RC := by
    intro a
    obtain ⟨o, ho⟩ := IsLocalRing.residue_surjective (σF a)
    have h1 := (hχ a o ho).1
    have h2 : algebraMap O C o ∈ RC := RC.algebraMap_mem o
    simpa using RC.add_mem h1 h2
  refine ⟨fun a => ⟨χ a, hmem a⟩, fun a => rfl, ?_⟩
  intro a
  have hq2 : 1 < Fintype.card F := Fintype.one_lt_card
  obtain ⟨f, -, hq⟩ := FiniteField.card F p
  set x := pq (Ideal.Quotient.mk _ a) with hx
  set c0 : RC := ⟨χ x, hmem x⟩ with hc0
  set d : RC := c0 - σ a with hd
  have hdn : ¬ IsUnit d := by
    obtain ⟨o, ho1, ho2⟩ := hσ a
    rintro ⟨u, hu⟩
    apply (hχ x o ho2).2 (((u⁻¹ : RCˣ) : RC) : C) ((u⁻¹ : RCˣ) : RC).2
    have h3 : ((u⁻¹ : RCˣ) : RC) * d = 1 := by rw [← hu]; simp
    have h4 := congrArg (fun r : RC => (r : C)) h3
    simp only [hd, hc0, Subalgebra.coe_mul, Subalgebra.coe_sub, Subalgebra.coe_one] at h4
    rw [ho1]
    exact h4
  have hvd : v (d : C) < 1 := by
    refine lt_of_le_of_ne ((hv _).1 d.2) ?_
    intro h
    exact hdn (isUnit_of_val hv d h)
  by_cases hpu : IsUnit (p : RC)
  · rw [Ideal.span_singleton_eq_top.mpr hpu]
    trivial
  haveI : CharP (RC ⧸ Ideal.span {(p : RC)}) p := CharP.quotient RC p hpu
  have hσq : σ a ^ Fintype.card F - σ a ∈ Ideal.span {(p : RC)} := by
    obtain ⟨e', he'⟩ := Ideal.Quotient.mk_surjective (sc 1)
    have hker : (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 E)}) (a ^ Fintype.card F - a)) * sc 1 = 0 := by
      apply hsec.2
      simp [map_sub, map_pow, FiniteField.pow_card]
    rw [← he', ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hker
    obtain ⟨c, hc⟩ := hker
    have hσe : IsUnit (σ e') := by
      obtain ⟨o, ho1, ho2⟩ := hσ e'
      have hres : IsLocalRing.residue O o ≠ 0 := by
        rw [ho2, he', hsec.1, map_one]
        exact one_ne_zero
      have hu := (IsLocalRing.residue_ne_zero_iff_isUnit o).1 hres
      have h5 : σ e' = algebraMap O RC o := Subtype.ext (by rw [← ho1]; rfl)
      rw [h5]
      exact hu.map _
    obtain ⟨w, hw⟩ := hσe
    have h2 := congrArg σ hc
    simp only [map_mul, map_sub, map_pow, map_natCast] at h2
    have h6 : σ a ^ Fintype.card F - σ a = (p : RC) * (σ c * ↑w⁻¹) := by
      calc σ a ^ Fintype.card F - σ a = (σ a ^ Fintype.card F - σ a) * σ e' * ↑w⁻¹ := by
            rw [← hw, mul_assoc, Units.mul_inv, mul_one]
        _ = _ := by rw [h2, mul_assoc]
    rw [h6]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hχq : c0 ^ Fintype.card F = c0 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hc0]
    show χ x ^ Fintype.card F = χ x
    rw [← map_pow, FiniteField.pow_card]
  have key : ∀ y z : RC ⧸ Ideal.span {(p : RC)}, (y - z) ^ Fintype.card F = y ^ Fintype.card F - z ^ Fintype.card F := by
    intro y z
    rw [hq]
    exact sub_pow_char_pow y z f
  have hdq : d ^ Fintype.card F - d ∈ Ideal.span {(p : RC)} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hσq ⊢
    rw [map_sub, map_pow] at hσq
    rw [map_sub, map_pow, hd, map_sub, key, ← map_pow, hχq, sub_eq_zero.mp hσq]
    ring
  have hunit : IsUnit (d ^ (Fintype.card F - 1) - 1) := by
    apply isUnit_of_val hv
    have h7 : ((d ^ (Fintype.card F - 1) - 1 : RC) : C) = (d : C) ^ (Fintype.card F - 1) - 1 := by
      push_cast
      rfl
    rw [h7, Valuation.map_sub_eq_of_lt_right, map_one]
    rw [map_one, map_pow]
    exact pow_lt_one₀ zero_le' hvd (by omega)
  obtain ⟨w, hw⟩ := hunit
  have e1 : d ^ Fintype.card F - d = d * (d ^ (Fintype.card F - 1) - 1) := by
    conv_lhs => rw [show Fintype.card F = (Fintype.card F - 1) + 1 by omega]
    ring
  have h8 : d = (d ^ Fintype.card F - d) * ↑w⁻¹ := by
    rw [e1, ← hw, mul_assoc, Units.mul_inv, mul_one]
  rw [h8]
  exact Ideal.mul_mem_right _ _ hdq

theorem gram_cong {E : Type} [Field E] [NumberField E] {R : Type} [CommRing R] {p Rr n : ℕ} [Fact p.Prime] (hRr : 1 ≤ Rr)
    (e : (Fin n → 𝓞 E) →+ (Fin n → 𝓞 E) →+ ZMod (p ^ Rr)) (alt : ∀ x, e x x = 0) (bar : 𝓞 E ≃+* 𝓞 E)
    (hbar : ∀ a, bar (bar a) = a) (hadj : ∀ a x y, e (a • x) y = e x (bar a • y)) (Eg : Matrix (Ix E n) (Ix E n) R)
    (hE : ∀ m m', Eg m m' - ((e (dl m) (dl m')).val : R) ∈ Ideal.span {(p : R)}) {σ' : 𝓞 E →+* R}
    {s : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → R} (hd : IsDualOf σ' s) (x' : Fin n → R) (m : Ix E n) :
    ∑ m', Eg m m' * (s m'.2 * x' m'.1) + σ' (bar (RingOfIntegers.basis E m.2)) * ∑ l, x' l * ∑ k, s k *
      ((e (Pi.single l (RingOfIntegers.basis E k)) (Pi.single m.1 1)).val : R) ∈ Ideal.span {(p : R)} := by
  by_cases hpu : IsUnit (p : R)
  · rw [Ideal.span_singleton_eq_top.mpr hpu]
    trivial
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p hpu
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : NeZero (p ^ Rr) := ⟨pow_ne_zero _ hp0⟩
  let mk := Ideal.Quotient.mk (Ideal.span {(p : R)})
  let φ : ZMod (p ^ Rr) →+* (R ⧸ Ideal.span {(p : R)}) := ZMod.castHom (dvd_pow_self p (by omega)) _
  have hφ : ∀ z : ZMod (p ^ Rr), mk (z.val : R) = φ z := by
    intro z
    show _ = ZMod.cast z
    rw [map_natCast, ZMod.cast_eq_val]
  have hskew : ∀ x y, e x y = - e y x := by
    intro x y
    have h := alt (x + y)
    simp only [map_add (f := _), AddMonoidHom.add_apply, alt x, alt y, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h)
  set B := RingOfIntegers.basis E with hB
  let L : Fin n → 𝓞 E →+ (R ⧸ Ideal.span {(p : R)}) := fun l =>
    φ.toAddMonoidHom.comp ((e.flip (Pi.single m.1 1)).comp (AddMonoidHom.single (fun _ => 𝓞 E) l))
  have hL : ∀ l c, L l c = φ (e (Pi.single l c) (Pi.single m.1 1)) := fun l c => rfl
  have hswap : ∀ l k, φ (e (dl m) (Pi.single l (B k))) = - L l (bar (B m.2) * B k) := by
    intro l k
    rw [hL, hskew, map_neg]
    congr 2
    have h1 : dl m = B m.2 • (Pi.single m.1 1 : Fin n → 𝓞 E) := by
      funext t
      by_cases h : t = m.1 <;> simp [dl, Pi.single_apply, h, hB]
    have h2 : (Pi.single l (bar (B m.2) * B k) : Fin n → 𝓞 E) = bar (B m.2) • (Pi.single l (B k) : Fin n → 𝓞 E) := by
      funext t
      by_cases h : t = l <;> simp [Pi.single_apply, h]
    rw [h1, h2, hadj, hbar]
  have hexp : ∀ l c, L l c = ∑ t, ((B.repr c t : ℤ) : R ⧸ Ideal.span {(p : R)}) * L l (B t) := by
    intro l c
    conv_lhs => rw [← B.sum_repr c]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_zsmul, zsmul_eq_mul]
  have hdual : ∀ l, ∑ k, mk (s k) * L l (bar (B m.2) * B k) = mk (σ' (bar (B m.2))) * ∑ t, mk (s t) * L l (B t) := by
    intro l
    have hx : ∀ k, L l (bar (B m.2) * B k) = ∑ t, ((B.repr (bar (B m.2) * B k) t : ℤ) : R ⧸ Ideal.span {(p : R)}) * L l (B t) :=
      fun k => hexp l _
    simp only [hx, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h3 := congrArg mk (hd.2 (bar (B m.2)) t)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_sum, map_intCast] at h3
    rw [← mul_assoc, h3, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hE' : ∀ m', mk (Eg m m') = φ (e (dl m) (dl m')) := by
    intro m'
    rw [← hφ]
    exact Ideal.Quotient.eq.mpr (hE m m')
  have hfirst : ∀ l, ∑ k, φ (e (dl m) (Pi.single l (B k))) * (mk (s k) * mk (x' l)) =
      - (mk (σ' (bar (B m.2))) * (mk (x' l) * ∑ k, mk (s k) * L l (B k))) := by
    intro l
    simp_rw [hswap l]
    calc ∑ k, -L l (bar (B m.2) * B k) * (mk (s k) * mk (x' l))
        = -(mk (x' l) * ∑ k, mk (s k) * L l (bar (B m.2) * B k)) := by
          rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = _ := by
          rw [hdual l]
          ring
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change mk _ = 0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_mul, hE', hφ]
  rw [Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro l _
  change ∑ k, φ (e (dl m) (Pi.single l (B k))) * (mk (s k) * mk (x' l)) +
    mk (σ' (bar (B m.2))) * (mk (x' l) * ∑ k, mk (s k) * L l (B k)) = 0
  rw [hfirst l]
  exact neg_add_cancel _

section Chart

variable {E : Type} [Field E] [NumberField E] {O Ω C Li : Type} [CommRing O] [Field Ω] [Field C] [Algebra O Ω]
  [Algebra O C] [Algebra Ω C] [AddCommGroup Li] [Module Ω Li] {R : Subalgebra O Ω} {RC : Subalgebra O C}
  {hR : ∀ a ∈ R, algebraMap Ω C a ∈ RC} {cc : E ≃+* E} {p Rr n g : ℕ}
  (Dh : HT.HTChart R Ω cc p Rr n (Module.Dual Ω Li)) (ρ : 𝓞 E →+* Module.End Ω Li) (bar : 𝓞 E ≃+* 𝓞 E)
  (io : Dh.om →ₛₗ[toRC R RC hR] (Fin g → RC)) (ev : Li → ((Fin g → C) →ₗ[C] C))
  (Hm : Matrix (Fin g) (Ix E n) RC)

theorem ev_col (hRr : 1 ≤ Rr) (hact : ∀ a u, Dh.ρΩ a u = u ∘ₗ ρ (bar a))
    (hev : ∀ v (u : Dh.om), ev v (fun k => (io u k : C)) = algebraMap Ω C (u.1 v))
    (hH : ∀ m k, Hm k m - io ⟨Dh.h (dl m), Dh.h_mem _⟩ k ∈ Ideal.span {(p : RC)}) (m : Ix E n) :
    ∃ u : Fin g → RC, ∀ (V : Li) (t : Ω), ρ (bar (RingOfIntegers.basis E m.2)) V = t • V →
      ev V (fun j => (Hm j m : C)) =
        algebraMap Ω C (t * Dh.h (Pi.single m.1 1) V) + (p : C) * ev V fun j => (u j : C) := by
  choose w hw using fun k => Ideal.mem_span_singleton.1 (hH m k)
  obtain ⟨y, hy, hyeq⟩ := Dh.h_lin (RingOfIntegers.basis E m.2) (Pi.single m.1 1)
  refine ⟨fun k => w k + (p : RC) ^ (Rr - 1) * io ⟨y, hy⟩ k, ?_⟩
  intro V t hV
  have hdl : dl m = RingOfIntegers.basis E m.2 • (Pi.single m.1 1 : Fin n → 𝓞 E) := by
    funext j
    by_cases h : j = m.1 <;> simp [dl, Pi.single_apply, h]
  have hvec : (fun j => (Hm j m : C)) =
      (fun j => (io ⟨Dh.h (dl m), Dh.h_mem _⟩ j : C)) + (p : C) • (fun j => (w j : C)) := by
    funext j
    have h1 := congrArg (fun r : RC => (r : C)) (hw j)
    push_cast at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination h1
  have hvec2 : (fun j => ((w j + (p : RC) ^ (Rr - 1) * io ⟨y, hy⟩ j : RC) : C)) =
      (fun j => (w j : C)) + ((p : C) ^ (Rr - 1)) • (fun j => (io ⟨y, hy⟩ j : C)) := by
    funext j
    simp
  have hhV : Dh.h (dl m) V = t * Dh.h (Pi.single m.1 1) V + (p : Ω) ^ Rr * y V := by
    rw [hdl, hyeq]
    simp [hact, hV, nsmul_eq_mul]
  rw [hvec, hvec2, map_add (f := _), map_smul, map_add (f := _), map_smul, hev, hev, smul_eq_mul, smul_eq_mul, hhV]
  have hRr' : (p : C) ^ Rr = p * p ^ (Rr - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  rw [hRr']
  ring

theorem hq_chart (hRr : 1 ≤ Rr) (hact : ∀ a u, Dh.ρΩ a u = u ∘ₗ ρ (bar a))
    (hev : ∀ v (u : Dh.om), ev v (fun k => (io u k : C)) = algebraMap Ω C (u.1 v))
    (hH : ∀ m k, Hm k m - io ⟨Dh.h (dl m), Dh.h_mem _⟩ k ∈ Ideal.span {(p : RC)})
    (σ : E →+* Ω) (σ' : 𝓞 E →+* RC) (hσ : ∀ a, (σ' a : C) = algebraMap Ω C (σ a)) {s : ℕ} (vs : Fin s → Li)
    (hvs : ∀ a k, ρ (bar a) (vs k) = σ a • vs k) (m : Ix E n) :
    ∃ u : Fin g → RC, ∀ k, ev (vs k) (fun j => (Hm j m : C)) -
      TestPt.bcLin C (Fintype.linearCombination Ω fun (i : Fin n) (k : Fin s) => Dh.h (Pi.single i 1) (vs k))
        (fun i => ((Pm n σ' i m : RC) : C)) k = (p : C) * ev (vs k) fun j => (u j : C) := by
  obtain ⟨u, hu⟩ := ev_col Dh ρ bar io ev Hm hRr hact hev hH m
  refine ⟨u, fun k => ?_⟩
  rw [hu _ _ (hvs _ k), bcLin_apply, Finset.sum_eq_single m.1 (fun i _ hi => by simp [Pm, hi.symm]) (by simp)]
  simp [Pm, hσ, mul_comm]

theorem hdual_chart [Fact p.Prime] (hRr : 1 ≤ Rr) (hact : ∀ a u, Dh.ρΩ a u = u ∘ₗ ρ (bar a))
    (hev : ∀ v (u : Dh.om), ev v (fun k => (io u k : C)) = algebraMap Ω C (u.1 v))
    (hH : ∀ m k, Hm k m - io ⟨Dh.h (dl m), Dh.h_mem _⟩ k ∈ Ideal.span {(p : RC)})
    (hbar : ∀ a, bar (bar a) = a) (hadj : ∀ a x y, Dh.e (a • x) y = Dh.e x (bar a • y))
    (Eg : Matrix (Ix E n) (Ix E n) RC)
    (hE : ∀ m m', Eg m m' - ((Dh.e (dl m) (dl m')).val : RC) ∈ Ideal.span {(p : RC)})
    (σ : E →+* Ω) (σ' : 𝓞 E →+* RC) (hσ : ∀ a, (σ' a : C) = algebraMap Ω C (σ a))
    (s : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → RC) (hs : ∀ k, (s k : C) = algebraMap Ω C (σ (HT.dualInt E k)))
    (hd : IsDualOf σ' s) {r : ℕ} (b : Fin r → Li) (hb : ∀ a k, ρ a (b k) = σ a • b k)
    (v : Valuation C NNReal) (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) (w : C) (hw0 : w ≠ 0) (hw1 : v w ≤ 1)
    (hpw : v (p : C) ≤ v w * v w) (a : Fin r → Ω) (x : Fin n → Ω) (hx : ∀ l, x l ∈ R) {M : ℕ} (hM : 1 ≤ M)
    (hseq : ∀ j, ∃ z ∈ R, ∑ l, x l * Dh.gram σ 1 l j = Dh.h (Pi.single j 1) (∑ k, a k • b k) + (p : Ω) ^ M * z)
    (ha : ∀ u : Fin g → RC, ∑ k, (w * algebraMap Ω C (a k)) * ev (b k) (fun j => (u j : C)) ∈ RC) (m : Ix E n) :
    v (∑ m', (Eg m m' : C) * ((Jm n s).map (algebraMap RC C) *ᵥ fun l => algebraMap Ω C (x l)) m' +
      ∑ k, algebraMap Ω C (a k) * ev (b k) fun j => (Hm j m : C)) ≤ v w := by
  set Bj := RingOfIntegers.basis E m.2 with hBj
  let x' : Fin n → RC := fun l => toRC R RC hR ⟨x l, hx l⟩
  have hx' : ∀ l, (x' l : C) = algebraMap Ω C (x l) := fun l => rfl
  have hP1 := gram_cong hRr Dh.e Dh.alt bar hbar hadj Eg hE hd x' m
  obtain ⟨c1, hc1⟩ := Ideal.mem_span_singleton.1 hP1
  obtain ⟨u, hu⟩ := ev_col (Dh := Dh) (ρ := ρ) (bar := bar) (io := io) (ev := ev) (Hm := Hm) hRr hact hev hH m
  obtain ⟨z, hz, hzeq⟩ := hseq m.1
  set t : Ω := σ ((bar Bj : 𝓞 E) : E) with ht
  have hσ' : (σ' (bar Bj) : C) = algebraMap Ω C t := hσ _
  set S : C := ∑ k, algebraMap Ω C (a k) * ev (b k) (fun j => (u j : C)) with hS
  set G : C := ∑ l, algebraMap Ω C (x l) * ∑ k, (s k : C) *
    (((Dh.e (Pi.single l (RingOfIntegers.basis E k))) (Pi.single m.1 1)).val : C) with hGdef
  have hF1 : ∀ m', ((Jm n s).map (algebraMap RC C) *ᵥ fun l => algebraMap Ω C (x l)) m' =
      (s m'.2 : C) * algebraMap Ω C (x m'.1) := by
    intro m'
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Jm]
    rw [Finset.sum_eq_single m'.1]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · simp
  have hc1C : ∑ m', (Eg m m' : C) * ((s m'.2 : C) * algebraMap Ω C (x m'.1)) + (σ' (bar Bj) : C) * G =
      (p : C) * (c1 : C) := by
    have h1 := congrArg (fun r : RC => (r : C)) hc1
    push_cast at h1
    simpa [hx', hGdef] using h1
  have hG : G = algebraMap Ω C (∑ l, x l * Dh.gram σ 1 l m.1) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hGdef, HT.HTChart.gram, map_one, one_mul, map_sum, map_mul, map_natCast, hs]
  have hzC : algebraMap Ω C (∑ l, x l * Dh.gram σ 1 l m.1) =
      algebraMap Ω C (Dh.h (Pi.single m.1 1) (∑ k, a k • b k)) + (p : C) ^ M * algebraMap Ω C z := by
    rw [hzeq, map_add (f := _), map_mul, map_pow, map_natCast]
  have hsec : ∑ k, algebraMap Ω C (a k) * ev (b k) (fun j => (Hm j m : C)) =
      algebraMap Ω C t * algebraMap Ω C (Dh.h (Pi.single m.1 1) (∑ k, a k • b k)) + (p : C) * S := by
    rw [Finset.sum_congr rfl fun k _ => by rw [hu (b k) t (hb _ k)]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hS, map_sum, map_smul, smul_eq_mul, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hT : ∑ m', (Eg m m' : C) * ((Jm n s).map (algebraMap RC C) *ᵥ fun l => algebraMap Ω C (x l)) m' +
      ∑ k, algebraMap Ω C (a k) * ev (b k) (fun j => (Hm j m : C)) =
      (p : C) * (c1 : C) - algebraMap Ω C t * ((p : C) ^ M * algebraMap Ω C z) + (p : C) * S := by
    simp only [hF1]
    rw [hsec]
    linear_combination hc1C - G * hσ' - algebraMap Ω C t * hG - algebraMap Ω C t * hzC
  rw [hT]
  have hvp : v (p : C) ≤ 1 := (hv _).1 (by simpa using (p : RC).2)
  have hvpw : v (p : C) ≤ v w := le_trans hpw (by
    calc v w * v w ≤ v w * 1 := by gcongr
      _ = v w := mul_one _)
  have hvc : v (c1 : C) ≤ 1 := (hv _).1 c1.2
  have hvt : v (algebraMap Ω C t) ≤ 1 := by
    rw [← hσ']
    exact (hv _).1 (σ' (bar Bj)).2
  have hvz : v (algebraMap Ω C z) ≤ 1 := (hv _).1 (hR z hz)
  have hwS : v w * v S ≤ 1 := by
    rw [← map_mul]
    apply (hv _).1
    have h2 := ha u
    convert h2 using 1
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  apply Valuation.map_add_le
  · apply Valuation.map_sub_le
    · rw [map_mul]
      calc v (p : C) * v (c1 : C) ≤ v (p : C) * 1 := by gcongr
        _ ≤ v w := by rw [mul_one]; exact hvpw
    · rw [map_mul, map_mul, map_pow]
      calc v (algebraMap Ω C t) * (v (p : C) ^ M * v (algebraMap Ω C z)) ≤ 1 * (v (p : C) ^ M * 1) := by
            gcongr
        _ = v (p : C) ^ M := by ring
        _ ≤ v (p : C) := pow_le_of_le_one zero_le' hvp (by omega)
        _ ≤ v w := hvpw
  · rw [map_mul]
    calc v (p : C) * v S ≤ (v w * v w) * v S := by gcongr
      _ = v w * (v w * v S) := by ring
      _ ≤ v w * 1 := by gcongr
      _ = v w := mul_one _

end Chart

end PositivityTheory.Xgn.TestGroupPoint
end
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Typed
open GlobalTheory.CompanionTheory.Ar.Num
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

theorem typed {O C : Type} [CommRing O] [Field C] [Algebra O C] (RC : Subalgebra O C) (v : Valuation C NNReal)
    (hv : ∀ c, c ∈ RC ↔ v c ≤ 1) (p w : C) (hw0 : w ≠ 0) (hw1 : v w < 1) (hpw : v p ≤ v w * v w) (c P : RC)
    (hc : v (c : C) = v w) (hP : (P : C) = p)
    {I : Type} [Fintype I] [DecidableEq I] {g n r s : ℕ} (AF : Submodule RC (I → RC))
    (Hm : Matrix (Fin g) I RC) (Eg Ei : Matrix I I RC) (hEi : Ei * Eg = 1)
    (h0 : ∀ l, c • l ∈ AF) (h1 : ∀ k, Hm k ∈ AF) (h2 : ∀ y, y ᵥ* Eg ∈ AF → ∃ u, Hm *ᵥ y = c • u)
    (h3 : ∀ u : Fin g → RC, ∃ (y : I → RC) (u' : Fin g → RC), y ᵥ* Eg ∈ AF ∧ Hm *ᵥ y = c • u + P • u')
    (h4 : ∀ u : Fin g → RC, ∃ x : I → C, (∀ l ∈ AF, v (∑ j, algebraMap RC C (l j) * x j) ≤ 1) ∧
      Hm.map (algebraMap RC C) *ᵥ x = fun k => algebraMap RC C (u k))
    (Pm : Matrix (Fin n) I RC) (Jm : Matrix I (Fin n) RC) (hPJ : Pm * Jm = 1)
    (hst : ∀ l ∈ AF, l ᵥ* (Jm * Pm) ∈ AF) (hh : AddSubgroup (Fin n → C))
    (hhh : ∀ u, u ∈ hh ↔ ∀ l ∈ AF, (∑ j, (l j : C) * (Jm.map (algebraMap RC C)).mulVec u j) ∈ RC)
    (evs : Fin s → ((Fin g → C) →ₗ[C] C)) (evr : Fin r → ((Fin g → C) →ₗ[C] C))
    (om : AddSubgroup (Fin s → C)) (lie W : AddSubgroup (Fin r → C))
    (hom : ∀ z, z ∈ om ↔ ∃ u : Fin g → RC, ∀ k, z k = evs k fun j => (u j : C))
    (hlie : ∀ a, a ∈ lie ↔ ∀ u : Fin g → RC, ∑ k, a k * evr k (fun j => (u j : C)) ∈ RC)
    (hlW : lie ≤ W) (hWl : ∀ a ∈ W, w • a ∈ lie)
    (q : (Fin n → C) →ₗ[C] (Fin s → C))
    (hq : ∀ m, ∃ u : Fin g → RC, ∀ k,
      evs k (fun j => (Hm j m : C)) - q (fun i => (Pm i m : C)) k = p * evs k fun j => (u j : C))
    (i' hb : (Fin r → C) →ₗ[C] (Fin n → C))
    (hdual : ∀ a ∈ W, ∀ m, v (∑ m', (Eg m m' : C) * (Jm.map (algebraMap RC C) *ᵥ i' a) m' +
      ∑ k, a k * evr k fun j => (Hm j m : C)) ≤ v w)
    (hW : (stdLat RC _).comap hb.toAddMonoidHom = W) (hcl : ∀ a ∈ W, hb a - i' a ∈ mulLat w (stdLat RC _)) :
    hh.map q.toAddMonoidHom = om ∧ hh.comap hb.toAddMonoidHom = divLat w lie := by
  have hvw : v w ≠ 0 := (Valuation.ne_zero_iff v).2 hw0
  have hvw' : 0 < v w := pos_iff_ne_zero.2 hvw
  have hle : ∀ a : RC, v (a : C) ≤ 1 := fun a => (hv _).1 a.2
  have htw : v (p / w) ≤ v w := by rw [map_div₀, div_le_iff₀ hvw']; exact hpw
  let t : RC := ⟨p / w, (hv _).2 (htw.trans hw1.le)⟩
  have hint : ∀ x : I → C, (∀ l ∈ AF, v (∑ j, (l j : C) * x j) ≤ 1) → ∀ m, w * x m ∈ RC := fun x hx m => by
    have := hx _ (h0 (Pi.single m 1))
    rw [Finset.sum_eq_single m (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)] at this
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, map_mul, hc] at this
    rw [hv, map_mul]
    exact this
  have hev : ∀ (f : (Fin g → C) →ₗ[C] C) (x : I → C),
      f (Hm.map (algebraMap RC C) *ᵥ x) = ∑ m, x m * f fun j => (Hm j m : C) := fun f x => by
    have : Hm.map (algebraMap RC C) *ᵥ x = ∑ m, x m • fun j => (Hm j m : C) := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.map_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]
    simp only [map_smul, smul_eq_mul]
  have key : ∀ x : I → C, (∀ m, w * x m ∈ RC) → ∃ u : Fin g → RC, ∀ k,
      q (Pm.map (algebraMap RC C) *ᵥ x) k = evs k (Hm.map (algebraMap RC C) *ᵥ x) - (t : C) * evs k fun j => (u j : C) := by
    intro x hx
    choose U hU using hq
    refine ⟨∑ m, (⟨_, hx m⟩ : RC) • U m, fun k => ?_⟩
    have e1 : Pm.map (algebraMap RC C) *ᵥ x = ∑ m, x m • fun i => (Pm i m : C) := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.map_apply]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have e2 : (fun j => (((∑ m, (⟨_, hx m⟩ : RC) • U m) j : RC) : C)) = ∑ m, (w * x m) • fun j => (U m j : C) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hev, e1, e2, map_sum, map_sum, Finset.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    have e3 : (t : C) * w = p := div_mul_cancel₀ p hw0
    linear_combination (-x m) * hU m k + (x m * evs k fun j => (U m j : C)) * e3
  have hPJ' : ∀ u : Fin n → C, Pm.map (algebraMap RC C) *ᵥ (Jm.map (algebraMap RC C) *ᵥ u) = u := fun u => by
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hPJ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  have hdot : ∀ {K : Type} [Fintype K] (l : I → RC) (M : Matrix I K RC) (x : K → C),
      ∑ j, (l j : C) * (M.map (algebraMap RC C) *ᵥ x) j = ∑ j, ((l ᵥ* M) j : C) * x j := fun l M x => by
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul,
      Finset.mul_sum, Finset.sum_mul, Matrix.map_apply, mul_assoc]
    exact Finset.sum_comm
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · rintro _ ⟨u₀, hu₀, rfl⟩
    have hu := (hhh u₀).1 hu₀
    obtain ⟨u, e⟩ := key _ (hint _ fun l hl => (hv _).1 (hu l hl))
    rw [hPJ'] at e
    refine (hom _).2 ⟨(fun j => ⟨_, hu _ (h1 j)⟩) - t • u, fun k => (e k).trans ?_⟩
    rw [← smul_eq_mul, ← map_smul, ← map_sub]
    rfl
  · let N : Submodule RC (Fin g → RC) :=
      { carrier := {u | ∃ x ∈ hh, ∀ k, q x k = evs k fun j => (u j : C)}
        add_mem' := by
          rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
          refine ⟨x + y, hh.add_mem hx hy, fun k => ?_⟩
          rw [map_add (f := _), Pi.add_apply, ha, hb, ← map_add (f := _)]
          rfl
        zero_mem' := ⟨0, hh.zero_mem, fun k => by rw [map_zero]; exact (map_zero (evs k)).symm⟩
        smul_mem' := by
          rintro a b ⟨x, hx, hb⟩
          refine ⟨(a : C) • x, (hhh _).2 fun l hl => ?_, fun k => ?_⟩
          · convert RC.mul_mem a.2 ((hhh _).1 hx l hl) using 1
            simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]
          · rw [map_smul, Pi.smul_apply, hb, ← map_smul]
            rfl }
    have hjac : Ideal.span {t} ≤ (⊥ : Ideal RC).jacobson := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_jacobson_bot]
      intro y
      have h1 : v ((t * y + 1 : RC) : C) = 1 := by
        rw [add_comm]
        refine v.map_one_add_of_lt ?_
        change v ((t : C) * y) < 1
        rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (htw.trans_lt hw1) (hle y)
      have h0 : ((t * y + 1 : RC) : C) ≠ 0 := fun h => by rw [h, map_zero] at h1; exact zero_ne_one h1
      refine IsUnit.of_mul_eq_one ⟨((t * y + 1 : RC) : C)⁻¹, (hv _).2 (by rw [map_inv₀, h1, inv_one])⟩ ?_
      exact Subtype.ext (mul_inv_cancel₀ h0)
    have hN : (⊤ : Submodule RC (Fin g → RC)) ≤ N := by
      refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hjac fun u _ => ?_
      obtain ⟨x, hx, hxu⟩ := h4 u
      obtain ⟨u', e⟩ := key x (hint x hx)
      refine Submodule.mem_sup.2 ⟨u - t • u', ⟨Pm.map (algebraMap RC C) *ᵥ x, (hhh _).2 fun l hl => ?_, fun k => ?_⟩,
        t • u', Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) Submodule.mem_top, sub_add_cancel _ _⟩
      · rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hdot]
        exact (hv _).2 (hx _ (hst l hl))
      · rw [e, hxu, ← smul_eq_mul, ← map_smul, ← map_sub]
        rfl
    intro z hz
    obtain ⟨u, hu⟩ := (hom z).1 hz
    obtain ⟨x, hx, e⟩ := hN (Submodule.mem_top (x := u))
    exact ⟨x, hx, funext fun k => (e k).trans (hu k).symm⟩
  · have est : ∀ a : Fin r → C, w • a ∈ W → ∀ y : I → RC,
        (∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ hb a) j ∈ RC ↔
          v (∑ k, (w • a) k * evr k fun j => ((Hm *ᵥ y) j : C)) ≤ v w) := by
      intro a ha y
      obtain ⟨z, hz, e⟩ := hcl _ ha
      have hz' : ∀ k, z k ∈ RC := fun k => hz k (Set.mem_univ k)
      have e1 : w • hb a = i' (w • a) + w • z := by
        rw [← map_smul hb, ← sub_eq_iff_eq_add', ← e]; rfl
      have e2 : w * ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ hb a) j =
          ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) j +
            w * ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ z) j := by
        have := congrArg (fun x => ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ x) j) e1
        simpa only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
          Finset.sum_add_distrib, mul_left_comm _ w, ← Finset.mul_sum] using this
      have e3 : v (w * ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ z) j) ≤ v w := by
        rw [map_mul]
        refine mul_le_of_le_one_right zero_le ((hv _).1 ?_)
        rw [hdot]
        exact RC.sum_mem fun j _ => RC.mul_mem (Subtype.prop _) (hz' j)
      have e4 : ∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) j +
          ∑ k, (w • a) k * evr k (fun j => ((Hm *ᵥ y) j : C)) =
          ∑ m, (y m : C) * (∑ m', (Eg m m' : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) m' +
            ∑ k, (w • a) k * evr k fun j => (Hm j m : C)) := by
        have : (fun j => ((Hm *ᵥ y) j : C)) = Hm.map (algebraMap RC C) *ᵥ fun m => (y m : C) := by
          funext j
          simp only [Matrix.mulVec, dotProduct, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, Matrix.map_apply]
          rfl
        rw [this, ← hdot]
        simp only [hev, mul_add, Finset.sum_add_distrib]
        congr 1
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        simp only [mul_left_comm]
      have e5 : v (∑ j, ((y ᵥ* Eg) j : C) * (Jm.map (algebraMap RC C) *ᵥ i' (w • a)) j +
          ∑ k, (w • a) k * evr k (fun j => ((Hm *ᵥ y) j : C))) ≤ v w := by
        rw [e4]
        refine v.map_sum_le fun m _ => ?_
        rw [map_mul]
        exact (mul_le_of_le_one_left zero_le (hle _)).trans (hdual _ ha m)
      have e6 := v.map_add_le e5 e3
      rw [add_right_comm, ← e2] at e6
      rw [hv, ← mul_le_mul_iff_right₀ hvw', mul_one, ← map_mul]
      constructor
      · intro h
        simpa using v.map_sub_le e6 h
      · intro h
        simpa using v.map_sub_le e6 h
    have hlin : ∀ (a : Fin r → C) (b : RC) (u : Fin g → RC), ∑ k, a k * evr k (fun j => ((b • u) j : C)) =
        (b : C) * ∑ k, a k * evr k (fun j => (u j : C)) := fun a b u => by
      have : (fun j => ((b • u) j : C)) = (b : C) • fun j => (u j : C) := rfl
      simp only [this, map_smul, smul_eq_mul, Finset.mul_sum, mul_left_comm]
    ext a
    change hb a ∈ hh ↔ w • a ∈ lie
    rw [hhh]
    constructor
    · intro h
      have ha : w • a ∈ W := by
        rw [← hW]
        intro k _
        have h5 := (hv _).1 (h _ (h0 (Pm k)))
        have h6 : ∑ j, ((c • Pm k) j : C) * (Jm.map (algebraMap RC C) *ᵥ hb a) j = (c : C) * hb a k := by
          conv_rhs => rw [← hPJ' (hb a)]
          generalize Jm.map (algebraMap RC C) *ᵥ hb a = x
          simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, MulMemClass.coe_mul, Finset.mul_sum,
            mul_assoc, Matrix.map_apply]
          rfl
        rw [h6, map_mul, hc, ← map_mul] at h5
        change hb (w • a) k ∈ RC
        rw [map_smul]
        exact (hv _).2 h5
      refine (hlie _).2 fun u => ?_
      obtain ⟨y, u', hy, e⟩ := h3 u
      have h5 := (est a ha y).1 (h _ hy)
      have h6 : ∑ k, (w • a) k * evr k (fun j => ((Hm *ᵥ y) j : C)) =
          (c : C) * ∑ k, (w • a) k * evr k (fun j => (u j : C)) +
            (p / w) * ∑ k, (w • w • a) k * evr k (fun j => (u' j : C)) := by
        have : (fun j => ((c • u + P • u') j : C)) = (fun j => ((c • u) j : C)) + fun j => ((P • u') j : C) := rfl
        rw [e, this]
        simp only [map_add (f := _), mul_add, Finset.sum_add_distrib, hlin, hP]
        congr 1
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc w, ← Finset.mul_sum]
        field_simp
      have h7 : v ((p / w) * ∑ k, (w • w • a) k * evr k (fun j => (u' j : C))) ≤ v w := by
        rw [map_mul]
        exact (mul_le_of_le_one_right zero_le ((hv _).1 ((hlie _).1 (hWl _ ha) u'))).trans htw
      rw [h6] at h5
      have h8 := v.map_sub_le h5 h7
      rw [add_sub_cancel_right, map_mul, hc] at h8
      rw [hv]
      exact (mul_le_iff_le_one_right hvw').1 h8
    · intro h l hl
      have hl' : (l ᵥ* Ei) ᵥ* Eg = l := by rw [Matrix.vecMul_vecMul, hEi, Matrix.vecMul_one]
      rw [← hl'] at hl ⊢
      obtain ⟨u, e⟩ := h2 _ hl
      rw [est a (hlW h), e, hlin, map_mul, hc]
      exact mul_le_of_le_one_right zero_le ((hv _).1 ((hlie _).1 h u))

end PositivityTheory.Xgn.TestGroupPoint
end
end

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TestGroupPoint

theorem spanOver_ind {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o C] [Algebra Ω C] (RC : Subalgebra o C)
    {r : ℕ} (L : AddSubgroup (Fin r → Ω)) (T : AddSubgroup (Fin r → C)) (hT : ∀ t ∈ RC, ∀ a ∈ T, t • a ∈ T)
    (h : ∀ a ∈ L, (fun k => algebraMap Ω C (a k)) ∈ T) : spanOver RC (bcMap Ω C _ '' L) ≤ T := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨t, ht, _, ⟨a, ha, rfl⟩, rfl⟩
  exact hT t ht _ (h a ha)

theorem mem_spanOver {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o C] [Algebra Ω C] (RC : Subalgebra o C)
    {r : ℕ} (L : AddSubgroup (Fin r → Ω)) {a : Fin r → Ω} (ha : a ∈ L) :
    (fun k => algebraMap Ω C (a k)) ∈ spanOver RC (bcMap Ω C _ '' L) :=
  AddSubgroup.subset_closure ⟨1, RC.one_mem, _, ⟨a, ha, rfl⟩, (one_smul _ _).symm⟩

def smallSub {C : Type} [Field C] (v : Valuation C NNReal) (t : NNReal) {r : ℕ} {I : Type}
    (f : I → ((Fin r → C) →ₗ[C] C)) : AddSubgroup (Fin r → C) where
  carrier := {a | ∀ m, v (f m a) ≤ t}
  add_mem' ha hb m := by rw [map_add (f := _)]; exact v.map_add_le (ha m) (hb m)
  zero_mem' m := by simp
  neg_mem' ha m := by rw [map_neg, Valuation.map_neg]; exact ha m

theorem bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a :=
  RingOfIntegers.ext (by rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply])

end PositivityTheory.Xgn.TestGroupPoint

open PositivityTheory.Xgn.TestGroupPoint PositivityTheory.HtPt.Sgp in
theorem PositivityTheory.Xgn.test_group_point_exists : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → ∀ τ (hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C))), Function.Injective hb → LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) → (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ → (∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _)) → (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).om τ ∧ (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).comap hb.toAddMonoidHom = divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ) := by
  intro hF _ _ hHD hOC E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hd hpq p _ hpS hfree hp2 hdisc b hb φ hφ A _ _ _ m _
    hpm O _ _ _ _ _ _ _ t₀ Sg _ e φ' F _ _ _ pq sc w σF hO hsec G c' hc' P i hseq hbase C _ _ _ _ RC hT χ hχ _ _ _ v hv hvp
    τ hbm _ _ hW hcl
  have hpp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  haveI : NeZero (p ^ 𝔐.R p) := ⟨pow_ne_zero _ hpp.ne_zero⟩
  have hR4 := 𝔐.R_ge p hpS
  obtain ⟨h0, hNoe, hIC, hFr⟩ := Par.chart_facts E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd p hpS A m hpm O c' hc'
  obtain ⟨-, hN, -⟩ := GlobalTheory.T.hodge_tate_free_integral_models E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS (Par.zp Ω p) (Par.mem_range_zp Ω p)
  obtain ⟨AA, AW, hAA, hAW, hM, hret, -⟩ := PositivityTheory.Xgn.test_order_sections E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p
    hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σF hO hsec G c' hc' P i hseq hbase C RC hT χ hχ
  obtain ⟨-, htight⟩ := GlobalTheory.T.arith_variety_model_hodge_relay hHD hOC E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p
    hpS hfree hp2 hdisc b hb φ hφ A m hpm O t₀ Sg e φ' F pq sc w σF hO hsec G c' hc' P i hseq hbase C RC hT χ hχ v hv hvp
  obtain ⟨g, io, ev, Hm, Eg, hio, hev, hcard, hEt, ⟨Ei, hEi, hiso⟩, hE, hH⟩ :=
    point_data hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p hpS A m hpm O G c' hc' P C RC w hO.2.2.2.2.2.2.2 hT
  obtain ⟨Dv, hD, hDs, hDch⟩ := exists_der hpS P hT.2.2.2 io
  have hlat := fun t => lattices E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p hpS A m hpm O G c' hc' P C RC hdisc
    hT.2.2.2 io ev hio hev t (b t) (hb t).1 (hb t).2
  haveI := hT.1
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap Ω C).injective
  have hint : v.Integers RC := ⟨Subtype.val_injective, fun x => (hv _).1 x.2, fun r hr => ⟨⟨r, (hv _).2 hr⟩, rfl⟩⟩
  obtain ⟨φN, hφN⟩ := exists_phiN E (D.p + D.q) p
  have hζ : IsPrimitiveRoot (algebraMap Ω C (G.ζ ^ p ^ (𝔐.R p - 1))) p :=
    (G.ζ_prim.pow (pow_pos hpp.pos _) (by rw [← pow_succ, Nat.sub_add_cancel (by omega)])).map_of_injective
      (algebraMap Ω C).injective
  let ih : (Fin (D.p + D.q) → 𝓞 E) →+ (Fin g → RC) := io.toAddMonoidHom.comp (P.Dh.h.codRestrict P.Dh.om P.Dh.h_mem)
  obtain ⟨cp, hcp, k0, k1, k2, k3, k4⟩ := core_pull hint hvp hp2 φN hφN AA _ hAA htight hcard
    (dvd_pow_self p (show 𝔐.R p ≠ 0 by omega)) G.e hζ (kernel_mem hpS P hT) Dv hD (Set.range io) hio
    (by rintro _ ⟨u, rfl⟩; exact hDs u) ih hDch Hm Eg Ei hEt hEi hiso hE hH
  obtain ⟨σ, hσ, hσs, -⟩ := PositivityTheory.Xgn.exists_cm_type_embedding E H D l Xo c O₀ β Y S Ω K J y 𝔐 (e τ)
  obtain ⟨hσO, x₀, hx₀, o₀, ho₀⟩ := PositivityTheory.Xgn.SequenceDifferentials.main E Ω p hdisc A m hpm O σ
  have hOC' : ∀ o : O, algebraMap Ω C (algebraMap O Ω o) = algebraMap O C o := fun o =>
    (IsScalarTower.algebraMap_apply O Ω C o).symm
  obtain ⟨σ', s, hσ', hs, hdu⟩ := exists_dualOf (R := RC) (C := C) Subtype.val_injective ((algebraMap Ω C).comp σ)
    (fun a => by
      obtain ⟨o, ho⟩ := hσO a
      exact ⟨algebraMap O RC o, by rw [RingHom.comp_apply, ← ho, hOC']; rfl⟩)
    (fun k => by
      obtain ⟨z, hz⟩ := HT.exists_different_mul_dualInt E x₀ hx₀ k
      obtain ⟨o, ho⟩ := hσO z
      refine ⟨algebraMap O RC (o₀ * o), ?_⟩
      have : algebraMap O Ω (o₀ * o) = σ (HT.dualInt E k) := by
        rw [map_mul, ho, hz, map_mul, ← _root_.mul_assoc, ho₀, _root_.one_mul]
      rw [RingHom.comp_apply, ← this, hOC']; rfl)
  obtain ⟨χ', hχ', hcong⟩ := chi_cong p RC v hv pq sc hsec (σF τ) (χ τ) (hχ τ) σ' fun a => by
    obtain ⟨o, ho, ho'⟩ := hO.2.2.2.2.1 τ a
    exact ⟨o, by rw [← hOC', ho, ← hσ]; exact (hσ' a).symm, ho'⟩
  have hst := afLat_stable hdu φN hφN AA.carrier (fun a f hf => by rw [hAA] at hf ⊢; exact act_mem P a f hf) _
    (mem_pull φN AA)
  have hhh := (pt_af_type_main RC p (ReciprocityTheory.PGsh.Up.hopfPull φN AA).carrier (ReciprocityTheory.PGsh.Up.hopfPull φN AA).le_int
    ((chartD e b pq sc w P i).bc RC) χ' (Subtype.ext (by rw [← hχ', map_zero]; rfl))
    (Subtype.ext (by rw [← hχ', map_one]; rfl))
    (φN.symm.toAddMonoidHom.comp (TestPt.toNAdd sc)) ((TestPt.fromNAdd pq).comp φN.toAddMonoidHom)
    (fun z => by
      change TestPt.fromNAdd pq (φN (φN.symm (TestPt.toNAdd sc z))) = z
      rw [AddEquiv.apply_symm_apply]
      exact funext fun k => hsec.1 (z k))
    (fun h hh => by
      obtain ⟨f, hf, rfl⟩ := (mem_pull φN AA h).1 hh
      refine (mem_pull φN AA _).2 ⟨_, hret f hf, funext fun x => ?_⟩
      change _ = f (φN (φN.symm _))
      rw [AddEquiv.apply_symm_apply]
      rfl)
    (by
      rw [← hM, hAW, TestPt.testOrdW, ← hAA]
      congr 1
      ext f
      constructor
      · rintro ⟨h, hh, rfl⟩
        obtain ⟨f, hf, rfl⟩ := (mem_pull φN AA h).1 hh
        refine ⟨f, hf, funext fun x => ?_⟩
        change _ = f (φN (φN.symm _))
        rw [AddEquiv.apply_symm_apply]
        rfl
      · rintro ⟨f, hf, rfl⟩
        refine ⟨_, (mem_pull φN AA _).2 ⟨f, hf, rfl⟩, funext fun x => ?_⟩
        change f (φN (φN.symm _)) = _
        rw [AddEquiv.apply_symm_apply]
        rfl)
    (Pm _ σ') (Jm _ s) (Pm_mul_Jm hdu) (Pm_cong pq φN hφN χ' hcong) hst).2
  simp only [← hχ'] at hhh
  obtain ⟨u, hu, hwu⟩ := hO.2.2.2.2.2.2.1.2.1
  have hp3 : 2 ≤ p - 1 := by have := hpp.two_le; omega
  have hvw : v (algebraMap O C w) ^ (p - 1) = v (p : C) := by
    rw [← map_pow, ← map_pow, hwu, map_mul, map_mul, map_natCast,
      show v (algebraMap O C u) = 1 from hint.one_of_isUnit (hu.map (algebraMap O RC)), _root_.one_mul]
  have hw1 : v (algebraMap O C w) < 1 := lt_of_not_ge fun h => absurd (hvw ▸ one_le_pow₀ h) (not_le.2 hvp)
  have hw0 : algebraMap O C w ≠ 0 := fun h => by
    rw [h, map_zero, zero_pow (by omega), eq_comm, Valuation.zero_iff] at hvw
    exact Nat.cast_ne_zero.2 hpp.ne_zero hvw
  have hpw : v (p : C) ≤ v (algebraMap O C w) * v (algebraMap O C w) := by
    rw [← hvw, ← sq]
    exact pow_le_pow_of_le_one zero_le hw1.le hp3
  have hWl : ∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, algebraMap O C w • a ∈ ((chartD e b pq sc w P i).bc RC).lie τ :=
    fun a ha => spanOver_ind RC _ (divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ))
      (fun t ht a ha => by
        simp only [divLat, AddSubgroup.mem_comap, DistribSMul.toAddMonoidHom_apply] at ha ⊢
        rw [smul_comm]
        exact smul_mem_spanOver RC _ ht ha)
      (fun a ha => by
        have h1 : algebraMap O Ω w • a ∈ (chartD e b pq sc w P i).lie τ := (hbase.incl τ).2.1 ha
        have h2 := mem_spanOver RC _ h1
        have e : algebraMap O C w • (fun k => algebraMap Ω C (a k)) =
            fun k => algebraMap Ω C ((algebraMap O Ω w • a) k) := by
          funext k
          change _ = algebraMap Ω C (algebraMap O Ω w * a k)
          rw [map_mul, hOC']
          rfl
        simp only [divLat, AddSubgroup.mem_comap, DistribSMul.toAddMonoidHom_apply]
        rw [e]
        exact h2) ha
  have heig : ∀ t a k, 𝔐.ρ a (b t k) = 𝔐.emb t a • b t k := fun t a k => by
    have : b t k ∈ 𝔐.Vgen t := (hb t).2 ▸ Submodule.subset_span ⟨k, rfl⟩
    simp only [HodgeCpt.Vgen, GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      sub_eq_zero] at this
    exact this a
  refine typed RC v hv (p : C) (algebraMap O C w) hw0 hw1 hpw cp (p : RC)
    ((pow_left_inj₀ zero_le zero_le (by omega)).1 (hcp.trans hvw.symm)) (SubringClass.coe_natCast _ _) _ Hm Eg Ei hEi
    k0 k1 k2 k3 k4 (Pm _ σ') (Jm _ s) (Pm_mul_Jm hdu) hst _ hhh (fun k => ev (b (e τ).swap k)) (fun k => ev (b (e τ) k))
    _ _ _ (hlat (e τ).swap).1 (hlat (e τ)).2
    (spanOver_ind RC _ _ (fun t ht a ha => smul_mem_spanOver RC _ ht ha) fun a ha =>
      mem_spanOver RC _ ((hbase.incl τ).1 ha)) hWl _
    (hq_chart P.Dh 𝔐.ρ H.bar io ev Hm (by omega) P.Dh_act hev hH σ σ' hσ' (b (e τ).swap) fun a k => ?_)
    (TestPt.bcLin C (i τ)) hbm (fun a ha => ?_) hW hcl
  · rw [heig, ← hσs, H.bar_eq, RingHom.comp_apply]
    congr 2
    first
      | exact IsCMField.complexConj_apply_apply E _
      | simp [HT.cmConj]
  · let f : Ix E (D.p + D.q) → ((Fin (labelRk D (e τ)) → C) →ₗ[C] C) := fun m =>
      ∑ m', (Eg m m' : C) • (LinearMap.proj m' ∘ₗ ((Jm _ s).map (algebraMap RC C)).mulVecLin ∘ₗ TestPt.bcLin C (i τ)) +
        ∑ k, ev (b (e τ) k) (fun j => (Hm j m : C)) • LinearMap.proj k
    have hf : ∀ m a, f m a = ∑ m', (Eg m m' : C) * ((Jm _ s).map (algebraMap RC C)).mulVec (TestPt.bcLin C (i τ) a) m' +
        ∑ k, a k * ev (b (e τ) k) fun j => (Hm j m : C) := fun m a => by
      simp only [f, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
        LinearMap.proj_apply, Matrix.mulVecLin_apply, smul_eq_mul, mul_comm (a _)]
    intro m
    rw [← hf]
    refine spanOver_ind RC _ (smallSub v (v (algebraMap O C w)) f) (fun t ht a ha m => ?_) (fun a ha m => ?_) ha m
    · rw [map_smul, smul_eq_mul, map_mul]
      exact (mul_le_of_le_one_left zero_le ((hv _).1 ht)).trans (ha m)
    · rw [hf, show TestPt.bcLin C (i τ) (fun k => algebraMap Ω C (a k)) = fun l => algebraMap Ω C (i τ a l) from
        funext (bcLin_bc _ _)]
      exact hdual_chart P.Dh 𝔐.ρ H.bar io ev Hm (by omega) P.Dh_act hev hH (bar_bar H)
        (by rw [P.Dh_e]; exact G.adj) Eg (by rw [P.Dh_e]; exact hE) σ σ' hσ' s hs hdu (b (e τ))
        (fun a k => by rw [heig, hσ]) v hv _ hw0 hw1.le hpw a (i τ a)
        (fun l => (hseq τ).1.1 a ha l (Set.mem_univ l)) (M := 𝔐.R p - 2) (by omega) ((hseq τ).2 σ hσ a ha)
        ((hlat (e τ)).2 _ |>.1 (hWl _ (mem_spanOver RC _ ha))) m
