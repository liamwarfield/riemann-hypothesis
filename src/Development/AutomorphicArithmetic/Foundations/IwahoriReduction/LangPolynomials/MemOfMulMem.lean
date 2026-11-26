module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.NormOfDvd
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.SerMulPow
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.RepFrob
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.Period
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DivEqZeroOfCg
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.HtvExpand
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.NormSubLeOne

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.RepAdd
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem nat_le_one' {l : ℕ} [Fact l.Prime] (a : ℕ) : ‖(a : Qbar l)‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one (PadicAlgCl l) a

private theorem dd_mul_eq_dd_mul_add_mul_dd {R : Type} [CommRing R] (f g : PowerSeries R) :
    dd (f * g) = dd f * g + f * dd g := by
  simp [dd]; ring

private theorem dl_mul_eq_add_of_isUnit {R : Type} [CommRing R] {f g : PowerSeries R}
    (hf : IsUnit f) (hg : IsUnit g) : dl (f * g) = dl f + dl g := by
  obtain ⟨u, rfl⟩ := hf
  obtain ⟨v, rfl⟩ := hg
  simp only [dl, ← Units.val_mul, Ring.inverse_unit]
  simp only [Units.val_mul, mul_inv_rev, dd_mul_eq_dd_mul_add_mul_dd]
  have h1 : (u : PowerSeries R) * ↑u⁻¹ = 1 := u.mul_inv
  have h2 : (v : PowerSeries R) * ↑v⁻¹ = 1 := v.mul_inv
  linear_combination (dd (u : PowerSeries R) * ↑u⁻¹) * h2 + (dd (v : PowerSeries R) * ↑v⁻¹) * h1

theorem UpperTheory.Kd.C7.pRepAdd :
    UpperTheory.Kd.C7.SRepAdd := by
  intro l _ hl Ω _ _ _ A hA j Φ c β ζ hζ
  have hB := (pBasEx l c).2 β
  have hpv : ∀ (P Q : Polynomial (R0 A)) (z : Ω), pv (P * Q) z = pv P z * pv Q z := by
    intro P Q z; simp [pv, Polynomial.eval₂_mul]
  refine ⟨?_, ?_⟩
  · rintro Z Z' D D' ⟨c₁, m₁, h₁⟩ ⟨c₂, m₂, h₂⟩
    refine ⟨max c₁ c₂, max (max m₁ m₂) 1, fun m hm => ?_⟩
    have hm₁ : m₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
    have hm₂ : m₂ ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
    have hm0 : 1 ≤ m := le_trans (le_max_right _ _) hm
    have hc₁ : m - max c₁ c₂ ≤ m - c₁ := Nat.sub_le_sub_left (le_max_left _ _) m
    have hc₂ : m - max c₁ c₂ ≤ m - c₂ := Nat.sub_le_sub_left (le_max_right _ _) m
    obtain ⟨P, hP, hPL⟩ := h₁ m hm₁
    obtain ⟨P', hP', hPL'⟩ := h₂ m hm₂
    have hQ := pPresMono l hl Ω A hA c β ζ hζ Z Z m (m - c₁) (m - max c₁ c₂) P hc₁
      (fun s _ => by simp [Cg]) hP
    have hQ' := pPresMono l hl Ω A hA c β ζ hζ Z' Z' m (m - c₂) (m - max c₁ c₂) P' hc₂
      (fun s _ => by simp [Cg]) hP'
    unfold UpperTheory.Kd.C7.BPres GlobalTheory.Col.KumPres at hQ hQ'
    obtain ⟨hprim, hnr, hu, ho, hk⟩ := hQ
    obtain ⟨-, -, hu', -, hk'⟩ := hQ'
    refine ⟨fun i => P i * P' i, ?_, fun i => ?_⟩
    · unfold UpperTheory.Kd.C7.BPres GlobalTheory.Col.KumPres
      refine ⟨hprim, hnr, fun i => ?_, ho, fun s hs hcyc hsζ => ?_⟩
      · dsimp only
        rw [hpv]
        obtain ⟨a₁, a₂, a₃⟩ := hu i
        obtain ⟨b₁, b₂, b₃⟩ := hu' i
        dsimp only at a₁ a₂ a₃ b₁ b₂ b₃
        exact ⟨mul_mem a₁ b₁, mul_ne_zero a₂ b₂, by rw [mul_inv]; exact mul_mem a₃ b₃⟩
      · obtain ⟨k, hkv, hkc⟩ := hk s hs hcyc hsζ
        obtain ⟨k', hkv', hkc'⟩ := hk' s hs hcyc hsζ
        have hsH : s ∈ Hm l A m := Subgroup.mem_inf.mpr ⟨hs, MonoidHom.mem_ker.mpr hcyc⟩
        have halg := (pKumAlg l hl Ω A hA ζ hζ m (m - max c₁ c₂) (Nat.sub_le _ _) s hsH).1
        refine ⟨k + k', fun i => ?_, ?_⟩
        · dsimp only
          rw [hpv]
          exact (halg _ _ _ _ (hkv i) (hkv' i)).1
        · have hNz : NeZero (l ^ (m - max c₁ c₂)) :=
            ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
          have key : ∀ i, (((k + k') i).val : Qbar l) = (k i).val + (k' i).val
              - (l : Qbar l) ^ (m - max c₁ c₂)
                * ((((k i).val + (k' i).val) / l ^ (m - max c₁ c₂) : ℕ) : Qbar l) := by
            intro i
            rw [Pi.add_apply, ZMod.val_add, eq_sub_iff_add_eq]
            exact_mod_cast Nat.mod_add_div ((k i).val + (k' i).val) (l ^ (m - max c₁ c₂))
          unfold Cg at hkc hkc' ⊢
          dsimp only
          have hsplit : Z m s 1 + Z' m s 1 - ∑ i, β.val i * (((k + k') i).val : Qbar l)
              = (Z m s 1 - ∑ i, β.val i * ((k i).val : Qbar l))
                + (Z' m s 1 - ∑ i, β.val i * ((k' i).val : Qbar l))
                + ∑ i, β.val i * ((l : Qbar l) ^ (m - max c₁ c₂)
                  * ((((k i).val + (k' i).val) / l ^ (m - max c₁ c₂) : ℕ) : Qbar l)) := by
            simp only [key, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
            ring
          rw [hsplit]
          have hN : 0 ≤ ‖(l : Qbar l) ^ (m - max c₁ c₂)‖ := norm_nonneg _
          refine le_trans (IsUltrametricDist.norm_add_le_max _ _)
            (max_le (le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hkc hkc')) ?_)
          refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hN (fun i _ => ?_)
          rw [norm_mul, norm_mul]
          have h1 := ho i
          have h2 := nat_le_one' (l := l) (((k i).val + (k' i).val) / l ^ (m - max c₁ c₂))
          calc _ ≤ 1 * (‖(l : Qbar l) ^ (m - max c₁ c₂)‖ * 1) :=
                mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hN) (by positivity) zero_le_one
            _ = _ := by ring
    · have hU : IsUnit (Φ.ser (P i)) := (pWD l hl Ω A hA j Φ ζ hζ m hm0 (P i)).2 (hu i)
      have hU' : IsUnit (Φ.ser (P' i)) := (pWD l hl Ω A hA j Φ ζ hζ m hm0 (P' i)).2 (hu' i)
      have hs : Φ.ser (P i * P' i) = Φ.ser (P i) * Φ.ser (P' i) := by
        simp [Fr.ser, Polynomial.map_mul, Polynomial.eval₂_mul]
      have ht : Φ.tw m ((D + D') i) = Φ.tw m (D i) + Φ.tw m (D' i) := by
        simp [Fr.tw, map_add (f := _)]
      have e₁ := hPL i
      have e₂ := hPL' i
      unfold LC at e₁ e₂ ⊢
      dsimp only
      rw [ht, hs, dl_mul_eq_add_of_isUnit hU hU', map_add (f := _), map_add (f := _)]
      have f₁ := Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hc₁) e₁
      have f₂ := Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hc₂) e₂
      convert Ideal.add_mem _ f₁ f₂ using 1
      ring
  · intro Z hZ
    refine ⟨0, 0, fun m _ => ⟨fun _ => 1, ?_, fun i => ?_⟩⟩
    · unfold UpperTheory.Kd.C7.BPres GlobalTheory.Col.KumPres
      refine ⟨by simpa using (hζ m).1, by simp, fun i => by simp [pv], fun i => hB.1 i,
        fun s hs hcyc hsζ => ⟨0, fun i => ?_, ?_⟩⟩
      · unfold KumVal
        exact ⟨1, by simp [pv], by simp⟩
      · unfold Cg
        have hz := hZ m s (Subgroup.mem_inf.mpr ⟨hs, MonoidHom.mem_ker.mpr hcyc⟩)
        simp [hz]
    · unfold LC
      simp [Fr.tw, Fr.ser, dl, dd]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.ToBasis
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7.ToBasisLogarithm

variable {l : ℕ} [Fact l.Prime]

private theorem norm_alg_le (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (PadicAlgCl l) z‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
  exact z.2

private theorem norm_nat_le (a : ℕ) : ‖(a : Qbar l)‖ ≤ 1 := by
  simpa using norm_alg_le (l := l) (a : ℤ_[l])

private theorem cg_sum {ι : Type} [Fintype ι] (n : ℕ) (f g : ι → Qbar l) (h : ∀ i, Cg n (f i) (g i)) :
    Cg n (∑ i, f i) (∑ i, g i) := by
  unfold Cg
  rw [← Finset.sum_sub_distrib]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => h i

private theorem cg_mul {n : ℕ} {a b y : Qbar l} (h : Cg n a b) (hy : ‖y‖ ≤ 1) : Cg n (a * y) (b * y) := by
  unfold Cg at *
  rw [← sub_mul, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) hy).trans h

private theorem cg_trans {n : ℕ} {a b c : Qbar l} (h : Cg n a b) (h' : Cg n b c) : Cg n a c := by
  unfold Cg at *
  rw [show a - c = (a - b) + (b - c) by ring]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

private theorem cg_nat {n x y : ℕ} (h : (x : ZMod (l ^ n)) = y) : Cg n (x : Qbar l) y := by
  obtain ⟨e, he⟩ := (Nat.modEq_iff_dvd.1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 h).symm)
  have he' : (x : Qbar l) - y = (l : Qbar l) ^ n * (e : Qbar l) := by exact_mod_cast congrArg (Int.cast : ℤ → Qbar l) he
  have hn : ‖(e : Qbar l)‖ ≤ 1 := by simpa using norm_alg_le (l := l) (e : ℤ_[l])
  unfold Cg
  rw [he', norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hn

private theorem coords {c : Coef l} (β : Bas c) (hβ : ∀ i, ‖β.val i‖ ≤ 1) (n : ℕ) (o : Qbar l) (ho : o ∈ c.O) :
    ∃ a : Fin β.d → ℕ, Cg n o (∑ i, β.val i * (a i : Qbar l)) := by
  refine ⟨fun i => (β.e.repr ⟨o, ho⟩ i).appr n, ?_⟩
  have h1 : o = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr ⟨o, ho⟩ i) := by
    have := congrArg (fun x : c.O => (x : PadicAlgCl l)) (β.e.sum_repr ⟨o, ho⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul] at this
    refine this.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [Algebra.smul_def, mul_comm]; rfl
  refine cg_trans (b := ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr ⟨o, ho⟩ i)) ?_ (cg_sum n _ _ fun i => ?_)
  · unfold Cg; rw [← h1, sub_self, norm_zero]; exact norm_nonneg _
  · rw [mul_comm (β.val i), mul_comm (β.val i)]
    refine cg_mul ?_ (hβ i)
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n (β.e.repr ⟨o, ho⟩ i))
    have := congrArg (algebraMap ℤ_[l] (PadicAlgCl l)) he
    rw [map_mul, map_pow, map_natCast, map_sub, map_natCast] at this
    unfold Cg
    rw [← this, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_alg_le e)

private theorem cg_swap {ι : Type} [Fintype ι] {d n : ℕ} (b : Fin d → Qbar l) (o y : ι → Qbar l) (a : ι → Fin d → ℕ)
    (h : ∀ k, Cg n (o k) (∑ i, b i * (a k i : Qbar l))) (hy : ∀ k, ‖y k‖ ≤ 1) :
    Cg n (∑ k, o k * y k) (∑ i, b i * ∑ k, (a k i : Qbar l) * y k) := by
  have e : ∑ i, b i * ∑ k, (a k i : Qbar l) * y k = ∑ k, (∑ i, b i * (a k i : Qbar l)) * y k := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  rw [e]
  exact cg_sum n _ _ fun k => cg_mul (h k) (hy k)

private theorem logd {Ω : Type} [Field Ω] {ι : Type} (S : Finset ι) (P : ι → Polynomial Ω) (a : ι → ℕ) (z : Ω)
    (hP : ∀ k, (P k).eval z ≠ 0) :
    z * (Polynomial.derivative (∏ k ∈ S, P k ^ a k)).eval z / (∏ k ∈ S, P k ^ a k).eval z =
      ∑ k ∈ S, (a k : Ω) * (z * (Polynomial.derivative (P k)).eval z / (P k).eval z) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    have h0 : (∏ k ∈ S, P k ^ a k).eval z ≠ 0 := by
      rw [Polynomial.eval_prod]
      exact Finset.prod_ne_zero_iff.2 fun k _ => by rw [Polynomial.eval_pow]; exact pow_ne_zero _ (hP k)
    have hk0 := hP k
    rw [Finset.prod_insert hk, Finset.sum_insert hk, ← ih, Polynomial.derivative_mul, Polynomial.derivative_pow]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C]
    rcases a k with _ | r
    · simp
    · simp only [Nat.add_sub_cancel, pow_succ]
      field_simp

private theorem pv_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} (P : Polynomial (R0 A)) {z : Ω} (hz : z ∈ A) :
    (P.map (R0 A).subtype).eval z ∈ A := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add (f := _), Polynomial.eval_add]; exact A.add_mem _ _ hp hq
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.eval_monomial]
    exact A.mul_mem _ _ a.2.1 (A.toSubring.pow_mem hz n)

private theorem pv_conj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} (P : Polynomial (R0 A)) (z : Ω)
    {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) :
    (P.map (R0 A).subtype).eval (s z) = s ((P.map (R0 A).subtype).eval z) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add (f := _), Polynomial.eval_add, Polynomial.eval_add, map_add (f := _), hp, hq]
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.eval_monomial, Polynomial.eval_monomial, map_mul, map_pow]
    congr 1
    exact (a.2.2 s hs).symm

private theorem root_mem {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {z : Ω} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) : z ∈ A := by
  rcases A.mem_or_inv_mem z with h | h
  · exact h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    have e : z = (z⁻¹) ^ k := by
      rw [inv_pow]; exact eq_inv_of_mul_eq_one_right (by rw [← hz, pow_succ])
    rw [e]; exact A.toSubring.pow_mem h k

private theorem ex_conj {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω}
    (h : ∀ u : ℤ_[l]ˣ, ∃ s ∈ Ine (F := ℚ) A, cycZ ℚ Ω l s = u) {m : ℕ} (hm : 1 ≤ m) {z : Ω} (hz : z ^ l ^ m = 1)
    (b : (ZMod (l ^ m))ˣ) : ∃ s ∈ Ine (F := ℚ) A, s z = z ^ (b : ZMod (l ^ m)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hc : ((b : ZMod (l ^ m)).val).Coprime l :=
    Nat.Coprime.coprime_dvd_right (dvd_pow_self l (by omega)) (ZMod.val_coe_unit_coprime b)
  have hu : IsUnit (((b : ZMod (l ^ m)).val : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 hc.symm
  obtain ⟨s, hs, hs'⟩ := h hu.unit
  refine ⟨s, hs, ?_⟩
  have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) z hz
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)) = hu.unit := hs'
  rw [h2, IsUnit.unit_spec, map_natCast, ZMod.natCast_zmod_val] at h1
  exact h1

end UpperTheory.Kd.C7.ToBasisLogarithm

open UpperTheory.Kd.C7.ToBasisLogarithm in
theorem UpperTheory.Kd.C7.pToBasis :
    UpperTheory.Kd.C7.SToBasis := by
  intro l _ hl Ω _ _ _ A hA c β ζ hζ j hj Z m n ι _ P o hm hP ho hK
  classical
  obtain ⟨hprim, hnm, hu, ho1, hpres⟩ := hK
  have hβ := ((pBasEx l c).2 β).1
  have hfr := (pFrobEx l hl Ω A hA).2.2
  choose a ha using fun k => coords β hβ n (o k) (ho k)
  have hQ : ∀ k, ∃ Q : Polynomial (R0 A), Q.map (R0 A).subtype = P k := fun k =>
    ⟨(P k).toSubring (R0 A) (fun x hx => hP k x hx), Polynomial.map_toSubring _ _ _⟩
  choose Q hQ using hQ
  have hmap : ∀ i, (∏ k, Q k ^ a k i).map (R0 A).subtype = ∏ k, P k ^ a k i := fun i => by
    simp only [Polynomial.map_prod, Polynomial.map_pow, hQ]
  have hpv : ∀ i, pv (∏ k, Q k ^ a k i) (ζ m) = ∏ k, (P k).eval (ζ m) ^ a k i := fun i => by
    rw [pv, Polynomial.eval₂_eq_eval_map, hmap, Polynomial.eval_prod]
    simp only [Polynomial.eval_pow]
  refine ⟨fun i => ∏ k, Q k ^ a k i, ⟨hprim, hnm, fun i => ?_, hβ, fun s hs hc hz => ?_⟩, fun b => ?_⟩
  · dsimp only
    rw [hpv]
    refine ⟨A.toSubring.prod_mem fun k _ => A.toSubring.pow_mem (hu k).1 _,
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hu k).2.1, ?_⟩
    rw [← Finset.prod_inv_distrib]
    exact A.toSubring.prod_mem fun k _ => by rw [← inv_pow]; exact A.toSubring.pow_mem (hu k).2.2 _
  · obtain ⟨κ, hκ, hcg⟩ := hpres s hs hc hz
    have hKA := (pKumAlg l hl Ω A hA ζ hζ m n hnm s ⟨hs, hc⟩).1
    refine ⟨fun i => ∑ k, (a k i : ZMod (l ^ n)) * κ k, fun i => ?_, ?_⟩
    · dsimp only
      rw [hpv]
      generalize (Finset.univ : Finset ι) = S
      induction S using Finset.induction_on with
      | empty => simpa using kumVal_one (l := l) n (ζ n) s
      | insert k S hk ih =>
        rw [Finset.prod_insert hk, Finset.sum_insert hk]
        exact (hKA _ _ _ _ ((hKA _ _ _ _ (hκ k) (hκ k)).2.2 (a k i)) ih).1
    · refine UpperTheory.Kd.C7.ToBasisLogarithm.cg_trans hcg (UpperTheory.Kd.C7.ToBasisLogarithm.cg_trans (cg_swap β.val o _ a ha fun k => norm_nat_le _) (cg_sum n _ _ fun i => ?_))
      rw [mul_comm (β.val i), mul_comm (β.val i)]
      refine cg_mul ?_ (hβ i)
      haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
      have := cg_nat (l := l) (n := n) (x := ∑ k, a k i * (κ k).val) (y := (∑ k, (a k i : ZMod (l ^ n)) * κ k).val)
        (by simp)
      simpa using this
  · obtain ⟨s, hs, hsz⟩ := ex_conj hfr hm (hζ m).1.pow_eq_one b
    have hzA : ζ m ∈ A := root_mem A (pow_pos (Fact.out : l.Prime).pos m) (hζ m).1.pow_eq_one
    have hz : ζ m ^ (b : ZMod (l ^ m)).val ∈ A := A.toSubring.pow_mem hzA _
    have hev : ∀ k, (P k).eval (ζ m ^ (b : ZMod (l ^ m)).val) = s ((P k).eval (ζ m)) := fun k => by
      rw [← hsz, ← hQ, pv_conj _ _ hs]
    have hne : ∀ k, (P k).eval (ζ m ^ (b : ZMod (l ^ m)).val) ≠ 0 := fun k => by
      rw [hev]; exact (map_ne_zero s).2 (hu k).2.1
    unfold htv
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hmap, logd _ P _ _ hne, map_sum, map_mul j, map_natCast]
    refine cg_swap β.val o _ a ha fun k => hj _ ?_
    rw [div_eq_mul_inv]
    refine A.mul_mem _ _ (A.mul_mem _ _ hz ?_) ?_
    · rw [← hQ, Polynomial.derivative_map]; exact pv_mem _ hz
    · rw [hev, ← map_inv₀, apply_mem_iff_of_mem_Dec (Ine_le_Dec A hs)]; exact (hu k).2.2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.ContOf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem cg_mono {l : ℕ} [Fact l.Prime] {n N : ℕ} (h : n ≤ N) {a b : Qbar l} (hc : Cg N a b) : Cg n a b := by
  unfold Cg at *
  refine hc.trans ?_
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _) h

private theorem cg_down {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {A : ValuationSubring Ω}
    {Z : Sy Ω l} (hZ : IwI c A Z) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) (n r : ℕ) :
    ∀ d, (∀ x, Cg n (Z (r + d) s x) 0) → ∀ x, Cg n (Z r s x) 0 := by
  intro d
  induction d with
  | zero => intro h; simpa using h
  | succ d ih =>
    intro h
    apply ih
    intro x
    have hsum := hZ.nrm (r + d) s hs x
    unfold Cg at h ⊢
    rw [sub_zero, hsum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) ?_
    intro x' _
    have := h x'
    rw [sub_zero] at this
    exact this

private theorem unit_lift (l : ℕ) [Fact l.Prime] (m : ℕ) (hm : 1 ≤ m) (x : (ZMod (l ^ m))ˣ) :
    ∃ u : ℤ_[l]ˣ, PadicInt.toZModPow m (u : ℤ_[l]) = x := by
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Fact (1 < l ^ m) := ⟨Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt⟩
  have hsurj : Function.Surjective (PadicInt.toZModPow (p := l) m) := by
    intro y
    obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective y
    exact ⟨k, map_natCast _ k⟩
  obtain ⟨u, hu⟩ := IsLocalRing.surjective_units_map_of_local_ringHom _ hsurj hsurj.isLocalHom x
  exact ⟨u, congrArg Units.val hu⟩

theorem UpperTheory.Kd.C7.pContOf :
    UpperTheory.Kd.C7.SContOf := by
  unfold UpperTheory.Kd.C7.SContOf
  intro l _ hl2 Ω _ _ _ A hA c β ζ hζ Z hZ hP
  obtain ⟨c₀, m₀, hP⟩ := hP
  intro r n
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  set m := r + (m₀ + n + c₀ + 1) with hm_def
  have hm0 : m₀ ≤ m := by omega
  obtain ⟨P, hKP⟩ := hP m hm0
  set N := m - c₀ with hN
  obtain ⟨hprim, hNm, hu, ho, hk⟩ := hKP
  have hlN : 0 < l ^ N := pow_pos (Fact.out : l.Prime).pos N
  choose w hw using fun i : Fin β.d => IsAlgClosed.exists_pow_nat_eq (pv (P i) (ζ m)) hlN
  have hfe := UpperTheory.Kd.C7.pFrobEx l hl2 Ω A hA
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hlift : ∀ y : (ZMod (l ^ m))ˣ, ∃ t ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m t = y⁻¹ := by
    intro y
    obtain ⟨u, hu'⟩ := unit_lift l m (by omega) y⁻¹
    obtain ⟨t, ht, htu⟩ := hfe.2.2 u
    refine ⟨t, ht, ?_⟩
    ext
    simp [ReciprocityTheory.Gal.cycMod, htu, hu']
  choose tt htt hcyc using hlift
  let f : (ZMod (l ^ m))ˣ × Option (Fin β.d) → Ω := fun q => (tt q.1)⁻¹ (q.2.elim (ζ N) w)
  let E := IntermediateField.adjoin ℚ (Set.range f)
  haveI : FiniteDimensional ℚ E :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral)
  refine ⟨(cycMod ℚ Ω l m).ker ⊓ E.fixingSubgroup, ?_, ?_⟩
  · rw [Subgroup.coe_inf]
    refine IsOpen.inter ?_ E.fixingSubgroup_isOpen
    have := (GlobalTheory.KZ.IwC.isLocallyConstant_cycMod (Ω := Ω) (l := l) m).isOpen_fiber 1
    rw [MonoidHom.coe_ker]
    exact this
  · intro s hsU hs
    obtain ⟨hsk, hsE⟩ := Subgroup.mem_inf.mp hsU
    have hfix : ∀ q, s (f q) = f q := by
      intro q
      exact (mem_fixingSubgroup_iff _).mp hsE (f q) (IntermediateField.subset_adjoin ℚ _ ⟨q, rfl⟩)
    apply cg_down hZ hs n r (m₀ + n + c₀ + 1)
    intro y
    have hsH : s ∈ Hm l A m := by
      unfold UpperTheory.Kd.C7.Hm
      exact Subgroup.mem_inf.mpr ⟨hs, hsk⟩
    obtain ⟨hconjH, hconj⟩ := UpperTheory.Kd.C7.pConj l hl2 Ω A hA c Z hZ m s hsH (tt y) (htt y)
    have hZeq : Z m (tt y * s * (tt y)⁻¹) 1 = Z m s y := by
      rw [hconj]
      simp [hcyc]
    have hconjH' := hconjH
    unfold UpperTheory.Kd.C7.Hm at hconjH'
    have hs'I := (Subgroup.mem_inf.mp hconjH').1
    have hs'k : cycMod ℚ Ω l m (tt y * s * (tt y)⁻¹) = 1 := (Subgroup.mem_inf.mp hconjH').2
    have hs'fix : ∀ o : Option (Fin β.d),
        (tt y * s * (tt y)⁻¹) (o.elim (ζ N) w) = o.elim (ζ N) w := by
      intro o
      have h := hfix (y, o)
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h, ← AlgEquiv.mul_apply, mul_inv_cancel,
        AlgEquiv.one_apply]
    have hz : (tt y * s * (tt y)⁻¹) (ζ N) = ζ N := hs'fix none
    obtain ⟨k, hkv, hcg⟩ := hk _ hs'I hs'k hz
    have hk0 : ∀ i, k i = 0 := by
      intro i
      have hwi : (tt y * s * (tt y)⁻¹) (w i) = w i := hs'fix (some i)
      have h0 : KumVal N (ζ N) (pv (P i) (ζ m)) (tt y * s * (tt y)⁻¹) 0 :=
        ⟨w i, hw i, by rw [hwi]; simp⟩
      exact kumVal_unique hprim hz (hu i).2.1 (hkv i) h0
    rw [← hZeq]
    apply cg_mono (n := n) (N := N) (by omega)
    simpa [hk0] using hcg
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.IwOpsRedUn
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem iwOps_red_un {l : ℕ} [Fact l.Prime] (b : ℕ) (hb : ¬ l ∣ b) (r : ℕ) :
    red l r (un b hb (r + 1)) = un b hb r := by
  ext
  simp only [un, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, ZMod.coe_unitOfCoprime, map_natCast]

private theorem iwOps_tr {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    {A : ValuationSubring Ω} {Z : Sy Ω l} (h : IwI c A Z) (b : ℕ) (hb : ¬ l ∣ b) : IwI c A (tr b hb Z) := by
  refine ⟨fun r s hs x => h.int r s hs _, fun r s hs t ht x => ?_, fun r s hs x => ?_⟩
  · simp only [UpperTheory.Kd.C7.tr]
    rw [h.coc r s hs t ht, mul_right_comm]
  · simp only [UpperTheory.Kd.C7.tr]
    rw [h.nrm r s hs]
    symm
    refine Finset.sum_equiv (Equiv.mulRight (un b hb (r + 1))) (fun y => ?_) (fun y _ => rfl)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulRight]
    rw [map_mul, iwOps_red_un, mul_left_inj]

theorem UpperTheory.Kd.C7.pIwOps :
    UpperTheory.Kd.C7.SIwOps := by
  intro l _ _ Ω _ _ _ A _ c Z h b hb
  have h' := iwOps_tr h b hb
  refine ⟨h', fun r s hs x => ?_, fun r s hs t ht x => ?_, fun r s hs x => ?_⟩
  · exact c.O.sub_mem (h.int r s hs x) (c.O.mul_mem (natCast_mem c.O b) (h'.int r s hs x))
  · simp only [sharp]
    rw [h.coc r s hs t ht, h'.coc r s hs t ht]
    ring
  · simp only [sharp]
    rw [h.nrm r s hs, h'.nrm r s hs, Finset.sum_sub_distrib, Finset.mul_sum]
end

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace UpperTheory.Kd.C7

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω}

private theorem norm_pow_anti (n' n : ℕ) (h : n' ≤ n) : ‖((l : ℕ) : Qbar l) ^ n‖ ≤ ‖((l : ℕ) : Qbar l) ^ n'‖ := by
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one.le h

private theorem cg_mono {n' n : ℕ} (h : n' ≤ n) {x y : Qbar l} (hc : Cg n x y) : Cg n' x y :=
  le_trans hc (norm_pow_anti n' n h)

private theorem cg_trans {n : ℕ} {x y z : Qbar l} (h1 : Cg n x y) (h2 : Cg n y z) : Cg n x z := by
  have e : x - z = (x - y) + (y - z) := by ring
  unfold Cg at *
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

private theorem cg_sub {n : ℕ} {x y x' y' : Qbar l} (h1 : Cg n x y) (h2 : Cg n x' y') : Cg n (x - x') (y - y') := by
  have e : x - x' - (y - y') = (x - y) + -(x' - y') := by ring
  unfold Cg at *
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
  rwa [norm_neg]

private theorem cg_mul {n : ℕ} {x y w : Qbar l} (hw : ‖w‖ ≤ 1) (h1 : Cg n x y) : Cg n (w * x) (w * y) := by
  unfold Cg at *
  rw [← mul_sub, norm_mul]
  calc ‖w‖ * ‖x - y‖ ≤ 1 * ‖x - y‖ := by gcongr
    _ ≤ _ := by rwa [one_mul]

private theorem cg_sum {n : ℕ} {ι : Type} (T : Finset ι) (x y : ι → Qbar l) (h : ∀ i ∈ T, Cg n (x i) (y i)) :
    Cg n (∑ i ∈ T, x i) (∑ i ∈ T, y i) := by
  unfold Cg at *
  rw [← Finset.sum_sub_distrib]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) h

private theorem norm_nat_le (d : ℕ) : ‖(d : Qbar l)‖ ≤ 1 := by
  have h : (d : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (d : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  have h1 := PadicInt.norm_le_one (d : ℤ_[l])
  rw [PadicInt.norm_def] at h1
  exact_mod_cast h1

private theorem norm_padic_nat (d : ℕ) (hd : ¬ l ∣ d) : ‖(d : ℚ_[l])‖ = 1 :=
  Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hd)

private theorem norm_nat_eq (d : ℕ) (hd : ¬ l ∣ d) : ‖(d : Qbar l)‖ = 1 := by
  have h : (d : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (d : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact norm_padic_nat d hd

private theorem exists_unit (d : ℕ) (hd : ¬ l ∣ d) : ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) = d := by
  have h : IsUnit (d : ℤ_[l]) := PadicInt.isUnit_iff.2 (by
    rw [PadicInt.norm_def]
    simpa using norm_padic_nat (l := l) d hd)
  exact ⟨h.unit, h.unit_spec⟩

private theorem exists_ine_un (hl : l ≠ 2) (hA : OverL l A) (d : ℕ) (hd : ¬ l ∣ d) (m : ℕ) :
    ∃ t ∈ Ine (F := ℚ) A, (cycMod ℚ Ω l m t)⁻¹ = un d hd m := by
  obtain ⟨u, hu⟩ := exists_unit (l := l) d hd
  obtain ⟨t, ht, e⟩ := (pFrobEx l hl Ω A hA).2.2 u⁻¹
  refine ⟨t, ht, Units.ext ?_⟩
  have h1 : (cycMod ℚ Ω l m t)⁻¹ = Units.map (PadicInt.toZModPow m : ℤ_[l] →+* ZMod (l ^ m)).toMonoidHom u := by
    simp [cycMod, e]
  rw [h1]
  simp [un, hu]

private theorem mem_of_mul_mem (c : Coef l) {θ y : Qbar l} (h1 : ‖θ‖ = 1) (hy : y ∈ c.O) (h0 : y ≠ 0)
    (hθ : θ * y ∈ c.O) : θ ∈ c.O := by
  obtain ⟨β⟩ := (pBasEx l c).1
  have hinv := ((pBasEx l c).2 β).2.2.2
  have hθ0 : θ ≠ 0 := by rintro rfl; simp at h1
  rcases ValuationRing.dvd_total (⟨y, hy⟩ : c.O) ⟨θ * y, hθ⟩ with ⟨k, hk⟩ | ⟨k, hk⟩
  · have h2 : θ * y = y * k := congrArg Subtype.val hk
    have h3 : θ = k := by
      apply mul_right_cancel₀ h0
      rw [h2, mul_comm]
    rw [h3]; exact k.2
  · have h2 : y = θ * y * k := congrArg Subtype.val hk
    have h3 : θ⁻¹ = k := by
      apply mul_left_cancel₀ (mul_ne_zero hθ0 h0)
      rw [← h2, mul_assoc, mul_comm θ, mul_assoc, inv_mul_cancel₀ hθ0, mul_one]
    have h4 : θ⁻¹ ∈ c.O := by rw [h3]; exact k.2
    have := hinv θ⁻¹ h4 (by rw [norm_inv, h1, inv_one])
    rwa [inv_inv] at this

private theorem eig_at (hl : l ≠ 2) (hA : OverL l A) {c : Coef l} {Z : Sy Ω l} (hZ : IwI c A Z) {a : Qbar l} {fr : G ℚ Ω}
    (hfr : fr ∈ Dec (F := ℚ) A) (E : ∀ m, ∀ s ∈ Hm l A m, Z m (fr * s * fr⁻¹) 1 = a * Z m s 1) (m : ℕ) {s : G ℚ Ω}
    (hs : s ∈ Hm l A m) {t : G ℚ Ω} (ht : t ∈ Ine (F := ℚ) A) :
    Z m (fr * s * fr⁻¹) (cycMod ℚ Ω l m t)⁻¹ = a * Z m s (cycMod ℚ Ω l m t)⁻¹ := by
  have hsI : s ∈ Ine (F := ℚ) A := (Subgroup.mem_inf.1 hs).1
  have hsk : cycMod ℚ Ω l m s = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hs).2
  have hs' : fr * s * fr⁻¹ ∈ Hm l A m := by
    refine Subgroup.mem_inf.2 ⟨conj_mem_Ine hfr hsI, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_mul, hsk, mul_one, ← map_mul, mul_inv_cancel, map_one]
  have ht' : fr * t * fr⁻¹ ∈ Ine (F := ℚ) A := conj_mem_Ine hfr ht
  have h1 := (pConj l hl Ω A hA c Z hZ m _ hs' _ ht').2 1
  have hc : cycMod ℚ Ω l m (fr * t * fr⁻¹) = cycMod ℚ Ω l m t := by
    rw [map_mul, map_mul, map_inv, mul_comm (cycMod ℚ Ω l m fr), mul_assoc, mul_inv_cancel, mul_one]
  have hconj : (fr * t * fr⁻¹) * (fr * s * fr⁻¹) * (fr * t * fr⁻¹)⁻¹ = fr * (t * s * t⁻¹) * fr⁻¹ := by group
  have h2 := pConj l hl Ω A hA c Z hZ m s hs t ht
  have h3 := E m _ h2.1
  have h4 := h2.2 1
  rw [hconj, hc, one_mul] at h1
  rw [one_mul] at h4
  rw [← h1, h3, h4]

private theorem sharp_eig (hl : l ≠ 2) (hA : OverL l A) {c : Coef l} {Z : Sy Ω l} (hZ : IwI c A Z) {a : Qbar l} {fr : G ℚ Ω}
    (hfr : fr ∈ Dec (F := ℚ) A) (E : ∀ m, ∀ s ∈ Hm l A m, Z m (fr * s * fr⁻¹) 1 = a * Z m s 1) (d : ℕ) (hd : ¬ l ∣ d) (m : ℕ)
    {s : G ℚ Ω} (hs : s ∈ Hm l A m) : sharp d hd Z m (fr * s * fr⁻¹) 1 = a * sharp d hd Z m s 1 := by
  obtain ⟨t, ht, e⟩ := exists_ine_un (Ω := Ω) hl hA d hd m
  simp only [sharp, tr, one_mul]
  rw [E m s hs, ← e, eig_at hl hA hZ hfr E m hs ht]
  ring

private theorem pack (hl : l ≠ 2) (hA : OverL l A) {j : Ω →+* Qbar l} (Φ : Fr l A j) {c : Coef l} (β : Bas c) {ζ : ℕ → Ω}
    (hζ : Roots l ζ) {Y : Sy Ω l} (hY : IwI c A Y) {D : Fin β.d → PowerSeries Φ.R} (hD : Rep Φ β ζ Y D) {a : Qbar l}
    (ha : ‖a‖ = 1) (E : ∀ m, ∀ s ∈ Hm l A m, Y m (Φ.fr * s * Φ.fr⁻¹) 1 = a * Y m s 1) :
    ∃ (a₁ : c.O) (Gs : PowerSeries (Qbar l)) (v : ℂ_[l]), (∀ i, Φ.tw 1 (D i) = Φ.act (β.mat a₁) D i) ∧ ‖v‖ = 1 ∧
      (∀ n, Gs.coeff n ∈ c.O) ∧
      (∀ n, Φ.lam β (fun i => (D i).coeff n) = v * algebraMap (PadicAlgCl l) ℂ_[l] (Gs.coeff n)) ∧
      ((a₁ : PadicAlgCl l) = a ∨ Gs = 0) := by
  by_cases haO : a ∈ c.O
  · let a' : c.O := ⟨a, haO⟩
    have hinv := ((pBasEx l c).2 β).2.2.2 a haO ha
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    have hu : IsUnit a' := IsUnit.of_mul_eq_one ⟨a⁻¹, hinv⟩ (Subtype.ext (mul_inv_cancel₀ ha0))
    have hfr := pRepFrob l hl Ω A hA j Φ c β ζ hζ Y D a' hD E
    obtain ⟨v, hv, hper⟩ := pPeriod l hl Ω A hA j Φ c β a' hu
    have hx : ∀ n, ∃ o : c.O, Φ.lam β (fun i => (D i).coeff n) = v * algebraMap (PadicAlgCl l) ℂ_[l] (o : PadicAlgCl l) := by
      intro n
      refine hper _ fun i => ?_
      have := congrArg (PowerSeries.coeff n) (hfr i)
      simpa [Fr.tw, Fr.act, PowerSeries.coeff_C_mul] using this
    choose o ho using hx
    refine ⟨a', PowerSeries.mk fun n => (o n : PadicAlgCl l), v, hfr, hv, fun n => ?_, fun n => ?_, Or.inl rfl⟩
    · rw [PowerSeries.coeff_mk]; exact (o n).2
    · rw [PowerSeries.coeff_mk]; exact ho n
  · have hz : ∀ m, ∀ s ∈ Hm l A m, Y m s 1 = 0 := by
      intro m s hs
      by_contra h0
      have hsI : s ∈ Ine (F := ℚ) A := (Subgroup.mem_inf.1 hs).1
      refine haO (mem_of_mul_mem c ha (hY.int m s hsI 1) h0 ?_)
      rw [← E m s hs]
      exact hY.int m _ (conj_mem_Ine Φ.fr_dec hsI) 1
    have h0 := pRepUniq l hl Ω A hA j Φ c β ζ hζ Y Y D 0 hD
      ((pRepAdd l hl Ω A hA j Φ c β ζ hζ).2 Y hz) (fun _ _ _ => rfl)
    subst h0
    refine ⟨1, 0, 1, fun i => ?_, by simp, fun n => by simp [zero_mem], fun n => ?_, Or.inr rfl⟩
    · simp [Fr.tw, Fr.act]
    · simp [Fr.lam]

private theorem exists_approx (v : ℂ_[l]) (hv : ‖v‖ = 1) : ∃ vm : ℕ → Qbar l,
    (∀ m, ‖algebraMap (PadicAlgCl l) ℂ_[l] (vm m) - v‖ ≤ ‖(l : ℂ_[l]) ^ m‖) ∧ ∀ m, ‖vm m‖ = 1 ∧ Cg m (vm (m + 1)) (vm m) := by
  have hn : ∀ n, ‖(l : ℂ_[l]) ^ n‖ = ‖((l : ℕ) : Qbar l) ^ n‖ := by
    intro n
    rw [norm_pow, norm_pow, ← PadicComplex.coe_natCast]
    congr 1
    exact PadicComplex.norm_extends l _
  have hal : ∀ x : Qbar l, ‖algebraMap (PadicAlgCl l) ℂ_[l] x‖ = ‖x‖ := fun x => PadicComplex.norm_extends l x
  have hl1 : ‖((l : ℕ) : Qbar l)‖ < 1 := GlobalTheory.LambdaValuationPowers.norm_natCast_lt_one
  have hl0 : 0 < ‖((l : ℕ) : Qbar l)‖ := norm_pos_iff.2 GlobalTheory.LambdaValuationPowers.natCast_ne_zero
  have hex : ∀ m : ℕ, ∃ y : Qbar l, ‖algebraMap (PadicAlgCl l) ℂ_[l] y - v‖ ≤ ‖(l : ℂ_[l]) ^ (m + 1)‖ := by
    intro m
    have hr : 0 < ‖(l : ℂ_[l]) ^ (m + 1)‖ := by
      rw [hn, norm_pow]; exact pow_pos hl0 _
    obtain ⟨y, hy⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl l)).exists_dist_lt v hr
    refine ⟨y, ?_⟩
    rw [dist_comm, dist_eq_norm] at hy
    exact hy.le
  choose vm hvm using hex
  have hlt : ∀ m, ‖algebraMap (PadicAlgCl l) ℂ_[l] (vm m) - v‖ < 1 := by
    intro m
    refine (hvm m).trans_lt ?_
    rw [hn, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hl1 (by omega)
  refine ⟨vm, fun m => (hvm m).trans ?_, fun m => ⟨?_, ?_⟩⟩
  · rw [hn, hn]; exact norm_pow_anti m (m + 1) (by omega)
  · rw [← hal]
    apply le_antisymm
    · have e : algebraMap (PadicAlgCl l) ℂ_[l] (vm m) = (algebraMap (PadicAlgCl l) ℂ_[l] (vm m) - v) + v := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hlt m).le hv.le)
    · have e : v = algebraMap (PadicAlgCl l) ℂ_[l] (vm m) + -(algebraMap (PadicAlgCl l) ℂ_[l] (vm m) - v) := by ring
      have h1 : ‖v‖ ≤ _ := (congrArg norm e).le.trans (IsUltrametricDist.norm_add_le_max _ _)
      rw [hv, norm_neg] at h1
      rcases le_max_iff.1 h1 with h | h
      · exact h
      · exact absurd h (not_le.2 (hlt m))
  · unfold Cg
    rw [← hal, map_sub]
    have e : algebraMap (PadicAlgCl l) ℂ_[l] (vm (m + 1)) - algebraMap (PadicAlgCl l) ℂ_[l] (vm m) =
        (algebraMap (PadicAlgCl l) ℂ_[l] (vm (m + 1)) - v) + -(algebraMap (PadicAlgCl l) ℂ_[l] (vm m) - v) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · refine (hvm (m + 1)).trans ?_
      rw [hn]; exact norm_pow_anti m _ (by omega)
    · rw [norm_neg]
      refine (hvm m).trans ?_
      rw [hn]; exact norm_pow_anti m _ (by omega)

private theorem sum_step {m : ℕ} (ψ : DirichletCharacter (Qbar l) (l ^ m)) (d₀ : ℕ) (hd : ¬ l ∣ d₀) (n : ℕ)
    (h h' T : (ZMod (l ^ m))ˣ → Qbar l) (w : Qbar l) (h1 : ∀ b, Cg n (h b) (h' b))
    (h2 : ∀ b, Cg n (h' b - (d₀ : Qbar l) * h' (b * un d₀ hd m)) (w * T b)) :
    Cg n ((1 - (d₀ : Qbar l) * ψ⁻¹ (d₀ : ZMod (l ^ m))) * ∑ b : (ZMod (l ^ m))ˣ, ψ b * h b)
      (w * ∑ b : (ZMod (l ^ m))ˣ, ψ b * T b) := by
  have hu : ((un d₀ hd m : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) = (d₀ : ZMod (l ^ m)) := by simp [un]
  have hinv : ψ⁻¹ (d₀ : ZMod (l ^ m)) * ψ (d₀ : ZMod (l ^ m)) = 1 := by
    rw [← hu, MulChar.inv_apply, Ring.inverse_unit, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  have hre : ∑ b : (ZMod (l ^ m))ˣ, ψ b * h (b * un d₀ hd m) =
      ψ⁻¹ (d₀ : ZMod (l ^ m)) * ∑ b : (ZMod (l ^ m))ˣ, ψ b * h b := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulRight (un d₀ hd m)) _ _ fun b => ?_
    simp only [Equiv.coe_mulRight, Units.val_mul, map_mul, hu]
    linear_combination (-(ψ b * h (b * un d₀ hd m))) * hinv
  have key : (1 - (d₀ : Qbar l) * ψ⁻¹ (d₀ : ZMod (l ^ m))) * ∑ b : (ZMod (l ^ m))ˣ, ψ b * h b =
      ∑ b : (ZMod (l ^ m))ˣ, ψ b * (h b - (d₀ : Qbar l) * h (b * un d₀ hd m)) := by
    have e : ∀ b : (ZMod (l ^ m))ˣ, ψ b * (h b - (d₀ : Qbar l) * h (b * un d₀ hd m)) =
        ψ b * h b - (d₀ : Qbar l) * (ψ b * h (b * un d₀ hd m)) := fun b => by ring
    simp only [e]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hre]
    ring
  rw [key, Finset.mul_sum]
  have e2 : ∀ b : (ZMod (l ^ m))ˣ, w * (ψ b * T b) = ψ b * (w * T b) := fun b => by ring
  simp only [e2]
  refine cg_sum _ _ _ fun b _ => cg_mul (DirichletCharacter.unit_norm_eq_one ψ b).le ?_
  exact cg_trans (cg_sub (h1 b) (cg_mul (norm_nat_le d₀) (h1 _))) (h2 b)

theorem pCore : SCore := by
  intro l _ hl Ω _ _ _ A hA c Z a j d₀ e₀ m₀ ζ hZ ha E hj hd hζ hP
  obtain ⟨Φ⟩ := pFrEx3 l hl Ω A hA j hj
  obtain ⟨β⟩ := (pBasEx l c).1
  have hHP : HasPres β A ζ Z := by
    refine ⟨e₀, max m₀ 1, fun m hm => ?_⟩
    obtain ⟨ι, _, P, o, h1, h2, h3⟩ := hP m (le_of_max_le_left hm)
    obtain ⟨P', hP', -⟩ := pToBasis l hl Ω A hA c β ζ hζ j hj Z m (m - e₀) ι P o (le_of_max_le_right hm) h1 h2 h3
    exact ⟨P', hP'⟩
  have hCont := pContOf l hl Ω A hA c β ζ hζ Z hZ hHP
  have hops := pIwOps l hl Ω A hA c Z hZ d₀ hd
  have hHS := pKumEx l hl Ω A hA c β ζ hζ Z hZ hCont d₀ hd
  obtain ⟨D, hD⟩ := pRepEx l hl Ω A hA j Φ c β ζ hζ _ hops.2 hHS
  have E' : ∀ m, ∀ s ∈ Hm l A m, Z m (Φ.fr * s * Φ.fr⁻¹) 1 = a * Z m s 1 := E Φ.fr Φ.fr_dec Φ.fr_frob Φ.fr_cyc
  obtain ⟨a₁, Gs, v, htw, hv, hGs, hlam, hor⟩ := pack hl hA Φ β hζ hops.2 hD ha
    (fun m s hs => sharp_eig hl hA hZ Φ.fr_dec E' d₀ hd m hs)
  have hGn : ∀ n, ‖Gs.coeff n‖ ≤ 1 := fun n => GlobalTheory.LambdaValuationPowers.norm_le_one_of_mem (hGs n)
  obtain ⟨vm, hvm, hvm2⟩ := exists_approx v hv
  obtain ⟨c₁, m₁, hcl⟩ := pClause1 l hl Ω A hA j Φ c β ζ hζ hj Z hZ d₀ hd D a₁ Gs v vm hD htw hGn hlam hvm e₀
  refine ⟨Gs, vm, max c₁ e₀, max m₁ 1, hGs, hvm2, ?_, ?_⟩
  · intro m hm ι _ P o h1 h2 h3 ψ
    obtain ⟨P', hP', hcg⟩ := pToBasis l hl Ω A hA c β ζ hζ j hj Z m (m - e₀) ι P o (le_of_max_le_right hm) h1 h2 h3
    have hc := hcl m (le_of_max_le_left hm) P' hP'
    have hT : ∀ (N : ℕ) (z : Qbar l), vm m * (a₁ : PadicAlgCl l) ^ m * tval Gs N z = vm m * a ^ m * tval Gs N z := by
      intro N z
      rcases hor with e | e
      · rw [e]
      · simp [e, tval]
    exact sum_step ψ d₀ hd (m - max c₁ e₀) (fun b => htv j (ζ m) P o (b : ZMod (l ^ m)).val)
      (fun b => htv j (ζ m) (fun i => (P' i).map (R0 A).subtype) β.val (b : ZMod (l ^ m)).val)
      (fun b => tval Gs (l ^ (3 * m)) (j (ζ m) ^ (b : ZMod (l ^ m)).val)) (vm m * a ^ m)
      (fun b => cg_mono (Nat.sub_le_sub_left (le_max_right _ _) m) (hcg b))
      (fun b => by
        have := hc b
        rw [hT] at this
        exact cg_mono (Nat.sub_le_sub_left (le_max_left _ _) m) this)
  · intro φ k hk hsp
    obtain ⟨g, hg, c₂, Z', hZ', hC', rel⟩ := pDiv l hl Ω A hA c Z hZ hCont φ k hk hsp
    have ops' := pIwOps l hl Ω A hA c Z' hZ' d₀ hd
    have hHS' := pKumEx l hl Ω A hA c β ζ hζ Z' hZ' hC' d₀ hd
    obtain ⟨D', hD'⟩ := pRepEx l hl Ω A hA j Φ c β ζ hζ _ ops'.2 hHS'
    have hθn : ‖φ (g : ZMod l) * (g : Qbar l) ^ k‖ = 1 := by
      have hcop : g.Coprime l := ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hg).symm
      have h1 := DirichletCharacter.unit_norm_eq_one φ (ZMod.unitOfCoprime g hcop)
      rw [ZMod.coe_unitOfCoprime] at h1
      rw [norm_mul, norm_pow, norm_nat_eq g hg, h1, one_pow, one_mul]
    have hrel : ∀ m, ∀ s ∈ Hm l A m, ∀ x, (l : Qbar l) ^ c₂ * sharp d₀ hd Z m s x =
        sharp d₀ hd Z' m s (x * un g hg m) - φ (g : ZMod l) * (g : Qbar l) ^ k * sharp d₀ hd Z' m s x := by
      intro m s hs x
      have r1 := rel m s hs x
      have r2 := rel m s hs (x * un d₀ hd m)
      simp only [sharp, tr] at r1 r2 ⊢
      rw [mul_right_comm x (un d₀ hd m) (un g hg m)] at r2
      linear_combination r1 - (d₀ : Qbar l) * r2
    by_cases hθ : φ (g : ZMod l) * (g : Qbar l) ^ k ∈ c.O
    · let θ : c.O := ⟨_, hθ⟩
      have R1 := pRepSmul l hl Ω A hA j Φ c β ζ hζ _ D ((l : c.O) ^ c₂) hD
      have R2 := pRepSmul l hl Ω A hA j Φ c β ζ hζ _ D' θ hD'
      have R3 := (pRepAdd l hl Ω A hA j Φ c β ζ hζ).1 _ _ _ _ R1 R2
      have R4 := pRepTr l hl Ω A hA j Φ c β ζ hζ _ ops'.2 g hg D' hD'
      have heq := pRepUniq l hl Ω A hA j Φ c β ζ hζ _ _ _ _ R3 R4 (fun m s hs => by
        have h1 := hrel m s hs 1
        have e : (((l : c.O) ^ c₂ : c.O) : PadicAlgCl l) = (l : Qbar l) ^ c₂ := by simp
        rw [e]
        change _ + (φ (g : ZMod l) * (g : Qbar l) ^ k) * _ = sharp d₀ hd Z' m s (1 * un g hg m)
        rw [h1]
        ring)
      refine pClause2 l hl Ω A hA j Φ hj c β D D' Gs v g c₂ k φ θ hg rfl hv hGn hlam fun i => ?_
      have := congrFun heq i
      rw [eq_sub_iff_add_eq]
      exact this
    · have hz' : ∀ m, ∀ s ∈ Hm l A m, ∀ x, sharp d₀ hd Z' m s x = 0 := by
        intro m s hs x
        by_contra h0
        have hsI : s ∈ Ine (F := ℚ) A := (Subgroup.mem_inf.1 hs).1
        refine hθ (mem_of_mul_mem c hθn (ops'.2.int m s hsI x) h0 ?_)
        have h1 := hrel m s hs x
        have e : φ (g : ZMod l) * (g : Qbar l) ^ k * sharp d₀ hd Z' m s x =
            sharp d₀ hd Z' m s (x * un g hg m) - (l : Qbar l) ^ c₂ * sharp d₀ hd Z m s x := by
          rw [h1]; ring
        rw [e]
        exact c.O.sub_mem (ops'.2.int m s hsI _) (c.O.mul_mem (pow_mem (natCast_mem _ _) _) (hops.2.int m s hsI x))
      have hz : ∀ m, ∀ s ∈ Hm l A m, sharp d₀ hd Z m s 1 = 0 := by
        intro m s hs
        have h1 := hrel m s hs 1
        rw [hz' m s hs, hz' m s hs, mul_zero, sub_zero] at h1
        exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ GlobalTheory.LambdaValuationPowers.natCast_ne_zero)
      have h0 := pRepUniq l hl Ω A hA j Φ c β ζ hζ _ _ D 0 hD
        ((pRepAdd l hl Ω A hA j Φ c β ζ hζ).2 _ hz) (fun _ _ _ => rfl)
      have hG0 : Gs = 0 := by
        ext n
        have h1 := hlam n
        have hv0 : v ≠ 0 := by rintro rfl; simp at hv
        have h2 : Φ.lam β (fun i => (D i).coeff n) = 0 := by simp [h0, Fr.lam]
        rw [h2] at h1
        have h3 := (mul_eq_zero.1 h1.symm).resolve_left hv0
        simpa using h3
      rw [hG0]
      intro n
      exact ⟨0, fun r _ ξ _ => by simp [Cg, intg, mass, tval]⟩

end UpperTheory.Kd.C7
