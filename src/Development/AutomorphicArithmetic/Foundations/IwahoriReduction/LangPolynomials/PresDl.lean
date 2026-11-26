module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PolyEx
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerElementFixedFieldClosedSubgroup

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PresDl
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem mem_of_pow_mem {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {v : Ω} {N : ℕ} (hN : N ≠ 0)
    (h : v ^ N ∈ A) : v ∈ A := by
  rcases A.mem_or_inv_mem v with hv | hv
  · exact hv
  · by_cases h0 : v = 0
    · rw [h0]
      exact zero_mem A
    · obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
      have e : v = v ^ (m + 1) * v⁻¹ ^ m := by
        rw [pow_succ, inv_pow, mul_comm (v ^ m) v, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ h0), mul_one]
      rw [e]
      exact mul_mem h (pow_mem hv _)

private theorem coord_eq {l : ℕ} [Fact l.Prime] {c : Coef l} (β : Bas c) {n : ℕ} {z : Qbar l}
    (k k' : Fin β.d → ZMod (l ^ n)) (h : Cg n z (∑ i, β.val i * ((k i).val : Qbar l)))
    (h' : Cg n z (∑ i, β.val i * ((k' i).val : Qbar l))) (i : Fin β.d) : k i = k' i := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hB := ((pBasEx l c).2 β).2.1 n (fun i => ((k i).val : ℤ_[l]) - ((k' i).val : ℤ_[l])) ?_ i
  · obtain ⟨d, hd⟩ := hB
    have h2 := congrArg (PadicInt.toZModPow n) hd
    simp only [map_sub, map_natCast, map_mul, map_pow, ZMod.natCast_zmod_val] at h2
    have hl : ((l : ZMod (l ^ n))) ^ n = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [hl, zero_mul, sub_eq_zero] at h2
    exact h2
  · unfold Cg at h h' ⊢
    simp only [map_sub, map_natCast, mul_sub, Finset.sum_sub_distrib, sub_zero]
    have key := (IsUltrametricDist.norm_add_le_max (z - ∑ i, β.val i * ((k' i).val : Qbar l))
      (-(z - ∑ i, β.val i * ((k i).val : Qbar l)))).trans (max_le h' (by rwa [norm_neg]))
    have e : (∑ x, β.val x * ((k x).val : Qbar l)) - ∑ x, β.val x * ((k' x).val : Qbar l)
        = (z - ∑ i, β.val i * ((k' i).val : Qbar l)) + -(z - ∑ i, β.val i * ((k i).val : Qbar l)) := by
      ring
    rw [e]
    exact key

private theorem ser_rel {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω}
    {j : Ω →+* Qbar l} (Φ : Fr l A j) (P P' Q : Polynomial (R0 A)) (N : ℕ) :
    Φ.ser (P - P' * Q ^ N) = Φ.ser P - Φ.ser P' * Φ.ser Q ^ N := by
  unfold Fr.ser
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow]

theorem UpperTheory.Kd.C7.pPresDl :
    UpperTheory.Kd.C7.SPresDl := by
  intro l _ hl2 Ω _ _ _ A hA j Φ c β ζ hζ Z m n hm P P' hP hP' i
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hlN : l ^ n ≠ 0 := pow_ne_zero _ hl0
  unfold BPres KumPres at hP hP'
  obtain ⟨-, hnm, hPu, -, hPk⟩ := hP
  obtain ⟨-, -, hP'u, -, hP'k⟩ := hP'
  beta_reduce at hPu hP'u hPk hP'k
  obtain ⟨huA, hu0, huiA⟩ := hPu i
  obtain ⟨hu'A, hu'0, hu'iA⟩ := hP'u i
  have hKum : ∀ s ∈ Hm l A m, KumVal (l := l) n (ζ n) (pv (P i) (ζ m) * (pv (P' i) (ζ m))⁻¹) s 0 := by
    intro s hs
    have hs' := hs
    unfold Hm at hs'
    obtain ⟨hsI, hsc⟩ := Subgroup.mem_inf.mp hs'
    rw [MonoidHom.mem_ker] at hsc
    haveI : ∀ i : ℕ, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => ⟨⟨ζ i, (hζ i).1⟩, inferInstance⟩
    have hfix : s (ζ n) = ζ n := fix_of_cycMod hnm hsc (hζ n).1.pow_eq_one
    obtain ⟨k, hk, hkZ⟩ := hPk s hsI hsc hfix
    obtain ⟨k', hk', hk'Z⟩ := hP'k s hsI hsc hfix
    have hkk : k i = k' i := coord_eq β k k' hkZ hk'Z i
    have hKA := pKumAlg l hl2 Ω A hA ζ hζ m n hnm s hs
    have hinv := (hKA.1 _ _ _ _ (hk' i) (hk' i)).2.1
    have hmul := (hKA.1 _ _ _ _ (hk i) hinv).1
    rw [hkk, add_neg_cancel] at hmul
    exact hmul
  obtain ⟨v, hv, hvfix⟩ := pKumTriv l hl2 Ω A hA ζ hζ m n hnm _ (mul_ne_zero hu0 (inv_ne_zero hu'0)) hKum
  have hvA : v ∈ A := mem_of_pow_mem A hlN (by rw [hv]; exact mul_mem huA hu'iA)
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, zero_pow hlN] at hv
    exact mul_ne_zero hu0 (inv_ne_zero hu'0) hv.symm
  have hviA : v⁻¹ ∈ A := mem_of_pow_mem A hlN (by
    rw [inv_pow, hv, mul_inv, inv_inv]
    exact mul_mem huiA hu'A)
  obtain ⟨Q, hQ⟩ := pPolyEx l hl2 Ω A hA ζ hζ m v hvA hvfix
  have hQu : pv Q (ζ m) ∈ A ∧ pv Q (ζ m) ≠ 0 ∧ (pv Q (ζ m))⁻¹ ∈ A := by
    rw [hQ]
    exact ⟨hvA, hv0, hviA⟩
  have heq : pv (P i) (ζ m) = pv (P' i) (ζ m) * pv Q (ζ m) ^ l ^ n := by
    rw [hQ, hv, mul_comm (pv (P i) (ζ m)), ← mul_assoc, mul_inv_cancel₀ hu'0, one_mul]
  refine ⟨⟨Q, hQu, heq⟩, ?_⟩
  have hWD := pWD l hl2 Ω A hA j Φ ζ hζ m hm
  have hUP := (hWD (P i)).2 ⟨huA, hu0, huiA⟩
  have hUP' := (hWD (P' i)).2 ⟨hu'A, hu'0, hu'iA⟩
  have hUQ := (hWD Q).2 hQu
  have hpv : pv (P i - P' i * Q ^ l ^ n) (ζ m) = pv (P i) (ζ m) - pv (P' i) (ζ m) * pv Q (ζ m) ^ l ^ n := by
    simp only [pv, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
  have hz : pv (P i - P' i * Q ^ l ^ n) (ζ m) = 0 := by
    rw [hpv, ← heq, sub_self]
  have h0 := (hWD (P i - P' i * Q ^ l ^ n)).1 hz
  rw [ser_rel] at h0
  have hLC : LC l m (m - 1) (Φ.ser (P i)) (Φ.ser (P' i) * Φ.ser Q ^ l ^ n) := by
    unfold LC
    rw [← map_sub, h0]
    exact Ideal.zero_mem _
  have hD := pDlogCmp Φ.R l m n (m - 1) hm _ _ _ hUP hUP' hUQ hLC
  rwa [min_self] at hD
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.IsUnitNat
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7

section
variable {R : Type} [CommRing R]

private theorem sb_one_add (b : ℕ) : sb (R := R) b (1 + PowerSeries.X) = (1 + PowerSeries.X) ^ b := by
  rw [map_add (f := _), map_one, sb, PowerSeries.substAlgHom_X]; ring

private theorem sb_C (b : ℕ) (a : R) : sb b (PowerSeries.C a : PowerSeries R) = PowerSeries.C a :=
  (sb (R := R) b).commutes a

private theorem sb_eval₂ (b : ℕ) (P : Polynomial R) :
    sb b (P.eval₂ PowerSeries.C (1 + PowerSeries.X)) =
      (Polynomial.expand R b P).eval₂ PowerSeries.C (1 + PowerSeries.X) := by
  induction P using Polynomial.induction_on' with
  | add f g hf hg => simp only [Polynomial.eval₂_add, map_add (f := _), hf, hg]
  | monomial n a =>
    rw [Polynomial.expand_monomial, Polynomial.eval₂_monomial, Polynomial.eval₂_monomial, map_mul, map_pow,
      sb_one_add, sb_C, ← pow_mul, mul_comm b n]

private theorem map_sb' {S : Type} [CommRing S] (τ : R →+* S) (b : ℕ) (h : PowerSeries R) :
    PowerSeries.map τ (sb b h) = sb b (PowerSeries.map τ h) := by
  unfold sb
  rw [PowerSeries.coe_substAlgHom, PowerSeries.coe_substAlgHom]
  refine Eq.trans (PowerSeries.map_subst (hasSubst_pow (R := R) b) (h := τ) h) ?_
  congr 1
  change PowerSeries.map τ _ = _
  simp

private theorem dd_sb (b : ℕ) (hb : b ≠ 0) (f : PowerSeries R) :
    dd (sb b f) = (b : PowerSeries R) * sb b (dd f) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
  unfold dd
  rw [map_mul, sb_one_add]
  unfold sb
  rw [PowerSeries.coe_substAlgHom, PowerSeries.derivative_subst (hasSubst_pow (R := R) _)]
  simp only [map_sub, Derivation.leibniz_pow, map_add (f := _), Derivation.map_one_eq_zero, PowerSeries.derivative_X,
    smul_eq_mul, nsmul_eq_mul, Nat.succ_sub_one, Nat.succ_eq_add_one]
  ring

private theorem dl_sb (b : ℕ) (hb : b ≠ 0) (f : PowerSeries R) (hf : IsUnit f) :
    dl (sb b f) = (b : PowerSeries R) * sb b (dl f) := by
  obtain ⟨u, rfl⟩ := hf
  unfold dl
  have h1 : Ring.inverse (sb b (u : PowerSeries R)) = sb b ((u⁻¹ : (PowerSeries R)ˣ) : PowerSeries R) := by
    have := Ring.inverse_unit (Units.map (sb (R := R) b : PowerSeries R →* PowerSeries R) u)
    simpa using this
  rw [dd_sb b hb, h1, Ring.inverse_unit, map_mul, mul_assoc]

private theorem isUnit_nat {l : ℕ} [Fact l.Prime] (b : ℕ) (hb : ¬ l ∣ b) : IsUnit (b : ℤ_[l]) := by
  rw [PadicInt.isUnit_iff]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hb ?_)
  have : ‖((b : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
  exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd (b : ℤ)).1 this

private theorem lc_sb {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] R] (b : ℕ) (hb : ¬ l ∣ b) (m n : ℕ) (f g : PowerSeries R)
    (h : LC l m n f g) : LC l m n ((b : PowerSeries R) * sb b f) ((b : PowerSeries R) * sb b g) := by
  obtain ⟨u, hu⟩ := isUnit_nat b hb
  unfold LC at h ⊢
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
  have h2 := congrArg (levAct (R := R) l m u) hy
  rw [map_sub, levAct_ev, levAct_ev, hu, sbp_nat, map_mul, map_pow, map_natCast] at h2
  rw [map_mul, map_mul, ← mul_sub, ← h2]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))

end

end UpperTheory.Kd.C7

theorem UpperTheory.Kd.C7.pRepTr :
    UpperTheory.Kd.C7.SRepTr := by
  intro l _ hl Ω _ _ _ A hA j Φ c β ζ hζ Z hZ b hb D hD
  have hb0 : b ≠ 0 := by rintro rfl; exact hb (dvd_zero l)
  have h1 : Rep Φ β ζ (fun r s x => (b : Qbar l) * tr b hb Z r s x)
      (fun i => (b : PowerSeries Φ.R) * sb b (D i)) := by
    obtain ⟨c₁, m₁, H⟩ := hD
    refine ⟨c₁, max m₁ 1, fun m hm => ?_⟩
    obtain ⟨P, hP, hL⟩ := H m (le_of_max_le_left hm)
    refine ⟨_, pPresTr l hl Ω A hA c β ζ hζ Z hZ b hb m _ P hP, fun i => ?_⟩
    have hu : IsUnit (Φ.ser (P i)) :=
      (pWD l hl Ω A hA j Φ ζ hζ m (le_of_max_le_right hm) (P i)).2 (hP.2.2.1 i)
    have e1 : Φ.ser (Polynomial.expand (R0 A) b (P i)) = sb b (Φ.ser (P i)) := by
      unfold Fr.ser
      rw [sb_eval₂, Polynomial.map_expand]
    have e2 : Φ.tw m ((b : PowerSeries Φ.R) * sb b (D i)) = (b : PowerSeries Φ.R) * sb b (Φ.tw m (D i)) := by
      unfold Fr.tw
      rw [map_mul, map_natCast, map_sb']
    rw [e1, e2, dl_sb b hb0 _ hu]
    exact lc_sb b hb _ _ _ _ (hL i)
  obtain ⟨u, hu⟩ := isUnit_nat (l := l) b hb
  have hw : ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * (b : ℤ_[l]) = 1 := by rw [← hu, Units.inv_mul]
  generalize ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) = w at hw
  have h2 := pRepSmul l hl Ω A hA j Φ c β ζ hζ _ _ (algebraMap ℤ_[l] c.O w) h1
  convert (preTransparency := .reducible) h2 using 1
  · funext r s x
    have : ((algebraMap ℤ_[l] c.O w : c.O) : PadicAlgCl l) * (b : Qbar l) = 1 := by
      have := congrArg (algebraMap ℤ_[l] (PadicAlgCl l)) hw
      rw [map_mul, map_natCast, map_one] at this
      exact this
    rw [← mul_assoc, this, one_mul]
  · funext i
    have hm : β.mat (algebraMap ℤ_[l] c.O w) = Matrix.diagonal fun _ => w := by
      unfold Bas.mat
      rw [AlgHom.commutes, Matrix.algebraMap_eq_diagonal]
      rfl
    have h3 : PowerSeries.C (algebraMap ℤ_[l] Φ.R w) * (b : PowerSeries Φ.R) = 1 := by
      have := congrArg (fun z => PowerSeries.C (algebraMap ℤ_[l] Φ.R z)) hw
      simpa using this
    unfold Fr.act
    rw [hm, Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq, ← mul_assoc, h3, one_mul]
    · intro k _ hk
      rw [Matrix.diagonal_apply_ne _ hk.symm]; simp
    · intro h; exact absurd (Finset.mem_univ i) h
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.ExistsTau
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem div_mem_of {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (A : ValuationSubring Ω)
    (t : G ℚ Ω) (ht : ∀ x ∈ A, t x ∈ A) (u : Ω) (hu : u ≠ 0) : u / t u ∈ A ∧ t u / u ∈ A := by
  have hfin : ∃ N : ℕ, (t ^ (N + 1)) u = u := by
    have hint : IsIntegral ℚ u := Algebra.IsIntegral.isIntegral u
    have hf : ((minpoly ℚ u).rootSet Ω).Finite := Polynomial.rootSet_finite _ _
    have hm : ∀ k : ℕ, (t ^ k) u ∈ (minpoly ℚ u).rootSet Ω := fun k => by
      rw [Polynomial.mem_rootSet]
      refine ⟨minpoly.ne_zero hint, ?_⟩
      rw [Polynomial.aeval_algEquiv]
      simp
    obtain ⟨i, j, hij, he⟩ := hf.exists_lt_map_eq_of_forall_mem hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    refine ⟨d, ?_⟩
    rw [add_assoc, pow_add, AlgEquiv.mul_apply] at he
    exact ((t ^ i).injective he).symm
  obtain ⟨N, hN⟩ := hfin
  have hne : ∀ k : ℕ, (t ^ k) u ≠ 0 := fun k => (map_ne_zero _).2 hu
  have htu : t u ≠ 0 := (map_ne_zero _).2 hu
  have hs : ∀ k : ℕ, (t ^ (k + 1)) u = t ((t ^ k) u) := fun k => by rw [pow_succ', AlgEquiv.mul_apply]
  rcases A.mem_or_inv_mem (t u / u) with h | h
  · have key : ∀ k : ℕ, (t ^ k) u / u ∈ A := by
      intro k
      induction k with
      | zero => simp [hu, A.one_mem]
      | succ k ih =>
        have := A.mul_mem _ _ (ht _ ih) h
        rwa [map_div₀, div_mul_div_cancel₀ htu, ← hs] at this
    have := ht _ (key N)
    rw [map_div₀, ← hs, hN] at this
    exact ⟨this, h⟩
  · rw [inv_div] at h
    have key : ∀ k : ℕ, u / (t ^ k) u ∈ A := by
      intro k
      induction k with
      | zero => simp [hu, A.one_mem]
      | succ k ih =>
        have := A.mul_mem _ _ h (ht _ ih)
        rwa [map_div₀, div_mul_div_cancel₀ htu, ← hs] at this
    have := ht _ (key N)
    rw [map_div₀, ← hs, hN] at this
    exact ⟨h, this⟩

private theorem cg_coord {l : ℕ} [Fact l.Prime] {c : Coef l} (β : Bas c) (m : ℕ) (w : c.O) :
    Cg m (w : PadicAlgCl l) (∑ i, β.val i * ((PadicInt.toZModPow m (β.e.repr w i)).val : Qbar l)) := by
  have h1 := ((pBasEx l c).2 β).1
  have hw : (w : PadicAlgCl l) = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr w i) := by
    conv_lhs => rw [← β.e.sum_repr w]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]; rfl
  unfold Cg
  rw [hw, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
  have h2 : β.e.repr w i - ((PadicInt.toZModPow m (β.e.repr w i)).val : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ m} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
    simp
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 h2
  have h3 := congrArg (algebraMap ℤ_[l] (PadicAlgCl l)) he
  rw [RingHom.map_sub, map_natCast, map_mul, map_pow, map_natCast] at h3
  rw [← mul_sub, ← h3, norm_mul, norm_mul]
  have h4 : ‖algebraMap ℤ_[l] (PadicAlgCl l) e‖ ≤ 1 := by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), norm_algebraMap']
    exact e.2
  calc _ ≤ 1 * (1 * ‖((l : ℕ) : Qbar l) ^ m‖) := by gcongr; exact h1 i
    _ = _ := by ring

private theorem exists_tau (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : OverL l A) (b : ℕ) (hb : ¬ l ∣ b) (m : ℕ) :
    ∃ τ ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m τ = un b hb m := by
  have hu : IsUnit (b : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hb)
  obtain ⟨τ, hτ, he⟩ := (pFrobEx l hl Ω A hA).2.2 hu.unit
  refine ⟨τ, hτ, Units.ext ?_⟩
  have : ((cycMod ℚ Ω l m τ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)) = PadicInt.toZModPow m ((cycZ ℚ Ω l τ : ℤ_[l]ˣ) : ℤ_[l]) := rfl
  rw [this, he]
  simp [un]

theorem UpperTheory.Kd.C7.pKumEx :
    UpperTheory.Kd.C7.SKumEx := by
  classical
  intro l _ hl Ω _ _ _ A hA c β ζ hζ Z hZ hC b hb
  refine ⟨0, 0, fun m _ => ?_⟩
  rw [Nat.sub_zero]
  haveI : NeZero (l : Ω) := by
    haveI : CharZero Ω := algebraRat.charZero Ω
    exact ⟨Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨τ, hτ, hτb⟩ := exists_tau l hl Ω A hA b hb m
  obtain ⟨U, hU, hUZ⟩ := hC m m
  let w : G ℚ Ω → c.O := fun s => if h : s ∈ Ine (F := ℚ) A then ⟨Z m s 1, hZ.int m s h 1⟩ else 0
  have hw : ∀ s ∈ Ine (F := ℚ) A, (w s : PadicAlgCl l) = Z m s 1 := fun s hs => by simp only [w, dif_pos hs]
  let χ : Fin β.d → G ℚ Ω → ZMod (l ^ m) := fun i s => PadicInt.toZModPow m (β.e.repr (w s) i)
  have hex : ∀ i, ∃ u : Ω, u ≠ 0 ∧ (∀ s ∈ Hm l A m, s u = u) ∧
      ∀ s ∈ Hm l A m, KumVal (l := l) m (ζ m) u s (χ i s) := by
    intro i
    refine GlobalTheory.T.exists_kummer_element_fixed_field_closed_subgroup l Ω m (Hm l A m) (GlobalTheory.T.isClosed_inertia_cyclotomic_kernel l Ω A m) (ζ m) (hζ m).1
      (fun s hs => fix_of_cycMod le_rfl hs.2 (hζ m).1.pow_eq_one) (χ i) (fun s hs t ht => ?_) U hU (fun s hs hsU => ?_)
    · have e : w (s * t) = w s + w t := by
        apply Subtype.ext
        have h1 : cycMod ℚ Ω l m s = 1 := hs.2
        rw [Subalgebra.coe_add, hw _ (mul_mem hs.1 ht.1), hw _ hs.1, hw _ ht.1, hZ.coc m s hs.1 t ht.1, h1, inv_one, mul_one]
      simp only [χ, e, map_add (f := _), Finsupp.add_apply]
    · obtain ⟨y, hy⟩ := ((pBasEx l c).2 β).2.2.1 m (w s) (by rw [hw s hs.1]; exact hUZ s hsU hs.1 1)
      have e : w s = ((l : ℤ_[l]) ^ m) • y := by rw [hy, Algebra.smul_def, map_pow, map_natCast]
      simp only [χ, e, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
      rw [← Nat.cast_pow, ZMod.natCast_self, zero_mul]
  choose u hu0 hufix huk using hex
  have hconj := fun s hs => pConj l hl Ω A hA c Z hZ m s hs τ⁻¹ (inv_mem hτ)
  simp only [inv_inv] at hconj
  have hun := fun i => div_mem_of A τ (fun x hx => (apply_mem_iff_of_mem_Dec (Ine_le_Dec A hτ) x).2 hx) (u i) (hu0 i)
  have hP : ∀ i, ∃ P : Polynomial (R0 A), pv P (ζ m) = u i / τ (u i) := by
    intro i
    refine pPolyEx l hl Ω A hA ζ hζ m _ (hun i).1 fun s hs => ?_
    have h1 := congrArg τ (hufix i _ (hconj s hs).1)
    rw [← AlgEquiv.mul_apply, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, AlgEquiv.mul_apply] at h1
    rw [map_div₀, h1, hufix i s hs]
  choose P hP using hP
  refine ⟨P, (hζ m).1, le_rfl, fun i => ?_, ((pBasEx l c).2 β).1, fun s hs hc _ => ?_⟩
  · simp only [hP, inv_div]
    exact ⟨(hun i).1, div_ne_zero (hu0 i) ((map_ne_zero _).2 (hu0 i)), (hun i).2⟩
  · have hH : s ∈ Hm l A m := ⟨hs, hc⟩
    obtain ⟨hs', hZ'⟩ := hconj s hH
    refine ⟨fun i => PadicInt.toZModPow m (β.e.repr (w s - (b : ℤ_[l]) • w (τ⁻¹ * s * τ)) i), fun i => ?_, ?_⟩
    · have k1 := (pKumAlg l hl Ω A hA ζ hζ m m le_rfl _ hs').2.2 (τ (u i)) (χ i (τ⁻¹ * s * τ)) τ (by
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]; exact huk i _ hs')
      rw [show τ * (τ⁻¹ * s * τ) * τ⁻¹ = s by group, hτb] at k1
      have a1 := (pKumAlg l hl Ω A hA ζ hζ m m le_rfl _ hH).1
      have k2 := (a1 _ _ _ _ (huk i s hH) (a1 _ _ _ _ k1 k1).2.1).1
      simp only [hP, div_eq_mul_inv]
      convert k2 using 1
      simp [χ, un, sub_eq_add_neg]
    · have := cg_coord β m (w s - (b : ℤ_[l]) • w (τ⁻¹ * s * τ))
      convert this using 1
      rw [Subalgebra.coe_sub, Subalgebra.coe_smul, hw s hs, hw _ hs'.1, hZ', map_inv, inv_inv, hτb, Algebra.smul_def,
        map_natCast]
      rfl
end
