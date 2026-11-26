module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.WeightWLet
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.IoBlockSupported
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.CharZeroOfW
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SymVarInlFst
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.MemIntPolOfCoeff

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SymbolFormOfOrthogonality
section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FactorialExponentEqProd
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory MvPolynomial

theorem fact_multinomial_le (p : ℕ) {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℕ) :
    (Nat.multinomial s f).factorization p ≤ s.card * Nat.log p (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Nat.multinomial_insert ha, Nat.factorization_mul (Nat.choose_pos (Nat.le_add_right _ _)).ne'
      (Nat.multinomial_pos _ _).ne', Finsupp.add_apply, Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    have h1 := Nat.factorization_choose_le_log (p := p) (n := f a + ∑ i ∈ s, f i) (k := f a)
    have h2 : Nat.log p (∑ i ∈ s, f i) ≤ Nat.log p (f a + ∑ i ∈ s, f i) := Nat.log_mono_right (Nat.le_add_left _ _)
    calc _ ≤ Nat.log p (f a + ∑ i ∈ s, f i) + s.card * Nat.log p (f a + ∑ i ∈ s, f i) :=
          add_le_add h1 (ih.trans (Nat.mul_le_mul_left _ h2))
      _ = (s.card + 1) * Nat.log p (f a + ∑ i ∈ s, f i) := by ring

theorem pow_div_mem {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hp : p.Prime)
    (S : UniformizedDVR p O) (M κ : ℕ) (hM : M ≠ 0) (h : M.factorization p ≤ κ) :
    ∃ y : O, (p : KK O) ^ κ / (M : KK O) = algebraMap O (KK O) y := by
  have := dvr_fraction_field_char_zero hp S
  set v := M.factorization p with hv
  set M' := M / p ^ v with hM'
  have hMM : p ^ v * M' = M := Nat.ordProj_mul_ordCompl_eq_self M p
  have hnd : ¬ p ∣ M' := Nat.not_dvd_ordCompl hp hM
  obtain ⟨uu, hu⟩ := natCast_isUnit_of_coprime hp S M' hnd
  have hy : (↑(uu⁻¹) : O) * (M' : O) = 1 := by rw [← hu]; exact Units.inv_mul uu
  have hK : algebraMap O (KK O) (↑(uu⁻¹) : O) * (M' : KK O) = 1 := by
    rw [← map_natCast (algebraMap O (KK O)), ← map_mul, hy, map_one]
  have hne : (M : KK O) ≠ 0 := Nat.cast_ne_zero.2 hM
  refine ⟨(p : O) ^ (κ - v) * ↑(uu⁻¹), ?_⟩
  rw [div_eq_iff hne]
  have hMK : (M : KK O) = (p : KK O) ^ v * (M' : KK O) := by rw [← hMM]; push_cast; rfl
  have hpow : (p : KK O) ^ κ = (p : KK O) ^ (κ - v) * (p : KK O) ^ v := by rw [← pow_add, Nat.sub_add_cancel h]
  simp only [map_mul, map_pow, map_natCast]
  rw [hMK, hpow]
  linear_combination (-((p : KK O) ^ (κ - v) * (p : KK O) ^ v)) * hK

theorem factorial_exponent_eq_prod {ι : Type} [Fintype ι] {k : ℕ} (μ : ι × Fin k →₀ ℕ) :
    expFact μ = ∏ x : ι, ∏ c : Fin k, (μ (x, c)).factorial := by
  rw [expFact, Finsupp.prod_fintype _ _ (fun _ => rfl), Fintype.prod_prod_type]

theorem tensor_factorial_integral {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hp : p.Prime)
    (S : UniformizedDVR p O) {n' : ℕ} (m : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ)
    (μ : (TT × Bool) × Fin (m + 1) →₀ ℕ) (hμ : ∀ x, multideg μ x = hhDegs TT aT bT x) :
    ∃ y : O, zTen (KK O) p m TT aT bT * (expFact μ : KK O) = algebraMap O (KK O) y := by
  classical
  have := dvr_fraction_field_char_zero hp S
  set M : ℕ := ∏ x : TT × Bool, Nat.multinomial Finset.univ (fun c : Fin (m + 1) => μ (x, c)) with hMdef
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => (Nat.multinomial_pos _ _).ne'
  have hEM : expFact μ * M = ∏ x : TT × Bool, (hhDegs TT aT bT x).factorial := by
    rw [factorial_exponent_eq_prod, hMdef, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Nat.multinomial_spec, ← hμ x]
    rfl
  have hfac : M.factorization p ≤ kapZ p m TT aT bT := by
    rw [hMdef, Nat.factorization_prod (fun x _ => (Nat.multinomial_pos _ _).ne'), Finsupp.finsetSum_apply]
    unfold kapZ
    refine Finset.sum_le_sum fun x _ => ?_
    have := fact_multinomial_le p (Finset.univ : Finset (Fin (m + 1))) (fun c => μ (x, c))
    rw [Finset.card_univ, Fintype.card_fin] at this
    rw [← hμ x]
    exact this
  obtain ⟨y, hy⟩ := pow_div_mem hp S M _ hM0 hfac
  refine ⟨y, ?_⟩
  rw [← hy]
  unfold zTen
  have hE0 : (expFact μ : KK O) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    intro h0
    rw [h0, zero_mul] at hEM
    exact (Finset.prod_ne_zero_iff.2 fun x _ => Nat.factorial_ne_zero _) hEM.symm
  have hMK : (M : KK O) ≠ 0 := Nat.cast_ne_zero.2 hM0
  have hcast : (∏ x : TT × Bool, ((hhDegs TT aT bT x).factorial : KK O)) = (expFact μ : KK O) * (M : KK O) := by
    rw [← Nat.cast_mul, hEM]
    push_cast
    rfl
  rw [hcast]
  field_simp

theorem intAt : IntAt := by
  intro p O _ _ _ hp S w n' m TT aT bT P hP Q i hPi hQ
  have hsup : ∀ μ ∈ P.support, ∀ x, multideg μ x = hhDegs TT aT bT x := by
    intro μ hμ
    have := ((mem_restrictSupport_iff _).1 hP) (Finset.mem_coe.2 hμ)
    exact this
  unfold fock
  rw [Finset.mul_sum]
  refine Finset.sum_induction _ (fun x => ∃ y : O, x = algebraMap O (KK O) (w ^ i * y)) ?_ ⟨0, by simp⟩ ?_
  · rintro _ _ ⟨y, rfl⟩ ⟨y', rfl⟩
    exact ⟨y + y', by rw [← map_add (f := _)]; congr 1; ring⟩
  · intro μ hμ
    obtain ⟨c, hc⟩ := hPi μ
    obtain ⟨c', hc'⟩ := hQ μ
    obtain ⟨y, hy⟩ := tensor_factorial_integral hp S m TT aT bT μ (hsup μ hμ)
    refine ⟨c * c' * y, ?_⟩
    rw [hc, hc']
    have : zTen (KK O) p m TT aT bT * (algebraMap O (KK O) (w ^ i * c) * algebraMap O (KK O) c' * (expFact μ : KK O)) =
        algebraMap O (KK O) (w ^ i * c) * algebraMap O (KK O) c' * (zTen (KK O) p m TT aT bT * (expFact μ : KK O)) := by
      ring
    rw [this, hy, ← map_mul, ← map_mul]
    congr 1
    ring

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem symPolAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X)
    (hO : OPlusAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : SymPolAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  classical
  intro X _ O _ _ hD1 hH hc mm β hβ s hs
  have St := hstd X hD1 hH hc
  unfold Pol
  rw [mem_restrictSupport_iff]
  intro μ hμ x
  have hwh : IsWeightedHomogeneous (wLet X x) (symFam (KK O) X.p C0 CE1 CE2 X β s)
      (∑ j, TD C0 CE1 CE2 X j (β j) (wLet X x)) :=
    IsWeightedHomogeneous.prod _ _ _ (fun j _ => ioBlock_wh C0 CE1 CE2 X j O mm (β j) (wLet X x) (fun _ _ _ => rfl)
      (fun _ => rfl) rfl (s j) (hs j))
  have h1 := hwh (mem_support_iff.1 (Finset.mem_coe.1 hμ))
  rw [weight_wLet] at h1
  rw [h1, Finset.sum_congr rfl fun j _ => TD_wLet C0 CE1 CE2 X j x (β j) (hβ j) (hO X hD1 hH hc j (β j) (hβ j)),
    ← natPartSum X.TT St.seg2 (fun s => if s = x.1.val then hhDegs X.TT X.aT X.bT x else 0), Finset.sum_ite_eq',
    if_pos x.1.2]

def RestOPlus : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => OPlusAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restSymPol_of (h : RestOPlus) : RestSymPol := by
  refine TransportedAlt.mono ?_ (thr_std.and h)
  rintro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ⟨⟨_, hstd⟩, hO⟩
  exact symPolAt_of hstd hO

theorem symbol_form_of_orthogonality (hB : RestBlockForm) (h1 : ∀ C0 CE1 CE2, OrthAt C0 CE1 CE2) (h3 : RestOPlus) : RestForm :=
  restForm_of' hB h1 prodAt (restSymPol_of h3) intAt numAt zProdAt

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LeadingExponentHomogeneous
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory MvPolynomial

theorem nat_split {O : Type} [CommRing O] [IsLocalRing O] {p : ℕ} (hp : p.Prime) (hpO : ¬ IsUnit (p : O)) {n : ℕ}
    (hn : n ≠ 0) : ∃ u : Oˣ, (n : O) = (p : O) ^ (n.factorization p) * u := by
  have hcop : Nat.Coprime (ordCompl[p] n) p := (Nat.coprime_ordCompl hp hn).symm
  have hunit : IsUnit ((ordCompl[p] n : ℕ) : O) := by
    by_contra hu
    have h1 := Nat.gcd_eq_gcd_ab (ordCompl[p] n) p
    rw [hcop] at h1
    have h2 : (1 : O) = ((ordCompl[p] n : ℕ) : O) * ((Nat.gcdA (ordCompl[p] n) p : ℤ) : O) +
        (p : O) * ((Nat.gcdB (ordCompl[p] n) p : ℤ) : O) := by
      have := congrArg (Int.cast : ℤ → O) h1
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_one, Int.cast_one] at this
      exact this
    have hm1 : ((ordCompl[p] n : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := hu
    have hm2 : (p : O) ∈ IsLocalRing.maximalIdeal O := hpO
    have h3 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [h2]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hm1) (Ideal.mul_mem_right _ _ hm2)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec, ← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]

theorem kap_transport {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} (hp : p.Prime) {w : O}
    (hw : Irreducible w) (h2 : w ^ 2 = (p : O)) {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) (E D : ℕ)
    (hlo : B.factorization p ≤ E + A.factorization p) (hhi : E + A.factorization p ≤ D + B.factorization p) :
    ∃ κ : O, κ ≠ 0 ∧ vLEO p κ (D : ℝ) ∧ (p : O) ^ E * (A : O) = κ * (B : O) := by
  have hpO := p_not_unit hw h2
  obtain ⟨uA, huA⟩ := nat_split hp hpO hA
  obtain ⟨uB, huB⟩ := nat_split hp hpO hB
  have hp0 : (p : O) ≠ 0 := by rw [← h2]; exact pow_ne_zero _ hw.ne_zero
  set n := E + A.factorization p - B.factorization p with hn
  have h1 : (p : O) ^ n ≠ 0 := pow_ne_zero _ hp0
  have hκ : (p : O) ^ n * uA * ((uB⁻¹ : Oˣ) : O) ≠ 0 := mul_ne_zero (mul_ne_zero h1 uA.ne_zero) (Units.ne_zero _)
  refine ⟨(p : O) ^ n * uA * ((uB⁻¹ : Oˣ) : O), hκ, ?_, ?_⟩
  · rw [vLEO_iff hw h2 hκ, dvr_order_mul (mul_ne_zero h1 uA.ne_zero) (Units.ne_zero _), dvr_order_mul h1 uA.ne_zero,
      dvr_order_pow hp0, dvr_order_unit_eq_zero uA.isUnit, dvr_order_unit_eq_zero (Units.isUnit _)]
    have hv : dvrOrderNat (p : O) = 2 := by rw [← h2, dvr_order_pow hw.ne_zero, nv_irr hw]
    rw [hv]
    have : (n : ℝ) ≤ D := by exact_mod_cast (by omega : n ≤ D)
    push_cast
    linarith
  · rw [huA, huB]
    have hu : ((uB⁻¹ : Oˣ) : O) * uB = 1 := by simp
    have hpw : (p : O) ^ E * (p : O) ^ A.factorization p = (p : O) ^ n * (p : O) ^ B.factorization p := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    linear_combination (uA : O) * hpw - ((p : O) ^ n * (p : O) ^ B.factorization p * uA) * hu

section

variable (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT))

def lvW (ℓ : ℕ) : BV C0 CE1 CE2 X j → ℕ := fun v => if symLev X.p C0 CE1 CE2 X j v = ℓ then 1 else 0

def lvL (ℓ : ℕ) : Fin (2 * segS X.TT j + 1 + 1) → ℕ :=
  fun a => if symLev X.p C0 CE1 CE2 X j (Sum.inl (a, 0)) = ℓ then 1 else 0

theorem lev_balanced (ℓ : ℕ) : Balanced X.m (X.seg C0 CE1 CE2 j) (lvW C0 CE1 CE2 X j ℓ) (lvL C0 CE1 CE2 X j ℓ) := by
  refine ⟨fun a c => rfl, ?_, ?_⟩
  · intro l
    have hi := (uTop (X.seg C0 CE1 CE2 j) l).2
    have e0 : finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ)) =
        Fin.castSucc (⟨2 * (uTop (X.seg C0 CE1 CE2 j) l).val, by omega⟩ : Fin (2 * segS X.TT j + 1)) :=
      Fin.ext (Nat.min_eq_left (by omega))
    have e1 : finPos (2 * segS X.TT j + 1) (2 * (uTop (X.seg C0 CE1 CE2 j) l : ℕ) + 1) =
        Fin.castSucc (⟨2 * (uTop (X.seg C0 CE1 CE2 j) l).val + 1, by omega⟩ : Fin (2 * segS X.TT j + 1)) :=
      Fin.ext (Nat.min_eq_left (by omega))
    unfold lvW lvL
    rw [sl_Z, sl_Z, e0, e1, symbol_level_lower_letter, sl_E]
  · unfold lvW lvL
    rw [symbol_level_last, symbol_level_last, sl_U, sl_xi]

theorem lev_const (b : SegBlock (segS X.TT j) X.m) (μ μ' : BV C0 CE1 CE2 X j →₀ ℕ) (hμ : HomExp C0 CE1 CE2 X j b μ)
    (hμ' : HomExp C0 CE1 CE2 X j b μ') (f : ℕ → ℕ) :
    ∏ v, f (symLev X.p C0 CE1 CE2 X j v) ^ μ v = ∏ v, f (symLev X.p C0 CE1 CE2 X j v) ^ μ' v := by
  classical
  have key : ∀ ν : BV C0 CE1 CE2 X j →₀ ℕ, HomExp C0 CE1 CE2 X j b ν →
      ∏ v, f (symLev X.p C0 CE1 CE2 X j v) ^ ν v =
        ∏ ℓ ∈ Finset.univ.image (symLev X.p C0 CE1 CE2 X j), f ℓ ^ (OmB X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j)
          (segAPlus X.TT X.aT j) b (lvW C0 CE1 CE2 X j ℓ) (lvL C0 CE1 CE2 X j ℓ)) := by
    intro ν hν
    rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image (symLev X.p C0 CE1 CE2 X j))
      (g := symLev X.p C0 CE1 CE2 X j) (fun v _ => Finset.mem_image_of_mem _ (Finset.mem_univ v))]
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [← hν _ _ (lev_balanced C0 CE1 CE2 X j ℓ), ← Finset.prod_pow_eq_pow_sum, Finset.prod_filter]
    refine Finset.prod_congr rfl fun v _ => ?_
    unfold lvW
    split_ifs with h
    · rw [h, mul_one]
    · rw [mul_zero, pow_zero]
  rw [key μ hμ, key μ' hμ']

def mu0F (b : SegBlock (segS X.TT j) X.m) : BV C0 CE1 CE2 X j → ℕ
  | Sum.inl (a, c) => if c = 0 then Fin.lastCases (motive := fun _ => ℕ) (X.seg C0 CE1 CE2 j).bPlus
      (fun a' => (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a') a else 0
  | Sum.inr (l, false) => Fin.lastCases (motive := fun _ => ℕ) (segAPlus X.TT X.aT j - b.oPlus)
      (fun l' => coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l') -
        b.o (uTop (X.seg C0 CE1 CE2 j) l')) l
  | Sum.inr (_, true) => 0

def mu0 (b : SegBlock (segS X.TT j) X.m) : BV C0 CE1 CE2 X j →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (mu0F C0 CE1 CE2 X j b)

theorem leading_exponent_homogeneous (b : SegBlock (segS X.TT j) X.m) : HomExp C0 CE1 CE2 X j b (mu0 C0 CE1 CE2 X j b) := by
  classical
  intro ω ωL hB
  obtain ⟨h1, -, -⟩ := hB
  show ∑ v, mu0F C0 CE1 CE2 X j b v * ω v = _
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  have a1 : ∀ a : Fin (2 * segS X.TT j + 1 + 1), ∑ c : Fin X.m, mu0F C0 CE1 CE2 X j b (Sum.inl (a, c)) * ω (Sum.inl (a, c)) =
      Fin.lastCases (motive := fun _ => ℕ) (X.seg C0 CE1 CE2 j).bPlus
        (fun a' => (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a') a * ωL a := by
    intro a
    rw [Finset.sum_eq_single (0 : Fin X.m)]
    · simp only [mu0F, if_true, h1]
    · intro c _ hc
      simp only [mu0F, if_neg hc, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have a2 : ∀ l : Fin ((X.seg C0 CE1 CE2 j).t + 1), ∑ β : Bool, mu0F C0 CE1 CE2 X j b (Sum.inr (l, β)) * ω (Sum.inr (l, β)) =
      Fin.lastCases (motive := fun _ => ℕ) (segAPlus X.TT X.aT j - b.oPlus)
        (fun l' => coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l') -
          b.o (uTop (X.seg C0 CE1 CE2 j) l')) l * ω (Sum.inr (l, false)) := by
    intro l
    rw [Fintype.sum_bool]
    simp only [mu0F, zero_mul, zero_add]
  rw [Finset.sum_congr rfl fun a _ => a1 a, Finset.sum_congr rfl fun l _ => a2 l]
  have s1 : ∑ a : Fin (2 * segS X.TT j + 1 + 1), Fin.lastCases (motive := fun _ => ℕ) (X.seg C0 CE1 CE2 j).bPlus
        (fun a' => (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a') a * ωL a =
      ∑ a' : Fin (2 * segS X.TT j + 1), (segChain X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b).deg a' *
        ωL (Fin.castSucc a') + (X.seg C0 CE1 CE2 j).bPlus * ωL (Fin.last _) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  have s2 : ∑ l : Fin ((X.seg C0 CE1 CE2 j).t + 1), Fin.lastCases (motive := fun _ => ℕ) (segAPlus X.TT X.aT j - b.oPlus)
        (fun l' => coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l') -
          b.o (uTop (X.seg C0 CE1 CE2 j) l')) l * ω (Sum.inr (l, false)) =
      ∑ l' : Fin (X.seg C0 CE1 CE2 j).t, (coarseA X.p (X.seg C0 CE1 CE2 j) b (uTop (X.seg C0 CE1 CE2 j) l') -
          b.o (uTop (X.seg C0 CE1 CE2 j) l')) * ω (Sum.inr (Fin.castSucc l', false)) +
        (segAPlus X.TT X.aT j - b.oPlus) * ω (Sum.inr (Fin.last _, false)) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [s1, s2]
  unfold OmB
  ring

def PhiB (b : SegBlock (segS X.TT j) X.m) : ℕ :=
  Rblk C0 CE1 CE2 X j b * ∏ v : BV C0 CE1 CE2 X j, (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial *
    (symLev X.p C0 CE1 CE2 X j v).factorial ^ (mu0 C0 CE1 CE2 X j b v)

end

def KapNumAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      (facSeg X j).factorization X.p ≤ (X.m + 1) * lgSeg X j +
          (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial).factorization X.p +
          (PhiB C0 CE1 CE2 X j b).factorization X.p ∧
      (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial).factorization X.p +
          (PhiB C0 CE1 CE2 X j b).factorization X.p ≤ lgSeg X j + (facSeg X j).factorization X.p

theorem facSeg_ne (X : Loc) (j : Fin (numSeg X.TT)) : facSeg X j ≠ 0 := by
  have : 0 < facSeg X j := by
    unfold facSeg
    positivity
  omega

theorem PhiB_ne (C0 CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m) :
    PhiB C0 CE1 CE2 X j b ≠ 0 := by
  have : 0 < PhiB C0 CE1 CE2 X j b := by
    unfold PhiB Rblk
    positivity
  omega

theorem kapAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hN : KapNumAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    KapAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  classical
  intro X _ O _ _ _ w hw h2 hD1 hH hc j b hb
  have hp : X.p.Prime := hD1.1
  have hO : CharZero O := charZero_of_w hp hw h2
  have : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))
  obtain ⟨n1, n2⟩ := hN X hD1 hH hc j b hb
  set sp := specConst X.p (X.seg C0 CE1 CE2 j) b with hsp
  have hsp0 : sp ≠ 0 := specConst_ne _ _ _
  have hc0 : (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun x _ => Nat.factorial_ne_zero _
  have hvN : padicValNat X.p (Nblk C0 CE1 CE2 X j b) =
      (∏ x : X.TT × Bool, (cdeg C0 CE1 CE2 X j b x).factorial).factorization X.p + sp.factorization X.p := by
    rw [Nat.padicValNat_def, ← Nat.factorization_def _ hp]
    unfold Nblk
    rw [Nat.factorization_mul hc0 hsp0]
    rfl
  have hBf : (facSeg X j * sp).factorization X.p = (facSeg X j).factorization X.p + sp.factorization X.p := by
    rw [Nat.factorization_mul (facSeg_ne X j) hsp0]
    rfl
  obtain ⟨κ, hκ0, hκv, hκ⟩ := kap_transport hp hw h2 (PhiB_ne C0 CE1 CE2 X j b) (mul_ne_zero (facSeg_ne X j) hsp0)
    ((X.m + 1) * lgSeg X j + padicValNat X.p (Nblk C0 CE1 CE2 X j b)) ((X.m + 2) * lgSeg X j)
    (by rw [hBf, hvN]; omega) (by
      rw [hBf, hvN]
      have : (X.m + 2) * lgSeg X j = (X.m + 1) * lgSeg X j + lgSeg X j := by ring
      omega)
  refine ⟨κ, hκ0, hκv, ?_⟩
  intro μ hμ
  have hΦ : Rblk C0 CE1 CE2 X j b * ∏ v : BV C0 CE1 CE2 X j,
      (baseExp C0 CE1 CE2 X j b (symVar C0 CE1 CE2 X j v)).factorial * (symLev X.p C0 CE1 CE2 X j v).factorial ^ (μ v) =
      PhiB C0 CE1 CE2 X j b := by
    unfold PhiB
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      lev_const C0 CE1 CE2 X j b μ _ hμ (leading_exponent_homogeneous C0 CE1 CE2 X j b) Nat.factorial]
  have hΦK := congrArg (fun n : ℕ => (n : KK O)) hΦ
  simp only [Nat.cast_mul, Nat.cast_prod, Nat.cast_pow] at hΦK
  have hκK := congrArg (algebraMap O (KK O)) hκ
  simp only [map_mul, map_pow, map_natCast, Nat.cast_mul] at hκK
  have hf0 : (facSeg X j : KK O) ≠ 0 := Nat.cast_ne_zero.2 (facSeg_ne X j)
  unfold zSeg
  rw [mul_assoc (_ * _) _ _, hΦK, div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hf0, ← pow_add, hκK]
  ring

end Formalism.MainNotions.ColumnSystems.Pf
end
end
