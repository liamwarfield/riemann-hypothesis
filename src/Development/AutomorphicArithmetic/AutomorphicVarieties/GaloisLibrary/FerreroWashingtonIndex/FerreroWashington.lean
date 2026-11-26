module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Nonvan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.AmbCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.StickH
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SgnCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ReflOdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.EmbedDeg

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.ToKOf
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.Struct
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.DeltaBij
open UpperTheory.V.FW

private theorem crt_apply {a b : ℕ} (hab : a.Coprime b) (x : ZMod (a * b)) :
    ZMod.chineseRemainder hab x =
      (ZMod.castHom (Dvd.intro b rfl) (ZMod a) x, ZMod.castHom (Dvd.intro_left a rfl) (ZMod b) x) := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [map_intCast, map_intCast, map_intCast]
  rfl

private theorem crt_inj {a b : ℕ} (hab : a.Coprime b) (ha : a ∣ a * b) (hb : b ∣ a * b) (x y : (ZMod (a * b))ˣ)
    (h1 : ZMod.unitsMap ha x = ZMod.unitsMap ha y) (h2 : ZMod.unitsMap hb x = ZMod.unitsMap hb y) : x = y := by
  apply Units.ext
  apply (ZMod.chineseRemainder hab).injective
  rw [crt_apply, crt_apply]
  exact Prod.ext (congrArg Units.val h1) (congrArg Units.val h2)

private theorem crt_surj {a b : ℕ} (hab : a.Coprime b) (ha : a ∣ a * b) (hb : b ∣ a * b)
    (u : (ZMod a)ˣ) (v : (ZMod b)ˣ) :
    ∃ x : (ZMod (a * b))ˣ, ZMod.unitsMap ha x = u ∧ ZMod.unitsMap hb x = v := by
  let x : (ZMod (a * b))ˣ :=
    Units.map (ZMod.chineseRemainder hab).symm.toMonoidHom (MulEquiv.prodUnits.symm (u, v))
  have hx : ZMod.chineseRemainder hab (x : ZMod (a * b)) = ((u : ZMod a), (v : ZMod b)) :=
    (ZMod.chineseRemainder hab).apply_symm_apply _
  rw [crt_apply] at hx
  exact ⟨x, Units.ext (congrArg Prod.fst hx), Units.ext (congrArg Prod.snd hx)⟩

private theorem map_map {a b c : ℕ} (h1 : a ∣ b) (h2 : b ∣ c) (x : (ZMod c)ˣ) :
    ZMod.unitsMap h1 (ZMod.unitsMap h2 x) = ZMod.unitsMap (h1.trans h2) x := by
  rw [← ZMod.unitsMap_comp h1 h2]
  rfl

private theorem map_redU (l : ℕ) [Fact l.Prime] {m n : ℕ} (hmn : m ≤ n) (h : l ^ m ∣ l ^ n) (w : ℤ_[l]ˣ) :
    ZMod.unitsMap h (redU l n w) = redU l m w := by
  apply Units.ext
  exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow m n hmn) (w : ℤ_[l])

theorem UpperTheory.V.FW.deltaBij :
    ∀ (l : ℕ) [Fact l.Prime] (f n : ℕ) (h : f * l ^ ee l ∣ f * l ^ n) (h' : l ^ n ∣ f * l ^ n), f.Coprime l → ee l ≤ n → Function.Bijective ((ZMod.unitsMap h).comp (((WW l).map (redU l n)).comap (ZMod.unitsMap h')).subtype) := by
  intro l _ f n h h' hf hn
  have hen : l ^ ee l ∣ l ^ n := pow_dvd_pow l hn
  have hfe : f ∣ f * l ^ ee l := Dvd.intro _ rfl
  have hle : l ^ ee l ∣ f * l ^ ee l := Dvd.intro_left _ rfl
  have hfn : f ∣ f * l ^ n := Dvd.intro _ rfl
  constructor
  · rw [injective_iff_map_eq_one]
    rintro ⟨g, w, hw, hwg⟩ hg
    have hg' : ZMod.unitsMap h g = 1 := hg
    have h1 : redU l (ee l) w = 1 := by
      rw [← map_redU l hn hen, hwg, map_map, ← map_map hle h, hg', map_one]
    have h2 : (⟨w, hw⟩ : WW l) = 1 := (injective_iff_map_eq_one _).1 (teich l).1 _ h1
    have h3 : w = 1 := congrArg Subtype.val h2
    apply Subtype.ext
    show g = 1
    apply crt_inj (hf.pow_right n) hfn h'
    · rw [← map_map hfe h, hg', map_one, map_one]
    · rw [← hwg, h3, map_one, map_one]
  · intro u
    obtain ⟨w, hw⟩ := (teich l).2 (ZMod.unitsMap hle u)
    have hw' : redU l (ee l) w = ZMod.unitsMap hle u := hw
    obtain ⟨g, hg1, hg2⟩ := crt_surj (hf.pow_right n) hfn h' (ZMod.unitsMap hfe u) (redU l n w)
    refine ⟨⟨g, w, w.2, hg2.symm⟩, ?_⟩
    show ZMod.unitsMap h g = u
    apply crt_inj (hf.pow_right (ee l)) hfe hle
    · rw [map_map, hg1]
    · rw [map_map, ← map_map hen h', hg2, map_redU l hn, hw']
end

open UpperTheory.V.FW

private theorem ee_bd (l : ℕ) : 1 ≤ ee l ∧ ee l ≤ 2 := by
  unfold ee; split_ifs <;> omega

private theorem neg_mem_WW (l : ℕ) [hl : Fact l.Prime] : (-1 : ℤ_[l]ˣ) ∈ WW l := by
  have h2 : 2 < l ^ ee l := by
    unfold ee
    split_ifs with h
    · subst h; norm_num
    · have := hl.out.two_le
      rw [pow_one]; omega
  unfold WW
  rw [mem_rootsOfUnity]
  exact (Nat.totient_even h2).neg_one_pow

private theorem red_red (l : ℕ) [Fact l.Prime] (m n : ℕ) (hmn : m ≤ n) (w : ℤ_[l]ˣ) :
    ZMod.unitsMap (pow_dvd_pow l hmn) (redU l n w) = redU l m w := by
  ext
  simp only [ZMod.unitsMap_def, redU, Units.coe_map, MonoidHom.coe_coe]
  exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow m n hmn) (w : ℤ_[l])

theorem UpperTheory.V.FW.struct :
    ∀ (l : ℕ) [Fact l.Prime] (f n : ℕ), f.Coprime l → 2 ≤ n → ∃ (γ : (ZMod (f * l ^ n))ˣ) (p : (ZMod (f * l ^ n))ˣ →* (ZMod (f * l ^ n))ˣ), (γ : ZMod (f * l ^ n)) = 1 + f * l ^ ee l ∧ γ ^ l ^ n = 1 ∧ (Subgroup.zpowers γ).index = Nat.totient (f * l ^ ee l) ∧ (∀ g, p g ∈ Subgroup.zpowers γ) ∧ (∀ g, (g * (p g)⁻¹) ^ Nat.totient (f * l ^ ee l) = 1) ∧ p (-1) = 1 ∧ ∀ (n₀ : ℕ) (h : l ^ n₀ ∣ f * l ^ n), n₀ ≤ n → (∀ g, piQ l n₀ h (p g) = piQ l n₀ h g) ∧ piQ l n₀ h γ ^ l ^ n₀ = 1 := by
  intro l _ f n hf hn
  have hl : l.Prime := Fact.out
  have hee := ee_bd l
  have hen : ee l ≤ n := by omega
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hf
    exact hl.one_lt.ne' hf
  have hdiv : f * l ^ ee l ∣ f * l ^ n := Nat.mul_dvd_mul_left f (pow_dvd_pow l hen)
  have hdiv' : l ^ n ∣ f * l ^ n := Dvd.intro_left f rfl
  haveI : NeZero (f * l ^ n) := ⟨mul_ne_zero hf0 (pow_ne_zero _ hl.ne_zero)⟩
  haveI : NeZero (f * l ^ ee l) := ⟨mul_ne_zero hf0 (pow_ne_zero _ hl.ne_zero)⟩
  have hnil : IsNilpotent ((f : ZMod (f * l ^ n)) * (l : ZMod (f * l ^ n)) ^ ee l) := by
    refine ⟨n, ?_⟩
    have hz : ((f ^ n * l ^ (ee l * n) : ℕ) : ZMod (f * l ^ n)) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact Nat.mul_dvd_mul (dvd_pow_self f (by omega))
        (pow_dvd_pow l (Nat.le_mul_of_pos_left n (by omega)))
    rw [mul_pow, ← pow_mul]
    exact_mod_cast hz
  obtain ⟨γ, hγ⟩ := hnil.isUnit_one_add
  obtain ⟨hker, hγpow⟩ := gamGen l f n hdiv γ hf hen hγ
  have hbij := deltaBij l f n hdiv hdiv' hf hen
  let e := MulEquiv.ofBijective _ hbij
  let σ : (ZMod (f * l ^ n))ˣ →* (ZMod (f * l ^ n))ˣ :=
    (Subgroup.comap (ZMod.unitsMap hdiv') (Subgroup.map (redU l n) (WW l))).subtype.comp
      (e.symm.toMonoidHom.comp (ZMod.unitsMap hdiv))
  have hσπ : ∀ g, ZMod.unitsMap hdiv (σ g) = ZMod.unitsMap hdiv g := fun g =>
    e.apply_symm_apply (ZMod.unitsMap hdiv g)
  have hσH : ∀ x ∈ Subgroup.comap (ZMod.unitsMap hdiv') (Subgroup.map (redU l n) (WW l)),
      σ x = x := by
    intro x hx
    have h1 : ZMod.unitsMap hdiv x = e ⟨x, hx⟩ := rfl
    show ((e.symm (ZMod.unitsMap hdiv x) : _) : (ZMod (f * l ^ n))ˣ) = x
    rw [h1, e.symm_apply_apply]
  have hcard : Nat.card (ZMod (f * l ^ ee l))ˣ = (f * l ^ ee l).totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hσpow : ∀ g, σ g ^ (f * l ^ ee l).totient = 1 := by
    intro g
    have h1 : (ZMod.unitsMap hdiv g) ^ (f * l ^ ee l).totient = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    show ((e.symm (ZMod.unitsMap hdiv g) : _) : (ZMod (f * l ^ n))ˣ) ^ _ = 1
    rw [← Subgroup.coe_pow, ← map_pow, h1, map_one, Subgroup.coe_one]
  let p : (ZMod (f * l ^ n))ˣ →* (ZMod (f * l ^ n))ˣ := MonoidHom.id _ / σ
  have hp : ∀ g, p g = g / σ g := fun g => rfl
  have hQ : ∀ (n₀ : ℕ) (h : l ^ n₀ ∣ f * l ^ n), n₀ ≤ n →
      ∀ x ∈ Subgroup.comap (ZMod.unitsMap hdiv') (Subgroup.map (redU l n) (WW l)),
      piQ l n₀ h x = 1 := by
    intro n₀ h hn₀ x hx
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hx)
    have hc := DFunLike.congr_fun (ZMod.unitsMap_comp (pow_dvd_pow l hn₀) hdiv') x
    simp only [MonoidHom.comp_apply] at hc
    show (QuotientGroup.mk' _) (ZMod.unitsMap h x) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨w, hw, ?_⟩
    rw [← red_red l n₀ n hn₀ w, hwx]
    exact hc
  refine ⟨γ, p, hγ, hγpow, ?_, ?_, ?_, ?_, ?_⟩
  · have hsurj : Function.Surjective (ZMod.unitsMap hdiv) := fun y => by
      obtain ⟨x, hx⟩ := hbij.2 y
      exact ⟨x.1, hx⟩
    rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hcard]
  · intro g
    rw [← hker, MonoidHom.mem_ker, hp, map_div, hσπ, div_self']
  · intro g
    rw [hp, inv_div, mul_div_cancel]
    exact hσpow g
  · have hm : (-1 : (ZMod (f * l ^ n))ˣ) ∈
        Subgroup.comap (ZMod.unitsMap hdiv') (Subgroup.map (redU l n) (WW l)) := by
      rw [Subgroup.mem_comap, Subgroup.mem_map]
      refine ⟨-1, neg_mem_WW l, ?_⟩
      ext
      simp [redU, ZMod.unitsMap_def]
    rw [hp, hσH _ hm, div_self']
  · intro n₀ h hn₀
    refine ⟨fun g => ?_, ?_⟩
    · rw [hp, map_div, hQ n₀ h hn₀ (σ g) (e.symm (ZMod.unitsMap hdiv g)).2, div_one]
    · haveI : NeZero (l ^ n₀) := ⟨pow_ne_zero _ hl.ne_zero⟩
      have h1 : ZMod.unitsMap h γ ^ l ^ n = 1 := by rw [← map_pow, hγpow, map_one]
      have h2 : ZMod.unitsMap h γ ^ (l ^ n₀).totient = 1 := by
        rw [← ZMod.card_units_eq_totient, ← Nat.card_eq_fintype_card]
        exact pow_card_eq_one'
      obtain ⟨j, hj, hjx⟩ := (Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one h1)
      have hle : l ^ j ≤ l ^ n₀ := by
        rw [← hjx]
        exact (Nat.le_of_dvd (Nat.totient_pos.mpr (pow_pos hl.pos _))
          (orderOf_dvd_of_pow_eq_one h2)).trans (Nat.totient_le _)
      have hj0 : j ≤ n₀ := (Nat.pow_le_pow_iff_right hl.one_lt).mp hle
      have hx : ZMod.unitsMap h γ ^ l ^ n₀ = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, hjx]
        exact pow_dvd_pow l hj0
      show (QuotientGroup.mk' _) (ZMod.unitsMap h γ) ^ l ^ n₀ = 1
      rw [← map_pow, hx, map_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.AlgK
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.SepChar
open UpperTheory.V.FW

theorem UpperTheory.V.FW.sepChar :
    ∀ (k D A : Type) [Field k] [IsAlgClosed k] [CommGroup D] [Finite D] [CommRing A] [Algebra k A] (ρ : D →* A) (x : A), (Nat.card D : k) ≠ 0 → (∀ (ψ : D →* kˣ) (e : A), (∀ d, ρ d * e = (ψ d : k) • e) → x * e = 0) → x = 0 := by
  intro k D A _ _ _ _ _ _ ρ x hD h
  classical
  letI := Fintype.ofFinite D
  have hexp : ((Monoid.exponent D : ℕ) : k) ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := Group.exponent_dvd_nat_card (G := D)
    apply hD
    rw [hc]; push_cast; rw [h0, zero_mul]
  haveI : NeZero ((Monoid.exponent D : ℕ) : k) := ⟨hexp⟩
  haveI : NeZero (Monoid.exponent D) := ⟨fun h0 => hexp (by rw [h0]; simp)⟩
  haveI : HasEnoughRootsOfUnity k (Monoid.exponent D) := inferInstance
  have hcard : Nat.card (D →* kˣ) = Nat.card D :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity D k
  haveI : Finite (D →* kˣ) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  letI := Fintype.ofFinite (D →* kˣ)
  have h1 : ∀ ψ : D →* kˣ, x * (∑ d : D, ((ψ d⁻¹ : kˣ) : k) • ρ d) = 0 := by
    intro ψ
    apply h ψ
    intro g
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ ?_
    intro d
    simp only [Equiv.coe_mulLeft, mul_smul_comm, smul_smul, ← map_mul, ← Units.val_mul]
    congr 3
    rw [mul_inv, mul_inv_cancel_left]
  have h2 : ∀ d : D, d ≠ 1 → ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) = 0 := by
    intro d hd
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity D k (a := d⁻¹) (inv_ne_one.mpr hd)
    have e : ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) = (φ d⁻¹ : k) * ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) := by
      rw [Finset.mul_sum]
      refine (Fintype.sum_equiv (Equiv.mulLeft φ) _ _ ?_).symm
      intro ψ
      simp only [Equiv.coe_mulLeft, MonoidHom.mul_apply, Units.val_mul]
    have hne : ((φ d⁻¹ : kˣ) : k) ≠ 1 := fun h' => hφ (Units.val_eq_one.mp h')
    have : (1 - ((φ d⁻¹ : kˣ) : k)) * ∑ ψ : D →* kˣ, ((ψ d⁻¹ : kˣ) : k) = 0 := by
      rw [sub_mul, one_mul, ← e, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne.symm)
  have h3 : ∑ ψ : D →* kˣ, ∑ d : D, ((ψ d⁻¹ : kˣ) : k) • ρ d = (Nat.card D : k) • (1 : A) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    rw [Finset.sum_eq_single (1 : D)]
    · rw [← hcard, Nat.card_eq_fintype_card]
      simp
    · intro d _ hd
      rw [h2 d hd, zero_smul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  have h4 : x * ((Nat.card D : k) • (1 : A)) = 0 := by
    rw [← h3, Finset.mul_sum]
    exact Finset.sum_eq_zero fun ψ _ => h1 ψ
  rw [mul_smul_comm, mul_one] at h4
  exact (smul_eq_zero.mp h4).resolve_left hD
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.PhiDvd
open UpperTheory.V.FW

private theorem UpperTheory.V.FW.phiDvd_pow (l : ℕ) [Fact l.Prime] (n : ℕ) (k A : Type) [Field k] [CharP k l]
    [CommRing A] [Algebra k A] (x : A) : (x - 1) ^ l ^ n = x ^ l ^ n - 1 := by
  have h : ((Polynomial.X : Polynomial k) - 1) ^ l ^ n = Polynomial.X ^ l ^ n - 1 := by
    rw [sub_pow_char_pow, one_pow]
  have := congrArg (Polynomial.aeval x) h
  simpa using this

private theorem UpperTheory.V.FW.phiDvd_nil (k A : Type) [Field k] [CommRing A] [Algebra k A] (T φ : A)
    (hT : IsNilpotent T) (hφ : φ ∈ Algebra.adjoin k {T}) (N : ℕ) (h : ¬ T ^ N ∣ φ) : φ ∣ T ^ N := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hφ
  obtain ⟨f, rfl⟩ := hφ
  change ¬ T ^ N ∣ Polynomial.aeval T f at h
  show Polynomial.aeval T f ∣ T ^ N
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact h (by simp)
  obtain ⟨q, hq, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf0 0
  simp only [map_zero, sub_zero] at hq hnd
  rw [Polynomial.X_dvd_iff] at hnd
  have hu : IsUnit (Polynomial.aeval T q) := by
    obtain ⟨r, hr⟩ : Polynomial.X ∣ q - Polynomial.C (q.coeff 0) :=
      Polynomial.X_dvd_iff.2 (by simp)
    have hq' : q = Polynomial.C (q.coeff 0) + Polynomial.X * r := sub_eq_iff_eq_add'.mp hr
    have hev : Polynomial.aeval T q = algebraMap k A (q.coeff 0) + T * Polynomial.aeval T r := by
      conv_lhs => rw [hq']
      simp
    have hnil : IsNilpotent (T * Polynomial.aeval T r) := by
      obtain ⟨M, hM⟩ := hT
      exact ⟨M, by rw [mul_pow, hM, zero_mul]⟩
    have hc : IsUnit (algebraMap k A (q.coeff 0)) := (Ne.isUnit hnd).map _
    rw [hev]
    first
      | exact hnil.isUnit_add_right_of_commute hc (Commute.all _ _)
      | (rw [add_comm]; exact hnil.isUnit_add_right_of_commute hc (Commute.all _ _))
  have hφ : Polynomial.aeval T f = T ^ Polynomial.rootMultiplicity 0 f * Polynomial.aeval T q := by
    conv_lhs => rw [hq]
    simp
  by_cases hv : N ≤ Polynomial.rootMultiplicity 0 f
  · exfalso
    exact h (hφ ▸ dvd_mul_of_dvd_left (pow_dvd_pow T hv) _)
  · push_neg at hv
    rw [hφ]
    refine ⟨↑hu.unit⁻¹ * T ^ (N - Polynomial.rootMultiplicity 0 f), ?_⟩
    calc T ^ N = T ^ Polynomial.rootMultiplicity 0 f * T ^ (N - Polynomial.rootMultiplicity 0 f) := by
          rw [← pow_add, Nat.add_sub_cancel' hv.le]
      _ = T ^ Polynomial.rootMultiplicity 0 f * Polynomial.aeval T q *
          (↑hu.unit⁻¹ * T ^ (N - Polynomial.rootMultiplicity 0 f)) := by
          rw [mul_assoc, ← mul_assoc (Polynomial.aeval T q), hu.mul_val_inv, one_mul]

theorem UpperTheory.V.FW.phiDvd :
    ∀ (l : ℕ) [Fact l.Prime] (b K : ℕ) (k G Q : Type) [Field k] [CharP k l] [CommGroup G] [CommGroup Q] (p : G →* G) (π : G →* Q) (γ : G) (χ : G →* kˣ) (θ : MonoidAlgebra k G), γ ^ l ^ b = 1 → (∀ g, p g ∈ Subgroup.zpowers γ) → (∀ g, π (p g) = π g) → π γ ^ l ^ K = 1 → tw χ π θ ≠ 0 → tw χ p θ ∣ (MonoidAlgebra.of k G γ - 1) ^ l ^ K := by
  intro l _ b K k G Q _ _ _ _ p π γ χ θ hγ hp hπ hπγ hne
  set T : MonoidAlgebra k G := MonoidAlgebra.of k G γ - 1 with hT
  have hof : ∀ m : ℕ, MonoidAlgebra.of k G (γ ^ m) ∈ Algebra.adjoin k {T} := by
    intro m
    have e : MonoidAlgebra.of k G (γ ^ m) = (T + 1) ^ m := by rw [hT, sub_add_cancel, map_pow]
    rw [e]
    exact Subalgebra.pow_mem _ (Subalgebra.add_mem _ (Algebra.self_mem_adjoin_singleton k T) (Subalgebra.one_mem _)) _
  have hfin : IsOfFinOrder γ :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨l ^ b, pow_pos (Fact.out : l.Prime).pos _, hγ⟩
  have hmem : tw χ p θ ∈ Algebra.adjoin k {T} := by
    rw [← MonoidAlgebra.sum_coeff_single θ, map_finsuppSum, Finsupp.sum]
    refine Subalgebra.sum_mem _ fun g _ => ?_
    rw [tw_single]
    obtain ⟨m, hm⟩ := (hfin.mem_powers_iff_mem_zpowers).2 (hp g)
    have e : MonoidAlgebra.single (p g) (θ.coeff g * ↑(χ g)) =
        (θ.coeff g * ↑(χ g)) • MonoidAlgebra.of k G (γ ^ m) := by
      rw [← (show γ ^ m = p g from hm), MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
    rw [e]
    exact Subalgebra.smul_mem _ (hof m) _
  have hTnil : IsNilpotent T :=
    ⟨l ^ b, by rw [hT, phiDvd_pow l b k, ← map_pow, hγ, map_one, sub_self]⟩
  refine phiDvd_nil k _ T _ hTnil hmem _ ?_
  intro hdvd
  apply hne
  set ψ := MonoidAlgebra.mapDomainAlgHom k k π with hψ
  have hcomp : ψ.comp (tw χ p) = tw χ π := by
    refine MonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
    simp [hψ, tw_single, hπ]
  have hψT : ψ T ^ l ^ K = 0 := by
    rw [← map_pow, hT, phiDvd_pow l K k, map_sub, map_pow, map_one]
    simp [hψ, MonoidAlgebra.of_apply, MonoidAlgebra.single_pow, ← map_pow, hπγ, MonoidAlgebra.one_def]
  obtain ⟨c, hc⟩ := hdvd
  have h1 : tw χ π θ = ψ (tw χ p θ) := by rw [← hcomp]; rfl
  rw [h1, hc, map_mul, map_pow, hψT, zero_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.FrobEig
open UpperTheory.V.FW

theorem UpperTheory.V.FW.frobEig :
    ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) (k G A : Type) [Field k] [CharP k l] [CommGroup G] [CommRing A] [Algebra k A] (r : MonoidAlgebra k G →ₐ[k] A) (p : G →* G) (χ : G →* kˣ) (e : A) (θ : MonoidAlgebra k G), (∀ g, r (MonoidAlgebra.of k G ((g * (p g)⁻¹) ^ l ^ a)) * e = ((χ g : k) ^ l ^ a) • e) → r θ ^ l ^ a * e = r (tw χ p θ) ^ l ^ a * e := by
  intro l _ a k G A _ _ _ _ _ r p χ e θ h
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  haveI : CharP A l := charP_of_injective_algebraMap (algebraMap k A).injective l
  set q := l ^ a with hq
  have frob_add : ∀ x y : A, (x + y) ^ q = x ^ q + y ^ q := fun x y => by
    rw [hq]
    exact add_pow_char_pow x y l a
  have hs : ∀ (x : G) (b : k), r (MonoidAlgebra.single x b) ^ q = b ^ q • r (MonoidAlgebra.of k G (x ^ q)) := by
    intro x b
    have e1 : MonoidAlgebra.single x b = b • MonoidAlgebra.of k G x := by
      simp [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single']
    rw [e1, map_smul, smul_pow, map_pow (MonoidAlgebra.of k G), map_pow r]
  induction θ using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add (f := _), frob_add, add_mul, hf, hg]
  | single g c =>
    rw [tw_single, hs, hs]
    have hg : g ^ q = (g * (p g)⁻¹) ^ q * (p g) ^ q := by
      rw [mul_pow, inv_pow, inv_mul_cancel_right]
    rw [hg, map_mul, map_mul, smul_mul_assoc, smul_mul_assoc,
      mul_comm (r (MonoidAlgebra.of k G ((g * (p g)⁻¹) ^ q))), mul_assoc, h g, mul_smul_comm,
      smul_smul, mul_pow]
end

open UpperTheory.V.FW

theorem UpperTheory.V.FW.algK :
    ∀ (l : ℕ) [Fact l.Prime] (a m b K : ℕ) (k G Q : Type) [Field k] [CharP k l] [IsAlgClosed k] [CommGroup G] [Finite G] [CommGroup Q] (p : G →* G) (π : G →* Q) (γ J : G) (θ : MonoidAlgebra k G), m.Coprime l → γ ^ l ^ b = 1 → (∀ g, p g ∈ Subgroup.zpowers γ) → (∀ g, (g * (p g)⁻¹) ^ (l ^ a * m) = 1) → p J = 1 → (∀ g, π (p g) = π g) → π γ ^ l ^ K = 1 → (∀ χ : G →* kˣ, χ J = -1 → tw χ π θ ≠ 0) → (MonoidAlgebra.of k G γ - 1) ^ (l ^ K * l ^ a) ∈ Ideal.span {θ, 1 + MonoidAlgebra.of k G J} := by
  intro l _ a m b K k G Q _ _ _ _ _ _ p π γ J θ hml hγ hp hord hpJ hπ hπγ htw
  have hl : l.Prime := Fact.out
  let I : Ideal (MonoidAlgebra k G) := Ideal.span {θ, 1 + MonoidAlgebra.of k G J}
  let r : MonoidAlgebra k G →ₐ[k] (MonoidAlgebra k G ⧸ I) := Ideal.Quotient.mkₐ k I
  have hr : ∀ x, r x = 0 ↔ x ∈ I := fun x => by
    rw [Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem
  let qh : G →* G :=
    { toFun := fun g => (g * (p g)⁻¹) ^ (l ^ a)
      map_one' := by simp
      map_mul' := by
        intro x y
        rw [map_mul, mul_inv, mul_mul_mul_comm, mul_pow] }
  let D : Subgroup G := qh.range
  let qD : G →* D := qh.rangeRestrict
  have hcard : (Nat.card D : k) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff k l] at h
    obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' l h
    obtain ⟨g, hg⟩ := d.2
    have h1 : (d : G) ^ m = 1 := by
      rw [← hg]
      show ((g * (p g)⁻¹) ^ (l ^ a)) ^ m = 1
      rw [← pow_mul]
      exact hord g
    have h2 : orderOf d ∣ m := by
      apply orderOf_dvd_of_pow_eq_one
      exact Subtype.ext (by simpa using h1)
    rw [hd] at h2
    have h3 : l ∣ Nat.gcd m l := Nat.dvd_gcd h2 dvd_rfl
    rw [hml] at h3
    exact hl.one_lt.ne' (Nat.dvd_one.mp h3)
  let ρ : D →* (MonoidAlgebra k G ⧸ I) :=
    ((r : MonoidAlgebra k G →+* (MonoidAlgebra k G ⧸ I)) : MonoidAlgebra k G →* (MonoidAlgebra k G ⧸ I)).comp
      ((MonoidAlgebra.of k G).comp D.subtype)
  have hρ : ∀ g, ρ (qD g) = r (MonoidAlgebra.of k G ((g * (p g)⁻¹) ^ (l ^ a))) := fun g => rfl
  have hθ : r θ = 0 := (hr θ).mpr (Ideal.subset_span (Set.mem_insert _ _))
  have hJ : r (MonoidAlgebra.of k G J) = -1 := by
    have h0 : r (1 + MonoidAlgebra.of k G J) = 0 :=
      (hr _).mpr (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    rw [map_add (f := _), map_one] at h0
    exact eq_neg_of_add_eq_zero_right h0
  have hla : l ^ a ≠ 0 := pow_ne_zero _ hl.ne_zero
  rw [← hr]
  apply sepChar k D _ ρ _ hcard
  intro ψ e he
  by_cases he0 : e = 0
  · rw [he0, mul_zero]
  let F : k ≃+* k := (iterateFrobeniusEquiv k l a).symm
  let χ : G →* kˣ := (Units.map (F : k →* k)).comp (ψ.comp qD)
  have hχ : ∀ g, (χ g : k) ^ (l ^ a) = ψ (qD g) := by
    intro g
    show (F (ψ (qD g) : k)) ^ (l ^ a) = _
    rw [← iterateFrobeniusEquiv_def]
    exact RingEquiv.apply_symm_apply _ _
  have hT : r (tw χ p θ) ^ (l ^ a) * e = 0 := by
    have := frobEig l a k G _ r p χ e θ (by
      intro g
      rw [hχ g, ← hρ g]
      exact he (qD g))
    rw [← this, hθ, zero_pow hla, zero_mul]
  have hχJ : χ J = -1 := by
    have h1 := he (qD J)
    rw [hρ J, hpJ, inv_one, mul_one, map_pow, map_pow, hJ] at h1
    have h2 : ((-1 : k) ^ (l ^ a)) • e = (ψ (qD J) : k) • e := by
      rw [← h1, Algebra.smul_def, map_pow, map_neg, map_one]
    have h3 := smul_left_injective k he0 h2
    rw [← hχ J] at h3
    apply Units.ext
    rw [Units.val_neg, Units.val_one]
    apply (iterateFrobeniusEquiv k l a).injective
    rw [iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def]
    exact h3.symm
  obtain ⟨c, hc⟩ := phiDvd l b K k G Q p π γ χ θ hγ hp hπ hπγ (htw χ hχJ)
  rw [pow_mul, hc, mul_pow, map_mul, map_pow, map_pow, mul_right_comm, hT, zero_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.DescZRetr
open UpperTheory.V.FW

private theorem UpperTheory.V.FW.descZ_retr (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] :
    ∃ ϖ : k →+ ZMod l, ϖ 1 = 1 := by
  letI := ZMod.algebra k l
  have hinj : LinearMap.ker (LinearMap.toSpanSingleton (ZMod l) k 1) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro a b h
    simp only [LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_one] at h
    exact (algebraMap (ZMod l) k).injective h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  refine ⟨g.toAddMonoidHom, ?_⟩
  have h1 := LinearMap.congr_fun hg 1
  simpa using h1

private theorem UpperTheory.V.FW.descZ_mul {k F G : Type} [CommRing k] [CommRing F] [CommGroup G] (ϖ : k →+ F)
    (u : MonoidAlgebra k G) (a : MonoidAlgebra ℤ G) :
    MonoidAlgebra.map ϖ (u * toK k G a) = MonoidAlgebra.map ϖ u * toK F G a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), mul_add, MonoidAlgebra.map_add (f := _), hx, hy, map_add (f := _), mul_add]
  | single g n =>
    ext h
    simp only [toK, MonoidAlgebra.mapRingHom_single, eq_intCast, MonoidAlgebra.coeff_map,
      Finsupp.mapRange_apply, MonoidAlgebra.mul_single_apply, AddMonoidHom.coe_coe]
    rw [← zsmul_eq_mul', map_zsmul, zsmul_eq_mul']

private theorem UpperTheory.V.FW.descZ_ker (l : ℕ) {G : Type} [CommGroup G] (y : MonoidAlgebra ℤ G)
    (hy : toK (ZMod l) G y = 0) : ∃ z, y = z * (l : MonoidAlgebra ℤ G) := by
  classical
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.mapRange (fun n : ℤ => n / (l : ℤ)) (by simp) y.coeff), ?_⟩
  ext g
  have hg : (l : ℤ) ∣ y.coeff g := by
    have h0 := congrArg (fun w => w.coeff g) hy
    simp only [toK, MonoidAlgebra.coeff_mapRingHom, eq_intCast, MonoidAlgebra.coeff_zero,
      Finsupp.coe_zero, Pi.zero_apply] at h0
    exact (CharP.intCast_eq_zero_iff (ZMod l) l _).mp h0
  rw [MonoidAlgebra.natCast_def, MonoidAlgebra.mul_single_apply, inv_one, mul_one,
    MonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply, Int.ediv_mul_cancel hg]

theorem UpperTheory.V.FW.descZ :
    ∀ (l : ℕ) [Fact l.Prime] (k G : Type) [Field k] [CharP k l] [CommGroup G] (x a b : MonoidAlgebra ℤ G), toK k G x ∈ Ideal.span {toK k G a, toK k G b} → x ∈ Ideal.span {a, b, (l : MonoidAlgebra ℤ G)} := by
  intro l _ k G _ _ _ x a b hx
  obtain ⟨ϖ, hϖ⟩ := descZ_retr l k
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hx
  have h1 : MonoidAlgebra.map ϖ (1 : MonoidAlgebra k G) = 1 := by
    rw [MonoidAlgebra.one_def, MonoidAlgebra.map_single, hϖ, MonoidAlgebra.one_def]
  have h2 := descZ_mul ϖ 1 x
  rw [one_mul, h1, one_mul, ← huv, MonoidAlgebra.map_add (f := _), descZ_mul, descZ_mul] at h2
  have hs : Function.Surjective (toK (ZMod l) G) :=
    MonoidAlgebra.map_surjective (Int.castRingHom (ZMod l) : ℤ →+ ZMod l) ZMod.intCast_surjective
  obtain ⟨u', hu⟩ := hs (MonoidAlgebra.map ϖ u)
  obtain ⟨v', hv⟩ := hs (MonoidAlgebra.map ϖ v)
  obtain ⟨z, hz⟩ := descZ_ker l (x - (u' * a + v' * b)) (by
    rw [map_sub, map_add (f := _), map_mul, map_mul, hu, hv, h2, sub_self])
  have hx' : x = u' * a + v' * b + z * (l : MonoidAlgebra ℤ G) := by rw [← hz]; ring
  rw [hx']
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_ <;>
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
end

open UpperTheory.V.FW

private theorem toK_of (k G : Type) [CommRing k] [Monoid G] (g : G) :
    toK k G (MonoidAlgebra.of ℤ G g) = MonoidAlgebra.of k G g := by
  simp [toK]

theorem UpperTheory.V.FW.memZ :
    ∀ (l : ℕ) [Fact l.Prime] (f c : ℕ), f.Coprime l → Odd c → 1 < c → c.Coprime (f * l) → ∃ N n₀ : ℕ, 2 ≤ n₀ ∧ ∀ (n : ℕ) [NeZero (f * l ^ n)], n₀ ≤ n → ∃ γ : (ZMod (f * l ^ n))ˣ, (γ : ZMod (f * l ^ n)) = 1 + f * l ^ ee l ∧ (Subgroup.zpowers γ).index = Nat.totient (f * l ^ ee l) ∧ (MonoidAlgebra.of ℤ _ γ - 1) ^ N ∈ Ideal.span {thetaH (f * l ^ n) c, 1 + MonoidAlgebra.of ℤ _ (-1 : (ZMod (f * l ^ n))ˣ), (l : MonoidAlgebra ℤ (ZMod (f * l ^ n))ˣ)} := by
  intro l hl f c hf hc hc1 hcf
  have hp : l.Prime := hl.out
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hf
    exact hp.one_lt.ne' hf
  have ht : Nat.totient (f * l ^ ee l) ≠ 0 :=
    (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (mul_ne_zero hf0 (pow_ne_zero _ hp.ne_zero)))).ne'
  obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_pow_mul_and_not_dvd ht l hp.one_lt.ne'
  have hml : m.Coprime l := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm
  obtain ⟨n₀, h2, hnv⟩ := nonvan l f c hf hc hc1 hcf
  refine ⟨l ^ n₀ * l ^ a, n₀, h2, ?_⟩
  intro n _ hn
  have h : l ^ n₀ ∣ f * l ^ n := Dvd.dvd.mul_left (pow_dvd_pow l hn) f
  obtain ⟨γ, p, hγ, hγ1, hidx, hpz, hpow, hpJ, hπ⟩ := struct l f n hf (h2.trans hn)
  obtain ⟨hπ1, hπ2⟩ := hπ n₀ h hn
  refine ⟨γ, hγ, hidx, ?_⟩
  refine descZ l (AlgebraicClosure (ZMod l)) _ _ _ _ ?_
  have key := algK l a m n n₀ (AlgebraicClosure (ZMod l)) _ _ p (piQ l n₀ h) γ (-1)
    (toK (AlgebraicClosure (ZMod l)) _ (thetaH (f * l ^ n) c)) hml hγ1 hpz
    (fun g => by rw [← ham]; exact hpow g) hpJ hπ1 hπ2
    (fun χ hχ => hnv n h hn _ χ hχ)
  simpa only [map_pow, map_sub, map_add (f := _), map_one, toK_of] using key
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CardRangeInfTorsionLeIndexPow
open UpperTheory.V.FW

private theorem UpperTheory.V.FW.card_range_inf_torsion_le_index_pow (l : ℕ) [Fact l.Prime] (C : Type) [CommGroup C] [Finite C]
    (φ ψ : C →* C) (N : ℕ) (hc : ∀ x, φ (ψ x) = ψ (φ x))
    (hN : ∀ x, ∃ y, (φ y) ^ l = φ (ψ^[N] x)) :
    Nat.card (φ.range ⊓ torK (C := C) l : Subgroup C) ≤ (powR (C := C) l ⊔ ψ.range).index ^ N := by
  set U : Subgroup C := (powR (C := φ.range) l).comap φ.rangeRestrict with hUdef
  have hU : ∀ x, x ∈ U ↔ ∃ y, (φ y) ^ l = φ x := by
    intro x
    constructor
    · rintro ⟨⟨_, y, rfl⟩, hy⟩
      exact ⟨y, congrArg Subtype.val hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨⟨φ y, y, rfl⟩, Subtype.ext hy⟩
  have h1 : Nat.card (φ.range ⊓ torK (C := C) l : Subgroup C) = U.index := by
    rw [hUdef, Subgroup.index_comap_of_surjective _ φ.rangeRestrict_surjective,
      (cardTors φ.range).1 l]
    refine Nat.card_congr ⟨fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩,
      fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩, fun _ => rfl, fun _ => rfl⟩
  have hle : U ≤ U.comap ψ := by
    intro x hx
    obtain ⟨y, hy⟩ := (hU x).1 hx
    exact (hU _).2 ⟨ψ y, by rw [hc, hc, ← hy, map_pow]⟩
  set S : C ⧸ U →* C ⧸ U := QuotientGroup.map U U ψ hle with hS
  let T : AddMonoid.End (Additive (C ⧸ U)) := MonoidHom.toAdditive S
  have hT : ∀ n (x : C), (T ^ n) (Additive.ofMul (x : C ⧸ U)) =
      Additive.ofMul ((ψ^[n] x : C) : C ⧸ U) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, Function.iterate_succ_apply, ← ih]
      rfl
  have hT0 : T ^ N = 0 := by
    refine AddMonoidHom.ext fun v => ?_
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have : v = Additive.ofMul (x : C ⧸ U) := by rw [hx]; rfl
    subst this
    have h := hT N x
    rw [(QuotientGroup.eq_one_iff _).2 ((hU _).2 (hN x))] at h
    exact h
  have h2 := nilCard _ T N hT0
  have h3 : (AddMonoidHom.range T).index = S.range.index := rfl
  have h4 : S.range.index ∣ (powR (C := C) l ⊔ ψ.range).index := by
    rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective U)]
    refine Subgroup.index_dvd_of_le (sup_le ?_ ?_)
    · rintro _ ⟨x, rfl⟩
      refine ⟨1, ?_⟩
      rw [map_one]
      exact ((QuotientGroup.eq_one_iff _).2 ((hU _).2 ⟨x, by simp⟩)).symm
    · rintro _ ⟨x, rfl⟩
      exact ⟨(x : C ⧸ U), rfl⟩
  rw [h1]
  refine le_trans (le_of_eq ?_) (h2.trans ?_)
  · rfl
  · rw [h3]
    exact Nat.pow_le_pow_left (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h4) N

theorem UpperTheory.V.FW.core :
    ∀ (l : ℕ) [Fact l.Prime] (G C : Type) [CommGroup G] [CommGroup C] [Finite C] (ρ : Representation ℤ G (Additive C)) (J γ : G) (Jc γc : C →* C) (θ : MonoidAlgebra ℤ G) (N : ℕ), J * J = 1 → (∀ x, ρ J (Additive.ofMul x) = Additive.ofMul (Jc x)) → (∀ x, ρ γ (Additive.ofMul x) = Additive.ofMul (γc x)) → ρ.asAlgebraHom (θ * (1 - MonoidAlgebra.of ℤ G J)) = 0 → (MonoidAlgebra.of ℤ G γ - 1) ^ N ∈ Ideal.span {θ, 1 + MonoidAlgebra.of ℤ G J, (l : MonoidAlgebra ℤ G)} → Nat.card (difR Jc ⊓ torK (C := C) l : Subgroup C) ≤ (powR (C := C) l ⊔ difR γc).index ^ N := by
  intro l _ G C _ _ _ ρ J γ Jc γc θ N hJJ hJ hγ hθ hmem
  have key : ∀ (g : G) (gc : C →* C), (∀ x, ρ g (Additive.ofMul x) = Additive.ofMul (gc x)) →
      ∀ x, ρ.asAlgebraHom (1 - MonoidAlgebra.of ℤ G g) (Additive.ofMul x) =
        Additive.ofMul ((MonoidHom.id C / gc) x) := by
    intro g gc h x
    rw [map_sub, map_one, Representation.asAlgebraHom_of, LinearMap.sub_apply, h]
    simp
  have hφ := key J Jc hJ
  have hψ := key γ γc hγ
  set φ := MonoidHom.id C / Jc
  set ψ := MonoidHom.id C / γc
  set a := 1 - MonoidAlgebra.of ℤ G J with ha
  set b := 1 - MonoidAlgebra.of ℤ G γ with hb
  have hit : ∀ n x, ρ.asAlgebraHom (b ^ n) (Additive.ofMul x) = Additive.ofMul (ψ^[n] x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, map_mul, mul_apply_eq_comp, hψ, ih, Function.iterate_succ_apply]
  refine card_range_inf_torsion_le_index_pow l C φ ψ N (fun x => ?_) (fun x => ?_)
  · apply Additive.ofMul.injective
    rw [← hφ, ← hψ, ← hψ, ← hφ, ← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul,
      ← map_mul, mul_comm]
  · have hmem' : b ^ N ∈ Ideal.span {θ, 1 + MonoidAlgebra.of ℤ G J, (l : MonoidAlgebra ℤ G)} := by
      have : b = -(MonoidAlgebra.of ℤ G γ - 1) := by rw [hb, neg_sub]
      rw [this, neg_pow]
      exact Ideal.mul_mem_left _ _ hmem
    obtain ⟨u, w, hw, h1⟩ := Ideal.mem_span_insert.1 hmem'
    obtain ⟨v, z, h2⟩ := Ideal.mem_span_pair.1 hw
    have hJ2 : MonoidAlgebra.of ℤ G J * MonoidAlgebra.of ℤ G J = 1 := by
      rw [← map_mul, hJJ, map_one]
    have h3 : a * b ^ N = u * (θ * a) + l • (a * z) := by
      rw [h1, ← h2, ha, nsmul_eq_mul]
      linear_combination (-v) * hJ2
    refine ⟨Additive.toMul (ρ.asAlgebraHom z (Additive.ofMul x)), ?_⟩
    apply Additive.ofMul.injective
    rw [ofMul_pow, ← hφ, ← hφ, ← hit, ofMul_toMul, ← mul_apply_eq_comp, ← mul_apply_eq_comp,
      ← map_mul, ← map_mul, h3, map_add, map_mul _ u, hθ, mul_zero, zero_add, map_nsmul,
      LinearMap.smul_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.POddRelIndexLe
open UpperTheory.V.FW

private theorem pOdd_relIndex_le (l : ℕ) (C : Type) [CommGroup C] [Finite C] (B : Subgroup C) :
    (powR (C := C) l).relIndex B ≤ Nat.card (B ⊓ torK (C := C) l : Subgroup C) := by
  have h1 : powR (C := B) l ≤ (powR (C := C) l).subgroupOf B := by
    rintro _ ⟨y, rfl⟩
    exact ⟨(y : C), by simp⟩
  have h2 : ((powR (C := C) l).subgroupOf B).index ≤ (powR (C := B) l).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) (Subgroup.index_dvd_of_le h1)
  have h3 : (powR (C := B) l).index = Nat.card (torK (C := B) l) := by
    have a := Subgroup.index_mul_card (powR (C := B) l)
    have b := Subgroup.index_mul_card (torK (C := B) l)
    have c : (torK (C := B) l).index = Nat.card (powR (C := B) l) := Subgroup.index_ker _
    have d : 0 < Nat.card (powR (C := B) l) := Nat.card_pos
    rw [c, ← a, mul_comm] at b
    exact (Nat.eq_of_mul_eq_mul_right d b).symm
  have h4 : Nat.card (torK (C := B) l) ≤ Nat.card (B ⊓ torK (C := C) l : Subgroup C) := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨(x.1 : C), x.1.2, ?_⟩ : (B ⊓ torK (C := C) l : Subgroup C))) ?_
    · have hx : x.1 ^ l = 1 := x.2
      show (x.1 : C) ^ l = 1
      rw [← Subgroup.coe_pow, hx]; rfl
    · intro x y hxy
      have e := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext e)
  exact h2.trans (h3.le.trans h4)

theorem UpperTheory.V.FW.pOdd :
    ∀ (l : ℕ) (C : Type) [CommGroup C] [Finite C] (J : C →* C), Odd l → (powR (C := C) l ⊔ difR J).index ≤ l * Nat.card (minK J ⊓ torK (C := C) l : Subgroup C) → (powR (C := C) l).index ≤ l * Nat.card (difR J ⊓ torK (C := C) l : Subgroup C) ^ 2 := by
  intro l C _ _ J hl h
  obtain ⟨k, hk⟩ := hl
  have h1 : minK J ⊓ torK (C := C) l ≤ difR J ⊓ torK (C := C) l := by
    rintro x ⟨hx, hx'⟩
    refine ⟨⟨x ^ (k + 1), ?_⟩, hx'⟩
    have a : J x * x = 1 := hx
    have b : x ^ l = 1 := hx'
    have c : J x = x⁻¹ := eq_inv_of_mul_eq_one_left a
    show x ^ (k + 1) / J (x ^ (k + 1)) = x
    rw [map_pow, c, inv_pow, div_inv_eq_mul, ← pow_add,
      show k + 1 + (k + 1) = l + 1 by omega, pow_succ, b, one_mul]
  have h2 : Nat.card (minK J ⊓ torK (C := C) l : Subgroup C) ≤ Nat.card (difR J ⊓ torK (C := C) l : Subgroup C) :=
    Subgroup.card_le_of_le h1
  have h3 := Subgroup.relIndex_mul_index (le_sup_left : powR (C := C) l ≤ powR (C := C) l ⊔ difR J)
  rw [Subgroup.relIndex_sup_left] at h3
  have h4 := pOdd_relIndex_le l C (difR J)
  calc (powR (C := C) l).index = (powR (C := C) l).relIndex (difR J) * (powR (C := C) l ⊔ difR J).index := h3.symm
    _ ≤ Nat.card (difR J ⊓ torK (C := C) l : Subgroup C) * (l * Nat.card (difR J ⊓ torK (C := C) l : Subgroup C)) :=
      Nat.mul_le_mul h4 (h.trans (Nat.mul_le_mul_left _ h2))
    _ = _ := by ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.PTwo
open UpperTheory.V.FW

theorem UpperTheory.V.FW.pTwo :
    ∀ (C : Type) [CommGroup C] [Finite C] (J : C →* C), (∀ x, J (J x) = x) →
      (powR (C := C) 2).index ≤
        ((difR J).relIndex (minK J) * Nat.card (difR J ⊓ torK (C := C) 2 : Subgroup C)) ^ 2 := by
  intro C _ _ J hJ
  classical
  have hcard : ∀ {G H : Type} [Group G] [Group H] (f : G →* H),
      Nat.card G = Nat.card f.ker * Nat.card f.range := by
    intro G H _ _ f
    rw [← f.ker.card_mul_index, Subgroup.index_ker]
  set T := torK (C := C) 2 with hT
  set D := difR J with hD
  set K := minK J with hK
  have memT : ∀ x : C, x ∈ T ↔ x ^ 2 = 1 := fun x => by simp [hT, torK]
  have memK : ∀ x : C, x ∈ K ↔ J x * x = 1 := fun x => by simp [hK, minK]
  have memD : ∀ x : C, x ∈ D ↔ ∃ y, y / J y = x := fun x => by simp [hD, difR]
  have hDK : D ≤ K := by
    intro x hx
    obtain ⟨y, rfl⟩ := (memD x).1 hx
    rw [memK, map_div, hJ, div_mul_div_comm, mul_comm (J y) y, div_self']
  have h1 : (powR (C := C) 2).index = Nat.card T := by
    have e1 := hcard (powMonoidHom 2 : C →* C)
    have e2 := (powR (C := C) 2).card_mul_index
    have hpos : 0 < Nat.card (powR (C := C) 2) := Nat.card_pos
    have e3 : Nat.card (powR (C := C) 2) * (powR (C := C) 2).index =
        Nat.card (powR (C := C) 2) * Nat.card T := by
      rw [e2, mul_comm]
      exact e1
    exact Nat.eq_of_mul_eq_mul_left hpos e3
  let g : T →* C := (MonoidHom.id C / J).comp T.subtype
  have e4 := hcard g
  have r1 : Nat.card g.range ≤ Nat.card (D ⊓ T : Subgroup C) := by
    apply Subgroup.card_le_of_le
    rintro _ ⟨t, rfl⟩
    have gt : g t = t.1 / J t.1 := rfl
    rw [gt, Subgroup.mem_inf]
    refine ⟨(memD _).2 ⟨t.1, rfl⟩, ?_⟩
    rw [memT, div_pow, ← map_pow, (memT _).1 t.2, map_one, div_one]
  have r2 : Nat.card g.ker ≤ Nat.card (K ⊓ T : Subgroup C) := by
    have hm : ∀ x : g.ker, (x.1.1 : C) ∈ K ⊓ T := by
      intro x
      have hx : g x.1 = 1 := MonoidHom.mem_ker.1 x.2
      have hT' : x.1.1 ^ 2 = 1 := (memT _).1 x.1.2
      have hd : x.1.1 / J x.1.1 = 1 := hx
      have hJx : J x.1.1 = x.1.1 := (div_eq_one.1 hd).symm
      refine Subgroup.mem_inf.2 ⟨(memK _).2 ?_, x.1.2⟩
      rw [hJx, ← pow_two, hT']
    refine Nat.card_le_card_of_injective (fun x => (⟨x.1.1, hm x⟩ : (K ⊓ T : Subgroup C))) ?_
    intro a b hab
    have hab' := congrArg Subtype.val hab
    simp only at hab'
    exact Subtype.ext (Subtype.ext hab')
  let incl : (K ⊓ T : Subgroup C) →* K := Subgroup.inclusion inf_le_left
  let h : (K ⊓ T : Subgroup C) →* K ⧸ D.subgroupOf K := (QuotientGroup.mk' (D.subgroupOf K)).comp incl
  have e5 := hcard h
  have r3 : Nat.card h.range ≤ D.relIndex K :=
    le_of_le_of_eq (Subgroup.card_le_card_group _) rfl
  have r4 : Nat.card h.ker ≤ Nat.card (D ⊓ T : Subgroup C) := by
    have hm : ∀ x : h.ker, (x.1.1 : C) ∈ D ⊓ T := by
      intro x
      have hx : h x.1 = 1 := MonoidHom.mem_ker.1 x.2
      have hx2 : incl x.1 ∈ D.subgroupOf K := (QuotientGroup.eq_one_iff _).1 hx
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hx2, (Subgroup.mem_inf.1 x.1.2).2⟩
    refine Nat.card_le_card_of_injective (fun x => (⟨x.1.1, hm x⟩ : (D ⊓ T : Subgroup C))) ?_
    intro a b hab
    have hab' := congrArg Subtype.val hab
    simp only at hab'
    exact Subtype.ext (Subtype.ext hab')
  rw [h1]
  set r := D.relIndex K
  set d := Nat.card (D ⊓ T : Subgroup C)
  have s1 : Nat.card T ≤ (r * d) * d := by
    rw [e4]
    apply Nat.mul_le_mul _ r1
    calc Nat.card g.ker ≤ Nat.card (K ⊓ T : Subgroup C) := r2
      _ = Nat.card h.ker * Nat.card h.range := e5
      _ ≤ d * r := Nat.mul_le_mul r4 r3
      _ = r * d := mul_comm _ _
  have s2 : (r * d) * d ≤ (r * d) ^ 2 := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · simp [hr]
    · rw [pow_two]
      exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left d hr)
  exact s1.trans s2
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.cyc (l : ℕ) [hl : Fact l.Prime] (f : ℕ) (hf : f.Coprime l) (h1 : 1 < f) :
    ∃ B n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (L : Type) [Field L] [NumberField L] [IsCyclotomicExtension {f * l ^ n} ℚ L],
      IsTotallyComplex L ∧ (powR (Cl L) l).index ≤ B := by
  classical
  have hf0 : 0 < f := by omega
  have hl0 : 0 < l := hl.out.pos
  have hfl0 : 0 < f * l := Nat.mul_pos hf0 hl0
  have hcodd : Odd (2 * (f * l) + 1) := ⟨f * l, by ring⟩
  have hc1 : 1 < 2 * (f * l) + 1 := by omega
  have hcfl : (2 * (f * l) + 1).Coprime (f * l) := by
    simp [Nat.coprime_mul_left_add_left]
  obtain ⟨N, n₀, hn₀2, hmem⟩ := memZ l f (2 * (f * l) + 1) hf hcodd hc1 hcfl
  obtain ⟨B, hB⟩ := ambCyc l f hf
  by_cases hl2 : l = 2
  · subst hl2
    refine ⟨((2 ^ (f * 2 ^ ee 2).totient) ^ N * B ^ N) ^ 2, n₀, ?_⟩
    intro n hn L _ _ _
    haveI : NeZero (f * 2 ^ n) := ⟨(Nat.mul_pos hf0 (pow_pos hl0 n)).ne'⟩
    have hM2 : 2 < f * 2 ^ n := by
      have : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    haveI : IsCMField L := IsCyclotomicExtension.Rat.isCMField L ⟨f * 2 ^ n, Set.mem_singleton _, hM2⟩
    refine ⟨inferInstance, ?_⟩
    obtain ⟨γ, hγ1, hγidx, hγmem⟩ := hmem n hn
    have hcM : (2 * (f * 2) + 1).Coprime (f * 2 ^ n) := by
      obtain ⟨h1, h2⟩ := Nat.coprime_mul_iff_right.mp hcfl
      exact Nat.coprime_mul_iff_right.mpr ⟨h1, h2.pow_right n⟩
    have hcore := core 2 (ZMod (f * 2 ^ n))ˣ (Cl L) (cycRep (f * 2 ^ n) L) (-1) γ
      (clA (f * 2 ^ n) L (-1)) (clA (f * 2 ^ n) L γ) (thetaH (f * 2 ^ n) (2 * (f * 2) + 1)) N
      (by simp) (fun x => cycRep_apply _ _ _ x) (fun x => cycRep_apply _ _ _ x)
      (stickH _ _ L hcM hcodd hM2) hγmem
    have hamb := hB n L γ (by omega) hγ1
    have hbound : Nat.card ↥(difR (clA (f * 2 ^ n) L (-1)) ⊓ torK (Cl L) 2) ≤ B ^ N :=
      hcore.trans (Nat.pow_le_pow_left hamb N)
    have hfodd : Odd f := Nat.coprime_two_right.mp hf
    obtain ⟨_, hcE2⟩ := conjEq (f * 2 ^ n) L
    have hsgn := sgnCyc f n (2 * (f * 2) + 1) N L γ hfodd h1 (by omega) hcM hcodd hγmem
    rw [← hcE2, hγidx] at hsgn
    have hinv : ∀ x : Cl L, clA (f * 2 ^ n) L (-1) (clA (f * 2 ^ n) L (-1) x) = x := by
      intro x
      apply Additive.ofMul.injective
      rw [← cycRep_apply, ← cycRep_apply, ← Module.End.mul_apply, ← map_mul]
      simp
    have hp := pTwo (Cl L) (clA (f * 2 ^ n) L (-1)) hinv
    exact hp.trans (Nat.pow_le_pow_left (Nat.mul_le_mul hsgn hbound) 2)
  · refine ⟨l * (B ^ N) ^ 2, n₀, ?_⟩
    intro n hn L _ _ _
    haveI : NeZero (f * l ^ n) := ⟨(Nat.mul_pos hf0 (pow_pos hl0 n)).ne'⟩
    have hl3 : 3 ≤ l := by
      have := hl.out.two_le
      omega
    have hM2 : 2 < f * l ^ n := by
      have : 3 ≤ l ^ n := by
        calc 3 ≤ l := hl3
          _ = l ^ 1 := (pow_one l).symm
          _ ≤ l ^ n := Nat.pow_le_pow_right hl0 (by omega)
      nlinarith
    haveI : IsCMField L := IsCyclotomicExtension.Rat.isCMField L ⟨f * l ^ n, Set.mem_singleton _, hM2⟩
    refine ⟨inferInstance, ?_⟩
    obtain ⟨γ, hγ1, _, hγmem⟩ := hmem n hn
    have hcM : (2 * (f * l) + 1).Coprime (f * l ^ n) := by
      obtain ⟨h1, h2⟩ := Nat.coprime_mul_iff_right.mp hcfl
      exact Nat.coprime_mul_iff_right.mpr ⟨h1, h2.pow_right n⟩
    have hcore := core l (ZMod (f * l ^ n))ˣ (Cl L) (cycRep (f * l ^ n) L) (-1) γ
      (clA (f * l ^ n) L (-1)) (clA (f * l ^ n) L γ) (thetaH (f * l ^ n) (2 * (f * l) + 1)) N
      (by simp) (fun x => cycRep_apply _ _ _ x) (fun x => cycRep_apply _ _ _ x)
      (stickH _ _ L hcM hcodd hM2) hγmem
    have hamb := hB n L γ (by omega) hγ1
    have hbound : Nat.card ↥(difR (clA (f * l ^ n) L (-1)) ⊓ torK (Cl L) l) ≤ B ^ N :=
      hcore.trans (Nat.pow_le_pow_left hamb N)
    have hlodd : Odd l := hl.out.odd_of_ne_two hl2
    obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ L (Set.mem_singleton (f * l ^ n))
      (NeZero.ne _)
    have hsplit : f * l ^ n = f * l ^ (n - 1) * l := by
      rw [mul_assoc, ← pow_succ]
      congr 2
      omega
    have hζl : IsPrimitiveRoot (ζ ^ (f * l ^ (n - 1))) l := hζ.pow (NeZero.pos _) hsplit
    obtain ⟨_, hcE2⟩ := conjEq (f * l ^ n) L
    have hrefl := reflOdd L l _ hl2 hζl
    rw [← hcE2] at hrefl
    have hp := pOdd l (Cl L) (clA (f * l ^ n) L (-1)) hlodd hrefl
    exact hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbound 2))

theorem UpperTheory.V.FW.ferreroWashington : UpperTheory.V.Published.FerreroWashington := by
  unfold UpperTheory.V.Published.FerreroWashington
  intro l _ K _ _ _ _
  obtain ⟨f, D, hf, h1, hemb⟩ := embed l K
  obtain ⟨B, n₀, hB⟩ := cyc l f hf h1
  refine ⟨D * l ^ n₀ * B, ?_⟩
  intro n K' _ _ _ _
  obtain ⟨m, L, iF, iN, iA, iC, hm, hdeg⟩ := hemb n n₀ K'
  obtain ⟨htc, hidx⟩ := hB m hm L
  have hd := desc l K' L htc
  have hl2 : 1 < l := (Fact.out : l.Prime).one_lt
  have key : Nat.card (ClassGroup (𝓞 K') ⧸ (powMonoidHom l).range) ≤ D * l ^ n₀ * B := by
    have e : Nat.card (ClassGroup (𝓞 K') ⧸ (powMonoidHom l).range) = (powR (Cl K') l).index := rfl
    rw [e]
    exact hd.trans (Nat.mul_le_mul hdeg hidx)
  exact key.trans (Nat.lt_pow_self hl2).le
