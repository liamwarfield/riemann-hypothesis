module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TorsionExponentBound
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem padic_val_one_add_pow_sub_one (l c m : ℕ) (hl : l.Prime) (hc : 1 ≤ c) (h2 : l = 2 → 2 ≤ c)
    (hm : m ≠ 0) : padicValNat l ((1 + l ^ c) ^ m - 1) = c + padicValNat l m := by
  simp only [Nat.padicValNat_def]
  haveI := Fact.mk hl
  have hpow1 : 1 ≤ l ^ c := Nat.one_le_pow c l hl.pos
  have hx1 : 1 < 1 + l ^ c := by omega
  have hdvd : l ∣ (1 + l ^ c) - 1 := by
    rw [Nat.add_sub_cancel_left]
    exact dvd_pow_self l (by omega)
  have hnd : ¬ l ∣ 1 + l ^ c := by
    intro h
    rw [add_comm] at h
    have := (Nat.dvd_add_right (dvd_pow_self l (by omega : c ≠ 0))).1 h
    exact hl.one_lt.ne' (Nat.dvd_one.1 this)
  rcases hl.eq_two_or_odd' with rfl | hodd
  · obtain ⟨d, rfl⟩ : ∃ d, c = d + 2 := ⟨c - 2, by have := h2 rfl; omega⟩
    have h4 : 2 ^ (d + 2) = 4 * 2 ^ d := by ring
    have h := padicValNat.pow_two_sub_pow (x := 1 + 2 ^ (d + 2)) (y := 1) hx1 hdvd hnd
      (n := 2 * m) (by omega) (even_two_mul m)
    rw [one_pow] at h
    have hA : multiplicity 2 (1 + 2 ^ (d + 2) + 1) = 1 := by
      have e : 1 + 2 ^ (d + 2) + 1 = 2 * (1 + 2 * 2 ^ d) := by rw [h4]; ring
      rw [e, Nat.multiplicity_mul (by norm_num) (by omega), Nat.multiplicity_self (by norm_num),
        (Nat.multiplicity_eq_zero_iff.mpr (Or.inr (Or.inr (by omega))))]
    have hB : multiplicity 2 (1 + 2 ^ (d + 2) - 1) = d + 2 := by
      rw [Nat.add_sub_cancel_left, Nat.multiplicity_prime_pow]
    have hC : multiplicity 2 (2 * m) = 1 + multiplicity 2 m := by
      rw [Nat.multiplicity_mul (by norm_num) hm, Nat.multiplicity_self (by norm_num)]
    have hxm : 1 < (1 + 2 ^ (d + 2)) ^ m := Nat.one_lt_pow hm hx1
    obtain ⟨b, hb⟩ : ∃ b, (1 + 2 ^ (d + 2)) ^ m = b + 1 := ⟨_ - 1, (Nat.sub_add_cancel hxm.le).symm⟩
    have hmod : (1 + 2 ^ (d + 2)) ^ m % 4 = 1 := by
      rw [Nat.pow_mod, h4]
      have : (1 + 4 * 2 ^ d) % 4 = 1 := by omega
      rw [this, one_pow]
      rfl
    have hD : multiplicity 2 ((1 + 2 ^ (d + 2)) ^ m + 1) = 1 := by
      obtain ⟨q, hq⟩ : ∃ q, (1 + 2 ^ (d + 2)) ^ m + 1 = 2 * (2 * q + 1) :=
        ⟨((1 + 2 ^ (d + 2)) ^ m + 1) / 4, by omega⟩
      rw [hq, Nat.multiplicity_mul (by norm_num) (by omega), Nat.multiplicity_self (by norm_num),
        (Nat.multiplicity_eq_zero_iff.mpr (Or.inr (Or.inr (by omega))))]
    have hfac : (1 + 2 ^ (d + 2)) ^ (2 * m) - 1 =
        ((1 + 2 ^ (d + 2)) ^ m - 1) * ((1 + 2 ^ (d + 2)) ^ m + 1) := by
      rw [pow_mul', hb, Nat.add_sub_cancel]
      have : (b + 1) ^ 2 = b * (b + 1 + 1) + 1 := by ring
      rw [this, Nat.add_sub_cancel]
    rw [hfac, Nat.multiplicity_mul (by omega) (by omega), hD, hA, hB, hC] at h
    omega
  · have := padicValNat.pow_sub_pow hodd hx1 hdvd hnd hm
    rwa [one_pow, Nat.add_sub_cancel_left, Nat.multiplicity_prime_pow] at this

theorem UpperTheory.V.ZK.Ct.lte :
    ∀ l c ν E : ℕ, l.Prime → 1 ≤ c → (l = 2 → 2 ≤ c) → c ≤ ν → 1 ≤ E → 2 ≤ (1 + l ^ c) ^ E ∧ ((1 + l ^ c) ^ E - 1).factorization l = c + E.factorization l ∧ (((1 + l ^ c) ^ E) ^ l ^ (ν - c) - 1).factorization l = ν + E.factorization l := by
  intro l c ν E hl hc h2 hcν hE
  haveI := Fact.mk hl
  have hE0 : E ≠ 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · have : 2 ≤ 1 + l ^ c := by have := Nat.one_le_pow c l hl.pos; omega
    exact this.trans (Nat.le_self_pow hE0 _)
  · rw [Nat.factorization_def _ hl, Nat.factorization_def _ hl]
    simpa only [← Nat.padicValNat_def] using padic_val_one_add_pow_sub_one l c E hl hc h2 hE0
  · have hval := padic_val_one_add_pow_sub_one l c (E * l ^ (ν - c)) hl hc h2
      (mul_ne_zero hE0 (pow_ne_zero _ hl.ne_zero))
    simp only [Nat.padicValNat_def] at hval
    rw [Nat.factorization_def _ hl, Nat.factorization_def _ hl, ← pow_mul, hval,
      Nat.multiplicity_mul hE0 (pow_ne_zero _ hl.ne_zero), Nat.multiplicity_prime_pow]
    omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.PCount
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem card_tors (W : Type) [AddCommGroup W] [Finite W] (l : ℤ) (s : ℕ) :
    Nat.card (Submodule.torsionBy ℤ W (l ^ s)) ≤ Nat.card {w : W // l • w = 0} ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    let T := Submodule.torsionBy ℤ W (l ^ (s + 1))
    let m : T →ₗ[ℤ] W := l • T.subtype
    have hr : LinearMap.range m ≤ Submodule.torsionBy ℤ W (l ^ s) := by
      rintro _ ⟨w, rfl⟩
      rw [Submodule.mem_torsionBy_iff]
      have hw := (Submodule.mem_torsionBy_iff _ _).1 w.2
      change l ^ s • (l • (w : W)) = 0
      rw [smul_smul, ← pow_succ]
      exact hw
    have h1 : Nat.card T = Nat.card (T ⧸ LinearMap.ker m) * Nat.card (LinearMap.ker m) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker m).toAddSubgroup
    rw [Nat.card_congr m.quotKerEquivRange.toEquiv] at h1
    have h2 : Nat.card (LinearMap.range m) ≤ Nat.card (Submodule.torsionBy ℤ W (l ^ s)) :=
      Nat.card_le_card_of_injective (Submodule.inclusion hr) (Submodule.inclusion_injective hr)
    have h3 : Nat.card (LinearMap.ker m) ≤ Nat.card {w : W // l • w = 0} :=
      Nat.card_le_card_of_injective (fun k => ⟨((k : T) : W), k.2⟩)
        (fun a b hab => by
          have h := congrArg Subtype.val hab
          apply Subtype.ext
          apply Subtype.ext
          exact h)
    calc Nat.card T = Nat.card (LinearMap.range m) * Nat.card (LinearMap.ker m) := h1
      _ ≤ Nat.card (Submodule.torsionBy ℤ W (l ^ s)) * Nat.card {w : W // l • w = 0} :=
          Nat.mul_le_mul h2 h3
      _ ≤ Nat.card {w : W // l • w = 0} ^ s * Nat.card {w : W // l • w = 0} :=
          Nat.mul_le_mul_right _ ih
      _ = Nat.card {w : W // l • w = 0} ^ (s + 1) := (pow_succ _ _).symm

theorem UpperTheory.V.ZK.Ct.pCount :
    ∀ (W Z : Type) [AddCommGroup W] [AddCommGroup Z] [Finite W] (f : W →ₗ[ℤ] Z) (l s g : ℕ) (u : ℤ), l.Prime → ¬(l : ℤ) ∣ u → (∀ w, f w = 0 → (u * (l : ℤ) ^ s) • w = 0) → Nat.card {w : W // (l : ℤ) • w = 0} ≤ l ^ g → l ^ (Nat.card W).factorization l ≤ Nat.card (LinearMap.range f) * l ^ (s * g) := by
  intro W Z _ _ _ f l s g u hl hlu hker hW
  haveI := Fact.mk hl
  let K := LinearMap.ker f
  let gm : K →ₗ[ℤ] K := ((l : ℤ) ^ s) • LinearMap.id
  haveI : Finite (LinearMap.range f) := Finite.of_surjective _ f.surjective_rangeRestrict
  have hWc : Nat.card W = Nat.card (LinearMap.range f) * Nat.card K := by
    have h : Nat.card W = Nat.card (W ⧸ LinearMap.ker f) * Nat.card (LinearMap.ker f) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker f).toAddSubgroup
    rwa [Nat.card_congr f.quotKerEquivRange.toEquiv] at h
  have hKc : Nat.card K = Nat.card (LinearMap.range gm) * Nat.card (LinearMap.ker gm) := by
    have h : Nat.card K = Nat.card (K ⧸ LinearMap.ker gm) * Nat.card (LinearMap.ker gm) :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker gm).toAddSubgroup
    rwa [Nat.card_congr gm.quotKerEquivRange.toEquiv] at h
  have hR0 : Nat.card (LinearMap.range f) ≠ 0 := Nat.card_pos.ne'
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hRg0 : Nat.card (LinearMap.range gm) ≠ 0 := Nat.card_pos.ne'
  have hKg0 : Nat.card (LinearMap.ker gm) ≠ 0 := Nat.card_pos.ne'
  have hcop : ¬ l ∣ Nat.card (LinearMap.range gm) := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' l hd
    have hux : u • x = 0 := by
      rcases x with ⟨y, k, rfl⟩
      apply Subtype.ext
      apply Subtype.ext
      change u • ((l : ℤ) ^ s • ((k : K) : W)) = 0
      rw [smul_smul]
      exact hker _ k.2
    have hdv := addOrderOf_dvd_iff_zsmul_eq_zero.2 hux
    rw [hx] at hdv
    exact hlu hdv
  have hvK : (Nat.card K).factorization l = (Nat.card (LinearMap.ker gm)).factorization l := by
    rw [hKc, Nat.factorization_mul hRg0 hKg0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hcop, zero_add]
  have hA : Nat.card (LinearMap.ker gm) ≤ l ^ (s * g) := by
    calc Nat.card (LinearMap.ker gm) ≤ Nat.card (Submodule.torsionBy ℤ W ((l : ℤ) ^ s)) :=
          Nat.card_le_card_of_injective
            (fun a => ⟨((a : K) : W), by
              rw [Submodule.mem_torsionBy_iff]
              exact congrArg Subtype.val (LinearMap.mem_ker.1 a.2)⟩)
            (fun a b hab => by
              have h := congrArg Subtype.val hab
              apply Subtype.ext
              apply Subtype.ext
              exact h)
      _ ≤ Nat.card {w : W // (l : ℤ) • w = 0} ^ s := card_tors W l s
      _ ≤ (l ^ g) ^ s := Nat.pow_le_pow_left hW s
      _ = l ^ (s * g) := by rw [← pow_mul, mul_comm]
  have hR : l ^ (Nat.card (LinearMap.range f)).factorization l ≤ Nat.card (LinearMap.range f) :=
    Nat.ordProj_le l hR0
  have hKl : l ^ (Nat.card (LinearMap.ker gm)).factorization l ≤ Nat.card (LinearMap.ker gm) :=
    Nat.ordProj_le l hKg0
  rw [hWc, Nat.factorization_mul hR0 hK0, Finsupp.add_apply, pow_add, hvK]
  exact Nat.mul_le_mul hR (hKl.trans hA)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.KerFDelNm
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem UpperTheory.V.ZK.Ct.kerF_tele {Y I : Type} [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I) :
    ∑ j ∈ Finset.range D.n, (((D.a : ℤ) ^ j) • D.g ^ (D.n - j + 1) - ((D.a : ℤ) ^ (j + 1)) • D.g ^ (D.n - j))
      = (1 - (D.a : ℤ) ^ D.n) • D.g := by
  have key : ∀ j ∈ Finset.range D.n,
      ((D.a : ℤ) ^ j • D.g ^ (D.n - j + 1) - (D.a : ℤ) ^ (j + 1) • D.g ^ (D.n - j))
        = (fun k => (D.a : ℤ) ^ k • D.g ^ (D.n - k + 1)) j
          - (fun k => (D.a : ℤ) ^ k • D.g ^ (D.n - k + 1)) (j + 1) := by
    intro j hj
    have hj' : j < D.n := Finset.mem_range.mp hj
    have e : D.n - (j + 1) + 1 = D.n - j := by omega
    simp only [e]
  rw [Finset.sum_congr rfl key, Finset.sum_range_sub']
  simp only [pow_zero, one_smul, Nat.sub_zero, Nat.sub_self, zero_add, pow_one]
  rw [pow_succ, D.g_pow, one_mul, sub_smul, one_smul]

private theorem UpperTheory.V.ZK.Ct.kerF_nm_del {Y I : Type} [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I) :
    D.nm * D.del = (1 - (D.a : ℤ) ^ D.n) • D.g := by
  rw [← kerF_tele D]
  simp only [Dat.nm, Dat.del, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_mul_assoc, mul_sub, mul_smul_comm, mul_one, smul_sub, smul_smul, ← pow_succ, ← pow_succ]

private theorem UpperTheory.V.ZK.Ct.kerF_del_nm {Y I : Type} [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I) :
    D.del * D.nm = (1 - (D.a : ℤ) ^ D.n) • D.g := by
  rw [← kerF_tele D]
  simp only [Dat.nm, Dat.del, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_smul_comm, sub_mul, smul_mul_assoc, one_mul, smul_sub, smul_smul, ← pow_succ, ← pow_succ']

private theorem UpperTheory.V.ZK.Ct.kerF_tors {Y : Type} [AddCommGroup Y] (φ : Module.End ℤ Y) {t : Y}
    (ht : t ∈ Submodule.torsion ℤ Y) : φ t ∈ Submodule.torsion ℤ Y := by
  obtain ⟨c, hc⟩ := (Submodule.mem_torsion_iff t).mp ht
  refine (Submodule.mem_torsion_iff _).mpr ⟨c, ?_⟩
  rw [Submonoid.smul_def] at hc ⊢
  rw [← φ.map_smul, hc, map_zero]

private theorem UpperTheory.V.ZK.Ct.kerF_tors' {Y : Type} [AddCommGroup Y] {q : ℤ} (hq : q ≠ 0) {t : Y}
    (ht : q • t ∈ Submodule.torsion ℤ Y) : t ∈ Submodule.torsion ℤ Y := by
  obtain ⟨c, hc⟩ := (Submodule.mem_torsion_iff _).mp ht
  rw [Submonoid.smul_def, smul_smul] at hc
  have hne : (c : ℤ) * q ≠ 0 := mul_ne_zero (nonZeroDivisors.coe_ne_zero c) hq
  exact (Submodule.mem_torsion_iff _).mpr ⟨⟨(c : ℤ) * q, mem_nonZeroDivisors_of_ne_zero hne⟩, hc⟩

theorem UpperTheory.V.ZK.Ct.kerF :
    ∀ (Y I : Type) [AddCommGroup Y] [AddCommGroup I] (D : Dat Y I), ∀ (q s : ℕ) (u : ℤ), (D.a : ℤ) ^ D.n - 1 = q * u → ∃ f : D.W →ₗ[ℤ] Y ⧸ mt Y q, (∀ y : D.U, f (Submodule.Quotient.mk y) = Submodule.Quotient.mk ((s : ℤ) • D.nm y)) ∧ ∀ w, f w = 0 → (u * s) • w = 0 := by
  intro Y I _ _ D q s u h
  set R : Submodule ℤ Y := LinearMap.range D.del ⊔ Submodule.torsion ℤ Y with hRdef
  have hq0 : (q : ℤ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, sub_eq_zero] at h
    have h2 : (2 : ℤ) ≤ (D.a : ℤ) := by exact_mod_cast D.two_le
    have : (2 : ℤ) ≤ (D.a : ℤ) ^ D.n := le_trans h2 (le_self_pow₀ (by linarith) D.n_pos.ne')
    linarith
  have hnd : ∀ z : Y, D.nm (D.del z) = ((q : ℤ) * (-u)) • D.g z := by
    intro z
    have e : ((q : ℤ) * (-u)) = 1 - (D.a : ℤ) ^ D.n := by linarith
    rw [e, ← LinearMap.smul_apply, ← kerF_nm_del D, Module.End.mul_apply]
  have hdn : ∀ z : Y, D.del (D.nm z) = ((q : ℤ) * (-u)) • D.g z := by
    intro z
    have e : ((q : ℤ) * (-u)) = 1 - (D.a : ℤ) ^ D.n := by linarith
    rw [e, ← LinearMap.smul_apply, ← kerF_del_nm D, Module.End.mul_apply]
  let φ : D.U →ₗ[ℤ] Y ⧸ mt Y q := (mt Y q).mkQ ∘ₗ ((s : ℤ) • D.nm) ∘ₗ D.U.subtype
  have hker : R.submoduleOf D.U ≤ LinearMap.ker φ := by
    have hle : R ≤ (mt Y q).comap ((s : ℤ) • D.nm) := by
      refine sup_le ?_ ?_
      · rintro _ ⟨z, rfl⟩
        rw [Submodule.mem_comap, LinearMap.smul_apply, hnd]
        refine Submodule.mem_sup_left ⟨(s : ℤ) • (-u) • D.g z, ?_⟩
        simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
        congr 1
        ring
      · intro x hx
        rw [Submodule.mem_comap, LinearMap.smul_apply]
        exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (kerF_tors _ hx))
    intro y hy
    rw [LinearMap.mem_ker]
    have := hle hy
    rw [Submodule.mem_comap] at this
    simp only [φ, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact this
  refine ⟨(R.submoduleOf D.U).liftQ φ hker, ?_, ?_⟩
  · intro y
    rfl
  · intro w hw
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hw' : (s : ℤ) • D.nm (y : Y) ∈ mt Y q := by
      have := hw
      simp only [Submodule.liftQ_apply, φ, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, LinearMap.smul_apply, Submodule.coe_subtype] at this
      exact this
    set v : Y := (s : ℤ) • (y : Y) with hv
    have hnv : D.nm v = (s : ℤ) • D.nm (y : Y) := by rw [hv, map_smul]
    rw [← hnv] at hw'
    obtain ⟨a, ⟨z, rfl⟩, b, hb, hab⟩ := Submodule.mem_sup.mp hw'
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hab
    have hdel : (q : ℤ) • ((-u) • D.g v - D.del z) = D.del b := by
      have e1 := congrArg D.del hab
      rw [map_add (f := _), map_smul, hdn] at e1
      rw [smul_sub, smul_smul, ← e1]
      abel
    have htor : (-u) • D.g v - D.del z ∈ Submodule.torsion ℤ Y :=
      kerF_tors' hq0 (by rw [hdel]; exact kerF_tors _ hb)
    have hR : (u : ℤ) • D.g v ∈ R := by
      have e : (u : ℤ) • D.g v = -(D.del z + ((-u) • D.g v - D.del z)) := by
        rw [neg_smul]
        abel
      rw [e]
      exact R.neg_mem (R.add_mem (Submodule.mem_sup_left ⟨z, rfl⟩) (Submodule.mem_sup_right htor))
    have hcomm : Commute (D.g ^ (D.n - 1)) D.del := by
      show Commute _ (D.g - (D.a : ℤ) • 1)
      exact ((Commute.refl D.g).pow_left _).sub_right ((Commute.one_right _).smul_right _)
    have hstab : ∀ x ∈ R, (D.g ^ (D.n - 1)) x ∈ R := by
      intro x hx
      obtain ⟨c, ⟨z', rfl⟩, e, he, rfl⟩ := Submodule.mem_sup.mp hx
      rw [map_add (f := _), ← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply]
      exact R.add_mem (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right (kerF_tors _ he))
    have hgv : (D.g ^ (D.n - 1)) ((u : ℤ) • D.g v) = (u : ℤ) • v := by
      rw [map_smul, ← Module.End.mul_apply, ← pow_succ, Nat.sub_add_cancel D.n_pos, D.g_pow,
        Module.End.one_apply]
    have hfin : ((u * s : ℤ) • (y : Y)) ∈ R := by
      rw [mul_smul, ← hv, ← hgv]
      exact hstab _ hR
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hfin
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.SelLCard
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

open scoped nonZeroDivisors

private theorem ord_eq_count {L : Type} [Field L] [NumberField L] (p : HeightOneSpectrum (𝓞 L)) (y : Lˣ) :
    ordP p y = FractionalIdeal.count L p (FractionalIdeal.spanSingleton (𝓞 L)⁰ (y : L)) := by
  obtain ⟨a, b, hab⟩ := IsLocalization.exists_mk'_eq (𝓞 L)⁰ (y : L)
  have ha : a ≠ 0 := by
    rintro rfl
    exact y.ne_zero (by rw [← hab, IsLocalization.mk'_zero])
  have hb : (b : 𝓞 L) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hI : FractionalIdeal.spanSingleton (𝓞 L)⁰ (y : L) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr y.ne_zero
  have h : FractionalIdeal.spanSingleton (𝓞 L)⁰ (y : L) =
      FractionalIdeal.spanSingleton (𝓞 L)⁰ ((algebraMap (𝓞 L) L) b)⁻¹ * ((Ideal.span {a} : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton, ← hab,
      IsFractionRing.mk'_eq_div, div_eq_inv_mul]
  rw [FractionalIdeal.count_well_defined L p hI h, ordP, ← hab, HeightOneSpectrum.valuation_of_mk',
    p.intValuation_if_neg ha, p.intValuation_if_neg hb, ← WithZero.exp_sub, WithZero.log_exp]
  ring

private theorem ord_mul {L : Type} [Field L] [NumberField L] (p : HeightOneSpectrum (𝓞 L)) (x y : Lˣ) :
    ordP p (x * y) = ordP p x + ordP p y := by
  rw [ord_eq_count, ord_eq_count, ord_eq_count, Units.val_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul L p (FractionalIdeal.spanSingleton_ne_zero_iff.mpr x.ne_zero)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr y.ne_zero)]

private theorem ord_one {L : Type} [Field L] [NumberField L] (p : HeightOneSpectrum (𝓞 L)) :
    ordP p (1 : Lˣ) = 0 := by
  have := ord_mul p (1 : Lˣ) 1
  rw [mul_one] at this
  omega

private theorem ord_inv {L : Type} [Field L] [NumberField L] (p : HeightOneSpectrum (𝓞 L)) (x : Lˣ) :
    ordP p x⁻¹ = -ordP p x := by
  have := ord_mul p x x⁻¹
  rw [mul_inv_cancel, ord_one] at this
  omega

private theorem fi_ext {L : Type} [Field L] [NumberField L] {I J : FractionalIdeal (𝓞 L)⁰ L} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ p, FractionalIdeal.count L p I = FractionalIdeal.count L p J) : I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' L hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' L hJ]
  exact finprod_congr fun p => by rw [h p]

private theorem root_unique {L : Type} [Field L] [NumberField L] {l : ℕ} (hl : l ≠ 0)
    {I J : (FractionalIdeal (𝓞 L)⁰ L)ˣ} (h : I ^ l = J ^ l) : I = J := by
  refine Units.ext (fi_ext I.ne_zero J.ne_zero fun p => ?_)
  have h1 := congrArg (fun X : (FractionalIdeal (𝓞 L)⁰ L)ˣ => FractionalIdeal.count L p (X : FractionalIdeal (𝓞 L)⁰ L)) h
  simp only [Units.val_pow_eq_pow_val, FractionalIdeal.count_pow] at h1
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hl) h1

private theorem root_exists {L : Type} [Field L] [NumberField L] {l : ℕ} (y : Lˣ)
    (h : ∀ p : HeightOneSpectrum (𝓞 L), (l : ℤ) ∣ ordP p y) :
    ∃ I : (FractionalIdeal (𝓞 L)⁰ L)ˣ, I ^ l = toPrincipalIdeal (𝓞 L) L y := by
  have hf : ∀ᶠ p : HeightOneSpectrum (𝓞 L) in Filter.cofinite, ordP p y / l = 0 := by
    filter_upwards [FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (𝓞 L)⁰ (y : L))] with p hp
    rw [ord_eq_count, hp, Int.zero_ediv]
  have h0 : (∏ᶠ p : HeightOneSpectrum (𝓞 L), (p.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ (ordP p y / l)) ≠ 0 := by
    refine finprod_induction (fun X => X ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun p => ?_
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr p.ne_bot)
  refine ⟨Units.mk0 _ h0, Units.ext (fi_ext (Units.ne_zero _) (Units.ne_zero _) fun p => ?_)⟩
  rw [Units.val_pow_eq_pow_val, FractionalIdeal.count_pow, Units.val_mk0, FractionalIdeal.count_finprod L p _ hf,
    coe_toPrincipalIdeal, ← ord_eq_count, Int.mul_ediv_cancel' (h p)]

private theorem primes_card (L : Type) [Field L] [NumberField L] {l : ℕ} (hl : l.Prime) :
    Finite {p : HeightOneSpectrum (𝓞 L) // (l : 𝓞 L) ∈ p.asIdeal} ∧
      Nat.card {p : HeightOneSpectrum (𝓞 L) // (l : 𝓞 L) ∈ p.asIdeal} ≤ Module.finrank ℚ L := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hne : Ideal.span {(l : ℤ)} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]; exact hp.ne_zero
  haveI hm : (Ideal.span {(l : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal hne
  let f : {p : HeightOneSpectrum (𝓞 L) // (l : 𝓞 L) ∈ p.asIdeal} →
      IsDedekindDomain.primesOverFinset (Ideal.span {(l : ℤ)}) (𝓞 L) := fun p =>
    ⟨p.1.asIdeal, (IsDedekindDomain.mem_primesOverFinset_iff hne (𝓞 L)).mpr ⟨p.1.isPrime, ⟨by
      haveI := p.1.isPrime
      refine hm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact p.2⟩⟩⟩
  have hf : Function.Injective f := fun p q h =>
    Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  refine ⟨Finite.of_injective f hf, (Nat.card_le_card_of_injective f hf).trans ?_⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact Ideal.card_primesOverFinset_le_finrank (𝓞 L) ℚ L hne

private theorem zpow_eq_val {Q : Type} [Group Q] {l : ℕ} [NeZero l] (x : Q) (hx : x ^ l = 1) (m : ℤ) :
    x ^ m = x ^ (m : ZMod l).val := by
  rw [← zpow_natCast, ZMod.val_intCast, ← zpow_eq_zpow_emod' m hx]

private theorem units_card (L : Type) [Field L] [NumberField L] {l : ℕ} (hl : l.Prime) {Q : Type} [CommGroup Q]
    (hQ : ∀ x : Q, x ^ l = 1) (f : (𝓞 L)ˣ →* Q) :
    Finite f.range ∧ Nat.card f.range ≤ l ^ Module.finrank ℚ L := by
  haveI : NeZero l := ⟨hl.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Units.torsion L)
  let g : ZMod l × (Fin (Units.rank L) → ZMod l) → f.range := fun e =>
    ⟨f ((ζ : (𝓞 L)ˣ) ^ e.1.val * ∏ i, Units.fundSystem L i ^ (e.2 i).val), _, rfl⟩
  have hg : Function.Surjective g := by
    rintro ⟨_, u, rfl⟩
    obtain ⟨⟨t, e⟩, rfl, -⟩ := Units.exist_unique_eq_mul_prod L u
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hζ t)
    refine ⟨((k : ZMod l), fun i => (e i : ZMod l)), Subtype.ext ?_⟩
    simp only [g, map_mul, map_prod, map_pow, map_zpow, SubgroupClass.coe_zpow]
    rw [← zpow_eq_val _ (hQ _)]
    congr 1
    exact Finset.prod_congr rfl fun i _ => (zpow_eq_val _ (hQ _) _).symm
  refine ⟨Finite.of_surjective g hg, (Nat.card_le_card_of_surjective g hg).trans ?_⟩
  rw [Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_fin, ← pow_succ']
  refine Nat.pow_le_pow_right hl.pos ?_
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank L
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces L
  have h3 : 0 < Fintype.card (InfinitePlace L) := Fintype.card_pos
  unfold Units.rank
  omega

private theorem exp_card {l : ℕ} (hl : l.Prime) {C : Type} [Group C] [Finite C] (R : Subgroup C)
    (hR : ∀ x ∈ R, x ^ l = 1) : Nat.card R ≤ l ^ Nat.log 2 (Nat.card C) := by
  haveI : Fact l.Prime := ⟨hl⟩
  have hp : IsPGroup l R := fun x => ⟨1, Subtype.ext (by rw [pow_one]; exact hR x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have h1 : Nat.card R ≤ Nat.card C := Nat.card_le_card_of_injective _ R.subtype_injective
  rw [hk] at h1 ⊢
  refine Nat.pow_le_pow_right hl.pos (Nat.le_log_of_pow_le one_lt_two ?_)
  exact (Nat.pow_le_pow_left hl.two_le k).trans h1

private theorem index_le {G T : Type} [Group G] [Group T] [Finite T] (f : G →* T) (K : Subgroup G)
    (h : f.ker ≤ K) : K.index ≠ 0 ∧ K.index ≤ Nat.card f.range := by
  have hd := Subgroup.index_dvd_of_le h
  rw [Subgroup.index_ker] at hd
  have hp : 0 < Nat.card f.range := Nat.card_pos
  exact ⟨ne_zero_of_dvd_ne_zero hp.ne' hd, Nat.le_of_dvd hp hd⟩

theorem UpperTheory.V.ZK.Ct.selLCard :
    ∀ (L : Type) [Field L] [NumberField L] (l : ℕ), l.Prime → Finite (SelL l L) ∧ Nat.card (SelL l L) ≤ l ^ (2 * Module.finrank ℚ L + Nat.log 2 (classNumber L)) := by
  intro L _ _ l hl
  haveI : NeZero l := ⟨hl.ne_zero⟩
  let P : Subgroup Lˣ := (powMonoidHom l : Lˣ →* Lˣ).range
  let q : Lˣ →* Lˣ ⧸ P := QuotientGroup.mk' P
  let ι : (𝓞 L)ˣ →* Lˣ := Units.map (algebraMap (𝓞 L) L : 𝓞 L →* L)
  let π := toPrincipalIdeal (𝓞 L) L
  let U : Subgroup Lˣ := (q.comp ι).range.comap q
  let H0 : Subgroup Lˣ :=
    (powMonoidHom l : (FractionalIdeal (𝓞 L)⁰ L)ˣ →* (FractionalIdeal (𝓞 L)⁰ L)ˣ).range.comap π
  let H : Subgroup Lˣ :=
    { carrier := {y | ∀ p : HeightOneSpectrum (𝓞 L), (l : 𝓞 L) ∉ p.asIdeal → (l : ℤ) ∣ ordP p y}
      one_mem' := fun p _ => by rw [ord_one]; exact dvd_zero _
      mul_mem' := fun ha hb p hp => by rw [ord_mul]; exact dvd_add (ha p hp) (hb p hp)
      inv_mem' := fun ha p hp => by rw [ord_inv]; exact (ha p hp).neg_right }
  have hqk : q.ker = P := QuotientGroup.ker_mk' P
  have hql : ∀ z : Lˣ, q (z ^ l) = 1 := fun z => (QuotientGroup.eq_one_iff _).mpr ⟨z, rfl⟩
  have hπι : ∀ u, π (ι u) = 1 := fun u => by
    apply Units.ext
    rw [coe_toPrincipalIdeal, Units.val_one, ← FractionalIdeal.spanSingleton_one,
      FractionalIdeal.spanSingleton_eq_spanSingleton]
    refine ⟨u⁻¹, ?_⟩
    rw [Units.smul_def, Algebra.smul_def]
    change algebraMap (𝓞 L) L _ * algebraMap (𝓞 L) L _ = 1
    rw [← map_mul, Units.inv_mul, map_one]
  have hPU : q.ker ≤ U := fun y hy => by
    change q y ∈ (q.comp ι).range
    rw [MonoidHom.mem_ker.mp hy]; exact one_mem _
  have hU0 : U ≤ H0 := by
    rintro y ⟨u, hu⟩
    obtain ⟨z, hz⟩ := QuotientGroup.eq.mp hu
    refine ⟨π z, ?_⟩
    rw [powMonoidHom_apply] at hz ⊢
    rw [← map_pow, hz, map_mul, map_inv, hπι, inv_one, one_mul]
  have h0H : H0 ≤ H := by
    rintro y ⟨I, hI⟩ p -
    rw [ord_eq_count, ← coe_toPrincipalIdeal, ← hI, powMonoidHom_apply, Units.val_pow_eq_pow_val,
      FractionalIdeal.count_pow]
    exact Dvd.intro _ rfl

  have hQ : ∀ x : Lˣ ⧸ P, x ^ l = 1 := fun x => by
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective P x
    rw [← map_pow]; exact hql z
  obtain ⟨hf1, hc1⟩ := units_card L hl hQ (q.comp ι)
  have e1 : q.ker.relIndex U = Nat.card (q.comp ι).range := by
    rw [Subgroup.relIndex_ker, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective P)]
  have n1 : q.ker.relIndex U ≠ 0 := by rw [e1]; exact Nat.card_pos.ne'

  have hr : ∀ y : H0, ∃ I : (FractionalIdeal (𝓞 L)⁰ L)ˣ, I ^ l = π y := fun y => y.2
  choose r hr using hr
  let ψ : H0 →* ClassGroup (𝓞 L) := MonoidHom.mk' (fun y => ClassGroup.mk L (r y)) fun x y => by
    rw [← map_mul]
    congr 1
    apply root_unique hl.ne_zero
    rw [mul_pow, hr, hr, hr, Subgroup.coe_mul, map_mul]
  have hψ : ψ.ker ≤ U.subgroupOf H0 := by
    intro y hy
    obtain ⟨z, hz⟩ := (FractionalIdeal.isPrincipal_iff _).mp (ClassGroup.mk_eq_one_iff.mp hy)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact (r y).ne_zero (by rw [hz, FractionalIdeal.spanSingleton_zero])
    have h1 := congrArg Units.val (hr y)
    rw [Units.val_pow_eq_pow_val, hz, FractionalIdeal.spanSingleton_pow, coe_toPrincipalIdeal,
      FractionalIdeal.spanSingleton_eq_spanSingleton] at h1
    obtain ⟨u, hu⟩ := h1
    have h2 : (y : Lˣ) = ι u * Units.mk0 z hz0 ^ l := by
      apply Units.ext
      rw [← hu, Units.smul_def, Algebra.smul_def, Units.val_mul, Units.val_pow_eq_pow_val]
      rfl
    refine ⟨u, ?_⟩
    change q (ι u) = q y
    rw [h2, map_mul, hql, mul_one]
  obtain ⟨n2, c2⟩ := index_le ψ _ hψ
  have c2' : Nat.card ψ.range ≤ l ^ Nat.log 2 (classNumber L) := by
    rw [classNumber, ← Nat.card_eq_fintype_card]
    refine exp_card hl _ ?_
    rintro _ ⟨y, rfl⟩
    change ClassGroup.mk L (r y) ^ l = 1
    rw [← map_pow, hr, ClassGroup.mk_eq_one_iff, FractionalIdeal.isPrincipal_iff]
    exact ⟨_, coe_toPrincipalIdeal _⟩

  obtain ⟨hf3, hc3⟩ := primes_card L hl
  let φ : H →* Multiplicative ({p : HeightOneSpectrum (𝓞 L) // (l : 𝓞 L) ∈ p.asIdeal} → ZMod l) :=
    MonoidHom.mk' (fun y => Multiplicative.ofAdd fun p => (ordP p.1 (y : Lˣ) : ZMod l)) fun x y => by
      rw [← ofAdd_add]
      congr 1
      funext p
      rw [Subgroup.coe_mul, ord_mul, Int.cast_add, Pi.add_apply]
  have hφ : φ.ker ≤ H0.subgroupOf H := by
    intro y hy
    refine root_exists (y : Lˣ) fun p => ?_
    by_cases hp : (l : 𝓞 L) ∈ p.asIdeal
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
        (congrFun (congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp hy)) ⟨p, hp⟩)
    · exact y.2 p hp
  obtain ⟨n3, c3⟩ := index_le φ _ hφ
  have c3' : Nat.card φ.range ≤ l ^ Module.finrank ℚ L := by
    refine (Nat.card_le_card_of_injective _ φ.range.subtype_injective).trans ?_
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod]
    exact Nat.pow_le_pow_right hl.pos hc3

  have hS : SelL l L = (H.map q : Set (Lˣ ⧸ P)) := by
    ext x
    exact ⟨fun ⟨y, h1, h2⟩ => ⟨y, h2, h1⟩, fun ⟨y, h1, h2⟩ => ⟨y, h2, h1⟩⟩
  have hcard : Nat.card (SelL l L) = q.ker.relIndex U * U.relIndex H0 * H0.relIndex H := by
    rw [Subgroup.relIndex_mul_relIndex _ _ _ hPU hU0,
      Subgroup.relIndex_mul_relIndex _ _ _ (hPU.trans hU0) h0H, Subgroup.relIndex_ker, hS]
    rfl
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [hcard]
    exact mul_ne_zero (mul_ne_zero n1 n2) n3
  · rw [hcard, show 2 * Module.finrank ℚ L + Nat.log 2 (classNumber L) =
      Module.finrank ℚ L + Nat.log 2 (classNumber L) + Module.finrank ℚ L by ring, pow_add, pow_add]
    exact Nat.mul_le_mul (Nat.mul_le_mul (e1.trans_le hc1) (c2.trans c2')) (c3.trans c3')
end
