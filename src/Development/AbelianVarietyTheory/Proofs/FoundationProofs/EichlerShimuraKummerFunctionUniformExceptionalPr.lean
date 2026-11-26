module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCoeffRingHomMapCoeff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveQuotientLevelPrimeTo
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPowOfGaussValuationCongrOneAlmostAllPrimes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationSubringGaussModularFunction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerCongruenceModularFunctionTowerLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NqSubGalSmall
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES


open GlobalTheory.KroneckerCongruence in
theorem nq_sub_gal_small : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (M q : ℕ), 0 < M → q.Prime → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s →
    ∀ a : X.K, Lev X M a → IntC X V a → SmallC X V (Nq X M q a - X.gal s a) := by
  intro Ω _ _ _ ε X M q hM hq V s hFr f hf hfV
  obtain ⟨hqV, hs⟩ := hFr
  have hε : Function.Injective ε := ε.injective
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  set ρ := IsLocalRing.residue V with hρ_def
  have hρ0 : ∀ x : V, ρ x = 0 ↔ V.valuation (x : Ω) < 1 := fun x => by
    rw [hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  haveI : CharP (IsLocalRing.ResidueField V) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    have : ρ (q : V) = 0 := (hρ0 _).2 (by simpa [ValuationSubring.mem_nonunits_iff] using hqV)
    simpa using this)
  have hfrob : ∀ x : V, ρ ⟨s x, (hs x x.2).1⟩ = ρ x ^ q := by
    intro x
    rw [← sub_eq_zero, ← map_pow, ← map_sub, hρ0]
    simpa using (hs x x.2).2.2
  set c := X.exp f with hc
  have hdet : ∀ j : ℕ, 0 < (!![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    intro j; simp [Matrix.det_fin_two]; exact_mod_cast hq.pos
  have hFj : ∀ (j : ℕ) (t : ℚ), (X.exp (X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f)).coeff t =
      eOm ε (t * j * M) * c.coeff (t * q) := by
    intro j t
    have h := X.exp_upper (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) (by rw [ent_toGQ _ (hdet j)]; simp) f (t * q)
    rw [ent_toGQ _ (hdet j), ent_toGQ _ (hdet j), ent_toGQ _ (hdet j)] at h
    simp at h
    convert h using 2 <;> first | field_simp | (congr 1; field_simp)
  have hw : ∀ (j : ℕ) (t : ℚ), c.coeff (t * q) ≠ 0 → ∃ h : eOm ε (t * j * M) ∈ V, ρ ⟨_, h⟩ = 1 := by
    intro j t ht
    have h1 : eOm ε (t * j * M) ^ q = 1 := by
      rw [← eOm_mul_nat hε, show (q : ℚ) * (t * j * M) = j * (t * q * M) by ring, eOm_mul_nat hε,
        eOm_level X M f hf _ ht, one_pow]
    have hmem : eOm ε (t * j * M) ∈ V := mem_of_pow_eq_one V hq.ne_zero h1
    refine ⟨hmem, ?_⟩
    have h2 : (⟨_, hmem⟩ : V) ^ q = 1 := Subtype.ext (by simpa using h1)
    have h3 : (ρ ⟨_, hmem⟩ - 1) ^ q = 0 := by rw [sub_pow_char, ← map_pow, h2, map_one, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff hq.ne_zero |>.1 h3)
  have memF : ∀ (j : ℕ) (t : ℚ), (X.exp (X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f)).coeff t ∈ V := by
    intro j t
    rw [hFj]
    by_cases h0 : c.coeff (t * q) = 0
    · rw [h0, mul_zero]; exact zero_mem V
    · exact mul_mem (hw j t h0).1 (hfV _)
  have redF : ∀ (j : ℕ) (t : ℚ), ρ ⟨_, memF j t⟩ = ρ ⟨_, hfV (t * q)⟩ := by
    intro j t
    by_cases h0 : c.coeff (t * q) = 0
    · exact congrArg ρ (Subtype.ext (by simp only; rw [hFj, h0, mul_zero]))
    · obtain ⟨hm, h1⟩ := hw j t h0
      have e : (⟨_, memF j t⟩ : V) = ⟨_, hm⟩ * ⟨_, hfV (t * q)⟩ :=
        Subtype.ext (by simp only [MulMemClass.mk_mul_mk]; rw [hFj])
      rw [e, map_mul, h1, one_mul]
  have memC : ∀ t : ℚ, (X.exp (X.gal s f)).coeff t ∈ V := by
    intro t; rw [X.gal_exp]; exact (hs _ (hfV t)).1
  set LF : ℕ → HahnSeries ℚ V := fun j => liftV V _ (memF j) with hLF
  set LC := liftV V _ memC with hLC
  have h1 : ∀ j, hahnSeriesCoeffRingHomMap ρ (LF j) = hahnSeriesCoeffRingHomMap ρ (LF 0) := by
    intro j; ext t; rw [hahnSeriesCoeffRingHomMap_coeff, hahnSeriesCoeffRingHomMap_coeff]; exact (redF j t).trans (redF 0 t).symm
  have h2 : hahnSeriesCoeffRingHomMap ρ (LF 0) ^ q = hahnSeriesCoeffRingHomMap ρ LC := by
    ext t
    rw [coeff_pow_char q, hahnSeriesCoeffRingHomMap_coeff, hahnSeriesCoeffRingHomMap_coeff]
    show ρ ⟨_, memF 0 (t / q)⟩ ^ q = ρ ⟨_, memC t⟩
    rw [redF 0 (t / q), ← hfrob]
    exact congrArg ρ (Subtype.ext (by simp only; rw [X.gal_exp, div_mul_cancel₀ t hq0]))
  have hexp : X.exp ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f) - X.gal s f) =
      hahnSeriesCoeffRingHomMap V.subtype ((∏ j ∈ Finset.range q, LF j) - LC) := by
    simp only [map_sub, map_prod, hLF, hLC, map_liftV]
  have hW : hahnSeriesCoeffRingHomMap ρ ((∏ j ∈ Finset.range q, LF j) - LC) = 0 := by
    rw [map_sub, map_prod, Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_const, Finset.card_range, h2, sub_self]
  intro r
  unfold Nq
  rw [hexp, hahnSeriesCoeffRingHomMap_coeff, ValuationSubring.mem_nonunits_iff]
  refine (hρ0 (((∏ j ∈ Finset.range q, LF j) - LC).coeff r)).1 ?_
  rw [← hahnSeriesCoeffRingHomMap_coeff, hW]
  rfl

end GlobalTheory.KZ.ES
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerCongruenceFrobeniusDiag
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerCongruenceFrobeniusDiag
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES


open GlobalTheory.KroneckerCongruence in
theorem kron_frob_diag : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (q : ℕ), q.Prime → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ a : X.K, IntC X V a →
    SmallC X V (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) a - (X.gal s.symm a) ^ q) := by
  intro Ω _ _ _ ε X q hq V s hs a ha r
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hε : Function.Injective ε := ε.injective
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  set ρ := IsLocalRing.residue V with hρ_def
  have hρ0 : ∀ x : V, ρ x = 0 ↔ V.valuation (x : Ω) < 1 := fun x => by
    rw [hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  haveI : CharP (IsLocalRing.ResidueField V) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    have : ρ (q : V) = 0 := (hρ0 _).2 (by simpa [ValuationSubring.mem_nonunits_iff] using hs.1)
    simpa using this)
  have hfrob : ∀ x : V, ρ ⟨s x, (hs.2 x x.2).1⟩ = ρ x ^ q := by
    intro x
    rw [← sub_eq_zero, ← map_pow, ← map_sub, hρ0]
    simpa using (hs.2 x x.2).2.2
  set c := X.exp a with hc
  have hdq : 0 < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two]; exact_mod_cast hq.pos
  have hA : (X.exp (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) a)).coeff r = c.coeff (r / q) := by
    have h := X.exp_upper (toGQ !![(q : ℤ), 0; 0, 1]) (by rw [ent_toGQ _ hdq]; simp) a (r / q)
    rw [ent_toGQ _ hdq, ent_toGQ _ hdq, ent_toGQ _ hdq] at h
    simp [eOm_zero hε, hq0] at h
    rw [← h]
  set B := X.exp (X.gal s.symm a) with hB
  have hBc : ∀ t, B.coeff t = s.symm (c.coeff t) := fun t => by rw [hB, X.gal_exp]
  have hBV : ∀ t, B.coeff t ∈ V := fun t => by rw [hBc]; exact (hs.2 _ (ha t)).2.1
  have hBq : X.exp ((X.gal s.symm a) ^ q) = hahnSeriesCoeffRingHomMap V.subtype (liftV V B hBV ^ q) := by
    rw [map_pow, map_pow, map_liftV]
  set y : V := (liftV V B hBV ^ q).coeff r with hy_def
  have hy : (X.exp ((X.gal s.symm a) ^ q)).coeff r = (y : Ω) := by rw [hBq, hahnSeriesCoeffRingHomMap_coeff]; rfl
  have hρy : ρ y = ρ ⟨c.coeff (r / q), ha _⟩ := by
    have h1 : ρ y = (hahnSeriesCoeffRingHomMap ρ (liftV V B hBV ^ q)).coeff r := by rw [hahnSeriesCoeffRingHomMap_coeff]
    rw [h1, map_pow, coeff_pow_char q, hahnSeriesCoeffRingHomMap_coeff]
    have h2 : (liftV V B hBV).coeff (r / q) = ⟨s.symm (c.coeff (r / q)), (hs.2 _ (ha _)).2.1⟩ :=
      Subtype.ext (hBc _)
    rw [h2, ← hfrob]
    congr 1
    apply Subtype.ext
    simp
  rw [map_sub, HahnSeries.coeff_sub, hA, hy]
  have hmem : c.coeff (r / q) - (y : Ω) = ((⟨c.coeff (r / q), ha _⟩ - y : V) : Ω) := rfl
  rw [hmem, ValuationSubring.mem_nonunits_iff, ← hρ0, map_sub, hρy, sub_self]

end GlobalTheory.KZ.ES
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerCongruenceFrobeniusDiagStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kronecker_congruence_frobenius_diag : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (q : ℕ), q.Prime → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ a : X.K, IntC X V a → SmallC X V (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) a - (X.gal s.symm a) ^ q) := by
  first | exact @GlobalTheory.KZ.ES.kron_frob_diag | exact GlobalTheory.KZ.ES.kron_frob_diag | (intros; apply GlobalTheory.KZ.ES.kron_frob_diag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTranslateNormProductEqOfDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTranslateNormProductEqOfDvd
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem toGQ_mul_pos' (m m' : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) (h' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have hmm : 0 < (m * m').det := by rw [Matrix.det_mul]; exact mul_pos h h'
  unfold toGQ
  rw [dite_eq_left hmm, dite_eq_left h, dite_eq_left h']
  apply Subtype.ext
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_mul] at *
  exact Matrix.map_mul (f := Int.castRingHom ℚ)

theorem sl_trans_of_lev {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) (f : X.K)
    (hf : Lev X M f) (t : ℕ) : X.sl (toGQ !![1, ((t * M : ℕ) : ℤ); 0, 1]) f = f := by
  let γ : SL(2, ℤ) := ⟨!![1, ((t * M : ℕ) : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩
  have hγ : γ ∈ CongruenceSubgroup.Gamma M := by
    rw [CongruenceSubgroup.Gamma_mem]
    simp [γ]
  have e : toGQ !![1, ((t * M : ℕ) : ℤ); 0, 1] = ofSL γ := Betti.toGQ_sl γ
  rw [e]; exact hf γ hγ

theorem Nq_eq_of_dvd : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (M M' q : ℕ) (f : X.K), 0 < q → M ∣ M' → Nat.Coprime q M' → Lev X M f → Nq X M q f = Nq X M' q f := by
  intro Ω _ _ _ ε X M M' q f hq hdvd hcop hlev
  obtain ⟨e, rfl⟩ := hdvd
  have hqe : Nat.Coprime q e := Nat.Coprime.coprime_dvd_right (dvd_mul_left e M) hcop
  set g : ℕ → X.K := fun i => X.sl (toGQ !![1, ((i : ℤ) * (M : ℤ)); 0, (q : ℤ)]) f with hg
  have step : ∀ j : ℕ, X.sl (toGQ !![1, ((j : ℤ) * ((M * e : ℕ) : ℤ)); 0, (q : ℤ)]) f = g (j * e % q) := by
    intro j
    have hm : !![1, ((j : ℤ) * ((M * e : ℕ) : ℤ)); 0, (q : ℤ)] =
        !![1, (((j * e / q) * M : ℕ) : ℤ); 0, 1] * !![1, (((j * e % q : ℕ) : ℤ) * (M : ℤ)); 0, (q : ℤ)] := by
      have hd := Nat.mod_add_div (j * e) q
      generalize j * e % q = a at hd ⊢
      generalize j * e / q = b at hd ⊢
      have hdz : (a : ℤ) + (q : ℤ) * (b : ℤ) = (j : ℤ) * (e : ℤ) := by exact_mod_cast hd
      ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (M : ℤ) * hdz.symm
    have h1 : (0 : ℤ) < (!![1, (((j * e / q) * M : ℕ) : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      simp [Matrix.det_fin_two]
    have h2 : (0 : ℤ) < (!![1, (((j * e % q : ℕ) : ℤ) * (M : ℤ)); 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      simp [Matrix.det_fin_two]; exact_mod_cast hq
    rw [hm, toGQ_mul_pos' _ _ h1 h2, X.sl_mul, sl_trans_of_lev X M f hlev]
  have hinj : Set.InjOn (fun j => j * e % q) (Finset.range q : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h' : a * e ≡ b * e [MOD q] := hab
    have := Nat.ModEq.cancel_right_of_coprime (by simpa [Nat.gcd_comm] using hqe) h'
    simpa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
  have himg : (Finset.range q).image (fun j => j * e % q) = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨j, _, rfl⟩ := hx
      exact Nat.mod_lt _ hq
    · rw [Finset.card_image_of_injOn hinj]
  unfold Nq
  simp_rw [step]
  show ∏ j ∈ Finset.range q, g j = _
  rw [← Finset.prod_image (f := g) hinj, himg]

end GlobalTheory.KZ.ES
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTranslateNormProductEqOfDvdStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTranslateNormProduct_eq_of_dvd : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (M M' q : ℕ) (f : X.K), 0 < q → M ∣ M' → Nat.Coprime q M' → Lev X M f → Nq X M q f = Nq X M' q f := by
  first | exact @GlobalTheory.KZ.ES.Nq_eq_of_dvd | exact GlobalTheory.KZ.ES.Nq_eq_of_dvd | (intros; apply GlobalTheory.KZ.ES.Nq_eq_of_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerCongruenceModularFunctionTowerLevel
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem kc_val_one_of_inv {V : ValuationSubring Ω} {x : Ω} (hx : x ∈ V) (hi : x⁻¹ ∈ V) (h0 : x ≠ 0) :
    V.valuation x = 1 := by
  have h1 := (V.valuation_le_one_iff x).2 hx
  have h2 := (V.valuation_le_one_iff x⁻¹).2 hi
  rw [map_inv₀] at h2
  have hne : V.valuation x ≠ 0 := by simpa using h0
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 h2)

theorem kc_inv_of_val_one {V : ValuationSubring Ω} {x : Ω} (h : V.valuation x = 1) :
    x ∈ V ∧ x⁻¹ ∈ V ∧ x ≠ 0 := by
  have h0 : x ≠ 0 := by rintro rfl; simp at h
  refine ⟨(V.valuation_le_one_iff x).1 h.le, (V.valuation_le_one_iff x⁻¹).1 ?_, h0⟩
  rw [map_inv₀, h, inv_one]

theorem kc_prim_gal (X : Tower Ω ε) (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ x ∈ V, s x ∈ V)
    {a : X.K} (ha : Prim X V a) : Prim X V (X.gal s a) := by
  obtain ⟨hI, r, hr⟩ := ha
  refine ⟨fun r' => by rw [X.gal_exp]; exact hs _ (hI r'), r, ?_⟩
  rw [X.gal_exp]
  obtain ⟨h1, h2, h3⟩ := kc_inv_of_val_one hr
  exact kc_val_one_of_inv (hs _ h1) (by rw [← map_inv₀]; exact hs _ h2) (by simpa using h3)

theorem kc_ne_zero_of_prim {X : Tower Ω ε} {V : ValuationSubring Ω} {a : X.K} (ha : Prim X V a) : a ≠ 0 := by
  rintro rfl
  obtain ⟨_, r, hr⟩ := ha
  simp at hr

theorem kc_Nq_mul (X : Tower Ω ε) (M q : ℕ) (f g : X.K) : Nq X M q (f * g) = Nq X M q f * Nq X M q g := by
  simp only [Nq, map_mul, Finset.prod_mul_distrib]

theorem kc_Nq_const (X : Tower Ω ε) (M q : ℕ) (c : Ω) (a : X.K) :
    Nq X M q (algebraMap Ω X.K c * a) = algebraMap Ω X.K c ^ q * Nq X M q a := by
  simp only [Nq, map_mul, AlgEquiv.commutes, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

theorem kc_Nq_ne_zero (X : Tower Ω ε) (M q : ℕ) {f : X.K} (hf : f ≠ 0) : Nq X M q f ≠ 0 := by
  simp only [Nq]
  exact Finset.prod_ne_zero_iff.2 fun j _ => by simpa using hf

theorem kc_gal_const (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext r
  show (X.exp (X.gal s (algebraMap Ω X.K c))).coeff r = (X.exp (algebraMap Ω X.K (s c))).coeff r
  rw [X.gal_exp, AlgHom.commutes, AlgHom.commutes]
  have e : ∀ x : Ω, (algebraMap Ω (HahnSeries ℚ Ω) x).coeff r = if r = 0 then x else 0 := by
    intro x
    rw [HahnSeries.algebraMap_apply']
    have : algebraMap Ω (PowerSeries Ω) x = PowerSeries.C x := rfl
    rw [this, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single]
    simp
  rw [e, e]
  split_ifs <;> simp

theorem kc_div_sub_one {L : Type} [Field L] (W : ValuationSubring L) {x y : L} (hy : W.valuation y = 1)
    (h : W.valuation (x - y) < 1) : W.valuation (x / y - 1) < 1 := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  rw [show x / y - 1 = (x - y) / y by field_simp, map_div₀, hy, div_one]
  exact h

theorem kc_quot_one {L : Type} [Field L] (W : ValuationSubring L) {x y : L} (hx : W.valuation (x - 1) < 1)
    (hy : W.valuation (y - 1) < 1) : W.valuation (x / y - 1) < 1 := by
  have hy1 : W.valuation y = 1 := by
    have := Valuation.map_one_add_of_lt W.valuation hy
    simpa using this
  apply kc_div_sub_one W hy1
  have e : x - y = (x - 1) - (y - 1) := by ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hx hy)

theorem kron_cong_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ W : ValuationSubring X.K, Dom X V W → ∀ (k : ℕ) (f : X.K), f ≠ 0 → Lev X (M₀ * l ^ k) f → (∃ c : Ω, W.valuation (algebraMap Ω X.K c * Nq X (M₀ * l ^ k) q f / X.gal s f - 1) < 1) ∧ ∃ c : Ω, W.valuation (algebraMap Ω X.K c * X.sl (toGQ !![(q : ℤ), 0; 0, 1]) f / (X.gal s.symm f) ^ q - 1) < 1 := by
  intro Ω _ _ _ ε X hj l M₀ hl hM₀
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_primitive_quotient_level_prime_to ε X hj l M₀ hl hM₀
  refine ⟨S, fun q hq hqS V s hF W hD k f hf hlev => ?_⟩
  obtain ⟨M', a, b, c, hM', hcop, hdvd, hla, hlb, hpa, hpb, hc, hfb⟩ := hS q hq hqS V hF.1 k f hf hlev
  have ha0 := kc_ne_zero_of_prim hpa
  have hb0 := kc_ne_zero_of_prim hpb
  have hsV : ∀ x ∈ V, s x ∈ V := fun x hx => (hF.2 x hx).1
  have hsV' : ∀ x ∈ V, s.symm x ∈ V := fun x hx => (hF.2 x hx).2.1
  have hC : algebraMap Ω X.K c ≠ 0 := (_root_.map_ne_zero _).2 hc
  have hgal : ∀ (t : Ω ≃ₐ[ℚ] Ω) (g : X.K), g ≠ 0 → X.gal t g ≠ 0 := fun t g hg => by simpa using hg
  have hE : ∀ t : Ω ≃ₐ[ℚ] Ω, X.gal t f = algebraMap Ω X.K (t c) * X.gal t a / X.gal t b := fun t => by
    rw [eq_div_iff (hgal t b hb0), ← map_mul, hfb, map_mul, kc_gal_const]
  have hC' : ∀ t : Ω ≃ₐ[ℚ] Ω, algebraMap Ω X.K (t c) ≠ 0 := fun t => (_root_.map_ne_zero _).2 (by simpa using hc)
  constructor
  · refine ⟨s c / c ^ q, ?_⟩
    have hN : Nq X (M₀ * l ^ k) q f = Nq X M' q f := GlobalTheory.T.heckeTranslateNormProduct_eq_of_dvd ε X _ _ q f hq.pos hdvd hcop hlev
    have A1 := kc_div_sub_one W (hD.2.2 _ (kc_prim_gal X V s hsV hpa))
      (hD.2.1 _ (GlobalTheory.KZ.ES.nq_sub_gal_small ε X M' q hM' hq V s hF a hla hpa.1))
    have B1 := kc_div_sub_one W (hD.2.2 _ (kc_prim_gal X V s hsV hpb))
      (hD.2.1 _ (GlobalTheory.KZ.ES.nq_sub_gal_small ε X M' q hM' hq V s hF b hlb hpb.1))
    have hNb := kc_Nq_ne_zero X M' q hb0
    have E1 : Nq X M' q f = algebraMap Ω X.K c ^ q * Nq X M' q a / Nq X M' q b := by
      rw [eq_div_iff hNb, ← kc_Nq_mul, hfb, kc_Nq_const]
    have key : algebraMap Ω X.K (s c / c ^ q) * Nq X (M₀ * l ^ k) q f / X.gal s f
        = (Nq X M' q a / X.gal s a) / (Nq X M' q b / X.gal s b) := by
      have h1 := hgal s a ha0
      have h2 := hgal s b hb0
      have h3 := hC' s
      rw [hN, E1, hE s, map_div₀, map_pow]
      field_simp
    rw [key]
    exact kc_quot_one W A1 B1
  · refine ⟨(s.symm c) ^ q / c, ?_⟩
    have A1 := kc_div_sub_one W (by rw [map_pow, hD.2.2 _ (kc_prim_gal X V s.symm hsV' hpa), one_pow])
      (hD.2.1 _ (GlobalTheory.T.kronecker_congruence_frobenius_diag ε X q hq V s hF a hpa.1))
    have B1 := kc_div_sub_one W (by rw [map_pow, hD.2.2 _ (kc_prim_gal X V s.symm hsV' hpb), one_pow])
      (hD.2.1 _ (GlobalTheory.T.kronecker_congruence_frobenius_diag ε X q hq V s hF b hpb.1))
    generalize toGQ !![(q : ℤ), 0; 0, 1] = T at A1 B1 ⊢
    have hTb : X.sl T b ≠ 0 := by simpa using hb0
    have E1 : X.sl T f = algebraMap Ω X.K c * X.sl T a / X.sl T b := by
      rw [eq_div_iff hTb, ← map_mul, hfb, map_mul, AlgEquiv.commutes]
    have key : algebraMap Ω X.K ((s.symm c) ^ q / c) * X.sl T f / (X.gal s.symm f) ^ q
        = (X.sl T a / (X.gal s.symm a) ^ q) / (X.sl T b / (X.gal s.symm b) ^ q) := by
      have h1 := hgal s.symm a ha0
      have h2 := hgal s.symm b hb0
      have h3 := hC' s.symm
      rw [E1, hE s.symm, map_div₀, map_pow, div_pow, mul_pow]
      field_simp
    rw [key]
    exact kc_quot_one W A1 B1

end GlobalTheory.KZ.ES
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerCongruenceModularFunctionTowerLevelStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kronecker_congruence_modularFunctionTower_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ W : ValuationSubring X.K, Dom X V W → ∀ (k : ℕ) (f : X.K), f ≠ 0 → Lev X (M₀ * l ^ k) f → (∃ c : Ω, W.valuation (algebraMap Ω X.K c * Nq X (M₀ * l ^ k) q f / X.gal s f - 1) < 1) ∧ ∃ c : Ω, W.valuation (algebraMap Ω X.K c * X.sl (toGQ !![(q : ℤ), 0; 0, 1]) f / (X.gal s.symm f) ^ q - 1) < 1 := by
  first | exact @GlobalTheory.KZ.ES.kron_cong_level | exact GlobalTheory.KZ.ES.kron_cong_level | (intros; apply GlobalTheory.KZ.ES.kron_cong_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDomGauss
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem exists_dom_gauss : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ V : ValuationSubring Ω, ∃ W : ValuationSubring X.K, Dom X V W ∧ Gauss X.jK V W := by
  intro Ω _ _ _ ε X V
  classical
  open GaussDom in
  haveI : (RingHom.ker (redA V X.exp)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨W, hA, hinv, hlt⟩ :=
    ReciprocityTheory.ChartRestriction.G.AR.Up.NOrd.exists_val_of_prime (GaussDom.intA V X.exp) (RingHom.ker (GaussDom.redA V X.exp))
  have hker : ∀ x : GaussDom.intA V X.exp, x ∈ RingHom.ker (GaussDom.redA V X.exp) ↔
      ∀ r, (X.exp x).coeff r ∈ V.nonunits :=
    fun x => (RingHom.mem_ker).trans (GaussDom.redA_eq_zero V X.exp x)
  have hone : ∀ x : GaussDom.intA V X.exp, x ∉ RingHom.ker (GaussDom.redA V X.exp) → W.valuation (x : X.K) = 1 := by
    intro x hx
    have hx0 : (x : X.K) ≠ 0 := by
      intro h0
      apply hx
      have : x = 0 := Subtype.ext h0
      rw [this]
      exact Ideal.zero_mem _
    have h1 := (W.valuation_le_one_iff _).2 (hA x)
    have h2 := (W.valuation_le_one_iff _).2 (hinv x hx)
    rw [map_inv₀] at h2
    have hv0 : W.valuation (x : X.K) ≠ 0 := by simpa using hx0
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hv0)).1 h2)
  have hj3 : ∀ r, (X.exp X.jK).coeff r ∈ V := fun r => by
    obtain ⟨n, hn⟩ := X.j_exp.2.2 r
    rw [hn]
    exact intCast_mem V n
  have hj1 : (X.exp X.jK).coeff (-1) = 1 := X.j_exp.1
  have hj2 : ∀ r : ℚ, r < -1 → (X.exp X.jK).coeff r = 0 := X.j_exp.2.1
  refine ⟨W, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro f hf
    exact hA ⟨f, (GaussDom.mem_intA V X.exp f).2 hf⟩
  · intro f hf
    have hfi : f ∈ GaussDom.intA V X.exp :=
      (GaussDom.mem_intA V X.exp f).2 (fun r => V.valuation_le_one_iff _ |>.1 (le_of_lt
        ((ValuationSubring.mem_nonunits_iff _).1 (hf r))))
    exact hlt ⟨f, hfi⟩ ((hker _).2 hf)
  · rintro f ⟨hf, r, hr⟩
    apply hone ⟨f, (GaussDom.mem_intA V X.exp f).2 hf⟩
    intro hk
    have := (hker _).1 hk r
    rw [ValuationSubring.mem_nonunits_iff] at this
    exact absurd hr (ne_of_lt this)
  · intro a
    constructor
    · intro ha
      by_contra hnot
      have ha0 : a ≠ 0 := fun h => hnot (h ▸ V.zero_mem)
      have hinvV : a⁻¹ ∈ V := (V.mem_or_inv_mem a).resolve_left hnot
      have hnu : a⁻¹ ∈ V.nonunits := by
        rw [ValuationSubring.mem_nonunits_iff]
        refine lt_of_le_of_ne ((V.valuation_le_one_iff _).2 hinvV) ?_
        intro h1
        apply hnot
        rw [map_inv₀, inv_eq_one] at h1
        exact (V.valuation_le_one_iff a).1 (le_of_eq h1)
      have hm : algebraMap Ω X.K a⁻¹ ∈ GaussDom.intA V X.exp := GaussDom.const_mem V X.exp _ hinvV
      have hk : (⟨_, hm⟩ : GaussDom.intA V X.exp) ∈ RingHom.ker (GaussDom.redA V X.exp) := by
        rw [hker]
        intro r
        show (X.exp (algebraMap Ω X.K a⁻¹)).coeff r ∈ V.nonunits
        rw [GaussDom.coeff_const]
        split_ifs
        · exact hnu
        · exact GaussDom.zero_mem_nonunits V
      have h3 : W.valuation (algebraMap Ω X.K a⁻¹) < 1 := hlt _ hk
      have h4 := (W.valuation_le_one_iff _).2 ha
      have h5 : W.valuation (algebraMap Ω X.K a) * W.valuation (algebraMap Ω X.K a⁻¹) = 1 := by
        rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one]
      have h6 : W.valuation (algebraMap Ω X.K a) * W.valuation (algebraMap Ω X.K a⁻¹) ≤
          1 * W.valuation (algebraMap Ω X.K a⁻¹) := by gcongr
      rw [h5, one_mul] at h6
      exact absurd (lt_of_le_of_lt h6 h3) (lt_irrefl 1)
    · intro ha
      exact hA ⟨_, GaussDom.const_mem V X.exp a ha⟩
  · rintro P hP ⟨i0, hne, hi0, hi0'⟩
    have hjA : X.jK ∈ GaussDom.intA V X.exp := (GaussDom.mem_intA V X.exp X.jK).2 hj3
    obtain ⟨P', hP'⟩ : ∃ P' : Polynomial V, P'.map V.subtype = P :=
      (Polynomial.lifts_iff_coeff_lifts P).2 (fun n => ⟨⟨_, hP n⟩, rfl⟩)
    let ι : V →+* GaussDom.intA V X.exp :=
      ((algebraMap Ω X.K).comp V.subtype).codRestrict (GaussDom.intA V X.exp)
        (fun v => GaussDom.const_mem V X.exp v v.2)
    have hx : Polynomial.aeval X.jK P = (GaussDom.intA V X.exp).subtype (P'.eval₂ ι ⟨X.jK, hjA⟩) := by
      rw [Polynomial.hom_eval₂, ← hP', Polynomial.aeval_def, Polynomial.eval₂_map]
      rfl
    rw [hx]
    apply hone
    intro hk
    rw [RingHom.mem_ker, Polynomial.hom_eval₂] at hk
    have hc : (GaussDom.redA V X.exp).comp ι =
        (algebraMap (IsLocalRing.ResidueField V) (HahnSeries ℚ (IsLocalRing.ResidueField V))).comp
          (IsLocalRing.residue V) := by
      apply RingHom.ext
      intro v
      exact GaussDom.redA_const V X.exp v
    rw [hc, ← Polynomial.eval₂_map, ← Polynomial.aeval_def] at hk
    set J := GaussDom.redA V X.exp ⟨X.jK, hjA⟩ with hJdef
    have hJ : J.orderTop = ((-1 : ℚ) : WithTop ℚ) := by
      apply HahnSeries.orderTop_eq_of_le
      · rw [HahnSeries.mem_support, hJdef, GaussDom.redA_coeff]
        have h1 : (⟨(X.exp X.jK).coeff (-1), (GaussDom.mem_intA V X.exp X.jK).1 hjA (-1)⟩ : V) = 1 :=
          Subtype.ext hj1
        rw [h1, map_one]
        exact one_ne_zero
      · intro g hg
        rw [HahnSeries.mem_support, hJdef, GaussDom.redA_coeff] at hg
        by_contra hlt'
        apply hg
        have h0 : (⟨(X.exp X.jK).coeff g, (GaussDom.mem_intA V X.exp X.jK).1 hjA g⟩ : V) = 0 :=
          Subtype.ext (hj2 g (lt_of_not_ge hlt'))
        rw [h0, map_zero]
    have hQ : P'.map (IsLocalRing.residue V) ≠ 0 := by
      intro h0
      have hc0 := congrArg (fun Q => Q.coeff i0) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc0
      have hPi : ((P'.coeff i0 : V) : Ω) = P.coeff i0 := by
        rw [← hP', Polynomial.coeff_map]
        rfl
      have hu : IsUnit (P'.coeff i0) := by
        refine isUnit_iff_exists_inv.2 ⟨⟨(P.coeff i0)⁻¹, hi0'⟩, Subtype.ext ?_⟩
        show ((P'.coeff i0 : V) : Ω) * (P.coeff i0)⁻¹ = 1
        rw [hPi, mul_inv_cancel₀ hne]
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal] at hc0
      exact hc0 hu
    have hot := GaussDom.orderTop_aeval J hJ _ _ hQ rfl
    rw [hk, HahnSeries.orderTop_zero] at hot
    exact WithTop.top_ne_coe hot

end GlobalTheory.KZ.ES
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemGammaOfMul
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES.HeckeLev

def rep (M q : ℕ) (γ : SL(2, ℤ)) : Option (Fin q) → Matrix (Fin 2) (Fin 2) ℤ
  | none => (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]
  | some j => !![1, ((j : ℕ) : ℤ) * (M : ℤ); 0, (q : ℤ)]

theorem det_rep (M q : ℕ) (γ : SL(2, ℤ)) (o : Option (Fin q)) : (rep M q γ o).det = q := by
  cases o with
  | none => simp [rep, Matrix.det_mul, Matrix.det_fin_two]
  | some j => simp [rep, Matrix.det_fin_two]

abbrev red (M : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) (ZMod M) :=
  (Int.castRingHom (ZMod M)).mapMatrix m

theorem red_mul (M : ℕ) (m m' : Matrix (Fin 2) (Fin 2) ℤ) : red M (m * m') = red M m * red M m' :=
  RingHom.map_mul _ _ _

theorem red_rep {M q : ℕ} {γ : SL(2, ℤ)} (hγ : DiagMod M q γ) (o : Option (Fin q)) :
    red M (rep M q γ o) = !![1, 0; 0, (q : ZMod M)] := by
  obtain ⟨h01, h10, h11⟩ := hγ
  simp only [en] at h01 h10 h11
  cases o with
  | some j =>
    ext i k; fin_cases i <;> fin_cases k <;> simp [rep, red]
  | none =>
    have hdet : (γ 0 0 : ZMod M) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2; rw [Matrix.det_fin_two] at this
      have := congrArg (fun z : ℤ => (z : ZMod M)) this; push_cast at this; exact this
    rw [h01, h10, h11] at hdet
    ext i k; fin_cases i <;> fin_cases k <;>
      simp [rep, red, Matrix.mul_apply, Fin.sum_univ_two, h01, h10, h11] <;> linear_combination hdet

theorem mem_Gamma_of_mul {M q : ℕ} (hqM : Nat.Coprime q M) (δ : SL(2, ℤ)) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (hm : red M m = !![1, 0; 0, (q : ZMod M)]) (h : red M ((δ : Matrix (Fin 2) (Fin 2) ℤ) * m) = !![1, 0; 0, (q : ZMod M)]) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem']
  have hu : IsUnit (!![1, 0; 0, (q : ZMod M)] : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]
    simpa using (ZMod.unitOfCoprime q hqM).isUnit
  have h2 : red M (δ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (q : ZMod M)] = !![1, 0; 0, (q : ZMod M)] := by
    rw [← hm]; exact (RingHom.map_mul _ _ _).symm.trans (h.trans hm.symm)
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  exact hu.mul_right_cancel (h2.trans (one_mul _).symm)

theorem map_rep {M q : ℕ} (hq : q.Prime) (hqM : Nat.Coprime q M) {γ : SL(2, ℤ)} (hγ : DiagMod M q γ)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma M) (o : Option (Fin q)) :
    ∃ o', ∃ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma M ∧
      rep M q γ o * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (g : Matrix (Fin 2) (Fin 2) ℤ) * rep M q γ o' := by
  set m := rep M q γ o * (δ : Matrix (Fin 2) (Fin 2) ℤ) with hmdef
  have hm : m.det = q := by
    rw [hmdef, Matrix.det_mul, det_rep, Matrix.SpecialLinearGroup.det_coe, mul_one]
  have hδ1 : red M (δ : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
    rw [CongruenceSubgroup.Gamma_mem'] at hδ
    have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) (ZMod M) => (x : Matrix (Fin 2) (Fin 2) (ZMod M))) hδ
    simpa using this
  have hred : red M m = !![1, 0; 0, (q : ZMod M)] := by
    rw [hmdef, red_mul, hδ1, Matrix.mul_one, red_rep hγ]

  have fin : ∀ o' (g : Matrix (Fin 2) (Fin 2) ℤ), g * rep M q γ o' = m →
      ∃ g' : SL(2, ℤ), g' ∈ CongruenceSubgroup.Gamma M ∧ m = (g' : Matrix (Fin 2) (Fin 2) ℤ) * rep M q γ o' := by
    intro o' g he
    have hd : g.det = 1 := by
      have := congrArg Matrix.det he
      rw [Matrix.det_mul, det_rep, hm] at this
      have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
      exact mul_right_cancel₀ hq' (this.trans (one_mul _).symm)
    refine ⟨⟨g, hd⟩, ?_, he.symm⟩
    exact mem_Gamma_of_mul hqM _ (rep M q γ o') (red_rep hγ o') (by rw [show ((⟨g, hd⟩ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = g from rfl, he, hred])
  rcases GlobalTheory.cosetPrimeDet q hq m hm with ⟨g, hg⟩ | ⟨k, hk, g, hg⟩
  · have hs : ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    obtain ⟨g', hg', he⟩ := fin none (g * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) (by
      rw [← hg]; show _ * ((γ : Matrix (Fin 2) (Fin 2) ℤ) * _) = _
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (γ : Matrix (Fin 2) (Fin 2) ℤ), hs, Matrix.one_mul])
    exact ⟨none, g', hg', he⟩
  ·
    have hMq : IsCoprime (M : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hqM.symm
    obtain ⟨u, v, huv⟩ := hMq
    haveI := Fact.mk hq
    set j : ℕ := ((k : ZMod q) * (u : ZMod q)).val with hj
    have hjq : j < q := ZMod.val_lt _
    have hdiv : (q : ℤ) ∣ (j : ℤ) * M - k := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hj, ZMod.natCast_zmod_val]
      have := congrArg (fun z : ℤ => (z : ZMod q)) huv
      push_cast at this
      rw [ZMod.natCast_self, mul_zero, add_zero] at this
      linear_combination (k : ZMod q) * this
    obtain ⟨t, ht⟩ := hdiv
    obtain ⟨g', hg', he⟩ := fin (some ⟨j, hjq⟩) (g * !![1, -t; 0, 1]) (by
      rw [← hg, Matrix.mul_assoc]; congr 1
      ext a b; fin_cases a <;> fin_cases b <;> simp [rep] <;> linear_combination ht)
    exact ⟨some ⟨j, hjq⟩, g', hg', he⟩

theorem rep_distinct {M q : ℕ} (hq : q.Prime) (hqM : Nat.Coprime q M) (γ : SL(2, ℤ)) (o o' : Option (Fin q))
    (h : SL(2, ℤ)) (H : (h : Matrix (Fin 2) (Fin 2) ℤ) * rep M q γ o = rep M q γ o') : o = o' := by
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
    have := h.2; rw [Matrix.det_fin_two] at this; exact this
  have nd : ¬ (q : ℤ) ∣ 1 := by
    intro hd
    have : q ∣ 1 := by exact_mod_cast hd
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some k =>
      exfalso
      have e00 := congrFun (congrFun H 0) 0
      simp [rep, Matrix.mul_apply, Fin.sum_univ_two] at e00
      exact nd ⟨h 0 0 * γ 0 0 + h 0 1 * γ 1 0, by linear_combination -e00⟩
  | some j =>
    cases o' with
    | none =>
      exfalso
      have e00 := congrFun (congrFun H 0) 0
      have e10 := congrFun (congrFun H 1) 0
      simp [rep, Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
      exact nd ⟨γ 0 0 * h 1 1 - h 0 1 * γ 1 0, by rw [e00, e10] at hdet; linear_combination -hdet⟩
    | some k =>
      have e00 := congrFun (congrFun H 0) 0
      have e01 := congrFun (congrFun H 0) 1
      simp [rep, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
      rw [e00] at e01
      have hdv : (q : ℤ) ∣ ((k : ℕ) - (j : ℕ) : ℤ) * M := ⟨h 0 1, by linear_combination -e01⟩
      have hc : IsCoprime (q : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.mpr hqM
      have h2 := hc.dvd_of_dvd_mul_right hdv
      have hj := j.2
      have hk := k.2
      congr 1
      apply Fin.ext
      obtain ⟨c, hc⟩ := h2
      have hj' : ((j : ℕ) : ℤ) < q := by exact_mod_cast hj
      have hk' : ((k : ℕ) : ℤ) < q := by exact_mod_cast hk
      have hj0 : (0 : ℤ) ≤ (j : ℕ) := by positivity
      have hk0 : (0 : ℤ) ≤ (k : ℕ) := by positivity
      have hc0 : c = 0 := by
        rcases lt_trichotomy c 0 with hlt | heq | hgt
        · nlinarith
        · exact heq
        · nlinarith
      rw [hc0, mul_zero] at hc
      exact_mod_cast (by linarith : ((j : ℕ) : ℤ) = (k : ℕ))

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem prod_sl_inv (X : Tower Ω ε) (M : ℕ) {ι : Type} [Fintype ι]
    (r : ι → Matrix (Fin 2) (Fin 2) ℤ) (hr : ∀ i, 0 < (r i).det) (δ : SL(2, ℤ))
    (hmap : ∀ i, ∃ i', ∃ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma M ∧
      r i * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (g : Matrix (Fin 2) (Fin 2) ℤ) * r i')
    (hdis : ∀ i i' (h : SL(2, ℤ)), (h : Matrix (Fin 2) (Fin 2) ℤ) * r i = r i' → i = i')
    (f : X.K) (hf : Lev X M f) :
    X.sl (ofSL δ) (∏ i, X.sl (toGQ (r i)) f) = ∏ i, X.sl (toGQ (r i)) f := by
  choose s g hg he using hmap
  have hdet1 : ∀ h : SL(2, ℤ), 0 < (h : Matrix (Fin 2) (Fin 2) ℤ).det := fun h => by
    rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos
  have hinj : Function.Injective s := by
    intro i1 i2 h12
    have hδ : (δ : Matrix (Fin 2) (Fin 2) ℤ) * ((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hg2 : (((g i2)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (g i2 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    symm
    apply hdis i2 i1 (g i1 * (g i2)⁻¹)
    have e1 := he i1
    have e2 := he i2
    rw [h12] at e1
    have a1 : r i1 = (g i1 : Matrix (Fin 2) (Fin 2) ℤ) * r (s i2) * ((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [← e1, Matrix.mul_assoc, hδ, Matrix.mul_one]
    have a2 : r i2 = (g i2 : Matrix (Fin 2) (Fin 2) ℤ) * r (s i2) * ((δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [← e2, Matrix.mul_assoc, hδ, Matrix.mul_one]
    rw [Matrix.SpecialLinearGroup.coe_mul, a1]
    conv_lhs => rw [a2]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc _ (g i2 : Matrix (Fin 2) (Fin 2) ℤ), hg2, Matrix.one_mul]
  have hbij : Function.Bijective s := Finite.injective_iff_bijective.mp hinj
  rw [map_prod]
  have step : ∀ i, X.sl (ofSL δ) (X.sl (toGQ (r i)) f) = X.sl (toGQ (r (s i))) f := by
    intro i
    rw [← X.sl_mul, ← MobLaws.toGQ_SL, ← MobLaws.toGQ_mul _ _ (hr i) (hdet1 δ), he i,
      MobLaws.toGQ_mul _ _ (hdet1 (g i)) (hr (s i)), X.sl_mul, MobLaws.toGQ_SL, hf _ (hg i)]
  simp only [step]
  exact Equiv.prod_comp (Equiv.ofBijective s hbij) (fun i => X.sl (toGQ (r i)) f)

end GlobalTheory.KZ.ES.HeckeLev

namespace GlobalTheory.KZ.ES

theorem lev_heckeProd : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (M q : ℕ) (f : X.K) (γ : SL(2, ℤ)), 0 < M → q.Prime → Nat.Coprime q M → Lev X M f → DiagMod M q γ →
    Lev X M (Nq X M q f * X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) := by
  intro Ω _ _ _ ε X M q f γ _ hq hqM hf hγ δ hδ
  have e : Nq X M q f * X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f =
      ∏ o : Option (Fin q), X.sl (toGQ (HeckeLev.rep M q γ o)) f := by
    rw [Fintype.prod_option, mul_comm, Nq, Finset.prod_range]
    rfl
  rw [e]
  exact HeckeLev.prod_sl_inv X M (HeckeLev.rep M q γ)
    (fun o => by rw [HeckeLev.det_rep]; exact_mod_cast hq.pos) δ
    (HeckeLev.map_rep hq hqM hγ δ hδ) (HeckeLev.rep_distinct hq hqM γ) f hf

end GlobalTheory.KZ.ES
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraKummerFunctionUniformExceptionalPr
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.Ues

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem toGQ_mul (m m' : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) (h' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have hmm : 0 < (m * m').det := by rw [Matrix.det_mul]; exact mul_pos h h'
  unfold toGQ
  rw [dite_eq_left hmm, dite_eq_left h, dite_eq_left h']
  apply Subtype.ext
  apply Units.ext
  exact Matrix.map_mul (f := Int.castRingHom ℚ)

theorem lev_mul {X : Tower Ω ε} {M : ℕ} {f g : X.K} (hf : Lev X M f) (hg : Lev X M g) : Lev X M (f * g) :=
  fun γ hγ => by rw [map_mul, hf γ hγ, hg γ hγ]

theorem lev_div {X : Tower Ω ε} {M : ℕ} {f g : X.K} (hf : Lev X M f) (hg : Lev X M g) : Lev X M (f / g) :=
  fun γ hγ => by rw [map_div₀, hf γ hγ, hg γ hγ]

theorem lev_pow {X : Tower Ω ε} {M : ℕ} {f : X.K} (hf : Lev X M f) (k : ℕ) : Lev X M (f ^ k) :=
  fun γ hγ => by rw [map_pow, hf γ hγ]

theorem lev_const (X : Tower Ω ε) (M : ℕ) (c : Ω) : Lev X M (algebraMap Ω X.K c) :=
  fun _ _ => AlgEquiv.commutes _ c

theorem lev_sl {X : Tower Ω ε} {M : ℕ} {f : X.K} (hf : Lev X M f) (γ : SL(2, ℤ)) : Lev X M (X.sl (ofSL γ) f) := by
  intro δ hδ
  have e : γ * δ = (γ * δ * γ⁻¹) * γ := by group
  rw [← X.sl_mul, ← map_mul, e, map_mul, X.sl_mul,
    hf _ ((CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ γ)]

theorem lev_gal [IsAlgClosure ℚ Ω] {X : Tower Ω ε} {M : ℕ} (hM : 0 < M) {f : X.K} (hf : Lev X M f)
    (s : Ω ≃ₐ[ℚ] Ω) : Lev X M (X.gal s f) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  intro δ hδ
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := s ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.1 hδ
  have := X.recip M f hM hf ζ hζ s (i : ℤ) (by rw [← hi, zpow_natCast]) 1 δ
    (by simp [en, h00, h01, h10, h11])
  rw [map_one, X.sl_one] at this
  exact this.symm

theorem val_mul_sub_one {K : Type} [Field K] (W : ValuationSubring K) {x y : K} (hx : W.valuation (x - 1) < 1)
    (hy : W.valuation (y - 1) < 1) : W.valuation (x * y - 1) < 1 := by
  have h1 : W.valuation x = 1 := by
    have e : x = 1 + (x - 1) := by ring
    rw [e, Valuation.map_add_eq_of_lt_left _ (by rwa [map_one]), map_one]
  have e : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [e]
  exact Valuation.map_add_lt _ (by rwa [map_mul, h1, one_mul]) hx

theorem const_mem_un (X : Tower Ω ε) (m : ℕ) {c : Ω} (hc : algebraMap Ω X.K c ≠ 0) :
    Units.mk0 (algebraMap Ω X.K c) hc ∈ X.Un m := by
  intro W hW
  refine ⟨1, ?_⟩
  rw [Units.val_one, one_pow, div_one, Units.val_mk0, KmapA.val_eq_one_iff _ hc]
  exact ⟨hW.1 c, by rw [← map_inv₀]; exact hW.1 _⟩

end GlobalTheory.KZ.ES.Ues


open GlobalTheory.KZ.ES.Ues in
theorem GlobalTheory.KZ.ES.eichlerShimura_unit : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → l ∣ M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ (n k : ℕ) (f : X.Kˣ), f ∈ X.Un (l ^ n) → Lev X (M₀ * l ^ k) f → ∀ γ : SL(2, ℤ), DiagMod (M₀ * l ^ k) q γ → ∃ g : X.Kˣ, Nq X (M₀ * l ^ k) q f * X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) = X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL γ) (f : X.K))) ^ q * (g : X.K) ^ (l ^ n) := by
  intro Ω _ _ _ ε X hhol l M₀ hl hM₀ hlM
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.kronecker_congruence_modularFunctionTower_level ε X hhol l M₀ hl hM₀
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.isPow_of_gauss_valuation_congr_one_almost_all_primes ε X hhol l M₀ hl hM₀ hlM
  refine ⟨S₁ ∪ S₂ ∪ M₀.primeFactors, ?_⟩
  intro q hq hqS V s hFrob n k f hf hlev γ hγ
  simp only [Finset.mem_union, not_or] at hqS
  obtain ⟨⟨hq1, hq2⟩, hq3⟩ := hqS
  have hqM₀ : Nat.Coprime q M₀ :=
    (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => hq3 (Nat.mem_primeFactors.2 ⟨hq, h, hM₀.ne'⟩)
  have hqM : Nat.Coprime q (M₀ * l ^ k) :=
    Nat.Coprime.mul_right hqM₀ (Nat.Coprime.pow_right k (Nat.Coprime.coprime_dvd_right hlM hqM₀))
  have hM : 0 < M₀ * l ^ k := Nat.mul_pos hM₀ (pow_pos hl.pos k)
  obtain ⟨W, hDom, hGauss⟩ := GlobalTheory.KZ.ES.exists_dom_gauss ε X V
  have hY := Tower.overY_comap_sl_gal ε X ε.injective hhol
  obtain ⟨hU1, hUmul, hUinv, -, -, hUpow, -⟩ := UnClosure.un_closure ε X ε.injective hhol (l ^ n)
  have hsl : ∀ (g : GQ) (u : X.Kˣ), u ∈ X.Un (l ^ n) → ∃ v ∈ X.Un (l ^ n), (v : X.K) = X.sl g u := fun g u hu =>
    ⟨_, KmapA.un_map X (X.sl g).toRingEquiv (fun W hW => (hY W hW).1 g) _ u hu, rfl⟩
  have hgal : ∀ (t : Ω ≃ₐ[ℚ] Ω) (u : X.Kˣ), u ∈ X.Un (l ^ n) → ∃ v ∈ X.Un (l ^ n), (v : X.K) = X.gal t u :=
    fun t u hu => ⟨_, KmapA.un_map X (X.gal t) (fun W hW => (hY W hW).2 t) _ u hu, rfl⟩
  obtain ⟨f', hf', ef'⟩ := hsl (ofSL γ) f hf
  have hlev' : Lev X (M₀ * l ^ k) (f' : X.K) := ef' ▸ lev_sl hlev γ
  obtain ⟨c₁, hc₁⟩ := (hS₁ q hq hq1 V s hFrob W hDom k f f.ne_zero hlev).1
  obtain ⟨c₂, hc₂⟩ := (hS₁ q hq hq1 V s hFrob W hDom k f' f'.ne_zero hlev').2
  have hc₁0 : c₁ ≠ 0 := by rintro rfl; simp at hc₁
  have hc₂0 : c₂ ≠ 0 := by rintro rfl; simp at hc₂
  have hc : algebraMap Ω X.K (c₁ * c₂) ≠ 0 := (_root_.map_ne_zero _).2 (mul_ne_zero hc₁0 hc₂0)
  have hsplit : X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) =
      X.sl (toGQ !![(q : ℤ), 0; 0, 1]) (f' : X.K) := by
    rw [toGQ_mul _ _ (by rw [γ.det_coe]; exact one_pos) (by simp [Matrix.det_fin_two, hq.pos]), Betti.toGQ_sl,
      X.sl_mul, ef']
  have hnlev := GlobalTheory.KZ.ES.lev_heckeProd ε X _ q f γ hM hq hqM hlev hγ
  obtain ⟨N, hN, eN⟩ : ∃ v ∈ X.Un (l ^ n), (v : X.K) = Nq X (M₀ * l ^ k) q f := by
    unfold Nq
    refine Finset.prod_induction _ (fun x => ∃ v ∈ X.Un (l ^ n), (v : X.K) = x) ?_ ⟨1, hU1, rfl⟩
      (fun j _ => hsl _ f hf)
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, hUmul a b ha hb, rfl⟩
  obtain ⟨T, hT, eT⟩ := hsl (toGQ !![(q : ℤ), 0; 0, 1]) f' hf'
  obtain ⟨A, hA, eA⟩ := hgal s f hf
  obtain ⟨B, hB, eB⟩ := hgal s.symm f' hf'
  have hAl : Lev X (M₀ * l ^ k) (A : X.K) := eA ▸ lev_gal hM hlev s
  have hBl : Lev X (M₀ * l ^ k) (B : X.K) := eB ▸ lev_gal hM hlev' s.symm
  rw [hsplit, ← eN, ← eT] at hnlev
  rw [hsplit, ← eN, ← eT, ← ef', ← eA, ← eB]
  rw [← eN, ← eA] at hc₁
  rw [← eT, ← eB] at hc₂
  have eU : ((Units.mk0 _ hc * (N * T) * (A * B ^ q)⁻¹ : X.Kˣ) : X.K) =
      algebraMap Ω X.K (c₁ * c₂) * (N * T) / (A * B ^ q) := by
    simp [div_eq_mul_inv]
  obtain ⟨g, hg⟩ := hS₂ q hq hq2 V hFrob.1 W hGauss n k (Units.mk0 _ hc * (N * T) * (A * B ^ q)⁻¹)
    (hUmul _ _ (hUmul _ _ (const_mem_un X _ hc) (hUmul _ _ hN hT)) (hUinv _ (hUmul _ _ hA (hUpow q _ hB))))
    (by rw [eU]; exact lev_div (lev_mul (lev_const X _ _) hnlev) (lev_mul hAl (lev_pow hBl q)))
    (by
      rw [eU]
      convert val_mul_sub_one W hc₁ hc₂ using 3
      rw [map_mul]; ring)
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (c₁ * c₂)⁻¹ (pow_pos hl.pos n)
  have hb0 : algebraMap Ω X.K b ≠ 0 := by
    refine (_root_.map_ne_zero _).2 ?_
    rintro rfl
    rw [zero_pow (pow_pos hl.pos n).ne'] at hb
    exact inv_ne_zero (mul_ne_zero hc₁0 hc₂0) hb.symm
  refine ⟨Units.mk0 _ hb0 * g, ?_⟩
  have hg' := congrArg (fun u : X.Kˣ => (u : X.K)) hg
  simp only [eU, Units.val_pow_eq_pow_val] at hg'
  rw [Units.val_mul, Units.val_mk0, mul_pow, ← map_pow, hb, ← hg', map_inv₀]
  have hA0 := A.ne_zero
  have hB0 := B.ne_zero
  field_simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraKummerFunctionUniformExceptionalPrStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerShimura_kummer_function_uniform_exceptional_primes : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → l ∣ M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ (n k : ℕ) (f : X.Kˣ), f ∈ X.Un (l ^ n) → Lev X (M₀ * l ^ k) f → ∀ γ : SL(2, ℤ), DiagMod (M₀ * l ^ k) q γ → ∃ g : X.Kˣ, Nq X (M₀ * l ^ k) q f * X.sl (toGQ ((γ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) = X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL γ) (f : X.K))) ^ q * (g : X.K) ^ (l ^ n) := by
  first | exact @GlobalTheory.KZ.ES.eichlerShimura_unit | exact GlobalTheory.KZ.ES.eichlerShimura_unit | (intros; apply GlobalTheory.KZ.ES.eichlerShimura_unit <;> assumption)
end
