module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnits
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueGalBEquivariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisConjValuationSubringSameTrace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoInvariantHolomorphicMemAdjoinJInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueNormalizedCyclotomicTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueNormalizedCyclotomicTrace
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.NTr

theorem zt_prim {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p n : ℕ) (hp : 0 < p) :
    IsPrimitiveRoot (zt ε p n) (p ^ n) := by
  have h := GlobalTheory.Glue.KTExp.map_eOm ε (1 / (p : ℚ) ^ n)
  have hn : p ^ n ≠ 0 := pow_ne_zero _ hp.ne'
  have hc := Complex.isPrimitiveRoot_exp (p ^ n) hn
  have e : Complex.exp (2 * Real.pi * Complex.I * (((1 / (p : ℚ) ^ n : ℚ)) : ℂ)) = Complex.exp (2 * Real.pi * Complex.I / ((p ^ n : ℕ) : ℂ)) := by
    congr 1; push_cast; ring
  rw [e] at h
  unfold zt
  rw [← h] at hc
  exact (IsPrimitiveRoot.map_iff_of_injective ε.injective).mp hc

theorem zt_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p L m : ℕ) (hp : 0 < p) (hm : m ≤ L) :
    zt ε p L ^ (p ^ (L - m)) = zt ε p m := by
  apply ε.injective
  unfold zt
  rw [map_pow, GlobalTheory.Glue.KTExp.map_eOm, GlobalTheory.Glue.KTExp.map_eOm, ← Complex.exp_nat_mul]
  congr 1
  have hpL : (p : ℂ) ^ L = (p : ℂ) ^ (L - m) * (p : ℂ) ^ m := by rw [← pow_add, Nat.sub_add_cancel hm]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  rw [hpL]
  field_simp

theorem exists_algEquiv_primitiveRoot_pow_of_isAlgClosed {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic ℚ Ω] (ζ : Ω) (n : ℕ) (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (k : ℕ) (hk : k.Coprime n) : ∃ σ : Ω ≃+* Ω, σ ζ = ζ ^ k := by
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  haveI : NeZero (n : Ω) := ⟨by exact_mod_cast hn.ne'⟩
  have hint : IsIntegral ℚ ζ := (hζ.isIntegral hn).tower_top
  have hk' : IsPrimitiveRoot (ζ ^ k) n := hζ.pow_of_coprime k hk
  have hmin : minpoly ℚ ζ = Polynomial.cyclotomic n ℚ := (Polynomial.cyclotomic_eq_minpoly_rat hζ hn).symm
  have hroot : ζ ^ k ∈ (minpoly ℚ ζ).aroots Ω := by
    rw [Polynomial.mem_aroots, hmin]
    refine ⟨Polynomial.cyclotomic_ne_zero n ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact (Polynomial.isRoot_cyclotomic_iff).2 hk'
  let φ := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hint).symm ⟨ζ ^ k, hroot⟩
  let ψ : Ω →ₐ[ℚ] Ω := φ.liftNormal Ω
  refine ⟨(AlgEquiv.ofBijective ψ (Algebra.IsAlgebraic.algHom_bijective ψ)).toRingEquiv, ?_⟩
  have h1 := φ.liftNormal_commutes Ω (IntermediateField.AdjoinSimple.gen ℚ ζ)
  rw [IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen] at h1
  change ψ ζ = ζ ^ k
  simpa [ψ] using h1

theorem exists_aut {Ω : Type} [Field Ω] [iA : Algebra ℚ Ω] [iC : IsAlgClosure ℚ Ω] (ζ : Ω) (n : ℕ) (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (k : ℕ) (hk : k.Coprime n) : ∃ σ : Ω ≃ₐ[ℚ] Ω, σ ζ = ζ ^ k := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have e : iA = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have i1 : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI i2 : @Algebra.IsAlgebraic ℚ Ω _ _ DivisionRing.toRatAlgebra := by convert i1 using 2; exact e.symm
  obtain ⟨σ, hσ⟩ := exists_algEquiv_primitiveRoot_pow_of_isAlgClosed (Ω := Ω) ζ n hn hζ k hk
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) (fun x => ?_), hσ⟩
  rw [eq_ratCast]
  exact map_ratCast σ x

open Classical in
theorem sum_reindex (p : ℕ) [hpf : Fact p.Prime] (L m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ L) {M : Type} [AddCommMonoid M] (g : ℕ → M) :
    ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), g (a : ZMod (p ^ L)).val
      = ∑ k ∈ Finset.range (p ^ (L - m)), g (1 + p ^ m * k) := by
  have hp : p.Prime := hpf.out
  have hp1 : 1 < p := hp.one_lt
  have hpm : 1 < p ^ m := Nat.one_lt_pow (by omega) hp1
  have hN : p ^ m * p ^ (L - m) = p ^ L := by rw [← pow_add, Nat.add_sub_cancel' hm]
  have cop : ∀ k : ℕ, Nat.Coprime (1 + p ^ m * k) (p ^ L) := by
    intro k
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have h2 : p ∣ p ^ m * k := dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) k
    exact hp.not_dvd_one ((Nat.dvd_add_left h2).mp h)
  have hlt : ∀ k < p ^ (L - m), 1 + p ^ m * k < p ^ L := by
    intro k hk
    have : p ^ m * (k + 1) ≤ p ^ m * p ^ (L - m) := Nat.mul_le_mul_left _ hk
    rw [hN] at this
    nlinarith
  have hval : ∀ k < p ^ (L - m), ((ZMod.unitOfCoprime (1 + p ^ m * k) (cop k) : (ZMod (p ^ L))ˣ) : ZMod (p ^ L)).val = 1 + p ^ m * k := by
    intro k hk
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (hlt k hk)]
  symm
  refine Finset.sum_bij (fun k _ => ZMod.unitOfCoprime (1 + p ^ m * k) (cop k)) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range] at hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hval k hk]
    simp [Nat.ModEq, Nat.add_mul_mod_self_left]
  · intro k hk k' hk' h
    rw [Finset.mem_range] at hk hk'
    have := congrArg (fun u : (ZMod (p ^ L))ˣ => (u : ZMod (p ^ L)).val) h
    rw [hval k hk, hval k' hk'] at this
    have h3 : p ^ m * k = p ^ m * k' := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) h3
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hv : (b : ZMod (p ^ L)).val % p ^ m = 1 := by
      have := hb; unfold Nat.ModEq at this; rw [this, Nat.mod_eq_of_lt hpm]
    have hvl : (b : ZMod (p ^ L)).val < p ^ L := ZMod.val_lt _
    have hdm := Nat.div_add_mod ((b : ZMod (p ^ L)).val) (p ^ m)
    rw [hv] at hdm
    set k := (b : ZMod (p ^ L)).val / p ^ m
    have hk : k < p ^ (L - m) := by
      by_contra hc
      push_neg at hc
      have : p ^ m * p ^ (L - m) ≤ p ^ m * k := Nat.mul_le_mul_left _ hc
      rw [hN] at this
      omega
    refine ⟨k, Finset.mem_range.mpr hk, ?_⟩
    apply Units.ext
    rw [ZMod.coe_unitOfCoprime]
    have : 1 + p ^ m * k = (b : ZMod (p ^ L)).val := by omega
    rw [this, ZMod.natCast_zmod_val]
  · intro k hk
    rw [hval k (Finset.mem_range.mp hk)]

open Classical in
theorem trace_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (L m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ L)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω))
    (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val) (i : ℕ) :
    ∃ z ∈ Subring.closure {ζ ^ p ^ (L - m)},
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a (ζ ^ i)
        = (p : Ω) ^ (L - m) * z := by
  have hp : p.Prime := hpf.out
  have hN : p ^ L = p ^ m * p ^ (L - m) := by rw [← pow_add, Nat.add_sub_cancel' hm]
  have hs : ∀ a : (ZMod (p ^ L))ˣ, τ a (ζ ^ i) = ζ ^ ((a : ZMod (p ^ L)).val * i) := by
    intro a; rw [map_pow, hτ, ← pow_mul]
  have hr := sum_reindex p L m hm1 hm (fun v => ζ ^ (v * i))
  rw [Finset.sum_congr rfl (fun a _ => hs a), hr]
  have hw : IsPrimitiveRoot (ζ ^ p ^ m) (p ^ (L - m)) := hζ.pow (pow_pos hp.pos _) hN
  have hterm : ∀ k, ζ ^ ((1 + p ^ m * k) * i) = ζ ^ i * ((ζ ^ p ^ m) ^ i) ^ k := by
    intro k; rw [← pow_mul, ← pow_mul, ← pow_add]; congr 1; ring
  simp only [hterm, ← Finset.mul_sum]
  by_cases hd : p ^ (L - m) ∣ i
  · obtain ⟨j, hj⟩ := hd
    refine ⟨(ζ ^ p ^ (L - m)) ^ j, Subring.pow_mem _ (Subring.subset_closure (Set.mem_singleton _)) _, ?_⟩
    have h1 : (ζ ^ p ^ m) ^ i = 1 := by rw [hj, pow_mul, hw.pow_eq_one, one_pow]
    have h2 : ζ ^ i = (ζ ^ p ^ (L - m)) ^ j := by rw [hj, pow_mul]
    rw [h1, h2]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_pow]
    ring
  · refine ⟨0, Subring.zero_mem _, ?_⟩
    have h1 : (ζ ^ p ^ m) ^ i ≠ 1 := fun h => hd ((hw.pow_eq_one_iff_dvd i).mp h)
    rw [geom_sum_eq h1, ← pow_mul, mul_comm i, pow_mul, hw.pow_eq_one, one_pow, sub_self, zero_div, mul_zero, mul_zero]

open Classical in
theorem trace_closure {Ω : Type} [Field Ω] [Algebra ℚ Ω] (p : ℕ) [hpf : Fact p.Prime] (L m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ L)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ (p ^ L)) (τ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω))
    (hτ : ∀ a, τ a ζ = ζ ^ (a : ZMod (p ^ L)).val) (y : Ω) (hy : y ∈ Subring.closure {ζ}) :
    ∃ z ∈ Subring.closure {ζ ^ p ^ (L - m)},
      ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a y
        = (p : Ω) ^ (L - m) * z := by
  rw [Subring.mem_closure_iff, Submonoid.closure_singleton_eq] at hy
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact trace_pow p L m hm1 hm ζ hζ τ hτ i
  | zero => exact ⟨0, Subring.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨z1, h1, e1⟩ := hx
    obtain ⟨z2, h2, e2⟩ := hy
    exact ⟨z1 + z2, Subring.add_mem _ h1 h2, by simp only [map_add (f := _), Finset.sum_add_distrib, e1, e2]; ring⟩
  | neg x _ hx =>
    obtain ⟨z1, h1, e1⟩ := hx
    exact ⟨-z1, Subring.neg_mem _ h1, by simp only [map_neg, Finset.sum_neg_distrib, e1]; ring⟩


open Classical in
theorem normTrace_exists_unique : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime] (L m : ℕ), 1 ≤ m → m ≤ L → ∀ F : Ω, InZl ε p L F → ∃ F' : Ω, IsNT ε p L m F F' ∧ InZl ε p m F' ∧ ∀ F'' : Ω, IsNT ε p L m F F'' → F'' = F' := by
  intro Ω _ _ _ ε p hpf L m hm1 hm F hF
  have hp : p.Prime := hpf.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hζ := zt_prim ε p L hp.pos
  have hpow := zt_pow ε p L m hp.pos hm
  have hcop : ∀ a : (ZMod (p ^ L))ˣ, ((a : ZMod (p ^ L)).val).Coprime (p ^ L) := fun a => ZMod.val_coe_unit_coprime a
  choose τ hτ using fun a : (ZMod (p ^ L))ˣ => exists_aut (zt ε p L) (p ^ L) (pow_pos hp.pos _) hζ _ (hcop a)
  obtain ⟨D, hD, hDF⟩ := hF
  have hD0 : (D : Ω) ≠ 0 := by
    have : D ≠ 0 := by rintro rfl; exact hD (dvd_zero p)
    exact_mod_cast this
  have hpN : (p : Ω) ^ (L - m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  obtain ⟨z, hz, hT⟩ := trace_closure p L m hm1 hm (zt ε p L) hζ τ hτ _ hDF
  rw [hpow] at hz
  simp only [map_mul, map_natCast, ← Finset.mul_sum] at hT
  have hsum : ∀ σ : (ZMod (p ^ L))ˣ → (Ω ≃ₐ[ℚ] Ω), (∀ a, σ a (zt ε p L) = zt ε p L ^ (a : ZMod (p ^ L)).val) →
      ∀ a, σ a F = τ a F := by
    intro σ hσ a
    have hagree : Set.EqOn ((σ a : Ω ≃+* Ω) : Ω →+* Ω) ((τ a : Ω ≃+* Ω) : Ω →+* Ω) (Subring.closure {zt ε p L}) := by
      apply RingHom.eqOn_set_closure
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      show σ a (zt ε p L) = τ a (zt ε p L)
      rw [hσ, hτ]
    have h2 : σ a ((D : Ω) * F) = τ a ((D : Ω) * F) := hagree hDF
    rw [map_mul, map_mul, map_natCast, map_natCast] at h2
    exact mul_left_cancel₀ hD0 h2
  have hE : (p : Ω) ^ (L - m) * (z / D) = ∑ a ∈ Finset.univ.filter (fun a : (ZMod (p ^ L))ˣ => (a : ZMod (p ^ L)).val ≡ 1 [MOD p ^ m]), τ a F := by
    rw [← mul_div_assoc, ← hT, mul_div_cancel_left₀ _ hD0]
  refine ⟨z / D, ⟨τ, hτ, hE⟩, ⟨D, hD, ?_⟩, ?_⟩
  · have : (D : Ω) * (z / D) = z := by field_simp
    rw [this]; exact hz
  · rintro F'' ⟨σ, hσ, hF''⟩
    rw [Finset.sum_congr rfl (fun a _ => hsum σ hσ a), ← hE] at hF''
    exact mul_left_cancel₀ hpN hF''

end GlobalTheory.NTr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueNormalizedCyclotomicTraceStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_normalizedCyclotomicTrace : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (p : ℕ) [Fact p.Prime] (L m : ℕ), 1 ≤ m → m ≤ L → ∀ F : Ω, InZl ε p L F → ∃ F' : Ω, IsNT ε p L m F F' ∧ InZl ε p m F' ∧ ∀ F'' : Ω, IsNT ε p L m F F'' → F'' = F' := by
  first | exact @GlobalTheory.NTr.normTrace_exists_unique | exact GlobalTheory.NTr.normTrace_exists_unique | (intros; apply GlobalTheory.NTr.normTrace_exists_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelIntegralMatrixConj
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelIntegralMatrixConj
noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem germ_eq_of_eqOn_Hs {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) := by
  rw [Filter.Germ.coe_eq]
  exact Filter.mem_of_superset (Filter.self_mem_codiscreteWithin Hs) (fun z hz => h z hz)

theorem kum_kmap_sl : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, ∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), 0 < m.det →
      Kum X l n x χ → Kum X l n (X.kmap l (X.sl (toGQ m)).toRingEquiv x) (fun δ => χ (cj m δ)) := by
  intro Ω _ _ ε X l _ n m x χ hm hK
  obtain ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab⟩, hrel⟩ := hK
  obtain ⟨mobHs, mobMul, mobOne, mobDiff, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_basic_laws
  obtain ⟨cj1, -, cj3⟩ := GlobalTheory.T.integralConjugateSL2Int_laws
  obtain ⟨-, -, gcomp, -, -⟩ := GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties
  have hcls := (GlobalTheory.T.towerUnitClassModPrimePow_properties Ω ε X l n).2.2.2.2.2.1 (X.sl (toGQ m)).toRingEquiv x f hx
  refine ⟨Units.map (X.sl (toGQ m)).toRingEquiv.toMonoidHom f, fun z => a (mob (toGQ m) z),
    fun z => b (mob (toGQ m) z), M * m.det.natAbs, ?_, hcls, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Nat.mul_pos hM (Int.natAbs_pos.2 hm.ne')
  · exact ha.comp (mobDiff _) (fun z hz => mobHs _ z hz)
  · exact hb.comp (mobDiff _) (fun z hz => mobHs _ z hz)
  · intro h0
    apply hb0
    have h0' : ((fun z => b (mob (toGQ m) z) : ℂ → ℂ) : Mero) = ((fun _ => (0 : ℂ) : ℂ → ℂ) : Mero) := h0
    have h1 := gcomp (toGQ m)⁻¹ _ _ h0'
    calc (b : Mero) = ((fun z => b (mob (toGQ m) (mob (toGQ m)⁻¹ z)) : ℂ → ℂ) : Mero) := by
          refine germ_eq_of_eqOn_Hs fun z hz => ?_
          rw [← mobMul _ _ z hz, mul_inv_cancel, mobOne]
      _ = ((fun _ => (0 : ℂ) : ℂ → ℂ) : Mero) := h1
      _ = 0 := rfl
  · obtain ⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, X.an (f : X.K) = (φ : Mero) :=
      (Quotient.exists_rep (X.an (f : X.K))).imp fun _ h => h.symm
    have h1 : X.an ((Units.map (X.sl (toGQ m)).toRingEquiv.toMonoidHom f : X.Kˣ) : X.K) =
        ((fun z => φ (mob (toGQ m) z) : ℂ → ℂ) : Mero) := X.an_sl (toGQ m) f φ hφ
    rw [h1]
    rw [hφ] at hab
    have e := gcomp (toGQ m) (φ * b ^ (l ^ n)) (a ^ (l ^ n))
      (by rw [Filter.Germ.coe_mul, Filter.Germ.coe_pow, Filter.Germ.coe_pow]; exact hab)
    rw [← Filter.Germ.coe_pow, ← Filter.Germ.coe_pow, ← Filter.Germ.coe_mul]
    exact e
  · intro δ hδ z hz
    obtain ⟨hmδ, hcj⟩ := cj1 m M hm δ hδ
    have e := cj3 m δ (cj m δ) hm hmδ z hz
    show a (mob (toGQ m) (mob (ofSL δ) z)) * b (mob (toGQ m) z) = _ * (a (mob (toGQ m) z) * b (mob (toGQ m) (mob (ofSL δ) z)))
    rw [e]
    exact hrel (cj m δ) hcj (mob (toGQ m) z) (mobHs _ z hz)

end GlobalTheory.KZ.H3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelIntegralMatrixConjStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKummerCharacterAtLevel_integral_matrix_conj : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), 0 < m.det → Kum X l n x χ → Kum X l n (X.kmap l (X.sl (toGQ m)).toRingEquiv x) (fun δ => χ (cj m δ)) := by
  first | exact @GlobalTheory.KZ.H3.kum_kmap_sl | exact GlobalTheory.KZ.H3.kum_kmap_sl | (intros; apply GlobalTheory.KZ.H3.kum_kmap_sl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjOverPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjOverPrime
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.ValConjClosure

theorem valuation_intCast_eq_one {Ω : Type} [Field Ω] {p : ℕ} (hp : p.Prime) (A : ValuationSubring Ω)
    (hA : A.valuation (p : Ω) < 1) (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) : A.valuation (n : Ω) = 1 := by
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  refine le_antisymm (hle n) (not_lt.mp fun hlt => ?_)
  obtain ⟨a, b, hab⟩ := ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mpr hn
  have hab' : (a : Ω) * (p : Ω) + (b : Ω) * (n : Ω) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have h1 : A.valuation ((a : Ω) * (p : Ω)) < 1 := by
    rw [map_mul]
    calc A.valuation (a : Ω) * A.valuation (p : Ω) ≤ 1 * A.valuation (p : Ω) :=
          mul_le_mul' (hle a) le_rfl
      _ < 1 := by rwa [one_mul]
  have h2 : A.valuation ((b : Ω) * (n : Ω)) < 1 := by
    rw [map_mul]
    calc A.valuation (b : Ω) * A.valuation (n : Ω) ≤ 1 * A.valuation (n : Ω) :=
          mul_le_mul' (hle b) le_rfl
      _ < 1 := by rwa [one_mul]
  have hadd := A.valuation.map_add ((a : Ω) * (p : Ω)) ((b : Ω) * (n : Ω))
  rw [hab', map_one] at hadd
  exact absurd hadd (not_le.mpr (max_lt h1 h2))

theorem ratCast_mem_iff {Ω : Type} [Field Ω] [CharZero Ω] {p : ℕ} (hp : p.Prime) (A : ValuationSubring Ω)
    (hA : A.valuation (p : Ω) < 1) (a : ℚ) : (a : Ω) ∈ A ↔ ¬ p ∣ a.den := by
  have hle : ∀ m : ℤ, A.valuation (m : Ω) ≤ 1 := fun m =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A m)
  have hden0 : (a.den : Ω) ≠ 0 := Nat.cast_ne_zero.mpr a.den_nz
  rw [Rat.cast_def, ← A.valuation_le_one_iff]
  constructor
  · intro ha hd
    have hnum : ¬ (p : ℤ) ∣ a.num := by
      intro h
      have h1 : p ∣ a.num.natAbs := Int.natCast_dvd.mp h
      exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 a.reduced) hd)
    have hv1 := valuation_intCast_eq_one hp A hA a.num hnum
    obtain ⟨k, hk⟩ := hd
    have hdlt : A.valuation (a.den : Ω) < 1 := by
      rw [hk, Nat.cast_mul, map_mul]
      calc A.valuation (p : Ω) * A.valuation (k : Ω) ≤ A.valuation (p : Ω) * 1 :=
            mul_le_mul' le_rfl (by exact_mod_cast hle k)
        _ < 1 := by rwa [mul_one]
    have hnd : A.valuation (a.num : Ω) ≤ A.valuation (a.den : Ω) := by
      rw [← div_mul_cancel₀ (a.num : Ω) hden0, map_mul]
      calc A.valuation ((a.num : Ω) / (a.den : Ω)) * A.valuation (a.den : Ω) ≤
            1 * A.valuation (a.den : Ω) := mul_le_mul' ha le_rfl
        _ = A.valuation (a.den : Ω) := one_mul _
    rw [hv1] at hnd
    exact absurd (lt_of_le_of_lt hnd hdlt) (lt_irrefl 1)
  · intro hd
    have hv1 : A.valuation (a.den : Ω) = 1 := by
      have h := valuation_intCast_eq_one hp A hA (a.den : ℤ) (by exact_mod_cast hd)
      exact_mod_cast h
    rw [map_div₀, hv1, div_one]
    exact hle a.num

theorem isClosed_apply_mem {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [Algebra.IsIntegral F Ω]
    (x : Ω) (T : Set Ω) : IsClosed {σ : Ω ≃ₐ[F] Ω | σ x ∈ T} := by
  let E := IntermediateField.adjoin F ({x} : Set Ω)
  haveI : FiniteDimensional F E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := F) x)
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun τ => σ⁻¹ * τ) ⁻¹' (E.fixingSubgroup : Set (Ω ≃ₐ[F] Ω)), ?_,
    E.fixingSubgroup_isOpen.preimage (continuous_const_mul σ⁻¹), ?_⟩
  · intro τ hτ hT
    apply hσ
    have hfix : (σ⁻¹ * τ) x = x := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ x
      (IntermediateField.mem_adjoin_simple_self F x)
    have hinv : ∀ y, σ (σ⁻¹ y) = y := fun y => by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    rw [AlgEquiv.mul_apply] at hfix
    have he : τ x = σ x :=
      calc τ x = σ (σ⁻¹ (τ x)) := (hinv _).symm
        _ = σ x := by rw [hfix]
    change σ x ∈ T
    rw [← he]
    exact hT
  · show σ⁻¹ * σ ∈ E.fixingSubgroup
    rw [inv_mul_cancel]
    exact E.fixingSubgroup.one_mem

theorem exists_conj_of_isGalois {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
    (A B : ValuationSubring Ω) (h : ∀ a : F, algebraMap F Ω a ∈ A ↔ algebraMap F Ω a ∈ B) :
    ∃ σ : Ω ≃ₐ[F] Ω, ∀ x, σ x ∈ B ↔ x ∈ A := by
  classical
  let C : Finset Ω → Set (Ω ≃ₐ[F] Ω) := fun s => {σ | ∀ x ∈ s, σ x ∈ B ↔ x ∈ A}
  have hclosed : ∀ s, IsClosed (C s) := by
    intro s
    have hC : C s = ⋂ x ∈ s, {σ : Ω ≃ₐ[F] Ω | σ x ∈ {y : Ω | y ∈ B ↔ x ∈ A}} := by
      ext σ
      simp [C]
    rw [hC]
    exact isClosed_biInter fun x _ => isClosed_apply_mem x _
  have hne : ∀ s, (C s).Nonempty := by
    intro s
    let L := (FiniteGaloisIntermediateField.adjoin F (s : Set Ω)).toIntermediateField
    have hsL : (s : Set Ω) ⊆ L := FiniteGaloisIntermediateField.subset_adjoin F (s : Set Ω)
    obtain ⟨τ, hτ⟩ := GlobalTheory.KZ.ES.exists_conj_of_same_trace F L (A.comap (algebraMap L Ω))
      (B.comap (algebraMap L Ω)) (by
        intro a
        rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
          ← IsScalarTower.algebraMap_apply]
        exact h a)
    refine ⟨τ.liftNormal Ω, fun x hx => ?_⟩
    have hxL : x ∈ L := hsL hx
    have key := hτ ⟨x, hxL⟩
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap] at key
    have he : (τ.liftNormal Ω) x = algebraMap L Ω (τ ⟨x, hxL⟩) :=
      AlgEquiv.liftNormal_commutes τ Ω ⟨x, hxL⟩
    rw [he]
    exact key
  have hdir : Directed (fun s t => s ⊇ t) C := by
    intro s t
    exact ⟨s ∪ t, fun σ hσ x hx => hσ x (Finset.mem_union_left _ hx),
      fun σ hσ x hx => hσ x (Finset.mem_union_right _ hx)⟩
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hne
    (fun s => (hclosed s).isCompact) hclosed
  refine ⟨σ, fun x => ?_⟩
  exact Set.mem_iInter.mp hσ {x} x (Finset.mem_singleton_self x)

theorem exists_conj_over_prime : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A B : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ((p : ℕ) : Ω) ∈ B.nonunits → ∃ σ : Ω ≃ₐ[ℚ] Ω, ∀ x, σ x ∈ B ↔ x ∈ A := by
  intro Ω _ _ _ p _ A B hA hB
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hp : p.Prime := Fact.out
  have hA' := (A.mem_nonunits_iff).mp hA
  have hB' := (B.mem_nonunits_iff).mp hB
  apply exists_conj_of_isGalois A B
  intro a
  rw [eq_ratCast, ratCast_mem_iff hp A hA', ratCast_mem_iff hp B hB']

end GlobalTheory.ValConjClosure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjOverPrimeStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algEquiv_map_valuationSubring_over_prime : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A B : ValuationSubring Ω), ((p : ℕ) : Ω) ∈ A.nonunits → ((p : ℕ) : Ω) ∈ B.nonunits → ∃ σ : Ω ≃ₐ[ℚ] Ω, ∀ x, σ x ∈ B ↔ x ∈ A := by
  first | exact @GlobalTheory.ValConjClosure.exists_conj_over_prime | exact GlobalTheory.ValConjClosure.exists_conj_over_prime | (intros; apply GlobalTheory.ValConjClosure.exists_conj_over_prime <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelAdjoinRootsIntegrallyClosedQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelAdjoinRootsIntegrallyClosedQuotient
open GlobalTheory.K5 GlobalTheory.KumDlog

noncomputable section

namespace GlobalTheory.K5.LevClosed

open Polynomial

theorem mem_adjoin_inv_of_isIntegral {R K : Type*} [CommRing R] [Field K] [Algebra R K] {z : K}
    (hz : z ≠ 0) (hi : IsIntegral R z) : z ∈ Algebra.adjoin R {z⁻¹} := by
  obtain ⟨f, hm, hf⟩ := hi
  letI : Invertible z := invertibleOfNonzero hz
  have h1 := eval₂_reverse_mul_pow (algebraMap R K) z f
  rw [hf, invOf_eq_inv] at h1
  have h2 : eval₂ (algebraMap R K) z⁻¹ f.reverse = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · exact absurd h (pow_ne_zero _ hz)
  have h3 := divX_mul_X_add f.reverse
  rw [coeff_zero_reverse, hm.leadingCoeff] at h3
  have h4 := congrArg (eval₂ (algebraMap R K) z⁻¹) h3
  rw [h2, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, map_one] at h4
  have hzz : z⁻¹ * z = 1 := inv_mul_cancel₀ hz
  have h5 : z = -(aeval z⁻¹ (divX f.reverse)) := by
    rw [aeval_def]
    linear_combination z * h4 - eval₂ (algebraMap R K) z⁻¹ (divX f.reverse) * hzz
  have hm' : -(aeval z⁻¹ (divX f.reverse)) ∈ Algebra.adjoin R {z⁻¹} :=
    neg_mem (aeval_mem_adjoin_singleton R _)
  rwa [← h5] at hm'

theorem lev_closed : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m → ∀ a ∈ Lev T m, ∀ b ∈ Lev T m, b ≠ 0 →
      IsInt (p := p) (a / b) → a / b ∈ Lev T m := by
  intro p _ Ω _ _ hΩ T m hm a ha b hb hb0 hint
  obtain ⟨ι, hι⟩ := GlobalTheory.K5.Basic.exists_isEmb T m
  obtain ⟨-, hrange⟩ := GlobalTheory.T.towerLevelEmbedding_injective_range_adjoinRoots p Ω hΩ T m hm ι hι
  obtain ⟨hdom, hdvr, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p m hm
  rw [← hrange] at ha hb ⊢
  obtain ⟨a', rfl⟩ := (AlgHom.mem_range ι).1 ha
  obtain ⟨b', rfl⟩ := (AlgHom.mem_range ι).1 hb
  rcases ValuationRing.dvd_total b' a' with ⟨c, hc⟩ | ⟨c, hc⟩
  · refine (AlgHom.mem_range ι).2 ⟨c, ?_⟩
    rw [hc, map_mul, mul_div_cancel_left₀ _ hb0]
  · have ha0 : ι a' ≠ 0 := by
      intro h; apply hb0; rw [hc, map_mul, h, zero_mul]
    have hz0 : ι a' / ι b' ≠ 0 := div_ne_zero ha0 hb0
    have hzi : (ι a' / ι b')⁻¹ = ι c := by
      rw [inv_div, hc, map_mul, mul_div_cancel_left₀ _ ha0]
    have hmem := mem_adjoin_inv_of_isIntegral hz0 hint
    rw [hzi] at hmem
    have hle : Algebra.adjoin (O0 p) {ι c} ≤ ι.range :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 ⟨c, rfl⟩)
    exact hle hmem

end GlobalTheory.K5.LevClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerLevelAdjoinRootsIntegrallyClosedQuotientStatement
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerLevelAdjoinRoots_integrallyClosed_quotient : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m → ∀ a ∈ Lev T m, ∀ b ∈ Lev T m, b ≠ 0 →
  GlobalTheory.K5.IsInt (p := p) (a / b) → a / b ∈ Lev T m := by
  intro p _ Ω _ _ hΩ T m hm a ha b hb hb0 hint
  obtain ⟨ι, hι⟩ := GlobalTheory.K5.Basic.exists_isEmb T m
  obtain ⟨-, hrange⟩ := GlobalTheory.T.towerLevelEmbedding_injective_range_adjoinRoots p Ω hΩ T m hm ι hι
  obtain ⟨hdom, hdvr, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p m hm
  rw [← hrange] at ha hb ⊢
  obtain ⟨a', rfl⟩ := (AlgHom.mem_range ι).1 ha
  obtain ⟨b', rfl⟩ := (AlgHom.mem_range ι).1 hb
  rcases ValuationRing.dvd_total b' a' with ⟨c, hc⟩ | ⟨c, hc⟩
  · refine (AlgHom.mem_range ι).2 ⟨c, ?_⟩
    rw [hc, map_mul, mul_div_cancel_left₀ _ hb0]
  · have ha0 : ι a' ≠ 0 := by
      intro h
      apply hb0
      rw [hc, map_mul, h, zero_mul]
    have hz0 : ι a' / ι b' ≠ 0 := div_ne_zero ha0 hb0
    have hzi : (ι a' / ι b')⁻¹ = ι c := by
      rw [inv_div, hc, map_mul, mul_div_cancel_left₀ _ ha0]
    have hmem := GlobalTheory.K5.LevClosed.mem_adjoin_inv_of_isIntegral (R := O0 p) hz0 hint
    rw [hzi] at hmem
    have hle : Algebra.adjoin (O0 p) {ι c} ≤ ι.range :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 ⟨c, rfl⟩)
    exact hle hmem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDlogDerivationsTowerLevelModIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDlogDerivationsTowerLevelModIntegral
open GlobalTheory.K5 GlobalTheory.KumDlog Polynomial

noncomputable section
namespace GlobalTheory.LevDer

theorem int_div_of_mk {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω] [CharZero Ω]
    (m : ℕ) (a : integralClosure (O0 p) Ω)
    (ha : Ideal.Quotient.mk (Ideal.span {((p : integralClosure (O0 p) Ω)) ^ m}) a = 0) :
    IsInt (p := p) ((a : Ω) / (p : Ω) ^ m) := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at ha
  obtain ⟨c, rfl⟩ := ha
  have hp : (p : Ω) ^ m ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  refine int_congr c.2 ?_
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast]
  field_simp

theorem natCast_eq_pow {Ω : Type} [Field Ω] (N p k : ℕ) (h : N = p ^ (k + 1)) :
    (N : Ω) = (p : Ω) ^ (k + 1) := by
  subst h; push_cast; rfl


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem exists_levDer : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m →
    ∃ dz dq : Ω → Ω, IsDer (Lev T m) dz ∧ IsDer (Lev T m) dq ∧ Vals T m dz dq := by
  intro p _ Ω _ _ hC T m hm
  haveI : CharZero Ω := Basic.charZero_of_isClo hC
  obtain ⟨ι, hι⟩ := Basic.exists_isEmb T m
  obtain ⟨hinj, hrange⟩ := GlobalTheory.T.towerLevelEmbedding_injective_range_adjoinRoots p Ω hC T m hm ι hι
  have hιA : ∀ z, ι z ∈ integralClosure (O0 p) Ω := fun z =>
    Lev_int T m _ (hrange ▸ AlgHom.mem_range_self ι z)
  let ιA : On p m →ₐ[O0 p] integralClosure (O0 p) Ω := ι.codRestrict _ hιA
  have hιAv : ∀ z, ((ιA z : integralClosure (O0 p) Ω) : Ω) = ι z := fun z => rfl
  let I : Ideal (integralClosure (O0 p) Ω) := Ideal.span {((p : integralClosure (O0 p) Ω)) ^ m}
  letI : Algebra (On p m) (integralClosure (O0 p) Ω ⧸ I) :=
    ((Ideal.Quotient.mk I).comp ιA.toRingHom).toAlgebra
  have halg : ∀ z, algebraMap (On p m) (integralClosure (O0 p) Ω ⧸ I) z = Ideal.Quotient.mk I (ιA z) :=
    fun z => rfl
  haveI : IsScalarTower (O0 p) (On p m) (integralClosure (O0 p) Ω ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [halg, AlgHom.commutes, Ideal.Quotient.mk_algebraMap]

  let g : Ω → On p m := Function.invFun ι
  have hg : ∀ x ∈ Lev T m, ι (g x) = x := fun x hx =>
    Function.invFun_eq ((AlgHom.mem_range ι).1 (hrange.symm ▸ hx))
  have hgm : ∀ x ∈ Lev T m, ∀ z, ι z = x → g x = z := fun x hx z hz =>
    hinj ((hg x hx).trans hz.symm)
  let lift : (integralClosure (O0 p) Ω ⧸ I) → integralClosure (O0 p) Ω :=
    Function.surjInv Ideal.Quotient.mk_surjective
  have hlift : ∀ s, Ideal.Quotient.mk I (lift s) = s := Function.surjInv_eq _
  have hdiv := fun a ha => GlobalTheory.LevDer.int_div_of_mk (p := p) (Ω := Ω) m a ha

  have hF : ∀ D : Derivation (O0 p) (On p m) (integralClosure (O0 p) Ω ⧸ I),
      IsDer (Lev T m) (fun x => ((lift (D (g x)) : integralClosure (O0 p) Ω) : Ω) / (p : Ω) ^ m) := by
    intro D
    refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_, fun c => ?_⟩
    · have e : g (x + y) = g x + g y :=
        hgm _ (add_mem hx hy) _ (by rw [map_add (f := _), hg x hx, hg y hy])
      refine int_congr (hdiv (lift (D (g (x + y))) - lift (D (g x)) - lift (D (g y))) ?_) ?_
      · rw [map_sub (Ideal.Quotient.mk I), map_sub (Ideal.Quotient.mk I), hlift, hlift, hlift, e, map_add (f := _)]; ring
      · push_cast; ring
    · have e : g (x * y) = g x * g y :=
        hgm _ (mul_mem hx hy) _ (by rw [map_mul, hg x hx, hg y hy])
      refine int_congr (hdiv (lift (D (g (x * y))) - ιA (g x) * lift (D (g y))
        - ιA (g y) * lift (D (g x))) ?_) ?_
      · rw [map_sub (Ideal.Quotient.mk I), map_sub (Ideal.Quotient.mk I), map_mul (Ideal.Quotient.mk I), map_mul (Ideal.Quotient.mk I), hlift, hlift, hlift, e, Derivation.leibniz,
          Algebra.smul_def, Algebra.smul_def, halg, halg]; ring
      · push_cast; rw [hιAv, hιAv, hg x hx, hg y hy]; ring
    · have e : g (algebraMap (O0 p) Ω c) = algebraMap (O0 p) (On p m) c :=
        hgm _ (Subalgebra.algebraMap_mem _ c) _ (ι.commutes c)
      refine hdiv _ ?_
      rw [hlift, e, Derivation.map_algebraMap]

  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hpd := GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T 1 1 le_rfl (Nat.totient_pos.2 (ppow_pos (p := p) 1))
  let u : integralClosure (O0 p) Ω := ⟨(p : Ω) / (T.ζ 1 - 1) ^ 1, hpd⟩
  have hz1 : T.ζ 1 - 1 ≠ 0 :=
    sub_ne_zero.2 ((T.prim 1).ne_one (by simpa using (Fact.out : p.Prime).one_lt))
  have hpow : T.ζ (k + 1) ^ p ^ k = T.ζ 1 := by
    have := zeta_pow T 1 k; rwa [add_comm] at this
  have hxn : Ideal.Quotient.mk (towerIdeal p (k + 1)) (C X) = xn p (k + 1) := rfl
  have hyn : Ideal.Quotient.mk (towerIdeal p (k + 1)) X = yn p (k + 1) := rfl
  have hd := congrArg ι (DlogUniq.derivative_cyclotomic_mul p k)
  simp only [map_mul, map_sub, map_pow, map_natCast, map_one, hι.1, hpow] at hd
  have hxz : algebraMap (On p (k + 1)) (integralClosure (O0 p) Ω ⧸ I)
      (aeval (xn p (k + 1)) (derivative (cyclotomic (p ^ (k + 1)) (O0 p)))) *
      algebraMap (On p (k + 1)) _ ((p : On p (k + 1)) * xn p (k + 1)) = 0 := by
    rw [← map_mul, halg, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨ιA (xn p (k + 1)) ^ (p ^ (k + 1) - 1) * u * ιA (xn p (k + 1)), Subtype.ext ?_⟩
    have hp' : (p : Ω) = (T.ζ 1 - 1) * ((p : Ω) / (T.ζ 1 - 1) ^ 1) := by field_simp
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast, hιAv,
      map_mul, map_natCast, hι.1, u]
    linear_combination (-((p : Ω) / (T.ζ 1 - 1) ^ 1 * T.ζ (k + 1))) * hd -
      (ι (aeval (xn p (k + 1)) (derivative (cyclotomic (p ^ (k + 1)) (O0 p)))) * T.ζ (k + 1)) * hp'
  obtain ⟨Dz, hzx, hzy⟩ := DlogUniq.exists_derivation (cyclotomic (p ^ (k + 1)) (O0 p)) (p ^ (k + 1))
    (qO p) (towerIdeal p (k + 1)) rfl (integralClosure (O0 p) Ω ⧸ I)
    (algebraMap (On p (k + 1)) _ ((p : On p (k + 1)) * xn p (k + 1))) 0 hxz (mul_zero _)
  have hyq : ∀ N : ℕ, N = p ^ (k + 1) → (N : integralClosure (O0 p) Ω ⧸ I) *
      algebraMap (On p (k + 1)) _ ((p : On p (k + 1)) * yn p (k + 1)) = 0 := by
    intro N hN
    rw [← map_natCast (algebraMap (On p (k + 1)) (integralClosure (O0 p) Ω ⧸ I)) N, ← map_mul, halg,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    refine ⟨ιA ((p : On p (k + 1)) * yn p (k + 1)), Subtype.ext ?_⟩
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast, hιAv,
      map_mul, map_natCast]
    rw [natCast_eq_pow (Ω := Ω) N p k hN]
    ring
  obtain ⟨N, hN⟩ : ∃ N, N = p ^ (k + 1) := ⟨_, rfl⟩
  obtain ⟨Dq, hqx, hqy⟩ := DlogUniq.exists_derivation (cyclotomic (p ^ (k + 1)) (O0 p)) N
    (qO p) (towerIdeal p (k + 1)) (by rw [hN]; rfl) (integralClosure (O0 p) Ω ⧸ I)
    0 (algebraMap (On p (k + 1)) _ ((p : On p (k + 1)) * yn p (k + 1))) (mul_zero _)
    (hyq N hN)
  rw [hxn] at hzx hqx
  rw [hyn] at hzy hqy
  have hgz : g (T.ζ (k + 1)) = xn p (k + 1) := hgm _ (zeta_mem_Lev T _) _ hι.1
  have hgq : g (T.qq (k + 1)) = yn p (k + 1) := hgm _ (qq_mem_Lev T _) _ hι.2
  refine ⟨fun x => ((lift (Dz (g x)) : integralClosure (O0 p) Ω) : Ω) / (p : Ω) ^ (k + 1),
    fun x => ((lift (Dq (g x)) : integralClosure (O0 p) Ω) : Ω) / (p : Ω) ^ (k + 1),
    hF Dz, hF Dq, ?_, ?_, ?_, ?_⟩
  · refine int_congr (hdiv (lift (Dz (xn p (k + 1))) - ιA ((p : On p (k + 1)) * xn p (k + 1))) ?_) ?_
    · rw [map_sub (Ideal.Quotient.mk I), hlift, hzx, halg, sub_self]
    · simp only [hgz, MulMemClass.coe_mul, AddSubgroupClass.coe_sub, SubringClass.coe_natCast, hιAv, map_mul, map_natCast, hι.1]
      ring
  · exact int_congr (hdiv (lift (Dz (yn p (k + 1)))) (by rw [hlift, hzy])) (by simp only [hgq])
  · exact int_congr (hdiv (lift (Dq (xn p (k + 1)))) (by rw [hlift, hqx])) (by simp only [hgz])
  · refine int_congr (hdiv (lift (Dq (yn p (k + 1))) - ιA ((p : On p (k + 1)) * yn p (k + 1))) ?_) ?_
    · rw [map_sub (Ideal.Quotient.mk I), hlift, hqy, halg, sub_self]
    · simp only [hgq, MulMemClass.coe_mul, AddSubgroupClass.coe_sub, SubringClass.coe_natCast, hιAv, map_mul, map_natCast, hι.2]
      ring

end GlobalTheory.LevDer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDlogDerivationsTowerLevelModIntegralStatement
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dlog_derivations_towerLevel_mod_integral : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (m : ℕ), 1 ≤ m →
  ∃ dz dq : Ω → Ω, IsDer (Lev T m) dz ∧ IsDer (Lev T m) dq ∧ Vals T m dz dq := by
  first | exact @GlobalTheory.LevDer.exists_levDer | exact GlobalTheory.LevDer.exists_levDer | (intros; apply GlobalTheory.LevDer.exists_levDer <;> assumption)
end
end
