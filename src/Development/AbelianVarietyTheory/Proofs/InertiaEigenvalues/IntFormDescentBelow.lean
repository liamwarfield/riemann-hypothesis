module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelativeDifferentOrderBoundedAbsoluteRamificatioStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCuspFormsAllEmbeddingsOfInclusionReading

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceCombinationCoverFormIntegralOverPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceIntegralOfSmallAtOtherPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceIntegralOfSmallAtOtherPlaces
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped WithZero

namespace GlobalTheory.TraceSmall

theorem valV_le_one_of_ext {T T' : CDVR} (i : T.Fr →+* T'.Fr) {e' : ℕ} (he' : 0 < e')
    (hv : ∀ z : T.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T.V z) (z : T.Fr) :
    valV T'.V (i z) ≤ 1 ↔ valV T.V z ≤ 1 := by
  by_cases hz : z = 0
  · subst hz; simp
  have h1 : valV T'.V (i z) ≠ 0 := valV_ne_zero ((map_ne_zero i).2 hz)
  have h2 : valV T.V z ≠ 0 := valV_ne_zero hz
  have h := hv z hz
  have he : (0 : ℤ) < e' := by exact_mod_cast he'
  rw [← WithZero.log_le_log h1 one_ne_zero, ← WithZero.log_le_log h2 one_ne_zero, WithZero.log_one]
  unfold vV at h
  constructor <;> intro h' <;> nlinarith

theorem exists_bound {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (p : HeightOneSpectrum (𝓞 K)) {m : ℕ} (y : Fin m → L) :
    ∃ N : ℕ, ∀ la' : HeightOneSpectrum (𝓞 L), la'.asIdeal.under (𝓞 K) = p.asIdeal → ∀ k,
      la'.valuation L (y k) ≤ WithZero.exp (N : ℤ) := by
  have hS : {la' : HeightOneSpectrum (𝓞 L) | la'.asIdeal.under (𝓞 K) = p.asIdeal}.Finite := by
    refine (Set.Finite.preimage (f := fun la' : HeightOneSpectrum (𝓞 L) => la'.asIdeal)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
      (IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 L))).subset fun la' h => ?_
    exact ⟨la'.isPrime, ⟨h.symm⟩⟩
  obtain ⟨B, hB⟩ := ((hS.prod (Set.finite_univ (α := Fin m))).image
    fun q : HeightOneSpectrum (𝓞 L) × Fin m => WithZero.log (q.1.valuation L (y q.2))).bddAbove
  refine ⟨B.toNat, fun la' h k => ?_⟩
  by_cases hy : y k = 0
  · simp [hy]
  have h0 : la'.valuation L (y k) ≠ 0 := by simpa using hy
  have := hB ⟨(la', k), ⟨h, Set.mem_univ _⟩, rfl⟩
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
  simp only at this
  omega

theorem valuation_le_of_mem {L : Type} [Field L] [NumberField L] (la' : HeightOneSpectrum (𝓞 L)) {N : ℕ}
    {b : 𝓞 L} (hb : b ∈ la'.asIdeal ^ N) : la'.valuation L (b : L) ≤ WithZero.exp (-(N : ℤ)) :=
  (la'.valuation_of_algebraMap b).trans_le ((la'.intValuation_le_pow_iff_mem b N).2 hb)

theorem trace_le_one : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L)), la.asIdeal.under (𝓞 K) = p.asIdeal → ∀ (m : ℕ) (y : Fin m → L), ∃ N : ℕ, ∀ b : 𝓞 L, (∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la → la'.asIdeal.under (𝓞 K) = p.asIdeal → b ∈ la'.asIdeal ^ N) → ∀ (T : CDVR), T.FinRes → ∀ (io : K →+* T.Fr) (e : ℕ), OverLa p T.V io e → ∀ x : Fin m → T.Fr, (∀ k, valV T.V (x k) ≤ 1) → (∀ (T' : CDVR) (i : T.Fr →+* T'.Fr) (e' : ℕ) (τ : L →+* T'.Fr) (e'' : ℕ), 0 < e' → (∀ z : T.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T.V z) → T'.FinRes → (∀ z : K, τ (algebraMap K L z) = i (io z)) → OverLa la T'.V τ e'' → valV T'.V (∑ k, τ (y k) * i (x k)) ≤ 1) → valV T.V (∑ k, io (Algebra.trace K L ((b : L) * y k)) * x k) ≤ 1 := by
  intro K L _ _ _ _ _ p la hla m y
  obtain ⟨N, hN⟩ := exists_bound p y
  refine ⟨N, fun b hb T hT io e ho x hx H => ?_⟩
  let Ω := AlgebraicClosure L
  let F := IntermediateField.normalClosure K L Ω
  obtain ⟨T', i, e', σ₀, he', hv, hT', hσ₀⟩ := GlobalTheory.SupDescent.exists_ext (L := F) T hT io
  have hv' : ∀ a : T.Fr, vV T'.V (i a) = (e' : ℤ) * vV T.V a := fun a => by
    by_cases h : a = 0
    · subst h; simp [vV]
    · exact hv a h
  have ho' := ho.bc i he' hv'
  have hF : ∀ (ρ : L →ₐ[K] Ω) (z : L), ρ z ∈ F := fun ρ z =>
    AlgHom.fieldRange_le_normalClosure ρ ⟨z, rfl⟩
  let τ : (L →ₐ[K] Ω) → L →+* T'.Fr := fun ρ =>
    σ₀.comp ((ρ.codRestrict F.toSubalgebra (hF ρ)).toRingHom)
  have hτ : ∀ ρ z, τ ρ z = σ₀ ⟨ρ z, hF ρ z⟩ := fun _ _ => rfl
  have hτK : ∀ ρ (a : K), τ ρ (algebraMap K L a) = i (io a) := fun ρ a => by
    rw [hτ, ← hσ₀ a]
    congr 1
    exact Subtype.ext (ρ.commutes a)
  have htr : ∀ z : L, i (io (Algebra.trace K L z)) = ∑ ρ : L →ₐ[K] Ω, τ ρ z := fun z => by
    have h1 := trace_eq_sum_embeddings Ω (K := K) (L := L) (x := z)
    have h2 : algebraMap K F (Algebra.trace K L z) = ∑ ρ : L →ₐ[K] Ω, (⟨ρ z, hF ρ z⟩ : F) := by
      apply Subtype.val_injective
      rw [IntermediateField.coe_sum]
      exact h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hσ₀, h2, map_sum]
    exact Finset.sum_congr rfl fun ρ _ => (hτ ρ z).symm
  rw [← valV_le_one_of_ext i he' hv]
  have hsum : i (∑ k, io (Algebra.trace K L ((b : L) * y k)) * x k) =
      ∑ ρ : L →ₐ[K] Ω, ∑ k, τ ρ (b : L) * (τ ρ (y k) * i (x k)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul (f := i), htr, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, mul_assoc]
  rw [hsum]
  refine Valuation.map_sum_le _ fun ρ _ => ?_
  have hunit (v : T'.V) : valV T'.V (algebraMap T'.V T'.Fr v) = 1 ↔ IsUnit v := by
    have hlt : valV T'.V (algebraMap T'.V T'.Fr v) < 1 ↔ v ∈ IsLocalRing.maximalIdeal T'.V := HeightOneSpectrum.valuation_lt_one_iff_mem _ v
    rw [← IsLocalRing.notMem_maximalIdeal, ← hlt, not_lt]
    exact ⟨fun h => h.ge, fun h => le_antisymm (HeightOneSpectrum.valuation_le_one _ v) h⟩
  have hpos_aux {v : T'.V} (h0 : v ≠ 0) (h : v ∈ IsLocalRing.maximalIdeal T'.V) :
      0 < vV T'.V (algebraMap T'.V T'.Fr v) := by
    have h1 : algebraMap T'.V T'.Fr v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective T'.V T'.Fr)).2 h0
    have h2 := (WithZero.log_lt_log (valV_ne_zero (V := T'.V) h1) one_ne_zero).2
      ((HeightOneSpectrum.valuation_lt_one_iff_mem _ v).2 h)
    simp only [WithZero.log_one] at h2
    simp only [vV]; omega
  have hex : ∃ (la : HeightOneSpectrum (𝓞 L)) (e : ℕ), OverLa la T'.V (τ ρ) e := by
    have hint : ∀ a : 𝓞 L, ∃ v : T'.V, algebraMap T'.V T'.Fr v = (τ ρ) a := fun a =>
      IsIntegrallyClosed.algebraMap_eq_of_integral (R := T'.V) (K := T'.Fr)
        (IsIntegral.map_of_comp_eq (Int.castRingHom T'.V) (τ ρ) (RingHom.ext_int _ _) a.isIntegral_coe)
    choose g0 hg0 using hint
    have hinj := IsFractionRing.injective T'.V T'.Fr
    let g : 𝓞 L →+* T'.V :=
      { toFun := g0
        map_one' := hinj (by simp [hg0])
        map_mul' := fun a b => hinj (by simp [hg0])
        map_zero' := hinj (by simp [hg0])
        map_add' := fun a b => hinj (by simp [hg0]) }
    have hg : ∀ a, algebraMap T'.V T'.Fr (g a) = (τ ρ) (algebraMap (𝓞 L) L a) := hg0
    have hne : (IsLocalRing.maximalIdeal T'.V).comap g ≠ ⊥ := by
      have : Finite (IsLocalRing.ResidueField T'.V) := hT'
      have hc : Nat.card (IsLocalRing.ResidueField T'.V) ≠ 0 := Nat.card_pos.ne'
      intro h
      have h1 : ((Nat.card (IsLocalRing.ResidueField T'.V) : ℕ) : 𝓞 L) ∈ (IsLocalRing.maximalIdeal T'.V).comap g := by
        rw [Ideal.mem_comap, map_natCast, ← IsLocalRing.residue_eq_zero_iff, map_natCast, ← nsmul_one]
        exact card_nsmul_eq_zero'
      rw [h, Ideal.mem_bot] at h1
      exact hc (by exact_mod_cast h1)
    let la : HeightOneSpectrum (𝓞 L) := ⟨(IsLocalRing.maximalIdeal T'.V).comap g, Ideal.comap_isPrime _ _, hne⟩
    have hun : ∀ a : 𝓞 L, a ∉ la.asIdeal → valV T'.V ((τ ρ) (algebraMap (𝓞 L) L a)) = 1 := fun a ha => by
      rw [← hg, hunit]
      exact IsLocalRing.notMem_maximalIdeal.1 ha
    have hone : ∀ x : L, la.valuation L x = 1 → valV T'.V ((τ ρ) x) = 1 := fun x hx => by
      obtain ⟨n, d, h⟩ := la.exists_primeCompl_mul_eq_of_integer x hx.le
      have hd : la.valuation L (algebraMap (𝓞 L) L d) = 1 := (la.valuation_eq_one_iff_notMem).2 d.2
      have hn : la.valuation L (algebraMap (𝓞 L) L n) = 1 := by rw [← h, map_mul, hx, hd, one_mul]
      have h2 := hun n ((la.valuation_eq_one_iff_notMem).1 hn)
      rwa [← h, map_mul, map_mul, hun d d.2, mul_one] at h2
    obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
    have hπK : la.valuation L (algebraMap (𝓞 L) L π) = WithZero.exp (-1 : ℤ) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, hπ]
    have hπ0 : algebraMap (𝓞 L) L π ≠ 0 := fun h => by simp [h] at hπK; exact WithZero.exp_ne_zero hπK.symm
    have hπm : π ∈ la.asIdeal := by
      rw [← la.valuation_lt_one_iff_mem (K := L), hπK, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    have hpos : 0 < vV T'.V ((τ ρ) (algebraMap (𝓞 L) L π)) := by
      rw [← hg]
      refine hpos_aux (fun h => ?_) hπm
      have := hg π
      rw [h, map_zero] at this
      exact (map_ne_zero (τ ρ)).2 hπ0 this.symm
    refine ⟨la, (vV T'.V ((τ ρ) (algebraMap (𝓞 L) L π))).toNat, by omega, fun a => ?_⟩
    rw [Int.toNat_of_nonneg hpos.le]
    by_cases ha : a = 0
    · simp [ha, vV, vLa]
    have hva : la.valuation L a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
    have h1 := hone (a * (algebraMap (𝓞 L) L π) ^ (-vLa la a)) (by
      rw [map_mul, map_zpow₀, hπK, ← WithZero.exp_zsmul, ← WithZero.exp_log hva, ← WithZero.exp_add]
      simp [vLa])
    have h2 := congrArg WithZero.log h1
    rw [map_mul, map_mul, map_zpow₀, map_zpow₀, WithZero.log_mul (valV_ne_zero ((map_ne_zero (τ ρ)).2 ha))
      (zpow_ne_zero _ (valV_ne_zero ((map_ne_zero (τ ρ)).2 hπ0))), WithZero.log_zpow, WithZero.log_one] at h2
    simp only [vV, smul_eq_mul] at h2 ⊢
    linarith
  obtain ⟨la', e'', hol⟩ := hex
  have hunder : la'.asIdeal.under (𝓞 K) = p.asIdeal := Ideal.ext fun a => by
    rw [Ideal.under_def, Ideal.mem_comap, ← GlobalTheory.SupDescent.val_lt_one_iff_mem hol,
      ← GlobalTheory.SupDescent.val_lt_one_iff_mem ho']
    exact Iff.of_eq (congrArg (fun t => valV T'.V t < 1) (hτK ρ a))
  rcases eq_or_ne la' la with rfl | hne
  · rw [← Finset.mul_sum, map_mul]
    exact mul_le_one' ((GlobalTheory.SupDescent.val_le_one_iff hol _).2 (la'.valuation_le_one b))
      (H T' i e' (τ ρ) e'' he' hv hT' (hτK ρ) hol)
  · refine Valuation.map_sum_le _ fun k _ => ?_
    rw [← mul_assoc, ← map_mul, map_mul]
    refine mul_le_one' ((GlobalTheory.SupDescent.val_le_one_iff hol _).2 ?_) ((valV_le_one_of_ext i he' hv _).2 (hx k))
    rw [map_mul]
    calc la'.valuation L (b : L) * la'.valuation L (y k)
        ≤ WithZero.exp (-(N : ℤ)) * WithZero.exp (N : ℤ) :=
          mul_le_mul' (valuation_le_of_mem la' (hb la' hne hunder)) (hN la' hunder k)
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]

end GlobalTheory.TraceSmall
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceIntegralOfSmallAtOtherPlacesStatement
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_integral_of_small_at_other_places : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L)), la.asIdeal.under (𝓞 K) = p.asIdeal → ∀ (m : ℕ) (y : Fin m → L), ∃ N : ℕ, ∀ b : 𝓞 L, (∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la → la'.asIdeal.under (𝓞 K) = p.asIdeal → b ∈ la'.asIdeal ^ N) → ∀ (T : CDVR), T.FinRes → ∀ (io : K →+* T.Fr) (e : ℕ), OverLa p T.V io e → ∀ x : Fin m → T.Fr, (∀ k, valV T.V (x k) ≤ 1) → (∀ (T' : CDVR) (i : T.Fr →+* T'.Fr) (e' : ℕ) (τ : L →+* T'.Fr) (e'' : ℕ), 0 < e' → (∀ z : T.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T.V z) → T'.FinRes → (∀ z : K, τ (algebraMap K L z) = i (io z)) → OverLa la T'.V τ e'' → valV T'.V (∑ k, τ (y k) * i (x k)) ≤ 1) → valV T.V (∑ k, io (Algebra.trace K L ((b : L) * y k)) * x k) ≤ 1 := by
  first | exact @GlobalTheory.TraceSmall.trace_le_one | exact GlobalTheory.TraceSmall.trace_le_one | (intros; apply GlobalTheory.TraceSmall.trace_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseSectionsValuesIntegralAtCoverLift
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseSectionsValuesIntegralAtCoverLift
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverLiftVal

theorem valV_le_one_of_nval {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] {e : ℕ} (he : 0 < e) {x : K'} (h : 0 ≤ nval V e x) : valV V x ≤ 1 := by
  by_cases hx : x = 0
  · subst hx; simp
  rw [nval_of_ne hx, EReal.coe_nonneg] at h
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have h1 : (0 : ℝ) ≤ (vV V x : ℝ) := by
    have := mul_nonneg h he'.le
    rwa [div_mul_cancel₀ _ he'.ne'] at this
  have h2 : 0 ≤ vV V x := by exact_mod_cast h1
  unfold vV at h2
  rw [← WithZero.log_le_log (valV_ne_zero hx) one_ne_zero, WithZero.log_one]
  omega

theorem le_one_at_lift : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, ∀ C : Cover T j σ, C.IsUnif → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c) (g : Fin m → Rul C.d.Xo₂ C.d.c₂), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n) → (∀ k, g k ∈ sec C.d.Xo₂ C.d.c₂ a n) → (∀ k, C.IsPull (β k) (g k)) → ∀ y : Fin m → C.d.c₂.F, (∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v (∑ k, y k • g k)) → ∀ (T0 : CDVR) (io : T.Q.c.F →+* T0.Fr) (pt : IntFr (T.Q.Xo j) T.Q.c T0 io), T0.FinRes → ∀ (T' : CDVR) (i : T0.Fr →+* T'.Fr) (e' : ℕ) (τ : C.d.c₂.F →+* T'.Fr) (e'' : ℕ), 0 < e' → (∀ z : T0.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T0.V z) → T'.FinRes → (∀ z : T.Q.c.F, τ (C.inc z) = i (io z)) → OverLa la T'.V τ e'' → valV T'.V (∑ k, τ (y k) * i (evI pt (β k))) ≤ 1 := by
  intro D T hL j hj σ C hU la a n m β g hβ hg hpull y hint T0 io pt hT0 T' i e' τ e'' he' hi hT' hτ ho
  obtain ⟨y₁, φ, hφ, hmap⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange _ _ _ _ (T.Q.Xo j) T.Q.c T0 T' io pt i e' he' hi
  let σ' : C.c'.F →+* T'.Fr := τ.comp (C.d.eF : C.c'.F →+* C.d.c₂.F)
  have hσ' : ∀ z, σ' (incF T.Q.c C.c' C.hle z) = (i.comp io) z := fun z => hτ z
  obtain ⟨y₂, hy₂⟩ := GlobalTheory.SupDescent.exists_intFr_ext C.hle (io := i.comp io) σ' hσ' y₁
  obtain ⟨T'', iT, e₃, y₃, io₂, y₄, hext, hT'', hio₂, hover⟩ := GlobalTheory.T.exists_finiteExtension_integralFramedPoint_lift_cover _ _ _ _ (T.Q.Xo j) C.c' 0 C.d hU.1 T' σ' y₂ hT'
  obtain ⟨he₃, hv₃, ψ, hψe, hψ⟩ := hext
  have hio : io₂ = iT.comp τ := by
    ext z
    obtain ⟨w, rfl⟩ := C.d.eF.surjective z
    exact hio₂ w
  subst hio
  letI : Algebra C.c'.F T''.Fr := (iT.comp σ').toAlgebra
  letI : Algebra C.d.c₂.F T''.Fr := (iT.comp τ).toAlgebra
  letI : Algebra T.Q.c.F T''.Fr := (iT.comp (i.comp io)).toAlgebra
  letI : Algebra T.Q.c.F T'.Fr := (i.comp io).toAlgebra
  letI : Algebra C.c'.F T'.Fr := σ'.toAlgebra
  have hA : AlgOver T.Q.c C.c' C.hle T''.Fr := fun z => congrArg iT (hσ' z)
  let φ₂ : T'.Fr →ₐ[T.Q.c.F] T''.Fr := { iT with commutes' := fun _ => rfl }
  have hmap₂ : FrMap φ₂ (y₂.1.res C.hle hσ') (y₃.1.res C.hle hA) := by
    obtain ⟨hx, hu, pm, h1, h2, h3⟩ := hψ
    rw [hψe] at hx hu h2
    exact ⟨hx, hu, pm, h1, h2, h3⟩
  have hval : ∀ k, evI y₄ (g k) = iT (i (evI pt (β k))) := fun k => by
    have h1 := hpull k T''.Fr hA (fun _ => rfl) y₄.1 y₃.1 hover
    have h2 := GlobalTheory.FlagTan.evR_frMap (hβ k).1 hmap₂
    letI : Algebra T.Q.c.F T0.Fr := io.toAlgebra
    have h3 := GlobalTheory.FlagTan.evR_frMap (hβ k).1 hmap
    rw [hy₂] at h2
    show evR _ _ (g k) y₄.1 = _
    rw [h1, h2, h3]
    exact congrArg iT (DFunLike.congr_fun hφ _)
  have hsum : evI y₄ (∑ k, y k • g k) = iT (∑ k, τ (y k) * i (evI pt (β k))) := by
    show evR _ _ (∑ k, y k • g k) y₄.1 = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [GlobalTheory.SupDescent.evR_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    exact congrArg₂ (· * ·) rfl (hval k)
  have ho₂ : OverLa la T''.V (iT.comp τ) (e₃ * e'') := ho.bc iT he₃ hv₃
  have h : 0 ≤ nval T''.V (e₃ * e'') (evI y₄ (∑ k, y k • g k)) := hint _ ⟨PtV.mk (cls := algCls C.d.Xo₂ C.d.c₂) (PY := Unit) (lies := fun _ _ _ _ => True) la ho₂ y₄ hT''
    () trivial, rfl⟩
  rw [hsum, nval_bc iT he₃ hv₃] at h
  exact valV_le_one_of_nval ho.1 h

end GlobalTheory.CoverLiftVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseSectionsValuesIntegralAtCoverLiftStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseSections_values_integral_at_coverLift : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, ∀ C : Cover T j σ, C.IsUnif → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c) (g : Fin m → Rul C.d.Xo₂ C.d.c₂), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n) → (∀ k, g k ∈ sec C.d.Xo₂ C.d.c₂ a n) → (∀ k, C.IsPull (β k) (g k)) → ∀ y : Fin m → C.d.c₂.F, (∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v (∑ k, y k • g k)) → ∀ (T0 : CDVR) (io : T.Q.c.F →+* T0.Fr) (pt : IntFr (T.Q.Xo j) T.Q.c T0 io), T0.FinRes → ∀ (T' : CDVR) (i : T0.Fr →+* T'.Fr) (e' : ℕ) (τ : C.d.c₂.F →+* T'.Fr) (e'' : ℕ), 0 < e' → (∀ z : T0.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T0.V z) → T'.FinRes → (∀ z : T.Q.c.F, τ (C.inc z) = i (io z)) → OverLa la T'.V τ e'' → valV T'.V (∑ k, τ (y k) * i (evI pt (β k))) ≤ 1 := by
  first | exact @GlobalTheory.CoverLiftVal.le_one_at_lift | exact GlobalTheory.CoverLiftVal.le_one_at_lift | (intros; apply GlobalTheory.CoverLiftVal.le_one_at_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCoverFormPullbackCombination
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCoverFormPullbackCombination
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

namespace GlobalTheory.CoverPullComb


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_pull_comb_integral : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ C : Cover T j σ, C.IsUnif → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n) → ∀ y : Fin m → C.d.c₂.F, (∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k)) ∈ C.intForms a n {la} → ∃ g : Fin m → Rul C.d.Xo₂ C.d.c₂, (∀ k, g k ∈ sec C.d.Xo₂ C.d.c₂ a n) ∧ (∀ k, C.IsPull (β k) (g k)) ∧ ∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v (∑ k, y k • g k) := by
  intro D T hL j hj σ hσ a n hD C hU hP la m β hβ y hy
  have hpull : ∀ k, ∃ g₂ ∈ sec C.d.Xo₂ C.d.c₂ a n, C.IsPull (β k) g₂ :=
    fun k => GlobalTheory.CovPull.exists_pull D T hL j hj σ hσ C hU.1 a n (β k) (hβ k)
  choose g hg hgp using hpull
  refine ⟨g, hg, hgp, ?_⟩
  obtain ⟨f₂, ⟨hf₂c, hf₂i⟩, hf₂r⟩ := hy

  let R : Rul C.d.Xo₂ C.d.c₂ →ₛₗ[C.σ₂] (GA D (T.V j σ) → ℂ) :=
    (lieFac (T.Q.Dw j) (xiR D) a : ℂ) •
      ((adel (T.V j σ) C.dict₂ (muPin (T.V j σ) C.dict₂ (T.mu j σ) C.cc₂)).comp (rdU C.U₂))
  have hR : ∀ f, C.rd a f = R f := fun _ => rfl
  have hsum : C.rd a (∑ k, y k • g k) = ∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hR, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, ← hR, hP.2 (β k) (hβ k) (g k) (hg k) (hgp k)]
  set s := ∑ k, y k • g k with hs
  have hsmem : s ∈ sec C.d.Xo₂ C.d.c₂ a n := Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hg k)
  have hdmem : f₂ - s ∈ sec C.d.Xo₂ C.d.c₂ a n := Submodule.sub_mem _ hf₂c.1 hsmem
  have hd0 : C.rd a (f₂ - s) = 0 := by
    rw [hR, map_sub, ← hR, ← hR, hf₂r, hsum, sub_self]
  have heq : f₂ = s := by
    by_contra hne
    have hne' : f₂ - s ≠ 0 := sub_ne_zero.mpr hne
    have hli : LinearIndependent C.d.c₂.F (fun _ : Fin 1 => f₂ - s) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      rw [Fin.sum_univ_one] at hc
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      by_contra hc0
      apply hne'
      calc f₂ - s = (c 0)⁻¹ • (c 0 • (f₂ - s)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        _ = 0 := by rw [hc, smul_zero]
    have hC := GlobalTheory.CoverIndep.cover_rd_linearIndependent D T hL j hj σ hσ C hU hP.1 a n hD 1 (fun _ => f₂ - s)
      (fun _ => hdmem) hli
    exact hC.ne_zero 0 hd0
  intro v hv
  rw [← heq]
  exact hf₂i la rfl v hv

end GlobalTheory.CoverPullComb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCoverFormPullbackCombinationStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_cover_form_pullback_combination : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ C : Cover T j σ, C.IsUnif → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n) → ∀ y : Fin m → C.d.c₂.F, (∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k)) ∈ C.intForms a n {la} → ∃ g : Fin m → Rul C.d.Xo₂ C.d.c₂, (∀ k, g k ∈ sec C.d.Xo₂ C.d.c₂ a n) ∧ (∀ k, C.IsPull (β k) (g k)) ∧ ∀ v ∈ valSet C.d.Xo₂ C.d.c₂ (algCls C.d.Xo₂ C.d.c₂) la, 0 ≤ v (∑ k, y k • g k) := by
  first | exact @GlobalTheory.CoverPullComb.exists_pull_comb_integral | exact GlobalTheory.CoverPullComb.exists_pull_comb_integral | (intros; apply GlobalTheory.CoverPullComb.exists_pull_comb_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceCombinationCoverFormIntegralOverPrime
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

noncomputable section

namespace GlobalTheory.TraceIdem

theorem nval_nonneg_iff {T : CDVR} {e : ℕ} (he : 0 < e) (z : T.Fr) : 0 ≤ nval T.V e z ↔ valV T.V z ≤ 1 := by
  by_cases hz : z = 0
  · subst hz; simp [nval]
  rw [nval_of_ne hz, EReal.coe_nonneg]
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  rw [div_nonneg_iff]
  have h1 : valV T.V z ≠ 0 := valV_ne_zero hz
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · have h' : 0 ≤ vV T.V z := by exact_mod_cast h
      unfold vV at h'
      rw [← WithZero.log_le_log h1 one_ne_zero, WithZero.log_one]; omega
    · linarith
  · intro h
    left
    refine ⟨?_, he'.le⟩
    have := (WithZero.log_le_log h1 one_ne_zero).2 h
    rw [WithZero.log_one] at this
    have h' : 0 ≤ vV T.V z := by unfold vV; omega
    exact_mod_cast h'

theorem trace_comb_integral : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}) → (∀ k ∈ T.Kf j σ, ∀ h, T.mu j σ (h * k) = T.mu j σ h) → ∀ C : Cover T j σ, C.IsUnif → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (p : HeightOneSpectrum (𝓞 T.Q.c.F)), (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; la.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal) → ∀ (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) (β k) ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)) → (∀ k, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) p, 0 ≤ v (β k)) → ∀ y : Fin m → C.d.c₂.F, (∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k)) ∈ C.intForms a n {la} → ∃ N : ℕ, ∀ b : 𝓞 C.d.c₂.F, (∀ la' : HeightOneSpectrum (𝓞 C.d.c₂.F), la' ≠ la → (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; la'.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal) → b ∈ la'.asIdeal ^ N) → ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) p, 0 ≤ v (∑ k, (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; Algebra.trace T.Q.c.F C.d.c₂.F ((b : C.d.c₂.F) * y k)) • β k) := by
  intro D T hL j hj σ hσ a n hD hspan hmu C hU hP la p hla m β hβ hβi y hφ
  obtain ⟨g, hgs, hgp, hgi⟩ := (GlobalTheory.T.exists_integral_cover_form_pullback_combination D T hL j hj σ hσ a n hD C hU hP la m β (fun k => (hβ k).1) y hφ)
  letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra
  obtain ⟨N, hN⟩ := GlobalTheory.T.trace_integral_of_small_at_other_places T.Q.c.F C.d.c₂.F p la hla m y
  refine ⟨N, fun b hb v hv => ?_⟩
  have hx : ∀ k, 0 ≤ v (β k) := fun k => hβi k v hv
  obtain ⟨⟨q, T0, io, e, ho, pt, hpt, eta, heta, rfl⟩, rfl⟩ := hv
  have hx' : ∀ k, valV T0.V (evI pt (β k)) ≤ 1 := fun k => (nval_nonneg_iff ho.1 _).1 (hx k)
  have hs : ∀ (s : Finset (Fin m)) (t : Fin m → T.Q.c.F),
      evI pt (∑ k ∈ s, t k • β k) = ∑ k ∈ s, io (t k) * evI pt (β k) := by
    intro s t
    induction s using Finset.induction_on with
    | empty => simpa using (isEval_evI pt).zero ()
    | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, evI_add, evI_smul, ih]
  show 0 ≤ nval T0.V e (evI pt _)
  rw [nval_nonneg_iff ho.1, hs]
  exact hN b hb T0 hpt io e ho (fun k => evI pt (β k)) hx'
    (fun T' i e' τ e'' he' hi hT' hτ ho' =>
      GlobalTheory.T.baseSections_values_integral_at_coverLift D T hL j hj σ C hU la a n m β g (fun k => (hβ k).1) hgs hgp y hgi T0 io pt hpt T' i e' τ e'' he' hi hT' hτ ho')

end GlobalTheory.TraceIdem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceCombinationCoverFormIntegralOverPrimeStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceCombination_coverForm_integral_over_prime : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → holSub0 (T.U j σ).X (laU (T.U j σ) a n) ≤ Submodule.span ℂ (rdU (T.U j σ) '' {f | f ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) f ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)}) → (∀ k ∈ T.Kf j σ, ∀ h, T.mu j σ (h * k) = T.mu j σ h) → ∀ C : Cover T j σ, C.IsUnif → C.IsPinned a n → ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (p : HeightOneSpectrum (𝓞 T.Q.c.F)), (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; la.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal) → ∀ (m : ℕ) (β : Fin m → Rul (T.Q.Xo j) T.Q.c), (∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c a n ∧ rdU (T.U j σ) (β k) ∈ holSub0 (T.U j σ).X (laU (T.U j σ) a n)) → (∀ k, ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) p, 0 ≤ v (β k)) → ∀ y : Fin m → C.d.c₂.F, (∑ k, C.σ₂ (y k) • T.phiJ j σ a (β k)) ∈ C.intForms a n {la} → ∃ N : ℕ, ∀ b : 𝓞 C.d.c₂.F, (∀ la' : HeightOneSpectrum (𝓞 C.d.c₂.F), la' ≠ la → (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; la'.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal) → b ∈ la'.asIdeal ^ N) → ∀ v ∈ valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c) p, 0 ≤ v (∑ k, (letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra; Algebra.trace T.Q.c.F C.d.c₂.F ((b : C.d.c₂.F) * y k)) • β k) := by
  first | exact @GlobalTheory.TraceIdem.trace_comb_integral | exact GlobalTheory.TraceIdem.trace_comb_integral | (intros; apply GlobalTheory.TraceIdem.trace_comb_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisBoundedModuleValuationRingPi
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisBoundedModuleValuationRingPi
open IsDedekindDomain NumberField

namespace GlobalTheory

theorem locBasis_of_bounded {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    (d : ℕ) (M : Set (Fin d → F)) (h0 : (0 : Fin d → F) ∈ M)
    (hadd : ∀ x ∈ M, ∀ y ∈ M, x + y ∈ M)
    (hsmul : ∀ a : F, p.valuation F a ≤ 1 → ∀ x ∈ M, a • x ∈ M)
    (hstd : ∀ i, Pi.single i 1 ∈ M)
    (hbd : ∃ D : F, D ≠ 0 ∧ ∀ x ∈ M, ∀ i, p.valuation F (D * x i) ≤ 1) :
    ∃ (m : ℕ) (b : Fin m → Fin d → F), (∀ k, b k ∈ M) ∧
      (∀ x ∈ M, ∃ a : Fin m → F, (∀ k, p.valuation F (a k) ≤ 1) ∧ x = ∑ k, a k • b k) ∧
      LinearIndependent F b := by
  obtain ⟨D, hD, hDM⟩ := hbd
  set A : ValuationSubring F := p.valuationSubringAtPrime F with hA
  haveI : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 F) p.ne_bot _
  have memA : ∀ a : F, a ∈ A ↔ p.valuation F a ≤ 1 := by
    intro a
    rw [hA, HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff]
  let M' : Submodule A (Fin d → F) :=
    { carrier := M
      add_mem' := fun {x y} hx hy => hadd x hx y hy
      zero_mem' := h0
      smul_mem' := fun c x hx => by
        have : c • x = (c : F) • x := rfl
        rw [this]
        exact hsmul _ ((memA _).1 c.2) x hx }
  let e : Fin d → Fin d → F := fun i => D⁻¹ • Pi.single i 1
  have heF : LinearIndependent F e := by
    have h1 := (Pi.basisFun F (Fin d)).linearIndependent.units_smul
      (fun _ => Units.mk0 D⁻¹ (inv_ne_zero hD))
    convert h1 using 1
    ext i j
    simp [e, Pi.basisFun_apply]
  have heA : LinearIndependent A e := (LinearIndependent.iff_fractionRing A F).2 heF
  have hle : M' ≤ Submodule.span A (Set.range e) := by
    intro x hx
    have hx' : x = ∑ i, (D * x i) • e i := by
      ext j
      simp [e, Finset.sum_apply, Pi.single_apply]
      rw [mul_comm D, mul_assoc, mul_inv_cancel₀ hD, mul_one]
    rw [hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    have hc : D * x i ∈ A := (memA _).2 (hDM x hx i)
    have : (D * x i) • e i = (⟨D * x i, hc⟩ : A) • e i := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨n, bas⟩ := Submodule.basisOfPidOfLE hle (Module.Basis.span heA)
  refine ⟨n, fun k => (bas k : Fin d → F), fun k => (bas k).2, ?_, ?_⟩
  · intro x hx
    refine ⟨fun k => (bas.repr ⟨x, hx⟩ k : F), fun k => (memA _).1 (bas.repr ⟨x, hx⟩ k).2, ?_⟩
    have h := congrArg (fun y : M' => (y : Fin d → F)) (bas.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  · have h1 : LinearIndependent A (M'.subtype ∘ bas) :=
      bas.linearIndependent.map' M'.subtype (Submodule.ker_subtype M')
    exact (LinearIndependent.iff_fractionRing A F).1 h1

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisBoundedModuleValuationRingPiStatement
open IsDedekindDomain NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_bounded_module_valuationRing_pi : ∀ {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) (d : ℕ) (M : Set (Fin d → F)), (0 : Fin d → F) ∈ M → (∀ x ∈ M, ∀ y ∈ M, x + y ∈ M) → (∀ a : F, p.valuation F a ≤ 1 → ∀ x ∈ M, a • x ∈ M) → (∀ i, Pi.single i 1 ∈ M) → (∃ D : F, D ≠ 0 ∧ ∀ x ∈ M, ∀ i, p.valuation F (D * x i) ≤ 1) → ∃ (m : ℕ) (b : Fin m → Fin d → F), (∀ k, b k ∈ M) ∧ (∀ x ∈ M, ∃ a : Fin m → F, (∀ k, p.valuation F (a k) ≤ 1) ∧ x = ∑ k, a k • b k) ∧ LinearIndependent F b := by
  first | exact @GlobalTheory.locBasis_of_bounded | exact GlobalTheory.locBasis_of_bounded | (intros; apply GlobalTheory.locBasis_of_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastPowMulValuationLeOneOfNotPowSuccDvdDiffer
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastPowMulValuationLeOneOfNotPowSuccDvdDiffer
open NumberField IsDedekindDomain
open Classical

namespace GlobalTheory

theorem natCast_pow_mul_valuation_le_one_of_not_pow_succ_dvd_differentIdeal :
    ∀ (l c : ℕ) (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      (la : HeightOneSpectrum (𝓞 L)), ((l : ℕ) : 𝓞 L) ∈ la.asIdeal →
      ¬ la.asIdeal ^ (c + 1) ∣ differentIdeal (𝓞 K) (𝓞 L) →
      ∀ y : L, (∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), la.valuation L (y * (d : L)) ≤ 1) →
        la.valuation L ((l : L) ^ c * y) ≤ 1 := by
  intro l c K L _ _ _ _ _ la hl hD y hy
  obtain ⟨d₀, hd₀D, hd₀⟩ : ∃ d₀ ∈ differentIdeal (𝓞 K) (𝓞 L), d₀ ∉ la.asIdeal ^ (c + 1) := by
    by_contra h
    push_neg at h
    exact hD (Ideal.dvd_iff_le.mpr h)
  have h1 : la.intValuation ((l : 𝓞 L) ^ c) ≤ WithZero.exp (-(c : ℤ)) :=
    (la.intValuation_le_pow_iff_mem _ c).mpr (Ideal.pow_mem_pow hl c)
  have h2 : WithZero.exp (-(c : ℤ)) ≤ la.intValuation d₀ := by
    rw [HeightOneSpectrum.exp_le_intValuation_iff_emultiplicity_le]
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem la,
      HeightOneSpectrum.intValuation_le_exp_iff_le_emultiplicity, not_le] at hd₀
    rw [← ENat.lt_natCast_add_one_iff]
    exact_mod_cast hd₀
  have hyd := hy d₀ hd₀D
  have e1 : la.valuation L (d₀ : L) = la.intValuation d₀ := la.valuation_of_algebraMap (K := L) d₀
  have e2 : la.valuation L ((l : L) ^ c) = la.intValuation ((l : 𝓞 L) ^ c) := by
    rw [← la.valuation_of_algebraMap (K := L)]
    simp
  rw [Valuation.map_mul] at hyd ⊢
  calc la.valuation L ((l : L) ^ c) * la.valuation L y
      ≤ la.valuation L (d₀ : L) * la.valuation L y := by
        gcongr
        rw [e1, e2]
        exact h1.trans h2
    _ = la.valuation L y * la.valuation L (d₀ : L) := mul_comm _ _
    _ ≤ 1 := hyd

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastPowMulValuationLeOneOfNotPowSuccDvdDifferStatement
open NumberField IsDedekindDomain
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_prime_pow_mul_le_one_of_not_dvd_different : ∀ (l c : ℕ) (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (la : HeightOneSpectrum (𝓞 L)), ((l : ℕ) : 𝓞 L) ∈ la.asIdeal → ¬ la.asIdeal ^ (c + 1) ∣ differentIdeal (𝓞 K) (𝓞 L) → ∀ y : L, (∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), la.valuation L (y * (d : L)) ≤ 1) → la.valuation L ((l : L) ^ c * y) ≤ 1 := by
  first | exact @GlobalTheory.natCast_pow_mul_valuation_le_one_of_not_pow_succ_dvd_differentIdeal | exact GlobalTheory.natCast_pow_mul_valuation_le_one_of_not_pow_succ_dvd_differentIdeal | (intros; apply GlobalTheory.natCast_pow_mul_valuation_le_one_of_not_pow_succ_dvd_differentIdeal <;> assumption)
end
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.NX Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.CoverRead GlobalTheory.TowerCov GlobalTheory.Member
open scoped TensorProduct Matrix
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.XiIntSteps

theorem exists_local_basis {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) {V : Type} [AddCommGroup V]
    [Module F V] (C : Submodule F V) [FiniteDimensional F C] (Int : V → Prop) (h0 : Int 0)
    (hadd : ∀ f g, Int f → Int g → Int (f + g)) (hsmul : ∀ (a : F) f, p.valuation F a ≤ 1 → Int f → Int (a • f))
    (hbd : ∀ f ∈ C, ∃ κ : F, κ ≠ 0 ∧ Int (κ • f)) {M : ℕ} (g : Fin M → V) (hg : ∀ i, g i ∈ C)
    (hgen : ∀ f ∈ C, Int f → ∃ o : Fin M → F, (∀ i, p.valuation F (o i) ≤ 1) ∧ f = ∑ i, o i • g i) :
    ∃ (m : ℕ) (β : Fin m → V), (∀ k, β k ∈ C ∧ Int (β k)) ∧ (∀ f ∈ C, ∃ c : Fin m → F, f = ∑ k, c k • β k) ∧
      ∀ c : Fin m → F, Int (∑ k, c k • β k) → ∀ k, p.valuation F (c k) ≤ 1 := by
  classical
  let B₀ := Module.finBasis F C
  choose κ hκ0 hκ using fun i => hbd (B₀ i : V) (B₀ i).2
  let B := B₀.unitsSMul fun i => Units.mk0 (κ i) (hκ0 i)
  have hB : ∀ i, ((B i : C) : V) = κ i • (B₀ i : V) := fun i => by
    simp [B, Module.Basis.unitsSMul_apply, Units.smul_def]
  let e : (Fin (Module.finrank F C) → F) →ₗ[F] V := C.subtype ∘ₗ (B.equivFun.symm : _ →ₗ[F] C)
  have heC : ∀ x, e x ∈ C := fun x => (B.equivFun.symm x).2
  have he1 : ∀ f : C, e (B.equivFun f) = f := fun f => by simp [e]
  have heinj : Function.Injective e := Subtype.val_injective.comp B.equivFun.symm.injective
  have hsingle : ∀ i, e (Pi.single i 1) = κ i • (B₀ i : V) := fun i => by
    rw [← hB, ← he1 (B i)]
    congr 1
    funext k
    simp [Module.Basis.equivFun_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]
  let S : Set (Fin (Module.finrank F C) → F) := {x | Int (e x)}
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 F))
    (fun ki : Fin M × Fin (Module.finrank F C) => B.equivFun ⟨g ki.1, hg ki.1⟩ ki.2)
  have hvle : ∀ s : 𝓞 F, p.valuation F (algebraMap (𝓞 F) F s) ≤ 1 := fun s => by
    rw [HeightOneSpectrum.valuation_of_algebraMap]; exact p.intValuation_le_one s
  obtain ⟨m, b, hbM, hbsp, hbli⟩ := GlobalTheory.T.exists_basis_bounded_module_valuationRing_pi p _ S (by show Int (e 0); rw [map_zero]; exact h0)
    (fun x hx y hy => by show Int (e (x + y)); rw [map_add (f := _)]; exact hadd _ _ hx hy)
    (fun a ha x hx => by show Int (e (a • x)); rw [map_smul]; exact hsmul _ _ ha hx)
    (fun i => by show Int (e _); rw [hsingle]; exact hκ i)
    ⟨algebraMap (𝓞 F) F d, (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 (nonZeroDivisors.coe_ne_zero d),
      fun x hx i => by
        obtain ⟨o, ho, hxo⟩ := hgen (e x) (heC x) hx
        have hx' : x = ∑ k, o k • B.equivFun ⟨g k, hg k⟩ := heinj (by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [hxo, map_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [map_smul, he1])
        rw [hx', Finset.sum_apply, Finset.mul_sum]
        refine Valuation.map_sum_le _ fun k _ => ?_
        obtain ⟨r, hr⟩ := hd (k, i)
        rw [Pi.smul_apply, smul_eq_mul, mul_left_comm, map_mul, ← Algebra.smul_def]
        refine mul_le_one' (ho k) ?_
        rw [← hr]
        exact hvle r⟩
  refine ⟨m, fun k => e (b k), fun k => ⟨heC _, hbM k⟩, fun f hf => ?_, fun c hc k => ?_⟩
  · have hxsp : B.equivFun ⟨f, hf⟩ ∈ Submodule.span F (Set.range b) := by
      rw [← Finset.univ_sum_single (B.equivFun ⟨f, hf⟩)]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : Pi.single i (B.equivFun ⟨f, hf⟩ i) = B.equivFun ⟨f, hf⟩ i • (Pi.single i (1 : F) : Fin _ → F) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this]
      refine Submodule.smul_mem _ _ ?_
      obtain ⟨a, -, ha⟩ := hbsp (Pi.single i 1) (by show Int (e _); rw [hsingle]; exact hκ i)
      rw [ha]; exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hxsp
    refine ⟨c, ?_⟩
    have := he1 ⟨f, hf⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc, map_sum] at this
    exact this.symm.trans (Finset.sum_congr rfl fun k _ => map_smul _ _ _)
  · have hy : (∑ k, c k • b k) ∈ S := by
      show Int (e _)
      convert hc using 1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; exact Finset.sum_congr rfl fun k _ => map_smul _ _ _
    obtain ⟨a, ha, hya⟩ := hbsp _ hy
    have hz : ∑ k, (c k - a k) • b k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]; rw [← hya, sub_self]
    rw [sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hbli _ hz k)]
    exact ha k

theorem intForm_descent_below (l e : ℕ) (hl : l.Prime) : ∃ c₀ : ℕ, ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j →
    ∀ w : WeightFamilies.Wt D j, w.LastPos → Dom (wtA w) w.n →
    holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) ≤ Submodule.span ℂ (rdU (T.U j T.σ₀) ''
      {f | f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧ rdU (T.U j T.σ₀) f ∈ holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n)}) →
    (∀ k ∈ T.Kf j T.σ₀, ∀ h, T.mu j T.σ₀ (h * k) = T.mu j T.σ₀ h) →
    ∀ C : Cover T j T.σ₀, C.IsUnif → C.IsPinned (wtA w) w.n →
    ∀ (la : HeightOneSpectrum (𝓞 C.d.c₂.F)) (p : HeightOneSpectrum (𝓞 T.Q.c.F)),
      la.asIdeal.comap (RingOfIntegers.mapRingHom C.inc) = p.asIdeal →
      ((l : ℕ) : 𝓞 C.d.c₂.F) ∈ la.asIdeal → ((l : ℕ) : 𝓞 C.d.c₂.F) ∉ la.asIdeal ^ (e + 1) →
      ∀ φ ∈ C.intForms (wtA w) w.n {la}, (∀ k ∈ T.Kf j T.σ₀, ∀ h, φ (h * k) = φ h) →
        ∃ (m : ℕ) (x : Fin m → C.d.c₂.F) (ψ : Fin m → (GA D (T.V j T.σ₀) → ℂ)), (∀ i, la.valuation C.d.c₂.F (x i) ≤ 1) ∧
          (∀ i, ψ i ∈ baseInt T j T.σ₀ (wtA w) w.n {p}) ∧ ((l : ℂ) ^ c₀) • φ = ∑ i, C.σ₂ (x i) • ψ i := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.relative_different_order_bounded_absolute_ramification l e hl
  refine ⟨c, ?_⟩
  intro D T hL j hj w hlast hD hspan hK C hU hP la p hp0 hl1 hl2 φ hφ hφK
  letI : Algebra T.Q.c.F C.d.c₂.F := C.inc.toAlgebra
  have hp : la.asIdeal.under (𝓞 T.Q.c.F) = p.asIdeal := by
    rw [← hp0]; ext x; rfl
  have hσ := T.toCore.good_σ₀
  have hlp : ((l : ℕ) : 𝓞 T.Q.c.F) ∈ p.asIdeal := by
    rw [← hp0, Ideal.mem_comap, map_natCast]; exact hl1
  have hgood : T.Q.l.GoodAt l :=
    Formalism.L2.Pj.goodAt_of_two_primes hL.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne l hl
  have hfd := hL.cuspFD _ hj _ _ hD
  obtain ⟨M, g, hg, hgen⟩ := GlobalTheory.SupFinite.supSet_finitelyGenerated _ _ _ _ (T.Q.Xo j) T.Q.c _ (T.U j) (hL.unf _ hj) p l hl hlp
    hgood (wtA w) w.n hD hfd
  have hval := GlobalTheory.TowVal.bddAll_one_iff_valSet_nonneg _ _ _ _ (T.Q.Xo j) T.Q.c p
  obtain ⟨m, β, hβ, hspanβ, hprim⟩ := exists_local_basis p (cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n)
    (GlobalTheory.GoodPts.BddAll (T.Q.Xo j) T.Q.c p 1)
    ((hval 0).2 (by rintro _ ⟨y, rfl⟩; rw [vAtV_zero]; exact le_top))
    (fun f g => GlobalTheory.GoodPtsModel.bddAll_add)
    (fun a f ha hf => by
      by_cases h0 : a = 0
      · subst h0
        set_option synthInstance.maxHeartbeats 100000 in
          rw [zero_smul]
        exact (hval 0).2 (by rintro _ ⟨y, rfl⟩; rw [vAtV_zero]; exact le_top)
      have hv : (0 : ℤ) ≤ vLa p a := by
        have hne : p.valuation T.Q.c.F a ≠ 0 := (Valuation.ne_zero_iff _).2 h0
        have := (WithZero.log_le_log hne one_ne_zero).2 ha
        simp only [WithZero.log_one] at this
        simp only [vLa]; omega
      exact (GlobalTheory.GoodPtsModel.smul_mem_supSet (W := ⊤) hv ⟨trivial, hf⟩).2)
    (fun f hf => by
      obtain ⟨κ, h1, h2⟩ := GlobalTheory.T.cuspidal_section_bounded_nonzero_multiple _ _ _ _ (T.Q.Xo j) T.Q.c _ (T.U j) (hL.unf _ hj) p l hl hlp hgood (wtA w) w.n f hD hf
      exact ⟨κ, h1, (GlobalTheory.GoodPtsModel.bddAll_iff_smul _ _).1 h2⟩)
    g (fun i => (hg i).1) (fun f hf hb => hgen f ⟨hf, hb⟩)
  have hβs : ∀ k, β k ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧
      rdU (T.U j T.σ₀) (β k) ∈ holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA w) w.n) := fun k =>
    ⟨cusp_le_sec _ _ _ _ _ (hβ k).1, ReciprocityTheory.ChartRestriction.G.PullbackSections.rdC_mem_holSub0 T.good_σ₀ (wtA w) w.n ⟨β k, (hβ k).1⟩⟩
  obtain ⟨m', x, ψ, hψ, hφe⟩ := GlobalTheory.T.holomorphic_sections_span_restriction D T hL j hj T.σ₀ hσ C hU _ _ hD hP hspan hK φ
    (C.intForms_subset _ _ _ hφ) hφK
  have hcc' : ∀ i, ∃ cc : Fin m → T.Q.c.F, ψ i = ∑ k, T.σ₀ (cc k) • T.phiJ j T.σ₀ (wtA w) (β k) := fun i => by
    obtain ⟨f, hf, hfe⟩ := hψ i
    obtain ⟨cc, hcc⟩ := hspanβ f (GlobalTheory.T.mem_cuspForms_allEmbeddings_of_inclusion_reading D T hL j hj w hlast f hf.1 hf.2)
    refine ⟨cc, ?_⟩
    rw [← hfe, hcc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [CoreJ.phiJ, map_sum, map_smulₛₗ, map_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  choose cc hcc using hcc'
  have hσ₂ : ∀ z, C.σ₂ (C.inc z) = T.σ₀ z := fun z => congrArg (fun f => f z) hU.2.2.1
  let y : Fin m → C.d.c₂.F := fun k => ∑ i, x i * C.inc (cc i k)
  have hsum : φ = ∑ k, C.σ₂ (y k) • T.phiJ j T.σ₀ (wtA w) (β k) := by
    rw [hφe]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, hcc, Finset.smul_sum, smul_smul, map_sum, Finset.sum_smul, map_mul, hσ₂]
    exact Finset.sum_comm
  have hφ' : (∑ k, C.σ₂ (y k) • T.phiJ j T.σ₀ (wtA w) (β k)) ∈ C.intForms (wtA w) w.n {la} := hsum ▸ hφ
  obtain ⟨N, hN⟩ := GlobalTheory.T.traceCombination_coverForm_integral_over_prime D T hL j hj T.σ₀ hσ _ _ hD hspan hK C hU hP la p hp m β hβs
    (fun k => (hval _).1 (hβ k).2) y hφ'
  have hdiff : ∀ k, ∀ d ∈ differentIdeal (𝓞 T.Q.c.F) (𝓞 C.d.c₂.F),
      la.valuation C.d.c₂.F (y k * (d : C.d.c₂.F)) ≤ 1 := fun k =>
    GlobalTheory.T.valuation_mul_le_one_of_trace_approxIdempotent_integral T.Q.c.F C.d.c₂.F la p hp (y k)
      ⟨N, fun b hb => hprim (fun k => Algebra.trace T.Q.c.F C.d.c₂.F ((b : C.d.c₂.F) * y k)) ((hval _).2 (hN b hb)) k⟩
  have hcd := hc T.Q.c.F C.d.c₂.F p la hp hl1 hl2
  refine ⟨m, fun k => (l : C.d.c₂.F) ^ c * y k, fun k => T.phiJ j T.σ₀ (wtA w) (β k), ?_, ?_, ?_⟩
  · exact fun k => GlobalTheory.T.valuation_prime_pow_mul_le_one_of_not_dvd_different l c T.Q.c.F C.d.c₂.F la hl1 hcd (y k) (hdiff k)
  · refine fun k => ⟨β k, ⟨(hβs k).1, (hβs k).2, fun q hq => ?_⟩, rfl⟩
    rw [Set.mem_singleton_iff.1 hq]
    exact (hval _).1 (hβ k).2
  · rw [hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, map_mul, map_pow, map_natCast]

end GlobalTheory.XiIntSteps
