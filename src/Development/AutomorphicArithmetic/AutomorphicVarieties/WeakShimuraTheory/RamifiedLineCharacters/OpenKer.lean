module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmHom

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.Descend
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.descend :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M) (S : Finset (HeightOneSpectrum (𝓞 F))), ContAction ρ → UnrOut ρ S →
      ∃ ρS : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M, ρS.comp (toGS Ω _) = ρ ∧ ContAction ρS := by
  intro F Ω _ _ _ _ _ R M _ _ _ _ _ _ ρ S hρ hU
  have hclosed : IsClosed (ρ.ker : Set (G F Ω)) := by
    have hset : (ρ.ker : Set (G F Ω)) = ⋂ m : M, {g | ρ g m = m} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h m
        rw [h]
        rfl
      · intro h
        exact LinearMap.ext h
    rw [hset]
    refine isClosed_iInter fun m => ?_
    have hc : Continuous fun g : G F Ω => ρ g m :=
      hρ.comp (continuous_id.prodMk continuous_const)
    exact isClosed_eq hc continuous_const
  have hle : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ ρ.ker := by
    unfold NS
    refine Subgroup.topologicalClosure_minimal _ ?_ hclosed
    refine Subgroup.normalClosure_le_normal ?_
    intro g hg
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hg
    obtain ⟨v, hv, A, hA, hgA⟩ := hg
    exact hU v hv A hA g (mem_Ine.mpr hgA)
  refine ⟨QuotientGroup.lift _ ρ hle, ?_, ?_⟩
  · exact MonoidHom.ext fun g => rfl
  · have h2 := (QuotientGroup.isOpenQuotientMap_mk (N := NS Ω (S : Set (HeightOneSpectrum (𝓞 F)))).prodMap
      (IsOpenQuotientMap.id (X := M))).continuous_comp_iff
      (g := fun p : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) × M => (QuotientGroup.lift _ ρ hle) p.1 p.2)
    exact h2.mp hρ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CocConj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.cocConj :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R (G F Ω) M), ∀ c ∈ Z1 ρ, ∀ (v : HeightOneSpectrum (𝓞 F)) (A A' : ValuationSubring Ω), IsPlaceOver A v → IsPlaceOver A' v →
      ((∃ m, ∀ g ∈ Dec (F := F) A, c g = ρ g m - m) → ∃ m, ∀ g ∈ Dec (F := F) A', c g = ρ g m - m) ∧
      ((∀ g ∈ Ine (F := F) A, ρ g = 1 ∧ c g = 0) → ∀ g ∈ Ine (F := F) A', c g = 0) := by
  intro F Ω _ _ _ _ _ R M _ _ _ _ _ _ ρ c hc v A A' hA hA'
  obtain ⟨-, hco⟩ := hc
  obtain ⟨s, hs⟩ := exists_smul_eq_of_isPlaceOver hA hA'
  have h1 : c 1 = 0 := by simpa using hco 1 1
  have hinv : ρ s (c s⁻¹) = - c s := by
    have h := hco s s⁻¹
    rw [mul_inv_cancel, h1] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  have hconj : ∀ g ∈ Dec (F := F) A', s⁻¹ * g * s ∈ Dec (F := F) A := by
    intro g hg
    rw [mem_Dec] at hg ⊢
    open scoped Pointwise in
    rw [mul_smul, mul_smul, hs, hg, ← hs, inv_smul_smul]
  refine ⟨?_, ?_⟩
  · rintro ⟨m, hm⟩
    refine ⟨ρ s m - c s, fun g hg => ?_⟩
    have hg' := hconj g hg
    have e2 : c (g * s) = c s + ρ s (c (s⁻¹ * g * s)) := by
      rw [← hco]
      congr 1
      group
    have e3 : c g = c (g * s) + ρ (g * s) (c s⁻¹) := by
      rw [← hco]
      congr 1
      group
    have e4 : ρ s (ρ (s⁻¹ * g * s) m) = ρ g (ρ s m) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    rw [e3, e2, map_mul ρ g s, Module.End.mul_apply, hinv, hm _ hg']
    simp only [map_sub, map_neg]
    rw [e4]
    abel
  · intro hI g hg
    rw [← hs] at hg
    obtain ⟨hρ, hc0⟩ := hI _ (GlobalTheory.Cut.ShaBound.conj_mem_Ine' hg)
    have e2 : c (g * s) = c s + ρ s (c (s⁻¹ * g * s)) := by
      rw [← hco]
      congr 1
      group
    have e3 : c g = c (g * s) + ρ (g * s) (c s⁻¹) := by
      rw [← hco]
      congr 1
      group
    have hρg : ρ g = 1 := by
      have hgs : g = s * (s⁻¹ * g * s) * s⁻¹ := by group
      rw [hgs, map_mul, map_mul, hρ, mul_one, ← map_mul, mul_inv_cancel, map_one]
    rw [e3, e2, hc0, map_zero, add_zero, map_mul ρ g s, hρg, one_mul, hinv, add_neg_cancel]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MapRep
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.unrS :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), D.Good → ∀ A : ValuationSubring Ω, Raw.Away D.S A → ∀ g ∈ Ine (F := T.F) A, D.rbar (resQ T.F g) = 1 := by
  intro Ω _ _ _ l _ c D T hG A hA g hg
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hine⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D hG
  have hq : resQ T.F g ∈ Ine (F := ℚ) A := hg
  have hps : ∀ i, D.ps i (resQ T.F g) = 1 := fun i => hine i A hA hq
  have hd : diagRep D.ps (resQ T.F g) = 1 := by
    unfold UpperTheory.V.GradeZeroInterpolatingElement.diagRep
    simp [hps]
    funext i
    have h : D.ps i (AlgEquiv.restrictScalars ℚ g) = 1 := hps i
    rw [h]
    rfl
  unfold UpperTheory.V.GradeZeroInterpolatingElement.Raw.rbar UpperTheory.V.GradeZeroInterpolatingElement.Raw.r0
  ext i j
  rw [mapRep_apply, hd]
  simp [Matrix.one_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.PlacesQ
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.SplitPrimes
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.splitPrimes :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (H : Subgroup (G ℚ Ω)), IsOpen (H : Set (G ℚ Ω)) →
      Set.Infinite {w : ℕ | w.Prime ∧ ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → Dec (F := ℚ) A ≤ H} := by
  intro Ω _ _ _ H hH
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hH H.one_mem
  set U : Subgroup (G ℚ Ω) := N.toOpenSubgroup.toSubgroup with hUdef
  haveI : U.Normal := N.isNormal'
  have hUo : IsOpen (U : Set (G ℚ Ω)) := N.isOpen'
  have hUH : U ≤ H := fun x hx => hN hx
  intro hfin
  set M : ℕ := ∏ q ∈ hfin.toFinset, q with hM
  have hM0 : M ≠ 0 := by
    rw [hM, Finset.prod_ne_zero_iff]
    intro q hq
    exact ((hfin.mem_toFinset.mp hq).1).ne_zero
  obtain ⟨w, A, p, σ, -, hp, hpM, -, hpw, hnorm, -, hpl, hIne, hfr, hσ⟩ :=
    UpperTheory.V.Loc.v00 (F := ℚ) U hUo 1 ∅ M hM0
  have hσU : σ ∈ U := by simpa using hσ
  have hDecU : Dec (F := ℚ) A ≤ U :=
    UpperTheory.V.Kum.decGen ℚ Ω A w σ U hpl (by rw [hnorm]; exact hfr) hUo hIne hσU
  have hAp : A.valuation (p : Ω) < 1 := by
    have := (hpl (p : 𝓞 ℚ)).mpr hpw
    simpa using this
  have hmem : p ∈ {w : ℕ | w.Prime ∧ ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → Dec (F := ℚ) A ≤ H} := by
    refine ⟨hp, fun A' hA' y hy => ?_⟩
    obtain ⟨u, hu, -⟩ := ((UpperTheory.V.Chr.placesQ Ω).2.2) p A' A hp hA' hAp
    have h1 : u⁻¹ * y * u ∈ U := hDecU (hu y hy)
    have h2 : y ∈ U := by
      have := (inferInstance : U.Normal).conj_mem _ h1 u
      simpa [mul_assoc] using this
    exact hUH h2
  exact hpM (hM ▸ Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.mpr hmem))
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem ex_place (K : Type) [Field K] [NumberField K] {w : ℕ} (hw : w.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), (w : 𝓞 K) ∈ v.asIdeal := by
  have hwZ : Prime (w : ℤ) := Nat.prime_iff_prime_int.mp hw
  haveI hPm : (Ideal.span {(w : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hwZ.irreducible
  obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K)
    (Ideal.span {(w : ℤ)}) (by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have hx0 : x = 0 := (algebraMap ℤ (𝓞 K)).injective_int (by rw [hx, map_zero])
      rw [hx0]
      exact Ideal.zero_mem _)
  have hmem : (w : 𝓞 K) ∈ Q := by
    have hc : (w : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (w : ℤ) ∈ Ideal.under ℤ Q
      rw [hQ]
      exact Ideal.mem_span_singleton_self _
    simpa using hc
  refine ⟨⟨Q, hQm.isPrime, ?_⟩, hmem⟩
  intro hbot
  rw [hbot, Ideal.mem_bot] at hmem
  exact hw.ne_zero (by exact_mod_cast hmem)

private theorem prime_eq {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (h1 : (p : 𝓞 K) ∈ v.asIdeal) (h2 : (q : 𝓞 K) ∈ v.asIdeal) : p = q := by
  by_contra hne
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  have hb := Nat.gcd_eq_gcd_ab p q
  rw [hc.gcd_eq_one] at hb
  have hone : (1 : 𝓞 K) ∈ v.asIdeal := by
    have e : (1 : 𝓞 K) = (p : 𝓞 K) * ((Nat.gcdA p q : ℤ) : 𝓞 K) + (q : 𝓞 K) * ((Nat.gcdB p q : ℤ) : 𝓞 K) := by
      have := congrArg (Int.cast : ℤ → 𝓞 K) hb
      push_cast at this
      exact this
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_right _ _ h2)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hone)

theorem UpperTheory.V.Ws.Gys.placesQ :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), D.Good → ∀ U : Subgroup (G T.F Ω), IsOpen (U : Set (G T.F Ω)) →
      Set.Infinite {v : HeightOneSpectrum (𝓞 T.F) | (∃ w : ℕ, w.Prime ∧ T.Splits w ∧ (w : 𝓞 T.F) ∈ v.asIdeal) ∧ ∀ A, IsPlaceOver A v → Dec (F := T.F) A ≤ U} := by
  intro Ω _ _ _ l _ c D T hD U hU
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hr, ho, -⟩ := UpperTheory.V.GradeZeroInterpolatingElement.facts D hD
  have hemb := (UpperTheory.V.Base.galEmbTop ℚ T.F Ω).1
  have hrng := (UpperTheory.V.Base.galEmbTop ℚ T.F Ω).2.1
  have hoe : Topology.IsOpenEmbedding (UpperTheory.V.Base.galEmb ℚ T.F Ω) := by
    refine ⟨hemb, ?_⟩
    rw [← MonoidHom.coe_range, UpperTheory.V.Base.range_galEmb]
    exact hrng
  have hmo : IsOpen ((U.map (resQ T.F) : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := by
    rw [Subgroup.coe_map]
    exact hoe.isOpenMap _ hU
  let H : Subgroup (G ℚ Ω) := U.map (resQ T.F) ⊓ D.rbar.ker ⊓ D.om.ker
  have hHo : IsOpen (H : Set (G ℚ Ω)) := IsOpen.inter (IsOpen.inter hmo hr) ho
  have hinf := Gys.splitPrimes Ω H hHo
  obtain ⟨v0, -⟩ := ex_place T.F Nat.prime_two
  let f : ℕ → HeightOneSpectrum (𝓞 T.F) := fun w => if hw : w.Prime then (ex_place T.F hw).choose else v0
  have hf : ∀ w (hw : w.Prime), (w : 𝓞 T.F) ∈ (f w).asIdeal := by
    intro w hw
    simp only [f, dif_pos hw]
    exact (ex_place T.F hw).choose_spec
  have himg := hinf.image (f := f) (by
    intro a ha b hb hab
    exact prime_eq (f a) ha.1 hb.1 (hf a ha.1) (by rw [hab]; exact hf b hb.1))
  refine himg.mono ?_
  rintro _ ⟨w, ⟨hwp, hwD⟩, rfl⟩
  refine ⟨⟨w, hwp, ?_, hf w hwp⟩, ?_⟩
  · unfold Tower.Splits
    intro A hA g hg
    have hg' := hwD A hA hg
    obtain ⟨hg12, hg3⟩ := Subgroup.mem_inf.mp hg'
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg12
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, hg2⟩, hg3⟩
    obtain ⟨σ, -, rfl⟩ := Subgroup.mem_map.mp hg1
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact σ.commutes ⟨x, hx⟩
  · intro A hA σ hσ
    have hv : A.valuation (w : Ω) < 1 := by
      have h0 := (hA (w : 𝓞 T.F)).mpr (hf w hwp)
      simpa using h0
    have hdec : resQ T.F σ ∈ Dec (F := ℚ) A := by
      rw [mem_Dec] at hσ ⊢
      exact hσ
    have hH := hwD A hv hdec
    obtain ⟨τ, hτ, he⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hH).1).1
    have hτσ : τ = σ := hemb.injective he
    exact hτσ ▸ hτ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.GysCore
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.SelBig
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.GwLower
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CcOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.ccEx :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω], ∃ c : InfinitePlace F → G F Ω, ∀ w, w.IsReal → IsCCAt w (c w) := by
  intro F Ω _ _ _ _ _
  classical
  have key : ∀ w : InfinitePlace F, w.IsReal → ∃ c : G F Ω, IsCCAt w c := by
    intro w hw
    have hφ : ∀ a, (starRingEnd ℂ) (w.embedding a) = w.embedding a := by
      intro a
      have h := ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hw)
      exact RingHom.congr_fun h a
    letI : Algebra F ℂ := w.embedding.toAlgebra
    let e : Ω ≃ₐ[F] algebraicClosure F ℂ := IsAlgClosure.equiv F Ω (algebraicClosure F ℂ)
    let κ : ℂ →ₐ[F] ℂ :=
      { (starRingEnd ℂ) with commutes' := fun a => hφ a }
    let j : Ω →ₐ[F] ℂ := (algebraicClosure F ℂ).val.comp e.toAlgHom
    have hmem : ∀ x : Ω, (κ.comp j) x ∈ (algebraicClosure F ℂ).toSubalgebra := by
      intro x
      show (κ.comp j) x ∈ algebraicClosure F ℂ
      rw [map_mem_algebraicClosure_iff, mem_algebraicClosure_iff]
      exact Algebra.IsAlgebraic.isAlgebraic x
    let f : Ω →ₐ[F] algebraicClosure F ℂ := (κ.comp j).codRestrict _ hmem
    let c0 : Ω →ₐ[F] Ω := e.symm.toAlgHom.comp f
    let c : G F Ω := AlgEquiv.ofBijective c0 (Algebra.IsAlgebraic.algHom_bijective c0)
    refine ⟨c, j.toRingHom, fun x => ?_, ?_⟩
    · show ((e (e.symm (f x)) : algebraicClosure F ℂ) : ℂ) = (starRingEnd ℂ) (j x)
      rw [AlgEquiv.apply_symm_apply]
      rfl
    · have hj : j.toRingHom.comp (algebraMap F Ω) = w.embedding := by
        ext a
        exact j.commutes a
      rw [hj, InfinitePlace.mk_embedding]
  refine ⟨fun w => if hw : w.IsReal then (key w hw).choose else 1, fun w hw => ?_⟩
  simp only [dif_pos hw]
  exact (key w hw).choose_spec
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.gwLower :
    GlobalFiniteness → GreenbergWiles → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M], l ≠ 2 → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), ContainsAbove S l → ContAction ρ →
      ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ L : LocCond ρ (locFam S Av),
        ∏ v : S, Nat.card (L v) ≤ Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) * (Nat.card (TDual (ZMod (l ^ 1)) M) * Nat.card M ^ Module.finrank ℚ F) *
          ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) := by
  classical
  intro hGF hGW F Ω _ _ _ _ _ l _ M _ _ _ _ _ hl S ρ hS hρ Av hA L
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := F) (Ω := Ω) (l := l) (r := 1) (S := S) hS
  obtain ⟨c, hc⟩ := UpperTheory.V.Ws.Gys.ccEx F Ω
  have e := hGW F Ω l 1 M S ρ one_pos hl hS hρ μ hμ Av hA c hc L
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI hfd : Finite (TDual (ZMod (l ^ 1)) M) := DFunLike.finite _
  haveI hf1 : Finite (H1 ρ) := (hGF F Ω l 1 M S ρ one_pos hS hρ).2.1
  have hM : 0 < Nat.card M := Nat.card_pos
  have p1 : 0 < Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) := Nat.card_pos
  have p2 : 0 < Nat.card (H0 (twDual μ ρ)) := Nat.card_pos
  have p3 : 0 < ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) :=
    Finset.prod_pos fun v _ => Nat.card_pos
  have p4 : 0 < archH0Card S ρ c := by
    unfold archH0Card
    refine Nat.mul_pos (Finset.prod_pos fun w _ => ?_) (pow_pos hM _)
    haveI : Nonempty {m : M // ρ (toGS Ω _ (c w)) m = m} := ⟨⟨0, map_zero _⟩⟩
    exact Nat.card_pos
  have b2 : Nat.card (H0 (twDual μ ρ)) ≤ Nat.card (TDual (ZMod (l ^ 1)) M) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  have b4 : archH0Card S ρ c ≤ Nat.card M ^ Module.finrank ℚ F := by
    unfold archH0Card
    have h1 : (∏ w ∈ Finset.univ.filter (fun w : InfinitePlace F => w.IsReal),
        Nat.card {m : M // ρ (toGS Ω _ (c w)) m = m}) ≤ Nat.card M ^ InfinitePlace.nrRealPlaces F := by
      have h2 := Finset.prod_le_pow_card (Finset.univ.filter (fun w : InfinitePlace F => w.IsReal))
        (fun w => Nat.card {m : M // ρ (toGS Ω _ (c w)) m = m}) (Nat.card M)
        (fun w _ => Nat.card_le_card_of_injective _ Subtype.val_injective)
      have h3 : (Finset.univ.filter (fun w : InfinitePlace F => w.IsReal)).card = InfinitePlace.nrRealPlaces F := by
        rw [InfinitePlace.nrRealPlaces, Fintype.card_subtype]
      rwa [h3] at h2
    refine (Nat.mul_le_mul_right _ h1).trans ?_
    rw [← pow_add]
    refine Nat.pow_le_pow_right hM ?_
    have := InfinitePlace.card_add_two_mul_card_eq_rank F
    omega
  have hpos := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos p1 p2) p3) p4
  refine (Nat.le_of_dvd hpos (Dvd.intro_left _ e.symm)).trans ?_
  calc _ = Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) * (Nat.card (H0 (twDual μ ρ)) * archH0Card S ρ c) *
          ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul b2 b4))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.LocHoms
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.CharRep
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.locNe :
    LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → (∀ g ∈ Dec (F := F) A, cycMod F Ω l 1 g = 1) → ∃ f ∈ Z1 (Representation.trivial (ZMod (l ^ 1)) (Dec (F := F) A) (ZMod (l ^ 1))), f ≠ 0 := by
  intro _ hE F Ω _ _ _ _ _ l _ A v hA hl _
  set ρ := Representation.trivial (ZMod (l ^ 1)) (Dec (F := F) A) (ZMod (l ^ 1)) with hρ
  have hcont : ReciprocityTheory.Gal.ContAction ρ := by
    show Continuous fun p : (Dec (F := F) A) × ZMod (l ^ 1) => (ρ p.1) p.2
    simpa [hρ] using continuous_snd
  have hE' := (hE F Ω l 1 (ZMod (l ^ 1)) A ρ v one_pos hA hcont).2 hl
  have h0 : Nat.card ↥(ReciprocityTheory.Gal.H0 ρ) = l := by
    have htop : ReciprocityTheory.Gal.H0 ρ = ⊤ := by
      ext x
      simp [ReciprocityTheory.Gal.H0, hρ]
    rw [htop, Nat.card_congr Submodule.topEquiv.toEquiv, Nat.card_zmod, pow_one]
  by_contra hne
  push_neg at hne
  haveI hz : Subsingleton ↥(ReciprocityTheory.Gal.Z1 ρ) :=
    ⟨fun a b => Subtype.ext ((hne a a.2).trans (hne b b.2).symm)⟩
  haveI hs : Subsingleton (ReciprocityTheory.Gal.H1 ρ) :=
    (Submodule.Quotient.mk_surjective _).subsingleton
  have h1 : Nat.card (ReciprocityTheory.Gal.H1 ρ) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hs, ⟨0⟩⟩
  rw [h1, h0] at hE'
  exact (Fact.out : l.Prime).one_lt.ne' (Nat.eq_one_of_mul_eq_one_right hE'.symm)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem rescale {l : ℕ} [Fact l.Prime] (a : ZMod (l ^ 1)) (ha : a ≠ 0) : ∃ b : ZMod (l ^ 1), b * a = 1 := by
  haveI : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  exact ⟨a⁻¹, inv_mul_cancel₀ ha⟩

theorem UpperTheory.V.Ws.Gys.locHoms :
    LocalTateDuality → LocalEulerChar → UnramifiedOrthogonality → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → (∀ g ∈ Dec (F := F) A, cycMod F Ω l 1 g = 1) →
      ∃ φ₁ ∈ Z1 (Representation.trivial (ZMod (l ^ 1)) (Dec (F := F) A) (ZMod (l ^ 1))), ∃ φ₂ ∈ Z1 (Representation.trivial (ZMod (l ^ 1)) (Dec (F := F) A) (ZMod (l ^ 1))),
        (∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → φ₁ g = 0) ∧ (∃ g, φ₁ g = 1) ∧ ∃ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A ∧ φ₂ g = 1 := by
  intro hT hE hU F Ω _ _ _ _ _ l _ A v hA hl hμ
  obtain ⟨f, hf, hf0⟩ := UpperTheory.V.Ws.Gys.locNe hT hE F Ω l A v hA hl hμ
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let ρ : Representation (ZMod (l ^ 1)) (Dec (F := F) A) (ZMod (l ^ 1)) := Representation.trivial _ _ _
  let χ := (cycMod F Ω l 1).comp (Dec (F := F) A).subtype
  have hχ : ∀ g, χ g = 1 := fun g => hμ g.1 g.2
  have hc : ContAction ρ := continuous_snd
  obtain ⟨hU1, hU2⟩ := hU F Ω l 1 (ZMod (l ^ 1)) A ρ v one_pos hA hl (fun _ _ => rfl) hc
  have hinj := (hT F Ω l 1 (ZMod (l ^ 1)) A ρ v one_pos hA hc).2.2.1.1
  let T : ZMod (l ^ 1) → TDual (ZMod (l ^ 1)) (ZMod (l ^ 1)) := fun t => TDual.mk (LinearMap.mul _ _ t)
  have htriv : ∀ g (m : TDual (ZMod (l ^ 1)) (ZMod (l ^ 1))), twDual χ ρ g m = m := fun g m => by
    apply DFunLike.ext
    intro t
    rw [twDual_apply, hχ, Units.val_one, one_mul]
    rfl
  let y : Z1 (twDual χ ρ) := ⟨fun g => T (f g), (continuous_of_discreteTopology (f := T)).comp hf.1, fun g h => by
    rw [htriv]
    apply DFunLike.ext
    intro m
    change f (g * h) * m = f g * m + f h * m
    rw [hf.2, add_mul]
    rfl⟩
  have hy : ∀ g (m : TDual (ZMod (l ^ 1)) (ZMod (l ^ 1))), y.1 g = twDual χ ρ g m - m → f g = 0 := fun g m h => by
    rw [htriv, sub_self] at h
    have h1 := congrArg (fun φ : TDual (ZMod (l ^ 1)) (ZMod (l ^ 1)) => φ 1) h
    change f g * 1 = 0 at h1
    rwa [mul_one] at h1
  have ha : ∃ φ ∈ Z1 ρ, (∀ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A → φ g = 0) ∧ φ ≠ 0 := by
    by_contra H
    push Not at H
    refine hf0 (H f hf fun g hg => ?_)
    have h := (hU2 (Submodule.Quotient.mk y)).2 fun x hx => by
      induction x using Submodule.Quotient.induction_on with | H x =>
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx)
      have : x = 0 := Subtype.ext (H x.1 x.2 fun g hg => (hm ⟨g, hg⟩).trans (sub_self _))
      rw [this]
      exact map_zero _
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h)
    exact hy g m (hm ⟨g, hg⟩)
  have hb : ∃ φ ∈ Z1 ρ, ∃ g : Dec (F := F) A, g.1 ∈ Ine (F := F) A ∧ φ g ≠ 0 := by
    by_contra H
    push Not at H
    have hyu : (Submodule.Quotient.mk y : H1 (twDual χ ρ)) ∈
        H1ur (twDual χ ρ) ((Ine (F := F) A).subgroupOf (Dec (F := F) A)) := by
      refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨0, fun j => ?_⟩)
      rw [map_zero, sub_zero]
      apply DFunLike.ext
      intro m
      change f j.1 * m = 0
      rw [H f hf j.1 j.2, zero_mul]
    have h0 : (Submodule.Quotient.mk y : H1 (twDual χ ρ)) = 0 := by
      refine hinj ?_
      refine Eq.trans ?_ (map_zero _).symm
      refine LinearMap.ext fun x => ?_
      induction x using Submodule.Quotient.induction_on with | H x =>
      exact (hU1 (Submodule.Quotient.mk x)).1
        ((Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2
          ⟨0, fun j => (H x.1 x.2 j.1 j.2).trans (sub_self _).symm⟩)) _ hyu
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
    exact hf0 (funext fun g => hy g m (hm g))
  obtain ⟨φ₁, h₁, hI, hne⟩ := ha
  obtain ⟨φ₂, h₂, g₂, hg₂, hne₂⟩ := hb
  obtain ⟨g₁, hg₁⟩ := Function.ne_iff.1 hne
  obtain ⟨b₁, e₁⟩ := rescale _ hg₁
  obtain ⟨b₂, e₂⟩ := rescale _ hne₂
  refine ⟨b₁ • φ₁, Submodule.smul_mem _ _ h₁, b₂ • φ₂, Submodule.smul_mem _ _ h₂, fun g hg => ?_, ⟨g₁, e₁⟩, g₂, hg₂, e₂⟩
  rw [Pi.smul_apply, hI g hg, smul_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.RamCard
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.ramCard :
    ∀ (R D M : Type) [CommRing R] [TopologicalSpace R] [DiscreteTopology R] [Group D] [TopologicalSpace D] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R D M) (I : Subgroup D) (m0 : M), (∀ g, ρ g = 1) → m0 ≠ 0 → Finite (H1 ρ) →
      ∀ φ₁ ∈ Z1 (Representation.trivial R D R), ∀ φ₂ ∈ Z1 (Representation.trivial R D R), (∀ g ∈ I, φ₁ g = 0) → (∃ g, φ₁ g = 1) → (∃ g ∈ I, φ₂ g = 1) →
      2 * Nat.card M ≤ Nat.card (ramLine ρ I m0) := by
  rintro R D M _ _ _ _ _ _ _ _ _ _ ρ I m0 hρ hm0 _ φ₁ hφ₁ φ₂ hφ₂ hI1 ⟨g1, hg1⟩ ⟨g2, hg2I, hg2⟩
  obtain ⟨c1, a1⟩ := (mem_Z1_iff_cocycle _ _).1 hφ₁
  obtain ⟨c2, a2⟩ := (mem_Z1_iff_cocycle _ _).1 hφ₂
  let fn : R → M → D → M := fun t m g => φ₁ g • m + (t * φ₂ g) • m0
  have hz : ∀ t m, fn t m ∈ Z1 ρ := by
    intro t m
    rw [mem_Z1_iff_cocycle]
    refine ⟨(continuous_of_discreteTopology (f := fun p : R × R => p.1 • m + (t * p.2) • m0)).comp
      (c1.prodMk c2), ?_⟩
    intro g h
    simp [fn, hρ g, a1 g h, a2 g h, add_smul, mul_add] <;> abel
  let F : Bool × M → ramLine ρ I m0 := fun p =>
    ⟨Submodule.Quotient.mk ⟨fn (if p.1 then 1 else 0) p.2, hz _ _⟩,
      (mem_ramLine ρ I m0 _).2 ⟨⟨fn (if p.1 then 1 else 0) p.2, hz _ _⟩, fun g hg => by
        show fn _ _ g ∈ _
        simp only [fn, hI1 g hg, zero_smul, zero_add]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self m0), rfl⟩⟩
  have hF : Function.Injective F := by
    rintro ⟨b, m⟩ ⟨b', m'⟩ h
    have h1 := congrArg Subtype.val h
    rw [Submodule.Quotient.eq, Submodule.mem_comap, mem_coboundaries1] at h1
    obtain ⟨x, hx⟩ := h1
    have hpt : ∀ g, fn (if b then 1 else 0) m g = fn (if b' then 1 else 0) m' g := by
      intro g
      have h2 := hx g
      rw [hρ g, Module.End.one_apply, sub_self] at h2
      exact sub_eq_zero.1 h2
    have hb : b = b' := by
      have h3 := hpt g2
      simp only [fn, hI1 g2 hg2I, hg2, zero_smul, zero_add, mul_one] at h3
      cases b <;> cases b' <;> simp_all
    subst hb
    have h4 := hpt g1
    simp only [fn, hg1, one_smul] at h4
    rw [add_right_cancel h4]
  have hc := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hc
  exact hc
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.selBig :
    CohomologyHyp → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M], l ≠ 2 → ∀ (S₀ S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation (ZMod (l ^ 1)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), S₀ ⊆ S → ContainsAbove S₀ l → ContAction ρ →
      (∀ v ∈ S, v ∉ S₀ → TrivAt l (ρ.comp (toGS Ω _)) v) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ m0 : M, m0 ≠ 0 →
        2 ^ (S.card - S₀.card) ≤ Nat.card (gysSel S₀ S ρ Av m0) * (Nat.card (TDual (ZMod (l ^ 1)) M) * Nat.card M ^ (Module.finrank ℚ F + S₀.card)) := by
  classical
  intro P F Ω _ _ _ _ _ l _ M _ _ _ _ _ hl S₀ S ρ hSS hS₀ hρ htr Av hA m0 hm0
  have hS : ContainsAbove S l := fun v hv => hSS (hS₀ v hv)
  have e := gwLower P.gf P.gw F Ω l M hl S ρ hS hρ Av hA (gysL S₀ S ρ Av m0)
  have h0 : ∏ v : S, Nat.card (H0 (ρ.comp (locFam S Av v))) ≤ Nat.card M ^ S.card := by
    have := Finset.prod_le_pow_card Finset.univ (fun v : S => Nat.card (H0 (ρ.comp (locFam S Av v)))) (Nat.card M)
      (fun v _ => Nat.card_le_card_of_injective _ Subtype.val_injective)
    rwa [Finset.card_univ, Fintype.card_coe] at this
  have hloc : ∀ v : S, (if v.1 ∈ S₀ then 1 else 2 * Nat.card M) ≤ Nat.card (gysL S₀ S ρ Av m0 v) := by
    intro v
    by_cases hv : v.1 ∈ S₀
    · rw [if_pos hv, show gysL S₀ S ρ Av m0 v = ⊥ from if_pos hv]
      exact Nat.card_pos
    · rw [if_neg hv, show gysL S₀ S ρ Av m0 v = _ from if_neg hv]
      have ht := htr v.1 v.2 hv (Av v) (hA v)
      obtain ⟨φ₁, h1, φ₂, h2, a1, a2, g, a3, a4⟩ := locHoms P.loc.lt P.loc.le P.uo F Ω l (Av v) v.1 (hA v)
        (fun h => hv (hS₀ _ h)) (fun g hg => (ht g hg).2)
      have hc : ContAction (ρ.comp (locFam S Av v)) := hρ.comp ((continuous_locFam S Av v).prodMap continuous_id)
      obtain ⟨-, f1, -, -⟩ := P.loc.lf F Ω l 1 M (Av v) _ v.1 one_pos (hA v) hc
      exact ramCard _ _ M _ _ m0 (fun g => (ht g.1 g.2).1) hm0 f1 φ₁ h1 φ₂ h2 a1 a2 ⟨g, a3, a4⟩
  have h1 : (2 * Nat.card M) ^ (S.card - S₀.card) ≤ ∏ v : S, Nat.card (gysL S₀ S ρ Av m0 v) := by
    refine le_trans (le_of_eq ?_) (Finset.prod_le_prod' fun v _ => hloc v)
    rw [Finset.prod_coe_sort S (fun v => if v ∈ S₀ then 1 else 2 * Nat.card M), Finset.prod_ite, Finset.prod_const_one, one_mul,
      Finset.prod_const, ← Finset.sdiff_eq_filter, Finset.card_sdiff_of_subset hSS]
  have hpos : 0 < Nat.card M ^ (S.card - S₀.card) := pow_pos Nat.card_pos _
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  rw [← mul_pow]
  refine h1.trans (e.trans ((Nat.mul_le_mul_left _ h0).trans (le_of_eq ?_)))
  have hc : Nat.card M ^ S.card = Nat.card M ^ S₀.card * Nat.card M ^ (S.card - S₀.card) := by
    rw [← pow_add, Nat.add_sub_cancel' (Finset.card_le_card hSS)]
  rw [hc, pow_add]
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.ZunrFin
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section

variable {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [DiscreteTopology M]

private theorem coc_one {ρ : Representation R Γ M} {c : Γ → M} (hc : c ∈ Z1 ρ) : c 1 = 0 := by
  have h := hc.2 1 1
  simpa using h

private def killSub (ρ : Representation R Γ M) {c : Γ → M} (hc : c ∈ Z1 ρ) : Subgroup Γ where
  carrier := {g | ρ g = 1 ∧ c g = 0}
  one_mem' := ⟨map_one ρ, coc_one hc⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [map_mul, ha, hb, one_mul], by rw [hc.2, ha', hb', map_zero, add_zero]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : ρ a⁻¹ = 1 := by
      have : ρ (a * a⁻¹) = 1 := by rw [mul_inv_cancel, map_one]
      rwa [map_mul, ha, one_mul] at this
    refine ⟨h1, ?_⟩
    have h := hc.2 a a⁻¹
    rw [mul_inv_cancel, coc_one hc, ha', ha] at h
    simpa using h.symm

private theorem killSub_normal (ρ : Representation R Γ M) {c : Γ → M} (hc : c ∈ Z1 ρ) : (killSub ρ hc).Normal where
  conj_mem := by
    rintro g ⟨hg, hg'⟩ h
    refine ⟨by rw [map_mul, map_mul, hg, mul_one, ← map_mul, mul_inv_cancel, map_one], ?_⟩
    have e := hc.2 h h⁻¹
    rw [mul_inv_cancel, coc_one hc] at e
    rw [hc.2, hc.2, hg', map_zero, add_zero, map_mul, hg, mul_one]
    exact e.symm

private theorem killSub_closed (ρ : Representation R Γ M) (hρ : ContAction ρ) {c : Γ → M} (hc : c ∈ Z1 ρ) :
    IsClosed (killSub ρ hc : Set Γ) := by
  have e : (killSub ρ hc : Set Γ) = (⋂ m : M, {g | ρ g m = m}) ∩ {g | c g = 0} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    exact and_congr_left' LinearMap.ext_iff
  rw [e]
  refine IsClosed.inter (isClosed_iInter fun m => isClosed_eq ?_ continuous_const) (isClosed_eq hc.1 continuous_const)
  exact Continuous.comp (g := fun p : Γ × M => ρ p.1 p.2) hρ (continuous_id.prodMk continuous_const)

private theorem module_finite_z1_padicInt [Finite M] (ρ : Representation R Γ M) [Finite (H1 ρ)] : Finite (Z1 ρ) := by
  haveI : Finite (B1 ρ) := (Set.finite_range (d0 ρ)).to_subtype
  haveI : Finite ((B1 ρ).comap (Z1 ρ).subtype) :=
    Finite.of_injective (fun x => (⟨x.1.1, x.2⟩ : B1 ρ)) fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : B1 ρ => z.1) h))
  haveI : Finite ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup := this
  haveI : Finite (Z1 ρ ⧸ ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup) := ‹Finite (H1 ρ)›
  exact Finite.of_addSubgroup_quotient ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup

end

theorem UpperTheory.V.Ws.Gys.zunrFin :
    GlobalFiniteness → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation (ZMod (l ^ 1)) (G F Ω) M) (S : Finset (HeightOneSpectrum (𝓞 F))), ContainsAbove S l → ContAction ρ → UnrOut ρ S → (Zunr ρ S).Finite := by
  intro hGF F Ω _ _ _ _ _ l _ M _ _ _ _ _ ρ S hS hρ hU
  obtain ⟨ρS, hcomp, hρS⟩ := UpperTheory.V.Ws.Gys.descend F Ω _ M ρ S hρ hU
  obtain ⟨-, f1, -⟩ := hGF F Ω l 1 M S ρS one_pos hS hρS
  haveI := f1
  haveI := module_finite_z1_padicInt ρS
  refine (Set.finite_range fun c : Z1 ρS => c.1 ∘ toGS Ω (S : Set (HeightOneSpectrum (𝓞 F)))).subset ?_
  rintro c ⟨hc, hI⟩
  haveI := killSub_normal ρ hc
  have hle : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ killSub ρ hc := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => ?_) (killSub_closed ρ hρ hc)
    simp only [Set.mem_iUnion] at hg
    obtain ⟨v, hv, A, hA, hg⟩ := hg
    exact ⟨hU v hv A hA g hg, hI v hv A hA g hg⟩
  let cS : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) → M := Quotient.lift c fun a b hab => by
    have h := (hle (QuotientGroup.leftRel_apply.1 hab)).2
    have e := hc.2 a (a⁻¹ * b)
    rw [mul_inv_cancel_left, h, map_zero, add_zero] at e
    exact e.symm
  refine ⟨⟨cS, hc.1.quotient_lift _, fun x y => ?_⟩, rfl⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  have e := hc.2 a b
  rw [← hcomp] at e
  exact e
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.SelMem
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.selMem :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S₀ S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), S₀ ⊆ S →
      (∀ v ∈ S, v ∉ S₀ → TrivAt l (ρ.comp (toGS Ω _)) v) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ (m0 : M) (f : Z1 ρ),
        Submodule.Quotient.mk f ∈ gysSel S₀ S ρ Av m0 →
        (fun g => f.1 (toGS Ω _ g)) ∈ Zunr (ρ.comp (toGS Ω _)) S ∧
        (∀ v ∈ S₀, ∀ A, IsPlaceOver A v → ∃ m, ∀ g ∈ Dec (F := F) A, f.1 (toGS Ω _ g) = ρ (toGS Ω _ g) m - m) ∧
        ∀ v : S, v.1 ∉ S₀ → ∀ g ∈ Ine (F := F) (Av v), f.1 (toGS Ω _ g) ∈ Submodule.span R {m0} := by
  intro F Ω _ _ _ _ _ l _ R M _ _ _ _ _ _ S₀ S ρ hS htriv Av hA m0 f hf
  have hZ : (fun g => f.1 (toGS Ω _ g)) ∈ Z1 (ρ.comp (toGS Ω _) : Representation R (G F Ω) M) :=
    ⟨f.2.1.comp QuotientGroup.continuous_mk, fun a b => by
      have := f.2.2 (toGS Ω _ a) (toGS Ω _ b)
      rw [← map_mul] at this
      exact this⟩
  have hloc := (mem_Sel _ _ _ _ _).1 hf
  refine ⟨⟨hZ, fun v hv A hAv g hg => ?_⟩, fun v hv A hAv => ?_, fun v hv g hg => ?_⟩
  · have h1 : f.1 1 = 0 := by
      have := f.2.2 1 1
      rw [one_mul, map_one] at this
      exact left_eq_add.1 this
    have h2 : toGS Ω (S : Set (HeightOneSpectrum (𝓞 F))) g = 1 := by
      refine (QuotientGroup.eq_one_iff g).2 ?_
      apply Subgroup.le_topologicalClosure
      apply Subgroup.subset_normalClosure
      simp only [Set.mem_iUnion]
      exact ⟨v, hv, A, hAv, hg⟩
    show f.1 (toGS Ω _ g) = 0
    rw [h2, h1]
  · have h := hloc ⟨v, hS hv⟩
    rw [show gysL S₀ S ρ Av m0 ⟨v, hS hv⟩ = ⊥ from if_pos hv, Submodule.mem_bot] at h
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h)
    exact (UpperTheory.V.Ws.Gys.cocConj F Ω R M (ρ.comp (toGS Ω _)) _ hZ v (Av ⟨v, hS hv⟩) A (hA ⟨v, hS hv⟩) hAv).1
      ⟨m, fun g hg => hm ⟨g, hg⟩⟩
  · have h := hloc v
    rw [show gysL S₀ S ρ Av m0 v = ramLine (ρ.comp (locFam S Av v)) ((Ine (F := F) (Av v)).subgroupOf (Dec (F := F) (Av v))) m0
      from if_neg hv, mem_ramLine] at h
    obtain ⟨f', h1, h2⟩ := h
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.eq _).1 h2)
    have hd : g ∈ Dec (F := F) (Av v) := Ine_le_Dec _ hg
    have h3 := hm ⟨g, hd⟩
    have h4 : ρ (toGS Ω _ g) = 1 := (htriv v.1 v.2 hv (Av v) (hA v) g hd).1
    have h5 : f'.1 ⟨g, hd⟩ - f.1 (toGS Ω _ g) = ρ (toGS Ω _ g) m - m := h3
    rw [h4, Module.End.one_apply, sub_self, sub_eq_zero] at h5
    rw [← h5]
    exact h1 ⟨g, hd⟩ hg
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.gysCore :
    CohomologyHyp → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M], l ≠ 2 → ∀ (ρ : Representation (ZMod (l ^ 1)) (G F Ω) M) (S₀ : Finset (HeightOneSpectrum (𝓞 F))) (Q : Set (HeightOneSpectrum (𝓞 F))), ContAction ρ → ContainsAbove S₀ l → UnrOut ρ S₀ →
      Q.Infinite → (∀ v ∈ Q, TrivAt l ρ v) → ∀ m0 : M, m0 ≠ 0 →
        ∃ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∈ S, v ∈ S₀ ∨ v ∈ Q) ∧ ∃ c ∈ Zunr ρ S, (∀ v ∈ S₀, ∀ A, IsPlaceOver A v → ∃ m, ∀ g ∈ Dec (F := F) A, c g = ρ g m - m) ∧
          ∃ g, ρ g = 1 ∧ c g ≠ 0 ∧ c g ∈ Submodule.span (ZMod (l ^ 1)) {m0} := by
  classical
  intro hP F Ω _ _ _ _ _ l _ M _ _ _ _ _ hl ρ S₀ Q hρ hS₀ hu hQ hT m0 hm0
  have hfin : Finite (Zunr ρ S₀) := UpperTheory.V.Ws.Gys.zunrFin hP.gf F Ω l M ρ S₀ hS₀ hρ hu
  obtain ⟨C, hC⟩ : ∃ C, C = Nat.card (TDual (ZMod (l ^ 1)) M) * Nat.card M ^ (Module.finrank ℚ F + S₀.card) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = Nat.card (Zunr ρ S₀) := ⟨_, rfl⟩
  obtain ⟨S₁, hS₁, hcard⟩ := (hQ.diff S₀.finite_toSet).exists_subset_card_eq (N * C)
  have hdisj : Disjoint S₀ S₁ := Finset.disjoint_left.2 fun v h0 h1 => (hS₁ (Finset.mem_coe.2 h1)).2 (Finset.mem_coe.2 h0)
  obtain ⟨S, hS⟩ : ∃ S, S = S₀ ∪ S₁ := ⟨_, rfl⟩
  have hsub : S₀ ⊆ S := hS ▸ Finset.subset_union_left
  have hSQ : ∀ v ∈ S, v ∈ S₀ ∨ v ∈ Q := fun v hv => by
    rw [hS, Finset.mem_union] at hv
    exact hv.imp_right fun h => (hS₁ (Finset.mem_coe.2 h)).1
  have hSc : S.card - S₀.card = N * C := by
    rw [hS, Finset.card_union_of_disjoint hdisj, hcard]; omega
  have huS : UnrOut ρ S := fun v hv => hu v fun h => hv (hsub h)
  obtain ⟨ρS, rfl, hρS⟩ := UpperTheory.V.Ws.Gys.descend F Ω _ M ρ S hρ huS
  have hTS : ∀ v ∈ S, v ∉ S₀ → TrivAt l (ρS.comp (toGS Ω _)) v := fun v hv h0 => hT v ((hSQ v hv).resolve_left h0)
  let Av : S → ValuationSubring Ω := fun v => placeOf Ω v.1
  have hAv : ∀ v, IsPlaceOver (Av v) v.1 := fun v => isPlaceOver_placeOf Ω v.1
  have hbig := UpperTheory.V.Ws.Gys.selBig hP F Ω l M hl S₀ S ρS hsub hS₀ hρS hTS Av hAv m0 hm0
  have hmem := UpperTheory.V.Ws.Gys.selMem F Ω l _ M S₀ S ρS hsub hTS Av hAv m0
  rw [← hC, hSc] at hbig
  refine ⟨S, hSQ, ?_⟩
  by_contra hno
  have hout : ∀ x : gysSel S₀ S ρS Av m0, Submodule.Quotient.mk (Quotient.out x.1) ∈ gysSel S₀ S ρS Av m0 := fun x => by
    have : (Submodule.Quotient.mk (Quotient.out x.1) : H1 ρS) = x.1 := Quotient.out_eq x.1
    rw [this]; exact x.2
  have hz : ∀ x : gysSel S₀ S ρS Av m0, (fun g => (Quotient.out x.1).1 (toGS Ω _ g)) ∈ Zunr (ρS.comp (toGS Ω _)) S₀ := fun x => by
    obtain ⟨h1, h2, h3⟩ := hmem _ (hout x)
    refine ⟨h1.1, fun v hv A hA => ?_⟩
    by_cases hvS : v ∈ S
    · refine (UpperTheory.V.Ws.Gys.cocConj F Ω _ M _ _ h1.1 v (Av ⟨v, hvS⟩) A (hAv ⟨v, hvS⟩) hA).2 fun g hg => ?_
      have hg1 := (hTS v hvS hv _ (hAv ⟨v, hvS⟩) g (Ine_le_Dec _ hg)).1
      refine ⟨hg1, ?_⟩
      by_contra hne
      exact hno ⟨_, h1, h2, g, hg1, hne, h3 ⟨v, hvS⟩ hv g hg⟩
    · exact h1.2 v hvS A hA
  have hinj : Function.Injective fun x : gysSel S₀ S ρS Av m0 => (⟨_, hz x⟩ : Zunr (ρS.comp (toGS Ω _)) S₀) := by
    intro x y hxy
    have h1 : Quotient.out x.1 = Quotient.out y.1 := by
      refine Subtype.ext (funext fun g => ?_)
      obtain ⟨σ, rfl⟩ : ∃ σ, toGS Ω _ σ = g := QuotientGroup.mk_surjective g
      exact congrFun (congrArg Subtype.val hxy) σ
    exact Subtype.ext (Quotient.out_injective h1)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [← hN] at hle
  have h2 : N * C < 2 ^ (N * C) := Nat.lt_two_pow_self
  exact absurd (hbig.trans (Nat.mul_le_mul_right C hle)) (not_le.2 h2)
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem val_nat {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A v) (n : ℕ) :
    A.valuation (n : Ω) < 1 ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  have h1 := h ((n : ℕ) : 𝓞 F)
  have e : algebraMap F Ω (((n : ℕ) : 𝓞 F) : F) = (n : Ω) := by simp
  rw [e] at h1
  exact h1

private theorem fin_over (F : Type) [Field F] [NumberField F] (U : Finset ℕ) (hU : ∀ p ∈ U, p ≠ 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v, v ∈ S ↔ ∃ p ∈ U, (p : 𝓞 F) ∈ v.asIdeal := by
  have h : {v : HeightOneSpectrum (𝓞 F) | ∃ p ∈ U, (p : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h1 : ∀ p ∈ (U : Set ℕ), {v : HeightOneSpectrum (𝓞 F) | (p : 𝓞 F) ∈ v.asIdeal}.Finite := by
      intro p hp
      have h0 : Ideal.span {(p : 𝓞 F)} ≠ ⊥ := by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact_mod_cast hU p hp
      refine (Ideal.finite_factors h0).subset fun v hv => ?_
      exact Ideal.dvd_span_singleton.2 hv
    refine (Set.Finite.biUnion U.finite_toSet h1).subset fun v hv => ?_
    obtain ⟨p, hp, hv⟩ := hv
    exact Set.mem_biUnion hp hv
  exact ⟨h.toFinset, fun v => h.mem_toFinset⟩

private theorem open_cyc (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] :
    IsOpen ((cycMod F Ω l 1).ker : Set (G F Ω)) :=
  (isOpen_discrete {(1 : (ZMod (l ^ 1))ˣ)}).preimage GlobalTheory.Published.PoitouTate.continuous_cycMod

private theorem open_ker {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (h : ContAction ρ) :
    IsOpen ((MonoidHom.ker ρ : Subgroup Γ) : Set Γ) := by
  have e : ((MonoidHom.ker ρ : Subgroup Γ) : Set Γ) = ⋂ m : M, (fun g => ρ g m) ⁻¹' {m} := by
    ext g
    simp [MonoidHom.mem_ker, LinearMap.ext_iff]
  rw [e]
  exact isOpen_iInter_of_finite fun m =>
    (isOpen_discrete _).preimage (Continuous.comp h (continuous_id.prodMk continuous_const))

theorem UpperTheory.V.Ws.Gys.gysT :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), D.Good → ∀ W : Finset ℕ, (∀ w ∈ W, w.Prime ∧ T.Splits w) → (T.fr W).Gys l (T.Next W) := by
  intro hP Ω _ _ _ l hl c D T hD W hW M _ _ _ _ _ ρ hρ hN m0 hm0
  classical
  obtain ⟨S₀, hS₀⟩ := fin_over T.F (D.S ∪ W) fun p hp => by
    rcases Finset.mem_union.1 hp with h | h
    · exact (hD.S_prime p h).ne_zero
    · exact (hW p h).1.ne_zero
  have hl₀ : ∀ v : HeightOneSpectrum (𝓞 T.F), (l : 𝓞 T.F) ∈ v.asIdeal → v ∈ S₀ := fun v hv =>
    (hS₀ v).2 ⟨l, Finset.mem_union_left _ hD.l_mem, hv⟩
  have hunr : UnrOut ρ S₀ := by
    intro v hv A hA g hg
    have haw : Raw.Away (D.S ∪ W) A := fun p hp h => hv ((hS₀ v).2 ⟨p, hp, (val_nat hA p).1 h⟩)
    refine hN g ⟨A, fun p hp => haw p ?_, hg, UpperTheory.V.Ws.Gys.unrS D T hD A (fun p hp => haw p (Finset.mem_union_left _ hp)) g hg⟩
    rcases Finset.mem_insert.1 hp with rfl | h
    · exact Finset.mem_union_left _ hD.l_mem
    · exact Finset.mem_union_right _ h
  have hQ := UpperTheory.V.Ws.Gys.placesQ D T hD (MonoidHom.ker ρ ⊓ (cycMod T.F Ω l 1).ker)
    ((open_ker ρ hρ).inter (open_cyc T.F Ω l))
  obtain ⟨S, hS, z, hz, hloc, hg⟩ := UpperTheory.V.Ws.Gys.gysCore hP T.F Ω l M hD.l_odd ρ S₀ _ hρ hl₀ hunr hQ
    (fun v hv A hA g hg => hv.2 A hA hg) m0 hm0
  have hw : ∀ v ∈ S, v ∉ S₀ → ∃ w : ℕ, w.Prime ∧ T.Splits w ∧ (w : 𝓞 T.F) ∈ v.asIdeal := fun v hv hv' =>
    ((hS v hv).resolve_left hv').1
  choose! wf hwf using hw
  have hnext : T.Next W (T.fr (W ∪ (S \ S₀).image wf)).N := by
    refine ⟨_, Finset.subset_union_left, fun w h => ?_, rfl⟩
    rcases Finset.mem_union.1 h with h | h
    · exact hW w h
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      have := hwf v (Finset.mem_sdiff.1 hv).1 (Finset.mem_sdiff.1 hv).2
      exact ⟨this.1, this.2.1⟩
  refine ⟨_, hnext, z, hz.1, fun g hg => ?_, fun u => ?_, hg⟩
  · have h1 : ρ g = 1 := hN g (hnext.sub hg)
    obtain ⟨A, hA, hg, -⟩ := hg
    obtain ⟨p1, p2, -⟩ := UpperTheory.V.Base.places T.F Ω l A
    by_cases ht : A = ⊤
    · rw [(p2 ht).1, Subgroup.mem_bot] at hg
      subst hg
      have := hz.1.2 1 1
      simpa using this
    obtain ⟨v, hv⟩ := p1 ht
    by_cases hvS : v ∈ S
    · by_cases hv0 : v ∈ S₀
      · obtain ⟨m, hm⟩ := hloc v hv0 A hv
        rw [hm g (Ine_le_Dec A hg), h1]
        simp
      · refine absurd ((val_nat hv _).2 (hwf v hvS hv0).2.2) (hA _ ?_)
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _
          (Finset.mem_image_of_mem _ (Finset.mem_sdiff.2 ⟨hvS, hv0⟩)))
    · exact hz.2 v hvS A hv g hg
  · obtain ⟨p1, p2, -⟩ := UpperTheory.V.Base.places T.F Ω l (T.pl u)
    obtain ⟨v, hv⟩ := p1 fun ht => (p2 ht).2 (T.ovl u)
    exact hloc v (hl₀ v ((val_nat hv l).1 (T.ovl u))) _ hv
