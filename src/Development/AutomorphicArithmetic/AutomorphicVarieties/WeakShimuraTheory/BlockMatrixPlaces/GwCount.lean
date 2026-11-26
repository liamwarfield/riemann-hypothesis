module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.GammaOneGammaZeroHomogeneousCocyclesFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.DecZhat

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.SelToZc
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem exists_norm {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (hρ : ContAction ρ)
    (h2 : Function.Surjective fun m : M => m + m) (c : Γ) (hc : ∀ m, ρ c m = -m) (x : H1 ρ) :
    ∃ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) = x ∧ z.1 c = 0 := by
  obtain ⟨z0, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m, hm⟩ := h2 (-(z0.1 c))
  have hB : d0 ρ m ∈ Z1 ρ := coboundaries_le_cocycles ρ hρ (LinearMap.mem_range_self _ m)
  refine ⟨z0 - ⟨d0 ρ m, hB⟩, ?_, ?_⟩
  · rw [Submodule.Quotient.eq, Submodule.mem_comap, sub_sub_cancel_left, map_neg]
    exact Submodule.neg_mem _ ⟨m, rfl⟩
  · show z0.1 c - d0 ρ m c = 0
    rw [amitsur_d0_apply, hc]
    have hm' : m + m = -(z0.1 c) := hm
    calc z0.1 c - (-m - m) = z0.1 c + (m + m) := by abel
      _ = 0 := by rw [hm']; abel

theorem UpperTheory.V.Ws.Bl.selToZc :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ρ : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), ContAction ρ → (Function.Bijective fun m : M => m + m) →
          ∀ c : G ℚ Ω, (∀ m, ρ (toGS Ω _ c) m = -m) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) →
          ∀ v0 : S, ((l : ℕ) : 𝓞 ℚ) ∈ v0.1.asIdeal → ∀ (P : Set M) (K : Subgroup (G ℚ Ω)), (∀ g ∈ K, ∀ m, ρ (toGS Ω _ g) m = m) →
          ∀ L : LocCond ρ (locFam S Av), (∀ v, v ≠ v0 → L v ≤ H1ur (ρ.comp (locFam S Av v)) ((Ine (F := ℚ) (Av v)).subgroupOf (Dec (F := ℚ) (Av v)))) →
          (∀ z : Z1 (ρ.comp (locFam S Av v0)), (Submodule.Quotient.mk z : H1 (ρ.comp (locFam S Av v0))) ∈ L v0 → ∃ y, ∀ h, z.1 h - (ρ (locFam S Av v0 h) y - y) ∈ P) →
          ∃ f : Sel ρ (locFam S Av) (continuous_locFam S Av) L → Zc (fun g m => ρ (toGS Ω _ g) m) c (neSet l K) (Dec (F := ℚ) (Av v0)) P, Function.Injective f := by
  intro Ω _ _ _ l _ R M _ _ _ _ _ S ρ hρ hbij c hcneg Av hAv v0 hlv0 P K hK L hL hP
  have val_top {Ω : Type} [Field Ω] {x : Ω} (h : (⊤ : ValuationSubring Ω).valuation x < 1) : x = 0 := by
    by_contra hx
    have h1 : (⊤ : ValuationSubring Ω).valuation x⁻¹ ≤ 1 :=
      (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
    have h2 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h h1
    rw [← map_mul, mul_inv_cancel₀ hx, map_one] at h2
    exact lt_irrefl _ h2

  have int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
      A.valuation b ≤ 1 := by
    have h : IsIntegral A b := hb.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [A.valuation_le_one_iff, ← hy]
    exact y.2

  have exists_place (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
      (A : ValuationSubring Ω) (hA : A ≠ ⊤) : ∃ v : HeightOneSpectrum (𝓞 K),
        ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ v.asIdeal := by
    have hm : ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A := fun x =>
      (A.valuation_le_one_iff _).1 (int_le A (x.isIntegral_coe.map (algebraMap K Ω).toIntAlgHom))
    let f : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hm
    let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f
    have hP : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ P := fun x =>
      (A.valuation_lt_one_iff (f x)).symm
    refine ⟨⟨P, inferInstance, fun h0 => hA ?_⟩, hP⟩
    rw [eq_top_iff]
    intro x _
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
    have h1 : Algebra.IsAlgebraic ℤ K := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := K)).2 inferInstance
    have h2 : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ K Ω
    obtain ⟨n, hn, hi⟩ := (h2.isAlgebraic x).exists_integral_multiple
    have h3 : ¬ A.valuation (algebraMap K Ω ((n : 𝓞 K) : K)) < 1 := by
      rw [hP, h0, Ideal.mem_bot]
      exact Int.cast_ne_zero.2 hn
    have h4 : A.valuation (n : Ω) = 1 :=
      le_antisymm (int_le A (isIntegral_algebraMap (R := ℤ) (x := n))) (by simpa using h3)
    have h5 := int_le A hi
    rw [zsmul_eq_mul, map_mul, h4, one_mul] at h5
    exact (A.valuation_le_one_iff x).1 h5

  have placeDict : Ine (F := ℚ) (⊤ : ValuationSubring Ω) = ⊥ ∧
      (∀ A : ValuationSubring Ω, A ≠ ⊤ → ∃ v : HeightOneSpectrum (𝓞 ℚ), IsPlaceOver A v) := by
    refine ⟨?_, fun A hA => exists_place ℚ Ω A hA⟩
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    ext x
    have h := hg.2 x ((ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _))
    exact sub_eq_zero.1 (val_top h)
  have hex : ∀ x : H1 ρ, ∃ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) = x ∧ z.1 (toGS Ω _ c) = 0 :=
    fun x => exists_norm ρ hρ hbij.2 (toGS Ω _ c) hcneg x
  have hA : ∀ x : H1 ρ, x ∈ Sel ρ (locFam S Av) (continuous_locFam S Av) L → ∀ z : Z1 ρ,
      (Submodule.Quotient.mk z : H1 ρ) = x → z.1 (toGS Ω _ c) = 0 →
      (fun g => z.1 (toGS Ω _ g)) ∈ Zc (fun g m => ρ (toGS Ω _ g) m) c (neSet l K) (Dec (F := ℚ) (Av v0)) P := by
    intro x hx z hzx hzc
    subst hzx
    have hcoc : ∀ g h, z.1 (g * h) = z.1 g + ρ g (z.1 h) := ((mem_Z1_iff_cocycle _ _).mp z.2).2
    have hz1 : z.1 1 = 0 := by
      have h := hcoc 1 1
      rw [one_mul, map_one, Module.End.one_apply] at h
      simpa using h
    have hmemv : ∀ v, (Submodule.Quotient.mk (restrictCocycles1 ρ (locFam S Av v) (continuous_locFam S Av v) z) :
        H1 (ρ.comp (locFam S Av v))) ∈ L v := fun v => (mem_Sel _ _ _ _ _).mp hx v
    obtain ⟨y, hy⟩ := hP _ (hmemv v0)
    refine ⟨y, ⟨?_, ?_, hzc, ?_, ?_⟩⟩
    · exact ((IsLocallyConstant.iff_continuous _).mpr ((mem_Z1_iff_cocycle _ _).mp z.2).1).comp_continuous
        continuous_quot_mk
    · intro g h
      show z.1 (toGS Ω _ (g * h)) = z.1 (toGS Ω _ g) + ρ (toGS Ω _ g) (z.1 (toGS Ω _ h))
      rw [map_mul]
      exact hcoc _ _
    · rintro g ⟨hgK, A, hAl, hgA⟩
      show z.1 (toGS Ω _ g) = 0
      by_cases hAtop : A = ⊤
      · subst hAtop
        rw [(placeDict).1, Subgroup.mem_bot] at hgA
        rw [hgA, map_one, hz1]
      obtain ⟨v, hAv'⟩ := (placeDict).2 A hAtop
      by_cases hvS : v ∈ S
      · set w : S := ⟨v, hvS⟩
        have hne : w ≠ v0 := by
          intro hw
          apply hAl
          have h := (hAv' (l : 𝓞 ℚ)).mpr (by rw [show v = v0.1 from congrArg Subtype.val hw]; exact hlv0)
          simpa using h
        obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hAv w) hAv'
        rw [← hσ] at hgA
        have hgA' : σ⁻¹ * g * σ ∈ Ine (F := ℚ) (Av w) := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hgA
        have hur := hL w hne (hmemv w)
        rw [H1ur, LinearMap.mem_ker] at hur
        have hur' := (Submodule.Quotient.mk_eq_zero _).mp hur
        rw [Submodule.mem_comap] at hur'
        obtain ⟨m, hm⟩ := hur'
        have hj := congrFun hm ⟨⟨σ⁻¹ * g * σ, Ine_le_Dec _ hgA'⟩, hgA'⟩
        rw [amitsur_d0_apply] at hj
        have hconj : z.1 (toGS Ω _ (σ⁻¹ * g * σ)) = 0 := by
          have hj' : z.1 (toGS Ω _ (σ⁻¹ * g * σ)) = ρ (toGS Ω _ (σ⁻¹ * g * σ)) m - m := hj.symm
          rw [hj']
          rw [map_mul, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
            show ρ (toGS Ω _ g) (ρ (toGS Ω _ σ) m) = ρ (toGS Ω _ σ) m from hK g hgK _,
            ← Module.End.mul_apply, ← map_mul, map_inv, inv_mul_cancel, map_one, Module.End.one_apply, sub_self]
        set a := toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) σ
        set b := toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g
        have hb : ∀ m, ρ b m = m := hK g hgK
        rw [map_mul, map_mul, map_inv] at hconj
        have e1 := hcoc (a⁻¹ * b) a
        have e2 := hcoc a⁻¹ b
        have e3 := hcoc a⁻¹ a
        rw [inv_mul_cancel, hz1] at e3
        rw [map_mul, Module.End.mul_apply, hb, e2, hconj] at e1
        have hinv0 : ρ a⁻¹ (z.1 b) = 0 := by
          have : (0 : M) = ρ a⁻¹ (z.1 b) + (z.1 a⁻¹ + ρ a⁻¹ (z.1 a)) := by rw [e1]; abel
          rw [← e3, add_zero] at this
          exact this.symm
        have : z.1 b = ρ a (ρ a⁻¹ (z.1 b)) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        rw [this, hinv0, map_zero]
      · have hgN : g ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) :=
          Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure
            (Set.mem_iUnion₂.mpr ⟨v, hvS, Set.mem_iUnion₂.mpr ⟨A, hAv', hgA⟩⟩))
        rw [show toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g = 1 from (QuotientGroup.eq_one_iff g).mpr hgN, hz1]
    · intro h hh
      exact hy ⟨h, hh⟩
  choose zc hzc using hex
  refine ⟨fun x => ⟨fun g => (zc x.1).1 (toGS Ω _ g), hA x.1 x.2 (zc x.1) (hzc x.1).1 (hzc x.1).2⟩, ?_⟩
  intro x x' hxx
  have hfun : (fun g => (zc x.1).1 (toGS Ω _ g)) = (fun g => (zc x'.1).1 (toGS Ω _ g)) :=
    congrArg Subtype.val hxx
  have hz : zc x.1 = zc x'.1 := by
    apply Subtype.ext
    funext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) q
    exact congrFun hfun g
  apply Subtype.ext
  rw [← (hzc x.1).1, ← (hzc x'.1).1, hz]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.GwIneq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem card_one_of {R N : Type} [Ring R] [AddCommGroup N] [Module R N] (P : Submodule R N)
    (h : ∀ x ∈ P, x = 0) : Nat.card P = 1 := by
  haveI : Subsingleton P := ⟨fun a b => Subtype.ext ((h a a.2).trans (h b b.2).symm)⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩

theorem UpperTheory.V.Ws.Bl.gwIneq :
    GlobalFiniteness → GreenbergWiles → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), 0 < r → l ≠ 2 → ContainsAbove S l → ContAction ρ →
          ∀ c : G ℚ Ω, IsCC c → (∀ m, ρ (toGS Ω _ c) m = -m) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) →
          ∀ (v0 : S) (s : G ℚ Ω), s ∈ Dec (F := ℚ) (Av v0) → cycZ ℚ Ω l s = 1 → (Function.Bijective fun x => ρ (toGS Ω _ s) x - x) →
          ∀ L : LocCond ρ (locFam S Av), (∀ v, v ≠ v0 → Nat.card (H0 (ρ.comp (locFam S Av v))) ≤ Nat.card (L v)) →
          Nat.card (L v0) ≤ Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) := by
  intro hGF hGW Ω _ _ _ l _ r M _ _ _ _ _ S ρ hr hl2 hS hρ c hc hcneg Av hAv v0 s hsD hsz hsbij L hL
  have hcop : Nat.Coprime 2 (l ^ r) :=
    Nat.Coprime.pow_right r ((Nat.coprime_primes Nat.prime_two (Fact.out)).mpr (Ne.symm hl2))
  have hinv : ∀ m : M, m = -m → m = 0 := by
    intro m hm
    set u := ZMod.unitOfCoprime 2 hcop
    have hu : (u : ZMod (l ^ r)) = 2 := by simp [u]
    have h2 : (2 : ZMod (l ^ r)) • m = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hm]
      exact add_neg_cancel m
    calc m = ((u⁻¹ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) • ((u : ZMod (l ^ r)) • m) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = 0 := by rw [hu, h2, smul_zero]
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := ℚ) (Ω := Ω) (l := l) (r := r) hS
  have hcc : ∀ w : InfinitePlace ℚ, w.IsReal → IsCCAt w c := by
    intro w _
    obtain ⟨j, hj⟩ := hc
    exact ⟨j, hj, Subsingleton.elim _ _⟩
  have key := hGW ℚ Ω l r M S ρ hr hl2 hS hρ μ hμ Av hAv (fun _ => c) hcc L
  have hμs : μ (toGS Ω _ s) = 1 := by
    have h := congrArg (fun f => f s) hμ
    simp only [MonoidHom.comp_apply] at h
    rw [h]
    simp [cycMod, hsz]
  have htw : Nat.card (H0 (twDual μ ρ)) = 1 := by
    refine card_one_of _ (fun φ hφ => ?_)
    have hfix := (mem_riemannRochSpace_iff_regularAt_everywhere _ φ).mp hφ (toGS Ω _ s)
    change (φ : Module.Dual (ZMod (l ^ r)) M) = 0
    apply LinearMap.ext
    intro m
    obtain ⟨x, rfl⟩ := hsbij.2 m
    have hx : φ (ρ (toGS Ω _ s) x) = φ x := by
      have h := congrArg (fun ψ : TDual (ZMod (l ^ r)) M => ψ (ρ (toGS Ω _ s) x)) hfix
      simp only [twDual_apply, hμs, Units.val_one, one_mul] at h
      rw [← h, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have hsub : (φ : Module.Dual (ZMod (l ^ r)) M) (ρ (toGS Ω _ s) x - x) =
        (φ : Module.Dual (ZMod (l ^ r)) M) (ρ (toGS Ω _ s) x) - (φ : Module.Dual (ZMod (l ^ r)) M) x :=
      LinearMap.map_sub _ _ _
    show φ (ρ (toGS Ω _ s) x - x) = 0
    exact hsub.trans (by erw [hx]; exact sub_self _)
  have harch : archH0Card S ρ (fun _ => c) = 1 := by
    have h0 : InfinitePlace.nrComplexPlaces ℚ = 0 := by simp
    unfold archH0Card
    rw [h0, pow_zero, mul_one]
    refine Finset.prod_eq_one (fun w _ => ?_)
    haveI : Subsingleton {m : M // ρ (toGS Ω _ c) m = m} :=
      ⟨fun a b => Subtype.ext (by
        have ha := hinv a.1 (by rw [← hcneg a.1, a.2])
        have hb := hinv b.1 (by rw [← hcneg b.1, b.2])
        rw [ha, hb])⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨⟨0, map_zero _⟩⟩⟩
  have hv0 : Nat.card (H0 (ρ.comp (locFam S Av v0))) = 1 := by
    refine card_one_of _ (fun m hm => ?_)
    have hfix := (mem_riemannRochSpace_iff_regularAt_everywhere _ m).mp hm ⟨s, hsD⟩
    have hfix' : ρ (toGS Ω _ s) m = m := hfix
    apply hsbij.1
    show ρ (toGS Ω _ s) m - m = ρ (toGS Ω _ s) 0 - 0
    rw [hfix', sub_self, map_zero, sub_self]
  classical
  rw [htw, harch, mul_one, mul_one] at key
  obtain ⟨-, hH1, -, -⟩ := hGF ℚ Ω l r M S ρ hr hS hρ
  have hSelpos : 0 < Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L) := Nat.card_pos
  have hH0pos : ∀ v, 0 < Nat.card (H0 (ρ.comp (locFam S Av v))) := fun v => Nat.card_pos
  have hP := Finset.mul_prod_erase Finset.univ (fun v => Nat.card (H0 (ρ.comp (locFam S Av v)))) (Finset.mem_univ v0)
  have hQ := Finset.mul_prod_erase Finset.univ (fun v => Nat.card (L v)) (Finset.mem_univ v0)
  simp only at hP hQ
  rw [hv0, one_mul] at hP
  set P' := ∏ v ∈ Finset.univ.erase v0, Nat.card (H0 (ρ.comp (locFam S Av v)))
  set Q' := ∏ v ∈ Finset.univ.erase v0, Nat.card (L v)
  have hP'pos : 0 < P' := Finset.prod_pos (fun v _ => hH0pos v)
  have hPQ : P' ≤ Q' := Finset.prod_le_prod₀ (fun v _ => Nat.zero_le _)
    (fun v hv => hL v (Finset.ne_of_mem_erase hv))
  rw [← hP, ← hQ] at key
  set a := Nat.card (Sel ρ (locFam S Av) (continuous_locFam S Av) L)
  set b := Nat.card (Sel (twDual μ ρ) (locFam S Av) _ (perpCond μ ρ (locFam S Av) _ L))
  set h0 := Nat.card (H0 ρ)
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with hb | hb
    · rw [hb, zero_mul, zero_mul] at key
      exact absurd key (Nat.mul_pos hSelpos hP'pos).ne'
    · exact hb
  have hh0 : 0 < h0 := Nat.card_pos
  have h1 : Nat.card (L v0) * Q' ≤ a * P' := by
    rw [key]
    calc Nat.card (L v0) * Q' ≤ (b * h0) * (Nat.card (L v0) * Q') :=
          Nat.le_mul_of_pos_left _ (Nat.mul_pos hbpos hh0)
      _ = _ := rfl
  have h2 : Nat.card (L v0) * P' ≤ a * P' :=
    le_trans (Nat.mul_le_mul_left _ hPQ) h1
  exact Nat.le_of_mul_le_mul_right h2 hP'pos
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.UrCard
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

namespace UpperTheory.V.Ws.Bl.UnramifiedCardinality

variable {k D M : Type} [CommRing k] [Group D] [AddCommGroup M] [Module k M]

private def NI (ρ : Representation k D M) (I : Subgroup D) : Submodule k M where
  carrier := {m | ∀ s ∈ I, ρ s m = m}
  zero_mem' := fun s _ => map_zero _
  add_mem' := fun {a b} ha hb s hs => by rw [map_add (f := _), ha s hs, hb s hs]
  smul_mem' c a ha s hs := by rw [map_smul, ha s hs]

private theorem NI_stable (ρ : Representation k D M) (I : Subgroup D) [hI : I.Normal] (g : D) {m : M}
    (hm : m ∈ NI ρ I) : ρ g m ∈ NI ρ I := by
  intro s hs
  have h1 := hm (g⁻¹ * s * g) (by simpa using hI.conj_mem s hs g⁻¹)
  calc ρ s (ρ g m) = ρ g (ρ (g⁻¹ * s * g) m) := by
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        congr 2
        group
    _ = ρ g m := by rw [h1]

private theorem inv_apply (ρ : Representation k D M) (g : D) (m : M) : ρ g⁻¹ (ρ g m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private theorem apply_inv (ρ : Representation k D M) (g : D) (m : M) : ρ g (ρ g⁻¹ m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

variable [TopologicalSpace D] [IsTopologicalGroup D]

private theorem all_of_closed {I : Subgroup D} {σ : D}
    (hd : (I ⊔ Subgroup.zpowers σ).topologicalClosure = ⊤) (H : Subgroup D) (hH : IsClosed (H : Set D))
    (hI : I ≤ H) (hσ : σ ∈ H) (g : D) : g ∈ H := by
  have := Subgroup.topologicalClosure_minimal (I ⊔ Subgroup.zpowers σ)
    (sup_le hI ((Subgroup.zpowers_le).2 hσ)) hH
  rw [hd] at this
  exact this (Subgroup.mem_top g)

private theorem exists_hom {E : Type} [Group E] [Finite E] {I : Subgroup D} {φ : D}
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1) (e : E) :
    ∃ w : D →* E, IsLocallyConstant w ∧ (∀ s ∈ I, w s = 1) ∧ w φ = e := by
  have hn : 0 < orderOf e := orderOf_pos e
  haveI : NeZero (orderOf e) := ⟨hn.ne'⟩
  obtain ⟨d, hdl, hdI, hdφ⟩ := hd (orderOf e) hn
  let f : Multiplicative (ZMod (orderOf e)) →* E :=
    MonoidHom.mk' (fun x => e ^ (Multiplicative.toAdd x).val) (by
      intro a b
      simp only [toAdd_mul, ZMod.val_add, pow_mod_orderOf, pow_add])
  have hf1 : f (Multiplicative.ofAdd 1) = e := by
    show e ^ (1 : ZMod (orderOf e)).val = e
    rw [ZMod.val_one_eq_one_mod, pow_mod_orderOf, pow_one]
  refine ⟨f.comp d, hdl.comp f, fun s hs => by simp [hdI s hs], ?_⟩
  show f (d φ) = e
  rw [hdφ, hf1]

variable [TopologicalSpace M] [DiscreteTopology M]

private theorem exists_cocycle [Finite M] (ρ : Representation k D M) (hρ : ContAction ρ) {I : Subgroup D} [I.Normal] {φ : D}
    (hcl : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1) {x : M} (hx : x ∈ NI ρ I) :
    ∃ z ∈ Z1 ρ, (∀ s ∈ I, z s = 0) ∧ z φ = x := by
  let e : Equiv.Perm (NI ρ I) :=
    { toFun := fun m => ⟨x + ρ φ m, add_mem hx (NI_stable ρ I φ m.2)⟩
      invFun := fun m => ⟨ρ φ⁻¹ (m - x), NI_stable ρ I _ (sub_mem m.2 hx)⟩
      left_inv := fun m => Subtype.ext (by simp only [add_sub_cancel_left, inv_apply])
      right_inv := fun m => Subtype.ext (by simp only [apply_inv, add_sub_cancel]) }
  obtain ⟨w, hw, hwI, hwφ⟩ := exists_hom hd e
  have hc : ∀ m : NI ρ I, Continuous fun g => ((w g m : NI ρ I) : M) := fun m =>
    (hw.comp fun σ : Equiv.Perm (NI ρ I) => ((σ m : NI ρ I) : M)).continuous
  let H : Subgroup D :=
    { carrier := {g | ∀ m m' : NI ρ I, ((w g m : NI ρ I) : M) - (w g m' : NI ρ I) = ρ g ((m : M) - m')}
      mul_mem' := fun {a b} ha hb m m' => by
        rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ha, hb, Module.End.mul_apply]
      one_mem' := fun m m' => by simp
      inv_mem' := fun {a} ha m m' => by
        have h1 := ha (w a⁻¹ m) (w a⁻¹ m')
        rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Equiv.Perm.one_apply, Equiv.Perm.one_apply] at h1
        rw [h1, inv_apply] }
  have hH : ∀ g, g ∈ H := by
    refine all_of_closed hcl H ?_ (fun s hs m m' => ?_) (fun m m' => ?_)
    · change IsClosed {g | ∀ m m' : NI ρ I, ((w g m : NI ρ I) : M) - (w g m' : NI ρ I) = ρ g ((m : M) - m')}
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun m => isClosed_iInter fun m' => isClosed_eq ((hc m).sub (hc m'))
        (Continuous.comp (f := fun g : D => (g, (m : M) - m')) hρ (by fun_prop))
    · rw [hwI s hs, (sub_mem m.2 m'.2 : _ ∈ NI ρ I) s hs]
      rfl
    · rw [hwφ, map_sub]
      change x + ρ φ m - (x + ρ φ m') = _
      abel
  refine ⟨fun g => ((w g 0 : NI ρ I) : M), ⟨hc 0, fun g h => ?_⟩, fun s hs => ?_, ?_⟩
  · have h1 := hH g (w h 0) 0
    rw [Submodule.coe_zero, sub_zero] at h1
    simp only [map_mul, Equiv.Perm.mul_apply]
    rw [← h1]
    abel
  · simp only [hwI s hs]
    rfl
  · simp only [hwφ]
    change x + ρ φ 0 = x
    simp

private theorem eq_zero_of (ρ : Representation k D M) {I : Subgroup D} {φ : D}
    (hcl : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤) {d : D → M} (hd0 : d ∈ Z1 ρ)
    (hI : ∀ s ∈ I, d s = 0) (hφ : d φ = 0) (g : D) : d g = 0 := by
  have d1 : d 1 = 0 := by
    have := hd0.2 1 1
    simpa using this
  let H : Subgroup D :=
    { carrier := {g | d g = 0}
      mul_mem' := fun {a b} ha hb => by
        change d (a * b) = 0
        rw [hd0.2, show d a = 0 from ha, show d b = 0 from hb]
        simp
      one_mem' := d1
      inv_mem' := fun {a} ha => by
        have := hd0.2 a⁻¹ a
        rw [inv_mul_cancel, d1, show d a = 0 from ha] at this
        change d a⁻¹ = 0
        simpa using this.symm }
  exact all_of_closed hcl H (isClosed_eq hd0.1 continuous_const) hI hφ g

private def Z0 (ρ : Representation k D M) (I : Subgroup D) : Submodule k (Z1 ρ) where
  carrier := {z | ∀ s ∈ I, z.1 s = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {a b} ha hb s hs => by
    change a.1 s + b.1 s = 0
    rw [ha s hs, hb s hs, add_zero]
  smul_mem' c a ha s hs := by
    change c • a.1 s = 0
    rw [ha s hs, smul_zero]

private theorem val_mem (ρ : Representation k D M) (I : Subgroup D) [hI : I.Normal] (z : Z0 ρ I) (g : D) :
    z.1.1 g ∈ NI ρ I := by
  intro s hs
  have h1 := z.1.2.2 s g
  have h2 := z.1.2.2 g (g⁻¹ * s * g)
  rw [z.2 s hs, zero_add] at h1
  rw [z.2 (g⁻¹ * s * g) (by simpa using hI.conj_mem s hs g⁻¹), map_zero, add_zero,
    show g * (g⁻¹ * s * g) = s * g by group] at h2
  rw [← h1, h2]

private theorem card_range_ker {k A B : Type} [CommRing k] [AddCommGroup A] [Module k A] [AddCommGroup B]
    [Module k B] (f : A →ₗ[k] B) :
    Nat.card A = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f),
    Nat.card_congr f.quotKerEquivRange.toEquiv]

end UpperTheory.V.Ws.Bl.UnramifiedCardinality

open UpperTheory.V.Ws.Bl.UnramifiedCardinality in
theorem UpperTheory.V.Ws.Bl.urCard :
    ∀ (R D M : Type) [CommRing R] [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R D M), ContAction ρ → ∀ (I : Subgroup D) [I.Normal] (φ : D), (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ →
          (∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) → Nat.card (H1ur ρ I) = Nat.card (H0 ρ) := by
  intro k D M _ _ _ _ _ _ _ _ _ ρ hρ I _ φ hcl hd
  let ev : Z0 ρ I →ₗ[k] NI ρ I :=
    { toFun := fun z => ⟨z.1.1 φ, val_mem ρ I z φ⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : Function.Bijective ev := by
    refine ⟨(injective_iff_map_eq_zero ev).2 fun z hz => ?_, fun x => ?_⟩
    · exact Subtype.ext (Subtype.ext (funext
        (eq_zero_of ρ hcl z.1.2 z.2 (congrArg Subtype.val hz))))
    · obtain ⟨z, hz, hzI, hzφ⟩ := exists_cocycle ρ hρ hcl hd x.2
      exact ⟨⟨⟨z, hz⟩, hzI⟩, Subtype.ext hzφ⟩
  let E := LinearEquiv.ofBijective ev hev
  haveI : Finite (Z0 ρ I) := Finite.of_equiv _ E.symm.toEquiv
  let p : Z0 ρ I →ₗ[k] H1 ρ := (Submodule.mkQ _).comp (Z0 ρ I).subtype
  let δ : NI ρ I →ₗ[k] Z0 ρ I :=
    { toFun := fun m => ⟨⟨d0 ρ m, coboundaries_le_cocycles ρ hρ ⟨m, rfl⟩⟩, fun s hs => sub_eq_zero.2 (m.2 s hs)⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (map_add (d0 ρ) _ _))
      map_smul' := fun c a => Subtype.ext (Subtype.ext (map_smul (d0 ρ) _ _)) }
  have h1 : LinearMap.range p = H1ur ρ I := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨0, fun s => ?_⟩)
      rw [map_zero, sub_zero]
      exact z.2 s s.2
    · intro c hc
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hc)
      refine ⟨⟨z - ⟨d0 ρ m, coboundaries_le_cocycles ρ hρ ⟨m, rfl⟩⟩, fun s hs =>
        sub_eq_zero.2 (show z.1 s = d0 ρ m s from hm ⟨s, hs⟩)⟩, ?_⟩
      refine (Submodule.Quotient.eq _).2 ?_
      rw [Submodule.subtype_apply, sub_sub_cancel_left]
      exact neg_mem ⟨m, rfl⟩
  have h2 : LinearMap.range δ = LinearMap.ker p := by
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨m, rfl⟩
    · intro z hz
      obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hz)
      refine ⟨⟨m, fun s hs => sub_eq_zero.1 ((hm s).symm.trans (z.2 s hs))⟩, ?_⟩
      exact Subtype.ext (Subtype.ext (funext fun g => (hm g).symm))
  have h3 : (LinearMap.ker δ).map (NI ρ I).subtype = H0 ρ := by
    apply le_antisymm
    · rintro _ ⟨m, hm, rfl⟩ g
      exact sub_eq_zero.1 (congrFun (congrArg (fun z : Z0 ρ I => z.1.1) hm) g)
    · intro m hm
      exact ⟨⟨m, fun s _ => hm s⟩, Subtype.ext (Subtype.ext (funext fun g => sub_eq_zero.2 (hm g))), rfl⟩
  have a1 := card_range_ker p
  have a2 := card_range_ker δ
  have a3 : Nat.card (Z0 ρ I) = Nat.card (NI ρ I) := Nat.card_congr E.toEquiv
  have a4 : Nat.card (H0 ρ) = Nat.card (LinearMap.ker δ) := by
    rw [← h3]
    exact (Nat.card_congr (Submodule.equivMapOfInjective _ (NI ρ I).injective_subtype _).toEquiv).symm
  have a5 : 0 < Nat.card (LinearMap.ker p) := Nat.card_pos
  rw [h2, ← a3, a1, mul_comm] at a2
  rw [← h1, a4]
  exact Nat.eq_of_mul_eq_mul_right a5 a2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.PlusCard
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.plusCard :
    LocalFiniteness → LocalEulerChar → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (B : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)) (ρ : Representation (ZMod (l ^ r)) (Dec (F := ℚ) B) M), 0 < r → IsPlaceOver B v → ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → ContAction ρ →
          ∀ P : Submodule (ZMod (l ^ r)) M, (∀ h, ∀ x ∈ P, ρ h x ∈ P) → (∃ s, Function.Bijective fun x => ρ s x - x) →
          ∃ L : Submodule (ZMod (l ^ r)) (H1 ρ), Nat.card P ≤ Nat.card L ∧ ∀ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) ∈ L → ∃ y, ∀ h, z.1 h - (ρ h y - y) ∈ P := by
  intro hFin hEul Ω _ _ _ l _ r M _ _ _ _ _ B v ρ hr hB hl hc P hP hs
  let ρP : Representation (ZMod (l ^ r)) (Dec (F := ℚ) B) P :=
    { toFun := fun h => (ρ h).restrict (fun x hx => hP h x hx)
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro a b
        ext x
        simp }
  have hρP : ∀ h (x : P), ((ρP h x : P) : M) = ρ h x := fun _ _ => rfl
  have hcP : ContAction ρP := by
    have h1 : Continuous fun p : Dec (F := ℚ) B × P => ρ p.1 (p.2 : M) :=
      hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact continuous_induced_rng.2 h1
  obtain ⟨hH0, hH1, hH2, -⟩ := hFin ℚ Ω l r P B ρP v hr hB hcP
  have hE := (hEul ℚ Ω l r P B ρP v hr hB hcP).1 hl
  have hdeg : 0 < locDeg v := by
    unfold locDeg
    exact Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  have hle : Nat.card P ≤ Nat.card (H1 ρP) := by
    rw [hE]
    have a0 : 0 < Nat.card (H0 ρP) := Nat.card_pos
    have a2 : 0 < Nat.card (H2 ρP) := Nat.card_pos
    calc Nat.card P ≤ Nat.card P ^ locDeg v := Nat.le_self_pow hdeg.ne' _
      _ ≤ Nat.card (H0 ρP) * Nat.card (H2 ρP) * Nat.card P ^ locDeg v :=
        Nat.le_mul_of_pos_left _ (Nat.mul_pos a0 a2)
  have hu : Continuous (P.subtype : P → M) := continuous_subtype_val
  have heq : ∀ (g : Dec (F := ℚ) B) (m : P), P.subtype (ρP g m) = ρ g (P.subtype m) := fun _ _ => rfl
  let φ := mapH1 ρP ρ P.subtype hu heq
  obtain ⟨s, hsb⟩ := hs
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    induction w using Submodule.Quotient.induction_on with
    | _ w =>
    rw [Submodule.Quotient.mk_eq_zero]
    have hw' : (φ (Submodule.Quotient.mk w)) = 0 := hw
    simp only [φ, mapH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.coe_subtype] at hw'
    rw [mem_coboundaries1] at hw'
    obtain ⟨m, hm⟩ := hw'
    have hm' : ∀ g, ((w.1 g : P) : M) = ρ g m - m := fun g => hm g
    have hmP : m ∈ P := by
      obtain ⟨q, hq⟩ : ∃ q : P, ρP s q - q = w.1 s := by
        have hinjP : Function.Injective fun q : P => ρP s q - q := by
          intro a b hab
          apply Subtype.ext
          apply hsb.1
          have := congrArg Subtype.val hab
          simpa [hρP] using this
        exact (Finite.injective_iff_surjective.1 hinjP) (w.1 s)
      have h1 : ρ s (q : M) - q = ρ s m - m := by
        have := congrArg Subtype.val hq
        simp only [AddSubgroupClass.coe_sub, hρP] at this
        rw [this, hm' s]
      have := hsb.1 h1
      rw [← this]
      exact q.2
    rw [Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
    refine ⟨⟨m, hmP⟩, fun g => ?_⟩
    apply Subtype.ext
    rw [hm' g]
    rfl
  refine ⟨LinearMap.range φ, ?_, ?_⟩
  · calc Nat.card P ≤ Nat.card (H1 ρP) := hle
      _ = Nat.card (LinearMap.range φ) := Nat.card_congr (LinearEquiv.ofInjective φ hinj).toEquiv
  · intro z hz
    obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hz
    induction w using Submodule.Quotient.induction_on with
    | _ w =>
    simp only [φ, mapH1, Submodule.mapQ_apply] at hw
    rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1] at hw
    obtain ⟨y, hy⟩ := hw
    refine ⟨-y, fun h => ?_⟩
    have h1 := hy h
    have h2 : ((cocycles1MapOfEquivariant ρP ρ P.subtype hu heq w : Z1 ρ) : _ → M) h = (w.1 h : M) := rfl
    simp only [Submodule.coe_sub, Pi.sub_apply, h2] at h1
    have h3 : z.1 h - (ρ h (-y) - -y) = (w.1 h : M) := by
      rw [map_neg]
      rw [sub_eq_iff_eq_add] at h1
      rw [h1]
      abel
    rw [h3]
    exact (w.1 h).2
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.gwCount :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R (G ℚ Ω) M) (r : ℕ), (∀ m : M, (l ^ r) • m = 0) → (∀ m, IsLocallyConstant fun g => ρ g m) →
          ∀ K : Subgroup (G ℚ Ω), K ≤ ρ.ker → (∀ A, Raw.Away S A → Ine (F := ℚ) A ≤ K) → (∀ m, ρ c m = -m) → (Function.Bijective fun m => ρ s m - m) →
          ∀ P : Submodule R M, (∀ h ∈ Dec (F := ℚ) B, ∀ x ∈ P, ρ h x ∈ P) → Nat.card P ≤ Nat.card (Zc (fun g m => ρ g m) c (neSet l K) (Dec (F := ℚ) B) (P : Set M)) := by
  classical
  intro hC Ω _ _ _ l hl S c s B hP R M _ _ _ _ ρ r hr hlc K hK hun hc hs P hPs
  have hfin := zcFin hC.gf S c s B hP R M ρ r hr hlc K hK hun (P : Set M)
  haveI : Finite (Zc (fun g m => ρ g m) c (neSet l K) (Dec (F := ℚ) B) (P : Set M)) := hfin
  obtain ⟨S', Av, v0, hS', hAv, hB, hv0, hNS⟩ := placeSet (l := l) S B hP.prime hP.mem hP.ovl
  subst hB
  have hr1 : ∀ m : M, (l ^ (r + 1)) • m = 0 := fun m => by rw [pow_succ', mul_smul, hr, smul_zero]
  haveI : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  haveI : Module (ZMod (l ^ (r + 1))) M := AddCommGroup.zmodModule hr1
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  have hcl : IsClosed (ρ.ker : Set (G ℚ Ω)) := by
    have e : (ρ.ker : Set (G ℚ Ω)) = ⋂ m : M, (fun g => ρ g m) ⁻¹' {m} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h m => by rw [h]; rfl, fun h => LinearMap.ext h⟩
    rw [e]
    exact isClosed_iInter fun m => ((hlc m).isClopen_fiber m).1
  have hN := hNS ρ.ker inferInstance hcl fun A hA => (hun A hA).trans hK
  let ρ1 : Representation (ZMod (l ^ (r + 1))) (G ℚ Ω) M :=
    { toFun := fun g => (ρ g).toAddMonoidHom.toZModLinearMap (l ^ (r + 1))
      map_one' := LinearMap.ext fun m => show ρ 1 m = m by rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => show ρ (g * h) m = ρ g (ρ h m) by
        rw [map_mul]; rfl }
  let σ : Representation (ZMod (l ^ (r + 1))) (GS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ)))) M :=
    QuotientGroup.lift _ ρ1 fun g hg => LinearMap.ext fun m => show ρ g m = m by
      rw [show ρ g = 1 from hN hg]; rfl
  have hσ : ∀ g m, σ (toGS Ω _ g) m = ρ g m := fun _ _ => rfl
  have hcont : ContAction σ := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (hlc m).continuous
  have hloc : ∀ v, ContAction (σ.comp (locFam S' Av v)) := fun v =>
    Continuous.comp (f := fun p : Dec (F := ℚ) (Av v) × M => (locFam S' Av v p.1, p.2)) hcont
      (((continuous_locFam S' Av v).comp continuous_fst).prodMk continuous_snd)
  let P' : Submodule (ZMod (l ^ (r + 1))) M := AddSubgroup.toZModSubmodule _ P.toAddSubgroup
  obtain ⟨L0, hL0, hL0'⟩ := plusCard hC.loc.lf hC.loc.le (r + 1) M (Av v0) v0.1 (σ.comp (locFam S' Av v0))
    r.succ_pos (hAv v0) hv0 (hloc v0) P' (fun h x hx => hPs h.1 h.2 x hx) ⟨⟨s, hP.dec⟩, hs⟩
  let L : LocCond σ (locFam S' Av) := Function.update
    (fun v => H1ur (σ.comp (locFam S' Av v)) ((Ine (F := ℚ) (Av v)).subgroupOf (Dec (F := ℚ) (Av v)))) v0 L0
  have hLv0 : L v0 = L0 := Function.update_self ..
  have hLv : ∀ v, v ≠ v0 →
      L v = H1ur (σ.comp (locFam S' Av v)) ((Ine (F := ℚ) (Av v)).subgroupOf (Dec (F := ℚ) (Av v))) :=
    fun v hv => Function.update_of_ne hv ..
  have h1 := gwIneq hC.gf hC.gw (r + 1) M S' σ r.succ_pos hP.odd hS' hcont c hP.cc hc Av hAv v0 s hP.dec hP.cyc hs L
    fun v hv => by
      obtain ⟨φ, -, h1, h2⟩ := GC.decZhat ℚ Ω v.1 (Av v) (hAv v)
      rw [hLv v hv, urCard _ _ _ _ (hloc v) _ φ h1 h2]
  have h2 : Function.Bijective fun m : M => m + m := by
    refine Finite.injective_iff_bijective.1 ((injective_iff_map_eq_zero (AddMonoidHom.id M + AddMonoidHom.id M)).2 ?_)
    intro m hm
    have hm2 : 2 • m = 0 := by rw [two_smul]; exact hm
    have hco : Nat.Coprime 2 (l ^ r) :=
      ((Nat.coprime_primes Nat.prime_two hl.out).2 hP.odd.symm).pow_right _
    have := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hm2) (addOrderOf_dvd_of_nsmul_eq_zero (hr m))
    rw [hco.gcd_eq_one, Nat.dvd_one] at this
    exact AddMonoid.addOrderOf_eq_one_iff.1 this
  obtain ⟨f, hf⟩ := selToZc (l := l) _ M S' σ hcont h2 c hc Av hAv v0 hv0 (P : Set M) K
    (fun g hg m => show ρ g m = m by rw [show ρ g = 1 from hK hg]; rfl) L (fun v hv => (hLv v hv).le)
    (fun z hz => hL0' z (hLv0 ▸ hz))
  rw [hLv0] at h1
  exact hL0.trans (h1.trans (Nat.card_le_card_of_injective f hf))
