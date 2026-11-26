module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC UpperTheory.V
open UpperTheory.V.W (Plc Lp resP)
open scoped Pointwise

section SlopeTestRemainingChoices

variable {F E Ω : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
  [IsScalarTower F E Ω]

private theorem place_conj {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A v) (t : G F Ω) :
    IsPlaceOver (t⁻¹ • A) v := fun x => by
  have hm : ∀ x, x ∈ t⁻¹ • A ↔ t x ∈ A := fun x => ValuationSubring.mem_inv_pointwise_smul_iff
  have hv : ∀ y, (t⁻¹ • A).valuation y < 1 ↔ A.valuation (t y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', hm, hm, map_inv₀, map_eq_zero_iff _ t.injective]
  rw [hv, AlgEquiv.commutes]
  exact h x

private theorem place_between {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 E), IsPlaceOver A w ∧ w.under (𝓞 F) = v := by
  have hint : ∀ x : 𝓞 E, algebraMap E Ω (x : E) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap E Ω (x : E)) := (x.isIntegral_coe.map (algebraMap E Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 E →+* A := ((algebraMap E Ω).comp (algebraMap (𝓞 E) E)).codRestrict A hint
  let P : Ideal (𝓞 E) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 E, A.valuation (algebraMap E Ω (x : E)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 F) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply F E Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP, HeightOneSpectrum.ext hu.symm⟩

end SlopeTestRemainingChoices

theorem UpperTheory.isSplitAt_of_decomposition_le_restriction_range :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (A : ValuationSubring Ω) (v : Plc (Lp L)), IsPlaceOver A v → Dec (F := Lp L) A ≤ (resP L Ω).range → ∀ w : Plc L, w.under (𝓞 (Lp L)) = v → IsSplitAt w := by
  intro L Ω _ _ _ _ _ _ A v hA hD w hw
  by_contra hs
  have huniq : ∀ u : Plc L, u.under (𝓞 (Lp L)) = v → u = w := fun u hu => by
    by_contra h
    exact hs ⟨u, h, hu.trans hw.symm⟩
  haveI : Normal (Lp L) Ω := IsAlgClosure.normal _ _
  let t : G (Lp L) Ω := (IsCMField.complexConj L).liftNormal Ω
  have ht : ∀ y : L, t (algebraMap L Ω y) = algebraMap L Ω (IsCMField.complexConj L y) := fun y =>
    AlgEquiv.liftNormal_commutes _ Ω y
  obtain ⟨u, hu, hu'⟩ := place_between (E := L) hA
  obtain ⟨u', hu1, hu1'⟩ := place_between (E := L) (place_conj hA t)
  rw [huniq u hu'] at hu
  rw [huniq u' hu1'] at hu1
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := L) hu hu1
  have hg' : resP L Ω g • A = t⁻¹ • A := hg
  have hm : t * resP L Ω g ∈ Dec (F := Lp L) A := by
    show (t * resP L Ω g) • A = A
    rw [mul_smul, hg', smul_inv_smul]
  obtain ⟨k, hk⟩ := (Subgroup.mul_mem_cancel_right _ (MonoidHom.mem_range.2 ⟨g, rfl⟩)).1 (hD hm)
  apply IsCMField.complexConj_ne_one L
  ext y
  apply (algebraMap L Ω).injective
  rw [← ht, ← hk]
  exact k.commutes y
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfUnramifiedOfInertiaDegEqOne
open NumberField IsDedekindDomain GlobalTheory.UnitaryBC

theorem UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → w.asIdeal.inertiaDeg ℤ = 1 → IsSplitAt w := by
  intro E _ _ _ w hun hf
  classical
  set F := maximalRealSubfield E
  set P : Ideal (𝓞 E) := w.asIdeal
  set p : Ideal (𝓞 F) := P.under (𝓞 F)
  have hfin : Module.finrank (𝓞 F) (𝓞 E) = 2 := by
    rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E]
    exact Algebra.IsQuadraticExtension.finrank_eq_two F E
  have he : P.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one P (𝓞 F)
  have hf' : P.inertiaDeg (𝓞 F) = 1 := by
    have h := Ideal.inertiaDeg_tower (R := ℤ) p P
    rw [hf] at h
    exact (Nat.eq_one_of_mul_eq_one_left h.symm)
  by_contra hns
  have hone : ∀ q : p.primesOver (𝓞 E), q.1 = P := by
    intro q
    by_contra hq
    apply hns
    have hq0 : q.1 ≠ ⊥ := by
      intro h0
      have hP0 : p = ⊥ := by
        have := q.2.2
        rw [Ideal.liesOver_iff, h0] at this
        rw [this]
        exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
      apply w.ne_bot
      exact Ideal.eq_bot_of_comap_eq_bot (R := 𝓞 F) hP0
    refine ⟨⟨q.1, q.2.1, hq0⟩, ?_, ?_⟩
    · intro h
      exact hq (congrArg HeightOneSpectrum.asIdeal h)
    · ext1
      change Ideal.under (𝓞 F) q.1 = p
      exact (Ideal.liesOver_iff _ _).mp q.2.2 |>.symm
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 E)
  have hPmem : P ∈ p.primesOver (𝓞 E) := ⟨w.isPrime, ⟨rfl⟩⟩
  have huniq : (Finset.univ : Finset (p.primesOver (𝓞 E))) = {⟨P, hPmem⟩} := by
    ext q
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subtype.ext (hone q)
  rw [huniq, Finset.sum_singleton, he, hf', hfin] at hsum
  omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsUnramifiedAtTotallyRealOfInertiaLeRestrictionR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC UpperTheory.V
open UpperTheory.V.W (Plc Lp resP)

theorem UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω], (∀ (A : ValuationSubring Ω) (v : Plc (Lp L)), IsPlaceOver A v → Ine (F := Lp L) A ≤ (resP L Ω).range) → ∀ w : Plc L, Algebra.IsUnramifiedAt (𝓞 (Lp L)) w.asIdeal := by
  intro L Ω _ _ _ _ _ _ h w
  obtain ⟨A, hA⟩ := exists_valuationSubring_over (Ω := Ω) w
  let v : Plc (Lp L) := ⟨w.asIdeal.comap (algebraMap (𝓞 (Lp L)) (𝓞 L)), inferInstance, by
    exact Ideal.IsMaximal.ne_bot_of_isIntegral_int (Ideal.comap (algebraMap (𝓞 (Lp L)) (𝓞 L)) w.asIdeal)⟩
  have hv : IsPlaceOver A v := by
    intro x
    have h1 := hA (algebraMap (𝓞 (Lp L)) (𝓞 L) x)
    show _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) x ∈ w.asIdeal
    rw [← h1, IsScalarTower.algebraMap_apply (Lp L) L Ω]
    rfl
  have hle := h A v hv
  have hbot : Ideal.inertia Gal(L/(Lp L)) w.asIdeal = ⊥ := by
    rw [← UpperTheory.V.CF.ineAbs (Lp L) L Ω A w hA, eq_bot_iff]
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨τ, rfl⟩ := hle hσ
    rw [Subgroup.mem_bot]
    ext x
    apply (algebraMap L Ω).injective
    rw [AlgEquiv.one_apply]
    show algebraMap L Ω ((AlgEquiv.restrictScalars (Lp L) τ).restrictNormal L x) = _
    rw [AlgEquiv.restrictNormal_commutes]
    exact τ.commutes x
  refine Ideal.ramificationIdx_eq_one_iff.mp ?_
  rw [← (UpperTheory.V.CF.ineCard).1 (Lp L) L w, hbot]
  simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EqOneOfTraceTranslationInvariantSemisimple
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC UpperTheory.V
open UpperTheory.V.W (Plc Lp resP)

theorem UpperTheory.eq_one_of_trace_translation_invariant_semisimple :
    ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (ρ : Γ →* GL (Fin n) k), Formalism.MainNotions.N.IsSSRep ρ → ∀ g : Γ, (∀ h : Γ, (ρ (h * g) : Matrix (Fin n) (Fin n) k).trace = (ρ h : Matrix (Fin n) (Fin n) k).trace) → ρ g = 1 := by
  intro Γ k _ _ _ n ρ hss g htr
  classical
  let σ : Γ →* Module.End k (Fin n → k) :=
    (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toRingEquiv.toMonoidHom.comp
      ((Units.coeHom (Matrix (Fin n) (Fin n) k)).comp ρ)
  have hσ : ∀ h, σ h = Matrix.toLin' (ρ h : Matrix (Fin n) (Fin n) k) := fun h => rfl
  let A : Subalgebra k (Module.End k (Fin n → k)) := Algebra.adjoin k (Set.range σ)
  have hspan : ∀ a ∈ A, a ∈ Submodule.span k (Set.range σ) := by
    intro a ha
    have h1 : a ∈ Subalgebra.toSubmodule A := ha
    rw [Algebra.adjoin_eq_span, ← MonoidHom.coe_mrange, Submonoid.closure_eq] at h1
    exact h1
  have hinv : ∀ W : Submodule k (Fin n → k), Formalism.MainNotions.N.IsInv ρ W →
      ∀ a ∈ A, ∀ v ∈ W, a v ∈ W := by
    intro W hW a ha v hv
    suffices H : ∀ b ∈ Submodule.span k (Set.range σ), b v ∈ W from H a (hspan a ha)
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b' hb' =>
      obtain ⟨h, rfl⟩ := hb'
      rw [hσ, Matrix.toLin'_apply]
      exact hW h v hv
    | zero => simpa using W.zero_mem
    | add b c _ _ hb hc => simpa using W.add_mem hb hc
    | smul c b _ hb => simpa using W.smul_mem c hb
  have hssA : IsSemisimpleModule A (Fin n → k) := by
    refine { exists_isCompl := fun W => ?_ }
    have hW : Formalism.MainNotions.N.IsInv ρ (W.restrictScalars k) := by
      intro h v hv
      have hmem : σ h ∈ A := Algebra.subset_adjoin ⟨h, rfl⟩
      have := W.smul_mem (⟨σ h, hmem⟩ : A) hv
      exact this
    obtain ⟨W', hW'inv, hc⟩ := hss _ hW
    let W'' : Submodule A (Fin n → k) :=
      { carrier := W'
        add_mem' := W'.add_mem
        zero_mem' := W'.zero_mem
        smul_mem' := fun a v hv => hinv W' hW'inv a a.2 v hv }
    refine ⟨W'', ?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro v hv hv'
      exact (Submodule.disjoint_def.mp hc.disjoint) v hv hv'
    · rw [codisjoint_iff, Submodule.eq_top_iff']
      intro v
      have hv : v ∈ W.restrictScalars k ⊔ W' := by rw [hc.sup_eq_top]; trivial
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
      exact Submodule.add_mem_sup hy hz
  let φ : A →ₗ[A] (Fin n → (Fin n → k)) :=
    { toFun := fun a i => (a : Module.End k (Fin n → k)) (Pi.single i 1)
      map_add' := fun a b => by ext i j; simp
      map_smul' := fun a b => by ext i j; rfl }
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply (Pi.basisFun k (Fin n)).ext
    intro i
    rw [Pi.basisFun_apply]
    exact congrFun hab i
  have hssAA : IsSemisimpleModule A A := IsSemisimpleModule.of_injective φ hφ
  have hgA : σ g ∈ A := Algebra.subset_adjoin ⟨g, rfl⟩
  have hxA : σ g - 1 ∈ A := A.sub_mem hgA A.one_mem
  have htrace : ∀ a ∈ A, LinearMap.trace k (Fin n → k) (a * (σ g - 1)) = 0 := by
    intro a ha
    suffices H : ∀ b ∈ Submodule.span k (Set.range σ),
        LinearMap.trace k (Fin n → k) (b * (σ g - 1)) = 0 from H a (hspan a ha)
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b' hb' =>
      obtain ⟨h, rfl⟩ := hb'
      rw [mul_sub, mul_one, ← map_mul, map_sub, hσ, hσ, Matrix.trace_toLin'_eq,
        Matrix.trace_toLin'_eq, htr, sub_self]
    | zero => simp
    | add b c _ _ hb hc => rw [add_mul, map_add (f := _), hb, hc, add_zero]
    | smul c b _ hb => rw [smul_mul_assoc, map_smul, hb, smul_zero]
  let x' : A := ⟨σ g - 1, hxA⟩
  obtain ⟨L', hL⟩ := exists_isCompl (Submodule.span A {x'})
  have h1 : (1 : A) ∈ Submodule.span A {x'} ⊔ L' := by rw [hL.sup_eq_top]; trivial
  obtain ⟨e, he, e', he', hee⟩ := Submodule.mem_sup.mp h1
  have he'eq : e' = 1 - e := by rw [← hee]; abel
  have key : ∀ l ∈ Submodule.span A {x'}, l * e = l := by
    intro l hl
    have h2 : l * e' ∈ L' := L'.smul_mem l he'
    have h5 : l * e' = l - l * e := by rw [he'eq, mul_sub, mul_one]
    have h3 : l * e' ∈ Submodule.span A {x'} := by
      rw [h5]
      exact Submodule.sub_mem _ hl (Submodule.smul_mem _ l he)
    have h4 := (Submodule.disjoint_def.mp hL.disjoint) _ h3 h2
    rw [h5, sub_eq_zero] at h4
    exact h4.symm
  have hidem : e * e = e := key e he
  obtain ⟨y, hy⟩ := Submodule.mem_span_singleton.mp he
  have htr_e : LinearMap.trace k (Fin n → k) (e : Module.End k (Fin n → k)) = 0 := by
    rw [← hy]
    exact htrace _ y.2
  have hI : IsIdempotentElem (e : Module.End k (Fin n → k)) := congrArg Subtype.val hidem
  have he0 : (e : Module.End k (Fin n → k)) = 0 := by
    first
    | exact (LinearMap.IsIdempotentElem.trace_eq_zero_iff hI).mp htr_e
    | exact (IsIdempotentElem.trace_eq_zero_iff hI).mp htr_e
  have he0' : e = 0 := Subtype.ext he0
  have hx0 : x' = 0 := by
    rw [← key x' (Submodule.mem_span_singleton_self x'), he0', mul_zero]
  have hx1 : σ g - 1 = 0 := congrArg Subtype.val hx0
  apply Units.ext
  apply Matrix.toLin'.injective
  rw [Units.val_one, Matrix.toLin'_one, ← hσ]
  exact sub_eq_zero.mp hx1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFixedVectorOfLocalFixedVectors
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFixedVectorInLocallyStableSubspace
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

theorem UpperTheory.exists_fixed_vector_in_locally_stable_subspace :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : Submodule ℂ (UA E n → ℂ)), IsAutRepU σ → ∀ (w : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E n)), K ≤ locU n w → (∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k ∈ K, RU E n k φ = φ) → ∀ W : Submodule ℂ (UA E n → ℂ), W ≤ σ → W ≠ ⊥ → (∀ x ∈ locU n w, ∀ φ ∈ W, RU E n x φ ∈ W) → ∃ φ ∈ W, φ ≠ 0 ∧ ∀ k ∈ K, RU E n k φ = φ := by
  intro E _ _ _ n π hπ w K hK hu W hWπ hW0 hW
  obtain ⟨φ, hφ, hφ0, hφK⟩ := hu
  let Ψ : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  obtain ⟨τ, -, hirr, f, hf0, hfm, hf⟩ := GlobalTheory.DefU.LocAdm.exists_admissible_comp E n Ψ w
  let ρ : Representation ℂ (locU n w) Ψ.V := Ψ.rep.comp (locU n w).subtype
  let F : Representation.IntertwiningMap τ.ρ ρ :=
    ⟨f.codRestrict _ hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  have htop := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) Ψ.V τ.V τ.V Ψ.rep (locU n w).subtype
    τ.ρ τ.ρ Ψ.isIrreducible_rep hirr hirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1
  have hfi : ∀ (i : Representation.IntertwiningMap τ.ρ ρ) g u, i.toLinearMap (τ.ρ g u) = ρ g (i.toLinearMap u) :=
    fun i g u => Representation.IntertwiningMap.isIntertwining _ _ i g u
  let K' : Subgroup (locU n w) := K.comap (locU n w).subtype
  have hfix : ∃ v : τ.V, v ≠ 0 ∧ ∀ k ∈ K', τ.ρ k v = v := by
    by_contra hn
    have key := GlobalTheory.InertHeckeEigen.mem_of_mem_iSup ρ τ.ρ hirr
      (fun i : Representation.IntertwiningMap τ.ρ ρ => i.toLinearMap) hfi (K' : Set (locU n w)) ⊥
      (fun i v hv => by
        have hv' : v = 0 := by
          by_contra h
          exact hn ⟨v, h, hv⟩
        rw [hv', map_zero]
        exact Submodule.zero_mem _)
      (fun z hz _ _ => by rw [(Submodule.mem_bot ℂ).1 hz, map_zero]) ⟨φ, hφ⟩
      (fun k hk => Subtype.ext (hφK k.1 hk)) (by rw [htop]; exact Submodule.mem_top)
    exact hφ0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 key))
  obtain ⟨v, hvW, hv0, hv⟩ := UpperTheory.V.Af.GlobalFixedVectors.sub_fixed τ.ρ hirr ρ
    (by
      rw [eq_top_iff, ← htop]
      exact iSup_le fun i => le_iSup_of_le ⟨i.toLinearMap, hfi i⟩ le_rfl)
    (W.comap π.subtype) (fun g v hv => hW g.1 g.2 v.1 hv)
    (fun e => hW0 ((Submodule.eq_bot_iff W).2 fun x hx => by
      have h : (⟨x, hWπ hx⟩ : π) ∈ W.comap π.subtype := hx
      rw [e] at h
      exact congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h))) K' hfix
  exact ⟨v.1, hvW, fun e => hv0 (Subtype.ext e), fun k hk => congrArg Subtype.val (hv ⟨k, hK hk⟩ hk)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteAdelicUnitaryMemNhdsOneOfTrivialAtPlaces
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

theorem UpperTheory.finiteAdelicUnitary_mem_nhds_one_of_trivial_at_places :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (T : Set (HeightOneSpectrum (𝓞 E))), T.Finite → ∀ U ∈ nhds (1 : finU (E := E) (n := n)), ∃ S : Finset (HeightOneSpectrum (𝓞 E)), ∀ k : finU (E := E) (n := n), (∀ u ∉ T, cLoc u (k : UA E n) ∈ GlobalTheory.LFun.KGL u (n := n)) → (∀ u ∈ S, cLoc u (k : UA E n) = 1) → k ∈ U := by
  classical
  intro E _ _ _ n T hT U hU
  have hι : Topology.IsInducing (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  rw [hι.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  have hV' : finGL E n ⁻¹' V ∈ nhds (1 : GL (Fin n) (Af E)) :=
    GlobalTheory.DefU.LocAdm.continuous_finGL.continuousAt.preimage_mem_nhds (by rw [map_one]; exact hV)
  obtain ⟨S, hS⟩ := UpperTheory.V.Af.GlobalFixedVectors.exists_KAway_subset (M := 1) hV'
  refine ⟨S ∪ hT.toFinset, fun k hk hk1 => hVU ?_⟩
  have hall : ∀ u, cLoc u (k : UA E n) ∈ GlobalTheory.LFun.KGL u (n := n) := fun u => by
    by_cases hu : u ∈ T
    · rw [hk1 u (Finset.mem_union_right _ (hT.mem_toFinset.2 hu))]; exact one_mem _
    · exact hk u hu
  have ent : ∀ (x : UA E n), (∀ u, cLoc u x ∈ GlobalTheory.LFun.KGL u (n := n)) → ∀ a b,
      Matrix.GeneralLinearGroup.map (pFin E) (x : GA E n) a b ∈ UpperTheory.V.Af.Ohat E := fun x hx a b =>
    UpperTheory.V.Af.GlobalFixedVectors.mem_Ohat.2 fun u => by
      obtain ⟨Q, hQ⟩ := hx u
      have e : (cLoc u x).val a b ∈ u.adicCompletionIntegers E := by
        rw [← hQ]; exact (Q.val a b).2
      exact e
  have h1 := ent _ hall
  have hmem : Matrix.GeneralLinearGroup.map (pFin E) ((k : UA E n) : GA E n) ∈
      UpperTheory.V.Af.GlobalFixedVectors.KAway n 1 S := by
    refine UpperTheory.V.Af.GlobalFixedVectors.mem_KAway.2 ⟨UpperTheory.V.Af.mem_KLev.2 ⟨h1, fun a b => ?_, fun a b => ?_⟩, fun w hw => ?_⟩
    · rw [← map_inv]
      exact ent (k : UA E n)⁻¹ (fun u => by rw [map_inv]; exact inv_mem (hall u)) a b
    · refine ⟨_, sub_mem (h1 a b) ?_, by rw [Nat.cast_one, one_mul]⟩
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · exact hk1 w (Finset.mem_union_left _ hw)
  have hk2 : Matrix.GeneralLinearGroup.map (pInf E) ((k : UA E n) : GA E n) = 1 := k.2
  have e : finGL E n (Matrix.GeneralLinearGroup.map (pFin E) ((k : UA E n) : GA E n)) = ((k : UA E n) : GA E n) :=
    ga_ext (by rw [pInf_finGL, hk2]) (by rw [pFin_finGL])
  have := hS hmem
  rwa [Set.mem_preimage, e] at this
end

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

theorem UpperTheory.exists_fixed_vector_of_local_fixed_vectors :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : Submodule ℂ (UA E n → ℂ)), IsAutRepU σ → ∀ K : Subgroup (UA E n), K ≤ finU (E := E) (n := n) → (∀ w, ∀ k ∈ K, GlobalTheory.DefU.LocRet.ret0 w n k ∈ K) → ∀ T : Set (HeightOneSpectrum (𝓞 E)), T.Finite → (∀ k ∈ K, ∀ u ∉ T, cLoc u k ∈ GlobalTheory.LFun.KGL u (n := n)) → (∀ w, ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k ∈ K, k ∈ locU n w → RU E n k φ = φ) → ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k ∈ K, RU E n k φ = φ := by
  classical
  intro E _ _ _ n σ hσ K hKf hKr T hT hKT h
  let P : Finset (HeightOneSpectrum (𝓞 E)) → UA E n → Prop := fun S k =>
    k ∈ K ∧ ∀ w ∈ S, ∀ u : HeightOneSpectrum (𝓞 E),
      u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → cLoc u k = 1
  have hR : ∀ (a b : UA E n) (φ : UA E n → ℂ), RU E n (a * b) φ = RU E n a (RU E n b φ) := fun a b φ => by
    rw [map_mul, Module.End.mul_apply]
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 E)), (∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k, P S k → RU E n k φ = φ) →
      ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k, P ∅ k → RU E n k φ = φ := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      rintro ⟨v, hvσ, hv0, hv⟩
      let W : Submodule ℂ (UA E n → ℂ) := σ ⊓ ⨅ k : {k // P (insert w S) k}, LinearMap.ker (RU E n k.1 - 1)
      have hWm : ∀ x, x ∈ W ↔ x ∈ σ ∧ ∀ k, P (insert w S) k → RU E n k x = x := fun x => by
        simp only [W, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          Module.End.one_apply, sub_eq_zero, Subtype.forall]
      obtain ⟨φ, hφ, hφ0, hφK⟩ := h w
      obtain ⟨x, hxW, hx0, hx⟩ := UpperTheory.exists_fixed_vector_in_locally_stable_subspace E n σ hσ w (K ⊓ locU n w) inf_le_right
        ⟨φ, hφ, hφ0, fun k hk => hφK k hk.1 hk.2⟩ W inf_le_left
        (fun e => hv0 (by
          have := (hWm v).2 ⟨hvσ, hv⟩
          rwa [e, Submodule.mem_bot] at this))
        (fun g hg x hx => (hWm _).2 ⟨hσ.stable g x ((hWm x).1 hx).1, fun k hk => by
          have e : k * g = g * k := by
            refine Subtype.ext (GlobalTheory.DefU.LocRet.ga_ext' ?_ fun u => ?_)
            · simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_inf hg, one_mul, mul_one]
            · by_cases hu : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
              · have h1 : Matrix.GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) k.1 = 1 :=
                  hk.2 w (Finset.mem_insert_self _ _) u hu
                simp only [Subgroup.coe_mul, map_mul, h1, one_mul, mul_one]
              · simp only [Subgroup.coe_mul, map_mul, GlobalTheory.DefU.LocRet.mem_locU_ne hg hu, one_mul, mul_one]
          rw [← hR, e, hR, ((hWm x).1 hx).2 k hk]⟩)
      refine ih ⟨x, ((hWm x).1 hxW).1, hx0, fun k hk => ?_⟩
      have h1 : GlobalTheory.DefU.LocRet.ret0 w n k ∈ K := hKr w k hk.1
      have h2 : P (insert w S) (k * (GlobalTheory.DefU.LocRet.ret0 w n k)⁻¹) := by
        refine ⟨mul_mem hk.1 (inv_mem h1), fun w' hw' u hu => ?_⟩
        by_cases huw : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
        · have h3 : cLoc u (GlobalTheory.DefU.LocRet.ret0 w n k) = cLoc u k := GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq huw k
          rw [map_mul, map_inv, h3, mul_inv_cancel]
        · have h3 : cLoc u (GlobalTheory.DefU.LocRet.ret0 w n k) = 1 := GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_ne huw k
          rcases Finset.mem_insert.1 hw' with rfl | hw'
          · exact absurd hu huw
          · rw [map_mul, map_inv, h3, hk.2 w' hw' u hu, inv_one, mul_one]
      have h3 : RU E n (GlobalTheory.DefU.LocRet.ret0 w n k) x = x := hx _ ⟨h1, GlobalTheory.DefU.LocRet.unitaryAdelicLocalRetractionEnd_mem_localPoints k⟩
      have h4 := ((hWm x).1 hxW).2 _ h2
      rwa [← h3, ← hR, inv_mul_cancel_right, h3] at h4
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff σ).1 hσ.ne_bot
  obtain ⟨S, hS⟩ := UpperTheory.finiteAdelicUnitary_mem_nhds_one_of_trivial_at_places E n T hT _ ((hσ.aut v hv).level.mem_nhds (x := 1) (by simp))
  obtain ⟨x, hx, hx0, hxK⟩ := key S ⟨v, hv, hv0, fun k hk =>
    hS ⟨k, hKf hk.1⟩ (hKT k hk.1) fun u hu => hk.2 u hu u rfl⟩
  exact ⟨x, hx, hx0, fun k hk => hxK k ⟨hk, by simp⟩⟩
end
