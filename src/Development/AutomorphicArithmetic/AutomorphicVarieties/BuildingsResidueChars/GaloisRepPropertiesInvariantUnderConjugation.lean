module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.IneConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepPropertiesInvariantUnderConjugation
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.S2

private theorem isIrr_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : RepIso r r')
    (hr : IsIrr r) : IsIrr r' := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨h1, -, h3⟩ := hr
  refine ⟨h1, fun _ _ _ => Submodule.mem_top, fun W _ hi => ?_⟩
  have key := h3 (W.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k))) le_top (fun s v hv => by
    have h4 := hi s _ hv
    rw [hg s] at h4
    simpa [Matrix.mulVec_mulVec, Matrix.mul_assoc] using h4)
  have hs : Function.Surjective (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)) := fun v =>
    ⟨((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v, by
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
  have e := Submodule.map_comap_eq_of_surjective hs W
  rcases key with key | key
  · left
    rw [← e, key, Submodule.map_bot]
  · right
    rw [← e, key, Submodule.map_top, LinearMap.range_eq_top.mpr hs]

private theorem ss_of_irrOpen {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k}
    (h : IrrOpen r) : IsSSRep r := by
  intro W hW
  obtain ⟨-, -, h3⟩ := h ⊤ (by simp)
  rcases h3 W le_top (fun s v hv => hW s v hv) with e | e
  · exact ⟨⊤, fun _ _ _ => Submodule.mem_top, e ▸ isCompl_bot_top⟩
  · refine ⟨⊥, fun s v hv => ?_, e ▸ isCompl_top_bot⟩
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, Matrix.mulVec_zero]

private theorem ordAt_iso {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r r' : G F Ω →* GL (Fin n) (Qbar l)} {m : Fin n → ℤ} {ψ : Fin n → G F Ω →* (Qbar l)ˣ} {A : ValuationSubring Ω}
    (h : RepIso r r') (H : OrdAt r m ψ A) : OrdAt r' m ψ A := by
  obtain ⟨κ, h1, h2⟩ := H
  exact ⟨κ, h1.of_iso h, h2⟩

private theorem irrOpen_iso {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k}
    (h : RepIso r r') (H : IrrOpen r) : IrrOpen r' := fun U hU => by
  obtain ⟨g, hg⟩ := h
  have e : RepIso (r.comp U.subtype) (r'.comp U.subtype) := ⟨g, fun s => hg s⟩
  exact isIrr_iso e (H U hU)

private theorem det_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : RepIso r r') :
    Matrix.GeneralLinearGroup.det.comp r' = Matrix.GeneralLinearGroup.det.comp r := by
  obtain ⟨g, hg⟩ := h
  refine MonoidHom.ext fun s => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hg, map_mul, map_mul, map_inv,
    mul_comm _ (Matrix.GeneralLinearGroup.det (r s)), mul_inv_cancel_right]

private theorem resSum_iso {Γ : Type} [Group Γ] {l : ℕ} [Fact l.Prime] {n : ℕ} {r r' : Γ →* GL (Fin n) (Qbar l)}
    {χ : Fin n → Γ →* (Qbar l)ˣ} (h : RepIso r r') (H : ResSum r χ) : ResSum r' χ := by
  obtain ⟨g, hg⟩ := h
  intro s i
  rw [hg, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  exact H s i

private theorem attR_iso {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} {ι : Qbar l ≃+* ℂ} {π} (h : RepIso r r')
    (hs : IsSSRep r') (H : AttR ι r π) : AttR ι r' π := by
  refine ⟨hs, H.2.mono fun w hw => ?_⟩
  obtain ⟨B, b1, b2⟩ := hw
  exact ⟨B, b1, b2.of_iso h⟩

private theorem away_iso {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {r r' : G F Ω →* GL (Fin n) (Qbar l)} {τ : Fin n → G F Ω →* (Qbar l)ˣ}
    (h : RepIso r r') (H : TypeAway r τ) : TypeAway r' τ := fun A hA => (H A hA).of_iso h

theorem UpperTheory.galoisRep_properties_invariant_under_conjugation :
    UpperTheory.V.Sd.S2.MixConj := by
  intro Ω _ _ _ l _ k₀ _ _ ι x k t r r' H h
  have hirr : IrrOpen r' := irrOpen_iso h H.irr
  obtain ⟨π, h2, h3⟩ := H.att
  refine ⟨H.hk, H.ht, H.dvd, continuous_of_iso H.cont h, hirr, ⟨π, attR_iso h (ss_of_irrOpen hirr) h2, h3⟩,
    (det_iso h).trans H.det, resSum_iso h H.res, away_iso h H.away, ?_⟩
  intro A A' hA g hg hy
  rcases H.above A A' hA g hg hy with a | a
  · exact Or.inl ⟨ordAt_iso h a.1, ordAt_iso h a.2⟩
  · exact Or.inr ⟨ordAt_iso h a.1, ordAt_iso h a.2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InducedRepresentationConstituentVanishing
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2
open scoped Pointwise

private theorem cyc_ine (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω) (hA : ¬ A.valuation (l : Ω) < 1) {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) :
    cycZ ℚ Ω l σ = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  show cyclotomicCharacter Ω l σ.toRingEquiv = 1
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ n) := ⟨hN0⟩
  have hspec := cyclotomicCharacter.spec (L := Ω) l σ.toRingEquiv ζ hζ.pow_eq_one
  have hv : ¬ A.valuation ((l ^ n : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, not_lt]
    exact one_le_pow₀ (not_lt.1 hA)
  have h1 : Chr.cls ℚ Ω (l ^ n) σ = 1 := (Chr.clsFacts ℚ Ω (l ^ n)).2.2.2.2 A hv hσ
  have h2 := Chr.cls_spec (l ^ n) σ ζ hζ.pow_eq_one
  rw [h1] at h2
  have h3 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (hspec.symm.trans h2)
  rw [ZMod.val_injective _ h3]
  simp

private theorem ine_iff {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F]
    (A : ValuationSubring Ω) (g : G F Ω) : g ∈ Ine (F := F) A ↔ resQ F g ∈ Ine (F := ℚ) A := Iff.rfl

private theorem mix_one {k : Type} [Field k] (h : (2 : k) ≠ 0) (γ : kˣ) : mix γ 1 1 = (1 : M4 k) := by
  have e : (2 : k)⁻¹ * (1 + 1) = 1 := by rw [one_add_one_eq_two, inv_mul_cancel₀ h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mix, e]

private theorem diag_one {Γ k : Type} [Group Γ] [Field k] {r : Γ →* GL (Fin 2) k} {H : Subgroup Γ} {x : Γ →* kˣ}
    (h : IsDiagOn r H ![1, x]) {s : Γ} (hs : s ∈ H) (hx : x s = 1) : r s = 1 := by
  obtain ⟨g, hg⟩ := h
  have h1 : g * r s * g⁻¹ = 1 := by
    apply Units.ext
    rw [hg s hs]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hx]
  simpa [mul_inv_eq_one] using h1

private theorem sqrt_one {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) {d : (Qbar l)ˣ} (h : d ^ 2 = 1) (hc : Cong d 1) : d = 1 := by
  have h1 : (d : Qbar l) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  rcases sq_eq_one_iff.1 h1 with h2 | h2
  · exact Units.ext h2
  · exfalso
    have h3 : ‖(2 : Qbar l)‖ < 1 := by
      have h4 : ‖(d : Qbar l) - 1‖ < 1 := hc
      rw [h2, show (-1 - 1 : Qbar l) = -2 by ring, norm_neg] at h4
      exact h4
    have h5 : ‖((2 : ℕ) : ℚ_[l])‖ = 1 := by
      rw [Padic.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes Fact.out Nat.prime_two).2 hl
    have h6 : (2 : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((2 : ℕ) : ℚ_[l]) := by rw [map_natCast, Nat.cast_ofNat]
    rw [h6, norm_algebraMap', h5] at h3
    exact lt_irrefl _ h3

theorem UpperTheory.induced_representation_constituent_vanishing :
    UpperTheory.V.Sd.S2.IndKill := by
  intro Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r α β R δ H g hg
  obtain ⟨A, hA, hgI, hrb⟩ := hg
  have hAl : ¬ A.valuation (l : Ω) < 1 := hA l (Finset.mem_insert_self _ _)
  have hsI : resQ T.F g ∈ Ine (F := ℚ) A := (ine_iff _ _ _).1 hgI
  have hψ : D.ψ (resQ T.F g) = 1 :=
    H.hyp.ok.kb A (fun p hp => by rw [Finset.mem_singleton.1 hp]; exact hAl) g hgI hrb
  have hk : resQ T.F g ∈ k₀.fixingSubgroup := (H.hyp.ps g).1 (H.hyp.two.unr A g hgI)
  have hδ2 := H.δ_sq g
  have hδ1 := H.δ_one g
  show (tw (R.comp (resQ T.F)) δ g).val = 1
  rw [tw_val, MonoidHom.comp_apply]
  generalize resQ T.F g = s at *
  have hz : cycZ ℚ Ω l s = 1 := cyc_ine Ω l A hAl hsI
  have hbar : cycBar ℚ Ω l s = 1 := by simp [cycBar, hz]
  have hchi : chiO ℚ Ω l c.O s = 1 := by simp [chiO, hz]
  have hom : D.om s = 1 := (H.chars.om s).2 (by rw [hbar]; simp [Cong])
  have hal : D.al s = D.ξ s := by simp [Raw.al, hchi, hom]
  have hξ : D.ξ s = 1 := by
    refine H.chars.xi s ?_
    have h1 : residue c.O (D.ξ s : c.O) = 1 := by
      have h2 := congrFun (congrFun hrb 2) 2
      rw [← hal]
      simpa [Raw.rbar, Raw.r0, mapRep, GradeZeroInterpolatingElement.diagRep, Raw.ps] using h2
    have h3 : (D.ξ s : c.O) - 1 ∈ maximalIdeal c.O := by
      rw [← residue_eq_zero_iff, map_sub, h1, map_one, sub_self]
    have h4 := (UpperTheory.V.Fr.sc_norm l c _).2.1 h3
    rw [Subalgebra.coe_sub, Subalgebra.coe_one] at h4
    unfold Cong
    rw [Units.val_one]
    exact h4
  have hth : D.th s = 1 := by simp [Raw.th, Raw.Psi, Chr.Psi, hal, hξ, hchi, hψ]
  have hup : up D.ξ s = 1 := by simp [up, hξ]
  have hδ : δ g = 1 := by
    refine sqrt_one H.hyp.good.l_odd ?_ hδ1
    simpa [hbar, hup, H.hyp.φ_in s hk, up, hth, hξ] using hδ2
  obtain ⟨h, rfl⟩ : s ∈ (resQ k₀).range := ⟨AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun x => hk ⟨x.1, x.2⟩, rfl⟩
  have hN : (resQ k₀).range.Normal := Subgroup.normal_of_index_eq_two H.mix.index
  set t₀ := resQ T.F T.g0 with ht₀
  obtain ⟨h', hh'⟩ : t₀⁻¹ * resQ k₀ h * t₀ ∈ (resQ k₀).range := hN.conj_mem' _ ⟨h, rfl⟩ t₀
  have r1 : r h = 1 := diag_one (H.dat.away A hAl) ((ine_iff _ _ _).2 hsI) hup
  obtain ⟨c1, c2, -⟩ := UpperTheory.V.Two.ineConj ℚ Ω t₀
  have hAA : t₀ • (t₀⁻¹ • A) = A := smul_inv_smul _ _
  have r2 : r h' = 1 := by
    refine diag_one (H.dat.away (t₀⁻¹ • A) fun h0 => hAl ?_) ((ine_iff _ _ _).2 ?_) ?_
    · rw [← hAA]; exact (c2 _ l).2 h0
    · rw [hh']; exact c1 _ _ (hAA.symm ▸ hsI)
    · rw [MonoidHom.comp_apply, hh', map_mul, map_mul, hup, mul_one, ← map_mul, inv_mul_cancel, map_one]
  rw [H.mix.on h h' hh', r1, r2, hδ, Units.val_one, Units.val_one, one_smul]
  exact mix_one H.mix.two _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.QuadraticFieldSplitPrimeTwoPlaces
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.S2
open scoped Pointwise

private theorem two_primes {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    {w w' : HeightOneSpectrum (𝓞 K)} (hne : w ≠ w') (hw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal) (hw' : ((p : ℕ) : 𝓞 K) ∈ w'.asIdeal) :
    Ideal.absNorm w.asIdeal = p ∧ Ideal.span {((p : ℕ) : 𝓞 K)} = w.asIdeal * w'.asIdeal := by
  have hco : IsCoprime w.asIdeal w'.asIdeal := by
    rw [Ideal.isCoprime_iff_sup_eq]
    exact w.isMaximal.coprime_of_ne w'.isMaximal fun h => hne (HeightOneSpectrum.ext h)
  have hd : w.asIdeal * w'.asIdeal ∣ Ideal.span {((p : ℕ) : 𝓞 K)} :=
    hco.mul_dvd (Ideal.dvd_span_singleton.2 hw) (Ideal.dvd_span_singleton.2 hw')
  obtain ⟨J, hJ⟩ := hd
  have hn : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2]
  have e := congrArg Ideal.absNorm hJ
  rw [hn, map_mul, map_mul] at e
  have a1 := NumberField.HeightOneSpectrum.one_lt_absNorm w
  have a2 := NumberField.HeightOneSpectrum.one_lt_absNorm w'
  generalize Ideal.absNorm w.asIdeal = a at *
  generalize Ideal.absNorm w'.asIdeal = b at *
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 (show a ∣ p ^ 2 from ⟨b * Ideal.absNorm J, by rw [e, mul_assoc]⟩)
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 (show b ∣ p ^ 2 from ⟨p ^ i * Ideal.absNorm J, by rw [e]; ring⟩)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 (show Ideal.absNorm J ∣ p ^ 2 from ⟨p ^ i * p ^ j, by rw [e]; ring⟩)
  rw [hk, ← pow_add, ← pow_add] at e
  have e2 := Nat.pow_right_injective hp.two_le e
  have i0 : i ≠ 0 := by rintro rfl; simp at a1
  have j0 : j ≠ 0 := by rintro rfl; simp at a2
  have i1 : i = 1 := by omega
  have k0 : k = 0 := by omega
  rw [k0, pow_zero, Ideal.absNorm_eq_one_iff] at hk
  refine ⟨by rw [i1, pow_one], ?_⟩
  rw [hJ, hk, Ideal.mul_top]

private theorem only_two {K : Type} [Field K] [NumberField K] {I : Ideal (𝓞 K)}
    {w w' u : HeightOneSpectrum (𝓞 K)} (h : I = w.asIdeal * w'.asIdeal) (hu : I ≤ u.asIdeal) : u = w ∨ u = w' := by
  rw [h] at hu
  rcases u.isPrime.mul_le.1 hu with h1 | h1
  · exact Or.inl (HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top h1).symm)
  · exact Or.inr (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le u.isPrime.ne_top h1).symm)

theorem UpperTheory.quadratic_field_split_prime_two_places :
    UpperTheory.V.Sd.S2.QuadSplit := by
  intro Ω _ _ _ k₀ _ h2 p hp hs
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure k₀ Ω := ⟨inferInstance, inferInstance⟩
  have key : ∀ A A' : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∀ g : G ℚ Ω, g ∉ k₀.fixingSubgroup →
      (∀ y, g y ∈ A ↔ y ∈ A') → ∃ w w' : Pl k₀, w ≠ w' ∧ ((p : ℕ) : 𝓞 k₀) ∈ w.asIdeal ∧ ((p : ℕ) : 𝓞 k₀) ∈ w'.asIdeal ∧
        IsPlaceOver A w ∧ IsPlaceOver A' w' := by
    intro A A' hA g hg hAA
    have hA' : A'.valuation (p : Ω) < 1 := by
      rw [valuation_lt_one_iff'] at hA ⊢
      rw [← hAA, ← hAA, map_inv₀, map_natCast]
      exact hA
    obtain ⟨a1, a2, a3, -⟩ := places k₀ Ω p A
    obtain ⟨b1, b2, b3, -⟩ := places k₀ Ω p A'
    obtain ⟨v, hv⟩ := a1 fun h => (a2 h).2 hA
    obtain ⟨u, hu⟩ := b1 fun h => (b2 h).2 hA'
    refine ⟨v, u, ?_, (a3 v hv).1 hA, (b3 u hu).1 hA', hv, hu⟩
    rintro rfl
    obtain ⟨h, hh⟩ := exists_smul_eq_of_isPlaceOver hv hu
    have hm : g * galEmb ℚ k₀ Ω h ∈ Dec (F := ℚ) A := by
      have e : g • A' = A := by
        ext y
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← hAA]
        exact iff_of_eq (congrArg (· ∈ A) (g.apply_symm_apply y))
      show (g * galEmb ℚ k₀ Ω h) • A = A
      rw [mul_smul, show galEmb ℚ k₀ Ω h • A = A' from hh, e]
    have hk : galEmb ℚ k₀ Ω h ∈ k₀.fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => h.commutes ⟨x, hx⟩
    exact hg ((Subgroup.mul_mem_cancel_right _ hk).1 (hs A hA hm))
  obtain ⟨g, hg⟩ : ∃ g : G ℚ Ω, g ∉ k₀.fixingSubgroup := by
    by_contra hc
    push Not at hc
    haveI : IsGalois ℚ Ω := {}
    have e : k₀ = ⊥ := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup k₀, (Subgroup.eq_top_iff' _).2 hc, InfiniteGalois.fixedField_bot]
    rw [IntermediateField.finrank_eq_one_iff.2 e] at h2
    omega
  have other : ∀ w : Pl k₀, ((p : ℕ) : 𝓞 k₀) ∈ w.asIdeal → ∃ w' : Pl k₀, w ≠ w' ∧ ((p : ℕ) : 𝓞 k₀) ∈ w'.asIdeal := by
    intro w hw
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨v, u, hne, hv, hu, h1, -⟩ := key A (A.comap g.toRingEquiv.toRingHom)
      (((places k₀ Ω p A).2.2.1 w hA).2 hw) g hg fun _ => Iff.rfl
    have e : v = w := HeightOneSpectrum.ext (Ideal.ext fun x => (h1 x).symm.trans (hA x))
    exact ⟨u, e ▸ hne, hu⟩
  refine ⟨fun w hw => ?_, ?_⟩
  · obtain ⟨w', hne, hw'⟩ := other w hw
    obtain ⟨h1, h3⟩ := two_primes h2 hp hne hw hw'
    refine ⟨h1, fun h => hne ?_⟩
    rw [← Ideal.dvd_span_singleton, h3, sq, mul_dvd_mul_iff_left w.ne_bot, Ideal.dvd_iff_le] at h
    exact HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top h).symm
  · obtain ⟨w, hw⟩ : ∃ w : Pl k₀, ((p : ℕ) : 𝓞 k₀) ∈ w.asIdeal := by
      have hn : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 k₀)}) = p ^ 2 := by
        rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2]
      have ht : Ideal.span {((p : ℕ) : 𝓞 k₀)} ≠ ⊤ := fun h => by
        rw [Ideal.absNorm_eq_one_iff.2 h] at hn
        exact (Nat.one_lt_pow two_ne_zero hp.one_lt).ne hn
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ ht
      have hpM := (Ideal.span_singleton_le_iff_mem _).1 hle
      refine ⟨⟨M, hM.isPrime, fun h => ?_⟩, hpM⟩
      rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at hpM
      exact hp.ne_zero hpM
    obtain ⟨w', hne, hw'⟩ := other w hw
    obtain ⟨-, h3⟩ := two_primes h2 hp hne hw hw'
    refine ⟨w, w', hne, hw, hw', fun A A' hA g hg hAA => ?_⟩
    obtain ⟨v, u, hvu, hv, hu, h1, h4⟩ := key A A' hA g hg hAA
    rcases only_two h3 ((Ideal.span_singleton_le_iff_mem _).2 hv) with rfl | rfl <;>
      rcases only_two h3 ((Ideal.span_singleton_le_iff_mem _).2 hu) with rfl | rfl
    exacts [absurd rfl hvu, Or.inl ⟨h1, h4⟩, Or.inr ⟨h1, h4⟩, absurd rfl hvu]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRingHomToLocalFieldInducingPlace
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Sd

namespace UpperTheory

section

variable {k : Type} [NormedField k] [IsUltrametricDist k] {K : Type} [Field K]

private theorem norm_ringHom_integer_le_one (σ : K →+* k) (x : 𝓞 K) : ‖σ (x : K)‖ ≤ 1 := by
  have hy : IsIntegral ℤ (σ (x : K)) := map_isIntegral_int σ (RingOfIntegers.isIntegral_coe x)
  have h : IsIntegral (NormedField.valuation (K := k)).integer (σ (x : K)) := hy.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := k))).mem_of_integral h
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h2
  exact_mod_cast h2

private def embeddingPrimeIdeal (σ : K →+* k) : Ideal (𝓞 K) where
  carrier := {x | ‖σ (x : K)‖ < 1}
  add_mem' := by
    intro x y hx hy
    change ‖σ (algebraMap (𝓞 K) K (x + y))‖ < 1
    rw [map_add (f := _), map_add (f := _)]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx hy)
  zero_mem' := by
    change ‖σ (algebraMap (𝓞 K) K 0)‖ < 1
    simp
  smul_mem' := by
    intro c x hx
    change ‖σ (algebraMap (𝓞 K) K (c * x))‖ < 1
    rw [map_mul, map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_ringHom_integer_le_one σ c)) hx

private theorem norm_embedding_eq_one_of_not_mem (σ : K →+* k) (x : 𝓞 K) (hx : x ∉ embeddingPrimeIdeal σ) :
    ‖σ (algebraMap (𝓞 K) K x)‖ = 1 :=
  le_antisymm (norm_ringHom_integer_le_one σ x) (not_lt.1 hx)

private theorem embedding_ideal_prime (σ : K →+* k) : (embeddingPrimeIdeal σ).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : ‖σ (algebraMap (𝓞 K) K 1)‖ < 1 := (Ideal.eq_top_iff_one _).1 h
    simp at h1
  · intro x y hxy
    by_contra hc
    push Not at hc
    change ‖σ (algebraMap (𝓞 K) K (x * y))‖ < 1 at hxy
    rw [map_mul, map_mul, norm_mul, norm_embedding_eq_one_of_not_mem σ x hc.1, norm_embedding_eq_one_of_not_mem σ y hc.2, one_mul] at hxy
    exact lt_irrefl _ hxy

private theorem exists_embedding_prime_above [NumberField K] [CharZero k] [IsAlgClosed k] {l : ℕ} (hp : l.Prime) (hk : ‖(l : k)‖ < 1)
    (w : HeightOneSpectrum (𝓞 K)) (hl : (l : 𝓞 K) ∈ w.asIdeal) :
    ∃ σ : K →+* k, embeddingPrimeIdeal σ = w.asIdeal := by
  classical
  by_contra hne
  push Not at hne
  have σ0 : K →ₐ[ℚ] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hnot : ¬ ((w.asIdeal : Set (𝓞 K)) ⊆ ⋃ σ ∈ ((Finset.univ : Finset (K →ₐ[ℚ] k)) : Set (K →ₐ[ℚ] k)),
      (embeddingPrimeIdeal (σ : K →+* k) : Set (𝓞 K))) := by
    rw [Ideal.subset_union_prime σ0 σ0 (fun σ _ _ _ => embedding_ideal_prime _)]
    rintro ⟨σ, -, hle⟩
    exact hne σ (((w.isPrime.isMaximal w.ne_bot).eq_of_le (embedding_ideal_prime _).ne_top hle).symm)
  obtain ⟨a, haw, ha⟩ := Set.not_subset.1 hnot
  have h1 : ∀ σ : K →ₐ[ℚ] k, ‖σ (a : K)‖ = 1 := by
    intro σ
    refine norm_embedding_eq_one_of_not_mem (σ : K →+* k) a fun h => ha ?_
    simp only [Set.mem_iUnion]
    exact ⟨σ, by simp, h⟩
  have hprod : ‖algebraMap ℚ k (Algebra.norm ℚ (a : K))‖ = 1 := by
    rw [Algebra.norm_eq_prod_embeddings, norm_prod]
    exact Finset.prod_eq_one (fun σ _ => h1 σ)
  have hmem : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : 𝓞 K) ∈ w.asIdeal :=
    (Ideal.span_le.2 (Set.singleton_subset_iff.2 haw)) (Ideal.absNorm_mem _)
  have hdvd : l ∣ Ideal.absNorm (Ideal.span {a}) := by
    by_contra hnd
    have hc : IsCoprime (l : 𝓞 K) ((Ideal.absNorm (Ideal.span {a}) : ℕ) : 𝓞 K) :=
      Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
    obtain ⟨u, v, huv⟩ := hc
    refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← huv]
    exact add_mem (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hmem)
  have hn : ‖((Ideal.absNorm (Ideal.span {a}) : ℕ) : k)‖ = 1 := by
    rw [Ideal.absNorm_span_singleton, ← hprod, ← Algebra.coe_norm_int, eq_ratCast, Rat.cast_intCast,
      Nat.cast_natAbs]
    rcases abs_choice (Algebra.norm ℤ a) with h | h
    · rw [h]
    · rw [h, Int.cast_neg, norm_neg]
  obtain ⟨m, hm⟩ := hdvd
  rw [hm, Nat.cast_mul, norm_mul] at hn
  have hk1 : ‖(m : k)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ m
  have h2 : ‖(l : k)‖ * ‖(m : k)‖ ≤ ‖(l : k)‖ * 1 := mul_le_mul_of_nonneg_left hk1 (norm_nonneg _)
  linarith

end

theorem exists_ringHom_to_localField_inducing_place : UpperTheory.V.Sd.S2.EmbEx := by
  intro F _ _ _ l hl ι
  refine ⟨fun w hw => ?_, fun w w' τ τ' h h' e => ?_⟩
  · have hk : ‖(l : Qbar l)‖ < 1 := by
      have : (l : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := (map_natCast _ l).symm
      rw [this, norm_algebraMap']
      exact Padic.norm_p_lt_one
    obtain ⟨σ, hσ⟩ := exists_embedding_prime_above hl.out hk w hw
    exact ⟨σ, fun x => by rw [← hσ]; rfl⟩
  · have e2 : ι.toRingHom.comp τ = ι.toRingHom.comp τ' := by
      rcases InfinitePlace.mk_eq_iff.1 e with e | e
      · exact e
      · rw [← e]
        exact (ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal _)).symm
    have e3 : τ = τ' := RingHom.ext fun x => ι.injective (RingHom.congr_fun e2 x)
    subst e3
    exact HeightOneSpectrum.ext (Ideal.ext fun x => (h x).trans (h' x).symm)

end UpperTheory
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusDualityComplexConj
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol
open scoped Matrix

private theorem eig_dual {K : Type} [Field K] (φ : K →+* ℂ) {n : ℕ} (M M' P : GL (Fin n) K) (t : K)
    (hP : (M : Matrix (Fin n) (Fin n) K)ᵀ * (P : Matrix (Fin n) (Fin n) K) * (M' : Matrix (Fin n) (Fin n) K) =
      t • (P : Matrix (Fin n) (Fin n) K)) (S S' : Multiset ℂ)
    (h : (M : Matrix (Fin n) (Fin n) K).charpoly.map φ = (S.map fun b => X - C b).prod)
    (h' : (M' : Matrix (Fin n) (Fin n) K).charpoly.map φ = (S'.map fun b => X - C b).prod) :
    S = S'.map fun a => φ t * a⁻¹ := by
  have h0 : (M : Matrix (Fin n) (Fin n) K)ᵀ = (P : Matrix (Fin n) (Fin n) K) *
      (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul, ← hP, Units.mul_inv_cancel_right, Units.mul_inv_cancel_right]
  have h1 : (M : Matrix (Fin n) (Fin n) K).charpoly =
      (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).charpoly := by
    rw [← Matrix.charpoly_transpose, h0, Matrix.coe_units_inv P, Matrix.charpoly_units_conj]
  rw [← Matrix.charpoly_map] at h'
  have h3 := GlobalTheory.charpoly_smul_inv_of_charpoly_eq_prod n (Matrix.GeneralLinearGroup.map φ M') (φ t) _ h'
  have h4 : (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map φ =
      φ t • (((Matrix.GeneralLinearGroup.map φ M')⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← map_inv]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rfl
  rw [h1, ← Matrix.charpoly_map, h4, h3] at h
  have h5 := congrArg roots h
  rw [roots_multiset_prod_X_sub_C] at h5
  rw [← roots_multiset_prod_X_sub_C (S'.map fun a => φ t * a⁻¹), Multiset.map_map]
  exact h5.symm

private theorem cPl_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    cPl w = preplace (IsCMField.complexConj E).toRingEquiv w :=
  HeightOneSpectrum.ext ((GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w))

private theorem normV_preplace {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) :
    normV (preplace τ v) = normV v := by
  show Nat.card (𝓞 K ⧸ (preplace τ v).asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv τ) ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
    (RingOfIntegers.mapRingEquiv τ).surjective v.asIdeal).symm

private theorem isFrob_conjGal {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {τ : K ≃+* K} {σ : Ω ≃+* Ω}
    (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {q : ℕ} {g : G K Ω}
    (hg : IsFrob (F := K) A' q g) : IsFrob (F := K) A q (conjGal h g) := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← val_lt_one hA, map_sub, apply_conjGal, map_pow]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))

private theorem isLift_conj {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω]
    {c : G (maximalRealSubfield F) Ω} (hc : IsConjEl c) :
    IsLift (IsCMField.complexConj F).toRingEquiv c.symm.toRingEquiv := by
  obtain ⟨j, hj⟩ := hc
  intro x
  refine c.symm_apply_eq.2 (j.injective ?_)
  rw [hj]
  have h := IsCMField.complexEmbedding_complexConj F (j.comp (algebraMap F Ω)) x
  exact (Complex.conj_conj _).symm.trans (congrArg (starRingEnd ℂ) h.symm)

private theorem frob_dual {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)} {θ : G F Ω →* (Qbar l)ˣ}
    {c : G (maximalRealSubfield F) Ω} {P : GL (Fin n) (Qbar l)} (hc : IsConjEl c)
    (hP : IsPairing c r (cycBar F Ω l ^ (1 - (n : ℤ)) * θ) P) {w : HeightOneSpectrum (𝓞 F)}
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {B B' : Multiset ℂˣ} {z : ℂˣ} (hB : FrobEig ι r w (algSat n (normV w) B))
    (hB' : FrobEig ι r (cPl w) (algSat n (normV (cPl w)) B')) (hz : CharEig ι θ w z) :
    B'.map (·⁻¹) = B.map (· * z⁻¹) := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have hL := isLift_conj hc
  have hAA : ∀ y, c.symm.toRingEquiv y ∈ A ↔ y ∈ A.comap c.symm.toRingEquiv.toRingHom := fun _ => Iff.rfl
  rw [cPl_eq] at hB'
  have e := (hB' _ (isPlaceOver_preplace hL hAA hA)).2 (conjGal hL σ)
    (by rw [normV_preplace]; exact isFrob_conjGal hL hAA hσ)
  rw [normV_preplace] at e
  have h1 := eig_dual ι.toRingHom (r σ⁻¹) (r (conjGal hL σ)⁻¹) P _
    (hP σ⁻¹ (conjGal hL σ)⁻¹ (by rw [← map_inv]; exact AlgEquiv.ext fun _ => rfl)) _ _ ((hB A hA).2 σ hσ) e
  have h2 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]
  have hq0 : normV w ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at h2
    exact Units.ne_zero _ h2
  have hqR : (0 : ℝ) < normV w := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have h3 := (hz A hA).2 σ hσ
  set d : ℂ := ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; exact_mod_cast (Real.rpow_pos_of_pos hqR _).ne'
  have hdd : d * d = (normV w : ℂ) ^ ((n : ℤ) - 1) := by
    rw [hd, ← Complex.ofReal_mul, ← Real.rpow_add hqR, add_halves,
      show ((n : ℝ) - 1) = (((n : ℤ) - 1 : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
    push_cast
    rfl
  have h4 : ι.toRingHom (((cycBar F Ω l ^ (1 - (n : ℤ)) * θ) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = d * d * z := by
    change ι _ = _
    rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, Units.val_mul, map_mul, map_inv (cycBar F Ω l),
      Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀, map_inv₀, map_natCast, h3, hdd, inv_zpow',
      neg_sub]
  have hS : ∀ B : Multiset ℂˣ, algSat n (normV w) B = B.map fun α : ℂˣ => d * (α : ℂ) := fun B => by
    simp only [algSat, ← hd, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map,
      Function.comp_def]
  rw [h4, hS, hS] at h1
  have h5 := congrArg (Multiset.map fun a : ℂ => d⁻¹ * a * (z : ℂ)⁻¹) h1
  simp only [Multiset.map_map, Function.comp_def] at h5
  apply Multiset.map_injective (f := (Units.val : ℂˣ → ℂ)) Units.val_injective
  simp only [Multiset.map_map, Function.comp_def]
  have := z.ne_zero
  refine (Multiset.map_congr rfl fun a _ => ?_).trans (h5.symm.trans (Multiset.map_congr rfl fun a _ => ?_))
  · rw [Units.val_inv_eq_inv_val]
    have := a.ne_zero
    field_simp
  · rw [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp

theorem UpperTheory.frobeniusDuality_complexConj :
    UpperTheory.V.Af.Sol.FrobDualC := by
  intro F Ω _ _ _ _ _ _ l _ ι n r θ c P hc hP w hw B B' z hB hB' hz
  exact frob_dual hc hP hw hB hB' hz
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ResidualCharactersPsiNe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open UpperTheory.V.Ws UpperTheory.V.Sd

private theorem closed_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F E : IntermediateField ℚ Ω) :
    IsClosed ((E.fixingSubgroup.comap (resQ F) : Subgroup (G F Ω)) : Set (G F Ω)) := by
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  have e : ((E.fixingSubgroup.comap (resQ F) : Subgroup (G F Ω)) : Set (G F Ω)) =
      ⋂ x ∈ E, (MulAction.stabilizer (Ω ≃ₐ[F] Ω) x : Set (Ω ≃ₐ[F] Ω)) := by
    ext g
    simp only [SetLike.mem_coe, Subgroup.mem_comap, Set.mem_iInter, MulAction.mem_stabilizer_iff]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rfl
  rw [e]
  exact isClosed_biInter fun x _ => Subgroup.isClosed_of_isOpen _ (stabilizer_isOpen_of_isIntegral x)

private theorem lim_pt {Γ : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime]
    (ε : Γ →* ℤ_[l]ˣ) (hε : Continuous ε) (S : Set Γ) (hS : IsClosed S) (g : Γ)
    (hg : (l : ℤ_[l]) ∣ (ε g : ℤ_[l]) - 1) (hm : ∀ n : ℕ, g ^ l ^ n ∈ S) : ∃ h ∈ S, ε h = 1 := by
  have ht : Filter.Tendsto (fun n : ℕ => ((ε (g ^ l ^ n) : ℤ_[l]ˣ) : ℤ_[l])) Filter.atTop (nhds 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have h0 : Filter.Tendsto (fun n : ℕ => ((l : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hl)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
    have h2 := dvd_sub_pow_of_dvd_sub hg n
    rw [one_pow] at h2
    have h3 := (pow_dvd_pow _ n.le_succ).trans h2
    rw [map_pow, Units.val_pow_eq_pow_val, inv_pow, ← zpow_natCast, ← zpow_neg,
      PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
    exact h3
  obtain ⟨h, hh, hc⟩ := hS.isCompact.exists_mapClusterPt (f := Filter.atTop) (u := fun n : ℕ => g ^ l ^ n)
    (Filter.tendsto_principal.2 (Filter.Eventually.of_forall hm))
  refine ⟨h, hh, Units.ext ?_⟩
  have hc' := hc.continuousAt_comp (Units.continuous_val.comp hε).continuousAt
  exact eq_of_nhds_neBot (hc'.clusterPt.mono ht)

private theorem dvd_of_om {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) (g : G ℚ Ω) (hg : D.om g = 1) : (l : ℤ_[l]) ∣ (cycZ ℚ Ω l g : ℤ_[l]) - 1 := by
  obtain ⟨-, -, hloc, -⟩ := dvrFacts l c.O
  have h := hD.om_bar g
  simp only [Raw.bar, hg, Units.val_one] at h
  have h1 : residue c.O (algebraMap ℤ_[l] c.O ((cycZ ℚ Ω l g : ℤ_[l]) - 1)) = 0 := by
    rw [map_sub, map_sub, map_one, h, sub_eq_zero]
    rfl
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff] at h1
  have h2 : (cycZ ℚ Ω l g : ℤ_[l]) - 1 ∈ maximalIdeal ℤ_[l] := fun hu => h1 (hu.map _)
  rwa [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h2

section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l} {D : Raw Ω c}
  (T : Tower D)

private noncomputable def eta : G T.F Ω →* (ResidueField c.O)ˣ :=
  (Units.map (residue c.O).toMonoidHom).comp ((T.fr ∅).rt wPs)

private theorem eta_val (g : G T.F Ω) : (eta T g : ResidueField c.O) = T.rb wPs g := rfl

private theorem eta_sq (hT : T.Two) (g : G T.F Ω) : eta T g ^ 2 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, eta_val, hT.sq, Units.val_one])

private theorem eta_om (hD : D.Good) (hT : T.Two) (hne : ∀ g ∈ T.G', T.rb wPs g = 1) (g : G T.F Ω) (hg' : g ∈ T.GalL)
    (hg : D.om (resQ T.F g) = 1) : eta T g = 1 := by
  haveI : Algebra.IsAlgebraic T.F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) T.F
  haveI : IsAlgClosure T.F Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  haveI : IsGalois T.F Ω := {}
  haveI : CompactSpace (G T.F Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[T.F] Ω))
  obtain ⟨k₀, -, -, -, hk⟩ := hT.quad
  have hk' : ∀ g, eta T g = 1 ↔ g ∈ k₀.fixingSubgroup.comap (resQ T.F) := fun g => by
    rw [Subgroup.mem_comap, ← hk, ← eta_val, Units.val_eq_one]
  have hc : Continuous fun h : G T.F Ω => g⁻¹ * h := continuous_const_mul _
  have h0 : IsClosed (T.GalL : Set (G T.F Ω)) := closed_fix T.F T.K
  have hd : (l : ℤ_[l]) ∣ (cycZ T.F Ω l g : ℤ_[l]) - 1 := dvd_of_om D hD (resQ T.F g) hg
  obtain ⟨h, ⟨h1, h2⟩, h3⟩ := lim_pt l (cycZ T.F Ω l) (continuous_cycZ T.F Ω l) _
    (h0.inter ((closed_fix T.F k₀).preimage hc)) g hd (fun n => ⟨T.GalL.pow_mem hg' _, by
      refine (hk' _).1 ?_
      obtain ⟨m, hm⟩ := (hl.out.odd_of_ne_two hD.l_odd).pow (n := n)
      rw [map_mul, map_inv, map_pow, hm, pow_succ, pow_mul, eta_sq T hT, one_pow, one_mul, inv_mul_cancel]⟩)
  have h4 : eta T h = 1 := by
    rw [← Units.val_eq_one, eta_val]
    exact hne h ⟨h1, h3⟩
  have h5 := (hk' _).2 h2
  rwa [map_mul, h4, mul_one, map_inv, inv_eq_one] at h5

private theorem eta_mul (g : G T.F Ω) :
    eta T g * Raw.bar (chi D T.pr 2) (resQ T.F g) = Raw.bar (chi D T.pr 0) (resQ T.F g) ∧
    eta T g * Raw.bar (chi D T.pr 3) (resQ T.F g) = Raw.bar (chi D T.pr 1) (resQ T.F g) := by
  have e : (T.fr ∅).rt wPs g = chi D T.pr 0 (resQ T.F g) * (chi D T.pr 2 (resQ T.F g))⁻¹ := by
    show (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 1 (resQ T.F g))⁻¹) ^ (0 : ℤ) *
      (chi D T.pr 0 (resQ T.F g) * (chi D T.pr 2 (resQ T.F g))⁻¹) ^ (1 : ℤ) = _
    rw [zpow_zero, zpow_one, one_mul]
  have e' : (T.fr ∅).rt wPs g = chi D T.pr 1 (resQ T.F g) * (chi D T.pr 3 (resQ T.F g))⁻¹ := by
    rw [e]
    generalize resQ T.F g = s
    cases T.pr
    · show D.al s * D.Psi s * (D.al s)⁻¹ = D.Psi s * 1⁻¹
      rw [inv_one, mul_one, mul_inv_cancel_comm]
    · show D.al s * (D.al s * D.Psi s)⁻¹ = 1 * (D.Psi s)⁻¹
      rw [one_mul, mul_inv, mul_inv_cancel_left]
  rw [eta_val]
  constructor
  · show residue c.O _ * residue c.O _ = residue c.O _
    rw [← map_mul, ← Units.val_mul, e, inv_mul_cancel_right]
  · show residue c.O _ * residue c.O _ = residue c.O _
    rw [← map_mul, ← Units.val_mul, e', inv_mul_cancel_right]

private theorem eta_mul' (hT : T.Two) (g : G T.F Ω) {u v : ResidueField c.O} (h : eta T g * u = v) : eta T g * v = u := by
  rw [← h, ← mul_assoc, ← Units.val_mul, ← pow_two, eta_sq T hT, Units.val_one, one_mul]

private noncomputable def etaL : T.GalL →* (ResidueField c.O)ˣ := (eta T).comp T.GalL.subtype

private theorem etaL_app (g : T.GalL) : etaL T g = eta T g := rfl

private theorem etaL_sq (hT : T.Two) : etaL T ^ 2 = 1 := by
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply, etaL_app, eta_sq T hT]

private theorem etaL_perm (hT : T.Two) (i : Fin 4) : ∃ j, ∀ g : T.GalL, etaL T g * Raw.bar (chi D T.pr i) (resQ T.F g) =
      Raw.bar (chi D T.pr j) (resQ T.F g) := by
  simp only [etaL_app]
  match i with
  | 0 => exact ⟨2, fun g => eta_mul' T hT g (eta_mul T g).1⟩
  | 1 => exact ⟨3, fun g => eta_mul' T hT g (eta_mul T g).2⟩
  | 2 => exact ⟨0, fun g => (eta_mul T g).1⟩
  | 3 => exact ⟨1, fun g => (eta_mul T g).2⟩

end

theorem UpperTheory.residual_characters_psi_ne :
    UpperTheory.V.Sd.S2.PsiNe := by
  intro Ω _ _ _ l hl c D T hD hO hT
  by_contra hne
  have hne' : ∀ g ∈ T.G', T.rb wPs g = 1 := fun g hg => by_contra fun h => hne ⟨g, hg, h⟩
  have key := hO.g3' (etaL T) (etaL_sq T hT)
    (fun g hg => by rw [etaL_app]; exact eta_om T hD hT hne' g g.2 hg) (etaL_perm T hT)
  obtain ⟨g, hg, hg'⟩ := hO.g3 wPs (by decide)
  have h1 := etaL_app T ⟨g, hg⟩
  rw [key, MonoidHom.one_apply] at h1
  apply hg'
  rw [← eta_val, ← h1, Units.val_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinContinuousLeftAction
open UpperTheory.V.Sd.Eis

noncomputable section

open NumberField MeasureTheory Topology Matrix Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem map_aff1 {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    GeneralLinearGroup.map f (aff 1 x) = aff 1 (f x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff]

private theorem aff_one_zero {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff]

private theorem infGL_aff (x : TR.Rinf F) : TR.infGL F 2 (aff 1 x) = aff 1 (TR.sInf F x) := by
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL, map_aff1]
    exact congrArg _ ((TR.infEq F).symm_apply_apply x).symm
  · rw [TR.pFin_infGL, map_aff1]
    exact aff_one_zero.symm

private theorem infGL_left (a : GL (Fin 2) (TR.Rinf F)) (g : GA F 2) :
    TR.infGL F 2 a * g = g * TR.infGL F 2 ((GeneralLinearGroup.map (TR.pInf F) g)⁻¹ * a * GeneralLinearGroup.map (TR.pInf F) g) :=
  TR.ga_ext (by simp only [map_mul, map_inv, TR.pInf_infGL]; group) (by simp only [map_mul, map_inv, TR.pFin_infGL]; group)

omit [IsTotallyReal F] in
private theorem conj_deriv (h : GL (Fin 2) (TR.Rinf F)) (a : ℝ → GL (Fin 2) (TR.Rinf F)) (X : Matrix (Fin 2) (Fin 2) (TR.Rinf F))
    (ha : HasDerivAt (fun t => TR.toL (a t).val) (TR.toL X) 0) :
    HasDerivAt (fun t => TR.toL (h⁻¹ * a t * h).val) (TR.toL ((h⁻¹).val * X * h.val)) 0 :=
  ((TR.rmul (TR.toL h.val)).comp (TR.lmul (TR.toL (h⁻¹).val))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ha

open Classical in
omit [IsTotallyReal F] in
private theorem conj_dec (h : GL (Fin 2) (TR.Rinf F)) (i j : Fin 2) (u : TR.Rinf F) :
    TR.toL ((h⁻¹).val * Matrix.single i j u * h.val) = ∑ v, u v • ∑ a, ∑ b,
      ((((GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h)⁻¹).val * Matrix.single i j (1 : ℝ) *
        (GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h).val) a b : ℝ) •
          TR.toL (Matrix.single a b (Pi.single v 1 : TR.Rinf F)) := by
  funext a b w
  simp only [← map_inv]
  generalize h⁻¹ = h'
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two, Pi.single_apply, Finset.sum_apply] <;> ring

omit [IsTotallyReal F] in
private theorem nil_curve (u : TR.Rinf F) :
    Continuous (fun t : ℝ => aff (1 : (TR.Rinf F)ˣ) (t • u)) ∧
    (∀ s t : ℝ, aff (1 : (TR.Rinf F)ˣ) ((s + t) • u) = aff 1 (s • u) * aff 1 (t • u)) ∧
    HasDerivAt (fun t : ℝ => TR.toL (aff (1 : (TR.Rinf F)ˣ) (t • u)).val) (TR.toL (Matrix.single 0 1 u)) 0 := by
  refine ⟨Units.continuous_iff.2 ⟨?_, ?_⟩, fun s t => ?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, -Matrix.coe_units_inv] <;> fun_prop
  · ext i j : 2
    fin_cases i <;> fin_cases j <;> simp [aff, add_smul, add_comm]
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, hasDerivAt_const]
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u

omit [IsTotallyReal F] in
private theorem tor_curve (u : TR.Rinf F) (y : ℝ → (TR.Rinf F)ˣ) (hy : ∀ t v, (y t).val v = Real.exp (t * u v)) :
    Continuous (fun t : ℝ => aff (y t) 0) ∧
    (∀ s t : ℝ, aff (y (s + t)) 0 = aff (y s) 0 * aff (y t) 0) ∧
    HasDerivAt (fun t : ℝ => TR.toL (aff (y t) 0).val) (TR.toL (Matrix.single 0 0 u)) 0 := by
  have e : ∀ t, (y t).val = fun v => Real.exp (t * u v) := fun t => funext (hy t)
  have e' : ∀ t, ((y t)⁻¹).val = fun v => Real.exp (-(t * u v)) := fun t =>
    Units.inv_eq_of_mul_eq_one_right (by funext v; simp [hy, ← Real.exp_add])
  refine ⟨Units.continuous_iff.2 ⟨?_, ?_⟩, fun s t => ?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, e] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, -Matrix.coe_units_inv, e'] <;> fun_prop
  · ext i j v
    fin_cases i <;> fin_cases j <;> simp [aff, hy, add_mul, Real.exp_add]
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, hasDerivAt_const]
    refine hasDerivAt_pi.2 fun v => ?_
    simpa [hy] using ((hasDerivAt_id (0 : ℝ)).mul_const (u v)).exp

theorem UpperTheory.eisenstein_continuous_left_action :
    UpperTheory.V.Sd.Eis.SmCont → UpperTheory.V.Sd.Eis.CtBasic → UpperTheory.V.Sd.Eis.CtLie → UpperTheory.V.Sd.Eis.LieAlg → UpperTheory.V.Sd.Eis.CentLie → UpperTheory.V.Sd.Eis.CtLeft := by
  intro hS hB hL hA hC F _ _ _ _ _ μ _ D hD k c ω hω φ hφ u y hy g
  classical
  have hl := hL F μ D hD φ hφ.aut.left hφ.aut.level
  have hb := hB F μ D hD φ.1 (hS F 2 φ hφ.aut.level) hφ.aut.left
  have hi : ∀ X, IntegrableOn (fun x : NA F => (TR.lie F 2 X φ).1 (unip x * g)) D μ := fun X =>
    (hB F μ D hD _ (hl X).1.2 (hl X).1.1).1 g
  let L : TR.Lie F 2 →ₗ[ℝ] ℂ :=
    { toFun := fun X => cterm μ D (TR.lie F 2 X φ).1 g
      map_add' := fun X Y => by
        rw [map_add (f := _)]
        exact integral_add (hi X) (hi Y)
      map_smul' := fun r X => by
        rw [map_smul]
        exact integral_smul r (fun x : NA F => (TR.lie F 2 X φ).1 (unip x * g)) }
  have hsm : ∀ (X) (z : ℂ) (ψ : TR.Sm F 2), TR.lie F 2 X φ = z • ψ → L X = z * cterm μ D ψ.1 g := fun X z ψ e => by
    change cterm μ D (TR.lie F 2 X φ).1 g = _
    rw [e]
    exact integral_const_mul z (fun x : NA F => ψ.1 (unip x * g))
  set h := GeneralLinearGroup.map (TR.pInf F) g with hh
  have key : ∀ (a : ℝ → GL (Fin 2) (TR.Rinf F)) (X : Matrix (Fin 2) (Fin 2) (TR.Rinf F)), Continuous a →
      (∀ s t, a (s + t) = a s * a t) → HasDerivAt (fun t => TR.toL (a t).val) (TR.toL X) 0 →
      HasDerivAt (fun t => cterm μ D φ.1 (TR.infGL F 2 (a t) * g)) (L (TR.toL ((h⁻¹).val * X * h.val))) 0 := by
    intro a X h1 h2 h3
    simp only [infGL_left _ g]
    exact (hl _).2 (fun t => h⁻¹ * a t * h) (by fun_prop) (fun s t => by rw [h2]; group) (conj_deriv h a X h3) g
  have hnil : ∀ x : TR.Rinf F, L (TR.toL ((h⁻¹).val * Matrix.single 0 1 x * h.val)) = 0 := fun x => by
    obtain ⟨h1, h2, h3⟩ := nil_curve x
    have := key _ _ h1 h2 h3
    simp only [infGL_aff, hb.2.1] at this
    exact this.unique (hasDerivAt_const _ _)
  let E : InfinitePlace F → Fin 2 → Fin 2 → TR.Lie F 2 := fun v a b => TR.toL (Matrix.single a b (Pi.single v 1 : TR.Rinf F))
  have hE : ∀ v a b, TR.lie F 2 (E v a b) = TR.Eop v a b := fun _ _ _ => by
    simp only [E, TR.Eop]
  have hdec : ∀ (i j : Fin 2) (x : TR.Rinf F), L (TR.toL ((h⁻¹).val * Matrix.single i j x * h.val)) =
      ∑ v, (x v : ℂ) * ∑ a, ∑ b,
      ((((GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h)⁻¹).val * Matrix.single i j (1 : ℝ) *
        (GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h).val) a b : ℝ) * L (E v a b) := fun i j x => by
    rw [conj_dec]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Complex.real_smul, E]
  have hv := fun v : InfinitePlace F => hA (GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h) (fun a b => L (E v a b))
    (k * cterm μ D φ.1 g)
    (by
      rw [← map_add (f := _), hsm _ 0 φ, zero_mul]
      rw [map_add (f := _), hE, hE, zero_smul]
      exact hC F k c ω hω φ hφ v)
    (by
      rw [← map_sub, hsm _ (Complex.I * k) φ, mul_assoc]
      rw [map_sub, hE, hE]
      exact hφ.wt v)
    (by
      rw [← map_sub, ← map_add (f := _), hsm _ Complex.I (TR.lie F 2 (E v 0 1 + E v 1 0) φ)]
      · rfl
      rw [map_sub, map_add (f := _), hE, hE, hE, hE]
      exact hφ.low v)
    (by
      have := hnil (Pi.single v 1)
      rw [hdec, Finset.sum_eq_single v (fun w _ hw => by simp [Pi.single_eq_of_ne hw]) (by simp)] at this
      simpa only [Pi.single_eq_same, Complex.ofReal_one, one_mul] using this)
  obtain ⟨h1, h2, h3⟩ := tor_curve u y hy
  have := key _ _ h1 h2 h3
  rw [hdec] at this
  simp only [hv] at this
  convert this using 1
  rw [← Finset.sum_mul]
  push_cast
  ring
end
end
