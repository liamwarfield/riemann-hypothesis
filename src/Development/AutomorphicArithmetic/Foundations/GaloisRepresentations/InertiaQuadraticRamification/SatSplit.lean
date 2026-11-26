module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ThreeApartOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionAbelianCompletion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameKummerInertiaSurjective

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.SatSplit
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem satSplit : SatSplit := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ A v w hv hw hD a π P hP B hB
  obtain ⟨i, hi, hi', hiv⟩ := splitIso_holds K M Ω A v w hv hw hD
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL K a π v
  obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL M a P w
  obtain ⟨e, he⟩ := hP v w i hi hi' σ σ' hσ hσ'
  obtain ⟨φ, hφ⟩ := exists_isFrob hv
  have hq : normV w = normV v ^ 1 := degOf K M Ω A v w hv hw (fun τ hτ => hD τ (Ine_le_Dec A hτ)) φ 1 one_pos hφ
    fun k => ⟨fun _ => one_dvd k, fun _ => hD _ (pow_mem (show φ ∈ Dec (F := K) A from hφ.1) k)⟩
  rw [pow_one] at hq
  refine ((GlobalTheory.T.cuspRep_satake_iff_localComponent_satake M a P w σ' hσ').1 B).2 (GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i hiv ?_ e (fun g x => (he g x).symm)
    (((GlobalTheory.T.cuspRep_satake_iff_localComponent_satake K a π v σ hσ).1 B).1 hB))
  first | exact hq | (unfold normV at hq; simp only [Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]; exact hq)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.AllUnr
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem unramifiedAt_of_dec_fixes (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)) (hA : IsPlaceOver A w)
    (hfix : ∀ g ∈ Dec (F := maximalRealSubfield L) A, Fixes L g) :
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
  haveI : IsAlgClosure (maximalRealSubfield L) Ω :=
    ⟨IsAlgClosure.isAlgClosed L, Algebra.IsAlgebraic.trans _ L Ω⟩
  have hAv : IsPlaceOver A (w.under (𝓞 (maximalRealSubfield L))) := fun x => by
    rw [IsScalarTower.algebraMap_apply (maximalRealSubfield L) L Ω]
    exact hA (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) x)
  obtain ⟨-, he⟩ := GlobalTheory.InertFixVal.ramificationIdx_eq_one A (w.under (𝓞 (maximalRealSubfield L))) w hAv hA
    fun σ hσ => hfix σ (Ine_le_Dec A hσ)
  exact Ideal.ramificationIdx_eq_one_iff.1 he

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.allUnr :
    SplitIff → AllUnr := by
  intro hS Y Ω _ _ _ _ _ T Q hQ w
  by_cases hw : IsSplitAt w
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    exact unramifiedAt_of_dec_fixes ↥Q.K Ω A w hA ((hS ↥Q.K Ω A w hA).1 hw)
  · exact (hQ.2.2.2.1 w hw).2.1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ApartUp
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem exists_real_lift (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M]
    [Algebra K M] (x : 𝓞 (maximalRealSubfield K)) :
    ∃ y : 𝓞 (maximalRealSubfield M), algebraMap (𝓞 (maximalRealSubfield M)) (𝓞 M) y =
      algebraMap (𝓞 K) (𝓞 M) (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) x) := by
  set y₀ : 𝓞 M := algebraMap (𝓞 K) (𝓞 M) (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) x) with hy₀
  have hz : (y₀ : M) = algebraMap K M (((x : maximalRealSubfield K)) : K) := rfl
  have hmem : (y₀ : M) ∈ maximalRealSubfield M := by
    rw [hz]
    exact (mem_maximalRealSubfield_iff _).2 fun φ =>
      (mem_maximalRealSubfield_iff _).1 (x : maximalRealSubfield K).2 (φ.comp (algebraMap K M))
  have hint : IsIntegral ℤ (⟨(y₀ : M), hmem⟩ : maximalRealSubfield M) :=
    (isIntegral_algebraMap_iff (B := M) ).1
      (RingOfIntegers.isIntegral_coe y₀)
  exact ⟨⟨⟨(y₀ : M), hmem⟩, hint⟩, RingOfIntegers.ext rfl⟩

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.apartUp :
    ApartUp := by
  intro K M _ _ _ _ _ _ _
  refine ⟨fun w₁ w₂ hap h => hap ?_, fun v => ?_⟩
  · apply HeightOneSpectrum.ext
    apply Ideal.ext
    intro x
    obtain ⟨y, hy⟩ := exists_real_lift K M x
    have h' : y ∈ (w₁.under (𝓞 (maximalRealSubfield M))).asIdeal ↔
        y ∈ (w₂.under (𝓞 (maximalRealSubfield M))).asIdeal := by rw [h]
    simp only [HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, hy] at h' ⊢
    exact h'
  · have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 M)) := FaithfulSMul.algebraMap_injective _ _
    have hker : RingHom.ker (algebraMap (𝓞 K) (𝓞 M)) ≤ v.asIdeal := by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
      exact bot_le
    haveI := v.isMaximal
    obtain ⟨Q, hQ, hQm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 M) v.asIdeal hker
    have hne : Q ≠ ⊥ := by
      rintro rfl
      apply v.ne_bot
      rw [← hQm, Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 hinj]
    refine ⟨⟨Q, hQ.isPrime, hne⟩, ?_⟩
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal]
    exact hQm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.LayerOf
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.layerOf :
    InclOf → IndexComap → LayerOf := by
  intro hIncl hIdx
  unfold LayerOf
  intro E Ω _ _ _ _ _ _ S H H' hH' hle hp X Y hX hY u hS hDec hτex
  obtain ⟨A, hA, τ, hτ, hτ'⟩ := hτex
  unfold Cuts at hX hY
  have overUnder : ∀ (B : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver B w →
      IsPlaceOver B (w.under (𝓞 (maximalRealSubfield E))) := by
    intro B w hB x
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, ← hB]
    rfl
  have resLift : ∀ (g : G (maximalRealSubfield E) Ω) (hg : Fixes E g),
      AlgEquiv.restrictScalarsHom (maximalRealSubfield E) (GlobalTheory.AboveL.DecRes.lift (E := E) g hg) = g :=
    fun g hg => AlgEquiv.ext fun x => rfl
  have hτD := Ine_le_Dec A hτ
  obtain ⟨hτE, hτH⟩ := hDec A hA τ hτD
  obtain ⟨τ', hres⟩ : ∃ τ' : G E Ω, AlgEquiv.restrictScalarsHom (maximalRealSubfield E) τ' = τ :=
    ⟨_, resLift τ hτE⟩
  have fY : fixGrp E Ω Y.K = H'.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) :=
    Subgroup.ext fun g => hY g
  have fX : fixGrp E Ω X.K = H.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) :=
    Subgroup.ext fun g => hX g
  have hidx := hIdx (G (maximalRealSubfield E) Ω) (G E Ω)
    (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) H H' hH'.comm hle hp
    ⟨τ', by rw [hres]; exact hτH, by rw [hres]; exact hτ'⟩
  obtain ⟨x0, t0E, t0Ω, hgal, hfin⟩ := hIncl E Ω X Y (by rw [fY, fX]; exact Subgroup.comap_mono hle)
  rw [fY, fX, hidx] at hfin
  obtain ⟨w, hw⟩ := GlobalTheory.AbOverSubfield.exists_place_between (F := maximalRealSubfield E) (K := E) hA
  have hwu : w.under (𝓞 (maximalRealSubfield E)) = u := eq_of_isPlaceOver (overUnder A w hw) hA
  have hfixX : Fixes X.K τ' := (hX τ').2 (by rw [hres]; exact hτH)
  refine ⟨⟨x0, t0E, t0Ω, hgal, by rw [hfin]; exact hp, w, ?_, ?_, A, hw,
    GlobalTheory.AboveL.DecRes.lift (E := X.K) τ' hfixX, ?_, ?_⟩, ?_⟩
  · intro hwS
    exact hS w hwS hwu
  · intro B hB g hg
    have hBu : IsPlaceOver B u := by
      rw [← hwu]
      exact overUnder B w hB
    obtain ⟨hgE, hgH⟩ := hDec B hBu g hg
    refine ⟨hgE, ?_⟩
    have h1 := (hX (GlobalTheory.AboveL.DecRes.lift (E := E) g hgE)).2 (by rw [resLift]; exact hgH)
    exact h1
  · subst hres
    rw [mem_Ine]
    have hτI := (mem_Ine (A := A)).1 hτ
    exact ⟨(GlobalTheory.AboveL.mem_dec_congr A _ _ (fun x => rfl)).2 hτI.1, hτI.2⟩
  · intro hfix
    exact hτ' (by rw [← hres]; exact (hY τ').1 hfix)
  · intro x1 t1
    have hx : x1 = x0 := by
      refine Algebra.algebra_ext _ _ fun r => (algebraMap Y.K Ω).injective ?_
      rw [← @IsScalarTower.algebraMap_apply X.K Y.K Ω _ _ _ x1 _ _ t1 r,
        ← @IsScalarTower.algebraMap_apply X.K Y.K Ω _ _ _ x0 _ _ t0Ω r]
    subst hx
    exact hfin
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplit
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem zpow_mem_fix {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (σ : G F Ω) (z : Ω)
    (h : σ z = z) (n : ℤ) : (σ ^ n) z = z := by
  have hs : σ ∈ MulAction.stabilizer (G F Ω) z := h
  exact (MulAction.stabilizer (G F Ω) z).zpow_mem hs n

private theorem sq_apply_of_pm {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (φ : G F Ω) (z : Ω)
    (h : φ z = z ∨ φ z = -z) : (φ ^ (2 : ℤ)) z = z := by
  have e : φ ^ (2 : ℤ) = φ * φ := zpow_two φ
  rw [e, AlgEquiv.mul_apply]
  rcases h with h | h
  · rw [h, h]
  · rw [h, map_neg, h, neg_neg]

private theorem fix_of_parity {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [CharZero Ω] (φ : G F Ω) (e x : Ω)
    (he0 : e ≠ 0) (hφe : φ e = e ∨ φ e = -e) (hφx : φ x = x ∨ φ x = -x) (k m : ℤ)
    (hk : (φ ^ k) e ≠ e) (hm : (φ ^ m) e = e) : (φ ^ m) x = x := by
  rcases Int.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [hj, ← two_mul, zpow_mul]
    exact zpow_mem_fix _ x (sq_apply_of_pm φ x hφx) j
  · exfalso
    have hφe' : φ e = -e := by
      rcases hφe with h | h
      · exact absurd (zpow_mem_fix φ e h k) hk
      · exact h
    rw [hj, zpow_add, zpow_one, zpow_mul, AlgEquiv.mul_apply, hφe', map_neg,
      zpow_mem_fix _ e (sq_apply_of_pm φ e hφe) j] at hm
    have h2 : (2 : Ω) * e = 0 := by linear_combination -hm
    rcases mul_eq_zero.1 h2 with h | h
    · exact two_ne_zero h
    · exact he0 h

private theorem pm_of_sq {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (σ : G F Ω) (z : Ω)
    (h : σ (z ^ 2) = z ^ 2) : σ z = z ∨ σ z = -z := by
  rw [map_pow] at h
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h

private theorem fixes_of_imag {Y Ω : Type} [Field Y] [NumberField Y] [IsCMField Y] [Field Ω] [Algebra Y Ω]
    (e : Y) (he : e ≠ 0) (hce : IsCMField.complexConj Y e = -e) (g : G (maximalRealSubfield Y) Ω)
    (hg : g (algebraMap Y Ω e) = algebraMap Y Ω e) : Fixes Y g := by
  intro y
  have h2 : (2 : Y) ≠ 0 := two_ne_zero
  obtain ⟨a, haa⟩ : ∃ a : Y, a = (y + IsCMField.complexConj Y y) / 2 := ⟨_, rfl⟩
  obtain ⟨b, hbb⟩ : ∃ b : Y, b = (y - IsCMField.complexConj Y y) / (2 * e) := ⟨_, rfl⟩
  have ha : IsCMField.complexConj Y a = a := by
    rw [haa, map_div₀, map_add (f := _), IsCMField.complexConj_apply_apply, map_ofNat, add_comm]
  have hb : IsCMField.complexConj Y b = b := by
    rw [hbb, map_div₀, map_sub, IsCMField.complexConj_apply_apply, map_mul, map_ofNat, hce]
    field_simp
    ring
  have hy : y = a + e * b := by
    rw [haa, hbb]
    field_simp
    ring
  have hfa : g (algebraMap Y Ω a) = algebraMap Y Ω a :=
    g.commutes ⟨a, (IsCMField.complexConj_eq_self_iff Y a).1 ha⟩
  have hfb : g (algebraMap Y Ω b) = algebraMap Y Ω b :=
    g.commutes ⟨b, (IsCMField.complexConj_eq_self_iff Y b).1 hb⟩
  rw [hy, map_add (f := _), map_mul, map_add (f := _), map_mul, hfa, hfb, hg]

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.inertSplit :
    DecGen → InertSplit := by
  intro hD Y Ω _ _ _ _ _ _ A u hu x a hx hI hg h hh
  obtain ⟨g, hgD, hgY⟩ := hg
  haveI : IsAlgClosure (maximalRealSubfield Y) Ω := IsAlgClosure.ofAlgebraic _ Y Ω
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective
  obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 (maximalRealSubfield Y)), IsPlaceOver A v := by
    refine ⟨⟨u.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield Y)) (𝓞 Y)), Ideal.IsPrime.comap _, ?_⟩, ?_⟩
    · intro hb
      exact u.ne_bot (Ideal.eq_bot_of_comap_eq_bot hb)
    · intro z
      exact hu (algebraMap (𝓞 (maximalRealSubfield Y)) (𝓞 Y) z)
  obtain ⟨φ, hφ⟩ := exists_isFrob hv
  obtain ⟨e, he0, hce⟩ : ∃ e : Y, e ≠ 0 ∧ IsCMField.complexConj Y e = -e := by
    obtain ⟨y, hy⟩ : ∃ y : Y, IsCMField.complexConj Y y ≠ y := by
      by_contra hc
      push_neg at hc
      exact IsCMField.complexConj_ne_one Y (AlgEquiv.ext hc)
    refine ⟨y - IsCMField.complexConj Y y, sub_ne_zero.2 (Ne.symm hy), ?_⟩
    rw [map_sub, IsCMField.complexConj_apply_apply, neg_sub]
  have hXf : ({x, algebraMap Y Ω e} : Set Ω).Finite := Set.toFinite _
  have hIX : ∀ τ ∈ (Ine A : Subgroup (G (maximalRealSubfield Y) Ω)),
      ∀ y ∈ ({x, algebraMap Y Ω e} : Set Ω), τ y = y := by
    intro τ hτ y hy
    rcases hy with rfl | rfl
    · exact (hI τ hτ).2
    · exact (hI τ hτ).1 e
  let h' : G (maximalRealSubfield Y) Ω := AlgEquiv.restrictScalars _ h
  have hh' : h' ∈ Dec A := (GlobalTheory.AboveL.mem_dec_congr A h' h (fun _ => rfl)).2 hh
  obtain ⟨k, hk⟩ := hD _ Ω A v hv φ hφ _ hXf hIX g hgD
  obtain ⟨m, hm⟩ := hD _ Ω A v hv φ hφ _ hXf hIX h' hh'
  have hE0 : algebraMap Y Ω e ≠ 0 := (map_ne_zero _).2 he0
  have hpmE : φ (algebraMap Y Ω e) = algebraMap Y Ω e ∨ φ (algebraMap Y Ω e) = -algebraMap Y Ω e := by
    apply pm_of_sq
    have hs : e ^ 2 ∈ maximalRealSubfield Y := by
      rw [← IsCMField.complexConj_eq_self_iff, map_pow, hce, neg_sq]
    rw [← map_pow]
    exact φ.commutes (⟨e ^ 2, hs⟩ : maximalRealSubfield Y)
  have hpmx : φ x = x ∨ φ x = -x := by
    apply pm_of_sq
    rw [hx, map_intCast]
  have hkE : (φ ^ k) (algebraMap Y Ω e) ≠ algebraMap Y Ω e := by
    rw [← hk _ (by simp)]
    intro hgE
    exact hgY (fixes_of_imag e he0 hce g hgE)
  have hmE : (φ ^ m) (algebraMap Y Ω e) = algebraMap Y Ω e := by
    rw [← hm _ (by simp)]
    exact h.commutes e
  have hfx := fix_of_parity φ _ x hE0 hpmE hpmx k m hkE hmE
  rw [← hm x (by simp)] at hfx
  exact hfx
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Double
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalCoreLeFixingSubgroupNormalClosure
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.NormalClosureSolv

open Pointwise

variable {Ω F : Type} [Field Ω] [Field F] [Algebra F Ω]

theorem algebraMap_mem_smul_iff (γ : Ω ≃ₐ[F] Ω) (A : ValuationSubring Ω) (c : F) :
    algebraMap F Ω c ∈ γ • A ↔ algebraMap F Ω c ∈ A := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.commutes]

theorem isPlaceOver_smul' [NumberField F] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}
    (h : Formalism.ConjugateSelfDual.IsPlaceOver A v) (γ : Ω ≃ₐ[F] Ω) : Formalism.ConjugateSelfDual.IsPlaceOver (γ • A) v := by
  intro x
  rw [← h x, valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, algebraMap_mem_smul_iff,
    algebraMap_mem_smul_iff, map_inv₀]

end GlobalTheory.NormalClosureSolv
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemRealOfSq
theorem UpperTheory.Reformulated.B.Qh55.mem_real_of_sq :
    ∀ {Y : Type} [inst : Field Y] {δ : Y}
    {q : ℕ}, (0 : ℕ) < q → δ ^ (2 : ℕ) = (↑q : Y) → δ ∈ NumberField.maximalRealSubfield Y := by
  intro Y _ δ q hq h
  rw [NumberField.mem_maximalRealSubfield_iff]
  intro φ
  have h1 : (φ δ) ^ 2 = (q : ℂ) := by rw [← map_pow, h, map_natCast]
  have h2 : (φ δ) ^ 2 = ((Real.sqrt q : ℝ) : ℂ) ^ 2 := by
    rw [h1, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg q), Complex.ofReal_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h3 | h3
  · rw [h3, Complex.star_def, Complex.conj_ofReal]
  · rw [h3, star_neg, Complex.star_def, Complex.conj_ofReal]
end

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open scoped Pointwise

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem over_under {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra K Ω] [Algebra F Ω] [IsScalarTower F K Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 K)}
    (h : IsPlaceOver A w) : IsPlaceOver A (w.under (𝓞 F)) := fun x => by
  rw [IsScalarTower.algebraMap_apply F K Ω]
  exact h (algebraMap (𝓞 F) (𝓞 K) x)

private theorem smul_congr {K K' Ω : Type} [Field K] [Field K'] [Field Ω] [Algebra K Ω] [Algebra K' Ω]
    (A : ValuationSubring Ω) (g : G K Ω) (g' : G K' Ω) (hg : ∀ x, g x = g' x) : g • A = g' • A := by
  apply SetLike.coe_injective
  rw [ValuationSubring.coe_pointwise_smul, ValuationSubring.coe_pointwise_smul]
  ext x
  simp only [Set.mem_smul_set, AlgEquiv.smul_def, hg]

private theorem mem_real_of_sq {Y : Type} [Field Y] {δ : Y} {q : ℕ} (hq : 0 < q) (hδ : δ ^ 2 = (q : Y)) :
    δ ∈ maximalRealSubfield Y :=
  _root_.UpperTheory.Reformulated.B.Qh55.mem_real_of_sq hq hδ

private theorem algebraMap_mem_real {E Y : Type} [Field E] [Field Y] [Algebra E Y] {x : E}
    (hx : x ∈ maximalRealSubfield E) : algebraMap E Y x ∈ maximalRealSubfield Y :=
  (mem_maximalRealSubfield_iff _).2 fun φ => (mem_maximalRealSubfield_iff x).1 hx (φ.comp (algebraMap E Y))

private theorem apart_of_moves {E Y Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Y] [NumberField Y] [IsCMField Y]
    [Field Ω] [Algebra E Y] [Algebra E Ω] [Algebra Y Ω] [IsScalarTower E Y Ω] [IsAlgClosure Y Ω] {δ : Y} {q : ℕ} (hq : 0 < q)
    (hδ : δ ^ 2 = (q : Y)) (A : ValuationSubring Ω) (σ : G E Ω) (hσ : σ (algebraMap Y Ω δ) = -algebraMap Y Ω δ)
    (hfix : ∀ g ∈ Dec (F := maximalRealSubfield E) A, g (algebraMap Y Ω δ) = algebraMap Y Ω δ)
    {w₁ w₂ : HeightOneSpectrum (𝓞 Y)} (hw₁ : IsPlaceOver A w₁) (hw₂ : IsPlaceOver (σ • A) w₂) : GlobalTheory.Cong.Apart w₁ w₂ := by
  intro hv
  haveI : IsAlgClosure (maximalRealSubfield Y) Ω :=
    ⟨IsAlgClosure.isAlgClosed Y, Algebra.IsAlgebraic.trans _ Y Ω⟩
  have h1 := over_under (F := maximalRealSubfield Y) hw₁
  have h2 := over_under (F := maximalRealSubfield Y) hw₂
  rw [← hv] at h2
  obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_isPlaceOver h1 h2
  have hδr : δ ∈ maximalRealSubfield Y := mem_real_of_sq hq hδ
  have hρδ : ρ (algebraMap Y Ω δ) = algebraMap Y Ω δ := ρ.commutes (⟨δ, hδr⟩ : maximalRealSubfield Y)
  have hρF : ∀ x : maximalRealSubfield E, ρ.toRingEquiv (algebraMap (maximalRealSubfield E) Ω x) =
      algebraMap (maximalRealSubfield E) Ω x := fun x => by
    have h := ρ.commutes (⟨algebraMap E Y x, algebraMap_mem_real x.2⟩ : maximalRealSubfield Y)
    have e : algebraMap (maximalRealSubfield Y) Ω ⟨algebraMap E Y x, algebraMap_mem_real x.2⟩ =
        algebraMap (maximalRealSubfield E) Ω x := by
      change algebraMap Y Ω (algebraMap E Y x) = algebraMap E Ω x
      exact (IsScalarTower.algebraMap_apply E Y Ω _).symm
    rw [e] at h
    exact h
  let ρ' : G (maximalRealSubfield E) Ω := AlgEquiv.ofRingEquiv (f := ρ.toRingEquiv) hρF
  let σ' : G (maximalRealSubfield E) Ω := σ.restrictScalars _
  have hg : ρ'⁻¹ * σ' ∈ Dec (F := maximalRealSubfield E) A := mem_Dec.2 (by
    rw [mul_smul, inv_smul_eq_iff, smul_congr A σ' σ (fun _ => rfl), ← hρ, smul_congr A ρ' ρ (fun _ => rfl)])
  have h3 := hfix _ hg
  have h4 : σ' (algebraMap Y Ω δ) = ρ' (algebraMap Y Ω δ) := by
    have := congrArg ρ' h3
    rwa [AlgEquiv.mul_apply, ← AlgEquiv.mul_apply ρ', mul_inv_cancel, AlgEquiv.one_apply] at this
  have h5 : -algebraMap Y Ω δ = algebraMap Y Ω δ := by
    have a : σ' (algebraMap Y Ω δ) = σ (algebraMap Y Ω δ) := rfl
    have b : ρ' (algebraMap Y Ω δ) = ρ (algebraMap Y Ω δ) := rfl
    rw [a, b, hσ, hρδ] at h4
    exact h4
  haveI : CharZero Y := algebraRat.charZero Y
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective
  have h6 : algebraMap Y Ω δ = 0 := self_eq_neg.1 h5.symm
  have h7 : δ = 0 := (map_eq_zero _).1 h6
  rw [h7] at hδ
  have : (q : Y) = 0 := by simpa using hδ.symm
  exact hq.ne' (by exact_mod_cast this)

theorem double : Double := by
  intro E Ω _ _ _ _ _ _ T Q h0 t ht
  obtain ⟨⟨δ, ⟨⟨q, hq, hδ⟩, _, s, hs, hsδ⟩, hfix⟩, _, _⟩ := h0
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω t
  let σ : G E Ω := AlgEquiv.ofRingEquiv (f := s) (fun x => hs (algebraMap E Ω) x)
  have hA' : IsPlaceOver (σ • A) t := GlobalTheory.NormalClosureSolv.isPlaceOver_smul' hA σ
  obtain ⟨w₁, hw₁⟩ := GlobalTheory.AbOverSubfield.exists_place_between (K := ↥Q.K) hA
  obtain ⟨w₂, hw₂⟩ := GlobalTheory.AbOverSubfield.exists_place_between (K := ↥Q.K) hA'
  exact ⟨w₁, w₂, eq_of_isPlaceOver (over_under hw₁) hA, eq_of_isPlaceOver (over_under hw₂) hA',
    apart_of_moves hq hδ A σ hsδ (hfix t ht A hA) hw₁ hw₂⟩

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ExistsPlaceOfPrime
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem exists_prime_val {Ω : Type} [Field Ω] (A : ValuationSubring Ω) :
    ∀ n : ℕ, n ≠ 0 → A.valuation (n : Ω) < 1 → ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ A.valuation (r : Ω) < 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hv
    have hn1 : n ≠ 1 := by
      rintro rfl
      simp at hv
    have hp := Nat.minFac_prime hn1
    obtain ⟨m, hm⟩ := Nat.minFac_dvd n
    by_cases h : A.valuation ((n.minFac : ℕ) : Ω) < 1
    · exact ⟨_, hp, Nat.minFac_dvd n, h⟩
    · have h1 : A.valuation ((n.minFac : ℕ) : Ω) = 1 :=
        le_antisymm (ReciprocityTheory.Gal.valuation_natCast_le_one A _) (not_lt.1 h)
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact hn (by simpa using hm)
      have hlt : m < n := by
        have h2 := hp.two_le
        have h3 := Nat.pos_of_ne_zero hm0
        nlinarith [hm]
      have hvm : A.valuation (m : Ω) < 1 := by
        have e : A.valuation ((n : ℕ) : Ω) = A.valuation ((n.minFac : ℕ) : Ω) * A.valuation (m : Ω) := by
          rw [← map_mul, ← Nat.cast_mul, ← hm]
        rwa [e, h1, one_mul] at hv
      obtain ⟨r, hr, hrm, hrv⟩ := ih m hlt hm0 hvm
      exact ⟨r, hr, hrm.trans ⟨n.minFac, by rw [mul_comm]; exact hm⟩, hrv⟩

private theorem normV_pos' {F : Type} [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) : 0 < normV t := by
  haveI : Finite (𝓞 F ⧸ t.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ t.ne_bot
  exact Nat.card_pos

private theorem normV_mem {F : Type} [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) :
    ((normV t : ℕ) : 𝓞 F) ∈ t.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  simpa [normV, nsmul_eq_mul] using card_nsmul_eq_zero' (G := 𝓞 F ⧸ t.asIdeal) (x := 1)

private theorem exists_place_of_prime {K : Type} [Field K] [NumberField K] {q : ℕ} (hq : q.Prime) :
    ∃ u : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ u.asIdeal := by
  have hne : Ideal.span {((q : ℕ) : 𝓞 K)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro h
    have h2 := h.map (Algebra.norm ℤ (S := 𝓞 K))
    rw [show ((q : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (q : ℤ) by simp, Algebra.norm_algebraMap,
      isUnit_pow_iff Module.finrank_pos.ne'] at h2
    exact (Nat.prime_iff_prime_int.1 hq).not_unit h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hq0 : ((q : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have hmem := hle (Ideal.mem_span_singleton_self ((q : ℕ) : 𝓞 K))
  exact ⟨⟨M, hM.isPrime, fun h => hq0 (by rwa [h, Ideal.mem_bot] at hmem)⟩, hmem⟩

private theorem exists_moves {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {q : ℕ} (hq : q.Prime) (h2 : 2 < q) (hB : ∀ w : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∉ w.asIdeal ^ 2)
    {x : Ω} (hx : x ^ 2 = ((q : ℕ) : Ω)) :
    ∃ (u : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω), ((q : ℕ) : 𝓞 K) ∈ u.asIdeal ∧ IsPlaceOver A u ∧
      ∃ σ ∈ Ine (F := K) A, σ x = -x := by
  obtain ⟨u, hu⟩ := exists_place_of_prime (K := K) hq
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨σ, hσ, h⟩ := GlobalTheory.TameKummerInertia.tame_kummer_surj K Ω A u hA q hu (hB u) 2 two_pos
    (fun hd => by have := Nat.le_of_dvd two_pos hd; omega) x (-1) hx (by norm_num)
  exact ⟨u, A, hu, hA, σ, hσ, by rw [h]; ring⟩

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.quad0Ex :
    SqrtFix → MkQ → UnrLarge → Quad0Ex := by
  intro hS hM hU E Ω _ _ _ _ _ _ T hT
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  obtain ⟨E', hfin, hE'⟩ : ∃ E' : IntermediateField ℚ Ω, FiniteDimensional ℚ E' ∧
      ∀ (j : E →+* Ω) (y : E), j y ∈ E' :=
    ⟨IntermediateField.normalClosure ℚ E Ω, inferInstance,
      fun j y => AlgHom.fieldRange_le_normalClosure j.toRatAlgHom ⟨y, rfl⟩⟩
  haveI : NumberField E' := { }
  haveI : IsAlgClosure E' Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  obtain ⟨B1, hB1⟩ := hU E
  obtain ⟨B2, hB2⟩ := hU E'
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = ∏ t ∈ hT.toFinset, normV t := ⟨_, rfl⟩
  have hc0 : 0 < c := hc ▸ Finset.prod_pos fun t _ => normV_pos' t
  have hcd : ∀ t ∈ T, normV t ∣ c := fun t ht => hc ▸ Finset.dvd_prod_of_mem _ (hT.mem_toFinset.2 ht)
  obtain ⟨q, hq, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one (k := 8 * c) (max (max B1 B2) (max c 2)) (by omega)
  simp only [max_lt_iff] at hgt
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hgt
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((q : ℕ) : Ω) two_pos
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : ((q : ℕ) : Ω) = 0 := by rw [← hx]; simp
    exact hq.ne_zero (Nat.cast_eq_zero.1 this)
  have hneg : -x ≠ x := fun h => hx0 (by
    have : (2 : Ω) * x = 0 := by linear_combination -h
    simpa using this)
  obtain ⟨u', A', _, _, σ', hσ', hσ'x⟩ := exists_moves (K := E') hq h4 (hB2 q hq h2) hx
  obtain ⟨u, A, huq, hA, τ, hτ, hτx⟩ := exists_moves (K := E) hq h4 (hB1 q hq h1) hx
  have hxZ : x ^ 2 = (((q : ℕ) : ℤ) : Ω) := by rw [hx]; simp
  obtain ⟨Q, hxQ, hspan, hfix⟩ := hM E Ω x (q : ℤ) hxZ ⟨τ, by rw [hτx]; exact hneg⟩
  have hfixT : ∀ (F : Type) [Field F] [NumberField F] [Algebra F Ω], ∀ t ∈ T, ∀ A : ValuationSubring Ω,
      IsPlaceOver A t → ∀ g ∈ Dec (F := F) A, g x = x := by
    intro F _ _ _ t ht A hA g hg
    have hv : A.valuation ((normV t : ℕ) : Ω) < 1 := by
      have := (hA _).2 (normV_mem t)
      simpa using this
    obtain ⟨r, hr, hrd, hrv⟩ := exists_prime_val A _ (normV_pos' t).ne' hv
    refine (hS F Ω A x q hxZ).1 r hr hrv ?_ g hg
    have h8 : 8 * r ∣ 8 * c := Nat.mul_dvd_mul_left 8 (hrd.trans (hcd t ht))
    exact (Int.natCast_dvd_natCast.2 h8).trans (Nat.modEq_iff_dvd.1 hmod.symm)
  have hs1 : ∀ (j : E →+* Ω) (y : E), σ'.toRingEquiv (j y) = j y := fun j y => by
    simpa using σ'.commutes (⟨j y, hE' j y⟩ : E')
  have huT : u ∉ T := by
    intro ht
    have hle : normV u ≤ c := Nat.le_of_dvd hc0 (hcd u ht)
    have hcop : Nat.Coprime q (normV u) :=
      (Nat.Prime.coprime_iff_not_dvd hq).2 fun hd => by
        have := Nat.le_of_dvd (normV_pos' u) hd
        omega
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : (a : 𝓞 E) * ((q : ℕ) : 𝓞 E) + (b : 𝓞 E) * ((normV u : ℕ) : 𝓞 E) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hab
    have hmem : (1 : 𝓞 E) ∈ u.asIdeal := by
      rw [← h1]
      exact add_mem (Ideal.mul_mem_left _ _ huq) (Ideal.mul_mem_left _ _ (normV_mem u))
    exact (Ideal.ne_top_iff_one _).1 u.isPrime.ne_top hmem
  refine ⟨Q, ⟨⟨x, hxQ⟩, ⟨⟨q, hq.pos, ?_⟩, hspan, σ'.toRingEquiv, hs1, hσ'x⟩, ?_⟩, ?_, u, huT, A, hA, τ, hτ, ?_⟩
  · apply Subtype.ext
    simpa using hx
  · intro t ht A hA g hg
    exact hfixT _ t ht A hA g hg
  · intro t ht A hA g hg
    exact hfix E g (fun y => g.commutes y) (hfixT E t ht A hA g hg)
  · intro hf
    have := hf ⟨x, hxQ⟩
    exact hneg (hτx.symm.trans this)
end
