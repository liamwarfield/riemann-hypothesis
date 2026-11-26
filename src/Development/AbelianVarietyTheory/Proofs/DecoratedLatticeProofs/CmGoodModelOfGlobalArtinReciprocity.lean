module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedStatus
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJInt
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFixJ
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModInertKur
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgClose
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorStatus
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmLatticeGoodModelUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmLatticeGoodModelUnramified
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField ReciprocityTheory.ChartRestriction.L1

namespace GlobalTheory.ArtinClassCM

theorem inertia_fixes (hW : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E), IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧ (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v → IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) (hC : ChebOmSt)
    {d : ℕ} {L : PeriodPair} (hsf : Squarefree d) (hd : d % 4 = 3) (hL : HasCMBy d L)
    (x : Om d) (hx : (x : ℂ) = jInv L) (B : ValuationSubring (Om d)) (σ : Om d ≃ₐ[KQ d] Om d) (hσ : InertiaEl B σ) :
    σ x = x := by
  obtain ⟨art, hop, hin, hfrob⟩ := hW (KQ d) (Om d)
  have hxi : IsIntegral ℤ x := by
    obtain ⟨y, hy, hyi⟩ := exists_Om d (cm1 d L hsf hd hL)
    have : y = x := Subtype.ext (hy.trans hx.symm)
    rwa [this] at hyi
  obtain ⟨P, hP, hPx⟩ := hxi
  have hxs : x ∈ fixJRoots (Ω := Om d) P := by
    rw [mem_fixJRoots hP]
    rwa [show algebraMap ℤ (Om d) = Int.castRingHom (Om d) from RingHom.ext_int _ _] at hPx
  obtain ⟨n, hn0, hn⟩ := sepInt (fixJRoots (Ω := Om d) P) (fun r hr => isIntegral_of_mem_fixJRoots hP hr)
  set S : Set (HeightOneSpectrum (𝓞 (KQ d))) := {v | (n : 𝓞 (KQ d)) ∈ v.asIdeal} with hS
  have hSfin : S.Finite := finite_places (KQ d) hn0

  have key : ∀ (A : ValuationSubring (Om d)) (v : HeightOneSpectrum (𝓞 (KQ d))), LiesAbove A v → v ∉ S →
      ∀ r ∈ fixJRoots (Ω := Om d) P, ∀ r' ∈ fixJRoots (Ω := Om d) P, r - r' ∈ A.nonunits → r = r' := by
    intro A v hA hv r hr r' hr' h
    by_contra hne
    have h1 := hn r hr r' hr' hne A h
    apply hv
    rw [hS, Set.mem_ofPred_eq, ← hA]
    simpa using h1
  set H : Subgroup (Om d ≃ₐ[KQ d] Om d) := art.ker ⊓ fixJStab (KQ d) (Om d) P with hH
  have := fixJStab_normal (E := KQ d) (Ω := Om d) hP
  have hHn : H.Normal := inferInstance
  have hHo : IsOpen (H : Set (Om d ≃ₐ[KQ d] Om d)) := by
    rw [hH, Subgroup.coe_inf]
    exact hop.inter fixJStab_isOpen
  obtain ⟨A, v, φ, hA, hv, hp, hφ, hσφ⟩ := hC (KQ d) (Om d) S hSfin H hHn hHo (by
    intro A v hA hv g hg
    refine ⟨hin A g hg, fun r hr => ?_⟩
    exact key A v hA hv _ (map_mem_fixJRoots hP g hr) _ hr
      (hg.2 r (mem_of_isIntegral A (isIntegral_of_mem_fixJRoots hP hr)))) σ
  have hσ1 : art σ = 1 := hin B σ hσ
  have hφ1 : art φ = 1 := by
    have : σ⁻¹ * φ ∈ art.ker := hσφ.1
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσ1, inv_one, one_mul] at this
    exact this
  have hcl := hfrob v A φ hA hφ
  rw [hφ1] at hcl
  have h1 := frobCong hsf hd hL x hx A v hA hp hcl.symm
  have h2 := hφ.2 x (mem_of_isIntegral A (isIntegral_of_mem_fixJRoots hP hxs))
  have h3 : φ x - x ∈ A.nonunits := by
    have := fixJ_nonunits_add A h2 h1
    simpa using this
  have h4 : φ x = x := key A v hA hv _ (map_mem_fixJRoots hP φ hxs) _ hxs h3
  have h5 := hσφ.2 x hxs
  rw [AlgEquiv.mul_apply, h4] at h5
  calc σ x = σ (σ⁻¹ x) := by rw [h5]
    _ = x := by rw [← AlgEquiv.mul_apply, mul_inv_cancel]; rfl

theorem good_model (hW : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E), IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧ (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v → IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) (hC : ChebOmSt) : CM2 := by
  refine goodReduction_of_integral_unramified jInt ?_
  intro d L hsf hd hL l _ hl hld ι
  obtain ⟨x, hx, -⟩ := exists_Om d (cm1 d L hsf hd hL)
  rw [← hx]
  exact inertKur (by omega) hld ι x fun σ hσ => inertia_fixes hW hC hsf hd hL x hx _ σ hσ

end GlobalTheory.ArtinClassCM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmLatticeGoodModelUnramifiedStatement
open NumberField IsDedekindDomain Neutral.HilbertClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLattice_good_model_unramified : (∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E), IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧ (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v → IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) → ReciprocityTheory.ChartRestriction.L1.ChebOmSt → Formalism.L2.Th1.CM.CM2 := by
  first | exact @GlobalTheory.ArtinClassCM.good_model | exact GlobalTheory.ArtinClassCM.good_model | (intros; apply GlobalTheory.ArtinClassCM.good_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdealClassArtinSymbolOfGlobalArtin
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdealClassArtinSymbolOfGlobalArtin
open NumberField IsDedekindDomain Neutral.HilbertClassField

open Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.IdealArtinSymbol

theorem exists_artinSymbol : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E),
      IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧
      (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧
      ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v →
        IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  intro H E Ω _ _ _ _ _
  obtain ⟨art, ha⟩ := H E Ω
  obtain ⟨cl, hclo, hclk, hunit, hunif⟩ := GlobalTheory.T.exists_ideleClassGroupHom_open_kernel E
  have hker : art.ker ≤ cl.ker := by
    rw [ha.ker]
    exact Subgroup.topologicalClosure_minimal _ hclk (Subgroup.isClosed_of_isOpen _ hclo)
  let ρ := art.liftOfSurjective ha.quot.surjective ⟨cl, hker⟩
  have hρ : ∀ x, ρ (art x) = cl x := fun x => art.liftOfRightInverse_comp_apply _ _ ⟨cl, hker⟩ x
  have hρo : IsOpen (ρ.ker : Set (Gab E Ω)) := by
    rw [← ha.quot.isQuotientMap.isOpen_preimage]
    convert hclo using 1
    ext x
    rw [Set.mem_preimage, SetLike.mem_coe, SetLike.mem_coe, MonoidHom.mem_ker, hρ, MonoidHom.mem_ker]
  let ψ : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E) := ρ.comp (toAb E Ω)
  have hlies : ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), LiesAbove A v → Formalism.ConjugateSelfDual.IsPlaceOver A v :=
    fun v A h x => by rw [← h x, A.mem_nonunits_iff]
  refine ⟨ψ⁻¹, ?_, ?_, ?_⟩
  · have e : ((ψ⁻¹).ker : Set (Ω ≃ₐ[E] Ω)) = toAb E Ω ⁻¹' (ρ.ker : Set (Gab E Ω)) := by
      ext σ
      simp [ψ, MonoidHom.mem_ker]
    rw [e]
    exact hρo.preimage QuotientGroup.continuous_mk
  · intro A g hg
    rcases GlobalTheory.T.inertiaElement_eq_one_or_liesAbove_finitePlace E Ω A g hg with rfl | ⟨v, hv⟩
    · exact map_one _
    have hI : g ∈ Ine (F := E) A := ⟨hg.1, fun x hx => by
      rw [← A.mem_nonunits_iff]
      exact hg.2 x ((A.valuation_le_one_iff x).1 hx)⟩
    obtain ⟨x, _, hx⟩ := (ha.ine v A (hlies v A hv) (toAb E Ω g)).2 ⟨g, hI, rfl⟩
    have : ψ g = 1 := by
      show ρ (toAb E Ω g) = 1
      rw [← hx, hρ]
      exact hunit v x ‹_›
    rw [MonoidHom.inv_apply, this, inv_one]
  · intro v A φ hv hφ
    have hF : IsFrob (F := E) A (normV v) φ := ⟨hφ.1, fun x hx => by
      rw [← A.mem_nonunits_iff]
      exact hφ.2 x ((A.valuation_le_one_iff x).1 hx)⟩
    obtain ⟨x, hxu, hx⟩ := (ha.frob v A (hlies v A hv) (toAb E Ω φ⁻¹)).2 ⟨φ, hF, rfl⟩
    rw [MonoidHom.inv_apply, ← map_inv]
    show ρ (toAb E Ω φ⁻¹) = _
    rw [← hx, hρ]
    exact hunif v x hxu

end GlobalTheory.IdealArtinSymbol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdealClassArtinSymbolOfGlobalArtinStatement
open NumberField IsDedekindDomain Neutral.HilbertClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idealClass_artinSymbol_of_globalArtin : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], ∃ art : (Ω ≃ₐ[E] Ω) →* ClassGroup (𝓞 E), IsOpen (art.ker : Set (Ω ≃ₐ[E] Ω)) ∧ (∀ (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → art g = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (φ : Ω ≃ₐ[E] Ω), LiesAbove A v → IsArithFrobenius A v φ → art φ = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  first | exact @GlobalTheory.IdealArtinSymbol.exists_artinSymbol | exact GlobalTheory.IdealArtinSymbol.exists_artinSymbol | (intros; apply GlobalTheory.IdealArtinSymbol.exists_artinSymbol <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChebotarevDegreeOneValuationSubrings
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChebotarevDegreeOneValuationSubrings
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory

theorem chebOmSt_holds : ReciprocityTheory.ChartRestriction.L1.ChebOmSt := by
  intro E Ω _ _ _ _ _ S hS H hn ho _ σ
  obtain ⟨v, hv, hd, -, B, hB, -, φ, hφ, hφσ⟩ := GlobalTheory.Published.cheb_holds E Ω H ho hn σ hS.toFinset
  refine ⟨B, v, φ, ?_, by simpa using hv, ?_, ?_, ?_⟩
  · intro x
    rw [ValuationSubring.mem_nonunits_iff]
    exact hB x
  · have := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hd
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
  · refine ⟨hφ.1, fun x hx => ?_⟩
    rw [ValuationSubring.mem_nonunits_iff]
    exact hφ.2 x ((B.valuation_le_one_iff x).2 hx)
  · have := hn.conj_mem _ hφσ σ⁻¹
    simpa [mul_assoc] using this

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChebotarevDegreeOneValuationSubringsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chebotarev_degreeOne_valuationSubrings : ReciprocityTheory.ChartRestriction.L1.ChebOmSt := by
  first | exact @GlobalTheory.chebOmSt_holds | exact GlobalTheory.chebOmSt_holds | (intros; apply GlobalTheory.chebOmSt_holds <;> assumption)
end
end

namespace GlobalTheory.Corev.CmTwoClosing

theorem cmGoodModel_of_globalArtinReciprocity (hA : GlobalTheory.Published.GlobalArtinReciprocity) : Formalism.L2.Th1.CM.CM2 :=
  GlobalTheory.T.cmLattice_good_model_unramified (GlobalTheory.T.exists_idealClass_artinSymbol_of_globalArtin hA) GlobalTheory.T.chebotarev_degreeOne_valuationSubrings

end GlobalTheory.Corev.CmTwoClosing
