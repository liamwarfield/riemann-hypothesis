module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RestrictsSelf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTorusEigenformOfCompactTorusEigenvector
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.ReindexedFiltrationComparison
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBlockGeneratorsLagrangianNormalF

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtension
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL
section
variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]

theorem comap_eq_of_placeOver {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}
    (h : IsPlaceOver A v) (h' : IsPlaceOver A v') :
    v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal := by
  ext x
  rw [Ideal.mem_comap, ← h x, ← h' (algebraMap (𝓞 K) (𝓞 L) x)]
  have : ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (x : K) := rfl
  rw [this, ← IsScalarTower.algebraMap_apply]

end

theorem normV_eq_pow {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L))
    (hc : v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal) :
    ∃ f : ℕ, normV v' = normV v ^ f := by
  classical
  haveI := v.isMaximal
  haveI := v'.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field _
  letI : Field (𝓞 L ⧸ v'.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  haveI : Finite (𝓞 L ⧸ v'.asIdeal) := v'.asIdeal.finiteQuotientOfFreeOfNeBot v'.ne_bot
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  letI : Fintype (𝓞 L ⧸ v'.asIdeal) := Fintype.ofFinite _
  letI : Algebra (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ v'.asIdeal) :=
    (Ideal.quotientMap v'.asIdeal (algebraMap (𝓞 K) (𝓞 L)) hc.ge).toAlgebra
  refine ⟨Module.finrank (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ v'.asIdeal), ?_⟩
  simp only [normV, Nat.card_eq_fintype_card]
  exact Module.card_eq_pow_finrank
end GlobalTheory.AboveL

namespace GlobalTheory.AboveL
section
variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]

theorem restrictScalars_mem_Dec {A : ValuationSubring Ω} {σ : G L Ω} (hσ : σ ∈ Dec (F := L) A) :
    (σ.restrictScalars K : G K Ω) ∈ Dec (F := K) A := hσ

theorem actsAs_restrictScalars {A : ValuationSubring Ω} {σ : G L Ω} {q f a b : ℕ} (hσ : ActsAs A (q ^ f) σ a b) :
    ActsAs A q (σ.restrictScalars K : G K Ω) (f * a) (f * b) := by
  refine ⟨restrictScalars_mem_Dec hσ.1, fun x hx => ?_⟩
  have := hσ.2 x hx
  rw [← pow_mul, ← pow_mul] at this
  exact this

theorem restrictScalars_mem_Ine_iff {A : ValuationSubring Ω} {σ : G L Ω} :
    (σ.restrictScalars K : G K Ω) ∈ Ine (F := K) A ↔ σ ∈ Ine (F := L) A := Iff.rfl

end

theorem exists_weil_restrict : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ' : Weil h'), ∃ σ : Weil h, (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) ∧ (deg σ = 0 ↔ deg σ' = 0) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' σ'
  obtain ⟨f, hf⟩ := normV_eq_pow v v' (comap_eq_of_placeOver h h')
  obtain ⟨a, b, hab⟩ := (mem_Weil h').mp σ'.2
  rw [hf] at hab
  refine ⟨⟨(σ' : G L Ω).restrictScalars K, (mem_Weil h).mpr ⟨_, _, actsAs_restrictScalars hab⟩⟩, fun z => rfl, ?_⟩
  rw [deg_eq_zero_iff, deg_eq_zero_iff]
  exact restrictScalars_mem_Ine_iff
end GlobalTheory.AboveL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtensionStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilGroup_restrict_extension : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ' : Weil h'), ∃ σ : Weil h, (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) ∧ (deg σ = 0 ↔ deg σ' = 0) := by
  first | exact @GlobalTheory.AboveL.exists_weil_restrict | exact GlobalTheory.AboveL.exists_weil_restrict | (intros; apply GlobalTheory.AboveL.exists_weil_restrict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalVacuumOfIsLatticeVacuumCoprimeLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalVacuumOfIsLatticeVacuumCoprimeLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacLat
variable {D : D7}

theorem under_eq_of_delta {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : GlobalTheory.IdemSupport.Comp D Φ)
    {P : Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (h1 : Φ (algebraMap (AF D.host.F) (AE D) ε) P ≠ 0) : P.under (𝓞 D.host.F) = v := by
  by_contra hne
  exact h1 ((GlobalTheory.IdemSupport.place_comp hΦ hε).2.2 P hne)

theorem place_of_primeIdem {P : Pl D.host.E} {e f : AE D} (h : IsPrimeIdem P e f) :
    ∃ v ε, IsPlaceIdem D v ε ∧ f = algebraMap (AF D.host.F) (AE D) ε ∧ P.under (𝓞 D.host.F) = v := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hff := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents D.sp.X').2.2.1 P e f h).1
  rcases h with ⟨hid, rfl⟩ | ⟨rfl, ⟨v, ε, hε, rfl⟩, hT⟩
  · obtain ⟨h1, h2, v, ε, hε, hsum⟩ := hid.1
    refine ⟨v, ε, hε, hsum, under_eq_of_delta hΦ hε ?_⟩
    have hinf : infPart D e = 0 := by
      have : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
      rw [this, map_mul, hsum, (GlobalTheory.IdemSupport.place_comp hΦ hε).1, mul_zero]
    have hd := (GlobalTheory.IdemSupport.tie_iff hΦ h1 hinf P).1 hid.2
    have hc0 : Φ (cA D e) P = 0 := by
      have := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) e (cA D e) P
      rw [h2, GlobalTheory.IdemSupport.ev_zero, hd.2.1, one_mul] at this
      exact this.symm
    rw [← hsum, GlobalTheory.IdemSupport.ev_add, hd.2.1, hc0, add_zero]
    exact one_ne_zero
  · refine ⟨v, ε, hε, rfl, under_eq_of_delta hΦ hε ?_⟩
    have hd := (GlobalTheory.IdemSupport.tie_iff hΦ hff (GlobalTheory.IdemSupport.place_comp hΦ hε).1 P).1 hT
    rw [hd.2.1]; exact one_ne_zero
end GlobalTheory.VacLat

namespace GlobalTheory.VacLat
variable {D : D7}

theorem two_not_mem {P : Pl D.host.E} {e : AE D} (he : GlobalTheory.IdemSupport.Comparison₂ P e) (hc : cA D e = e) (hi : e * e = e)
    (h0 : infPart D e = 0) : ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hd := (GlobalTheory.IdemSupport.tie_iff hΦ hi h0 P).1 he
  have hd' := GlobalTheory.IdemSupport.delta_conj hΦ hd
  rw [hc] at hd'
  have hPP : GlobalTheory.IdemSupport.cP P = P := by
    by_contra hne
    have := hd.2.2 _ hne
    rw [hd'.2.1] at this
    exact one_ne_zero this
  intro h2
  refine Formalism.MainNotions.KudlaSiegelWeil.InertConditionsOfHost.not_fixed_ram D P 2 (Or.inl rfl) h2 (Ideal.ext fun x => ?_)
  rw [Ideal.mem_comap]
  have : Formalism.MainNotions.KudlaSiegelWeil.InertConditionsOfHost.sgO D x = GlobalTheory.IdemSupport.cO D x := by
    apply RingOfIntegers.ext
    rw [GlobalTheory.IdemSupport.cO_coe, GlobalTheory.SplitIdem.star_eq_conj]
    rfl
  rw [this, ← GlobalTheory.IdemSupport.mem_cP, hPP]

theorem unit_factor {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) (M : ℕ)
    (hM : (M : 𝓞 D.host.F) ∉ v.asIdeal) :
    ∃ γ ∈ intAf D.host.F, ε = pairA D.host.F 0 ((M : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * γ) := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  have hM0 : (M : D.host.F) ≠ 0 := by
    intro h
    apply hM
    have : (M : 𝓞 D.host.F) = 0 := by
      apply RingOfIntegers.ext; simpa using h
    rw [this]; exact zero_mem _
  refine ⟨α * algebraMap D.host.F _ ((M : D.host.F)⁻¹), fun w => ?_, ?_⟩
  · rw [map_mul, AlgHom.commutes]
    by_cases hw : w = v
    · subst hw
      rw [h1, one_mul]
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap, map_inv₀]
      have : HeightOneSpectrum.valuation D.host.F w (M : D.host.F) = 1 := by
        rw [← map_natCast (algebraMap (𝓞 D.host.F) D.host.F) M, HeightOneSpectrum.valuation_of_algebraMap]
        exact HeightOneSpectrum.intValuation_eq_one_iff.2 hM
      rw [this, inv_one]
    · rw [h0 w hw, zero_mul]; exact zero_mem _
  · congr 1
    rw [← mul_assoc, mul_comm _ α, mul_assoc, ← map_natCast (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) M,
      ← map_mul, mul_inv_cancel₀ hM0, map_one, mul_one]
end GlobalTheory.VacLat

namespace GlobalTheory.VacLat
variable {D : D7}

theorem intAf_mul {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F} (hx : x ∈ intAf D.host.F) (hy : y ∈ intAf D.host.F) :
    x * y ∈ intAf D.host.F := fun w => by
  rw [map_mul]; exact mul_mem (hx w) (hy w)

theorem pairA_mul (x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) :
    pairA D.host.F 0 x * pairA D.host.F 0 y = pairA D.host.F 0 (x * y) := by
  exact Prod.ext (zero_mul _) rfl

theorem pairA_smul (a : D.host.F) (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) :
    pairA D.host.F 0 (algebraMap D.host.F _ a * x) = a • pairA D.host.F 0 x := by
  refine Prod.ext ?_ ?_
  · exact (smul_zero a).symm
  · exact (Algebra.smul_def a x).symm

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem lat_scale (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (NS NT c : ℕ)
    (hS : ∀ x ∈ L0c D S, (NS : D.host.E) • x ∈ ΛS) (hT : ∀ x ∈ L0c D T, (NT : D.host.E) • x ∈ ΛT)
    (γ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (hγ : γ ∈ intAf D.host.F) (u : WO S T)
    (hu : u ∈ latO S T (L0c D S) (L0c D T) fun _ => True) :
    ∃ u' ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      ∀ i j, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (((c * NS * NT : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * γ)) * u i j =
        (c • u') i j := by
  set a₀ := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (((c * NS * NT : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * γ)) with ha₀
  let φ : WO S T →+ WO S T := DistribSMul.toAddMonoidHom (WO S T) a₀
  let ψc : WO S T →+ WO S T := DistribSMul.toAddMonoidHom (WO S T) c
  have key : latO S T (L0c D S) (L0c D T) (fun _ => True) ≤
      ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True)).map ψc).comap φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    refine ⟨Matrix.of fun i j => (pairA D.host.F 0 (γ * α)) ⊗ₜ[D.host.F]
        (a * ((NT : D.host.E) • t) i * ∑ k, star (((NS : D.host.E) • s) k) * S.gram k j),
      AddSubgroup.subset_closure ⟨γ * α, intAf_mul hγ hα, fun v hv => (hv trivial).elim, a, ha, _, hS s hs, _, hT t ht, rfl⟩, ?_⟩
    ext i j
    simp only [ψc, φ, DistribSMul.toAddMonoidHom_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Pi.smul_apply]
    rw [ha₀, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      Algebra.algebraMap_self, RingHom.id_apply, pairA_mul, mul_assoc (((c * NS * NT : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) γ α, ← map_natCast (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)),
      pairA_smul, ← TensorProduct.smul_tmul', ← TensorProduct.tmul_smul, ← TensorProduct.tmul_smul]
    congr 1
    rw [nsmul_eq_mul, Algebra.smul_def, map_natCast]
    simp only [star_mul', star_natCast, Nat.cast_mul]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  obtain ⟨u', hu', he⟩ := key hu
  exact ⟨u', hu', fun i j => (congrFun (congrFun he i) j).symm⟩
end GlobalTheory.VacLat

namespace GlobalTheory.VacLat

theorem isVacAt_of_isLatVac : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) ΛS ΛT (NS NT : ℕ), IsBaseFrame S βS ΛS NS → IsBaseFrame T βT ΛT NT → ∀ P : Pl D.host.E, ((NS * NT : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ f₀, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ → IsVacAt ψ S T P f₀ := by
  intro D ψ S T βS βT ΛS ΛT NS NT hS hT P hP f₀ hth hvac
  refine ⟨hth, fun e f' he u hu hhalf => ?_⟩
  have hNS : (NS : 𝓞 D.host.E) ∉ P.asIdeal := fun h => hP (by rw [Nat.cast_mul]; exact P.asIdeal.mul_mem_right _ h)
  have hNT : (NT : 𝓞 D.host.E) ∉ P.asIdeal := fun h => hP (by rw [Nat.cast_mul]; exact P.asIdeal.mul_mem_left _ h)
  obtain ⟨v, ε, hε, hf, hv⟩ := place_of_primeIdem he
  have hff := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents S).2.2.1 P e f' he).1
  have hunder : ∀ c : ℕ, (c : 𝓞 D.host.E) ∉ P.asIdeal → ((c * NS * NT : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
    intro c hc h
    rw [← hv] at h
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal at h
    rw [map_natCast, Nat.cast_mul, Nat.cast_mul] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · rcases P.isPrime.mem_or_mem h with h | h
      · exact hc h
      · exact hNS h
    · exact hNT h
  rcases he with ⟨hid, rfl⟩ | ⟨hfe, -, hTie⟩
  · have hfu : ∀ i j, (e + cA D e) * u i j = u i j := by
      have h1 := hid.1.1
      have h2 := hid.1.2.1
      have h3 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
      have h4 : cA D e * e = 0 := by rw [mul_comm]; exact h2
      rcases hhalf with h | h <;> intro i j
      · have h' : e * u i j = u i j := h i j
        rw [← h', ← mul_assoc, add_mul, h1, h4, add_zero]
      · have h' : cA D e * u i j = u i j := h i j
        rw [← h', ← mul_assoc, add_mul, h2, h3, zero_add]
    obtain ⟨γ, hγ, hεγ⟩ := unit_factor hε (1 * NS * NT) (hunder 1 (by rw [Nat.cast_one]; exact fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)))
    obtain ⟨u', hu', heq⟩ := lat_scale S T ΛS ΛT NS NT 1 hS.2.2.2.1 hT.2.2.2.1 γ hγ u hu
    have hue : u = u' := by
      ext i j
      rw [← hfu i j, hf, hεγ, heq, one_smul]
    subst hue
    rcases hhalf with h | h
    · exact hvac.2 e hid.1 u hu' h
    · refine hvac.2 (cA D e) ⟨by rw [← map_mul, hid.1.1], by rw [cA_cA, mul_comm]; exact hid.1.2.1, ?_⟩ u hu' h
      obtain ⟨w, η, hη, hwη⟩ := hid.1.2.2
      exact ⟨w, η, hη, by rw [cA_cA, add_comm]; exact hwη⟩
  · have hf' : e = algebraMap (AF D.host.F) (AE D) ε := hfe.symm.trans hf
    have hc : cA D e = e := by rw [hf']; exact GlobalTheory.IdemSupport.cA_algebraMap ε
    have hi : e * e = e := hfe ▸ hff
    have h0 : infPart D e = 0 := by
      obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
      rw [hf']; exact (GlobalTheory.IdemSupport.place_comp hΦ hε).1
    have h2 := two_not_mem hTie hc hi h0
    have hfu : ∀ i j, e * u i j = u i j := by
      rcases hhalf with h | h
      · exact fun i j => h i j
      · rw [hc] at h; exact fun i j => h i j
    obtain ⟨γ, hγ, hεγ⟩ := unit_factor hε (2 * NS * NT) (hunder 2 h2)
    obtain ⟨u', hu', heq⟩ := lat_scale S T ΛS ΛT NS NT 2 hS.2.2.2.1 hT.2.2.2.1 γ hγ u hu
    have hue : u = 2 • u' := by
      ext i j
      rw [← hfu i j, hf', hεγ, heq]
    rw [hue]
    exact hvac.1 u' hu'

end GlobalTheory.VacLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalVacuumOfIsLatticeVacuumCoprimeLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalVacuum_of_isLatticeVacuum_coprime_level : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) ΛS ΛT (NS NT : ℕ), IsBaseFrame S βS ΛS NS → IsBaseFrame T βT ΛT NT → ∀ P : Pl D.host.E, ((NS * NT : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ f₀, IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ → IsVacAt ψ S T P f₀ := by
  first | exact @GlobalTheory.VacLat.isVacAt_of_isLatVac | exact GlobalTheory.VacLat.isVacAt_of_isLatVac | (intros; apply GlobalTheory.VacLat.isVacAt_of_isLatVac <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLocCharUnit
noncomputable section

namespace GlobalTheory.ColPeriod.Scal

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver IsFrames)

variable {X : Fields} {Pr : Primes X}

theorem g_mem_of_vG (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
  rw [← hPr.piG_norm i]
  exact P.asIdeal.mul_mem_left _ (GlobalTheory.ColPeriod.mem_divs h)

theorem g_notMem_of_vGs (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vGs) (h' : P ∉ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  have h2 : ∃ k, P ∈ Pr.vG k := by
    rcases Finset.mem_union.1 h with h2 | h2
    exacts [⟨0, h2⟩, ⟨1, h2⟩]
  obtain ⟨k, hk⟩ := h2
  have hne : Pr.g i ≠ Pr.g k := by
    have h0 := hPr.g_ne
    fin_cases i <;> fin_cases k
    · exact absurd hk h'
    · exact h0
    · exact h0.symm
    · exact absurd hk h'
  exact natCast_notMem_of_ne (hPr.g_prime i) (hPr.g_prime k) hne P (g_mem_of_vG hPr hk)

theorem under_conjP (hX : X.Ok) (Q : HeightOneSpectrum (𝓞 X.E)) :
    (conjPrime₂ Q).asIdeal.under (𝓞 X.F) = Q.asIdeal.under (𝓞 X.F) := by
  ext r
  have e : cO X.E (algebraMap (𝓞 X.F) (𝓞 X.E) r) = algebraMap (𝓞 X.F) (𝓞 X.E) r :=
    RingOfIntegers.ext (hX.star_F (r : X.F))
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, mem_conjP, e]

variable {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem g_notMem_sel (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) {v : HeightOneSpectrum (𝓞 X.F)}
    (hv : ¬ ∃ P ∈ rowSG Pr sel mu, P.asIdeal.under (𝓞 X.F) = v.asIdeal) (k : Fin 2) :
    ((Pr.g k : ℕ) : 𝓞 X.E) ∉ (sel v).asIdeal := by
  classical
  intro h
  have hsub : ∀ Q, Q ∈ Pr.vG k → Q ∈ rowSG Pr sel mu := fun Q hQ => Finset.mem_union_left _ (by
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases k
    exacts [Or.inl hQ, Or.inr hQ])
  have h0 : X.conjO (Pr.piG k) ≠ 0 := by
    refine right_ne_zero_of_mul (a := Pr.piG k) ?_
    rw [hPr.piG_norm k]
    exact_mod_cast (hPr.g_prime k).ne_zero
  rw [← hPr.piG_norm k] at h
  rcases (sel v).isPrime.mem_or_mem h with h | h
  · refine hv ⟨conjPrime₂ (sel v), hsub _ ((Formalism.L2.Col.mem_divs h0 _).2 ?_), by rw [under_conjP hX, hsel v]⟩
    rw [mem_conjP]
    exact (cO_cO (Pr.piG k)).symm ▸ h
  · exact hv ⟨sel v, hsub _ ((Formalism.L2.Col.mem_divs h0 _).2 h), hsel v⟩

theorem val_locChar_unit {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (P : HeightOneSpectrum (𝓞 E)) (cq : K) (ψ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (ha : P.valuation E a = 1) :
    w.valuation K (LocE.locChar (qOf P) cq ψ a) = 1 := by
  have hu := GlobalTheory.LocCharVal.isUnit_redP P _ ha
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  rw [GlobalTheory.LastSteps.locChar_unit _ _ hu, LocE.unitV, dite_eq_left hu]
  exact GlobalTheory.CharVal.unit_of_finOrder (MonoidHom.isOfFinOrder ψ (isOfFinOrder_of_finite _))

theorem val_locChar {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
    (P : HeightOneSpectrum (𝓞 E)) {cq : K} (ψ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    (hc : w.valuation K cq = 1) {a : E} (ha : a ≠ 0) : w.valuation K (LocE.locChar (qOf P) cq ψ a) = 1 := by
  obtain ⟨z, ζ, hζ, e⟩ := GlobalTheory.LocCharVal.locChar_eq_zpow_mul E K P (qOf P) cq ψ a
    (GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _) hq) ha
  rw [e, map_mul, map_zpow₀, hc, GlobalTheory.CharVal.unit_of_finOrder hζ, one_zpow, one_mul]

end GlobalTheory.ColPeriod.Scal

namespace GlobalTheory.ColPeriod

open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker Scal

theorem scalarUnit_of (hL : LevelPrimes) (hH : HeckeUnit) (hT : TwistUnit) : ScalarUnit := by
  intro X Pr R Ch sel S mu cst L G m2 e eta hX hPr hsel hS ht hOk i w hw j hj
  have hH' := hH X Pr R.m Ch G.σ₀ (e ⟨j, hj⟩) ⟨j, hj⟩ (G.mu0 ⟨j, hj⟩) hX hPr (ht.mu0 _) (Pr.g i) w
  have hval : ∀ P : HeightOneSpectrum (𝓞 X.E), (∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.asIdeal) →
      w.valuation X.K (Ch.muVal ⟨j, hj⟩ P : X.K) = 1 := fun P hP =>
    hH' P (hPr.g_prime i) hw (hP i) (Formalism.L2.Host.unif P) _ (ht.muVal _ P hP)
  have h1 : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vG i → w.valuation X.K (cst.muq (j + 1) P) = 1 := by
    intro P hPi
    have hq := (hT X.F X.E X.K S mu P.1 w).2
    obtain ⟨hd, hn⟩ := hL X Pr sel S mu hX hPr hsel P
    by_cases hP : P.1 ∈ Pr.vGs
    · have h1 := hOk.muqG j hj P hP (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) rfl
      have h2 : G.σ₀ ((cst.muq (j + 1) P * ((qValC (mu : Chr X.F X.E X.K) P.1 : X.Kˣ) : X.K))⁻¹) =
          (((G.mu0 ⟨j, hj⟩).locK P.1 (Units.mk0 _ (Proof.NormalFormAtPrime.qOf_ne_zero P.1)) : ℂˣ) : ℂ) := by
        rw [map_inv₀, map_mul, h1, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one, inv_inv]
      have h3 := hH' P.1 (hPr.g_prime i) hw (g_notMem_of_vGs hPr hP hPi) _ _ h2
      rwa [map_inv₀, map_mul, hq, mul_one, inv_eq_one] at h3
    · have hg : ∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal := fun k =>
        natCast_notMem_of_ne (hPr.g_prime k) hd.1 (fun h => hn hP (h ▸ hS k)) P.1 (Ideal.absNorm_mem _)
      rw [hOk.muqQ j hj P hP, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀,
        hq, hval _ hg]
      simp
  refine ⟨h1, fun n N fr _ hN hfr => ?_⟩
  have h2 : w.valuation X.K (muOff sel (rowSG Pr sel mu) (mUof Ch mu j) N) = 1 := by
    unfold muOff
    refine finprod_induction (fun x => w.valuation X.K x = 1) (map_one _)
      (fun x y hx hy => by rw [map_mul, hx, hy, one_mul]) fun v => ?_
    split_ifs with hv
    · exact map_one _
    · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, mUof, dite_eq_left hj, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀, hval _ (g_notMem_sel hX hPr hsel hv),
        (hT X.F X.E X.K S mu _ w).1]
      simp
  rw [muInvDet, map_mul, h2, one_mul, map_prod]
  refine Finset.prod_eq_one fun P _ => ?_
  unfold muAt
  by_cases hP : P.1 ∈ Pr.vG i
  · refine val_locChar_unit w P.1 _ _ ?_
    rw [LinearEquiv.coe_det]
    refine GlobalTheory.StdReps.val_det_eq fun x => ?_
    rw [← hfr P x, hN P.1 (g_mem_of_vG hPr hP)]
  · exact val_locChar w P.1 _ (hL X Pr sel S mu hX hPr hsel P).1.2 (h1 P hP) (Units.ne_zero _)

end GlobalTheory.ColPeriod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NuRowSuccEqWt
noncomputable section

namespace GlobalTheory.ColPeriod

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recWts)

theorem nuRow_succ_eq_wt (D : D7) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (τ : D.what₂.Tau) (n : ℕ) (hn : n < D.R.N j) :
    DV.nuRow D u (j + 1) τ n =
      ((Examples₂.wtN (D.hcW u τ) n + wG D.R ((D.hcW u τ).e ⟨j, hj⟩) (j + 1) : ℚ) : ℝ) := by
  have hw : DV.wSz D (j + 1) τ = (((D.hcW u τ).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold DV.wSz
    rw [dite_eq_left ⟨by omega, by omega⟩, D.hcW_e]
    rfl
  unfold DV.nuRow
  rw [hw]
  unfold DV.srcPar Examples₂.wtN Examples₂.blkN
  by_cases hk : n < D.R.k
  · rw [dite_eq_left hk, dite_eq_left hk]
    unfold hcToWeightQ rhoVec wG Ranks.N
    push_cast
    ring
  · have hb : (n - D.R.k) / (D.R.t + 1) < D.R.m := by
      have hN : n < D.R.k + j * (D.R.t + 1) := hn
      have h2 : n - D.R.k < j * (D.R.t + 1) := Nat.sub_lt_left_of_lt_add (by omega) hN
      have h3 : (n - D.R.k) / (D.R.t + 1) < j := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h2)
      omega
    rw [dite_eq_right hk, dite_eq_right hk, dite_eq_left hb, dite_eq_left hb]
    have hnat : n = D.R.k + (n - D.R.k) / (D.R.t + 1) * (D.R.t + 1) + (n - D.R.k) % (D.R.t + 1) := by
      have := Nat.div_add_mod (n - D.R.k) (D.R.t + 1)
      rw [mul_comm] at this
      omega
    have key : (n : ℝ) = (D.R.k : ℝ) + (((n - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) * ((D.R.t : ℝ) + 1)
        + (((n - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
      conv_lhs => rw [hnat]
      push_cast
      ring
    unfold wG Ranks.N
    push_cast
    linear_combination key

theorem partitionSize : PartitionSize := by
  intro D EX u j hj τ
  unfold nuAbs
  show ∑ i ∈ Finset.range (D.R.N j), DV.nuRow D u (j + 1) τ i = _
  rw [Finset.sum_range, Int.cast_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [nuRow_succ_eq_wt D u j hj τ a a.2]
  have h1 := Wts.nuW_eq (recWts EX) u hj τ a
  have h2 := lamOf_wtN ((recWts EX).hc u τ) hj.le a
  have h3 : (((recWts EX).nuW u (j + 1) τ).w a : ℝ) = ((((recWts EX).nuW u (j + 1) τ).w a : ℚ) : ℝ) := by
    simp
  rw [h3, h1]
  unfold Wts.lamN
  rw [h2]
  rfl

end GlobalTheory.ColPeriod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostFieldPadicEmbeddingMemMaxUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostFieldPadicEmbeddingMemMaxUnramified
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory.HostKur

theorem host_image_mem_Kur : ∀ {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime], l ∉ H.small → l ≠ H.q → l ≠ H.d →
    ∀ (c : H.E →+* PadicAlgCl l) (x : H.E), c x ∈ Loc.MaximalUnramifiedExtension l := by
  intro R H l _ hl2 hq hd c x
  exact GlobalTheory.HubLoc.image_mem_Kur H c (UpperTheory.Small.not_dvd_condN H Fact.out hl2 hq hd) x

end GlobalTheory.HostKur
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HostFieldPadicEmbeddingMemMaxUnramifiedStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hostField_padicEmbedding_mem_maxUnramified : ∀ {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime], l ∉ H.small → l ≠ H.q → l ≠ H.d → ∀ (c : H.E →+* PadicAlgCl l) (x : H.E), c x ∈ Loc.MaximalUnramifiedExtension l := by
  first | exact @GlobalTheory.HostKur.host_image_mem_Kur | exact GlobalTheory.HostKur.host_image_mem_Kur | (intros; apply GlobalTheory.HostKur.host_image_mem_Kur <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationFinOrderApply
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.ColPeriod

theorem valuation_finOrder_apply {G K : Type} [Group G] [Field K] [NumberField K] (ξ : G →* Kˣ) (hξ : IsOfFinOrder ξ)
    (w : HeightOneSpectrum (𝓞 K)) (y : G) : w.valuation K ((ξ y : Kˣ) : K) = 1 := by
  obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hξ
  have h1 : (ξ y) ^ n = 1 := by
    have := congrArg (fun φ : G →* Kˣ => φ y) h
    simpa using this
  have h2 : (w.valuation K ((ξ y : Kˣ) : K)) ^ n = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  exact (pow_eq_one_iff_of_nonneg zero_le hn.ne').1 h2

theorem twistUnit : TwistUnit := by
  intro F E K _ _ _ _ _ _ _ S mu P w
  have hfin : IsOfFinOrder (mu : Chr F E K) := mu.2.1.1.1.2
  let v : HeightOneSpectrum (𝓞 F) := P.under (𝓞 F)
  have hv : P.asIdeal.under (𝓞 F) = v.asIdeal := rfl
  constructor
  · unfold Formalism.L2.Ker.unifVal
    split_ifs with h
    · obtain ⟨b, hb, hb2⟩ : ∃ b ∈ P.asIdeal, b ∉ P.asIdeal ^ 2 := by
        have := Ideal.exists_mem_pow_notMem_pow_succ P.asIdeal P.ne_bot P.isPrime.ne_top 1
        simpa using this
      obtain ⟨y, y₀, h1, h2, h3, h4⟩ := GlobalTheory.SuppIdele.exists_supported_idele F E P v b hv
      rw [← h.choose_spec v hv y y₀ b h1 hb hb2 h2 h3 h4]
      exact valuation_finOrder_apply _ hfin w y
    · simp
  · unfold qValC
    split_ifs with h
    · obtain ⟨y, y₀, h1, h2, h3, h4⟩ :=
        GlobalTheory.SuppIdele.exists_supported_idele F E P v ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) hv
      rw [← h.choose_spec v hv y y₀ h1 h2 h3 h4]
      exact valuation_finOrder_apply _ hfin w y
    · simp

end GlobalTheory.ColPeriod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubHalfRankInt
namespace GlobalTheory.ColPeriod

open Formalism.L2.Col Formalism.BasicNotions Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint (WtCompat)

theorem sub_half_rank_int (R : Ranks) (z : ℤ) (j : ℕ) : ∃ a : ℤ, (z : ℚ) - (R.N j : ℚ) / 2 = a := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨c, hc⟩ := R.t_odd
  unfold Ranks.N
  rw [ha, hc]
  exact ⟨z - a - (j : ℤ) * (c + 1), by push_cast; ring⟩

theorem chainWeights : ChainWeights := by
  intro X Pr R W u j hj
  have hs : ∀ τ : X.Tau, ∃ a : ℤ, sExp R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) = a := by
    intro τ
    obtain ⟨z, hz⟩ := (W.hc u τ).e_int ⟨j, hj⟩
    rw [hz]
    exact sub_half_rank_int R z _
  have hs' : ∀ τ : X.Tau, ∃ a : ℤ, sExp' R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) = a := by
    intro τ
    obtain ⟨z, hz⟩ := (W.hc u τ).e_int ⟨j, hj⟩
    rw [hz]
    exact sub_half_rank_int R z _
  choose s hs using hs
  choose s' hs' using hs'
  have hlt := N_lt_succ R j
  have h1 : ∀ τ (i : Fin (R.N j)),
      (W.lamTrue u (j + 1) τ).w (Fin.castLE hlt.le i) + s τ = (W.lamTrue u j τ).w i + s' τ := by
    intro τ i
    have h := W.lamTrue_old u hj τ (Fin.castLE hlt.le i) i.2
    rw [hs, hs'] at h
    have h' : (((W.lamTrue u (j + 1) τ).w (Fin.castLE hlt.le i) + s τ : ℤ) : ℚ) =
        (((W.lamTrue u j τ).w i + s' τ : ℤ) : ℚ) := by
      push_cast
      rw [h]
      simp
    exact_mod_cast h'
  have h2 : ∀ τ (i : Fin (R.N (j + 1))), R.N j ≤ (i : ℕ) → (W.lamTrue u (j + 1) τ).w i = -s τ := by
    intro τ i hi
    have h := W.lamTrue_new u hj τ i (by omega)
    rw [hs] at h
    exact_mod_cast h
  have h3 : ∀ (τ : X.Tau) (a : Fin (R.N j)), (W.lamTrue u j τ).w a + s' τ = (W.nuW u (j + 1) τ).w a := by
    intro τ a
    have h := W.nuW_eq_true u hj τ a
    rw [hs'] at h
    exact_mod_cast h.symm
  refine ⟨s, s', ⟨h1, h2, fun τ => ?_⟩, h3⟩
  have hpos : 0 < R.N j := R.N_pos j
  have e1 : (W.lamTrue u j τ).detShift = (W.lamTrue u j τ).w ⟨R.N j - 1, by omega⟩ := by
    unfold DomWeight.detShift
    rw [dif_pos hpos]
  have e2 : (W.nuW u (j + 1) τ).detShift = (W.nuW u (j + 1) τ).w (⟨R.N j - 1, by omega⟩ : Fin (R.N j)) := by
    unfold DomWeight.detShift
    exact dif_pos hpos
  have hge : 0 ≤ (W.lamTrue u j τ).w ⟨R.N j - 1, by omega⟩ + s' τ := by
    rw [← h1]
    have ha := (W.lamTrue u (j + 1) τ).anti
      (show Fin.castLE hlt.le (⟨R.N j - 1, by omega⟩ : Fin (R.N j)) ≤ ⟨R.N j, hlt⟩ from by
        rw [Fin.le_def]; simp)
    have hb := h2 τ ⟨R.N j, hlt⟩ le_rfl
    omega
  unfold nuLast
  rw [e1, e2, ← h3, Int.toNat_of_nonneg hge]

end GlobalTheory.ColPeriod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairingEquivContra
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InvPairing

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def pairMap (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b) :
    π'.IntertwiningMap (contra π) where
  toLinearMap :=
    { toFun := fun b => ⟨B.flip b, mem_smoothPart_of_nhds (Filter.mem_of_superset
        ((hπ' b).mem_nhds (by simp)) fun g hg => by
          have hg' : π' g b = b := hg
          ext a
          show B (π g⁻¹ a) b = B a b
          have h := hB g (π g⁻¹ a) b
          rw [hg'] at h
          rw [← h, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])⟩
      map_add' := fun b c => Subtype.ext (by simp)
      map_smul' := fun c b => Subtype.ext (by simp) }
  isIntertwining' g := by
    refine LinearMap.ext fun b => Subtype.ext (LinearMap.ext fun a => ?_)
    show B a (π' g b) = B (π g⁻¹ a) b
    have h := hB g (π g⁻¹ a) b
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    exact h

theorem pairMap_apply (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b) (a : V) (b : W) :
    ((pairMap π hπ' B hB b : smoothPart π.dual) : Module.Dual ℂ V) a = B a b := rfl

theorem eq_zero_of_pairMap (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b)
    (h : ∀ b, pairMap π hπ' B hB b = 0) : B = 0 :=
  LinearMap.ext fun a => LinearMap.ext fun b => by
    have := congrArg (fun l : smoothPart π.dual => (l : Module.Dual ℂ V) a) (h b)
    simpa [pairMap_apply] using this

theorem pairMap_bijective (π : Representation ℂ G V) {π' : Representation ℂ G W} (hπ' : IsSmooth π')
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g a b, B (π g a) (π' g b) = B a b) (hB0 : B ≠ 0)
    (hirr' : π'.IsIrreducible) (hirr : (contra π).IsIrreducible) :
    Function.Bijective (pairMap π hπ' B hB) := by
  set f := pairMap π hπ' B hB with hf
  constructor
  · let S : Subrepresentation π' :=
      { toSubmodule := LinearMap.ker f.toLinearMap
        apply_mem_toSubmodule := fun g v hv => by
          simp only [LinearMap.mem_ker] at hv ⊢
          have := LinearMap.congr_fun (f.isIntertwining' g) v
          simp only [LinearMap.comp_apply] at this
          rw [this, hv, map_zero] }
    rcases hirr'.eq_bot_or_eq_top S with hS | hS
    · intro x y hxy
      have : x - y ∈ S.toSubmodule := by
        show f.toLinearMap (x - y) = 0
        rw [map_sub]; exact sub_eq_zero.2 hxy
      rw [hS] at this
      exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 this)
    · exfalso
      refine hB0 (eq_zero_of_pairMap π hπ' B hB fun b => ?_)
      have : b ∈ S.toSubmodule := by rw [hS]; exact Submodule.mem_top
      exact this
  · let R : Subrepresentation (contra π) :=
      { toSubmodule := LinearMap.range f.toLinearMap
        apply_mem_toSubmodule := fun g v hv => by
          obtain ⟨w, rfl⟩ := hv
          refine ⟨π' g w, ?_⟩
          have := LinearMap.congr_fun (f.isIntertwining' g) w
          simpa only [LinearMap.comp_apply] using this }
    rcases hirr.eq_bot_or_eq_top R with hR | hR
    · exfalso
      refine hB0 (eq_zero_of_pairMap π hπ' B hB fun b => ?_)
      have : f b ∈ R.toSubmodule := ⟨b, rfl⟩
      rw [hR] at this
      exact (Submodule.mem_bot ℂ).1 this
    · intro l
      have : l ∈ R.toSubmodule := by rw [hR]; exact Submodule.mem_top
      obtain ⟨b, hb⟩ := this
      exact ⟨b, hb⟩

end GlobalTheory.InvPairing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeUnit
open GlobalTheory.ColPeriod

namespace GlobalTheory.ColPeriod

theorem heckeUnit : GlobalTheory.ColPeriod.HeckeUnit :=
  fun _ _ _ _ _ _ _ _ hX hPr hμ _ _ _ _ hw hP x _ hk => GlobalTheory.CharVal.mu_unit hX hPr hμ x hk hP hw

end GlobalTheory.ColPeriod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNeZeroMemJumpTypeTwo
noncomputable section

namespace GlobalTheory.HTW.Rec.Model

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

instance decThickN {n b η : ℕ} (sz : ZMod n → ℕ) : DecidablePred (ThickN b η sz) := fun i => by
  unfold ThickN; infer_instance

section Input

variable (D : D7) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
  (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1)

end Input

end GlobalTheory.HTW.Rec.Model
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExponentHeckeCharCompNormConjEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExponentHeckeCharCompNormConjEmbedding
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

namespace GlobalTheory.NormExpo

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem adeleMap_real_injective :
    Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap (maximalRealSubfield E) E) := by
  intro x y h
  rw [← GlobalTheory.UnitaryHeckeBaseChange.toAdele_algebraMap, ← GlobalTheory.UnitaryHeckeBaseChange.toAdele_algebraMap] at h
  have h2 := (GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (isCMExt_real E)).injective (a₁ := algebraMap _ _ x) (a₂ := algebraMap _ _ y) h
  exact Algebra.TensorProduct.includeLeft_injective (S := maximalRealSubfield E)
    (algebraMap (maximalRealSubfield E) E).injective h2

theorem conjAd_infId (u : (Cinf E)ˣ) :
    Units.map (GlobalTheory.UnitaryBC.conjAd E).toMonoidHom (infId E u) = infId E (Units.map (starRingEnd (Cinf E)).toMonoidHom u) := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change infEq E (starRingEnd (Cinf E) ((infEq E).symm (1 - infEq E 1 + infEq E u))) =
      1 - infEq E 1 + infEq E (starRingEnd (Cinf E) u)
    simp
  · change conjFin _ ((1 : Af E) - 0 + 0) = (1 : Af E) - 0 + 0
    simp

theorem ideleNorm_infId_star (u : (Cinf E)ˣ) :
    ideleNorm E (infId E (Units.map (starRingEnd (Cinf E)).toMonoidHom u)) = ideleNorm E (infId E u) := by
  refine Units.ext (adeleMap_real_injective E ?_)
  refine congrArg Units.val (a₁ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E _) (a₂ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E _) ?_
  rw [ideleMap_ideleNorm, ideleMap_ideleNorm, GlobalTheory.PolChar.ideleConj_eq, GlobalTheory.PolChar.ideleConj_eq, conjAd_infId,
    conjAd_infId, mul_comm]
  congr 2
  exact Units.ext (star_star _)

theorem star_expU_atEmb (τ : E →+* ℂ) (z : ℂ) :
    Units.map (starRingEnd (Cinf E)).toMonoidHom (expU (atEmb τ z)) = expU (atEmb τ (starRingEnd ℂ z)) := by
  classical
  refine Units.ext (funext fun w => ?_)
  change starRingEnd ℂ (Complex.exp (atEmb τ z w)) = Complex.exp (atEmb τ (starRingEnd ℂ z) w)
  rw [← Complex.exp_conj]
  congr 1
  unfold atEmb
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw; split_ifs <;> simp
  · simp [Pi.single_eq_of_ne hw]

theorem expo_compNorm_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (χ : HChar (maximalRealSubfield E)) (τ : E →+* ℂ),
    expo (compNorm E χ) (ComplexEmbedding.conjugate τ) = expo (compNorm E χ) τ := by
  intro E _ _ _ χ τ
  refine (GlobalTheory.CuspRep.expo_eq_of_exp _ τ _ (expo (compNorm E χ) τ) fun z => ?_).symm
  have h : chiInf (compNorm E χ) (expU (atEmb τ z)) = chiInf (compNorm E χ) (expU (atEmb τ (starRingEnd ℂ z))) := by
    rw [← star_expU_atEmb]
    exact congrArg χ.1 (ideleNorm_infId_star E _).symm
  rw [h, chiInf_expU_atEmb, Complex.conj_conj, add_comm]

end GlobalTheory.NormExpo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExponentHeckeCharCompNormConjEmbeddingStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G Dec IsPlaceOver
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponent_heckeChar_compNorm_conjEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar (maximalRealSubfield E)) (τ : E →+* ℂ), expo (compNorm E χ) (ComplexEmbedding.conjugate τ) = expo (compNorm E χ) τ := by
  first | exact @GlobalTheory.NormExpo.expo_compNorm_conjugate | exact GlobalTheory.NormExpo.expo_compNorm_conjugate | (intros; apply GlobalTheory.NormExpo.expo_compNorm_conjugate <;> assumption)
end
end
