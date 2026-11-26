module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsMulMinusculeTopTerm
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Product
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPToLiftReal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFramedPointLiesOverTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntegralVacuumIntertwinesSphericalHecke
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntegralVacuumIntertwinesSphericalHecke
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaIntHecke

theorem integral_move {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
    [BorelSpace H] {μ : Measure H} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    {Γ : Subgroup H} [Countable Γ] {𝓕 : Set H} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (K : Set H) (x : H)
    (A A' : Finset H) (Kn F : H → ℂ) (hA : ∀ a ∈ A, ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x * k₂)
    (hA' : ∀ a ∈ A', ∃ k₁ ∈ K, ∃ k₂ ∈ K, a = k₁ * x⁻¹ * k₂) (hcard : A'.card = A.card)
    (hFl : ∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) (hFr : ∀ k ∈ K, ∀ h, F (h * k) = F h)
    (hKl : ∀ γ ∈ Γ, ∀ h, Kn (γ * h) = Kn h) (hKr : ∀ k ∈ K, ∀ h, Kn (h * k) = Kn h)
    (hx : IntegrableOn (fun h => Kn h * F (h * x)) 𝓕 μ) :
    IntegrableOn (fun h => Kn h * ∑ a ∈ A, F (h * a)) 𝓕 μ ∧
      IntegrableOn (fun h => (∑ a ∈ A', Kn (h * a)) * F h) 𝓕 μ ∧
      ∫ h in 𝓕, Kn h * ∑ a ∈ A, F (h * a) ∂μ = ∫ h in 𝓕, (∑ a ∈ A', Kn (h * a)) * F h ∂μ := by
  have hu : ∀ γ ∈ Γ, ∀ h, (fun h => Kn h * F (h * x)) (γ * h) = (fun h => Kn h * F (h * x)) h := by
    intro γ hγ h
    simp only [hKl γ hγ, mul_assoc, hFl γ hγ]
  have h1e : ∀ a ∈ A, ∃ y, (fun h => Kn h * F (h * a)) = fun h => (fun h => Kn h * F (h * x)) (h * y) := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA a ha
    refine ⟨k₁, funext fun h => ?_⟩
    simp only
    rw [hKr k₁ hk₁, ← mul_assoc, hFr k₂ hk₂, ← mul_assoc]
  have h2e : ∀ a ∈ A', ∃ y, (fun h => Kn (h * a) * F h)
      = fun h => (fun h => Kn h * F (h * x)) (h * y) := by
    intro a ha
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hA' a ha
    refine ⟨k₁ * x⁻¹, funext fun h => ?_⟩
    have : h * (k₁ * x⁻¹) * x = h * k₁ := by group
    simp only [this]
    rw [hFr k₁ hk₁, ← mul_assoc, hKr k₂ hk₂]
  have key : ∀ u : H → ℂ, (∃ y, u = fun h => (fun h => Kn h * F (h * x)) (h * y)) →
      IntegrableOn u 𝓕 μ ∧ ∫ h in 𝓕, u h ∂μ = ∫ h in 𝓕, Kn h * F (h * x) ∂μ := by
    rintro _ ⟨y, rfl⟩
    exact ⟨integrableOn_fundamentalDomain_mul_right h𝓕 y _ hu hx,
      setIntegral_fundamentalDomain_mul_right h𝓕 y _ hu⟩
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  refine ⟨integrable_finsetSum _ fun a ha => (key _ (h1e a ha)).1,
    integrable_finsetSum _ fun a ha => (key _ (h2e a ha)).1, ?_⟩
  rw [integral_finsetSum _ fun a ha => (key _ (h1e a ha)).1,
    integral_finsetSum _ fun a ha => (key _ (h2e a ha)).1,
    Finset.sum_congr rfl fun a ha => (key _ (h1e a ha)).2,
    Finset.sum_congr rfl fun a ha => (key _ (h2e a ha)).2, Finset.sum_const, Finset.sum_const, hcard]

variable {D : D7}

theorem exists_dual (V : HSp D) (P : Pl D.host.E) (d : List ℤ) (R : Finset (GA D V)) (h : SphOp V P d R) :
    ∃ α ∈ GfC V, ∃ R', SphOp V P (dualLab d) R' ∧ R'.card = R.card ∧
      (∀ γ ∈ R, ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * α * k₂) ∧
      ∀ γ ∈ R', ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * α⁻¹ * k₂ := by
  obtain ⟨e, f, ϖ, α, hS, hef, hϖ, hϖ2, hd, hJ, hχ, hα, hdiv, hR, hrep⟩ := h
  obtain ⟨he, v, hf⟩ := HeckeDual.idem_of_isPrimeIdem hef
  obtain ⟨a, rfl⟩ := (HeckeDual.suppF_iff V hf α).1 hα
  obtain ⟨δ, hδ, hσδ⟩ := HeckeDual.exists_skew D
  have := GlobalTheory.AdelicU.SelfDual.isLattice_frameLat V
  have hK : ∀ g, g ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k} ↔
      ∃ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v,
        GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k = g := fun g => by
    constructor
    · rintro ⟨h3, h2⟩
      obtain ⟨k, rfl⟩ := (HeckeDual.suppF_iff V hf g).1 h2
      rw [GlobalTheory.AdelicU.KsphC_eq] at h3
      have h4 := (GlobalTheory.AdelicU.mem_levelOff.1 h3).2.2 v (Finset.notMem_empty v)
      rw [GlobalTheory.AdelicU.proj_emb_self] at h4
      exact ⟨k, h4, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      have h2 := (HeckeDual.suppF_iff V hf _).2 ⟨k, rfl⟩
      refine ⟨?_, h2⟩
      rw [GlobalTheory.AdelicU.KsphC_eq]
      exact GlobalTheory.AdelicU.emb_mem_levelOff (Finset.notMem_empty v) hk
  obtain ⟨R', h1, h2, h3⟩ := HeckeDual.exists_rep_inv
    (HeckeDual.modular_eq_one D.sp.cm.sig V.gram (fun x => star_star x) hδ hσδ
      ((GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V) v)
    (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v) (GlobalTheory.AdelicU.emb_injective _ _ v) _
    (GlobalTheory.AdelicU.isOpen_stabLoc _ _ _ v) (GlobalTheory.AdelicU.isCompact_stabLoc _ _ _ v) _ hK a R
    (fun γ hγ => (hrep.1 γ hγ).2) hrep.2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := fun h => hϖ2 (by
    rw [show ϖ = 0 from RingOfIntegers.ext h]
    exact zero_mem _)
  have hh : ∀ (β γ : GA D V), (∃ k₁ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k}, ∃ k₂ ∈ {k | k ∈ KsphC V ∅ ∧ SuppF V f k},
      γ = k₁ * β * k₂) → ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * β * k₂ := by
    rintro β γ ⟨k₁, g₁, k₂, g₂, rfl⟩
    exact ⟨k₁, ⟨g₁.1, e, f, hef, g₁.2⟩, k₂, ⟨g₂.1, e, f, hef, g₂.2⟩, rfl⟩
  refine ⟨_, GlobalTheory.AdelicU.mem_finPts.2 (GlobalTheory.AdelicU.projInf_emb _ _ v a), R',
    ⟨e, f, ϖ, _, hS, hef, hϖ, hϖ2, ?_, hJ, hχ, (HeckeDual.suppF_iff V hf _).2 (inv_mem ⟨a, rfl⟩),
    (GlobalTheory.DivDual.divAt_inv_and_mul V e _ d _ he hϖ0 hdiv).1,
    fun γ hγ => (HeckeDual.suppF_iff V hf _).2 (h1 γ hγ).1,
    fun γ hγ => ⟨?_, (h1 γ hγ).2⟩, h2⟩, h3, fun γ hγ => hh _ _ (hrep.1 γ hγ).2, fun γ hγ => hh _ _ (h1 γ hγ).2⟩
  · rw [dualLab, List.pairwise_reverse, List.pairwise_map]
    exact hd.imp fun h => neg_le_neg h
  · obtain ⟨x, rfl⟩ := (h1 γ hγ).1
    exact GlobalTheory.AdelicU.mem_finPts.2 (GlobalTheory.AdelicU.projInf_emb _ _ v x)

theorem opOf_single {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M)
    (P : Pl D.host.E) (d : List ℤ) : opOf π P (Finsupp.single d 1) = ∑ γ ∈ Hk3.rep V P d, π γ := by
  unfold opOf
  rw [Finsupp.sum_single_index (by exact zero_smul _ _), one_smul]

theorem opOf_dualC {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M)
    (P : Pl D.host.E) (c : List ℤ →₀ ℂ) :
    opOf π P (dualC c) = ∑ d ∈ c.support, c d • ∑ γ ∈ Hk3.rep V P (dualLab d), π γ := by
  unfold opOf dualC
  rw [Finsupp.sum_mapDomain_index (by exact fun _ => zero_smul _ _) (by exact fun _ _ _ => add_smul _ _ _)]
  rfl

theorem exists_dual_rep (V : HSp D) (P : Pl D.host.E) (d : List ℤ) :
    ∃ α ∈ GfC V, ∃ R' : Finset (GA D V), R'.card = (Hk3.rep V P d).card ∧
      (∀ γ ∈ Hk3.rep V P d, ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * α * k₂) ∧
      (∀ γ ∈ R', ∃ k₁ ∈ hyp V P, ∃ k₂ ∈ hyp V P, γ = k₁ * α⁻¹ * k₂) ∧
      ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M),
        (∀ k ∈ hyp V P, π k u = u) → ∑ γ ∈ R', π γ u = ∑ γ ∈ Hk3.rep V P (dualLab d), π γ u := by
  by_cases h : IsLab V P d
  · have hs : SphOp V P d (Hk3.rep V P d) := by
      unfold Hk3.rep
      rw [dite_eq_left h]
      exact h.choose_spec
    obtain ⟨α, hα, R', h1, h2, h3, h4⟩ := exists_dual V P d _ hs
    refine ⟨α, hα, R', h2, h3, h4, fun M _ _ π u hu => ?_⟩
    rw [((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P).1 _ _ h1).2 M π u hu, opOf_single, LinearMap.sum_apply]
  · have h0 : Hk3.rep V P d = ∅ := dite_eq_right h
    have h1 : Hk3.rep V P (dualLab d) = ∅ := dite_eq_right fun h' => h (((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V P).2.2.2.1 d).1.2 h')
    exact ⟨1, one_mem _, ∅, by rw [h0], by simp [h0], by simp, fun M _ _ π u _ => by rw [h1]⟩

theorem hk_apply (V : HSp D) (P : Pl D.host.E) (c : List ℤ →₀ ℂ) (F : GA D V → ℂ) (g : GA D V) :
    hk V P c F g = ∑ d ∈ c.support, c d * ∑ γ ∈ Hk3.rep V P d, F (g * γ) := by
  unfold hk Finsupp.sum
  rw [LinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem liftInt_hk : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → ∀ (ν : Measure (GA D T)) (𝓕 : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ T) 𝓕 ν → VacFix ψ om P → ∀ cS cT, Match ψ om P cS (dualC cT) → ∀ f, IsVacAt ψ S T P f → ∀ Φ : GA D T → ℂ, (∀ γ ∈ GQ T, ∀ h, Φ (γ * h) = Φ h) → (∀ k ∈ hyp T P, ∀ h, Φ (h * k) = Φ h) → (∀ g, ∀ y ∈ GfC T, IntegrableOn (fun h => thetaKO om g h f * Φ (h * y)) 𝓕 ν) → Lift.liftInt ν 𝓕 (thetaKO om) f (hk T P cT Φ) = hk S P cS (Lift.liftInt ν 𝓕 (thetaKO om) f Φ) := by
  intro D ψ S T χS χT om P hW ν 𝓕 hν h𝓕 hfix cS cT hM f hf Φ hΦl hΦr hint
  have : IsTopologicalGroup (GA D T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D T) := ⟨rfl⟩
  have : Countable (GQ T) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig T.gram
  have : ν.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D T ν hν
  obtain ⟨hl, hr⟩ := GlobalTheory.thetaKO_rat_left_and_eigen_right ψ S T χS χT om hW f hf.1
  have hfT : ∀ k ∈ hyp T P, om (1, k) f = f := fun k hk => by
    obtain ⟨e, f', hef⟩ : ∃ e f', IsPrimeIdem P e f' := hk.2.imp fun _ h => h.imp fun _ h => h.1
    refine hfix f hf 1 ⟨⟨one_mem _, fun y => ?_, by simp⟩, e, f', hef, fun i j => ?_⟩ k hk
    · have : finMat D.sp.cm.sig S.gram (1 : GA D S) = 1 := by
        unfold finMat
        exact Matrix.map_one _ (map_zero _) (map_one _)
      rw [this, Matrix.one_mulVec]
    · have : Formalism.L2.Theta.mt S (1 : GA D S) = 1 := by simp [Formalism.L2.Theta.mt]
      rw [this, sub_self, Matrix.zero_apply, mul_zero]
  have hth : ∀ g h a b, thetaKO om (g * a) (h * b) f = om (g, h) (om (a, b) f) 0 := fun g h a b => by
    unfold thetaKO
    rw [show ((g * a, h * b) : GA D S × GA D T) = (g, h) * (a, b) from rfl, map_mul, mul_apply_eq_comp]
  funext g
  have step : ∀ d, IntegrableOn (fun h => thetaKO om g h f * ∑ a ∈ Hk3.rep T P d, Φ (h * a)) 𝓕 ν ∧
      IntegrableOn (fun h => (∑ a ∈ Hk3.rep T P (dualLab d), thetaKO om g (h * a) f) * Φ h) 𝓕 ν ∧
      ∫ h in 𝓕, thetaKO om g h f * ∑ a ∈ Hk3.rep T P d, Φ (h * a) ∂ν =
        ∫ h in 𝓕, (∑ a ∈ Hk3.rep T P (dualLab d), thetaKO om g (h * a) f) * Φ h ∂ν := fun d => by
    obtain ⟨α, hα, R', h1, h2, h3, h4⟩ := exists_dual_rep T P d
    have h5 := h4 _ (om.comp (MonoidHom.inr _ _)) f hfT
    have h6 : ∀ h, ∑ a ∈ Hk3.rep T P (dualLab d), thetaKO om g (h * a) f = ∑ a ∈ R', thetaKO om g (h * a) f := fun h => by
      have h7 := congrArg (fun u => om (g, h) u 0) h5
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, Finset.sum_apply] at h7
      have h8 : ∀ a, thetaKO om g (h * a) f = om (g, h) (om (1, a) f) 0 := fun a => by rw [← hth, mul_one]
      simp only [h8]
      exact h7.symm
    simp only [h6]
    exact integral_move h𝓕 (hyp T P) α _ R' (fun h => thetaKO om g h f) Φ h2 h3 h1 hΦl hΦr
      (fun γ hγ h => by simpa only [one_mul] using hl 1 (one_mem _) γ hγ g h)
      (fun k hk h => by simpa only [one_mul, mul_one] using hr 1 k 1 (by rw [hfT k hk, one_smul]) g h)
      (hint g α hα)
  have hker : ∀ h, ∑ d ∈ cT.support, cT d * ∑ a ∈ Hk3.rep T P (dualLab d), thetaKO om g (h * a) f =
      ∑ d ∈ cS.support, cS d * ∑ a ∈ Hk3.rep S P d, thetaKO om (g * a) h f := fun h => by
    have h7 := congrArg (fun u => om (g, h) u 0) (hM f hf)
    rw [opOf_dualC] at h7
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [opOf, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] at h7
    have h8 : ∀ a, thetaKO om g (h * a) f = om (g, h) (om (1, a) f) 0 := fun a => by rw [← hth, mul_one]
    have h9 : ∀ a, thetaKO om (g * a) h f = om (g, h) (om (a, 1) f) 0 := fun a => by rw [← hth, mul_one]
    simp only [h8, h9]
    exact h7.symm
  have hi1 : ∀ g, IntegrableOn (fun h => thetaKO om g h f * Φ h) 𝓕 ν := fun g => by
    simpa only [mul_one] using hint g 1 (one_mem _)
  rw [hk_apply]
  unfold Lift.liftInt
  calc ∫ h in 𝓕, thetaKO om g h f * hk T P cT Φ h ∂ν
      = ∫ h in 𝓕, ∑ d ∈ cT.support, cT d * (thetaKO om g h f * ∑ a ∈ Hk3.rep T P d, Φ (h * a)) ∂ν := by
        congr 1
        funext h
        rw [hk_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => mul_left_comm _ _ _
    _ = ∫ h in 𝓕, ∑ d ∈ cT.support, cT d * ((∑ a ∈ Hk3.rep T P (dualLab d), thetaKO om g (h * a) f) * Φ h) ∂ν := by
        rw [integral_finsetSum _ fun d _ => (step d).1.const_mul _,
          integral_finsetSum _ fun d _ => (step d).2.1.const_mul _]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [integral_const_mul, integral_const_mul, (step d).2.2]
    _ = ∫ h in 𝓕, ∑ d ∈ cS.support, cS d * ∑ a ∈ Hk3.rep S P d, thetaKO om (g * a) h f * Φ h ∂ν := by
        congr 1
        funext h
        simp only [← Finset.sum_mul, ← mul_assoc]
        rw [hker]
    _ = _ := by
        rw [integral_finsetSum _ fun d _ => (integrable_finsetSum _ fun a _ => hi1 (g * a)).const_mul _]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [integral_const_mul, integral_finsetSum _ fun a _ => hi1 (g * a)]

end GlobalTheory.ThetaIntHecke
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntegralVacuumIntertwinesSphericalHeckeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIntegral_vacuum_intertwines_sphericalHecke : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (P : Pl D.host.E), IsWeilDatumO ψ S T χS χT om → ∀ (ν : Measure (GA D T)) (𝓕 : Set (GA D T)), ν.IsHaarMeasure → IsFundamentalDomain (GQ T) 𝓕 ν → VacFix ψ om P → ∀ cS cT, Match ψ om P cS (dualC cT) → ∀ f, IsVacAt ψ S T P f → ∀ Φ : GA D T → ℂ, (∀ γ ∈ GQ T, ∀ h, Φ (γ * h) = Φ h) → (∀ k ∈ hyp T P, ∀ h, Φ (h * k) = Φ h) → (∀ g, ∀ y ∈ GfC T, IntegrableOn (fun h => thetaKO om g h f * Φ (h * y)) 𝓕 ν) → Lift.liftInt ν 𝓕 (thetaKO om) f (hk T P cT Φ) = hk S P cS (Lift.liftInt ν 𝓕 (thetaKO om) f Φ) := by
  exact @GlobalTheory.ThetaIntHecke.liftInt_hk
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CartanExponentsNonnegMinusculeTopProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CartanExponentsNonnegMinusculeTopProduct
open IsDedekindDomain NumberField Matrix

noncomputable section

namespace GlobalTheory.Hk3.MinuscTopLocal

theorem ov_eq (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Formalism.UG.Ov F v = Formalism.UG.intL (v.adicCompletion F) := by
  ext x
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) (K := F) v).trans Iff.rfl

theorem zpow_int {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) (m : ℤ) :
    ϖ ^ m ∈ Formalism.UG.intL (v.adicCompletion F) ↔ 0 ≤ m := by
  rw [← ov_eq]
  show ϖ ^ m ∈ v.adicCompletionIntegers F ↔ 0 ≤ m
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_zpow₀, hϖ, ← WithZero.coe_zpow,
    ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zsmul, ← ofAdd_zero, Multiplicative.ofAdd_le,
    smul_eq_mul]
  omega

def dU {L : Type} [Field L] {n : ℕ} {ϖ : L} (h0 : ϖ ≠ 0) (e : Fin n → ℤ) : GL (Fin n) L where
  val := Matrix.diagonal fun i => ϖ ^ e i
  inv := Matrix.diagonal fun i => ϖ ^ (-e i)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; rw [← zpow_add₀ h0]; simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; rw [← zpow_add₀ h0]; simp

theorem intM_mul {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) :
    ∀ i j, (A * B) i j ∈ Formalism.UG.intL L := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hA _ _) (hB _ _)

theorem intM_diag {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {n : ℕ}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) {e : Fin n → ℤ} (he : ∀ i, 0 ≤ e i) :
    ∀ i j, (Matrix.diagonal fun i => ϖ ^ e i) i j ∈ Formalism.UG.intL (v.adicCompletion F) := fun i j => by
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · exact (zpow_int hϖ _).2 (he i)
  · exact zero_mem _

theorem unif_ne_zero {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) : ϖ ≠ 0 := by
  intro h
  rw [Formalism.UG.IsUnifV, h, map_zero] at hϖ
  exact WithZero.zero_ne_coe hϖ

theorem cartan_top_step : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F), Formalism.UG.IsUnifV F v ϖ → ∀ (d : Fin n → ℤ) (k : ℕ), Antitone d → (∀ i, 0 ≤ d i) → (∀ i : Fin n, 0 < d i ↔ (i : ℕ) < k) → ∀ a₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ a₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ a₃ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ d' : Fin n → ℤ, Antitone d' → ∀ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), (a₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ (fun i => if 0 < d i then d i - 1 else d i) * (a₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ (fun i => if (i : ℕ) < k then 1 else 0) * (a₃ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (k₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ d' * (k₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → (∀ i, 0 ≤ d' i) ∧ (d' = d ∨ (∑ i, d' i = ∑ i, d i ∧ ∑ i, d' i ^ 2 < ∑ i, d i ^ 2)) := by
  intro F _ _ v n ϖ hϖ d k hd hd0 hk a₁ ha₁ a₂ ha₂ a₃ ha₃ d' hd' k₁ hk₁ k₂ hk₂ e
  have h0 : ϖ ≠ 0 := unif_ne_zero hϖ
  rw [ov_eq] at ha₁ ha₂ ha₃ hk₁ hk₂
  have hm0 : ∀ i, 0 ≤ (fun i => if 0 < d i then d i - 1 else d i) i := fun i => by
    have := hd0 i; dsimp only; split_ifs <;> omega
  have hw0 : ∀ i : Fin n, 0 ≤ (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) i := fun i => by
    dsimp only; split_ifs <;> omega
  have hG : a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂ *
      dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃ = k₁ * dU h0 d' * k₂ :=
    Units.ext (by simp only [Units.val_mul]; exact e)
  have hD : k₁⁻¹ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂ *
      dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * k₂⁻¹ = dU h0 d' := by
    rw [hG]; group
  have hd'0 : ∀ i, 0 ≤ d' i := by
    intro i
    have hI : ∀ a b, ((k₁⁻¹ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂ *
        dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * k₂⁻¹ : GL (Fin n) _) :
          Matrix (Fin n) (Fin n) _) a b ∈ Formalism.UG.intL (v.adicCompletion F) := by
      simp only [Units.val_mul]
      refine intM_mul (intM_mul (GlobalTheory.Hk3.MinuscTop.glint_entry (inv_mem hk₁)) ?_)
        (GlobalTheory.Hk3.MinuscTop.glint_entry (inv_mem hk₂))
      refine intM_mul (intM_mul (intM_mul (intM_mul (GlobalTheory.Hk3.MinuscTop.glint_entry ha₁) ?_)
        (GlobalTheory.Hk3.MinuscTop.glint_entry ha₂)) ?_) (GlobalTheory.Hk3.MinuscTop.glint_entry ha₃)
      · exact intM_diag hϖ hm0
      · exact intM_diag hϖ hw0
    have := hI i i
    rw [hD] at this
    change (Matrix.diagonal fun i => ϖ ^ d' i) i i ∈ _ at this
    rw [Matrix.diagonal_apply_eq] at this
    exact (zpow_int hϖ _).1 this
  obtain ⟨dN, hdN⟩ : ∃ f : Fin n → ℕ, ∀ i, (f i : ℤ) = d i :=
    ⟨fun i => (d i).toNat, fun i => Int.toNat_of_nonneg (hd0 i)⟩
  obtain ⟨d'N, hd'N⟩ : ∃ f : Fin n → ℕ, ∀ i, (f i : ℤ) = d' i :=
    ⟨fun i => (d' i).toNat, fun i => Int.toNat_of_nonneg (hd'0 i)⟩
  have hdA : Antitone dN := fun i j h => by have := hd h; have := hdN i; have := hdN j; omega
  have hd'A : Antitone d'N := fun i j h => by have := hd' h; have := hd'N i; have := hd'N j; omega
  have hkN : ∀ i : Fin n, 0 < dN i ↔ (i : ℕ) < k := fun i => by rw [← hk i, ← hdN i]; omega
  have hg : ∃ l₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ∃ l₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ((l₁ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂) * l₂ : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) _) = Matrix.diagonal fun i => ϖ ^ (dN i - 1) := by
    refine ⟨a₁⁻¹, inv_mem ha₁, a₂⁻¹, inv_mem ha₂, ?_⟩
    have : a₁⁻¹ * (a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂) * a₂⁻¹ =
        dU h0 (fun i => if 0 < d i then d i - 1 else d i) := by group
    rw [this]
    change (Matrix.diagonal fun i => ϖ ^ (if 0 < d i then d i - 1 else d i)) = _
    congr 1; funext i
    rw [← zpow_natCast]; congr 1
    have := hdN i
    split_ifs <;> omega
  have ha : ∃ l₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ∃ l₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ((l₁ * (dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * l₂ : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) _) = Matrix.diagonal fun i : Fin n => if (i : ℕ) < k then ϖ else 1 := by
    refine ⟨1, one_mem _, a₃⁻¹, inv_mem ha₃, ?_⟩
    have : 1 * (dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃) * a₃⁻¹ =
        dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) := by group
    rw [this]
    change (Matrix.diagonal fun i : Fin n => ϖ ^ (if (i : ℕ) < k then (1 : ℤ) else 0)) = _
    congr 1; funext i
    split_ifs <;> simp
  have hga : ∃ l₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ∃ l₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL (v.adicCompletion F)),
      ((l₁ * ((a₁ * dU h0 (fun i => if 0 < d i then d i - 1 else d i) * a₂) *
        (dU h0 (fun i : Fin n => if (i : ℕ) < k then (1 : ℤ) else 0) * a₃)) * l₂ : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) _) = Matrix.diagonal fun i => ϖ ^ d'N i := by
    refine ⟨k₁⁻¹, inv_mem hk₁, k₂⁻¹, inv_mem hk₂, ?_⟩
    rw [← mul_assoc (a₁ * _ * a₂), hD]
    change (Matrix.diagonal fun i => ϖ ^ d' i) = _
    congr 1; funext i
    rw [← hd'N i, zpow_natCast]
  have key := GlobalTheory.Hk3.MinuscTop.elemDiv_mul_minuscule (v.adicCompletion F) ϖ n hϖ dN k hdA hkN _ _ hg ha
    d'N hd'A hga
  refine ⟨hd'0, ?_⟩
  have s1 : ∑ i, d' i = ((∑ i, d'N i : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => (hd'N i).symm
  have s2 : ∑ i, d i = ((∑ i, dN i : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => (hdN i).symm
  have s3 : ∑ i, d' i ^ 2 = ((∑ i, d'N i ^ 2 : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => by rw [hd'N i]
  have s4 : ∑ i, d i ^ 2 = ((∑ i, dN i ^ 2 : ℕ) : ℤ) := by
    push_cast; exact Finset.sum_congr rfl fun i _ => by rw [hdN i]
  rcases key with h | ⟨h1, h2⟩
  · left; funext i; rw [← hd'N i, ← hdN i, h]
  · right
    rw [s1, s2, s3, s4]
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

end GlobalTheory.Hk3.MinuscTopLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CartanExponentsNonnegMinusculeTopProductStatement
open IsDedekindDomain NumberField Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartanExponents_nonneg_minusculeTop_product : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F), Formalism.UG.IsUnifV F v ϖ → ∀ (d : Fin n → ℤ) (k : ℕ), Antitone d → (∀ i, 0 ≤ d i) → (∀ i : Fin n, 0 < d i ↔ (i : ℕ) < k) → ∀ a₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ a₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ a₃ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ d' : Fin n → ℤ, Antitone d' → ∀ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), (a₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ (fun i => if 0 < d i then d i - 1 else d i) * (a₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ (fun i => if (i : ℕ) < k then 1 else 0) * (a₃ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = (k₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Formalism.UG.diagPow F v ϖ d' * (k₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) → (∀ i, 0 ≤ d' i) ∧ (d' = d ∨ (∑ i, d' i = ∑ i, d i ∧ ∑ i, d' i ^ 2 < ∑ i, d i ^ 2)) := by
  first | exact @GlobalTheory.Hk3.MinuscTopLocal.cartan_top_step | exact GlobalTheory.Hk3.MinuscTopLocal.cartan_top_step | (intros; apply GlobalTheory.Hk3.MinuscTopLocal.cartan_top_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.T2SpaceAfP
open NumberField GlobalTheory.LKTrip IsDedekindDomain
open scoped TensorProduct Matrix.Norms.L2Operator RestrictedProduct

noncomputable section

open Topology

namespace GlobalTheory.GfTop

theorem td_of_inj {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TotallyDisconnectedSpace Y]
    {f : X → Y} (hf : Continuous f) (hi : Function.Injective f) : TotallyDisconnectedSpace X :=
  ⟨fun s _ hs => Set.subsingleton_of_image hi s
    (isTotallyDisconnected_of_totallyDisconnectedSpace (f '' s) (f '' s) subset_rfl (hs.image f hf.continuousOn))⟩

theorem props_of_closedEmb {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [LocallyCompactSpace Y]
    [T2Space Y] [TotallyDisconnectedSpace Y] [SecondCountableTopology Y] {f : X → Y} (hf : IsClosedEmbedding f) :
    LocallyCompactSpace X ∧ T2Space X ∧ TotallyDisconnectedSpace X ∧ SecondCountableTopology X :=
  ⟨hf.locallyCompactSpace, hf.isEmbedding.t2Space, td_of_inj hf.continuous hf.injective,
    hf.isEmbedding.secondCountableTopology⟩

theorem isClosedEmbedding_embedProduct' (A : Type*) [TopologicalSpace A] [Monoid A] [ContinuousMul A] [T2Space A] :
    IsClosedEmbedding (Units.embedProduct A) := by
  refine ⟨Units.isEmbedding_embedProduct, ?_⟩
  have h : Set.range (Units.embedProduct A) =
      {x : A × Aᵐᵒᵖ | x.1 * x.2.unop = 1 ∧ x.2.unop * x.1 = 1} := by
    ext ⟨a, b⟩
    constructor
    · rintro ⟨u, hu⟩
      rw [← hu]
      simp
    · rintro ⟨h1, h2⟩
      exact ⟨⟨a, b.unop, h1, h2⟩, rfl⟩
  rw [h]
  exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd)) continuous_const).inter
    (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)

theorem units_props (A : Type*) [TopologicalSpace A] [Monoid A] [ContinuousMul A] [LocallyCompactSpace A]
    [T2Space A] [TotallyDisconnectedSpace A] [SecondCountableTopology A] :
    LocallyCompactSpace Aˣ ∧ T2Space Aˣ ∧ TotallyDisconnectedSpace Aˣ ∧ SecondCountableTopology Aˣ := by
  obtain ⟨o1, o2, o3, o4⟩ := props_of_closedEmb (MulOpposite.opHomeomorph (M := A)).symm.isClosedEmbedding
  exact props_of_closedEmb (isClosedEmbedding_embedProduct' A)

theorem module_props (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [T2Space R] [TotallyDisconnectedSpace R] [SecondCountableTopology R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] [TopologicalSpace M]
    [IsModuleTopology R M] :
    LocallyCompactSpace M ∧ T2Space M ∧ TotallyDisconnectedSpace M ∧ SecondCountableTopology M := by
  haveI : ContinuousAdd M := IsModuleTopology.toContinuousAdd R M
  let b := Module.Free.chooseBasis R M
  let e : M ≃ₜ (Module.Free.ChooseBasisIndex R M → R) :=
    { toEquiv := b.equivFun.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  exact props_of_closedEmb e.isClosedEmbedding

section UPts

open GlobalTheory.LKTrip

variable {C : Type} [Ring C] [Algebra ℚ C] [Module.Finite ℚ C] (star : C →+* Cᵐᵒᵖ)

theorem upts_props (R : Type) [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [SecondCountableTopology R] :
    LocallyCompactSpace (UPts star R) ∧ T2Space (UPts star R) ∧ TotallyDisconnectedSpace (UPts star R) ∧
      SecondCountableTopology (UPts star R) := by
  letI : TopologicalSpace (R ⊗[ℚ] C) := moduleTopology R (R ⊗[ℚ] C)
  haveI : IsModuleTopology R (R ⊗[ℚ] C) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[ℚ] C) := IsModuleTopology.isTopologicalRing R (R ⊗[ℚ] C)
  obtain ⟨m1, m2, m3, m4⟩ := module_props R (R ⊗[ℚ] C)
  obtain ⟨u1, u2, u3, u4⟩ := units_props (R ⊗[ℚ] C)
  obtain ⟨v1, v2, v3, v4⟩ := units_props R
  let f : C →ₗ[ℚ] C := (MulOpposite.opLinearEquiv ℚ).symm.toLinearMap ∘ₗ star.toRatAlgHom.toLinearMap
  have hσeq : (fun y : R ⊗[ℚ] C => (starT star R y).unop) = LinearMap.baseChange R f := by
    funext y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      rw [starT_tmul, LinearMap.baseChange_tmul]
      rfl
    | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add] at hx hy ⊢; rw [hx, hy]
  have hσ : Continuous (fun y : R ⊗[ℚ] C => (starT star R y).unop) := by
    rw [hσeq]
    exact IsModuleTopology.continuous_of_linearMap _
  have hcl : IsClosed ((UPts star R : Subgroup ((R ⊗[ℚ] C)ˣ × Rˣ)) : Set ((R ⊗[ℚ] C)ˣ × Rˣ)) := by
    have hs : ((UPts star R : Subgroup ((R ⊗[ℚ] C)ˣ × Rˣ)) : Set ((R ⊗[ℚ] C)ˣ × Rˣ)) =
        {x | ((x.1 : (R ⊗[ℚ] C)ˣ) : R ⊗[ℚ] C) * (starT star R ((x.1 : (R ⊗[ℚ] C)ˣ) : R ⊗[ℚ] C)).unop =
          algebraMap R (R ⊗[ℚ] C) ((x.2 : Rˣ) : R)} := rfl
    rw [hs]
    exact isClosed_eq ((Units.continuous_val.comp continuous_fst).mul (hσ.comp (Units.continuous_val.comp continuous_fst)))
      ((continuous_algebraMap R (R ⊗[ℚ] C)).comp (Units.continuous_val.comp continuous_snd))
  exact props_of_closedEmb hcl.isClosedEmbedding_subtypeVal

end UPts

end GlobalTheory.GfTop

namespace GlobalTheory.GfTop

open GlobalTheory.LKTrip IsDedekindDomain

section AfP

variable (p : ℕ)

theorem t2Space_afP : T2Space (AfP p) :=
  inferInstanceAs (T2Space (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]))

theorem finiteAdeleRingAway_locallyCompactSpace : LocallyCompactSpace (AfP p) :=
  (LevelExists.isCompact_intAfP p).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((LevelExists.isOpen_intAfP p).mem_nhds (LevelExists.intAfP p).zero_mem)

theorem finiteAdeleRingAway_totallyDisconnectedSpace : TotallyDisconnectedSpace (AfP p) :=
  td_of_inj (X := Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ])
    (f := fun x => (x : ∀ v : AwayP p, v.1.adicCompletion ℚ)) RestrictedProduct.continuous_coe
    (fun x y h => RestrictedProduct.ext _ _ fun i => congrFun h i)

theorem countable_awayP : Countable (AwayP p) := by
  have hI : Countable (Ideal ℤ) := by
    have hs : Function.Surjective (fun n : ℤ => Ideal.span {n}) := fun I =>
      ⟨Submodule.IsPrincipal.generator I, Ideal.span_singleton_generator I⟩
    exact hs.countable
  have hi : Function.Injective (fun v : AwayP p => v.1.asIdeal) := fun v w h =>
    Subtype.ext (HeightOneSpectrum.ext h)
  exact hi.countable

theorem compl_sc (v : HeightOneSpectrum ℤ) : SecondCountableTopology (v.adicCompletion ℚ) := by
  haveI : Fact ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ).Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  exact (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.isEmbedding.secondCountableTopology

theorem finiteAdeleRingAway_secondCountableTopology : SecondCountableTopology (AfP p) := by
  haveI := countable_awayP p
  haveI : ∀ v : AwayP p, SecondCountableTopology (v.1.adicCompletion ℚ) := fun v => compl_sc v.1
  have hAopen : ∀ v : AwayP p, IsOpen ((v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) :=
    fun v => Valued.isOpen_valuationSubring _
  have hS : ∀ S : Finset (AwayP p), Filter.cofinite ≤ Filter.principal ((S : Set (AwayP p))ᶜ) := fun S =>
    Filter.le_principal_iff.2 S.finite_toSet.compl_mem_cofinite
  let U : Finset (AwayP p) → Set (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]) :=
    fun S => Set.range (RestrictedProduct.inclusion (fun v : AwayP p => v.1.adicCompletion ℚ)
      (fun v : AwayP p => (v.1.adicCompletionIntegers ℚ : Set (v.1.adicCompletion ℚ))) (hS S))
  have hUo : ∀ S, IsOpen (U S) := fun S =>
    (RestrictedProduct.isOpenEmbedding_inclusion_principal hAopen (hS S)).isOpen_range
  have hsc : ∀ S, SecondCountableTopology (U S) := fun S => by
    haveI : SecondCountableTopology (Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]_[
        Filter.principal ((S : Set (AwayP p))ᶜ)]) :=
      RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
    exact (RestrictedProduct.isOpenEmbedding_inclusion_principal hAopen
      (hS S)).isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have hcov : ⋃ S, U S = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨(Filter.eventually_cofinite.1 x.2).toFinset, ?_⟩
    show x ∈ Set.range _
    rw [RestrictedProduct.range_inclusion]
    refine Filter.eventually_principal.2 fun i hi => ?_
    by_contra h
    exact hi (by rw [Finset.mem_coe, Set.Finite.mem_toFinset]; exact h)
  exact @TopologicalSpace.secondCountableTopology_of_countable_cover _ _ _ _ U hsc hUo hcov

end AfP

end GlobalTheory.GfTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryElementaryDivisorsInertPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryElementaryDivisorsInertPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InertExist

section Local

open GlobalTheory.SelfDualGenus GlobalTheory.PlaceComp GlobalTheory.HeckeLabels

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem mem_stdLat_iff {n : ℕ} (x : Fin n → E) :
    x ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)) ↔ ∀ i, IsIntegral ℤ (x i) := by
  show x ∈ Formalism.L2.Col.stdLat E n ↔ _
  simp only [Formalism.L2.Col.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  refine forall_congr' fun i => ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun h => ⟨⟨x i, h⟩, rfl⟩⟩

theorem antiJ_herm (n : ℕ) (a b : Fin n) :
    ReciprocityTheory.ChartRestriction.G.FD.cc (Formalism.UG.antiJ E n a b) = Formalism.UG.antiJ E n b a := by
  simp only [Formalism.UG.antiJ, add_comm b.val a.val]
  split_ifs <;> simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, map_one, map_zero]

theorem antiJ_det_ne_zero (n : ℕ) : (Formalism.UG.antiJ E n).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (GlobalTheory.DualDivU.antiJ_sq (L := E) (n := n))
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem selfDual_antiJ (n : ℕ) (x : Fin n → E) :
    x ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)) ↔
      ∀ y ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)),
        IsIntegral ℤ (ReciprocityTheory.ChartRestriction.G.FD.herm (Formalism.UG.antiJ E n) x y) := by
  rw [mem_stdLat_iff]
  constructor
  · intro hx y hy
    rw [mem_stdLat_iff] at hy
    refine IsIntegral.sum _ fun a _ => IsIntegral.sum _ fun b _ => ?_
    refine ((hx a).mul ?_).mul ?_
    · unfold Formalism.UG.antiJ; split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    · exact (hy b).map (IsCMField.complexConj E : E →+* E).toIntAlgHom
  · intro h i
    have hy : (Pi.single i.rev (1 : E) : Fin n → E) ∈ (Formalism.L2.Col.stdLat E n : Set (Fin n → E)) := by
      rw [mem_stdLat_iff]
      intro j
      by_cases hj : j = i.rev
      · subst hj; simpa using isIntegral_one
      · simpa [hj] using isIntegral_zero
    have := h _ hy
    convert this using 1
    simp [ReciprocityTheory.ChartRestriction.G.FD.herm, Formalism.UG.antiJ, Pi.single_apply, ReciprocityTheory.ChartRestriction.G.FD.cc]
    rw [Finset.sum_eq_single i]
    · rw [if_pos (by have := i.2; omega)]
    · intro b _ hb
      rw [if_neg]
      intro hc; apply hb; ext; have := i.2; have := b.2; omega
    · intro h; exact absurd (Finset.mem_univ i) h

theorem locLattice_le {n : ℕ} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    {x : Fin n → LocAlg v} (hx : x ∈ locLattice v (Formalism.L2.Col.stdLat E n)) (i : Fin n) : x i ∈ locOrder v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, (z : E) = y i := ⟨⟨y i, (mem_stdLat_iff y).1 hy i⟩, rfl⟩
    show locEmb v (y i) ∈ locOrder v
    rw [← hz]
    exact locEmb_mem_locOrder v z
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Subalgebra.smul_mem _ hx c

theorem mulVec_int {R : Type} [CommRing R] {O : Subring R} {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hM : ∀ i j, M i j ∈ O) {z : Fin n → R} (hz : ∀ i, z i ∈ O) (i : Fin n) : (M *ᵥ z) i ∈ O := by
  show ∑ j, M i j * z j ∈ O
  exact O.sum_mem fun j _ => mul_mem (hM i j) (hz j)

theorem single_int {R : Type} [CommRing R] {O : Subring R} {n : ℕ} (j i : Fin n) :
    (Pi.single j (1 : R) : Fin n → R) i ∈ O := by
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem exists_antiFrame [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (hc : CMData (maximalRealSubfield E) E) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (n : ℕ) :
    ∃ h : GL (Fin n) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E),
      Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) h.1 *
        (Formalism.UG.antiJ E n).map (inclR (Fv (maximalRealSubfield E) v)) * h.1 = 1 ∧
      (∀ i j, h.1 i j ∈ ordAt E v) ∧ ∀ i j, (h⁻¹).1 i j ∈ ordAt E v := by
  obtain ⟨h, h1, h2⟩ := exists_orthonormal_frame (antiJ_herm n) (antiJ_det_ne_zero n)
    ⟨Formalism.L2.Col.stdLat_lattice.fg, by
      rw [Formalism.L2.Col.stdLat_eq_span, Submodule.span_span_of_tower]
      convert (Pi.basisFun E (Fin n)).span_eq using 1
      congr 2
      ext i
      exact congrFun (Pi.basisFun_apply E (Fin n) i).symm _⟩ (selfDual_antiJ n) v
  have hs : ∀ j, (Pi.single j (1 : LocAlg v) : Fin n → LocAlg v) ∈ locLattice v (Formalism.L2.Col.stdLat E n) := by
    intro j
    refine Submodule.subset_span ⟨Pi.single j 1, ?_, ?_⟩
    · rw [SetLike.mem_coe, ← SetLike.mem_coe, mem_stdLat_iff]
      intro i
      by_cases hi : i = j
      · subst hi; simpa using isIntegral_one
      · simpa [hi] using isIntegral_zero
    · funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
  refine ⟨h, ?_, fun i j => ?_, fun i j => ?_⟩
  · have h3 := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc,
      Matrix.transpose_one] at h3
    have hT : ((Formalism.UG.antiJ E n).map (locEmb v))ᵀ = (Formalism.UG.antiJ E n).map (locEmb v) := by
      ext a b; simp only [Matrix.transpose_apply, Matrix.map_apply, Formalism.UG.antiJ, add_comm b.val a.val]
    rw [hT] at h3
    exact h3
  · rw [mem_ordAt_iff]
    have hm : (fun k => (h.1 *ᵥ Pi.single j 1) k) ∈ locLattice v (Formalism.L2.Col.stdLat E n) := by
      rw [h2]
      intro k
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      exact single_int (O := (locOrder v).toSubring) j k
    have := locLattice_le v hm i
    rw [Matrix.mulVec_single_one] at this
    exact this
  · rw [mem_ordAt_iff]
    have := (h2 _).1 (hs j) i
    rw [Matrix.mulVec_single_one] at this
    exact this

theorem exists_std [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    (hc : CMData (maximalRealSubfield E) E) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
    (n : ℕ) {ϖ : E} (h0 : ϖ ≠ 0) (hσ : hc.sig ϖ = ϖ) (d : ℕ → ℤ) (hd : ∀ i : Fin n, d i.rev.1 = -d i.1) :
    ∃ u ∈ Formalism.UG.UJ (sigR (Fv (maximalRealSubfield E) v) hc.sig) (1 : Matrix (Fin n) (Fin n) _),
      StdDiv (ordAt E v) 1 (fun i : Fin n => inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.1)) u.1 := by
  obtain ⟨h, hh, hi, hi'⟩ := exists_antiFrame hc v n
  have hσι : ∀ x : E, sigR (Fv (maximalRealSubfield E) v) hc.sig (inclR (Fv (maximalRealSubfield E) v) x) =
      inclR (Fv (maximalRealSubfield E) v) (hc.sig x) := fun x => by
    show (Algebra.TensorProduct.map (AlgHom.id _ _) hc.sig) ((1 : Fv (maximalRealSubfield E) v) ⊗ₜ x) =
      (1 : Fv (maximalRealSubfield E) v) ⊗ₜ hc.sig x
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  let t : Fin n → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E :=
    fun i => inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.1)
  let t' : Fin n → Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E :=
    fun i => inclR (Fv (maximalRealSubfield E) v) (ϖ ^ (-d i.1))
  have tt : ∀ i, t i * t' i = 1 := fun i => by
    simp only [t, t', ← map_mul, ← zpow_add₀ h0, add_neg_cancel, zpow_zero, map_one]
  let T : GL (Fin n) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E) :=
    ⟨Matrix.diagonal t, Matrix.diagonal t',
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact tt i,
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [mul_comm]; exact tt i⟩
  have hT : T ∈ Formalism.UG.UJ (sigR (Fv (maximalRealSubfield E) v) hc.sig)
      ((Formalism.UG.antiJ E n).map (inclR (Fv (maximalRealSubfield E) v))) := by
    show Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) (Matrix.diagonal t) * _ * Matrix.diagonal t = _
    rw [Formalism.UG.cT, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
    by_cases hij : i.val + j.val + 1 = n
    · have hj : j = i.rev := Fin.ext (by rw [Fin.val_rev]; omega)
      subst hj
      simp only [Formalism.UG.antiJ, if_pos hij, map_one, mul_one]
      show sigR (Fv (maximalRealSubfield E) v) hc.sig (inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.1)) *
        inclR (Fv (maximalRealSubfield E) v) (ϖ ^ d i.rev.1) = 1
      rw [hσι, map_zpow₀, hσ, hd, ← map_mul, ← zpow_add₀ h0, add_neg_cancel, zpow_zero, map_one]
    · simp only [Formalism.UG.antiJ, if_neg hij, map_zero, mul_zero, zero_mul]
  have hu := conj_mem_UJ _ hh hT
  have hTv : ∀ w, T.1 *ᵥ w = t * w := fun w => funext fun k => by
    show (Matrix.diagonal t *ᵥ w) k = t k * w k
    rw [Matrix.mulVec_diagonal]
  refine ⟨h⁻¹ * T * h, hu, (h⁻¹).1, fun z hz i => ?_, fun y hy => ⟨h.1 *ᵥ y, mulVec_int hi hy, ?_⟩,
    fun y hy => ⟨h.1 *ᵥ y, mulVec_int hi hy, ?_⟩, fun z hz => ⟨(h⁻¹).1 *ᵥ z, mulVec_int hi' hz, ?_⟩⟩
  · rw [one_smul]; exact mulVec_int hi' hz i
  · rw [one_smul, one_smul, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · rw [one_smul, one_smul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hTv]
  · have hz' : h.1 *ᵥ ((h⁻¹).1 *ᵥ z) = z := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [one_smul, one_smul, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz', hTv]

end Local

section Host

open GlobalTheory.PlaceComp

theorem exists_suppF_divAt : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (x : 𝓞 D.host.F) (ϖ : 𝓞 D.host.E) (d : List ℤ), IsPrimeIdem P e e → (ϖ : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.length = V.rank → dualLab d = d → ∃ g : GA D V, SuppF V e g ∧ DivAt V e (ϖ : D.host.E) d g := by
  intro D V P e x ϖ d hP hx h1 h2 hlen hdual
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  haveI := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  obtain ⟨v, hf, hef⟩ : ∃ v, GlobalTheory.PlaceComp.IsIdemOf D.host.E v e ∧ e * e = e := by
    rcases id hP with ⟨⟨⟨a1, a2, v, ε, ⟨a, rfl, b1, b2⟩, a3⟩, -⟩, he⟩ | ⟨-, ⟨v, ε, ⟨a, rfl, b1, b2⟩, a3⟩, -⟩
    · rw [← he] at a3
      exact ⟨v, a3 ▸ GlobalTheory.PlaceComp.isIdemOf_algebraMap b1 b2, ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e e hP).1⟩
    · exact ⟨v, a3 ▸ GlobalTheory.PlaceComp.isIdemOf_algebraMap b1 b2, ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e e hP).1⟩
  have h0 : (ϖ : D.host.E) ≠ 0 := fun h => h2 (by
    rw [show ϖ = 0 from Subtype.ext h]
    exact zero_mem _)
  have hσ : D.sp.cm.sig (ϖ : D.host.E) = ϖ := by
    rw [hx]
    exact D.sp.cm.sig.commutes _
  have hd : ∀ i : Fin V.rank, d.getD i.rev.1 0 = -d.getD i.1 0 := fun i => by
    have := GlobalTheory.DualDivU.getD_dualLab d hlen i
    rw [hdual] at this
    rw [this, neg_neg]
  obtain ⟨u, hu, hs⟩ := GlobalTheory.InertExist.exists_std D.sp.cm v V.rank h0 hσ (fun i => d.getD i 0) hd
  obtain ⟨g, hg, hg'⟩ := (GlobalTheory.HeckeLabels.exists_div_iff (E := D.host.E) D.sp.cm V hf hef (ϖ : D.host.E)
    (fun i => d.getD i 0) rfl).2 ⟨u, hu, by rw [hf.2.1]; exact hs⟩
  exact ⟨g, hg, hlen, hg'⟩

end Host

end GlobalTheory.InertExist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryElementaryDivisorsInertPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_elementaryDivisors_inertPrime : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (x : 𝓞 D.host.F) (ϖ : 𝓞 D.host.E) (d : List ℤ), IsPrimeIdem P e e → (ϖ : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.length = V.rank → dualLab d = d → ∃ g : GA D V, SuppF V e g ∧ DivAt V e (ϖ : D.host.E) d g := by
  first | exact @GlobalTheory.InertExist.exists_suppF_divAt | exact GlobalTheory.InertExist.exists_suppF_divAt | (intros; apply GlobalTheory.InertExist.exists_suppF_divAt <;> assumption)
end
end
