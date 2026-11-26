module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestric
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestric
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.PcRes

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (pc P h hN hF hS).Dpcris ρ = Dcris (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) ∧ ((pc P h hN hF hS).IsPotCrys ρ ↔ IsCrys (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) := by
  intro l _ P K K' LL h hN hF hS V _ _ _ _ ρ
  have key : (pc P h hN hF hS).Dpcris ρ =
      Dcris (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) := by
    unfold PotCrysData.Dpcris Dcris
    exact (GKinEquiv h).surjective.iInf_congr (GKinEquiv h) (fun x => rfl)
  refine ⟨key, ?_⟩
  unfold PotCrysData.IsPotCrys IsCrys
  have key' : Dcris (pc P h hN hF hS).PD' ((pc P h hN hF hS).resH ρ) =
      Dcris (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) := key
  rw [key']

end GlobalTheory.PcRes
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestricStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentiallyCrystalline_module_eq_crystalline_restriction : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), (pc P h hN hF hS).Dpcris ρ = Dcris (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) ∧ ((pc P h hN hF hS).IsPotCrys ρ ↔ IsCrys (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) := by
  first | exact @GlobalTheory.PcRes.main | exact GlobalTheory.PcRes.main | (intros; apply GlobalTheory.PcRes.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenOfFgOfSpanEqTop
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.Cyc

theorem isOpen_of_fg_of_span_eq_top {LL O V : Type} [Field LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] [TopologicalSpace V] [IsModuleTopology LL V]
    (hO : IsOpen (Set.range (algebraMap O LL))) (M : Submodule O V) (hfg : M.FG)
    (hspan : Submodule.span LL (M : Set V) = ⊤) : IsOpen (M : Set V) := by
  obtain ⟨n, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  have hbM : ∀ i, b i ∈ M := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
  have hsurj : Function.Surjective (Fintype.linearCombination LL b) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, ← hspan, ← hb,
      Submodule.span_span_of_tower]
  have hopen : IsOpenMap (Fintype.linearCombination LL b) :=
    IsModuleTopology.isOpenMap_of_surjective hsurj
  haveI := IsModuleTopology.topologicalAddGroup LL V
  have hU : IsOpen (Set.pi Set.univ fun _ : Fin n => Set.range (algebraMap O LL)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => hO
  refine M.toAddSubgroup.isOpen_of_mem_nhds (g := 0)
    (Filter.mem_of_superset ((hopen _ hU).mem_nhds ⟨0, fun _ _ => ⟨0, by simp⟩, map_zero _⟩) ?_)
  rintro _ ⟨x, hx, rfl⟩
  rw [Fintype.linearCombination_apply]
  refine M.sum_mem fun i _ => ?_
  obtain ⟨a, ha⟩ := hx i (Set.mem_univ i)
  rw [← ha, algebraMap_smul]
  exact M.smul_mem a (hbM i)

theorem locLat_isOpen : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp : Type} [Field Qp] [TopologicalSpace Qp] {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O → ∀ T : LocLat G Qp LL O, IsOpen (T.L.T : Set T.V) := by
  intro G _ _ Qp _ _ LL _ _ _ O _ _ h T
  haveI := h.2.2.2.1
  exact isOpen_of_fg_of_span_eq_top h.2.2.2.2 T.L.T T.L.fg T.L.span

end GlobalTheory.Cyc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualFamiliesContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualFamiliesContinuous
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass.FamCont

theorem epsU_cont {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) :
    Continuous fun g => ((epsU N i g : (N.O i)ˣ) : N.O i) := by
  have h : ∀ g, ((epsU N i g : (N.O i)ˣ) : N.O i) =
      ((N.chi i 1 g : (N.O i)ˣ) : N.O i) * ((N.chi i 2 g⁻¹ : (N.O i)ˣ) : N.O i) := by
    intro g
    have := R.rank_add_five_le
    rw [← Units.val_mul, N.chi_def i 2 (by omega) (by omega)]
    simp [Glob.epsO]
  simp only [h]
  exact (N.chi_cont i 1).mul ((N.chi_cont i 2).comp continuous_inv)

theorem stepCont : StepCont := by
  intro D i r hr x
  have hc := (hr x).1
  constructor
  · have h1 : Continuous fun g : GE D.nd => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) :=
      (D.nd.chi_cont i 1).comp continuous_inv
    refine (h1.smul hc).congr fun g => ?_
    simp [rTwO, twistM, rO]
  · have h1 := (D.nd.chi_cont i 1).mul (epsU_cont D.nd i)
    have h2 := (hc.comp continuous_inv).matrix_transpose
    refine (h1.smul h2).congr fun g => ?_
    rfl

end GlobalTheory.Pass.FamCont

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualFamiliesContinuousStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_dual_families_continuous : StepCont := by
  first | exact @GlobalTheory.Pass.FamCont.stepCont | exact GlobalTheory.Pass.FamCont.stepCont | (intros; apply GlobalTheory.Pass.FamCont.stepCont <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingSubgroupEquivBicontinuous
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

open scoped Topology

theorem fixingSubgroupEquiv_bicontinuous (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k ↥K] :
    Continuous (IntermediateField.fixingSubgroupEquiv K) ∧
      Continuous (IntermediateField.fixingSubgroupEquiv K).symm := by
  refine ⟨continuous_of_continuousAt_one _ ?_, continuous_of_continuousAt_one _ ?_⟩
  · rw [ContinuousAt, map_one, Filter.tendsto_def]
    intro s hs
    obtain ⟨E, hE, hEs⟩ := (krullTopology_mem_nhds_one_iff K Ω s).1 hs
    have : IsScalarTower k K E := ⟨fun a b x => Subtype.ext (smul_assoc a b (x : Ω))⟩
    have hE' : Module.Finite k E := Module.Finite.trans K E
    have hfin : FiniteDimensional k (E.restrictScalars k) := hE'
    rw [mem_nhds_subtype]
    refine ⟨(E.restrictScalars k).fixingSubgroup,
      (krullTopology_mem_nhds_one_iff k Ω _).2 ⟨E.restrictScalars k, hfin, subset_rfl⟩, ?_⟩
    intro σ hσ
    apply hEs
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x hx
  · rw [ContinuousAt, map_one, Filter.tendsto_def]
    intro s hs
    obtain ⟨u, hu, hus⟩ := (mem_nhds_subtype _ _ _).1 hs
    obtain ⟨E, hE, hEu⟩ := (krullTopology_mem_nhds_one_iff k Ω u).1 hu
    let F : IntermediateField K Ω := IntermediateField.extendScalars (le_sup_right : K ≤ E ⊔ K)
    have hk : FiniteDimensional k (E ⊔ K : IntermediateField k Ω) := inferInstance
    have : Module.Finite k F := hk
    have hF : FiniteDimensional K F := Module.Finite.of_restrictScalars_finite k K F
    refine (krullTopology_mem_nhds_one_iff K Ω _).2 ⟨F, hF, ?_⟩
    intro τ hτ
    apply hus
    apply hEu
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x
      ((IntermediateField.mem_extendScalars _).2 (le_sup_left (a := E) hx))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaOnAinf
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaOnAinf
noncomputable section

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem actC_eq_σC (g : GQ l) (y : PadicComplex l) : AI.actC g y = Formalism.Per.σC g y := by
  have hc : Continuous (AI.actC g) :=
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq hc (by apply GlobalTheory.RingIface.sigC_cont)
  | ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm

theorem actT_eq_σF (g : GQ l) (x : OCb l) : AI.actT g x = Formalism.Per.σF g x := by
  refine Perfection.ext fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff n x)
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g x n y hy.symm
  have h3 : y' = Formalism.Per.σO g y := Subtype.ext ((h1.trans (actC_eq_σC AI g y)).trans
    (by symm; apply GlobalTheory.RingIface.sigO_coe))
  refine h2.trans ?_
  rw [h3]
  exact (GlobalTheory.AdicMaps.coeff_galois l g x n y hy.symm).symm

theorem ζ_add_pow (j n : ℕ) : AI.ζ (j + n) ^ l ^ n = AI.ζ j := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ← add_assoc, AI.ζ_succ, ih]

theorem coeff_εroot (j n : ℕ) : PreTilt.coeff n (AI.εroot j) =
    Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (AI.ζ (j + n)) := by
  rw [← AI.ε_coeff, LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm, add_comm]

theorem untilt_εroot (j : ℕ) : (AI.εroot j).untilt = AI.ζ j := by
  refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : OC l)}) fun n => ?_
  refine ⟨AI.ζ (j + n), (coeff_εroot AI j n).symm, ?_⟩
  rw [ζ_add_pow]

theorem isTheta_fontaineTheta : IsTheta AI (WittVector.fontaineTheta (OC l) l) := by
  have hprim : IsPrimitiveRoot (((frobeniusEquiv (OCb l) l).symm AI.ε).untilt) l := by
    have h : ((frobeniusEquiv (OCb l) l).symm AI.ε).untilt = AI.ζ 1 := untilt_εroot AI 1
    rw [h]
    have h1 : AI.ζ 1 ^ l = 1 := (AI.ζ_succ 0).trans AI.ζ_zero
    have h2 := IsPrimitiveRoot.orderOf (AI.ζ 1)
    rwa [orderOf_eq_prime h1 AI.ζ_one] at h2
  refine ⟨fun x y h => ?_, ?_, fun g a => ?_, fun a => ?_, fun j => ?_⟩
  · rw [← Ideal.Quotient.eq, WittVector.fontaineTheta_teichmuller, ← h]
    exact PreTilt.mk_untilt_eq_coeff_zero x
  · exact ReciprocityTheory.PGsh.Ainf.theta_surj l (OC l) (PadicComplexInt.integers l)
  · have e : AI.actW g a = Formalism.Per.σA g a := WittVector.ext fun n =>
      (actT_eq_σF AI g (a.coeff n)).trans (by symm; apply GlobalTheory.RingIface.sigA_coeff)
    rw [e, actC_eq_σC]
    exact (congrArg Subtype.val (GlobalTheory.RingBasics.θ_σA g a)).trans (by apply GlobalTheory.RingIface.sigO_coe)
  · rw [← RingHom.mem_ker,
      ReciprocityTheory.PGsh.Ainf.ker_theta l (OC l) (PadicComplexInt.integers l) AI.ε hprim,
      Ideal.mem_span_singleton]
    rfl
  · rw [WittVector.fontaineTheta_teichmuller, untilt_εroot]

theorem exists_isTheta : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    ∃ θ : Ainf l →+* OC l, IsTheta AI θ :=
  fun _ _ _ AI => ⟨_, isTheta_fontaineTheta AI⟩

end GlobalTheory.Cyc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaOnAinfStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fontaineTheta_on_Ainf : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), ∃ θ : Ainf l →+* OC l, IsTheta AI θ := by
  first | exact @GlobalTheory.Cyc.exists_isTheta | exact GlobalTheory.Cyc.exists_isTheta | (intros; apply GlobalTheory.Cyc.exists_isTheta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndepOnOfInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsExtra
namespace GlobalTheory.SimpStatement

open Finset

theorem main {K B W G ι : Type} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [AddCommGroup W] [Module B W] [Module K W] [IsScalarTower K B W] [Module.IsTorsionFree B W]
    (a : G → B → B) (σ : G → W →+ W)
    (hσ : ∀ (g : G) (b : B) (w : W), (σ g : W → W) (b • w) = a g b • (σ g : W → W) w)
    (ha : ∀ (b b' : B), b ≠ (0 : B) → (∀ (g : G), b * a g b' = a g b * b') →
      ∃ (c : K), b' = (Algebra.algebraMap K B : K → B) c * b)
    (v : ι → W) (hv : ∀ (g : G) (i : ι), (σ g : W → W) (v i) = v i)
    (s : Finset ι) (hK : LinearIndepOn K v (↑s : Set ι)) :
    LinearIndepOn B v (↑s : Set ι) := by
  classical

  have key : ∀ T : Finset ι, T ⊆ s → ∀ f : ι → B, ∑ i ∈ T, f i • v i = 0 → ∀ i ∈ T, f i = 0 := by
    intro T
    induction T using Finset.strongInduction with
    | H T ih =>
      intro hTs f hf
      by_contra hne
      push_neg at hne
      obtain ⟨i₀, hi₀, hfi₀⟩ := hne

      have hrel : ∀ j ∈ T, ∀ g : G, f i₀ * a g (f j) = a g (f i₀) * f j := by
        intro j hj g
        set f' : ι → B := fun i => f i₀ * a g (f i) - a g (f i₀) * f i with hf'
        have hsum : ∑ i ∈ T, f' i • v i = 0 := by
          have h1 : ∑ i ∈ T, a g (f i) • v i = 0 := by
            have := congrArg (σ g : W → W) hf
            set_option synthInstance.maxHeartbeats 100000 in
              rw [map_sum, map_zero] at this
            rw [← this]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hσ, hv]
          simp only [hf', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, h1, hf,
            smul_zero, sub_zero]
        have hf'i₀ : f' i₀ = 0 := by simp only [hf']; ring
        have hsum' : ∑ i ∈ T.erase i₀, f' i • v i = 0 := by
          rw [← Finset.add_sum_erase T _ hi₀, hf'i₀, zero_smul, zero_add] at hsum
          exact hsum
        by_cases hj0 : j = i₀
        · subst hj0; ring
        · have := ih (T.erase i₀) (Finset.erase_ssubset hi₀)
            ((Finset.erase_subset _ _).trans hTs) f' hsum' j (Finset.mem_erase.2 ⟨hj0, hj⟩)
          simp only [hf'] at this
          exact sub_eq_zero.1 this
      have hc : ∀ j ∈ T, ∃ c : K, f j = (Algebra.algebraMap K B : K → B) c * f i₀ :=
        fun j hj => ha (f i₀) (f j) hfi₀ (hrel j hj)
      choose! c hc using hc
      have hsumK : ∑ i ∈ T, c i • v i = 0 := by
        have : f i₀ • ∑ i ∈ T, c i • v i = 0 := by
          rw [← hf, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [hc i hi, mul_comm, mul_smul, smul_comm]
          rw [algebraMap_smul]
          exact smul_comm (c i) (f i₀) (v i)
        exact (smul_eq_zero_iff_right hfi₀).1 this
      have hKT : LinearIndepOn K v (↑T : Set ι) := hK.mono (by exact_mod_cast hTs)
      have hci₀ := (linearIndepOn_finset_iff.1 hKT) c hsumK i₀ hi₀
      apply hfi₀
      rw [hc i₀ hi₀, hci₀, map_zero, zero_mul]
  exact linearIndepOn_finset_iff.2 (key s subset_rfl)

end GlobalTheory.SimpStatement
end

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.Per.FontaineBound

theorem linearIndepOn_of_invariant {K B W G ι : Type} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [AddCommGroup W] [Module B W] [Module K W] [IsScalarTower K B W] [Module.IsTorsionFree B W]
    (a : G → B → B) (σ : G → W →+ W) (hσ : ∀ g b w, σ g (b • w) = a g b • σ g w)
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * a g b' = a g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (v : ι → W) (hv : ∀ g i, σ g (v i) = v i)
    (s : Finset ι) (h : LinearIndepOn K v s) : LinearIndepOn B v s := by
  first
  | (rename_i h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13; revert K B W G ι h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 a σ hσ hreg v hv s h; exact @_root_.GlobalTheory.SimpStatement.main)
  | exact @_root_.GlobalTheory.SimpStatement.main
  | exact _root_.GlobalTheory.SimpStatement.main
  | (apply _root_.GlobalTheory.SimpStatement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SimpStatement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SimpStatement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SimpStatement.main ..)

section General

variable {G Qp K B LL V : Type} [Group G] [Field Qp] [Field K] [Algebra Qp K] [CommRing B] [IsDomain B]
  [Algebra Qp B] [Algebra K B] [IsScalarTower Qp K B] [Field LL] [Algebra Qp LL]
  [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def invs (act : G →* (B ≃ₐ[K] B)) (ρ : Representation LL G V) : Submodule LL (V ⊗[Qp] B) :=
  ⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (ρ g)
    (((act g).toAlgHom.toLinearMap).restrictScalars Qp) - LinearMap.id)

theorem finite_finrank_le_base [FiniteDimensional Qp K] [FiniteDimensional Qp V] (act : G →* (B ≃ₐ[K] B))
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * act g b' = act g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (ρ : Representation LL G V) :
    Module.Finite Qp (invs (Qp := Qp) act ρ) ∧
      finrank Qp (invs (Qp := Qp) act ρ) ≤ finrank Qp K * finrank Qp V := by
  let σ : G → B ⊗[Qp] V →ₗ[Qp] B ⊗[Qp] V := fun g =>
    TensorProduct.map (((act g).toAlgHom.toLinearMap).restrictScalars Qp) ((ρ g).restrictScalars Qp)
  have hσ : ∀ g (b : B) w, σ g (b • w) = act g b • σ g w := by
    intro g b w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  let U : Submodule K (B ⊗[Qp] V) :=
    { carrier := {x | ∀ g, σ g x = x}
      zero_mem' := fun g => map_zero _
      add_mem' := fun hx hy g => by rw [map_add (f := _), hx g, hy g]
      smul_mem' := fun c x hx g => by
        rw [← algebraMap_smul B c x, hσ, hx g, AlgEquiv.commutes] }
  have hr : Module.rank K U ≤ finrank Qp V := by
    refine rank_le fun s hs => ?_
    have h1 : LinearIndepOn K (fun x : U => (x : B ⊗[Qp] V)) s := hs.map' U.subtype U.ker_subtype
    have h2 := linearIndepOn_of_invariant (fun g b => act g b) (fun g => (σ g).toAddMonoidHom) hσ hreg
      (fun x : U => (x : B ⊗[Qp] V)) (fun g x => x.2 g) s h1
    simpa using LinearIndependent.fintype_card_le_finrank h2
  haveI : Module.Finite K U := by
    rw [← Module.rank_lt_aleph0_iff]
    exact lt_of_le_of_lt hr Cardinal.natCast_lt_aleph0
  have hr' : finrank K U ≤ finrank Qp V := finrank_le_of_rank_le hr
  haveI : Module.Finite Qp U := Module.Finite.trans K U
  have hc : ∀ g x, σ g (TensorProduct.comm Qp V B x) =
      TensorProduct.comm Qp V B (AlgebraTensorModule.map (ρ g)
        (((act g).toAlgHom.toLinearMap).restrictScalars Qp) x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  let f : invs (Qp := Qp) act ρ →ₗ[Qp] U :=
    { toFun := fun x => ⟨TensorProduct.comm Qp V B x, fun g => by
        have := x.2
        simp only [invs, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.id_apply, sub_eq_zero] at this
        rw [hc, this g]⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun c x => Subtype.ext (map_smul (TensorProduct.comm Qp V B) c _) }
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext ((TensorProduct.comm Qp V B).injective (congrArg Subtype.val h))
  refine ⟨Module.Finite.of_injective f hf, (LinearMap.finrank_le_finrank_of_injective hf).trans ?_⟩
  rw [← Module.finrank_mul_finrank Qp K U]
  exact Nat.mul_le_mul_left _ hr'

theorem finite_finrank_le [FiniteDimensional Qp K] [FiniteDimensional Qp LL] [FiniteDimensional LL V]
    (act : G →* (B ≃ₐ[K] B))
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * act g b' = act g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (ρ : Representation LL G V) :
    Module.Finite LL (invs (Qp := Qp) act ρ) ∧
      finrank LL (invs (Qp := Qp) act ρ) ≤ finrank Qp K * finrank LL V := by
  haveI : FiniteDimensional Qp V := Module.Finite.trans LL V
  obtain ⟨h1, h2⟩ := finite_finrank_le_base (Qp := Qp) act hreg ρ
  refine ⟨Module.Finite.of_restrictScalars_finite Qp LL _, ?_⟩
  rw [← Module.finrank_mul_finrank Qp LL (invs (Qp := Qp) act ρ), ← Module.finrank_mul_finrank Qp LL V,
    mul_left_comm] at h2
  exact Nat.le_of_mul_le_mul_left h2 Module.finrank_pos

end General

section Periods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

theorem frac_dR (hF : IsField BdR) (b b' : BdR) (hb : b ≠ 0)
    (h : ∀ g, b * PD.actdR g b' = PD.actdR g b * b') : ∃ c : K, b' = algebraMap K BdR c * b := by
  letI : Field BdR := hF.toField
  obtain ⟨c, hc⟩ := PD.invdR (b' / b) fun g => by
    have hg : PD.actdR g b ≠ 0 := (map_ne_zero _).2 hb
    rw [map_div₀, div_eq_div_iff hg hb, mul_comm, h g, mul_comm]
  exact ⟨c, by rw [hc, div_mul_cancel₀ _ hb]⟩


include PD in
theorem isDomain_cris (hF : IsField BdR) : IsDomain B :=
  letI : Field BdR := hF.toField
  PD.ι_inj.isDomain PD.ι.toRingHom

variable {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]

theorem ddR_finite_le (hF : IsField BdR) (ρ : Representation LL G V) :
    Module.Finite LL (DdR PD ρ) ∧ finrank LL (DdR PD ρ) ≤ finrank Qp K * finrank LL V := by
  haveI := hF.isDomain
  haveI := PD.finK
  exact finite_finrank_le PD.actdR (frac_dR PD hF) ρ

end Periods

section Tied

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}

theorem isField_of_tied (T : LocTied l P AI) : IsField P.R.BdR :=
  T.eD.toMulEquiv.isField (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1

theorem frac_cris (hfit : GlobalTheory.MemLoc.Fits T C) (hinj : C.TensorInj) (K : FinExt l) (b b' : P.R.B) (hb : b ≠ 0)
    (h : ∀ g, b * (P.PD K).actB g b' = (P.PD K).actB g b * b') :
    ∃ c : ↥(K0 K), b' = algebraMap ↥(K0 K) P.R.B c * b := by
  have hF : IsField P.R.BdR := isField_of_tied T
  obtain ⟨c, hc⟩ := frac_dR (P.PD K) hF ((P.PD K).ι b) ((P.PD K).ι b')
    (fun h0 => hb ((P.PD K).ι_inj (h0.trans (map_zero _).symm)))
    (fun g => by rw [← (P.PD K).ι_comm, ← (P.PD K).ι_comm, ← map_mul, ← map_mul, h g])
  have hcU : (c : Om l) ∈ MaximalUnramifiedExtension l := by
    by_contra hn
    have hli : LinearIndependent ↥(MaximalUnramifiedExtension l) ![(1 : Om l), (c : Om l)] := by
      rw [LinearIndependent.pair_iff' one_ne_zero]
      intro a ha
      apply hn
      rw [← ha, Algebra.smul_def, mul_one]
      exact a.2
    have h0 := hinj 2 _ hli ![T.eB b', - T.eB b] (by
      have h1 := congrArg T.eD hc
      rw [map_mul, P.PD_ι, P.PD_ι, hfit.ι, hfit.ι] at h1
      have h2 : T.eD (algebraMap ↥K.1 P.R.BdR c) = C.oD (c : Om l) := hfit.o _
      rw [h2] at h1
      simp [Fin.sum_univ_two, h1]) 1
    apply hb
    apply T.eB.injective
    simpa using h0
  refine ⟨⟨c, c.2, hcU⟩, (P.PD K).ι_inj ?_⟩
  rw [map_mul, AlgHom.commutes, hc]
  rfl

theorem dcris_finite_le (hfit : GlobalTheory.MemLoc.Fits T C) (hinj : C.TensorInj) (K LL : FinExt l)
    (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) :
    Module.Finite ↥LL.1 (Dcris (P.PD K) ρ) ∧
      finrank ↥LL.1 (Dcris (P.PD K) ρ) ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V := by
  haveI := isDomain_cris (P.PD K) (isField_of_tied T)
  haveI := (P.PD K).finK₀
  haveI := LL.2
  exact finite_finrank_le (P.PD K).actB (frac_cris hfit hinj K) ρ

end Tied

end GlobalTheory.Per.FontaineBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegree
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.TrIdem

theorem zOf_coeff {G : Type} [Group G] [Fintype G] (χ : G → ℂ) (y : G) :
    (zOf χ).coeff y = χ 1 / (Fintype.card G : ℂ) * χ y⁻¹ := by
  simp only [zOf, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, MonoidAlgebra.single_apply,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem coeff_mul_zOf_one {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ) :
    (a * zOf χ).coeff 1 = χ 1 / (Fintype.card G : ℂ) * tr a χ := by
  rw [MonoidAlgebra.coeff_mul, Finsupp.sum_fintype _ _ (by simp)]
  simp only [tr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [zOf_coeff, mul_eq_one_iff_eq_inv', Finset.sum_ite_eq', Finset.mem_univ, if_true, inv_inv]
  ring

theorem trace_asAlgebraHom {G : Type} [Group G] [Fintype G] (V : FDRep ℂ G) (a : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ V (Representation.asAlgebraHom (k := ℂ) (V.ρ : Representation ℂ G V) a) =
      tr a V.character := by
  simp only [tr, Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, FDRep.character]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.sum_fintype _ _ (by simp), map_sum]
  simp

theorem tr_idem_nat {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ)
    (ha : a * a = a) (hχ : IsChar χ) : ∃ n : ℕ, tr a χ = n := by
  obtain ⟨V, hV⟩ := hχ
  have hc : V.character = χ := funext hV
  set f := Representation.asAlgebraHom (k := ℂ) (V.ρ : Representation ℂ G V) a with hf
  have hi : IsIdempotentElem f := by
    rw [IsIdempotentElem, hf, ← map_mul, ha]
  refine ⟨Module.finrank ℂ (LinearMap.range f), ?_⟩
  rw [← hc, ← trace_asAlgebraHom, ← hf]
  exact (LinearMap.IsIdempotentElem.isProj_range f hi).trace

theorem irr_one_pos {G : Type} [Group G] (χ : G → ℂ) (hχ : IsIrr χ) : ∃ d : ℕ, 0 < d ∧ χ 1 = d := by
  obtain ⟨V, hs, hV⟩ := hχ
  refine ⟨Module.finrank ℂ V, Nat.pos_of_ne_zero fun h => ?_, by rw [← hV, FDRep.char_one]⟩
  apply CategoryTheory.Simple.not_isZero V
  rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
  have : Subsingleton V := Module.finrank_zero_iff.mp h
  ext x
  exact Subsingleton.elim _ _

end GlobalTheory.GLq.TrIdem

theorem GlobalTheory.GLq.trIdem : ∀ (G : Type) [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ),
    (a * a = a → IsChar χ → ∃ n : ℕ, tr a χ = n) ∧ (IsIrr χ → ∃ d : ℕ, 0 < d ∧ χ 1 = d) ∧
      (a * zOf χ).coeff 1 = χ 1 / (Fintype.card G : ℂ) * tr a χ :=
  fun _ _ _ a χ => ⟨GlobalTheory.GLq.TrIdem.tr_idem_nat a χ, GlobalTheory.GLq.TrIdem.irr_one_pos χ,
    GlobalTheory.GLq.TrIdem.coeff_mul_zOf_one a χ⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegreeStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree : ∀ (G : Type) [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ), (a * a = a → IsChar χ → ∃ n : ℕ, tr a χ = n) ∧ (IsIrr χ → ∃ d : ℕ, 0 < d ∧ χ 1 = d) ∧ (a * zOf χ).coeff 1 = χ 1 / (Fintype.card G : ℂ) * tr a χ := by
  first | exact @GlobalTheory.GLq.trIdem | exact GlobalTheory.GLq.trIdem | (intros; apply GlobalTheory.GLq.trIdem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFilGradedSymbolToTateTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFilGradedSymbolToTateTwist
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

noncomputable section

namespace GlobalTheory.DeRhamSymbol

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem mem_iff (K : FinExt l) (a : ℤ) (x : P.R.BdR) :
    x ∈ (P.PD K).Fil a ↔ x ∈ (P.PD (botExt l)).Fil a := by
  have h := P.PD_Fil K (botExt l) a
  rw [← SetLike.mem_coe, h, SetLike.mem_coe]

theorem om_mem (x : Om l) : algebraMap (Om l) P.R.BdR x ∈ (P.PD (botExt l)).Fil 0 := by
  obtain ⟨K, hK⟩ : ∃ K : FinExt l, x ∈ K.1 := ⟨⟨IntermediateField.adjoin ℚ_[l] {x},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)⟩,
    IntermediateField.mem_adjoin_simple_self _ x⟩
  have h := ((P.PD K).Fil 0).smul_mem ⟨x, hK⟩ (P.PD K).one_mem
  rw [Algebra.smul_def, mul_one] at h
  exact (mem_iff K 0 _).1 h

theorem t_isUnit (P : LocPrime l) : IsUnit (P.ιB P.tB) := by
  have hu := (P.PD (botExt l)).t_unit
  rw [P.period_datum_t_eq] at hu
  exact hu.map P.ιB

def tU (P : LocPrime l) : P.R.BdRˣ := (t_isUnit P).unit

theorem tU_val : ((tU P : P.R.BdRˣ) : P.R.BdR) = P.ιB P.tB := rfl

theorem act_mem {a : ℤ} (g : GQ l) {x : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil a) :
    P.actQdR g x ∈ (P.PD (botExt l)).Fil a := by
  have := (P.PD (botExt l)).Fil_G ⟨g, mem_GK_bot g⟩ a x hx
  rwa [P.PD_actdR] at this

theorem actQdR_periodT_eq_cyclotomic_bottom (g : GQ l) :
    P.actQdR g (P.ιB P.tB) = algebraMap ℚ_[l] P.R.BdR (P.χQ g) * P.ιB P.tB := by
  have h := (P.PD (botExt l)).t_act ⟨g, mem_GK_bot g⟩
  rw [P.PD_actB, P.period_datum_t_eq, P.PD_χ] at h
  have h3 := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_bot g⟩ P.tB
  rw [P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR] at h3
  rw [← h3, h, map_smul, Algebra.smul_def]

theorem act_zpow (g : GQ l) (n : ℤ) :
    P.actQdR g ((tU P ^ n : P.R.BdRˣ) : P.R.BdR) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ n : ℚ_[l]ˣ) : ℚ_[l]) * ((tU P ^ n : P.R.BdRˣ) : P.R.BdR) := by
  have h : Units.map ((P.actQdR g : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) : P.R.BdR →* P.R.BdR) (tU P) =
      Units.map (algebraMap ℚ_[l] P.R.BdR : ℚ_[l] →* P.R.BdR) (P.χQ g) * tU P :=
    Units.ext (actQdR_periodT_eq_cyclotomic_bottom g)
  have h2 := congrArg (fun u : P.R.BdRˣ => ((u ^ n : P.R.BdRˣ) : P.R.BdR)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul] at h2
  rw [map_zpow P.χQ] at h2
  exact h2

variable {AI : LocAinf l P} (J : ThetaL P AI)
include J

theorem zpow_mem (n : ℤ) : ((tU P ^ n : P.R.BdRˣ) : P.R.BdR) ∈ (P.PD (botExt l)).Fil n := by
  have h1 : ((tU P : P.R.BdRˣ) : P.R.BdR) ∈ (P.PD (botExt l)).Fil 1 := by
    have := (P.PD (botExt l)).mem_filtration_one
    rwa [P.PD_ι, P.period_datum_t_eq] at this
  have h2 : (((tU P)⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ (P.PD (botExt l)).Fil (-1) := by
    obtain ⟨y, hy, e⟩ := (J.fil_succ_iff_mul_t (-1) 1).1 (by simpa using (P.PD (botExt l)).one_mem)
    rw [← tU_val] at e
    rwa [Units.inv_eq_of_mul_eq_one_right e.symm]
  induction n using Int.induction_on with
  | zero => simpa using (P.PD (botExt l)).one_mem
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul]
    exact (P.PD (botExt l)).Fil_mul _ _ _ _ ih h1
  | pred n ih =>
    rw [zpow_sub_one, Units.val_mul, sub_eq_add_neg]
    exact (P.PD (botExt l)).Fil_mul _ _ _ _ ih h2

theorem shift_iff (a b : ℤ) (x : P.R.BdR) :
    ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x ∈ (P.PD (botExt l)).Fil b ↔
      x ∈ (P.PD (botExt l)).Fil (a + b) := by
  constructor
  · intro h
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ (zpow_mem J a) h
    rwa [← mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
      one_mul] at this
  · intro h
    have := (P.PD (botExt l)).Fil_mul _ _ _ _ (zpow_mem J (-a)) h
    rwa [neg_add_cancel_left] at this


omit J in
theorem exists_symbol : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), ThetaL P AI →
    ∀ (K : FinExt l), ∃ sy : ℤ → P.R.BdR → PadicComplex l, ∀ a : ℤ,
      (∀ x ∈ (P.PD K).Fil a, ∀ y ∈ (P.PD K).Fil a, sy a (x + y) = sy a x + sy a y) ∧
      (∀ (c : Om l), ∀ x ∈ (P.PD K).Fil a,
        sy a (algebraMap (Om l) P.R.BdR c * x) = (c : PadicComplex l) * sy a x) ∧
      (∀ x ∈ (P.PD K).Fil a, sy a x = 0 ↔ x ∈ (P.PD K).Fil (a + 1)) ∧
      ∀ (g : GQ l), ∀ x ∈ (P.PD K).Fil a,
        sy a (P.actQdR g x) = chiC P.χQ a g * AI.actC g (sy a x) := by
  intro l _ P AI J K
  refine ⟨fun a x => J.θ (((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x), fun a => ?_⟩
  have key : ∀ x ∈ (P.PD K).Fil a,
      ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x ∈ (P.PD (botExt l)).Fil 0 := fun x hx =>
    (shift_iff J a 0 x).2 (by rw [add_zero]; exact (mem_iff K a x).1 hx)
  refine ⟨fun x hx y hy => ?_, fun c x hx => ?_, fun x hx => ?_, fun g x hx => ?_⟩
  · beta_reduce
    rw [mul_add, J.θ_add _ (key x hx) _ (key y hy)]
  · beta_reduce
    rw [mul_left_comm, J.θ_mul _ (om_mem c) _ (key x hx), J.θ_Om]
  · beta_reduce
    rw [J.θ_ker _ (key x hx), shift_iff J, mem_iff K]
  · beta_reduce
    have e : ((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * P.actQdR g x =
        algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l])) *
          P.actQdR g (((tU P ^ (-a) : P.R.BdRˣ) : P.R.BdR) * x) := by
      rw [← IsScalarTower.algebraMap_apply, map_mul, act_zpow, ← mul_assoc, ← mul_assoc,
        ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
        map_one, one_mul]
    rw [e, J.θ_mul _ (om_mem _) _ (act_mem g (key x hx)), J.θ_Om, J.θ_act g _ (key x hx)]
    rfl

end GlobalTheory.DeRhamSymbol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFilGradedSymbolToTateTwistStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deRhamFil_graded_symbol_to_tate_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), ThetaL P AI → ∀ (K : FinExt l), ∃ sy : ℤ → P.R.BdR → PadicComplex l, ∀ a : ℤ, (∀ x ∈ (P.PD K).Fil a, ∀ y ∈ (P.PD K).Fil a, sy a (x + y) = sy a x + sy a y) ∧ (∀ (c : Om l), ∀ x ∈ (P.PD K).Fil a, sy a (algebraMap (Om l) P.R.BdR c * x) = (c : PadicComplex l) * sy a x) ∧ (∀ x ∈ (P.PD K).Fil a, sy a x = 0 ↔ x ∈ (P.PD K).Fil (a + 1)) ∧ ∀ (g : GQ l), ∀ x ∈ (P.PD K).Fil a, sy a (P.actQdR g x) = chiC P.χQ a g * AI.actC g (sy a x) := by
  intro l _ P AI h K
  exact GlobalTheory.DeRhamSymbol.exists_symbol l P AI h K
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMemAdjoin
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.CentralIdem

theorem trace_mem_adjoin {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0) (hT : T ^ (n + 1) = T) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    LinearMap.trace ℂ V T ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ) := by
  haveI : NeZero n := ⟨hn⟩
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  apply Subalgebra.multiset_sum_mem
  intro μ hμ
  have hr : T.charpoly.IsRoot μ := Polynomial.isRoot_of_mem_roots hμ
  have he : T.HasEigenvalue μ := (Module.End.hasEigenvalue_iff_isRoot_charpoly T μ).2 hr
  obtain ⟨v, hv⟩ := he.exists_hasEigenvector
  have h1 := hv.pow_apply (n + 1)
  rw [hT, hv.apply_eq_smul] at h1
  have h2 : μ = μ ^ (n + 1) := smul_left_injective ℂ hv.2 h1
  by_cases h0 : μ = 0
  · rw [h0]; exact Subalgebra.zero_mem _
  · have h3 : μ ^ n = 1 := by
      rw [pow_succ] at h2
      exact mul_right_cancel₀ h0 (by rw [one_mul]; exact h2.symm)
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h3
    rw [← hi]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) _

theorem trace_lmul {Γ : Type} [Group Γ] [Finite Γ] (x : MonoidAlgebra ℂ Γ) :
    LinearMap.trace ℂ _ (Algebra.lmul ℂ (MonoidAlgebra ℂ Γ) x) = (Nat.card Γ : ℂ) * x.coeff 1 := by
  classical
  haveI := Fintype.ofFinite Γ
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis Γ ℂ), Matrix.trace]
  have : ∀ g : Γ, (LinearMap.toMatrix (MonoidAlgebra.basis Γ ℂ) (MonoidAlgebra.basis Γ ℂ)
      (Algebra.lmul ℂ (MonoidAlgebra ℂ Γ) x)).diag g = x.coeff 1 := by
    intro g
    rw [Matrix.diag, LinearMap.toMatrix_apply]
    have hb : MonoidAlgebra.basis Γ ℂ g = MonoidAlgebra.single g 1 := by simp
    rw [hb]
    change (x * MonoidAlgebra.single g (1 : ℂ)).coeff g = _
    rw [MonoidAlgebra.coeff_mul_single_apply]
    simp
  rw [Finset.sum_congr rfl fun g _ => this g]
  simp

theorem centralIdemCoeff : CentralIdemCoeff := by
  intro Γ _ _ e he hc ζ hζ h
  haveI : Module.Finite ℂ (MonoidAlgebra ℂ Γ) := Module.Finite.of_basis (MonoidAlgebra.basis Γ ℂ)
  set x : MonoidAlgebra ℂ Γ := MonoidAlgebra.single h⁻¹ (1 : ℂ) * e with hx
  have hcm : Commute (MonoidAlgebra.single h⁻¹ (1 : ℂ)) e := (hc _).symm
  have hid : IsIdempotentElem e := he
  have hp : x ^ (Nat.card Γ + 1) = x := by
    rw [hx, hcm.mul_pow, hid.pow_succ_eq, MonoidAlgebra.single_pow, one_pow, pow_succ,
      pow_card_eq_one', one_mul]
  have hT := trace_mem_adjoin (Algebra.lmul ℂ (MonoidAlgebra ℂ Γ) x) (n := Nat.card Γ)
    Nat.card_pos.ne' (by rw [← map_pow, hp]) hζ
  rw [trace_lmul, hx, MonoidAlgebra.coeff_single_mul_apply] at hT
  simpa using hT

end GlobalTheory.CentralIdem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobSubMulSurjective
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

namespace GlobalTheory.ArtinSchreierWitt

open Polynomial

theorem frob_sub_mul_surjective (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] [CharP k p]
    [PerfectRing k p] (h : ∀ c y : k, ∃ x : k, x ^ p - c * x = y) (c y : WittVector p k) :
    ∃ β : WittVector p k, WittVector.frobenius β - c * β = y := by
  have hc : IsAdicComplete (Ideal.span {(p : ℤ)}) (WittVector p k) := by
    rw [← IsAdicComplete.map_algebraMap_iff (S := WittVector p k), Ideal.map_span,
      Set.image_singleton, map_natCast]
    infer_instance
  let f : WittVector p k →ₗ[ℤ] WittVector p k :=
    (WittVector.frobenius (p := p) (R := k)).toAddMonoidHom.toIntLinearMap
      - (AddMonoidHom.mulLeft c).toIntLinearMap
  have hf : ∀ β, f β = WittVector.frobenius β - c * β := fun β => rfl
  have hs : Function.Surjective f := by
    refine surjective_of_mkQ_comp_surjective (I := Ideal.span {(p : ℤ)}) fun G => ?_
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ G
    obtain ⟨x, hx⟩ := h (c.coeff 0) (g.coeff 0)
    refine ⟨WittVector.teichmuller p x, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hf]
    have h0 : (WittVector.frobenius (WittVector.teichmuller p x)
        - c * WittVector.teichmuller p x - g) ∈ Ideal.span {(p : WittVector p k)} := by
      rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_sub, map_mul]
      simp only [WittVector.constantCoeff_apply, WittVector.coeff_frobenius_charP,
        WittVector.teichmuller_coeff_zero]
      rw [hx, sub_self]
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.1 h0
    rw [hu]
    have : (p : WittVector p k) * u = (p : ℤ) • u := by simp
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  obtain ⟨β, hβ⟩ := hs y
  exact ⟨β, (hf β).symm.trans hβ⟩

theorem monic_as (p : ℕ) [hp : Fact p.Prime] {k : Type} [CommRing k] [Nontrivial k] (c y : k) :
    (X ^ p - (C c * X + C y) : k[X]).Monic ∧ (X ^ p - (C c * X + C y) : k[X]).degree = p := by
  have h1 : (C c * X + C y : k[X]).degree < (p : WithBot ℕ) :=
    lt_of_le_of_lt degree_linear_le (by exact_mod_cast hp.out.one_lt)
  refine ⟨monic_X_pow_sub h1, ?_⟩
  rw [degree_sub_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]

theorem exists_root_field (p : ℕ) [hp : Fact p.Prime] {K : Type} [Field K] [IsAlgClosed K]
    (c y : K) : ∃ x : K, x ^ p - c * x = y := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ p - (C c * X + C y) : K[X]) (by
    rw [(monic_as p c y).2]; exact_mod_cast hp.out.ne_zero)
  refine ⟨x, ?_⟩
  simp only [IsRoot.def, eval_sub, eval_pow, eval_X, eval_add, eval_mul, eval_C] at hx
  linear_combination hx

theorem exists_root_ring (p : ℕ) [hp : Fact p.Prime] {O K : Type} [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [IsAlgClosed K]
    (c y : O) : ∃ x : O, x ^ p - c * x = y := by
  obtain ⟨x, hx⟩ := exists_root_field p (algebraMap O K c) (algebraMap O K y)
  have hi : IsIntegral O x := by
    refine ⟨X ^ p - (C c * X + C y), (monic_as p c y).1, ?_⟩
    simp only [eval₂_sub, eval₂_X_pow, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
    linear_combination hx
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  refine ⟨z, IsFractionRing.injective O K ?_⟩
  rw [map_sub, map_pow, map_mul, hx]

theorem fixed_frob (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (b : WittVector p K)
    (hb : WittVector.map (frobenius K p) b = b) : ∃ z : ℤ_[p], b = zlW p K z := by
  have h : ∀ n, ∃ a : ZMod p, ZMod.castHom (dvd_refl p) K a = b.coeff n := by
    intro n
    have h1 : (b.coeff n) ^ p = b.coeff n := by
      have := congrArg (fun w => WittVector.coeff w n) hb
      simpa [WittVector.map_coeff, frobenius_def] using this
    have h2 := (Subfield.mem_bot_iff_pow_eq_self K p).2 h1
    have h3 : (⊥ : Subfield K) ≤ (ZMod.castHom (dvd_refl p) K).fieldRange := bot_le
    exact h3 h2
  choose a ha using h
  refine ⟨WittVector.equiv p (WittVector.mk p a), ?_⟩
  ext n
  simp [zlW, WittVector.map_coeff, ← ha]

theorem main : ∀ (l : ℕ) [Fact l.Prime], (∀ y : WCb l, ∃ b, frobW l b - b = y) ∧ (∀ b : WCb l, frobW l b = b → ∃ z : ℤ_[l], b = algebraMap ℤ_[l] (WCb l) z) ∧ ∀ (c p : Ainf l), ∃ β : Ainf l, WittVector.frobenius β - c * β = p := by
  intro l _
  obtain ⟨hK, hV⟩ := GlobalTheory.T.isAlgClosed_tiltField_and_valuationRing l
  refine ⟨fun y => ?_, fun b hb => fixed_frob l (Cb l) b hb, fun c p => ?_⟩
  · obtain ⟨β, hβ⟩ := frob_sub_mul_surjective l (Cb l) (exists_root_field l) 1 y
    refine ⟨β, ?_⟩
    rw [one_mul, WittVector.frobenius_eq_map_frobenius] at hβ
    exact hβ
  · exact frob_sub_mul_surjective l (OCb l) (exists_root_ring l (K := Cb l)) c p

end GlobalTheory.ArtinSchreierWitt
end
