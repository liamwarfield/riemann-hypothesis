module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.LocLift
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ConstructionA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ConstructionB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.StdLatEqSpan
public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.GmapLocEqOfFrame

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeFinK
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.VecVMulVec
noncomputable section

namespace PI.FinKW

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst)
open Formalism.L2.SG.AdBridge

theorem psiV_tauF (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    psiV I v (tauF I z) =
      Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v) (AlgHom.id I.F I.E) (prF I z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tauF_tmul]
    simp only [psiV, prF, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.map_tmul]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem vecV_mulVec (I : AutInst) (h : HAd I) (v : HeightOneSpectrum (𝓞 I.F))
    (x : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :
    vecV I v (ofHAFin I h *ᵥ x) =
      ((Formalism.L2.SG.Sub.compV v (Formalism.UG.bc (prF I)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h)) :
          GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) : Matrix _ _ _) *ᵥ vecV I v x := by
  funext i
  simp only [vecV]
  have := RingHom.map_mulVec (psiV I v).toRingHom (ofHAFin I h) x i
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [this]
  congr 1
  ext a b
  simp [ofHAFin, Formalism.L2.SG.Sub.compV, Formalism.UG.bc, psiV_tauF]

theorem finK_of (hT : MemLocTo) (hF : MemLocFrom) (hS : LiftV) : PI.AdBridgeSteps.FinK := by
  intro I h
  have hL : ∀ x, x ∈ I.Lf ↔ ∀ v, vecV I v x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) :=
    fun x => ⟨hT I x, hF I x⟩
  constructor
  · intro hst v y
    obtain ⟨x, hxv, hxw⟩ := hS I v y
    have ex : x ∈ I.Lf ↔ y ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
      rw [hL x]
      constructor
      · intro H
        have := H v
        rwa [hxv] at this
      · intro H w
        by_cases hw : w = v
        · subst hw
          rwa [hxv]
        · rw [hxw w hw]
          exact zero_mem _
    have egx : ofHAFin I h *ᵥ x ∈ I.Lf ↔
        ((Formalism.L2.SG.Sub.compV v (Formalism.UG.bc (prF I)
          (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig I.J h)) :
            GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) : Matrix _ _ _) *ᵥ y ∈
          Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
      rw [hL]
      constructor
      · intro H
        have := H v
        rwa [vecV_mulVec, hxv] at this
      · intro H w
        rw [vecV_mulVec]
        by_cases hw : w = v
        · subst hw
          rwa [hxv]
        · rw [hxw w hw, Matrix.mulVec_zero]
          exact zero_mem _
    exact ex.symm.trans ((hst x).trans egx)
  · intro hK x
    rw [hL x, hL (ofHAFin I h *ᵥ x)]
    refine forall_congr' fun v => ?_
    rw [vecV_mulVec]
    exact hK v (vecV I v x)

end PI.FinKW
end
end

theorem adelic_compact_finite_places : PI.AdBridgeSteps.FinK :=
  PI.FinKW.finK_of PI.FinKW.LocTo.mem_local_lattice_iff (PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective)
    PI.FinKW.local_vector_lift
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.Assembly
noncomputable section

namespace PI.WHw

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem natW_antitone {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  unfold Formalism.BasicNotions.DomWeight.natW
  exact Int.toNat_le_toNat (by linarith [lam.anti hij])

theorem hwIrred_of (hA1 : StableClosedC) (hA2 : FixedKilledC) (hB1 : HWInClosedC)
    (hB2 : ClosedEqNablaC) : PI.HwIrred := by
  intro N lam
  have hν := natW_antitone lam
  have hsub : delSq ℂ N lam ≤ nablaSq ℂ N lam := weylLeDual ℂ N N le_rfl lam.natW hν
  have hclosed : RowDivClosed (delSq ℂ N lam) := fun a b k f hf =>
    weylRowDivStable ℂ N N le_rfl lam.natW a b k f hf
  have hhw : extremal ℂ N lam ∈ delSq ℂ N lam :=
    Submodule.subset_span ⟨[], rfl⟩
  refine ⟨(hB2 N N le_rfl lam.natW hν _ hsub hclosed hhw).symm, ?_, ?_⟩
  · intro U hU hst
    by_cases h0 : U = ⊥
    · exact Or.inl h0
    · exact Or.inr (hB2 N N le_rfl lam.natW hν U hU (hA1 N lam U hU hst)
        (hB1 N N le_rfl lam.natW hν U hU (hA1 N lam U hU hst) h0))
  · intro f hf hfix
    exact hwLine ℂ N N le_rfl lam.natW hν f hf (hA2 N lam f hf hfix)

end PI.WHw
end
end

theorem highest_weight_irreducible : PI.HwIrred :=
  PI.WHw.hwIrred_of PI.WHw.stable_subspace_closed PI.WHw.fixed_vectors_killed PI.WHw.highest_weight_in_closure
    PI.WHw.closure_eq_nabla
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UnimodGenus
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.Bridge
section -- merged from Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.ExistsIsomLoc
open NumberField Module

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L3

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_isom_loc (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    {I : Submodule (𝓞 K) V} {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) (p : Ideal (𝓞 K)) (hp : p.IsMaximal)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := K) p I) = Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  have hpos := isTotPosDef_of_ortho hK hs hI
  have hd : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hpos x hne φ
    rw [hx, map_zero] at this
    simp at this
  obtain ⟨e, -, hspan, rfl, he⟩ := hI
  have hS : WA.IsHermSemilocal (WA.locRing p) :=
    { star_mem := fun _ ha => WA.star_mem_locRing hp.isPrime ha
      frac := WA.frac_locRing p
      unram := WA.unram_locRing hK hp
      principal := WA.principal_locRing hK hp
      unit_or := fun a ha κ hκ μ hna hμ => WA.unit_or_locRing hp.isPrime a ha κ hκ μ hna hμ }
  obtain ⟨g, hg, hge⟩ := WA.exists_isom_frame hS hs hd
    (WA.isSelfDualMod_loc hL hp.isPrime hu) e he
  exact ⟨g, hg, WA.gmap_loc_eq_of_frame hp.isPrime hu hspan he hg hge⟩

end ReciprocityTheory.ChartRestriction.L3
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.UnimodLocalOfLocDual
open NumberField

noncomputable section

namespace PI.UG.W

theorem stdLat_isOrtho (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) :
    Formalism.HermitianLatticesTheory.IsOrthoLattice (hStd E n) (stdLat E n) n := by
  refine ⟨fun i => Pi.single i 1, ?_, ?_, ?_, ?_⟩
  · convert (Pi.basisFun E (Fin n)).linearIndependent using 1 <;> first | rfl | (funext i; simp)
  · convert (Pi.basisFun E (Fin n)).span_eq using 3 <;> first | rfl | (funext i; simp)
  · apply le_antisymm
    · intro x hx
      rw [stdLat, Submodule.mem_pi] at hx
      have hx' : ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x i := fun i =>
        Submodule.mem_one.mp (hx i (Set.mem_univ i))
      choose r hr using hx'
      have hxe : x = ∑ i, r i • (Pi.single i (1 : E) : Fin n → E) := by
        funext k
        simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]
      rw [hxe]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, stdLat, Submodule.mem_pi]
      intro j _
      rw [Submodule.mem_one]
      by_cases hij : j = i
      · subst hij
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_apply, hij]⟩
  · intro i j
    simp only [hStd, LinearMap.mk₂'ₛₗ_apply]
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.single_apply, hij, Ne.symm hij]

theorem unimodLocal_of_locDual (hLD : Formalism.HermitianLatticesTheory.LocDual) : UnimodLocal := by
  intro E _ _ _ n N hN hU p hp
  have hsymm : (hStd E n).IsSymm := by
    first
      | (refine ⟨fun x y => ?_⟩
         set_option synthInstance.maxHeartbeats 100000 in
           simp [hStd, map_sum, starRingEnd_apply, star_mul', mul_comm])
      | (intro x y
         set_option synthInstance.maxHeartbeats 100000 in
           simp [hStd, map_sum, starRingEnd_apply, star_mul', mul_comm])
  have hstar : ∀ r : 𝓞 E, star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) := by
    intro r
    exact ⟨RingOfIntegers.mapRingHom (starRingEnd E) r, rfl⟩
  have hfg : N.FG := hN.fg
  have key := (hLD (𝓞 E) E (Sp E n) (hStd E n) hsymm hstar N hfg).2
  exact key.mp hU p hp

theorem unimodLocal : UnimodLocal := unimodLocal_of_locDual Formalism.HermitianLatticesTheory.locDual

end PI.UG.W
end
end

namespace PI.UG.W

open NumberField Module
open Formalism.HermitianLatticesTheory (locBasic_hcompl_not_mem locDual_mem_dualAt)

theorem isomLocStd : IsomLocStd := by
  intro E _ _ _ n hE N hN p hp hu
  have hs := hStd_isSymm E n
  have hI := stdLat_isOrtho E n
  have hFull : Submodule.IsFullLattice E N := by
    refine { toIsLattice := hN, span_eq_top := ?_ }
    let W := Submodule.span E (N : Set (Sp E n))
    change W = ⊤
    by_contra hW
    let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
    let g : Sp E n →ₗ[E] Module.Dual E W :=
      (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
    have hdim : finrank E (Module.Dual E W) < finrank E (Sp E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have horth (y : Sp E n) (hy : y ∈ W) : hStd E n y (e x) = 0 := by
      have hxy : hStd E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨y, hy⟩) (LinearMap.mem_ker.mp hx)
      rw [← (LinearMap.isSymm_def.mp hs) (e x) y, hxy, map_zero]
    -- Localization preserves the ambient span, and self-duality puts the orthogonal vector in it.
    let : p.IsPrime := hp.isPrime
    have hloc {y : Sp E n}
        (hy : y ∈ Formalism.HermitianLatticesTheory.loc (K := E) p N) : y ∈ W := by
      obtain ⟨s, hs', hsy⟩ := hy
      have hs₀ : algebraMap (𝓞 E) E s ≠ 0 := by
        intro hzero
        have : s = 0 := IsFractionRing.injective (𝓞 E) E (by simpa using hzero)
        exact locBasic_hcompl_not_mem p s hs' (this ▸ p.zero_mem)
      exact (W.smul_mem_iff hs₀).mp
        (by rw [algebraMap_smul]; exact Submodule.subset_span hsy)
    have hxW : e x ∈ W := by
      apply hloc
      change Formalism.HermitianLatticesTheory.IsUnimodularAt (hStd E n) p N at hu
      rw [Formalism.HermitianLatticesTheory.IsUnimodularAt] at hu
      rw [← hu, locDual_mem_dualAt]
      intro y hy
      rw [horth y (hloc hy)]
      exact Submodule.zero_mem _
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hpos := ReciprocityTheory.ChartRestriction.L3.isTotPosDef_of_ortho hE hs hI (e x)
      (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) φ
    simp [horth (e x) hxW] at hpos
  exact ReciprocityTheory.ChartRestriction.L3.exists_isom_loc hE hs hI hFull p hp hu

end PI.UG.W
end

theorem unimodular_genus_unique : PI.UnimodGenus :=
  PI.UG.W.unimodGenus_of PI.UG.W.unimodLocal PI.UG.W.isomLocStd
end
