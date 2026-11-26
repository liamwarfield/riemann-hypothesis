module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VecTheta

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem isThetaFunO_of_thetaAt (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {e : AE D} {Λ : AddSubgroup (WO S T)}
    {c : ℂ} {f₀ Φ f : WO S T → ℂ} (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f)
    (h₀ : IsThetaFunO ψ S T f₀) : IsThetaFunO ψ S T f := by
  let U : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {g | IsThetaFunO ψ S T g}
      add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
      zero_mem' := GlobalTheory.OrientedHeis.theta_zero
      smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }
  show f ∈ U
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  let A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    LinearMap.pi fun w => l ∘ₗ GlobalTheory.SplitScalar.heisL ψ S T w
  have hA0 : ∀ g w, A g w = l (heisO ψ S T w g) := fun _ _ => rfl
  have hA : ∀ u g, A (heisO ψ S T u g) = heisO ψ S T u (A g) := fun u g => by
    funext w
    rw [hA0, GlobalTheory.OrientedHeis.heisO_heisO, map_smul]
    rfl
  have hf0 : A f₀ = 0 := by
    funext w
    exact (Submodule.mem_dualAnnihilator l).1 hl _ ((GlobalTheory.ThetaClosed.thetaClosed ψ θ hψ hθ S T f₀ h₀).1 w)
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + A ∘ₗ Tm) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.trans Φ hΦ x hx, hA x]
        exact ((GlobalTheory.SplitScalar.heisL ψ S T x).map_add _ _).symm
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          hT.modul Φ hΦ y hy, hA y]
        exact ((GlobalTheory.SplitScalar.heisL ψ S T y).map_add _ _).symm
      vac := by
        rw [LinearMap.add_apply, LinearMap.comp_apply, hT.vac, hf0, add_zero] }
  have e1 : f = Tm Φ := hall Tm hT
  have e2 : f = (Tm + A ∘ₗ Tm) Φ := hall _ hT'
  rw [LinearMap.add_apply, LinearMap.comp_apply, ← e1] at e2
  have e3 := congrFun (left_eq_add.1 e2) 0
  rwa [hA0, GlobalTheory.OrientedHeis.heisO_zero] at e3

variable {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)}
  {βS : GL (Fin S.rank) (EAf D)} {βT : GL (Fin T.rank) (EAf D)}
  {ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ}

theorem isThetaFunO_stepVec {LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank}
    {χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f) : IsThetaFunO ψ S T f := by
  obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := h
  exact isThetaFunO_of_thetaAt hψ h0.inf h h0.theta

theorem isThetaFunO_thPVec {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) : IsThetaFunO ψ S T f := by
  obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := h
  exact isThetaFunO_of_thetaAt hψ h0.inf h h0.theta

end GlobalTheory.VecTheta

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.AdelicGroupFund

theorem rightInvariant_and_exists_fundamentalDomain : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)), μ.IsHaarMeasure → μ.IsMulRightInvariant ∧ ∃ 𝓕, IsFundamentalDomain (GQ V) 𝓕 μ :=
  fun D V μ hμ => ⟨GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V μ hμ,
    GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμ⟩

end GlobalTheory.Mem.AdelicGroupFund
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomainStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitary_unimodular_exists_fundamentalDomain : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)), μ.IsHaarMeasure → μ.IsMulRightInvariant ∧ ∃ 𝓕, IsFundamentalDomain (GQ V) 𝓕 μ := by
  first | exact @GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain | exact GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain | (intros; apply GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevel
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.DefiniteClassFinite

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

noncomputable abbrev sig : L →ₐ[maximalRealSubfield L] L :=
  ((IsCMField.complexConj L : L ≃ₐ[maximalRealSubfield L] L) : L →ₐ[maximalRealSubfield L] L)

noncomputable def swapAd : ReciprocityTheory.Aut.AL L ≃ₐ[maximalRealSubfield L]
    TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L :=
  Algebra.TensorProduct.comm _ _ _

theorem flip_symm_tmul (a : L) (b : Af (maximalRealSubfield L)) : (swapAd L).symm (b ⊗ₜ a) = a ⊗ₜ b := rfl

theorem flip_conj (x : ReciprocityTheory.Aut.AL L) :
    swapAd L (ReciprocityTheory.Aut.conjAL L x) = sigR (Af (maximalRealSubfield L)) (sig L) (swapAd L x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.DefiniteClassFinite

namespace GlobalTheory.DefiniteClassFinite
variable (L : Type) [Field L] [NumberField L] [IsCMField L]

noncomputable def flipGL (n : ℕ) : GL (Fin n) (ReciprocityTheory.Aut.AL L) ≃*
    GL (Fin n) (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) :=
  Units.mapEquiv (swapAd L).toRingEquiv.mapMatrix.toMulEquiv

theorem JR_one (n : ℕ) : JR (F := ↥(maximalRealSubfield L)) (Af (maximalRealSubfield L)) (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  unfold JR
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem mem_GA_iff {n : ℕ} (g : GL (Fin n) (ReciprocityTheory.Aut.AL L)) :
    g ∈ ReciprocityTheory.Aut.GA L n ↔
      flipGL L n g ∈ HR (Af (maximalRealSubfield L)) (sig L) (1 : Matrix (Fin n) (Fin n) L) := by
  set M : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) := (g : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L))
  have hc : Formalism.UG.cT (sigR (Af (maximalRealSubfield L)) (sig L)) (M.map (swapAd L)) =
      (ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL L) M).map (swapAd L) := by
    ext i j; simp [Formalism.UG.cT, ReciprocityTheory.Aut.conjT, flip_conj]
  change M * ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL L) M = 1 ↔
    Formalism.UG.cT (sigR (Af (maximalRealSubfield L)) (sig L)) (M.map (swapAd L)) *
      JR (F := ↥(maximalRealSubfield L)) (Af (maximalRealSubfield L)) (1 : Matrix (Fin n) (Fin n) L) * M.map (swapAd L) =
      JR (F := ↥(maximalRealSubfield L)) (Af (maximalRealSubfield L)) (1 : Matrix (Fin n) (Fin n) L)
  rw [hc, JR_one, mul_one]
  have key : ∀ X Y : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L),
      X.map (swapAd L) * Y.map (swapAd L) = (X * Y).map (swapAd L) := fun X Y =>
    (map_mul (swapAd L).toRingEquiv.mapMatrix X Y).symm
  rw [key, mul_eq_one_comm]
  constructor
  · intro h; rw [h]; exact Matrix.map_one _ (map_zero _) (map_one _)
  · intro h
    apply (swapAd L).toRingEquiv.mapMatrix.injective
    rw [map_one]; exact h

end GlobalTheory.DefiniteClassFinite

namespace GlobalTheory.DefiniteClassFinite
variable (L : Type) [Field L] [NumberField L] [IsCMField L]

abbrev Jn (n : ℕ) : Matrix (Fin n) (Fin n) L := 1

abbrev Hf (n : ℕ) := HA (Af (maximalRealSubfield L)) (sig L) (Jn L n)

noncomputable def back (n : ℕ) : Hf L n →* Formalism.AUTREP.GAf L n where
  toFun h := ⟨(flipGL L n).symm (HA.mat _ _ _ h), by
    rw [mem_GA_iff, MulEquiv.apply_symm_apply]; exact h.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (flipGL L n).symm
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (flipGL L n).symm (HA.mat _ _ _ x) (HA.mat _ _ _ y)

noncomputable def fwd (n : ℕ) (g : Formalism.AUTREP.GAf L n) : Hf L n :=
  ⟨flipGL L n g.1, (mem_GA_iff L g.1).1 g.2⟩

theorem back_fwd (n : ℕ) (g : Formalism.AUTREP.GAf L n) : back L n (fwd L n g) = g := by
  apply Subtype.ext
  exact MulEquiv.symm_apply_apply (flipGL L n) g.1

theorem back_smul (n : ℕ) (γ : HFinIn (Af (maximalRealSubfield L)) (sig L) (Jn L n)) (h : Hf L n) :
    back L n (γ • h) = back L n γ.1 * back L n h := by
  apply Subtype.ext
  exact map_mul (flipGL L n).symm (γ.1.1) (HA.mat _ _ _ h)

theorem back_mem_GQ (n : ℕ) (γ : HFinIn (Af (maximalRealSubfield L)) (sig L) (Jn L n)) :
    back L n γ.1 ∈ ReciprocityTheory.Aut.GQ L n := by
  obtain ⟨γ0, hγ0, e⟩ := γ.2
  rw [ReciprocityTheory.Aut.GQ, Subgroup.mem_subgroupOf]
  refine ⟨γ0, ?_, ?_⟩
  · change (γ0 : Matrix (Fin n) (Fin n) L) * ReciprocityTheory.Aut.conjT _ (γ0 : Matrix (Fin n) (Fin n) L) = 1
    have h0 : Formalism.UG.cT (sig L : L →+* L) (γ0 : Matrix (Fin n) (Fin n) L) * 1 * (γ0 : Matrix (Fin n) (Fin n) L) = 1 := hγ0
    rw [mul_one] at h0
    rw [mul_eq_one_comm]
    exact h0
  · apply Units.ext
    have e' : Units.val (γ.1.1 : GL (Fin n) _) =
        Units.val (Formalism.UG.bc (inclR (F := ↥(maximalRealSubfield L)) (E := L) (Af (maximalRealSubfield L))) γ0) := by
      rw [e]; rfl
    change ((γ0 : Matrix (Fin n) (Fin n) L)).map Algebra.TensorProduct.includeLeftRingHom =
      ((γ.1.1 : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map (swapAd L).symm
    rw [e']
    ext i j
    rfl

end GlobalTheory.DefiniteClassFinite

namespace GlobalTheory.DefiniteClassFinite
variable (L : Type) [Field L] [NumberField L] [IsCMField L]

noncomputable def intSet : Set (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) :=
  (swapAd L).symm ⁻¹' (ReciprocityTheory.Aut.ALint L : Set (ReciprocityTheory.Aut.AL L))

theorem isOpen_intSet : IsOpen (intSet L) := by
  classical
  let b0 := Module.finBasisOfFinrankEq (maximalRealSubfield L) L
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L)
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := L) (Finset.univ.image b0)
  let b := b0.unitsSMul (fun _ => Units.mk0 ((y : maximalRealSubfield L)) (by exact_mod_cast hy0))
  have hb : ∀ i, IsIntegral ℤ (b i) := by
    intro i
    rw [Module.Basis.unitsSMul_apply]
    have := hy _ (Finset.mem_image_of_mem b0 (Finset.mem_univ i))
    simpa [Units.smul_def, Int.cast_smul_eq_zsmul] using this
  let B := Algebra.TensorProduct.basis (Af (maximalRealSubfield L)) b
  haveI : IsModuleTopology (Af (maximalRealSubfield L))
      (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) := ⟨rfl⟩
  have hc : Continuous B.equivFun := IsModuleTopology.continuous_of_linearMap B.equivFun.toLinearMap
  let H : AddSubgroup (Fin 2 → Af (maximalRealSubfield L)) :=
    (ReciprocityTheory.Aut.ALint L).toAddSubgroup.comap
      ((swapAd L).symm.toRingEquiv.toAddMonoidHom.comp B.equivFun.symm.toLinearMap.toAddMonoidHom)
  have hW := GlobalTheory.AdLat.OpenLat.isOpen_integral (maximalRealSubfield L)
  have hV : (Set.univ.pi fun _ : Fin 2 => {a : Af (maximalRealSubfield L) |
      ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers (maximalRealSubfield L) v}) ⊆ H := by
    intro c hc'
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_setOf_eq] at hc'
    change (swapAd L).symm (B.equivFun.symm c) ∈ ReciprocityTheory.Aut.ALint L
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Module.Basis.equivFun_symm_apply, map_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one, flip_symm_tmul]
    have : b i ⊗ₜ[maximalRealSubfield L] c i =
        (b i ⊗ₜ[maximalRealSubfield L] (1 : Af (maximalRealSubfield L))) * (1 ⊗ₜ c i) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [this]
    exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨b i, hb i⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨c i, hc' i, rfl⟩))
  have hHo : IsOpen (H : Set (Fin 2 → Af (maximalRealSubfield L))) := by
    apply AddSubgroup.isOpen_of_mem_nhds H (g := 0)
    apply Filter.mem_of_superset _ hV
    apply (isOpen_set_pi Set.finite_univ fun _ _ => hW).mem_nhds
    intro i _ v
    exact (v.adicCompletionIntegers (maximalRealSubfield L)).zero_mem
  have : intSet L = B.equivFun ⁻¹' H := by
    ext x
    simp [intSet, H]
  rw [this]
  exact hHo.preimage hc

end GlobalTheory.DefiniteClassFinite

namespace GlobalTheory.DefiniteClassFinite
variable (L : Type) [Field L] [NumberField L] [IsCMField L]

noncomputable def Kmax (n : ℕ) : Subgroup (Hf L n) := (ReciprocityTheory.Aut.Umax L n).comap (back L n)

theorem isOpen_Kmax (n : ℕ) : IsOpen (Kmax L n : Set (Hf L n)) := by
  refine ⟨{x : GL (Fin n) (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) |
    ∀ i j, (x : Matrix (Fin n) (Fin n) _) i j ∈ intSet L}, ?_, ?_⟩
  · have : {x : GL (Fin n) (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) |
        ∀ i j, (x : Matrix (Fin n) (Fin n) _) i j ∈ intSet L} =
        ⋂ i, ⋂ j, (fun x : GL (Fin n) (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L) =>
          (x : Matrix (Fin n) (Fin n) _) i j) ⁻¹' intSet L := by
      ext x; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_intSet L).preimage ((Units.continuous_val (M := Matrix (Fin n) (Fin n)
        (TensorProduct (maximalRealSubfield L) (Af (maximalRealSubfield L)) L))).matrix_elem i j)
  · ext h
    rfl

theorem herm_one (n : ℕ) : IsHermND (sig L) (Jn L n) := by
  refine ⟨fun i j => ?_, by simp⟩
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h, Ne.symm h]

theorem exists_finset_double_cosets_Umax (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) :
    ∃ T : Finset (Formalism.AUTREP.GAf L n), ∀ g : Formalism.AUTREP.GAf L n,
      ∃ (γ : ReciprocityTheory.Aut.GQ L n) (t : Formalism.AUTREP.GAf L n) (u : Formalism.AUTREP.GAf L n),
        t ∈ T ∧ u ∈ ReciprocityTheory.Aut.Umax L n ∧ g = (γ : Formalism.AUTREP.GAf L n) * t * u := by
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.Mem.ClassFinite.exists_finset_classes _ L (sig L)
    (GlobalTheory.AdelicU.isCMExt_of_isCMField L) n (Jn L n) (herm_one L n) (Kmax L n) (isOpen_Kmax L n)
  refine ⟨S.image (back L n), fun g => ?_⟩
  obtain ⟨γ, s, hs, k, hk, e⟩ := hS (fwd L n g)
  refine ⟨⟨back L n γ.1, back_mem_GQ L n γ⟩, back L n s, back L n k,
    Finset.mem_image_of_mem _ hs, hk, ?_⟩
  have := congrArg (back L n) e
  rw [back_fwd, back_smul, map_mul, ← mul_assoc] at this
  exact this

end GlobalTheory.DefiniteClassFinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), ∃ T : Finset (Formalism.AUTREP.GAf L n), ∀ g : Formalism.AUTREP.GAf L n, ∃ (γ : ReciprocityTheory.Aut.GQ L n) (t : Formalism.AUTREP.GAf L n) (u : Formalism.AUTREP.GAf L n), t ∈ T ∧ u ∈ ReciprocityTheory.Aut.Umax L n ∧ g = (γ : Formalism.AUTREP.GAf L n) * t * u := by
  first | exact @GlobalTheory.DefiniteClassFinite.exists_finset_double_cosets_Umax | exact GlobalTheory.DefiniteClassFinite.exists_finset_double_cosets_Umax | (intros; apply GlobalTheory.DefiniteClassFinite.exists_finset_double_cosets_Umax <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeChar
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR.Links
  Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharTransport

section General

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem locMap_eq (P : HeightOneSpectrum (𝓞 E)) (a : (P.under (𝓞 F)).adicCompletion F) :
    GlobalTheory.AdeleBaseChange.locMap F P a = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P a := by
  refine sub_eq_zero.1 (GlobalTheory.PlaceIdem.eq_zero_of_val P _ fun n => ?_)
  have hc := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_finiteCompletionMap F E P
  have h1 := (GlobalTheory.Mem.UnitOpen.isOpen_val_le (P.under (𝓞 F)) (-(n : ℤ))).preimage (continuous_sub_left a)
  have h2 := (GlobalTheory.Mem.UnitOpen.isOpen_val_le P (-(n : ℤ))).preimage
    ((continuous_sub_left (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P a)).comp hc)
  obtain ⟨k, hk1, hk2⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F)
    (P.under (𝓞 F))).exists_mem_open (h1.inter h2) ⟨a, by simp, by simp⟩
  have e : GlobalTheory.AdeleBaseChange.locMap F P a - GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P a =
      GlobalTheory.AdeleBaseChange.locMap F P (a - algebraMap F _ k) -
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P a -
          GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P (algebraMap F _ k)) := by
    rw [map_sub, GlobalTheory.AdeleBaseChange.locMap_algebraMap, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe]
    ring
  rw [e]
  exact Valuation.map_sub_le _ (GlobalTheory.AdeleBaseChange.locMap_valued P n _ hk1) hk2

theorem exists_toAdele : ∃ Θ : AF F ⊗[F] E →+* AdeleRing (𝓞 E) E, Continuous Θ ∧
    ∀ a x, Θ (a ⊗ₜ[F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a * algebraMap E _ x := by
  letI : Algebra F (AdeleRing (𝓞 E) E) :=
    ((algebraMap E (AdeleRing (𝓞 E) E)).comp (algebraMap F E)).toAlgebra
  let f : E →ₐ[F] AdeleRing (𝓞 E) E := ⟨algebraMap E _, fun _ => rfl⟩
  let g : AF F →ₐ[F] AdeleRing (𝓞 E) E :=
    ⟨GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E, fun x => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap F E x⟩
  let Θ : AF F ⊗[F] E →+* AdeleRing (𝓞 E) E := (Algebra.TensorProduct.productMap g f).toRingHom
  have hΘ : ∀ a x, Θ (a ⊗ₜ[F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a * algebraMap E _ x := fun a x => rfl
  refine ⟨Θ, ?_, hΘ⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  let φ : AF F ⊗[F] E →ₛₗ[GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E] AdeleRing (𝓞 E) E :=
    { toFun := Θ
      map_add' := map_add Θ
      map_smul' := fun r z => by
        rw [Algebra.smul_def, map_mul, smul_eq_mul]
        congr 1
        change Θ (r ⊗ₜ[F] 1) = _
        rw [hΘ, map_one, mul_one] }
  exact IsModuleTopology.continuous_of_linearMapₛₗ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap F E) φ

end General

theorem isDelta_of_isPlIdem {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}
    (hΦ : GlobalTheory.IdemSupport.Comp D Φ) {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (h : IsPlIdem D e P) :
    GlobalTheory.IdemSupport.IsDelta Φ P e := by
  obtain ⟨h1, ⟨v, ε, hε, h2⟩, ht⟩ := h
  refine (GlobalTheory.IdemSupport.tie_iff hΦ h1 ?_ P).1 ht
  rcases h2 with ⟨h2, h3⟩ | h2
  · have : e = (e + cA D e) * e := by linear_combination -h1 - h2
    rw [this, h3, RingHom.map_mul, (GlobalTheory.IdemSupport.place_comp hΦ hε).1, zero_mul]
  · rw [h2, (GlobalTheory.IdemSupport.place_comp hΦ hε).1]

theorem map_loc {A B : Type} [Ring A] [Ring B] (f : A →+* B) (e k : A) :
    f (1 + e * (k - 1)) = 1 + f e * (f k - 1) := by
  rw [map_add (f := _), map_mul, map_sub, map_one]


set_option maxHeartbeats 800000 in
theorem exists_hom (D : D7) : ∃ Θ : AE D →+* AdeleRing (𝓞 D.host.E) D.host.E, Continuous Θ ∧
    (∀ x, Θ (incA D x) = algebraMap D.host.E _ x) ∧
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
      Θ (locE D e (k : D.host.E)) =
        ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E) := by
  obtain ⟨Θ, hc, hΘ⟩ := exists_toAdele D.host.F D.host.E
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hinc : ∀ x, Θ (incA D x) = algebraMap D.host.E _ x := fun x => by
    change Θ ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
    rw [hΘ, map_one, one_mul]
  have hfin : ∀ z, (Θ z).2 = Φ z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [RingHom.map_zero, RingHom.map_zero]; rfl
    | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ← hx, ← hy]; rfl
    | tmul a x =>
      have e : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap (AF D.host.F) (AE D) a * incA D x := by
        change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hΘ, e, RingHom.map_mul, hΦ.inc]
      refine FiniteAdeleRing.ext _ fun Q => ?_
      change _ = Φ _ Q * _
      rw [hΦ.base, locMap_eq]
      rfl
  have hinf : ∀ z, infPart D z = 0 → (Θ z).1 = 0 := fun z hz => by
    let u : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)
    have h1 : u * z = 0 := by
      refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
      · rw [RingHom.map_mul, hz, mul_zero, RingHom.map_zero]
      · have : finPart D u = 0 := TensorProduct.zero_tmul _ _
        rw [RingHom.map_mul, this, zero_mul, RingHom.map_zero]
    have h2 : (Θ u).1 = 1 := by
      change (Θ (pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 : D.host.E))).1 = 1
      rw [hΘ, map_one, mul_one]
      exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap D.host.F D.host.E)
    have h3 : (Θ u).1 * (Θ z).1 = 0 := by
      change (Θ u * Θ z).1 = 0
      rw [← RingHom.map_mul, h1, RingHom.map_zero]
      rfl
    rwa [h2, one_mul] at h3
  refine ⟨Θ, hc, hinc, fun P e he k => ?_⟩
  obtain ⟨d0, d1, d2⟩ := isDelta_of_isPlIdem hΦ he
  have hl : Θ (locE D e (k : D.host.E)) =
      1 + Θ e * (algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) - 1) :=
    (map_loc Θ e (incA D (k : D.host.E))).trans (by rw [hinc])
  rw [hl]
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun Q => ?_)
  · change 1 + (Θ e).1 * _ = 1
    rw [hinf e d0, zero_mul, add_zero]
  · classical
    change 1 + (Θ e).2 Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) (k : D.host.E) - 1) =
      Function.update (fun w : HeightOneSpectrum (𝓞 D.host.E) => (1 : w.adicCompletion D.host.E)) P
        (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) Q
    rw [hfin]
    by_cases hQ : Q = P
    · subst hQ
      rw [d1, Function.update_self]
      ring
    · rw [d2 Q hQ, Function.update_of_ne hQ]
      ring

theorem exists_chrEq : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E), χ.IsUnitary → ∃ c, ChrEq c χ := by
  intro D χ hχ
  obtain ⟨Θ, hc, hinc, hloc⟩ := exists_hom D
  let u : (AE D)ˣ →* Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hc
  let c : (AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  refine ⟨c, ⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩
  · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
  · have : u (Units.map (incA D).toMonoidHom x) = diagUnits D.host.E x := Units.ext (hinc x)
    rw [hcoe, this, χ.2.2]
    rfl
  · have : u x = localIdele D.host.E P (atFin P k) := by
      refine Units.ext ?_
      change Θ (x : AE D) = _
      rw [hx, hloc P e he]
    rw [hcoe, this]
    rfl

end GlobalTheory.CharTransport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmAdeleUnitCharacterReadingHeckeCharStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmAdeleUnitCharacter_reading_heckeChar : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E), χ.IsUnitary → ∃ c, ChrEq c χ := by
  first | exact @GlobalTheory.CharTransport.exists_chrEq | exact GlobalTheory.CharTransport.exists_chrEq | (intros; apply GlobalTheory.CharTransport.exists_chrEq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Datum Matrix
open scoped InnerProductSpace Classical

namespace GlobalTheory.JointHarm

section Hol

variable {n : ℕ} {P : Type} [AddCommGroup P] [Module ℂ P]

def IsHolRep (ε : Fin n → Bool) (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) : Prop :=
  (∀ x, B x x = 0 → x = 0) ∧ π 1 = 1 ∧
    (∀ a ∈ GlobalTheory.Dec.KC ε, ∀ b ∈ GlobalTheory.Dec.KC ε, π (a * b) = π a * π b) ∧
    (∀ g ∈ GlobalTheory.Dec.KC ε, ∀ x y, B (π g x) y = B x (π gᴴ y)) ∧
    ∀ x y, DifferentiableOn ℂ (fun g : Fin n → Fin n → ℂ => B x (π (Matrix.of g) y))
      {g | Matrix.of g ∈ GlobalTheory.Dec.KC ε}

def IsBottom (ε : Fin n → Bool) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P) (μ : Fin n → ℝ) (x : P) : Prop :=
  (∀ g ∈ GlobalTheory.Dec.KC ε, IsLoUni g → π g x = x) ∧
    ∀ θ : Fin n → ℝ, π (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) x =
      Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • x

variable {ι : Type}

def IsHolFam (ε : ι → Fin n → Bool) (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ)
    (ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P) : Prop :=
  (∀ x, B x x = 0 → x = 0) ∧ ϖ 1 = 1 ∧
    (∀ a b, (∀ τ, a τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, b τ ∈ GlobalTheory.Dec.KC (ε τ)) → ϖ (a * b) = ϖ a * ϖ b) ∧
    ∀ τ, IsHolRep (ε τ) B fun g => ϖ (Pi.mulSingle τ g)

def IsBotFam (ε : ι → Fin n → Bool) (ϖ : (ι → Matrix (Fin n) (Fin n) ℂ) → Module.End ℂ P)
    (μ : ι → Fin n → ℝ) (x : P) : Prop :=
  ∀ τ, IsBottom (ε τ) (fun g => ϖ (Pi.mulSingle τ g)) (μ τ) x

theorem isHolRep_of_isTau {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : GlobalTheory.Dec.IsTau ε abelian₂ τ w) :
    IsHolRep ε (innerₛₗ ℂ) (fun g => (τ g : W →ₗ[ℂ] W)) ∧
      IsBottom ε (fun g => (τ g : W →ₗ[ℂ] W)) (-abelian₂) w := by
  obtain ⟨-, ⟨h1, hm⟩, hd, ha, -, -, hw, hl⟩ := h
  refine ⟨⟨fun x hx => inner_self_eq_zero.1 hx, ?_, fun a ha b hb => ?_, ha, hd⟩, hl, fun θ => hw θ ⟨?_, ?_⟩⟩
  · show (τ 1 : W →ₗ[ℂ] W) = 1
    rw [h1]; rfl
  · show (τ (a * b) : W →ₗ[ℂ] W) = _
    rw [hm a ha b hb]; rfl
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp [← Complex.exp_conj, ← Complex.exp_add]
  · simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]

end Hol

section Fock

variable {D : D7} {m n : ℕ}

def fsub (ε : D.what₂.Tau → Fin m → Bool) (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : PolF D m n →ₐ[ℂ] PolF D m n :=
  MvPolynomial.aeval fun v => ∑ a : Fin m, ∑ b : Fin n,
    MvPolynomial.C (if ε v.1 v.2.1 = true then k v.1 a v.2.1 * (u v.1)⁻¹ v.2.2 b
      else (k v.1)⁻¹ v.2.1 a * u v.1 b v.2.2) * MvPolynomial.X (v.1, a, b)

def detP (ε : Fin m → Bool) (k : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ((1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε) * k + (1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε)).det

def detM (ε : Fin m → Bool) (k : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ((1 / 2 : ℂ) • (1 - Formalism.REAL.Jm ε) * k + (1 / 2 : ℂ) • (1 + Formalism.REAL.Jm ε)).det

def fchar (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∏ τ, detP (ε τ) (k τ) ^ x₁ τ * detM (ε τ) (k τ) ^ x₂ τ * (u τ).det ^ x₃ τ

def fact (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    Module.End ℂ (PolF D m n) :=
  fchar ε x₁ x₂ x₃ k u • (fsub ε k u).toLinearMap

def factK (n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (g : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) : Module.End ℂ (PolF D m n) :=
  fact ε x₁ x₂ x₃ (fun τ => ((g τ)⁻¹)ᵀ) 1

def factU (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ)
    (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (PolF D m n) :=
  fact ε x₁ x₂ x₃ 1 u

def wtK (p : ℕ) (ap am : ℕ → ℕ) (x₁ x₂ : ℤ) (a : Fin m) : ℤ :=
  if (a : ℕ) < p then (ap a : ℤ) + x₁ else -(am (m - 1 - a) : ℤ) + x₂

def wtU (p q : ℕ) (ap am : ℕ → ℕ) (x₃ : ℤ) (j : Fin n) : ℤ :=
  -(if (j : ℕ) < p then (ap j : ℤ) else 0) + (if n - 1 - j < q then (am (n - 1 - j) : ℤ) else 0) + x₃

end Fock

def vact {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (u : ι → Matrix (Fin n) (Fin n) ℂ) :
    Module.End ℂ (Pol ℂ ι n) :=
  (∏ τ, (u τ).det ^ (-(lam τ).detShift)) • (Formalism.GradedWeylDivisibility.blockAct ℂ fun τ => (u τ)⁻¹).toLinearMap

end GlobalTheory.JointHarm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelic
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.FinTranslate

open GlobalTheory.PointAtPlaceHom

variable {D : D7} {θ : InfF D} {V : HSp D}

theorem Rder_rTr {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (φ : GA D V → ℂ) : Rder θ V τ X (rTr V k φ) = rTr V k (Rder θ V τ X φ) := by
  funext g
  unfold Rder rTr
  congr 1
  funext t
  rw [mul_assoc, mul_assoc, oneP, comm_of_mem V (atTau_mem V τ _) hk]

theorem foldr_rTr {α : Type} (k : GA D V) (F : α → (GA D V → ℂ) → (GA D V → ℂ)) (l : List α)
    (h : ∀ a ∈ l, ∀ φ, F a (rTr V k φ) = rTr V k (F a φ)) (φ : GA D V → ℂ) :
    l.foldr F (rTr V k φ) = rTr V k (l.foldr F φ) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih fun b hb => h b (List.mem_cons_of_mem _ hb), h a List.mem_cons_self]

theorem gelf_rTr {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) (n : ℕ) (φ : GA D V → ℂ) :
    gelf θ V τ n (rTr V k φ) = rTr V k (gelf θ V τ n φ) := by
  unfold gelf
  rw [Finset.sum_congr rfl fun idx _ => foldr_rTr k _ _ (fun a ha ψ => ?_) φ]
  · funext g
    simp only [rTr, Finset.sum_apply]
  · obtain ⟨b, rfl⟩ := List.mem_ofFn.1 ha
    unfold RderC
    rw [Rder_rTr hk, Rder_rTr hk]
    rfl

theorem isAutFunSm_rTr_fin : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ),
    IsAutFunSm θ V φ → ∀ k ∈ GfC V, IsAutFunSm θ V (rTr V k φ) := by
  intro D θ _ V φ h k hk
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine { left := fun γ hγ g => ?_, level := ?_, cont := h.cont.comp (continuous_mul_const k),
           smooth := fun n τs Xs hX g => ?_, zfin := ?_, growth := ?_ }
  · unfold rTr
    rw [mul_assoc, h.left γ hγ]
  · obtain ⟨U, hU, e⟩ := h.level
    refine ⟨U.comap (MulAut.conj k⁻¹).toMonoidHom, hU.preimage ?_, fun u hu hf g => ?_⟩
    · show Continuous fun u : GA D V => k⁻¹ * u * k⁻¹⁻¹
      fun_prop
    · have hu' : k⁻¹ * u * k⁻¹⁻¹ ∈ U := hu
      have := e _ hu' (mul_mem (mul_mem (inv_mem hk) hf) (inv_mem (inv_mem hk))) (g * k)
      unfold rTr
      rw [← this]
      congr 1
      group
  · have := h.smooth n τs Xs hX (g * k)
    convert this using 2 with t
    unfold rTr
    rw [mul_assoc, mul_assoc, comm_of_mem V (list_prod_mem fun a ha => ?_) hk]
    obtain ⟨b, rfl⟩ := List.mem_ofFn.1 ha
    exact atTau_mem V _ _
  · obtain ⟨W, hW, m, s⟩ := h.zfin
    refine ⟨W.map (LinearMap.funLeft ℂ ℂ fun g => g * k), inferInstance, ⟨φ, m, rfl⟩, ?_⟩
    rintro τ n _ ⟨f, hf, rfl⟩
    exact ⟨_, s τ n f hf, (gelf_rTr hk τ n f).symm⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl (x * k)
    refine ⟨C, fun g hg => ?_⟩
    rw [foldr_rTr k _ l (fun a _ ψ => Rder_rTr hk _ _ ψ) φ]
    unfold rTr
    rw [mul_assoc, comm_of_mem V hg hk, ← mul_assoc]
    exact hC g hg

end GlobalTheory.Mem.FinTranslate

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAutomorphicFormRightTranslateFiniteAdelicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothAutomorphicForm_rightTranslate_finiteAdelic : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFunSm θ V φ → ∀ k ∈ GfC V, IsAutFunSm θ V (rTr V k φ) := by
  first | exact @GlobalTheory.Mem.FinTranslate.isAutFunSm_rTr_fin | exact GlobalTheory.Mem.FinTranslate.isAutFunSm_rTr_fin | (intros; apply GlobalTheory.Mem.FinTranslate.isAutFunSm_rTr_fin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitOfCocompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Per.UnitN

theorem exists_unit_of_cocompact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] (Γ : Subgroup G) [Countable Γ] [DiscreteTopology Γ]
    {K : Set G} (hK : IsCompact K) (hcov : ∀ n, ∃ γ ∈ Γ, ∃ k ∈ K, n = γ * k) :
    ∃ (ν : Measure G) (𝓝 : Set G), ν.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓝 ν ∧ ν 𝓝 = 1 := by
  let μ : Measure G := Measure.haar
  obtain ⟨𝓕, h⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain Γ μ
  have hle : μ 𝓕 ≤ μ K := by
    rw [h.measure_eq_tsum K]
    refine (measure_mono fun n hn => ?_).trans (measure_iUnion_le _)
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov n
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨k, hk, rfl⟩, hn⟩
  have hfin : μ 𝓕 ≠ ⊤ := (hle.trans_lt hK.measure_lt_top).ne
  have hpos : μ 𝓕 ≠ 0 := h.measure_ne_zero (NeZero.ne μ)
  refine ⟨(μ 𝓕)⁻¹ • μ, 𝓕, Measure.IsHaarMeasure.smul μ (ENNReal.inv_ne_zero.2 hfin) (ENNReal.inv_ne_top.2 hpos),
    h.mono Measure.smul_absolutelyContinuous, ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]

theorem exists_isUnitN : ∀ (D : D7) (B : HSp D) (ρ : ℕ) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E), IsIsoSub B e →
    ∃ ν 𝓝, GlobalTheory.Per.IsUnitN B e ν 𝓝 := by
  intro D B ρ e he
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨K, hK, h⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1
  have hcl : IsClosed (NFlag B e : Set (GA D B)) := by
    have : DiscreteTopology (GQ B ⊓ NFlag B e : Subgroup (GA D B)) :=
      DiscreteTopology.of_subset (s := (GQ B : Set (GA D B))) i6 (fun x hx => hx.1)
    have h1 : IsClosed ((GQ B ⊓ NFlag B e : Subgroup (GA D B)) : Set (GA D B)) := Subgroup.isClosed_of_discrete
    have h2 := h1.mul_right_of_isCompact (hK.image continuous_subtype_val)
    convert h2 using 1
    ext x
    constructor
    · intro hx
      obtain ⟨γ, hγ, k, hk, e⟩ := h ⟨x, hx⟩
      exact ⟨γ, ⟨hγ, γ.2⟩, k, ⟨k, hk, rfl⟩, (congrArg Subtype.val e).symm⟩
    · rintro ⟨γ, hγ, _, ⟨k, -, rfl⟩, rfl⟩
      exact mul_mem hγ.2 k.2
  have : LocallyCompactSpace (NFlag B e) := hcl.locallyCompactSpace
  have : SecondCountableTopology (NFlag B e) := TopologicalSpace.Subtype.secondCountableTopology _
  have hinj : Function.Injective fun γ : NFlagQ B e => (⟨γ.1.1, γ.2⟩ : GQ B) :=
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ B => (x : GA D B)) h))
  have : Countable (NFlagQ B e) := hinj.countable
  have : DiscreteTopology (NFlagQ B e) :=
    DiscreteTopology.of_continuous_injective
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hinj
  exact exists_unit_of_cocompact (NFlagQ B e) hK h

end GlobalTheory.Per.UnitN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueIsStdChar
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdAdelicChar

theorem eq_of_psiInf_eq {F : Type} [Field F] [NumberField F] {ψ ψ' : AddChar (AF F) ℂ}
    (h : IsCharAF F ψ) (h' : IsCharAF F ψ') (e : ∀ x, psiInf F ψ x = psiInf F ψ' x) : ψ = ψ' := by
  have hrat : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) = ψ' (pairA F 0 (algebraMap F (Af F) x)) := fun x => by
    rw [GlobalTheory.StdRat.char_fin_rat ψ h, GlobalTheory.StdRat.char_fin_rat ψ' h', e]
  have hp : Continuous fun y : Af F => pairA F 0 y := Continuous.prodMk continuous_const continuous_id
  have hint : ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 α) = ψ' (pairA F 0 α) :=
    fun α hα => GlobalTheory.IntDense.mem_of_isClosed F (C := {y | ψ (pairA F 0 y) = ψ' (pairA F 0 y)})
      (isClosed_eq (h.1.comp hp) (h'.1.comp hp)) (fun a => hrat a) α hα
  have hfin : ∀ y : Af F, ψ (pairA F 0 y) = ψ' (pairA F 0 y) := fun y => by
    obtain ⟨a, s, hs, hy⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos y
    have e1 : pairA F 0 y = pairA F 0 (algebraMap F (Af F) a) + pairA F 0 s := by
      refine Prod.ext (add_zero _).symm ?_
      show y = algebraMap F (Af F) a + s
      simpa only [one_smul] using hy
    rw [e1, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hrat, hint s hs]
  refine AddChar.ext _ _ fun a => ?_
  have e2 : a = pairA F a.1 0 + pairA F 0 a.2 := Prod.ext (add_zero _).symm (zero_add _).symm
  rw [e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hfin]
  exact congrArg (· * _) (e a.1)

theorem isCharAF_inv {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (h : IsCharAF F ψ) :
    IsCharAF F ψ⁻¹ := by
  refine ⟨?_, fun x => ?_, fun a => ?_, ?_⟩
  · exact h.1.comp continuous_neg
  · exact h.2.1 (-x)
  · rw [AddChar.inv_apply, ← map_neg]; exact h.2.2.1 _
  · obtain ⟨x, hx⟩ := h.2.2.2
    exact ⟨-x, by rwa [AddChar.inv_apply, neg_neg]⟩

theorem isStdChar_inv {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {s : ℤ} (h : IsStdChar D ψ s) :
    IsStdChar D ψ⁻¹ (-s) := by
  refine ⟨isCharAF_inv h.1, h.2.1, fun θ hθ x => ?_⟩
  have e : psiInf D.host.F ψ⁻¹ x = psiInf D.host.F ψ (-x) := by
    rw [psiInf, psiInf, AddChar.inv_apply]
    exact congrArg ψ (Prod.ext rfl neg_zero)
  rw [e, h.2.2 θ hθ]
  simp only [TensorProduct.neg_tmul, map_neg, Finset.sum_neg_distrib]
  congr 1
  push_cast
  ring

theorem isStdChar_unique {D : D7} {ψ ψ' : AddChar (AF D.host.F) ℂ} {s : ℤ} (h : IsStdChar D ψ s)
    (h' : IsStdChar D ψ' s) : ψ = ψ' := by
  obtain ⟨θ, hθ⟩ := h.2.1
  exact eq_of_psiInf_eq h.1 h'.1 fun x => (h.2.2 θ hθ x).trans (h'.2.2 θ hθ x).symm

theorem existsUnique_isStdChar :
    ∀ (D : D7) (s : ℤ), s = 1 ∨ s = -1 → ∃! ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ s := by
  intro D s hs
  obtain ⟨ψ, hψ⟩ := exists_isStdChar D
  rcases hs with rfl | rfl
  · have h1 : IsStdChar D ψ⁻¹ 1 := by simpa using isStdChar_inv hψ
    exact ⟨ψ⁻¹, h1, fun ψ' h' => isStdChar_unique h' h1⟩
  · exact ⟨ψ, hψ, fun ψ' h' => isStdChar_unique h' hψ⟩

end GlobalTheory.StdAdelicChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryAdelicQuotientVolumeIsVolume
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryAdelicQuotientVolumeIsVolume
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem volIs_trueVol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → VolIs cm τ cd W (trueVol cm τ cd W) := by
  intro F E _ _ _ _ _ _ cm I _ τ cd W hτ hW
  apply trueVol_spec
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.exists_isUnitaryAdelicVolumeMeasure F E cm I τ cd W hτ hW
  obtain ⟨⟨𝓕, h𝓕⟩, hall⟩ := GlobalTheory.T.fundamentalDomain_unitaryAdelic_exists_measure_eq F E cm.sig W.rank W.gram μ hμ.1
  have hcm := cmData_isCMExt_and_gram_isHermND F E cm
  have hfin : μ 𝓕 < ⊤ := GlobalTheory.T.finiteVolume_adelicUnitaryQuotient F E cm.sig hcm.1 W.rank W.gram (hcm.2 W) μ hμ.1 𝓕 h𝓕
  have hne : μ 𝓕 ≠ 0 := (hall 𝓕 𝓕 h𝓕 h𝓕).2
  refine ⟨(μ 𝓕).toReal, ENNReal.toReal_pos hne hfin.ne, ⟨μ, hμ⟩, ?_⟩
  intro μ' hμ'
  have e : μ = μ' := GlobalTheory.Mem.VolUnique.volMeas_unique F E cm I τ cd W hτ hW μ μ' hμ hμ'
  subst e
  refine ⟨⟨𝓕, h𝓕⟩, fun 𝓕' h' => ?_⟩
  rw [ENNReal.ofReal_toReal hfin.ne]
  exact (hall 𝓕' 𝓕 h' h𝓕).1

end GlobalTheory.Mem.Vol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryAdelicQuotientVolumeIsVolumeStatement
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicQuotientVolume_is_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (cd : CDHaar) (W : HSpace E), IsCMFam τ → W.SigOK → VolIs cm τ cd W (trueVol cm τ cd W) := by
  first | exact @GlobalTheory.Mem.Vol.volIs_trueVol | exact GlobalTheory.Mem.Vol.volIs_trueVol | (intros; apply GlobalTheory.Mem.Vol.volIs_trueVol <;> assumption)
end
end
