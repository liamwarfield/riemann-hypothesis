module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCompletedSelfDualLatticeIffIntegralStdFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementUniformizerRatioDeterminant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SphericalVectorFixedLocal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalComponentConjSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalComponentConjSplitPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

theorem conjLoc_exists_split (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host) (h : IsConjPl D.host w s.w) :
    ∃ s' : SplitPlace D.host.E, s'.w = w := by
  have hc : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x := fun x => by
    apply D.host.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj]
    exact Formalism.HC.HostAx.conjE_apply _ _ _
  refine ⟨⟨s.v, s.i.comp (IsCMField.complexConj D.host.E).toAlgHom⟩, ?_⟩
  apply HeightOneSpectrum.ext
  ext x
  have hy : ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [hc]; rfl
  rw [h x _ hy]
  exact Iff.rfl

theorem conjLoc (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) (w : PlE D.host)
    (h : IsConjPl D.host w s.w) : ∃ x, GlobalTheory.AutQuot.LocAt π w x := by
  obtain ⟨s', rfl⟩ := conjLoc_exists_split D s w h
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV π s'
  exact ⟨_, s', σ, rfl, hσ, HEq.rfl⟩

end GlobalTheory.AutQuot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalComponentConjSplitPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localComponent_conj_splitPlace : ∀ (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) (w : PlE D.host),
    IsConjPl D.host w s.w → ∃ x, GlobalTheory.AutQuot.LocAt π w x := by
  first | exact @GlobalTheory.AutQuot.conjLoc | exact GlobalTheory.AutQuot.conjLoc | (intros; apply GlobalTheory.AutQuot.conjLoc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SatakeParametersInertPlaceIndependentOfModel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SatakeParametersInertPlaceIndependentOfModel
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

namespace GlobalTheory.SatInd

theorem satAt_indep : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n), π.Iso π' → ∀ v w, NG.OverPl w v → ∀ (Dv Dv' : InertDatum L n v w) α, NG.SatAt π Dv α → NG.SatAt π' Dv' α := by
  intro L _ _ _ n π π' hiso v w _ Dv Dv' α hsat
  have h1 : NG.SatAt π Dv' α := by
    obtain ⟨f, hfS, hf0, U, hU, hUv, hH⟩ := hsat
    refine ⟨f, hfS, hf0, U, hU, hUv, fun h' hh' => ?_⟩
    have hm : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    rw [GlobalTheory.T.inertHeckeOperator_indep_of_inertDatum L n v w Dv Dv' U _ h' hh'.1 f,
      hH _ (GlobalTheory.T.heckeAlgebra_comp_unitaryGroupAntidiagTransport_mem (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') n h' hh'),
      GlobalTheory.T.unitarySatake_invariant_antidiagTransport (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') Dv.ϖ Dv'.ϖ _ n (n / 2) h' hh'.1
        (GlobalTheory.T.unitaryTorus_unipotent_coset_transport_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') Dv.ϖ Dv'.ϖ _ _ n (n / 2)
          Dv.unram Dv'.unram hm)]
  exact GlobalTheory.T.inertSatakeParameters_eq_of_iso L n π π' hiso v w Dv' α
    (GlobalTheory.T.finite_inertHecke_support_cosets L n v w Dv' (GlobalTheory.T.unitary_doubleCoset_finite_left_cosets Dv'.ϖ Dv'.σw _ n Dv'.unram) (GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv')) h1

end GlobalTheory.SatInd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SatakeParametersInertPlaceIndependentOfModelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satakeParameters_inertPlace_independent_of_model : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n), π.Iso π' → ∀ v w, NG.OverPl w v → ∀ (Dv Dv' : InertDatum L n v w) α, NG.SatAt π Dv α → NG.SatAt π' Dv' α := by
  first | exact @GlobalTheory.SatInd.satAt_indep | exact GlobalTheory.SatInd.satAt_indep | (intros; apply GlobalTheory.SatInd.satAt_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordinateModelOfAlgWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordinateModelOfAlgWeight
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot.Model

theorem isIrreducible_of_linearEquiv {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] {ρ : Representation F G V} {σ : Representation F G W} (κ : V ≃ₗ[F] W)
    (h : ∀ g v, κ (ρ g v) = σ g (κ v)) (hρ : ρ.IsIrreducible) : σ.IsIrreducible := by
  let E : Subrepresentation ρ ≃o Subrepresentation σ :=
    { toFun := fun S => ⟨S.toSubmodule.comap κ.symm.toLinearMap, fun g w hw => by
        obtain ⟨v, rfl⟩ := κ.surjective w
        have hv : v ∈ S.toSubmodule := κ.symm_apply_apply v ▸ hw
        simpa [← h] using S.apply_mem_toSubmodule g hv⟩
      invFun := fun T => ⟨T.toSubmodule.comap κ.toLinearMap, fun g v hv => by
        show κ (ρ g v) ∈ T.toSubmodule
        rw [h]
        exact T.apply_mem_toSubmodule _ hv⟩
      left_inv := fun S => Subrepresentation.toSubmodule_injective (by ext v; simp)
      right_inv := fun T => Subrepresentation.toSubmodule_injective (by ext v; simp)
      map_rel_iff' := fun {S T} => ⟨fun hh v hv => by
        have : κ.symm (κ v) ∈ S.toSubmodule := (κ.symm_apply_apply v).symm ▸ hv
        have h2 : κ.symm (κ v) ∈ T.toSubmodule := hh this
        exact κ.symm_apply_apply v ▸ h2, fun hh v hv => hh hv⟩ }
  exact E.isSimpleOrder_iff.1 hρ

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def conjRep {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (e : W ≃ₗ[ℂ] W')
    (ρ : Representation ℂ (GQ L n) W) : Representation ℂ (GQ L n) W' where
  toFun γ := e.toLinearMap ∘ₗ ρ γ ∘ₗ e.symm.toLinearMap
  map_one' := by ext x; simp
  map_mul' γ δ := by ext x; simp

theorem conjRep_apply {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (e : W ≃ₗ[ℂ] W')
    (ρ : Representation ℂ (GQ L n) W) (γ : GQ L n) (x : W') : conjRep e ρ γ x = e (ρ γ (e.symm x)) := rfl

theorem isAlgWeight_conjRep {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (e : W ≃ₗ[ℂ] W')
    (ρ : Representation ℂ (GQ L n) W) (h : IsAlgWeight L n ρ) : IsAlgWeight L n (conjRep e ρ) := by
  obtain ⟨hfd, ι, i1, i2, b, P, hP⟩ := h
  refine ⟨LinearEquiv.finiteDimensional e, ι, i1, i2, b.map e, P, fun γ γ₀ hγ => ?_⟩
  rw [← hP γ γ₀ hγ]
  ext i j
  simp [LinearMap.toMatrix_apply, conjRep_apply]

theorem exists_model : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n),
    ∃ m : GlobalTheory.AutQuot.AlgWtM L n, a.Iso m.toAlgWt := by
  intro L _ _ _ n a
  haveI : FiniteDimensional ℂ a.W := a.alg.1
  let e : a.W ≃ₗ[ℂ] (Fin (Module.finrank ℂ a.W) → ℂ) := (Module.finBasis ℂ a.W).equivFun
  refine ⟨⟨Module.finrank ℂ a.W, conjRep e a.ρ, isAlgWeight_conjRep e a.ρ a.alg,
    isIrreducible_of_linearEquiv e (fun γ x => by simp [conjRep_apply]) a.irr⟩, e, fun γ x => ?_⟩
  show e (a.ρ γ x) = conjRep e a.ρ γ (e x)
  simp [conjRep_apply]

end GlobalTheory.AutQuot.Model

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordinateModelOfAlgWeightStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinate_model_of_algWeight : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n),
    ∃ m : GlobalTheory.AutQuot.AlgWtM L n, a.Iso m.toAlgWt := by
  first | exact @GlobalTheory.AutQuot.Model.exists_model | exact GlobalTheory.AutQuot.Model.exists_model | (intros; apply GlobalTheory.AutQuot.Model.exists_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicMultiplicityEqOfIso
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicMultiplicityEqOfIso
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.MultIso

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem mem_AFall_iff {ρ : Representation ℂ (GQ L n) W} {f : GAf L n → W} :
    f ∈ NG.AFall L n ρ ↔ (∀ (γ : GQ L n) (g : GAf L n), f ((γ : GAf L n) * g) = ρ γ (f g)) ∧
      ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g := Iff.rfl

theorem mem_HomG_iff {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)}
    {Φ : S →ₗ[ℂ] (GAf L n → W)} :
    Φ ∈ NG.HomG ρ S ↔ (∀ f, Φ f ∈ NG.AFall L n ρ) ∧ ∀ (h : GAf L n) (f f' : S),
      (f' : GAf L n → W) = NG.rt L n h (f : GAf L n → W) → Φ f' = NG.rt L n h (Φ f) := Iff.rfl

theorem comp_mem_AFall {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    (A : W →ₗ[ℂ] W') (hA : ∀ γ x, A (ρ γ x) = ρ' γ (A x)) {f : GAf L n → W} (hf : f ∈ NG.AFall L n ρ) :
    (fun g => A (f g)) ∈ NG.AFall L n ρ' := by
  obtain ⟨h1, N, hN, h2⟩ := mem_AFall_iff.1 hf
  exact mem_AFall_iff.2 ⟨fun γ g => by simp only [h1 γ g, hA], N, hN, fun κ hκ g => by simp only [h2 κ hκ g]⟩

def transport {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    {S : Submodule ℂ (GAf L n → W)} {S' : Submodule ℂ (GAf L n → W')}
    (A : W →ₗ[ℂ] W') (hA : ∀ γ x, A (ρ γ x) = ρ' γ (A x))
    (T : S' →ₗ[ℂ] S) (hT : ∀ (h : GAf L n) (f f' : S'), (f' : GAf L n → W') = NG.rt L n h (f : GAf L n → W') →
      ((T f' : S) : GAf L n → W) = NG.rt L n h ((T f : S) : GAf L n → W)) :
    NG.HomG ρ S →ₗ[ℂ] NG.HomG ρ' S' where
  toFun Φ := ⟨(LinearMap.compLeft A (GAf L n)).comp ((Φ : S →ₗ[ℂ] (GAf L n → W)).comp T), mem_HomG_iff.2
     ⟨fun f => comp_mem_AFall A hA ((mem_HomG_iff.1 Φ.2).1 (T f)),
      fun h f f' e => by
        have := (mem_HomG_iff.1 Φ.2).2 h (T f) (T f') (hT h f f' e)
        simp only [LinearMap.comp_apply]
        rw [this]
        rfl⟩⟩
  map_add' Φ Ψ := by
    apply Subtype.ext
    apply LinearMap.ext; intro x; funext g
    simp
  map_smul' c Φ := by
    apply Subtype.ext
    apply LinearMap.ext; intro x; funext g
    simp

theorem transport_apply {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    {S : Submodule ℂ (GAf L n → W)} {S' : Submodule ℂ (GAf L n → W')}
    (A : W →ₗ[ℂ] W') (hA : ∀ γ x, A (ρ γ x) = ρ' γ (A x))
    (T : S' →ₗ[ℂ] S) (hT : ∀ (h : GAf L n) (f f' : S'), (f' : GAf L n → W') = NG.rt L n h (f : GAf L n → W') →
      ((T f' : S) : GAf L n → W) = NG.rt L n h ((T f : S) : GAf L n → W)) (Φ : NG.HomG ρ S) (x : S') (g : GAf L n) :
    ((transport A hA T hT Φ : S' →ₗ[ℂ] (GAf L n → W')) x) g = A ((Φ : S →ₗ[ℂ] (GAf L n → W)) (T x) g) := rfl

theorem mult_eq_of_iso : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n),
    π.Iso π' → π.mult = π'.mult := by
  rintro L _ _ _ n π π' ⟨⟨A, hA⟩, ⟨T, hT⟩⟩
  have hTs : ∀ (h : GAf L n) (g g' : π'.S), (g' : GAf L n → π'.W) = NG.rt L n h (g : GAf L n → π'.W) →
      ((T.symm g' : π.S) : GAf L n → π.W) = NG.rt L n h ((T.symm g : π.S) : GAf L n → π.W) := by
    intro h g g' hg
    have key := hT h (T.symm g) ⟨NG.rt L n h (T.symm g : GAf L n → π.W), π.irrS.1.stable h _ (T.symm g).2⟩ rfl
    rw [LinearEquiv.apply_symm_apply, ← hg] at key
    have e2 : T ⟨NG.rt L n h (T.symm g : GAf L n → π.W), π.irrS.1.stable h _ (T.symm g).2⟩ = g' := Subtype.ext key
    rw [← e2, LinearEquiv.symm_apply_apply]
  have hAs : ∀ γ x, A.symm (π'.ρ γ x) = π.ρ γ (A.symm x) := by
    intro γ x
    apply A.injective
    rw [LinearEquiv.apply_symm_apply, hA, LinearEquiv.apply_symm_apply]
  let F := transport (ρ := π.ρ) (ρ' := π'.ρ) A.toLinearMap hA T.symm.toLinearMap hTs
  let G := transport (ρ := π'.ρ) (ρ' := π.ρ) A.symm.toLinearMap hAs T.toLinearMap hT
  let e : NG.HomG π.ρ π.S ≃ₗ[ℂ] NG.HomG π'.ρ π'.S := LinearEquiv.ofLinear F G
    (by
      apply LinearMap.ext; intro Ψ
      apply Subtype.ext; apply LinearMap.ext; intro x; funext g
      simp [F, G, transport_apply])
    (by
      apply LinearMap.ext; intro Ψ
      apply Subtype.ext; apply LinearMap.ext; intro x; funext g
      simp [F, G, transport_apply])
  exact e.finrank_eq

end GlobalTheory.MultIso

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicMultiplicityEqOfIsoStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_multiplicity_eq_of_iso : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n),
    π.Iso π' → π.mult = π'.mult := by
  first | exact @GlobalTheory.MultIso.mult_eq_of_iso | exact GlobalTheory.MultIso.mult_eq_of_iso | (intros; apply GlobalTheory.MultIso.mult_eq_of_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicRepCmQuotientModel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubrepTopToSubmodule
namespace GlobalTheory.SubrepTopBot

open Representation

theorem subrep_bot_toSubmodule {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl

theorem subrep_top_toSubmodule {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl

theorem main : ∀ {G : Type} [inst : Group G] {V : Type} [inst_1 : AddCommGroup V] [inst_2 : Module ℂ V] (ρ : Representation ℂ G V), Representation.IsIrreducible ρ ↔ Nontrivial V ∧ ∀ (U : Submodule ℂ V), (∀ (g : G), ∀ v ∈ U, ((ρ : G → V →ₗ[ℂ] V) g : V → V) v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro G _ V _ _ ρ
  have hbot := subrep_bot_toSubmodule ρ
  have htop := subrep_top_toSubmodule ρ
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
      rw [← Submodule.nontrivial_iff ℂ]
      refine ⟨⟨⊥, ⊤, fun e => hne ?_⟩⟩
      apply Subrepresentation.toSubmodule_injective
      rw [hbot, htop]; exact e
    · intro U hU
      let S : Subrepresentation ρ := ⟨U, fun g v hv => hU g v hv⟩
      rcases h.eq_bot_or_eq_top S with e | e
      · left
        have := congrArg Subrepresentation.toSubmodule e
        rw [hbot] at this; exact this
      · right
        have := congrArg Subrepresentation.toSubmodule e
        rw [htop] at this; exact this
  · rintro ⟨hV, hU⟩
    haveI : Nontrivial (Subrepresentation ρ) := by
      refine ⟨⟨⊥, ⊤, fun e => ?_⟩⟩
      have := congrArg Subrepresentation.toSubmodule e
      rw [hbot, htop] at this
      exact (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤) this
    refine { eq_bot_or_eq_top := ?_ }
    intro S
    rcases hU S.toSubmodule (fun g v hv => S.apply_mem_toSubmodule g hv) with e | e
    · left; apply Subrepresentation.toSubmodule_injective; rw [hbot]; exact e
    · right; apply Subrepresentation.toSubmodule_injective; rw [htop]; exact e

end GlobalTheory.SubrepTopBot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicRepCmQuotientModel
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.AutModel

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
  {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def compE (e : W ≃ₗ[ℂ] W') : (GAf L n → W) ≃ₗ[ℂ] (GAf L n → W') :=
  LinearEquiv.piCongrRight fun _ => e

theorem compE_symm (e : W ≃ₗ[ℂ] W') : compE (L := L) (n := n) e.symm = (compE e).symm :=
  LinearEquiv.ext fun _ => rfl

theorem rt_compE (e : W ≃ₗ[ℂ] W') (h : GAf L n) (f : GAf L n → W) :
    NG.rt L n h (compE e f) = compE e (NG.rt L n h f) := rfl

def conjRep (e : W ≃ₗ[ℂ] W') (ρ : Representation ℂ (GQ L n) W) : Representation ℂ (GQ L n) W' where
  toFun γ := e.toLinearMap ∘ₗ ρ γ ∘ₗ e.symm.toLinearMap
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp

theorem conjRep_apply (e : W ≃ₗ[ℂ] W') (ρ : Representation ℂ (GQ L n) W) (γ : GQ L n) (x : W') :
    conjRep e ρ γ x = e (ρ γ (e.symm x)) := rfl

theorem conjRep_inter (e : W ≃ₗ[ℂ] W') (ρ : Representation ℂ (GQ L n) W) (γ : GQ L n) (x : W) :
    e (ρ γ x) = conjRep e ρ γ (e x) := by simp [conjRep_apply]

theorem isSubrep_map (e : W ≃ₗ[ℂ] W') {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    (he : ∀ γ x, e (ρ γ x) = ρ' γ (e x)) {S : Submodule ℂ (GAf L n → W)} (hS : NG.IsSubrep ρ S) :
    NG.IsSubrep ρ' (S.map (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨h1, N, hN, h2⟩ := hS.le hf
    refine ⟨fun γ g => ?_, N, hN, fun κ hκ g => ?_⟩
    · change e (f (γ * g)) = ρ' γ (e (f g))
      rw [h1 γ g, he]
    · change e (f (g * κ)) = e (f g)
      rw [h2 κ hκ g]
  · rintro h _ ⟨f, hf, rfl⟩
    exact ⟨NG.rt L n h f, hS.stable h f hf, rfl⟩

theorem isIrrRep_map (e : W ≃ₗ[ℂ] W') {ρ : Representation ℂ (GQ L n) W} {ρ' : Representation ℂ (GQ L n) W'}
    (he : ∀ γ x, e (ρ γ x) = ρ' γ (e x)) {S : Submodule ℂ (GAf L n → W)} (hS : NG.IsIrrRep ρ S) :
    NG.IsIrrRep ρ' (S.map (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) := by
  have he' : ∀ γ y, e.symm (ρ' γ y) = ρ γ (e.symm y) := fun γ y => by
    apply e.injective; rw [he]; simp
  obtain ⟨hsub, hne, hmin⟩ := hS
  refine ⟨isSubrep_map e he hsub, ?_, fun S' hS' hle => ?_⟩
  · intro h0
    apply hne
    have := congrArg (Submodule.comap (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) h0
    rwa [Submodule.comap_map_eq_of_injective (compE (L := L) (n := n) e).injective, Submodule.comap_bot,
      LinearMap.ker_eq_bot.mpr (compE (L := L) (n := n) e).injective] at this
  · set T := S'.comap (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W')) with hT
    have hTm : T = S'.map (compE (L := L) (n := n) e.symm : (GAf L n → W') →ₗ[ℂ] (GAf L n → W)) := by
      rw [compE_symm, Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm]
    have hTs : NG.IsSubrep ρ T := hTm ▸ isSubrep_map e.symm he' hS'
    have hTle : T ≤ S := by
      have := Submodule.comap_mono (f := (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) hle
      rwa [Submodule.comap_map_eq_of_injective (compE (L := L) (n := n) e).injective] at this
    have hS'eq : S' = T.map (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W')) := by
      rw [hT, Submodule.map_comap_eq_of_surjective (compE (L := L) (n := n) e).surjective]
    rcases hmin T hTs hTle with h | h
    · left; rw [hS'eq, h, Submodule.map_bot]
    · right; rw [hS'eq, h]

theorem isoRep_map (e : W ≃ₗ[ℂ] W') (S : Submodule ℂ (GAf L n → W)) :
    NG.IsoRep S (S.map (compE (L := L) (n := n) e : (GAf L n → W) →ₗ[ℂ] (GAf L n → W'))) := by
  refine ⟨(compE e).submoduleMap S, fun h f f' hf => ?_⟩
  simp only [LinearEquiv.submoduleMap_apply]
  rw [hf, rt_compE]

omit [Field L] [NumberField L] [IsCMField L] in
theorem irr_iff {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    ρ.IsIrreducible ↔ Nontrivial V ∧
      ∀ U : Submodule ℂ V, (∀ g : G, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  first
  | exact @_root_.GlobalTheory.SubrepTopBot.main
  | exact _root_.GlobalTheory.SubrepTopBot.main
  | (apply _root_.GlobalTheory.SubrepTopBot.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SubrepTopBot.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SubrepTopBot.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SubrepTopBot.main ..)

theorem irr_conj (e : W ≃ₗ[ℂ] W') {ρ : Representation ℂ (GQ L n) W} (h : ρ.IsIrreducible) :
    (conjRep e ρ).IsIrreducible := by
  rw [irr_iff] at h ⊢
  obtain ⟨hW, hmin⟩ := h
  refine ⟨e.symm.surjective.nontrivial, fun U' hU' => ?_⟩
  have hU : ∀ γ, ∀ x ∈ U'.comap (e : W →ₗ[ℂ] W'), ρ γ x ∈ U'.comap (e : W →ₗ[ℂ] W') := by
    intro γ x hx
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hx ⊢
    rw [conjRep_inter]; exact hU' γ _ hx
  have hback : U' = (U'.comap (e : W →ₗ[ℂ] W')).map (e : W →ₗ[ℂ] W') :=
    (Submodule.map_comap_eq_of_surjective e.surjective U').symm
  rcases hmin _ hU with h0 | h0
  · left; rw [hback, h0, Submodule.map_bot]
  · right; rw [hback, h0, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]

theorem alg_conj (e : W ≃ₗ[ℂ] W') {ρ : Representation ℂ (GQ L n) W} (h : IsAlgWeight L n ρ)
    [FiniteDimensional ℂ W'] : IsAlgWeight L n (conjRep e ρ) := by
  obtain ⟨-, ι, hι, hd, b, P, hP⟩ := h
  refine ⟨inferInstance, ι, hι, hd, b.map e, P, fun γ γ₀ hγ => ?_⟩
  rw [← hP γ γ₀ hγ]
  ext i j
  simp [LinearMap.toMatrix_apply, conjRep_apply]

theorem exists_autRepM (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n) :
    ∃ m : GlobalTheory.AutQuot.AutRepM L n, π.Iso m.toAutRep := by
  haveI : FiniteDimensional ℂ π.W := π.alg.1
  let e : π.W ≃ₗ[ℂ] (Fin (Module.finrank ℂ π.W) → ℂ) := (Module.finBasis ℂ π.W).equivFun
  let m : GlobalTheory.AutQuot.AutRepM L n :=
    { d := Module.finrank ℂ π.W
      ρ := conjRep e π.ρ
      alg := alg_conj e π.alg
      irr := irr_conj e π.irr
      S := π.S.map (compE (L := L) (n := n) e : (GAf L n → π.W) →ₗ[ℂ] (GAf L n → _))
      irrS := isIrrRep_map e (conjRep_inter e π.ρ) π.irrS }
  exact ⟨m, ⟨e, conjRep_inter e π.ρ⟩, isoRep_map e π.S⟩

end GlobalTheory.AutModel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicRepCmQuotientModelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_rep_cm_quotient_model : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π : NG.AutRep L n),
    ∃ m : GlobalTheory.AutQuot.AutRepM L n, π.Iso m.toAutRep := by
  first | exact @GlobalTheory.AutModel.exists_autRepM | exact GlobalTheory.AutModel.exists_autRepM | (intros; apply GlobalTheory.AutModel.exists_autRepM <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem autIso_symm {π π' : NG.AutRep L n} (h : π.Iso π') : π'.Iso π := (NG.AutRep.iso_equivalence (L := L) (n := n)).symm h

theorem autIso_trans {π π' π'' : NG.AutRep L n} (h : π.Iso π') (h' : π'.Iso π'') : π.Iso π'' :=
  (NG.AutRep.iso_equivalence (L := L) (n := n)).trans h h'

theorem clsA_eq_iff (π π' : NG.AutRep L n) : clsA π = clsA π' ↔ π.Iso π' := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := GlobalTheory.T.automorphic_rep_cm_quotient_model L n π'
    have h2 : m ∈ (clsA π).1 := by rw [h]; exact hm
    exact autIso_trans h2 (autIso_symm hm)
  · intro h
    apply Subtype.ext
    ext m
    exact ⟨fun h' => autIso_trans (autIso_symm h) h', fun h' => autIso_trans h h'⟩

theorem clsW_eq_iff (a b : NG.AlgWt L n) : clsW a = clsW b ↔ a.Iso b := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := GlobalTheory.T.exists_coordinate_model_of_algWeight L n b
    have h2 : m ∈ (clsW a).1 := by rw [h]; exact hm
    exact h2.trans hm.symm
  · intro h
    apply Subtype.ext
    ext m
    exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

theorem rep_iso (π : NG.AutRep L n) : (clsA π).rep.Iso π :=
  (clsA_eq_iff _ _).1 (AUq.cls_rep (clsA π))

theorem repW_iso (a : NG.AlgWt L n) : (clsW a).rep.Iso a :=
  (clsW_eq_iff _ _).1 (WtQ.cls_rep (clsW a))

theorem sphAt_iso {π π' : NG.AutRep L n} (h : π.Iso π') {v} (hs : π.SphAt v) : π'.SphAt v := by
  obtain ⟨-, T, hT⟩ := h
  obtain ⟨f, hf, hf0, hfix⟩ := hs
  refine ⟨(T ⟨f, hf⟩ : _), (T ⟨f, hf⟩).2, ?_, fun κ hκ ht => ?_⟩
  · intro h0
    apply hf0
    have : T ⟨f, hf⟩ = 0 := Subtype.ext h0
    have := congrArg Subtype.val (T.injective (this.trans T.map_zero.symm))
    exact this
  · have := hT κ ⟨f, hf⟩ ⟨f, hf⟩ (hfix κ hκ ht).symm
    exact this.symm

omit [NumberField L] [IsCMField L] in
theorem overPl_unique {w : HeightOneSpectrum (𝓞 L)} {v v' : HeightOneSpectrum (𝓞 (maximalRealSubfield L))}
    (h : NG.OverPl w v) (h' : NG.OverPl w v') : v = v' :=
  HeightOneSpectrum.ext (h.symm.trans h')

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem locAt_of_split (π : NG.AutRep L n) (s : SplitPlace L) : ∃ x, LocAt π s.w x := by
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class L n π s
  exact ⟨_, s, σ, rfl, hσ, HEq.rfl⟩

theorem locAt_unique {π π' : NG.AutRep L n} (hi : π.Iso π') {w : HeightOneSpectrum (𝓞 L)} {x x'}
    (hx : LocAt π w x) (hx' : LocAt π' w x') : x = x' := by
  obtain ⟨s, σ, hs, hσ, e⟩ := hx
  obtain ⟨s', σ', hs', hσ', e'⟩ := hx'
  obtain ⟨σ₀, -, hu⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class L n π s
  have h1 := hu π s rfl σ ((NG.AutRep.iso_equivalence (L := L) (n := n)).refl π) hσ
  have h2 := hu π' s' (hs'.trans hs.symm) σ' hi hσ'
  have key : ∀ (u u' : HeightOneSpectrum (𝓞 L)) (_ : u = u') (a : GlobalTheory.SmGL.IrrCl (GL (Fin n) (u.adicCompletion L)))
      (b : GlobalTheory.SmGL.IrrCl (GL (Fin n) (u'.adicCompletion L))), HEq a b →
      HEq (⟨n, a⟩ : GlobalTheory.LocGL.IrrGL (k := u.adicCompletion L)) (⟨n, b⟩ : GlobalTheory.LocGL.IrrGL (k := u'.adicCompletion L)) := by
    intro u u' hu a b hab
    subst hu
    cases eq_of_heq hab
    rfl
  have h3 : HEq (GlobalTheory.LocLanglands.cls σ) (GlobalTheory.LocLanglands.cls σ') :=
    key _ _ (hs.trans hs'.symm) _ _ (h1.trans h2.symm)
  exact eq_of_heq (e.symm.trans (h3.trans e'))

end

end GlobalTheory.AutQuot

namespace GlobalTheory.AutQuot

section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable (D : D7)

theorem f_sat (π : NG.AutRep D.host.E D.R.nV) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (w : PlE D.host)
    (hv : NG.OverPl w v) (Dv : InertDatum D.host.E D.R.nV v w) (hα : ∃ α, NG.SatAt π Dv α) :
    ∃ α, NG.SatAt π Dv α ∧ satOf (clsA π).rep w = Finset.univ.val.map α := by
  obtain ⟨α, hα⟩ := hα
  have hex : ∃ (v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (Dv' : InertDatum D.host.E D.R.nV v' w)
      (α' : Fin (D.R.nV / 2) → ℂ), NG.OverPl w v' ∧ NG.SatAt (clsA π).rep Dv' α' :=
    ⟨v, Dv, α, hv, GlobalTheory.T.satakeParameters_inertPlace_independent_of_model _ _ π _ (autIso_symm (rep_iso π)) v w hv Dv Dv α hα⟩
  unfold satOf
  rw [dite_eq_left hex]
  have key : ∀ (v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (Dv' : InertDatum D.host.E D.R.nV v' w)
      (α' : Fin (D.R.nV / 2) → ℂ), NG.OverPl w v' → NG.SatAt (clsA π).rep Dv' α' → NG.SatAt π Dv α' := by
    intro v' Dv' α' hv' hs'
    have e := overPl_unique hv hv'
    subst e
    exact GlobalTheory.T.satakeParameters_inertPlace_independent_of_model _ _ _ π (rep_iso π) v w hv _ Dv _ hs'
  obtain ⟨hv', hs'⟩ := hex.choose_spec.choose_spec.choose_spec
  exact ⟨_, key _ _ _ hv' hs', rfl⟩

theorem f_wt (π : NG.AutRep D.host.E D.R.nV) (a : NG.AlgWt D.host.E D.R.nV) (hd : π.toAlgWt.IsDual a) :
    wtOf D (clsA π).rep = clsW a := by
  have hπ : (clsA π).rep.toAlgWt.Iso π.toAlgWt := (rep_iso π).1
  obtain ⟨b, hb, hbu, hba⟩ := GlobalTheory.T.algWeight_contragredient_exists_unique _ _ π.toAlgWt
  have hrb : (clsA π).rep.toAlgWt.IsDual b := (hba _ hπ.symm).1
  have hex : ∃ b, (clsA π).rep.toAlgWt.IsDual b := ⟨b, hrb⟩
  unfold wtOf
  rw [dite_eq_left hex]
  obtain ⟨b', -, hbu', -⟩ := GlobalTheory.T.algWeight_contragredient_exists_unique _ _ (clsA π).rep.toAlgWt
  have h1 : b'.Iso hex.choose := (hbu' _).1 hex.choose_spec
  have h2 : b'.Iso b := (hbu' _).1 hrb
  have h3 : b.Iso a := (hbu a).1 hd
  exact (clsW_eq_iff _ _).2 ((h1.symm.trans h2).trans h3)

theorem f_infW (a : NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ) (hl : a.HWAt τ lam) :
    NG.infOf (hwOf (clsW a).rep τ) = NG.infOf lam := by
  have hi : a.Iso (clsW a).rep := (repW_iso a).symm
  obtain ⟨b0, hb0, hb0', hhw⟩ := GlobalTheory.T.algWeight_contragredient_exists_unique _ _ a
  have hr : (clsW a).rep.HWAt τ lam := ((hhw _ hi).2 τ lam hl)
  obtain ⟨huniq, hanti⟩ := GlobalTheory.T.algWeight_highestWeight_exists_unique_antitone _ _ (clsW a).rep τ
  have hex : ∃ lam, (clsW a).rep.HWAt τ lam ∧ Antitone lam := ⟨lam, hr, hanti lam hr⟩
  unfold hwOf
  rw [dite_eq_left hex, huniq.unique hex.choose_spec.1 hr]

end

end GlobalTheory.AutQuot
