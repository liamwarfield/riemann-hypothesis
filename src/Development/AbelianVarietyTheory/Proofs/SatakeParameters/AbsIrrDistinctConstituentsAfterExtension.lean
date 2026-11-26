module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceNondegenerateOfIsSSRep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfTensorInj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.WeightedChainData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctConstituentsAfterExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctOfSsOfAbsIrrOfMapRepDistinct
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoSubSpanExtensionOfScalars
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoSubSpanExtensionOfScalars
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem isoSub_span_map : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W₁ W₂ : Submodule k (Fin a → k)), IsInv ρ W₁ → IsInv ρ W₂ → IsoSub ρ W₁ W₂ → IsoSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k)))) (Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k)))) := by
  intro k Γ _ _ L _ f a ρ W₁ W₂ h₁ h₂ ⟨e, he⟩
  obtain ⟨g₁, hg₁⟩ := LinearMap.exists_extend (W₂.subtype ∘ₗ (e : W₁ →ₗ[k] W₂))
  obtain ⟨g₂, hg₂⟩ := LinearMap.exists_extend (W₁.subtype ∘ₗ (e.symm : W₂ →ₗ[k] W₁))
  have hg₁' : ∀ v : W₁, g₁ v = (e v : Fin a → k) := fun v => by
    simpa using LinearMap.congr_fun hg₁ v
  have hg₂' : ∀ v : W₂, g₂ v = (e.symm v : Fin a → k) := fun v => by
    simpa using LinearMap.congr_fun hg₂ v
  have key : ∀ (M : Matrix (Fin a) (Fin a) k) (v : Fin a → k),
      (M.map f).mulVec (f ∘ v) = f ∘ (M.mulVec v) := by
    intro M v; funext i; exact (RingHom.map_mulVec f M v i).symm
  let φ : (Fin a → L) →ₗ[L] (Fin a → L) := ((LinearMap.toMatrix' g₁).map f).mulVecLin
  let ψ : (Fin a → L) →ₗ[L] (Fin a → L) := ((LinearMap.toMatrix' g₂).map f).mulVecLin
  have hφ : ∀ w (hw : w ∈ W₁), φ (f ∘ w) = f ∘ (e ⟨w, hw⟩ : Fin a → k) := by
    intro w hw
    show ((LinearMap.toMatrix' g₁).map f).mulVec (f ∘ w) = _
    rw [key, LinearMap.toMatrix'_mulVec]
    exact congrArg _ (hg₁' ⟨w, hw⟩)
  have hψ : ∀ w (hw : w ∈ W₂), ψ (f ∘ w) = f ∘ (e.symm ⟨w, hw⟩ : Fin a → k) := by
    intro w hw
    show ((LinearMap.toMatrix' g₂).map f).mulVec (f ∘ w) = _
    rw [key, LinearMap.toMatrix'_mulVec]
    exact congrArg _ (hg₂' ⟨w, hw⟩)
  set S₁ := (fun v => f ∘ v) '' (W₁ : Set (Fin a → k)) with hS₁
  set S₂ := (fun v => f ∘ v) '' (W₂ : Set (Fin a → k)) with hS₂
  have mφ : ∀ x ∈ Submodule.span L S₁, φ x ∈ Submodule.span L S₂ := by
    intro x hx
    have : Submodule.span L S₁ ≤ (Submodule.span L S₂).comap φ := by
      rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      change φ (f ∘ w) ∈ Submodule.span L S₂
      rw [hφ w hw]
      exact Submodule.subset_span ⟨_, (e ⟨w, hw⟩).2, rfl⟩
    exact this hx
  have mψ : ∀ x ∈ Submodule.span L S₂, ψ x ∈ Submodule.span L S₁ := by
    intro x hx
    have : Submodule.span L S₂ ≤ (Submodule.span L S₁).comap ψ := by
      rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      change ψ (f ∘ w) ∈ Submodule.span L S₁
      rw [hψ w hw]
      exact Submodule.subset_span ⟨_, (e.symm ⟨w, hw⟩).2, rfl⟩
    exact this hx
  have ψφ : ∀ x ∈ Submodule.span L S₁, ψ (φ x) = x := by
    intro x hx
    have : Set.EqOn (ψ ∘ₗ φ) (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L)) S₁ := by
      rintro _ ⟨w, hw, rfl⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [hφ w hw, hψ _ (e ⟨w, hw⟩).2]
      simp
    exact LinearMap.eqOn_span' this hx
  have φψ : ∀ x ∈ Submodule.span L S₂, φ (ψ x) = x := by
    intro x hx
    have : Set.EqOn (φ ∘ₗ ψ) (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L)) S₂ := by
      rintro _ ⟨w, hw, rfl⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [hψ w hw, hφ _ (e.symm ⟨w, hw⟩).2]
      simp
    exact LinearMap.eqOn_span' this hx
  let φ' : Submodule.span L S₁ →ₗ[L] Submodule.span L S₂ := φ.restrict mφ
  let ψ' : Submodule.span L S₂ →ₗ[L] Submodule.span L S₁ := ψ.restrict mψ
  refine ⟨LinearEquiv.ofLinear φ' ψ'
    (LinearMap.ext fun x => Subtype.ext (φψ x x.2))
    (LinearMap.ext fun x => Subtype.ext (ψφ x x.2)), ?_⟩
  intro g v hv
  show φ (((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVec v)
      = ((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVec (φ v)
  have : Set.EqOn (φ ∘ₗ ((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVecLin)
      (((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVecLin ∘ₗ φ) S₁ := by
    rintro _ ⟨w, hw, rfl⟩
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply]
    have hgw : (ρ g : Matrix (Fin a) (Fin a) k).mulVec w ∈ W₁ := h₁ g w hw
    rw [key, hφ _ hgw, hφ w hw, key]
    congr 1
    exact he g ⟨w, hw⟩ hgw
  exact LinearMap.eqOn_span' this v.2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoSubSpanExtensionOfScalarsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isoSub_span_extension_of_scalars : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W₁ W₂ : Submodule k (Fin a → k)), IsInv ρ W₁ → IsInv ρ W₂ → IsoSub ρ W₁ W₂ → IsoSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k)))) (Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k)))) := by
  first | exact @GlobalTheory.isoSub_span_map | exact GlobalTheory.isoSub_span_map | (intros; apply GlobalTheory.isoSub_span_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanExtendScalarsInfEqBotOfInfEqBot
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanExtendScalarsInfEqBotOfInfEqBot
namespace GlobalTheory

theorem span_map_inf_eq_bot_of_inf_eq_bot : ∀ {k : Type} [Field k] {L : Type} [Field L] (f : k →+* L)
    {a : ℕ} (W₁ W₂ : Submodule k (Fin a → k)), W₁ ⊓ W₂ = ⊥ →
    Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))) ⊓
      Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))) = ⊥ := by
  intro k _ L _ f a W₁ W₂ h
  have hker : LinearMap.ker (W₂.mkQ ∘ₗ W₁.subtype) = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr ?_
    intro w hw
    have hw2 : (w : Fin a → k) ∈ W₂ := by
      simpa [Submodule.Quotient.mk_eq_zero] using hw
    have hw12 : (w : Fin a → k) ∈ W₁ ⊓ W₂ := ⟨w.2, hw2⟩
    rw [h] at hw12
    exact Subtype.ext (by simpa using hw12)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  let p : (Fin a → k) →ₗ[k] (Fin a → k) := W₁.subtype ∘ₗ g ∘ₗ W₂.mkQ
  have hp1 : ∀ w ∈ W₁, p w = w := by
    intro w hw
    have := LinearMap.congr_fun hg (⟨w, hw⟩ : W₁)
    have h2 : g (W₂.mkQ w) = ⟨w, hw⟩ := by simpa using this
    simp only [p, LinearMap.comp_apply, h2]
    rfl
  have hp2 : ∀ w ∈ W₂, p w = 0 := by
    intro w hw
    have h2 : W₂.mkQ w = 0 := by simpa [Submodule.Quotient.mk_eq_zero] using hw
    simp [p, h2]
  let P : (Fin a → L) →ₗ[L] (Fin a → L) := Matrix.mulVecLin ((LinearMap.toMatrix' p).map f)
  have hP : ∀ v : Fin a → k, P (f ∘ v) = f ∘ (p v) := by
    intro v
    funext i
    have := RingHom.map_mulVec f (LinearMap.toMatrix' p) v i
    simpa [P, LinearMap.toMatrix'_mulVec] using this.symm
  have hS1 : ∀ x ∈ Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))), P x = x := by
    intro x hx
    have heq : Set.EqOn P (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L))
        ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))) := by
      rintro _ ⟨v, hv, rfl⟩
      simp only [LinearMap.id_apply]
      rw [hP, hp1 v hv]
    exact LinearMap.eqOn_span heq hx
  have hS2 : ∀ x ∈ Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))), P x = 0 := by
    intro x hx
    have heq : Set.EqOn P (0 : (Fin a → L) →ₗ[L] (Fin a → L))
        ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))) := by
      rintro _ ⟨v, hv, rfl⟩
      simp only [LinearMap.zero_apply]
      rw [hP, hp2 v hv]
      funext i
      simp
    exact LinearMap.eqOn_span heq hx
  refine (Submodule.eq_bot_iff _).mpr ?_
  rintro x ⟨hx1, hx2⟩
  rw [← hS1 x hx1, hS2 x hx2]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanExtendScalarsInfEqBotOfInfEqBotStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_extendScalars_inf_eq_bot_of_inf_eq_bot : ∀ {k : Type} [Field k] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (W₁ W₂ : Submodule k (Fin a → k)), W₁ ⊓ W₂ = ⊥ → Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k))) ⊓ Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k))) = ⊥ := by
  first | exact @GlobalTheory.span_map_inf_eq_bot_of_inf_eq_bot | exact GlobalTheory.span_map_inf_eq_bot_of_inf_eq_bot | (intros; apply GlobalTheory.span_map_inf_eq_bot_of_inf_eq_bot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctOfSsOfAbsIrrOfMapRepDistinct
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct :
    ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ}
      (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → (∀ W, IsIrrSub ρ W → AbsIrrSub ρ W) →
      (∀ W₁ W₂, IsIrrSub (mapRep f ρ) W₁ → IsIrrSub (mapRep f ρ) W₂ → W₁ ⊓ W₂ = ⊥ →
        ¬ IsoSub (mapRep f ρ) W₁ W₂) →
      AbsIrrDistinct (matRep ((Units.coeHom _).comp ρ)) := by
  intro k Γ _ _ L _ f a ρ hss habs hdist
  obtain ⟨n, Vs, hint, hirr⟩ := GlobalTheory.T.semisimple_matrixRep_isInternal_irreducible ρ hss
  have hs : ∀ j, Stable (matRep ((Units.coeHom _).comp ρ)) (Vs j) :=
    fun j g v hv => (hirr j).2.1 g v hv
  have hsp : ∀ j, Submodule.span k (Set.range fun g =>
      (matRep ((Units.coeHom _).comp ρ) g).restrict (hs j g)) = ⊤ :=
    fun j => GlobalTheory.T.span_restrict_eq_top_of_absIrrSub_alt ρ (Vs j) (hs j) (habs _ (hirr j))
  refine ⟨Fin n, inferInstance, inferInstance, Vs, hs, hint, fun j => (hirr j).1, hsp, ?_⟩
  intro j j' hjj' e he
  have hiso : IsoSub ρ (Vs j) (Vs j') := by
    refine ⟨e, fun g v h => ?_⟩
    have := congrArg Subtype.val (he g v)
    exact this
  have hdisj : Vs j ⊓ Vs j' = ⊥ :=
    (hint.submodule_iSupIndep.pairwiseDisjoint hjj').eq_bot
  exact hdist _ _
    (GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top f ρ (Vs j) (hs j) (hirr j).1 (hsp j))
    (GlobalTheory.isIrrSub_mapRep_of_span_restrict_eq_top f ρ (Vs j') (hs j') (hirr j').1 (hsp j'))
    (GlobalTheory.T.span_extendScalars_inf_eq_bot_of_inf_eq_bot f (Vs j) (Vs j') hdisj)
    (GlobalTheory.T.isoSub_span_extension_of_scalars f ρ (Vs j) (Vs j') (hirr j).2.1 (hirr j').2.1 hiso)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctOfSsOfAbsIrrOfMapRepDistinctStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrrDistinct_of_isSS_absIrr_mapRep_nonIso : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → (∀ W, IsIrrSub ρ W → AbsIrrSub ρ W) → (∀ W₁ W₂, IsIrrSub (mapRep f ρ) W₁ → IsIrrSub (mapRep f ρ) W₂ → W₁ ⊓ W₂ = ⊥ → ¬ IsoSub (mapRep f ρ) W₁ W₂) → AbsIrrDistinct (matRep ((Units.coeHom _).comp ρ)) := by
  first | exact @GlobalTheory.absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct | exact GlobalTheory.absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct | (intros; apply GlobalTheory.absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctConstituentsAfterExtension
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory

theorem absIrrDistinct_repK_of_oSplitAt_of_mapRep_distinct : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GlobalTheory.SplitCoef.OSplitAt D i → GoodR D.nd i r → ∀ (K' : Type) [Field K'] (f : Kf D.nd i →+* K'), (∀ x W₁ W₂, IsIrrSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₁ → IsIrrSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₂ → W₁ ⊓ W₂ = ⊥ → ¬ IsoSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₁ W₂) → ∀ x, AbsIrrDistinct (repK D.nd i r x) := by
  intro D i r hO hr K' _ f hd x
  exact GlobalTheory.T.absIrrDistinct_of_isSS_absIrr_mapRep_nonIso f (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x)) (hr x).2.1 (hO x (r x) (hr x)) (hd x)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctConstituentsAfterExtensionStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absIrr_distinct_constituents_after_extension : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GlobalTheory.SplitCoef.OSplitAt D i → GoodR D.nd i r → ∀ (K' : Type) [Field K'] (f : Kf D.nd i →+* K'), (∀ x W₁ W₂, IsIrrSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₁ → IsIrrSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₂ → W₁ ⊓ W₂ = ⊥ → ¬ IsoSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₁ W₂) → ∀ x, AbsIrrDistinct (repK D.nd i r x) := by
  first | exact @GlobalTheory.absIrrDistinct_repK_of_oSplitAt_of_mapRep_distinct | exact GlobalTheory.absIrrDistinct_repK_of_oSplitAt_of_mapRep_distinct | (intros; apply GlobalTheory.absIrrDistinct_repK_of_oSplitAt_of_mapRep_distinct <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepDecompositionInduced
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
open GlobalTheory.WeilDeligne Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

namespace GlobalTheory.PstLine

section Letter

variable {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* End LL D)
  (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) {M : Type} [AddCommGroup M] [Module F M]

end Letter

section St

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L L' : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  (f : V →ₗ[ℚ_[l]] V') (ρ : Representation ↥L.1 ↥(GK K) V) (ρ' : Representation ↥L'.1 ↥(GK K) V')

def stMap : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P := f.rTensor (Bst P)

@[simp] theorem stMap_tmul (v : V) (b : Bst P) : stMap P f (v ⊗ₜ b) = f v ⊗ₜ b := rfl

theorem stMap_smul {a : ↥L.1} {a' : ↥L'.1} (h : ∀ x, f (a • x) = a' • f x) (x : V ⊗[ℚ_[l]] Bst P) :
    stMap P f (a • x) = a' • stMap P f x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rw [smul_tmul', stMap_tmul, h, stMap_tmul, smul_tmul']
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]

variable {f ρ ρ'}

theorem stMap_stRep (he : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] Bst P) :
    stMap P f (stRep P ρ g x) = stRep P ρ' g (stMap P f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [he]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem stMap_mem_Dpst (he : ∀ g x, f (ρ g x) = ρ' g (f x)) {x : V ⊗[ℚ_[l]] Bst P} (hx : x ∈ Dpst P ρ) :
    stMap P f x ∈ Dpst P ρ' := by
  obtain ⟨K', hx⟩ := (mem_Dpst P ρ).mp hx
  exact (mem_Dpst P ρ').mpr ⟨K', fun g hg => by rw [← stMap_stRep P he, hx g hg]⟩

variable (he : ∀ g x, f (ρ g x) = ρ' g (f x))

include he

end St

section Fun

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K L L' : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {f : V →ₗ[ℚ_[l]] V'} {ρ : Representation ↥L.1 ↥(GK K) V} {ρ' : Representation ↥L'.1 ↥(GK K) V'}

structure IsMor (hL : L.1 ≤ L'.1) (f : V →ₗ[ℚ_[l]] V') (ρ : Representation ↥L.1 ↥(GK K) V)
    (ρ' : Representation ↥L'.1 ↥(GK K) V') : Prop where
  smul : ∀ (a : ↥L.1) x, f (a • x) = IntermediateField.inclusion hL a • f x
  equiv : ∀ g x, f (ρ g x) = ρ' g (f x)

variable {hL : L.1 ≤ L'.1} (hm : IsMor hL f ρ ρ')

section Decomp

variable {n : ℕ} {e : Fin n → ↥L'.1} {A : Fin n → V' →ₗ[ℚ_[l]] V}

variable (he : ∀ g x, f (ρ g x) = ρ' g (f x)) (hA : ∀ i g y, A i (ρ' g y) = ρ g (A i y))
  (hs : ∀ y, ∑ i, e i • f (A i y) = y)




end Decomp

end Fun

section Bridge

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
  {L L' : FinExt l}
  {V V' : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  [AddCommGroup V'] [Module ↥L'.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {f : V →ₗ[ℚ_[l]] V'} {ρ : Representation ↥L.1 ↥(GK Bw.Kw) V} {ρ' : Representation ↥L'.1 ↥(GK Bw.Kw) V'}

end Bridge

section Model

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
  {L L' : FinExt l} (hL : L.1 ≤ L'.1) (m : ℕ) (r : ↥Gw →* GL (Fin m) ↥L.1)

def incV : (Fin m → ↥L.1) →ₗ[ℚ_[l]] (Fin m → ↥L'.1) :=
  (IntermediateField.inclusion hL).toLinearMap.compLeft (Fin m)

abbrev upRep : ↥Gw →* GL (Fin m) ↥L'.1 := mapRep (IntermediateField.inclusion hL).toRingHom r

theorem isMor_incV : IsMor hL (incV hL m) (Bw.repE L r) (Bw.repE L' (upRep hL m r)) := by
  constructor
  · intro a x
    exact funext fun i => map_mul (IntermediateField.inclusion hL) a (x i)
  · intro g x
    funext i
    exact RingHom.map_mulVec (IntermediateField.inclusion hL).toRingHom
      (r (Bw.e.symm g) : Matrix (Fin m) (Fin m) ↥L.1) x i

end Model

section Line

variable {l : ℕ} [Fact l.Prime]

variable {L₁ L : FinExt l} (hL : L₁.1 ≤ L.1) {a : ℕ}

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)

end Line

section Models

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
  [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
  {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {a : ℕ}

end Models

section Vec

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Bw : LocBridge l E Ω Gw O} {a : ℕ}

end Vec

end GlobalTheory.PstLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeGaloisQOfIsHeckeGalois
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NRows

theorem isHeckeGaloisQ_of_isHeckeGalois : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i)
    (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)),
    IsHeckeGalois D.nd i x r → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) r) := by
  intro D i x r hr
  refine ⟨SumRepresentations.contQ_of_continuous D.nd D.naut i r hr.1, ?_, ?_⟩
  · have : CharZero (Kf D.nd i) := RingHom.charZero (D.naut.iotaQ i)
    have h := GlobalTheory.TraceSemisimple.isSSRep_mapRep _ _ _ (D.naut.iotaQ i) _ _ hr.2.1
    have e : mapRep (iotaOQ D.nd D.naut i) r =
        mapRep (D.naut.iotaQ i) (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) r) := by
      ext g a b
      rfl
    rw [e]
    exact h
  · intro w hw B σ hB hσ
    have e3 : ((mapRep (iotaOQ D.nd D.naut i) r σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))) =
        ((r σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (iotaOQ D.nd D.naut i) := rfl
    rw [e3, Matrix.charpoly_map, hr.2.2 w hw B σ hB hσ]

end GlobalTheory.NRows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisRepQbarConjugateUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisRepQbarConjugateUnique
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.RepConjUniq

theorem main : ∀ D : D7, SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (ρ ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ' → ∃ Pm : GL (Fin D.R.nV) (Qbar (D.nd.l i)), ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm := by
  intro D hAN i x ρ ρ' h1 h2
  obtain ⟨-, -, hCheb, hBN⟩ := hAN
  have hl : (D.nd.l i).Prime := Fact.out
  have hfin : (((placesOver D.host.E (D.nd.l i)) ∪ (D.nd.S i : Set _)) ∪ (D.nd.Q i : Set _)).Finite :=
    ((Formalism.MainNotions.SumRepresentations.placesOver_finite D.host.E (D.nd.l i) hl.ne_zero).union (D.nd.S i).finite_toSet).union
      (D.nd.Q i).finite_toSet
  have hdense := hCheb _ hfin
  have hfrob : ∀ g ∈ {σ : G D.host.E D.nd.Om | ∃ w ∉ (((placesOver D.host.E (D.nd.l i)) ∪ (D.nd.S i : Set _)) ∪
      (D.nd.Q i : Set _)), IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om,
      IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ},
      ((ρ g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
      ((ρ' g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly := by
    rintro σ ⟨w, hw, hsp, B, hB', hσ⟩
    simp only [Set.mem_union, not_or] at hw
    obtain ⟨⟨hwl, hwS⟩, hwQ⟩ := hw
    replace hwS : w ∉ D.nd.S i := by simpa using hwS
    replace hwQ : w ∉ D.nd.Q i := by simpa using hwQ
    have hso : SplitOut D.nd i w := ⟨hsp, hwl, hwS, hwQ⟩
    rw [h1.2.2 w hso B σ hB' hσ, h2.2.2 w hso B σ hB' hσ]
  have hall := GlobalTheory.BaseChangeConj.charpoly_eq_of_dense' ρ ρ' h1.1 h2.1 _ hdense hfrob
  exact hBN _ _ ρ ρ' h1.2.1 h2.2.1 hall

end GlobalTheory.RepConjUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisRepQbarConjugateUniqueStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeGaloisRepQbar_conjugate_unique : ∀ D : D7, SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (ρ ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ' → ∃ Pm : GL (Fin D.R.nV) (Qbar (D.nd.l i)), ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm := by
  first | exact @GlobalTheory.RepConjUniq.main | exact GlobalTheory.RepConjUniq.main | (intros; apply GlobalTheory.RepConjUniq.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBcrisHolds
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Published

theorem FontaineBcris.fund_holds (l : ℕ) [Fact l.Prime] (C : Core l) : C.Fund := by
  intro b h1 h2
  exact GlobalTheory.MemLoc.fundamental_exact l C b h1 h2

theorem FontaineBcris_holds : FontaineBcris :=
  FontaineBcris.of_rest fun l _ C =>
    ⟨GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective l C, FontaineBcris.fund_holds l C, GlobalTheory.MemLoc.FundOnto.fundOnto l C,
      GlobalTheory.T.bcris_regular_of_tensorInj l C (GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective l C)⟩

end GlobalTheory.Published
end
end

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

def Clos {R : Type} [CommRing R] (S : Subring R) (π : R) : Subring R where
  carrier := {x | ∀ n : ℕ, ∃ s ∈ S, π ^ n ∣ x - s}
  mul_mem' := by
    intro a b ha hb n
    obtain ⟨s, hs, c, hc⟩ := ha n
    obtain ⟨s', hs', c', hc'⟩ := hb n
    refine ⟨s * s', mul_mem hs hs', a * c' + s' * c, ?_⟩
    linear_combination a * hc' + s' * hc
  one_mem' := fun n => ⟨1, one_mem _, by simp⟩
  add_mem' := by
    intro a b ha hb n
    obtain ⟨s, hs, c, hc⟩ := ha n
    obtain ⟨s', hs', c', hc'⟩ := hb n
    refine ⟨s + s', add_mem hs hs', c + c', ?_⟩
    linear_combination hc + hc'
  zero_mem' := fun n => ⟨0, zero_mem _, by simp⟩
  neg_mem' := by
    intro a ha n
    obtain ⟨s, hs, c, hc⟩ := ha n
    refine ⟨-s, neg_mem hs, -c, ?_⟩
    linear_combination -hc

variable {l : ℕ} [Fact l.Prime]

def linv (l : ℕ) [Fact l.Prime] : Per.AinfP l := ((GlobalTheory.RingBasics.isUnit_l l).unit⁻¹ : (Per.AinfP l)ˣ)

theorem mul_linv : ((l : ℕ) : Per.AinfP l) * linv l = 1 := (GlobalTheory.RingBasics.isUnit_l l).mul_val_inv

def beta (ϖ : Per.Fl l) : Per.AinfP l :=
  linv l * algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm ϖ) - 1

theorem l_mul_beta (ϖ : Per.Fl l) : ((l : ℕ) : Per.AinfP l) * beta ϖ =
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm ϖ) - ((l : ℕ) : Per.AinfP l) := by
  have h := mul_linv (l := l)
  rw [beta]
  linear_combination algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm ϖ) * h

def Sa (ϖ : Per.Fl l) : Subalgebra (Per.Ainf l) (Per.AinfP l) := Algebra.adjoin _ {beta ϖ}

def Sg (ϖ : Per.Fl l) : Subring (Per.BdRp l) :=
  (Sa ϖ).toSubring.map (algebraMap (Per.AinfP l) (Per.BdRp l))

def betaD (ϖ : Per.Fl l) : Per.BdRp l := algebraMap (Per.AinfP l) (Per.BdRp l) (beta ϖ)

end GlobalTheory.Pst.StLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrimeOfLiesOver
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.InertCompare Classical

namespace GlobalTheory.InertCompare

open Formalism.FrobeniusOrbits GlobalTheory.Proof.IdempotentLatticeSequence

theorem ne_of_inert (D : D7) (l : ℕ) (h : IsResidueClassZero D l ∨ IsSg D l) : l ∉ D.host.small ∧ l ≠ D.host.q ∧ l ≠ D.host.d := by
  rcases h with h | h
  · have k := (primeClass_eq_inert_iff D.host.toHostRaw).1 h
    exact ⟨k.1, k.2.1, k.2.2.1⟩
  · have k := (primeClass_eq_signal_iff D.host.toHostRaw).1 h
    exact ⟨k.1, k.2.1, k.2.2.1⟩

theorem primeOf_liesOver {l : ℕ} [Fact l.Prime] {E : Type} [Field E] (ρ : E →+* ℂ_[l]) :
    (primeOf ρ).LiesOver (Ideal.span {(l : ℤ)}) := by
  have := primeOf_isPrime ρ
  refine ⟨(span_prime_isMaximal l Fact.out).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact natCast_mem_primeOf ρ

theorem galE_frob_snd (D : D7) (l : ℕ) [Fact l.Prime] (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q) (hd : l ≠ D.host.d)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) :
    (D.host.galE σ).2 = D.R.iota (G.hP D l) := by
  have hc : l.Coprime D.host.condN :=
    (Nat.Prime.coprime_iff_not_dvd Fact.out).2 (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd)
  have hne : ∃ g, g ∈ Formalism.MainNotions.G.frobSet D l := ⟨_, P, inferInstance, inferInstance, σ, hσ, rfl⟩
  obtain ⟨P₀, hP₀, hL₀, σ₀, hσ₀, hg₀⟩ := Classical.epsilon_spec hne
  have e1 := (D.host.toHostAx.frob_iff l hc P σ).1 hσ
  have e2 := (@Formalism.HC.HostAx.frob_iff _ D.host.toHostAx l _ hc P₀ hP₀ hL₀ σ₀).1 hσ₀
  unfold Formalism.MainNotions.G.hP
  rw [Formalism.HC.Frame.iota_iotaInv, ← hg₀]
  exact congrArg Prod.snd (e1.trans e2.symm)

theorem plGG_posPl_one (D : D7) (l : ℕ) [Fact l.Prime] (h : IsResidueClassZero D l ∨ IsSg D l)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) (z : Bool × HH D) :
    plGG D (posPl D l z 1) = plGG D z * D.host.galE σ * D.R.cc := by
  obtain ⟨h2, hq, hd⟩ := ne_of_inert D l h
  have hC := factClassFrob D.R D.host l (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) P σ hσ
  have hH := galE_frob_snd D l h2 hq hd P σ hσ
  have hpl : ∀ z : Bool × HH D, plGG D z = ((if z.1 then -1 else 1, 1), D.R.iota z.2) := by
    rintro ⟨b, t⟩
    cases b <;> rfl
  rw [hpl, hpl]
  refine Prod.ext ?_ ?_
  · rcases h with h | h
    · have h1 := hC.2.2.1 h
      have hs : ¬ IsSg D l := fun hs => by
        have := h.symm.trans hs
        cases this
      simp only [Prod.fst_mul, h1, Formalism.HC.Frame.cc, c0, posPl, partner, hs]
      cases z.1 <;> simp
    · have h1 := hC.2.1.1 h
      have hp : (partner D l z.2 1).1 = true := decide_eq_true ⟨h, odd_one⟩
      simp only [Prod.fst_mul, h1, Formalism.HC.Frame.cc, c0, posPl, hp]
      cases z.1 <;> simp
  · simp only [Prod.snd_mul, Formalism.HC.Frame.cc, mul_one, hH, posPl, partner, one_smul]
    rw [Formalism.HC.Frame.iota_add]

theorem exists_frob_step (D : D7) (l : ℕ) [Fact l.Prime] (h : IsResidueClassZero D l ∨ IsSg D l)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})] :
    ∃ φ : D.host.E ≃ₐ[ℚ] D.host.E, IsArithFrobAt ℤ φ P ∧ ∀ z : Bool × HH D,
      plGG D (posPl D l z 1) = plGG D z * D.host.galE φ * D.R.cc := by
  obtain ⟨h2, hq, hd⟩ := ne_of_inert D l h
  obtain ⟨φ, hφ⟩ := (D.host.der.frob l (UpperTheory.Small.not_dvd_condN D.host Fact.out h2 hq hd) P).1
  exact ⟨φ, hφ, plGG_posPl_one D l h P φ hφ⟩

theorem embT_tauPl (D : D7) (z : Bool × HH D) : embT D (tauPl D z) = D.host.emb (plGG D z) := by
  unfold embT tauPl
  rw [Equiv.apply_symm_apply]

theorem emb_mul_galE {R : Ranks} (H : Formalism.BasicNotions.Host R) (g : R.GG) (σ : H.E ≃ₐ[ℚ] H.E) (x : H.E) :
    H.emb (g * H.galE σ) x = H.emb g (σ x) := by
  have he : H.sigmaOf (g * H.galE σ) = H.sigmaOf g * σ := by
    unfold Host.sigmaOf
    rw [map_mul, MulEquiv.symm_apply_apply]
  change H.φ₀ (H.sigmaOf (g * H.galE σ) x) = H.φ₀ ((H.sigmaOf g * σ) x)
  rw [he]

theorem rhoH_posPl_one (D : D7) (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]) (h : IsResidueClassZero D l ∨ IsSg D l)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) (z : Bool × HH D) (x : D.host.E) :
    rhoH D lam (tauPl D (posPl D l z 1)) x = rhoH D lam (tauPl D z) (σ (D.host.conj x)) := by
  rw [rhoH_apply, rhoH_apply, embT_tauPl, embT_tauPl, plGG_posPl_one D l h P σ hσ z,
    ← D.host.galE_conjE, emb_mul_galE, emb_mul_galE]

theorem samePrime_step : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]), (IsResidueClassZero D l ∨ IsSg D l) →
    ∀ z : Bool × HH D, SamePrime (rhoH D lam (tauPl D (posPl D l z 1))) (rhoC D lam (tauPl D z)) := by
  intro D l _ lam h z a
  have := primeOf_isPrime (rhoH D lam (tauPl D z))
  have := primeOf_liesOver (rhoH D lam (tauPl D z))
  obtain ⟨φ, hφ, -⟩ := exists_frob_step D l h (primeOf (rhoH D lam (tauPl D z)))
  rw [rhoH_posPl_one D l lam h _ φ hφ]
  have hc := AlgHom.IsArithFrobAt.comap_eq hφ
  have := Ideal.ext_iff.1 hc (D.host.conj • a)
  exact this

end GlobalTheory.InertCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobGIsArithFrobAndSign
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobGIsArithFrobAndSign
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.FrobSign

theorem frobG_isArithFrob_and_sign : ∀ (D : D7) (l : ℕ) [Fact l.Prime], l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d →
    (∀ (Q : Ideal (𝓞 D.host.E)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(l : ℤ)})],
      IsArithFrobAt ℤ (D.host.sigmaOf (DV.frobG D l)) Q) ∧
    ((((DV.frobG D l).1.2 : ℤˣ) : ℤ) = jacobiSym (-(D.host.d : ℤ)) l) := by
  intro D l hl h2 hq hd
  have hlN : ¬ l ∣ D.host.condN := fun h => by
    rcases (D.host.dvd_condN_iff_small Fact.out).1 h with h | h | h
    exacts [h2 h, hq h, hd h]
  have hall : ∀ (Q : Ideal (𝓞 D.host.E)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(l : ℤ)})],
      IsArithFrobAt ℤ (D.host.sigmaOf (DV.frobG D l)) Q :=
    fun Q _ _ => GlobalTheory.FrobEmb.isArithFrobAt_frobG D l hl.out Q
  refine ⟨hall, ?_⟩
  have hlZ : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  have hlI : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hlZ.ne_zero).2 hlZ
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((Ideal.span {(l : ℤ)}).primesOver (𝓞 D.host.E)) := inferInstance
  have hg : D.host.gal (D.host.sigmaOf (DV.frobG D l)) = DV.frobG D l := MulEquiv.apply_symm_apply _ _
  have h := ((D.host.der.frob l hlN P).2.2.1 _ (hall P)).2.1
  rw [hg] at h
  exact h

end GlobalTheory.FrobSign
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobGIsArithFrobAndSignStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobG_isArithFrobAt_and_sign_eq_jacobiSym : ∀ (D : D7) (l : ℕ) [Fact l.Prime], l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → (∀ (Q : Ideal (𝓞 D.host.E)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(l : ℤ)})], IsArithFrobAt ℤ (D.host.sigmaOf (DV.frobG D l)) Q) ∧ ((((DV.frobG D l).1.2 : ℤˣ) : ℤ) = jacobiSym (-(D.host.d : ℤ)) l) := by
  first | exact @GlobalTheory.FrobSign.frobG_isArithFrob_and_sign | exact GlobalTheory.FrobSign.frobG_isArithFrob_and_sign | (intros; apply GlobalTheory.FrobSign.frobG_isArithFrob_and_sign <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumSupportDivLatticeFinal
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

namespace GlobalTheory.SuppTop

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem intAt_nat (P : HeightOneSpectrum (𝓞 E)) (c : ℕ) : IntAt P (c : E) := by
  simpa using IntAt.coe P (c : 𝓞 E)

theorem intAt_sum {ι : Type} (P : HeightOneSpectrum (𝓞 E)) (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    IntAt P (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IntAt P) (fun _ _ ha hb => ha.add hb) (by simpa using intAt_nat P 0) h

theorem smul_mem_of_inFr {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b)
    (hf : ∀ y, f y ∈ localization₂ P.asIdeal N ↔ y ∈ stdAt E a P) (hf' : ∀ y, f' y ∈ localization₂ P.asIdeal N' ↔ y ∈ stdAt E b P)
    (c : ℕ) (x : HomE E a b) (h : ∀ s l, IntAt P ((c : E) * inFr f f' x (Pi.single s 1) l)) :
    ∀ y ∈ localization₂ P.asIdeal N, (c : E) • x y ∈ localization₂ P.asIdeal N' := by
  intro y hy
  have hv : f.symm y ∈ stdAt E a P := (hf _).1 (by simpa using hy)
  have hv' : ∀ i, IntAt P (f.symm y i) := (mem_localization_standardLattice P _).1 hv
  have e : (c : E) • x y = f' ((c : E) • inFr f f' x (f.symm y)) := by simp [inFr]
  rw [e, hf']
  refine (mem_localization_standardLattice P _).2 fun l => ?_
  have e2 : inFr f f' x (f.symm y) = ∑ s, f.symm y s • inFr f f' x (Pi.single s 1) := by
    conv_lhs => rw [pi_eq_sum_univ' (f.symm y)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  rw [e2]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine intAt_sum P _ _ fun s _ => ?_
  rw [mul_left_comm]
  exact (hv' s).mul (h s l)

theorem entB_zero {N' N : ℕ} (q k₀ c' n' n : ℕ) (hc : c' = 0) (ex' ex : ℕ → ℕ) (x : HomE E N' N) (p p' : ℕ) (hp : p < n)
    (hp' : p' < n') :
    LocE.entB q k₀ c' n' 0 n ex' ex x p p' = Loc.atN (x (Loc.eN E N' p')) p := by
  subst hc
  have h1 : ∀ m s, LocE.fIdx k₀ 0 m s = s := by
    intro m s
    unfold LocE.fIdx
    split_ifs <;> omega
  simp [LocE.entB, h1, LocE.scE, hp, hp']

end General

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem intAt_of_phiTop (sharp : Bool) (m2 : ℕ) (hm : R.m = m2 + 2) (P : HeightOneSpectrum (𝓞 X.E))
    (z : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)) (hz : PhiTop Ch mu sharp m2 P z ≠ 0)
    (p p' : ℕ) (hp : p < R.N R.m - 1) (hp' : p' < R.N (m2 + 1)) :
    IntAt P (Loc.atN (z (Loc.eN X.E _ p')) p) := by
  have hc : cOf R (m2 + 1) = 0 := by unfold cOf; omega
  have ha : p' < R.r + (R.m - 1) * R.t := by
    have : R.m - 1 = m2 + 1 := by omega
    unfold Ranks.N at hp'
    unfold Ranks.r
    rw [this]
    have : (m2 + 1) * (R.t + 1) = (m2 + 1) * R.t + (m2 + 1) := by ring
    omega
  unfold PhiTop at hz
  split_ifs at hz
  · unfold LocE.PhiGS at hz
    simp only at hz
    split_ifs at hz with h
    · have := h.1 p p' hp ha
      rwa [entB_zero _ _ _ _ _ hc _ _ _ _ _ hp hp'] at this
    · exact absurd rfl hz
  · unfold LocE.PhiG at hz
    simp only at hz
    split_ifs at hz with h
    · have := h.1 p p' hp ha
      rwa [entB_zero _ _ _ _ _ hc _ _ _ _ _ hp hp'] at this
    · exact absurd rfl hz
  · unfold LocE.PhiQ at hz
    split_ifs at hz with h
    · have := h.1 p p' hp (by omega)
      rwa [entB_zero _ _ _ _ _ hc _ _ _ _ _ hp hp'] at this
    · exact absurd rfl hz

theorem intAt_of_ftY {n : ℕ} (P : rowSG Pr sel mu) (η : Sp X.E n →ₗ[X.E] X.E) (y' : Sp X.E n)
    (h : ftY sel mu cst P η y' ≠ 0) (s : Fin n) : IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η (Pi.single s 1)) := by
  unfold ftY at h
  split_ifs at h with h1 h2 h3
  · have := (intAt_nat P.1 (qOf P.1 ^ cst.M)).mul (h2 s)
    simpa using this
  · exact absurd rfl h
  · exact h3 s
  · exact absurd rfl h

end Chain

end GlobalTheory.SuppTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumSupportDivLatticeInterior
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

namespace GlobalTheory.Proof.datum_support_div_lattice_interior

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem intAt_sum {P : HeightOneSpectrum (𝓞 E)} {ι : Type} (s : Finset ι) (f : ι → E)
    (h : ∀ i ∈ s, IntAt P (f i)) : IntAt P (∑ i ∈ s, f i) := by
  refine Finset.sum_induction f (IntAt P) (fun _ _ ha hb => ha.add hb) ?_ h
  simpa using IntAt.coe P 0

theorem smul_mem_of_frames {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E a))
    (M' : Submodule (𝓞 E) (Sp E b)) (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b)
    (hf : ∀ x, f x ∈ M ↔ x ∈ stdAt E a P) (hf' : ∀ x, f' x ∈ M' ↔ x ∈ stdAt E b P)
    (x : HomE E a b) (c : E) (h : ∀ s l, IntAt P (c * inFr f f' x (Pi.single s 1) l)) :
    ∀ y ∈ M, c • x y ∈ M' := by
  classical
  intro y hy
  obtain ⟨z, rfl⟩ := f.surjective y
  have hz : ∀ i, IntAt P (z i) := (mem_localization_standardLattice P z).1 ((hf z).1 hy)
  have e : c • x (f z) = f' (c • inFr f f' x z) := by simp [inFr]
  rw [e, hf']
  refine (mem_localization_standardLattice P _).2 fun l => ?_
  have hz' : z = ∑ s, z s • (Pi.single s (1 : E) : Sp E a) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have e2 : (c • inFr f f' x z) l = ∑ s, z s * (c * inFr f f' x (Pi.single s 1) l) := by
    conv_lhs => rw [hz']
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e2]
  exact intAt_sum _ _ fun s _ => (hz s).mul (h s l)

end General

end GlobalTheory.Proof.datum_support_div_lattice_interior
end
