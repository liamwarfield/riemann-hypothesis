module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumRealRestrictionGaussianEntire
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureChangeFramedGeometricPointUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSplitTorusSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapLtSwapIffOfAddTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmMulRightOfIsCMExt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverFibreTorsorTrivialLevelChanges
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverFibreTorsorTrivialLevelChanges
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevOrbit

def quotEquiv {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (K : Submodule R M) (f g : M →ₗ[R] M)
    (hK : ∀ a ∈ K, f a ∈ K) (hK' : ∀ a ∈ K, g a ∈ K) (hfg : ∀ a, f (g a) - a ∈ K) (hgf : ∀ a, g (f a) - a ∈ K) :
    (M ⧸ K) ≃ₗ[R] (M ⧸ K) :=
  LinearEquiv.ofLinear (K.mapQ K f (fun a ha => hK a ha)) (K.mapQ K g (fun a ha => hK' a ha))
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        LinearMap.id_apply]
      exact (Submodule.Quotient.eq _).2 (hfg a))
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_)
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
        LinearMap.id_apply]
      exact (Submodule.Quotient.eq _).2 (hgf a))

theorem smul_top_comap {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M) :
    ∀ a ∈ (I • ⊤ : Submodule R M), f a ∈ (I • ⊤ : Submodule R M) := by
  have h : (I • ⊤ : Submodule R M) ≤ (I • ⊤ : Submodule R M).comap f := by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact fun a ha => h ha

theorem exists_gam_of_sim {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (g : Sim Dw) :
    ∃ γ : Gam Dw l₂, ∀ a, γ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (g.f l₂.M a) := by
  obtain ⟨h, hh⟩ := g.inv l₂.M (GlobalTheory.LevelFibre.level_pos l₂)
  exact ⟨quotEquiv _ (g.f l₂.M) h (smul_top_comap _ _) (smul_top_comap _ _)
    (fun a => GlobalTheory.LevelFibre.mem_of_modN l₂ (hh a).2) (fun a => GlobalTheory.LevelFibre.mem_of_modN l₂ (hh a).1),
    fun a => rfl⟩

theorem fibre_torsor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (lift : Gam Dw d.l₂ → Dw.La →ₗ[𝓞 E] Dw.La), IsLift lift → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (y₂ y₂' : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k), FrOver d y₂ y → (FrOver d y₂' y ↔ ∃ γ, CongMod l.Mb (lift γ) LinearMap.id ∧ levR (lift γ, LinearMap.id) y₂ y₂') ∧ ∀ γ γ', levR (lift γ, LinearMap.id) y₂ y₂' → levR (lift γ', LinearMap.id) y₂ y₂' → γ = γ' := by
  intro E _ _ _ H Dw l Xo c d hpq hlev hA hbase lift hlift k _ _ _ _ hk y₂ y₂' y hy
  obtain ⟨hd, hM, -, -, -, hE, -, -, -⟩ := id hlev
  have hLaws : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.T.abelianScheme_laws_unconditional.1
  have hN := GlobalTheory.levelMaps_closed hLaws E H Dw hpq
  refine ⟨⟨fun h' => ?_, fun ⟨γ, hγ, hr⟩ => ?_⟩, fun γ γ' h₁ h₂ => GlobalTheory.T.levelStructureChange_framedGeometricPoint_unique E H Dw d.l₂ d.Xo₂ d.c₂ hpq hA lift hlift k y₂ y₂' γ γ' h₁ h₂⟩
  · obtain ⟨g, ρ, ν, hg, -, hmv, hfr⟩ :=
      GlobalTheory.exists_levMove_of_frOver hLaws E H Dw l Xo c 0 d hN hd hM hE d.r d.m hE k hk y y₂ y₂' hy h'
    obtain ⟨γ, hγ⟩ := exists_gam_of_sim d.l₂ g
    have hl : ∀ a, lift γ a - g.f d.l₂.M a ∈ d.l₂.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := fun a => by
      have e := congrArg (fun f => f a) (hlift γ)
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe, hγ] at e
      exact (Submodule.Quotient.eq _).1 e
    refine ⟨γ, fun a => ?_, (GlobalTheory.LevelActionOfLifts.levR_congr hl y₂ y₂').2 ⟨ρ.hom, ν, inferInstance,
      ⟨hmv.1, hmv.2.1, fun a => ?_⟩, hfr⟩⟩
    · have h1 : lift γ a - g.f d.l₂.M a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
        Submodule.smul_mono_left hd.2.1 (hl a)
      have h2 := GlobalTheory.LevelFibre.sub_mem_of_inGam hd hg a
      have := Submodule.add_mem _ h1 h2
      rwa [sub_add_sub_cancel] at this
    · have e : ∀ x x', d.Xo₂.univ.etaA x = d.Xo₂.univ.etaA x' := fun x x' => by
        have h1 := d.Xo₂.univ.etaA_ker x
        have h2 := d.Xo₂.univ.etaA_ker x'
        rw [hA, one_smul] at h1 h2
        rw [h1, h2]
      rw [e (LinearMap.id a) (g.f d.l₂.A a)]
      exact hmv.2.2 a
  · obtain ⟨ρ₂, ν₂, hi, hmv, hfr⟩ := hr
    obtain ⟨e₁, e₂⟩ := GlobalTheory.T.levMove_comp_r_eq_of_trivial_mod E H Dw l Xo c 0 d hpq hlev hA hbase ρ₂ ν₂ (lift γ) LinearMap.id hi hmv hγ
    obtain ⟨⟨ι, hι, hone⟩, -, -⟩ := GlobalTheory.T.framedPointMove_calculus E H Dw l Xo c
    exact GlobalTheory.frOver_of_square_of_frMove E H Dw l Xo c 0 d (𝟙 _) ι ρ₂ ν₂ d.r d.m (by rw [e₁, Category.comp_id])
      (by rw [e₂, hι, Category.comp_id]) k y y y₂ y₂' hy (hone k y) hfr

end GlobalTheory.LevOrbit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverFibreTorsorTrivialLevelChangesStatement
open CategoryTheory NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCover_fibre_torsor_trivial_level_changes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → d.l₂.A = 1 → (∀ h : KA l ≤ KA d.l₂, d.r ≫ Xo.s = d.Xo₂.s ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (IntermediateField.inclusion h).toRingHom) → ∀ (lift : Gam Dw d.l₂ → Dw.La →ₗ[𝓞 E] Dw.La), IsLift lift → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) → ∀ (y₂ y₂' : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k), FrOver d y₂ y → (FrOver d y₂' y ↔ ∃ γ, CongMod l.Mb (lift γ) LinearMap.id ∧ levR (lift γ, LinearMap.id) y₂ y₂') ∧ ∀ γ γ', levR (lift γ, LinearMap.id) y₂ y₂' → levR (lift γ', LinearMap.id) y₂ y₂' → γ = γ' := by
  first | exact @GlobalTheory.LevOrbit.fibre_torsor | exact GlobalTheory.LevOrbit.fibre_torsor | (intros; apply GlobalTheory.LevOrbit.fibre_torsor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergRhoArchimedeanAdelicPureTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergRhoArchimedeanAdelicPureTensor
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

noncomputable section

namespace GlobalTheory.ArchHeisPure

open scoped Classical Matrix

theorem exists_phase_translate {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : V →L[ℝ] ℝ) (c : ℝ) (a : V)
    (f : SchwartzMap V ℂ) : ∃ g : SchwartzMap V ℂ, ∀ x,
      g x = Complex.exp (-(2 * Real.pi * Complex.I) * ((L x + c : ℝ) : ℂ)) * f (x + a) := by
  refine ⟨SchwartzMap.smulLeftCLM ℂ (GlobalTheory.LinPhaseSeminorm.phaseLine c 1 ∘ ⇑L) (SchwartzMap.compSubConstCLM ℂ (-a) f),
    fun x => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (GlobalTheory.LinPhaseSeminorm.hasTemperateGrowth_phase L c 1),
    ← GlobalTheory.LinPhaseSeminorm.phase_eq]
  simp

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]


variable (F) in
def evHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

def trForm (c : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ c)
      map_add' := fun y y' => by rw [add_dotProduct, map_add (f := _)]
      map_smul' := fun r y => by rw [smul_dotProduct, map_smul]; rfl }

theorem evHom_apply (a : AF F) : evHom F a = evI F a := rfl

theorem trForm_apply (c y : κ → mixedEmbedding.mixedSpace F) :
    trForm c y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ c) := rfl

theorem schr_pureA [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {w : (κ → AF F) × (κ → AF F)}
    (hw : At (evI F) w) (f : SInf F κ) :
    ∃ f₁ : SInf F κ, ∀ h : (κ → Af F) → ℂ, schr ψ w (pureA F f h) = pureA F f₁ h := by
  obtain ⟨p, q⟩ := w
  obtain ⟨g, hg⟩ := exists_phase_translate (trForm fun i => evI F (q i))
    (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (p ⬝ᵥ q)))) (fun i => evI F (p i)) f
  refine ⟨g, fun h => funext fun x => ?_⟩
  have hfin : (fun i => ((x + p) i).2) = fun i => (x i).2 := by
    funext i
    have h0 : evI F ((0, 1) : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    have h1 : (1 : Af F) * (p i).2 = 0 := congrArg (fun z : (κ → AF F) × (κ → AF F) => (z.1 i).2) (hw _ h0)
    change (x i).2 + (p i).2 = _
    rw [one_mul] at h1
    rw [h1, add_zero]
  have harch : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + p) i).1) =
      (fun i => evI F (x i)) + fun i => evI F (p i) := by
    funext i
    exact map_add (evHom F) (x i) (p i)
  have hAt : At (evI F) (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q)) := by
    intro v hv
    have hq : v • q = 0 := congrArg Prod.snd (hw v hv)
    rw [smul_add, ← dotProduct_smul, smul_eq_mul, mul_left_comm, ← smul_eq_mul v, ← dotProduct_smul, hq]
    simp
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q))) =
      trForm (fun i => evI F (q i)) (fun i => evI F (x i)) +
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (⅟(2 : AF F) * (p ⬝ᵥ q))) := by
    rw [← evHom_apply, map_add (f := _), map_add (f := _), RingHom.map_dotProduct, trForm_apply]
    rfl
  simp only [schr, pureA]
  rw [hψ.2.2 _ hAt, htr, hfin, harch, ← mul_assoc, ← hg]
  rfl

theorem rho_pureA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ),
    IsStd ψ → ∀ u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → ∀ f : SInf F κ,
      ∃ f₁ : SInf F κ, ∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d hψ u hu f
  refine schr_pureA hψ (fun r hr => ?_) f
  rw [← map_smul, hu r hr, map_zero]

end GlobalTheory.ArchHeisPure

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergRhoArchimedeanAdelicPureTensorStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergRho_archimedean_adelicPureTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ),
    IsStd ψ → ∀ u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → ∀ f : SInf F κ,
      ∃ f₁ : SInf F κ, ∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h := by
  first | exact @GlobalTheory.ArchHeisPure.rho_pureA | exact GlobalTheory.ArchHeisPure.rho_pureA | (intros; apply GlobalTheory.ArchHeisPure.rho_pureA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicRepExtendingArchimedeanSchwartzRep
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicRepExtendingArchimedeanSchwartzRep
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.SliceExt

noncomputable def splitPts (F : Type) [Field F] [NumberField F] (κ : Type) :
    (κ → AF F) ≃ (κ → mixedEmbedding.mixedSpace F) × (κ → Af F) where
  toFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  invFun p := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  left_inv x := by
    funext i
    show (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1), (x i).2) : AF F) = x i
    rw [RingEquiv.symm_apply_apply]; rfl
  right_inv p := by
    refine Prod.ext ?_ rfl
    funext i
    exact RingEquiv.apply_symm_apply _ _


open scoped TensorProduct in
open NumberField MeasureTheory in
theorem _root_.GlobalTheory.SliceExt.exists_rep_pure (F : Type) [Field F] [NumberField F]
    (κ : Type) [Fintype κ]
    (G : Type) [Group G] (ρ : G →* (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →L[ℂ] _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)) :
    ∃ ω₀ : G →* Module.End ℂ ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ), ∀ (g : G) (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ)
      (h : (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ),
      ω₀ g (_root_.GlobalTheory.WeilM.pureA F f h) = _root_.GlobalTheory.WeilM.pureA F (ρ g f) h := by
  classical
  let ι : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ →ₗ[ℂ] ((κ → mixedEmbedding.mixedSpace F) → ℂ) :=
    { toFun := fun f => ⇑f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hι : Function.Injective ι := DFunLike.coe_injective
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range ι)
  let j := LinearEquiv.ofInjective ι hι
  let e := Submodule.prodEquivOfIsCompl _ C hC
  let A : G → Module.End ℂ ((κ → mixedEmbedding.mixedSpace F) → ℂ) := fun g =>
    e.toLinearMap ∘ₗ ((j.toLinearMap ∘ₗ (ρ g).toLinearMap ∘ₗ j.symm.toLinearMap).prodMap
      LinearMap.id) ∘ₗ e.symm.toLinearMap
  have hA1 : A 1 = 1 := by
    ext v
    simp [A]
  have hAmul : ∀ g h, A (g * h) = A g * A h := by
    intro g h
    ext v
    simp [A]
  have hAι : ∀ g f, A g (ι f) = ι (ρ g f) := by
    intro g f
    have : e.symm (ι f) = (j f, 0) := by
      rw [show ι f = ((j f : LinearMap.range ι) : _) from rfl]
      exact Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hC _
    simp only [A, LinearMap.comp_apply, LinearEquiv.coe_coe, this, LinearMap.prodMap_apply,
      LinearEquiv.symm_apply_apply, map_zero, LinearMap.id_apply]
    rw [Submodule.coe_prodEquivOfIsCompl']
    simp [j]
  let s := _root_.GlobalTheory.SliceExt.splitPts F κ
  let slice : ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) → (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → (κ → mixedEmbedding.mixedSpace F) → ℂ :=
    fun Φ y a => Φ (s.symm (a, y))
  let W : G → Module.End ℂ ((κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) := fun g =>
    { toFun := fun Φ x => A g (slice Φ (s x).2) (s x).1
      map_add' := by
        intro Φ Ψ
        funext x
        have : slice (Φ + Ψ) (s x).2 = slice Φ (s x).2 + slice Ψ (s x).2 := rfl
        simp only [this, map_add (f := _), Pi.add_apply]
      map_smul' := by
        intro c Φ
        funext x
        have : slice (c • Φ) (s x).2 = c • slice Φ (s x).2 := rfl
        simp only [this, map_smul, Pi.smul_apply, RingHom.id_apply] }
  refine ⟨{ toFun := W, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · ext Φ x
    simp only [W, hA1, LinearMap.coe_mk, AddHom.coe_mk, Module.End.one_apply, slice,
      Prod.mk.eta, Equiv.symm_apply_apply]
  · intro g h
    ext Φ x
    simp only [W, hAmul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
    have hsl : slice (fun x => A h (slice Φ (s x).2) (s x).1) (s x).2 = A h (slice Φ (s x).2) := by
      funext a
      simp only [slice, Equiv.apply_symm_apply]
    rw [hsl]
  · intro g f h
    funext x
    have hsl : ∀ (f' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ),
        slice (_root_.GlobalTheory.WeilM.pureA F f' h) (s x).2 = h (s x).2 • ι f' := by
      intro f'
      funext a
      have h1 := s.apply_symm_apply (a, (s x).2)
      simp only [slice, _root_.GlobalTheory.WeilM.pureA, Pi.smul_apply, smul_eq_mul]
      have ha : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (s.symm (a, (s x).2) i).1) = a :=
        congrArg Prod.fst h1
      have hy : (fun i => (s.symm (a, (s x).2) i).2) = (s x).2 := congrArg Prod.snd h1
      rw [ha, hy, mul_comm]
      rfl
    show A g (slice (_root_.GlobalTheory.WeilM.pureA F f h) (s x).2) (s x).1 = _
    rw [hsl, map_smul, hAι]
    simp only [Pi.smul_apply, smul_eq_mul, _root_.GlobalTheory.WeilM.pureA]
    rw [mul_comm]
    rfl

end GlobalTheory.SliceExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicRepExtendingArchimedeanSchwartzRepStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicRep_extending_archimedeanSchwartzRep : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (G : Type) [Group G]
    (ρ : G →* (SInf F κ →L[ℂ] SInf F κ)),
    ∃ ω₀ : G →* Module.End ℂ ((κ → AF F) → ℂ), ∀ (g : G) (f : SInf F κ) (h : (κ → Af F) → ℂ),
      ω₀ g (pureA F f h) = pureA F (ρ g f) h := by
  first | exact @GlobalTheory.SliceExt.exists_rep_pure | exact GlobalTheory.SliceExt.exists_rep_pure | (intros; apply GlobalTheory.SliceExt.exists_rep_pure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLinearOperatorL2Isometry
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLinearOperatorL2Isometry
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.PolarSB

open MeasureTheory ComplexConjugate

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

theorem integrable_mul_conj {f h : X → ℂ} (hf : f ∈ SB X) (hh : h ∈ SB X) :
    Integrable (fun x => f x * conj (h x)) μ := by
  have cf : Continuous f := hf.1.continuous
  have ch : Continuous h := hh.1.continuous
  exact (cf.mul (Complex.continuous_conj.comp ch)).integrable_of_hasCompactSupport
    (hf.2.mul_right)

theorem conj_mem {h : X → ℂ} (hh : h ∈ SB X) : (fun y => conj (h y)) ∈ SB X :=
  ⟨hh.1.comp _, hh.2.comp_left (map_zero _)⟩

theorem self_eq {g : X → ℂ} (hg : g ∈ SB X) :
    ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂μ) = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ ∧
    (∫ x, g x * conj (g x) ∂μ) = ((∫ x, ‖g x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have hi : Integrable (fun x => g x * conj (g x)) μ := integrable_mul_conj μ hg hg
  have hn : Integrable (fun x => ‖g x‖ ^ 2) μ := by
    have := hi.norm
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  constructor
  · rw [ofReal_integral_eq_lintegral_ofReal hn (Filter.Eventually.of_forall fun x => by positivity)]
    congr 1; funext x
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  · rw [← integral_complex_ofReal]
    congr 1; funext x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem expand {f h : X → ℂ} (hf : f ∈ SB X) (hh : h ∈ SB X) (c : ℂ) :
    ∫ x, (c • h + f) x * conj ((c • h + f) x) ∂μ =
      c * conj c * ∫ x, h x * conj (h x) ∂μ + c * ∫ x, h x * conj (f x) ∂μ +
      conj c * ∫ x, f x * conj (h x) ∂μ + ∫ x, f x * conj (f x) ∂μ := by
  have e : (fun x => (c • h + f) x * conj ((c • h + f) x)) =
      fun x => (c * conj c) * (h x * conj (h x)) + c * (h x * conj (f x)) +
        conj c * (f x * conj (h x)) + f x * conj (f x) := by
    funext x; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul]; ring
  rw [e, integral_add, integral_add, integral_add, integral_const_mul, integral_const_mul,
    integral_const_mul]
  all_goals first
    | exact integrable_mul_conj μ hf hf
    | exact (integrable_mul_conj μ hh hh).const_mul _
    | exact (integrable_mul_conj μ hh hf).const_mul _
    | exact (integrable_mul_conj μ hf hh).const_mul _
    | exact ((integrable_mul_conj μ hh hh).const_mul _).add ((integrable_mul_conj μ hh hf).const_mul _)
    | exact (((integrable_mul_conj μ hh hh).const_mul _).add
        ((integrable_mul_conj μ hh hf).const_mul _)).add ((integrable_mul_conj μ hf hh).const_mul _)

end GlobalTheory.PolarSB


open MeasureTheory ComplexConjugate in
theorem GlobalTheory.PolarSB.pairing_eq : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F))
    (T : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ),
    (∀ φ ∈ SB (κ → Fv F v), T φ ∈ SB (κ → Fv F v)) →
    (∀ φ ∈ SB (κ → Fv F v), ∀ φ' ∈ SB (κ → Fv F v), ∀ c : ℂ, T (c • φ + φ') = c • T φ + T φ') →
    ∀ μ : @MeasureTheory.Measure (κ → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    (∀ φ ∈ SB (κ → Fv F v), ∫⁻ y, ‖T φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v),
      ∫ x, T φ₁ x * starRingEnd ℂ (T (fun y => starRingEnd ℂ (φ₂ y)) x) ∂μ = ∫ x, φ₁ x * φ₂ x ∂μ := by
  open MeasureTheory ComplexConjugate in
  intro F _ _ κ _ v T hSB hlin μ hμ hnorm φ₁ h₁ φ₂ h₂
  letI : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  set w : (κ → Fv F v) → ℂ := fun y => starRingEnd ℂ (φ₂ y) with hw
  have hwSB : w ∈ SB (κ → Fv F v) := GlobalTheory.PolarSB.conj_mem h₂
  have hN : ∀ g ∈ SB (κ → Fv F v),
      ∫ x, T g x * conj (T g x) ∂μ = ∫ x, g x * conj (g x) ∂μ := by
    intro g hg
    obtain ⟨a1, a2⟩ := GlobalTheory.PolarSB.self_eq μ hg
    obtain ⟨b1, b2⟩ := GlobalTheory.PolarSB.self_eq μ (hSB g hg)
    rw [a2, b2]
    congr 1
    have := hnorm g hg
    rw [← a1, ← b1] at this
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun _ => by positivity)
      (integral_nonneg fun _ => by positivity)).1 this
  have key : ∀ c : ℂ,
      c * ∫ x, T w x * conj (T φ₁ x) ∂μ + conj c * ∫ x, T φ₁ x * conj (T w x) ∂μ =
      c * ∫ x, w x * conj (φ₁ x) ∂μ + conj c * ∫ x, φ₁ x * conj (w x) ∂μ := by
    intro c
    have hm : c • w + φ₁ ∈ SB (κ → Fv F v) := add_mem (Submodule.smul_mem _ c hwSB) h₁
    have e1 := hN _ hm
    rw [hlin w hwSB φ₁ h₁ c, GlobalTheory.PolarSB.expand μ h₁ hwSB c,
      GlobalTheory.PolarSB.expand μ (hSB _ h₁) (hSB _ hwSB) c, hN _ h₁, hN _ hwSB] at e1
    linear_combination e1
  have k1 := key 1
  have kI := key Complex.I
  simp only [map_one, one_mul, Complex.conj_I] at k1 kI
  have hfin : ∫ x, T φ₁ x * conj (T w x) ∂μ = ∫ x, φ₁ x * conj (w x) ∂μ := by
    linear_combination (k1 + Complex.I * kI) / 2 +
      (-(∫ x, T w x * conj (T φ₁ x) ∂μ) + ∫ x, T φ₁ x * conj (T w x) ∂μ
        + ∫ x, w x * conj (φ₁ x) ∂μ - ∫ x, φ₁ x * conj (w x) ∂μ) / 2 * Complex.I_sq
  rw [hfin]
  simp [hw]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLinearOperatorL2IsometryStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_linear_operator_l2_isometry : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F))
    (T : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ),
    (∀ φ ∈ SB (κ → Fv F v), T φ ∈ SB (κ → Fv F v)) →
    (∀ φ ∈ SB (κ → Fv F v), ∀ φ' ∈ SB (κ → Fv F v), ∀ c : ℂ, T (c • φ + φ') = c • T φ + T φ') →
    ∀ μ : @MeasureTheory.Measure (κ → Fv F v) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    (∀ φ ∈ SB (κ → Fv F v), ∫⁻ y, ‖T φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v),
      ∫ x, T φ₁ x * starRingEnd ℂ (T (fun y => starRingEnd ℂ (φ₂ y)) x) ∂μ = ∫ x, φ₁ x * φ₂ x ∂μ := by
  first | exact @GlobalTheory.PolarSB.pairing_eq | exact GlobalTheory.PolarSB.pairing_eq | (intros; apply GlobalTheory.PolarSB.pairing_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergRhoSplitArchimedeanFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergRhoSplitArchimedeanFinite
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.HeisSplit

theorem schr_add_of_orth {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a b : (κ → R) × (κ → R)) (h1 : a.1 ⬝ᵥ b.2 = 0) (h2 : b.1 ⬝ᵥ a.2 = 0) (φ : (κ → R) → ℂ) :
    schr ψ (a + b) φ = schr ψ a (schr ψ b φ) := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add, h1, h2]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  ring

theorem dot_eq_zero {R : Type} [CommRing R] {κ : Type} [Fintype κ] (e : R) (a c : κ → R) (h : e • a = 0) :
    a ⬝ᵥ (e • c) = 0 := by
  rw [dotProduct_smul, ← smul_dotProduct, h, zero_dotProduct]

section

variable (F : Type) [Field F] [NumberField F]

noncomputable def finAd (z : Af F) : AF F := ((0 : InfiniteAdeleRing F), z)

theorem finAd_mul (x : AF F) : finAd F x.2 * finAd F 1 = x * finAd F 1 := by
  refine Prod.ext ?_ ?_
  · show (0 : InfiniteAdeleRing F) * 0 = x.1 * 0
    simp
  · rfl

theorem finAd_idem : finAd F 1 * finAd F 1 = finAd F 1 := by
  refine Prod.ext ?_ ?_
  · show (0 : InfiniteAdeleRing F) * 0 = 0
    simp
  · show (1 : Af F) * 1 = 1
    simp

theorem evI_finAd : evI F (finAd F 1) = 0 := by
  exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem mul_finAd_of (t : AF F) (ht : evI F t = 0) : t * finAd F 1 = t := by
  have h : t.1 = 0 := (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 ht
  refine Prod.ext ?_ ?_
  · show t.1 * 0 = t.1
    simp [h]
  · show t.2 * 1 = t.2
    simp

theorem schr_pureA [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ] (c : (κ → AF F) × (κ → AF F))
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (h : (κ → Af F) → ℂ) :
    schr ψ (finAd F 1 • c) (pureA F f h) =
      pureA F f (fun z => schr ψ (finAd F 1 • c) (fun x => h fun i => (x i).2) fun i => finAd F (z i)) := by
  funext x
  have e1 : (fun i => finAd F (x i).2) ⬝ᵥ (finAd F 1 • c).2 = x ⬝ᵥ (finAd F 1 • c).2 := by
    simp only [dotProduct, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, ← mul_assoc, finAd_mul]
  have e2 : ∀ i, ((x + (finAd F 1 • c).1) i).1 = (x i).1 := by
    intro i
    show (x i).1 + 0 * (c.1 i).1 = (x i).1
    simp
  have e3 : ∀ i, (((fun i => finAd F (x i).2) + (finAd F 1 • c).1) i).2 = ((x + (finAd F 1 • c).1) i).2 := fun i => rfl
  simp only [schr, pureA, e1, e2, e3]
  ring

end

theorem rho_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ),
    ∀ w : Matrix α β (AE F E),
    ∃ (u : Matrix α β (AE F E)) (H : ((κ → Af F) → ℂ) → (κ → Af F) → ℂ), At (evI F) u ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        ∀ (f f₁ : SInf F κ) (h : (κ → Af F) → ℂ),
          (∀ h' : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F f h') = pureA F f₁ h') →
            d.rho ψ (actB (cA σ) g w) (pureA F f h) = pureA F f₁ (H h) := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d w
  have hu : finAd F 1 • (w - finAd F 1 • w) = 0 := by
    rw [smul_sub, smul_smul, finAd_idem, sub_self]
  refine ⟨w - finAd F 1 • w,
    fun h z => schr ψ (finAd F 1 • d.e w) (fun x => h fun i => (x i).2) fun i => finAd F (z i), ?_, ?_⟩
  · intro t ht
    rw [smul_sub, smul_smul, mul_finAd_of F t ht, sub_self]
  · intro g hg f f₁ h hyp
    have hg' := hg _ (evI_finAd F)
    rw [smul_sub, sub_eq_zero] at hg'
    have hv : actB (cA σ) g (finAd F 1 • w) = finAd F 1 • w := by
      unfold actB
      rw [Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.transpose_smul, hg', Matrix.transpose_smul, Matrix.transpose_one,
        Matrix.mul_smul, Matrix.mul_one]
    have hw : actB (cA σ) g w = actB (cA σ) g (w - finAd F 1 • w) + finAd F 1 • w := by
      have : actB (cA σ) g (w - finAd F 1 • w) = actB (cA σ) g w - actB (cA σ) g (finAd F 1 • w) := by
        unfold actB
        rw [Matrix.sub_mul]
      rw [this, hv, sub_add_cancel]
    have ha : finAd F 1 • d.e (actB (cA σ) g (w - finAd F 1 • w)) = 0 := by
      rw [← map_smul]
      unfold actB
      rw [← Matrix.smul_mul, hu, Matrix.zero_mul, map_zero]
    rw [← hyp, hw]
    unfold Darboux.rho
    rw [map_add (f := _), map_smul, schr_add_of_orth, schr_pureA]
    · exact dot_eq_zero _ _ _ (congrArg Prod.fst ha)
    · rw [dotProduct_comm]
      exact dot_eq_zero _ _ _ (congrArg Prod.snd ha)

end GlobalTheory.HeisSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergRhoSplitArchimedeanFiniteStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergRho_split_archimedean_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ),
    ∀ w : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    ∃ (u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (H : ((κ → Af F) → ℂ) → (κ → Af F) → ℂ), At (evI F) u ∧
      ∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) →
        ∀ (f f₁ : SInf F κ) (h : (κ → Af F) → ℂ),
          (∀ h' : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F f h') = pureA F f₁ h') →
            d.rho ψ (actB (cA σ) g w) (pureA F f h) = pureA F f₁ (H h) := by
  first | exact @GlobalTheory.HeisSplit.rho_split | exact GlobalTheory.HeisSplit.rho_split | (intros; apply GlobalTheory.HeisSplit.rho_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonKltLocusDimLtAfterPerturbation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimClosureLeOfSpecializes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimClosureLeOfSpecializes
namespace GlobalTheory.ClosureDimensionSpecialization

open Order TopologicalSpace Topology

theorem dim_closure_le_of_specializes : ∀ (X : AlgebraicGeometry.Scheme) (z w : ↥X) (j : ℕ),
    z ⤳ w → w ≠ z →
    topologicalKrullDim (↑(closure {z}) : Type) = (↑(j + (1 : ℕ)) : WithBot ℕ∞) →
    topologicalKrullDim (↑(closure {w}) : Type) ≤ (↑j : WithBot ℕ∞) := by
  intro X z w j hzw hne hdim
  have hsub : closure ({w} : Set X) ⊆ closure {z} :=
    closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hzw))
      isClosed_closure
  have hind : IsInducing (Set.inclusion hsub) := (IsEmbedding.inclusion hsub).isInducing
  haveI : IrreducibleSpace (closure ({z} : Set X)) :=
    Subtype.irreducibleSpace isIrreducible_singleton.closure
  let top : IrreducibleCloseds (closure ({z} : Set X)) :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩
  have hlt : ∀ a, IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a < top := by
    intro a
    refine lt_of_le_of_ne (fun _ _ => Set.mem_univ _) ?_
    intro h
    have hz : (⟨z, subset_closure rfl⟩ : closure ({z} : Set X)) ∈
        (IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a : Set _) := by
      rw [h]; exact Set.mem_univ _
    have hcl : IsClosed {x : closure ({z} : Set X) | x.1 ∈ closure ({w} : Set X)} :=
      isClosed_closure.preimage continuous_subtype_val
    have hsub' : (IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a : Set _) ⊆
        {x : closure ({z} : Set X) | x.1 ∈ closure ({w} : Set X)} := by
      rw [IrreducibleCloseds.coe_map]
      refine closure_minimal ?_ hcl
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hwz : w ⤳ z := specializes_iff_mem_closure.mpr (hsub' hz)
    exact hne ((hzw.antisymm hwz).eq).symm
  rw [topologicalKrullDim, krullDim_eq_iSup_height]
  refine iSup_le fun a => ?_
  have h1 : height a + 1 ≤ height top :=
    calc height a + 1 ≤ height (IrreducibleCloseds.map (Set.inclusion hsub) hind.continuous a) + 1 := by
          gcongr
          exact height_le_height_apply_of_strictMono _
            (IrreducibleCloseds.map_strictMono_of_isInducing hind) a
      _ ≤ height top := height_add_one_le (hlt a)
  have h2 : (height top : WithBot ℕ∞) ≤ (↑(j + (1 : ℕ)) : WithBot ℕ∞) := by
    rw [← hdim]; exact height_le_krullDim top
  have h3 : height top ≤ ((j : ℕ∞) + 1) := by exact_mod_cast h2
  have h4 : height a ≤ (j : ℕ∞) :=
    (WithTop.add_le_add_iff_right ENat.one_ne_top).mp (h1.trans h3)
  exact_mod_cast h4

end GlobalTheory.ClosureDimensionSpecialization
end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem topologicalKrullDim_closure_le_of_specializes :
    ∀ (X : Scheme.{0}) (z w : X) (j : ℕ), z ⤳ w → w ≠ z →
      topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) →
      topologicalKrullDim (closure ({w} : Set X)) ≤ j := by
  first
  | exact @_root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes
  | exact _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes
  | (apply _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes ..)

end GlobalTheory.PairStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonKltLocusDimLtAfterPerturbation
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem logCanonicalCut_of_step : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ D B : X → ℚ) (δ c : ℚ) (x z : X) (j : ℕ), KltAt p n Δ x → IsQCart D → IsQCart B →
      LcAt p n (Δ + D) x → 0 < δ → δ ≤ 1 → c ≤ 1 → Off B z →
      (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) →
      topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) →
      LcAt p n (Δ + (1 - δ) • D + c • B) x → ¬ KltAt p n (Δ + (1 - δ) • D + c • B) x →
      LcCut p n (Δ + (1 - δ) • D + c • B) x j := by
  intro X _ _ _ p n hp hn Δ D B δ c x z j hk hD hB hl hδ hδ1 hc hoff hsep hdim hlc hnk
  refine ⟨hlc, hnk, fun w hwx hw => ?_⟩
  have hx : KltAt p n (Δ + (1 - δ) • D) x :=
    kltAt_add_smul_of_lcAt X p n hp hn Δ D δ x hD hk hl hδ hδ1
  have hkw : KltAt p n (Δ + (1 - δ) • D) w :=
    (GlobalTheory.T.kawamataLogTerminal_logCanonical_generisation X p n (Δ + (1 - δ) • D) x w hwx).1 hx
  by_cases hzw : z ⤳ w
  · by_cases hwz : w = z
    · subst hwz
      exact absurd ((off_add_smul X p n (Δ + (1 - δ) • D) B c w hoff).1.2 hkw) hw
    · exact topologicalKrullDim_closure_le_of_specializes X z w j hzw hwz hdim
  · exfalso
    have h1 : KltAt p n (Δ + (1 - δ) • D + (1 : ℚ) • B) w := by
      rw [one_smul]; exact hsep w hzw (1 - δ) (by linarith) hkw
    exact hw ((GlobalTheory.T.kltAt_and_lcAt_antitone_coeff X p n hp hn (Δ + (1 - δ) • D) B c 1 w hB hc).1 h1)

end GlobalTheory.PairStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonKltLocusDimLtAfterPerturbationStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonKlt_locus_dim_lt_after_perturbation : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D B : X → ℚ) (δ c : ℚ) (x z : X) (j : ℕ), KltAt p n Δ x → IsQCart D → IsQCart B → LcAt p n (Δ + D) x → 0 < δ → δ ≤ 1 → c ≤ 1 → Off B z → (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) → topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) → LcAt p n (Δ + (1 - δ) • D + c • B) x → ¬ KltAt p n (Δ + (1 - δ) • D + c • B) x → LcCut p n (Δ + (1 - δ) • D + c • B) x j := by
  first | exact @GlobalTheory.PairStep.logCanonicalCut_of_step | exact GlobalTheory.PairStep.logCanonicalCut_of_step | (intros; apply GlobalTheory.PairStep.logCanonicalCut_of_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirGlFactorEmbeddingMemCapelliAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirGlFactorEmbeddingMemCapelliAlgebra
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CasCentre

open Finset Polynomial

variable {A : Type} [Ring A] [Algebra ℂ A]

def pS {n : ℕ} (s : Finset (Fin n)) : ℂ[X] := ∏ l ∈ s, (X - C ((l : ℕ) : ℂ))

theorem natDegree_pS {n : ℕ} (s : Finset (Fin n)) : (pS s).natDegree = s.card :=
  natDegree_finsetProd_X_sub_C_eq_card _ _

theorem prod_eq_sum {n : ℕ} (s : Finset (Fin n)) (u : ℂ) :
    ∏ l ∈ s, (u - (l : ℂ)) = ∑ k ∈ range (n + 1), u ^ k * (pS s).coeff k := by
  have h1 : (pS s).eval u = ∏ l ∈ s, (u - (l : ℂ)) := by simp [pS, eval_prod]
  have h2 : (pS s).natDegree < n + 1 := by
    rw [natDegree_pS]; have := Finset.card_le_univ s; simp at this; omega
  rw [← h1, eval_eq_sum_range' h2]
  exact sum_congr rfl fun k _ => mul_comm _ _

theorem coeff_pS_top {n : ℕ} (s : Finset (Fin n)) : (pS s).coeff s.card = 1 := by
  have hm : (pS s).Monic := monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _
  rw [← natDegree_pS]; exact hm.coeff_natDegree

theorem coeff_pS_next {n : ℕ} (s : Finset (Fin n)) (hs : 0 < s.card) :
    (pS s).coeff (s.card - 1) = -∑ l ∈ s, (l : ℂ) := by
  have h := prod_X_sub_C_nextCoeff (s := s) (fun l : Fin n => ((l : ℕ) : ℂ))
  rw [nextCoeff_of_natDegree_pos (by rw [natDegree_finsetProd_X_sub_C_eq_card]; exact hs),
    natDegree_finsetProd_X_sub_C_eq_card] at h
  exact h

theorem sum_fin_cast (n : ℕ) : 2 * ∑ l : Fin n, (l : ℂ) = (n : ℂ) * ((n : ℂ) - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := Finset.sum_range_id_mul_two n
  rw [Fin.sum_univ_eq_sum_range (fun l => ((l : ℕ) : ℂ)) n]
  have h' : ((∑ i ∈ range n, i : ℕ) : ℂ) * 2 = ((n * (n - 1) : ℕ) : ℂ) := by exact_mod_cast h
  rw [Nat.cast_mul, Nat.cast_sub (by omega)] at h'
  push_cast at h'
  linear_combination h'

theorem cas_mem_of_qdet_mem {n : ℕ} (X : Fin n → Fin n → A) (hX : Formalism.REAL.GlRel X) (S : Subalgebra ℂ A)
    (h : ∀ u : ℂ, Formalism.REAL.qdet X u ∈ S) : Formalism.REAL.Cas X ∈ S := by
  classical
  have hT : ∑ i, X i i ∈ S := GlobalTheory.CapTrace.trace_mem_of_qdet_mem X S h
  rcases lt_or_ge n 2 with hn | hn
  · have e : Formalism.REAL.Cas X = (∑ i, X i i) * (∑ i, X i i) := by
      interval_cases n <;> simp [Formalism.REAL.Cas]
    rw [e]; exact S.mul_mem hT hT
  obtain ⟨Rm, hR⟩ := GlobalTheory.qdet_top_three_orders A n X
  let Cf : ℕ → A := fun k => (pS (univ : Finset (Fin n))).coeff k • (1 : A) +
    ∑ i, (pS (univ.erase i)).coeff k • X i i +
    ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (pS ((univ.erase i).erase j)).coeff k • (X i i * X j j - X j i * X i j) +
    (if k < n - 2 then Rm k else 0)
  have hexp : ∀ u : ℂ, Formalism.REAL.qdet X u = ∑ k ∈ range (n + 1), u ^ k • Cf k := by
    intro u
    have hRm : ∑ k ∈ range (n + 1), u ^ k • (if k < n - 2 then Rm k else 0) = ∑ d ∈ range (n - 2), u ^ d • Rm d := by
      simp only [smul_ite, smul_zero]
      rw [← Finset.sum_filter]
      congr 1
      ext k; simp only [mem_filter, mem_range]; omega
    rw [hR u]
    simp only [Cf, smul_add, sum_add_distrib, hRm, prod_eq_sum, sum_smul, smul_sum, smul_smul]
    congr 1
    congr 1
    · congr 1
      exact sum_comm
    · rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      exact sum_comm
  have hmem : Cf (n - 2) ∈ S :=
    GlobalTheory.CapTrace.coeff_mem (Subalgebra.toSubmodule S) n Cf (fun u => by rw [← hexp]; exact h u) (n - 2) (by omega)
  have hc2 : ∀ i : Fin n, ∀ j ∈ univ.filter (fun j => i < j), (pS ((univ.erase i).erase j)).coeff (n - 2) = 1 := by
    intro i j hj
    have hij : j ≠ i := (mem_filter.1 hj).2.ne'
    have hc : ((univ.erase i).erase j).card = n - 2 := by
      rw [card_erase_of_mem (mem_erase.2 ⟨hij, mem_univ _⟩), card_erase_of_mem (mem_univ _), card_univ,
        Fintype.card_fin]; omega
    rw [← hc]; exact coeff_pS_top _
  have hc1 : ∀ i : Fin n, (pS (univ.erase i)).coeff (n - 2) = -∑ l ∈ univ.erase i, (l : ℂ) := by
    intro i
    have hc : (univ.erase i).card = n - 1 := by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    have := coeff_pS_next (univ.erase i) (by omega)
    rw [hc, show n - 1 - 1 = n - 2 by omega] at this
    exact this
  set c := (pS (univ : Finset (Fin n))).coeff (n - 2)
  have hC : Cf (n - 2) = c • (1 : A) + ∑ i, (pS (univ.erase i)).coeff (n - 2) • X i i +
      ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (X i i * X j j - X j i * X i j) := by
    simp only [Cf, lt_irrefl, if_false, add_zero]
    congr 1
    exact sum_congr rfl fun i _ => sum_congr rfl fun j hj => by rw [hc2 i j hj, one_smul]
  have h3 : ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • X i i + (2 : ℂ) • ∑ i, (pS (univ.erase i)).coeff (n - 2) • X i i
      = -(((n : ℂ) - 1) ^ 2) • ∑ i, X i i := by
    rw [smul_sum, smul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← add_smul, hc1, sum_erase_eq_sub (mem_univ _)]
    congr 1
    have := sum_fin_cast n
    linear_combination (-1 : ℂ) * this
  have h1 := GlobalTheory.CapelliCasimir.sq_sub_cas X hX
  have key : Formalism.REAL.Cas X = (∑ i, X i i) * (∑ i, X i i) - (2 : ℂ) • Cf (n - 2) + (2 * c) • (1 : A)
      - (((n : ℂ) - 1) ^ 2) • ∑ i, X i i := by
    linear_combination (norm := module) (-1 : ℂ) • h1 + (2 : ℂ) • hC + h3
  rw [key]
  exact S.sub_mem (S.add_mem (S.sub_mem (S.mul_mem hT hT) (S.smul_mem hmem _)) (S.smul_mem (S.one_mem) _))
    (S.smul_mem hT _)

theorem cas_Eop_mem_Zalg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ),
    Formalism.REAL.Cas (Eop (a := a) τ) ∈ Zalg E a := by
  intro E _ _ _ a τ
  refine cas_mem_of_qdet_mem (Eop τ) (glRel_Eop τ) (Zalg E a) fun u => ?_
  have e : Formalism.REAL.qdet (Eop (a := a) τ) u = cap τ (u - ((a : ℂ) - 1) / 2) := by
    rw [cap]; congr 1; ring
  rw [e]
  exact Algebra.subset_adjoin ⟨τ, _, rfl⟩

end GlobalTheory.CasCentre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirGlFactorEmbeddingMemCapelliAlgebraStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_glFactor_embedding_mem_capelliAlgebra : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ),
    Formalism.REAL.Cas (Eop (a := a) τ) ∈ Zalg E a := by
  first | exact @GlobalTheory.CasCentre.cas_Eop_mem_Zalg | exact GlobalTheory.CasCentre.cas_Eop_mem_Zalg | (intros; apply GlobalTheory.CasCentre.cas_Eop_mem_Zalg <;> assumption)
end
end
