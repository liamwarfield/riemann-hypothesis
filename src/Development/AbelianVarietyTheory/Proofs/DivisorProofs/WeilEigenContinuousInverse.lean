module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformFixedBySmallFiniteHeisenberg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenContinuousInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenContinuousInverse
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section

namespace GlobalTheory.ArchIntertw

open GlobalTheory.AdelicU

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]

def infAd : mixedEmbedding.mixedSpace F →+ AF F :=
  (LinearMap.inl F (Ainf F) (Af F)).toAddMonoidHom.comp
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddEquiv.toAddMonoidHom

def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (fstA F).toRingHom

theorem evIHom_apply (a : AF F) : evIHom a = evI F a := rfl

theorem evI_infAd (s : mixedEmbedding.mixedSpace F) : evI F (infAd s) = s :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply s

theorem sndA_infAd (s : mixedEmbedding.mixedSpace F) : sndA F (infAd s) = 0 := rfl

theorem evFin_infAd (v : Pl (F := F)) (s : mixedEmbedding.mixedSpace F) : evFin F v (infAd s) = 0 := by
  show evalV F v (sndA F (infAd s)) = 0
  rw [sndA_infAd, map_zero]

theorem infAd_evI (t : AF F) (h : sndA F t = 0) : infAd (evI F t) = t := by
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F t.1) = t.1
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _
  · exact h.symm

theorem at_infAd (s : mixedEmbedding.mixedSpace F) : At (evI F) (infAd s) := by
  intro u hu
  have h1 : fstA F u = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  rw [smul_eq_mul]
  refine Prod.ext ?_ ?_
  · change fstA F (u * infAd s) = 0
    rw [map_mul, h1, zero_mul]
  · change sndA F (u * infAd s) = 0
    rw [map_mul, sndA_infAd, mul_zero]

end SlopeTestRemainingChoices

section Aux2

variable {F : Type} [Field F] [NumberField F]

theorem evIHom_invOf [Invertible (2 : AF F)] [Invertible (2 : mixedEmbedding.mixedSpace F)] :
    evIHom (⅟(2 : AF F)) = ⅟(2 : mixedEmbedding.mixedSpace F) := by
  refine (invOf_eq_left_inv ?_).symm
  rw [show (2 : mixedEmbedding.mixedSpace F) = evIHom (2 : AF F) from (map_ofNat _ 2).symm, ← map_mul, invOf_mul_self,
    map_one]

theorem schr_pure [Invertible (2 : AF F)] [Invertible (2 : mixedEmbedding.mixedSpace F)] {κ : Type} [Fintype κ]
    (Ψ : AddChar (AF F) ℂ) (a b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ)
    (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (x : κ → AF F) :
    schr Ψ (fun i => infAd (a i), fun i => infAd (b i)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x =
      schr (Ψ.compAddMonoidHom infAd) (a, b) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (fun i => evI F (x i)) *
        ∏ᶠ v, φ v fun i => evFin F v (x i) := by
  have e1 : (fun i => evI F ((x + fun i => infAd (a i)) i)) = (fun i => evI F (x i)) + a := by
    funext i
    change evIHom (x i + infAd (a i)) = evIHom (x i) + a i
    rw [map_add (f := _), evIHom_apply (infAd _), evI_infAd]
  have e2 : ∀ v, (fun i => evFin F v ((x + fun i => infAd (a i)) i)) = fun i => evFin F v (x i) := fun v => by
    funext i
    simp only [Pi.add_apply, map_add (f := _), evFin_infAd, add_zero]
  have hs : sndA F (x ⬝ᵥ (fun i => infAd (b i)) + ⅟(2 : AF F) * ((fun i => infAd (a i)) ⬝ᵥ fun i => infAd (b i))) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_add (f := _), map_sum, map_mul, sndA_infAd, mul_zero, Finset.sum_const_zero, add_zero]
  have hi : evI F (x ⬝ᵥ (fun i => infAd (b i)) + ⅟(2 : AF F) * ((fun i => infAd (a i)) ⬝ᵥ fun i => infAd (b i))) =
      (fun i => evI F (x i)) ⬝ᵥ b + ⅟(2 : mixedEmbedding.mixedSpace F) * (a ⬝ᵥ b) := by
    rw [← evIHom_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_add (f := _), map_sum, map_mul, evIHom_invOf]
    simp only [evIHom_apply, evI_infAd]
  have e3 := infAd_evI _ hs
  rw [hi] at e3
  simp only [schr, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  have e2' : (∏ᶠ v, φ v fun i => evFin F v ((x + fun i => infAd (a i)) i)) = ∏ᶠ v, φ v fun i => evFin F v (x i) :=
    finprod_congr fun v => by rw [e2 v]
  rw [e1, e2', ← e3, AddChar.compAddMonoidHom_apply]
  ring


open Classical in
theorem exists_finprod_ne {κ : Type} [Fintype κ] (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (y : κ → mixedEmbedding.mixedSpace F) :
    ∃ x : κ → AF F, (fun i => evI F (x i)) = y ∧ ∏ᶠ v, φ v (fun i => evFin F v (x i)) ≠ 0 := by
  choose p hp using fun v => Function.ne_iff.mp (h0 v)
  have hS := Filter.eventually_cofinite.mp hstd
  let T := hS.toFinset
  let xf : κ → AF F := fun i => ∑ w ∈ T, GlobalTheory.LatVac.liftV w (p w i)
  have hxf1 : ∀ i, evI F (xf i) = 0 := fun i => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← evIHom_apply, map_sum]
    exact Finset.sum_eq_zero fun w _ => (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F))
  have hxf2 : ∀ w i, w ∈ T → evFin F w (xf i) = p w i := fun w i hw => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [xf, map_sum]
    rw [Finset.sum_eq_single_of_mem w hw]
    · exact GlobalTheory.LatVac.evFin_liftV w _
    · intro x _ hx
      exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hx) _
  have hxf3 : ∀ w i, w ∉ T → evFin F w (xf i) = 0 := fun w i hw => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [xf, map_sum]
    exact Finset.sum_eq_zero fun x hx => GlobalTheory.AdelicU.evalV_singleFin_ne (fun h => hw (by rw [h]; exact hx)) _
  refine ⟨fun i => infAd (y i) + xf i, funext fun i => ?_, ?_⟩
  · rw [← evIHom_apply, map_add (f := _), evIHom_apply, evIHom_apply, evI_infAd, hxf1, add_zero]
  · have hfin := GlobalTheory.PureFactor.mulSupport_finite φ hstd (fun i => infAd (y i) + xf i)
    rw [finprod_eq_prod_of_mulSupport_toFinset_subset _ hfin (subset_refl _)]
    refine Finset.prod_ne_zero_iff.mpr fun w _ => ?_
    by_cases hw : w ∈ T
    · have : (fun i => evFin F w (infAd (y i) + xf i)) = p w := funext fun i => by
        rw [map_add (f := _), evFin_infAd, zero_add, hxf2 w i hw]
      rw [this]
      simpa using hp w
    · have : (fun i => evFin F w (infAd (y i) + xf i)) = 0 := funext fun i => by
        rw [map_add (f := _), evFin_infAd, zero_add, hxf3 w i hw, Pi.zero_apply]
      have hw' : φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
        by_contra h
        exact hw (hS.mem_toFinset.mpr h)
      rw [this, hw', Set.indicator_of_mem (fun i => by simpa using (w.adicCompletionIntegers F).zero_mem)]
      exact one_ne_zero

end Aux2

theorem ei_schr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d,
    IsEv B M M₁ 1 1 ∅ e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
      (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
      ∀ [Invertible (2 : mixedEmbedding.mixedSpace F)], ∃ ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ,
        (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) ∧
        ∃ A : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) →
            (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
          ∀ w (f g : SInf F (Fin n × Fin d)), (g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
            (ei g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (ei f) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP M₁ hM₁ e hE ei ev hei hev hloc _
  classical
  refine ⟨B.ψ.compAddMonoidHom infAd, fun a => ?_, ?_⟩
  · show B.ψ (infAd a) = _
    rw [hP.base.std.2.2 _ (at_infAd a), evI_infAd]
  let u : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) →
      (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) := fun w => (fun i => infAd (w.1 i), fun i => infAd (w.2 i))
  refine ⟨fun w => (fun i => evI F ((M₁.co.e (M.co.e.symm (u w))).1 i),
    fun i => evI F ((M₁.co.e (M.co.e.symm (u w))).2 i)), fun w f g hg => ?_⟩
  have hM := hP.good
  have hvacM : ∀ v, M.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hpure : ∀ h : SInf F (Fin n × Fin d), e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure h M.vac) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei h) M₁.vac :=
    fun h => by
      rw [hloc h M.vac hvacM (Filter.Eventually.of_forall fun _ => rfl)]
      congr 1
      funext v
      exact (hev v).1
  have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac ∈ schA F (Fin n × Fin d) := GlobalTheory.TensUniq.pure_mem_schA f M.vac hvacM hM.std
  have key := hE.Heisenberg₂ (M.co.e.symm (u w)) _ hmem
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at key

  have hL : M.co.rho B.ψ (M.co.e.symm (u w)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac := by
    funext x
    simp only [Darboux.rho, LinearEquiv.apply_symm_apply, u]
    rw [schr_pure, Prod.mk.eta, ← hg]
    rfl

  let c : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
  have hc : ∀ s, c * infAd s = 0 := fun s => by
    refine Prod.ext ?_ ?_
    · change fstA F (c * infAd s) = 0
      rw [map_mul]
      exact zero_mul _
    · change sndA F (c * infAd s) = 0
      rw [map_mul, sndA_infAd, mul_zero]
  have hcu : c • u w = 0 := Prod.ext (funext fun i => hc _) (funext fun i => hc _)
  have hcz : c • M₁.co.e (M.co.e.symm (u w)) = 0 := by
    rw [← LinearEquiv.map_smul, ← LinearEquiv.map_smul, hcu, map_zero, map_zero]
  have hsnd : ∀ y : AF F, c * y = 0 → sndA F y = 0 := fun y hy => by
    have := congrArg (sndA F) hy
    have h1c : sndA F c = 1 := rfl
    rw [map_mul, map_zero, h1c, one_mul] at this
    exact this
  have hz : M₁.co.e (M.co.e.symm (u w)) =
      u ((fun i => evI F ((M₁.co.e (M.co.e.symm (u w))).1 i)), fun i => evI F ((M₁.co.e (M.co.e.symm (u w))).2 i)) := by
    refine Prod.ext (funext fun i => (infAd_evI _ (hsnd _ ?_)).symm) (funext fun i => (infAd_evI _ (hsnd _ ?_)).symm)
    · exact congrFun (congrArg Prod.fst hcz) i
    · exact congrFun (congrArg Prod.snd hcz) i
  rw [hL, hpure, hpure] at key
  funext y
  obtain ⟨x, hx, hne⟩ := exists_finprod_ne M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std y
  have k := congrFun key x
  rw [Darboux.rho, hz] at k
  simp only [u] at k
  rw [schr_pure] at k
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hx] at k
  exact mul_right_cancel₀ hne k

end GlobalTheory.ArchIntertw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenContinuousInverseStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_eigen_continuous_inverse : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d,
    IsEv B M M₁ 1 1 ∅ e →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
      (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
        e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
      ∀ [Invertible (2 : mixedEmbedding.mixedSpace F)], ∃ ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ,
        (∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ))) ∧
        ∃ A : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) →
            (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F),
          ∀ w (f g : SInf F (Fin n × Fin d)), (g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ w f →
            (ei g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) = schr ψ (A w) (ei f) := by
  first | exact @GlobalTheory.ArchIntertw.ei_schr | exact GlobalTheory.ArchIntertw.ei_schr | (intros; apply GlobalTheory.ArchIntertw.ei_schr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSurjectiveExtends
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSurjectiveExtends
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.ArchSurj

theorem exists_point_ne_zero {F : Type} [Field F] [NumberField F] {κ : Type} (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ)
    (hne : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    ∃ y : κ → Af F, ∀ v, φ v (fun i => y i v) ≠ 0 := by
  have key : ∀ v : Pl (F := F), ∃ z : κ → Fv F v, φ v z ≠ 0 ∧
      (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 → ∀ i, z i ∈ v.adicCompletionIntegers F) := by
    intro v
    obtain ⟨z, hz⟩ := Function.ne_iff.mp (hne v)
    refine ⟨z, hz, fun h => ?_⟩
    rw [h] at hz
    exact Set.mem_of_indicator_ne_zero hz
  choose z hz hz' using key
  exact ⟨fun i => ⟨fun v => z v i, hstd.mono fun v hv => hz' v hv i⟩, hz⟩

theorem surjective_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood B.ψ → M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, Set.SurjOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)) (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) → (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) → Function.Surjective ei := by
  intro F E _ _ _ _ _ σ B n d X W M M₁ hM hM₁ e hsurj ei ev hev he h
  have h₁ : pure h M₁.vac ∈ schA F (Fin n × Fin d) :=
    GlobalTheory.TensUniq.pure_mem_schA h M₁.vac (fun v => (hM₁.vac v).1) hM₁.std
  obtain ⟨Ψ, hΨ, heΨ⟩ := hsurj h₁
  obtain ⟨T, m, f, φ, hSB, hstd, hsum⟩ := GlobalTheory.SchADecomp.exists_sum_pure F _ Ψ hΨ
  have hvac : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = M.vac v := by
    intro i
    filter_upwards [hM.std, T.eventually_cofinite_notMem] with v hv hT
    rw [hv, hstd i v hT]
  have hid : pure h M₁.vac = ∑ i, pure (ei (f i)) fun v => ev v (φ i v) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← heΨ, hsum, map_sum]
    exact Finset.sum_congr rfl fun i _ => he (f i) (φ i) (hSB i) (hvac i)
  obtain ⟨y, hy⟩ := exists_point_ne_zero M₁.vac (fun v => (hM₁.vac v).2.1) hM₁.std
  set c : ℂ := ∏ᶠ v, M₁.vac v (fun j => y j v) with hc
  have hc0 : c ≠ 0 := finprod_induction (fun a : ℂ => a ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) hy
  set cs : Fin m → ℂ := fun i => ∏ᶠ v, ev v (φ i v) (fun j => y j v) with hcs
  refine ⟨∑ i, (cs i / c) • f i, ?_⟩
  refine DFunLike.ext _ _ fun x => ?_
  let a : Fin n × Fin d → AF F := fun j => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x j), y j)
  have hI : (fun j => evI F (a j)) = x := by
    funext j
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x j)
  have hx : h x * c = ∑ i, ei (f i) x * cs i := by
    have := congrFun hid a
    rw [Finset.sum_apply] at this
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hI] at this
    exact this
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have hs : (∑ i, ei ((cs i / c) • f i)) x = ∑ i, (cs i / c) * ei (f i) x := by
    rw [SchwartzMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]; rfl
  rw [hs]
  apply mul_right_cancel₀ hc0
  rw [hx, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

end GlobalTheory.ArchSurj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSurjectiveExtendsStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_eigen_surjective_extends : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood B.ψ → M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, Set.SurjOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)) (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) → (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) → Function.Surjective ei := by
  first | exact @GlobalTheory.ArchSurj.surjective_arch | exact GlobalTheory.ArchSurj.surjective_arch | (intros; apply GlobalTheory.ArchSurj.surjective_arch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariantCm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariantCm
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.ThetaQuasiRatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_eq_cAF' (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) : cA σ z = cAF σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem sum_three_fintype_reverse_order {ι κ μ M : Type} [Fintype ι] [Fintype κ] [Fintype μ] [AddCommMonoid M] (f : ι → κ → μ → M) :
    ∑ i, ∑ k, ∑ l, f i k l = ∑ l, ∑ k, ∑ i, f i k l := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
  exact Finset.sum_comm

theorem symp_eq_symplOF' (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E)
    (ξ : AF F ⊗[F] E) (hA : JA = JTᵀ) (hB : ξ • incM F JB = incM F (ξ₀ • JS⁻¹)) (x y : WOF F E nS nT) :
    symp (cA σ) ξ (incM F JA) (incM F JB) x y = symplOF σ JS JT ξ₀ x y := by
  have hB' : ∀ j l, ξ * incM F JB j l = incAF F E ξ₀ * incAF F E (JS⁻¹ j l) := by
    intro j l
    have h1 := congrFun (congrFun hB j) l
    rw [Matrix.smul_apply, smul_eq_mul] at h1
    rw [h1]
    show inclR (F := F) (AF F) (ξ₀ * JS⁻¹ j l) = _
    exact map_mul _ _ _
  have hA' : ∀ i k, incM F JA i k = incAF F E (JT k i) := by
    intro i k; subst hA; rfl
  unfold symp hTens symplOF hOF
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_three_fintype_reverse_order]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hA', cA_eq_cAF']
  calc ξ * (x i j * incAF F E (JT k i) * incM F JB j l * cAF σ (y k l))
      = x i j * incAF F E (JT k i) * (ξ * incM F JB j l) * cAF σ (y k l) := by ring
    _ = _ := by rw [hB']; ring

theorem thetaTr_ratWF_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : WOF F E nS nT),
            GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (ratWF γ + w) = B.ψ (-(symplOHF σ JS JT ξ₀ (ratWF γ) w)) * GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ w := by
  intro F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ hA hB κ _ co hrat Φ _ γ w
  obtain ⟨y, z, hyz⟩ := hrat γ
  have hγ : ratWF γ = incM F γ := rfl
  have hform := co.form (incM F γ) w
  rw [symp_eq_symplOF' σ JS JT ξ₀ JA JB ξ hA hB, hyz] at hform
  unfold GlobalTheory.WeilSchrodinger.thetaTr GlobalTheory.WeilM.Darboux.rho
  rw [map_add (f := _), hγ, hyz]
  set u : (κ → AF F) × (κ → AF F) :=
    (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) with hu
  set v := co.e w
  have law := GlobalTheory.ThetaQuasiRat.schr_schr B.ψ u v Φ
  have hinv : B.ψ (-(⅟(2 : AF F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) *
      B.ψ (⅟(2 : AF F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2)) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hsum : GlobalTheory.WeilM.schr B.ψ (u + v) Φ =
      B.ψ (-(⅟(2 : AF F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) • GlobalTheory.WeilM.schr B.ψ u (GlobalTheory.WeilM.schr B.ψ v Φ) := by
    rw [law, smul_smul, hinv, one_smul]
  have h2 : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
    norm_num
  rw [hsum, GlobalTheory.ThetaQuasiRat.thetaSum_smul', hu, GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F B.ψ hψ.1.2.2.1 y z, ← hu,
    symplOHF, hform, h2]

end GlobalTheory.ThetaQuasiRatF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariantCmStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTransform_rationalTranslate_quasiInvariant_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : WOF F E nS nT),
            GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (ratWF γ + w) = B.ψ (-(symplOHF σ JS JT ξ₀ (ratWF γ) w)) * GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ w := by
  first | exact @GlobalTheory.ThetaQuasiRatF.thetaTr_ratWF_add | exact GlobalTheory.ThetaQuasiRatF.thetaTr_ratWF_add | (intros; apply GlobalTheory.ThetaQuasiRatF.thetaTr_ratWF_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformAdelicSchwartzHasFiniteLevelCM
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformAdelicSchwartzHasFiniteLevelCM
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.ThetaLevelF

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


set_option maxHeartbeats 2000000 in
theorem infIdem_smul (z : AF F ⊗[F] E) :
    pairA F 1 0 • z = TensorProduct.map (GlobalTheory.ThetaLevel.infIncl F) LinearMap.id
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [TensorProduct.smul_tmul']
    rw [Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul]
    congr 1
    exact Prod.ext (one_mul _) (zero_mul _)
  | add z z' hz hz' =>
    rw [smul_add (pairA F 1 0) z z', hz, hz', map_add (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) z z',
      map_add]

theorem finIdem_smul (z : AF F ⊗[F] E) (hz : infPartF F E z = 0) : pairA F 0 1 • z = z := by
  have h1 : pairA F 0 1 + pairA F 1 0 = 1 := Prod.ext (zero_add 1) (add_zero 1)
  have h2 := infIdem_smul z
  rw [show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z = 0 from hz, map_zero] at h2
  calc pairA F 0 1 • z = pairA F 0 1 • z + pairA F 1 0 • z := by rw [h2, add_zero]
    _ = z := by rw [← add_smul, h1, one_smul]

theorem e_eq_fin {nS nT : ℕ} {B : WOF F E nS nT → WOF F E nS nT → AF F}
    {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (u : WOF F E nS nT)
    (hu : u.map (infPartF F E) = 0) :
    co.e u = ((fun i => pairA F 0 ((co.e u).1 i).2), (fun i => pairA F 0 ((co.e u).2 i).2)) := by
  have hu' : pairA F 0 1 • u = u := by
    ext a b
    exact finIdem_smul (u a b) (congrFun (congrFun hu a) b)
  have h2 := congrArg co.e hu'
  rw [LinearEquiv.map_smul] at h2
  conv_lhs => rw [← h2]
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact Prod.ext (zero_mul _) (one_mul _)
  · exact Prod.ext (zero_mul _) (one_mul _)


set_option maxHeartbeats 1000000 in
theorem thetaTr_levelF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
            ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) = GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ := by
  intro F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ hA hB κ _ co _ Φ hΦ
  haveI : IsModuleTopology (AF F) (WOF F E nS nT) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → AF F ⊗[F] E))
  obtain ⟨K, hK⟩ := GlobalTheory.ThetaLevel.schr_fin_fix F B.ψ hψ.1.1 Φ hΦ
  have hcont : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  let f1 : WOF F E nS nT →+ (κ → Af F) :=
    AddMonoidHom.mk' (fun u i => ((co.e u).1 i).2) (fun u v => by funext i; rw [map_add (f := _)]; rfl)
  let f2 : WOF F E nS nT →+ (κ → Af F) :=
    AddMonoidHom.mk' (fun u i => ((co.e u).2 i).2) (fun u v => by funext i; rw [map_add (f := _)]; rfl)
  have hf1 : Continuous f1 :=
    continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_fst.comp hcont))
  have hf2 : Continuous f2 :=
    continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_snd.comp hcont))
  let U : OpenAddSubgroup (WOF F E nS nT) := K.comap f1 hf1 ⊓ K.comap f2 hf2
  refine ⟨(U : AddSubgroup _), U.isOpen, fun u hu hinf => funext fun w => ?_⟩
  have hfix : GlobalTheory.WeilM.schr B.ψ (co.e u) Φ = Φ := by
    rw [e_eq_fin co u hinf]
    exact hK _ hu.1 _ hu.2
  show B.ψ (symplOHF σ JS JT ξ₀ w u) * GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ (co.e (w + u)) Φ) =
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ (co.e w) Φ)
  rw [map_add (f := _)]
  have h1 : GlobalTheory.WeilM.schr B.ψ (co.e w + co.e u) Φ = fun x =>
      B.ψ (-(⅟(2 : AF F) * ((co.e w).1 ⬝ᵥ (co.e u).2 - (co.e u).1 ⬝ᵥ (co.e w).2))) *
        GlobalTheory.WeilM.schr B.ψ (co.e w) (GlobalTheory.WeilM.schr B.ψ (co.e u) Φ) x :=
    funext (GlobalTheory.ThetaLevel.schr_add B.ψ _ _ Φ)
  rw [h1, hfix]
  simp only [GlobalTheory.WeilM.thetaSum]
  rw [tsum_mul_left, ← mul_assoc, ← AddChar.map_add_eq_mul]
  have h2 : symplOHF σ JS JT ξ₀ w u =
      ⅟(2 : AF F) * ((co.e w).1 ⬝ᵥ (co.e u).2 - (co.e u).1 ⬝ᵥ (co.e w).2) := by
    rw [symplOHF, GlobalTheory.TransportF.symplOF_eq_symp hA hB, co.form]
    congr 1
    refine (invOf_eq_right_inv ?_).symm
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
    norm_num
  rw [h2, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.ThetaLevelF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformAdelicSchwartzHasFiniteLevelCMStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTransform_adelicSchwartz_hasFiniteLevel_CM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
            ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) = GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ := by
  first | exact @GlobalTheory.ThetaLevelF.thetaTr_levelF | exact GlobalTheory.ThetaLevelF.thetaTr_levelF | (intros; apply GlobalTheory.ThetaLevelF.thetaTr_levelF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeHermitianSkew
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFourReorder
namespace GlobalTheory.FourTermSumReorder

theorem sum_four_reorder {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β]
    (f : α → β → α → β → R) :
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e := by
  calc ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ b : β, ∑ a : α, ∑ c : α, ∑ e : β, f a b c e := Finset.sum_comm
    _ = ∑ p : β × α, ∑ q : α × β, f p.2 p.1 q.1 q.2 := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ q : α × β, ∑ p : β × α, f p.2 p.1 q.1 q.2 := Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e := by
        simp only [Fintype.sum_prod_type]

end GlobalTheory.FourTermSumReorder
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeHermitianSkew
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SplitTraceForm
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piW_cA {σ : E →ₐ[F] E} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Fv F v) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ w) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem piW_inclR {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Fv F v) (e : E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (inclR (F := F) (AF F) e) = τ e := by
  change evFin F v 1 * τ e = τ e
  simp

theorem sum_four_fintype_permute {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β] (f : α → β → α → β → R) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ c, ∑ e, ∑ b, ∑ a, f a b c e := by
  first
  | exact @_root_.GlobalTheory.FourTermSumReorder.sum_four_reorder
  | exact _root_.GlobalTheory.FourTermSumReorder.sum_four_reorder
  | (apply _root_.GlobalTheory.FourTermSumReorder.sum_four_reorder <;> assumption)
  | (intros; apply _root_.GlobalTheory.FourTermSumReorder.sum_four_reorder <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FourTermSumReorder.sum_four_reorder <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FourTermSumReorder.sum_four_reorder ..)

theorem splitTrace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    IsCMExt F E σ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (K : Matrix (Fin d) (Fin d) E), (∀ i j, σ (J j i) = J i j) → (∀ i j, σ (K j i) = -K i j) →
    ∀ (x u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x →
    GlobalTheory.AdelicU.evFin F v (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F K) x u) =
      ∑ i, ∑ j, (x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t)) i j * (-(J.map t * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp σ)) * (K.map t)ᵀ)) i j -
        ∑ i, ∑ j, (-(J.map t * x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp σ)) * (K.map t)ᵀ)) i j * (u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t)) i j := by
  intro F E _ _ _ _ _ σ hcm v t n d J K hJ hK x u hx
  have hzAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v)
      ((-1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) * GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F K) x u) := by
    intro a ha
    have h0 : ∀ i j, a • x i j = 0 := fun i j => by
      have := congrFun (congrFun (hx a ha) i) j
      simpa using this
    simp only [GlobalTheory.WeilM.hTens, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    rw [show ∀ (p q r : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), a • ((-1) * (x i j * p * q * r)) = -1 * ((a • x i j) * p * q * r) from
      fun p q r => by simp only [Algebra.smul_def]; ring, h0]
    simp
  show GlobalTheory.AdelicU.evFin F v (Algebra.trace (AF F) _ _) = _
  rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v t _ hzAt, GlobalTheory.LatVac.evFin_liftV]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.WeilM.hTens, map_mul, map_neg, map_one, map_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, piW_cA, piW_inclR,
    GlobalTheory.AdelicU.comp_conj_conj hcm, AlgHom.comp_apply, hJ, hK]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, Finset.mul_sum, Finset.sum_mul]
  rw [sub_eq_add_neg]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · rw [sum_four_fintype_permute]
    simp only [neg_mul, mul_neg, one_mul, Finset.sum_mul, Finset.sum_neg_distrib, neg_neg]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun k _ => ?_
    ring
end GlobalTheory.SplitTraceForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeHermitianSkewStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lattice_hermitian_skew : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    IsCMExt F E σ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (K : Matrix (Fin d) (Fin d) E), (∀ i j, σ (J j i) = J i j) → (∀ i j, σ (K j i) = -K i j) →
    ∀ (x u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x →
    GlobalTheory.AdelicU.evFin F v (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F K) x u) =
      ∑ i, ∑ j, (x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t)) i j * (-(J.map t * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp σ)) * (K.map t)ᵀ)) i j -
        ∑ i, ∑ j, (-(J.map t * x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp σ)) * (K.map t)ᵀ)) i j * (u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t)) i j := by
  first | exact @GlobalTheory.SplitTraceForm.splitTrace | exact GlobalTheory.SplitTraceForm.splitTrace | (intros; apply GlobalTheory.SplitTraceForm.splitTrace <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumTwistedVacuumConditionDoubledLattic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumTwistedVacuumConditionDoubledLattic
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.DblVacLine

theorem norm_psiAt_le {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl (F := F))
    (y : Fv F v) : ‖GlobalTheory.LatVac.psiAt ψ v y‖ ≤ 1 := by
  have hc := GlobalTheory.SchrSB.continuous_psiAt ψ hψ v
  have hK := (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).image
    (f := fun t : Fv F v => ‖GlobalTheory.LatVac.psiAt ψ v (y * t)‖) ((hc.comp (continuous_const.mul continuous_id)).norm)
  obtain ⟨C, hC⟩ := hK.bddAbove
  by_contra h
  push_neg at h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  have hle : ‖GlobalTheory.LatVac.psiAt ψ v y‖ ^ n ≤ C := by
    refine hC ⟨(n : Fv F v), natCast_mem _ n, ?_⟩
    show ‖GlobalTheory.LatVac.psiAt ψ v (y * (n : Fv F v))‖ = _
    rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, norm_pow]
  linarith

theorem norm_psiAt {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl (F := F))
    (y : Fv F v) : ‖GlobalTheory.LatVac.psiAt ψ v y‖ = 1 := by
  have h1 := norm_psiAt_le ψ hψ v y
  have h2 := norm_psiAt_le ψ hψ v (-y)
  have h3 : ‖GlobalTheory.LatVac.psiAt ψ v y‖ * ‖GlobalTheory.LatVac.psiAt ψ v (-y)‖ = 1 := by
    rw [← norm_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one, norm_one]
  nlinarith [norm_nonneg (GlobalTheory.LatVac.psiAt ψ v y), norm_nonneg (GlobalTheory.LatVac.psiAt ψ v (-y))]

theorem star_psiAt {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl (F := F))
    (y : Fv F v) : star (GlobalTheory.LatVac.psiAt ψ v y) = GlobalTheory.LatVac.psiAt ψ v (-y) := by
  rw [AddChar.map_neg_eq_inv]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [Complex.star_def, Complex.conj_mul', norm_psiAt ψ hψ v y]
  simp

theorem symp_dbl_fromCols {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (w₁ w₂ : Matrix α β E) :
    symp (R := R) c ξ JA (dbl JB) (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂) =
      symp (R := R) c ξ JA JB w₁ w₁ - symp (R := R) c ξ JA JB w₂ w₂ := by
  unfold symp
  rw [← map_sub, ← mul_sub]
  congr 2
  unfold hTens
  simp only [dbl, Fintype.sum_sum_type, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_neg,
    neg_mul, Finset.sum_neg_distrib]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem at_symp_self {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n d : ℕ} (JA : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (ξ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (v : Pl (F := F)) {w : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hw : At (evFin F v) w) :
    At (evFin F v) (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ JA JB w w) := by
  intro u hu
  have h1 := GlobalTheory.LatVac.symp_smul_smul σ JA JB ξ u 1 w w
  have h0 := GlobalTheory.LatVac.symp_smul_smul σ JA JB ξ 0 1 w w
  rw [hw u hu, mul_one] at h1
  rw [zero_smul, zero_mul, zero_mul] at h0
  change u * symp (cA σ) ξ JA JB w w = 0
  rw [← h1, h0]

end GlobalTheory.DblVacLine

namespace GlobalTheory.DblVacLine

theorem dbl_vac_acts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))), IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • (G.M'.vac v))) →
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)))
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v dd hdd θ hθ hvac w₁ hw₁ w₂ hw₂
  have hψc : Continuous B.ψ := hT.base.std.1
  have hSB : G.M'.vac v ∈ SB _ := (hT.geo.hM'.vac v).1
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin a' × Fin (a + a')) v
  have hat := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W v).1
  have hloc : ∀ w ∈ latAtV G.V' G.W v, ∀ ξ, GlobalTheory.LatVac.psiAt B.ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo G.M'.co v w).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo G.M'.co v w).1 ⬝ᵥ (GlobalTheory.LatVac.locCo G.M'.co v w).2)) *
      G.M'.vac v (ξ + (GlobalTheory.LatVac.locCo G.M'.co v w).1) =
        B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w w) *
          G.M'.vac v ξ := fun w hw ξ =>
    GlobalTheory.LatVac.heis_at_local_identity v G.M'.co B.ψ w _ _ (hat w hw) (hvac w hw) R (hR _ hSB) 0 hR0 ξ
  have hatd : At (evFin F v) (Matrix.fromCols w₁ w₂) := by
    intro u hu
    have h1 := hat w₁ hw₁ u hu
    have h2 := hat w₂ hw₂ u hu
    ext i j
    rcases j with j | j
    · simpa using congrFun (congrFun h1 i) j
    · simpa using congrFun (congrFun h2 i) j
  have key := GlobalTheory.VacBridge.rho_acts_locCo dd B.ψ v _ hatd (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)))

  set x₁ := (GlobalTheory.LatVac.locCo G.M'.co v w₁).1 with hx₁
  set y₁ := (GlobalTheory.LatVac.locCo G.M'.co v w₁).2 with hy₁
  set x₂ := (GlobalTheory.LatVac.locCo G.M'.co v w₂).1 with hx₂
  set y₂ := (GlobalTheory.LatVac.locCo G.M'.co v w₂).2 with hy₂
  have hdl : GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ w₂) = (Sum.elim x₁ x₂, Sum.elim y₁ (-y₂)) := by
    simp only [hx₁, hx₂, hy₁, hy₂, GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hdd w₁ w₂]
    ext k <;> rcases k with k | k <;> simp
  set s₁ := symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₁ w₁ with hs₁
  set s₂ := symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₂ w₂ with hs₂
  have hb : At (evFin F v) (⅟(2 : AF F) * s₂) :=
    GlobalTheory.VacIndic.at_mul_left (at_symp_self σ _ _ _ v (hat w₂ hw₂))
  have hstarg : star (B.ψ (⅟(2 : AF F) * s₂)) = B.ψ (-(⅟(2 : AF F) * s₂)) := by
    have hb' : At (evFin F v) (-(⅟(2 : AF F) * s₂)) := fun u hu => by rw [smul_neg, hb u hu, neg_zero]
    rw [GlobalTheory.VacIndic.psi_of_at B.ψ hb, GlobalTheory.VacIndic.psi_of_at B.ψ hb', map_neg, ← GlobalTheory.LatVac.psiAt_apply,
      ← GlobalTheory.LatVac.psiAt_apply, star_psiAt B.ψ hψc v]
  have hcd : B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
      (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) = B.ψ (⅟(2 : AF F) * s₁) * star (B.ψ (⅟(2 : AF F) * s₂)) := by
    rw [symp_dbl_fromCols, ← hs₁, ← hs₂, hstarg, mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
  have e : GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols w₁ w₂))
      (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))) =
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
        (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)) := by
    funext x
    rw [hdl, hcd]
    simp only [GlobalTheory.WeilM.schr, boxFun, Pi.smul_apply, smul_eq_mul, invOf_eq_inv]
    have hA : x ⬝ᵥ Sum.elim y₁ (-y₂) + (2 : Fv F v)⁻¹ * (Sum.elim x₁ x₂ ⬝ᵥ Sum.elim y₁ (-y₂)) =
        ((x ∘ Sum.inl) ⬝ᵥ y₁ + (2 : Fv F v)⁻¹ * (x₁ ⬝ᵥ y₁)) +
          -((x ∘ Sum.inr) ⬝ᵥ y₂ + (2 : Fv F v)⁻¹ * (x₂ ⬝ᵥ y₂)) := by
      simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Pi.neg_apply,
        mul_neg, Finset.sum_neg_distrib]
      ring
    have h1 : (x + Sum.elim x₁ x₂) ∘ Sum.inl = x ∘ Sum.inl + x₁ := by funext i; simp
    have h2 : (x + Sum.elim x₁ x₂) ∘ Sum.inr = x ∘ Sum.inr + x₂ := by funext i; simp
    rw [hA, AddChar.map_add_eq_mul, ← star_psiAt B.ψ hψc v, h1, h2]
    have l1 := hloc w₁ hw₁ (x ∘ Sum.inl)
    have l2 := congrArg star (hloc w₂ hw₂ (x ∘ Sum.inr))
    rw [star_mul', star_mul'] at l2
    linear_combination (star (GlobalTheory.LatVac.psiAt B.ψ v ((x ∘ Sum.inr) ⬝ᵥ y₂ + (2 : Fv F v)⁻¹ * (x₂ ⬝ᵥ y₂))) *
      star (G.M'.vac v (x ∘ Sum.inr + x₂))) * l1 + (B.ψ (⅟(2 : AF F) * s₁) * G.M'.vac v (x ∘ Sum.inl)) * l2
  rw [← e]
  exact key

end GlobalTheory.DblVacLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumTwistedVacuumConditionDoubledLatticStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledVacuum_twistedVacuumCondition_doubledLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))), IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) G.M'.co dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) (G.M'.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • (G.M'.vac v))) →
    (∀ w₁ ∈ latAtV G.V' G.W v, ∀ w₂ ∈ latAtV G.V' G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ w₂)) (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)))
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))
          (Matrix.fromCols w₁ w₂) (Matrix.fromCols w₁ w₂)) • (boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x))))) := by
  first | exact @GlobalTheory.DblVacLine.dbl_vac_acts | exact GlobalTheory.DblVacLine.dbl_vac_acts | (intros; apply GlobalTheory.DblVacLine.dbl_vac_acts <;> assumption)
end
end
