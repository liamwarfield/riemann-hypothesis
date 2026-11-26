module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionLineOperatorSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalGridNodeType
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOMemLatOOfHat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkGeneratedCuspFormsOfType
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.CuspGKForms

open Matrix Filter Topology GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes GlobalTheory.CuspGK
open Formalism.IndefR.Mult

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem exists_sigOK (V : HSp D) : ∃ s, (GlobalTheory.SmoothAutCheck.reSig V s).SigOK := by
  have h : ∀ ρ : D.host.E →+* ℂ, ∃ pq : ℕ × ℕ, Formalism.UG.HasSignature (V.gram.map ρ) pq.1 pq.2 := fun ρ => by
    have hd : IsUnit (V.gram.map ρ).det := by
      have : (V.gram.map ρ).det = ρ V.gram.det := (RingHom.map_det _ _).symm
      rw [this, isUnit_iff_ne_zero]
      exact (map_ne_zero _).2 (GlobalTheory.SmoothAutCheck.gram_det_ne V)
    have hh : Formalism.UG.IsHerm (starRingEnd ℂ) (V.gram.map ρ) := by
      ext i j
      have hcm := D.host.isCMField_hostE
      have h1 : star (V.hT (V.frame j) (V.frame i)) = V.hT (V.frame i) (V.frame j) := V.herm.eq _ _
      simp only [Formalism.UG.cT, transpose_apply, map_apply, HSpace.gram]
      rw [← h1]
      exact (NumberField.IsCMField.complexEmbedding_complexConj _ ρ _).symm
    obtain ⟨p, q, h⟩ := Formalism.UG.P.signature_exists _ _ hh hd
    exact ⟨(p, q), h⟩
  choose s hs using h
  exact ⟨s, hs⟩

theorem goodPar_of_isTypeAt (hV : V.SigOK) {τ : D.what₂.Tau} {S : SPar} {φ : GA D V → ℂ} (h : IsTypeAt θ V τ S φ) :
    GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 S := by
  obtain ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, -⟩ := h
  obtain ⟨e1, e2⟩ := GlobalTheory.TypeAtCompare.card_eq_of_congr hP hJ (hV (tauE D τ))
  exact ⟨lam, ε, hE, GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS hE.1 hD, e1, e2⟩

theorem isTypeAt_rTr_same (hθ : IsInfFam θ) {τ : D.what₂.Tau} {S : SPar} {φ : GA D V → ℂ} (h : IsTypeAt θ V τ S φ)
    {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    IsTypeAt θ V τ S (rTr V (atTau θ V τ k) φ) := by
  obtain ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, h⟩ := h
  refine ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, fun x => ?_⟩
  have hσ := hD.2.2.1
  have hG : IsUnit (gramAt D V τ) := (isUnit_iff_isUnit_det _).2 (GlobalTheory.SmoothAutCheck.gramAt_unit V τ)
  have hk' : kᴴ * gramAt D V τ * k = gramAt D V τ := hk
  have hku : IsUnit k := by
    have := congrArg Matrix.det hk'
    rw [det_mul] at this
    rw [isUnit_iff_isUnit_det]
    exact isUnit_of_mul_isUnit_right (this ▸ GlobalTheory.SmoothAutCheck.gramAt_unit V τ)
  have a1 : k * k⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hku)
  have a2 : k⁻¹ * k = 1 := Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hku)
  have b2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).1 hP)
  have hki : k⁻¹ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    show (k⁻¹)ᴴ * gramAt D V τ * k⁻¹ = gramAt D V τ
    calc (k⁻¹)ᴴ * gramAt D V τ * k⁻¹ = (k⁻¹)ᴴ * (kᴴ * gramAt D V τ * k) * k⁻¹ := by rw [hk']
      _ = (k * k⁻¹)ᴴ * gramAt D V τ * (k * k⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [a1]; simp
  have hm := GlobalTheory.TypeAtCompare.conj_mem hP hJ hk
  have t0 : HasTypeAll (lieOf (gramAt D V τ)) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (fun g => σ (P * g * P⁻¹))
      fun g => φ (x * atTau θ V τ k * atTau θ V τ g) := hasTypeAll_iff.2 (h (x * atTau θ V τ k))
  have t1 := hasTypeAll_transport _ H H (fun g => σ (P * g * P⁻¹)) (fun g => σ (P * g * P⁻¹)) _ _ k hG hku hk'
    (opEquiv hσ hm) (fun g hg v => by
      have m1 := GlobalTheory.TypeAtCompare.conj_mem hP hJ hg
      have m2 := GlobalTheory.TypeAtCompare.conj_mem hP hJ (mul_mem_UH (mul_mem_UH hk hg) hki)
      show σ (P * k * P⁻¹) (σ (P * g * P⁻¹) v) = σ (P * (k * g * k⁻¹) * P⁻¹) (σ (P * k * P⁻¹) v)
      rw [← sigma_mul hσ hm m1, ← sigma_mul hσ m2 hm]
      congr 2
      calc P * k * P⁻¹ * (P * g * P⁻¹) = P * k * (P⁻¹ * P) * g * (k⁻¹ * k) * P⁻¹ := by
            rw [a2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = P * k * g * k⁻¹ * (P⁻¹ * P) * k * P⁻¹ := by rw [b2]; simp only [Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
        _ = _ := by simp only [Matrix.mul_assoc]) _ t0
  obtain ⟨v, h1, ℓ, h2, h3, h4⟩ := hasTypeAll_iff.1 t1
  refine ⟨v, h1, ℓ, h2, h3, fun g hg => ?_⟩
  have e : x * atTau θ V τ k * atTau θ V τ (k⁻¹ * g * k) = x * atTau θ V τ g * atTau θ V τ k := by
    rw [mul_assoc x, mul_assoc x, ← atTau_mul hθ V τ hk (mul_mem_UH (mul_mem_UH hki hg) hk), ← atTau_mul hθ V τ hg hk,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, a1, Matrix.one_mul]
  have := h4 g hg
  simp only [e] at this
  exact this

theorem isTypeAt_rTr (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} {S : SPar} {φ : GA D V → ℂ} (h : IsTypeAt θ V τ' S φ)
    {k : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hk : k ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    IsTypeAt θ V τ' S (rTr V (atTau θ V τ k) φ) := by
  by_cases c : τ = τ'
  · subst c
    exact isTypeAt_rTr_same hθ h hk
  obtain ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, h⟩ := h
  refine ⟨H, _, _, σ, lam, ε, P, hE, hD, hP, hJ, fun x => ?_⟩
  obtain ⟨v, h1, ℓ, h2, h3, h4⟩ := h (x * atTau θ V τ k)
  refine ⟨v, h1, ℓ, h2, h3, fun g hg => ?_⟩
  have := h4 g hg
  rw [mul_assoc x, GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ V τ τ' c k hk g hg, ← mul_assoc x] at this
  exact this

theorem exists_quotient_near (hθ : IsInfFam θ) {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) {φ : GA D V → ℂ} (hφ : IsAutFunSm θ V φ) {C : Set (GA D V)} (hC : IsCompact C) {δ : ℝ}
    (hδ : 0 < δ) : ∃ t : ℝ, ∀ x ∈ C,
      ‖Rder θ V τ X φ x - (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ + (-1 : ℂ) • φ)) x‖ < δ := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hc := (GlobalTheory.CuspLie.isAutFunSm_Rder hθ hX hφ).cont
  have hu := GlobalTheory.Mem.Lift.continuous_oneP hθ hX
  have h0 := GlobalTheory.Mem.Lift.oneP_zero (V := V) (τ := τ) (X := X) hθ
  have hd := GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder hφ.smooth hX)
  set ψ := Rder θ V τ X φ
  have ev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ x ∈ C, ‖ψ (x * oneP θ V τ X t) - ψ x‖ < δ / 2 := by
    refine hC.eventually_forall_of_forall_eventually fun y _ => ?_
    have cF : Continuous fun z : ℝ × GA D V => ‖ψ (z.2 * oneP θ V τ X z.1) - ψ z.2‖ :=
      ((hc.comp (continuous_snd.mul (hu.comp continuous_fst))).sub (hc.comp continuous_snd)).norm
    refine cF.continuousAt.eventually_lt continuousAt_const ?_
    simp only [h0, mul_one, sub_self, norm_zero]
    linarith
  obtain ⟨η, hη, hb⟩ := Metric.eventually_nhds_iff.1 ev
  refine ⟨η / 2, fun x hx => ?_⟩
  have hp : 0 < η / 2 := by linarith
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s : ℝ => φ (x * oneP θ V τ X s) - (s : ℂ) * ψ x)
    (f' := fun s => ψ (x * oneP θ V τ X s) - ψ x) (a := 0) (b := η / 2) (C := δ / 2)
    (fun s _ => by
      have := (hd x s).fun_sub ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (ψ x))
      simpa using this.hasDerivWithinAt)
    (fun s hs => (hb (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]; linarith [hs.2]) x hx).le)
    (η / 2) ⟨hp.le, le_rfl⟩
  set t := η / 2
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have e : ψ x - (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ + (-1 : ℂ) • φ)) x =
      -(t : ℂ)⁻¹ * ((φ (x * oneP θ V τ X t) - (t : ℂ) * ψ x) - (φ (x * oneP θ V τ X 0) - ((0 : ℝ) : ℂ) * ψ x)) := by
    simp only [h0, mul_one, Pi.smul_apply, Pi.add_apply, rTr, smul_eq_mul, Complex.ofReal_zero]
    field_simp
    ring
  rw [e, norm_mul, norm_neg, norm_inv, Complex.norm_real, Real.norm_of_nonneg hp.le, inv_mul_lt_iff₀ hp]
  refine key.trans_lt ?_
  nlinarith

section Sig

variable (hPr : GlobalTheory.FunPr.Hypotheses₂) (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} {S : SPar} {φ ψ : GA D V → ℂ}
include hPr hθ

end Sig

variable {S : D.what₂.Tau → SPar}

end GlobalTheory.CuspGKForms

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryMovesHeisenbergDerivative
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryMovesHeisenbergDerivative
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.KHeisComm

variable {F : Type} [Field F] [NumberField F]

theorem archimedean_isomorphism_split_trivial {κ : Type} (z : κ → mixedEmbedding.mixedSpace F) :
    GlobalTheory.ArchIsom.r0 F κ (GlobalTheory.ArchIsom.splitEquiv F κ (z, 0)) = 1 := by
  change GlobalTheory.ArchIsom.g0 F κ 0 = 1
  simp [GlobalTheory.ArchIsom.g0, Set.indicator_of_mem (GlobalTheory.ArchIsom.zero_mem_intPts (F := F) κ)]

theorem tens_split {κ : Type} (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (z : κ → mixedEmbedding.mixedSpace F) :
    tens (evI F) φ (GlobalTheory.ArchIsom.r0 F κ) (GlobalTheory.ArchIsom.splitEquiv F κ (z, 0)) = φ z := by
  have hz : (fun i => evI F (GlobalTheory.ArchIsom.splitEquiv F κ (z, 0) i)) = z :=
    funext fun i => GlobalTheory.ArchIsom.evI_splitEquiv κ _ i
  simp only [tens, hz, archimedean_isomorphism_split_trivial, mul_one]


open scoped Classical in
theorem proj_mem_adm {κ : Type} [Fintype κ] (x : κ → AF F) :
    (LinearMap.proj x : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (x i).2) • ((BoundedContinuousFunction.evalCLM ℂ
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

end GlobalTheory.KHeisComm


open GlobalTheory.KHeisComm in
open scoped Classical in
theorem GlobalTheory.KHeisComm.actsD_heisLine_mat_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u →
    ∀ f f₁ fk h : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f f₁ → Acts (evI F) (om (k, 1)) f fk →
      Acts (evI F) (om (k, 1)) f₁ h → ActsD (evI F) (M.heisLine B.ψ (mat k * u)) fk h := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k _ u hu f f₁ fk h hD hA hA₁
  have hψ : IsStd B.ψ := hP.base.std
  have hS := IsUWeilPair.isUSplitting hP.weil
  obtain ⟨D, hDD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) B.ψ (incM F X.J) (incM F W.J) M.co hψ
  obtain ⟨D₁, hD₁⟩ := GlobalTheory.HeisDeriv.exists_heisLine_deriv M B.ψ hψ (mat k * u)
  have hg0 := GlobalTheory.ArchIsom.standard_vector_mem_schwartz_bruhat (F := F) (Fin n × Fin d)

  have hf₁ : (D u f : SInf F (Fin n × Fin d)) = f₁ := by
    refine SchwartzMap.ext fun z => ?_
    set x := GlobalTheory.ArchIsom.splitEquiv F (Fin n × Fin d) (z, 0)
    have a1 : HasDerivAt (fun t => M.heisLine B.ψ u t (tens (evI F) (⇑f) (GlobalTheory.ArchIsom.r0 F (Fin n × Fin d))) x)
        (pureA F (⇑(D u f)) (GlobalTheory.ArchIsom.g0 F (Fin n × Fin d)) x) 0 :=
      (hDD u hu f).1 _ hg0 _ (proj_mem_adm x)
    have a2 := hD _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f) x
    have e := a1.unique a2
    rw [← GlobalTheory.ArchIsom.tensor_at_standard_point, tens_split, tens_split] at e
    exact e
  suffices e : h = D₁ fk by rw [e]; exact hD₁ fk
  refine SchwartzMap.ext fun z => ?_
  set x := GlobalTheory.ArchIsom.splitEquiv F (Fin n × Fin d) (z, 0)
  have hl := hS.adm (k, 1) _ (proj_mem_adm x)
  have b1 := (hDD u hu f).1 _ hg0 _ hl
  have hmem : ∀ g : SInf F (Fin n × Fin d), tens (evI F) (⇑g) (GlobalTheory.ArchIsom.r0 F (Fin n × Fin d)) ∈ schA F (Fin n × Fin d) :=
    fun g => (GlobalTheory.ArchIsom.restriction_at_standard_point _ g).2
  have hfun : (fun t : ℝ => ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ om (k, 1))
      (M.co.rho B.ψ (realAd F t • u) (pureA F (⇑f) (GlobalTheory.ArchIsom.g0 F (Fin n × Fin d))))) =
      fun t => M.heisLine B.ψ (mat k * u) t (tens (evI F) (⇑fk) (GlobalTheory.ArchIsom.r0 F (Fin n × Fin d))) x := by
    funext t
    rw [LinearMap.comp_apply, LinearMap.proj_apply, ← GlobalTheory.ArchIsom.tensor_at_standard_point, hS.impl (k, 1) _ _ (hmem f),
      hA _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f)]
    have hw : actAB (cA σ) ((k, 1) : UA σ X.J × UA σ W.J) (realAd F t • u) = realAd F t • (mat k * u) := by
      simp only [actAB, mat, OneMemClass.coe_one, Units.val_one, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_smul]
    rw [hw]
    rfl
  have hval : ((LinearMap.proj x : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ om (k, 1))
      (pureA F (⇑(D u f)) (GlobalTheory.ArchIsom.g0 F (Fin n × Fin d))) = h z := by
    rw [LinearMap.comp_apply, LinearMap.proj_apply, hf₁, ← GlobalTheory.ArchIsom.tensor_at_standard_point, hA₁ _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f₁),
      tens_split]
  dsimp only at b1
  rw (config := { transparency := .all }) [hfun, hval] at b1
  have b2 := hD₁ fk _ (GlobalTheory.ArchIsom.restriction_at_standard_point _ fk) x
  rw [tens_split] at b2
  exact b1.unique b2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryMovesHeisenbergDerivativeStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactUnitary_moves_heisenbergDerivative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ∀ f f₁ fk h : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine B.ψ u) f f₁ → Acts (evI F) (om (k, 1)) f fk →
      Acts (evI F) (om (k, 1)) f₁ h → ActsD (evI F) (M.heisLine B.ψ (mat k * u)) fk h := by
  first | exact @GlobalTheory.KHeisComm.actsD_heisLine_mat_mul | exact GlobalTheory.KHeisComm.actsD_heisLine_mat_mul | (intros; apply GlobalTheory.KHeisComm.actsD_heisLine_mat_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergLineDerivativeFiniteSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergLineDerivativeFiniteSpan
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ArchUniq
open scoped SchwartzMap Classical

noncomputable section

namespace GlobalTheory.HeisDerivSpan

open GlobalTheory.HeisDeriv

variable {F : Type} [Field F] [NumberField F]

def trPairL {κ : Type} [Fintype κ] (z : κ → mixedEmbedding.mixedSpace F) :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).comp
    (∑ i, (LinearMap.mulLeft ℝ (z i)).comp (LinearMap.proj i))

theorem trPairL_apply {κ : Type} [Fintype κ] (z w : κ → mixedEmbedding.mixedSpace F) :
    trPairL z w = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, z i * w i) := by
  simp [trPairL, LinearMap.sum_apply]

theorem fderiv_basis {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (f : SInf F κ)
    (z v : κ → mixedEmbedding.mixedSpace F) :
    fderiv ℝ (⇑f) z v = ∑ j, (b.repr v j : ℂ) * fderiv ℝ (⇑f) z (b j) := by
  calc fderiv ℝ (⇑f) z v = fderiv ℝ (⇑f) z (∑ j, b.repr v j • b j) := by rw [b.sum_repr]
    _ = _ := by rw [map_sum]; simp only [map_smul, Complex.real_smul]

theorem mult_basis {κ : Type} [Fintype κ] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℝ (κ → mixedEmbedding.mixedSpace F)) (y : κ → AF F)
    (z : κ → mixedEmbedding.mixedSpace F) :
    mult F y z = ∑ j, (b.repr (fun i => evI F (y i)) j : ℂ) * mult F (liftV (b j)) z := by
  have h1 : ∀ w : κ → AF F, trForm F w z = trPairL z (fun i => evI F (w i)) := by
    intro w
    rw [trForm_apply, trPairL_apply]
  have h2 : trPairL z (fun i => evI F (y i)) =
      ∑ j, b.repr (fun i => evI F (y i)) j * trPairL z (b j) := by
    calc trPairL z (fun i => evI F (y i))
        = trPairL z (∑ j, b.repr (fun i => evI F (y i)) j • b j) := by rw [b.sum_repr]
      _ = _ := by rw [map_sum]; simp only [map_smul, smul_eq_mul]
  have h3 : ∀ j, (fun i => evI F (liftV (F := F) (b j) i)) = b j := fun j => Coord.loc_lift (b j)
  simp only [mult_apply, h1, h3, h2]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.HeisDerivSpan

namespace GlobalTheory.HeisDerivSpan

open GlobalTheory.HeisDeriv GlobalTheory.HeisDerivArch

variable {F : Type} [Field F] [NumberField F]

theorem actsD_heisLine_eq {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (f g : SInf F (Fin n × Fin d))
    (hg : ActsD (evI F) (M.heisLine ψ u) f g) :
    g = heisD F (fun i => evI F ((M.co.e u).1 i)) (M.co.e u).2 f := by
  ext y
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) (Fin n × Fin d)
  have hr := hR f
  set x : Fin n × Fin d → AF F := liftV y with hx
  have hd1 := hg R hr x
  have hd2 := actsD_heisLine_heisD M ψ hψ u f R hr x
  have huniq := hd1.unique hd2
  have hRx : R x = R 0 := by
    have := hr.1 0 x (at_liftV y)
    rwa [zero_add] at this
  have hlx : (fun i => evI F (x i)) = y := Coord.loc_lift y
  simp only [tens, hlx, hRx] at huniq
  exact mul_right_cancel₀ hR0 huniq

theorem heisLine_deriv_finite_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∃ (m : ℕ) (L : Fin m → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)),
      ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = D f) ∧
        ∀ f, D f ∈ Submodule.span ℂ (Set.range fun i => L i f) := by
  intro F E _ _ _ _ _ σ n d X W M ψ hψ
  let b := Module.finBasis ℝ (Fin n × Fin d → mixedEmbedding.mixedSpace F)
  set N := Module.finrank ℝ (Fin n × Fin d → mixedEmbedding.mixedSpace F)
  let A : Fin N → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun j =>
    (LineDeriv.lineDerivOpCLM ℂ (SInf F (Fin n × Fin d)) (b j)).toLinearMap
  let B : Fin N → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun j =>
    (SchwartzMap.smulLeftCLM ℂ (⇑(mult F (liftV (b j))))).toLinearMap
  refine ⟨N + N, fun i => Sum.elim A B (finSumFinEquiv.symm i), fun u _ => ?_⟩
  refine ⟨heisD F (fun i => evI F ((M.co.e u).1 i)) (M.co.e u).2, fun f f₁ =>
    ⟨actsD_heisLine_eq M ψ hψ u f f₁, fun h => by subst h; exact actsD_heisLine_heisD M ψ hψ u f⟩, fun f => ?_⟩
  set S := Submodule.span ℂ (Set.range fun i => Sum.elim A B (finSumFinEquiv.symm i) f) with hS
  have hA : ∀ j, A j f ∈ S := fun j => Submodule.subset_span ⟨finSumFinEquiv (Sum.inl j), by simp only [Equiv.symm_apply_apply, Sum.elim_inl]⟩
  have hB : ∀ j, B j f ∈ S := fun j => Submodule.subset_span ⟨finSumFinEquiv (Sum.inr j), by simp only [Equiv.symm_apply_apply, Sum.elim_inr]⟩
  set v : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).1 i) with hv
  set y := (M.co.e u).2 with hy
  have key : heisD F v y f = ∑ j, (b.repr v j : ℂ) • A j f +
      ∑ j, (b.repr (fun i => evI F (y i)) j : ℂ) • B j f := by
    ext z
    rw [heisD_apply, fderiv_basis b f z v, mult_basis b y z, Finset.sum_mul]
    simp only [SchwartzMap.add_apply, SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul, A, B,
      ContinuousLinearMap.coe_coe, SchwartzMap.lineDerivOp_apply_eq_fderiv]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [SchwartzMap.smulLeftCLM_apply_apply (mult F (liftV (F := F) (b j))).hasTemperateGrowth]
    simp only [smul_eq_mul]
    ring
  rw [key]
  exact add_mem (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hA j))
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hB j))

end GlobalTheory.HeisDerivSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergLineDerivativeFiniteSpanStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergLine_derivative_finite_span : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∃ (m : ℕ) (L : Fin m → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)),
      ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → ∃ D : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = D f) ∧
        ∀ f, D f ∈ Submodule.span ℂ (Set.range fun i => L i f) := by
  first | exact @GlobalTheory.HeisDerivSpan.heisLine_deriv_finite_span | exact GlobalTheory.HeisDerivSpan.heisLine_deriv_finite_span | (intros; apply GlobalTheory.HeisDerivSpan.heisLine_deriv_finite_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EdgeFactorNeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FirstRowTermLaw

open GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Grid

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Γ : Grid k}

theorem mulSingle_ne {m : ℕ} (κ : GL (Fin (Γ.rank (0, m))) k) {X : ℕ × ℕ} (h : X ≠ (0, m)) :
    (Pi.mulSingle (0, m) κ : Γ.VertexGroup) X = 1 := Pi.mulSingle_eq_of_ne h _

theorem moveArgs_fill (hs : 1 ≤ Γ.s) (hm : Γ.m ≠ 0) (κ : GL (Fin (Γ.rank (0, Γ.m))) k) (x : ColArgs Γ) (y : RowArgs Γ)
    (e : Vars Γ) :
    Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) (fill hs x y e) = fill hs x (Function.update y 0 ((κ⁻¹).val * y 0)) e := by
  funext b
  cases b with
  | theta i j =>
    by_cases h : i = Γ.m
    · subst h
      rw [moveArgs, mulSingle_ne κ (by simp [Edge.tgt, hm]), mulSingle_ne κ (by simp [Edge.src, hm])]
      simp [fill]
    · simp [moveArgs, fill, h]
  | ex i j =>
    by_cases hj : j = Γ.m
    · subst hj
      by_cases hi : i = 0
      · subst hi
        rw [moveArgs, mulSingle_ne κ (by simp [Edge.tgt]), fill_ex, fill_ex]
        simp only [Edge.src, Pi.mulSingle_eq_same, Function.update_self, map_one, inv_one, Units.val_one, Matrix.one_mul]
        rw [Matrix.transpose_mul, Assignment.read, invT_val]
      · rw [moveArgs, mulSingle_ne κ (by simp [Edge.tgt]), mulSingle_ne κ (by simp [Edge.src, hi])]
        simp [fill, Function.update_of_ne hi]
    · simp [moveArgs, fill, hj]

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

open GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Grid MeasureTheory

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Γ : Grid k}

theorem moveArgs_mul (s : Assignment) (g g' : Γ.VertexGroup) (z : Γ.Args) :
    Γ.moveArgs s (g * g') z = Γ.moveArgs s g' (Γ.moveArgs s g z) := by
  funext b
  simp only [moveArgs, Pi.mul_apply, map_mul, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem mulSingle_comm (κ : GL (Fin (Γ.rank (0, Γ.m))) k) (g : Γ.VertexGroup) (hg : g (0, Γ.m) = 1) :
    Pi.mulSingle (0, Γ.m) κ * g = g * Pi.mulSingle (0, Γ.m) κ := by
  funext X
  by_cases h : X = (0, Γ.m)
  · subst h; simp [hg]
  · simp [Pi.mulSingle_eq_of_ne h]

theorem elt_zero_m (hs : 1 ≤ Γ.s) (hm : Γ.m ≠ 0) {J : Γ.Level} (ρ : Reps hs J) (β : Cosets hs J) : ρ.elt β (0, Γ.m) = 1 := by
  simp [Reps.elt, onColumn, Ne.symm hm]

theorem prod_edgeFactor (hm : Γ.m ≠ 0) (κ : GL (Fin (Γ.rank (0, Γ.m))) k) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod =
      Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ) (.ex 0 Γ.m) := by
  have h1 : ∀ b : Edge, b.src ≠ (0, Γ.m) → b.tgt ≠ (0, Γ.m) → Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ) b = 1 := by
    intro b hs ht
    simp [edgeFactor, Pi.mulSingle_eq_of_ne hs, Pi.mulSingle_eq_of_ne ht]
  obtain ⟨n, hn⟩ : ∃ n, Γ.m = n + 1 := ⟨Γ.m - 1, by omega⟩
  rw [oppositePath, List.map_append, List.prod_append]
  have h2 : (((List.range Γ.m).reverse.map (Edge.theta Γ.m)).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod = 1 := by
    refine List.prod_eq_one fun a ha => ?_
    simp only [List.map_map, List.mem_map, Function.comp_apply] at ha
    obtain ⟨j, -, rfl⟩ := ha
    exact h1 _ (by simp [Edge.src, hm]) (by simp [Edge.tgt, hm])
  rw [h2, mul_one]
  have h3 : List.range Γ.m = 0 :: (List.range n).map Nat.succ := by rw [hn, List.range_succ_eq_map]
  rw [h3, List.map_cons, List.map_cons, List.prod_cons]
  have h4 : ((((List.range n).map Nat.succ).map (Edge.ex · Γ.m)).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod = 1 := by
    refine List.prod_eq_one fun a ha => ?_
    simp only [List.map_map, List.mem_map, Function.comp_apply] at ha
    obtain ⟨j, -, rfl⟩ := ha
    exact h1 _ (by simp [Edge.src]) (by simp [Edge.tgt])
  rw [h4, mul_one]

variable [MeasurableSpace k] [BorelSpace k]

theorem moved_law (keep : Bool) (g : Γ.VertexGroup) (hg : g (0, Γ.m) = 1) (κ : GL (Fin (Γ.rank (0, Γ.m))) k)
    (T : Γ.Args → ℂ) (c : ℂ) (hlaw : Γ.pathAct .one (oppositePath Γ.m) (Pi.mulSingle (0, Γ.m) κ) T = c • T) (z : Γ.Args) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod *
      moved Γ keep g T (Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) z) = c * moved Γ keep g T z := by
  have h1 := congrFun hlaw (Γ.moveArgs .one g z)
  simp only [pathAct, Pi.smul_apply, smul_eq_mul] at h1
  have h2 : Γ.moveArgs .one g (Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) z) =
      Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) (Γ.moveArgs .one g z) := by
    rw [← moveArgs_mul, ← moveArgs_mul, mulSingle_comm κ g hg]
  simp only [moved, pathAct, h2]
  calc _ = (if keep then (1 : ℂ) else (((charFactor Γ g)⁻¹ : ℂˣ) : ℂ)) * ((oppositePath Γ.m).map (Γ.edgeFactor .one g)).prod *
        (((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod *
          T (Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) (Γ.moveArgs .one g z))) := by ring
    _ = _ := by rw [h1]; ring

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

open GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Grid MeasureTheory

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Γ : Grid k}
  [MeasurableSpace k] [BorelSpace k]

theorem datum_law (hs : 1 ≤ Γ.s) (hm : Γ.m ≠ 0) (ψ : AddChar k Circle) (ν : Measure k) {J : Γ.Level} (keep : Bool)
    (ρ : Reps hs J) (T : Γ.Args → ℂ) (β : Cosets hs J) (κ : GL (Fin (Γ.rank (0, Γ.m))) k) (c : ℂ)
    (hlaw : Γ.pathAct .one (oppositePath Γ.m) (Pi.mulSingle (0, Γ.m) κ) T = c • T) (x : ColArgs Γ) (y : RowArgs Γ) :
    Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ) (.ex 0 Γ.m) *
        (unfTerm ψ ν keep ρ T β).datum x (Function.update y 0 ((κ⁻¹).val * y 0)) =
      c * (unfTerm ψ ν keep ρ T β).datum x y := by
  simp only [unfTerm, flatTensor, flatIntegrand, ← moveArgs_fill hs hm κ x y]
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  have h := moved_law keep (ρ.elt β) (elt_zero_m hs hm ρ β) κ T c hlaw (fill hs x y e)
  rw [prod_edgeFactor hm] at h
  simp only
  rw [← mul_assoc, h, mul_assoc]

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def kapAt (S : GridChoice W U) (t : T) (w : Pl D.host.E) (k : FinPt G (.grid 0 D.R.m)) :
    GL (Fin ((locGrid G t w).rank (0, D.R.m))) (Kw w) :=
  inBasis (rank_vertex G t w (X := (0, D.R.m)) ⟨Nat.zero_le _, le_rfl⟩) (S.B.β 0 D.R.m) w (finG (G.V (.grid 0 D.R.m)) k)

theorem edgeFactor_ne_zero {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Γ : GlobalTheory.SplitFlip.Grid k) (g : Γ.VertexGroup) (b : GlobalTheory.SplitFlip.Edge) : Γ.edgeFactor .one g b ≠ 0 := by
  simp only [GlobalTheory.SplitFlip.Grid.edgeFactor]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (GlobalTheory.SplitFlip.apow_ne_zero _ _))
    (GlobalTheory.SplitFlip.apow_ne_zero _ _)

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

theorem prod_update_comp {m : ℕ} {X : Fin m → Type} (F : ∀ i, X i → ℂ) (i₀ : Fin m) (f : X i₀ → X i₀) (ys : ∀ i, X i) :
    ∏ i, Function.update F i₀ (fun y => F i₀ (f y)) i (ys i) = ∏ i, F i (Function.update ys i₀ (f (ys i₀)) i) := by
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : i = i₀
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem sum_update_comp {κ : Type} {m n : ℕ} {X : Fin n → Type} {Y : Fin m → Type} (τ : κ →₀ ℂ) (A : κ → ∀ j, X j → ℂ)
    (B : κ → ∀ i, Y i → ℂ) (i₀ : Fin m) (f : Y i₀ → Y i₀) (xs : ∀ j, X j) (ys : ∀ i, Y i) :
    (τ.sum fun d a' => a' * (∏ j, A d j (xs j)) * ∏ i, Function.update (B d) i₀ (fun y => B d i₀ (f y)) i (ys i)) =
      τ.sum fun d a' => a' * (∏ j, A d j (xs j)) * ∏ i, B d i (Function.update ys i₀ (f (ys i₀)) i) :=
  Finset.sum_congr rfl fun d _ => by beta_reduce; rw [prod_update_comp]

theorem key_cancel (s PE PL P P' : ℂ) (h1 : PE ≠ 0) (h2 : s * PL = PE) (h3 : PE * P' = PL * P) : s * P' = P :=
  mul_left_cancel₀ h1 (by linear_combination s * h3 + P * h2)

end GlobalTheory.FirstRowTermLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanLineIntertwinesRealSchrodinger
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanLineIntertwinesRealSchrodinger
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

noncomputable section

namespace GlobalTheory.ArchFam

open scoped Matrix

variable {F : Type} [Field F] [NumberField F]

theorem at_liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) : At (evI F) (liftV y) := by
  intro u hu
  have h : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hu
  funext i
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h, zero_mul]
  · change u.2 * 0 = 0
    exact mul_zero _

theorem rho_tens (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {W' : Type} [AddCommGroup W'] [Module (AF F) W']
    {Bf : W' → W' → AF F} {κ : Type} [Fintype κ] (dc : Darboux Bf κ) (w : W') (hw : At (evI F) w)
    (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (r : (κ → AF F) → ℂ)
    (hr : ∀ x z, At (evI F) z → r (x + z) = r x) :
    dc.rho ψ w (tens (evI F) φ r) =
      tens (evI F) (schrF (trP F κ) (locV (dc.e w).1, locV (dc.e w).2) φ) r := by
  have hab : ∀ u : AF F, evI F u = 0 → u • dc.e w = 0 := fun u hu => by
    rw [← map_smul, hw u hu, map_zero]
  have ha : At (evI F) (dc.e w).1 := fun u hu => congrArg Prod.fst (hab u hu)
  have hb : At (evI F) (dc.e w).2 := fun u hu => congrArg Prod.snd (hab u hu)
  funext x
  have ht : At (evI F) (x ⬝ᵥ (dc.e w).2 + ⅟(2 : AF F) * (dc.e w).1 ⬝ᵥ (dc.e w).2) := fun u hu => by
    have h : ∀ y : κ → AF F, u * (y ⬝ᵥ (dc.e w).2) = 0 := fun y => by
      rw [← smul_eq_mul, ← dotProduct_smul, hb u hu, dotProduct_zero]
    rw [smul_eq_mul, mul_add, h, mul_left_comm, h, mul_zero, add_zero]
  have hloc : (fun i => evI F ((x + (dc.e w).1) i)) = locV x + locV (dc.e w).1 := by
    funext i
    simp only [Pi.add_apply, locV, evI_eq_evIHom, map_add (f := _)]
  simp only [Darboux.rho, schr, tens]
  rw [hψ.2.2 _ ht, trace_evI_heis, hr x _ ha, hloc, schrF]
  exact (mul_assoc _ _ _).symm

theorem tens_inj {κ : Type} (r : (κ → AF F) → ℂ) (hr : ∀ x z, At (evI F) z → r (x + z) = r x)
    (x₀ : κ → AF F) (h0 : r x₀ ≠ 0) (φ₁ φ₂ : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (h : tens (evI F) φ₁ r = tens (evI F) φ₂ r) : φ₁ = φ₂ := by
  funext y
  have hz : At (evI F) (liftV (y - locV x₀)) := at_liftV _
  have hx := congrFun h (x₀ + liftV (y - locV x₀))
  simp only [tens] at hx
  have hl : (fun i => evI F ((x₀ + liftV (y - locV x₀)) i)) = y := by
    change locV (x₀ + liftV (y - locV x₀)) = y
    rw [Coord.loc_add, Coord.loc_lift]
    abel
  rw [hl, hr _ _ hz] at hx
  exact mul_right_cancel₀ h0 hx

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def wv (M : Model σ X W)
    (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  M.co.e.symm (liftV v.1, liftV v.2)

theorem at_wv (M : Model σ X W)
    (v : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    At (evI F) (wv M v) := by
  intro u hu
  rw [wv, ← map_smul, Prod.smul_mk, at_liftV v.1 u hu, at_liftV v.2 u hu, Prod.mk_zero_zero, map_zero]

theorem at_mul {w : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hw : At (evI F) w) (m : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    At (evI F) (w * m) := by
  intro u hu
  rw [← Matrix.smul_mul, hw u hu, Matrix.zero_mul]

def amap (M : Model σ X W) (m : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) where
  toFun v := Coord.coordI M (wv M v * m)
  map_add' v v' := by
    simp only [wv, Prod.fst_add, Prod.snd_add, Coord.lift_add, ← Prod.mk_add_mk, map_add (f := _), Matrix.add_mul,
      Coord.coordI_add]
  map_smul' c v := by
    simp only [wv, Prod.smul_fst, Prod.smul_snd, Coord.lift_smul, ← Prod.smul_mk, map_smul, Matrix.smul_mul,
      Coord.coordI_smul, RingHom.id_apply]

end GlobalTheory.ArchFam

namespace GlobalTheory.ArchFam

open scoped Matrix


open GlobalTheory.ArchUniq.Coord in
theorem schr_equiv : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    ∃ A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      (∀ v, Continuous fun t => A t v) ∧
      ∀ t v (f f₁ : SInf F (Fin n × Fin d)), ⇑f₁ = schrF (trP F (Fin n × Fin d)) v ⇑f →
        ⇑(T t f₁) = schrF (trP F (Fin n × Fin d)) (A t v) ⇑(T t f) := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hψ hW γ hγ T hT
  refine ⟨fun t => amap M (mat (γ (Multiplicative.ofAdd t)))ᵀ, fun v => ?_, fun t v f f₁ hf => ?_⟩
  · haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
    haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
    haveI : IsModuleTopology (AF F) (Matrix (Fin n) (Fin d) (AE F E)) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
    have hm : Continuous fun t : ℝ => (mat (γ (Multiplicative.ofAdd t)))ᵀ :=
      ((Units.continuous_val.comp continuous_subtype_val).comp (hγ.1.comp continuous_ofAdd)).matrix_transpose
    have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
    have hev : Continuous (evI F) := by
      change Continuous fun a : AF F => InfiniteAdeleRing.ringEquiv_mixedSpace F a.1
      refine Continuous.comp ?_ continuous_fst
      change Continuous fun x : InfiniteAdeleRing F =>
        ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
         (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
      refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
      · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
      · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)
    have hl : Continuous (locV : (Fin n × Fin d → AF F) → _) := continuous_pi fun i => hev.comp (continuous_apply i)
    show Continuous fun t => (locV (M.co.e (wv M v * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1,
      locV (M.co.e (wv M v * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2)
    exact ((hl.comp continuous_fst).prodMk (hl.comp continuous_snd)).comp (he.comp (continuous_const.matrix_mul hm))
  · obtain ⟨r₀, hr₀, hinj⟩ := GlobalTheory.T.exists_admissible_finiteFactor_archimedeanSchwartz (F := F) (Fin n × Fin d)
    have hrr := (hr₀ 0).1
    by_cases hz : ∀ x, r₀ x = 0
    · have h0 : ∀ g : SInf F (Fin n × Fin d), g = 0 := fun g => hinj g 0 (by funext x; simp [tens, hz])
      rw [h0 (T t f₁), h0 (T t f)]
      funext y
      simp [schrF]
    simp only [not_forall] at hz
    obtain ⟨x₀, hx₀⟩ := hz
    have hs := hW.isUSplitting
    have hc : (locV (M.co.e (wv M v)).1, locV (M.co.e (wv M v)).2) = v := coordI_lift M v
    have e1 : tens (evI F) ⇑f₁ r₀ = M.co.rho ψ (wv M v) (tens (evI F) ⇑f r₀) := by
      rw [rho_tens ψ hψ M.co _ (at_wv M v) _ _ hrr, hc, ← hf]
    have e2 : om (1, γ (Multiplicative.ofAdd t)) (M.co.rho ψ (wv M v) (tens (evI F) ⇑f r₀)) =
        M.co.rho ψ (wv M v * (mat (γ (Multiplicative.ofAdd t)))ᵀ)
          (om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f r₀)) := by
      rw [hs.impl (1, γ (Multiplicative.ofAdd t)) (wv M v) _ (hr₀ f).2]
      congr 2
      simp only [actAB, mat, OneMemClass.coe_one, Units.val_one, Matrix.one_mul]
    have e3 := hT t f r₀ (hr₀ f)
    have e4 := hT t f₁ r₀ (hr₀ f₁)
    apply tens_inj r₀ hrr x₀ hx₀
    rw [← e4, e1, e2, e3, rho_tens ψ hψ M.co _ (at_mul (at_wv M v) _) _ _ hrr]
    rfl

end GlobalTheory.ArchFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanLineIntertwinesRealSchrodingerStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanLine_intertwines_realSchrodinger : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    ∃ A : ℝ → ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      (∀ v, Continuous fun t => A t v) ∧
      ∀ t v (f f₁ : SInf F (Fin n × Fin d)), ⇑f₁ = schrF (trP F (Fin n × Fin d)) v ⇑f →
        ⇑(T t f₁) = schrF (trP F (Fin n × Fin d)) (A t v) ⇑(T t f) := by
  first | exact @GlobalTheory.ArchFam.schr_equiv | exact GlobalTheory.ArchFam.schr_equiv | (intros; apply GlobalTheory.ArchFam.schr_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitDoublingTMatrixMulInverseEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitDoublingTMatrixMulInverseEqOne
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.SplitDblGen

theorem tMat_mul_tMat_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (K K' : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    K * K' = 1 → (c * c) • (K - 1) = K - 1 →
    GlobalTheory.SplitDblGen.tMat c K * GlobalTheory.SplitDblGen.tMat c K' = 1 := by
  intro F E _ _ _ _ _ d c K K' hKK hc
  have h2 : (half : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) * 2 = 1 := by
    unfold half
    rw [show (2 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) 2 from (map_ofNat _ 2).symm, ← map_mul, invOf_mul_self, map_one]
  have hP : (c * c) • ((K - 1) * (K' - 1)) = (K - 1) * (K' - 1) := by rw [← smul_mul_assoc, hc]
  have hsum : (K - 1) + (K' - 1) + (K - 1) * (K' - 1) = 0 := by
    rw [sub_mul, mul_sub, mul_sub, hKK]; noncomm_ring
  have hff : ((half * (1 + c)) * (half * (1 + c))) • ((K - 1) * (K' - 1))
      = (half * (1 + c)) • ((K - 1) * (K' - 1)) := by
    rw [show (half * (1 + c)) * (half * (1 + c)) = half * half * (1 + 2 * c) + half * half * (c * c) by ring,
      add_smul, ← smul_smul (half * half) (c * c), hP, ← add_smul]
    congr 1
    linear_combination (half * (1 + c)) * h2
  unfold tMat
  generalize half * (1 + c) = f at hff ⊢
  have e : (1 + f • (K - 1)) * (1 + f • (K' - 1))
      = 1 + f • ((K - 1) + (K' - 1)) + (f * f) • ((K - 1) * (K' - 1)) := by
    rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, smul_add]; abel
  rw [e, hff, add_assoc, ← smul_add, hsum, smul_zero, add_zero]

end GlobalTheory.SplitDblGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitDoublingTMatrixMulInverseEqOneStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (K K' : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    K * K' = 1 → (c * c) • (K - 1) = K - 1 →
    GlobalTheory.SplitDblGen.tMat c K * GlobalTheory.SplitDblGen.tMat c K' = 1 := by
  first | exact @GlobalTheory.SplitDblGen.tMat_mul_tMat_eq_one | exact GlobalTheory.SplitDblGen.tMat_mul_tMat_eq_one | (intros; apply GlobalTheory.SplitDblGen.tMat_mul_tMat_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SquareNuHeckeCharacterNotUnramifiedAtChosenPlace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri FieldCond)

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem squareNuHeckeCharacter_not_unramified_at_chosenPlace {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) :
    ¬ (SqNum.nuH G t i j).UnrAt (G.pl.w G.pl.v0) := by
  intro hnu

  have hunder : (G.pl.w G.pl.v0).under (𝓞 D.host.F) = G.pl.v0 :=
    G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  have hnotS1 : G.pl.v0 ∉ S1 D := G.ch.basePlace_not_mem_chiGridBadPlaces

  have hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q t →
      (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ (G.pl.w G.pl.v0).under (𝓞 D.host.F) := by
    intro PP hPP
    rw [hunder]
    rcases hPP with hP | hP
    · intro heq
      apply hnotS1
      obtain ⟨k, hk⟩ := (hL.Pg PP).1 hP
      have hmem := GlobalTheory.LevelPlaces.mem_of_div L.C.P k PP hk
      have hF : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
        simpa using hmem
      rw [← heq, S1_mem_OmF]
      fin_cases k
      · exact Or.inl hF
      · exact Or.inr (Or.inl hF)
    · exact G.pl.levelPlace_ne_basePlace t PP hP
  obtain ⟨hxi, hmu⟩ := (GlobalTheory.levCh_unramified_places D T L μ₀ hL t).2.2.2 _ hoff

  have hchi := (G.ch.lev0 (D.R.m - i) (by omega) (by omega) _ hunder).2
  apply hchi
  intro x hx
  have h := hnu x hx
  change (L.C.mu0 j * L.xiH t / G.ch.chiH (D.R.m - i)).loc (G.pl.w G.pl.v0) x = 1 at h
  change (L.C.mu0 j).loc (G.pl.w G.pl.v0) x * (L.xiH t).loc (G.pl.w G.pl.v0) x * ((G.ch.chiH (D.R.m - i)).loc (G.pl.w G.pl.v0) x)⁻¹ = 1 at h
  rw [hmu j x hx, hxi x hx, one_mul, one_mul] at h
  exact inv_eq_one.mp h

end GlobalTheory.RowTest

end
end
