module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.LeviBlockInduction.GxBlock
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.LeviBlockInduction.GxLevi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.CoefInd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalZetaIntegralLaurentExpansion
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalZetaIntegralShellMean
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ExpAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.SideCenOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.CoefSm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.SideOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterCentralExponentProperties
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ExistsPullback
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.Regroup
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.ContDiffFderivApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.HasDerivAtProdLog
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.TestEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ArchimedeanDerivatives.HasFDerivAtExpF
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.PairGOps

@[expose] public section

attribute [-instance] GlobalTheory.CompanionTheory.QL.instMeasGL

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.LeviBlockInduction.GxSupp
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
open GroundTheory.Automorphic.GLnLocal (integralGL mem_integralGL_iff)
open GroundTheory.Automorphic.Parabolic (levi parabolicInd mem_levi leviUnipotent)
open GroundTheory.Automorphic.GodementJacquet (centralUnif coe_centralUnif)
open scoped Classical

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem mem_int_one (g : GL (Fin 1) k) :
    g ∈ integralGL k 1 ↔ valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 := by
  have h1 : ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = g 0 0 := by simp [Matrix.det_unique]
  have h2 : (g⁻¹ : GL (Fin 1) k) 0 0 * g 0 0 = 1 := by
    have := congrFun (congrFun g.inv_mul 0) 0
    simpa [Matrix.mul_apply] using this
  have h3 := congrArg (valuation k) h2
  rw [map_mul, map_one] at h3
  rw [mem_integralGL_iff, h1]
  constructor
  · rintro ⟨a, b⟩
    have a' : valuation k (g 0 0) ≤ 1 := a 0 0
    have b' : valuation k ((g⁻¹ : GL (Fin 1) k) 0 0) ≤ 1 := b 0 0
    refine le_antisymm a' ?_
    calc 1 = _ := h3.symm
      _ ≤ 1 * valuation k (g 0 0) := by gcongr
      _ = _ := one_mul _
  · intro h
    rw [h, mul_one] at h3
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; exact h.le
    · rw [Subsingleton.elim i 0, Subsingleton.elim j 0]; exact h3.le

private theorem unram_iff {D : ℕ} {Y : Type} [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ (GL (Fin D) k) Y)
    (hρ : IsSmooth ρ) (y : IrrRep (GL (Fin D) k)) (hy : IsSubquotient y.ρ ρ)
    (hc : D = 1 → ∀ g v, v ≠ 0 → ρ g v = v → ρ g = 1) :
    (∃ ξ hξ, IrrGL.of y.ρ y.smooth y.irr = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * 1)) ↔
      D = 1 ∧ ∀ g ∈ integralGL k D, ρ g = 1 := by
  have key : ∀ (hD : D = 1) ξ hξ, IrrGL.of y.ρ y.smooth y.irr = IrrGL.ofChar ξ hξ →
      ∀ g v, y.ρ g v = (ξ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
    rintro rfl ξ hξ h g v
    have h' : IrrGL.of y.ρ y.smooth y.irr = IrrGL.of (detRep (Fin 1) ξ) (isCuspidal_detRep_one hξ).1
        (isIrreducible_ofChar _) := h
    obtain ⟨φ⟩ := IrrGL.of_eq_of.1 h'
    refine φ.toLinearEquiv.injective ?_
    refine (φ.toIntertwiningMap.isIntertwining _ _ g v).trans ?_
    rw [map_smul]
    simp [detRep]
    rfl
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible y.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : y.V)
  constructor
  · rintro ⟨ξ, hξ, h, hu⟩
    have hD : D = 1 := congrArg Sigma.fst h
    have k1 := key hD ξ hξ h
    subst hD
    rw [mul_one] at hu
    have hf : fixed y.ρ (integralGL k 1) ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨v, fun g => by
      rw [k1, hu _ ((mem_int_one g.1).1 g.2)]; simp, hv⟩
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 (UpperTheory.fixed_ne_bot_of_isSubquotient_of_isCompact _ _ _ _ _ _ hρ hy
      (GroundTheory.Automorphic.GLnLocal.isCompact_integralGL k 1) hf)
    exact ⟨rfl, fun g hg => hc rfl g w hw0 (by simpa using hw ⟨g, hg⟩)⟩
  · rintro ⟨hD, h⟩
    obtain ⟨ξ, hξ, e⟩ : ∃ ξ hξ, IrrGL.of y.ρ y.smooth y.irr = IrrGL.ofChar ξ hξ := by
      subst hD
      obtain ⟨θ, hθ, e⟩ := RankLeOne.exists_equiv_detRep k (Fin 1) _ y.ρ y.smooth y.irr
      exact ⟨θ, hθ, congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 e)⟩
    have k1 := key hD ξ hξ e
    subst hD
    refine ⟨ξ, hξ, e, fun x hx => ?_⟩
    have h2 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) x) = x := by
      ext; simp [Matrix.GeneralLinearGroup.scalar]
    have h3 := h _ ((mem_int_one (Matrix.GeneralLinearGroup.scalar (Fin 1) x)).2 (by rw [h2, hx]))
    obtain ⟨S, f, hf⟩ := hy
    obtain ⟨w, rfl⟩ := hf v
    have h4 := k1 (Matrix.GeneralLinearGroup.scalar (Fin 1) x) (f w)
    have h5 : S.toRepresentation (Matrix.GeneralLinearGroup.scalar (Fin 1) x) w = w :=
      Subtype.ext (by show ρ _ _ = _; rw [h3]; rfl)
    rw [← f.isIntertwining, h5, h2] at h4
    have h6 : ((ξ x : ℂ) - 1) • f w = 0 := by rw [sub_smul, ← h4, one_smul, sub_self]
    have h7 := (smul_eq_zero.1 h6).resolve_right hv
    rw [mul_one]
    exact Units.ext (sub_eq_zero.1 h7)

private theorem val_unif : valuation k (unif k : k) = valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) := by
  have h1 : ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) := by
    intro x hx
    have := (GroundTheory.Automorphic.GLnLocal.mem_maximalIdeal_pow_iff k (m := 1) (y := ⟨x, hx.le⟩)).1 (by
      rw [pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
      exact hx.ne)
    simpa using this
  have h2 := Classical.epsilon_spec (p := fun p : kˣ => valuation k (p : k) < 1 ∧
      ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k (p : k))
    ⟨Units.mk0 _ ((Valuation.ne_zero_iff _).1 (GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_ne_zero k)),
      GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_lt_one k, h1⟩
  exact le_antisymm (h1 _ h2.1) (h2.2 _ (GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_lt_one k))

private theorem val_eq {D : ℕ} {Y : Type} [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ (GL (Fin D) k) Y)
    (y : IrrRep (GL (Fin D) k)) (hy : IsSubquotient y.ρ ρ) {α : ℂ} (hα : ∀ v, ρ (centralUnif k D) v = α • v)
    (ξ : kˣ →* ℂˣ) (hξ : IsSmoothChar ξ) (h : IrrGL.of y.ρ y.smooth y.irr = IrrGL.ofChar ξ hξ) (hu : IsUnram (ξ * 1)) :
    (((ξ * 1) (unif k) : ℂˣ) : ℂ) = α := by
  have hD : D = 1 := congrArg Sigma.fst h
  subst hD
  rw [mul_one] at hu ⊢
  have key : ∀ g v, y.ρ g v = (ξ (Matrix.GeneralLinearGroup.det g) : ℂ) • v := by
    intro g v
    have h' : IrrGL.of y.ρ y.smooth y.irr = IrrGL.of (detRep (Fin 1) ξ) (isCuspidal_detRep_one hξ).1
        (isIrreducible_ofChar _) := h
    obtain ⟨φ⟩ := IrrGL.of_eq_of.1 h'
    refine φ.toLinearEquiv.injective ?_
    refine (φ.toIntertwiningMap.isIntertwining _ _ g v).trans ?_
    rw [map_smul]
    simp [detRep]
    rfl
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible y.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : y.V)
  obtain ⟨S, f, hf⟩ := hy
  obtain ⟨w, rfl⟩ := hf v
  have h4 := key (centralUnif k 1) (f w)
  have h5 : S.toRepresentation (centralUnif k 1) w = α • w := Subtype.ext (hα _)
  rw [← f.isIntertwining, h5, map_smul] at h4
  have h7 := smul_left_injective ℂ hv h4
  have hd : ((Matrix.GeneralLinearGroup.det (centralUnif k 1) : kˣ) : k) =
      (GroundTheory.Automorphic.GLnLocal.uniformizer k : k) := by
    simp [Matrix.det_unique, coe_centralUnif]
  have h8 := hu (unif k / Matrix.GeneralLinearGroup.det (centralUnif k 1)) (by
    rw [Units.val_div_eq_div_val, map_div₀, hd, val_unif,
      div_self (GroundTheory.Automorphic.GLnLocal.valuation_uniformizer_ne_zero k)])
  rw [map_div, div_eq_one] at h8
  rw [h8]
  exact h7.symm

private theorem cusp_block {n r : ℕ} {d : Fin r → ℕ} (e : (Σ j, Fin (d j)) ≃ Fin n) {β : Fin n → ℕ}
    (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (φ : Levi k (fun j => Fin (d j)) ≃* levi k n β)
    (hφ : ∀ g, ((φ g : levi k n β) : GL (Fin n) k) = leviEmb k e g) {W : Type} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (levi k n β) W) (hc : GroundTheory.Automorphic.Parabolic.IsCuspidal σ) (j : Fin r)
    {t : ℕ} {c : Fin t → ℕ} (e' : (Σ a, Fin (c a)) ≃ Fin (d j)) (hU : unipRad k e' ≠ ⊥) :
    Subsingleton (Jacquet ((σ.comp φ.toMonoidHom).comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) :
      Representation ℂ (GL (Fin (d j)) k) W) (unipRad k e')) := by
  have hinj : Function.Injective fun p : Fin (d j) => e ⟨j, p⟩ := fun p q h => by simpa using h
  let γ : Fin n → ℕ := Function.extend (fun p : Fin (d j) => e ⟨j, p⟩) (fun p => (blk e' p).val) 0
  have γ1 : ∀ p, γ (e ⟨j, p⟩) = (blk e' p).val := fun p => hinj.extend_apply _ _ p
  have γ0 : ∀ a, a ≠ j → ∀ p, γ (e ⟨a, p⟩) = 0 := fun a ha p =>
    Function.extend_apply' _ _ _ (by
      rintro ⟨q, hq⟩
      exact ha (congrArg Sigma.fst (e.injective hq)).symm)
  obtain ⟨p, q, hpq⟩ := GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.1 hU
  have hs := hc γ ⟨e ⟨j, p⟩, e ⟨j, q⟩, le_antisymm (not_lt.1 fun h => by simpa using (hβ _ _).1 h)
    (not_lt.1 fun h => by simpa using (hβ _ _).1 h), by
      rw [γ1, γ1]; exact fun h => hpq.ne (Fin.ext h)⟩
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun w _ => ?_)
  have hw : w ∈ Representation.Coinvariants.ker (σ.comp (leviUnipotent k n β γ).subtype) :=
    (Representation.Coinvariants.mk_eq_zero _).1 (Subsingleton.elim _ _)
  refine Submodule.span_mono ?_ hw
  rintro _ ⟨⟨u, v⟩, rfl⟩
  obtain ⟨g, hg⟩ := φ.surjective u.1
  obtain ⟨hP, h1⟩ := GroundTheory.Automorphic.Parabolic.mem_unipotentRadical.1 (Subgroup.mem_subgroupOf.1 u.2)
  rw [← hg, hφ] at hP h1
  have hg1 : g = Pi.mulSingle j (g j) := by
    funext a
    by_cases ha : a = j
    · subst ha; simp
    · rw [Pi.mulSingle_eq_of_ne ha]
      ext x y
      have := h1 (e ⟨a, x⟩) (e ⟨a, y⟩) (by rw [γ0 a ha, γ0 a ha])
      rw [leviEmb_apply_same] at this
      rw [this]
      simp [Matrix.one_apply]
  have hu : g j ∈ unipRad k e' := by
    refine mem_unipRad.2 ⟨mem_parab.2 fun x y hxy => ?_, fun a x y => ?_⟩
    · have := hP (show γ (e ⟨j, y⟩) < γ (e ⟨j, x⟩) by rw [γ1, γ1]; exact hxy)
      rwa [leviEmb_apply_same] at this
    · have := h1 (e ⟨j, e' ⟨a, x⟩⟩) (e ⟨j, e' ⟨a, y⟩⟩) (by rw [γ1, γ1]; simp)
      rw [leviEmb_apply_same] at this
      rw [this]
      simp [Matrix.one_apply]
  refine ⟨⟨g j, hu⟩, v, ?_⟩
  show σ u.1 v - v = σ (φ (Pi.mulSingle j (g j))) v - _
  rw [← hg1, hg]
  simp

private theorem pol_eq {n r : ℕ} {d : Fin r → ℕ} (hd : ∀ j, 0 < d j) (e : (Σ j, Fin (d j)) ≃ Fin n) {β : Fin n → ℕ}
    (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (φ : Levi k (fun j => Fin (d j)) ≃* levi k n β)
    (hφ : ∀ g, ((φ g : levi k n β) : GL (Fin n) k) = leviEmb k e g) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} {s : Multiset (IrrGL (k := k))} (hs : HasSupport π s)
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi k n β) W) (hi : σ.IsIrreducible)
    (hc : GroundTheory.Automorphic.Parabolic.IsCuspidal σ) (ι : Representation.IntertwiningMap π (parabolicInd k n β σ))
    (hι : Function.Injective ι) (α : Fin r → ℂ)
    (hα : ∀ j v, σ (φ (Pi.mulSingle j (centralUnif k (d j)))) v = α j • v) :
    pol s 1 = ∏ j, if d j = 1 ∧ ∀ g ∈ integralGL k (d j), σ (φ (Pi.mulSingle j g)) = 1 then
      1 - Polynomial.C (α j) * Polynomial.X else 1 := by
  let τ : Representation ℂ (Levi k fun j => Fin (d j)) W := σ.comp φ.toMonoidHom
  have hστ : τ.comp φ.symm.toMonoidHom = σ := by
    ext g v
    simp [τ]
  have hτ : τ.IsIrreducible := by
    let o : Subrepresentation τ ≃o Subrepresentation σ :=
      { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
          simpa [τ] using S.apply_mem_toSubmodule (φ.symm g) hv⟩
        invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (φ g) hv⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
    exact (OrderIso.isSimpleOrder_iff o).2 hi
  obtain ⟨E⟩ := GlobalTheory.CompanionTheory.ParIndBridge.parInd_equiv_parabolicInd k e β hβ φ hφ τ
  rw [hστ] at E
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hs.isIrreducible
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let f := E.symm.toIntertwiningMap.comp ι
  have hf : f v ≠ 0 := by
    intro h
    apply hv
    apply hι
    apply E.symm.toLinearEquiv.injective
    change E.symm.toLinearEquiv (ι.toLinearMap v) = E.symm.toLinearEquiv (ι.toLinearMap 0)
    rw [ι.map_zero, E.symm.toLinearEquiv.map_zero]
    exact h
  have hτs : IsSubquotient τ (jac e π) := .of_surjective (GlobalTheory.CompanionTheory.FrobJm.frobMap e f)
    (GlobalTheory.CompanionTheory.FrobJm.surjective_of_ne_zero hτ _ (GlobalTheory.CompanionTheory.FrobJm.frobMap_ne_zero e f ⟨v, hf⟩))
  have hτsm : IsSmooth τ := hτs.isSmooth (isSmooth_jac e hs.isSmooth)
  have hsm : ∀ j, IsSmooth (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) :
      Representation ℂ (GL (Fin (d j)) k) W) := fun j =>
    isSmooth_comp hτsm _ (continuous_mulSingle (A := fun j => GL (Fin (d j)) k) j)
  have hy : ∀ j, ∃ y : IrrRep (GL (Fin (d j)) k), IsSubquotient y.ρ
      (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) : Representation ℂ (GL (Fin (d j)) k) W) := by
    intro j
    obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
      (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j)) inferInstance
    exact ⟨⟨X, υ, hυs.isSmooth (hsm j), hυ⟩, hυs⟩
  choose y hy using hy
  obtain ⟨u, hu, rfl⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_sum_of_jac GlobalTheory.CompanionTheory.GeoLink.geometricLemma
    GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness hs e hτ hτs y hy
  have hu1 : ∀ j, u j = {IrrGL.of (y j).ρ (y j).smooth (y j).irr} := fun j => by
    refine SupportUnique.eq_singleton_of_isCusp (IrrGL.isCusp_of.2 ⟨hd j, (y j).smooth, fun t c e' hU => ?_⟩)
      ((hu j).of_equiv (IrrGL.equivOf _ _ _))
    have h0 := cusp_block e hβ φ hφ σ hc j e' hU
    obtain ⟨S, g, hg⟩ := GlobalTheory.JacquetExact.isSubquotient_jac e' (hsm j) (hy j)
    haveI : Subsingleton S.toSubmodule := ⟨fun a b => Subtype.ext (h0.elim _ _)⟩
    exact Function.Surjective.subsingleton hg
  suffices key : ∀ j, (∃ ξ hξ, IrrGL.of (y j).ρ (y j).smooth (y j).irr = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * 1)) ↔
      d j = 1 ∧ ∀ g ∈ integralGL k (d j), σ (φ (Pi.mulSingle j g)) = 1 by
    simp only [hu1]
    rw [← GlobalTheory.CompanionTheory.Hypotheses₂.TD.map_univ_eq_sum, pol, Multiset.map_map, ← Finset.prod_eq_multiset_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Function.comp]
    split_ifs with h1 h2 h2
    · obtain ⟨⟨hξ, h⟩, hu'⟩ := h1.choose_spec
      rw [val_eq _ (y j) (hy j) (hα j) _ hξ h hu']
    · obtain ⟨ξ, ⟨hξ, h⟩, hu'⟩ := h1
      exact absurd ((key j).1 ⟨ξ, hξ, h, hu'⟩) h2
    · obtain ⟨ξ, hξ, h, hu'⟩ := (key j).2 h2
      exact absurd ⟨ξ, ⟨hξ, h⟩, hu'⟩ h1
    · rfl
  intro j
  refine unram_iff _ (hsm j) (y j) (hy j) fun hD g w hw0 hw => ?_
  have hcomm : ∀ x : Levi k fun j => Fin (d j), Pi.mulSingle j g * x = x * Pi.mulSingle j g := fun x => by
    funext a
    by_cases ha : a = j
    · subst ha
      haveI : Unique (Fin (d a)) := hD ▸ inferInstance
      ext p q
      simp [Matrix.mul_apply, Subsingleton.elim p default, Subsingleton.elim q default, mul_comm]
    · simp [Pi.mulSingle_eq_of_ne ha]
  let K : Subrepresentation τ :=
    ⟨LinearMap.eqLocus (τ (Pi.mulSingle j g)) 1, fun x z hz => by
      have hz' : τ (Pi.mulSingle j g) z = z := hz
      show (τ (Pi.mulSingle j g) * τ x) z = τ x z
      rw [← map_mul, hcomm, map_mul, Module.End.mul_apply, hz']⟩
  haveI := hτ
  rcases eq_bot_or_eq_top K with h | h
  · have : w ∈ K.toSubmodule := hw
    rw [h] at this
    exact absurd ((Submodule.mem_bot ℂ).1 this) hw0
  · refine LinearMap.ext fun z => ?_
    have : z ∈ K.toSubmodule := by rw [h]; trivial
    exact this

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

open UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GroundTheory.Automorphic.GodementJacquet GroundTheory.Automorphic.Parabolic in
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.gxSupp {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V} {s : Multiset (IrrGL (k := F))}
    (hs : HasSupport π s) {β : Fin n → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (levi F n β) W} (hi : σ.IsIrreducible) (hc : GroundTheory.Automorphic.Parabolic.IsCuspidal σ)
    (ι : Representation.IntertwiningMap π (parabolicInd F n β σ)) (hι : Function.Injective ι) {ω : Set.range β → ℂ}
    (hω : ∀ b v, σ (blockUnif F b) v = ω b • v) : pol s 1 = polF σ ω := by
  let o : Fin (Fintype.card (Set.range β)) ≃o Set.range β := monoEquivOfFin _ rfl
  let d := fun j => blockSize β (o j)
  let e : (Σ j, Fin (d j)) ≃ Fin n :=
    (Equiv.sigmaCongr o.toEquiv fun j => fiberFin β (o j)).trans (Equiv.sigmaFiberEquiv (blockOf β))
  have he : ∀ j p, e ⟨j, p⟩ = (fiberFin β (o j) p).1 := fun _ _ => rfl
  have hb : ∀ j p, β (e ⟨j, p⟩) = (o j).1 := fun j p => congrArg Subtype.val (fiberFin β (o j) p).2
  let ψ : levi F n β ≃* Levi F (fun j => Fin (d j)) :=
    { (leviEquivPi F β).toEquiv.trans
        (Equiv.piCongrLeft' (fun a => GL (Fin (blockSize β a)) F) o.symm.toEquiv) with
      map_mul' := fun x y => funext fun j => congrFun (map_mul (leviEquivPi F β) x y) (o j) }
  have hψ : ∀ m j, ψ m j = leviEquivPi F β m (o j) := fun _ _ => rfl
  have hm : ∀ j g, ψ.symm (Pi.mulSingle j g) = (leviEquivPi F β).symm (Pi.mulSingle (o j) g) := fun j g => by
    rw [MulEquiv.symm_apply_eq]
    funext a
    rw [hψ, ContinuousMulEquiv.apply_symm_apply]
    by_cases ha : a = j
    · subst ha; simp
    · rw [Pi.mulSingle_eq_of_ne ha, Pi.mulSingle_eq_of_ne (o.injective.ne ha)]
  have h := pol_eq (d := d) (fun j => blockSize_pos β (o j)) e (β := β) (fun x y => by
    obtain ⟨⟨a, p⟩, rfl⟩ := e.surjective x
    obtain ⟨⟨b, q⟩, rfl⟩ := e.surjective y
    rw [hb, hb, blk_apply, blk_apply, Subtype.coe_lt_coe, o.lt_iff_lt]) ψ.symm (fun g => by
    obtain ⟨m, rfl⟩ := ψ.surjective g
    rw [ψ.symm_apply_apply]
    ext x y
    obtain ⟨⟨a, p⟩, rfl⟩ := e.surjective x
    obtain ⟨⟨b, q⟩, rfl⟩ := e.surjective y
    by_cases hab : a = b
    · subst hab
      rw [leviEmb_apply_same, hψ, leviEquivPi_apply, he, he]
    · rw [leviEmb_apply_ne _ _ _ hab]
      refine mem_levi.1 m.2 _ _ ?_
      rw [hb, hb]
      exact fun h => hab (o.injective (Subtype.ext h))) hs σ hi hc ι hι (fun j => ω (o j)) (fun j v => by
    rw [hm, leviEquivPi_symm_mulSingle, hω])
  rw [h, polF]
  refine Fintype.prod_equiv o.toEquiv _ _ fun j => ?_
  simp only [hm]
  rfl
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SideXCen
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.GamLocX
open NumberField IsDedekindDomain MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet GroundTheory.Automorphic.GJStandardL UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.kappa_one {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] {n : ℕ} {β : Fin n → ℕ} (a : Set.range β) (ha : blockSize β a = 1) :
    inducedChar β (blockUnif F a) = 1 := by
  have hML : leviModulus β (blockUnif F a) = leviAbsDet β (blockUnif F a) := by
    rw [← leviEquivPi_symm_mulSingle (F := F) a]
    set x : (b : Set.range β) → GL (Fin (blockSize β b)) F := Pi.mulSingle a (centralUnif F (blockSize β a)) with hx
    have hC : ((leviAbsDet β ((leviEquivPi F β).symm x) : ℝ≥0) : ℂ) = ∏ b, detPow (x b) 1 := by
      rw [← detPow_leviEquivPi_symm, detPow_eq_cpow, Complex.cpow_one]
      rfl
    rw [Finset.prod_eq_single a (fun b _ hb => by
        rw [hx, Pi.mulSingle_eq_of_ne hb]
        exact detPow_of_mem_integralGL (one_mem _) 1) (by simp), detPow_eq_cpow, Complex.cpow_one] at hC
    rw [leviModulus_leviEquivPi_symm, Finset.prod_eq_single a]
    · rw [detModulusPow]
      conv_lhs => arg 2; rw [ha]
      rw [pow_one]
      exact_mod_cast hC.symm
    · intro b _ hb
      rw [hx, Pi.mulSingle_eq_of_ne hb, detModulusPow]
      simp
    · simp
  set m := blockUnif F a
  have key := leviRatio_sq_mul_modular_mul_det m
  rw [hML] at key
  have hD : 0 < leviAbsDet β m := modulus_det_pos _
  have hsq : inducedChar β m ^ 2 = 1 := by
    have e : inducedChar β m = leviRatio β m * NNReal.sqrt (MeasureTheory.Measure.modularCharacter (leviIncl m)) *
        leviAbsDet β m ^ (((n : ℝ) - 1) / 2) := rfl
    rw [e, mul_pow, mul_pow, NNReal.sq_sqrt, ← NNReal.rpow_natCast (leviAbsDet β m ^ (((n : ℝ) - 1) / 2)),
      ← NNReal.rpow_mul]
    have h2 : ((n : ℝ) - 1) / 2 * ((2 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast; ring
    rw [h2]
    apply mul_right_cancel₀ hD.ne'
    rw [one_mul]
    conv_rhs => rw [← key]
    rw [mul_assoc, ← NNReal.rpow_add_one hD.ne', sub_add_cancel, NNReal.rpow_natCast]
  exact (pow_left_inj₀ (by positivity) zero_le_one two_ne_zero).1 (by rw [hsq, one_pow])

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.gamLocX :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.GamLocX := by
  intro K _ _ n hn v V _ _ π s hs
  haveI := hs.isIrreducible
  obtain ⟨β, W, _, _, σ, hirr, hsm, hcusp, hadm, Φ, hinj⟩ := exists_embedding_parabolicInd hs.isSmooth
  letI : MeasurableSpace (levi (HeightOneSpectrum.adicCompletion K v) n β) := borel _
  haveI : BorelSpace (levi (HeightOneSpectrum.adicCompletion K v) n β) := ⟨rfl⟩
  haveI := hirr
  obtain ⟨ω, hω⟩ := exists_blockChar (σ := σ) hsm
  have hB := gxBlock_of UpperTheory.local_zeta_integral_laurent_expansion UpperTheory.local_zeta_integral_shell_mean UpperTheory.local_zeta_integral_tate_comparison
  have hψc := GroundTheory.Global.continuous_localAdelicChar (K := K) v
  have hψ1 := GroundTheory.Global.localAdelicChar_ne_one (K := K) v
  obtain ⟨γ, hshape, hFE⟩ := gxLevi hB hadm hcusp (inducedChar β) continuous_inducedChar
    (leviMeasure β (GroundTheory.Global.localAdelicChar K v)) hψc hψ1 hω
  have hInd := inducedFE_of_leviFE (localHaar n v) hψc hψ1 hFE
  have hG := coefInd _ n V π hs.isSmooth β W σ hsm Φ hinj (localHaar n v) _ hψc hψ1 γ hInd
  have hpolF : polF σ (fun a => ((inducedChar β (blockUnif (HeightOneSpectrum.adicCompletion K v) a) : ℝ≥0) : ℂ) * ω a)
      = polF σ ω := by
    unfold polF
    refine Finset.prod_congr rfl (fun a _ => ?_)
    split_ifs with h
    · beta_reduce
      rw [kappa_one a h.1]
      simp
    · rfl
  have hpol := gxSupp hs hirr hcusp Φ hinj hω
  rw [hpolF, GroundTheory.Global.residueCard_adicCompletion] at hshape
  obtain ⟨c, j, hc, hγ⟩ := hshape
  refine ⟨c, j, hc, ?_⟩
  rw [hpol, ← hγ]
  exact hG
end

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.HenQ Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardL GroundTheory.Automorphic.GodementJacquet
open GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.GJStandardLCuspidal UpperTheory.V UpperTheory.V.Z.Inf UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem eval_quot (N D : ℂ[X]) (x : ℂ) (hD : D.eval x ≠ 0) :
    (algebraMap ℂ[X] (RatFunc ℂ) N / algebraMap ℂ[X] (RatFunc ℂ) D).eval (RingHom.id ℂ) x = N.eval x / D.eval x := by
  have hD0 : D ≠ 0 := fun e => hD (by simp [e])
  set R := algebraMap ℂ[X] (RatFunc ℂ) N / algebraMap ℂ[X] (RatFunc ℂ) D with hR
  have h1 : R.denom ∣ D := RatFunc.denom_div_dvd N D
  have h2 : R.denom.eval x ≠ 0 := fun e => by
    obtain ⟨u, hu⟩ := h1
    exact hD (by rw [hu, eval_mul, e, zero_mul])
  have h3 : R.num * D = N * R.denom := (RatFunc.num_mul_eq_mul_denom_iff hD0).2 hR
  have h4 := congrArg (eval x) h3
  simp only [eval_mul] at h4
  simp only [RatFunc.eval, eval₂_id]
  rw [div_eq_div_iff h2 hD, h4]

private theorem loc_dual {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (P : ℂ[X]) (c Q b : ℂ) (j : ℤ) (hP : P.eval 0 = 1) {A B : ℂ → ℂ}
    (h : RatFE F (RatFunc.C c * RatFunc.X ^ j * algebraMap ℂ[X] (RatFunc ℂ) P /
      algebraMap ℂ[X] (RatFunc ℂ) (P.comp (C Q * X))) A B) (hA : ∀ s, A s = b) :
    ∃ r : ℝ, ∀ s : ℂ, s.re < -r → B s = c * b * qs F s ^ j * P.eval (qs F s) / P.eval (Q * qs F s) := by
  obtain ⟨R, s₁, h1, h2⟩ := h
  have hR : R = RatFunc.C b := eq_of_eval_qs_eq_right (F := F) (s₁ := s₁) fun s hs => by
    rw [← h1 s hs, hA, RatFunc.eval_C]
    rfl
  have hD0 : P.comp (C Q * X) ≠ 0 := fun e => by
    have := congrArg (eval 0) e
    simp [eval_comp, hP] at this
  obtain ⟨Bd, hB, h4⟩ := exists_norm_gt_eval_ne_zero hD0
  have hq : (1 : ℝ) < GroundTheory.LocalField.residueCard F := by exact_mod_cast GroundTheory.LocalField.one_lt_residueCard
  refine ⟨max s₁ (Real.logb (GroundTheory.LocalField.residueCard F) Bd), fun s hs => ?_⟩
  have hs1 := le_max_left s₁ (Real.logb (GroundTheory.LocalField.residueCard F) Bd)
  have hs2 := le_max_right s₁ (Real.logb (GroundTheory.LocalField.residueCard F) Bd)
  have h5 : (P.comp (C Q * X)).eval (qs F s) ≠ 0 := h4 _ (by
    rw [norm_qs]
    calc Bd = (GroundTheory.LocalField.residueCard F : ℝ) ^ (Real.logb (GroundTheory.LocalField.residueCard F) Bd) :=
          (Real.rpow_logb (by linarith) hq.ne' hB).symm
      _ < _ := Real.rpow_lt_rpow_of_exponent_lt hq (by linarith))
  have hx : qs F s ≠ 0 := qs_ne_zero s
  have hj : j = (j.toNat : ℤ) - ((-j).toNat : ℤ) := (Int.toNat_sub_toNat_neg j).symm
  have e : RatFunc.C c * RatFunc.X ^ j * algebraMap ℂ[X] (RatFunc ℂ) P /
      algebraMap ℂ[X] (RatFunc ℂ) (P.comp (C Q * X)) * RatFunc.C b =
      algebraMap ℂ[X] (RatFunc ℂ) (C c * C b * X ^ j.toNat * P) /
        algebraMap ℂ[X] (RatFunc ℂ) (X ^ (-j).toNat * P.comp (C Q * X)) := by
    simp only [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    rw [hj, zpow_sub₀ RatFunc.X_ne_zero, zpow_natCast, zpow_natCast, ← hj]
    ring
  rw [h2 s (by linarith), hR, e, eval_quot _ _ _ (by rw [eval_mul, eval_pow, eval_X]; exact mul_ne_zero (pow_ne_zero _ hx) h5)]
  simp only [eval_mul, eval_pow, eval_X, eval_C, eval_comp]
  rw [hj, zpow_sub₀ hx, zpow_natCast, zpow_natCast, ← hj]
  ring

private theorem comb {I : Type} (S : Finset I) (N : I → ℕ) (P : I → ℂ[X]) (c : I → ℂ) (j : I → ℤ) (q : ℕ) (f d : I → ℕ)
    (hq : 1 < q) (h : ∀ v ∈ S, 1 < N v ∧ (P v).eval 0 = 1 ∧ (P v).natDegree = d v ∧ (d v ≠ 0 → N v = q ^ f v)) :
    ∃ (c₀ : ℂ) (t : ℝ), ∀ s : ℂ,
      ∏ v ∈ S, c v * ((N v : ℂ) ^ (-s)) ^ j v * (P v).eval ((N v : ℂ) ^ (-s)) / (P v).eval (N v * (N v : ℂ) ^ (-s)) =
        fac c₀ t q (∏ v ∈ S, (P v).comp (X ^ f v)) s := by
  have h1 : ∀ v ∈ S, d v = 0 → P v = 1 := fun v hv e => by
    have a := eq_C_of_natDegree_eq_zero ((h v hv).2.2.1.trans e)
    have b := (h v hv).2.1
    rw [a, eval_C] at b
    rw [a, b, C_1]
  have hev : ∀ v ∈ S, ∀ u : ℂ, ((P v).comp (X ^ f v)).eval (((q : ℝ) : ℂ) ^ u) = (P v).eval ((N v : ℂ) ^ u) := fun v hv u => by
    by_cases e : d v = 0
    · simp [h1 v hv e]
    · rw [eval_comp, eval_pow, eval_X, (h v hv).2.2.2 e, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul,
        Complex.ofReal_natCast, Complex.cpow_nat_mul]
  refine ⟨∏ v ∈ S, c v, ∑ v ∈ S, -(j v * Real.log (N v)), fun s => ?_⟩
  · rw [fac, eval_prod, eval_prod, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hN : (N v : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by have := (h v hv).1; omega)
    rw [hev v hv, hev v hv, sub_eq_add_neg, Complex.cpow_add _ _ hN, Complex.cpow_one]
    congr 3
    rw [Complex.cpow_def_of_ne_zero hN, ← Complex.exp_int_mul, ← Complex.natCast_log]
    congr 1
    push_cast
    ring

private theorem far_ne {A : ℂ → ℂ} (hA : Differentiable ℂ A) (h0 : A ≠ 0) (c : ℝ) : ∃ s : ℂ, c < s.re ∧ A s ≠ 0 := by
  by_contra h
  push Not at h
  refine h0 (funext fun x => AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (hA.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (Set.mem_univ ((c + 1 : ℝ) : ℂ)) ?_ trivial)
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show c < ((c + 1 : ℝ) : ℂ).re by simp)] with s hs using h s hs

set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.sideXCen :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.SideXCen := by
  have hGL := gamLocX
  have hLI := locIso
  intro K _ _ _ n hn σ h S hRS B hB sp q f hq hsp
  classical
  have hLU := locUnr
  have hSD := satDict
  have hCS := coefSm
  have hAS := archOf (shiftOf (ptwOf weyl) parts) fourD testEx (bridgeOf haarL)
  choose m hm using fun τ : K →+* ℂ => (GlobalTheory.ResW.IrrInfChar.main K n τ).1 σ
  have hn1 : 1 ≤ n := by omega
  obtain ⟨D⟩ := (Cm.toRep σ h).nonempty_adelicDecomposition
  let μ : Measure (Reduction.normOneGL (K := K) (n := n)) := Measure.haar
  obtain ⟨a, x, hx, ha, hx0, hxK⟩ := exists_pureTensor_spherical _ D
  obtain ⟨ℓ, fi, hℓs, hℓ1, hℓK, hf, hF1⟩ := matrixCoeff_factorization_of_pureTensor _ D μ a x hx ha hx0
  have hfix : ∀ v ∉ S, x v ∈ fixedVectors (D.finite.π v) (integralGL (v.adicCompletion K) n) := fun v hv =>
    hxK v ((hLI K n σ h D v).2 _ (hB v hv))
  have hsm : ∀ v, x v ∈ smoothVectors (D.finite.π v) := fun v => (D.finite.isAdmissible v).1 (x v)
  set φ₀ : cuspForms K n := Phi0 _ D a x hx with hφ₀
  have hmem : φ₀ ∈ Cm.carrier σ := (phi D a x hx).2
  have hf' : ∀ g, GJGlobal.matrixCoeff μ φ₀.1 φ₀.1 g = fi (archComp K n g) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), Parabolic.matrixCoeff (F := v.adicCompletion K) (D.finite.π v) (x v) (ℓ v)
        (localComp n v g) := hf
  have hF1' : GJGlobal.matrixCoeff μ φ₀.1 φ₀.1 1 ≠ 0 := hF1
  have hone : ∀ v : HeightOneSpectrum (𝓞 K),
      Parabolic.matrixCoeff (F := v.adicCompletion K) (D.finite.π v) (x v) (ℓ v) 1 = 1 := fun v => by
    simpa [Parabolic.matrixCoeff] using hℓ1 v

  obtain ⟨T, hT, hTc⟩ := hCS K n hn1 μ σ h φ₀
  let p : σ.V := ⟨Cm.ofCusp K n φ₀, hmem⟩
  have hfi : ∀ y, fi y = (T p).1 ((AdelicGLn.prodEquiv K n).symm (y, 1)) := fun y => by
    have e1 : archComp K n ((AdelicGLn.prodEquiv K n).symm (y, 1)) = y :=
      congrArg Prod.fst ((AdelicGLn.prodEquiv K n).apply_symm_apply (y, 1))
    have e2 : ∀ v, localComp n v ((AdelicGLn.prodEquiv K n).symm (y, 1)) = 1 := fun v => by
      have e : finComp K n ((AdelicGLn.prodEquiv K n).symm (y, 1)) = 1 :=
        congrArg Prod.snd ((AdelicGLn.prodEquiv K n).apply_symm_apply (y, 1))
      change AdelicGLn.finiteRestrictedEquiv K n (finComp K n _) v = 1
      rw [e, map_one, RestrictedProduct.one_apply]
    rw [hT]
    change _ = GJGlobal.matrixCoeff μ φ₀.1 φ₀.1 _
    rw [hf', e1]
    simp [e2, hone]
  have hfi0 : ∃ y, fi y ≠ 0 := ⟨_, left_ne_zero_of_mul (hf' 1 ▸ hF1')⟩
  obtain ⟨φ, φ', k, k', hk, hk', hAd, hA0, hsh, hsh'⟩ := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact hAS K n hn1 (T p) m (fun τ u => by
        rw [← hTc τ u p (((m τ).map (u + ·)).prod • p) (show _ = _ by first | exact (hm τ u _ hmem).symm | exact ((hm τ).2 u _ hmem).symm | exact (hm τ _ hmem u).symm | exact ((hm τ).2 _ hmem u).symm), map_smul]) fi hfi hfi0 Measure.haar

  have hz : ∀ v, ∃ z : Fin n → ℂˣ, v ∉ S →
      Spherical.IsSatakeParameter (F := v.adicCompletion K) (D.finite.π v) (localHaar n v) z ∧ B v = Finset.univ.val.map z :=
    fun v => by
      by_cases hv : v ∈ S
      · exact ⟨1, fun e => absurd hv e⟩
      · exact (hSD K n σ h D v _ (hB v hv)).imp fun z hz _ => hz
  choose z hz using hz
  have hb := fun v : HeightOneSpectrum (𝓞 K) => exists_localBump (localHaar n v) (D.finite.π v) (hsm v) (ℓ v) (g₀ := 1)
    (by rw [hone]; exact one_ne_zero)
  choose Φb hΦb b hb0 hb using hb
  let Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ :=
    fun v => if v ∈ S then Φb v else integralIndicator (v.adicCompletion K) n
  have hΦS : ∀ v ∈ S, Φ v = Φb v := fun v hv => if_pos hv
  obtain ⟨c, c', hc, hc', hSB1, hG⟩ := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact genFE hn μ φ₀.2 φ₀.2 (h hmem) S hRS
        D.finite.π x ℓ hsm hℓs (fun v hv => ⟨hfix v hv, hℓ1 v⟩) (fun v hv => hℓK v (hfix v hv)) D.finite.isIrreducible
        D.finite.isAdmissible z (fun v hv => (hz v hv).1) fi hf' ⟨1, hF1'⟩ Φ (fun v hv => hΦS v hv ▸ hΦb v)
        (fun v hv => if_neg hv)
  obtain ⟨σ₁, Λ, hΛ, h1⟩ := hG φ
  obtain ⟨σ₂, Λ', hΛ', h2⟩ := hG φ'
  have hloc : ∀ s, ∏ v ∈ S, zetaIntegral (localHaar n v) (Φ v)
      (Parabolic.matrixCoeff (F := v.adicCompletion K) (D.finite.π v) (x v) (ℓ v)) s = ∏ v ∈ S, b v := fun s =>
    Finset.prod_congr rfl fun v hv => by rw [hΦS v hv, (hb v s).2.2, detPow, GodementJacquet.absDet]; simp
  have hU := fun v (hv : v ∉ S) => hLU K n hn1 v _ (D.finite.π v) (D.finite.isIrreducible v) (D.finite.isAdmissible v)
    (fun e => hx0 v (by simpa [e] using hfix v hv)) (z v) (hz v hv).1
  have hL : ∀ s, partialL S D.finite.π s = eulerL K (cx B) S s := fun s =>
    tprod_congr fun v => by
      rw [(hU v.1 v.2 s).1, cx, (hz v.1 v.2).2, Multiset.map_map, Multiset.map_map]
      rfl
  have hL' : ∀ s, dualPartialL S D.finite.π (1 - s) = eulerLd K (cx B) S s := fun s =>
    tprod_congr fun v => by
      rw [(hU v.1 v.2 (1 - s)).2]
      simp only [cx]
      rw [(hz v.1 v.2).2, Multiset.map_map, Multiset.map_map, Multiset.map_map]
      rfl
  have hd : ∀ v, ∃ (P : ℂ[X]) (e : ℂ) (j : ℤ) (c : ℝ), v ∈ S → P = pol (sp v) 1 ∧ P.eval 0 = 1 ∧ P.natDegree = cnt (sp v) 1 ∧
      ∀ s : ℂ, s.re < -c →
      zetaIntegral (localHaar n v) (GJMatrix.localMatrixFourier (GroundTheory.Global.localAdelicChar K v) (Φ v))
        (fun g => Parabolic.matrixCoeff (F := v.adicCompletion K) (D.finite.π v) (x v) (ℓ v) g⁻¹) (1 - s) =
        e * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) ^ j * P.eval (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) /
          P.eval (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) :=
    fun v => by
      by_cases hv : v ∈ S
      · obtain ⟨e, j, -, hγ⟩ := hGL K n hn1 v _ (D.finite.π v) (sp v) ((hLI K n σ h D v).1 _ (hsp v hv).1)
        obtain ⟨hP0, hPd, -⟩ := (polFacts (v.adicCompletion K)).2.2.2 (sp v) 1
        obtain ⟨r, hr⟩ := loc_dual (pol (sp v) 1) e _ (b v) j hP0 (hγ (Φ v) (hΦS v hv ▸ hΦb v) (x v) (ℓ v) (hℓs v)) fun s => by
          rw [hΦS v hv, (hb v s).2.2, detPow, GodementJacquet.absDet]; simp
        refine ⟨pol (sp v) 1, e * b v, j, r, fun _ => ⟨rfl, hP0, hPd, fun s hs => ?_⟩⟩
        have hqs : qs (v.adicCompletion K) s = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) := by
          rw [qs, GroundTheory.Global.residueCard_adicCompletion]
        rw [← hqs]
        exact hr s hs
      · exact ⟨0, 0, 0, 0, fun e => absurd e hv⟩
  choose P e j cv hd using hd
  obtain ⟨c₀, t, hfac⟩ := comb S (fun v => Ideal.absNorm v.asIdeal) P e j q f (fun v => cnt (sp v) 1) hq
    fun v hv => ⟨NumberField.HeightOneSpectrum.one_lt_absNorm v, (hd v hv).2.1, (hd v hv).2.2.1, (hsp v hv).2⟩
  have hPe : ∏ v ∈ S, (pol (sp v) 1).comp (X ^ f v) = ∏ v ∈ S, (P v).comp (X ^ f v) :=
    Finset.prod_congr rfl fun v hv => by rw [(hd v hv).1]
  rw [hPe]
  generalize ∏ v ∈ S, (P v).comp (X ^ f v) = P₀ at hfac ⊢
  have hb' : ∏ v ∈ S, b v ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hb0 v
  set r : ℝ := |σ₁| + |σ₂| + ∑ v ∈ S, |cv v| + 2 with hr
  have hs0 : 0 ≤ ∑ v ∈ S, |cv v| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have a1 := le_abs_self σ₁
  have a2 := le_abs_self σ₂
  have a3 := abs_nonneg σ₁
  have a4 := abs_nonneg σ₂
  have hND : ∀ s : ℂ, s.re < -r + 1 → (∏ v ∈ S, zetaIntegral (localHaar n v)
      (GJMatrix.localMatrixFourier (GroundTheory.Global.localAdelicChar K v) (Φ v))
      (fun g => Parabolic.matrixCoeff (F := v.adicCompletion K) (D.finite.π v) (x v) (ℓ v) g⁻¹) (1 - s)) =
      fac c₀ t q P₀ s := fun s hs => by
    rw [← hfac]
    refine Finset.prod_congr rfl fun v hv => (hd v hv).2.2.2 s ?_
    have := Finset.single_le_sum (f := fun v => |cv v|) (fun _ _ => abs_nonneg _) hv
    linarith [le_abs_self (cv v)]
  set_option synthInstance.maxHeartbeats 200000 in
    refine ⟨linPoly (∑ τ, m τ), (monic_multiset_prod_of_monic _ _ fun z _ => monic_X_add_C z).ne_zero,
      Λ, fun s => Λ' (s + 1), fun s => c * archZeta Measure.haar φ fi s * ∏ v ∈ S, b v,
      fun s => c' * archZeta Measure.haar (archMatrixFourier φ) (fun y => fi y⁻¹) (1 - s),
      k, k', c₀, t, r, hΛ, hΛ'.comp (differentiable_id.add_const 1), ?_, hk, hk', fun s hs => ⟨?_, ?_⟩,
      fun s hs => ⟨?_, ?_⟩⟩
  · obtain ⟨s, hs, hA⟩ := far_ne hAd hA0 σ₁
    intro e
    have := (h1 s hs).2.1
    rw [e, hloc] at this
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hc hA) hb') (h1 s hs).1 this.symm
  · rw [(h1 s (by linarith)).2.1, hloc, hL]
    ring
  · beta_reduce
    rw [(h2 (s + 1) (by simp; linarith)).2.1, hloc, hL, hsh]
    ring
  · have := (h1 (1 - s) (by simp; linarith)).2.2
    rw [sub_sub_cancel, hL', hND s (by linarith)] at this
    rw [this]
    ring
  · have := (h2 (1 - (s + 1)) (by simp; linarith)).2.2
    rw [sub_sub_cancel, hL', hND (s + 1) (by simp; linarith), hsh', show 1 - (s + 1) + 1 = 1 - s by ring] at this
    beta_reduce
    rw [this]
    ring
end
end

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V UpperTheory.V.Z.Gam
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

variable {K : Type} [Field K] [NumberField K]

private theorem norm_ne (w : HeightOneSpectrum (𝓞 K)) : ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ≠ 0 := by
  have h0 : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := by
    simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  exact_mod_cast h0

private theorem euler_shift (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ) (S : Set (HeightOneSpectrum (𝓞 K))) (z s : ℂ) :
    eulerL K (fun w => (B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)) S (s - z) = eulerL K B S s := by
  unfold eulerL
  refine tprod_congr fun w => ?_
  rw [Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [mul_assoc, ← Complex.cpow_add _ _ (norm_ne w.1)]
  congr 4
  ring

private theorem eulerd_shift (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ) (S : Set (HeightOneSpectrum (𝓞 K))) (z s : ℂ) :
    eulerLd K (fun w => (B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z)) S (s - z) = eulerLd K B S s := by
  unfold eulerLd eulerL
  refine tprod_congr fun w => ?_
  rw [Multiset.map_map, Multiset.map_map, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [mul_inv, Complex.cpow_neg, inv_inv, mul_assoc, ← Complex.cpow_add _ _ (norm_ne w.1)]
  congr 4
  ring

private theorem cnt_unram {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : Multiset (IrrGL (k := k))) {χ : kˣ →* ℂˣ} (h : IsUnram χ) : cnt s χ = cnt s 1 := by
  unfold cnt
  congr 1
  refine Multiset.filter_congr fun y _ => ?_
  have key : ∀ ξ : kˣ →* ℂˣ, IsUnram (ξ * χ) ↔ IsUnram (ξ * 1) := fun ξ =>
    forall_congr' fun x => forall_congr' fun hx => by
      rw [MonoidHom.mul_apply, MonoidHom.mul_apply, h x hx, MonoidHom.one_apply]
  simp only [key]

private theorem unram_loc {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)} (h : χ.UnrAt v) : IsUnram (χ.loc v) := by
  intro x hx
  haveI : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact h x ((ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K)) Valued.v).eq_one_iff_eq_one.1 hx)

private theorem loc_unif {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)} (h : χ.UnrAt v) :
    χ.loc v (unif (v.adicCompletion K)) = χ.val v := by
  haveI : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have E := ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K))
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))
  obtain ⟨h1, h2⟩ := (polFacts (v.adicCompletion K)).1
  have hp : Valued.v ((atFin v (Formalism.L2.Host.unif v) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
    unif_spec v
  have a1 := E.lt_one_iff_lt_one.1 h1
  have a2 := (E _ _).1 (h2 ((atFin v (Formalism.L2.Host.unif v) : (v.adicCompletion K)ˣ) : v.adicCompletion K)
    (E.lt_one_iff_lt_one.2 (by rw [hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)))
  have a3 : Valued.v ((unif (v.adicCompletion K) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    refine le_antisymm ((WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero).1 ?_) (hp ▸ a2)
    rwa [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  have a4 := h (unif (v.adicCompletion K) * (atFin v (Formalism.L2.Host.unif v))⁻¹) (by
    change Valued.v _ = 1
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, a3, hp, mul_inv_cancel₀ WithZero.exp_ne_zero])
  rw [map_mul, map_inv, mul_inv_eq_one] at a4
  exact a4

private theorem pol_shift (P : ℂ[X]) (N q f d : ℕ) (z : ℂ) (hq : 1 < q) (h0 : P.eval 0 = 1) (hd : P.natDegree = d)
    (h : d ≠ 0 → N = q ^ f) :
    ((P.comp (C ((N : ℂ) ^ (-z)) * X)).comp (X ^ f)).comp (C (((q : ℝ) : ℂ) ^ z) * X) = P.comp (X ^ f) := by
  by_cases e : d = 0
  · rw [eq_C_of_natDegree_eq_zero (hd.trans e)]
    simp
  · have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have : (N : ℂ) ^ (-z) * (((q : ℝ) : ℂ) ^ z) ^ f = 1 := by
      rw [h e, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.ofReal_natCast, ← Complex.cpow_nat_mul,
        ← Complex.cpow_add _ _ hq0]
      simp
    rw [comp_assoc, comp_assoc]
    congr 1
    simp only [mul_comp, C_comp, X_comp, pow_comp, mul_pow, ← C_pow]
    rw [← mul_assoc, ← C_mul, this, C_1, one_mul]

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

open UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter in
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.sideX :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.SideX := by
  intro K _ _ _ n hn σ S hS B hB s q f hq hs
  let x : GlobalTheory.ResW.Letter K := ⟨n, σ⟩
  have hd : ((n : ℂ) * (Module.finrank ℚ K : ℂ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  let z : ℂ := -GlobalTheory.ResW.cex x / ((n : ℂ) * (Module.finrank ℚ K : ℂ))
  let χ : HChar K := Model.absC K z
  have hspec := (GlobalTheory.ResW.letter_centralExponent K x).1
  have htr : (Matrix.of (oneL K n)).trace = (n : ℝ) • (1 : Cinf K) := by
    change (Matrix.of (fun i j : Fin n => if i = j then (1 : Cinf K) else 0)).trace = _
    simp [Matrix.trace, Nat.cast_smul_eq_nsmul]
  have hz : ∀ φ ∈ (σ.twist χ).V, lie K n (oneL K n) φ = 0 := by
    rintro _ ⟨ψ, hψ, rfl⟩
    have e0 : lie K n (oneL K n) ψ = GlobalTheory.ResW.cex x • ψ := hspec ψ hψ
    have e1 : dchi χ (Matrix.of (oneL K n)).trace = -GlobalTheory.ResW.cex x := by
      rw [htr, map_smul, GlobalTheory.ResW.dchi_absC_one_finrank]
      have hzd : z * ((n : ℂ) * (Module.finrank ℚ K : ℂ)) = -GlobalTheory.ResW.cex x := div_mul_cancel₀ _ hd
      simp only [Complex.real_smul, Complex.ofReal_natCast]
      linear_combination hzd
    change lie K n (oneL K n) (mulChi n χ ψ) = 0
    rw [lie_mulChi, e0, e1, ← add_smul, add_neg_cancel, zero_smul, map_zero]
  have hval : ∀ v, χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z) := fun v => by
    refine ⟨fun y hy => Units.ext ?_, ?_⟩
    · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm K (GlobalTheory.Mem.Chr.localIdele K v y)) = 1
      rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v y 0 (by simpa [IsUnitAt] using hy)]; simp
    · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm K (GlobalTheory.Mem.Chr.localIdele K v (atFin v (Formalism.L2.Host.unif v)))) = _
      have h0 : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot
      rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v _ 1 (unif_spec v), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
        ← Complex.natCast_log]
      congr 1; push_cast; ring
  have hex : ∀ v, ∃ s', v ∈ S → SuppAt (σ.twist χ) v s' ∧ cnt s' 1 = cnt (s v) 1 ∧
      pol s' 1 = (pol (s v) 1).comp (C (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)) * X) := fun v => by
    by_cases hv : v ∈ S
    · obtain ⟨s', h1, h2, -⟩ := suppTw K n (by omega) σ v χ (s v) (hs v hv).1
      have hF := (polFacts (v.adicCompletion K)).2.2.2
      refine ⟨s', fun _ => ⟨h1, ?_, ?_⟩⟩
      · rw [← (hF s' 1).2.1, h2, (hF _ _).2.1, mul_one, cnt_unram _ (unram_loc (hval v).1)]
      · rw [h2, mul_comm, (hF (s v) 1).2.2.2 _ (unram_loc (hval v).1), loc_unif (hval v).1, (hval v).2]
    · exact ⟨0, fun h => absurd h hv⟩
  choose s' hs' using hex
  obtain ⟨β, hβ, hP⟩ := sideXCen K n hn (σ.twist χ) (Cm.carrier_le_central _ hz) S hS
    (fun w => (B w).map (· * χ.val w)) (fun w hw => by
      have h := (hB w hw).twist (hval w).1
      rwa [CG.twist_mk] at h) s' q f hq
    (fun v hv => ⟨(hs' v hv).1, fun h => (hs v hv).2 (by rwa [← (hs' v hv).2.1])⟩)
  have hP2 := pairGOps.2.2.2 _ _ _ _ _ z (by exact_mod_cast hq) hP
  have e : ∀ w, cx (fun w => (B w).map (· * χ.val w)) w =
      (cx B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z) := fun w => by
    simp only [cx, Multiset.map_map, Function.comp_def, Units.val_mul, (hval w).2]
  have e' : cx (fun w => (B w).map (· * χ.val w)) =
      fun w => (cx B w).map fun b => b * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-z) := funext e
  have e'' : (∏ v ∈ S, (pol (s' v) 1).comp (X ^ f v)).comp (C (((q : ℝ) : ℂ) ^ z) * X) =
      ∏ v ∈ S, (pol (s v) 1).comp (X ^ f v) := by
    rw [Polynomial.prod_comp]
    refine Finset.prod_congr rfl fun v hv => ?_
    have hF := (polFacts (v.adicCompletion K)).2.2.2 (s v) 1
    rw [(hs' v hv).2.2]
    exact pol_shift _ _ q _ _ z hq hF.1 hF.2.1 (hs v hv).2
  rw [e', e''] at hP2
  refine ⟨β.comp (X - C z), ?_, ?_⟩
  · intro h
    apply hβ
    have := congrArg (fun p => p.comp (X + C z)) h
    simpa [comp_assoc] using this
  · simpa only [euler_shift, eulerd_shift] using hP2
