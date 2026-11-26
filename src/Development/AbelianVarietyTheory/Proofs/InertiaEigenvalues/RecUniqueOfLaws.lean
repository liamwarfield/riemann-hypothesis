module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTorusEigenformOfCompactTorusEigenvector
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.ReindexedFiltrationComparison
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDerivativeInducedTensorForms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecUniqueOfLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleGL1IsCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleGL1IsCharacter
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.DegreeOne

theorem classOfDegreeOne_eq_ofChar : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)), x.1 = 1 →
    ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), x = IrrGL.ofChar χ hχ := by
  intro _ k _ _ _ _ _ x hx
  obtain ⟨n, c⟩ := x
  obtain rfl : n = 1 := hx
  obtain ⟨θ, hθ, ⟨e⟩⟩ := RankLeOne.exists_equiv_detRep k (Fin 1) _ c.rep.ρ c.rep.smooth c.rep.irr
  exact ⟨θ, hθ, congrArg (Sigma.mk 1) (c.cl_rep.symm.trans (IrrRep.cl_eq_iff.2 ⟨e⟩))⟩

end GlobalTheory.LocLanglands.DegreeOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleGL1IsCharacterStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_GL1_is_character : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)), x.1 = 1 → ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), x = IrrGL.ofChar χ hχ := by
  first | exact @GlobalTheory.LocLanglands.DegreeOne.classOfDegreeOne_eq_ofChar | exact GlobalTheory.LocLanglands.DegreeOne.classOfDegreeOne_eq_ofChar | (intros; apply GlobalTheory.LocLanglands.DegreeOne.classOfDegreeOne_eq_ofChar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecUniqueOfLaws
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.Unique

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem segSum_congr (rc rc' : IrrGL (k := w.adicCompletion E) → WD h) (l : List (Segment (w.adicCompletion E)))
    (H : ∀ Δ ∈ l, rc Δ.first = rc' Δ.first) : segSum rc l = segSum rc' l := by
  unfold segSum
  congr 1
  exact List.map_congr_left fun Δ hΔ => by rw [H Δ hΔ]

theorem first_fst_le_of_isL {k V : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [AddCommGroup V] [Module ℂ V] {N : ℕ} {π : Representation ℂ (GL (Fin N) k) V} {𝔪 : Multiset (Segment k)}
    (hL : IsL 𝔪 π) {Δ : Segment k} (hΔ : Δ ∈ 𝔪) : Δ.first.1 ≤ N := by
  obtain ⟨_, xs, hd, ⟨Δs, ⟨hmap, -⟩, hLs⟩, -⟩ := hL
  rw [← hmap] at hΔ
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hΔ
  have h1 := (hLs i).deg_eq
  have h2 : (xs i).1 ≤ ∑ a, (xs a).1 := Finset.single_le_sum (f := fun a => (xs a).1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h3 : (Δs i).d ≤ (Δs i).deg := Nat.le_mul_of_pos_left _ (Δs i).len_pos
  show (Δs i).d ≤ N
  omega

theorem eq_of_isCusp (hLC : LocalConverseGL) (hBZ : BernsteinZelevinskyFiniteness)
    {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
    {e e' : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {rc rc' : IrrGL (k := w.adicCompletion E) → WD h}
    {ψ : AddChar (w.adicCompletion E) Circle} (hψc : Continuous ψ) (hψ : ψ ≠ 1) (he : e ψ = e' ψ)
    (H : LawsMin a ha e rc) (H' : LawsMin a ha e' rc') (x : IrrGL (k := w.adicCompletion E)) (hx : x.IsCusp)
    (ih : ∀ y : IrrGL (k := w.adicCompletion E), y.1 < x.1 → rc y = rc' y) : rc x = rc' x := by
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  obtain ⟨n, c⟩ := x
  obtain ⟨hn, hc⟩ := hx
  rcases n with _ | m
  · exact absurd hn (lt_irrefl 0)
  rcases m with _ | m
  · obtain ⟨χ, hχ, hx⟩ := GlobalTheory.T.irreducible_GL1_is_character hBZ _ ⟨1, c⟩ rfl
    rw [hx, H.one, H'.one]
  · obtain ⟨x', hx'⟩ := H'.bij.2 (rc ⟨m + 2, c⟩)
    have hd : x'.1 = m + 2 := by
      have := H'.dim x'
      rw [hx', H.dim] at this
      exact this.symm
    have hcx' : x'.IsCusp := (H'.cusp x').2 (hx' ▸ (H.cusp _).1 ⟨hn, hc⟩)
    obtain ⟨n', c'⟩ := x'
    obtain rfl : n' = m + 2 := hd
    have hcls : ∀ d : IrrCl (GL (Fin (m + 2)) (w.adicCompletion E)), cls d.rep = ⟨m + 2, d⟩ := fun d => by
      simp [cls, IrrCl.cl_rep]
    have key : c = c' := by
      rw [← c.cl_rep, ← c'.cl_rep]
      refine IrrRep.cl_eq_iff.2 ?_
      refine hLC _ ψ hψc hψ (m + 1) (Nat.succ_pos m) c.rep c'.rep hc hcx'.2 fun τ => ?_
      have h2 : rc (cls τ) = rc' (cls τ) := ih _ (by show m + 1 < m + 2; omega)
      refine ⟨_, H.eps ψ hψc hψ (m + 1) c.rep τ hc, ?_⟩
      have h1 := H'.eps ψ hψc hψ (m + 1) c'.rep τ hcx'.2
      rw [hcls] at h1 ⊢
      rw [he, ← hx', h2]
      exact h1
    subst key
    exact hx'.symm

theorem eq_of_lawsMin : LocalConverseGL → LanglandsExhaustionGL → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h) (rc' : IrrGL (k := w.adicCompletion E) → WD h) (ψ : AddChar (w.adicCompletion E) Circle) (e' : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ), Continuous ψ → ψ ≠ 1 → e ψ = e' ψ → LawsMin a ha e rc → LawsMin a ha e' rc' → rc = rc' := by
  intro hLC hEx hBZ E Ω _ _ _ _ _ A w h a ha e rc rc' ψ e' hψc hψ he H H'
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  have main : ∀ n, ∀ x : IrrGL (k := w.adicCompletion E), x.1 = n → rc x = rc' x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hxn
      obtain ⟨𝔪, h𝔪⟩ := hEx _ x
      have hL : IsL ((𝔪.toList : List _) : Multiset _) x.rep := by rwa [Multiset.coe_toList]
      rw [H.langlands _ x hL, H'.langlands _ x hL]
      refine segSum_congr rc rc' _ fun Δ hΔ => ?_
      have hle : Δ.first.1 ≤ n := hxn ▸ first_fst_le_of_isL h𝔪 (Multiset.mem_toList.1 hΔ)
      exact eq_of_isCusp hLC hBZ hψc hψ he H H' Δ.first Δ.isCusp_first
        fun y hy => ih y.1 (by omega) y rfl
  funext x
  exact main _ x rfl

end GlobalTheory.LocLanglands.Unique

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecUniqueOfLawsStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rec_unique_of_laws : LocalConverseGL → LanglandsExhaustionGL → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h) (rc' : IrrGL (k := w.adicCompletion E) → WD h) (ψ : AddChar (w.adicCompletion E) Circle) (e' : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ), Continuous ψ → ψ ≠ 1 → e ψ = e' ψ → LawsMin a ha e rc → LawsMin a ha e' rc' → rc = rc' := by
  first | exact @GlobalTheory.LocLanglands.Unique.eq_of_lawsMin | exact GlobalTheory.LocLanglands.Unique.eq_of_lawsMin | (intros; apply GlobalTheory.LocLanglands.Unique.eq_of_lawsMin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationDetCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationDetCharacter
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
  GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

namespace GlobalTheory.LocGL.DetQuot

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nonempty_equiv_multiProd {t : ℕ} {n : Type} [Fintype n] [DecidableEq n] (e : (Σ _ : Fin t, Fin 1) ≃ n)
    {θ : Fin t → kˣ →* ℂˣ} {Θ : Levi k (fun _ : Fin t => Fin 1) →* ℂˣ}
    (hΘ : ∀ g, Θ g = ∏ a, θ a (GeneralLinearGroup.det (g a))) :
    Nonempty ((parInd e (ofChar Θ)).Equiv (multiProd e fun a => detRep (Fin 1) (θ a))) := by
  refine ⟨parIndEquiv e (Representation.Equiv.mk
    (PiTensorProduct.constantBaseRingEquiv (Fin t) ℂ).toLinearEquiv.symm fun g => ?_)⟩
  refine LinearMap.ext_ring ?_
  apply (PiTensorProduct.constantBaseRingEquiv (Fin t) ℂ).injective
  simp [ofChar_apply, hΘ, PiTensorProduct.one_def, piTensor_tprod, detRep, detChar_apply, Units.coe_prod]

theorem exists_embedding {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {η : kˣ →* ℂˣ} (hη : IsSmoothChar η) :
    ∃ f : (detRep n η).IntertwiningMap (parInd e (ofChar (detLevi e η))), Function.Injective f := by
  have hsm : IsSmooth (detRep n η) := (isSmooth_ofChar_iff _).2 hη.detChar
  let ψ : (GlobalTheory.SmGL.jac e (detRep n η)).IntertwiningMap (ofChar (detLevi e η)) :=
    { toLinearMap := (twKer (detRep n η) (unipRad k e) 1).liftQ LinearMap.id
        (by rw [twKer_detRep]; exact bot_le)
      isIntertwining' := fun g => LinearMap.ext fun x => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, GlobalTheory.SmGL.Model.jac_detRep, map_smul, ofChar_apply,
          smul_eq_mul] }
  obtain ⟨f, hf⟩ := (GlobalTheory.SmGL.Model.evalOne_bijective e hsm (ofChar (detLevi e η))).2 ψ
  refine ⟨f, (injective_iff_map_eq_zero f).2 fun c hc => ?_⟩
  by_contra hc0
  have h1 : f 1 = 0 := by
    have h1' : (1 : ℂ) = c⁻¹ • c := by simp [hc0]
    rw [h1', map_smul, hc, smul_zero]
  have h2 : ψ (Submodule.Quotient.mk (p := twKer (detRep n η) (unipRad k e) 1) (1 : ℂ)) = 1 := rfl
  have h3 : ψ (Submodule.Quotient.mk (p := twKer (detRep n η) (unipRad k e) 1) (1 : ℂ)) = (f 1).1.1 1 := by
    rw [← hf]; rfl
  rw [h1] at h3
  exact one_ne_zero (h2.symm.trans h3)

theorem exists_surjective_of_contra {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] {π : Representation ℂ G V} {χ : G →* ℂˣ} (f : (ofChar χ⁻¹).IntertwiningMap (contra π))
    (hf : Function.Injective f) : ∃ l : π.IntertwiningMap (ofChar χ), Function.Surjective l := by
  set lam : Module.Dual ℂ V := ((f 1 : smoothPart π.dual) : Module.Dual ℂ V) with hlam
  have key : ∀ g v, lam (π g v) = (χ g : ℂ) * lam v := by
    intro g v
    have h1 : f (ofChar (χ⁻¹) (g⁻¹) (1 : ℂ)) = contra π (g⁻¹) (f 1) :=
      LinearMap.congr_fun (f.isIntertwining' (g⁻¹)) (1 : ℂ)
    have h2 : ofChar (χ⁻¹) (g⁻¹) (1 : ℂ) = (χ g : ℂ) • (1 : ℂ) := by
      rw [ofChar_apply]
      simp
    rw [h2, map_smul] at h1
    have h3 := congrArg (fun x : smoothPart π.dual => (x : Module.Dual ℂ V) v) h1
    simp only [contra_apply, inv_inv] at h3
    rw [← h3]
    simp [lam]
  have hne : lam ≠ 0 := by
    intro h0
    have h1 : f 1 = 0 := Subtype.ext (by simpa [lam] using h0)
    exact one_ne_zero (hf (h1.trans (map_zero f).symm))
  obtain ⟨v, hv⟩ : ∃ v, lam v ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (LinearMap.ext h)
  refine ⟨⟨lam, fun g => LinearMap.ext fun w => ?_⟩, fun c => ⟨(c / lam v) • v, ?_⟩⟩
  · simp [key, ofChar_apply]
  · simp [hv]

theorem exists_surjective {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {η : kˣ →* ℂˣ} (hη : IsSmoothChar η) :
    ∃ l : (parInd e (ofChar (detLevi e η⁻¹)⁻¹)).IntertwiningMap (detRep n η), Function.Surjective l := by
  have hc : IsSmoothChar (detLevi e η⁻¹) := by
    unfold detLevi
    exact (hη.inv.detChar.comp (leviEmb k e) (continuous_leviEmb (R := k) e)).mul
      (isSmoothChar_deltaHalf k).inv
  have hc' : IsSmoothChar (detLevi e η⁻¹)⁻¹ := hc.inv
  have hτ : IsSmooth (ofChar (detLevi e η⁻¹)⁻¹) := (isSmooth_ofChar_iff _).2 hc'
  obtain ⟨Φ1⟩ := GlobalTheory.LocGL.ProjLine.nonempty_equiv_contra_ofChar hc'
  rw [inv_inv] at Φ1
  obtain ⟨Φ2⟩ := (GlobalTheory.SmGL.IndDual.inductionContragredient k).nonempty_equiv e hτ
  obtain ⟨f, hf⟩ := exists_embedding e hη.inv
  let F := (Φ2.toIntertwiningMap.comp (parIndEquiv e Φ1).toIntertwiningMap).comp f
  have hF : Function.Injective F := fun a b h =>
    hf ((EquivLike.injective (parIndEquiv e Φ1)) ((EquivLike.injective Φ2) h))
  have hdet : detChar n η⁻¹ = (detChar n η)⁻¹ := by
    ext g
    simp [detChar_apply]
  have key : ∀ (χ' : GL n k →* ℂˣ), χ' = (detChar n η)⁻¹ →
      ∀ f' : (ofChar χ').IntertwiningMap (contra (parInd e (ofChar (detLevi e η⁻¹)⁻¹))), Function.Injective f' →
      ∃ l : (parInd e (ofChar (detLevi e η⁻¹)⁻¹)).IntertwiningMap (ofChar (detChar n η)), Function.Surjective l := by
    rintro χ' rfl f' hf'
    exact exists_surjective_of_contra f' hf'
  exact key (detChar n η⁻¹) hdet F hF

theorem surj_of_equiv {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup X] [Module ℂ X] {π : Representation ℂ G V} {σ : Representation ℂ G W} {τ : Representation ℂ G X}
    (Φ : π.Equiv σ) (l : π.IntertwiningMap τ) (hl : Function.Surjective l) :
    ∃ l' : σ.IntertwiningMap τ, Function.Surjective l' := by
  refine ⟨l.comp Φ.symm.toIntertwiningMap, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hl y
  refine ⟨Φ x, ?_⟩
  show l (Φ.symm (Φ x)) = l x
  rw [Representation.Equiv.symm_apply_apply]

theorem detLevi_inv_apply {t : ℕ} {n : Type} [Fintype n] [DecidableEq n] (e : (Σ _ : Fin t, Fin 1) ≃ n)
    (χ : kˣ →* ℂˣ) (g : Levi k fun _ : Fin t => Fin 1) :
    (detLevi e χ⁻¹)⁻¹ g =
      ∏ a : Fin t, (χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) (GeneralLinearGroup.det (g a)) := by
  rw [MonoidHom.inv_apply, detLevi_apply, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hs : (((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) =
      -(-((modExp (fun _ : Fin t => Fin 1) a : ℤ) : ℂ) / 2) := by
    rw [modExp_fin (fun _ : Fin t => Fin 1) (fun _ => Fintype.card_fin 1) a]
    push_cast
    ring
  rw [hs, absPow_neg]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv]

theorem exists_surjective_multiProd {t : ℕ} {n : Type} [Fintype n] [DecidableEq n] (e : (Σ _ : Fin t, Fin 1) ≃ n)
    {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    ∃ l : (multiProd e fun a : Fin t => detRep (Fin 1)
      (χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ))).IntertwiningMap (detRep n χ), Function.Surjective l := by
  obtain ⟨Φ⟩ := nonempty_equiv_multiProd e (Θ := (detLevi e χ⁻¹)⁻¹)
    (θ := fun a : Fin t => χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) (detLevi_inv_apply e χ)
  obtain ⟨l, hl⟩ := exists_surjective e hχ
  exact surj_of_equiv Φ l hl

theorem exists_equiv_prodIrr {t : ℕ} {θ : Fin t → kˣ →* ℂˣ} (hθ : ∀ a, IsSmoothChar (θ a)) {x : Fin t → IrrGL (k := k)}
    (hx : ∀ a, x a = IrrGL.ofChar (θ a) (hθ a)) :
    ∃ (e : (Σ _ : Fin t, Fin 1) ≃ Fin t) (hd' : ∑ a, (x a).1 = t), Nonempty ((multiProd e fun a => detRep (Fin 1) (θ a)).Equiv (prodIrr x hd')) := by
  obtain rfl : x = fun a => IrrGL.ofChar (θ a) (hθ a) := funext hx
  have hd : ∑ a : Fin t, (IrrGL.ofChar (θ a) (hθ a)).1 = t := by simp [IrrGL.ofChar]
  exact ⟨stdBlocks _ hd, hd, ⟨multiProdEquiv _ fun a => equivRep (IrrRep.det (Fin 1) (θ a) (hθ a))⟩⟩

set_option maxHeartbeats 1600000 in
private theorem exists_surjective_prodIrr_to_detRep (t : ℕ) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) {x : Fin t → IrrGL (k := k)}
    (hx : ∀ j, x j = (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - (j : ℕ) : ℝ) : ℂ)) :
    ∃ (hd : ∑ a, (x a).1 = t) (l : (prodIrr x hd).IntertwiningMap (detRep (Fin t) χ)), Function.Surjective l := by
  have hθ : ∀ a : Fin t, IsSmoothChar (χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) :=
    fun a => hχ.mul (isSmoothChar_absPow _)
  have hx' : ∀ a, x a = IrrGL.ofChar (χ * absPow k ((((t : ℝ) - 1) / 2 - (a : ℕ) : ℝ) : ℂ)) (hθ a) :=
    fun a => (hx a).trans (IrrGL.tw_ofChar χ _ hχ (isSmoothChar_absPow _))
  obtain ⟨e, hd, hΦ⟩ := exists_equiv_prodIrr hθ hx'
  obtain ⟨Φ⟩ := hΦ
  obtain ⟨l, hl⟩ := exists_surjective_multiProd (t := t) (n := Fin t) e (χ := χ) hχ
  refine ⟨hd, ?_⟩
  exact surj_of_equiv Φ l hl

theorem exists_surjective_prodIrr (t : ℕ) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) {x : Fin t → IrrGL (k := k)}
    (hx : ∀ j, x j = (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - (j : ℕ) : ℝ) : ℂ)) :
    ∃ (hd : ∑ a, (x a).1 = t) (l : (prodIrr x hd).IntertwiningMap (detRep (Fin t) χ)), Function.Surjective l :=
  exists_surjective_prodIrr_to_detRep t hχ hx

end GlobalTheory.LocGL.DetQuot

namespace GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem isL_det : StandardCosocleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (t : ℕ) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
    IsL (((List.range t).map fun j : ℕ => Segment.single ((IrrGL.ofChar χ hχ).nu
      ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ)) ((IrrGL.isCusp_ofChar χ hχ).nu _) : List (Segment k)) : Multiset (Segment k))
      (IrrRep.det (Fin t) χ hχ).ρ := by
  intro H k _ _ _ _ _ t χ hχ
  let x : Fin t → IrrGL (k := k) := fun j => (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - (j : ℕ) : ℝ) : ℂ)
  obtain ⟨hd, l, hl⟩ := DetQuot.exists_surjective_prodIrr t hχ (x := x) (fun j => rfl)
  have hcusp : ∀ j, (x j).IsCusp := fun j => (IrrGL.isCusp_ofChar χ hχ).nu _
  let Δ : Fin t → Segment k := fun j => Segment.single (x j) (hcusp j)
  have hfirst : ∀ j, (Δ j).first = x j := fun j => Segment.first_ofFirst _ _ _ _
  have hord : IsOrderedForm Δ (((List.range t).map fun j : ℕ => Segment.single ((IrrGL.ofChar χ hχ).nu
      ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ)) ((IrrGL.isCusp_ofChar χ hχ).nu _) : List (Segment k)) : Multiset (Segment k)) := by
    refine ⟨?_, ?_⟩
    · rw [Fin.univ_val_map]
      congr 1
      apply List.ext_get (by simp)
      intro i h1 h2
      simp [Δ, x]
    · rintro i j hij ⟨-, m, hm, heq⟩
      rw [hfirst, hfirst] at heq
      have key : (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - ((j : ℕ) : ℝ) : ℝ) : ℂ) =
          (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - ((i : ℕ) : ℝ) + (m : ℝ) : ℝ) : ℂ) := by
        calc (IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - ((j : ℕ) : ℝ) : ℝ) : ℂ) = x j := rfl
          _ = (x i).nu (m : ℂ) := heq
          _ = ((IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - ((i : ℕ) : ℝ) : ℝ) : ℂ)).nu (m : ℂ) := rfl
          _ = _ := by
            rw [IrrGL.nu_nu]
            congr 1
            push_cast
            ring
      rw [IrrGL.nu_ofChar_inj] at key
      have hij' : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      linarith
  have hL : LFactors (((List.range t).map fun j : ℕ => Segment.single ((IrrGL.ofChar χ hχ).nu
      ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ)) ((IrrGL.isCusp_ofChar χ hχ).nu _) : List (Segment k)) : Multiset (Segment k)) x :=
    ⟨Δ, hord, fun j => (single_spec (hcusp j)).2.1⟩
  obtain ⟨π0, hπ0⟩ := H k _ t t x hd hL
  obtain ⟨Ψ⟩ := hπ0.equiv_of_surjective (IrrRep.det (Fin t) χ hχ).irr l hl
  exact ⟨t, x, hd, hL, hπ0.of_equiv Ψ.symm (Representation.Equiv.refl _)⟩

end GlobalTheory.LocGL

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationDetCharacterStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLanglandsClassification_detCharacter : StandardCosocleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (t : ℕ) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsL (((List.range t).map fun j : ℕ => Segment.single ((IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ)) ((IrrGL.isCusp_ofChar χ hχ).nu _) : List (Segment k)) : Multiset (Segment k)) (IrrRep.det (Fin t) χ hχ).ρ := by
  first | exact @GlobalTheory.LocGL.isL_det | exact GlobalTheory.LocGL.isL_det | (intros; apply GlobalTheory.LocGL.isL_det <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWeilDeligneEqDiagonalInv
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWeilDeligneEqDiagonalInv
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem unr_eq_diag_inv : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (y : WD h), y.unr → ∃ α : Fin y.lpDim → ℂˣ, y = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  intro E Ω _ _ _ _ _ A w h y hy
  obtain ⟨n, c, rfl⟩ := GlobalTheory.WeilDeligne.Unram.exists_diag hy
  have hn : (WD.mk (WDRep.diag h c)).lpDim = n := by simp
  refine ⟨fun i => (c (Fin.cast hn i))⁻¹, ?_⟩
  simp only [inv_inv]
  refine WD.sound ⟨LinearEquiv.funCongrLeft ℂ ℂ (finCongr hn), fun σ v => funext fun k => ?_,
    fun v => by simp⟩
  simp [LinearEquiv.funCongrLeft_apply]

end GlobalTheory.LocLanglands
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWeilDeligneEqDiagonalInvStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_weilDeligne_eq_diagonal_inv : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (y : WD h), y.unr → ∃ α : Fin y.lpDim → ℂˣ, y = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  first | exact @GlobalTheory.LocLanglands.unr_eq_diag_inv | exact GlobalTheory.LocLanglands.unr_eq_diag_inv | (intros; apply GlobalTheory.LocLanglands.unr_eq_diag_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinInertiaIsUnitAt
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinInertiaIsUnitAt
open NumberField IsDedekindDomain Polynomial ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
open Neutral.B1 hiding IsPlaceOver

noncomputable section

namespace GlobalTheory.ArtinInertia

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem isUnitAt_artin_ine : ∀ {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A w')
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha : IsLocalArtin h' a') (t : Ine (F := E') A),
    IsUnitAt w' (a' (ineIncl h' t)) := by
  intro E' Ω _ _ _ _ _ A w' h' a' ha t
  have h1 := ha.ord_eq (ineIncl h' t)
  rw [deg_ineIncl, neg_zero, SphCompletion.ord_completion, neg_eq_zero] at h1
  have h0 : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') ≠ 0 := by simp
  show Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') = 1
  rw [← WithZero.exp_log h0, h1, WithZero.exp_zero]

end GlobalTheory.ArtinInertia
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinInertiaIsUnitAtStatement
open NumberField IsDedekindDomain Polynomial ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
open Neutral.B1 hiding IsPlaceOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localArtin_inertia_isUnitAt : ∀ {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A w')
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha : IsLocalArtin h' a') (t : Ine (F := E') A),
    IsUnitAt w' (a' (ineIncl h' t)) := by
  first | exact @GlobalTheory.ArtinInertia.isUnitAt_artin_ine | exact GlobalTheory.ArtinInertia.isUnitAt_artin_ine | (intros; apply GlobalTheory.ArtinInertia.isUnitAt_artin_ine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivOfSameSatakeParameters
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivOfSameSatakeParameters
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SmGL.SphUniq

section Abstract

variable {G X V V' : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup V'] [Module ℂ V']

theorem map_eq_top {ρ : Representation ℂ G X} {π : Representation ℂ G V} (hπ : π.IsIrreducible)
    (f : ρ.IntertwiningMap π) (U : Submodule ℂ X) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) {u : X} (hu : u ∈ U)
    (h0 : f u ≠ 0) (v : V) : ∃ x ∈ U, f x = v := by
  let R : Subrepresentation π := ⟨U.map f.toLinearMap, by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨ρ g x, hU g x hx, f.isIntertwining _ _ g x⟩⟩
  rcases eq_bot_or_eq_top R with h | h
  · have h1 : f u ∈ R.toSubmodule := ⟨u, hu, rfl⟩
    rw [h] at h1
    exact absurd h1 h0
  · have h1 : v ∈ R.toSubmodule := by rw [h]; trivial
    exact h1

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem ker_le {ρ : Representation ℂ G X} {π : Representation ℂ G V} {π' : Representation ℂ G V'}
    (hρ : IsSmooth ρ) (hπ' : π'.IsIrreducible) {K : Subgroup G} (hK : IsCompact (K : Set G))
    (f : ρ.IntertwiningMap π) (f' : ρ.IntertwiningMap π') {w : X} (hw : w ∈ fixed ρ K) (h0 : f w ≠ 0)
    (h0' : f' w ≠ 0) (hl : ∀ v ∈ fixed ρ K, ∃ c : ℂ, v = c • w) :
    LinearMap.ker f.toLinearMap ≤ LinearMap.ker f'.toLinearMap := by
  intro u hu
  by_contra hu'
  obtain ⟨x, hx, e⟩ := map_eq_top hπ' f' (LinearMap.ker f.toLinearMap) (fun g y hy => by
    have hy' : f y = 0 := hy
    show f (ρ g y) = 0
    rw [f.isIntertwining, hy', map_zero]) hu hu' (f' w)
  have hx' : f x = 0 := hx
  obtain ⟨v, hv, ev⟩ := IwahoriOnto.exists_fixed_map_eq hρ hK (f.toLinearMap.prod f'.toLinearMap) x fun g hg => by
    have h1 : ρ g w = w := by simpa using hw ⟨g, hg⟩
    refine Prod.ext ?_ ?_
    · show f (ρ g x) = f x
      rw [f.isIntertwining, hx', map_zero]
    · show f' (ρ g x) = f' x
      rw [f'.isIntertwining, e, ← f'.isIntertwining, h1]
  obtain ⟨c, rfl⟩ := hl v hv
  have e1 : f (c • w) = f x := congrArg Prod.fst ev
  have e2 : f' (c • w) = f' x := congrArg Prod.snd ev
  rw [hx', map_smul, smul_eq_zero] at e1
  rw [e1.resolve_right h0, zero_smul, map_zero, e] at e2
  exact h0' e2.symm

theorem equiv_of_line {ρ : Representation ℂ G X} {π : Representation ℂ G V} {π' : Representation ℂ G V'}
    (hρ : IsSmooth ρ) (hπ : π.IsIrreducible) (hπ' : π'.IsIrreducible) {K : Subgroup G} (hK : IsCompact (K : Set G))
    (f : ρ.IntertwiningMap π) (f' : ρ.IntertwiningMap π') {w : X} (hw : w ∈ fixed ρ K) (h0 : f w ≠ 0)
    (h0' : f' w ≠ 0) (hl : ∀ v ∈ fixed ρ K, ∃ c : ℂ, v = c • w) : Nonempty (π.Equiv π') := by
  have hk := le_antisymm (ker_le hρ hπ' hK f f' hw h0 h0' hl) (ker_le hρ hπ hK f' f hw h0' h0 hl)
  have hs : Function.Surjective f.toLinearMap := fun v => by
    obtain ⟨x, -, e⟩ := map_eq_top hπ f ⊤ (fun _ _ _ => trivial) trivial h0 v
    exact ⟨x, e⟩
  have hs' : Function.Surjective f'.toLinearMap := fun v => by
    obtain ⟨x, -, e⟩ := map_eq_top hπ' f' ⊤ (fun _ _ _ => trivial) trivial h0' v
    exact ⟨x, e⟩
  let L : V ≃ₗ[ℂ] V' := (f.toLinearMap.quotKerEquivOfSurjective hs).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hk ≪≫ₗ
    f'.toLinearMap.quotKerEquivOfSurjective hs'
  have hL : ∀ x, L (f x) = f' x := fun x => by
    have : (f.toLinearMap.quotKerEquivOfSurjective hs).symm (f x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [L, LinearEquiv.trans_apply, this]
    rfl
  refine ⟨Representation.Equiv.mk L fun g => LinearMap.ext fun v => ?_⟩
  obtain ⟨x, rfl⟩ := hs v
  show L (π g (f x)) = π' g (L (f x))
  rw [← f.isIntertwining, hL, hL, f'.isIntertwining]

theorem exists_vector {ρ : Representation ℂ G X} {π : Representation ℂ G V} (hρ : IsSmooth ρ) {K : Subgroup G}
    (hK : IsCompact (K : Set G)) (S : Subrepresentation ρ) (f : S.toRepresentation.IntertwiningMap π)
    (hf : Function.Surjective f) (hs : fixed π K ≠ ⊥) :
    ∃ w : S.toSubmodule, w.1 ∈ fixed ρ K ∧ f w ≠ 0 := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
  obtain ⟨u, rfl⟩ := hf v
  have hS : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth (ρ := ρ) ⟨S, .id _, Function.surjective_id⟩ hρ
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hS hK f.toLinearMap u fun h hh => by
    show f (S.toRepresentation h u) = f u
    rw [f.isIntertwining]
    simpa using hv ⟨h, hh⟩
  exact ⟨w, fun g => congrArg Subtype.val (hw g), fun h => hv0 (hfw.symm.trans h)⟩

theorem equiv_of_form {ρ : Representation ℂ G X} {π : Representation ℂ G V} {π' : Representation ℂ G V'}
    (hρ : IsSmooth ρ) (hπ : π.IsIrreducible) (hπ' : π'.IsIrreducible) {K : Subgroup G} (hK : IsCompact (K : Set G))
    (E : X →ₗ[ℂ] ℂ) (hE : ∀ u ∈ fixed ρ K, E u = 0 → u = 0) (h : IsSubquotient π ρ) (h' : IsSubquotient π' ρ)
    (hs : fixed π K ≠ ⊥) (hs' : fixed π' K ≠ ⊥) : Nonempty (π.Equiv π') := by
  obtain ⟨S, f, hf⟩ := h
  obtain ⟨S', f', hf'⟩ := h'
  obtain ⟨w, hw, h0⟩ := exists_vector hρ hK S f hf hs
  obtain ⟨w', hw', h0'⟩ := exists_vector hρ hK S' f' hf' hs'
  have hl : ∀ z ∈ fixed ρ K, z ≠ 0 → ∀ v ∈ fixed ρ K, ∃ c : ℂ, v = c • z := fun z hz hz0 v hv => by
    have hEz : E z ≠ 0 := fun e => hz0 (hE z hz e)
    refine ⟨E v / E z, sub_eq_zero.1 (hE _ (sub_mem hv (Submodule.smul_mem _ _ hz)) ?_)⟩
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hEz, sub_self]
  have hw0 : w.1 ≠ 0 := fun e => h0 (by rw [show w = 0 from Subtype.ext e, map_zero])
  have hw0' : w'.1 ≠ 0 := fun e => h0' (by rw [show w' = 0 from Subtype.ext e, map_zero])
  obtain ⟨c, hc⟩ := hl _ hw' hw0' _ hw
  have hc0 : c ≠ 0 := fun e => hw0 (by rw [hc, e, zero_smul])
  let R : Subrepresentation ρ := ⟨S.toSubmodule ⊓ S'.toSubmodule, fun g _ hv =>
    ⟨S.apply_mem_toSubmodule g hv.1, S'.apply_mem_toSubmodule g hv.2⟩⟩
  have hR : IsSmooth R.toRepresentation :=
    IsSubquotient.isSmooth (ρ := ρ) ⟨R, .id _, Function.surjective_id⟩ hρ
  let F : R.toRepresentation.IntertwiningMap π :=
    ⟨f.toLinearMap ∘ₗ Submodule.inclusion inf_le_left, fun g => LinearMap.ext fun x =>
      f.isIntertwining _ _ g (Submodule.inclusion inf_le_left x)⟩
  let F' : R.toRepresentation.IntertwiningMap π' :=
    ⟨f'.toLinearMap ∘ₗ Submodule.inclusion inf_le_right, fun g => LinearMap.ext fun x =>
      f'.isIntertwining _ _ g (Submodule.inclusion inf_le_right x)⟩
  have hm : w.1 ∈ S'.toSubmodule := hc ▸ Submodule.smul_mem _ _ w'.2
  refine equiv_of_line hR hπ hπ' hK F F' (w := ⟨w.1, w.2, hm⟩) (fun g => Subtype.ext (hw g)) h0 (fun e => ?_)
    fun v hv => ?_
  · have e1 : f' (c • w') = 0 := by
      rw [← e]
      exact congrArg f' (Subtype.ext hc.symm)
    rw [map_smul, smul_eq_zero] at e1
    exact e1.elim hc0 h0'
  · obtain ⟨d, hd⟩ := hl _ hw hw0 v.1 fun g => congrArg Subtype.val (hv g)
    exact ⟨d, Subtype.ext hd⟩

end Abstract

theorem equiv_of_parInd {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (σ : Representation ℂ (Levi k m) ℂ)
    {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {π : Representation ℂ (GL n k) V} {π' : Representation ℂ (GL n k) V'}
    (hπ : π.IsIrreducible) (hπ' : π'.IsIrreducible) (h : IsSubquotient π (parInd e σ))
    (h' : IsSubquotient π' (parInd e σ)) (hs : IsSpherical π) (hs' : IsSpherical π') : Nonempty (π.Equiv π') := by
  let E : IndSp e σ →ₗ[ℂ] ℂ := ⟨⟨fun f => f.1.1 1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  refine equiv_of_form (isSmooth_parInd e σ) hπ hπ' SplitFlip.isCompact_KO E (fun u hu h0 => ?_) h h' hs hs'
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  obtain ⟨p, c, hc, rfl⟩ := MultiIrr.exists_parab_mul e x
  have h1 := congrArg (fun F : IndSp e σ => F.1.1 1) (hu ⟨c, hc⟩)
  simp only [parInd_apply, MonoidHom.one_apply, Units.val_one, one_smul, one_mul] at h1
  have h2 : u.1.1 1 = 0 := h0
  rw [parInd_law, h1, h2, map_zero, smul_zero]
  rfl

theorem equiv_of_hasSatake : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (α : Fin n → ℂˣ) (π π' : IrrRep (GL (Fin n) k)), HasSatake π.ρ α → HasSatake π'.ρ α → Nonempty (π.ρ.Equiv π'.ρ) :=
  fun _ _ _ _ _ _ _ _ _ _ _ h h' => equiv_of_parInd _ _ h.1 h'.1 h.2.2 h'.2.2 h.2.1 h'.2.1

end GlobalTheory.SmGL.SphUniq

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivOfSameSatakeParametersStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_equiv_of_same_satakeParameters : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) (α : Fin n → ℂˣ) (π π' : IrrRep (GL (Fin n) k)), HasSatake π.ρ α → HasSatake π'.ρ α → Nonempty (π.ρ.Equiv π'.ρ) := by
  first | exact @GlobalTheory.SmGL.SphUniq.equiv_of_hasSatake | exact GlobalTheory.SmGL.SphUniq.equiv_of_hasSatake | (intros; apply GlobalTheory.SmGL.SphUniq.equiv_of_hasSatake <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldUnramified
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.HubLoc

theorem localField_unramified : ∀ (D : D7) (i : D.nd.Loc), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), Loc.K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 ∧ (D.nbr i w hw).Kw.1 ≤ Loc.Ks (D.nbr i w hw).Kw 1 ∧ Loc.Good (D.nbr i w hw).Kw 1 (D.nbr i w hw).LL := by
  intro D i hs hq hd w hw
  have h2 : D.nd.l i ≠ 2 := fun e => hs (e ▸ D.host.toHostRaw.two_mem_small)
  have hN : ¬ D.nd.l i ∣ D.host.condN := fun h => by
    rcases (D.host.toHostRaw.dvd_condN_iff_small (Fact.out : (D.nd.l i).Prime)).1 h with h | h | h
    exacts [hs h, hq h, hd h]
  have hK := kw_le_Kur_of_ne i hN w hw
  have h1 := le_Ks_one_of_Kur _ hK
  exact ⟨inf_eq_left.2 hK, h1, (D.self_good i w hw).good_one (D.nbr i w hw).LL_split h2 h1⟩

end GlobalTheory.HubLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldUnramifiedStatement
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.K0_eq_and_good_of_ne : ∀ (D : D7) (i : D.nd.Loc), D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), Loc.K0 (D.nbr i w hw).Kw = (D.nbr i w hw).Kw.1 ∧ (D.nbr i w hw).Kw.1 ≤ Loc.Ks (D.nbr i w hw).Kw 1 ∧ Loc.Good (D.nbr i w hw).Kw 1 (D.nbr i w hw).LL := by
  exact GlobalTheory.HubLoc.localField_unramified
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCycOInvPow
noncomputable section

namespace GlobalTheory.AdmLoc.CycWitness

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct

section Line

variable {G Qp LL R : Type} [Group G] [Field Qp] [Field LL] [Algebra Qp LL] [CommRing R] [Algebra Qp R]

end Line

section Per

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

variable (hK : Function.Surjective (algebraMap Qp K)) (a : ℕ) (θ : G →* LLˣ)
  (hθ : ∀ g, (θ g : LL) = algebraMap Qp LL (((PD.χ g)⁻¹ ^ a : Qpˣ) : Qp))


include hK hθ

end Per

variable {l : ℕ} [Fact l.Prime]

def cycO (P : LocPrime l) (K LL : FinExt l) : ↥(GK K) →* (↥(OL LL))ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => ⟨_, GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.cyc_mem P K LL g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }

theorem cycO_val (P : LocPrime l) (K LL : FinExt l) (g : ↥(GK K)) :
    algebraMap ↥(OL LL) ↥LL.1 (cycO P K LL g) = algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g) := rfl

end GlobalTheory.AdmLoc.CycWitness
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvalSum
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

noncomputable section

namespace GlobalTheory.KFinExp

theorem exists_eval_sum {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    (W : Submodule ℂ (Sm E N)) [FiniteDimensional ℂ W] (l : Module.Dual ℂ W) :
    ∃ a : GA E N →₀ ℂ, ∀ w : W, l w = ∑ x ∈ a.support, a x * w.1.1 x := by
  let ev : GA E N → Module.Dual ℂ W := fun x =>
    (LinearMap.proj x : (GA E N → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (Sm E N).subtype ∘ₗ W.subtype
  have hs : Submodule.span ℂ (Set.range ev) = ⊤ := Submodule.span_eq_top_of_ne_zero fun z hz => by
    by_contra h
    refine hz (Subtype.ext (Subtype.ext (funext fun x => ?_)))
    by_contra hx
    exact h ⟨ev x, ⟨x, rfl⟩, hx⟩
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hs ▸ Submodule.mem_top : l ∈ _)
  refine ⟨a, fun w => ?_⟩
  rw [← ha, Finsupp.sum, LinearMap.sum_apply]
  rfl

theorem exists_expansion (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (φ : Sm E N)
    (hφ : φ ∈ finVec (cptRep E N)) :
    ∃ (r : ℕ) (ψ : Fin r → Sm E N) (C : Fin r → Lie E N → ℂ),
      (∀ j, ψ j ∈ Submodule.span ℂ (Set.range fun k => cptRep E N k φ)) ∧
      (∀ j, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (C j) (oneL E N)) ∧
      ∀ k : Kinf E N, cptRep E N k φ = ∑ j, C j (toL k.1) • ψ j := by
  set W := Submodule.span ℂ (Set.range fun k => cptRep E N k φ)
  have hf : FiniteDimensional ℂ W := hφ
  let b := Module.finBasis ℂ W
  choose a ha using fun j => exists_eval_sum W (b.coord j)
  refine ⟨_, fun j => (b j).1, fun j y => ∑ x ∈ (a j).support, a j x * chart φ.1 x y, fun j => (b j).2,
    fun j => ContDiffAt.sum fun x _ => contDiffAt_const.mul (contDiffAt_chart φ.2 x isUnit_one), fun k => ?_⟩
  let w : W := ⟨cptRep E N k φ, Submodule.subset_span ⟨k, rfl⟩⟩
  have h := congrArg Subtype.val (b.sum_repr w)
  rw [Submodule.coe_sum] at h
  refine h.symm.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [Submodule.coe_smul]
  congr 1
  refine (ha j w).trans (Finset.sum_congr rfl fun x _ => ?_)
  congr 1
  exact (chart_val φ.1 x (Unitary.toUnits k)).symm

end GlobalTheory.KFinExp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowApplySubPowLtOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowApplySubPowLtOne
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem valuation_pow_sub_pow_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {a b : Ω}
    (ha : A.valuation a ≤ 1) (hb : A.valuation b ≤ 1) (hab : A.valuation (a - b) < 1) (k : ℕ) :
    A.valuation (a ^ k - b ^ k) < 1 := by
  rw [← Commute.geom_sum₂_mul (Commute.all a b), map_mul]
  have hs : A.valuation (∑ i ∈ Finset.range k, a ^ i * b ^ (k - 1 - i)) ≤ 1 := by
    apply Valuation.map_sum_le
    intro i _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one' (pow_le_one' ha _) (pow_le_one' hb _)
  exact lt_of_le_of_lt (mul_le_of_le_one_left' hs) hab

theorem frob_pow_apply_sub_lt_one :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω) (q : ℕ) (σ : Ω ≃ₐ[F] Ω),
    Formalism.ConjugateSelfDual.IsFrob A q σ → ∀ (n : ℕ) (x : Ω), A.valuation x ≤ 1 → A.valuation ((σ ^ n) x - x ^ (q ^ n)) < 1 := by
  intro F Ω _ _ _ _ A q σ hσ n
  obtain ⟨hD, hF⟩ := hσ
  have hD' : σ ∈ ReciprocityTheory.Gal.Dec (F := F) A := hD
  have hle : ∀ y : Ω, A.valuation y ≤ 1 → A.valuation (σ y) ≤ 1 := by
    intro y hy
    rw [A.valuation_le_one_iff] at hy ⊢
    exact (ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hD' y).mpr hy
  induction n with
  | zero =>
    intro x _
    simp
  | succ n ih =>
    intro x hx
    have e : (σ ^ (n + 1)) x - x ^ (q ^ (n + 1)) =
        σ ((σ ^ n) x - x ^ (q ^ n)) + ((σ x) ^ (q ^ n) - (x ^ q) ^ (q ^ n)) := by
      rw [pow_succ' σ n, AlgEquiv.mul_apply, map_sub, map_pow, ← pow_mul, ← pow_succ']
      ring
    rw [e]
    refine Valuation.map_add_lt _ ?_ ?_
    · exact (ReciprocityTheory.Gal.valuation_apply_lt_one_iff hD' _).mpr (ih x hx)
    · refine valuation_pow_sub_pow_lt_one A (hle x hx) ?_ (hF x hx) _
      rw [map_pow]; exact pow_le_one' hx _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPowApplySubPowLtOneStatement
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_pow_apply_sub_pow_lt_one : ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω) (q : ℕ) (σ : Ω ≃ₐ[F] Ω),
    Formalism.ConjugateSelfDual.IsFrob A q σ → ∀ (n : ℕ) (x : Ω), A.valuation x ≤ 1 → A.valuation ((σ ^ n) x - x ^ (q ^ n)) < 1 := by
  first | exact @GlobalTheory.frob_pow_apply_sub_lt_one | exact GlobalTheory.frob_pow_apply_sub_lt_one | (intros; apply GlobalTheory.frob_pow_apply_sub_lt_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerApproxUnitAdicCompletion
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerApproxUnitAdicCompletion
open NumberField IsDedekindDomain Polynomial ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
open Neutral.B1 hiding IsPlaceOver

noncomputable section

namespace GlobalTheory

open IsDedekindDomain.HeightOneSpectrum

theorem unit_completion_approx_integer : ∀ {E' : Type} [Field E'] [NumberField E'] (w' : HeightOneSpectrum (𝓞 E'))
    (u : (w'.adicCompletion E')ˣ) (hu : IsUnitAt w' u),
    ∃ x : 𝓞 E', Valued.v ((u : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := by
  intro E' _ _ w' u hu
  have hvF : ∀ z : E', Valued.v (algebraMap E' (w'.adicCompletion E') z) = w'.valuation E' z :=
    fun z => valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' z
  set x : w'.adicCompletion E' := (u : w'.adicCompletion E') with hxdef
  have hx1 : Valued.v x ≤ 1 := by
    have : Valued.v x = 1 := hu
    exact this.le
  have hopen : IsOpen {z : w'.adicCompletion E' | Valued.v (z - x) < 1} := by
    have h1 := Valued.isOpen_ball (w'.adicCompletion E') 1
    have h2 : {z : w'.adicCompletion E' | Valued.v (z - x) < 1} =
        (fun z => z - x) ⁻¹' {w | Valued.v.restrict w < 1} := by
      ext z; simp [Valuation.restrict_lt_one_iff]
    rw [h2]
    exact h1.preimage (continuous_id.sub continuous_const)
  obtain ⟨k, hk⟩ := (denseRange_algebraMap (R := 𝓞 E') (K := E') w').exists_mem_open hopen
    ⟨x, by simp⟩
  simp only [Set.mem_setOf_eq] at hk
  have hk1 : Valued.v (algebraMap E' (w'.adicCompletion E') k) ≤ 1 := by
    have : algebraMap E' (w'.adicCompletion E') k =
        (algebraMap E' (w'.adicCompletion E') k - x) + x := by ring
    rw [this]
    exact Valuation.map_add_le _ hk.le hx1
  have hk1' : w'.valuation E' k ≤ 1 := by
    rw [← hvF]; exact hk1
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer (K := E') w' hk1' 1
  refine ⟨a, ?_⟩
  have e1 : x - algebraMap E' (w'.adicCompletion E') (a : E') =
      (x - algebraMap E' (w'.adicCompletion E') k) +
      (algebraMap E' (w'.adicCompletion E') k - algebraMap E' (w'.adicCompletion E') (a : E')) := by
    ring
  rw [e1]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [← Valuation.map_neg, neg_sub]; exact hk
  · rw [← map_sub, hvF]
    have : w'.valuation E' ((a : E') - k) < 1 := by simpa using ha
    rw [← Valuation.map_neg, neg_sub]; exact this

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerApproxUnitAdicCompletionStatement
open NumberField IsDedekindDomain Polynomial ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
open Neutral.B1 hiding IsPlaceOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_approx_unit_adicCompletion : ∀ {E' : Type} [Field E'] [NumberField E'] (w' : HeightOneSpectrum (𝓞 E'))
    (u : (w'.adicCompletion E')ˣ) (hu : IsUnitAt w' u),
    ∃ x : 𝓞 E', Valued.v ((u : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := by
  first | exact @GlobalTheory.unit_completion_approx_integer | exact GlobalTheory.unit_completion_approx_integer | (intros; apply GlobalTheory.unit_completion_approx_integer <;> assumption)
end
end
