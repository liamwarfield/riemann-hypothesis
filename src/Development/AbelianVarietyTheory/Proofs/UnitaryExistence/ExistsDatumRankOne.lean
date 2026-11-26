module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FinrankInt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PointEqIffIsometryClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExpFourClauses
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumRankOne
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

namespace GlobalTheory.RankOneDatum

theorem selfDual_of_perfect {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Submodule (𝓞 E) E) (ξ : E)
    (hfg : A.FG) (hne : A ≠ ⊥)
    (h : ∀ x : E, (∀ a ∈ A, ∀ b ∈ A, ∃ z : ℤ,
      Algebra.trace ℚ E (ξ * x * a * IsCMField.complexConj E b) = z) ↔ IsIntegral ℤ x) (x : E) :
    (∀ y ∈ A, ∃ n : ℤ, Algebra.trace ℚ E (ξ * x * IsCMField.complexConj E y) = n) ↔ x ∈ A := by
  constructor
  · intro hx
    let I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E := ⟨A, FractionalIdeal.isFractional_of_fg hfg⟩
    have hI : I ≠ 0 := fun h0 => hne (FractionalIdeal.coeToSubmodule_eq_bot.2 h0)
    have hc : ∀ c ∈ I⁻¹, IsIntegral ℤ (x * c) := fun c hc => (h _).1 fun a ha b hb => by
      have h1 : c * a ∈ I⁻¹ * I := FractionalIdeal.mul_mem_mul hc ha
      rw [inv_mul_cancel₀ hI, FractionalIdeal.mem_one_iff] at h1
      obtain ⟨u, hu⟩ := h1
      obtain ⟨n, hn⟩ := hx _ (A.smul_mem (IsCMField.ringOfIntegersComplexConj E u) hb)
      refine ⟨n, ?_⟩
      rw [← hn, Algebra.smul_def]
      congr 1
      have e : algebraMap (𝓞 E) E (IsCMField.ringOfIntegersComplexConj E u) = IsCMField.complexConj E (c * a) := by
        rw [← hu]; rfl
      rw [e, map_mul (IsCMField.complexConj E) _ b, IsCMField.complexConj_apply_apply]
      ring
    have h1 : (1 : E) ∈ I⁻¹ * I := by
      rw [inv_mul_cancel₀ hI]
      exact FractionalIdeal.one_mem_one _
    have h2 : x * 1 ∈ A := by
      refine FractionalIdeal.mul_induction_on (C := fun w => x * w ∈ A) h1 (fun c hc' a ha => ?_)
        (fun u v hu hv => ?_)
      · rw [← mul_assoc]
        exact A.smul_mem (⟨x * c, hc c hc'⟩ : 𝓞 E) ha
      · rw [mul_add]
        exact A.add_mem hu hv
    rwa [mul_one] at h2
  · intro hx y hy
    simpa using (h 1).2 isIntegral_one x hx y hy


set_option maxHeartbeats 1000000 in
theorem exists_datum_of_rt (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E)
    (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) (hrt0 : H.rt0 = D.host.φ₀ D.host.sqrtMinusD) :
    ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0 := by
  obtain ⟨A, hfg, hne, h⟩ := GlobalTheory.principalDatum_trace_perfect D
  have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hc : IsCMField.complexConj D.host.E D.host.sqrtMinusD = -D.host.sqrtMinusD := by
    apply D.host.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj, map_neg, hφ]
    simp
  have hN : (0 : ℝ) < (Ideal.absNorm D.host.ccK : ℕ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0))
  have hd : (0 : ℝ) < Real.sqrt D.host.d := by
    rw [Real.sqrt_pos, Nat.cast_pos, Nat.pos_iff_ne_zero]
    intro h0
    have h1 := H.sqrt_neg_disc_sq
    rw [hrt0, hφ, h0] at h1
    have h2 : (H.d : ℂ) = 0 := by simpa using h1
    exact H.d_prime.ne_zero (by exact_mod_cast h2)
  obtain ⟨D₁, -, hp, hq, -⟩ := GlobalTheory.CM.SelfDualDatum.exists_datum D.host.E H A (-D.host.xi0) hfg hne
    (by
      unfold Formalism.BasicNotions.Host.xi0
      rw [map_neg, map_div₀, map_mul, hc, map_neg, map_one, map_natCast, mul_neg, div_neg])
    (fun τ hτ => by
      rw [hrt, hrt0, hφ] at hτ
      unfold Formalism.BasicNotions.Host.xi0
      rw [map_neg, map_div₀, map_mul, hτ, map_neg, map_one, map_natCast]
      generalize Ideal.absNorm D.host.ccK = N at hN ⊢
      generalize Real.sqrt D.host.d = s at hd ⊢
      have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      have e : -(-1 / ((N : ℂ) * (Complex.I * (s : ℂ)))) = ((-(1 / (N * s)) : ℝ) : ℂ) * Complex.I := by
        push_cast
        field_simp
        simp
      rw [e, Complex.mul_I_im, Complex.ofReal_re, neg_lt_zero]
      positivity)
    (fun x => by
      rw [← selfDual_of_perfect A D.host.xi0 hfg hne h x]
      refine forall₂_congr fun y _ => ?_
      rw [neg_mul, neg_mul, map_neg]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨-n, by rw [Int.cast_neg, ← hn, neg_neg]⟩
      · rintro ⟨n, hn⟩
        exact ⟨-n, by rw [Int.cast_neg, hn]⟩)
  exact ⟨D₁, hp, hq⟩

theorem exists_datum_rank_one : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (V : HSp D) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0 :=
  fun D H _ _ _ h _ => exists_datum_of_rt D H h.rt h.rt0

end GlobalTheory.RankOneDatum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsPeriodCompIsometry
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.ClassUniq

lemma isHolTo_ex {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo σ' ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di k) ty P) :
    IsHolTo Set.univ (fun z => (F.ex k P z).left) := by
  have h1 := (F.hol k 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  unfold IsHolTo at h1 ⊢
  intro U f
  obtain ⟨ho, hd⟩ := h1 U f
  have hj : Continuous (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) := continuous_const.prodMk continuous_id
  have hjd : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) :=
    (differentiable_const _).prodMk differentiable_id
  have hset : {b | b ∈ (Set.univ : Set (Fin g → ℂ)) ∧ ⊤ ≤ (fun z => (F.ex k P z).left) b ⁻¹ᵁ U} =
      (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) ⁻¹'
        {b | b ∈ (Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ)) ∧
          ⊤ ≤ (fun bz : (Fin 0 → ℂ) × (Fin g → ℂ) => (F.ex k P bz.2).left) b ⁻¹ᵁ U} := by
    ext z
    simp
  rw [hset]
  refine ⟨ho.preimage hj, ?_⟩
  have h2 := hd.comp (s := (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) ⁻¹'
      {b | b ∈ (Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ)) ∧
        ⊤ ≤ (fun bz : (Fin 0 → ℂ) × (Fin g → ℂ) => (F.ex k P bz.2).left) b ⁻¹ᵁ U})
    hjd.differentiableOn (fun _ hz => hz)
  rw [Function.comp_def] at h2
  dsimp only at h2 ⊢
  exact h2

lemma isPeriod_comp_isometry {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D D' : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (gam : D.La ≃ₗ[𝓞 E] D'.La) (hg : ∀ a b, D'.EF (gam a) (gam b) = D.EF a b)
    {P' : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D' ty P') :
    IsPeriod D ty (P'.comp gam.toLinearMap.toAddMonoidHom) := by
  unfold IsPeriod at hP ⊢
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, him⟩ := hP
  have hrange : (P'.comp gam.toLinearMap.toAddMonoidHom).range = P'.range := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨gam a, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨gam.symm b, by simp⟩
  have hr2 : Set.range (P'.comp gam.toLinearMap.toAddMonoidHom) = Set.range P' := by
    rw [← AddMonoidHom.coe_range, ← AddMonoidHom.coe_range, hrange]
  refine ⟨?_, ?_, ?_, ?_, Hm, hH, hpos, ?_⟩
  · intro a x i
    show P' (gam (a • x)) i = (ty i) (a : E) * P' (gam x) i
    rw [map_smul]
    exact hlin a (gam x) i
  · intro a b hab
    exact gam.injective (hinj hab)
  · rw [hrange]
    exact hdisc
  · rw [hr2]
    exact hspan
  · intro x y
    have h := him (gam x) (gam y)
    rw [hg] at h
    exact h

theorem eq_of_matched : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (r : ℕ) (M : FrameUnif.ModelsOf F r) (k k' : Fin F.n) (γ : GL (Fin r) E), 1 ≤ Dw.p + Dw.q → σ' (baseKA l).ρ = H.rt0 → IsTypeFn H Dw.p Dw.q ty → ModelBase M → (M.X k').Gm = (M.X k).Gm → (M.X k').ξ0 = (M.X k).ξ0 → (∀ u v, herm (M.X k).Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm (M.X k).Gm u v) → (∀ v, v ∈ (M.X k).Λ ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ (M.X k').Λ) → (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ w ∈ (M.X k').Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k (F.t k a) : Fin r → E) = (M.φ k' (F.t k' a) : Fin r → E) + l.M • w) → (∀ a, ∃ w ∈ (M.X k').Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k (F.t k a) : Fin r → E) = (M.φ k' (F.t k' a) : Fin r → E) + l.A • w) → k = k' := by
  intro hT hL E _ _ _ H Dw l Xo σ' g ty F r M k k' γ hpq hρ hty hMB hGm hξ hunit hΛ hcM hcA
  have hmem : ∀ a : (F.Di k).La,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ ((M.φ k a : (M.X k).Λ) : Fin r → E) ∈ (M.X k').Λ :=
    fun a => (hΛ _).1 (M.φ k a).2
  let gmap : (F.Di k).La →ₗ[𝓞 E] (F.Di k').La :=
    (M.φ k').symm.toLinearMap ∘ₗ LinearMap.codRestrict (M.X k').Λ
      (((Matrix.mulVecLin (γ : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E)) ∘ₗ
        (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap) (fun a => hmem a)
  have hgmap : ∀ a, ((M.φ k' (gmap a) : (M.X k').Λ) : Fin r → E) =
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) := by
    intro a
    simp only [gmap, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rfl
  have hinv : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * (γ : Matrix (Fin r) (Fin r) E) = 1 :=
    Units.inv_mul γ
  have hinv' : (γ : Matrix (Fin r) (Fin r) E) * ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = 1 :=
    Units.mul_inv γ
  have hinj : Function.Injective gmap := by
    intro a b hab
    have h1 := congrArg (fun x => ((M.φ k' x : (M.X k').Λ) : Fin r → E)) hab
    simp only [hgmap] at h1
    have h2 := congrArg (fun v => ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) h1
    simp only [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at h2
    exact (M.φ k).injective (Subtype.ext h2)
  have hsurj : Function.Surjective gmap := by
    intro b
    have hAv : (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        ((M.φ k' b : (M.X k').Λ) : Fin r → E)) = ((M.φ k' b : (M.X k').Λ) : Fin r → E) := by
      rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
    have hvmem : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ
        ((M.φ k' b : (M.X k').Λ) : Fin r → E) ∈ (M.X k).Λ := by
      rw [hΛ, hAv]
      exact (M.φ k' b).2
    refine ⟨(M.φ k).symm ⟨_, hvmem⟩, ?_⟩
    apply (M.φ k').injective
    apply Subtype.ext
    rw [hgmap, LinearEquiv.apply_symm_apply]
    exact hAv
  let gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k').La := LinearEquiv.ofBijective gmap ⟨hinj, hsurj⟩
  have hgam : ∀ a, ((M.φ k' (gam a) : (M.X k').Λ) : Fin r → E) =
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ (M.φ k a : Fin r → E) := fun a => hgmap a
  have hiso : ∀ a b, (F.Di k').EF (gam a) (gam b) = (F.Di k).EF a b := by
    intro a b
    have h1 := hMB.ef k' (gam a) (gam b)
    have h2 := hMB.ef k a b
    rw [hgam, hgam, hGm, hξ, hunit] at h1
    exact_mod_cast h1.trans h2.symm
  have hcM' : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ x, gam (F.t k a) = F.t k' a + l.M • x := by
    intro a ha
    obtain ⟨w, hw, hweq⟩ := hcM a ha
    refine ⟨(M.φ k').symm ⟨w, hw⟩, ?_⟩
    apply (M.φ k').injective
    apply Subtype.ext
    rw [hgam, hweq]
    simp
  have hcA' : ∀ a, ∃ x, gam (F.t k a) = F.t k' a + l.A • x := by
    intro a
    obtain ⟨w, hw, hweq⟩ := hcA a
    refine ⟨(M.φ k').symm ⟨w, hw⟩, ?_⟩
    apply (M.φ k').injective
    apply Subtype.ext
    rw [hgam, hweq]
    simp
  have htyk' : IsTypeFn H (F.Di k').p (F.Di k').q ty := by
    rw [(F.sig k').1, (F.sig k').2]
    exact hty
  obtain ⟨P', hP'⟩ := (GlobalTheory.PeriodExists.period_of_isTypeFn H (F.Di k') g ty htyk').2
  have hP := isPeriod_comp_isometry gam hiso hP'
  have key := GlobalTheory.UnifPoint.point_eq_iff_isometry_closed hT hL E H Dw l Xo σ' g ty hpq hρ hty
    (F.Di k) (F.Di k') (F.t k) (F.t k') (P'.comp gam.toLinearMap.toAddMonoidHom) P'
    (F.u k (P'.comp gam.toLinearMap.toAddMonoidHom)) (F.u k' P')
    (F.ex k (P'.comp gam.toLinearMap.toAddMonoidHom)) (F.ex k' P')
    ⟨F.over_σ k _ hP, hP, ⟨F.ex_add k _ hP, F.ex_onto k _ hP, isHolTo_ex F k _ hP, (F.ex_diff k _ hP).1,
      (F.ex_diff k _ hP).2⟩, F.ex_ker k _ hP, F.ex_lin k _ hP, F.ex_weil k _ hP, F.ex_eta k _ hP,
      F.ex_etaA k _ hP⟩
    ⟨F.over_σ k' _ hP', hP', ⟨F.ex_add k' _ hP', F.ex_onto k' _ hP', isHolTo_ex F k' _ hP',
      (F.ex_diff k' _ hP').1, (F.ex_diff k' _ hP').2⟩, F.ex_ker k' _ hP', F.ex_lin k' _ hP',
      F.ex_weil k' _ hP', F.ex_eta k' _ hP', F.ex_etaA k' _ hP'⟩
  have hu := key.2 ⟨gam, LinearEquiv.refl ℂ _, hiso, hcM', hcA', fun a => rfl⟩
  exact F.disj k k' _ _ hP hP' hu

end GlobalTheory.ClassUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntAll
namespace GlobalTheory.IntegralFrames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem intAll : PartI → N1ab → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → Formalism.L2.PjFree.IntAll Xo c := by
  intro hI hA hB hT E _ _ _ H Dw l Xo c hpq hg
  exact Formalism.L2.PjFree.intAll_of' (GlobalTheory.T.intFrExt_of_good_level hI hA hB hT E H Dw l Xo c hpq hg)
    (fun S S' _ _ _ _ φ y => GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hB E H Dw l Xo c S S' φ y)
    (fun S _ x _ v hv _ w A N w' hw hw' => GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S x v hv w A N w' hw hw')
    (GlobalTheory.T.integralFrame_change_integral_invertible_matrix hB E H Dw l Xo c)

end GlobalTheory.IntegralFrames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralAlgebraicFramedPointExists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem integralAlgebraicFramedPoint_exists : PartI → N1ab → N1c → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → IntFrNe Xo c (Formalism.L2.PjFree.algCls Xo c) :=
  fun hP hab hc hB hT E _ _ _ H Dw l Xo c hpq hg =>
    intFrNe_of (GlobalTheory.T.algebraicPoints_moduli_every_place hc E H Dw l Xo c hpq) (GlobalTheory.T.intFrExt_of_good_level hP hab hB hT E H Dw l Xo c hpq hg)

end GlobalTheory
end
