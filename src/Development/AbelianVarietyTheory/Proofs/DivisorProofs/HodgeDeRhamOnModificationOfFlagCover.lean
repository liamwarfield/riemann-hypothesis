module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerMatrixFirstOrderDeformation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerTangentVectorsLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerTangentVectorsLift
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagTan

theorem le_preimage_of_trivSqZeroExt {L M : Type} [Field L] [AddCommGroup M] [Module L M] [Module Lᵐᵒᵖ M]
    [IsCentralScalar L M] {T : Scheme.{0}} (φ : TrivSqZeroExt L M →+* L) (hφ : ∀ a, φ a = a.fst)
    (x : Sp (TrivSqZeroExt L M) ⟶ T) (V : T.Opens) (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  let q : PrimeSpectrum L := ⟨⊥, Ideal.isPrime_bot⟩
  have hp : (spMap φ) q = s := by
    refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
    change φ a ∈ (⊥ : Ideal L) ↔ a ∈ s.asIdeal
    rw [Ideal.mem_bot, hφ]
    constructor
    · intro ha
      refine s.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by
        rw [pow_two, show a = TrivSqZeroExt.inr a.snd from TrivSqZeroExt.ext ha rfl, TrivSqZeroExt.inr_mul_inr]]
      exact s.asIdeal.zero_mem
    · intro ha
      by_contra h0
      exact s.2.ne_top (s.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
  have h₁ : (spMap φ ≫ x) q ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

theorem IsKS.sum_of_der : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K} (hy : KSIso (psiSet H) y)
    {ι : Type} [Fintype ι] {x : ι → (Sp (DualNumber K) ⟶ Xo.X)} (hx : ∀ a, GlobalTheory.FlagTan.IsTanX y (x a))
    {Mx : ι → HIx Dw (psiSet H) → K} (hM : ∀ a, GlobalTheory.FlagTan.IsKS (psiSet H) y (x a) (Mx a))
    {x' : Sp (DualNumber K) ⟶ Xo.X} (hx' : GlobalTheory.FlagTan.IsTanX y x') (m : ι → K)
    (h : ∀ (O : Xo.X.Opens) (f : Γ(Xo.X, O)) (h' : ⊤ ≤ x' ⁻¹ᵁ O) (hc : ∀ a, ⊤ ≤ x a ⁻¹ᵁ O),
      (evalPt x' O h' f).snd = ∑ a, m a * (evalPt (x a) O (hc a) f).snd), GlobalTheory.FlagTan.IsKS (psiSet H) y x' (∑ a, m a • Mx a) := by
  intro E _ _ _ H Dw l Xo c K _ _ y hy ι _ x hx Mx hM x' hx' m h
  obtain ⟨X, -, hXy, hX⟩ := hy
  have ex : ∀ a, x a = spMap (dir c (Mx a)).toRingHom ≫ X := fun a => ((hX _ (hx a)).2 _).1 (hM a)
  refine ((hX x' hx').2 _).2 ?_
  obtain ⟨U, hU, hpU, -⟩ := Opens.isBasis_iff_nbhd.1 Xo.X.isBasis_affineOpens
    (Opens.mem_top (y.x (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)))
  have hyU : ⊤ ≤ y.x ⁻¹ᵁ U := fun s _ => by
    have : s = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) := Subsingleton.elim _ _
    subst this
    exact hpU
  have hXU : ⊤ ≤ X ⁻¹ᵁ U :=
    le_preimage_of_trivSqZeroExt (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).toRingHom (fun _ => rfl) X U
      (by rw [hXy]; exact hyU)
  have htan : ∀ z : Sp (DualNumber K) ⟶ Xo.X, IsTanX y z → ⊤ ≤ z ⁻¹ᵁ U := fun z hz =>
    le_preimage_of_trivSqZeroExt (red c K).toRingHom (fun _ => rfl) z U (by rw [hz.2]; exact hyU)
  have hev : ∀ (N : HIx Dw (psiSet H) → K) (z : Sp (DualNumber K) ⟶ Xo.X)
      (hz : z = spMap (dir c N).toRingHom ≫ X) (hzU : ⊤ ≤ z ⁻¹ᵁ U) (f : Γ(Xo.X, U)),
      evalPt z U hzU f = dir c N (evalPt X U hXU f) := by
    intro N z hz hzU f
    subst hz
    exact evalPt_spMap_comp _ X U hXU hzU f
  have hx'U := htan x' hx'
  have hcU : ∀ a, ⊤ ≤ x a ⁻¹ᵁ U := fun a => htan _ (hx a)
  set M'' : HIx Dw (psiSet H) → K := ∑ a, m a • Mx a
  have hzU : ⊤ ≤ (spMap (dir c M'').toRingHom ≫ X) ⁻¹ᵁ U := by
    intro s hs
    exact hXU (Set.mem_univ _)
  refine ext_evalPt hU hx'U hzU (RingHom.ext fun f => ?_)
  rw [hev M'' _ rfl hzU f]
  refine TrivSqZeroExt.ext ?_ ?_
  · have e1 := evalPt_spMap_comp (red c K).toRingHom x' U hx'U (by rw [hx'.2]; exact hyU) f
    have e2 := evalPt_spMap_comp (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).toRingHom X U hXU
      (by rw [hXy]; exact hyU) f
    simp only [hx'.2, hXy] at e1 e2
    rw [fst_dir]
    exact e1.symm.trans e2
  · rw [h U f hx'U hcU, snd_dir]
    simp only [fun a => hev (Mx a) (x a) (ex a) (hcU a) f, snd_dir, M'', Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.FlagTan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerTangentVectorsLiftStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodaira_spencer_tangent_vectors_lift : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K} (hy : KSIso (psiSet H) y)
    {ι : Type} [Fintype ι] {x : ι → (Sp (DualNumber K) ⟶ Xo.X)} (hx : ∀ a, GlobalTheory.FlagTan.IsTanX y (x a))
    {Mx : ι → HIx Dw (psiSet H) → K} (hM : ∀ a, GlobalTheory.FlagTan.IsKS (psiSet H) y (x a) (Mx a))
    {x' : Sp (DualNumber K) ⟶ Xo.X} (hx' : GlobalTheory.FlagTan.IsTanX y x') (m : ι → K)
    (h : ∀ (O : Xo.X.Opens) (f : Γ(Xo.X, O)) (h' : ⊤ ≤ x' ⁻¹ᵁ O) (hc : ∀ a, ⊤ ≤ x a ⁻¹ᵁ O),
      (evalPt x' O h' f).snd = ∑ a, m a * (evalPt (x a) O (hc a) f).snd), GlobalTheory.FlagTan.IsKS (psiSet H) y x' (∑ a, m a • Mx a) := by
  first | exact @GlobalTheory.FlagTan.IsKS.sum_of_der | exact GlobalTheory.FlagTan.IsKS.sum_of_der | (intros; apply GlobalTheory.FlagTan.IsKS.sum_of_der <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomDualNumberSndEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomDualNumberSndEqZero
namespace GlobalTheory

open Polynomial

theorem ringHom_dualNumber_snd_eq_zero (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F]
    {R : Type} [CommRing R] (φ : F →+* DualNumber R) (a : F) : (φ a).snd = 0 := by
  classical
  let ψ : F →+* R := (TrivSqZeroExt.fstHom R R R).toRingHom.comp φ
  have hψ : ∀ x, ψ x = (φ x).fst := fun x => rfl
  have hcomp : φ.comp (algebraMap ℚ F) =
      (TrivSqZeroExt.inlHom R R).comp (ψ.comp (algebraMap ℚ F)) := RingHom.ext_rat _ _
  have hint : IsIntegral ℚ a := Algebra.IsIntegral.isIntegral a
  have hsep : (minpoly ℚ a).Separable := (minpoly.irreducible hint).separable
  have hf0 : aeval a (minpoly ℚ a) = 0 := minpoly.aeval ℚ a
  have hd : aeval a (derivative (minpoly ℚ a)) ≠ 0 := hsep.aeval_derivative_ne_zero hf0
  have hu : IsUnit (ψ (aeval a (derivative (minpoly ℚ a)))) := (isUnit_iff_ne_zero.mpr hd).map ψ
  have hsplit : φ a = TrivSqZeroExt.inl (φ a).fst + TrivSqZeroExt.inr (φ a).snd :=
    (TrivSqZeroExt.inl_fst_add_inr_snd_eq _).symm
  have hsq : (TrivSqZeroExt.inr (φ a).snd : DualNumber R) ^ 2 = 0 := by
    rw [sq, TrivSqZeroExt.inr_mul_inr]
  have hev : ∀ p : ℚ[X], (p.map (φ.comp (algebraMap ℚ F))).eval (TrivSqZeroExt.inl (φ a).fst) =
      TrivSqZeroExt.inl (ψ (aeval a p)) := by
    intro p
    rw [hcomp, eval_map, aeval_def, ← hψ, Polynomial.hom_eval₂]
    change eval₂ _ (TrivSqZeroExt.inlHom R R (ψ a)) p = TrivSqZeroExt.inlHom R R _
    rw [Polynomial.hom_eval₂]
  have hlhs : ((minpoly ℚ a).map (φ.comp (algebraMap ℚ F))).eval (φ a) = 0 := by
    rw [eval_map, ← Polynomial.hom_eval₂, ← aeval_def, hf0, map_zero]
  have key := eval_add_of_sq_eq_zero ((minpoly ℚ a).map (φ.comp (algebraMap ℚ F)))
    (TrivSqZeroExt.inl (φ a).fst) (TrivSqZeroExt.inr (φ a).snd) hsq
  rw [← hsplit, hlhs, derivative_map, hev, hev, hf0, map_zero] at key
  have h2 := congrArg TrivSqZeroExt.snd key
  simp only [TrivSqZeroExt.snd_zero, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    DualNumber.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_inr,
    mul_zero, zero_add, add_zero] at h2
  exact (hu.mul_right_eq_zero).mp h2.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomDualNumberSndEqZeroStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_numberField_dualNumber_snd_eq_zero : ∀ (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] {R : Type} [CommRing R] (φ : F →+* DualNumber R) (a : F), (φ a).snd = 0 := by
  first | exact @GlobalTheory.ringHom_dualNumber_snd_eq_zero | exact GlobalTheory.ringHom_dualNumber_snd_eq_zero | (intros; apply GlobalTheory.ringHom_dualNumber_snd_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartFrameDeformationOfDerivationCombinati
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartFrameDeformationOfDerivationCombinati
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem GlobalTheory.HorFrame.exists_deform_of_comb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (k : X.F.J) {W₁ : M.X.Opens} (hW₁ : IsAffineOpen W₁) (hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k) [Algebra c.F Γ(M.X, W₁)] (Q₀ : FrPt Xo c Γ(M.X, W₁)), X.F.ChartFr k _ hk₁ Q₀ → ∀ {ι : Type} [Fintype ι] (d : ι → (Γ(M.X, W₁) →+* DualNumber Γ(M.X, W₁))), (∀ a s, (d a s).fst = s) → ∀ (Mx : ι → HIx Dw (psiSet H) → Γ(M.X, W₁)), (∀ a (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →ₐ[c.F] K) (y' : FrPt Xo c K), FrMap ψ Q₀ y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ spMap (d a) ≫ Q₀.x) (ψ ∘ Mx a)) → ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →+* K) (hk : ⊤ ≤ ((spMap ψ ≫ tau hW₁) ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K), X.F.ChartFr k _ hk Q → ∀ (θ : Γ(M.X, W₁) →+* DualNumber K) (m : ι → K), (∀ s, (θ s).fst = ψ s) → (∀ s, (θ s).snd = ∑ a, m a * ψ (d a s).snd) → ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧ GlobalTheory.FlagTan.IsKS (psiSet H) Q w.x (∑ a, m a • (ψ ∘ Mx a)) ∧ spMap θ ≫ tau hW₁ ≫ toFlag M = X.ptY w := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS k W₁ hW₁ hk₁ _ Q₀ hQ₀ ι _ d hd Mx hMx K _ _ ψ hk Q hQ θ m hθ1 hθ2
  haveI := c.fin
  have hinj : ∀ {A B : Type} [CommRing A] [CommRing B] (f g : A →+* B), spMap f = spMap g → f = g := by
    intro A B _ _ f g h
    have := Spec.map_injective h
    exact congrArg CommRingCat.Hom.hom this
  have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  have hjs : ∀ {T : Type} [CommRing T] [Algebra c.F T] (P : FrPt Xo c T),
      frX P ≫ Y.j ≫ Y.s = spMap (algebraMap c.F T) := by
    intro T _ _ P
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, frX_snd,
      hid, Category.comp_id]
  have e1 : frX Q ≫ Y.j = spMap ψ ≫ frX Q₀ ≫ Y.j := by
    rw [hQ.over, hQ₀.over]; simp only [Category.assoc]
  have hψα : ψ.comp (algebraMap c.F Γ(M.X, W₁)) = algebraMap c.F K := by
    have h2 := congrArg (· ≫ Y.s) e1
    simp only [Category.assoc] at h2
    rw [hjs Q, hjs Q₀, spMap_comp'] at h2
    exact (hinj _ _ h2).symm

  let ψA : Γ(M.X, W₁) →ₐ[c.F] K := ⟨ψ, fun r => RingHom.congr_fun hψα r⟩
  have hfrX : frX Q = spMap ψ ≫ frX Q₀ := by
    refine xF_ext (Y := Y) (frX_snd Q) ?_ (by rw [e1, Category.assoc])
    rw [Category.assoc, frX_snd, spMap_comp', hψα]
  have hQx : Q.x = spMap ψ ≫ Q₀.x := by
    rw [← frX_fst, hfrX, Category.assoc, frX_fst]
  have hFQ : FrMap ψA Q₀ Q := by
    obtain ⟨Q', hQ'⟩ := exists_frMap ψA Q₀
    have hc := hQ₀.frMap hQ' (z' := (spMap ψ ≫ tau hW₁) ≫ toFlag M) (by simp only [Category.assoc]) hk
    rwa [hc.unique hQ] at hQ'

  have hdu : ∀ φ : Γ(M.X, W₁) →+* DualNumber K, (∀ s, (φ s).fst = ψ s) →
      φ.comp (algebraMap c.F Γ(M.X, W₁)) = algebraMap c.F (DualNumber K) := by
    intro φ hφ
    refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
    · rw [RingHom.comp_apply, hφ, ← RingHom.comp_apply, hψα]; simp [TrivSqZeroExt.algebraMap_eq_inl']
    · rw [GlobalTheory.T.ringHom_numberField_dualNumber_snd_eq_zero c.F (φ.comp (algebraMap c.F _)) a]; simp [TrivSqZeroExt.algebraMap_eq_inl']
  let θA : Γ(M.X, W₁) →ₐ[c.F] DualNumber K := ⟨θ, fun r => RingHom.congr_fun (hdu θ hθ1) r⟩
  obtain ⟨w, hw⟩ := exists_frMap θA Q₀
  have hwc : X.F.ChartFr k (spMap θ ≫ tau hW₁ ≫ toFlag M) (le_preimage_comp _ hk₁) w :=
    hQ₀.frMap hw rfl _
  have hwpt : spMap θ ≫ tau hW₁ ≫ toFlag M = X.ptY w := FlagCover.eq_ptY hwc.lies
  have hwx : w.x = spMap θ ≫ Q₀.x := by
    rw [← frX_fst, ← frX_frMap hw, Category.assoc, frX_fst]
  have hred : (GlobalTheory.FlagTan.red c K).toRingHom.comp θ = ψ := RingHom.ext fun s => hθ1 s
  have hdef : IsDef Q w := by
    obtain ⟨Q', hQ'⟩ := exists_frMap (GlobalTheory.FlagTan.red c K) w
    have hc := hwc.frMap hQ' (z' := (spMap ψ ≫ tau hW₁) ≫ toFlag M)
      (by rw [← Category.assoc, spMap_comp', hred]; simp only [Category.assoc]) hk
    show FrMap _ w Q
    rwa [hc.unique hQ] at hQ'

  have hθc1 : ∀ a s, (((dualMap ψ).comp (d a)) s).fst = ψ s := by
    intro a s; simp [dualMap, hd]
  have hTan : ∀ φ : Γ(M.X, W₁) →+* DualNumber K, (∀ s, (φ s).fst = ψ s) →
      GlobalTheory.FlagTan.IsTanX Q (spMap φ ≫ Q₀.x) := by
    intro φ hφ
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, Q₀.x_over]
      unfold sOf
      rw [spMap_comp', ← RingHom.comp_assoc, hdu φ hφ]
    · rw [← Category.assoc, spMap_comp', hQx]
      have : (GlobalTheory.FlagTan.red c K).toRingHom.comp φ = ψ := RingHom.ext fun s => hφ s
      rw [this]
  have hKSa : ∀ a, GlobalTheory.FlagTan.IsKS (psiSet H) Q (spMap ((dualMap ψ).comp (d a)) ≫ Q₀.x) (ψ ∘ Mx a) := by
    intro a
    have := hMx a K ψA Q hFQ
    rwa [← Category.assoc, spMap_comp'] at this
  refine ⟨w, hdef, ?_, hwpt⟩
  rw [hwx]
  refine GlobalTheory.T.kodaira_spencer_tangent_vectors_lift (hKS K Q) (x := fun a => spMap ((dualMap ψ).comp (d a)) ≫ Q₀.x)
    (fun a => hTan _ (hθc1 a)) hKSa (hTan θ hθ1) m ?_
  intro O f h' hc
  exact GlobalTheory.T.evalRingPoint_dualNumber_snd_linear_derivation Q₀.x ψ (fun a => (dualMap ψ).comp (d a)) θ m hθc1 hθ1
    (fun s => by rw [hθ2 s]; simp [dualMap]) O f h' hc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartFrameDeformationOfDerivationCombinatiStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_frame_deformation_of_derivation_combination : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (k : X.F.J) {W₁ : M.X.Opens} (hW₁ : IsAffineOpen W₁) (hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k) [Algebra c.F Γ(M.X, W₁)] (Q₀ : FrPt Xo c Γ(M.X, W₁)), X.F.ChartFr k _ hk₁ Q₀ → ∀ {ι : Type} [Fintype ι] (d : ι → (Γ(M.X, W₁) →+* DualNumber Γ(M.X, W₁))), (∀ a s, (d a s).fst = s) → ∀ (Mx : ι → HIx Dw (psiSet H) → Γ(M.X, W₁)), (∀ a (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →ₐ[c.F] K) (y' : FrPt Xo c K), FrMap ψ Q₀ y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ spMap (d a) ≫ Q₀.x) (ψ ∘ Mx a)) → ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →+* K) (hk : ⊤ ≤ ((spMap ψ ≫ tau hW₁) ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K), X.F.ChartFr k _ hk Q → ∀ (θ : Γ(M.X, W₁) →+* DualNumber K) (m : ι → K), (∀ s, (θ s).fst = ψ s) → (∀ s, (θ s).snd = ∑ a, m a * ψ (d a s).snd) → ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧ GlobalTheory.FlagTan.IsKS (psiSet H) Q w.x (∑ a, m a • (ψ ∘ Mx a)) ∧ spMap θ ≫ tau hW₁ ≫ toFlag M = X.ptY w := by
  first | exact @GlobalTheory.HorFrame.exists_deform_of_comb | exact GlobalTheory.HorFrame.exists_deform_of_comb | (intros; apply GlobalTheory.HorFrame.exists_deform_of_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerMatrixFirstOrderDeformationStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kodairaSpencerMatrix_firstOrderDeformation : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hP : GlobalTheory.Published.AbelianDeRham) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (x' : Sp (DualNumber S) ⟶ Xo.X) (h1 : x' ≫ Xo.s = sOf c (DualNumber S))
    (h2 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ x' = y.x), ∃ Mx : HIx Dw (psiSet H) → S, ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : S →ₐ[c.F] K) (y' : FrPt Xo c K),
      FrMap ψ y y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ x') (ψ ∘ Mx) := by
  first | exact @GlobalTheory.KSFam.ksFamily | exact GlobalTheory.KSFam.ksFamily | (intros; apply GlobalTheory.KSFam.ksFamily <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenKodairaSpencerLeftInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenExistsFieldPointBasicOpenCommonDenomAl
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenExistsFieldPointBasicOpenCommonDenomAl
open AlgebraicGeometry

namespace GlobalTheory

theorem affineOpen_exists_field_point_basicOpen_commonDenom :
    ∀ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (p : X), p ∈ U →
      ∃ (K : Type) (_ : Field K) (ψ : Γ(X, U) →+* K), (∀ g, ψ g ≠ 0 → p ∈ X.basicOpen g) ∧
        ∀ (ι : Type) [Fintype ι] (m : ι → K), ∃ (a : ι → Γ(X, U)) (t : Γ(X, U)),
          ψ t ≠ 0 ∧ ∀ i, m i * ψ t = ψ (a i) := by
  intro X U hU p hp
  classical
  let P := hU.primeIdealOf ⟨p, hp⟩
  haveI : P.asIdeal.IsPrime := P.isPrime
  let K := FractionRing (Γ(X, U) ⧸ P.asIdeal)
  let ψ : Γ(X, U) →+* K := (algebraMap (Γ(X, U) ⧸ P.asIdeal) K).comp (Ideal.Quotient.mk P.asIdeal)
  have hψ : ∀ g, ψ g ≠ 0 ↔ g ∉ P.asIdeal := by
    intro g
    simp only [ψ, RingHom.comp_apply, ne_eq]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨K, inferInstance, ψ, ?_, ?_⟩
  · intro g hg
    have h1 : P ∈ PrimeSpectrum.basicOpen g := (hψ g).1 hg
    rw [← hU.fromSpec_preimage_basicOpen] at h1
    have h2 : hU.fromSpec P = p := hU.fromSpec_primeIdealOf ⟨p, hp⟩
    have h3 : hU.fromSpec P ∈ X.basicOpen g := h1
    rwa [h2] at h3
  · intro ι _ m
    have hrep : ∀ i, ∃ b s : Γ(X, U), ψ s ≠ 0 ∧ m i * ψ s = ψ b := by
      intro i
      obtain ⟨⟨b', ⟨s', hs'⟩⟩, he⟩ := IsLocalization.mk'_surjective
        (nonZeroDivisors (Γ(X, U) ⧸ P.asIdeal)) (m i)
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
      refine ⟨b, s, ?_, ?_⟩
      · simp only [ψ, RingHom.comp_apply, ne_eq]
        exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs'
      · rw [← he]
        simp only [ψ, RingHom.comp_apply]
        exact IsLocalization.mk'_spec _ _ _
    choose b s hs hbs using hrep
    refine ⟨fun i => b i * ∏ j ∈ Finset.univ.erase i, s j, ∏ j, s j, ?_, ?_⟩
    · rw [map_prod]
      exact Finset.prod_ne_zero_iff.2 (fun j _ => hs j)
    · intro i
      rw [map_prod, ← Finset.mul_prod_erase Finset.univ (fun j => ψ (s j)) (Finset.mem_univ i),
        ← mul_assoc, hbs i, map_mul, map_prod]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenExistsFieldPointBasicOpenCommonDenomAlStatement
open AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_field_common_denom_of_mem_isAffineOpen : ∀ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (p : X), p ∈ U → ∃ (K : Type) (_ : Field K) (ψ : Γ(X, U) →+* K), (∀ g, ψ g ≠ 0 → p ∈ X.basicOpen g) ∧ ∀ (ι : Type) [Fintype ι] (m : ι → K), ∃ (a : ι → Γ(X, U)) (t : Γ(X, U)), ψ t ≠ 0 ∧ ∀ i, m i * ψ t = ψ (a i) := by
  first | exact @GlobalTheory.affineOpen_exists_field_point_basicOpen_commonDenom | exact GlobalTheory.affineOpen_exists_field_point_basicOpen_commonDenom | (intros; apply GlobalTheory.affineOpen_exists_field_point_basicOpen_commonDenom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenKodairaSpencerLeftInverse
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

theorem GlobalTheory.HorFrame.exists_ksComb_eq_single : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (k : X.F.J) {W₁ : M.X.Opens} (hW₁ : IsAffineOpen W₁), W₁ ≤ M.off → ∀ (hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k) [Algebra c.F Γ(M.X, W₁)] (Q₀ : FrPt Xo c Γ(M.X, W₁)), X.F.ChartFr k _ hk₁ Q₀ → ∀ (d : Fin (dimFlag Dw) → (Γ(M.X, W₁) →+* DualNumber Γ(M.X, W₁))), (∀ a s, (d a s).fst = s) → (∀ (K : Type) [Field K] (θ : Γ(M.X, W₁) →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s, (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd)) → ∀ (Mx : Fin (dimFlag Dw) → HIx Dw (psiSet H) → Γ(M.X, W₁)), (∀ a (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →ₐ[c.F] K) (y' : FrPt Xo c K), FrMap ψ Q₀ y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ spMap (d a) ≫ Q₀.x) (ψ ∘ Mx a)) → ∀ (K : Type) [Field K] (ψ : Γ(M.X, W₁) →+* K) (b : HIx Dw (psiSet H)), ∃ m : Fin (dimFlag Dw) → K, ∑ a, m a • (ψ ∘ Mx a) = Pi.single b 1 := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS k W₁ hW₁ hoff hk₁ _ Q₀ hQ₀ d hd hspan Mx hMx K _ ψ b
  letI : Algebra c.F K := (ψ.comp (algebraMap c.F Γ(M.X, W₁))).toAlgebra
  let ψA : Γ(M.X, W₁) →ₐ[c.F] K := { ψ with commutes' := fun _ => rfl }
  obtain ⟨Qp, hQp⟩ := GlobalTheory.FlagMod.exists_frMap ψA Q₀
  have hk : ⊤ ≤ ((spMap ψ ≫ tau hW₁) ≫ toFlag M) ⁻¹ᵁ X.F.U k := by
    rw [Category.assoc]; exact le_preimage_comp _ hk₁
  have hch : X.F.ChartFr k _ hk Qp := hQ₀.frMap hQp (Category.assoc _ _ _).symm hk
  have e : (spMap ψ ≫ tau hW₁) ≫ toFlag M = X.ptY Qp := GlobalTheory.FlagMod.FlagCover.eq_ptY hch.lies
  have ho : ⊤ ≤ (spMap ψ ≫ tau hW₁) ⁻¹ᵁ M.off := le_preimage_comp _ (tau_le hW₁ hoff)
  obtain ⟨v, hv⟩ := (hKS K Qp).exists_isTanFrame
  obtain ⟨zv, hzv, hzO⟩ := GlobalTheory.CompHS.exists_tanLift M (hv.isDef (.inl b)) e ho
  have hzW : ⊤ ≤ zv ⁻¹ᵁ W₁ := hzO W₁ (le_preimage_comp _ (tau_le hW₁ le_rfl))
  have hθ : spMap (ev zv W₁ hzW) ≫ tau hW₁ = zv := spMap_ev zv hW₁ hzW
  have hred : spMap (GlobalTheory.FlagTan.red c K).toRingHom ≫ zv = spMap ψ ≫ tau hW₁ := by
    have hU : ⊤ ≤ ((spMap ψ ≫ tau hW₁) ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
      have := ho (Set.mem_univ s)
      rw [M.off_eq] at this
      exact this
    refine (M.existsUnique_lift _ hU).unique ?_ rfl
    rw [← cancel_mono (inc₀ X Z)]
    have h1 : zv ≫ M.σ ≫ inc₀ X Z = X.ptY (v (.inl b)) := hzv
    have h2 : ((spMap ψ ≫ tau hW₁) ≫ M.σ) ≫ inc₀ X Z = X.ptY Qp := by
      rw [← e, Category.assoc]
    rw [h2, Category.assoc, Category.assoc, h1]
    exact X.ptY_frMap (hv.isDef (.inl b))
  have hfst : ∀ s, (ev zv W₁ hzW s).fst = ψ s := by
    have h1 := ev_spMap (GlobalTheory.FlagTan.red c K).toRingHom zv W₁ hzW
      (by rw [hred]; exact le_preimage_comp _ (tau_le hW₁ le_rfl))
    have h2 := ev_spMap_tau hW₁ ψ (le_preimage_comp _ (tau_le hW₁ le_rfl))
    rw [ev_congr hred _ _ (le_preimage_comp _ (tau_le hW₁ le_rfl)), h2] at h1
    intro s
    have := congrArg (fun f : Γ(M.X, W₁) →+* K => f s) h1
    simp only [RingHom.comp_apply] at this
    rw [this]
    rfl
  obtain ⟨m, hm⟩ := hspan K (ev zv W₁ hzW)
  have hsnd : ∀ s, (ev zv W₁ hzW s).snd = ∑ a, m a * ψ (d a s).snd := fun s => by
    rw [hm s]
    exact Finset.sum_congr rfl fun a _ => by rw [← hfst]; rfl
  obtain ⟨w, hwD, hwKS, hwpt⟩ := GlobalTheory.T.exists_chart_frame_deformation_of_derivation_combination M hKS k hW₁ hk₁ Q₀ hQ₀ d hd Mx hMx K ψ hk Qp hch
    (ev zv W₁ hzW) m hfst hsnd
  have hpt : X.ptY w = X.ptY (v (.inl b)) := by
    rw [← hwpt, ← Category.assoc, hθ, hzv]
  have hx : w.x = (v (.inl b)).x := by
    have h1 := (X.lies_ptY w).1
    have h2 := (X.lies_ptY (v (.inl b))).1
    rw [hpt] at h1
    rw [← frX_fst, ← frX_fst, xF_ext (Y := Y) (frX_snd w) (frX_snd _) (h1.symm.trans h2)]
  obtain ⟨M', -, hu⟩ := (hKS K Qp).existsUnique hwD.isTanX
  refine ⟨m, (hu _ hwKS).trans (hu _ ?_).symm⟩
  rw [hx]
  exact (hv.1 b).2

theorem GlobalTheory.HorFrame.exists_basicOpen_det_ks : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (k : X.F.J) {W₁ : M.X.Opens} (hW₁ : IsAffineOpen W₁), W₁ ≤ M.off → ∀ (hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k) [Algebra c.F Γ(M.X, W₁)] (Q₀ : FrPt Xo c Γ(M.X, W₁)), X.F.ChartFr k _ hk₁ Q₀ → ∀ (d : Fin (dimFlag Dw) → (Γ(M.X, W₁) →+* DualNumber Γ(M.X, W₁))), (∀ a s, (d a s).fst = s) → (∀ (K : Type) [Field K] (θ : Γ(M.X, W₁) →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s, (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd)) → ∀ (Mx : Fin (dimFlag Dw) → HIx Dw (psiSet H) → Γ(M.X, W₁)), (∀ a (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →ₐ[c.F] K) (y' : FrPt Xo c K), FrMap ψ Q₀ y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ spMap (d a) ≫ Q₀.x) (ψ ∘ Mx a)) → ∀ (p : M.X), p ∈ W₁ → ∃ B : Matrix (HIx Dw (psiSet H)) (Fin (dimFlag Dw)) Γ(M.X, W₁), p ∈ M.X.basicOpen (B * Matrix.of (fun a h => Mx a h)).det := by
  intro E _ _ _ H Dw l Xo c Y X Z M hKS k W₁ hW₁ hoff hk₁ _ Q₀ hQ₀ d hd hspan Mx hMx p hp
  obtain ⟨K, hK, ψ, hbo, hden⟩ := GlobalTheory.T.exists_ringHom_field_common_denom_of_mem_isAffineOpen hW₁ p hp
  choose m hm using fun b => GlobalTheory.HorFrame.exists_ksComb_eq_single M hKS k hW₁ hoff hk₁ Q₀ hQ₀ d hd hspan Mx hMx K ψ b
  obtain ⟨a, t, ht, hat⟩ := hden (HIx Dw (psiSet H) × Fin (dimFlag Dw)) (fun bc => m bc.1 bc.2)
  refine ⟨Matrix.of fun b c => a (b, c), hbo _ ?_⟩
  have hmap : ((Matrix.of fun b c => a (b, c)) * Matrix.of (fun a h => Mx a h)).map ψ =
      Matrix.scalar (HIx Dw (psiSet H)) (ψ t) := by
    ext b h
    have e := congrFun (hm b) h
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul] at e
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, Matrix.scalar_apply,
      Matrix.diagonal_apply]
    simp only [← hat]
    calc ∑ x, m b x * ψ t * ψ (Mx x h) = ψ t * ∑ x, m b x * ψ (Mx x h) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
      _ = _ := by
          rw [e, Pi.single_apply]
          by_cases hh : h = b
          · subst hh; simp
          · simp [hh, Ne.symm hh]
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const]
  exact pow_ne_zero _ ht
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenKodairaSpencerLeftInverseStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_kodairaSpencer_left_inverse : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)), (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (k : X.F.J) {W₁ : M.X.Opens} (hW₁ : IsAffineOpen W₁), W₁ ≤ M.off → ∀ (hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k) [Algebra c.F Γ(M.X, W₁)] (Q₀ : FrPt Xo c Γ(M.X, W₁)), X.F.ChartFr k _ hk₁ Q₀ → ∀ (d : Fin (dimFlag Dw) → (Γ(M.X, W₁) →+* DualNumber Γ(M.X, W₁))), (∀ a s, (d a s).fst = s) → (∀ (K : Type) [Field K] (θ : Γ(M.X, W₁) →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s, (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd)) → ∀ (Mx : Fin (dimFlag Dw) → HIx Dw (psiSet H) → Γ(M.X, W₁)), (∀ a (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W₁) →ₐ[c.F] K) (y' : FrPt Xo c K), FrMap ψ Q₀ y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (dualMap ψ.toRingHom) ≫ spMap (d a) ≫ Q₀.x) (ψ ∘ Mx a)) → ∀ (p : M.X), p ∈ W₁ → ∃ B : Matrix (HIx Dw (psiSet H)) (Fin (dimFlag Dw)) Γ(M.X, W₁), p ∈ M.X.basicOpen (B * Matrix.of (fun a h => Mx a h)).det := by
  first | exact @GlobalTheory.HorFrame.exists_basicOpen_det_ks | exact GlobalTheory.HorFrame.exists_basicOpen_det_ks | (intros; apply GlobalTheory.HorFrame.exists_basicOpen_det_ks <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCoverWithDualNumberDerivations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndEqSum
namespace GlobalTheory.SecondComponentSum

theorem snd_eq_sum {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {D : ℕ}
    (f : Fin D → A) (B : Module.Basis (Fin D) A Ω[A⁄k])
    (hB : ∀ i : Fin D, B i = KaehlerDifferential.D k A (f i))
    {K : Type} [Field K] (θ : A →+* DualNumber K)
    (hθ : ∀ a : k, TrivSqZeroExt.snd (θ (algebraMap k A a)) = (0 : K)) (s : A) :
    TrivSqZeroExt.snd (θ s) = ∑ b : Fin D, TrivSqZeroExt.snd (θ (f b)) *
      TrivSqZeroExt.fst (θ ((LinearMap.compDer (Module.Basis.coord B b)
        (KaehlerDifferential.D k A)) s)) := by
  classical

  let φ : A →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom.comp θ
  let _ : Module A K := Module.compHom K φ
  let _ : Module k K := Module.compHom K (φ.comp (algebraMap k A))
  have : IsScalarTower k A K := ⟨fun c a x => by
    change φ (c • a) * x = φ (algebraMap k A c) * (φ a * x)
    rw [Algebra.smul_def, map_mul, mul_assoc]⟩
  have hsmul : ∀ (a : A) (x : K), a • x = TrivSqZeroExt.fst (θ a) * x := fun _ _ => rfl
  have hsndmul : ∀ a b : A, TrivSqZeroExt.snd (θ (a * b)) =
      TrivSqZeroExt.fst (θ a) * TrivSqZeroExt.snd (θ b) +
        TrivSqZeroExt.snd (θ a) * TrivSqZeroExt.fst (θ b) := by
    intro a b
    rw [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, op_smul_eq_mul]
  let ℓ : A →ₗ[k] K :=
    { toFun := fun a => TrivSqZeroExt.snd (θ a)
      map_add' := fun a b => by
        simp only [map_add (f := _), TrivSqZeroExt.snd_add]
      map_smul' := fun c a => by
        change TrivSqZeroExt.snd (θ (c • a)) = φ (algebraMap k A c) * TrivSqZeroExt.snd (θ a)
        rw [Algebra.smul_def, hsndmul, hθ, zero_mul, add_zero]
        rfl }
  let d : Derivation k A K := Derivation.mk' ℓ fun a b => by
    change TrivSqZeroExt.snd (θ (a * b)) = TrivSqZeroExt.fst (θ a) * TrivSqZeroExt.snd (θ b) +
      TrivSqZeroExt.fst (θ b) * TrivSqZeroExt.snd (θ a)
    rw [hsndmul, mul_comm (TrivSqZeroExt.snd (θ a))]

  have key := congrArg d.liftKaehlerDifferential (B.sum_repr (KaehlerDifferential.D k A s))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Derivation.liftKaehlerDifferential_comp_D, map_sum] at key
  change d s = _
  rw [← key]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [LinearMap.map_smul, hB, Derivation.liftKaehlerDifferential_comp_D, hsmul, mul_comm]
  rfl

end GlobalTheory.SecondComponentSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCoverWithDualNumberDerivations
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

theorem exists_basis_kaehler_D {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {D : ℕ}
    [Algebra.IsStandardSmoothOfRelativeDimension D k A] :
    ∃ (f : Fin D → A) (B : Module.Basis (Fin D) A Ω[A⁄k]), ∀ i, B i = KaehlerDifferential.D k A (f i) := by
  classical
  obtain ⟨ι, σ, _, _, P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension D k A›.out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨fun i => P.val (e.symm i), P.basisKaehler.reindex e, fun i => by simp⟩

def derivHom {k A : Type} [CommRing k] [CommRing A] [Algebra k A] (δ : Derivation k A A) :
    A →+* DualNumber A where
  toFun s := TrivSqZeroExt.inl s + TrivSqZeroExt.inr (δ s)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [Derivation.leibniz, smul_eq_mul, mul_comm]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp [add_comm, add_left_comm, add_assoc]

theorem snd_eq_sum_of_basis {k A : Type} [CommRing k] [CommRing A] [Algebra k A] {D : ℕ}
    (f : Fin D → A) (B : Module.Basis (Fin D) A Ω[A⁄k]) (hB : ∀ i, B i = KaehlerDifferential.D k A (f i))
    {K : Type} [Field K] (θ : A →+* DualNumber K) (h : ∀ a, (θ (algebraMap k A a)).snd = 0) (s : A) :
    (θ s).snd = ∑ b, (θ (f b)).snd *
      (θ (((B.coord b).compDer (KaehlerDifferential.D k A)) s)).fst := by
  first
  | exact @_root_.GlobalTheory.SecondComponentSum.snd_eq_sum
  | exact _root_.GlobalTheory.SecondComponentSum.snd_eq_sum
  | (apply _root_.GlobalTheory.SecondComponentSum.snd_eq_sum <;> assumption)
  | (intros; apply _root_.GlobalTheory.SecondComponentSum.snd_eq_sum <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SecondComponentSum.snd_eq_sum <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SecondComponentSum.snd_eq_sum ..)

theorem snd_eq_zero_of_isAlgebraic {F K : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] [Field K]
    (φ : F →+* DualNumber K) (a : F) : (φ a).snd = 0 := by
  letI : Algebra ℚ (DualNumber K) := (φ.comp (algebraMap ℚ F)).toAlgebra
  have : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  have := Algebra.FormallyUnramified.ext' (R := ℚ) (A := F) (B := DualNumber K)
    (TrivSqZeroExt.fstHom K K K).toRingHom ⟨2, TrivSqZeroExt.kerIdeal_sq K K⟩ φ.toRatAlgHom
    ((algebraMap K (DualNumber K)).comp ((TrivSqZeroExt.fstHom K K K).toRingHom.comp φ)).toRatAlgHom
    (fun a => by simp [TrivSqZeroExt.algebraMap_eq_inl])
  have e := DFunLike.congr_fun this a
  change φ a = _ at e
  rw [e]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}

theorem exists_derivFrame (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (W : M.X.Opens) (p : M.X)
    (hp : p ∈ W) : ∃ (W' : M.X.Opens) (_ : IsAffineOpen W')
      (d : Fin (dimFlag Dw) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W'))), p ∈ W' ∧ W' ≤ W ∧
      (∀ b s, (d b s).fst = s) ∧
      ∀ (K : Type) [Field K] (θ : Γ(M.X, W') →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s,
        (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd) := by
  obtain ⟨V, hV, hx, hVW⟩ := Opens.isBasis_iff_nbhd.1 M.X.isBasis_affineOpens hp
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension (dimFlag Dw)) M.str M.smooth
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(M.X, V)), p ∈ M.X.basicOpen (t : Γ(M.X, V)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(M.X, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(M.X, M.X.basicOpen (t : Γ(M.X, V))))
  have h₂ : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX M.str (M.X.basicOpen (t : Γ(M.X, V)))).IsStandardSmoothOfRelativeDimension
      (dimFlag Dw) := by
    rw [← resG_comp_algX M.str (M.X.basicOpen_le (t : Γ(M.X, V)))]
    exact h₁
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX M.str (M.X.basicOpen (t : Γ(M.X, V)))).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension (dimFlag Dw) c.F Γ(M.X, M.X.basicOpen (t : Γ(M.X, V))) := h₂
  obtain ⟨f, B, hB⟩ := exists_basis_kaehler_D (D := dimFlag Dw) (k := c.F) (A := Γ(M.X, M.X.basicOpen (t : Γ(M.X, V))))
  refine ⟨_, IsAffineOpen.basicOpen hV _, fun b => derivHom ((B.coord b).compDer (KaehlerDifferential.D c.F _)),
    hxt, (M.X.basicOpen_le _).trans (hVW.trans le_rfl), fun b s => by simp [derivHom], fun K _ θ =>
    ⟨fun b => (θ (f b)).snd, fun s => ?_⟩⟩
  rw [snd_eq_sum_of_basis f B hB θ (fun a => snd_eq_zero_of_isAlgebraic (θ.comp (algebraMap c.F _)) a) s]
  simp [derivHom]

end GlobalTheory.CompHS
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCoverWithDualNumberDerivationsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_cover_with_dual_number_derivations : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (W : M.X.Opens) (p : M.X) (hp : p ∈ W), ∃ (W' : M.X.Opens) (_ : IsAffineOpen W')
      (d : Fin (dimFlag Dw) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W'))), p ∈ W' ∧ W' ≤ W ∧
      (∀ b s, (d b s).fst = s) ∧
      ∀ (K : Type) [Field K] (θ : Γ(M.X, W') →+* DualNumber K), ∃ m : Fin (dimFlag Dw) → K, ∀ s,
        (θ s).snd = ∑ b, m b * (TrivSqZeroExt.fstHom K K K).toRingHom (θ (d b s).snd) := by
  first | exact @GlobalTheory.CompHS.exists_derivFrame | exact GlobalTheory.CompHS.exists_derivFrame | (intros; apply GlobalTheory.CompHS.exists_derivFrame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberDeformationExtendsAway
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberDeformationExtendsAway
namespace GlobalTheory

def dualNumberRingHomMap {S S' : Type} [CommRing S] [CommRing S'] (f : S →+* S') :
    DualNumber S →+* DualNumber S' where
  toFun x := TrivSqZeroExt.inl (f x.fst) + TrivSqZeroExt.inr (f x.snd)
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, mul_comm] <;> ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp <;> ring

theorem dualNumber_deformation_extends_away :
    ∀ {S S' : Type} [CommRing S] [CommRing S'] [Algebra S S'] (g : S) [IsLocalization.Away g S']
      (d : S →+* DualNumber S), (∀ s, (d s).fst = s) →
      ∃ d' : S' →+* DualNumber S', (∀ s, (d' s).fst = s) ∧
        ∀ s, (d' (algebraMap S S' s)).snd = algebraMap S S' (d s).snd := by
  intro S S' _ _ _ g _ d hd
  let ψ : S →+* DualNumber S' := (dualNumberRingHomMap (algebraMap S S')).comp d
  have hψ : ∀ s, ψ s = TrivSqZeroExt.inl (algebraMap S S' (d s).fst)
      + TrivSqZeroExt.inr (algebraMap S S' (d s).snd) := fun s => rfl
  have hu : IsUnit (ψ g) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hψ]
    simpa [hd] using IsLocalization.Away.algebraMap_isUnit (S := S') g
  refine ⟨IsLocalization.Away.lift g hu, ?_, ?_⟩
  · have h : (TrivSqZeroExt.fstHom S' S' S').toRingHom.comp (IsLocalization.Away.lift g hu)
        = RingHom.id S' := by
      apply IsLocalization.ringHom_ext (Submonoid.powers g)
      ext s
      simp [IsLocalization.Away.lift, IsLocalization.lift_eq, hψ, hd]
    intro s
    exact congrArg (fun F : S' →+* S' => F s) h
  · intro s
    simp [IsLocalization.Away.lift, IsLocalization.lift_eq, hψ]
    rw [Algebra.smul_def, mul_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberDeformationExtendsAwayStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualNumber_deformation_extend_away : ∀ {S S' : Type} [CommRing S] [CommRing S'] [Algebra S S'] (g : S) [IsLocalization.Away g S'] (d : S →+* DualNumber S), (∀ s, (d s).fst = s) → ∃ d' : S' →+* DualNumber S', (∀ s, (d' s).fst = s) ∧ ∀ s, (d' (algebraMap S S' s)).snd = algebraMap S S' (d s).snd := by
  first | exact @GlobalTheory.dualNumber_deformation_extends_away | exact GlobalTheory.dualNumber_deformation_extends_away | (intros; apply GlobalTheory.dualNumber_deformation_extends_away <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeDeRhamOnModificationOfFlagCover
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

namespace GlobalTheory.HorFrame

def combDer {R : Type} [CommRing R] {ι : Type} [Fintype ι] (δ : ι → (R →+* DualNumber R))
    (hδ : ∀ i s, (δ i s).fst = s) (A : ι → R) : R →+* DualNumber R where
  toFun s := TrivSqZeroExt.inl s + TrivSqZeroExt.inr (∑ i, A i * (δ i s).snd)
  map_one' := by
    have h : ∀ i, (δ i 1).snd = 0 := fun i => by rw [map_one]; rfl
    ext <;> simp [h]
  map_mul' x y := by
    have h : ∀ i, (δ i (x * y)).snd = x * (δ i y).snd + (δ i x).snd * y := fun i => by
      rw [map_mul, TrivSqZeroExt.snd_mul, hδ, hδ, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add,
        TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
        smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, h, Finset.mul_sum, Finset.sum_mul,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
  map_zero' := by
    have h : ∀ i, (δ i 0).snd = 0 := fun i => by rw [map_zero]; rfl
    ext <;> simp [h]
  map_add' x y := by
    ext <;> simp [Finset.sum_add_distrib, mul_add]

theorem combDer_fst {R : Type} [CommRing R] {ι : Type} [Fintype ι] (δ : ι → (R →+* DualNumber R))
    (hδ : ∀ i s, (δ i s).fst = s) (A : ι → R) (s : R) : (combDer δ hδ A s).fst = s := by
  simp [combDer]

theorem combDer_snd {R : Type} [CommRing R] {ι : Type} [Fintype ι] (δ : ι → (R →+* DualNumber R))
    (hδ : ∀ i s, (δ i s).fst = s) (A : ι → R) (s : R) :
    (combDer δ hδ A s).snd = ∑ i, A i * (δ i s).snd := by
  simp [combDer]

theorem fst_dualMap {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (x : DualNumber S) :
    (dualMap φ x).fst = φ x.fst := by simp [dualMap]

theorem snd_dualMap {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (x : DualNumber S) :
    (dualMap φ x).snd = φ x.snd := by simp [dualMap]

end GlobalTheory.HorFrame


open GlobalTheory.HorFrame in
theorem GlobalTheory.HorFrame.exists_horizontal_lift : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hP : GlobalTheory.Published.AbelianDeRham)
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) (k : X.F.J)
    (W : M.X.Opens) (hW : W ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k) (p : M.X) (hp : p ∈ W), ∃ (W' : M.X.Opens) (hW' : IsAffineOpen W')
      (e : HIx Dw (psiSet H) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W'))),
      p ∈ W' ∧ W' ≤ W ∧ (∀ b s, (e b s).fst = s) ∧
      ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W') →+* K)
        (hk : ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
        X.F.ChartFr k _ hk Q → ∀ b, ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧
          GlobalTheory.FlagTan.IsKS (psiSet H) Q w.x (Pi.single b 1) ∧
          spMap ((dualMap ψ).comp (e b)) ≫ tau hW' ≫ toFlag M = X.ptY w := by
  intro E _ _ _ H Dw l Xo c Y X Z M hP hKS k W hW p hp
  haveI := c.fin
  obtain ⟨W₁, hW₁, d, hpW₁, hW₁W, hd, hspan⟩ := GlobalTheory.T.exists_affine_cover_with_dual_number_derivations M W p hp
  have hoff : W₁ ≤ M.off := fun x hx => (hW (hW₁W hx)).1
  have hτ : ⊤ ≤ tau hW₁ ⁻¹ᵁ W₁ := tau_le hW₁ le_rfl
  have hk₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ X.F.U k := fun s _ => (hW (hW₁W (hτ (Set.mem_univ s)))).2
  have hF₁ : ⊤ ≤ (tau hW₁ ≫ toFlag M) ⁻¹ᵁ flagOpen X := fun s _ => by
    have := hoff (hτ (Set.mem_univ s))
    rw [M.off_eq] at this
    exact this
  obtain ⟨alg₁, hch⟩ := GlobalTheory.CompHS.exists_chartFr (tau hW₁ ≫ toFlag M) hF₁
  obtain ⟨Q₀, hQ₀⟩ := hch k hk₁
  have hdalg : ∀ b, (d b).comp (algebraMap c.F Γ(M.X, W₁)) = algebraMap c.F (DualNumber Γ(M.X, W₁)) :=
    fun b => RingHom.ext fun a => TrivSqZeroExt.ext
      (by rw [RingHom.comp_apply, hd]; rfl) (by
      rw [GlobalTheory.T.ringHom_numberField_dualNumber_snd_eq_zero c.F ((d b).comp (algebraMap c.F _)) a]; rfl)
  have hx1 : ∀ b, (spMap (d b) ≫ Q₀.x) ≫ Xo.s = sOf c (DualNumber Γ(M.X, W₁)) := fun b => by
    rw [Category.assoc, Q₀.x_over]
    unfold sOf
    rw [spMap_comp', ← RingHom.comp_assoc, hdalg]
  have hx2 : ∀ b, spMap (TrivSqZeroExt.fstHom Γ(M.X, W₁) Γ(M.X, W₁) Γ(M.X, W₁)).toRingHom ≫ spMap (d b) ≫ Q₀.x
      = Q₀.x := fun b => by
    rw [← Category.assoc, spMap_comp']
    have : (TrivSqZeroExt.fstHom Γ(M.X, W₁) Γ(M.X, W₁) Γ(M.X, W₁)).toRingHom.comp (d b) = RingHom.id _ :=
      RingHom.ext fun s => hd b s
    rw [this]
    exact (congrArg (· ≫ Q₀.x) (Spec.map_id _)).trans (Category.id_comp _)
  choose Mx hMx using fun b => GlobalTheory.T.exists_kodairaSpencerMatrix_firstOrderDeformation hP Q₀ (spMap (d b) ≫ Q₀.x) (hx1 b) (hx2 b)
  obtain ⟨B, hB⟩ := GlobalTheory.T.exists_basicOpen_kodairaSpencer_left_inverse M hKS k hW₁ hoff hk₁ Q₀ hQ₀ d hd hspan Mx hMx p hpW₁
  set MxM : Matrix (Fin (dimFlag Dw)) (HIx Dw (psiSet H)) Γ(M.X, W₁) := Matrix.of (fun a h => Mx a h) with hMxM
  set g : Γ(M.X, W₁) := (B * MxM).det with hg
  have hW' : IsAffineOpen (M.X.basicOpen g) := hW₁.basicOpen g
  have hW'W₁ : M.X.basicOpen g ≤ W₁ := M.X.basicOpen_le g
  haveI := hW₁.isLocalization_basicOpen g
  set ρ := algebraMap Γ(M.X, W₁) Γ(M.X, M.X.basicOpen g) with hρ
  choose d' hd'1 hd'2 using fun b => GlobalTheory.T.exists_dualNumber_deformation_extend_away (S' := Γ(M.X, M.X.basicOpen g)) g (d b) (hd b)
  have hunit : IsUnit ((B * MxM).map ρ).det := by
    have : ((B * MxM).map ρ).det = ρ (B * MxM).det := by rw [RingHom.map_det]; rfl
    rw [this]
    exact IsLocalization.Away.algebraMap_isUnit g
  set A := ((B * MxM).map ρ)⁻¹ * B.map ρ with hA
  have hAM : A * MxM.map ρ = 1 := by
    rw [hA, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hunit]
  have hτ' : spMap ρ ≫ tau hW₁ = tau hW' := by
    have e1 := spMap_ev (tau hW') hW₁ (tau_le hW' hW'W₁)
    have e2 : ev (tau hW') W₁ (tau_le hW' hW'W₁) = ρ := RingHom.ext fun a => ev_tau hW' hW'W₁ _ a
    rw [← e2]
    exact e1
  refine ⟨M.X.basicOpen g, hW', fun b => combDer d' hd'1 (fun a => A b a), hB, hW'W₁.trans hW₁W,
    fun b s => combDer_fst _ _ _ _, ?_⟩
  intro K _ _ ψ hk Q hQ b
  have ez : (spMap ψ ≫ tau hW') ≫ toFlag M = (spMap (ψ.comp ρ) ≫ tau hW₁) ≫ toFlag M := by
    rw [← hτ', ← spMap_comp' ρ ψ]
    simp only [Category.assoc]
  have hk' : ⊤ ≤ ((spMap (ψ.comp ρ) ≫ tau hW₁) ≫ toFlag M) ⁻¹ᵁ X.F.U k := ez ▸ hk
  have hQ' : X.F.ChartFr k _ hk' Q :=
    hQ.frMap (frMap_refl Q) ((spMap_algId _).trans ez) hk'
  obtain ⟨w, hwD, hwKS, hwpt⟩ := GlobalTheory.T.exists_chart_frame_deformation_of_derivation_combination M hKS k hW₁ hk₁ Q₀ hQ₀ d hd Mx hMx K (ψ.comp ρ) hk' Q hQ'
    ((dualMap ψ).comp ((combDer d' hd'1 (fun a => A b a)).comp ρ)) (fun a => ψ (A b a))
    (fun s => by rw [RingHom.comp_apply, fst_dualMap, RingHom.comp_apply, combDer_fst]; rfl)
    (fun s => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [RingHom.comp_apply, snd_dualMap, RingHom.comp_apply, combDer_snd, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, hd'2]
      rfl)
  refine ⟨w, hwD, ?_, ?_⟩
  · have key : ∀ h, ∑ a, ψ (A b a) * ψ (ρ (Mx a h)) = (Pi.single b (1 : K) : HIx Dw (psiSet H) → K) h := fun h => by
      have e := congrArg (fun N => ψ (N b h)) hAM
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_apply, Matrix.map_apply, hMxM, Matrix.of_apply, map_sum, map_mul] at e
      rw [e, Matrix.one_apply, Pi.single_apply]
      by_cases hh : h = b
      · subst hh; simp
      · simp [hh, Ne.symm hh]
    convert hwKS using 1
    funext h
    rw [Finset.sum_apply, ← key h]
    rfl
  · rw [← hwpt, ← hτ']
    simp only [← Category.assoc, spMap_comp']
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeDeRhamOnModificationOfFlagCoverStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_de_rham_on_modification_of_flag_cover : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) (hP : GlobalTheory.Published.AbelianDeRham)
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) (k : X.F.J)
    (W : M.X.Opens) (hW : W ≤ M.off ⊓ (toFlag M) ⁻¹ᵁ X.F.U k) (p : M.X) (hp : p ∈ W), ∃ (W' : M.X.Opens) (hW' : IsAffineOpen W')
      (e : HIx Dw (psiSet H) → (Γ(M.X, W') →+* DualNumber Γ(M.X, W'))),
      p ∈ W' ∧ W' ≤ W ∧ (∀ b s, (e b s).fst = s) ∧
      ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : Γ(M.X, W') →+* K)
        (hk : ⊤ ≤ ((spMap ψ ≫ tau hW') ≫ toFlag M) ⁻¹ᵁ X.F.U k) (Q : FrPt Xo c K),
        X.F.ChartFr k _ hk Q → ∀ b, ∃ w : FrPt Xo c (DualNumber K), IsDef Q w ∧
          GlobalTheory.FlagTan.IsKS (psiSet H) Q w.x (Pi.single b 1) ∧
          spMap ((dualMap ψ).comp (e b)) ≫ tau hW' ≫ toFlag M = X.ptY w := by
  first | exact @GlobalTheory.HorFrame.exists_horizontal_lift | exact GlobalTheory.HorFrame.exists_horizontal_lift | (intros; apply GlobalTheory.HorFrame.exists_horizontal_lift <;> assumption)
end
